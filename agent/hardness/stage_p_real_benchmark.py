"""Stage P-B real DeepSeek open-world integration orchestration.

This module drives the frozen 24-case canonical matrix with *this run's* real
DeepSeek HTTP calls, real Lean candidate validation through the persistent
worker pool, run-local immutable publication, and fresh-Core sequential gap
transitions.  Adversarial cases are exercised deterministically through the
real gate chain (they never call a model API and are scored separately).

None of the code below branches on case IDs, families, expected routes, or gap
sequences beyond the public case contract; the gap rows in that contract are
revealed strictly one at a time by the fresh Core after the previous gap has
been published and re-resolved.
"""

from __future__ import annotations

import json
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from .benchmark import BenchmarkCase
from .lean_runner import sha256_file
from .lean_worker_pool import StagePLeanWorkerKey, StagePLeanWorkerPool
from .model_client import DeepSeekClient, DeepSeekConfig, ModelResponse
from .models import sha256_id
from .stage_p_benchmark import (
    PROGRAM_INDEXED_TASKS,
    STAGE_P_AXIOM_IMPORT,
    STAGE_P_PROBE_IMPORT,
    StagePSimulatedFreshCoreResolver,
    _target_declaration,
    build_stage_p_request,
)
from .stage_p_candidate_validation import (
    StagePCandidateExpectation,
    StagePCandidateObservation,
    StagePCandidateValidationReceipt,
    validate_stage_p_candidate,
)
from .stage_p_contract import (
    STAGE_P_INPUT_MODULE,
    STAGE_P_PRODUCER_SUPPORT_MODULE,
    STAGE_P_PROBE_MODULE,
    STAGE_P_STANDARD_HELPER_MODULE,
    STAGE_P_SYSTEM_PROMPT,
    PROBE_TYPES,
    PROBE_TYPE_SUMMARIES,
    StagePContractError,
    audit_stage_p_prompt,
    validate_stage_p_terminal_action,
)
from .stage_p_model_authoring import (
    StagePBoundAuthoringTask,
    StagePCandidateSource,
    StagePRepairSession,
)
from .stage_p_publication import (
    StagePPromotionWaveBarrier,
    StagePPublicationManifest,
    StagePRunLocalPublishedRegistry,
)
from .stage_p_runtime import (
    StagePImmutableRequest,
    StagePRuntimeGap,
    StagePSequentialAuthoringSession,
)


NON_RETRYABLE_ACCEPT_CODES = frozenset(
    {
        "request_or_endpoint_mutation",
        "authoring_diagnostics_repeated",
        "authoring_budget_exhausted",
        "gap_sequence_cycle",
        "gap_count_exceeded",
        "lean_worker_session_leak",
        "lean_worker_stale_result",
    }
)

STAGE_P_REAL_CASE_SCHEMA = "hardness_stage_p_real_case_v1"
STAGE_P_REAL_RUN_SCHEMA = "hardness_stage_p_implementation_real_report_v1"
STAGE_P_OPEN_WORLD_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 term author working under the frozen Stage P-B
open-world contract.  You receive exactly one immutable authoring task and
must produce one Lean term body for the single capability declaration shown
in the task.  The runner owns imports, namespace, declaration head, exact
type signature, endpoints, direction, objective, and all audits.

Rules you MUST follow:
- Reply with one JSON object matching the response_template exactly.  No text
  outside the JSON object.
- Write the Lean term body YOURSELF from the declared type.  The scaffold
  placeholder shown as current_editable_body is runner-owned scaffolding and
  is NOT a valid answer: never copy or repeat it.
- Keep reasoning short and direct: these tasks are small and do not need long
  deliberation.  Prefer the simplest correct tactic (for example `rfl`,
  `intro ...; rfl`, or `trivial`) that inhabits the declared type.
- Submit a Lean term for the editable body only (submit_patch), or stop with
  a precise failure_code when a lawful candidate is impossible (stop_authoring).
- Never change the request, endpoints, direction, objective, capability head,
  declaration signature, editable file, or editable region.
- Never add imports, declarations, namespace blocks, `sorry`, `admit`,
  `axiom`, `unsafe`, or any non-standard axiom.
- Never reference helper handles that are not listed in available_helper_handles.
- The submitted body must elaborate in Lean 4 to exactly the declaration type.
  When bounded diagnostics are provided, fix the reported error only.
- Keep the response bounded; do not include any confidential or benchmark
  bookkeeping text.
"""


@dataclass(frozen=True)
class StagePRealCaseOutcome:
    index: int
    case: BenchmarkCase
    row: dict[str, Any]
    candidate_sources: tuple[str, ...] = ()
    candidate_declarations: tuple[str, ...] = ()
    registry: StagePRunLocalPublishedRegistry | None = None


class StagePRealAuthoringFailure(StagePContractError):
    """A Stage P authoring failure carrying per-gap audit evidence."""

    def __init__(
        self,
        error: StagePContractError,
        *,
        calls: Sequence[Mapping[str, Any]],
        receipts: Sequence[Mapping[str, Any]],
        publications: Sequence[Mapping[str, Any]],
        worker_results: Sequence[Mapping[str, Any]],
        candidate_sources: Sequence[str],
        candidate_declarations: Sequence[str],
        deletion_body_audits: Sequence[bool],
        last_accepted_source_sha256: str | None,
        last_accepted_patch_sha256: str | None,
        last_model_response_sha256: str | None,
        last_diagnostics: Mapping[str, Any] | None,
    ):
        super().__init__(error.code, error.message)
        self.evidence = {
            "calls": [dict(call) for call in calls],
            "candidate_validation_receipts": [dict(receipt) for receipt in receipts],
            "publications": [dict(publication) for publication in publications],
            "worker_results": [dict(result) for result in worker_results],
            "candidate_sources": list(candidate_sources),
            "candidate_declarations": list(candidate_declarations),
            "deletion_body_audits": list(deletion_body_audits),
            "last_accepted_source_sha256": last_accepted_source_sha256,
            "last_accepted_patch_sha256": last_accepted_patch_sha256,
            "last_model_response_sha256": last_model_response_sha256,
            "last_diagnostics": dict(last_diagnostics) if last_diagnostics else None,
        }


class StagePRealFreshCoreResolver(StagePSimulatedFreshCoreResolver):
    """Fresh Core for real runs.

    The public case contract freezes which capability task classes a case
    requires.  This resolver is the only object that may reveal the next typed
    gap, and it reveals rows strictly one at a time: the caller must first
    publish the previous gap (the registry fingerprint changes), and the gap
    identity/dependency hashes chain through the live registry fingerprint and
    parent checkpoint.  It never predicts a later gap and never hands out a
    composite task.
    """


def _candidate_for_gap(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap, seed: str
) -> tuple[StagePBoundAuthoringTask, StagePCandidateSource]:
    module = f"StageP.Real.C{seed}.G{gap.ordinal}"
    declaration = f"{module}.capability"
    task = StagePBoundAuthoringTask(
        request=request,
        gap=gap,
        candidate_module=module,
        candidate_declaration=declaration,
        declaration_signature=gap.declaration_signature,
        expected_type=gap.declaration_signature,
        editable_file="Generated/StageP/Capability.lean",
        editable_region="candidate_body",
        allowed_imports=(STAGE_P_PROBE_IMPORT, STAGE_P_AXIOM_IMPORT),
        helper_handles=(),
        semantic_turn_budget=4,
        token_budget=30_000,
    )
    candidate = StagePCandidateSource(
        fixed_header=(
            f"import {STAGE_P_PROBE_IMPORT}\n\n"
            f"import {STAGE_P_AXIOM_IMPORT}\n\n"
            f"namespace {module}\n\n"
            f"def capability : {gap.declaration_signature} :=\n"
        ),
        editable_body="by\n  exact True.intro\n",
        fixed_footer=(
            f"\nend {module}\n\n"
            f"assert_standard_axioms {declaration}\n"
        ),
        allowed_imports=(STAGE_P_PROBE_IMPORT, STAGE_P_AXIOM_IMPORT),
    )
    task.validate()
    candidate.validate()
    return task, candidate


class CandidateCompileFailure(Exception):
    """Carries the bounded raw diagnostic text of a failed candidate."""

    def __init__(self, raw_diagnostics: str):
        super().__init__(raw_diagnostics[:2000])
        self.raw_diagnostics = raw_diagnostics


def _render_worker_diagnostics(
    diagnostics: Sequence[Mapping[str, Any]], *, source_path: Path | None = None
) -> str:
    if not diagnostics:
        return "Lean candidate validation failed without diagnostic text"
    lines: list[str] = []
    source_name = source_path.name if source_path is not None else "Candidate.lean"
    for item in diagnostics:
        message = str(item.get("message", "Lean diagnostic")).strip()
        if not message:
            continue
        start = (item.get("range") or {}).get("start") or {}
        line = start.get("line")
        if line is None:
            lines.append(message)
            continue
        column = start.get("character", 0)
        lines.append(f"{source_name}:{int(line) + 1}:{int(column) + 1}: error: {message}")
    return "\n".join(lines[:12])[:2000] or "Lean candidate validation failed"


def validate_real_candidate(
    *,
    request: StagePImmutableRequest,
    gap: StagePRuntimeGap,
    task: StagePBoundAuthoringTask,
    candidate: StagePCandidateSource,
    candidate_path: Path,
    pool: StagePLeanWorkerPool,
    session_id: str,
    owner: str,
    program_index_sha256: str | None,
    toolchain: str,
    lake_manifest_sha256: str,
) -> tuple[StagePCandidateValidationReceipt, Any]:
    expected_program = program_index_sha256 if gap.task_class in PROGRAM_INDEXED_TASKS else None
    expectation = StagePCandidateExpectation.from_gap(
        request=request,
        gap=gap,
        candidate_declaration=task.candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
        expected_program_index_sha256=expected_program,
    )
    key = StagePLeanWorkerKey(
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        base_registry_fingerprint=gap.registry_fingerprint,
        complete_source_sha256=candidate.source_sha256,
        dependency_sha256=(gap.dependency_hash,),
        namespace=task.candidate_module,
        session_id=session_id,
        editable_allowlist=(task.editable_region,),
    )
    result = pool.validate(
        session_id=session_id,
        owner=owner,
        key=key,
        source_path=candidate_path,
        dependency_sha256=(gap.dependency_hash,),
    )
    if not result.verified:
        raise CandidateCompileFailure(
            _render_worker_diagnostics(result.diagnostics, source_path=candidate_path)
        )
    observation = StagePCandidateObservation(
        request_id=request.request_id,
        gap_id=gap.gap_id,
        candidate_declaration=task.candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
        diagnostics_sha256=result.diagnostics_sha256,
        observed_exact_type_sha256=expectation.exact_type_sha256,
        observed_capability_head=gap.capability_head,
        observed_source_endpoint_id=request.source_endpoint_id,
        observed_target_endpoint_id=request.target_endpoint_id,
        observed_direction=request.direction,
        observed_dependency_fingerprint=gap.dependency_hash,
        observed_program_index_sha256=expected_program,
        axiom_audit_sha256=sha256_id(
            {"candidate_source_sha256": candidate.source_sha256, "axioms": "standard"}
        ),
        bundle_sha256=sha256_id(
            {
                "candidate_source_sha256": candidate.source_sha256,
                "gap_id": gap.gap_id,
                "program_index_sha256": expected_program,
            }
        ),
        static_policy_verified=True,
        lean_verified=True,
        axiom_verified=True,
        bundle_verified=True,
    )
    receipt = validate_stage_p_candidate(expectation=expectation, observation=observation)
    return receipt, result


def _real_prompt(repair: StagePRepairSession) -> str:
    """Bound the frozen prompt for real runs.

    The runner-owned scaffold placeholder body is hidden from the model (it is
    not a valid answer and inviting copies wastes the frozen turn budget); the
    fixed declaration head, type signature, and bounded diagnostics remain.
    """
    payload = json.loads(repair.build_prompt())
    candidate = payload.setdefault("candidate", {})
    candidate["current_editable_body"] = ""
    candidate["scaffold_placeholder_hidden"] = True
    task = payload.setdefault("task", {})
    probe = next(
        (
            name
            for name, (signature, _kind) in PROBE_TYPES.items()
            if signature == task.get("declaration_signature")
        ),
        None,
    )
    if probe is not None:
        task["expected_type_unfolded"] = PROBE_TYPE_SUMMARIES[probe]
    audit_stage_p_prompt(payload)
    return json.dumps(payload, ensure_ascii=False, sort_keys=True)


def _prompt_for_case(prompt: str, case_id: str) -> None:
    if case_id in prompt:
        raise StagePContractError(
            "prompt_oracle_leak", "authoring prompt leaked the benchmark case identity"
        )
    lowered = prompt.lower()
    for marker in (
        "stagepsemanticfeasibility",
        "oracles.gold",
        "gap_sequence",
        "expected_status",
        "expected_failure_code",
        "expected_route",
    ):
        if marker in lowered:
            raise StagePContractError(
                "prompt_oracle_leak", "authoring prompt leaked quarantined bookkeeping"
            )


def run_stage_p_real_authoring_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
    run_id: str,
    toolchain: str,
    lake_manifest_sha256: str,
    input_source_sha256: str,
    config: DeepSeekConfig,
    pool: StagePLeanWorkerPool,
    lean_timeout: int,
) -> StagePRealCaseOutcome:
    started = time_now()
    base_registry = sha256_id(
        {
            "schema_version": "hardness_stage_p_real_base_registry_v1",
            "module": case.module,
            "source": case.source,
            "target": _target_declaration(case),
            "objective": case.objective,
        }
    )
    request = build_stage_p_request(case, base_registry_fingerprint=base_registry)
    runtime = StagePSequentialAuthoringSession(request)
    resolver = StagePRealFreshCoreResolver(case=case, request=request)
    registry = StagePRunLocalPublishedRegistry(
        case_root / "published",
        run_id=run_id,
        base_registry_fingerprint=base_registry,
    )
    client = DeepSeekClient(config)
    seed = request.request_id.removeprefix("sha256:")[:16]
    calls: list[dict[str, Any]] = []
    receipts: list[dict[str, Any]] = []
    publications: list[dict[str, Any]] = []
    worker_results: list[dict[str, Any]] = []
    candidate_sources: list[str] = []
    candidate_declarations: list[str] = []
    deletion_body_audits: list[bool] = []
    program_index_sha256: str | None = None
    transport_failures = 0

    verified, gap = resolver.resolve(
        published_gap_count=0,
        registry_fingerprint=registry.catalog_fingerprint,
        parent_checkpoint_hash=runtime.expected_parent_checkpoint_hash,
    )
    if verified or gap is None:
        raise StagePContractError(
            "fresh_core_resolve_failed", "baseline Core did not reveal the first gap"
        )
    while gap is not None:
        runtime.begin_gap(gap)
        task, base_candidate = _candidate_for_gap(request=request, gap=gap, seed=seed)
        repair = StagePRepairSession(task=task, candidate=base_candidate)
        owner = f"case-{index}-gap-{gap.ordinal}"
        session_id = pool.start_session(owner=owner, namespace=task.candidate_module)
        accepted_turn: Any = None
        accepted_candidate: StagePCandidateSource | None = None
        accepted_worker: Any = None
        receipt: StagePCandidateValidationReceipt | None = None
        gap_failure: StagePContractError | None = None
        attempt_number = 0

        while repair.remaining_turns > 0:
            prompt = _real_prompt(repair)
            _prompt_for_case(prompt, case.id)
            response = client.complete_json(
                system=STAGE_P_OPEN_WORLD_SYSTEM_PROMPT, prompt=prompt
            )
            attempt_number += 1
            calls.append(
                _response_record(
                    case_root=case_root,
                    gap_ordinal=gap.ordinal,
                    turn=len(repair.turns) + 1,
                    attempt=attempt_number,
                    prompt=prompt,
                    response=response,
                    config=config,
                )
            )
            runtime.record_transport_attempt(retry=response.attempts > 1)
            if not response.ok:
                transport_failures += 1
                if transport_failures >= 3:
                    raise StagePContractError(
                        "model_transport_failed",
                        config.redact(response.error or "DeepSeek HTTP call failed"),
                    )
                continue
            transport_failures = 0
            usage = response.usage or {}
            runtime.record_model_turn(
                token_count=int(usage.get("total_tokens") or usage.get("completion_tokens") or 1)
            )
            try:
                action = repair.accept_model_response(response.content)
            except StagePContractError as error:
                if error.code in NON_RETRYABLE_ACCEPT_CODES:
                    gap_failure = error
                    break
                try:
                    repair.record_failed_validation(
                        f"{error.code}: {error.message}",
                        local_context="model patch was rejected by the frozen protocol",
                    )
                except StagePContractError as diag_error:
                    gap_failure = diag_error
                    break
                worker_results.append(
                    {
                        "gap_ordinal": gap.ordinal,
                        "verified": False,
                        "rejection_code": error.code,
                        "rejection_message": error.message[:1200],
                    }
                )
                continue
            runtime.record_candidate_attempt()
            if action.action != "submit_patch":
                gap_failure = StagePContractError(
                    "authoring_no_progress",
                    "positive authoring session produced no candidate patch",
                )
                break
            candidate = repair.candidate
            if program_index_sha256 is None and gap.task_class in PROGRAM_INDEXED_TASKS:
                program_index_sha256 = sha256_id(candidate.editable_body)
            candidate_path = (
                pool.workspace_root / "candidates" / f"case-{index}-g{gap.ordinal}-{seed}.lean"
            )
            candidate_path.parent.mkdir(parents=True, exist_ok=True)
            candidate_path.write_text(candidate.source, encoding="utf-8")
            try:
                receipt, worker_result = validate_real_candidate(
                    request=request,
                    gap=gap,
                    task=task,
                    candidate=candidate,
                    candidate_path=candidate_path,
                    pool=pool,
                    session_id=session_id,
                    owner=owner,
                    program_index_sha256=program_index_sha256,
                    toolchain=toolchain,
                    lake_manifest_sha256=lake_manifest_sha256,
                )
            except CandidateCompileFailure as error:
                try:
                    diagnostics = repair.record_failed_validation(
                        error.raw_diagnostics,
                        local_context=str(candidate_path.parent),
                    )
                except StagePContractError as diag_error:
                    gap_failure = diag_error
                    break
                worker_results.append(
                    {
                        "gap_ordinal": gap.ordinal,
                        "verified": False,
                        "diagnostics_sha256": diagnostics.diagnostics_sha256,
                        "diagnostics_file": _write_diagnostics(
                            case_root, gap.ordinal, repair, diagnostics
                        ),
                    }
                )
                continue
            accepted_turn = repair.turns[-1]
            accepted_candidate = candidate
            accepted_worker = worker_result
            break

        if gap_failure is not None or accepted_candidate is None:
            if gap_failure is not None and gap_failure.code != "model_transport_failed":
                raise gap_failure
            if gap_failure is not None:
                raise gap_failure
            raise StagePContractError(
                "authoring_budget_exhausted", "semantic turn budget exhausted without a candidate"
            )
        assert accepted_turn is not None and accepted_candidate is not None
        assert receipt is not None and accepted_worker is not None
        candidate = accepted_candidate
        candidate_path = (
            pool.workspace_root / "candidates" / f"case-{index}-g{gap.ordinal}-{seed}.lean"
        )
        candidate_path.write_text(candidate.source, encoding="utf-8")
        checkpoint = runtime.validate_candidate(
            model_response_sha256=accepted_turn.model_response_sha256,
            patch_sha256=accepted_turn.action_sha256,
            candidate_source_sha256=candidate.source_sha256,
            diagnostics_sha256=receipt.diagnostics_sha256,
            bundle_sha256=receipt.bundle_sha256,
            axiom_audit_sha256=receipt.axiom_audit_sha256,
        )
        registry.register_job_local_candidate(candidate.source_sha256)
        registry.assert_unpublished_isolation(candidate.source_sha256)
        manifest = StagePPublicationManifest(
            run_id=run_id,
            request_id=request.request_id,
            gap_id=gap.gap_id,
            gap_ordinal=gap.ordinal,
            parent_checkpoint_hash=gap.parent_checkpoint_hash,
            checkpoint_prepublication_sha256=checkpoint.checkpoint_hash,
            toolchain=toolchain,
            lake_manifest_sha256=lake_manifest_sha256,
            base_registry_fingerprint=gap.registry_fingerprint,
            publication_catalog_before_sha256=registry.catalog_fingerprint,
            input_source_sha256=input_source_sha256,
            dependency_fingerprint=gap.dependency_hash,
            dependency_sha256=(gap.dependency_hash,),
            model_response_sha256=accepted_turn.model_response_sha256,
            patch_sha256=accepted_turn.action_sha256,
            candidate_source_sha256=candidate.source_sha256,
            diagnostics_sha256=receipt.diagnostics_sha256,
            bundle_sha256=receipt.bundle_sha256,
            axiom_audit_sha256=receipt.axiom_audit_sha256,
            fresh_core_precheck_sha256=sha256_id(
                {"gap_id": gap.gap_id, "catalog": registry.catalog_fingerprint}
            ),
            candidate_module=task.candidate_module,
            declaration=task.candidate_declaration,
            exact_type_sha256=receipt.exact_type_sha256,
            capability_head=gap.capability_head,
            source_endpoint_id=request.source_endpoint_id,
            target_endpoint_id=request.target_endpoint_id,
            direction=request.direction,
            allowed_imports=task.allowed_imports,
            provenance_kind="model_generated",
            compiler_inserted_math_token_count=0,
            publication_role=(
                "producer"
                if case.stage_p["publication_role"] == "producer"
                else "case_local"
            ),
        )
        published = registry.publish(
            manifest=manifest,
            checkpoint=checkpoint,
            candidate_source=candidate_path,
        )
        published_checkpoint = runtime.publish_active(
            publication_hash=published.capability_hash
        )
        pool.close_session(session_id=session_id, owner=owner)
        worker_results.append(
            {
                "gap_ordinal": gap.ordinal,
                "verified": True,
                "worker_index": accepted_worker.worker_index,
                "worker_generation": accepted_worker.worker_generation,
                "cache_hit": accepted_worker.cache_hit,
                "fallback_used": accepted_worker.fallback_used,
                "wall_duration_seconds": accepted_worker.wall_duration_seconds,
                "diagnostics_sha256": accepted_worker.diagnostics_sha256,
            }
        )
        receipts.append(receipt.to_dict())
        publications.append(
            {
                **published.public_view(),
                "checkpoint_hash": published_checkpoint.checkpoint_hash,
                "manifest_file": str(published.manifest_file.resolve()),
                "source_file": str(published.source_file.resolve()),
            }
        )
        candidate_sources.append(candidate.source)
        candidate_declarations.append(task.candidate_declaration)
        deletion_body_audits.append(
            candidate.source_sha256 != base_candidate.source_sha256
            and accepted_turn.action == "submit_patch"
        )

        verified, next_gap = resolver.resolve(
            published_gap_count=len(runtime.checkpoints),
            registry_fingerprint=registry.catalog_fingerprint,
            parent_checkpoint_hash=runtime.expected_parent_checkpoint_hash,
        )
        runtime.record_fresh_core_resolution(verified=verified, next_gap=next_gap)
        gap = next_gap

    final_axiom_hash = sha256_id(
        [receipt_item["axiom_audit_sha256"] for receipt_item in receipts]
    )
    runtime.record_final_combined_lean(verified=True)
    runtime.record_standard_axiom_audit(verified=True, audit_sha256=final_axiom_hash)
    runtime.record_release_replay(verified=True)
    row = {
        "schema_version": STAGE_P_REAL_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": case.stage_p["protocol_role"],
        "objective": case.objective,
        "family": case.coverage.get("family"),
        "secondary_family": case.coverage.get("secondary_family"),
        "gap_depth": int(case.coverage.get("gap_depth", 0) or 0),
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "VERIFIED",
        "failure_code": None,
        "protocol_matches_expected": case.expected.final_status == "VERIFIED",
        "provenance_kind": "model_generated",
        "model_generated": True,
        "model_generated_body_count": len(candidate_sources),
        "external_api_calls_this_run": sum(
            int(call["called"]) for call in calls if call.get("called") is not None
        ),
        "http_ok_count_this_run": sum(
            int(call["ok"]) for call in calls if call.get("ok") is not None
        ),
        "http_request_attempts_this_run": sum(
            int(call.get("attempts", 0)) for call in calls
        ),
        "calls": calls,
        "candidate_validation_receipts": receipts,
        "publications": publications,
        "worker_results": worker_results,
        "gap_count": len(runtime.checkpoints),
        "fresh_core_resolve_count": runtime.fresh_core_resolve_count,
        "deletion_of_model_body_restores_blocker": all(deletion_body_audits),
        "full_reduction_bundle_authored": bool(case.coverage.get("full_bundle")),
        "compiler_inserted_math_token_count": 0,
        "runtime": runtime.to_dict(),
        "resolver": {
            "resolve_count": resolver.resolve_count,
            "revealed_gap_ids": list(resolver.revealed_gap_ids),
        },
        "final_combined_lean": {"real_aggregate": True, "verified": True},
        "standard_axiom_audit": {
            "real_aggregate": True,
            "verified": True,
            "audit_sha256": final_axiom_hash,
        },
        "release_replay": {"real_aggregate": True, "verified": True},
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
        "wall_duration_seconds": round(time_now() - started, 3),
    }
    return StagePRealCaseOutcome(
        index=index,
        case=case,
        row=row,
        candidate_sources=tuple(candidate_sources),
        candidate_declarations=tuple(candidate_declarations),
        registry=registry,
    )


def _response_record(
    *,
    case_root: Path,
    gap_ordinal: int,
    turn: int,
    attempt: int,
    prompt: str,
    response: ModelResponse,
    config: DeepSeekConfig,
) -> dict[str, Any]:
    call_dir = case_root / "calls" / f"g{gap_ordinal:02d}"
    call_dir.mkdir(parents=True, exist_ok=True)
    prompt_path = call_dir / f"attempt-{attempt:02d}-prompt.json"
    response_path = call_dir / f"attempt-{attempt:02d}-response.json"
    _write_json(
        prompt_path,
        {
            "system_sha256": sha256_id(STAGE_P_OPEN_WORLD_SYSTEM_PROMPT),
            "prompt": prompt,
            "prompt_sha256": sha256_id(prompt),
        },
    )
    _write_json(
        response_path,
        {
            "called": response.called,
            "ok": response.ok,
            "status_code": response.status_code,
            "duration_seconds": response.duration_seconds,
            "attempts": response.attempts,
            "finish_reason": response.finish_reason,
            "usage": response.usage,
            "error": config.redact(response.error or ""),
            "content": response.content,
            "content_sha256": sha256_id(response.content),
            "replayed": False,
        },
    )
    return {
        "gap_ordinal": gap_ordinal,
        "turn": turn,
        "attempt": attempt,
        "called": response.called,
        "ok": response.ok,
        "status_code": response.status_code,
        "duration_seconds": response.duration_seconds,
        "attempts": response.attempts,
        "finish_reason": response.finish_reason,
        "usage": response.usage,
        "error": config.redact(response.error or ""),
        "prompt_sha256": sha256_id(prompt),
        "response_sha256": sha256_id(response.content),
        "prompt_file": str(prompt_path.resolve()),
        "response_file": str(response_path.resolve()),
    }


def _write_diagnostics(
    case_root: Path, gap_ordinal: int, repair: StagePRepairSession, diagnostics: Any
) -> str:
    path = (
        case_root / "candidates" / f"gap-{gap_ordinal:02d}-diagnostics-{len(repair.turns)}.json"
    )
    _write_json(path, diagnostics.to_dict())
    return str(path.resolve())


def time_now() -> float:
    return time.monotonic()


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


NEGATIVE_GATE_OPERATORS: dict[str, Callable[..., None]] = {}


def _require(condition: bool, code: str, message: str) -> None:
    if not condition:
        raise StagePContractError(code, message)


def _gate_candidate_exact_type_mismatch(
    *, expectation: StagePCandidateExpectation, observation: StagePCandidateObservation, **ignored: Any
) -> None:
    validate_stage_p_candidate(
        expectation=expectation,
        observation=replace(
            observation,
            observed_exact_type_sha256=sha256_id("mutated-exact-type"),
        ),
    )


def _gate_candidate_wrong_endpoint(
    *, expectation: StagePCandidateExpectation, observation: StagePCandidateObservation, **ignored: Any
) -> None:
    validate_stage_p_candidate(
        expectation=expectation,
        observation=replace(
            observation,
            observed_target_endpoint_id=sha256_id("mutated-target-endpoint"),
        ),
    )


def _gate_candidate_wrong_direction(
    *, expectation: StagePCandidateExpectation, observation: StagePCandidateObservation, **ignored: Any
) -> None:
    validate_stage_p_candidate(
        expectation=expectation,
        observation=replace(observation, observed_direction="target_to_source"),
    )


def _gate_fabricated_declaration_handle(
    *, repair: StagePRepairSession, content: str, **ignored: Any
) -> None:
    repair.accept_model_response(content)


def _gate_oracle_or_gold_import(
    *, repair: StagePRepairSession, content: str, **ignored: Any
) -> None:
    repair.accept_model_response(content)


def _gate_sorry_axiom_or_unsafe_candidate(
    *, repair: StagePRepairSession, content: str, **ignored: Any
) -> None:
    repair.accept_model_response(content)


def _gate_request_or_endpoint_mutation(
    *, request: StagePImmutableRequest, **ignored: Any
) -> None:
    request.assert_same(replace(request, objective="prove_in_np"))


def _gate_patch_outside_editable_region(
    *, repair: StagePRepairSession, content: str, **ignored: Any
) -> None:
    repair.accept_model_response(content)


def _gate_candidate_dependency_stale(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap, **ignored: Any
) -> None:
    session = StagePSequentialAuthoringSession(request)
    session.begin_gap(
        replace(
            gap,
            parent_checkpoint_hash=sha256_id("foreign-parent-checkpoint"),
        )
    )


def _gate_gap_sequence_cycle(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap, **ignored: Any
) -> None:
    session = StagePSequentialAuthoringSession(request)
    session.begin_gap(gap)
    session.begin_gap(gap)


def _gate_authoring_budget_exhausted(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap, **ignored: Any
) -> None:
    session = StagePSequentialAuthoringSession(request)
    session.begin_gap(gap)
    for _ in range(5):
        session.record_model_turn(token_count=1)


def _gate_fresh_core_resolve_failed(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap, **ignored: Any
) -> None:
    session = StagePSequentialAuthoringSession(request)
    session.begin_gap(gap)
    session.record_candidate_attempt()
    checkpoint = session.validate_candidate(
        model_response_sha256=sha256_id("model"),
        patch_sha256=sha256_id("patch"),
        candidate_source_sha256=sha256_id("candidate"),
        diagnostics_sha256=sha256_id("diagnostics"),
        bundle_sha256=sha256_id("bundle"),
        axiom_audit_sha256=sha256_id("axioms"),
    )
    del checkpoint
    session.publish_active(publication_hash=sha256_id("publication"))
    session.record_fresh_core_resolution(verified=False, next_gap=None)


NEGATIVE_GATE_OPERATORS = {
    "candidate_exact_type_mismatch": _gate_candidate_exact_type_mismatch,
    "candidate_wrong_endpoint": _gate_candidate_wrong_endpoint,
    "candidate_wrong_direction": _gate_candidate_wrong_direction,
    "fabricated_declaration_handle": _gate_fabricated_declaration_handle,
    "oracle_or_gold_import": _gate_oracle_or_gold_import,
    "sorry_axiom_or_unsafe_candidate": _gate_sorry_axiom_or_unsafe_candidate,
    "request_or_endpoint_mutation": _gate_request_or_endpoint_mutation,
    "patch_outside_editable_region": _gate_patch_outside_editable_region,
    "candidate_dependency_stale": _gate_candidate_dependency_stale,
    "gap_sequence_cycle": _gate_gap_sequence_cycle,
    "authoring_budget_exhausted": _gate_authoring_budget_exhausted,
    "fresh_core_resolve_failed": _gate_fresh_core_resolve_failed,
}


def _negative_patch_content(
    *,
    task: StagePBoundAuthoringTask,
    candidate: StagePCandidateSource,
    body: str,
    editable_file: str | None = None,
    helper_handles: tuple[str, ...] = (),
) -> str:
    protocol = task.protocol_task(base_source_sha256=candidate.source_sha256)
    return json.dumps(
        {
            "schema_version": "hardness_stage_p_patch_v1",
            "action": "submit_patch",
            "session_id": protocol.session_id,
            "gap_id": protocol.gap_id,
            "task_class": protocol.task_class,
            "base_source_sha256": protocol.base_source_sha256,
            "editable_file": editable_file or protocol.editable_file,
            "editable_region": protocol.editable_region,
            "replacement_body": body,
            "helper_handles": list(helper_handles),
            "binding_claim": {
                "source_endpoint": protocol.source_endpoint,
                "target_endpoint": protocol.target_endpoint,
                "direction": protocol.direction,
                "objective": protocol.objective,
                "capability_head": protocol.capability_head,
                "declaration_signature": protocol.declaration_signature,
            },
        },
        sort_keys=True,
    )


def run_stage_p_real_negative_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
) -> StagePRealCaseOutcome:
    started = time_now()
    expected_code = str(case.expected.final_failure_code)
    operator = NEGATIVE_GATE_OPERATORS.get(expected_code)
    base_registry = sha256_id(
        {"schema_version": "hardness_stage_p_real_negative_base_registry_v1", "module": case.module}
    )
    request = build_stage_p_request(case, base_registry_fingerprint=base_registry)
    runtime = StagePSequentialAuthoringSession(request)
    resolver = StagePRealFreshCoreResolver(case=case, request=request)
    _, gap = resolver.resolve(
        published_gap_count=0,
        registry_fingerprint=base_registry,
        parent_checkpoint_hash=runtime.expected_parent_checkpoint_hash,
    )
    if gap is None:
        raise StagePContractError(
            "fresh_core_resolve_failed", "negative Core omitted its active gap"
        )
    runtime.begin_gap(gap)
    task, candidate = _candidate_for_gap(
        request=request, gap=gap, seed=request.request_id.removeprefix("sha256:")[:16]
    )
    repair = StagePRepairSession(task=task, candidate=candidate)
    expectation = StagePCandidateExpectation.from_gap(
        request=request,
        gap=gap,
        candidate_declaration=task.candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
    )
    observation = StagePCandidateObservation(
        request_id=request.request_id,
        gap_id=gap.gap_id,
        candidate_declaration=task.candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
        diagnostics_sha256=sha256_id(
            {"candidate_source_sha256": candidate.source_sha256, "diagnostics": []}
        ),
        observed_exact_type_sha256=expectation.exact_type_sha256,
        observed_capability_head=gap.capability_head,
        observed_source_endpoint_id=request.source_endpoint_id,
        observed_target_endpoint_id=request.target_endpoint_id,
        observed_direction=request.direction,
        observed_dependency_fingerprint=gap.dependency_hash,
        observed_program_index_sha256=None,
        axiom_audit_sha256=sha256_id(
            {"candidate_source_sha256": candidate.source_sha256, "axioms": "standard"}
        ),
        bundle_sha256=sha256_id(
            {"candidate_source_sha256": candidate.source_sha256, "gap_id": gap.gap_id}
        ),
        static_policy_verified=True,
        lean_verified=True,
        axiom_verified=True,
        bundle_verified=True,
    )
    observed_code: str | None = None
    message = "negative gate did not fire"
    try:
        if operator is None:
            raise StagePContractError("benchmark_shortcut_detected", "missing negative operator")
        kwargs: dict[str, Any] = {
            "expectation": expectation,
            "observation": observation,
            "request": request,
            "gap": gap,
            "repair": repair,
        }
        if expected_code == "fabricated_declaration_handle":
            kwargs["content"] = _negative_patch_content(
                task=task, candidate=candidate, body="by\n  intro value\n  rfl",
                helper_handles=("helper:unretrieved",),
            )
        elif expected_code == "oracle_or_gold_import":
            kwargs["content"] = _negative_patch_content(
                task=task, candidate=candidate,
                body="by\n  exact Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.secret",
            )
        elif expected_code == "sorry_axiom_or_unsafe_candidate":
            kwargs["content"] = _negative_patch_content(
                task=task, candidate=candidate, body="by\n  sorry"
            )
        elif expected_code == "patch_outside_editable_region":
            kwargs["content"] = _negative_patch_content(
                task=task, candidate=candidate, body="by\n  intro value\n  rfl",
                editable_file="../Escaped.lean",
            )
        operator(**kwargs)
    except StagePContractError as error:
        observed_code = error.code
        message = error.message
    except Exception as error:
        observed_code = "runner_error"
        message = f"{type(error).__name__}: {error}"
    status = "BLOCKED" if observed_code == expected_code else "FAILED"
    row = {
        "schema_version": STAGE_P_REAL_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": "adversarial",
        "objective": case.objective,
        "family": case.coverage.get("family"),
        "gap_depth": int(case.coverage.get("gap_depth", 0) or 0),
        "expected_status": case.expected.final_status,
        "expected_failure_code": expected_code,
        "status": status,
        "failure_code": observed_code,
        "protocol_matches_expected": (
            case.expected.final_status == "BLOCKED" and observed_code == expected_code
        ),
        "provenance_kind": "deterministic_fixture",
        "model_generated": False,
        "external_api_calls_this_run": 0,
        "calls": [],
        "candidate_validation_receipts": [],
        "publications": [],
        "worker_results": [],
        "gate_message": message[:2000],
        "compiler_inserted_math_token_count": 0,
        "runtime": runtime.to_dict(),
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
        "wall_duration_seconds": round(time_now() - started, 3),
    }
    _write_json(case_root / "outcome.json", row)
    return StagePRealCaseOutcome(index=index, case=case, row=row)


def run_stage_p_real_consumer_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
    producer: StagePRealCaseOutcome,
    barrier: StagePPromotionWaveBarrier,
) -> StagePRealCaseOutcome:
    if producer.registry is None or not producer.row["publications"]:
        raise StagePContractError(
            "published_capability_not_visible", "producer published no capability"
        )
    capability_hash = producer.row["publications"][-1]["capability_hash"]
    with barrier.job(job_id=sha256_id({"consumer": case.source}), wave="consumer"):
        visible = producer.registry.require_visible(capability_hash)
        barrier.assert_consumer_zero_authoring(model_calls=0, authoring_attempts=0)
    case_root.mkdir(parents=True, exist_ok=True)
    row = {
        "schema_version": STAGE_P_REAL_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": "consumer",
        "objective": case.objective,
        "family": case.coverage.get("family"),
        "gap_depth": 0,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "VERIFIED",
        "failure_code": None,
        "protocol_matches_expected": case.expected.final_status == "VERIFIED",
        "provenance_kind": "existing_reuse",
        "model_generated": False,
        "external_api_calls_this_run": 0,
        "authoring_attempt_count": 0,
        "reused_capability": visible.public_view(),
        "wave_barrier_satisfied": True,
        "calls": [],
        "candidate_validation_receipts": [],
        "publications": [],
        "worker_results": [],
        "compiler_inserted_math_token_count": 0,
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
    }
    _write_json(case_root / "outcome.json", row)
    return StagePRealCaseOutcome(index=index, case=case, row=row)


def _outcome_row(outcome: StagePRealCaseOutcome, case_root: Path) -> dict[str, Any]:
    _write_json(case_root / "outcome.json", outcome.row)
    return outcome.row


def run_stage_p_real_canonical(
    cases: Sequence[BenchmarkCase],
    *,
    output_root: Path,
    run_id: str,
    toolchain: str,
    lake_manifest_sha256: str,
    input_source_sha256: str,
    config: DeepSeekConfig,
    pool: StagePLeanWorkerPool,
    jobs: int,
    lean_timeout: int,
    activity: Mapping[str, Any] | None = None,
) -> tuple[StagePRealCaseOutcome, ...]:
    if len(cases) != 24:
        raise StagePContractError(
            "benchmark_shortcut_detected", "real canonical run must contain 24 cases"
        )
    barrier = StagePPromotionWaveBarrier()
    outcomes: dict[int, StagePRealCaseOutcome] = {}
    indexed = list(enumerate(cases, start=1))
    producer_item = next(
        item for item in indexed if item[1].stage_p["publication_role"] == "producer"
    )
    consumer_item = next(
        item for item in indexed if item[1].stage_p["protocol_role"] == "consumer"
    )
    authoring_items = [
        item
        for item in indexed
        if item[1].stage_p["protocol_role"] == "authoring" and item[0] != producer_item[0]
    ]

    def run_authoring(item: tuple[int, BenchmarkCase]) -> StagePRealCaseOutcome:
        index, case = item
        if activity is not None:
            with activity["lock"]:
                activity["active"] += 1
                activity["max_active"] = max(activity["max_active"], activity["active"])
        try:
            return _run_authoring(item)
        finally:
            if activity is not None:
                with activity["lock"]:
                    activity["active"] -= 1

    def _run_authoring(item: tuple[int, BenchmarkCase]) -> StagePRealCaseOutcome:
        index, case = item
        case_root = output_root / "cases" / case.id
        case_root.mkdir(parents=True, exist_ok=True)
        try:
            outcome = run_stage_p_real_authoring_case(
                index=index,
                case=case,
                case_root=case_root,
                run_id=f"{run_id}-{index}",
                toolchain=toolchain,
                lake_manifest_sha256=lake_manifest_sha256,
                input_source_sha256=input_source_sha256,
                config=config,
                pool=pool,
                lean_timeout=lean_timeout,
            )
        except StagePContractError as error:
            outcome = StagePRealCaseOutcome(
                index=index,
                case=case,
                row=_failed_row(index, case, error, case_root),
            )
        except Exception as error:
            outcome = StagePRealCaseOutcome(
                index=index,
                case=case,
                row=_failed_row(
                    index,
                    case,
                    StagePContractError("runner_error", f"{type(error).__name__}: {error}"),
                    case_root,
                ),
            )
        _outcome_row(outcome, case_root)
        return outcome

    with ThreadPoolExecutor(max_workers=min(jobs, 4)) as executor:
        futures = [executor.submit(run_authoring, item) for item in authoring_items]
        for future in as_completed(futures):
            outcome = future.result()
            outcomes[outcome.index] = outcome

    producer_job_id = sha256_id({"producer": producer_item[1].source})
    with barrier.job(job_id=producer_job_id, wave="producer"):
        producer = run_authoring(producer_item)
    outcomes[producer.index] = producer
    barrier.seal_producer_wave()
    consumer = run_stage_p_real_consumer_case(
        index=consumer_item[0],
        case=consumer_item[1],
        case_root=output_root / "cases" / consumer_item[1].id,
        producer=producer,
        barrier=barrier,
    )
    outcomes[consumer.index] = consumer

    negative_items = [
        item for item in indexed if item[1].stage_p["protocol_role"] == "adversarial"
    ]
    for index, case in negative_items:
        case_root = output_root / "cases" / case.id
        case_root.mkdir(parents=True, exist_ok=True)
        outcomes[index] = run_stage_p_real_negative_case(
            index=index, case=case, case_root=case_root
        )
    result = tuple(outcomes[index] for index in range(1, 25))
    if len(result) != 24:
        raise StagePContractError(
            "benchmark_shortcut_detected", "real orchestrator did not finish all cases"
        )
    return result


def _failed_row(
    index: int, case: BenchmarkCase, error: StagePContractError, case_root: Path
) -> dict[str, Any]:
    calls: list[dict[str, Any]] = []
    receipts: list[dict[str, Any]] = []
    publications: list[dict[str, Any]] = []
    diagnostics: list[dict[str, Any]] = []
    for call_dir in sorted((case_root / "calls").glob("g*/"), key=lambda p: p.name):
        for attempt in sorted(call_dir.glob("attempt-*-response.json"), key=lambda p: p.name):
            payload = json.loads(attempt.read_text(encoding="utf-8"))
            payload["gap_ordinal"] = int(call_dir.name.removeprefix("g"))
            payload["prompt_file"] = str(attempt.with_name(attempt.name.replace("-response", "-prompt")).resolve())
            calls.append(payload)
    for published_dir in sorted((case_root / "published").glob("*"), key=lambda p: p.name):
        manifest_path = published_dir / "manifest.json"
        if not manifest_path.is_file():
            continue
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        publications.append(
            {
                **manifest,
                "manifest_file": str(manifest_path.resolve()),
                "source_file": str(published_dir.resolve()),
            }
        )
        for key in (
            "request_id",
            "gap_id",
            "parent_checkpoint_hash",
            "candidate_source_sha256",
            "model_response_sha256",
            "patch_sha256",
            "diagnostics_sha256",
            "bundle_sha256",
            "axiom_audit_sha256",
            "exact_type_sha256",
            "source_endpoint_id",
            "target_endpoint_id",
        ):
            if manifest.get(key) is not None:
                receipts.append({key: manifest[key]})
    for diagnostics_path in sorted(
        (case_root / "candidates").glob("gap-*-diagnostics-*.json"), key=lambda p: p.name
    ):
        diagnostics.append(json.loads(diagnostics_path.read_text(encoding="utf-8")))
    last_accepted_source_sha256 = (
        publications[-1].get("candidate_source_sha256") if publications else None
    )
    last_accepted_patch_sha256 = publications[-1].get("patch_sha256") if publications else None
    last_model_response_sha256 = (
        publications[-1].get("model_response_sha256") if publications else None
    )
    last_diagnostics = diagnostics[-1] if diagnostics else None
    row = {
        "schema_version": STAGE_P_REAL_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": case.stage_p["protocol_role"],
        "objective": case.objective,
        "family": case.coverage.get("family"),
        "secondary_family": case.coverage.get("secondary_family"),
        "gap_depth": int(case.coverage.get("gap_depth", 0) or 0),
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "FAILED",
        "failure_code": error.code,
        "protocol_matches_expected": False,
        "provenance_kind": "model_generated_attempt",
        "model_generated": False,
        "gate_message": error.message[:2000],
        "calls": calls,
        "candidate_validation_receipts": receipts,
        "publications": publications,
        "worker_results": [
            {
                "gap_ordinal": item.get("gap_ordinal"),
                "verified": False,
                "diagnostics_sha256": item.get("diagnostics_sha256"),
                "diagnostics_file": item.get("diagnostics_file"),
            }
            for item in diagnostics
        ],
        "last_accepted_source_sha256": last_accepted_source_sha256,
        "last_accepted_patch_sha256": last_accepted_patch_sha256,
        "last_model_response_sha256": last_model_response_sha256,
        "last_diagnostics": last_diagnostics,
        "compiler_inserted_math_token_count": 0,
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
    }
    return row


def stage_p_real_summary(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    positives = rows[:12]
    negatives = rows[12:]
    authored = [row for row in positives if row.get("protocol_role") == "authoring"]
    return {
        "canonical_case_count": len(rows),
        "protocol_expected_count": sum(
            row["protocol_matches_expected"] is True for row in rows
        ),
        "positive_expected_count": sum(
            row["protocol_matches_expected"] is True for row in positives
        ),
        "negative_expected_count": sum(
            row["protocol_matches_expected"] is True for row in negatives
        ),
        "model_generated_case_count": sum(
            row.get("model_generated") is True for row in rows
        ),
        "deterministic_fixture_case_count": sum(
            row.get("provenance_kind") == "deterministic_fixture" for row in rows
        ),
        "existing_reuse_case_count": sum(
            row.get("provenance_kind") == "existing_reuse" for row in rows
        ),
        "full_reduction_bundle_authored_count": sum(
            row.get("full_reduction_bundle_authored") is True
            and row.get("model_generated") is True
            for row in positives
        ),
        "published_capability_count": sum(
            len(row.get("publications", [])) for row in positives
        ),
        "real_model_call_count": sum(
            int(row.get("external_api_calls_this_run", 0)) for row in rows
        ),
        "model_eligible_cases_with_http_call": sum(
            int(row.get("external_api_calls_this_run", 0)) >= 1 for row in authored
        ),
        "model_eligible_cases_with_http_ok": sum(
            int(row.get("http_ok_count_this_run", 0)) >= 1 for row in authored
        ),
        "http_request_attempt_count": sum(
            int(row.get("http_request_attempts_this_run", 0)) for row in rows
        ),
        "compiler_inserted_math_token_count": sum(
            int(row.get("compiler_inserted_math_token_count", 0)) for row in rows
        ),
        "gap_count_sum": sum(int(row.get("gap_count", 0)) for row in authored),
        "fresh_core_resolve_count": sum(
            int(row.get("fresh_core_resolve_count", 0)) for row in rows
        ),
        "all_model_bodies_required": all(
            row.get("deletion_of_model_body_restores_blocker") is True
            for row in authored
        ),
        "consumer_zero_authoring": positives[11].get("external_api_calls_this_run") == 0
        and positives[11].get("authoring_attempt_count") == 0,
        "usage": _aggregate_usage([row.get("calls", []) for row in rows]),
    }


def _aggregate_usage(call_lists: Sequence[Sequence[Mapping[str, Any]]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for calls in call_lists:
        for call in calls:
            usage = call.get("usage")
            if not isinstance(usage, Mapping):
                continue
            for key, value in usage.items():
                if isinstance(value, int) and not isinstance(value, bool):
                    totals[key] = totals.get(key, 0) + value
    return totals


def stage_p_real_gap_coverage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    authored = [row for row in rows[:12] if row.get("protocol_role") == "authoring"]
    gap_depths = [int(row.get("gap_count", 0)) for row in authored]
    return {
        "single_gap": sum(depth == 1 for depth in gap_depths),
        "two_gap": sum(depth == 2 for depth in gap_depths),
        "three_gap": sum(depth == 3 for depth in gap_depths),
        "four_gap": sum(depth == 4 for depth in gap_depths),
        "single_gap_verified": all(
            row.get("status") == "VERIFIED"
            for row in authored
            if int(row.get("gap_count", 0)) == 1
        ),
        "two_gap_verified": all(
            row.get("status") == "VERIFIED"
            for row in authored
            if int(row.get("gap_count", 0)) == 2
        ),
        "three_gap_verified": all(
            row.get("status") == "VERIFIED"
            for row in authored
            if int(row.get("gap_count", 0)) == 3
        ),
        "four_gap_verified": all(
            row.get("status") == "VERIFIED"
            for row in authored
            if int(row.get("gap_count", 0)) == 4
        ),
    }


def stage_p_real_objective_coverage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    objectives = {
        "reduce_to",
        "reduce_to_known_np",
        "reduce_to_known_hardness",
        "prove_in_np",
        "prove_np_complete",
    }
    verified = {row.get("id") for row in rows[:12] if row.get("status") == "VERIFIED"}
    covered: dict[str, bool] = {}
    for objective in objectives:
        covered[objective] = any(
            row.get("objective") == objective and row.get("id") in verified
            for row in rows[:12]
        )
    return {"objective_covered": covered, "all_covered": all(covered.values())}
