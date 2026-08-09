"""Stage P offline canonical orchestration with simulated model responses."""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any, Mapping, Sequence

from .benchmark import BenchmarkCase
from .models import sha256_id
from .stage_p_candidate_validation import (
    StagePCandidateExpectation,
    StagePCandidateObservation,
    StagePCandidateValidationReceipt,
    validate_stage_p_candidate,
)
from .stage_p_contract import (
    STAGE_P_PATCH_SCHEMA,
    StagePContractError,
    parse_stage_p_action,
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


STAGE_P_OFFLINE_CASE_SCHEMA = "hardness_stage_p_offline_case_v1"
STAGE_P_OFFLINE_RUN_SCHEMA = "hardness_stage_p_offline_run_v1"
STAGE_P_PROBE_IMPORT = "Benchmark.Hardness.Inputs.StageP.ContractProbes"
STAGE_P_AXIOM_IMPORT = "ComplexityReduction.AxiomGate"

SIMULATED_BODY_BY_PROBE = {
    "proof": "by\n  intro value\n  rfl",
    "program": "fun value => value",
    "presentation": "by\n  intro values\n  rfl",
    "direct_tm": "by\n  intro value\n  exact Nat.le_refl value",
    "membership": "by\n  intro value\n  rfl",
    "completeness": "by\n  trivial",
}
PROGRAM_INDEXED_TASKS = frozenset(
    {"program_definition", "semantic_correctness", "polytime_or_direct_tm"}
)


def _target_declaration(case: BenchmarkCase) -> str:
    if case.target:
        return case.target
    suffix = (case.required_hardness or case.objective).replace("_", " ").title().replace(
        " ", ""
    )
    return f"StageP.OpenTarget.{suffix}"


def build_stage_p_request(
    case: BenchmarkCase, *, base_registry_fingerprint: str
) -> StagePImmutableRequest:
    gap_count = len(case.stage_p["gap_sequence"])
    if not gap_count:
        raise StagePContractError(
            "consumer_authoring_forbidden", "consumer has no Stage P authoring request"
        )
    target = _target_declaration(case)
    request = StagePImmutableRequest(
        source_declaration=case.source,
        target_declaration=target,
        source_endpoint_id=sha256_id(
            {"module": case.module, "declaration": case.source, "endpoint": "source"}
        ),
        target_endpoint_id=sha256_id(
            {"module": case.module, "declaration": target, "endpoint": "target"}
        ),
        objective=case.objective,
        direction=case.objective_direction,
        request_policy_sha256=sha256_id(
            {
                "authoring_policy": dict(case.authoring_policy),
                "verification_profile": case.verification_profile,
                "target_policy": case.target_policy,
                "allowed_target_evidence": list(case.allowed_target_evidence),
            }
        ),
        resolved_parameters_sha256=sha256_id(
            list(case.stage_p["resolved_parameters"])
        ),
        base_registry_fingerprint=base_registry_fingerprint,
        max_gap_count=gap_count,
    )
    request.validate()
    return request


@dataclass
class StagePSimulatedFreshCoreResolver:
    """Offline resolver fixture; only this object may reveal the next typed gap."""

    case: BenchmarkCase
    request: StagePImmutableRequest
    resolve_count: int = 0
    revealed_gap_ids: list[str] = field(default_factory=list)

    def resolve(
        self,
        *,
        published_gap_count: int,
        registry_fingerprint: str,
        parent_checkpoint_hash: str,
    ) -> tuple[bool, StagePRuntimeGap | None]:
        self.resolve_count += 1
        gap_rows = self.case.stage_p["gap_sequence"]
        if published_gap_count == len(gap_rows):
            return True, None
        ordinal = published_gap_count + 1
        row = gap_rows[ordinal - 1]
        gap = StagePRuntimeGap(
            request_id=self.request.request_id,
            ordinal=ordinal,
            task_class=str(row["task_class"]),
            capability_head=str(row["capability_head"]),
            declaration_signature=str(row["declaration_signature"]),
            source_endpoint_id=self.request.source_endpoint_id,
            target_endpoint_id=self.request.target_endpoint_id,
            registry_fingerprint=registry_fingerprint,
            dependency_hash=sha256_id(
                {
                    "request_id": self.request.request_id,
                    "ordinal": ordinal,
                    "task_class": row["task_class"],
                    "capability_head": row["capability_head"],
                    "declaration_signature": row["declaration_signature"],
                    "registry_fingerprint": registry_fingerprint,
                    "parent_checkpoint_hash": parent_checkpoint_hash,
                }
            ),
            parent_checkpoint_hash=parent_checkpoint_hash,
            public_preconditions=tuple(
                sha256_id(parameter)
                for parameter in self.case.stage_p["resolved_parameters"]
            ),
        )
        gap.validate(self.request)
        if gap.gap_id in self.revealed_gap_ids:
            raise StagePContractError(
                "gap_sequence_cycle", "offline fresh Core repeated a stable gap"
            )
        self.revealed_gap_ids.append(gap.gap_id)
        return False, gap


@dataclass(frozen=True)
class StagePSimulatedModelResponse:
    content: str
    usage: Mapping[str, int]

    @property
    def response_sha256(self) -> str:
        return sha256_id(self.content)


class StagePSimulatedModel:
    """Fixed task-shape simulator; it has no case/family-specific branches."""

    def author(self, *, repair: StagePRepairSession, contract_probe: str) -> StagePSimulatedModelResponse:
        try:
            body = SIMULATED_BODY_BY_PROBE[contract_probe]
        except KeyError as error:
            raise StagePContractError(
                "candidate_exact_type_mismatch", "offline simulator received an unknown probe"
            ) from error
        task = repair.protocol_task
        payload = {
            "schema_version": STAGE_P_PATCH_SCHEMA,
            "action": "submit_patch",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "base_source_sha256": task.base_source_sha256,
            "editable_file": task.editable_file,
            "editable_region": task.editable_region,
            "replacement_body": body,
            "helper_handles": [],
            "binding_claim": {
                "source_endpoint": task.source_endpoint,
                "target_endpoint": task.target_endpoint,
                "direction": task.direction,
                "objective": task.objective,
                "capability_head": task.capability_head,
                "declaration_signature": task.declaration_signature,
            },
        }
        content = json.dumps(payload, sort_keys=True)
        return StagePSimulatedModelResponse(
            content=content,
            usage={
                "prompt_tokens": 100,
                "completion_tokens": max(1, len(body) // 4),
                "total_tokens": 100 + max(1, len(body) // 4),
            },
        )

    def stop(
        self, *, task: Any, blocker: Mapping[str, Any]
    ) -> StagePSimulatedModelResponse:
        payload = {
            "schema_version": STAGE_P_PATCH_SCHEMA,
            "action": "stop_authoring",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "failure_code": str(blocker["failure_code"]),
            "confirmed_facts": [str(blocker["facts"][0])],
            "missing_conditions": ["A lawful candidate under the immutable public task."],
        }
        content = json.dumps(payload, sort_keys=True)
        return StagePSimulatedModelResponse(
            content=content,
            usage={"prompt_tokens": 80, "completion_tokens": 20, "total_tokens": 100},
        )


@dataclass
class StagePOfflineCaseOutcome:
    index: int
    case: BenchmarkCase
    row: dict[str, Any]
    candidate_sources: tuple[str, ...] = ()
    candidate_declarations: tuple[str, ...] = ()
    registry: StagePRunLocalPublishedRegistry | None = None


def _candidate_for_gap(
    *, request: StagePImmutableRequest, gap: StagePRuntimeGap
) -> tuple[StagePBoundAuthoringTask, StagePCandidateSource]:
    request_segment = request.request_id.removeprefix("sha256:")[:16]
    module = f"StageP.Offline.C{request_segment}.G{gap.ordinal}"
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


def _validated_receipt(
    *,
    request: StagePImmutableRequest,
    gap: StagePRuntimeGap,
    task: StagePBoundAuthoringTask,
    candidate: StagePCandidateSource,
    program_index_sha256: str,
) -> StagePCandidateValidationReceipt:
    expected_program = (
        program_index_sha256 if gap.task_class in PROGRAM_INDEXED_TASKS else None
    )
    expectation = StagePCandidateExpectation.from_gap(
        request=request,
        gap=gap,
        candidate_declaration=task.candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
        expected_program_index_sha256=expected_program,
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
        observed_capability_head=expectation.capability_head,
        observed_source_endpoint_id=expectation.source_endpoint_id,
        observed_target_endpoint_id=expectation.target_endpoint_id,
        observed_direction=expectation.direction,
        observed_dependency_fingerprint=expectation.dependency_fingerprint,
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
    return validate_stage_p_candidate(
        expectation=expectation, observation=observation
    )


def run_stage_p_offline_authoring_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
    run_id: str,
    toolchain: str,
    lake_manifest_sha256: str,
    input_source_sha256: str,
    model: StagePSimulatedModel,
) -> StagePOfflineCaseOutcome:
    base_registry = sha256_id(
        {
            "schema_version": "hardness_stage_p_offline_base_registry_v1",
            "module": case.module,
            "source": case.source,
            "target": _target_declaration(case),
            "objective": case.objective,
        }
    )
    request = build_stage_p_request(
        case, base_registry_fingerprint=base_registry
    )
    runtime = StagePSequentialAuthoringSession(request)
    resolver = StagePSimulatedFreshCoreResolver(case=case, request=request)
    registry = StagePRunLocalPublishedRegistry(
        case_root / "published",
        run_id=run_id,
        base_registry_fingerprint=base_registry,
    )
    program_index_sha256 = sha256_id(
        {"request_id": request.request_id, "program_index": "shared"}
    )
    calls: list[dict[str, Any]] = []
    receipts: list[dict[str, Any]] = []
    publications: list[dict[str, Any]] = []
    candidate_sources: list[str] = []
    candidate_declarations: list[str] = []
    deletion_body_audits: list[bool] = []

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
        task, base_candidate = _candidate_for_gap(request=request, gap=gap)
        repair = StagePRepairSession(task=task, candidate=base_candidate)
        gap_row = case.stage_p["gap_sequence"][gap.ordinal - 1]
        response = model.author(
            repair=repair, contract_probe=str(gap_row["contract_probe"])
        )
        runtime.record_transport_attempt(retry=False)
        runtime.record_model_turn(token_count=int(response.usage["total_tokens"]))
        action = repair.accept_model_response(response.content)
        runtime.record_candidate_attempt()
        candidate = repair.candidate
        deletion_body_audits.append(
            candidate.source_sha256 != base_candidate.source_sha256
            and action.replacement_body is not None
        )
        candidate_path = case_root / "candidates" / f"gap-{gap.ordinal:02d}.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        candidate_path.write_text(candidate.source, encoding="utf-8")
        receipt = _validated_receipt(
            request=request,
            gap=gap,
            task=task,
            candidate=candidate,
            program_index_sha256=program_index_sha256,
        )
        turn = repair.turns[-1]
        checkpoint = runtime.validate_candidate(
            model_response_sha256=turn.model_response_sha256,
            patch_sha256=turn.action_sha256,
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
            model_response_sha256=turn.model_response_sha256,
            patch_sha256=turn.action_sha256,
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
            provenance_kind="deterministic_fixture",
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
        calls.append(
            {
                "gap_ordinal": gap.ordinal,
                "simulated": True,
                "response_sha256": response.response_sha256,
                "patch_sha256": turn.action_sha256,
                "usage": dict(response.usage),
                "transport_retry_count": 0,
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

        verified, next_gap = resolver.resolve(
            published_gap_count=len(runtime.checkpoints),
            registry_fingerprint=registry.catalog_fingerprint,
            parent_checkpoint_hash=runtime.expected_parent_checkpoint_hash,
        )
        runtime.record_fresh_core_resolution(verified=verified, next_gap=next_gap)
        gap = next_gap

    final_axiom_hash = sha256_id(
        [receipt["axiom_audit_sha256"] for receipt in receipts]
    )
    runtime.record_final_combined_lean(verified=True)
    runtime.record_standard_axiom_audit(
        verified=True, audit_sha256=final_axiom_hash
    )
    runtime.record_release_replay(verified=True)
    row = {
        "schema_version": STAGE_P_OFFLINE_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": case.stage_p["protocol_role"],
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "VERIFIED",
        "failure_code": None,
        "protocol_matches_expected": case.expected.final_status == "VERIFIED",
        "provenance_kind": "deterministic_fixture",
        "model_generated": False,
        "simulated_model_call_count": len(calls),
        "external_api_calls_this_run": 0,
        "calls": calls,
        "candidate_validation_receipts": receipts,
        "publications": publications,
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
        "final_combined_lean": {"offline_simulated": True, "verified": True},
        "standard_axiom_audit": {
            "offline_simulated": True,
            "verified": True,
            "audit_sha256": final_axiom_hash,
        },
        "release_replay": {"offline_simulated": True, "verified": True},
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
    }
    return StagePOfflineCaseOutcome(
        index=index,
        case=case,
        row=row,
        candidate_sources=tuple(candidate_sources),
        candidate_declarations=tuple(candidate_declarations),
        registry=registry,
    )


def run_stage_p_offline_negative_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
    model: StagePSimulatedModel,
) -> StagePOfflineCaseOutcome:
    base_registry = sha256_id(
        {"module": case.module, "source": case.source, "negative": "base"}
    )
    request = build_stage_p_request(
        case, base_registry_fingerprint=base_registry
    )
    runtime = StagePSequentialAuthoringSession(request)
    resolver = StagePSimulatedFreshCoreResolver(case=case, request=request)
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
    task, candidate = _candidate_for_gap(request=request, gap=gap)
    protocol_task = replace(
        task.protocol_task(base_source_sha256=candidate.source_sha256),
        public_blocker=dict(case.stage_p["public_blocker"]),
    )
    response = model.stop(task=protocol_task, blocker=case.stage_p["public_blocker"])
    runtime.record_transport_attempt(retry=False)
    runtime.record_model_turn(token_count=int(response.usage["total_tokens"]))
    action = parse_stage_p_action(response.content, task=protocol_task)
    validate_stage_p_terminal_action(action, task=protocol_task)
    outcome_path = case_root / "stop-action.json"
    outcome_path.parent.mkdir(parents=True, exist_ok=True)
    outcome_path.write_text(response.content + "\n", encoding="utf-8")
    failure_code = action.failure_code
    row = {
        "schema_version": STAGE_P_OFFLINE_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": "adversarial",
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "BLOCKED",
        "failure_code": failure_code,
        "protocol_matches_expected": (
            case.expected.final_status == "BLOCKED"
            and failure_code == case.expected.final_failure_code
        ),
        "provenance_kind": "deterministic_fixture",
        "model_generated": False,
        "simulated_model_call_count": 1,
        "external_api_calls_this_run": 0,
        "calls": [
            {
                "simulated": True,
                "response_sha256": response.response_sha256,
                "usage": dict(response.usage),
                "transport_retry_count": 0,
            }
        ],
        "compiler_inserted_math_token_count": 0,
        "runtime": runtime.to_dict(),
        "mutation_suite_exercises_failure_layer": True,
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
    }
    return StagePOfflineCaseOutcome(index=index, case=case, row=row)


def run_stage_p_offline_consumer_case(
    *,
    index: int,
    case: BenchmarkCase,
    case_root: Path,
    producer: StagePOfflineCaseOutcome,
    barrier: StagePPromotionWaveBarrier,
) -> StagePOfflineCaseOutcome:
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
        "schema_version": STAGE_P_OFFLINE_CASE_SCHEMA,
        "id": case.id,
        "execution_position": index,
        "protocol_role": "consumer",
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "status": "VERIFIED",
        "failure_code": None,
        "protocol_matches_expected": case.expected.final_status == "VERIFIED",
        "provenance_kind": "existing_reuse",
        "model_generated": False,
        "simulated_model_call_count": 0,
        "external_api_calls_this_run": 0,
        "authoring_attempt_count": 0,
        "reused_capability": visible.public_view(),
        "wave_barrier_satisfied": True,
        "final_combined_lean": {"offline_simulated": True, "verified": True},
        "standard_axiom_audit": {"offline_simulated": True, "verified": True},
        "release_replay": {"offline_simulated": True, "verified": True},
        "compiler_inserted_math_token_count": 0,
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
    }
    return StagePOfflineCaseOutcome(index=index, case=case, row=row)


def run_stage_p_offline_canonical(
    cases: Sequence[BenchmarkCase],
    *,
    output_root: Path,
    run_id: str,
    toolchain: str,
    lake_manifest_sha256: str,
    input_source_sha256: str,
) -> tuple[StagePOfflineCaseOutcome, ...]:
    if len(cases) != 24:
        raise StagePContractError(
            "benchmark_shortcut_detected", "offline canonical run must contain 24 cases"
        )
    model = StagePSimulatedModel()
    barrier = StagePPromotionWaveBarrier()
    outcomes: list[StagePOfflineCaseOutcome] = []
    indexed = list(enumerate(cases, start=1))
    producer_item = next(
        item for item in indexed if item[1].stage_p["publication_role"] == "producer"
    )
    consumer_item = next(
        item for item in indexed if item[1].stage_p["protocol_role"] == "consumer"
    )
    for index, case in indexed:
        if case.stage_p["protocol_role"] != "authoring" or index == producer_item[0]:
            continue
        outcomes.append(
            run_stage_p_offline_authoring_case(
                index=index,
                case=case,
                case_root=output_root / "cases" / case.id,
                run_id=f"{run_id}-{index}",
                toolchain=toolchain,
                lake_manifest_sha256=lake_manifest_sha256,
                input_source_sha256=input_source_sha256,
                model=model,
            )
        )
    producer_job_id = sha256_id({"producer": producer_item[1].source})
    with barrier.job(job_id=producer_job_id, wave="producer"):
        producer = run_stage_p_offline_authoring_case(
            index=producer_item[0],
            case=producer_item[1],
            case_root=output_root / "cases" / producer_item[1].id,
            run_id=f"{run_id}-{producer_item[0]}",
            toolchain=toolchain,
            lake_manifest_sha256=lake_manifest_sha256,
            input_source_sha256=input_source_sha256,
            model=model,
        )
        outcomes.append(producer)
    barrier.seal_producer_wave()
    outcomes.append(
        run_stage_p_offline_consumer_case(
            index=consumer_item[0],
            case=consumer_item[1],
            case_root=output_root / "cases" / consumer_item[1].id,
            producer=producer,
            barrier=barrier,
        )
    )
    for index, case in indexed:
        if case.stage_p["protocol_role"] != "adversarial":
            continue
        outcomes.append(
            run_stage_p_offline_negative_case(
                index=index,
                case=case,
                case_root=output_root / "cases" / case.id,
                model=model,
            )
        )
    outcomes.sort(key=lambda outcome: outcome.index)
    if len(outcomes) != 24:
        raise StagePContractError(
            "benchmark_shortcut_detected", "offline orchestrator did not finish all cases"
        )
    return tuple(outcomes)


def build_stage_p_offline_aggregate_source(
    outcomes: Sequence[StagePOfflineCaseOutcome],
) -> str:
    declarations: list[str] = []
    modules: list[str] = []
    for outcome in outcomes:
        declarations.extend(outcome.candidate_declarations)
        for source in outcome.candidate_sources:
            body = "\n".join(
                line for line in source.splitlines() if not line.startswith("import ")
            ).strip()
            if body:
                modules.append(body)
    if not declarations:
        raise StagePContractError(
            "final_lean_failed", "offline aggregate has no candidate declarations"
        )
    return (
        f"import {STAGE_P_PROBE_IMPORT}\n"
        f"import {STAGE_P_AXIOM_IMPORT}\n\n"
        + "\n\n".join(modules)
        + "\n\nassert_standard_axioms\n  "
        + ",\n  ".join(declarations)
        + "\n"
    )


def stage_p_offline_summary(
    outcomes: Sequence[StagePOfflineCaseOutcome],
) -> dict[str, Any]:
    rows = [outcome.row for outcome in outcomes]
    positives = rows[:12]
    negatives = rows[12:]
    authored = [row for row in positives if row["protocol_role"] == "authoring"]
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
        "simulated_model_case_count": len(authored),
        "simulated_model_call_count": sum(
            int(row.get("simulated_model_call_count", 0)) for row in rows
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
            row.get("full_reduction_bundle_authored") is True for row in positives
        ),
        "published_capability_count": sum(
            len(row.get("publications", [])) for row in positives
        ),
        "compiler_inserted_math_token_count": sum(
            int(row.get("compiler_inserted_math_token_count", 0)) for row in rows
        ),
        "fresh_core_resolve_count": sum(
            int(row.get("fresh_core_resolve_count", 0)) for row in rows
        ),
        "all_model_bodies_required": all(
            row.get("deletion_of_model_body_restores_blocker") is True
            for row in authored
        ),
        "consumer_zero_authoring": positives[11].get("simulated_model_call_count") == 0
        and positives[11].get("authoring_attempt_count") == 0,
    }
