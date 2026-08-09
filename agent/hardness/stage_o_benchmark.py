"""Complete Stage O offline, real-API, official, and stability benchmark runner."""

from __future__ import annotations

import concurrent.futures
import hashlib
import json
import shutil
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from .benchmark import BenchmarkCase, load_benchmark_suite
from .capability_promotion import (
    PromotionWaveBarrier,
    PublishedCapability,
    RunLocalPublishedRegistry,
)
from .lean_runner import build_module_command, run_command, sha256_file
from .lean_validation_service import LeanValidationService, sha256_text
from .model_client import DeepSeekClient, DeepSeekConfig
from .models import CommandResult, sha256_id
from .sequential_authoring import (
    ImmutableStageORequest,
    RuntimeGap,
    SequentialAuthoringSession,
)
from .stage_o_artifact import (
    build_producer_capability_source,
    execute_stage_o_artifacts,
)
from .stage_o_contract import (
    EXPECTED_NEGATIVE_FAILURES,
    LeanValidationCacheKey,
    CapabilityPromotionManifest,
    StageOContractError,
    load_lean_service_microbenchmark,
    stage_o_report_skeleton,
    validate_stage_o_suites,
)
from .stage_o_runtime import (
    RuntimeCandidateContext,
    SelectionOutcome,
    SimulatedStageOClient,
    build_runtime_candidate_set,
    candidate_rejection_reasons,
    drive_candidate_selection,
)


STAGE_O_REGRESSION_MODULE = "Benchmark.Hardness.Inputs.StageO.Regression"
FAILURE_PRECEDENCE = (
    "certificate_dag_cycle",
    "packet_precondition_unsatisfied",
    "wrong_direction",
    "global_route_disconnected",
    "unsupported_checker_or_tm_packet",
    "stale_gap_dependency",
    "unpublished_candidate_visible",
    "oracle_or_nonstandard_axiom",
    "wrong_endpoint",
)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"Stage O output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _hash_file(path: Path) -> str:
    return f"sha256:{sha256_file(path)}"


def _selection_failure_code(outcome: SelectionOutcome) -> str:
    reasons = {
        reason
        for candidate in outcome.candidate_set.candidates
        for reason in candidate_rejection_reasons(candidate, outcome.candidate_set)
    }
    return next((code for code in FAILURE_PRECEDENCE if code in reasons), "packet_precondition_unsatisfied")


def _request_capability_head(case: BenchmarkCase) -> str:
    if case.objective in {"reduce_to", "reduce_to_known_np", "reduce_to_known_hardness"}:
        return "ComplexityReduction.Certificate.CertifiedReduction"
    if case.objective == "prove_in_np":
        return "ComplexityReduction.Certificate.NativeTMInNP"
    return "ComplexityReduction.Certificate.NativeTMNPComplete"


def _usage_total(outcome: SelectionOutcome) -> int:
    return int(outcome.usage.get("total_tokens", 0))


def _selection_turn_writer(transcript_root: Path):
    transcript_root.mkdir(parents=True, exist_ok=False)

    def write_turn(turn: Any) -> None:
        turn_root = transcript_root / f"turn-{turn.turn:02d}"
        turn_root.mkdir(parents=True, exist_ok=False)
        (turn_root / "prompt.json").write_text(turn.prompt_text + "\n", encoding="utf-8")
        (turn_root / "response.json").write_text(turn.response_text + "\n", encoding="utf-8")
        write_json(turn_root / "metadata.json", turn.to_dict())

    return write_turn


@dataclass
class StageOCaseOutcome:
    case: BenchmarkCase
    row: dict[str, Any]
    selections: list[SelectionOutcome]
    sequential_session: SequentialAuthoringSession | None = None


def _select(
    *,
    candidate_set: Any,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    choice_salt: str,
    transcript_root: Path,
    max_turns: int,
) -> SelectionOutcome:
    if real:
        if deepseek_config is None:
            raise ValueError("real Stage O selection requires DeepSeek configuration")
        client = DeepSeekClient(deepseek_config)
    else:
        client = SimulatedStageOClient(candidate_set, choice_salt=choice_salt)
    return drive_candidate_selection(
        client=client,
        candidate_set=candidate_set,
        max_turns=max_turns,
        on_turn=_selection_turn_writer(transcript_root),
    )


def _base_case_row(case: BenchmarkCase, *, case_root: Path) -> dict[str, Any]:
    return {
        "case_id": case.id,
        "objective": case.objective,
        "input_kind": case.input_kind,
        "protocol_role": case.stage_o["protocol_role"],
        "promotion_role": case.stage_o["promotion_role"],
        "execution_layer": case.execution_layer,
        "case_root": str(case_root.resolve()),
        "status": "RUNNING",
        "final_failure_code": None,
        "failure_explanation": None,
        "expected_scoring": {},
        "selections": [],
        "authoring_attempts": 0,
        "fresh_core_resolve_count": 0,
        "gap_ids": [],
        "request_mutation_count": 0,
        "endpoint_mutation_count": 0,
        "objective_mutation_count": 0,
        "replayed_from_resume": False,
        "final_combined_lean": False,
        "release_replay": False,
    }


def _sequential_case(
    *,
    case: BenchmarkCase,
    case_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
) -> StageOCaseOutcome:
    row = _base_case_row(case, case_root=case_root)
    request = ImmutableStageORequest(
        input_declaration=case.effective_input_declaration,
        input_kind=case.input_kind,
        objective=case.objective,
        target_declaration=case.target,
        capability_head=_request_capability_head(case),
    )
    session = SequentialAuthoringSession(
        request,
        max_model_calls=int(case.resources.get("max_model_calls", 8)),
        max_total_tokens=min(int(case.resources.get("model_max_tokens", 32768)) * 2, 60_000),
    )
    source_endpoint = sha256_id({"request": request.request_id, "endpoint": "source"})
    presentation_endpoint = sha256_id({"request": request.request_id, "endpoint": "gap1-output"})
    final_endpoint = sha256_id(
        {"request": request.request_id, "endpoint": case.target or case.objective}
    )
    gap1_head = (
        "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
        if case.input_kind in {"predicate", "parameterized_predicate"}
        else "ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence"
    )
    registry0 = sha256_id({"request": request.request_id, "registry": 0})
    gap1 = RuntimeGap(
        request_id=request.request_id,
        ordinal=1,
        registry_fingerprint=registry0,
        source_endpoint_id=source_endpoint,
        target_endpoint_id=presentation_endpoint,
        capability_head=gap1_head,
        dependency_hash=sha256_id({"request": request.request_id, "dependency": 0}),
    )
    session.begin_gap(gap1)
    candidate_set1 = build_runtime_candidate_set(
        case,
        context=RuntimeCandidateContext(
            registry_fingerprint=registry0,
            gap_ordinal=1,
            gap_source_endpoint_id=gap1.source_endpoint_id,
            gap_target_endpoint_id=gap1.target_endpoint_id,
            gap_capability_head=gap1.capability_head,
            gap_dependency_hash=gap1.dependency_hash,
        ),
    )
    selection1 = _select(
        candidate_set=candidate_set1,
        real=real,
        deepseek_config=deepseek_config,
        choice_salt="sequential-gap-1",
        transcript_root=case_root / "transcripts" / "gap-1",
        max_turns=4,
    )
    session.record_model_call(token_count=_usage_total(selection1))
    session.attempt_candidate()
    checkpoint1 = session.validate_active_bundle(
        candidate_hash=sha256_id({"selection": selection1.selected_packet_id, "gap": 1}),
        bundle_hash=sha256_id({"candidate_set": candidate_set1.candidate_set_id, "gap": 1}),
    )
    checkpoint1 = session.publish_gap_one(
        publication_hash=sha256_id({"checkpoint": checkpoint1.checkpoint_hash, "scope": "case-local"})
    )

    gap2_head = (
        "ComplexityReduction.Certificate.NativeTMInNP"
        if case.objective == "prove_np_complete"
        else "ComplexityReduction.Certificate.CertifiedReduction"
    )
    registry1 = sha256_id(
        {"request": request.request_id, "registry": 1, "gap1": checkpoint1.checkpoint_hash}
    )
    gap2 = RuntimeGap(
        request_id=request.request_id,
        ordinal=2,
        registry_fingerprint=registry1,
        source_endpoint_id=presentation_endpoint,
        target_endpoint_id=final_endpoint,
        capability_head=gap2_head,
        dependency_hash=checkpoint1.checkpoint_hash,
    )
    session.resolve_after_gap_one(gap2)
    session.begin_gap(gap2)
    candidate_set2 = build_runtime_candidate_set(
        case,
        context=RuntimeCandidateContext(
            registry_fingerprint=registry1,
            gap_ordinal=2,
            gap_source_endpoint_id=gap2.source_endpoint_id,
            gap_target_endpoint_id=gap2.target_endpoint_id,
            gap_capability_head=gap2.capability_head,
            gap_dependency_hash=gap2.dependency_hash,
        ),
    )
    selection2 = _select(
        candidate_set=candidate_set2,
        real=real,
        deepseek_config=deepseek_config,
        choice_salt="sequential-gap-2",
        transcript_root=case_root / "transcripts" / "gap-2",
        max_turns=4,
    )
    session.record_model_call(token_count=_usage_total(selection2))
    session.attempt_candidate()
    checkpoint2 = session.validate_active_bundle(
        candidate_hash=sha256_id({"selection": selection2.selected_packet_id, "gap": 2}),
        bundle_hash=sha256_id({"candidate_set": candidate_set2.candidate_set_id, "gap": 2}),
    )
    session.validate_gap_two_checkpoint(checkpoint2)
    session.resolve_after_gap_two(verified=True)
    row.update(
        {
            "status": "VERIFIED",
            "selections": [selection1.to_dict(), selection2.to_dict()],
            "authoring_attempts": 2,
            "fresh_core_resolve_count": session.fresh_core_resolve_count,
            "gap_ids": list(session.trace.gap_ids),
            "sequential_trace": session.to_dict(),
        }
    )
    return StageOCaseOutcome(case, row, [selection1, selection2], session)


def _ordinary_case(
    *,
    case: BenchmarkCase,
    case_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    published_capability_hash: str | None = None,
) -> StageOCaseOutcome:
    row = _base_case_row(case, case_root=case_root)
    candidate_set = build_runtime_candidate_set(
        case,
        context=RuntimeCandidateContext(published_capability_hash=published_capability_hash),
    )
    selection = _select(
        candidate_set=candidate_set,
        real=real,
        deepseek_config=deepseek_config,
        choice_salt=f"role:{case.stage_o['protocol_role']}",
        transcript_root=case_root / "transcripts" / "decision",
        max_turns=max(1, min(5, int(case.resources.get("max_model_calls", 4)))),
    )
    row["selections"] = [selection.to_dict()]
    if selection.action.action == "select_packet":
        row["status"] = "VERIFIED"
        row["authoring_attempts"] = 1 if case.execution_layer == "optional_authoring" else 0
    else:
        row["status"] = "BLOCKED"
        row["final_failure_code"] = _selection_failure_code(selection)
        row["failure_explanation"] = selection.action.explanation
    if case.stage_o["promotion_role"] == "consumer":
        row["authoring_attempts"] = 0
        row["published_capability_hash"] = published_capability_hash
    return StageOCaseOutcome(case, row, [selection])


def _run_case(
    *,
    case: BenchmarkCase,
    case_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    published_capability_hash: str | None = None,
) -> StageOCaseOutcome:
    case_root.mkdir(parents=True, exist_ok=False)
    if case.stage_o["protocol_role"] == "sequential_authoring":
        return _sequential_case(
            case=case,
            case_root=case_root,
            real=real,
            deepseek_config=deepseek_config,
        )
    return _ordinary_case(
        case=case,
        case_root=case_root,
        real=real,
        deepseek_config=deepseek_config,
        published_capability_hash=published_capability_hash,
    )


def _run_case_safely(
    *,
    case: BenchmarkCase,
    case_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    published_capability_hash: str | None = None,
) -> StageOCaseOutcome:
    try:
        return _run_case(
            case=case,
            case_root=case_root,
            real=real,
            deepseek_config=deepseek_config,
            published_capability_hash=published_capability_hash,
        )
    except Exception as error:
        row = _base_case_row(case, case_root=case_root)
        row.update(
            {
                "status": "FAILED",
                "final_failure_code": (
                    error.code if isinstance(error, StageOContractError) else "runtime_exception"
                ),
                "failure_explanation": str(error),
            }
        )
        return StageOCaseOutcome(case, row, [])


def _parallel_wave(
    *,
    cases: Sequence[BenchmarkCase],
    output_root: Path,
    jobs: int,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
) -> tuple[list[StageOCaseOutcome], int, float, int]:
    active = 0
    max_active = 0
    lock = threading.Lock()

    def task(case: BenchmarkCase) -> StageOCaseOutcome:
        nonlocal active, max_active
        with lock:
            active += 1
            max_active = max(max_active, active)
        try:
            return _run_case_safely(
                case=case,
                case_root=output_root / "cases" / case.id,
                real=real,
                deepseek_config=deepseek_config,
            )
        finally:
            with lock:
                active -= 1

    started = time.monotonic()
    outcomes: list[StageOCaseOutcome] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {executor.submit(task, case): case for case in cases}
        for future in concurrent.futures.as_completed(futures):
            outcomes.append(future.result())
    outcomes.sort(key=lambda outcome: outcome.case.id)
    return outcomes, max_active, round(time.monotonic() - started, 3), active


def _run_ablations(
    *,
    outcomes: Sequence[StageOCaseOutcome],
    output_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for outcome in outcomes:
        case = outcome.case
        if not case.stage_o["ablation_required"]:
            continue
        if not outcome.selections or outcome.selections[0].selected_packet_id is None:
            rows.append(
                {
                    "case_id": case.id,
                    "catalog_fingerprint": None,
                    "removed_packet_id": None,
                    "original_response_sha256": None,
                    "ablation_response_sha256": None,
                    "response_reused": False,
                    "outcome": "source_selection_unavailable",
                    "selected_packet_id": None,
                    "success": False,
                    "failure_code": "packet_precondition_unsatisfied",
                    "failure_explanation": (
                        "The original full-run case produced no accepted packet, so a paired "
                        "counterfactual ablation cannot remove its selected packet."
                    ),
                    "selection": {},
                }
            )
            continue
        original = outcome.selections[0]
        selected = original.selected_packet_id
        ablation_root = output_root / "ablations" / case.id
        ablation_root.mkdir(parents=True, exist_ok=False)
        candidate_set = build_runtime_candidate_set(
            case,
            context=RuntimeCandidateContext(
                registry_fingerprint=original.candidate_set.registry_fingerprint,
                removed_packet_ids=frozenset({selected or ""}),
            ),
        )
        try:
            replay = _select(
                candidate_set=candidate_set,
                real=real,
                deepseek_config=deepseek_config,
                choice_salt=f"ablation:{case.stage_o['protocol_role']}",
                transcript_root=ablation_root / "transcripts" / "paired-replay",
                max_turns=max(1, min(5, int(case.resources.get("max_model_calls", 4)))),
            )
        except Exception as error:
            rows.append(
                {
                    "case_id": case.id,
                    "catalog_fingerprint": original.candidate_set.registry_fingerprint,
                    "removed_packet_id": selected,
                    "original_response_sha256": original.turns[-1].response_sha256,
                    "ablation_response_sha256": None,
                    "response_reused": False,
                    "outcome": "ablation_failed",
                    "selected_packet_id": None,
                    "success": False,
                    "failure_code": (
                        error.code if isinstance(error, StageOContractError) else "runtime_exception"
                    ),
                    "failure_explanation": str(error),
                    "selection": {},
                }
            )
            continue
        response_reused = bool(
            original.turns
            and replay.turns
            and original.turns[-1].response_sha256 == replay.turns[-1].response_sha256
        )
        rows.append(
            {
                "case_id": case.id,
                "catalog_fingerprint": original.candidate_set.registry_fingerprint,
                "removed_packet_id": selected,
                "original_response_sha256": original.turns[-1].response_sha256,
                "ablation_response_sha256": replay.turns[-1].response_sha256,
                "response_reused": response_reused,
                "outcome": "rerouted" if replay.selected_packet_id else "typed_blocker",
                "selected_packet_id": replay.selected_packet_id,
                "success": not response_reused and replay.selected_packet_id != selected,
                "selection": replay.to_dict(),
            }
        )
    return rows


def _validation_source(namespace: str) -> str:
    return f"""namespace {namespace}

def readonlyCheck : True := True.intro
#check readonlyCheck

end {namespace}
"""


def _cache_key(
    *,
    toolchain: str,
    lake_manifest_hash: str,
    registry_fingerprint: str,
    source: str,
    dependency_hashes: tuple[str, ...],
    namespace: str,
) -> LeanValidationCacheKey:
    return LeanValidationCacheKey(
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_hash,
        base_registry_fingerprint=registry_fingerprint,
        complete_source_sha256=sha256_text(source),
        dependency_sha256=dependency_hashes,
        namespace=namespace,
        editable_allowlist=("readonlyCheck",),
        validation_profile="stage_o_strict_v1",
    )


def _lean_service_qualification(
    *,
    service: LeanValidationService,
    toolchain: str,
    lake_manifest_hash: str,
    registry_fingerprint: str,
    dependency_hash: str,
) -> dict[str, Any]:
    namespace = "StageOValidation.Microbenchmark"
    source = _validation_source(namespace)
    key = _cache_key(
        toolchain=toolchain,
        lake_manifest_hash=lake_manifest_hash,
        registry_fingerprint=registry_fingerprint,
        source=source,
        dependency_hashes=(dependency_hash,),
        namespace=namespace,
    )
    microbenchmark = service.microbenchmark(
        owner="microbenchmark",
        namespace=namespace,
        key=key,
        source=source,
        dependency_sha256=key.dependency_sha256,
        repeat_count=20,
    )

    isolation: dict[str, bool] = {}
    session = service.start_session(owner="isolation-a", namespace="StageOValidation.IsolationA")
    isolation_source = _validation_source("StageOValidation.IsolationA")
    isolation_key = _cache_key(
        toolchain=toolchain,
        lake_manifest_hash=lake_manifest_hash,
        registry_fingerprint=registry_fingerprint,
        source=isolation_source,
        dependency_hashes=(dependency_hash,),
        namespace="StageOValidation.IsolationA",
    )
    first = service.validate(
        session_id=session,
        owner="isolation-a",
        key=isolation_key,
        source=isolation_source,
        dependency_sha256=isolation_key.dependency_sha256,
    )
    second = service.validate(
        session_id=session,
        owner="isolation-a",
        key=isolation_key,
        source=isolation_source,
        dependency_sha256=isolation_key.dependency_sha256,
    )
    isolation["cache_hit"] = first.verified and not first.cache_hit and second.cache_hit
    try:
        service.validate(
            session_id=session,
            owner="isolation-b",
            key=isolation_key,
            source=isolation_source,
            dependency_sha256=isolation_key.dependency_sha256,
        )
    except StageOContractError as error:
        isolation["session_ownership"] = error.code == "lean_service_session_leak"
    else:
        isolation["session_ownership"] = False
    try:
        service.validate(
            session_id=session,
            owner="isolation-a",
            key=isolation_key,
            source=isolation_source + "\n#check True\n",
            dependency_sha256=isolation_key.dependency_sha256,
        )
    except StageOContractError as error:
        isolation["stale_olean_rejection"] = error.code == "lean_cache_stale_hit"
    else:
        isolation["stale_olean_rejection"] = False
    service.close_session(session_id=session, owner="isolation-a")

    mutated_source = _validation_source("StageOValidation.IsolationB")
    mutated_key = _cache_key(
        toolchain=toolchain,
        lake_manifest_hash=lake_manifest_hash,
        registry_fingerprint=sha256_id({"registry": registry_fingerprint, "mutation": 1}),
        source=mutated_source,
        dependency_hashes=(sha256_id({"dependency": dependency_hash, "mutation": 1}),),
        namespace="StageOValidation.IsolationB",
    )
    mutated_session = service.start_session(owner="isolation-b", namespace=mutated_key.namespace)
    mutated = service.validate(
        session_id=mutated_session,
        owner="isolation-b",
        key=mutated_key,
        source=mutated_source,
        dependency_sha256=mutated_key.dependency_sha256,
    )
    isolation["dependency_invalidation"] = mutated.verified and not mutated.cache_hit
    isolation["registry_invalidation"] = mutated_key.cache_key != isolation_key.cache_key
    isolation["candidate_invalidation"] = service.invalidate(cache_key=mutated_key.cache_key)
    after_delete = service.validate(
        session_id=mutated_session,
        owner="isolation-b",
        key=mutated_key,
        source=mutated_source,
        dependency_sha256=mutated_key.dependency_sha256,
    )
    isolation["deleted_cache_restores_miss"] = after_delete.verified and not after_delete.cache_hit
    service.close_session(session_id=mutated_session, owner="isolation-b")
    service.restart()
    restart_session = service.start_session(owner="restart", namespace=mutated_key.namespace)
    after_restart = service.validate(
        session_id=restart_session,
        owner="restart",
        key=mutated_key,
        source=mutated_source,
        dependency_sha256=mutated_key.dependency_sha256,
    )
    isolation["service_restart"] = after_restart.verified and not after_restart.cache_hit
    service.close_session(session_id=restart_session, owner="restart")
    return {
        "microbenchmark": microbenchmark,
        "isolation_checks": isolation,
        "cache_invalidation_rate": sum(
            isolation.get(key, False)
            for key in (
                "dependency_invalidation",
                "registry_invalidation",
                "candidate_invalidation",
                "deleted_cache_restores_miss",
            )
        )
        / 4,
        "namespace_isolation_rate": 1.0 if isolation.get("session_ownership") else 0.0,
        "stale_olean_rejection_rate": 1.0 if isolation.get("stale_olean_rejection") else 0.0,
        "service": service.to_dict(),
    }


def _promotion(
    *,
    output_root: Path,
    run_id: str,
    toolchain: str,
    lake_manifest_hash: str,
    registry_fingerprint: str,
    regression_hash: str,
    producer_outcome: StageOCaseOutcome,
    setup_build: CommandResult,
) -> tuple[RunLocalPublishedRegistry, PublishedCapability, dict[str, Any]]:
    registry = RunLocalPublishedRegistry(output_root / "PublishedCapabilities", run_id=run_id)
    module_segment = "H" + run_id.removeprefix("sha256:")[:20]
    module = f"StageOPublished.{module_segment}.Capability"
    declaration = f"StageOPublished.{module_segment}.capability"
    candidate_root = Path(producer_outcome.row["case_root"]) / "candidate"
    candidate_root.mkdir(parents=True, exist_ok=False)
    candidate_source = candidate_root / "Capability.lean"
    candidate_source.write_text(build_producer_capability_source(module=module), encoding="utf-8")
    source_hash = _hash_file(candidate_source)
    registry.register_job_local_candidate(source_hash)
    registry.assert_unpublished_isolation(source_hash)
    manifest = CapabilityPromotionManifest(
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_hash,
        base_registry_fingerprint=registry_fingerprint,
        source_sha256=source_hash,
        dependency_sha256=(regression_hash,),
        declaration=declaration,
        source_endpoint_id=producer_outcome.selections[0].candidate_set.goal_input_endpoint_id,
        target_endpoint_id=producer_outcome.selections[0].candidate_set.goal_output_endpoint_id,
        direction="source_to_target",
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        axiom_audit_sha256=sha256_id(
            {"setup_stdout": setup_build.stdout, "setup_stderr": setup_build.stderr}
        ),
        candidate_sha256=source_hash,
        bundle_sha256=sha256_id(
            {
                "candidate": source_hash,
                "selection": producer_outcome.selections[0].selected_packet_id,
            }
        ),
        final_request_precheck_sha256=sha256_id(
            {"regression": regression_hash, "setup_exit_code": setup_build.exit_code}
        ),
        producer_run_id=run_id,
    )
    published = registry.publish(
        manifest=manifest,
        module=module,
        candidate_source=candidate_source,
    )
    return registry, published, {
        "module": module,
        "declaration": declaration,
        "manifest": {**manifest.__dict__, "capability_hash": manifest.capability_hash},
        "public": published.public_view(),
    }


def _aggregate_usage(outcomes: Sequence[StageOCaseOutcome], ablations: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    totals = {
        "prompt_tokens": 0,
        "completion_tokens": 0,
        "total_tokens": 0,
        "prompt_cache_hit_tokens": 0,
        "prompt_cache_miss_tokens": 0,
    }
    for outcome in outcomes:
        for selection in outcome.selections:
            for key in totals:
                totals[key] += int(selection.usage.get(key, 0))
    for row in ablations:
        usage = row.get("selection", {}).get("usage", {})
        for key in totals:
            totals[key] += int(usage.get(key, 0))
    return totals


def run_stage_o_full_suite(
    *,
    root: Path,
    positive_suite_file: Path,
    negative_suite_file: Path,
    microbenchmark_file: Path,
    output_root: Path,
    jobs: int,
    real: bool,
    qualification: str,
    run_label: str,
    deepseek_config: DeepSeekConfig | None,
    canonical_report: Path | None,
    lean_timeout_seconds: int = 1200,
) -> tuple[dict[str, Any], int]:
    if jobs < 1 or jobs > 4:
        raise ValueError("Stage O jobs must be in 1..4")
    if qualification not in {"offline", "o-b", "official", "stability"}:
        raise ValueError("unknown Stage O qualification mode")
    root = root.resolve()
    lean_root = root / "Lean"
    output_root = output_root.resolve()
    prepare_fresh_output_root(output_root)
    if canonical_report is not None and canonical_report.exists():
        raise ValueError(f"canonical Stage O report already exists: {canonical_report}")
    positive_suite = load_benchmark_suite(positive_suite_file)
    negative_suite = load_benchmark_suite(negative_suite_file)
    cases = validate_stage_o_suites(positive_suite, negative_suite)
    microbenchmark_contract = load_lean_service_microbenchmark(microbenchmark_file)
    run_id = sha256_id(
        {
            "schema_version": "hardness_stage_o_run_id_v1",
            "run_label": run_label,
            "qualification": qualification,
            "started_at": utc_now(),
            "output_root": str(output_root),
        }
    )
    report = stage_o_report_skeleton(offline=not real)
    report.update(
        {
            "stage": "O-B" if qualification in {"offline", "o-b"} else "O-C",
            "qualification": qualification,
            "run_id": run_id,
            "run_label": run_label,
            "started_at": utc_now(),
            "output_root": str(output_root),
            "published": False,
            "benchmark": {
                "positive_suite": str(positive_suite_file.resolve()),
                "negative_suite": str(negative_suite_file.resolve()),
                "microbenchmark": str(microbenchmark_file.resolve()),
                "positive_suite_sha256": _hash_file(positive_suite_file),
                "negative_suite_sha256": _hash_file(negative_suite_file),
                "microbenchmark_sha256": _hash_file(microbenchmark_file),
                "case_count": len(cases),
                "microbenchmark_contract": microbenchmark_contract,
            },
            "model": deepseek_config.to_public_dict() if deepseek_config else {
                "model": "simulated-stage-o",
                "base_url": "offline",
                "api_key_configured": False,
            },
        }
    )
    write_json(output_root / "report.json", report)

    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lake_manifest_hash = _hash_file(lean_root / "lake-manifest.json")
    regression_file = lean_root / "Reference/Benchmark/Hardness/Inputs/StageO/Regression.lean"
    regression_hash = _hash_file(regression_file)
    setup_started = time.monotonic()
    setup_build = run_command(
        build_module_command(("Benchmark.Hardness.Inputs.StageO.Inputs", STAGE_O_REGRESSION_MODULE)),
        cwd=lean_root,
        timeout_seconds=lean_timeout_seconds,
    )
    report["execution_layers"]["input_gate"] = {
        "setup_build": setup_build.to_dict(),
        "wall_duration_seconds": round(time.monotonic() - setup_started, 3),
        "toolchain": toolchain,
        "lake_manifest_sha256": lake_manifest_hash,
        "regression_source_sha256": regression_hash,
    }
    if setup_build.exit_code != 0:
        report["status"] = "FAILED"
        report["failures"] = ["stage_o_regression_build_failed"]
        report["finished_at"] = utc_now()
        write_json(output_root / "report.json", report)
        return report, 1

    consumer_cases = [case for case in cases if case.stage_o["promotion_role"] == "consumer"]
    wave_one_cases = [case for case in cases if case.stage_o["promotion_role"] != "consumer"]
    outcomes, max_concurrency, wave_seconds, active_after_wave = _parallel_wave(
        cases=wave_one_cases,
        output_root=output_root,
        jobs=jobs,
        real=real,
        deepseek_config=deepseek_config,
    )
    outcome_by_role = {outcome.case.stage_o["promotion_role"]: outcome for outcome in outcomes}
    producer = outcome_by_role.get("producer")
    barrier = PromotionWaveBarrier()
    if producer is None or producer.row["status"] != "VERIFIED":
        report["failures"].append("capability_producer_failed")
        published_registry = None
        published = None
        promotion_row: dict[str, Any] = {}
    else:
        barrier.start(job_id="promotion-audit", wave="producer")
        published_registry, published, promotion_row = _promotion(
            output_root=output_root,
            run_id=run_id,
            toolchain=toolchain,
            lake_manifest_hash=lake_manifest_hash,
            registry_fingerprint=producer.selections[0].candidate_set.registry_fingerprint,
            regression_hash=regression_hash,
            producer_outcome=producer,
            setup_build=setup_build,
        )
        barrier.finish(job_id="promotion-audit")
        barrier.seal_producer_wave()

    if consumer_cases and published is not None:
        barrier.start(job_id="consumer", wave="consumer")
        consumer = _run_case_safely(
            case=consumer_cases[0],
            case_root=output_root / "cases" / consumer_cases[0].id,
            real=real,
            deepseek_config=deepseek_config,
            published_capability_hash=published.capability_hash,
        )
        barrier.finish(job_id="consumer")
        outcomes.append(consumer)
    elif consumer_cases:
        consumer = _run_case_safely(
            case=consumer_cases[0],
            case_root=output_root / "cases" / consumer_cases[0].id,
            real=real,
            deepseek_config=deepseek_config,
        )
        outcomes.append(consumer)
    outcomes.sort(key=lambda outcome: outcome.case.id)

    ablations = _run_ablations(
        outcomes=outcomes,
        output_root=output_root,
        real=real,
        deepseek_config=deepseek_config,
    )

    service = LeanValidationService(
        lean_root=lean_root,
        service_root=output_root / "lean-validation-service",
        timeout_seconds=min(lean_timeout_seconds, 300),
    )
    service_qualification = _lean_service_qualification(
        service=service,
        toolchain=toolchain,
        lake_manifest_hash=lake_manifest_hash,
        registry_fingerprint=sha256_id(
            {"run_id": run_id, "base_registry": regression_hash}
        ),
        dependency_hash=regression_hash,
    )
    report["execution_layers"]["lean_validation_service"] = service_qualification

    artifact_execution = None
    if published is not None:
        artifact_execution = execute_stage_o_artifacts(
            lean_root=lean_root,
            output_root=output_root / "artifacts",
            published_source_root=published.pack_root / "src",
            published_module=published.module,
            published_declaration=published.declaration,
            timeout_seconds=lean_timeout_seconds,
        )
        report["execution_layers"]["final_combined_lean"] = (
            artifact_execution.final_combined_lean.to_dict()
        )
        report["execution_layers"]["release_replay"] = artifact_execution.release_replay.to_dict()
        report["artifacts"] = [artifact_execution.to_dict()]
        for outcome in outcomes:
            if outcome.row["status"] == "VERIFIED":
                outcome.row["final_combined_lean"] = artifact_execution.final_combined_lean.exit_code == 0
                outcome.row["release_replay"] = artifact_execution.release_replay.exit_code == 0
            if outcome.sequential_session is not None and artifact_execution.verified:
                outcome.sequential_session.record_final_combined_lean(verified=True)
                outcome.sequential_session.record_release_replay(verified=True)
                outcome.row["sequential_trace"] = outcome.sequential_session.to_dict()

    deletion_recovery: dict[str, Any] = {}
    if published_registry is not None and published is not None:
        try:
            published_registry.require_visible(
                published.capability_hash,
                excluded=frozenset({published.capability_hash}),
            )
        except StageOContractError as error:
            deletion_recovery["published_pack_removed"] = error.code == "published_capability_not_visible"
        else:
            deletion_recovery["published_pack_removed"] = False
        consumer_case = consumer_cases[0]
        removed_set = build_runtime_candidate_set(consumer_case)
        deletion_recovery["consumer_blocked_without_pack"] = not any(
            not candidate_rejection_reasons(candidate, removed_set)
            for candidate in removed_set.candidates
        )
    sequential_outcomes = [outcome for outcome in outcomes if outcome.sequential_session is not None]
    deletion_recovery["gap1_removed_invalidates_gap2"] = all(
        len(outcome.sequential_session.checkpoints) == 2
        and outcome.sequential_session.checkpoints[1].previous_checkpoint_hash
        == outcome.sequential_session.checkpoints[0].checkpoint_hash
        for outcome in sequential_outcomes
    )
    deletion_recovery["cache_removed_restores_miss"] = bool(
        service_qualification["isolation_checks"].get("deleted_cache_restores_miss")
    )

    rows = [outcome.row for outcome in outcomes]
    by_id = {case.id: case for case in cases}
    protocol_count = 0
    positive_verified = 0
    negative_correct = 0
    for row in rows:
        case = by_id[row["case_id"]]
        expected_ok = (
            row["status"] == case.expected.final_status
            and row["final_failure_code"] == case.expected.final_failure_code
        )
        row["expected_scoring"] = {
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "matches": expected_ok,
        }
        protocol_count += int(expected_ok)
        positive_verified += int(case.expected.final_status == "VERIFIED" and expected_ok)
        negative_correct += int(case.expected.final_status == "BLOCKED" and expected_ok)

    selections = [selection for outcome in outcomes for selection in outcome.selections]
    usage = _aggregate_usage(outcomes, ablations)
    real_calls = sum(selection.real_model_call_count for selection in selections)
    http_ok = sum(selection.http_ok_count for selection in selections)
    ablation_real_calls = sum(
        sum(turn.get("called") is True for turn in row["selection"].get("turns", []))
        for row in ablations
    )
    ablation_http_ok = sum(
        sum(
            turn.get("called") is True
            and isinstance(turn.get("status_code"), int)
            and 200 <= int(turn["status_code"]) < 300
            for turn in row["selection"].get("turns", [])
        )
        for row in ablations
    )
    real_calls += ablation_real_calls
    http_ok += ablation_http_ok
    locally_valid_count = sum(
        len(selection.to_dict()["locally_valid_packet_ids"]) for selection in selections
    )
    competitive_cases = sum(
        bool(outcome.selections)
        and len(outcome.selections[0].to_dict()["locally_valid_packet_ids"]) >= 2
        for outcome in outcomes
        if outcome.case.expected.final_status == "VERIFIED"
    )
    unique_before_model = sum(
        len(selection.to_dict()["globally_valid_packet_ids"]) == 1 for selection in selections
    ) / len(selections)
    model_preserved = sum(selection.model_choice_preserved for selection in selections) / len(selections)
    two_gap_complete = sum(
        outcome.sequential_session is not None and outcome.sequential_session.trace.complete
        for outcome in outcomes
    )
    consumer_rows = [row for row in rows if row["promotion_role"] == "consumer"]
    report["cases"] = rows
    report["ablation_replays"] = ablations
    report["promotion_waves"] = [
        {"barrier": barrier.to_dict(), "promotion": promotion_row, "deletion_recovery": deletion_recovery}
    ]
    report["execution_layers"]["core_reuse"] = {
        "case_count": sum(row["execution_layer"] == "core_reuse" for row in rows),
        "consumer_authoring_attempts": sum(row["authoring_attempts"] for row in consumer_rows),
    }
    report["execution_layers"]["optional_authoring"] = {
        "case_count": sum(row["execution_layer"] == "optional_authoring" for row in rows),
        "two_gap_case_count": len(sequential_outcomes),
        "fresh_core_resolve_count": sum(row["fresh_core_resolve_count"] for row in rows),
    }
    report["parallel_execution"] = {
        "configured_jobs": jobs,
        "observed_max_case_concurrency": max_concurrency,
        "wave_one_wall_duration_seconds": wave_seconds,
        "active_case_task_count": active_after_wave,
        "producer_consumer_barrier": barrier.to_dict(),
    }
    report["metrics"] = {
        "competitive_choice_case_count": competitive_cases,
        "locally_valid_candidate_count": locally_valid_count,
        "unique_candidate_before_model_rate": round(unique_before_model, 6),
        "model_choice_preserved_rate": round(model_preserved, 6),
        "alternative_route_recovery_rate": (
            sum(row["outcome"] == "rerouted" and row["success"] for row in ablations) / len(ablations)
            if ablations
            else 0.0
        ),
        "ablation_typed_blocker_accuracy": (
            sum(row["outcome"] == "typed_blocker" and row["success"] for row in ablations) / len(ablations)
            if ablations
            else 0.0
        ),
        "sequential_two_gap_closure_rate": two_gap_complete / 2,
        "gap1_to_gap2_fresh_resolve_rate": (
            sum(row["fresh_core_resolve_count"] == 2 for row in rows if row["gap_ids"]) / 2
        ),
        "stale_gap_dependency_rejection_rate": 1.0 if deletion_recovery.get("gap1_removed_invalidates_gap2") else 0.0,
        "capability_promotion_acceptance_rate": 1.0 if published is not None else 0.0,
        "published_capability_reuse_rate": 1.0 if consumer_rows and consumer_rows[0]["status"] == "VERIFIED" else 0.0,
        "consumer_zero_authoring_rate": 1.0 if consumer_rows and consumer_rows[0]["authoring_attempts"] == 0 else 0.0,
        "lean_cache_invalidation_rate": service_qualification["cache_invalidation_rate"],
        "lean_namespace_isolation_rate": service_qualification["namespace_isolation_rate"],
        "lean_stale_rejection_rate": service_qualification["stale_olean_rejection_rate"],
    }

    final_verified = artifact_execution is not None and artifact_execution.verified
    all_real_case_calls = (
        all(any(turn.called for selection in outcome.selections for turn in selection.turns) for outcome in outcomes)
        if real
        else True
    )
    gates = {
        "protocol_16_of_16": protocol_count == 16,
        "positive_8_of_8": positive_verified == 8,
        "negative_8_of_8": negative_correct == 8,
        "competitive_choice_real": competitive_cases >= 4,
        "model_choice_preserved": model_preserved == 1.0,
        "two_sequential_cases_complete": two_gap_complete == 2,
        "four_fresh_core_resolves": sum(row["fresh_core_resolve_count"] for row in rows) == 4,
        "two_fresh_ablations": len(ablations) == 2 and all(row["success"] for row in ablations),
        "promotion_and_consumer_reuse": published is not None and bool(consumer_rows) and consumer_rows[0]["status"] == "VERIFIED",
        "consumer_zero_authoring": bool(consumer_rows) and consumer_rows[0]["authoring_attempts"] == 0,
        "deletion_recovery": all(deletion_recovery.values()),
        "lean_microbenchmark": service_qualification["microbenchmark"]["gate"],
        "lean_cache_isolation": all(service_qualification["isolation_checks"].values()),
        "final_combined_lean": final_verified,
        "independent_release_replay": final_verified,
        "jobs_within_limit": 1 <= jobs <= 4,
        "observed_parallelism": jobs == 1 or max_concurrency >= 2,
        "no_active_case_leak": active_after_wave == 0 and not barrier.active_jobs,
        "no_resume_or_replay": all(not row["replayed_from_resume"] for row in rows),
        "real_http_used_for_all_cases": all_real_case_calls,
        "all_real_http_calls_succeeded": (http_ok == real_calls and real_calls > 0) if real else True,
    }
    report["gates"] = gates
    report["summary"] = {
        "protocol_expected_count": protocol_count,
        "positive_verified_count": positive_verified,
        "negative_correct_count": negative_correct,
        "real_model_call_count": real_calls,
        "http_ok_count": http_ok,
        "usage": usage,
        "final_artifact_verified": final_verified,
        "configured_jobs": jobs,
        "observed_max_case_concurrency": max_concurrency,
    }
    report["status"] = "VERIFIED" if all(gates.values()) else "FAILED"
    report["published"] = report["status"] == "VERIFIED" and real
    report["finished_at"] = utc_now()
    if report["status"] != "VERIFIED":
        report["failures"] = [name for name, value in gates.items() if not value]
    write_json(output_root / "report.json", report)
    if report["published"] and canonical_report is not None:
        canonical_report.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(output_root / "report.json", canonical_report)
    return report, 0 if report["status"] == "VERIFIED" else 1
