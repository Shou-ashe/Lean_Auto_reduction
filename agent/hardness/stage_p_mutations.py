"""Executable deterministic mutation/adversarial qualification for Stage P."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Callable, Mapping

from .lean_worker_pool import StagePLeanWorkerKey, StagePLeanWorkerPool
from .models import sha256_id
from .stage_p_candidate_validation import validate_stage_p_candidate
from .stage_p_contract import StagePContractError
from .stage_p_fixture import StagePOfflineFixture, build_stage_p_offline_fixture
from .stage_p_runtime import StagePSequentialAuthoringSession


STAGE_P_MUTATION_RESULT_SCHEMA = "hardness_stage_p_mutation_result_v1"


@dataclass(frozen=True)
class StagePMutationResult:
    mutation_id: str
    parent_case: str
    mutation_operator: str
    seed: int
    expected_failure_code: str
    observed_failure_code: str | None
    passed: bool
    message: str
    schema_version: str = STAGE_P_MUTATION_RESULT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


class _MutationWorker:
    def __init__(self, *, generation: int, crash: bool = False):
        self.generation = generation
        self.crash = crash
        self.alive = False

    def start(self) -> None:
        self.alive = True

    def validate(
        self, *, source_path: Path, source: str, timeout_seconds: int
    ) -> list[dict[str, Any]]:
        del source_path, source, timeout_seconds
        if self.crash:
            raise RuntimeError("deterministic mutation worker crash")
        return []

    def is_alive(self) -> bool:
        return self.alive

    def close(self) -> None:
        self.alive = False


def _candidate_mutation(
    fixture: StagePOfflineFixture, **changes: object
) -> None:
    validate_stage_p_candidate(
        expectation=fixture.expectation,
        observation=replace(fixture.observation, **changes),
    )


def _repair(fixture: StagePOfflineFixture):
    return fixture.repair_session()


def _runtime(fixture: StagePOfflineFixture, **kwargs: object):
    session = StagePSequentialAuthoringSession(fixture.request, **kwargs)
    session.begin_gap(fixture.gap)
    return session


def _worker_pool(
    *, root: Path, fixture: StagePOfflineFixture, crash: bool = False
) -> tuple[StagePLeanWorkerPool, str, StagePLeanWorkerKey, Path]:
    workspace = root / "workspace"
    lean_root = workspace / "Lean"
    lean_root.mkdir(parents=True, exist_ok=False)
    source_path = workspace / "Generated" / "Candidate.lean"
    source_path.parent.mkdir(parents=True, exist_ok=False)
    source_path.write_text(fixture.candidate.source, encoding="utf-8")

    def factory(index: int, generation: int) -> _MutationWorker:
        del index
        return _MutationWorker(generation=generation, crash=crash)

    pool = StagePLeanWorkerPool(
        lean_root=lean_root,
        workspace_root=workspace,
        service_root=root / "worker-service",
        maximum_workers=1,
        timeout_seconds=5,
        worker_factory=factory,
    )
    session_id = pool.start_session(owner="mutation", namespace=fixture.namespace)
    key = StagePLeanWorkerKey(
        toolchain="leanprover/lean4:mutation",
        lake_manifest_sha256=sha256_id("mutation-lake-manifest"),
        base_registry_fingerprint=fixture.request.base_registry_fingerprint,
        complete_source_sha256=fixture.candidate.source_sha256,
        dependency_sha256=(fixture.gap.dependency_hash,),
        namespace=fixture.namespace,
        session_id=session_id,
        editable_allowlist=("candidate_body",),
    )
    return pool, session_id, key, source_path


def _audit_report_shortcuts(report: Mapping[str, Any]) -> None:
    if (
        report.get("resume_used") is not False
        or report.get("replay_used") is not False
        or report.get("old_response_used") is not False
        or report.get("canonical_case_count") != 24
    ):
        raise StagePContractError(
            "benchmark_shortcut_detected", "offline report used a forbidden shortcut"
        )


def _mutate_source_endpoint(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(
        fixture, observed_source_endpoint_id=sha256_id("mutated-source-endpoint")
    )


def _mutate_target_endpoint(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(
        fixture, observed_target_endpoint_id=sha256_id("mutated-target-endpoint")
    )


def _reverse_direction(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(fixture, observed_direction="target_to_source")


def _mutate_objective(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    fixture.request.assert_same(replace(fixture.request, objective="prove_in_np"))


def _mutate_signature(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(
        fixture, observed_exact_type_sha256=sha256_id("mutated-exact-type")
    )


def _mutate_head(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(
        fixture,
        observed_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
    )


def _mutate_base_hash(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(base_source_sha256=sha256_id("foreign-source"))
    )


def _escape_file(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(editable_file="../Escaped.lean")
    )


def _escape_region(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(editable_region="foreign_region")
    )


def _body_mutation(
    fixture: StagePOfflineFixture, root: Path, body: str
) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(replacement_body=body)
    )


def _fabricate_helper(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(helper_handles=("helper:unretrieved",))
    )


def _repeat_gap(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _runtime(fixture)
    session.begin_gap(fixture.gap)


def _append_fifth_gap(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    replace(fixture.gap, ordinal=5).validate(fixture.request)


def _mutate_parent(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = StagePSequentialAuthoringSession(fixture.request)
    session.begin_gap(
        replace(
            fixture.gap,
            parent_checkpoint_hash=sha256_id("foreign-parent-checkpoint"),
        )
    )


def _mutate_dependency(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(
        fixture,
        observed_dependency_fingerprint=sha256_id("mutated-dependency"),
    )


def _foreign_worker_session(fixture: StagePOfflineFixture, root: Path) -> None:
    pool, _, key, source_path = _worker_pool(root=root, fixture=fixture)
    try:
        pool.validate(
            session_id=sha256_id("foreign-session"),
            owner="mutation",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
        )
    finally:
        pool.close()


def _foreign_namespace(fixture: StagePOfflineFixture, root: Path) -> None:
    pool, session_id, key, source_path = _worker_pool(root=root, fixture=fixture)
    try:
        pool.validate(
            session_id=session_id,
            owner="mutation",
            key=replace(key, namespace="StageP.Offline.Foreign"),
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
        )
    finally:
        pool.close()


def _deleted_candidate_cache(fixture: StagePOfflineFixture, root: Path) -> None:
    pool, session_id, key, source_path = _worker_pool(root=root, fixture=fixture)
    try:
        pool.validate(
            session_id=session_id,
            owner="mutation",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
        )
        source_path.unlink()
        pool.validate(
            session_id=session_id,
            owner="mutation",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
        )
    finally:
        pool.close()


def _worker_crash(fixture: StagePOfflineFixture, root: Path) -> None:
    pool, session_id, key, source_path = _worker_pool(
        root=root, fixture=fixture, crash=True
    )
    try:
        pool.validate(
            session_id=session_id,
            owner="mutation",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
            allow_cold_fallback=False,
        )
    finally:
        pool.close()


def _transport_without_turn(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _runtime(fixture)
    session.record_transport_attempt(retry=True)
    if session.semantic_model_call_count == 0:
        raise StagePContractError(
            "authoring_no_progress", "transport retry produced no semantic candidate"
        )


def _repeat_diagnostics(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _repair(fixture)
    raw = "Candidate.lean:1:1: error: deterministic failure"
    session.record_failed_validation(raw)
    session.record_failed_validation(raw)


def _repeat_candidate(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _repair(fixture)
    first = "by\n  intro value\n  rfl"
    second = "by\n  intro value\n  simpa using Eq.refl value"
    session.accept_model_response(
        fixture.submit_patch_content(replacement_body=first)
    )
    session.accept_model_response(
        fixture.submit_patch_content(
            replacement_body=second,
            base_source_sha256=session.candidate.source_sha256,
        )
    )
    session.accept_model_response(
        fixture.submit_patch_content(
            replacement_body=first,
            base_source_sha256=session.candidate.source_sha256,
        )
    )


def _unchanged_patch(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _repair(fixture).accept_model_response(
        fixture.submit_patch_content(
            replacement_body=fixture.candidate.editable_body
        )
    )


def _exhaust_turns(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _runtime(fixture)
    for _ in range(5):
        session.record_model_turn(token_count=1)


def _exhaust_tokens(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    session = _runtime(fixture, max_total_tokens=1)
    session.record_model_turn(token_count=2)


def _report_mutation(field: str, value: object) -> Callable[[StagePOfflineFixture, Path], None]:
    def execute(fixture: StagePOfflineFixture, root: Path) -> None:
        del fixture, root
        report = {
            "resume_used": False,
            "replay_used": False,
            "old_response_used": False,
            "canonical_case_count": 24,
        }
        report[field] = value
        _audit_report_shortcuts(report)

    return execute


def _compiler_math(fixture: StagePOfflineFixture, root: Path) -> None:
    del root
    _candidate_mutation(fixture, compiler_inserted_math_token_count=1)


MutationOperation = Callable[[StagePOfflineFixture, Path], None]


OPERATIONS: dict[str, MutationOperation] = {
    "replace_source_endpoint_fingerprint": _mutate_source_endpoint,
    "replace_target_endpoint_fingerprint": _mutate_target_endpoint,
    "reverse_direction": _reverse_direction,
    "mutate_objective": _mutate_objective,
    "mutate_declaration_signature": _mutate_signature,
    "mutate_capability_head": _mutate_head,
    "mutate_base_source_hash": _mutate_base_hash,
    "escape_editable_file": _escape_file,
    "escape_editable_region": _escape_region,
    "insert_unallowlisted_import": lambda fixture, root: _body_mutation(
        fixture, root, "by\n  import StageP.Escaped"
    ),
    "insert_oracle_reference": lambda fixture, root: _body_mutation(
        fixture, root, "by\n  exact StageP.Gold.hidden"
    ),
    "insert_sorry": lambda fixture, root: _body_mutation(fixture, root, "by\n  sorry"),
    "insert_axiom": lambda fixture, root: _body_mutation(
        fixture, root, "by\n  exact axiom"
    ),
    "insert_unsafe": lambda fixture, root: _body_mutation(
        fixture, root, "by\n  exact unsafe"
    ),
    "fabricate_helper_handle": _fabricate_helper,
    "repeat_stable_gap_id": _repeat_gap,
    "append_fifth_gap": _append_fifth_gap,
    "mutate_parent_checkpoint": _mutate_parent,
    "mutate_dependency_hash": _mutate_dependency,
    "reuse_foreign_worker_session": _foreign_worker_session,
    "reuse_foreign_namespace": _foreign_namespace,
    "accept_deleted_candidate_cache": _deleted_candidate_cache,
    "simulate_worker_crash": _worker_crash,
    "transport_timeout_without_semantic_turn": _transport_without_turn,
    "repeat_diagnostics_hash": _repeat_diagnostics,
    "repeat_candidate_hash": _repeat_candidate,
    "submit_unchanged_patch": _unchanged_patch,
    "exhaust_semantic_turn_budget": _exhaust_turns,
    "exhaust_token_budget": _exhaust_tokens,
    "set_resume_used": _report_mutation("resume_used", True),
    "set_replay_used": _report_mutation("replay_used", True),
    "mutate_report_case_count": _report_mutation("canonical_case_count", 23),
    "inject_compiler_math_tokens": _compiler_math,
}


def execute_stage_p_mutation(
    row: Mapping[str, Any], *, workspace_root: Path
) -> StagePMutationResult:
    mutation_id = str(row["mutation_id"])
    operator = str(row["mutation_operator"])
    expected = str(row["expected_failure_code"])
    seed = int(row["seed"])
    root = workspace_root / mutation_id
    root.mkdir(parents=True, exist_ok=False)
    fixture = build_stage_p_offline_fixture(seed)
    operation = OPERATIONS.get(operator)
    if operation is None:
        return StagePMutationResult(
            mutation_id=mutation_id,
            parent_case=str(row["parent_case"]),
            mutation_operator=operator,
            seed=seed,
            expected_failure_code=expected,
            observed_failure_code=None,
            passed=False,
            message="mutation operator is not implemented",
        )
    observed: str | None = None
    message = "mutation unexpectedly passed"
    try:
        operation(fixture, root)
    except StagePContractError as error:
        observed = error.code
        message = error.message
    except Exception as error:
        observed = "runner_error"
        message = f"{type(error).__name__}: {error}"
    return StagePMutationResult(
        mutation_id=mutation_id,
        parent_case=str(row["parent_case"]),
        mutation_operator=operator,
        seed=seed,
        expected_failure_code=expected,
        observed_failure_code=observed,
        passed=observed == expected,
        message=message,
    )


def run_stage_p_mutation_suite(
    rows: tuple[dict[str, Any], ...], *, workspace_root: Path
) -> tuple[StagePMutationResult, ...]:
    workspace_root.mkdir(parents=True, exist_ok=False)
    return tuple(
        execute_stage_p_mutation(row, workspace_root=workspace_root) for row in rows
    )
