"""Versioned production orchestrator for exact native NP-hardness.

The V2 entrypoint owns the complete job state machine.  Existing reductions are
still resolved by the deterministic V1 kernel-facing implementation, but every
model-authored reduction is executed by the sequential V2 capability runtime.
Benchmark runners may provide a deterministic planner product during H-A; they
may not invoke the gap runtime directly.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Mapping

from .lean_runner import (
    module_file,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .model_client import DeepSeekClient, DeepSeekConfig
from .models import sha256_id
from .np_hard import (
    NP_HARD_DIRECTION,
    NP_HARD_OBJECTIVE,
    NP_HARD_RESULT_SCHEMA_V1,
    NPHardAgentConfigV1,
    NPHardAgentV1,
)
from .np_hard_authoring import NPHardAuthoringTaskV2
from .np_hard_authoring_planner import (
    NPHardAuthoringPlanV2,
    NPHardAuthoringPlannerError,
    NPHardAuthoringPlannerV2,
)
from .np_hard_gap_runtime import NPHardGapRuntimeV1, NPHardNodeModelClient
from .np_hard_input import NPHardInputReferenceV1, resolve_np_hard_input_reference
from .np_hard_production import (
    NPHardProductionPreflightV1,
    is_formal_np_hard_qualification_config,
    public_node_reasoning_policy,
    required_model_call_budget,
)
from .np_hard_scope_policy import (
    NPHardScopePolicyError,
    NPHardScopePolicyEntryV1,
    POLICY_DISPOSITION_AUXILIARY,
    POLICY_DISPOSITION_ENCODING_COMPLEXITY_FRONTIER,
    scope_policy_entry_for_input_reference,
)
from .state import JobStore, compute_job_id


NP_HARD_PROOF_REQUEST_SCHEMA_V2 = "hardness_np_hard_proof_request_v2"
NP_HARD_PROOF_RESULT_SCHEMA_V2 = "hardness_np_hard_proof_result_v2"
NP_HARD_PROOF_RESULT_STATUSES_V2 = {"VERIFIED", "BLOCKED", "FAILED"}
NP_HARD_MODEL_POLICIES_V2 = {"disabled", "model-auto", "model-required"}
NP_HARD_MAX_MODEL_CALL_BUDGET_V2 = 66
NP_HARD_AUTHORABLE_DETERMINISTIC_BLOCKERS_V2 = frozenset(
    {"no_forward_path_from_hardness_seed", "wrong_direction_only"}
)


class NPHardOrchestratorError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardOrchestratorError(code, message)


def _deterministic_outcome_allows_authoring(
    *,
    status: str,
    failure_code: str,
    authoring_policy: str,
    qualification_force_authoring: bool,
) -> bool:
    """Admit only deterministic route blockers that a forward author can repair."""

    if authoring_policy not in {"model-auto", "model-required"}:
        return False
    if qualification_force_authoring:
        return True
    return (
        status == "BLOCKED"
        and failure_code in NP_HARD_AUTHORABLE_DETERMINISTIC_BLOCKERS_V2
    )


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        _fail(
            "invalid_np_hard_proof_v2_schema",
            f"{label} keys drifted; missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}",
        )


def _require_sha256(value: str, *, label: str) -> None:
    if not (
        isinstance(value, str)
        and value.startswith("sha256:")
        and len(value) == 71
        and all(character in "0123456789abcdef" for character in value[7:])
    ):
        _fail("invalid_np_hard_proof_v2_schema", f"{label} is not a tagged SHA-256")


def _public_model_configuration(config: DeepSeekConfig | None) -> dict[str, Any] | None:
    if config is None:
        return None
    value = config.to_public_dict()
    value["node_reasoning_policy"] = public_node_reasoning_policy()
    return value


@dataclass(frozen=True)
class NPHardProofRequestV2:
    request_id: str
    requested_term: str
    input_module: str
    problem_declaration: str
    input_sha256: str
    toolchain: str
    lake_manifest_sha256: str
    authoring_policy: str
    qualification_force_authoring: bool
    attempt_budget: int
    call_budget: int
    model_configuration: Mapping[str, Any] | None
    candidate_validation_mode: str
    authoring_task: NPHardAuthoringTaskV2 | None
    final_program_declaration: str | None
    objective: str = NP_HARD_OBJECTIVE
    direction: str = NP_HARD_DIRECTION
    planner: str = "deterministic"
    schema_version: str = NP_HARD_PROOF_REQUEST_SCHEMA_V2

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "requested_term": self.requested_term,
            "input_module": self.input_module,
            "problem_declaration": self.problem_declaration,
            "input_sha256": self.input_sha256,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "objective": self.objective,
            "direction": self.direction,
            "planner": self.planner,
            "authoring_policy": self.authoring_policy,
            "qualification_force_authoring": self.qualification_force_authoring,
            "attempt_budget": self.attempt_budget,
            "call_budget": self.call_budget,
            "model_configuration": (
                dict(self.model_configuration)
                if self.model_configuration is not None
                else None
            ),
            "candidate_validation_mode": self.candidate_validation_mode,
            "authoring_task": (
                self.authoring_task.to_dict() if self.authoring_task is not None else None
            ),
            "final_program_declaration": self.final_program_declaration,
        }

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content())

    def validate(self) -> None:
        if self.schema_version != NP_HARD_PROOF_REQUEST_SCHEMA_V2:
            _fail("invalid_np_hard_proof_v2_schema", "unsupported proof request schema")
        _require_sha256(self.request_id, label="request_id")
        try:
            validate_module_name(self.input_module)
            validate_declaration_name(
                self.problem_declaration, label="NP-hard V2 target problem"
            )
        except ValueError as error:
            _fail("invalid_np_hard_proof_v2_schema", str(error))
        if self.objective != NP_HARD_OBJECTIVE or self.direction != NP_HARD_DIRECTION:
            _fail("candidate_wrong_direction", "the V2 objective or direction changed")
        if self.planner != "deterministic":
            _fail("invalid_np_hard_proof_v2_schema", "V2 requires deterministic planning")
        if self.authoring_policy not in NP_HARD_MODEL_POLICIES_V2:
            _fail("invalid_np_hard_proof_v2_schema", "unknown V2 authoring policy")
        if not isinstance(self.qualification_force_authoring, bool):
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "qualification_force_authoring must be boolean",
            )
        if self.qualification_force_authoring and self.authoring_policy != "model-required":
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "forced qualification authoring requires model-required policy",
            )
        if (
            not 1 <= self.attempt_budget <= 4
            or not 0 <= self.call_budget <= NP_HARD_MAX_MODEL_CALL_BUDGET_V2
        ):
            _fail("authoring_gap_budget_exhausted", "V2 model budget is outside policy")
        if self.candidate_validation_mode != "persistent-worker":
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "V2 production authoring requires the persistent worker",
            )
        _require_sha256(self.input_sha256, label="input_sha256")
        _require_sha256(self.lake_manifest_sha256, label="lake_manifest_sha256")
        if not self.toolchain.strip():
            _fail("invalid_np_hard_proof_v2_schema", "Lean toolchain is empty")
        if self.authoring_task is None:
            if self.final_program_declaration is not None:
                _fail(
                    "invalid_np_hard_proof_v2_schema",
                    "final program cannot exist without a capability DAG",
                )
        else:
            self.authoring_task.validate()
            if self.authoring_policy == "disabled":
                _fail("invalid_np_hard_proof_v2_schema", "disabled request contains a DAG")
            if (
                self.authoring_task.target_problem.module != self.input_module
                or self.authoring_task.target_problem.term != self.problem_declaration
            ):
                _fail("candidate_wrong_endpoint", "capability DAG targets another input")
            if self.authoring_task.attempt_budget > self.attempt_budget:
                _fail("authoring_gap_budget_exhausted", "DAG exceeds request attempt budget")
            minimum_call_budget = required_model_call_budget(
                gap_node_count=len(self.authoring_task.gap_nodes),
                attempt_budget=self.attempt_budget,
                semantic_planner=any(
                    node.node_id == "reference-semantic-forward"
                    for node in self.authoring_task.gap_nodes
                ),
            )
            if minimum_call_budget > self.call_budget:
                _fail(
                    "authoring_gap_budget_exhausted",
                    "request call budget does not reserve every allowed attempt for the full DAG",
                )
            if self.final_program_declaration is None:
                _fail("invalid_np_hard_proof_v2_schema", "capability DAG lacks final program")
            try:
                validate_declaration_name(
                    self.final_program_declaration, label="V2 final program"
                )
            except ValueError as error:
                _fail("invalid_np_hard_proof_v2_schema", str(error))
        if self.request_id != self.computed_request_id:
            _fail("candidate_dependency_stale", "V2 request ID does not bind its content")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {"request_id": self.request_id, **self._content()}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardProofRequestV2":
        if not isinstance(value, Mapping):
            _fail("invalid_np_hard_proof_v2_schema", "V2 request must be an object")
        expected = {
            "schema_version",
            "request_id",
            "requested_term",
            "input_module",
            "problem_declaration",
            "input_sha256",
            "toolchain",
            "lake_manifest_sha256",
            "objective",
            "direction",
            "planner",
            "authoring_policy",
            "qualification_force_authoring",
            "attempt_budget",
            "call_budget",
            "model_configuration",
            "candidate_validation_mode",
            "authoring_task",
            "final_program_declaration",
        }
        _exact_keys(value, expected, label="V2 request")
        string_fields = expected - {
            "attempt_budget",
            "call_budget",
            "model_configuration",
            "authoring_task",
            "final_program_declaration",
            "qualification_force_authoring",
        }
        if not all(isinstance(value[name], str) for name in string_fields):
            _fail("invalid_np_hard_proof_v2_schema", "V2 string field is invalid")
        if not isinstance(value["attempt_budget"], int) or not isinstance(
            value["call_budget"], int
        ):
            _fail("invalid_np_hard_proof_v2_schema", "V2 budget field is invalid")
        if not isinstance(value["qualification_force_authoring"], bool):
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "qualification_force_authoring must be boolean",
            )
        model_configuration = value["model_configuration"]
        if model_configuration is not None and not isinstance(model_configuration, Mapping):
            _fail("invalid_np_hard_proof_v2_schema", "V2 model configuration is invalid")
        task_value = value["authoring_task"]
        task = (
            NPHardAuthoringTaskV2.from_dict(task_value)
            if isinstance(task_value, Mapping)
            else None
        )
        if task_value is not None and task is None:
            _fail("invalid_np_hard_proof_v2_schema", "V2 authoring task is invalid")
        final_program = value["final_program_declaration"]
        if final_program is not None and not isinstance(final_program, str):
            _fail("invalid_np_hard_proof_v2_schema", "V2 final program is invalid")
        request = cls(
            request_id=value["request_id"],
            requested_term=value["requested_term"],
            input_module=value["input_module"],
            problem_declaration=value["problem_declaration"],
            input_sha256=value["input_sha256"],
            toolchain=value["toolchain"],
            lake_manifest_sha256=value["lake_manifest_sha256"],
            objective=value["objective"],
            direction=value["direction"],
            planner=value["planner"],
            authoring_policy=value["authoring_policy"],
            qualification_force_authoring=value["qualification_force_authoring"],
            attempt_budget=value["attempt_budget"],
            call_budget=value["call_budget"],
            model_configuration=(
                dict(model_configuration) if model_configuration is not None else None
            ),
            candidate_validation_mode=value["candidate_validation_mode"],
            authoring_task=task,
            final_program_declaration=final_program,
            schema_version=value["schema_version"],
        )
        request.validate()
        return request


@dataclass(frozen=True)
class NPHardProofResultV2:
    request_id: str
    job_id: str
    status: str
    failure_code: str | None
    output_dir: str
    input_identity: Mapping[str, Any] | None
    selected_hub: str | None
    capability_dag: Mapping[str, Any] | None
    model_call_ledger: tuple[Mapping[str, Any], ...]
    candidate_publication: tuple[Mapping[str, Any], ...]
    fresh_core: Mapping[str, Any] | None
    artifact: Mapping[str, Any] | None
    independent_replay: Mapping[str, Any] | None
    axiom_audit: Mapping[str, Any] | None
    deletion_audit: Mapping[str, Any] | None
    deterministic_result: Mapping[str, Any]
    authoring_runtime: Mapping[str, Any] | None
    schema_version: str = NP_HARD_PROOF_RESULT_SCHEMA_V2

    @property
    def verified(self) -> bool:
        return self.status == "VERIFIED"

    @property
    def model_calls(self) -> int:
        return len(self.model_call_ledger)

    def validate(self) -> None:
        if self.schema_version != NP_HARD_PROOF_RESULT_SCHEMA_V2:
            _fail("invalid_np_hard_proof_v2_schema", "unsupported proof result schema")
        _require_sha256(self.request_id, label="result request_id")
        _require_sha256(self.job_id, label="result job_id")
        if self.status not in NP_HARD_PROOF_RESULT_STATUSES_V2:
            _fail("invalid_np_hard_proof_v2_schema", "unknown proof result status")
        if self.status == "VERIFIED":
            if self.failure_code is not None:
                _fail("invalid_np_hard_proof_v2_schema", "verified result has a failure")
            if self.artifact is None or self.independent_replay is None:
                _fail("independent_replay_failed", "verified result lacks final evidence")
            if not self.independent_replay.get("passed"):
                _fail("independent_replay_failed", "verified replay did not pass")
            if self.axiom_audit is None or not self.axiom_audit.get("passed"):
                _fail("candidate_nonstandard_axiom", "verified axiom audit did not pass")
            if self.deletion_audit is not None and not self.deletion_audit.get("passed"):
                _fail("deletion_audit_failed", "verified deletion audit did not pass")
        elif not self.failure_code:
            _fail("invalid_np_hard_proof_v2_schema", "non-verified result lacks failure code")
        if self.authoring_runtime is None and self.model_call_ledger:
            _fail("invalid_np_hard_proof_v2_schema", "deterministic result claims model calls")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {
            "schema_version": self.schema_version,
            "request_id": self.request_id,
            "job_id": self.job_id,
            "status": self.status,
            "failure_code": self.failure_code,
            "output_dir": self.output_dir,
            "input_identity": dict(self.input_identity) if self.input_identity else None,
            "selected_hub": self.selected_hub,
            "capability_dag": dict(self.capability_dag) if self.capability_dag else None,
            "model_calls": self.model_calls,
            "model_call_ledger": [dict(item) for item in self.model_call_ledger],
            "candidate_publication": [dict(item) for item in self.candidate_publication],
            "fresh_core": dict(self.fresh_core) if self.fresh_core else None,
            "artifact": dict(self.artifact) if self.artifact else None,
            "independent_replay": (
                dict(self.independent_replay) if self.independent_replay else None
            ),
            "axiom_audit": dict(self.axiom_audit) if self.axiom_audit else None,
            "deletion_audit": dict(self.deletion_audit) if self.deletion_audit else None,
            "deterministic_result": dict(self.deterministic_result),
            "authoring_runtime": (
                dict(self.authoring_runtime) if self.authoring_runtime else None
            ),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardProofResultV2":
        if not isinstance(value, Mapping):
            _fail("invalid_np_hard_proof_v2_schema", "V2 result must be an object")
        expected = {
            "schema_version",
            "request_id",
            "job_id",
            "status",
            "failure_code",
            "output_dir",
            "input_identity",
            "selected_hub",
            "capability_dag",
            "model_calls",
            "model_call_ledger",
            "candidate_publication",
            "fresh_core",
            "artifact",
            "independent_replay",
            "axiom_audit",
            "deletion_audit",
            "deterministic_result",
            "authoring_runtime",
        }
        _exact_keys(value, expected, label="V2 result")
        if not isinstance(value["model_calls"], int):
            _fail("invalid_np_hard_proof_v2_schema", "V2 model call count is invalid")
        ledger = value["model_call_ledger"]
        publications = value["candidate_publication"]
        if not isinstance(ledger, list) or not all(isinstance(item, Mapping) for item in ledger):
            _fail("invalid_np_hard_proof_v2_schema", "V2 model ledger is invalid")
        if not isinstance(publications, list) or not all(
            isinstance(item, Mapping) for item in publications
        ):
            _fail("invalid_np_hard_proof_v2_schema", "V2 publication list is invalid")
        mapping_fields = (
            "input_identity",
            "capability_dag",
            "fresh_core",
            "artifact",
            "independent_replay",
            "axiom_audit",
            "deletion_audit",
            "authoring_runtime",
        )
        if any(
            value[name] is not None and not isinstance(value[name], Mapping)
            for name in mapping_fields
        ) or not isinstance(value["deterministic_result"], Mapping):
            _fail("invalid_np_hard_proof_v2_schema", "V2 evidence field is invalid")
        if value["model_calls"] != len(ledger):
            _fail("invalid_np_hard_proof_v2_schema", "V2 model call count drifted")
        result = cls(
            request_id=value["request_id"],
            job_id=value["job_id"],
            status=value["status"],
            failure_code=value["failure_code"],
            output_dir=value["output_dir"],
            input_identity=(
                dict(value["input_identity"]) if value["input_identity"] else None
            ),
            selected_hub=value["selected_hub"],
            capability_dag=(
                dict(value["capability_dag"]) if value["capability_dag"] else None
            ),
            model_call_ledger=tuple(dict(item) for item in ledger),
            candidate_publication=tuple(dict(item) for item in publications),
            fresh_core=dict(value["fresh_core"]) if value["fresh_core"] else None,
            artifact=dict(value["artifact"]) if value["artifact"] else None,
            independent_replay=(
                dict(value["independent_replay"])
                if value["independent_replay"]
                else None
            ),
            axiom_audit=dict(value["axiom_audit"]) if value["axiom_audit"] else None,
            deletion_audit=(
                dict(value["deletion_audit"]) if value["deletion_audit"] else None
            ),
            deterministic_result=dict(value["deterministic_result"]),
            authoring_runtime=(
                dict(value["authoring_runtime"]) if value["authoring_runtime"] else None
            ),
            schema_version=value["schema_version"],
        )
        result.validate()
        return result


def read_np_hard_result(value: Mapping[str, Any]) -> Mapping[str, Any] | NPHardProofResultV2:
    """Read V2 strictly while preserving the exact semantics of stored V1 results."""

    schema = value.get("schema_version") if isinstance(value, Mapping) else None
    if schema == NP_HARD_PROOF_RESULT_SCHEMA_V2:
        return NPHardProofResultV2.from_dict(value)
    if schema == NP_HARD_RESULT_SCHEMA_V1:
        return dict(value)
    _fail("invalid_np_hard_proof_v2_schema", "unsupported NP-hard result schema")


@dataclass(frozen=True)
class NPHardOrchestratorConfigV2:
    root: Path
    input_module: str | None
    problem_declaration: str
    output_dir: Path | None = None
    lean_timeout_seconds: int = 600
    authoring_policy: str = "model-auto"
    attempt_budget: int = 4
    call_budget: int | None = None
    deepseek: DeepSeekConfig | None = None
    runtime_prebuilt: bool = False
    authoring_task: NPHardAuthoringTaskV2 | None = None
    final_program_declaration: str | None = None
    resume_checkpoint_path: Path | None = None
    expected_checkpoint_file_sha256: str | None = None
    max_new_nodes: int | None = None
    preflight_path: Path | None = None
    formal_qualification: bool = False
    qualification_force_authoring: bool = False


def build_np_hard_proof_request_v2(config: NPHardOrchestratorConfigV2) -> NPHardProofRequestV2:
    root = config.root.resolve()
    reference = resolve_np_hard_input_reference(
        root=root,
        input_module=config.input_module,
        requested_term=config.problem_declaration,
    )
    minimum_call_budget = required_model_call_budget(
        gap_node_count=(len(config.authoring_task.gap_nodes) if config.authoring_task else 0),
        attempt_budget=config.attempt_budget,
        semantic_planner=bool(
            config.authoring_task is not None
            and any(
                node.node_id == "reference-semantic-forward"
                for node in config.authoring_task.gap_nodes
            )
        ),
    )
    call_budget = (
        minimum_call_budget if config.call_budget is None else config.call_budget
    )
    arguments = {
        "requested_term": reference.requested_term,
        "input_module": reference.input_module,
        "problem_declaration": reference.problem_declaration,
        "input_sha256": reference.normalization_observation.import_closure_sha256,
        "toolchain": (root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lake_manifest_sha256": "sha256:" + sha256_file(root / "Lean" / "lake-manifest.json"),
        "authoring_policy": config.authoring_policy,
        "qualification_force_authoring": config.qualification_force_authoring,
        "attempt_budget": config.attempt_budget,
        "call_budget": call_budget,
        "model_configuration": _public_model_configuration(config.deepseek),
        "candidate_validation_mode": "persistent-worker",
        "authoring_task": config.authoring_task,
        "final_program_declaration": config.final_program_declaration,
    }
    provisional = NPHardProofRequestV2(
        request_id="sha256:" + "0" * 64, **arguments
    )
    request = NPHardProofRequestV2(
        request_id=provisional.computed_request_id, **arguments
    )
    request.validate()
    return request


def _publication_records(runtime_root: Path) -> tuple[Mapping[str, Any], ...]:
    records: list[Mapping[str, Any]] = []
    for manifest_path in sorted((runtime_root / "published").glob("*/manifest.json")):
        payload = json.loads(manifest_path.read_text(encoding="utf-8"))
        records.append(
            {
                "manifest_file": str(manifest_path),
                "manifest_sha256": "sha256:" + sha256_file(manifest_path),
                "node_id": payload["node_id"],
                "declaration": payload["declaration"],
                "body_sha256": payload["body_sha256"],
                "cumulative_source_sha256": payload["cumulative_source_sha256"],
                "fresh_core_evidence_sha256": payload["fresh_core_evidence_sha256"],
            }
        )
    return tuple(records)


class NPHardOrchestratorV2:
    def __init__(
        self,
        config: NPHardOrchestratorConfigV2,
        *,
        model_client: NPHardNodeModelClient | None = None,
    ):
        self.config = config
        self.root = config.root.resolve()
        self.model_client = model_client or (
            DeepSeekClient(config.deepseek) if config.deepseek is not None else None
        )
        self.authoring_plan: NPHardAuthoringPlanV2 | None = None
        self.authoring_planner_failure_code: str | None = None
        self.input_reference: NPHardInputReferenceV1 | None = None
        self.scope_policy_entry: NPHardScopePolicyEntryV1 | None = None

    def _result(
        self,
        *,
        request: NPHardProofRequestV2,
        job_id: str,
        output_dir: Path,
        deterministic: Mapping[str, Any],
        status: str,
        failure_code: str | None,
        runtime_payload: Mapping[str, Any] | None = None,
    ) -> NPHardProofResultV2:
        task = request.authoring_task
        runtime_root = output_dir / "authoring" / "runtime"
        ledger = tuple(
            dict(item) for item in (runtime_payload or {}).get("model_call_ledger", [])
        )
        publications = _publication_records(runtime_root) if runtime_payload else ()
        artifact_path = runtime_root / "Final.lean"
        replay_path = runtime_root / "Replay.lean"
        deterministic_verified = deterministic.get("status") == "VERIFIED"
        artifact = None
        replay = None
        axiom = None
        deletion = None
        fresh_core = None
        if deterministic_verified and runtime_payload is None:
            artifact_file = deterministic.get("artifact_file")
            artifact = {
                "file": artifact_file,
                "sha256": (
                    "sha256:" + str(deterministic.get("artifact_sha256"))
                    if deterministic.get("artifact_sha256")
                    else None
                ),
                "endpoint": request.problem_declaration,
                "authority": "independent-lean-process",
            }
            replay = dict((deterministic.get("certificates") or {}).get("replay") or {})
            axiom = {"passed": True, "authority": "assert_standard_axioms"}
            fresh_core = {"count": 0, "passed": True, "deterministic_fast_path": True}
        elif runtime_payload is not None:
            verified_runtime = runtime_payload.get("status") == "VERIFIED"
            if artifact_path.is_file():
                artifact = {
                    "file": str(artifact_path),
                    "sha256": "sha256:" + sha256_file(artifact_path),
                    "endpoint": request.problem_declaration,
                    "authority": "independent-lean-process",
                }
            commands = list(runtime_payload.get("commands") or [])
            replay = {
                "file": str(replay_path) if replay_path.is_file() else None,
                "sha256": (
                    "sha256:" + sha256_file(replay_path) if replay_path.is_file() else None
                ),
                "command": commands[-1] if len(commands) >= 2 else None,
                "passed": bool(verified_runtime and len(commands) >= 2 and commands[-1]["exit_code"] == 0),
                "authority": "independent-lean-process",
            }
            axiom = {
                "passed": bool(
                    verified_runtime
                    and artifact_path.is_file()
                    and "assert_standard_axioms" in artifact_path.read_text(encoding="utf-8")
                ),
                "authority": "Lean assert_standard_axioms",
            }
            audits = [dict(item) for item in runtime_payload.get("deletion_audits", [])]
            deletion = {
                "passed": bool(
                    verified_runtime
                    and task is not None
                    and len(audits) == len(task.gap_nodes)
                    and all(item.get("passed") for item in audits)
                ),
                "node_count": len(audits),
                "nodes": audits,
            }
            fresh_core = {
                "count": runtime_payload.get("fresh_core_rediscoveries", 0),
                "passed": bool(
                    runtime_payload.get("fresh_core_rediscoveries", 0)
                    >= len(runtime_payload.get("accepted_nodes", []))
                ),
            }
        result = NPHardProofResultV2(
            request_id=request.request_id,
            job_id=job_id,
            status=status,
            failure_code=failure_code,
            output_dir=str(output_dir),
            input_identity=deterministic.get("input_identity"),
            selected_hub=(
                task.source_problem.term if task is not None else deterministic.get("selected_hub")
            ),
            capability_dag=task.to_dict() if task is not None else None,
            model_call_ledger=ledger,
            candidate_publication=publications,
            fresh_core=fresh_core,
            artifact=artifact,
            independent_replay=replay,
            axiom_audit=axiom,
            deletion_audit=deletion,
            deterministic_result=dict(deterministic),
            authoring_runtime=(dict(runtime_payload) if runtime_payload is not None else None),
        )
        result.validate()
        return result

    def run(self) -> NPHardProofResultV2:
        self.input_reference = resolve_np_hard_input_reference(
            root=self.root,
            input_module=self.config.input_module,
            requested_term=self.config.problem_declaration,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        self.scope_policy_entry = scope_policy_entry_for_input_reference(
            root=self.root, reference=self.input_reference
        )
        initial_request = build_np_hard_proof_request_v2(self.config)
        initial_job_id = compute_job_id(
            {
                "schema_version": NP_HARD_PROOF_RESULT_SCHEMA_V2,
                "request_id": initial_request.request_id,
            }
        )
        output_dir = (
            self.config.output_dir.resolve()
            if self.config.output_dir is not None
            else self.root
            / ".reduction-agent"
            / "np-hard-v2-jobs"
            / initial_job_id.removeprefix("sha256:")
        )
        if (
            self.config.authoring_task is None
            and self.config.authoring_policy in {"model-auto", "model-required"}
            and self.scope_policy_entry is None
        ):
            deepseek = self.config.deepseek
            try:
                self.authoring_plan = NPHardAuthoringPlannerV2(
                    root=self.root,
                    input_module=initial_request.input_module,
                    input_problem_declaration=initial_request.problem_declaration,
                    output_dir=output_dir / "planning",
                    attempt_budget=self.config.attempt_budget,
                    timeout_seconds=(
                        min(deepseek.timeout_seconds, 600) if deepseek is not None else 60
                    ),
                    max_output_tokens=(deepseek.max_tokens if deepseek is not None else 3000),
                    lean_timeout_seconds=self.config.lean_timeout_seconds,
                ).plan()
            except NPHardAuthoringPlannerError as error:
                self.authoring_planner_failure_code = error.code
            else:
                if (
                    self.authoring_plan.task is not None
                    and self.authoring_plan.final_program_declaration is not None
                ):
                    self.config = replace(
                        self.config,
                        authoring_task=self.authoring_plan.task,
                        final_program_declaration=(
                            self.authoring_plan.final_program_declaration
                        ),
                    )
                else:
                    self.authoring_planner_failure_code = (
                        self.authoring_plan.failure_code
                        or "authoring_plan_unavailable"
                    )
        request = build_np_hard_proof_request_v2(self.config)
        job_id = compute_job_id(
            {
                "schema_version": NP_HARD_PROOF_RESULT_SCHEMA_V2,
                "request_id": request.request_id,
            }
        )
        model_configuration = _public_model_configuration(self.config.deepseek)
        if model_configuration is None:
            model_configuration = {
                "base_url": None,
                "model": None,
                "timeout_seconds": None,
                "temperature": None,
                "max_tokens": None,
                "max_retries": None,
                "reasoning_effort": None,
                "api_key_configured": False,
                "node_reasoning_policy": public_node_reasoning_policy(),
            }
        qualification_profile_matched = bool(
            self.config.deepseek is not None
            and is_formal_np_hard_qualification_config(self.config.deepseek)
        )
        preflight = NPHardProductionPreflightV1(
            authoring_policy=request.authoring_policy,
            qualification_force_authoring=request.qualification_force_authoring,
            attempt_budget=request.attempt_budget,
            call_budget=request.call_budget,
            model_configuration=model_configuration,
            formal_qualification=self.config.formal_qualification,
            qualification_profile_matched=qualification_profile_matched,
            input_module=request.input_module,
            requested_problem=request.requested_term,
            output_dir=str(output_dir),
        )
        preflight.write(
            self.config.preflight_path.resolve()
            if self.config.preflight_path is not None
            else output_dir / "preflight.json"
        )
        if self.config.formal_qualification and not qualification_profile_matched:
            _fail(
                "qualification_model_profile_mismatch",
                "formal qualification requires the accepted DeepSeek V4 Flash profile",
            )
        if request.qualification_force_authoring and not self.config.formal_qualification:
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "forced authoring is restricted to formal qualification jobs",
            )
        if request.qualification_force_authoring and not request.input_module.startswith(
            "ComplexityReduction."
        ):
            _fail(
                "invalid_np_hard_proof_v2_schema",
                "forced qualification authoring requires a public ComplexityReduction input",
            )
        store = JobStore(output_dir)
        with store.exclusive_run():
            store.write_json("request.json", request.to_dict())
            store.transition("RECEIVED", details={"job_id": job_id, "request_id": request.request_id})
            deterministic_result = NPHardAgentV1(
                NPHardAgentConfigV1(
                    root=self.root,
                    input_module=request.input_module,
                    problem_declaration=request.problem_declaration,
                    output_dir=store.path("deterministic"),
                    lean_timeout_seconds=self.config.lean_timeout_seconds,
                    authoring_mode="disabled",
                    runtime_prebuilt=self.config.runtime_prebuilt,
                    candidate_validation_mode="persistent-worker",
                    input_reference=self.input_reference,
                )
            ).run()
            deterministic = deterministic_result.to_dict()
            if self.scope_policy_entry is not None:
                deterministic = {
                    **deterministic,
                    "target_scope_policy": self.scope_policy_entry.to_dict(root=self.root),
                }
            store.write_json("deterministic-result.json", deterministic)
            if (
                deterministic_result.status == "VERIFIED"
                and not request.qualification_force_authoring
            ):
                if self.scope_policy_entry is not None:
                    result = self._result(
                        request=request,
                        job_id=job_id,
                        output_dir=output_dir,
                        deterministic=deterministic,
                        status="FAILED",
                        failure_code="scope_policy_conflict",
                    )
                    store.transition(
                        "FAILED", details={"code": "scope_policy_conflict"}
                    )
                    store.write_json("report.json", result.to_dict())
                    return result
                result = self._result(
                    request=request,
                    job_id=job_id,
                    output_dir=output_dir,
                    deterministic=deterministic,
                    status="VERIFIED",
                    failure_code=None,
                )
                store.transition("VERIFIED", details={"fast_path": True, "model_calls": 0})
                store.write_json("report.json", result.to_dict())
                return result

            initial_failure = deterministic_result.failure
            initial_code = initial_failure.code if initial_failure is not None else "deterministic_probe_failed"
            if self.scope_policy_entry is not None:
                if (
                    self.scope_policy_entry.disposition
                    == POLICY_DISPOSITION_AUXILIARY
                ):
                    policy_failure_code = "auxiliary_or_non_target"
                elif (
                    self.scope_policy_entry.disposition
                    == POLICY_DISPOSITION_ENCODING_COMPLEXITY_FRONTIER
                ):
                    policy_failure_code = self.scope_policy_entry.failure_code
                    if policy_failure_code is None:
                        raise NPHardScopePolicyError(
                            "encoding-complexity policy row lacks a production blocker"
                        )
                else:
                    raise NPHardScopePolicyError(
                        "unsupported production scope-policy disposition"
                    )
                result = self._result(
                    request=request,
                    job_id=job_id,
                    output_dir=output_dir,
                    deterministic=deterministic,
                    status="BLOCKED",
                    failure_code=policy_failure_code,
                )
                store.transition(
                    "BLOCKED", details={"code": policy_failure_code}
                )
                store.write_json("report.json", result.to_dict())
                return result
            authorable = _deterministic_outcome_allows_authoring(
                status=deterministic_result.status,
                failure_code=initial_code,
                authoring_policy=request.authoring_policy,
                qualification_force_authoring=request.qualification_force_authoring,
            )
            if not authorable:
                result = self._result(
                    request=request,
                    job_id=job_id,
                    output_dir=output_dir,
                    deterministic=deterministic,
                    status=("BLOCKED" if deterministic_result.status == "BLOCKED" else "FAILED"),
                    failure_code=initial_code,
                )
                store.transition(result.status, details={"code": initial_code})
                store.write_json("report.json", result.to_dict())
                return result
            if request.authoring_task is None:
                planner_code = (
                    self.authoring_planner_failure_code
                    or "authoring_plan_unavailable"
                )
                result = self._result(
                    request=request,
                    job_id=job_id,
                    output_dir=output_dir,
                    deterministic=deterministic,
                    status="BLOCKED",
                    failure_code=planner_code,
                )
                store.transition("BLOCKED", details={"code": planner_code})
                store.write_json("report.json", result.to_dict())
                return result
            if self.model_client is None:
                result = self._result(
                    request=request,
                    job_id=job_id,
                    output_dir=output_dir,
                    deterministic=deterministic,
                    status="BLOCKED",
                    failure_code="model_provider_unavailable",
                )
                store.transition("BLOCKED", details={"code": "model_provider_unavailable"})
                store.write_json("report.json", result.to_dict())
                return result

            runtime_root = store.path("authoring/runtime")
            resume_path = self.config.resume_checkpoint_path
            if resume_path is not None:
                resolved_resume = resume_path.resolve()
                try:
                    resolved_resume.relative_to(runtime_root.resolve())
                except ValueError:
                    _fail("cross_job_candidate", "resume checkpoint belongs to another job")
                resume_path = resolved_resume
            store.write_json("authoring/task.json", request.authoring_task.to_dict())
            store.transition(
                "PLAN_SELECTED",
                details={
                    "task_request_id": request.authoring_task.request_id,
                    "node_count": len(request.authoring_task.gap_nodes),
                },
            )
            store.transition("AUTHORING")
            runtime = NPHardGapRuntimeV1(
                root=self.root,
                task=request.authoring_task,
                output_root=runtime_root,
                model=self.model_client,
                final_program_declaration=request.final_program_declaration or "",
                timeout_seconds=self.config.lean_timeout_seconds,
                instance_call_budget=request.call_budget,
            ).run(
                resume_checkpoint_path=resume_path,
                expected_checkpoint_file_sha256=self.config.expected_checkpoint_file_sha256,
                max_new_nodes=self.config.max_new_nodes,
            )
            runtime_payload = runtime.to_dict(request.authoring_task)
            store.write_json("authoring/runtime-result.json", runtime_payload)
            if runtime.model_calls > request.call_budget:
                _fail("authoring_gap_budget_exhausted", "runtime exceeded V2 call budget")
            if runtime.status == "VERIFIED":
                status = "VERIFIED"
                failure_code = None
            elif runtime.status == "CHECKPOINTED":
                status = "BLOCKED"
                failure_code = "authoring_checkpoint_created"
            else:
                infrastructure_codes = {
                    "lean_infrastructure_error",
                    "final_lean_failed",
                    "independent_replay_failed",
                    "fresh_core_resolve_failed",
                    "deletion_audit_failed",
                }
                status = "FAILED" if runtime.failure_code in infrastructure_codes else "BLOCKED"
                failure_code = runtime.failure_code or "authoring_failed"
            result = self._result(
                request=request,
                job_id=job_id,
                output_dir=output_dir,
                deterministic=deterministic,
                status=status,
                failure_code=failure_code,
                runtime_payload=runtime_payload,
            )
            store.transition(status, details={"code": failure_code, "model_calls": result.model_calls})
            store.write_json("report.json", result.to_dict())
            return result
