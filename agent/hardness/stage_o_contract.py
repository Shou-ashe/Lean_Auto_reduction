"""Frozen Stage O contracts for competitive choice and sequential authoring.

The objects in this module are observational only.  They validate benchmark
metadata, model actions, content-addressed state, and report structure; none of
them grants a Lean capability or substitutes for final elaboration.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any

from .benchmark import BenchmarkCase, BenchmarkSuite
from .model_client import extract_json_object
from .models import sha256_id


STAGE_O_CASE_SCHEMA = "hardness_stage_o_case_v1"
STAGE_O_CANDIDATE_SCHEMA = "hardness_stage_o_candidate_v1"
STAGE_O_CANDIDATE_SET_SCHEMA = "hardness_stage_o_candidate_set_v1"
STAGE_O_ACTION_SCHEMA = "hardness_stage_o_action_v1"
STAGE_O_PROMPT_SCHEMA = "hardness_stage_o_contract_prompt_v1"
STAGE_O_PROMOTION_SCHEMA = "hardness_stage_o_promotion_manifest_v1"
STAGE_O_CACHE_KEY_SCHEMA = "hardness_stage_o_lean_cache_key_v1"
STAGE_O_REPORT_SCHEMA = "hardness_stage_o_multi_gap_report_v1"
STAGE_O_OFFLINE_REPORT_SCHEMA = "hardness_stage_o_multi_gap_offline_report_v1"
STAGE_O_CONTRACT_REPORT_SCHEMA = "hardness_stage_o_contract_deepseek_report_v1"
STAGE_O_STABILITY_AGGREGATE_SCHEMA = "hardness_stage_o_stability_aggregate_v1"
STAGE_O_MICROBENCHMARK_SCHEMA = "hardness_stage_o_lean_service_microbenchmark_v1"

STAGE_O_POSITIVE_SUITE_ID = "stage-o-multi-gap"
STAGE_O_NEGATIVE_SUITE_ID = "stage-o-adversarial"
STAGE_O_INPUT_MODULE = "Benchmark.Hardness.Inputs.StageO.Inputs"
STAGE_O_MAX_JOBS = 4
STAGE_O_INSPECT_LIMIT = 3
STAGE_O_CANDIDATE_MIN = 3
STAGE_O_CANDIDATE_MAX = 8

STAGE_O_SYSTEM_PROMPT = """You are an untrusted Stage O candidate selector.
Use only the public goal, searched candidate summaries, bounded inspected packet metadata, and
available dependency IDs. Preserve the exact input/output endpoints, direction, objective, and
capability kind. Select a retrieved packet only when its public preconditions, dependency hash,
visibility, imports, axioms, and route segments are all valid. Otherwise stop with concrete missing
conditions. A literal self dependency is a cycle; job_local_unpublished is never visible to this
session; every precondition/dependency must occur in available_dependencies; source and bound
dependency hashes must match; route segments must connect consecutively from the exact input to the
exact output; any oracle import or declared axiom is forbidden. Never invent or replace a packet,
endpoint, dependency, declaration, proof, next gap,
case ID, expected answer, or hidden ranking. Return exactly one JSON object matching
hardness_stage_o_action_v1 and no markdown fence."""

STAGE_O_FAILURE_CODES = frozenset(
    {
        "competitive_choice_not_real",
        "packet_precondition_unsatisfied",
        "global_route_disconnected",
        "gap_sequence_mismatch",
        "second_gap_not_revealed",
        "sequential_gap_budget_exhausted",
        "stale_gap_dependency",
        "capability_promotion_failed",
        "published_capability_not_visible",
        "unpublished_candidate_visible",
        "consumer_authoring_forbidden",
        "ablation_response_reused",
        "no_alternative_after_ablation",
        "lean_service_session_leak",
        "lean_cache_key_incomplete",
        "lean_cache_stale_hit",
        "parameterized_input_unresolved",
        "parameter_fingerprint_mismatch",
        "presentation_adapter_not_lean_confirmed",
        "wrong_endpoint",
        "wrong_direction",
        "unsupported_checker_or_tm_packet",
        "oracle_or_nonstandard_axiom",
        "final_lean_failed",
        "release_replay_failed",
        "certificate_dag_cycle",
    }
)

EXPECTED_POSITIVE_OBJECTIVES: Mapping[str, str] = {
    "o-core-ambiguous-fixed-target": "reduce_to",
    "o-core-ambiguous-auto-target": "reduce_to_known_hardness",
    "o-predicate-adapter-route": "reduce_to_known_np",
    "o-parameterized-predicate-membership": "prove_in_np",
    "o-two-gap-presentation-then-reduction": "reduce_to",
    "o-two-gap-checker-then-membership": "prove_np_complete",
    "o-capability-producer": "reduce_to",
    "o-capability-consumer": "prove_np_complete",
}

EXPECTED_NEGATIVE_FAILURES: Mapping[str, str] = {
    "o-cycle-dag-blocked": "certificate_dag_cycle",
    "o-second-gap-precondition-missing": "packet_precondition_unsatisfied",
    "o-type-correct-wrong-direction": "wrong_direction",
    "o-locally-valid-globally-disconnected": "global_route_disconnected",
    "o-unsupported-checker": "unsupported_checker_or_tm_packet",
    "o-stale-gap1-invalidates-gap2": "stale_gap_dependency",
    "o-unpublished-cross-case-isolation": "unpublished_candidate_visible",
    "o-oracle-or-axiom-candidate-rejected": "oracle_or_nonstandard_axiom",
}

PUBLIC_CASE_KEYS = {
    "schema_version",
    "protocol_role",
    "contract_probe_profile",
    "candidate_search_actions",
    "candidate_count_range",
    "minimum_locally_valid_candidates",
    "inspect_limit",
    "maximum_gap_count",
    "promotion_role",
    "ablation_required",
    "resolved_parameters",
    "lean_validation_profile",
}

PROTOCOL_ROLES = {
    "competitive_core",
    "predicate_core",
    "parameterized_membership",
    "sequential_authoring",
    "capability_producer",
    "capability_consumer",
    "adversarial",
}
CONTRACT_PROBE_PROFILES = {
    "valid_competitive",
    "cycle",
    "missing_precondition",
    "wrong_direction",
    "disconnected",
    "unsupported_checker",
    "stale_dependency",
    "unpublished",
    "oracle_or_axiom",
}
PROMOTION_ROLES = {"none", "producer", "consumer", "unpublished_consumer"}
CANDIDATE_KINDS = {
    "route_packet",
    "gadget_packet",
    "membership_packet",
    "tm_certificate_packet",
}
DIRECTIONS = {"identity", "source_to_target"}
VISIBILITIES = {"base_registry", "case_local", "published", "job_local_unpublished"}
SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}")
ORACLE_MARKERS = (".Oracles.", ".Gold.", ".GoldProofs.", ".HiddenTargets.", ".Legacy.")
FORBIDDEN_AXIOMS = {"Classical.choice", "propext", "Quot.sound", "admit", "sorryAx"}
PROMPT_FORBIDDEN_KEYS = {
    "expected",
    "coverage",
    "gold",
    "gold_route",
    "gold_proof",
    "case_id",
    "hidden_ranking",
    "old_response",
    "previous_response",
    "resume_report",
    "replay_response",
}


class StageOContractError(ValueError):
    """Stable, machine-readable Stage O contract rejection."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _json_copy(value: Any, *, label: str) -> Any:
    try:
        return json.loads(json.dumps(value, ensure_ascii=True, sort_keys=True))
    except (TypeError, ValueError) as error:
        raise StageOContractError("invalid_schema", f"{label} is not JSON serializable") from error


def _nonempty_string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise StageOContractError("invalid_schema", f"{label} must be a non-empty string")
    return value.strip()


def _string_tuple(value: Any, *, label: str, allow_empty: bool = True) -> tuple[str, ...]:
    if not isinstance(value, list) or (not allow_empty and not value):
        raise StageOContractError("invalid_schema", f"{label} must be a string list")
    result = tuple(_nonempty_string(item, label=f"{label}[]") for item in value)
    if len(set(result)) != len(result):
        raise StageOContractError("invalid_schema", f"{label} contains duplicates")
    return result


def _forbidden_key_paths(value: Any, *, path: str = "") -> set[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, nested in value.items():
            key_text = str(key).lower()
            nested_path = f"{path}.{key}" if path else str(key)
            if key_text in PROMPT_FORBIDDEN_KEYS:
                found.add(nested_path)
            found.update(_forbidden_key_paths(nested, path=nested_path))
    elif isinstance(value, (list, tuple)):
        for index, nested in enumerate(value):
            found.update(_forbidden_key_paths(nested, path=f"{path}[{index}]"))
    return found


def _all_strings(value: Any) -> tuple[str, ...]:
    if isinstance(value, str):
        return (value,)
    if isinstance(value, Mapping):
        return tuple(item for nested in value.values() for item in _all_strings(nested))
    if isinstance(value, (list, tuple)):
        return tuple(item for nested in value for item in _all_strings(nested))
    return ()


def audit_stage_o_prompt(
    payload: Mapping[str, Any], *, forbidden_values: Iterable[str] = ()
) -> None:
    if payload.get("schema_version") != STAGE_O_PROMPT_SCHEMA:
        raise StageOContractError("unsupported_schema", "Stage O prompt schema is not frozen v1")
    forbidden_paths = _forbidden_key_paths(payload)
    if forbidden_paths:
        raise StageOContractError(
            "prompt_oracle_leak",
            "Stage O prompt contains forbidden fields: " + ", ".join(sorted(forbidden_paths)),
        )
    strings = _all_strings(payload)
    for forbidden in forbidden_values:
        if forbidden and any(forbidden in value for value in strings):
            raise StageOContractError(
                "prompt_oracle_leak", "Stage O prompt contains a forbidden benchmark value"
            )


def _validate_public_case_contract(case: BenchmarkCase) -> None:
    contract = case.stage_o
    if set(contract) != PUBLIC_CASE_KEYS:
        raise StageOContractError(
            "invalid_schema",
            f"{case.id}.stage_o keys must exactly equal {sorted(PUBLIC_CASE_KEYS)}",
        )
    if contract.get("schema_version") != STAGE_O_CASE_SCHEMA:
        raise StageOContractError("unsupported_schema", f"{case.id} uses an unsupported Stage O ABI")
    role = contract.get("protocol_role")
    if role not in PROTOCOL_ROLES:
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid protocol role")
    if contract.get("contract_probe_profile") not in CONTRACT_PROBE_PROFILES:
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid contract probe profile")
    actions = _string_tuple(
        contract.get("candidate_search_actions"),
        label=f"{case.id}.stage_o.candidate_search_actions",
        allow_empty=False,
    )
    if not set(actions).issubset(
        {
            "search_problems",
            "search_hardness_targets",
            "search_reductions",
            "search_native_evidence",
            "search_packets",
        }
    ):
        raise StageOContractError("invalid_schema", f"{case.id} has an unsupported search action")
    candidate_range = contract.get("candidate_count_range")
    if candidate_range != [STAGE_O_CANDIDATE_MIN, STAGE_O_CANDIDATE_MAX]:
        raise StageOContractError("invalid_schema", f"{case.id} must freeze the 3..8 candidate range")
    locally_valid = contract.get("minimum_locally_valid_candidates")
    if (
        isinstance(locally_valid, bool)
        or not isinstance(locally_valid, int)
        or locally_valid < 0
        or locally_valid > STAGE_O_CANDIDATE_MAX
    ):
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid local-candidate bound")
    if contract.get("inspect_limit") != STAGE_O_INSPECT_LIMIT:
        raise StageOContractError("invalid_schema", f"{case.id} must freeze inspect_limit=3")
    maximum_gaps = contract.get("maximum_gap_count")
    if isinstance(maximum_gaps, bool) or maximum_gaps not in {0, 1, 2}:
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid gap bound")
    if contract.get("promotion_role") not in PROMOTION_ROLES:
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid promotion role")
    if not isinstance(contract.get("ablation_required"), bool):
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid ablation flag")
    parameters = contract.get("resolved_parameters")
    if not isinstance(parameters, list):
        raise StageOContractError("invalid_schema", f"{case.id} resolved_parameters must be a list")
    for index, parameter in enumerate(parameters):
        if not isinstance(parameter, Mapping) or set(parameter) != {"name", "type", "value"}:
            raise StageOContractError(
                "invalid_schema", f"{case.id} resolved_parameters[{index}] has an invalid shape"
            )
        for key in ("name", "type", "value"):
            _nonempty_string(parameter.get(key), label=f"{case.id}.resolved_parameters[{index}].{key}")
    if contract.get("lean_validation_profile") != "stage_o_strict_v1":
        raise StageOContractError("invalid_schema", f"{case.id} has an invalid Lean profile")
    forbidden = _forbidden_key_paths(contract)
    if forbidden:
        raise StageOContractError(
            "contract_oracle_leak", f"{case.id} public contract leaks {sorted(forbidden)}"
        )


def validate_stage_o_suites(
    positive_suite: BenchmarkSuite, negative_suite: BenchmarkSuite
) -> tuple[BenchmarkCase, ...]:
    """Validate the frozen, answer-isolated 8+8 Stage O matrix."""

    if positive_suite.id != STAGE_O_POSITIVE_SUITE_ID:
        raise StageOContractError("wrong_suite", "Stage O positive suite ID drifted")
    if negative_suite.id != STAGE_O_NEGATIVE_SUITE_ID:
        raise StageOContractError("wrong_suite", "Stage O adversarial suite ID drifted")
    positives = positive_suite.cases
    negatives = negative_suite.cases
    if len(positives) != 8 or len(negatives) != 8:
        raise StageOContractError("wrong_case_count", "Stage O must freeze exactly 8+8 cases")
    if {case.id for case in positives} != set(EXPECTED_POSITIVE_OBJECTIVES):
        raise StageOContractError("case_id_drift", "Stage O positive case IDs drifted")
    if {case.id for case in negatives} != set(EXPECTED_NEGATIVE_FAILURES):
        raise StageOContractError("case_id_drift", "Stage O negative case IDs drifted")

    all_cases = (*positives, *negatives)
    for case in all_cases:
        if (
            case.module != STAGE_O_INPUT_MODULE
            or case.evaluation_lane != "stage_o"
            or case.verification_profile != "strict-release"
            or case.catalog_mode != "full"
            or case.objective_direction != "source_to_target"
            or case.maximum_route_atoms is None
            or case.maximum_dependencies is None
            or not case.require_simple_path
            or case.typed_authoring
            or case.expected.baseline_status is not None
            or case.expected.baseline_failure_code is not None
        ):
            raise StageOContractError("case_outside_abi", f"{case.id} is outside the Stage O ABI")
        _validate_public_case_contract(case)

    for case in positives:
        if case.objective != EXPECTED_POSITIVE_OBJECTIVES[case.id]:
            raise StageOContractError("objective_drift", f"{case.id} objective drifted")
        if case.expected.final_status != "VERIFIED" or case.expected.final_failure_code is not None:
            raise StageOContractError("expected_outcome_drift", f"{case.id} must expect VERIFIED")
    for case in negatives:
        expected_failure = EXPECTED_NEGATIVE_FAILURES[case.id]
        if (
            case.expected.final_status != "BLOCKED"
            or case.expected.final_failure_code != expected_failure
            or expected_failure not in STAGE_O_FAILURE_CODES
        ):
            raise StageOContractError("expected_outcome_drift", f"{case.id} blocker drifted")

    by_id = {case.id: case for case in all_cases}
    sequential_ids = {
        "o-two-gap-presentation-then-reduction",
        "o-two-gap-checker-then-membership",
    }
    if any(by_id[case_id].stage_o["maximum_gap_count"] != 2 for case_id in sequential_ids):
        raise StageOContractError("gap_contract_drift", "both sequential positives must freeze two gaps")
    if any(by_id[case_id].execution_layer != "optional_authoring" for case_id in sequential_ids):
        raise StageOContractError("gap_contract_drift", "sequential positives must use Optional Authoring")
    if by_id["o-capability-producer"].stage_o["promotion_role"] != "producer":
        raise StageOContractError("promotion_contract_drift", "producer role drifted")
    if by_id["o-capability-consumer"].stage_o["promotion_role"] != "consumer":
        raise StageOContractError("promotion_contract_drift", "consumer role drifted")
    if by_id["o-capability-consumer"].authoring_policy != {"enabled": False, "mode": "disabled"}:
        raise StageOContractError("promotion_contract_drift", "consumer must freeze zero authoring")
    ablations = [case.id for case in positives if case.stage_o["ablation_required"] is True]
    if ablations != ["o-core-ambiguous-fixed-target", "o-core-ambiguous-auto-target"]:
        raise StageOContractError("ablation_contract_drift", "Stage O must freeze exactly two ablations")
    competitive = [
        case
        for case in positives
        if case.stage_o["minimum_locally_valid_candidates"] >= 2
    ]
    if len(competitive) < 4:
        raise StageOContractError("competitive_choice_not_real", "fewer than four positives require two local candidates")
    candidate_range_cases = [
        case for case in positives if case.stage_o["candidate_count_range"] == [3, 8]
    ]
    if len(candidate_range_cases) < 6:
        raise StageOContractError("competitive_choice_not_real", "fewer than six positives freeze 3..8 candidates")
    parameter_case = by_id["o-parameterized-predicate-membership"]
    if parameter_case.input_kind != "parameterized_predicate" or not parameter_case.stage_o[
        "resolved_parameters"
    ]:
        raise StageOContractError("parameterized_input_unresolved", "parameter case has no resolved parameter")
    if by_id["o-predicate-adapter-route"].input_kind != "predicate":
        raise StageOContractError("presentation_adapter_not_lean_confirmed", "predicate adapter input drifted")

    family_counts = Counter(str(case.coverage.get("family")) for case in all_cases)
    if not {"graph", "clause_csp", "set_system", "numeric_path"}.issubset(family_counts):
        raise StageOContractError("coverage_drift", "Stage O no longer covers four families")
    return tuple(all_cases)


@dataclass(frozen=True)
class StageOCandidateMetadata:
    candidate_kind: str
    input_endpoint_id: str
    output_endpoint_id: str
    direction: str
    capability_kind: str
    preconditions: tuple[str, ...]
    dependencies: tuple[str, ...]
    compiler_role: str
    visibility: str
    allowed_imports: tuple[str, ...]
    declared_axioms: tuple[str, ...]
    route_segments: tuple[tuple[str, str], ...]
    candidate_source_hash: str
    bound_dependency_hash: str
    producer: str = "stage_o_contract_candidate_builder"
    schema_version: str = STAGE_O_CANDIDATE_SCHEMA

    @property
    def packet_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def search_summary(self) -> dict[str, Any]:
        return {
            "packet_id": self.packet_id,
            "candidate_kind": self.candidate_kind,
            "input_endpoint_id": self.input_endpoint_id,
            "output_endpoint_id": self.output_endpoint_id,
            "direction": self.direction,
            "capability_kind": self.capability_kind,
            "compiler_role": self.compiler_role,
        }

    def inspect_view(self) -> dict[str, Any]:
        return {
            **self.search_summary(),
            "preconditions": list(self.preconditions),
            "dependencies": list(self.dependencies),
            "visibility": self.visibility,
            "allowed_imports": list(self.allowed_imports),
            "declared_axioms": list(self.declared_axioms),
            "route_segments": [list(segment) for segment in self.route_segments],
            "candidate_source_hash": self.candidate_source_hash,
            "bound_dependency_hash": self.bound_dependency_hash,
        }


@dataclass(frozen=True)
class StageOCandidateSet:
    goal_input_endpoint_id: str
    goal_output_endpoint_id: str
    required_direction: str
    required_capability_kind: str
    available_dependencies: tuple[str, ...]
    registry_fingerprint: str
    candidates: tuple[StageOCandidateMetadata, ...]
    producer: str = "stage_o_contract_candidate_builder"
    schema_version: str = STAGE_O_CANDIDATE_SET_SCHEMA

    @property
    def candidate_set_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "goal_input_endpoint_id": self.goal_input_endpoint_id,
                "goal_output_endpoint_id": self.goal_output_endpoint_id,
                "required_direction": self.required_direction,
                "required_capability_kind": self.required_capability_kind,
                "available_dependencies": list(self.available_dependencies),
                "registry_fingerprint": self.registry_fingerprint,
                "packet_ids": [candidate.packet_id for candidate in self.candidates],
                "producer": self.producer,
            }
        )

    @property
    def session_id(self) -> str:
        return sha256_id(
            {
                "schema_version": "hardness_stage_o_contract_session_v1",
                "candidate_set_id": self.candidate_set_id,
            }
        )

    def candidate(self, packet_id: str) -> StageOCandidateMetadata:
        for candidate in self.candidates:
            if candidate.packet_id == packet_id:
                return candidate
        raise StageOContractError("unknown_packet", "selected packet was not retrieved")


def locally_valid_candidate(candidate: StageOCandidateMetadata, candidate_set: StageOCandidateSet) -> bool:
    return bool(
        candidate.schema_version == STAGE_O_CANDIDATE_SCHEMA
        and candidate.candidate_kind in CANDIDATE_KINDS
        and candidate.input_endpoint_id == candidate_set.goal_input_endpoint_id
        and candidate.output_endpoint_id == candidate_set.goal_output_endpoint_id
        and candidate.direction == candidate_set.required_direction
        and candidate.capability_kind == candidate_set.required_capability_kind
    )


def candidate_rejection_reasons(
    candidate: StageOCandidateMetadata, candidate_set: StageOCandidateSet
) -> tuple[str, ...]:
    reasons: list[str] = []
    if candidate.schema_version != STAGE_O_CANDIDATE_SCHEMA or candidate.candidate_kind not in CANDIDATE_KINDS:
        reasons.append("unsupported_checker_or_tm_packet")
    if candidate.input_endpoint_id != candidate_set.goal_input_endpoint_id or candidate.output_endpoint_id != candidate_set.goal_output_endpoint_id:
        reasons.append("wrong_endpoint")
    if candidate.direction != candidate_set.required_direction:
        reasons.append("wrong_direction")
    if candidate.capability_kind != candidate_set.required_capability_kind:
        reasons.append("unsupported_checker_or_tm_packet")
    if "self" in candidate.preconditions or "self" in candidate.dependencies:
        reasons.append("certificate_dag_cycle")
    available = set(candidate_set.available_dependencies)
    if not set(candidate.preconditions).issubset(available) or not set(candidate.dependencies).issubset(available):
        reasons.append("packet_precondition_unsatisfied")
    if candidate.visibility == "job_local_unpublished":
        reasons.append("unpublished_candidate_visible")
    if candidate.visibility not in VISIBILITIES:
        reasons.append("capability_promotion_failed")
    if any(marker in value for value in candidate.allowed_imports for marker in ORACLE_MARKERS):
        reasons.append("oracle_or_nonstandard_axiom")
    if set(candidate.declared_axioms) & FORBIDDEN_AXIOMS or candidate.declared_axioms:
        reasons.append("oracle_or_nonstandard_axiom")
    if candidate.candidate_source_hash != candidate.bound_dependency_hash:
        reasons.append("stale_gap_dependency")
    segments = candidate.route_segments
    if segments:
        connected = (
            segments[0][0] == candidate_set.goal_input_endpoint_id
            and segments[-1][1] == candidate_set.goal_output_endpoint_id
            and all(left[1] == right[0] for left, right in zip(segments, segments[1:]))
        )
        if not connected:
            reasons.append("global_route_disconnected")
    return tuple(dict.fromkeys(reasons))


def globally_valid_candidate(candidate: StageOCandidateMetadata, candidate_set: StageOCandidateSet) -> bool:
    return not candidate_rejection_reasons(candidate, candidate_set)


def inspect_packet(
    candidate_set: StageOCandidateSet,
    packet_id: str,
    *,
    retrieved_packet_ids: Iterable[str],
    already_inspected: Iterable[str] = (),
) -> dict[str, Any]:
    retrieved = set(retrieved_packet_ids)
    inspected = set(already_inspected)
    if packet_id not in retrieved:
        raise StageOContractError("unknown_packet", "inspect_packet requires a retrieved ID")
    if packet_id not in inspected and len(inspected) >= STAGE_O_INSPECT_LIMIT:
        raise StageOContractError("inspect_budget_exhausted", "at most three packets may be inspected")
    return candidate_set.candidate(packet_id).inspect_view()


@dataclass(frozen=True)
class StageOAction:
    action: str
    session_id: str
    packet_id: str | None = None
    candidate_kind: str | None = None
    typed_bindings: Mapping[str, str] = field(default_factory=dict)
    dependencies: tuple[str, ...] = ()
    explanation: str = ""
    checked_packet_ids: tuple[str, ...] = ()
    missing_conditions: tuple[str, ...] = ()
    schema_version: str = STAGE_O_ACTION_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "action": self.action,
            "session_id": self.session_id,
            "packet_id": self.packet_id,
            "candidate_kind": self.candidate_kind,
            "typed_bindings": dict(self.typed_bindings),
            "dependencies": list(self.dependencies),
            "explanation": self.explanation,
            "checked_packet_ids": list(self.checked_packet_ids),
            "missing_conditions": list(self.missing_conditions),
        }


def parse_stage_o_action(content: str, *, candidate_set: StageOCandidateSet) -> StageOAction:
    payload = extract_json_object(content)
    if not isinstance(payload, Mapping):
        raise StageOContractError("invalid_model_json", "model response is not one JSON object")
    if payload.get("schema_version") != STAGE_O_ACTION_SCHEMA:
        raise StageOContractError("unsupported_schema", "model action schema is not Stage O v1")
    session_id = _nonempty_string(payload.get("session_id"), label="action.session_id")
    if session_id != candidate_set.session_id:
        raise StageOContractError("session_mismatch", "model action belongs to another session")
    action = _nonempty_string(payload.get("action"), label="action.action")
    explanation = _nonempty_string(payload.get("explanation"), label="action.explanation")
    if action == "inspect_packet":
        packet_id = _nonempty_string(payload.get("packet_id"), label="action.packet_id")
        candidate_set.candidate(packet_id)
        return StageOAction(
            action=action,
            session_id=session_id,
            packet_id=packet_id,
            explanation=explanation,
        )
    if action == "select_packet":
        packet_id = _nonempty_string(payload.get("packet_id"), label="action.packet_id")
        candidate = candidate_set.candidate(packet_id)
        candidate_kind = _nonempty_string(payload.get("candidate_kind"), label="action.candidate_kind")
        if candidate_kind != candidate.candidate_kind:
            raise StageOContractError("packet_binding_mismatch", "candidate kind changed in selection")
        bindings = payload.get("typed_bindings")
        if not isinstance(bindings, Mapping) or set(bindings) != {
            "input_endpoint_id",
            "output_endpoint_id",
            "direction",
            "capability_kind",
        }:
            raise StageOContractError("packet_binding_mismatch", "typed bindings have the wrong shape")
        normalized_bindings = {
            key: _nonempty_string(bindings.get(key), label=f"action.typed_bindings.{key}")
            for key in bindings
        }
        expected_bindings = {
            "input_endpoint_id": candidate.input_endpoint_id,
            "output_endpoint_id": candidate.output_endpoint_id,
            "direction": candidate.direction,
            "capability_kind": candidate.capability_kind,
        }
        if normalized_bindings != expected_bindings:
            raise StageOContractError("packet_binding_mismatch", "model mutated immutable packet bindings")
        dependencies = _string_tuple(payload.get("dependencies", []), label="action.dependencies")
        if dependencies != candidate.dependencies:
            raise StageOContractError("packet_binding_mismatch", "model mutated packet dependencies")
        return StageOAction(
            action=action,
            session_id=session_id,
            packet_id=packet_id,
            candidate_kind=candidate_kind,
            typed_bindings=normalized_bindings,
            dependencies=dependencies,
            explanation=explanation,
        )
    if action == "stop_authoring":
        checked = _string_tuple(
            payload.get("checked_packet_ids", []),
            label="action.checked_packet_ids",
            allow_empty=False,
        )
        known = {candidate.packet_id for candidate in candidate_set.candidates}
        if not set(checked).issubset(known):
            raise StageOContractError("unknown_packet", "stop action cites an unretrieved packet")
        missing = _string_tuple(
            payload.get("missing_conditions", []),
            label="action.missing_conditions",
            allow_empty=False,
        )
        return StageOAction(
            action=action,
            session_id=session_id,
            explanation=explanation,
            checked_packet_ids=checked,
            missing_conditions=missing,
        )
    raise StageOContractError("unsupported_action", f"unsupported Stage O action {action}")


def validate_stage_o_terminal_action(
    action: StageOAction, *, candidate_set: StageOCandidateSet
) -> None:
    valid_packets = {
        candidate.packet_id
        for candidate in candidate_set.candidates
        if globally_valid_candidate(candidate, candidate_set)
    }
    if action.action == "select_packet":
        if action.packet_id not in valid_packets:
            candidate = candidate_set.candidate(action.packet_id or "")
            reasons = candidate_rejection_reasons(candidate, candidate_set)
            raise StageOContractError(
                reasons[0] if reasons else "packet_precondition_unsatisfied",
                "model selected a packet rejected by the frozen public contract",
            )
        return
    if action.action == "stop_authoring":
        if valid_packets:
            raise StageOContractError(
                "model_stopped_with_valid_candidate",
                "model stopped even though a public globally valid candidate exists",
            )
        return
    raise StageOContractError("nonterminal_action", "contract qualification requires a terminal action")


def _goal_capability_kind(objective: str) -> str:
    if objective in {"reduce_to", "reduce_to_known_np", "reduce_to_known_hardness"}:
        return "ComplexityReduction.Certificate.CertifiedReduction"
    if objective == "prove_in_np":
        return "ComplexityReduction.Certificate.NativeTMInNP"
    if objective == "prove_np_complete":
        return "ComplexityReduction.Certificate.NativeTMNPComplete"
    raise StageOContractError("unsupported_objective", f"unsupported Stage O objective {objective}")


def _candidate_kind(case: BenchmarkCase) -> str:
    role = str(case.stage_o["protocol_role"])
    if role in {"parameterized_membership", "capability_consumer"}:
        return "membership_packet"
    if role in {"sequential_authoring", "capability_producer"}:
        return "gadget_packet"
    return "route_packet"


def build_contract_candidate_set(case: BenchmarkCase) -> StageOCandidateSet:
    """Build an answer-free synthetic packet set used only for O-A ABI qualification."""

    goal_input = sha256_id(
        {
            "schema_version": "hardness_stage_o_prompt_endpoint_v1",
            "declaration": case.effective_input_declaration,
        }
    )
    output_name = case.target or f"objective:{case.objective}:exact-source"
    goal_output = sha256_id(
        {
            "schema_version": "hardness_stage_o_prompt_endpoint_v1",
            "declaration": output_name,
        }
    )
    direction = "identity" if case.objective in {"prove_in_np", "prove_np_complete"} else "source_to_target"
    capability_kind = _goal_capability_kind(case.objective)
    packet_kind = _candidate_kind(case)
    registry = sha256_id(
        {
            "schema_version": "hardness_stage_o_contract_registry_v1",
            "module": case.module,
            "input": case.effective_input_declaration,
        }
    )
    source_hash = sha256_id(
        {
            "schema_version": "hardness_stage_o_contract_source_v1",
            "input": case.effective_input_declaration,
            "objective": case.objective,
        }
    )
    available = ("dep:core", "dep:input-gate", "dep:standard-axioms")
    middle = sha256_id(
        {
            "schema_version": "hardness_stage_o_contract_middle_v1",
            "input": goal_input,
            "output": goal_output,
        }
    )

    base = StageOCandidateMetadata(
        candidate_kind=packet_kind,
        input_endpoint_id=goal_input,
        output_endpoint_id=goal_output,
        direction=direction,
        capability_kind=capability_kind,
        preconditions=("dep:core", "dep:input-gate"),
        dependencies=("dep:standard-axioms",),
        compiler_role="global_composition",
        visibility="base_registry",
        allowed_imports=("ComplexityReduction.Agent.Hardness.Runtime",),
        declared_axioms=(),
        route_segments=((goal_input, middle), (middle, goal_output)),
        candidate_source_hash=source_hash,
        bound_dependency_hash=source_hash,
    )
    alternative = replace(
        base,
        compiler_role="locally_valid_missing_dependency",
        dependencies=("dep:not-published",),
        route_segments=((goal_input, goal_output),),
    )
    wrong_direction = replace(
        base,
        direction="identity" if direction == "source_to_target" else "source_to_target",
        compiler_role="wrong_direction_decoy",
    )
    wrong_endpoint = replace(
        base,
        output_endpoint_id=middle,
        compiler_role="wrong_endpoint_decoy",
        route_segments=((goal_input, middle),),
    )
    candidates = (base, alternative, wrong_direction, wrong_endpoint)

    profile = str(case.stage_o["contract_probe_profile"])
    if profile == "cycle":
        candidates = tuple(replace(base, preconditions=("self",), compiler_role=f"cycle_{index}") for index in range(3))
    elif profile == "missing_precondition":
        candidates = tuple(replace(base, dependencies=(f"dep:missing-{index}",), compiler_role=f"missing_precondition_{index}") for index in range(3))
    elif profile == "wrong_direction":
        reversed_direction = "identity" if direction == "source_to_target" else "source_to_target"
        candidates = tuple(replace(base, direction=reversed_direction, compiler_role=f"wrong_direction_{index}") for index in range(3))
    elif profile == "disconnected":
        candidates = tuple(
            replace(
                base,
                route_segments=((goal_input, middle), (goal_input, goal_output)),
                compiler_role=f"disconnected_{index}",
            )
            for index in range(3)
        )
    elif profile == "unsupported_checker":
        candidates = tuple(
            replace(
                base,
                capability_kind="ComplexityReduction.Certificate.UnsupportedChecker",
                compiler_role=f"unsupported_checker_{index}",
            )
            for index in range(3)
        )
    elif profile == "stale_dependency":
        candidates = tuple(
            replace(
                base,
                bound_dependency_hash=sha256_id({"stale": index}),
                compiler_role=f"stale_dependency_{index}",
            )
            for index in range(3)
        )
    elif profile == "unpublished":
        candidates = tuple(
            replace(base, visibility="job_local_unpublished", compiler_role=f"unpublished_{index}")
            for index in range(3)
        )
    elif profile == "oracle_or_axiom":
        candidates = tuple(
            replace(
                base,
                allowed_imports=("Benchmark.Hardness.Oracles.Gold.Answer",),
                declared_axioms=("sorryAx",),
                compiler_role=f"quarantined_{index}",
            )
            for index in range(3)
        )

    candidate_set = StageOCandidateSet(
        goal_input_endpoint_id=goal_input,
        goal_output_endpoint_id=goal_output,
        required_direction=direction,
        required_capability_kind=capability_kind,
        available_dependencies=available,
        registry_fingerprint=registry,
        candidates=tuple(sorted(candidates, key=lambda candidate: candidate.packet_id)),
    )
    if not STAGE_O_CANDIDATE_MIN <= len(candidate_set.candidates) <= STAGE_O_CANDIDATE_MAX:
        raise StageOContractError("competitive_choice_not_real", "contract candidate count is outside 3..8")
    return candidate_set


def build_stage_o_contract_prompt(
    *,
    candidate_set: StageOCandidateSet,
    inspected_packet_ids: Sequence[str],
    previous_rejection: str | None = None,
    remaining_model_turns: int | None = None,
) -> str:
    inspected = tuple(dict.fromkeys(inspected_packet_ids))
    if len(inspected) > STAGE_O_INSPECT_LIMIT:
        raise StageOContractError("inspect_budget_exhausted", "prompt may include at most three inspections")
    retrieved = {candidate.packet_id for candidate in candidate_set.candidates}
    inspected_views = [
        inspect_packet(
            candidate_set,
            packet_id,
            retrieved_packet_ids=retrieved,
            already_inspected=inspected[:index],
        )
        for index, packet_id in enumerate(inspected)
    ]
    return_actions: dict[str, Any] = {
        "select_packet": {
            "schema_version": STAGE_O_ACTION_SCHEMA,
            "action": "select_packet",
            "session_id": candidate_set.session_id,
            "packet_id": "<retrieved packet_id>",
            "candidate_kind": "<same candidate_kind>",
            "typed_bindings": {
                "input_endpoint_id": "<same input endpoint>",
                "output_endpoint_id": "<same output endpoint>",
                "direction": "<same direction>",
                "capability_kind": "<same capability kind>",
            },
            "dependencies": ["<same public dependency IDs>"],
            "explanation": "<brief public-contract reason>",
        },
        "stop_authoring": {
            "schema_version": STAGE_O_ACTION_SCHEMA,
            "action": "stop_authoring",
            "session_id": candidate_set.session_id,
            "checked_packet_ids": ["<retrieved packet_id>"],
            "missing_conditions": ["<specific public missing condition>"],
            "explanation": "<brief public-contract reason>",
        },
    }
    if remaining_model_turns is not None and remaining_model_turns < 1:
        raise StageOContractError("invalid_schema", "remaining model turns must be positive")
    inspection_remaining = STAGE_O_INSPECT_LIMIT - len(inspected)
    may_inspect = inspection_remaining > 0 and (
        remaining_model_turns is None or remaining_model_turns > 1
    )
    if may_inspect:
        return_actions = {
            "inspect_packet": {
                "schema_version": STAGE_O_ACTION_SCHEMA,
                "action": "inspect_packet",
                "session_id": candidate_set.session_id,
                "packet_id": "<retrieved packet_id not yet inspected>",
                "explanation": "<brief reason this packet needs bounded inspection>",
            },
            **return_actions,
        }
    payload = {
        "schema_version": STAGE_O_PROMPT_SCHEMA,
        "session_id": candidate_set.session_id,
        "goal": {
            "input_endpoint_id": candidate_set.goal_input_endpoint_id,
            "output_endpoint_id": candidate_set.goal_output_endpoint_id,
            "direction": candidate_set.required_direction,
            "capability_kind": candidate_set.required_capability_kind,
            "available_dependencies": list(candidate_set.available_dependencies),
            "registry_fingerprint": candidate_set.registry_fingerprint,
        },
        "search_results": [candidate.search_summary() for candidate in candidate_set.candidates],
        "inspected_packets": inspected_views,
        "limits": {
            "candidate_count_min": STAGE_O_CANDIDATE_MIN,
            "candidate_count_max": STAGE_O_CANDIDATE_MAX,
            "inspect_packet_max": STAGE_O_INSPECT_LIMIT,
            "inspect_packet_remaining": inspection_remaining,
            "select_packet_max": 1,
            "remaining_model_turns": remaining_model_turns,
            "must_terminate_this_turn": remaining_model_turns == 1,
        },
        "validation_rules": [
            "A precondition or dependency equal to self is a certificate-DAG cycle and requires stop_authoring.",
            "Every precondition and dependency must be listed in goal.available_dependencies.",
            "visibility=job_local_unpublished is not selectable across case boundaries.",
            "candidate_source_hash must exactly equal bound_dependency_hash.",
            "Route segments must start at the goal input, connect consecutively, and end at the goal output.",
            "Any oracle/quarantined import or any declared axiom requires stop_authoring.",
            "Do not treat endpoint/head/type agreement as sufficient when any global rule fails.",
        ],
        "return_one_of": return_actions,
    }
    if previous_rejection:
        payload["previous_rejection"] = previous_rejection
    audit_stage_o_prompt(payload)
    return json.dumps(payload, ensure_ascii=True, sort_keys=True)


SEQUENTIAL_STATES = (
    "CORE_BASELINE_BLOCKED",
    "AUTHORING_GAP_1",
    "GAP_1_BUNDLE_VALIDATED",
    "GAP_1_CASE_LOCAL_PUBLISHED",
    "FRESH_CORE_RESOLVE_1",
    "CORE_BLOCKED_GAP_2",
    "AUTHORING_GAP_2",
    "GAP_2_BUNDLE_VALIDATED",
    "FRESH_CORE_RESOLVE_2",
    "CORE_VERIFIED",
    "FINAL_COMBINED_LEAN",
    "RELEASE_REPLAY",
)
SEQUENTIAL_TRANSITIONS = dict(zip(SEQUENTIAL_STATES, SEQUENTIAL_STATES[1:]))


@dataclass(frozen=True)
class SequentialAuthoringTrace:
    request_id: str
    states: tuple[str, ...] = ("CORE_BASELINE_BLOCKED",)
    gap_ids: tuple[str, ...] = ()

    def advance(self, next_state: str, *, gap_id: str | None = None) -> "SequentialAuthoringTrace":
        current = self.states[-1]
        expected = SEQUENTIAL_TRANSITIONS.get(current)
        if next_state != expected:
            raise StageOContractError(
                "gap_sequence_mismatch", f"cannot transition from {current} to {next_state}"
            )
        gap_ids = self.gap_ids
        if next_state in {"AUTHORING_GAP_1", "AUTHORING_GAP_2"}:
            if not gap_id or not SHA256_RE.fullmatch(gap_id):
                raise StageOContractError("gap_sequence_mismatch", "authoring state requires a stable gap ID")
            if gap_id in gap_ids:
                raise StageOContractError("gap_sequence_mismatch", "the second gap repeats a previous gap ID")
            gap_ids = (*gap_ids, gap_id)
        elif gap_id is not None:
            raise StageOContractError("gap_sequence_mismatch", "only authoring transitions accept a gap ID")
        return replace(self, states=(*self.states, next_state), gap_ids=gap_ids)

    @property
    def complete(self) -> bool:
        return self.states[-1] == "RELEASE_REPLAY" and len(self.gap_ids) == 2


def stable_gap_id(
    *,
    request_id: str,
    ordinal: int,
    registry_fingerprint: str,
    source_endpoint_id: str,
    target_endpoint_id: str,
    capability_head: str,
    dependency_hash: str,
) -> str:
    if ordinal not in {1, 2}:
        raise StageOContractError("gap_sequence_mismatch", "Stage O supports only gap ordinals 1 and 2")
    return sha256_id(
        {
            "schema_version": "hardness_stage_o_gap_v1",
            "request_id": request_id,
            "ordinal": ordinal,
            "registry_fingerprint": registry_fingerprint,
            "source_endpoint_id": source_endpoint_id,
            "target_endpoint_id": target_endpoint_id,
            "capability_head": capability_head,
            "dependency_hash": dependency_hash,
        }
    )


@dataclass(frozen=True)
class CapabilityPromotionManifest:
    toolchain: str
    lake_manifest_sha256: str
    base_registry_fingerprint: str
    source_sha256: str
    dependency_sha256: tuple[str, ...]
    declaration: str
    source_endpoint_id: str
    target_endpoint_id: str
    direction: str
    capability_head: str
    axiom_audit_sha256: str
    candidate_sha256: str
    bundle_sha256: str
    final_request_precheck_sha256: str
    producer_run_id: str
    schema_version: str = STAGE_O_PROMOTION_SCHEMA

    @property
    def capability_hash(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def validate(self) -> None:
        if self.schema_version != STAGE_O_PROMOTION_SCHEMA:
            raise StageOContractError("capability_promotion_failed", "unsupported promotion schema")
        if self.direction not in DIRECTIONS:
            raise StageOContractError("capability_promotion_failed", "promotion direction is invalid")
        hashes = (
            self.lake_manifest_sha256,
            self.base_registry_fingerprint,
            self.source_sha256,
            *self.dependency_sha256,
            self.axiom_audit_sha256,
            self.candidate_sha256,
            self.bundle_sha256,
            self.final_request_precheck_sha256,
        )
        if not all(SHA256_RE.fullmatch(value) for value in hashes):
            raise StageOContractError("capability_promotion_failed", "promotion manifest has an invalid hash")
        for label, value in {
            "toolchain": self.toolchain,
            "declaration": self.declaration,
            "source_endpoint_id": self.source_endpoint_id,
            "target_endpoint_id": self.target_endpoint_id,
            "capability_head": self.capability_head,
            "producer_run_id": self.producer_run_id,
        }.items():
            _nonempty_string(value, label=f"promotion.{label}")


@dataclass(frozen=True)
class LeanValidationCacheKey:
    toolchain: str
    lake_manifest_sha256: str
    base_registry_fingerprint: str
    complete_source_sha256: str
    dependency_sha256: tuple[str, ...]
    namespace: str
    editable_allowlist: tuple[str, ...]
    validation_profile: str
    schema_version: str = STAGE_O_CACHE_KEY_SCHEMA

    @property
    def cache_key(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def validate(self) -> None:
        if self.schema_version != STAGE_O_CACHE_KEY_SCHEMA:
            raise StageOContractError("lean_cache_key_incomplete", "unsupported Lean cache-key schema")
        required_hashes = (
            self.lake_manifest_sha256,
            self.base_registry_fingerprint,
            self.complete_source_sha256,
            *self.dependency_sha256,
        )
        if not required_hashes or not all(SHA256_RE.fullmatch(value) for value in required_hashes):
            raise StageOContractError("lean_cache_key_incomplete", "Lean cache key omits a content hash")
        if not self.editable_allowlist:
            raise StageOContractError("lean_cache_key_incomplete", "Lean cache key omits the editable allowlist")
        for label, value in {
            "toolchain": self.toolchain,
            "namespace": self.namespace,
            "validation_profile": self.validation_profile,
        }.items():
            _nonempty_string(value, label=f"lean_cache_key.{label}")


def validate_lean_service_microbenchmark(value: Mapping[str, Any]) -> None:
    required = {
        "schema_version",
        "benchmark_id",
        "repeat_count",
        "command_profile",
        "cache_key_fields",
        "isolation_checks",
        "gates",
    }
    if set(value) != required or value.get("schema_version") != STAGE_O_MICROBENCHMARK_SCHEMA:
        raise StageOContractError("invalid_schema", "Lean service microbenchmark schema drifted")
    if value.get("repeat_count") != 20:
        raise StageOContractError("invalid_schema", "Lean microbenchmark must run exactly 20 repeats")
    cache_fields = _string_tuple(value.get("cache_key_fields"), label="microbenchmark.cache_key_fields")
    expected_fields = {
        "toolchain",
        "lake_manifest",
        "base_registry_fingerprint",
        "complete_source_hash",
        "dependency_hash",
        "namespace",
        "editable_allowlist",
        "validation_profile",
    }
    if set(cache_fields) != expected_fields:
        raise StageOContractError("lean_cache_key_incomplete", "microbenchmark cache fields drifted")
    checks = _string_tuple(value.get("isolation_checks"), label="microbenchmark.isolation_checks")
    if set(checks) != {
        "session_ownership",
        "namespace_isolation",
        "dependency_invalidation",
        "candidate_invalidation",
        "registry_invalidation",
        "stale_olean_rejection",
        "service_restart",
    }:
        raise StageOContractError("invalid_schema", "Lean isolation checks drifted")
    gates = value.get("gates")
    if not isinstance(gates, Mapping) or gates != {
        "warm_p50_over_cold_p50_max": 0.5,
        "cache_invalidation_rate_min": 1.0,
        "namespace_isolation_rate_min": 1.0,
        "stale_olean_rejection_rate_min": 1.0,
    }:
        raise StageOContractError("invalid_schema", "Lean microbenchmark gates drifted")


def stage_o_report_skeleton(*, offline: bool, contract_only: bool = False) -> dict[str, Any]:
    schema = (
        STAGE_O_CONTRACT_REPORT_SCHEMA
        if contract_only
        else (STAGE_O_OFFLINE_REPORT_SCHEMA if offline else STAGE_O_REPORT_SCHEMA)
    )
    return {
        "schema_version": schema,
        "stage": "O-A" if contract_only else "O",
        "status": "RUNNING",
        "published": False,
        "benchmark": {},
        "model": {},
        "parallel_execution": {},
        "execution_layers": {
            "input_gate": {},
            "core_reuse": {},
            "optional_authoring": {},
            "lean_validation_service": {},
            "final_combined_lean": {},
            "release_replay": {},
        },
        "cases": [],
        "ablation_replays": [],
        "promotion_waves": [],
        "artifacts": [],
        "metrics": {
            "competitive_choice_case_count": 0,
            "locally_valid_candidate_count": 0,
            "unique_candidate_before_model_rate": 0.0,
            "model_choice_preserved_rate": 0.0,
            "alternative_route_recovery_rate": 0.0,
            "ablation_typed_blocker_accuracy": 0.0,
            "sequential_two_gap_closure_rate": 0.0,
            "gap1_to_gap2_fresh_resolve_rate": 0.0,
            "stale_gap_dependency_rejection_rate": 0.0,
            "capability_promotion_acceptance_rate": 0.0,
            "published_capability_reuse_rate": 0.0,
            "consumer_zero_authoring_rate": 0.0,
        },
        "summary": {},
        "failures": [],
    }


def stability_aggregate_skeleton() -> dict[str, Any]:
    return {
        "schema_version": STAGE_O_STABILITY_AGGREGATE_SCHEMA,
        "stage": "O",
        "status": "RUNNING",
        "run_reports": [],
        "outcome_matrix": {},
        "typed_gap_sequences": {},
        "reuse": {},
        "ablations": {},
        "route_packet_choice_distribution": {},
        "artifact_hash_distribution": {},
        "lean_release_replay": {},
        "summary": {},
    }


def load_lean_service_microbenchmark(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StageOContractError("invalid_schema", f"cannot read Lean microbenchmark: {error}") from error
    if not isinstance(value, Mapping):
        raise StageOContractError("invalid_schema", "Lean microbenchmark must be one object")
    copied = _json_copy(value, label="lean_service_microbenchmark")
    validate_lean_service_microbenchmark(copied)
    return copied
