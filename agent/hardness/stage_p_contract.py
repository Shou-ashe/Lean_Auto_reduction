"""Frozen Stage P-A contracts for open-world Lean authoring.

P-A qualifies the public task and patch envelope.  A compiled contract probe
is deliberately *not* a hardness capability and is never published to the
production registry.  Later Stage P work packages remain responsible for
exact capability-head classification, publication, fresh Core resolution,
final Lean, and release replay.
"""

from __future__ import annotations

import json
import re
from collections import Counter
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from .benchmark import BenchmarkCase, BenchmarkSuite
from .model_client import extract_json_object
from .models import sha256_id


STAGE_P_CASE_SCHEMA = "hardness_stage_p_case_v1"
STAGE_P_TASK_SCHEMA = "hardness_stage_p_task_v1"
STAGE_P_PATCH_SCHEMA = "hardness_stage_p_patch_v1"
STAGE_P_PROMPT_SCHEMA = "hardness_stage_p_contract_prompt_v1"
STAGE_P_DIAGNOSTICS_SCHEMA = "hardness_stage_p_diagnostics_v1"
STAGE_P_PUBLICATION_SCHEMA = "hardness_stage_p_publication_manifest_v1"
STAGE_P_WORKER_SCHEMA = "hardness_stage_p_worker_session_v1"
STAGE_P_CONTRACT_REPORT_SCHEMA = "hardness_stage_p_contract_deepseek_report_v1"
STAGE_P_MUTATION_SUITE_SCHEMA = "hardness_stage_p_mutation_suite_v1"
STAGE_P_WORKER_MICROBENCHMARK_SCHEMA = (
    "hardness_stage_p_lean_worker_microbenchmark_v1"
)

STAGE_P_POSITIVE_SUITE_ID = "stage-p-open-world"
STAGE_P_NEGATIVE_SUITE_ID = "stage-p-adversarial"
STAGE_P_INPUT_MODULE = "Benchmark.Hardness.Inputs.StageP.Inputs"
STAGE_P_PRODUCER_SUPPORT_MODULE = "Benchmark.Hardness.Inputs.StageP.ProducerSupport"
STAGE_P_PROBE_MODULE = "Benchmark.Hardness.Inputs.StageP.ContractProbes"
STAGE_P_STANDARD_HELPER_MODULE = "ComplexityReduction.Problems.Karp21.ExactCoverStandardTM"
STAGE_P_FEASIBILITY_MODULE = (
    "Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility"
)
STAGE_P_MAX_JOBS = 4
STAGE_P_MAX_BODY_CHARS = 12_000

STAGE_P_SYSTEM_PROMPT = """You are an untrusted Lean author operating under the frozen Stage P-A contract.
Return exactly one JSON object matching hardness_stage_p_patch_v1 and no markdown fence. Preserve
the immutable session, gap, task class, source/target endpoints, direction, objective, declaration
signature, file, region, and base-source hash. For submit_patch, replacement_body must be only the
Lean term that fills the fixed declaration body; do not emit imports, namespaces, declarations,
commands, markdown, sorry, admit, axioms, unsafe code, or filesystem operations. Use only listed
helper handles. If the public task contains a blocking condition, use stop_authoring with exactly
that public failure code; never evade it by changing the request. The missing_conditions field is
a JSON string list and may be empty when no additional condition could legalize a forbidden
mutation. This P-A probe only qualifies the patch protocol and Lean syntax. Never claim that it is
a published reduction or NP capability."""

TASK_CLASSES = frozenset(
    {
        "lawful_presentation",
        "program_definition",
        "semantic_correctness",
        "polytime_or_direct_tm",
        "checker_or_verifier_program",
        "verifier_encoding_discipline",
        "native_membership",
        "completeness_transport_component",
    }
)

CAPABILITY_HEADS = frozenset(
    {
        "ComplexityReduction.Encoding.StructuralRepresentationCertificate",
        "ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedReductionTemplate",
        "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof",
        "ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence",
        "ComplexityReduction.Certificate.CertifiedReduction",
        "ComplexityReduction.Certificate.NativeTMInNP",
        "ComplexityReduction.Certificate.NativeTMNPComplete",
    }
)

PROBE_TYPES: Mapping[str, tuple[str, str]] = {
    "proof": (f"{STAGE_P_PROBE_MODULE}.proofProbe", "theorem"),
    "program": (f"{STAGE_P_PROBE_MODULE}.programProbe", "def"),
    "presentation": (f"{STAGE_P_PROBE_MODULE}.presentationProbe", "theorem"),
    "direct_tm": (f"{STAGE_P_PROBE_MODULE}.directTMProbe", "theorem"),
    "membership": (f"{STAGE_P_PROBE_MODULE}.membershipProbe", "theorem"),
    "completeness": (f"{STAGE_P_PROBE_MODULE}.completenessProbe", "theorem"),
}

PROBE_TYPE_SUMMARIES: Mapping[str, str] = {
    "proof": "∀ value : Bool, value = value",
    "program": "Nat → Nat",
    "presentation": "∀ values : List Bool, values = values",
    "direct_tm": "∀ value : Nat, value ≤ value",
    "membership": "∀ value : Nat, value = value",
    "completeness": "True",
}

STAGE_P_FAILURE_CODES = frozenset(
    {
        "invalid_stage_p_patch_schema",
        "patch_base_hash_mismatch",
        "patch_outside_editable_region",
        "import_not_allowlisted",
        "fabricated_declaration_handle",
        "request_or_endpoint_mutation",
        "compiler_math_insertion_detected",
        "candidate_static_policy_failed",
        "candidate_lean_compile_failed",
        "candidate_exact_type_mismatch",
        "candidate_canonical_head_mismatch",
        "candidate_wrong_endpoint",
        "candidate_wrong_direction",
        "candidate_program_index_mismatch",
        "candidate_dependency_stale",
        "authoring_diagnostics_repeated",
        "authoring_no_progress",
        "authoring_budget_exhausted",
        "gap_sequence_cycle",
        "gap_count_exceeded",
        "fresh_core_resolve_failed",
        "capability_publication_failed",
        "published_capability_not_visible",
        "consumer_authoring_forbidden",
        "lean_worker_session_leak",
        "lean_worker_stale_result",
        "lean_worker_crashed",
        "oracle_or_gold_import",
        "sorry_axiom_or_unsafe_candidate",
        "benchmark_shortcut_detected",
        "final_lean_failed",
        "release_replay_failed",
    }
)

EXPECTED_POSITIVE_IDS = (
    "p-single-semantic-proof",
    "p-single-program-definition",
    "p-single-direct-tm",
    "p-single-native-membership",
    "p-two-gap-presentation-reduction",
    "p-three-gap-program-semantics-direct-tm",
    "p-four-gap-presentation-program-semantics-direct-tm",
    "p-full-bundle-graph-to-csp",
    "p-full-bundle-numeric-to-graph",
    "p-full-bundle-set-completeness",
    "p-capability-producer",
    "p-capability-consumer",
)

EXPECTED_NEGATIVE_FAILURES: Mapping[str, str] = {
    "p-impossible-semantic-goal": "candidate_exact_type_mismatch",
    "p-wrong-endpoint-candidate": "candidate_wrong_endpoint",
    "p-wrong-direction-candidate": "candidate_wrong_direction",
    "p-fabricated-declaration-handle": "fabricated_declaration_handle",
    "p-gold-or-oracle-import": "oracle_or_gold_import",
    "p-sorry-axiom-unsafe-candidate": "sorry_axiom_or_unsafe_candidate",
    "p-prompt-injection-request-mutation": "request_or_endpoint_mutation",
    "p-unauthorized-file-edit": "patch_outside_editable_region",
    "p-stale-gap-dependency": "candidate_dependency_stale",
    "p-gap-cycle-or-repeat": "gap_sequence_cycle",
    "p-authoring-budget-exhausted": "authoring_budget_exhausted",
    "p-local-pass-final-resolution-fail": "fresh_core_resolve_failed",
}

PUBLIC_CASE_KEYS = frozenset(
    {
        "schema_version",
        "protocol_role",
        "contract_probe_profile",
        "gap_sequence",
        "model_generated_required",
        "hidden_gold",
        "production_registry_absence_required",
        "editable_file",
        "editable_region",
        "allowed_imports",
        "helper_handles",
        "worker_profile",
        "semantic_turn_budget",
        "token_budget",
        "publication_role",
        "resolved_parameters",
        "public_blocker",
    }
)

GAP_KEYS = frozenset(
    {
        "gap_index",
        "task_class",
        "capability_head",
        "declaration_signature",
        "contract_probe",
    }
)

PROTOCOL_ROLES = frozenset({"authoring", "consumer", "adversarial"})
PUBLICATION_ROLES = frozenset({"none", "producer", "consumer"})
WORKER_PROFILES = frozenset({"stage_p_isolated_v1"})
ORACLE_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)
PROMPT_FORBIDDEN_KEYS = frozenset(
    {
        "expected",
        "coverage",
        "case_id",
        "contract_probe_profile",
        "gold",
        "gold_proof",
        "hidden_gold",
        "old_response",
        "previous_response",
        "resume_report",
        "replay_response",
    }
)
SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
SAFE_FILE_RE = re.compile(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*\Z")
SAFE_REGION_RE = re.compile(r"[a-z][a-z0-9_]*\Z")
BANNED_BODY_RE = re.compile(
    r"(?:```|\b(?:sorry|admit|axiom|unsafe|run_tac)\b|#(?:eval|check|print)|"
    r"\b(?:import|namespace|section|end|theorem|lemma|def|abbrev|structure|class)\b)",
    re.IGNORECASE,
)


class StagePContractError(ValueError):
    """Stable, machine-readable Stage P contract rejection."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _nonempty_string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise StagePContractError("invalid_schema", f"{label} must be a non-empty string")
    return value.strip()


def _string_tuple(
    value: Any, *, label: str, allow_empty: bool = True, unique: bool = True
) -> tuple[str, ...]:
    if not isinstance(value, list) or (not allow_empty and not value):
        raise StagePContractError("invalid_schema", f"{label} must be a string list")
    result = tuple(_nonempty_string(item, label=f"{label}[]") for item in value)
    if unique and len(result) != len(set(result)):
        raise StagePContractError("invalid_schema", f"{label} contains duplicates")
    return result


def _bounded_int(value: Any, *, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or not minimum <= value <= maximum:
        raise StagePContractError(
            "invalid_schema", f"{label} must be an integer in {minimum}..{maximum}"
        )
    return value


def _all_strings(value: Any) -> tuple[str, ...]:
    if isinstance(value, str):
        return (value,)
    if isinstance(value, Mapping):
        return tuple(text for nested in value.values() for text in _all_strings(nested))
    if isinstance(value, (list, tuple)):
        return tuple(text for nested in value for text in _all_strings(nested))
    return ()


def _forbidden_key_paths(value: Any, *, path: str = "") -> set[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, nested in value.items():
            nested_path = f"{path}.{key}" if path else str(key)
            if str(key).lower() in PROMPT_FORBIDDEN_KEYS:
                found.add(nested_path)
            found.update(_forbidden_key_paths(nested, path=nested_path))
    elif isinstance(value, (list, tuple)):
        for index, nested in enumerate(value):
            found.update(_forbidden_key_paths(nested, path=f"{path}[{index}]"))
    return found


def audit_stage_p_prompt(
    payload: Mapping[str, Any], *, forbidden_values: Iterable[str] = ()
) -> None:
    if payload.get("schema_version") != STAGE_P_PROMPT_SCHEMA:
        raise StagePContractError("unsupported_schema", "Stage P prompt schema is not frozen v1")
    forbidden_paths = _forbidden_key_paths(payload)
    if forbidden_paths:
        raise StagePContractError(
            "prompt_oracle_leak",
            "Stage P prompt contains forbidden fields: " + ", ".join(sorted(forbidden_paths)),
        )
    strings = _all_strings(payload)
    for marker in ORACLE_MARKERS:
        if any(marker in text for text in strings):
            raise StagePContractError("prompt_oracle_leak", "Stage P prompt exposes oracle text")
    for forbidden in forbidden_values:
        if forbidden and any(forbidden in text for text in strings):
            raise StagePContractError(
                "prompt_oracle_leak", "Stage P prompt contains a forbidden benchmark value"
            )


def _validate_gap(raw: Any, *, case_id: str, expected_index: int) -> dict[str, Any]:
    if not isinstance(raw, Mapping) or set(raw) != GAP_KEYS:
        raise StagePContractError(
            "invalid_schema", f"{case_id}.gap_sequence[{expected_index - 1}] has wrong keys"
        )
    gap_index = _bounded_int(
        raw.get("gap_index"), label=f"{case_id}.gap_index", minimum=1, maximum=4
    )
    if gap_index != expected_index:
        raise StagePContractError("gap_sequence_cycle", f"{case_id} gap indexes are not consecutive")
    task_class = _nonempty_string(raw.get("task_class"), label=f"{case_id}.task_class")
    if task_class not in TASK_CLASSES:
        raise StagePContractError("invalid_schema", f"{case_id} has unsupported task class")
    head = _nonempty_string(raw.get("capability_head"), label=f"{case_id}.capability_head")
    if head not in CAPABILITY_HEADS:
        raise StagePContractError("invalid_schema", f"{case_id} has unsupported capability head")
    probe = _nonempty_string(raw.get("contract_probe"), label=f"{case_id}.contract_probe")
    if probe not in PROBE_TYPES:
        raise StagePContractError("invalid_schema", f"{case_id} has unsupported contract probe")
    signature = _nonempty_string(
        raw.get("declaration_signature"), label=f"{case_id}.declaration_signature"
    )
    if signature != PROBE_TYPES[probe][0]:
        raise StagePContractError(
            "invalid_schema", f"{case_id} declaration signature does not match its probe"
        )
    return dict(raw)


def _validate_public_case_contract(case: BenchmarkCase) -> None:
    contract = case.stage_p
    if set(contract) != PUBLIC_CASE_KEYS:
        raise StagePContractError(
            "invalid_schema", f"{case.id}.stage_p keys must exactly equal {sorted(PUBLIC_CASE_KEYS)}"
        )
    if contract.get("schema_version") != STAGE_P_CASE_SCHEMA:
        raise StagePContractError("unsupported_schema", f"{case.id} uses unsupported Stage P ABI")
    role = _nonempty_string(contract.get("protocol_role"), label=f"{case.id}.protocol_role")
    if role not in PROTOCOL_ROLES:
        raise StagePContractError("invalid_schema", f"{case.id} has invalid protocol role")
    _nonempty_string(
        contract.get("contract_probe_profile"), label=f"{case.id}.contract_probe_profile"
    )
    gaps_raw = contract.get("gap_sequence")
    if not isinstance(gaps_raw, list):
        raise StagePContractError("invalid_schema", f"{case.id}.gap_sequence must be a list")
    gaps = tuple(
        _validate_gap(raw, case_id=case.id, expected_index=index)
        for index, raw in enumerate(gaps_raw, start=1)
    )
    if len(gaps) > 4:
        raise StagePContractError("gap_count_exceeded", f"{case.id} exceeds four frozen gaps")
    model_required = contract.get("model_generated_required")
    hidden_gold = contract.get("hidden_gold")
    absence = contract.get("production_registry_absence_required")
    if not all(isinstance(value, bool) for value in (model_required, hidden_gold, absence)):
        raise StagePContractError("invalid_schema", f"{case.id} has invalid Boolean contract fields")
    editable_file = _nonempty_string(
        contract.get("editable_file"), label=f"{case.id}.editable_file"
    )
    editable_region = _nonempty_string(
        contract.get("editable_region"), label=f"{case.id}.editable_region"
    )
    if not SAFE_FILE_RE.fullmatch(editable_file) or ".." in Path(editable_file).parts:
        raise StagePContractError("invalid_schema", f"{case.id} has unsafe editable file")
    if not SAFE_REGION_RE.fullmatch(editable_region):
        raise StagePContractError("invalid_schema", f"{case.id} has unsafe editable region")
    imports = _string_tuple(
        contract.get("allowed_imports"), label=f"{case.id}.allowed_imports", allow_empty=False
    )
    if imports != (STAGE_P_PROBE_MODULE,):
        raise StagePContractError("invalid_schema", f"{case.id} must freeze the probe-only import")
    _string_tuple(contract.get("helper_handles"), label=f"{case.id}.helper_handles")
    if contract.get("worker_profile") not in WORKER_PROFILES:
        raise StagePContractError("invalid_schema", f"{case.id} has invalid worker profile")
    turns = _bounded_int(
        contract.get("semantic_turn_budget"),
        label=f"{case.id}.semantic_turn_budget",
        minimum=0,
        maximum=16,
    )
    tokens = _bounded_int(
        contract.get("token_budget"),
        label=f"{case.id}.token_budget",
        minimum=0,
        maximum=120_000,
    )
    publication_role = contract.get("publication_role")
    if publication_role not in PUBLICATION_ROLES:
        raise StagePContractError("invalid_schema", f"{case.id} has invalid publication role")
    parameters = contract.get("resolved_parameters")
    if not isinstance(parameters, list):
        raise StagePContractError("invalid_schema", f"{case.id}.resolved_parameters must be a list")
    for index, parameter in enumerate(parameters):
        if not isinstance(parameter, Mapping) or set(parameter) != {"name", "type", "value"}:
            raise StagePContractError(
                "invalid_schema", f"{case.id}.resolved_parameters[{index}] has wrong shape"
            )
        for key in ("name", "type", "value"):
            _nonempty_string(
                parameter.get(key), label=f"{case.id}.resolved_parameters[{index}].{key}"
            )
    blocker = contract.get("public_blocker")
    if role != "consumer" and (
        case.resources.get("model_timeout_seconds") != 300
        or case.resources.get("model_max_tokens") != 24_576
        or case.resources.get("max_model_calls") != 4
    ):
        raise StagePContractError(
            "invalid_schema", f"{case.id} must freeze the P-A model-call budget"
        )
    if role == "consumer":
        if gaps or model_required or turns or tokens or case.requires_authoring:
            raise StagePContractError(
                "consumer_authoring_forbidden", f"{case.id} consumer must have zero authoring"
            )
        if publication_role != "consumer" or blocker is not None:
            raise StagePContractError("invalid_schema", f"{case.id} consumer contract is malformed")
    elif role == "authoring":
        if not gaps or not model_required or not absence or not case.requires_authoring:
            raise StagePContractError("invalid_schema", f"{case.id} authoring contract is incomplete")
        if turns != 4 * len(gaps) or tokens != 30_000 * len(gaps):
            raise StagePContractError("invalid_schema", f"{case.id} has noncanonical depth budget")
        if blocker is not None:
            raise StagePContractError("invalid_schema", f"{case.id} positive task exposes a blocker")
    else:
        if not gaps or not model_required or not case.requires_authoring:
            raise StagePContractError("invalid_schema", f"{case.id} adversarial contract is incomplete")
        if not isinstance(blocker, Mapping) or set(blocker) != {"failure_code", "facts"}:
            raise StagePContractError("invalid_schema", f"{case.id} blocker has wrong shape")
        code = _nonempty_string(blocker.get("failure_code"), label=f"{case.id}.failure_code")
        facts = _string_tuple(blocker.get("facts"), label=f"{case.id}.facts", allow_empty=False)
        if code not in STAGE_P_FAILURE_CODES or not facts:
            raise StagePContractError("invalid_schema", f"{case.id} blocker is unsupported")


def validate_stage_p_suites(
    positive: BenchmarkSuite, negative: BenchmarkSuite
) -> tuple[BenchmarkCase, ...]:
    if positive.id != STAGE_P_POSITIVE_SUITE_ID or negative.id != STAGE_P_NEGATIVE_SUITE_ID:
        raise StagePContractError("invalid_schema", "Stage P suite IDs are not frozen v1")
    if tuple(case.id for case in positive.cases) != EXPECTED_POSITIVE_IDS:
        raise StagePContractError("invalid_schema", "Stage P positive case order/matrix changed")
    if tuple(case.id for case in negative.cases) != tuple(EXPECTED_NEGATIVE_FAILURES):
        raise StagePContractError("invalid_schema", "Stage P negative case order/matrix changed")
    cases = (*positive.cases, *negative.cases)
    if len(cases) != 24 or len({case.id for case in cases}) != 24:
        raise StagePContractError("invalid_schema", "Stage P canonical matrix must contain 24 cases")
    for case in cases:
        _validate_public_case_contract(case)
        if case.module != STAGE_P_INPUT_MODULE or case.evaluation_lane != "stage_p":
            raise StagePContractError("invalid_schema", f"{case.id} is outside the Stage P ABI")
        if "expected" in case.stage_p or "coverage" in case.stage_p:
            raise StagePContractError("benchmark_shortcut_detected", f"{case.id} leaks scoring data")
    for case in positive.cases:
        if case.expected.final_status != "VERIFIED" or case.expected.final_failure_code is not None:
            raise StagePContractError("invalid_schema", f"{case.id} positive expectation changed")
    for case in negative.cases:
        expected = EXPECTED_NEGATIVE_FAILURES[case.id]
        blocker = case.stage_p["public_blocker"]
        if (
            case.expected.final_status != "BLOCKED"
            or case.expected.final_failure_code != expected
            or not isinstance(blocker, Mapping)
            or blocker.get("failure_code") != expected
        ):
            raise StagePContractError("invalid_schema", f"{case.id} negative expectation changed")

    positives = positive.cases
    authoring = [case for case in positives if case.stage_p["protocol_role"] == "authoring"]
    if len(authoring) != 11 or sum(bool(case.stage_p["model_generated_required"]) for case in authoring) != 11:
        raise StagePContractError("invalid_schema", "Stage P must freeze 11 model-authored positives")
    if sum(case.stage_p["publication_role"] == "producer" for case in positives) != 1:
        raise StagePContractError("invalid_schema", "Stage P must freeze one producer")
    if sum(case.stage_p["publication_role"] == "consumer" for case in positives) != 1:
        raise StagePContractError("invalid_schema", "Stage P must freeze one consumer")
    if sum(bool(case.stage_p["hidden_gold"]) for case in authoring) < 8:
        raise StagePContractError("invalid_schema", "Stage P needs at least eight hidden-gold positives")
    if sum(case.coverage.get("full_bundle") is True for case in positives) < 3:
        raise StagePContractError("invalid_schema", "Stage P needs three full-bundle positives")
    depths = Counter(len(case.stage_p["gap_sequence"]) for case in authoring)
    if not all(depths[depth] >= 1 for depth in (1, 2, 3, 4)):
        raise StagePContractError("invalid_schema", "Stage P must cover gap depths 1..4")
    families = Counter(str(case.coverage.get("family")) for case in positives)
    for family in ("graph", "numeric", "set_system", "clause_csp"):
        if not 2 <= families[family] <= 4:
            raise StagePContractError("invalid_schema", f"Stage P family coverage failed: {family}")
    if {case.objective for case in positives} != {
        "reduce_to",
        "reduce_to_known_np",
        "reduce_to_known_hardness",
        "prove_in_np",
        "prove_np_complete",
    }:
        raise StagePContractError("invalid_schema", "Stage P must cover all five objectives")
    if not {
        "presented_problem",
        "predicate",
        "parameterized_predicate",
    }.issubset({case.input_kind for case in positives}):
        raise StagePContractError("invalid_schema", "Stage P input-form coverage is incomplete")
    positive_task_classes = {
        str(gap["task_class"])
        for case in authoring
        for gap in case.stage_p["gap_sequence"]
    }
    if positive_task_classes != TASK_CLASSES:
        raise StagePContractError("invalid_schema", "Stage P positive task-class coverage is incomplete")
    fingerprints = {
        sha256_id(
            {
                "source": case.source,
                "target": case.target,
                "objective": case.objective,
                "family": case.coverage.get("family"),
                "gaps": case.stage_p["gap_sequence"],
            }
        )
        for case in cases
    }
    if len(fingerprints) != 24:
        raise StagePContractError("benchmark_shortcut_detected", "canonical cases are isomorphic")
    return tuple(cases)


@dataclass(frozen=True)
class StagePAuthoringTask:
    session_id: str
    gap_id: str
    parent_checkpoint_hash: str
    task_class: str
    capability_head: str
    declaration_signature: str
    contract_probe: str
    source_endpoint: str
    target_endpoint: str
    direction: str
    objective: str
    editable_file: str
    editable_region: str
    base_source_sha256: str
    allowed_imports: tuple[str, ...]
    helper_handles: tuple[str, ...]
    semantic_turn_budget: int
    token_budget: int
    public_blocker: Mapping[str, Any] | None
    schema_version: str = STAGE_P_TASK_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["allowed_imports"] = list(self.allowed_imports)
        value["helper_handles"] = list(self.helper_handles)
        return value


def build_stage_p_task(case: BenchmarkCase, *, gap_index: int = 1) -> StagePAuthoringTask:
    _validate_public_case_contract(case)
    gaps = case.stage_p["gap_sequence"]
    if not gaps:
        raise StagePContractError("consumer_authoring_forbidden", "consumer has no authoring task")
    if not 1 <= gap_index <= len(gaps):
        raise StagePContractError("gap_count_exceeded", "requested gap is outside frozen sequence")
    gap = gaps[gap_index - 1]
    parent = sha256_id(
        {
            "schema_version": "hardness_stage_p_parent_checkpoint_v1",
            "module": case.module,
            "source": case.source,
            "target": case.target,
            "objective": case.objective,
            "gap_index": gap_index,
        }
    )
    base_source = (
        f"import {STAGE_P_PROBE_MODULE}\n\n"
        "namespace StageP.Generated\n\n"
        f"-- HARDNESS_EDITABLE_REGION {case.stage_p['editable_region']}\n"
        f"-- exact signature: {gap['declaration_signature']}\n"
        "-- replacement body is supplied by the untrusted model\n\n"
        "end StageP.Generated\n"
    )
    gap_id = sha256_id(
        {
            "schema_version": "hardness_stage_p_gap_id_v1",
            "parent": parent,
            "task_class": gap["task_class"],
            "head": gap["capability_head"],
            "signature": gap["declaration_signature"],
        }
    )
    session_id = sha256_id(
        {
            "schema_version": "hardness_stage_p_session_v1",
            "gap_id": gap_id,
            "base_source_sha256": sha256_id(base_source),
        }
    )
    blocker = case.stage_p["public_blocker"]
    return StagePAuthoringTask(
        session_id=session_id,
        gap_id=gap_id,
        parent_checkpoint_hash=parent,
        task_class=str(gap["task_class"]),
        capability_head=str(gap["capability_head"]),
        declaration_signature=str(gap["declaration_signature"]),
        contract_probe=str(gap["contract_probe"]),
        source_endpoint=case.source,
        target_endpoint=case.target or case.source,
        direction="source_to_target",
        objective=case.objective,
        editable_file=str(case.stage_p["editable_file"]),
        editable_region=str(case.stage_p["editable_region"]),
        base_source_sha256=sha256_id(base_source),
        allowed_imports=tuple(case.stage_p["allowed_imports"]),
        helper_handles=tuple(case.stage_p["helper_handles"]),
        semantic_turn_budget=int(case.stage_p["semantic_turn_budget"]),
        token_budget=int(case.stage_p["token_budget"]),
        public_blocker=dict(blocker) if isinstance(blocker, Mapping) else None,
    )


def build_stage_p_contract_prompt(
    *, task: StagePAuthoringTask, previous_rejection: str | None = None
) -> str:
    if task.public_blocker is None:
        response_template: dict[str, Any] = {
            "schema_version": STAGE_P_PATCH_SCHEMA,
            "action": "submit_patch",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "base_source_sha256": task.base_source_sha256,
            "editable_file": task.editable_file,
            "editable_region": task.editable_region,
            "replacement_body": "<Lean term only>",
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
    else:
        response_template = {
            "schema_version": STAGE_P_PATCH_SCHEMA,
            "action": "stop_authoring",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "failure_code": str(task.public_blocker["failure_code"]),
            "confirmed_facts": ["<public fact>"],
            "missing_conditions": ["<missing condition>"],
        }
    payload: dict[str, Any] = {
        "schema_version": STAGE_P_PROMPT_SCHEMA,
        "contract_scope": "P-A patch envelope and isolated Lean syntax probe only",
        "task": task.to_dict(),
        "fixed_declaration": {
            "kind": PROBE_TYPES[task.contract_probe][1],
            "name": "candidate",
            "expected_type": task.declaration_signature,
            "expected_type_unfolded": PROBE_TYPE_SUMMARIES[task.contract_probe],
            "editable_component": "body_after_assignment",
            "instruction": "Return a Lean term after := that inhabits expected_type_unfolded.",
        },
        "permitted_actions": [response_template["action"]],
        "response_template": response_template,
        "constraints": {
            "json_only": True,
            "replacement_body_only": True,
            "may_change_request": False,
            "may_add_imports": False,
            "may_add_declarations": False,
            "may_use_unlisted_helpers": False,
            "compiler_inserts_math": False,
            "probe_is_publishable_capability": False,
        },
    }
    if previous_rejection:
        payload["last_protocol_error"] = previous_rejection[:2000]
    audit_stage_p_prompt(payload)
    return json.dumps(payload, ensure_ascii=False, sort_keys=True)


@dataclass(frozen=True)
class StagePPatchAction:
    action: str
    session_id: str
    gap_id: str
    task_class: str
    base_source_sha256: str | None = None
    editable_file: str | None = None
    editable_region: str | None = None
    replacement_body: str | None = None
    helper_handles: tuple[str, ...] = ()
    binding_claim: Mapping[str, str] = field(default_factory=dict)
    failure_code: str | None = None
    confirmed_facts: tuple[str, ...] = ()
    missing_conditions: tuple[str, ...] = ()
    schema_version: str = STAGE_P_PATCH_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["helper_handles"] = list(self.helper_handles)
        value["confirmed_facts"] = list(self.confirmed_facts)
        value["missing_conditions"] = list(self.missing_conditions)
        value["binding_claim"] = dict(self.binding_claim)
        return value


def parse_stage_p_action(content: str, *, task: StagePAuthoringTask) -> StagePPatchAction:
    if "```" in content:
        raise StagePContractError(
            "invalid_stage_p_patch_schema", "markdown-fenced model output is forbidden"
        )
    payload = extract_json_object(content)
    if not isinstance(payload, Mapping):
        raise StagePContractError("invalid_stage_p_patch_schema", "response is not one JSON object")
    if payload.get("schema_version") != STAGE_P_PATCH_SCHEMA:
        raise StagePContractError("invalid_stage_p_patch_schema", "patch schema is not Stage P v1")
    action = _nonempty_string(payload.get("action"), label="action.action")
    session_id = _nonempty_string(payload.get("session_id"), label="action.session_id")
    gap_id = _nonempty_string(payload.get("gap_id"), label="action.gap_id")
    task_class = _nonempty_string(payload.get("task_class"), label="action.task_class")
    if (session_id, gap_id, task_class) != (task.session_id, task.gap_id, task.task_class):
        raise StagePContractError("request_or_endpoint_mutation", "immutable task binding changed")
    if action == "submit_patch":
        if set(payload) != {
            "schema_version",
            "action",
            "session_id",
            "gap_id",
            "task_class",
            "base_source_sha256",
            "editable_file",
            "editable_region",
            "replacement_body",
            "helper_handles",
            "binding_claim",
        }:
            raise StagePContractError(
                "invalid_stage_p_patch_schema", "submit_patch has unexpected or missing fields"
            )
        base = _nonempty_string(payload.get("base_source_sha256"), label="patch.base_source_sha256")
        editable_file = _nonempty_string(payload.get("editable_file"), label="patch.editable_file")
        editable_region = _nonempty_string(payload.get("editable_region"), label="patch.editable_region")
        body = _nonempty_string(payload.get("replacement_body"), label="patch.replacement_body")
        handles = _string_tuple(payload.get("helper_handles", []), label="patch.helper_handles")
        binding = payload.get("binding_claim")
        expected_keys = {
            "source_endpoint",
            "target_endpoint",
            "direction",
            "objective",
            "capability_head",
            "declaration_signature",
        }
        if not isinstance(binding, Mapping) or set(binding) != expected_keys:
            raise StagePContractError("request_or_endpoint_mutation", "binding claim has wrong shape")
        normalized = {key: _nonempty_string(binding.get(key), label=f"binding.{key}") for key in binding}
        action_value = StagePPatchAction(
            action=action,
            session_id=session_id,
            gap_id=gap_id,
            task_class=task_class,
            base_source_sha256=base,
            editable_file=editable_file,
            editable_region=editable_region,
            replacement_body=body,
            helper_handles=handles,
            binding_claim=normalized,
        )
        validate_stage_p_patch(action_value, task=task)
        return action_value
    if action == "stop_authoring":
        if set(payload) != {
            "schema_version",
            "action",
            "session_id",
            "gap_id",
            "task_class",
            "failure_code",
            "confirmed_facts",
            "missing_conditions",
        }:
            raise StagePContractError(
                "invalid_stage_p_patch_schema", "stop_authoring has unexpected or missing fields"
            )
        failure_code = _nonempty_string(payload.get("failure_code"), label="stop.failure_code")
        facts = _string_tuple(
            payload.get("confirmed_facts", []), label="stop.confirmed_facts", allow_empty=False
        )
        missing = _string_tuple(
            payload.get("missing_conditions", []),
            label="stop.missing_conditions",
            allow_empty=True,
        )
        return StagePPatchAction(
            action=action,
            session_id=session_id,
            gap_id=gap_id,
            task_class=task_class,
            failure_code=failure_code,
            confirmed_facts=facts,
            missing_conditions=missing,
        )
    if action == "request_helper":
        if set(payload) != {
            "schema_version",
            "action",
            "session_id",
            "gap_id",
            "task_class",
            "helper_handle",
        }:
            raise StagePContractError(
                "invalid_stage_p_patch_schema", "request_helper has unexpected or missing fields"
            )
        handle = _nonempty_string(payload.get("helper_handle"), label="request.helper_handle")
        if handle not in task.helper_handles:
            raise StagePContractError("fabricated_declaration_handle", "helper was not retrieved")
        return StagePPatchAction(
            action=action,
            session_id=session_id,
            gap_id=gap_id,
            task_class=task_class,
            helper_handles=(handle,),
        )
    raise StagePContractError("invalid_stage_p_patch_schema", f"unsupported action {action}")


def validate_stage_p_patch(action: StagePPatchAction, *, task: StagePAuthoringTask) -> None:
    if action.action != "submit_patch":
        raise StagePContractError("invalid_stage_p_patch_schema", "only submit_patch has a body")
    if action.base_source_sha256 != task.base_source_sha256:
        raise StagePContractError("patch_base_hash_mismatch", "patch is based on another source")
    if action.editable_file != task.editable_file or action.editable_region != task.editable_region:
        raise StagePContractError("patch_outside_editable_region", "patch escaped the frozen fence")
    if not set(action.helper_handles).issubset(task.helper_handles):
        raise StagePContractError("fabricated_declaration_handle", "patch cites an unlisted helper")
    expected_binding = {
        "source_endpoint": task.source_endpoint,
        "target_endpoint": task.target_endpoint,
        "direction": task.direction,
        "objective": task.objective,
        "capability_head": task.capability_head,
        "declaration_signature": task.declaration_signature,
    }
    if dict(action.binding_claim) != expected_binding:
        raise StagePContractError("request_or_endpoint_mutation", "patch mutated an exact binding")
    body = action.replacement_body or ""
    if len(body) > STAGE_P_MAX_BODY_CHARS:
        raise StagePContractError("candidate_static_policy_failed", "replacement body is too large")
    if BANNED_BODY_RE.search(body):
        match = BANNED_BODY_RE.search(body)
        token = match.group(0).lower() if match else ""
        if token in {"sorry", "admit", "axiom", "unsafe"}:
            code = "sorry_axiom_or_unsafe_candidate"
        elif token == "import":
            code = "import_not_allowlisted"
        else:
            code = "patch_outside_editable_region"
        raise StagePContractError(code, "replacement body contains a forbidden token")
    if any(marker.lower() in body.lower() for marker in ORACLE_MARKERS):
        raise StagePContractError("oracle_or_gold_import", "replacement body references oracle text")


def validate_stage_p_terminal_action(
    action: StagePPatchAction, *, task: StagePAuthoringTask
) -> None:
    blocker = task.public_blocker
    if blocker is None:
        if action.action != "submit_patch":
            raise StagePContractError("authoring_no_progress", "positive task did not submit a patch")
        validate_stage_p_patch(action, task=task)
        return
    expected = str(blocker["failure_code"])
    if action.action != "stop_authoring":
        raise StagePContractError(expected, "adversarial task must stop at its public blocker")
    if action.failure_code != expected:
        raise StagePContractError(expected, "stop action reported the wrong public failure code")


def build_contract_probe_source(
    *, task: StagePAuthoringTask, action: StagePPatchAction, namespace_suffix: str
) -> str:
    validate_stage_p_patch(action, task=task)
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", namespace_suffix):
        raise StagePContractError("invalid_schema", "unsafe generated namespace suffix")
    declaration_kind = PROBE_TYPES[task.contract_probe][1]
    return (
        f"import {STAGE_P_PROBE_MODULE}\n\n"
        f"namespace StageP.ContractRun.{namespace_suffix}\n\n"
        f"{declaration_kind} candidate : {task.declaration_signature} :=\n"
        f"{action.replacement_body}\n\n"
        "#check candidate\n\n"
        f"end StageP.ContractRun.{namespace_suffix}\n"
    )


def validate_stage_p_mutation_suite(payload: Mapping[str, Any]) -> tuple[dict[str, Any], ...]:
    if payload.get("schema_version") != STAGE_P_MUTATION_SUITE_SCHEMA:
        raise StagePContractError("unsupported_schema", "Stage P mutation suite is not v1")
    if payload.get("suite_id") != "stage-p-mutations-72":
        raise StagePContractError("invalid_schema", "Stage P mutation suite ID changed")
    groups = payload.get("groups")
    if not isinstance(groups, list) or len(groups) != 4:
        raise StagePContractError("invalid_schema", "Stage P mutation suite needs four groups")
    expected_counts = {
        "endpoint_direction_type": 24,
        "patch_security": 16,
        "state_worker": 16,
        "api_diagnostics_report": 16,
    }
    rows: list[dict[str, Any]] = []
    canonical = (*EXPECTED_POSITIVE_IDS, *EXPECTED_NEGATIVE_FAILURES)
    for group in groups:
        if not isinstance(group, Mapping) or set(group) != {
            "group_id",
            "count",
            "seed_base",
            "operators",
            "expected_failure_codes",
        }:
            raise StagePContractError("invalid_schema", "mutation group has wrong shape")
        group_id = _nonempty_string(group.get("group_id"), label="mutation.group_id")
        if group_id not in expected_counts or group.get("count") != expected_counts[group_id]:
            raise StagePContractError("invalid_schema", f"mutation count changed for {group_id}")
        seed_base = _bounded_int(
            group.get("seed_base"), label=f"{group_id}.seed_base", minimum=1, maximum=1_000_000
        )
        operators = _string_tuple(group.get("operators"), label=f"{group_id}.operators", allow_empty=False)
        codes = _string_tuple(
            group.get("expected_failure_codes"),
            label=f"{group_id}.expected_failure_codes",
            allow_empty=False,
            unique=False,
        )
        if not set(codes).issubset(STAGE_P_FAILURE_CODES):
            raise StagePContractError("invalid_schema", f"{group_id} has unsupported failure code")
        for offset in range(expected_counts[group_id]):
            rows.append(
                {
                    "mutation_id": f"{group_id}-{offset + 1:02d}",
                    "parent_case": canonical[offset % len(canonical)],
                    "mutation_operator": operators[offset % len(operators)],
                    "expected_failure_code": codes[offset % len(codes)],
                    "seed": seed_base + offset,
                }
            )
    if len(rows) != 72 or len({row["mutation_id"] for row in rows}) != 72:
        raise StagePContractError("invalid_schema", "Stage P must materialize exactly 72 mutations")
    return tuple(rows)


def load_and_validate_stage_p_mutations(path: Path) -> tuple[dict[str, Any], ...]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StagePContractError("invalid_schema", f"cannot load mutation suite: {error}") from error
    if not isinstance(payload, Mapping):
        raise StagePContractError("invalid_schema", "mutation suite must be an object")
    return validate_stage_p_mutation_suite(payload)


def validate_stage_p_worker_microbenchmark(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_version") != STAGE_P_WORKER_MICROBENCHMARK_SCHEMA:
        raise StagePContractError("unsupported_schema", "Stage P worker benchmark is not v1")
    if payload.get("repeat_count") != 20 or payload.get("maximum_workers") != 4:
        raise StagePContractError("invalid_schema", "worker benchmark must freeze 20 repeats/4 workers")
    cache_fields = _string_tuple(
        payload.get("cache_key_fields"), label="worker.cache_key_fields", allow_empty=False
    )
    required_fields = {
        "toolchain",
        "lake_manifest",
        "base_registry_fingerprint",
        "complete_source_hash",
        "dependency_hash",
        "namespace",
        "session_id",
        "validation_profile",
    }
    if not required_fields.issubset(cache_fields):
        raise StagePContractError("lean_worker_stale_result", "worker cache key is incomplete")
    checks = _string_tuple(
        payload.get("isolation_checks"), label="worker.isolation_checks", allow_empty=False
    )
    if not {"session_ownership", "namespace_isolation", "deletion_after_cache"}.issubset(checks):
        raise StagePContractError("lean_worker_session_leak", "worker isolation matrix is incomplete")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != {
        "warm_p50_over_cold_p50_max",
        "wall_time_reduction_min",
        "cache_invalidation_rate_min",
        "namespace_isolation_rate_min",
        "stale_result_rejection_rate_min",
    }:
        raise StagePContractError("invalid_schema", "worker gates have wrong shape")
    if gates.get("warm_p50_over_cold_p50_max") != 0.5 or gates.get("wall_time_reduction_min") != 0.5:
        raise StagePContractError("invalid_schema", "worker performance gates changed")
    if any(gates.get(key) != 1.0 for key in (
        "cache_invalidation_rate_min",
        "namespace_isolation_rate_min",
        "stale_result_rejection_rate_min",
    )):
        raise StagePContractError("invalid_schema", "worker isolation gates must be 100%")


def load_and_validate_stage_p_worker_microbenchmark(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise StagePContractError("invalid_schema", f"cannot load worker benchmark: {error}") from error
    if not isinstance(payload, Mapping):
        raise StagePContractError("invalid_schema", "worker benchmark must be an object")
    validate_stage_p_worker_microbenchmark(payload)
    return dict(payload)


def stage_p_report_skeleton() -> dict[str, Any]:
    return {
        "schema_version": STAGE_P_CONTRACT_REPORT_SCHEMA,
        "status": "FAILED",
        "stage": "P-A",
        "qualification_scope": "contract_only_not_production_capability",
        "canonical_case_count": 24,
        "positive_case_count": 12,
        "negative_case_count": 12,
        "model_eligible_case_count": 23,
        "consumer_zero_authoring_case_count": 1,
        "mutation_case_count": 72,
        "compiler_inserted_math_token_count": 0,
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
        "cases": [],
        "gates": {},
    }
