#!/usr/bin/env python3
"""Build the fail-closed H-J typed-authoring capability report.

The builder is evidence-only.  It does not run Lean, pytest, or a model.  It
binds the frozen H-I baseline, the current answer-free capability contract,
and five distinct full C0/F0 raw+score pairs.  Aggregate scorer metrics are
never trusted on their own: the H-J improvement gates are recomputed from the
34 scorer case rows and the independently loaded scorer oracle.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.models import canonical_json, sha256_id  # noqa: E402
from agent.hardness.np_hard_authoring import (  # noqa: E402
    NP_HARD_AUTHORING_TASK_CLASSES_V2,
    NPHardAuthoringContractError,
    NPHardAuthoringTaskV2,
    deletion_command_matches_declaration_v2,
    validate_successor_only_authoritative_evidence_v2,
)
from agent.hardness.np_hard_capability import (  # noqa: E402
    CAPABILITY_RUN_SCHEMA_V1,
    CAPABILITY_RUN_SCHEMA_V2,
    CAPABILITY_SCORE_SCHEMA_V1,
    CAPABILITY_SCORE_SCHEMA_V2,
    CAPABILITY_SPLIT_COUNTS,
    CAPABILITY_SPLITS,
    load_capability_bundle,
    load_capability_oracle,
)


REPORT_SCHEMA = "hardness_main_h_j_full_report_v2"
REPORT_PATH = ROOT / "Reports/MAIN_H_J_FULL_REPORT.json"
H_I_REPORT_SCHEMA = "hardness_main_h_i_full_report_v1"
UNIFIED_REPORT_SCHEMA = "hardness_np_hard_unified_benchmark_report_v1"
RELEASE_REPORT_SCHEMA = "hardness_np_hard_release_real_run_v2"
STAGE_LABELS = (
    "h-j.1-adapter",
    "h-j.2-tmkarp",
    "h-j.3-dependent",
    "h-j.4-direct-tm",
    "h-j.5-gadget",
)
CONTRACT_EPOCHS = ("v1", "v2")
CONTRACT_VERSIONS = ("v1", "v2a", "v2b")
CAPABILITY_RUN_SCHEMA_BY_EPOCH = {
    "v1": CAPABILITY_RUN_SCHEMA_V1,
    "v2": CAPABILITY_RUN_SCHEMA_V2,
}
CAPABILITY_SCORE_SCHEMA_BY_EPOCH = {
    "v1": CAPABILITY_SCORE_SCHEMA_V1,
    "v2": CAPABILITY_SCORE_SCHEMA_V2,
}
STAGE_CONTRACT_EPOCH = {
    "h-j.1-adapter": "v1",
    "h-j.2-tmkarp": "v1",
    "h-j.3-dependent": "v1",
    "h-j.4-direct-tm": "v2",
    "h-j.5-gadget": "v2",
}
STAGE_CONTRACT_VERSION = {
    "h-j.1-adapter": "v1",
    "h-j.2-tmkarp": "v1",
    "h-j.3-dependent": "v1",
    "h-j.4-direct-tm": "v2a",
    "h-j.5-gadget": "v2b",
}
CONTRACT_EPOCH_BY_VERSION = {"v1": "v1", "v2a": "v2", "v2b": "v2"}
R1_SUITE_SCHEMAS = {
    "v1": "hardness_np_hard_public_r1_coverage_suite_v1",
    "v2": "hardness_np_hard_public_r1_coverage_suite_v2",
}
MIGRATION_AUDIT_SCHEMA = "hardness_np_hard_capability_migration_audit_v1"
V2_REFINEMENT_AUDIT_SCHEMA = "hardness_np_hard_v2_refinement_audit_v1"
MIGRATION_BOUNDARY_FAILURE = "encoding_polynomial_reverse_bridge_unavailable"
V2_REFINEMENT_CASE_IDS = (
    "chld-au-03-max-cut-structured",
    "chld-au-04-max-cut-binary",
)
V2_REFINEMENT_REQUIRED_MOTIFS: Mapping[str, Mapping[str, Any]] = {
    "chld-au-03-max-cut-structured": {
        "task_class": "typed_gadget_indexed_admission_dag",
        "nodes": [
            {
                "node_id": "gadget-reference-audit",
                "capability": "gadget_reference_audit",
                "depends_on": [],
            },
            {
                "node_id": "gadget-normalization-audit",
                "capability": "gadget_normalization_audit",
                "depends_on": ["gadget-reference-audit"],
            },
            {
                "node_id": "gadget-executable",
                "capability": "gadget_executable",
                "depends_on": [
                    "gadget-reference-audit",
                    "gadget-normalization-audit",
                ],
            },
            {
                "node_id": "gadget-parameter-audit",
                "capability": "gadget_parameter_audit",
                "depends_on": ["gadget-executable"],
            },
            {
                "node_id": "gadget-semantic-forward",
                "capability": "gadget_semantic_forward",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                ],
            },
            {
                "node_id": "gadget-semantic-reverse",
                "capability": "gadget_semantic_reverse",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                ],
            },
            {
                "node_id": "gadget-direct-tm",
                "capability": "gadget_direct_tm",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                    "gadget-semantic-forward",
                    "gadget-semantic-reverse",
                ],
            },
            {
                "node_id": "gadget-program",
                "capability": "gadget_program",
                "depends_on": ["gadget-executable", "gadget-direct-tm"],
            },
            {
                "node_id": "gadget-composed-program",
                "capability": "gadget_composed_program",
                "depends_on": ["gadget-program"],
            },
            {
                "node_id": "gadget-composed-semantic-iff",
                "capability": "gadget_composed_semantic_iff",
                "depends_on": [
                    "gadget-semantic-forward",
                    "gadget-semantic-reverse",
                    "gadget-program",
                    "gadget-composed-program",
                ],
            },
        ],
        "terminal_node_id": "gadget-composed-semantic-iff",
        "final_program_node_id": "gadget-composed-program",
    },
    "chld-au-04-max-cut-binary": {
        "task_class": "typed_tmkarp_dependent_composition_dag",
        "nodes": [
            {
                "node_id": "tmkarp-primitive",
                "capability": "tmkarp_primitive",
                "depends_on": [],
            },
            {
                "node_id": "tmkarp-program",
                "capability": "tmkarp_program",
                "depends_on": ["tmkarp-primitive"],
            },
            {
                "node_id": "tmkarp-semantic-iff",
                "capability": "tmkarp_semantic_iff",
                "depends_on": ["tmkarp-program"],
            },
            {
                "node_id": "composed-program",
                "capability": "dependent_composed_program",
                "depends_on": ["tmkarp-program"],
            },
            {
                "node_id": "composed-semantic-iff",
                "capability": "dependent_composed_semantic_iff",
                "depends_on": ["tmkarp-semantic-iff", "composed-program"],
            },
        ],
        "terminal_node_id": "composed-semantic-iff",
        "final_program_node_id": "composed-program",
    },
}
V2_REFINEMENT_REQUIRED_MOTIF_IDS = {
    case_id: sha256_id(motif)
    for case_id, motif in V2_REFINEMENT_REQUIRED_MOTIFS.items()
}
H_J_4_V2_MANIFEST_SHA256 = (
    "sha256:9a788946edc985947eb2c7eb5ac6c1f34491a88283a310ca960bb39402e50174"
)
H_J_4_V2_ORACLE_SHA256 = (
    "sha256:45a00b107f72cdf664ec9172fa3b5648d3decfca52b9362a405443fb2b429346"
)
H_J_4_V2_MIGRATION_SHA256 = (
    "sha256:b7f06335943ac3dd70799a87800b5271f2d002a523488683b3949d4da771c696"
)
MIGRATION_TRANSITIONS: tuple[dict[str, Any], ...] = (
    {
        "canonical_problem": "ComplexityReduction.Presentation.Knapsack.structuredProblem",
        "from_case_id": "cval-au-01-knapsack-native-bridge",
        "to_case_id": "frontier-01-knapsack-unary-boundary",
        "classification": "unary_numeric_demotion",
        "reason": MIGRATION_BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.Partition.structuredProblem",
        "from_case_id": "cval-au-02-partition-native-bridge",
        "to_case_id": "frontier-02-partition-unary-boundary",
        "classification": "unary_numeric_demotion",
        "reason": MIGRATION_BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.JobSequencing.structuredProblem",
        "from_case_id": "chld-au-02-job-sequencing-native",
        "to_case_id": "r1-pub-09-job-sequencing-unary-boundary",
        "classification": "unary_numeric_zero_weight_boundary",
        "reason": MIGRATION_BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem",
        "from_case_id": "frontier-01-feedback-arc-set",
        "to_case_id": "chld-au-09-feedback-arc-set",
        "classification": "frontier_to_scored_authoring",
        "reason": "typed_dependent_composition_now_in_scope",
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem",
        "from_case_id": "frontier-02-three-dimensional-matching",
        "to_case_id": "chld-au-10-three-dimensional-matching",
        "classification": "frontier_to_scored_authoring",
        "reason": "typed_direct_tm_authoring_now_in_scope",
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.ZeroOneIPBinary.binaryStructuredProblem",
        "from_case_id": "r1-pub-09-zero-one-ip-binary",
        "to_case_id": "cval-er-05-zero-one-ip-binary",
        "classification": "zero_weight_to_scored_existing",
        "reason": "frozen_public_forward_route_promoted_to_c0_existing",
    },
    {
        "canonical_problem": "ComplexityReduction.Presentation.SeeingSet.presentedProblem",
        "from_case_id": "chld-au-05-seeing-set",
        "to_case_id": "cval-au-03-seeing-set",
        "classification": "split_rebalance",
        "reason": "heldout_authoring_capacity_reserved_for_new_h_j_families",
    },
)
FORMAL_MODEL = {
    "api_key_configured": True,
    "base_url": "https://api.deepseek.com",
    "max_retries": 0,
    "max_tokens": 16000,
    "model": "deepseek-v4-flash",
    "reasoning_effort": "low",
    "temperature": 0.0,
    "timeout_seconds": 300,
}
FORMAL_MANIFEST_MODEL = {"provider": "DeepSeek", **FORMAL_MODEL}
FORMAL_MANIFEST_MODEL.pop("api_key_configured")
TAGGED_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
SECRET_VALUE_RE = re.compile(
    r"(?:Bearer\s+[A-Za-z0-9._~+/=-]{8,}|"
    r"\bsk-[A-Za-z0-9_-]{16,}|"
    r"DEEPSEEK_API_KEY\s*=\s*[^\s\"']+)",
    re.IGNORECASE,
)
SENSITIVE_KEY_RE = re.compile(
    r"(?:^|_)(?:api_?key|authorization|bearer|password|secret)(?:$|_)",
    re.IGNORECASE,
)
SAFETY_FIELDS = (
    "wrong_direction_acceptance_count",
    "wrong_endpoint_acceptance_count",
    "erroneous_non_target_count",
    "nonstandard_axiom_acceptance_count",
    "oracle_leakage_count",
)


class HJReportError(ValueError):
    """Stable fail-closed error emitted by the H-J report builder."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise HJReportError(code, message)


def _expect(condition: bool, code: str, message: str) -> None:
    if not condition:
        _fail(code, message)


def _sha256(path: Path, *, tagged: bool = False) -> str:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return f"sha256:{digest}" if tagged else digest


def _hashes_equal(left: Any, right: Any) -> bool:
    if not isinstance(left, str) or not isinstance(right, str):
        return False
    return left.removeprefix("sha256:") == right.removeprefix("sha256:")


def _path_within(value: Any, root: Path) -> bool:
    if not isinstance(value, str) or not value.strip():
        return False
    try:
        Path(value).resolve().relative_to(root.resolve())
    except (OSError, ValueError):
        return False
    return True


def _deletion_command_matches_declaration(
    command: Mapping[str, Any], declaration: str
) -> bool:
    return deletion_command_matches_declaration_v2(command, declaration)


def _authored_task_motif(
    value: Any,
) -> tuple[dict[str, Any], NPHardAuthoringTaskV2]:
    _expect(
        isinstance(value, Mapping),
        "h_j_authoring_audit_invalid",
        "v2 authored case lacks a typed capability DAG",
    )
    try:
        task = NPHardAuthoringTaskV2.from_dict(value)
    except NPHardAuthoringContractError as error:
        _fail(
            "h_j_authoring_audit_invalid",
            f"v2 authored capability DAG failed its typed contract: {error.code}",
        )
    return (
        {
            "task_class": task.task_class,
            "nodes": [
                {
                    "node_id": node.node_id,
                    "capability": node.capability,
                    "depends_on": list(node.depends_on),
                }
                for node in task.gap_nodes
            ],
            "terminal_node_id": task.terminal_node_id,
            "final_program_node_id": task.final_program_node_id,
        },
        task,
    )


def _assert_no_secret(value: Any, *, label: str) -> None:
    """Reject credential material while allowing boolean absence guards."""

    def walk(item: Any, trail: str) -> None:
        if isinstance(item, Mapping):
            for key, child in item.items():
                key_text = str(key)
                if (
                    SENSITIVE_KEY_RE.search(key_text)
                    and isinstance(child, str)
                    and child.strip()
                ):
                    _fail(
                        "h_j_secret_leak",
                        f"{label}:{trail}.{key_text} contains a secret",
                    )
                walk(child, f"{trail}.{key_text}")
        elif isinstance(item, list):
            for index, child in enumerate(item):
                walk(child, f"{trail}[{index}]")
        elif isinstance(item, str) and SECRET_VALUE_RE.search(item):
            _fail("h_j_secret_leak", f"{label}:{trail} contains credential material")

    walk(value, "$")


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        _fail("h_j_evidence_unreadable", f"{label}: {error}")
    if not isinstance(value, dict):
        _fail("h_j_evidence_schema_invalid", f"{label} is not a JSON object")
    _assert_no_secret(value, label=label)
    return value


def _repo_file(path: Path, *, label: str) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(ROOT)
    except ValueError:
        _fail("h_j_path_escape", f"{label} is outside the repository: {resolved}")
    if not resolved.is_file():
        _fail("h_j_evidence_missing", f"{label} does not exist: {resolved}")
    return resolved


def _repo_reference(value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value.strip():
        _fail("h_j_evidence_schema_invalid", f"{label} is not a path")
    candidate = Path(value)
    return _repo_file(
        candidate if candidate.is_absolute() else ROOT / candidate,
        label=label,
    )


def _parse_timestamp(value: Any, *, label: str) -> datetime:
    if not isinstance(value, str):
        _fail("h_j_evidence_schema_invalid", f"{label} timestamp is missing")
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        _fail("h_j_evidence_schema_invalid", f"{label} timestamp is invalid")
    if parsed.tzinfo is None:
        _fail("h_j_evidence_schema_invalid", f"{label} timestamp has no timezone")
    return parsed


def _parse_labeled_paths(
    values: Sequence[str], *, expected: Sequence[str], option: str
) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        label, separator, raw_path = value.partition("=")
        if separator != "=" or not label or not raw_path:
            _fail("h_j_cli_evidence_invalid", f"{option} must use LABEL=PATH")
        if label in result:
            _fail("h_j_cli_evidence_invalid", f"{option} repeats {label}")
        result[label] = Path(raw_path)
    if set(result) != set(expected):
        _fail(
            "h_j_partial_evidence",
            f"{option} labels differ; missing={sorted(set(expected) - set(result))}, "
            f"extra={sorted(set(result) - set(expected))}",
        )
    return {label: result[label] for label in expected}


def _canonical_content_hash(value: Mapping[str, Any], *, field: str) -> str:
    payload = dict(value)
    payload.pop(field, None)
    return sha256_id(payload)


def _token_usage(calls: Iterable[Mapping[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in calls:
        usage = call.get("usage")
        if not isinstance(usage, Mapping):
            continue
        for name, amount in usage.items():
            if isinstance(amount, int) and not isinstance(amount, bool):
                totals[str(name)] = totals.get(str(name), 0) + amount
    return dict(sorted(totals.items()))


def _model_calls_from_capability(report: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    calls: list[Mapping[str, Any]] = []
    rows = report.get("cases")
    if not isinstance(rows, list):
        return calls
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        raw = row.get("raw_result")
        ledger = raw.get("model_call_ledger") if isinstance(raw, Mapping) else None
        if isinstance(ledger, list):
            calls.extend(call for call in ledger if isinstance(call, Mapping))
    return calls


def _model_calls_from_release(report: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    calls: list[Mapping[str, Any]] = []
    rows = report.get("cases")
    if not isinstance(rows, list):
        return calls
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        ledger = row.get("model_call_ledger")
        if isinstance(ledger, list):
            calls.extend(call for call in ledger if isinstance(call, Mapping))
    return calls


def _validate_http_calls(
    calls: Sequence[Mapping[str, Any]], *, label: str, require_positive: bool = True
) -> tuple[str, ...]:
    if require_positive:
        _expect(
            bool(calls),
            "h_j_deepseek_http_evidence_missing",
            f"{label} has no real DeepSeek HTTP evidence",
        )
    request_ids: list[str] = []
    for index, call in enumerate(calls):
        request_id = call.get("request_id")
        usage = call.get("usage")
        _expect(
            call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            and call.get("provider_attempts") == 1
            and isinstance(call.get("duration_seconds"), (int, float))
            and not isinstance(call.get("duration_seconds"), bool)
            and float(call["duration_seconds"]) > 0
            and isinstance(request_id, str)
            and TAGGED_HASH_RE.fullmatch(request_id) is not None
            and isinstance(call.get("prompt_sha256"), str)
            and TAGGED_HASH_RE.fullmatch(str(call["prompt_sha256"])) is not None
            and isinstance(call.get("response_sha256"), str)
            and TAGGED_HASH_RE.fullmatch(str(call["response_sha256"])) is not None
            and isinstance(usage, Mapping)
            and isinstance(usage.get("total_tokens"), int)
            and not isinstance(usage.get("total_tokens"), bool)
            and int(usage["total_tokens"]) > 0,
            "h_j_deepseek_http_evidence_invalid",
            f"{label} call {index} is not a successful live HTTP response",
        )
        request_ids.append(request_id)
    _expect(
        len(request_ids) == len(set(request_ids)),
        "h_j_deepseek_http_evidence_reused",
        f"{label} repeats a request identity within one full run",
    )
    return tuple(request_ids)


def _rate(numerator: int, denominator: int) -> float | None:
    return round(numerator / denominator, 6) if denominator else None


def _macro(groups: Mapping[str, Sequence[bool]]) -> dict[str, Any]:
    scorecard: dict[str, Any] = {}
    rates: list[float] = []
    for family, successes in sorted(groups.items()):
        count = len(successes)
        success = sum(successes)
        rate = _rate(success, count)
        scorecard[family] = {"count": count, "success": success, "rate": rate}
        if rate is not None:
            rates.append(rate)
    return {
        "groups": scorecard,
        "macro_score": round(sum(rates) / len(rates), 6) if rates else None,
    }


@dataclass(frozen=True)
class StaticEvidencePaths:
    h_i_report: Path
    plan: Path
    v1_capability_manifest: Path
    v1_capability_oracle: Path
    v1_target_matrix: Path
    v1_r1_suite: Path
    v2_capability_manifest: Path
    v2_capability_oracle: Path
    v2_target_matrix: Path
    v2_r1_suite: Path
    v2_h_j_4_capability_manifest: Path | None = None
    v2_h_j_4_capability_oracle: Path | None = None
    v2_h_j_4_migration_report: Path | None = None


def _case_contract(static: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    bundle = static["capability_bundle"]
    oracle = static["capability_oracle_object"]
    result: dict[str, dict[str, Any]] = {}
    for split in CAPABILITY_SPLITS:
        for case in bundle.suites[split].cases:
            policy = oracle[case.case_id]
            identity = bundle.case_identity[case.case_id]
            result[case.case_id] = {
                "split": split,
                "family": case.family,
                "tier": policy.tier,
                "outcome_class": policy.outcome_class,
                "scored": policy.scored,
                "requires_model": policy.requires_model,
                "expected_public_status": policy.expected_public_status,
                "expected_failure_codes": tuple(policy.expected_failure_codes),
                "required_authoring_motif": deepcopy(
                    policy.required_authoring_motif
                ),
                "canonical_identity": str(identity["identity_id"]),
                "canonical_problem": str(identity["canonical_declaration"]),
                "canonical_module": str(identity["canonical_module"]),
            }
    return result


def _identity_universe(
    matrix: Mapping[str, Any], *, label: str
) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]]]:
    identities = matrix.get("identities")
    _expect(
        matrix.get("identity_count") == 44
        and isinstance(identities, list)
        and len(identities) == 44,
        "h_j_identity_partition_invalid",
        f"{label} is not a 44-identity target matrix",
    )
    by_id: dict[str, Mapping[str, Any]] = {}
    by_declaration: dict[str, Mapping[str, Any]] = {}
    for index, raw in enumerate(identities):
        _expect(
            isinstance(raw, Mapping)
            and isinstance(raw.get("identity_id"), str)
            and TAGGED_HASH_RE.fullmatch(str(raw["identity_id"])) is not None
            and isinstance(raw.get("canonical_declaration"), str)
            and isinstance(raw.get("canonical_module"), str)
            and isinstance(raw.get("family"), str)
            and isinstance(raw.get("member_declarations"), list),
            "h_j_identity_partition_invalid",
            f"{label} identity {index} lacks canonical fields",
        )
        identity_id = str(raw["identity_id"])
        _expect(
            identity_id not in by_id,
            "h_j_identity_partition_invalid",
            f"{label} repeats canonical identity {identity_id}",
        )
        by_id[identity_id] = raw
        declarations = [raw["canonical_declaration"], *raw["member_declarations"]]
        for declaration in declarations:
            _expect(
                isinstance(declaration, str),
                "h_j_identity_partition_invalid",
                f"{label} identity {identity_id} has a non-string declaration",
            )
            previous = by_declaration.get(declaration)
            _expect(
                previous is None or previous.get("identity_id") == identity_id,
                "h_j_identity_partition_invalid",
                f"{label} declaration {declaration} belongs to two identities",
            )
            by_declaration[declaration] = raw
    return by_id, by_declaration


def _load_r1_suite(
    path: Path,
    *,
    epoch: str,
    matrix: Mapping[str, Any],
    label: str,
) -> dict[str, dict[str, Any]]:
    value = _read_json(path, label=label)
    _expect(
        set(value) == {"schema_version", "suite_id", "cases"}
        and value.get("schema_version") == R1_SUITE_SCHEMAS[epoch]
        and isinstance(value.get("suite_id"), str)
        and isinstance(value.get("cases"), list)
        and len(value["cases"]) == 10,
        "h_j_r1_suite_invalid",
        f"{label} is not a ten-case answer-free R1 suite",
    )
    _, by_declaration = _identity_universe(matrix, label=f"{label} matrix")
    result: dict[str, dict[str, Any]] = {}
    case_ids: set[str] = set()
    expected_fields = (
        {"case_id", "module", "problem", "family"}
        if epoch == "v1"
        else {"case_id", "module", "problem", "family", "budget_profile"}
    )
    for index, row in enumerate(value["cases"]):
        _expect(
            isinstance(row, Mapping)
            and set(row) == expected_fields
            and isinstance(row.get("case_id"), str)
            and isinstance(row.get("module"), str)
            and isinstance(row.get("problem"), str)
            and isinstance(row.get("family"), str)
            and (
                epoch == "v1"
                or isinstance(row.get("budget_profile"), (str, Mapping))
            ),
            "h_j_r1_suite_invalid",
            f"{label} case {index} is invalid",
        )
        identity = by_declaration.get(str(row["problem"]))
        _expect(
            identity is not None
            and identity.get("family") == row["family"]
            and row["case_id"] not in case_ids,
            "h_j_r1_suite_invalid",
            f"{label} case {row.get('case_id')} has no unique canonical identity",
        )
        identity_id = str(identity["identity_id"])
        _expect(
            identity_id not in result,
            "h_j_identity_partition_invalid",
            f"{label} repeats canonical identity {identity_id}",
        )
        case_ids.add(str(row["case_id"]))
        result[identity_id] = {
            "partition": "R1-zero-weight",
            "case_id": str(row["case_id"]),
            "split": "r1-public",
            "family": str(row["family"]),
            "canonical_identity": identity_id,
            "canonical_problem": str(identity["canonical_declaration"]),
            "canonical_module": str(identity["canonical_module"]),
            "tier": "R1-zero-weight",
            "outcome_class": "zero_weight_control",
            "scored": False,
            "requires_model": False,
        }
    return result


def _capability_placements(
    contract: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for case_id, row in contract.items():
        identity_id = str(row["canonical_identity"])
        _expect(
            identity_id not in result,
            "h_j_identity_partition_invalid",
            f"capability contract repeats canonical identity {identity_id}",
        )
        result[identity_id] = {
            "partition": "capability",
            "case_id": case_id,
            "split": row["split"],
            "family": row["family"],
            "canonical_identity": identity_id,
            "canonical_problem": row["canonical_problem"],
            "canonical_module": row["canonical_module"],
            "tier": row["tier"],
            "outcome_class": row["outcome_class"],
            "scored": row["scored"],
            "requires_model": row["requires_model"],
            "expected_public_status": row["expected_public_status"],
            "expected_failure_codes": list(row["expected_failure_codes"]),
        }
    return result


def _contract_asset_record(
    *,
    epoch: str,
    version: str,
    bundle: Any,
    oracle_path: Path,
    target_matrix_path: Path,
    r1_suite_path: Path,
    oracle_relocated_for_scorer: bool = False,
) -> dict[str, Any]:
    return {
        "contract_epoch": epoch,
        "contract_version": version,
        "manifest": {
            "file": str(bundle.manifest.path),
            "sha256": _sha256(bundle.manifest.path, tagged=True),
        },
        "oracle": {
            "file": str(oracle_path),
            "sha256": _sha256(oracle_path, tagged=True),
            "runner_access": "forbidden",
            "manifest_embedded_file": str(bundle.manifest.oracle.path),
            "relocated_for_scorer": oracle_relocated_for_scorer,
        },
        "suites": {
            split: {
                "file": str(bundle.manifest.suites[split].path),
                "sha256": bundle.manifest.suites[split].sha256,
            }
            for split in CAPABILITY_SPLITS
        },
        "target_matrix": {
            "file": str(target_matrix_path),
            "sha256": _sha256(target_matrix_path, tagged=True),
            "matrix_id": bundle.target_matrix.get("matrix_id"),
        },
        "r1_suite": {
            "file": str(r1_suite_path),
            "sha256": _sha256(r1_suite_path, tagged=True),
        },
        "case_count": 34,
        "r1_case_count": 10,
        "identity_partition_count": 44,
    }


def _strict_v2_refinement_motif(value: Any, *, case_id: str) -> dict[str, Any]:
    """Validate the only hidden payload that may change from v2a to v2b."""

    label = f"v2b oracle case {case_id}.required_authoring_motif"
    expected_fields = {
        "task_class",
        "nodes",
        "terminal_node_id",
        "final_program_node_id",
    }
    _expect(
        isinstance(value, Mapping) and set(value) == expected_fields,
        "h_j_v2_refinement_invalid",
        f"{label} is not a strict motif object",
    )
    task_class = value["task_class"]
    nodes_value = value["nodes"]
    _expect(
        isinstance(task_class, str)
        and task_class in NP_HARD_AUTHORING_TASK_CLASSES_V2
        and isinstance(nodes_value, list)
        and bool(nodes_value),
        "h_j_v2_refinement_invalid",
        f"{label} has an invalid task class or empty node list",
    )
    prior: set[str] = set()
    nodes: list[dict[str, Any]] = []
    depended_on: set[str] = set()
    for index, raw_node in enumerate(nodes_value):
        _expect(
            isinstance(raw_node, Mapping)
            and set(raw_node) == {"node_id", "capability", "depends_on"},
            "h_j_v2_refinement_invalid",
            f"{label}.nodes[{index}] is not a strict motif node",
        )
        node_id = raw_node["node_id"]
        capability = raw_node["capability"]
        dependencies = raw_node["depends_on"]
        _expect(
            isinstance(node_id, str)
            and bool(node_id)
            and node_id not in prior
            and isinstance(capability, str)
            and bool(capability)
            and isinstance(dependencies, list)
            and all(isinstance(item, str) and item for item in dependencies)
            and len(dependencies) == len(set(dependencies))
            and all(item in prior for item in dependencies),
            "h_j_v2_refinement_invalid",
            f"{label}.nodes[{index}] is duplicated or not topologically ordered",
        )
        prior.add(node_id)
        depended_on.update(dependencies)
        nodes.append(
            {
                "node_id": node_id,
                "capability": capability,
                "depends_on": list(dependencies),
            }
        )
    terminal_node_id = value["terminal_node_id"]
    final_program_node_id = value["final_program_node_id"]
    _expect(
        isinstance(terminal_node_id, str)
        and terminal_node_id in prior
        and prior - depended_on == {terminal_node_id}
        and (
            final_program_node_id is None
            or (
                isinstance(final_program_node_id, str)
                and final_program_node_id in prior
            )
        ),
        "h_j_v2_refinement_invalid",
        f"{label} has an invalid terminal or final program node",
    )
    return {
        "task_class": task_class,
        "nodes": nodes,
        "terminal_node_id": terminal_node_id,
        "final_program_node_id": final_program_node_id,
    }


def _validate_v2_oracle_refinement(
    v2a_oracle: Mapping[str, Any],
    v2b_oracle: Mapping[str, Any],
) -> list[dict[str, Any]]:
    """Require a field-exact oracle refinement at the two MaxCut cases."""

    _expect(
        set(v2a_oracle) == set(v2b_oracle) == {"schema_version", "benchmark_id", "cases"}
        and v2a_oracle["schema_version"] == v2b_oracle["schema_version"]
        and v2a_oracle["benchmark_id"] == v2b_oracle["benchmark_id"]
        and isinstance(v2a_oracle["cases"], list)
        and isinstance(v2b_oracle["cases"], list)
        and len(v2a_oracle["cases"]) == len(v2b_oracle["cases"]) == 34,
        "h_j_v2_refinement_invalid",
        "v2a/v2b scorer oracles do not share one 34-case envelope",
    )
    allowed = set(V2_REFINEMENT_CASE_IDS)
    changes: list[dict[str, Any]] = []
    observed_ids: list[str] = []
    for index, (before_raw, after_raw) in enumerate(
        zip(v2a_oracle["cases"], v2b_oracle["cases"], strict=True)
    ):
        _expect(
            isinstance(before_raw, Mapping)
            and isinstance(after_raw, Mapping)
            and isinstance(before_raw.get("case_id"), str)
            and before_raw.get("case_id") == after_raw.get("case_id"),
            "h_j_v2_refinement_invalid",
            f"v2a/v2b oracle row {index} changed case identity or ordering",
        )
        case_id = str(before_raw["case_id"])
        observed_ids.append(case_id)
        if case_id not in allowed:
            _expect(
                dict(before_raw) == dict(after_raw),
                "h_j_v2_refinement_invalid",
                f"v2b changed a forbidden oracle field for {case_id}",
            )
            continue
        before = dict(before_raw)
        after = dict(after_raw)
        before_motif = before.pop("required_authoring_motif", None)
        after_motif = after.pop("required_authoring_motif", None)
        _expect(
            before_motif is None and before == after,
            "h_j_v2_refinement_invalid",
            f"{case_id} changed more than its hidden authoring motif",
        )
        motif = _strict_v2_refinement_motif(after_motif, case_id=case_id)
        motif_id = sha256_id(motif)
        _expect(
            motif == V2_REFINEMENT_REQUIRED_MOTIFS[case_id]
            and motif_id == V2_REFINEMENT_REQUIRED_MOTIF_IDS[case_id],
            "h_j_v2_refinement_invalid",
            f"{case_id} does not carry its frozen target-specific motif",
        )
        changes.append(
            {
                "case_id": case_id,
                "field": "required_authoring_motif",
                "from": None,
                "to": motif,
                "motif_id": motif_id,
            }
        )
    _expect(
        len(observed_ids) == len(set(observed_ids)) == 34
        and {row["case_id"] for row in changes} == allowed,
        "h_j_v2_refinement_invalid",
        "v2b must add strict motifs to exactly the two frozen MaxCut cases",
    )
    return changes


def validate_v2_contract_refinement(
    *,
    v2a: Mapping[str, Any],
    v2b: Mapping[str, Any],
) -> dict[str, Any]:
    """Prove v2a and v2b are content subversions of one denominator."""

    v2a_bundle = v2a["bundle"]
    v2b_bundle = v2b["bundle"]
    _expect(
        v2a.get("epoch") == v2b.get("epoch") == "v2"
        and v2a.get("version") == "v2a"
        and v2b.get("version") == "v2b",
        "h_j_v2_refinement_invalid",
        "refinement inputs are not the frozen v2a/v2b versions",
    )
    suite_invariants = {
        split: (
            v2a_bundle.manifest.suites[split].path
            == v2b_bundle.manifest.suites[split].path
            and v2a_bundle.manifest.suites[split].sha256
            == v2b_bundle.manifest.suites[split].sha256
            and v2a_bundle.suites[split] == v2b_bundle.suites[split]
        )
        for split in CAPABILITY_SPLITS
    }
    identity_invariant = (
        v2a_bundle.case_identity == v2b_bundle.case_identity
        and set(v2a["contract"]) == set(v2b["contract"])
        and all(
            all(
                v2a["contract"][case_id][field]
                == v2b["contract"][case_id][field]
                for field in (
                    "split",
                    "family",
                    "canonical_identity",
                    "canonical_problem",
                    "canonical_module",
                )
            )
            for case_id in v2a["contract"]
        )
    )
    matrix_invariant = (
        v2a_bundle.manifest.target_matrix.path
        == v2b_bundle.manifest.target_matrix.path
        and v2a_bundle.manifest.target_matrix.sha256
        == v2b_bundle.manifest.target_matrix.sha256
        and v2a_bundle.target_matrix == v2b_bundle.target_matrix
    )
    scope_invariant = (
        v2a_bundle.manifest.scope_policy.path
        == v2b_bundle.manifest.scope_policy.path
        and v2a_bundle.manifest.scope_policy.sha256
        == v2b_bundle.manifest.scope_policy.sha256
    )
    r1_invariant = (
        v2a["r1"] == v2b["r1"]
        and v2a["assets"]["r1_suite"]["sha256"]
        == v2b["assets"]["r1_suite"]["sha256"]
    )
    model_invariant = (
        v2a_bundle.manifest.required_model_profile
        == v2b_bundle.manifest.required_model_profile
        == FORMAL_MANIFEST_MODEL
    )
    contract_counts_invariant = (
        v2a_bundle.manifest.contract_counts
        == v2b_bundle.manifest.contract_counts
    )
    _expect(
        identity_invariant
        and matrix_invariant
        and scope_invariant
        and r1_invariant
        and model_invariant
        and contract_counts_invariant
        and all(suite_invariants.values()),
        "h_j_v2_refinement_invalid",
        "v2a/v2b changed the public denominator, matrix, scope, model, or counts",
    )

    v2a_manifest = _read_json(
        v2a_bundle.manifest.path, label="v2a capability manifest"
    )
    v2b_manifest = _read_json(
        v2b_bundle.manifest.path, label="v2b capability manifest"
    )
    manifest_before = deepcopy(v2a_manifest)
    manifest_after = deepcopy(v2b_manifest)
    before_oracle_reference = manifest_before.get("oracle")
    after_oracle_reference = manifest_after.get("oracle")
    _expect(
        isinstance(before_oracle_reference, Mapping)
        and isinstance(after_oracle_reference, Mapping),
        "h_j_v2_refinement_invalid",
        "v2 manifest oracle references are invalid",
    )
    manifest_before["oracle"] = {
        **dict(before_oracle_reference),
        "sha256": "<content-addressed-oracle>",
    }
    manifest_after["oracle"] = {
        **dict(after_oracle_reference),
        "sha256": "<content-addressed-oracle>",
    }
    _expect(
        manifest_before == manifest_after
        and before_oracle_reference.get("file")
        == after_oracle_reference.get("file")
        and before_oracle_reference.get("runner_access")
        == after_oracle_reference.get("runner_access")
        and before_oracle_reference.get("sha256")
        == _sha256(v2a["oracle_path"])
        and after_oracle_reference.get("sha256")
        == _sha256(v2b["oracle_path"]),
        "h_j_v2_refinement_invalid",
        "v2b manifest changed more than its content-addressed oracle hash",
    )
    changes = _validate_v2_oracle_refinement(
        _read_json(v2a["oracle_path"], label="v2a capability oracle"),
        _read_json(v2b["oracle_path"], label="v2b capability oracle"),
    )
    v2a_manifest_hash = _sha256(v2a_bundle.manifest.path, tagged=True)
    v2b_manifest_hash = _sha256(v2b_bundle.manifest.path, tagged=True)
    v2a_oracle_hash = _sha256(v2a["oracle_path"], tagged=True)
    v2b_oracle_hash = _sha256(v2b["oracle_path"], tagged=True)
    _expect(
        v2a_manifest_hash != v2b_manifest_hash
        and v2a_oracle_hash != v2b_oracle_hash,
        "h_j_v2_refinement_invalid",
        "v2a/v2b content addresses did not change with the two added motifs",
    )
    audit: dict[str, Any] = {
        "schema_version": V2_REFINEMENT_AUDIT_SCHEMA,
        "passed": True,
        "denominator_epoch": "v2",
        "from_contract_version": "v2a",
        "to_contract_version": "v2b",
        "assets": {"v2a": v2a["assets"], "v2b": v2b["assets"]},
        "invariants": {
            "case_count_34": len(v2a["contract"]) == len(v2b["contract"]) == 34,
            "canonical_identity_and_public_cases_exact": identity_invariant,
            "public_suites_exact": suite_invariants,
            "target_matrix_exact": matrix_invariant,
            "scope_policy_exact": scope_invariant,
            "r1_zero_weight_suite_exact": r1_invariant,
            "formal_model_profile_exact": model_invariant,
            "contract_counts_exact": contract_counts_invariant,
            "manifest_only_oracle_hash_changed": True,
            "all_other_oracle_fields_byte_for_field_equal": True,
        },
        "allowed_hidden_refinement_case_ids": list(V2_REFINEMENT_CASE_IDS),
        "hidden_oracle_refinements": changes,
    }
    audit["audit_id"] = sha256_id(audit)
    return audit


def _validate_migration_transition(
    *,
    expected: Mapping[str, Any],
    before: Mapping[str, Any],
    after: Mapping[str, Any],
) -> dict[str, Any]:
    canonical_problem = str(expected["canonical_problem"])
    _expect(
        before.get("canonical_problem") == canonical_problem
        and after.get("canonical_problem") == canonical_problem
        and before.get("case_id") == expected["from_case_id"]
        and after.get("case_id") == expected["to_case_id"],
        "h_j_migration_crosswalk_invalid",
        f"migration transition for {canonical_problem} does not match the frozen mapping",
    )
    classification = str(expected["classification"])
    if classification == "unary_numeric_demotion":
        _expect(
            before.get("partition") == after.get("partition") == "capability"
            and before.get("split") == "validation"
            and before.get("tier") == "C0-authoring"
            and before.get("scored") is True
            and after.get("split") == "frontier"
            and after.get("tier") == "F0-frontier"
            and after.get("scored") is False
            and after.get("expected_public_status")
            == "BLOCKED_MISSING_PREREQUISITE"
            and MIGRATION_BOUNDARY_FAILURE
            in after.get("expected_failure_codes", []),
            "h_j_migration_crosswalk_invalid",
            f"{canonical_problem} is not an explicit unary numeric F0 demotion",
        )
    elif classification == "unary_numeric_zero_weight_boundary":
        _expect(
            before.get("partition") == "capability"
            and before.get("split") == "heldout"
            and before.get("tier") == "C0-authoring"
            and after.get("partition") == "R1-zero-weight"
            and after.get("requires_model") is False,
            "h_j_migration_crosswalk_invalid",
            f"{canonical_problem} is not an R1 zero-weight unary boundary",
        )
    elif classification == "frontier_to_scored_authoring":
        _expect(
            before.get("partition") == after.get("partition") == "capability"
            and before.get("split") == "frontier"
            and before.get("tier") == "F0-frontier"
            and before.get("scored") is False
            and after.get("split") == "heldout"
            and after.get("tier") == "C0-authoring"
            and after.get("scored") is True,
            "h_j_migration_crosswalk_invalid",
            f"{canonical_problem} is not a heldout scored authoring promotion",
        )
    elif classification == "zero_weight_to_scored_existing":
        _expect(
            before.get("partition") == "R1-zero-weight"
            and after.get("partition") == "capability"
            and after.get("split") == "validation"
            and after.get("tier") == "C0-existing"
            and after.get("scored") is True,
            "h_j_migration_crosswalk_invalid",
            f"{canonical_problem} is not a validation existing-route promotion",
        )
    elif classification == "split_rebalance":
        _expect(
            before.get("partition") == after.get("partition") == "capability"
            and before.get("split") == "heldout"
            and after.get("split") == "validation"
            and before.get("tier") == after.get("tier") == "C0-authoring"
            and before.get("scored") is after.get("scored") is True,
            "h_j_migration_crosswalk_invalid",
            f"{canonical_problem} is not the frozen heldout-to-validation rebalance",
        )
    else:
        _fail(
            "h_j_migration_crosswalk_invalid",
            f"unsupported migration classification {classification}",
        )
    return {
        **dict(expected),
        "canonical_identity": before["canonical_identity"],
        "family": before["family"],
        "v1": dict(before),
        "v2": dict(after),
        "accepted_without_failure": classification.startswith("unary_numeric_"),
    }


def validate_capability_migration(
    *,
    v1: Mapping[str, Any],
    v2: Mapping[str, Any],
) -> dict[str, Any]:
    v1_ids, _ = _identity_universe(v1["bundle"].target_matrix, label="v1 target matrix")
    v2_ids, _ = _identity_universe(v2["bundle"].target_matrix, label="v2 target matrix")
    _expect(
        set(v1_ids) == set(v2_ids) and len(v1_ids) == 44,
        "h_j_migration_identity_universe_changed",
        "v1/v2 target matrices do not preserve the same 44 canonical identities",
    )
    for identity_id in sorted(v1_ids):
        before = v1_ids[identity_id]
        after = v2_ids[identity_id]
        _expect(
            all(
                before.get(key) == after.get(key)
                for key in ("canonical_declaration", "canonical_module", "family")
            ),
            "h_j_migration_identity_universe_changed",
            f"canonical identity {identity_id} declaration/module/family drifted",
        )

    v1_capability = _capability_placements(v1["contract"])
    v2_capability = _capability_placements(v2["contract"])
    v1_r1 = v1["r1"]
    v2_r1 = v2["r1"]
    _expect(
        len(v1_capability) == len(v2_capability) == 34
        and len(v1_r1) == len(v2_r1) == 10
        and not (set(v1_capability) & set(v1_r1))
        and not (set(v2_capability) & set(v2_r1))
        and set(v1_capability) | set(v1_r1) == set(v1_ids)
        and set(v2_capability) | set(v2_r1) == set(v2_ids),
        "h_j_identity_partition_invalid",
        "v1/v2 capability+R1 partitions are not disjoint exhaustive 34+10 sets",
    )
    v1_placements = {**v1_capability, **v1_r1}
    v2_placements = {**v2_capability, **v2_r1}
    expected_by_problem = {
        str(row["canonical_problem"]): row for row in MIGRATION_TRANSITIONS
    }
    transition_rows: list[dict[str, Any]] = []
    identity_rows: list[dict[str, Any]] = []
    unchanged = 0
    for identity_id in sorted(v1_ids):
        identity = v1_ids[identity_id]
        canonical_problem = str(identity["canonical_declaration"])
        before = v1_placements[identity_id]
        after = v2_placements[identity_id]
        expected = expected_by_problem.get(canonical_problem)
        if expected is None:
            _expect(
                before == after,
                "h_j_migration_crosswalk_invalid",
                f"unapproved migration for canonical identity {identity_id}",
            )
            classification = "unchanged"
            reason = None
            unchanged += 1
        else:
            transition = _validate_migration_transition(
                expected=expected, before=before, after=after
            )
            transition_rows.append(transition)
            classification = str(expected["classification"])
            reason = str(expected["reason"])
        identity_rows.append(
            {
                "canonical_identity": identity_id,
                "canonical_problem": canonical_problem,
                "canonical_module": identity["canonical_module"],
                "family": identity["family"],
                "classification": classification,
                "reason": reason,
                "v1": dict(before),
                "v2": dict(after),
            }
        )
    _expect(
        len(transition_rows) == 7 and unchanged == 37,
        "h_j_migration_crosswalk_invalid",
        "migration must contain exactly seven approved transitions and 37 unchanged identities",
    )
    _expect(
        {row["canonical_problem"] for row in transition_rows}
        == set(expected_by_problem),
        "h_j_migration_crosswalk_invalid",
        "one or more frozen migration transitions were not observed",
    )

    capability_crosswalk = [
        row for row in identity_rows if row["canonical_identity"] in v2_capability
    ]
    _expect(
        len(capability_crosswalk) == 34,
        "h_j_migration_crosswalk_invalid",
        "v2 capability denominator crosswalk is not 34 canonical identities",
    )
    demotions = [
        row
        for row in transition_rows
        if str(row["classification"]).startswith("unary_numeric_")
    ]
    _expect(
        len(demotions) == 3
        and all(row.get("reason") == MIGRATION_BOUNDARY_FAILURE for row in demotions),
        "h_j_migration_crosswalk_invalid",
        "unary numeric demotions lack the frozen polynomial reverse-bridge reason",
    )
    audit: dict[str, Any] = {
        "schema_version": MIGRATION_AUDIT_SCHEMA,
        "passed": True,
        "contracts": {
            "v1": v1["assets"],
            "v2": v2["assets"],
        },
        "stage_contract_epochs": dict(STAGE_CONTRACT_EPOCH),
        "stage_contract_versions": dict(STAGE_CONTRACT_VERSION),
        "identity_universe": {
            "count": 44,
            "canonical_identity_set_preserved": True,
            "canonical_declaration_module_family_preserved": True,
            "unchanged_count": unchanged,
            "approved_transition_count": len(transition_rows),
            "crosswalk": identity_rows,
        },
        "capability_denominator": {
            "v1_count": 34,
            "v2_count": 34,
            "shared_identity_count": len(set(v1_capability) & set(v2_capability)),
            "departed_to_r1": sorted(set(v1_capability) - set(v2_capability)),
            "introduced_from_r1": sorted(set(v2_capability) - set(v1_capability)),
            "canonical_identity_crosswalk_count": len(capability_crosswalk),
            "canonical_identity_crosswalk": capability_crosswalk,
        },
        "r1_zero_weight_partition": {
            "v1_count": 10,
            "v2_count": 10,
            "shared_identity_count": len(set(v1_r1) & set(v2_r1)),
            "crosswalk": [
                row
                for row in identity_rows
                if row["canonical_identity"] in set(v1_r1) | set(v2_r1)
            ],
        },
        "approved_transitions": sorted(
            transition_rows, key=lambda row: str(row["from_case_id"])
        ),
        "accepted_unary_numeric_demotions": sorted(
            demotions, key=lambda row: str(row["from_case_id"])
        ),
        "cross_epoch_metric_policy": {
            "stage_curves_directly_comparable": False,
            "note": (
                "H-J.1-.3 are native v1 evidence; H-J.4 is native v2a; "
                "H-J.5 and final gates are native v2b"
            ),
            "final_gate_contract_epoch": "v2",
            "final_gate_contract_version": "v2b",
        },
    }
    audit["audit_id"] = sha256_id(audit)
    return audit


def validate_h_j_4_migration_archive(
    path: Path,
    *,
    v1: Mapping[str, Any],
    v2a: Mapping[str, Any],
) -> dict[str, Any]:
    """Bind the archived H-J.4 migration audit and its historical live paths."""

    report = _read_json(path, label="H-J.4 migration archive")
    report_hash = _sha256(path, tagged=True)
    _expect(
        report_hash == H_J_4_V2_MIGRATION_SHA256
        and report.get("schema_version") == MIGRATION_AUDIT_SCHEMA
        and report.get("passed") is True
        and report.get("audit_id")
        == _canonical_content_hash(report, field="audit_id"),
        "h_j_h_j_4_archive_invalid",
        "H-J.4 migration archive is not the frozen content-addressed audit",
    )
    contracts = report.get("contracts")
    _expect(
        isinstance(contracts, Mapping)
        and set(contracts) == {"v1", "v2"}
        and isinstance(contracts.get("v1"), Mapping)
        and isinstance(contracts.get("v2"), Mapping),
        "h_j_h_j_4_archive_invalid",
        "H-J.4 migration archive lacks v1/v2 contracts",
    )

    def validate_contract_record(
        raw: Mapping[str, Any], expected: Mapping[str, Any], *, label: str
    ) -> None:
        assets = expected["assets"]
        suites = raw.get("suites")
        _expect(
            isinstance(raw.get("manifest"), Mapping)
            and _hashes_equal(
                raw["manifest"].get("sha256"), assets["manifest"]["sha256"]
            )
            and isinstance(raw.get("oracle"), Mapping)
            and _hashes_equal(
                raw["oracle"].get("sha256"), assets["oracle"]["sha256"]
            )
            and raw["oracle"].get("runner_access") == "forbidden"
            and isinstance(raw.get("target_matrix"), Mapping)
            and _hashes_equal(
                raw["target_matrix"].get("sha256"),
                assets["target_matrix"]["sha256"],
            )
            and raw["target_matrix"].get("matrix_id")
            == assets["target_matrix"]["matrix_id"]
            and isinstance(raw.get("r1_suite"), Mapping)
            and _hashes_equal(
                raw["r1_suite"].get("sha256"), assets["r1_suite"]["sha256"]
            )
            and isinstance(suites, Mapping)
            and set(suites) == set(CAPABILITY_SPLITS)
            and all(
                isinstance(suites[split], Mapping)
                and _hashes_equal(
                    suites[split].get("sha256"),
                    assets["suites"][split]["sha256"],
                )
                for split in CAPABILITY_SPLITS
            )
            and raw.get("case_count") == 34
            and raw.get("r1_case_count") == 10
            and raw.get("identity_partition_count") == 44,
            "h_j_h_j_4_archive_invalid",
            f"H-J.4 migration archive {label} asset hashes drifted",
        )

    validate_contract_record(contracts["v1"], v1, label="v1")
    validate_contract_record(contracts["v2"], v2a, label="v2a")
    historical_manifest_path = _repo_reference(
        contracts["v2"]["manifest"].get("file"),
        label="H-J.4 historical live manifest",
    )
    historical_oracle_path = _repo_reference(
        contracts["v2"]["oracle"].get("file"),
        label="H-J.4 historical live oracle",
    )
    _expect(
        v2a["bundle"].manifest.oracle.path == historical_oracle_path
        and _hashes_equal(
            v2a["bundle"].manifest.oracle.sha256,
            _sha256(v2a["oracle_path"]),
        ),
        "h_j_h_j_4_archive_invalid",
        "archived manifest does not embed the old scorer oracle hash/path",
    )
    return {
        "file": str(path),
        "sha256": report_hash,
        "audit_id": report["audit_id"],
        "historical_live_manifest": str(historical_manifest_path),
        "historical_live_oracle": str(historical_oracle_path),
        "manifest_hash": v2a["assets"]["manifest"]["sha256"],
        "oracle_hash": v2a["assets"]["oracle"]["sha256"],
        "passed": True,
    }


def _scorecard_from_rows(
    rows: Sequence[Mapping[str, Any]],
    *,
    contract: Mapping[str, Mapping[str, Any]],
    label: str,
) -> dict[str, Any]:
    by_id: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        case_id = row.get("case_id")
        _expect(
            isinstance(case_id, str) and case_id in contract and case_id not in by_id,
            "h_j_capability_score_invalid",
            f"{label} repeats or invents a case_id",
        )
        by_id[case_id] = row
    _expect(
        set(by_id) == set(contract),
        "h_j_capability_score_invalid",
        f"{label} does not contain all 34 oracle identities",
    )

    family_groups: dict[str, list[bool]] = {}
    authoring_groups: dict[str, list[bool]] = {}
    verified_authoring: list[dict[str, Any]] = []
    positive_success = 0
    first_attempt_success = 0
    positive_model_calls = 0
    safety_correct = 0
    frontier: list[dict[str, Any]] = []
    status_matrix: dict[str, dict[str, int]] = {}

    for case_id, expected in contract.items():
        row = by_id[case_id]
        _expect(
            row.get("split") == expected["split"]
            and row.get("family") == expected["family"]
            and row.get("tier") == expected["tier"]
            and row.get("outcome_class") == expected["outcome_class"]
            and row.get("scored") is expected["scored"]
            and row.get("requires_model") is expected["requires_model"],
            "h_j_capability_score_invalid",
            f"{label} case {case_id} differs from the scorer-only oracle",
        )
        calls = row.get("model_calls")
        success_claim = row.get("capability_success")
        _expect(
            isinstance(calls, int)
            and not isinstance(calls, bool)
            and calls >= 0
            and isinstance(success_claim, bool),
            "h_j_capability_score_invalid",
            f"{label} case {case_id} has invalid score primitives",
        )
        public_status = row.get("public_status")
        failure_code = row.get("failure_code")
        surface_success = False
        if expected["tier"] == "C0-existing":
            surface_success = bool(
                public_status == "VERIFIED" and failure_code is None and calls == 0
            )
        elif expected["tier"] == "C0-authoring":
            surface_success = bool(
                public_status == "VERIFIED" and failure_code is None and calls > 0
            )
        elif expected["tier"] == "C0-safety":
            surface_success = bool(
                public_status == expected["expected_public_status"]
                and failure_code in expected["expected_failure_codes"]
                and calls == 0
            )
        elif expected["tier"] == "F0-frontier":
            frontier.append(
                {
                    "case_id": case_id,
                    "family": expected["family"],
                    "canonical_identity": expected["canonical_identity"],
                    "canonical_problem": expected["canonical_problem"],
                    "public_status": public_status,
                    "failure_code": failure_code,
                    "model_calls": calls,
                    "capability_success": success_claim,
                }
            )
        accepted_success = bool(success_claim and surface_success)
        statuses = status_matrix.setdefault(str(expected["tier"]), {})
        status_key = str(public_status)
        statuses[status_key] = statuses.get(status_key, 0) + 1

        if expected["outcome_class"] in {"existing_route", "first_authoring"}:
            family_groups.setdefault(str(expected["family"]), []).append(
                accepted_success
            )
            positive_success += int(accepted_success)
            positive_model_calls += calls
            first_attempt_success += int(
                accepted_success and row.get("first_attempt_verified") is True
            )
        if expected["tier"] == "C0-authoring":
            authoring_groups.setdefault(str(expected["family"]), []).append(
                accepted_success
            )
            if accepted_success:
                verified_authoring.append(
                    {
                        "case_id": case_id,
                        "split": expected["split"],
                        "family": expected["family"],
                        "canonical_identity": expected["canonical_identity"],
                        "canonical_problem": expected["canonical_problem"],
                        "model_calls": calls,
                        "first_attempt_verified": (
                            row.get("first_attempt_verified") is True
                        ),
                    }
                )
        if expected["tier"] == "C0-safety":
            safety_correct += int(accepted_success)

    identities = [row["canonical_identity"] for row in verified_authoring]
    _expect(
        len(identities) == len(set(identities)),
        "h_j_duplicate_capability_identity",
        f"{label} double-counted an authored canonical identity",
    )
    family_scorecard = _macro(family_groups)
    authoring_scorecard = _macro(authoring_groups)
    return {
        "case_count": len(by_id),
        "unique_identity_count": len(
            {expected["canonical_identity"] for expected in contract.values()}
        ),
        "positive_case_count": sum(len(rows) for rows in family_groups.values()),
        "verified_at_budget_count": positive_success,
        "verified_at_budget_rate": _rate(
            positive_success, sum(len(rows) for rows in family_groups.values())
        ),
        "verified_at_first_attempt_count": first_attempt_success,
        "family_scorecard": family_scorecard,
        "first_authoring_scorecard": authoring_scorecard,
        "family_macro_verified_at_budget": family_scorecard["macro_score"],
        "first_authoring_family_macro": authoring_scorecard["macro_score"],
        "verified_authoring": sorted(
            verified_authoring, key=lambda row: str(row["case_id"])
        ),
        "verified_authoring_identity_count": len(verified_authoring),
        "verified_authoring_family_count": len(
            {row["family"] for row in verified_authoring}
        ),
        "verified_authoring_families": sorted(
            {str(row["family"]) for row in verified_authoring}
        ),
        "heldout_verified_authoring_identity_count": sum(
            row["split"] == "heldout" for row in verified_authoring
        ),
        "safety_correct_count": safety_correct,
        "safety_case_count": sum(
            expected["tier"] == "C0-safety" for expected in contract.values()
        ),
        "positive_model_calls": positive_model_calls,
        "outcome_matrix": {
            tier: dict(sorted(statuses.items()))
            for tier, statuses in sorted(status_matrix.items())
        },
        "frontier": sorted(frontier, key=lambda row: str(row["case_id"])),
    }


def _frozen_h_i_baseline(
    report: Mapping[str, Any],
    *,
    contract: Mapping[str, Mapping[str, Any]],
    v1: Mapping[str, Any],
) -> dict[str, Any]:
    baseline = report.get("capability_baseline")
    _expect(
        isinstance(baseline, Mapping)
        and baseline.get("case_count") == 34
        and baseline.get("run_valid") is True
        and baseline.get("score_valid") is True
        and baseline.get("regression_scores_used") is False,
        "h_j_h_i_baseline_invalid",
        "H-I capability baseline is absent or invalid",
    )
    expected_outcomes = {
        "C0-authoring": {"BLOCKED_MISSING_PREREQUISITE": 12},
        "C0-existing": {"VERIFIED": 12},
        "C0-safety": {"BLOCKED_NOT_TARGET": 8},
        "F0-frontier": {"BLOCKED_MISSING_PREREQUISITE": 2},
    }
    _expect(
        baseline.get("outcome_matrix") == expected_outcomes,
        "h_j_h_i_baseline_invalid",
        "H-I no-route baseline no longer has 12 blocked C0 authoring identities",
    )
    guardrails = baseline.get("security_guardrails")
    _expect(
        isinstance(guardrails, Mapping)
        and all(value == 0 for value in guardrails.values()),
        "h_j_h_i_baseline_invalid",
        "H-I safety baseline is not clean",
    )
    split_reports = baseline.get("split_reports")
    split_rows = {
        row.get("split"): row
        for row in split_reports
        if isinstance(row, Mapping) and isinstance(row.get("split"), str)
    } if isinstance(split_reports, list) else {}
    _expect(
        set(split_rows) == set(CAPABILITY_SPLITS),
        "h_j_h_i_baseline_invalid",
        "H-I baseline does not bind all four splits",
    )
    for split in CAPABILITY_SPLITS:
        row = split_rows[split]
        run = row.get("run")
        score = row.get("score")
        metrics = score.get("metrics") if isinstance(score, Mapping) else None
        _expect(
            isinstance(run, Mapping)
            and run.get("run_valid") is True
            and run.get("case_count") == CAPABILITY_SPLIT_COUNTS[split]
            and isinstance(score, Mapping)
            and score.get("score_valid") is True
            and isinstance(metrics, Mapping),
            "h_j_h_i_baseline_invalid",
            f"H-I {split} split evidence is invalid",
        )
        if split != "frontier":
            _expect(
                metrics.get("existing_route_family_macro") == 1.0
                and metrics.get("first_authoring_family_macro") == 0.0
                and metrics.get("safety_correct_rate") == 1.0,
                "h_j_h_i_baseline_invalid",
                f"H-I {split} baseline metrics drifted",
            )

    bundle = v1["bundle"]
    manifest_hash = _sha256(bundle.manifest.path, tagged=True)
    oracle_hash = _sha256(v1["oracle_path"], tagged=True)
    target_hash = _sha256(bundle.manifest.target_matrix.path, tagged=True)
    evidence_rows: list[Mapping[str, Any]] = []
    evidence_records: list[dict[str, Any]] = []
    for split in CAPABILITY_SPLITS:
        summary = split_rows[split]
        run_summary = summary["run"]
        score_summary = summary["score"]
        run_path = _repo_reference(
            run_summary.get("file"), label=f"H-I {split} raw report"
        )
        score_path = _repo_reference(
            score_summary.get("file"), label=f"H-I {split} score report"
        )
        run_hash = _sha256(run_path, tagged=True)
        score_hash = _sha256(score_path, tagged=True)
        _expect(
            run_summary.get("sha256") == run_hash
            and score_summary.get("sha256") == score_hash,
            "h_j_h_i_baseline_invalid",
            f"H-I {split} summary no longer binds its original raw+score files",
        )
        run = _read_json(run_path, label=f"H-I {split} raw report")
        score = _read_json(score_path, label=f"H-I {split} score report")
        run_cases = run.get("cases")
        score_cases = score.get("cases")
        _expect(
            run.get("schema_version") == CAPABILITY_RUN_SCHEMA_V1
            and run.get("run_valid") is True
            and run.get("selected_splits") == [split]
            and run.get("run_id") == run_summary.get("run_id")
            and run.get("run_id") == _canonical_content_hash(run, field="run_id")
            and isinstance(run_cases, list)
            and len(run_cases) == CAPABILITY_SPLIT_COUNTS[split],
            "h_j_h_i_baseline_invalid",
            f"H-I {split} raw report is not the original valid split execution",
        )
        manifest_record = run.get("manifest")
        target_record = run.get("target_matrix")
        suites = run.get("suites")
        _expect(
            isinstance(manifest_record, Mapping)
            and manifest_record.get("sha256") == manifest_hash
            and manifest_record.get("oracle_opened_by_runner") is False
            and isinstance(target_record, Mapping)
            and target_record.get("sha256") == target_hash
            and isinstance(suites, Mapping)
            and set(suites) == set(CAPABILITY_SPLITS)
            and all(
                isinstance(suites[name], Mapping)
                and suites[name].get("sha256")
                == bundle.manifest.suites[name].sha256
                for name in CAPABILITY_SPLITS
            ),
            "h_j_h_i_baseline_invalid",
            f"H-I {split} raw report does not bind the v1 contract",
        )
        expected_split_ids = {
            case_id
            for case_id, row in contract.items()
            if row["split"] == split
        }
        observed_run_ids = {
            row.get("case_id") for row in run_cases if isinstance(row, Mapping)
        }
        _expect(
            observed_run_ids == expected_split_ids,
            "h_j_h_i_baseline_invalid",
            f"H-I {split} raw report case identities drifted",
        )
        provenance = score.get("provenance")
        integrity = score.get("integrity")
        mutation = score.get("r0_mutation_audit")
        _expect(
            score.get("schema_version") == CAPABILITY_SCORE_SCHEMA_V1
            and score.get("run_valid") is True
            and score.get("score_valid") is True
            and score.get("run_id") == run.get("run_id")
            and score.get("score_id") == score_summary.get("score_id")
            and score.get("score_id")
            == _canonical_content_hash(score, field="score_id")
            and isinstance(score_cases, list)
            and len(score_cases) == CAPABILITY_SPLIT_COUNTS[split]
            and isinstance(provenance, Mapping)
            and isinstance(provenance.get("manifest"), Mapping)
            and provenance["manifest"].get("sha256") == manifest_hash
            and isinstance(provenance.get("oracle"), Mapping)
            and provenance["oracle"].get("sha256") == oracle_hash
            and provenance["oracle"].get("opened_by")
            == "independent scorer only"
            and isinstance(provenance.get("run_report"), Mapping)
            and provenance["run_report"].get("sha256") == run_hash
            and isinstance(integrity, Mapping)
            and bool(integrity)
            and all(value is True for value in integrity.values())
            and isinstance(mutation, Mapping)
            and mutation.get("passed") is True
            and mutation.get("audit_count") == mutation.get("passed_count") == 8,
            "h_j_h_i_baseline_invalid",
            f"H-I {split} score is not independently content-addressed to v1",
        )
        evidence_rows.extend(
            row for row in score_cases if isinstance(row, Mapping)
        )
        evidence_records.append(
            {
                "split": split,
                "run": {
                    "file": str(run_path),
                    "sha256": run_hash,
                    "run_id": run.get("run_id"),
                },
                "score": {
                    "file": str(score_path),
                    "sha256": score_hash,
                    "score_id": score.get("score_id"),
                },
            }
        )
    scorecard = _scorecard_from_rows(
        evidence_rows, contract=contract, label="original H-I v1 score rows"
    )
    _expect(
        scorecard["verified_authoring_identity_count"] == 0,
        "h_j_h_i_baseline_invalid",
        "H-I baseline unexpectedly contains authored successes",
    )
    scorecard["safety"] = {key: 0 for key in SAFETY_FIELDS}
    scorecard["evidence_mode"] = "original_content_addressed_h_i_v1_score_rows"
    scorecard["split_evidence"] = evidence_records
    scorecard["original_score_rows"] = [dict(row) for row in evidence_rows]
    return scorecard


def _load_contract_epoch(
    *,
    epoch: str,
    version: str,
    manifest_path: Path,
    oracle_path: Path,
    target_matrix_path: Path,
    r1_suite_path: Path,
    allow_oracle_relocation: bool = False,
) -> dict[str, Any]:
    _expect(
        version in CONTRACT_VERSIONS
        and CONTRACT_EPOCH_BY_VERSION[version] == epoch,
        "h_j_hash_binding_mismatch",
        f"contract version {version} does not belong to epoch {epoch}",
    )
    bundle = load_capability_bundle(
        manifest_path,
        root=ROOT,
        verify_oracle=not allow_oracle_relocation,
    )
    embedded_oracle_hash_matches = _hashes_equal(
        bundle.manifest.oracle.sha256, _sha256(oracle_path)
    )
    embedded_matrix_matches = (
        bundle.manifest.target_matrix.path == target_matrix_path
        if not allow_oracle_relocation
        else _hashes_equal(
            bundle.manifest.target_matrix.sha256, _sha256(target_matrix_path)
        )
    )
    _expect(
        embedded_matrix_matches
        and embedded_oracle_hash_matches
        and (
            allow_oracle_relocation
            or bundle.manifest.oracle.path == oracle_path
        ),
        "h_j_hash_binding_mismatch",
        f"{version} manifest points at another oracle/hash or target matrix",
    )
    _expect(
        bundle.manifest.required_model_profile == FORMAL_MANIFEST_MODEL,
        "h_j_model_profile_invalid",
        f"{version} capability manifest is not frozen to formal DeepSeek",
    )
    oracle = load_capability_oracle(oracle_path, bundle=bundle)
    _expect(
        len(bundle.cases) == len(oracle) == 34
        and len(
            {
                str(bundle.case_identity[case.case_id]["identity_id"])
                for case in bundle.cases
            }
        )
        == 34,
        "h_j_identity_partition_invalid",
        f"{version} capability denominator is not 34 unique identities",
    )
    contract_input = {
        "capability_bundle": bundle,
        "capability_oracle_object": oracle,
    }
    contract = _case_contract(contract_input)
    tier_counts: dict[str, int] = {}
    for row in contract.values():
        tier = str(row["tier"])
        tier_counts[tier] = tier_counts.get(tier, 0) + 1
    expected_tiers = (
        {
            "C0-existing": 12,
            "C0-authoring": 12,
            "C0-safety": 8,
            "F0-frontier": 2,
        }
        if epoch == "v1"
        else {
            "C0-existing": 13,
            "C0-authoring": 11,
            "C0-safety": 8,
            "F0-frontier": 2,
        }
    )
    _expect(
        tier_counts == expected_tiers,
        "h_j_identity_partition_invalid",
        f"{version} tier partition differs from the frozen migration contract",
    )
    r1 = _load_r1_suite(
        r1_suite_path,
        epoch=epoch,
        matrix=bundle.target_matrix,
        label=f"{version} R1 suite",
    )
    assets = _contract_asset_record(
        epoch=epoch,
        version=version,
        bundle=bundle,
        oracle_path=oracle_path,
        target_matrix_path=target_matrix_path,
        r1_suite_path=r1_suite_path,
        oracle_relocated_for_scorer=allow_oracle_relocation,
    )
    return {
        "epoch": epoch,
        "version": version,
        "bundle": bundle,
        "oracle": oracle,
        "oracle_path": oracle_path,
        "contract": contract,
        "r1": r1,
        "assets": assets,
    }


def validate_static_assets(paths: StaticEvidencePaths) -> dict[str, Any]:
    supplied = dict(paths.__dict__)
    supplied["v2_h_j_4_capability_manifest"] = supplied.get(
        "v2_h_j_4_capability_manifest"
    ) or (ROOT / "Archive/History/CAPABILITY_MANIFEST_V2_H_J_4.json")
    supplied["v2_h_j_4_capability_oracle"] = supplied.get(
        "v2_h_j_4_capability_oracle"
    ) or (
        ROOT
        / "Evaluation/History/np_hard_capability_oracle_v2_h_j_4.json"
    )
    supplied["v2_h_j_4_migration_report"] = supplied.get(
        "v2_h_j_4_migration_report"
    ) or (
        ROOT
        / "Archive/History/H_I_TO_H_J_CAPABILITY_MIGRATION_REPORT_H_J_4.json"
    )
    resolved = {
        name: _repo_file(path, label=name) for name, path in supplied.items()
    }
    plan_text = resolved["plan"].read_text(encoding="utf-8")
    _expect(
        "H-J 已由 `Reports/MAIN_H_J_FULL_REPORT.json` 证明通过" in plan_text
        and "MAIN_H_J_FULL_REPORT.json" in plan_text
        and "至少 8 个此前没有现成最终路线" in plan_text
        and "至少 4 个 authoring family" in plan_text,
        "h_j_active_plan_drift",
        "the active plan no longer contains the frozen H-J contract",
    )
    if SECRET_VALUE_RE.search(plan_text):
        _fail("h_j_secret_leak", "active plan contains credential material")

    h_i = _read_json(resolved["h_i_report"], label="H-I full report")
    _expect(
        h_i.get("schema_version") == H_I_REPORT_SCHEMA
        and h_i.get("passed") is True
        and h_i.get("report_id") == _canonical_content_hash(h_i, field="report_id"),
        "h_j_h_i_baseline_invalid",
        "H-I report is not a valid content-addressed passing baseline",
    )

    contracts: dict[str, Any] = {
        "v1": _load_contract_epoch(
            epoch="v1",
            version="v1",
            manifest_path=resolved["v1_capability_manifest"],
            oracle_path=resolved["v1_capability_oracle"],
            target_matrix_path=resolved["v1_target_matrix"],
            r1_suite_path=resolved["v1_r1_suite"],
        ),
        "v2a": _load_contract_epoch(
            epoch="v2",
            version="v2a",
            manifest_path=resolved["v2_h_j_4_capability_manifest"],
            oracle_path=resolved["v2_h_j_4_capability_oracle"],
            target_matrix_path=resolved["v2_target_matrix"],
            r1_suite_path=resolved["v2_r1_suite"],
            allow_oracle_relocation=True,
        ),
        "v2b": _load_contract_epoch(
            epoch="v2",
            version="v2b",
            manifest_path=resolved["v2_capability_manifest"],
            oracle_path=resolved["v2_capability_oracle"],
            target_matrix_path=resolved["v2_target_matrix"],
            r1_suite_path=resolved["v2_r1_suite"],
        ),
    }
    _expect(
        contracts["v2a"]["assets"]["manifest"]["sha256"]
        == H_J_4_V2_MANIFEST_SHA256
        and contracts["v2a"]["assets"]["oracle"]["sha256"]
        == H_J_4_V2_ORACLE_SHA256,
        "h_j_h_j_4_archive_invalid",
        "H-J.4 v2a manifest/oracle hashes differ from the frozen formal run",
    )
    # Compatibility alias: callers that ask for generic v2 always receive the
    # final v2b contract. Stage validation uses content-addressed versions.
    contracts["v2"] = contracts["v2b"]
    h_i_contract = h_i.get("capability_contract")
    h_i_partition = h_i.get("identity_partition")
    _expect(
        isinstance(h_i_contract, Mapping)
        and isinstance(h_i_contract.get("manifest"), Mapping)
        and h_i_contract["manifest"].get("sha256")
        == contracts["v1"]["assets"]["manifest"]["sha256"]
        and isinstance(h_i_contract.get("oracle"), Mapping)
        and h_i_contract["oracle"].get("sha256")
        == contracts["v1"]["assets"]["oracle"]["sha256"]
        and isinstance(h_i_partition, Mapping)
        and isinstance(h_i_partition.get("target_matrix"), Mapping)
        and h_i_partition["target_matrix"].get("sha256")
        == _sha256(resolved["v1_target_matrix"]),
        "h_j_incomparable_baseline",
        "H-I is not content-addressed to the supplied immutable v1 contract",
    )
    migration_v2a = validate_capability_migration(
        v1=contracts["v1"], v2=contracts["v2a"]
    )
    migration = validate_capability_migration(
        v1=contracts["v1"], v2=contracts["v2b"]
    )
    h_j_4_migration_archive = validate_h_j_4_migration_archive(
        resolved["v2_h_j_4_migration_report"],
        v1=contracts["v1"],
        v2a=contracts["v2a"],
    )
    contracts["v2a"]["evidence_manifest_paths"] = {
        Path(h_j_4_migration_archive["historical_live_manifest"]),
    }
    contracts["v2a"]["evidence_oracle_paths"] = {
        Path(h_j_4_migration_archive["historical_live_oracle"]),
    }
    refinement = validate_v2_contract_refinement(
        v2a=contracts["v2a"], v2b=contracts["v2b"]
    )
    baseline = _frozen_h_i_baseline(
        h_i,
        contract=contracts["v1"]["contract"],
        v1=contracts["v1"],
    )
    static: dict[str, Any] = {
        "source_files": resolved,
        "contracts": contracts,
        "migration": migration,
        "migration_v2a": migration_v2a,
        "h_j_4_migration_archive": h_j_4_migration_archive,
        "v2_refinement": refinement,
        "h_i_report_object": h_i,
        "h_i_baseline_scorecard": baseline,
        # Compatibility aliases are deliberately v2: final H-J gates and new
        # focused tests must never silently fall back to the historical oracle.
        "capability_bundle": contracts["v2b"]["bundle"],
        "capability_oracle_object": contracts["v2b"]["oracle"],
        "case_contract": contracts["v2b"]["contract"],
    }
    static["public"] = {
        "h_i_baseline": {
            "file": str(resolved["h_i_report"]),
            "sha256": _sha256(resolved["h_i_report"], tagged=True),
            "report_id": h_i.get("report_id"),
            "contract_epoch": "v1",
            "evidence_mode": baseline["evidence_mode"],
            "case_count": baseline["case_count"],
            "family_macro_verified_at_budget": baseline[
                "family_macro_verified_at_budget"
            ],
            "verified_authoring_identity_count": 0,
            "safety": baseline["safety"],
            "split_evidence": baseline["split_evidence"],
        },
        "active_plan": {
            "file": str(resolved["plan"]),
            "sha256": _sha256(resolved["plan"], tagged=True),
            "h_j_contract_present": True,
        },
        "capability_contracts": {
            epoch: {
                **contracts[epoch]["assets"],
                "scope_policy": {
                    "file": str(contracts[epoch]["bundle"].manifest.scope_policy.path),
                    "sha256": contracts[epoch]["bundle"].manifest.scope_policy.sha256,
                },
                "selected_splits": list(CAPABILITY_SPLITS),
                "split_counts": dict(CAPABILITY_SPLIT_COUNTS),
                "unique_identity_count": 34,
                "formal_model_profile": FORMAL_MANIFEST_MODEL,
            }
            for epoch in CONTRACT_EPOCHS
        },
        "v2_content_addressed_subversions": {
            version: {
                **contracts[version]["assets"],
                "scope_policy": {
                    "file": str(
                        contracts[version]["bundle"].manifest.scope_policy.path
                    ),
                    "sha256": contracts[version][
                        "bundle"
                    ].manifest.scope_policy.sha256,
                },
                "selected_splits": list(CAPABILITY_SPLITS),
                "split_counts": dict(CAPABILITY_SPLIT_COUNTS),
                "unique_identity_count": 34,
                "formal_model_profile": FORMAL_MANIFEST_MODEL,
            }
            for version in ("v2a", "v2b")
        },
        "capability_migration_audit": migration,
        "h_j_4_v2a_migration_archive": h_j_4_migration_archive,
        "v2_refinement_audit": refinement,
    }
    return static


def migrate_h_i_baseline_to_v2(static: Mapping[str, Any]) -> dict[str, Any]:
    """Reindex immutable H-I observations onto the v2 scorer denominator.

    This does not rewrite or rescore any H-I artifact.  Every shared identity
    keeps its original v1 public outcome/model-call primitives.  The one v2
    C0-existing identity that came from the v1 R1 partition is normalized as
    a zero-call existing-route control and is called out explicitly.
    """

    baseline = static["h_i_baseline_scorecard"]
    v1_contract = static["contracts"]["v1"]["contract"]
    v2_contract = static["contracts"]["v2"]["contract"]
    original_rows = baseline.get("original_score_rows")
    _expect(
        isinstance(original_rows, list) and len(original_rows) == 34,
        "h_j_h_i_baseline_invalid",
        "H-I v1 score rows are unavailable for migration",
    )
    original_by_case = {
        row.get("case_id"): row
        for row in original_rows
        if isinstance(row, Mapping) and isinstance(row.get("case_id"), str)
    }
    _expect(
        set(original_by_case) == set(v1_contract),
        "h_j_h_i_baseline_invalid",
        "H-I v1 score rows do not match the v1 contract",
    )
    observation_by_identity = {
        str(v1_contract[case_id]["canonical_identity"]): row
        for case_id, row in original_by_case.items()
    }
    zero_one_problem = (
        "ComplexityReduction.Presentation.ZeroOneIPBinary.binaryStructuredProblem"
    )
    migrated_rows: list[dict[str, Any]] = []
    migration_sources: list[dict[str, Any]] = []
    for case_id, expected in v2_contract.items():
        identity_id = str(expected["canonical_identity"])
        observed = observation_by_identity.get(identity_id)
        if observed is not None:
            source = "original_h_i_v1_capability_score_row"
            source_case_id = str(observed["case_id"])
            public_status = observed.get("public_status")
            failure_code = observed.get("failure_code")
            model_calls = observed.get("model_calls")
            first_attempt = observed.get("first_attempt_verified") is True
            capability_success = observed.get("capability_success") is True
        else:
            _expect(
                expected["canonical_problem"] == zero_one_problem
                and identity_id in static["contracts"]["v1"]["r1"],
                "h_j_migration_crosswalk_invalid",
                f"v2 identity {identity_id} has no approved v1 baseline source",
            )
            source = "v1_r1_zero_weight_existing_route_control"
            source_case_id = static["contracts"]["v1"]["r1"][identity_id][
                "case_id"
            ]
            public_status = "VERIFIED"
            failure_code = None
            model_calls = 0
            first_attempt = True
            capability_success = True
        migrated_rows.append(
            {
                "case_id": case_id,
                "split": expected["split"],
                "family": expected["family"],
                "tier": expected["tier"],
                "outcome_class": expected["outcome_class"],
                "scored": expected["scored"],
                "requires_model": expected["requires_model"],
                "public_status": public_status,
                "failure_code": failure_code,
                "model_calls": model_calls,
                "first_attempt_verified": first_attempt,
                "capability_success": capability_success,
            }
        )
        migration_sources.append(
            {
                "v2_case_id": case_id,
                "canonical_identity": identity_id,
                "source": source,
                "v1_case_id": source_case_id,
            }
        )
    scorecard = _scorecard_from_rows(
        migrated_rows,
        contract=v2_contract,
        label="H-I observations migrated onto the v2 contract",
    )
    _expect(
        scorecard["verified_authoring_identity_count"] == 0
        and scorecard["safety_correct_count"] == scorecard["safety_case_count"] == 8,
        "h_j_h_i_baseline_invalid",
        "migrated H-I baseline changed authoring or safety outcomes",
    )
    scorecard["safety"] = dict(baseline["safety"])
    scorecard["evidence_mode"] = (
        "v2_reindex_of_original_content_addressed_h_i_v1_rows"
    )
    scorecard["migration_sources"] = migration_sources
    scorecard["native_contract_epoch"] = "v1"
    scorecard["comparison_contract_epoch"] = "v2"
    scorecard["comparison_contract_version"] = "v2b"
    return scorecard


def _validate_authored_run_evidence(
    run_rows: Mapping[str, Mapping[str, Any]],
    *,
    scorecard: Mapping[str, Any],
    contract: Mapping[str, Mapping[str, Any]],
    contract_epoch: str,
    label: str,
) -> None:
    _expect(
        contract_epoch in CONTRACT_EPOCHS,
        "h_j_authoring_audit_invalid",
        f"{label} has an unknown capability contract epoch",
    )
    for authored in scorecard["verified_authoring"]:
        case_id = str(authored["case_id"])
        row = run_rows[case_id]
        raw = row.get("raw_result")
        _expect(
            isinstance(raw, Mapping),
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} lacks raw evidence",
        )
        artifact = raw.get("artifact")
        replay = raw.get("independent_replay")
        axiom = raw.get("axiom_audit")
        deletion = raw.get("deletion_audit")
        fresh_core = raw.get("fresh_core")
        dag = raw.get("capability_dag")
        deletion_nodes = deletion.get("nodes") if isinstance(deletion, Mapping) else None
        _expect(
            raw.get("status") == "VERIFIED"
            and isinstance(artifact, Mapping)
            and artifact.get("endpoint") == contract[case_id]["canonical_problem"]
            and isinstance(replay, Mapping)
            and replay.get("passed") is True
            and isinstance(axiom, Mapping)
            and axiom.get("passed") is True
            and isinstance(deletion, Mapping)
            and deletion.get("passed") is True
            and isinstance(deletion.get("node_count"), int)
            and not isinstance(deletion.get("node_count"), bool)
            and int(deletion["node_count"]) > 0
            and isinstance(deletion_nodes, list)
            and len(deletion_nodes) == deletion["node_count"]
            and all(
                isinstance(node, Mapping) and node.get("passed") is True
                for node in deletion_nodes
            )
            and isinstance(fresh_core, Mapping)
            and fresh_core.get("passed") is True
            and isinstance(dag, Mapping)
            and dag.get("required_direction") == "source_to_target"
            and isinstance(dag.get("target_problem"), Mapping)
            and dag["target_problem"].get("term")
            == contract[case_id]["canonical_problem"],
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} lacks exact endpoint/replay/axiom/"
            "fresh-core/deletion evidence",
        )
        if contract_epoch == "v1":
            continue

        required_motif = contract[case_id].get("required_authoring_motif")
        _expect(
            isinstance(required_motif, Mapping),
            "h_j_authoring_audit_invalid",
            f"{label} verified v2 authoring case {case_id} lacks a frozen motif",
        )
        observed_motif, task = _authored_task_motif(dag)
        _expect(
            observed_motif == required_motif,
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} changed its exact required DAG motif",
        )
        expected_ids = [node["node_id"] for node in required_motif["nodes"]]
        task_nodes = {node.node_id: node for node in task.gap_nodes}
        runtime = raw.get("authoring_runtime")
        runtime_result = runtime.get("result") if isinstance(runtime, Mapping) else None
        _expect(
            isinstance(runtime, Mapping)
            and runtime.get("status") == "VERIFIED"
            and runtime.get("task_request_id") == task.request_id
            and runtime.get("accepted_nodes") == expected_ids
            and isinstance(runtime_result, Mapping)
            and runtime_result.get("accepted_nodes") == expected_ids,
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} accepted nodes differ from its motif",
        )
        fresh_count = fresh_core.get("count")
        _expect(
            isinstance(fresh_count, int)
            and not isinstance(fresh_count, bool)
            and fresh_count == len(expected_ids)
            and runtime.get("fresh_core_rediscoveries") == fresh_count,
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} did not fresh-resolve every motif node",
        )
        _expect(
            deletion.get("node_count") == len(expected_ids)
            and len(deletion_nodes) == len(expected_ids)
            and runtime.get("deletion_audits") == deletion_nodes,
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} lacks exact motif deletion coverage",
        )
        case_output_value = row.get("output_dir")
        _expect(
            isinstance(case_output_value, str) and case_output_value.strip(),
            "h_j_authoring_audit_invalid",
            f"{label} authored case {case_id} lacks its case output path",
        )
        case_output = Path(case_output_value).resolve()
        try:
            validate_successor_only_authoritative_evidence_v2(
                task=task,
                runtime=runtime,
                case_output=case_output,
                require_files=True,
            )
        except NPHardAuthoringContractError as error:
            _fail(
                "h_j_authoring_audit_invalid",
                f"{label} authored case {case_id} lacks authoritative "
                f"successor-only evidence: {error.code}",
            )
        for node_id, deletion_node in zip(
            expected_ids, deletion_nodes, strict=True
        ):
            task_node = task_nodes[node_id]
            _expect(
                isinstance(deletion_node, Mapping),
                "h_j_authoring_audit_invalid",
                f"{label} authored case {case_id} has an invalid deletion node",
            )
            declaration = deletion_node.get("declaration")
            command = deletion_node.get("command")
            audit_file = deletion_node.get("audit_file")
            _expect(
                deletion_node.get("node_id") == node_id
                and declaration == task_node.declaration
                and deletion_node.get("diagnostic_matched") is True
                and deletion_node.get("passed") is True
                and isinstance(command, Mapping)
                and _deletion_command_matches_declaration(
                    command, task_node.declaration
                )
                and _path_within(audit_file, case_output),
                "h_j_authoring_audit_invalid",
                f"{label} authored case {case_id} deletion did not fail on "
                f"the exact declaration for {node_id}",
            )
            audit_path = Path(str(audit_file)).resolve()
            _expect(
                audit_path.is_file()
                and deletion_node.get("audit_file_sha256")
                == _sha256(audit_path, tagged=True),
                "h_j_authoring_audit_invalid",
                f"{label} authored case {case_id} deletion file/hash drifted",
            )


def validate_stage_capability_reports(
    run_paths: Mapping[str, Path],
    score_paths: Mapping[str, Path],
    *,
    static: Mapping[str, Any],
) -> dict[str, Any]:
    contracts = static["contracts"]
    rows: list[dict[str, Any]] = []
    run_paths_seen: set[Path] = set()
    run_hashes_seen: set[str] = set()
    score_paths_seen: set[Path] = set()
    score_hashes_seen: set[str] = set()
    previous_time: datetime | None = None
    total_http_calls = 0
    total_tokens: dict[str, int] = {}

    for label in STAGE_LABELS:
        epoch = STAGE_CONTRACT_EPOCH[label]
        version = STAGE_CONTRACT_VERSION[label]
        expected_run_schema = CAPABILITY_RUN_SCHEMA_BY_EPOCH[epoch]
        expected_score_schema = CAPABILITY_SCORE_SCHEMA_BY_EPOCH[epoch]
        version_static = contracts[version]
        bundle = version_static["bundle"]
        contract = version_static["contract"]
        manifest_path = bundle.manifest.path
        manifest_hash = _sha256(manifest_path, tagged=True)
        oracle_path = version_static["oracle_path"]
        oracle_hash = _sha256(oracle_path, tagged=True)
        evidence_manifest_paths = version_static.get(
            "evidence_manifest_paths", {manifest_path}
        )
        evidence_oracle_paths = version_static.get(
            "evidence_oracle_paths", {oracle_path}
        )
        expected_ids = set(contract)
        run_path = _repo_file(run_paths[label], label=f"{label} capability run")
        score_path = _repo_file(score_paths[label], label=f"{label} capability score")
        run = _read_json(run_path, label=f"{label} capability run")
        score = _read_json(score_path, label=f"{label} capability score")
        run_hash = _sha256(run_path, tagged=True)
        score_hash = _sha256(score_path, tagged=True)
        generated_at = _parse_timestamp(run.get("generated_at"), label=f"{label}.run")
        score_generated_at = _parse_timestamp(
            score.get("generated_at"), label=f"{label}.score"
        )
        _expect(
            previous_time is None or generated_at > previous_time,
            "h_j_stage_evidence_order_invalid",
            "H-J capability stage timestamps must be strictly increasing",
        )
        previous_time = generated_at
        _expect(
            score_generated_at >= generated_at,
            "h_j_stage_evidence_order_invalid",
            f"{label} score predates its raw run",
        )
        _expect(
            run_path not in run_paths_seen
            and run_hash not in run_hashes_seen
            and score_path not in score_paths_seen
            and score_hash not in score_hashes_seen,
            "h_j_stage_evidence_reused",
            f"{label} reuses another stage raw or score report",
        )
        run_paths_seen.add(run_path)
        run_hashes_seen.add(run_hash)
        score_paths_seen.add(score_path)
        score_hashes_seen.add(score_hash)

        run_cases = run.get("cases")
        _expect(
            run.get("schema_version") == expected_run_schema
            and run.get("benchmark_id") == bundle.manifest.benchmark_id
            and run.get("run_valid") is True
            and run.get("selected_splits") == list(CAPABILITY_SPLITS)
            and run.get("model") == FORMAL_MODEL
            and isinstance(run_cases, list)
            and len(run_cases) == 34,
            "h_j_capability_run_invalid",
            f"{label} is not a valid full formal capability run",
        )
        _expect(
            run.get("run_id") == _canonical_content_hash(run, field="run_id"),
            "h_j_hash_binding_mismatch",
            f"{label} run_id does not bind its content",
        )
        run_by_id: dict[str, Mapping[str, Any]] = {}
        observed_identities: set[str] = set()
        for raw_row in run_cases:
            _expect(
                isinstance(raw_row, Mapping),
                "h_j_capability_run_invalid",
                f"{label} contains a non-object case",
            )
            case_id = raw_row.get("case_id")
            _expect(
                isinstance(case_id, str)
                and case_id in expected_ids
                and case_id not in run_by_id,
                "h_j_capability_run_invalid",
                f"{label} repeats or invents a case_id",
            )
            expected = contract[case_id]
            _expect(
                raw_row.get("split") == expected["split"]
                and raw_row.get("family") == expected["family"]
                and raw_row.get("canonical_identity_id")
                == expected["canonical_identity"]
                and raw_row.get("canonical_problem") == expected["canonical_problem"]
                and raw_row.get("canonical_module") == expected["canonical_module"]
                and raw_row.get("protocol_valid") is True,
                "h_j_capability_run_invalid",
                f"{label} case {case_id} identity/protocol drifted",
            )
            run_by_id[case_id] = raw_row
            observed_identities.add(str(raw_row["canonical_identity_id"]))
        _expect(
            set(run_by_id) == expected_ids and len(observed_identities) == 34,
            "h_j_identity_partition_invalid",
            f"{label} did not execute 34 unique capability identities",
        )

        manifest_record = run.get("manifest")
        target_record = run.get("target_matrix")
        scope_record = run.get("scope_policy")
        suite_records = run.get("suites")
        _expect(
            isinstance(manifest_record, Mapping)
            and manifest_record.get("sha256") == manifest_hash
            and _repo_reference(
                manifest_record.get("file"), label=f"{label}.manifest"
            )
            in evidence_manifest_paths
            and manifest_record.get("oracle_opened_by_runner") is False
            and isinstance(target_record, Mapping)
            and target_record.get("sha256")
            == _sha256(bundle.manifest.target_matrix.path, tagged=True)
            and _repo_reference(
                target_record.get("file"), label=f"{label}.target_matrix"
            )
            == bundle.manifest.target_matrix.path
            and isinstance(scope_record, Mapping)
            and scope_record.get("sha256") == bundle.manifest.scope_policy.sha256
            and _repo_reference(
                scope_record.get("file"), label=f"{label}.scope_policy"
            )
            == bundle.manifest.scope_policy.path
            and isinstance(suite_records, Mapping)
            and set(suite_records) == set(CAPABILITY_SPLITS),
            "h_j_hash_binding_mismatch",
            f"{label} manifest/suite/target provenance drifted",
        )
        for split in CAPABILITY_SPLITS:
            record = suite_records[split]
            _expect(
                isinstance(record, Mapping)
                and record.get("sha256") == bundle.manifest.suites[split].sha256
                and _repo_reference(
                    record.get("file"), label=f"{label}.suite.{split}"
                )
                == bundle.manifest.suites[split].path,
                "h_j_hash_binding_mismatch",
                f"{label} {split} suite provenance drifted",
            )

        preflight = run.get("preflight")
        isolation = run.get("isolation")
        parallel = run.get("parallel_execution")
        security = run.get("security")
        metrics = run.get("metrics")
        _expect(
            isinstance(preflight, Mapping)
            and preflight.get("exit_code") == 0
            and preflight.get("timed_out") is False,
            "h_j_capability_run_invalid",
            f"{label} preflight did not pass",
        )
        _expect(
            isinstance(isolation, Mapping)
            and isolation.get("passed") is True
            and isolation.get("forbidden_paths") == []
            and isolation.get("active_plan_present") is False
            and isolation.get("evaluation_oracle_present") is False
            and isolation.get("problem_archive_present") is False
            and isolation.get("problem_archive_copy_present") is False,
            "h_j_oracle_leakage",
            f"{label} physical isolation is invalid",
        )
        _expect(
            isinstance(parallel, Mapping)
            and parallel.get("configured_jobs") == 4
            and parallel.get("submitted_case_tasks") == 34
            and parallel.get("maximum_concurrent_case_tasks") == 4
            and parallel.get("final_active_case_tasks") == 0
            and parallel.get("observed_parallelism") is True,
            "h_j_concurrency_not_drained",
            f"{label} jobs=4 concurrency evidence is invalid",
        )
        _expect(
            isinstance(security, Mapping)
            and security.get("formal_model_profile_matched") is True
            and security.get("api_key_or_authorization_absent") is True
            and security.get("fixture_model_used") is False
            and security.get("cached_or_recorded_response_used") is False
            and security.get("oracle_opened_by_runner") is False
            and security.get("oracle_passed_to_orchestrator") is False
            and security.get("active_plan_present_in_isolation") is False
            and security.get("evaluation_present_in_isolation") is False
            and security.get("problem_archive_present_in_isolation") is False,
            "h_j_oracle_leakage",
            f"{label} secret/oracle security gates failed",
        )
        calls = _model_calls_from_capability(run)
        request_ids = _validate_http_calls(calls, label=label)
        usage = _token_usage(calls)
        _expect(
            isinstance(metrics, Mapping)
            and metrics.get("case_count") == 34
            and metrics.get("model_calls") == len(calls)
            and metrics.get("token_usage") == usage,
            "h_j_deepseek_http_evidence_invalid",
            f"{label} raw metrics differ from real HTTP ledgers",
        )

        score_cases = score.get("cases")
        _expect(
            score.get("schema_version") == expected_score_schema
            and score.get("benchmark_id") == bundle.manifest.benchmark_id
            and score.get("run_valid") is True
            and score.get("score_valid") is True
            and score.get("run_id") == run.get("run_id")
            and isinstance(score_cases, list)
            and len(score_cases) == 34,
            "h_j_capability_score_invalid",
            f"{label} is not a valid full capability score",
        )
        _expect(
            score.get("score_id") == _canonical_content_hash(score, field="score_id"),
            "h_j_hash_binding_mismatch",
            f"{label} score_id does not bind its content",
        )
        integrity = score.get("integrity")
        mutations = score.get("r0_mutation_audit")
        provenance = score.get("provenance")
        safety = score.get("safety")
        _expect(
            isinstance(integrity, Mapping)
            and bool(integrity)
            and all(value is True for value in integrity.values())
            and isinstance(mutations, Mapping)
            and mutations.get("passed") is True
            and mutations.get("audit_count") == mutations.get("passed_count") == 8,
            "h_j_capability_score_invalid",
            f"{label} scorer integrity or mutation audit failed",
        )
        _expect(
            isinstance(provenance, Mapping)
            and isinstance(provenance.get("manifest"), Mapping)
            and provenance["manifest"].get("sha256") == manifest_hash
            and _repo_reference(
                provenance["manifest"].get("file"),
                label=f"{label}.score.manifest",
            )
            in evidence_manifest_paths
            and isinstance(provenance.get("oracle"), Mapping)
            and provenance["oracle"].get("sha256") == oracle_hash
            and provenance["oracle"].get("opened_by") == "independent scorer only"
            and _repo_reference(
                provenance["oracle"].get("file"),
                label=f"{label}.score.oracle",
            )
            in evidence_oracle_paths
            and isinstance(provenance.get("run_report"), Mapping)
            and _repo_reference(
                provenance["run_report"].get("file"),
                label=f"{label}.score.run_report",
            )
            == run_path
            and provenance["run_report"].get("sha256") == run_hash,
            "h_j_hash_binding_mismatch",
            f"{label} scorer provenance drifted",
        )
        _expect(
            isinstance(safety, Mapping)
            and all(safety.get(key) == 0 for key in SAFETY_FIELDS),
            "h_j_capability_safety_regression",
            f"{label} accepted unsafe evidence",
        )

        scorecard = _scorecard_from_rows(
            score_cases, contract=contract, label=f"{label} scorer cases"
        )
        score_metrics = score.get("metrics")
        _expect(
            isinstance(score_metrics, Mapping)
            and score_metrics.get("scored_case_count") == 32
            and score_metrics.get("positive_case_count")
            == scorecard["positive_case_count"]
            and score_metrics.get("verified_at_budget_count")
            == scorecard["verified_at_budget_count"]
            and score_metrics.get("verified_at_first_attempt_count")
            == scorecard["verified_at_first_attempt_count"]
            and score_metrics.get("family_macro_verified_at_budget")
            == scorecard["family_macro_verified_at_budget"]
            and score_metrics.get("first_authoring_family_macro")
            == scorecard["first_authoring_family_macro"]
            and score_metrics.get("safety_correct_count")
            == scorecard["safety_correct_count"]
            and score_metrics.get("model_calls")
            == scorecard["positive_model_calls"],
            "h_j_capability_score_invalid",
            f"{label} aggregate score metrics differ from independent case-row scoring",
        )
        _expect(
            scorecard["safety_correct_count"] == scorecard["safety_case_count"] == 8,
            "h_j_capability_safety_regression",
            f"{label} did not preserve all eight safety decisions",
        )
        _validate_authored_run_evidence(
            run_by_id,
            scorecard=scorecard,
            contract=contract,
            contract_epoch=epoch,
            label=label,
        )

        for key, amount in usage.items():
            total_tokens[key] = total_tokens.get(key, 0) + amount
        total_http_calls += len(calls)
        rows.append(
            {
                "stage": label,
                "contract_epoch": epoch,
                "contract_version": version,
                "contract": version_static["assets"],
                "run": {
                    "file": str(run_path),
                    "sha256": run_hash,
                    "run_id": run.get("run_id"),
                    "generated_at": run.get("generated_at"),
                    "run_valid": True,
                    "selected_splits": list(CAPABILITY_SPLITS),
                    "case_count": 34,
                    "unique_identity_count": 34,
                    "parallel_execution": parallel,
                },
                "score": {
                    "file": str(score_path),
                    "sha256": score_hash,
                    "score_id": score.get("score_id"),
                    "generated_at": score.get("generated_at"),
                    "score_valid": True,
                },
                "real_deepseek_http_calls": len(calls),
                "http_200_count": len(calls),
                "request_identity_count": len(request_ids),
                "token_usage": usage,
                "independent_scorecard": scorecard,
                "safety": {key: int(safety[key]) for key in SAFETY_FIELDS},
                "secret_absent": True,
                "oracle_opened_by_runner": False,
            }
        )

    return {
        "required_stages": list(STAGE_LABELS),
        "stage_contract_epochs": dict(STAGE_CONTRACT_EPOCH),
        "stage_contract_versions": dict(STAGE_CONTRACT_VERSION),
        "cross_epoch_metric_curve_allowed": False,
        "stage_count": len(rows),
        "reports": rows,
        "all_selected_splits": list(CAPABILITY_SPLITS),
        "case_executions": 34 * len(rows),
        "unique_identities_per_stage": 34,
        "real_deepseek_http_calls": total_http_calls,
        "http_200_count": total_http_calls,
        "token_usage": dict(sorted(total_tokens.items())),
        "all_runs_valid": True,
        "all_scores_valid": True,
        "all_concurrency_drained": True,
        "all_secret_and_oracle_guards_clean": True,
    }


def validate_optional_stage_regressions(
    paths: Mapping[str, Path] | None,
) -> dict[str, Any]:
    if paths is None:
        return {
            "provided": False,
            "capability_weight": 0,
            "note": "optional unified all regression evidence was not supplied",
            "reports": [],
        }
    rows: list[dict[str, Any]] = []
    paths_seen: set[Path] = set()
    hashes_seen: set[str] = set()
    production_seen: set[Path] = set()
    previous_time: datetime | None = None
    total_calls = 0
    for label in STAGE_LABELS:
        path = _repo_file(paths[label], label=f"{label} unified regression")
        report = _read_json(path, label=f"{label} unified regression")
        report_hash = _sha256(path, tagged=True)
        generated_at = _parse_timestamp(report.get("generated_at"), label=label)
        _expect(
            previous_time is None or generated_at > previous_time,
            "h_j_stage_evidence_order_invalid",
            "unified regression timestamps must be strictly increasing",
        )
        previous_time = generated_at
        _expect(
            path not in paths_seen and report_hash not in hashes_seen,
            "h_j_stage_evidence_reused",
            f"{label} reuses another unified report",
        )
        paths_seen.add(path)
        hashes_seen.add(report_hash)
        counts = report.get("counts")
        parallel = report.get("parallel_execution")
        trust = report.get("trust_boundary")
        _expect(
            report.get("schema_version") == UNIFIED_REPORT_SCHEMA
            and report.get("selector") == "all"
            and report.get("run_valid") is True
            and report.get("passed") is True
            and report.get("formal_profile_matched") is True
            and report.get("model_configuration") == FORMAL_MODEL,
            "h_j_regression_invalid",
            f"{label} is not a formal unified all regression",
        )
        _expect(
            isinstance(counts, Mapping)
            and counts.get("logical_cases") == 59
            and counts.get("case_executions") == 59
            and counts.get("matched_executions") == 59
            and counts.get("failed_executions") == 0
            and counts.get("model_calls") == 12
            and counts.get("capability_weight") == 0,
            "h_j_regression_invalid",
            f"{label} did not pass the zero-weight 59/59 registry",
        )
        _expect(
            isinstance(parallel, Mapping)
            and parallel.get("configured_jobs") == 4
            and parallel.get("maximum_concurrent_case_tasks") == 4
            and all(
                value == 0
                for key, value in parallel.items()
                if key.endswith("final_active_case_tasks")
            )
            and isinstance(trust, Mapping)
            and trust.get("capability_weight_zero") is True
            and trust.get("component_reports_passed") is True,
            "h_j_regression_invalid",
            f"{label} regression concurrency/trust gates failed",
        )
        components = report.get("component_reports")
        _expect(
            isinstance(components, Mapping)
            and isinstance(components.get("production"), str),
            "h_j_regression_invalid",
            f"{label} production component is absent",
        )
        production_path = _repo_reference(
            components["production"], label=f"{label}.production"
        )
        production = _read_json(production_path, label=f"{label}.production")
        _expect(
            production_path not in production_seen,
            "h_j_stage_evidence_reused",
            f"{label} reuses another production component",
        )
        production_seen.add(production_path)
        metrics = production.get("metrics")
        production_parallel = production.get("parallel_execution")
        security = production.get("security")
        _expect(
            production.get("schema_version") == RELEASE_REPORT_SCHEMA
            and production.get("passed") is True
            and production.get("fresh_output") is True
            and production.get("resume") is False
            and production.get("round") == 1
            and production.get("model") == FORMAL_MODEL
            and isinstance(metrics, Mapping)
            and metrics.get("case_count") == metrics.get("matched_case_count") == 12
            and metrics.get("real_api_calls") == 12
            and isinstance(production_parallel, Mapping)
            and production_parallel.get("configured_jobs") == 4
            and production_parallel.get("maximum_concurrent_case_tasks") == 4
            and production_parallel.get("final_active_case_tasks") == 0
            and isinstance(security, Mapping)
            and security.get("secret_absent") is True
            and security.get("nonstandard_axiom_acceptance_count") == 0
            and security.get("oracle_or_gold_prompt_acceptance_count") == 0,
            "h_j_regression_invalid",
            f"{label} production regression evidence is invalid",
        )
        calls = _model_calls_from_release(production)
        _expect(
            len(calls) == 12,
            "h_j_deepseek_http_evidence_invalid",
            f"{label} production regression lacks 12 call ledgers",
        )
        _validate_http_calls(calls, label=f"{label} unified production")
        usage = _token_usage(calls)
        _expect(
            metrics.get("token_usage") == usage,
            "h_j_deepseek_http_evidence_invalid",
            f"{label} production token totals drifted",
        )
        total_calls += len(calls)
        rows.append(
            {
                "stage": label,
                "file": str(path),
                "sha256": report_hash,
                "generated_at": report.get("generated_at"),
                "logical_cases": 59,
                "matched_executions": 59,
                "capability_weight": 0,
                "real_deepseek_http_calls": 12,
                "production": {
                    "file": str(production_path),
                    "sha256": _sha256(production_path, tagged=True),
                },
            }
        )
    return {
        "provided": True,
        "stage_count": len(rows),
        "reports": rows,
        "logical_case_executions": 59 * len(rows),
        "real_deepseek_http_calls": total_calls,
        "http_200_count": total_calls,
        "capability_weight": 0,
        "all_concurrency_drained": True,
    }


def _source_control(files: Iterable[Path]) -> dict[str, Any]:
    unique = sorted({path.resolve() for path in files}, key=str)
    hashes = {str(path.relative_to(ROOT)): _sha256(path) for path in unique}
    return {
        "files": hashes,
        "combined_sha256": hashlib.sha256(
            canonical_json(hashes).encode("utf-8")
        ).hexdigest(),
        "lean_toolchain": (ROOT / "Lean/lean-toolchain")
        .read_text(encoding="utf-8")
        .strip(),
        "lean_toolchain_sha256": _sha256(ROOT / "Lean/lean-toolchain"),
        "lake_manifest_sha256": _sha256(ROOT / "Lean/lake-manifest.json"),
    }


def build_full_report(
    *,
    static_paths: StaticEvidencePaths,
    stage_run_paths: Mapping[str, Path],
    stage_score_paths: Mapping[str, Path],
    stage_regression_paths: Mapping[str, Path] | None = None,
) -> dict[str, Any]:
    static = validate_static_assets(static_paths)
    capability = validate_stage_capability_reports(
        stage_run_paths, stage_score_paths, static=static
    )
    regression = validate_optional_stage_regressions(stage_regression_paths)
    native_baseline = static["h_i_baseline_scorecard"]
    baseline = migrate_h_i_baseline_to_v2(static)
    _expect(
        capability["reports"][-1]["contract_epoch"] == "v2"
        and capability["reports"][-1]["contract_version"] == "v2b",
        "h_j_final_gate_failed",
        "the final H-J capability report is not natively scored under v2b",
    )
    final_scorecard = capability["reports"][-1]["independent_scorecard"]
    baseline_authoring = {
        row["canonical_identity"] for row in baseline["verified_authoring"]
    }
    final_authoring = {
        row["canonical_identity"] for row in final_scorecard["verified_authoring"]
    }
    new_identities = final_authoring - baseline_authoring
    new_rows = [
        row
        for row in final_scorecard["verified_authoring"]
        if row["canonical_identity"] in new_identities
    ]
    new_families = sorted({str(row["family"]) for row in new_rows})
    heldout_new_rows = [row for row in new_rows if row["split"] == "heldout"]
    baseline_macro = baseline["family_macro_verified_at_budget"]
    final_macro = final_scorecard["family_macro_verified_at_budget"]
    _expect(
        isinstance(baseline_macro, (int, float))
        and not isinstance(baseline_macro, bool)
        and isinstance(final_macro, (int, float))
        and not isinstance(final_macro, bool),
        "h_j_family_macro_invalid",
        "baseline or final family macro is absent",
    )
    final_safety = capability["reports"][-1]["safety"]
    improvement = {
        "baseline": {
            "native_contract_epoch": "v1",
            "comparison_contract_epoch": "v2",
            "comparison_contract_version": "v2b",
            "evidence_mode": baseline["evidence_mode"],
            "family_macro_verified_at_budget": baseline_macro,
            "verified_authoring_identity_count": len(baseline_authoring),
            "safety": baseline["safety"],
            "native_v1_family_macro_verified_at_budget": native_baseline[
                "family_macro_verified_at_budget"
            ],
        },
        "final": {
            "stage": STAGE_LABELS[-1],
            "contract_epoch": "v2",
            "contract_version": "v2b",
            "family_macro_verified_at_budget": final_macro,
            "verified_authoring_identity_count": len(final_authoring),
            "verified_authoring_family_count": final_scorecard[
                "verified_authoring_family_count"
            ],
            "heldout_verified_authoring_identity_count": final_scorecard[
                "heldout_verified_authoring_identity_count"
            ],
            "safety": final_safety,
        },
        "delta": {
            "family_macro_verified_at_budget": round(
                float(final_macro) - float(baseline_macro), 6
            ),
            "new_c0_authoring_verified_identity_count": len(new_identities),
            "new_c0_authoring_verified_family_count": len(new_families),
            "heldout_new_c0_authoring_verified_identity_count": len(
                heldout_new_rows
            ),
            "new_c0_authoring_verified_families": new_families,
            "new_c0_authoring_verified": sorted(
                new_rows, key=lambda row: str(row["case_id"])
            ),
        },
        "accepted_unary_numeric_demotions": static["migration"][
            "accepted_unary_numeric_demotions"
        ],
        "unresolved_frontier": final_scorecard["frontier"],
    }

    gates = {
        "h_i_full_report_bound_and_passing": True,
        "active_h_j_plan_bound": True,
        "immutable_h_i_v1_evidence_recomputed_from_original_rows": (
            native_baseline["evidence_mode"]
            == "original_content_addressed_h_i_v1_score_rows"
        ),
        "contract_epoch_migration_bound": static["migration"]["passed"] is True,
        "h_j_4_v2a_migration_archive_bound": static[
            "h_j_4_migration_archive"
        ]["passed"]
        is True,
        "v2a_to_v2b_refinement_bound": static["v2_refinement"]["passed"]
        is True,
        "stage_contract_epochs_exact": capability["stage_contract_epochs"]
        == STAGE_CONTRACT_EPOCH,
        "stage_contract_versions_exact": capability["stage_contract_versions"]
        == STAGE_CONTRACT_VERSION,
        "no_cross_epoch_stage_curve_claim": capability[
            "cross_epoch_metric_curve_allowed"
        ]
        is False,
        "final_score_recomputed_with_v2b_oracle": (
            capability["reports"][-1]["contract_epoch"] == "v2"
            and capability["reports"][-1]["contract_version"] == "v2b"
        ),
        "capability_denominator_34_unique_identities": True,
        "five_distinct_full_capability_raw_reports": capability["stage_count"] == 5,
        "five_distinct_full_capability_score_reports": capability["stage_count"] == 5,
        "every_stage_selected_dev_validation_heldout_frontier": True,
        "every_stage_run_and_score_valid": (
            capability["all_runs_valid"] and capability["all_scores_valid"]
        ),
        "every_stage_formal_deepseek_http_200_positive": all(
            row["real_deepseek_http_calls"]
            == row["http_200_count"]
            == row["request_identity_count"]
            and row["real_deepseek_http_calls"] > 0
            for row in capability["reports"]
        ),
        "every_stage_jobs_4_and_final_active_0": capability[
            "all_concurrency_drained"
        ],
        "no_secret_or_oracle_leakage": capability[
            "all_secret_and_oracle_guards_clean"
        ],
        "all_eight_safety_cases_preserved": final_scorecard["safety_correct_count"]
        == 8,
        "safety_guardrails_do_not_regress": all(
            final_safety[key] <= baseline["safety"][key] for key in SAFETY_FIELDS
        ),
        "new_c0_authoring_verified_at_least_8": len(new_identities) >= 8,
        "heldout_new_c0_authoring_verified_at_least_8": len(heldout_new_rows)
        >= 8,
        "new_c0_authoring_covers_at_least_4_families": len(new_families) >= 4,
        "family_macro_verified_at_budget_improves": float(final_macro)
        > float(baseline_macro),
        "verified_authoring_uses_public_complexity_reduction_targets": all(
            str(row["canonical_problem"]).startswith("ComplexityReduction.")
            and "Benchmark.Hardness.Inputs" not in str(row["canonical_problem"])
            for row in new_rows
        ),
        "frontier_failures_and_successes_reported": len(
            improvement["unresolved_frontier"]
        )
        == 2,
        "unary_numeric_demotions_recorded_not_failed": len(
            improvement["accepted_unary_numeric_demotions"]
        )
        == 3
        and all(
            row.get("accepted_without_failure") is True
            and row.get("reason") == MIGRATION_BOUNDARY_FAILURE
            for row in improvement["accepted_unary_numeric_demotions"]
        ),
        "optional_unified_regression_has_zero_capability_weight": regression[
            "capability_weight"
        ]
        == 0,
    }
    _expect(
        all(value is True for value in gates.values()),
        "h_j_final_gate_failed",
        "one or more H-J final report gates did not pass",
    )

    runtime_files = [
        *(
            _repo_file(path, label=f"stage run {label}")
            for label, path in stage_run_paths.items()
        ),
        *(
            _repo_file(path, label=f"stage score {label}")
            for label, path in stage_score_paths.items()
        ),
        *(
            _repo_file(path, label=f"stage regression {label}")
            for label, path in (stage_regression_paths or {}).items()
        ),
    ]
    builder_files = [
        Path(__file__).resolve(),
        ROOT / "tests/test_hardness_np_hard_h_j_full_report.py",
    ]
    _expect(
        all(path.is_file() for path in builder_files),
        "h_j_evidence_missing",
        "H-J report builder or its static test is missing",
    )
    report: dict[str, Any] = {
        "schema_version": REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-J-general-typed-authoring-planner",
        "passed": True,
        **static["public"],
        "substage_capability_evidence": capability,
        "optional_unified_regression_evidence": regression,
        "improvement_over_h_i": improvement,
        "gates": gates,
        "source_control": _source_control(
            [
                *static["source_files"].values(),
                *(
                    static["contracts"][version][
                        "bundle"
                    ].manifest.scope_policy.path
                    for version in CONTRACT_VERSIONS
                ),
                *runtime_files,
                *builder_files,
            ]
        ),
    }
    _assert_no_secret(report, label="final H-J report")
    report["report_id"] = sha256_id(report)
    return report


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    resolved = path.resolve()
    _expect(
        resolved == REPORT_PATH.resolve(),
        "h_j_output_path_invalid",
        f"H-J report must be written to {REPORT_PATH}",
    )
    temporary = resolved.with_suffix(resolved.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(resolved)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Build MAIN_H_J_FULL_REPORT.json from five full H-J capability stages"
    )
    parser.add_argument("--h-i-report", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument(
        "--v1-capability-manifest",
        "--capability-manifest",
        dest="v1_capability_manifest",
        type=Path,
        required=True,
        help="immutable H-I/H-J.1-.3 v1 capability manifest",
    )
    parser.add_argument(
        "--v1-capability-oracle",
        "--capability-oracle",
        dest="v1_capability_oracle",
        type=Path,
        required=True,
        help="immutable H-I/H-J.1-.3 v1 scorer oracle",
    )
    parser.add_argument(
        "--v1-target-matrix",
        "--target-matrix",
        dest="v1_target_matrix",
        type=Path,
        required=True,
        help="immutable 44-identity v1 target matrix",
    )
    parser.add_argument("--v1-r1-suite", type=Path, required=True)
    parser.add_argument("--v2-capability-manifest", type=Path, required=True)
    parser.add_argument("--v2-capability-oracle", type=Path, required=True)
    parser.add_argument("--v2-target-matrix", type=Path, required=True)
    parser.add_argument("--v2-r1-suite", type=Path, required=True)
    parser.add_argument(
        "--h-j-4-v2-capability-manifest",
        "--v2a-capability-manifest",
        dest="v2_h_j_4_capability_manifest",
        type=Path,
        help=(
            "archived H-J.4 v2a manifest; defaults to the frozen History asset"
        ),
    )
    parser.add_argument(
        "--h-j-4-v2-capability-oracle",
        "--v2a-capability-oracle",
        dest="v2_h_j_4_capability_oracle",
        type=Path,
        help=(
            "archived H-J.4 v2a scorer oracle; its hash must match the "
            "manifest-embedded historical hash"
        ),
    )
    parser.add_argument(
        "--h-j-4-v2-migration-report",
        "--v2a-migration-report",
        dest="v2_h_j_4_migration_report",
        type=Path,
        help=(
            "archived H-J.4 v1-to-v2a migration audit; defaults to History"
        ),
    )
    parser.add_argument(
        "--stage-run",
        action="append",
        required=True,
        metavar="STAGE=PATH",
        help="repeat for all five H-J full capability raw reports",
    )
    parser.add_argument(
        "--stage-score",
        action="append",
        required=True,
        metavar="STAGE=PATH",
        help="repeat for all five H-J full capability scorer reports",
    )
    parser.add_argument(
        "--stage-regression",
        action="append",
        default=[],
        metavar="STAGE=PATH",
        help="optional; if used, repeat for all five unified all regression reports",
    )
    parser.add_argument("--output", type=Path, default=REPORT_PATH)
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    try:
        stage_runs = _parse_labeled_paths(
            arguments.stage_run,
            expected=STAGE_LABELS,
            option="--stage-run",
        )
        stage_scores = _parse_labeled_paths(
            arguments.stage_score,
            expected=STAGE_LABELS,
            option="--stage-score",
        )
        stage_regressions = (
            _parse_labeled_paths(
                arguments.stage_regression,
                expected=STAGE_LABELS,
                option="--stage-regression",
            )
            if arguments.stage_regression
            else None
        )
        report = build_full_report(
            static_paths=StaticEvidencePaths(
                h_i_report=arguments.h_i_report,
                plan=arguments.plan,
                v1_capability_manifest=arguments.v1_capability_manifest,
                v1_capability_oracle=arguments.v1_capability_oracle,
                v1_target_matrix=arguments.v1_target_matrix,
                v1_r1_suite=arguments.v1_r1_suite,
                v2_capability_manifest=arguments.v2_capability_manifest,
                v2_capability_oracle=arguments.v2_capability_oracle,
                v2_target_matrix=arguments.v2_target_matrix,
                v2_r1_suite=arguments.v2_r1_suite,
                v2_h_j_4_capability_manifest=(
                    arguments.v2_h_j_4_capability_manifest
                ),
                v2_h_j_4_capability_oracle=arguments.v2_h_j_4_capability_oracle,
                v2_h_j_4_migration_report=arguments.v2_h_j_4_migration_report,
            ),
            stage_run_paths=stage_runs,
            stage_score_paths=stage_scores,
            stage_regression_paths=stage_regressions,
        )
        _write_json(arguments.output, report)
    except (HJReportError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "output_written": False,
                    "failure_code": getattr(
                        error, "code", "h_j_report_build_failed"
                    ),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 1
    print(
        json.dumps(
            {
                "passed": True,
                "output_written": True,
                "report": str(arguments.output.resolve()),
                "report_id": report["report_id"],
                "gate_count": len(report["gates"]),
                "new_c0_authoring_verified": report["improvement_over_h_i"][
                    "delta"
                ]["new_c0_authoring_verified_identity_count"],
                "new_families": report["improvement_over_h_i"]["delta"][
                    "new_c0_authoring_verified_family_count"
                ],
            },
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
