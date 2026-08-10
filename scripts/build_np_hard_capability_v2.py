#!/usr/bin/env python3
"""Build the honest, content-addressed NP-hard capability v2 contract.

The H-I v1 contract is historical evidence and is never rewritten here.  V2
preserves the same 44 canonical identities while correcting three unary
numeric assignments whose originally proposed binary-to-unary direction is
not backed by a polynomial encoding bridge in the public library.

Public capability and R1 suites remain answer-free.  Expected outcomes and
the explicit encoding-complexity blocker live only in the scorer oracle or the
zero-weight migration audit.
"""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.models import canonical_json, sha256_id  # noqa: E402
from agent.hardness.np_hard_scope_policy import (  # noqa: E402
    load_np_hard_scope_policy,
)


HARDNESS = ROOT / "Benchmark" / "Hardness"
SUITES = HARDNESS / "Suites"
GATE_SUITES = ROOT / "Gate" / "Suites"
EVALUATION = HARDNESS / "Evaluation"
DATA = ROOT / "agent" / "hardness" / "data"

V1_MANIFEST = ROOT / "Archive/CAPABILITY_MANIFEST.json"
V1_MATRIX = ROOT / "Gate/NP_HARD_TARGET_MATRIX.json"
V1_SCOPE_POLICY = DATA / "np_hard_scope_policy.json"
V1_ORACLE = EVALUATION / "np_hard_capability_oracle_v1.json"
V1_R1 = GATE_SUITES / "np_hard_public_r1_coverage_v1.json"
V1_SUITES = {
    split: GATE_SUITES / f"np_hard_capability_{split}_v1.json"
    for split in ("dev", "validation", "heldout", "frontier")
}

V2_MANIFEST = HARDNESS / "CAPABILITY_MANIFEST_V2.json"
V2_MATRIX = ROOT / "Gate/NP_HARD_TARGET_MATRIX_V2.json"
V2_SCOPE_POLICY = DATA / "np_hard_scope_policy_v2.json"
V2_ORACLE = EVALUATION / "np_hard_capability_oracle_v2.json"
V2_R1 = GATE_SUITES / "np_hard_public_r1_coverage_v2.json"
V2_SUITES = {
    split: SUITES / f"np_hard_capability_{split}_v2.json"
    for split in ("dev", "validation", "heldout", "frontier")
}
MIGRATION_REPORT = ROOT / "Reports/H_I_TO_H_J_CAPABILITY_MIGRATION_REPORT.json"
H_I_REPORT = ROOT / "Reports/MAIN_H_I_FULL_REPORT.json"

MANIFEST_SCHEMA = "hardness_np_hard_capability_manifest_v2"
SUITE_SCHEMA = "hardness_np_hard_capability_suite_v2"
ORACLE_SCHEMA = "hardness_np_hard_capability_oracle_v2"
MATRIX_SCHEMA = "hardness_np_hard_target_matrix_v2"
MATRIX_ROW_SCHEMA = "hardness_np_hard_target_matrix_row_v2"
SCOPE_SCHEMA = "hardness_np_hard_scope_policy_v2"
SCOPE_ENTRY_SCHEMA = "hardness_np_hard_scope_policy_entry_v2"
R1_SCHEMA = "hardness_np_hard_public_r1_coverage_suite_v2"
MIGRATION_SCHEMA = "hardness_np_hard_capability_migration_audit_v1"
BENCHMARK_ID = "np-hard-capability-v2"
BOUNDARY_DISPOSITION = "encoding_complexity_frontier"
BOUNDARY_BUCKET = "encoding_complexity_boundary"
BOUNDARY_FAILURE = "encoding_polynomial_reverse_bridge_unavailable"
H_I_REPORT_ID = "sha256:29ee47469e8502bb9b2406073bd19192683680ecf35fcad5d67b56d2c6d855b7"

PUBLIC_CASE_FIELDS = ("case_id", "module", "problem", "family", "budget_profile")
SPLITS = ("dev", "validation", "heldout", "frontier")
SPLIT_COUNTS = {"dev": 8, "validation": 8, "heldout": 16, "frontier": 2}

KNAPSACK = "ComplexityReduction.Presentation.Knapsack.structuredProblem"
PARTITION = "ComplexityReduction.Presentation.Partition.structuredProblem"
JOB_SEQUENCING = "ComplexityReduction.Presentation.JobSequencing.structuredProblem"
FEEDBACK_ARC_SET = "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem"
THREE_DIMENSIONAL_MATCHING = (
    "ComplexityReduction.Presentation.ThreeDimensionalMatching.structuredProblem"
)
ZERO_ONE_IP_BINARY = (
    "ComplexityReduction.Presentation.ZeroOneIPBinary.binaryStructuredProblem"
)
SEEING_SET = "ComplexityReduction.Presentation.SeeingSet.presentedProblem"

TAGGED_THREE_SAT_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
    "task_class": "typed_capability_dag",
    "nodes": [
        {
            "node_id": "representation-adapter",
            "capability": "representation_adapter",
            "depends_on": [],
        },
        {
            "node_id": "semantic-forward",
            "capability": "semantic_forward",
            "depends_on": ["representation-adapter"],
        },
        {
            "node_id": "semantic-reverse",
            "capability": "semantic_reverse",
            "depends_on": ["representation-adapter"],
        },
        {
            "node_id": "semantic-iff",
            "capability": "semantic_iff",
            "depends_on": ["semantic-forward", "semantic-reverse"],
        },
    ],
    "terminal_node_id": "semantic-iff",
    "final_program_node_id": "representation-adapter",
}

SEEING_SET_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
    "task_class": "typed_tmkarp_program_indexed_composition_dag",
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
            "node_id": "program-executable",
            "capability": "program_indexed_executable",
            "depends_on": [],
        },
        {
            "node_id": "program-primitive",
            "capability": "program_indexed_primitive",
            "depends_on": ["program-executable"],
        },
        {
            "node_id": "program",
            "capability": "program_indexed_program",
            "depends_on": ["program-primitive"],
        },
        {
            "node_id": "program-run-coherence-direct-tm",
            "capability": "program_indexed_coherence_direct_tm",
            "depends_on": ["program"],
        },
        {
            "node_id": "program-semantic-iff",
            "capability": "program_indexed_semantic_iff",
            "depends_on": ["program-run-coherence-direct-tm"],
        },
        {
            "node_id": "composed-program",
            "capability": "program_indexed_composed_program",
            "depends_on": ["tmkarp-program", "program"],
        },
        {
            "node_id": "composed-semantic-iff",
            "capability": "program_indexed_composed_semantic_iff",
            "depends_on": [
                "tmkarp-semantic-iff",
                "program-semantic-iff",
                "composed-program",
            ],
        },
    ],
    "terminal_node_id": "composed-semantic-iff",
    "final_program_node_id": "composed-program",
}

THREE_DIMENSIONAL_MATCHING_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
    "task_class": "typed_tmkarp_admission_dag",
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
    ],
    "terminal_node_id": "tmkarp-semantic-iff",
    "final_program_node_id": "tmkarp-program",
}

DEPENDENT_COMPOSITION_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
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
}

MAX_CUT_STRUCTURED_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
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
            "depends_on": ["gadget-executable", "gadget-parameter-audit"],
        },
        {
            "node_id": "gadget-semantic-reverse",
            "capability": "gadget_semantic_reverse",
            "depends_on": ["gadget-executable", "gadget-parameter-audit"],
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
}

MAX_CUT_BINARY_REQUIRED_AUTHORING_MOTIF: dict[str, Any] = {
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
}

REQUIRED_AUTHORING_MOTIFS = {
    "cdev-au-01-tagged-three-sat-adapter": (
        TAGGED_THREE_SAT_REQUIRED_AUTHORING_MOTIF
    ),
    "cval-au-03-seeing-set": SEEING_SET_REQUIRED_AUTHORING_MOTIF,
    "chld-au-01-feedback-node-set": (
        THREE_DIMENSIONAL_MATCHING_REQUIRED_AUTHORING_MOTIF
    ),
    "chld-au-03-max-cut-structured": (
        MAX_CUT_STRUCTURED_REQUIRED_AUTHORING_MOTIF
    ),
    "chld-au-04-max-cut-binary": MAX_CUT_BINARY_REQUIRED_AUTHORING_MOTIF,
    "chld-au-06-hitting-set": DEPENDENT_COMPOSITION_REQUIRED_AUTHORING_MOTIF,
    "chld-au-07-set-covering": (
        THREE_DIMENSIONAL_MATCHING_REQUIRED_AUTHORING_MOTIF
    ),
    "chld-au-08-set-packing": (
        THREE_DIMENSIONAL_MATCHING_REQUIRED_AUTHORING_MOTIF
    ),
    "chld-au-09-feedback-arc-set": (
        DEPENDENT_COMPOSITION_REQUIRED_AUTHORING_MOTIF
    ),
    "chld-au-10-three-dimensional-matching": (
        THREE_DIMENSIONAL_MATCHING_REQUIRED_AUTHORING_MOTIF
    ),
}

BOUNDARY_SPECS: dict[str, dict[str, str]] = {
    KNAPSACK: {
        "canonical_module": "ComplexityReduction.Presentation.Knapsack",
        "source_file": "Lean/Reference/ComplexityReduction/Presentation/Knapsack.lean",
        "semantic_evidence": (
            "ComplexityReduction.Presentation.Knapsack.structuredProblem_accepts"
        ),
        "rationale": (
            "The canonical target uses unaryNat payloads.  The public library "
            "certifies unary-to-binary normalization, but the v1 task proposed "
            "the reverse binary-hardness-to-unary direction.  Expanding a binary "
            "integer to unary is not polynomial in the binary input length, so "
            "that reverse representation bridge cannot be assumed by this "
            "benchmark.  This is a benchmark/formalization boundary, not a claim "
            "that the decision predicate is tractable."
        ),
    },
    PARTITION: {
        "canonical_module": "ComplexityReduction.Presentation.Partition",
        "source_file": "Lean/Reference/ComplexityReduction/Presentation/Partition.lean",
        "semantic_evidence": (
            "ComplexityReduction.Presentation.Partition.structuredProblem_accepts"
        ),
        "rationale": (
            "The canonical target stores weights with unaryNat.  The available "
            "certified representation adapter runs from unary Partition to binary "
            "Partition; v1 requested the reverse direction from the binary "
            "hardness route.  A literal binary-to-unary expansion can be "
            "exponential in encoded input length and therefore is not an "
            "admissible polynomial bridge without new independent evidence.  This "
            "classification makes no tractability claim."
        ),
    },
    JOB_SEQUENCING: {
        "canonical_module": "ComplexityReduction.Presentation.JobSequencing",
        "source_file": (
            "Lean/Reference/ComplexityReduction/Presentation/JobSequencing.lean"
        ),
        "semantic_evidence": (
            "ComplexityReduction.Presentation.JobSequencing.structuredProblem_accepts"
        ),
        "rationale": (
            "The canonical Job Sequencing endpoint uses unaryNat processing times, "
            "deadlines, profits, and threshold.  The known binary hardness route "
            "targets the distinct JobSequencingBinary presentation; promoting it "
            "to this unary endpoint would require the same unsupported "
            "polynomial binary-to-unary expansion.  The identity remains a "
            "zero-weight regression boundary and is not reclassified as an easy "
            "problem."
        ),
    },
}

TRANSITIONS: tuple[dict[str, str], ...] = (
    {
        "canonical_problem": KNAPSACK,
        "from_case_id": "cval-au-01-knapsack-native-bridge",
        "to_case_id": "frontier-01-knapsack-unary-boundary",
        "classification": "unary_numeric_demotion",
        "reason": BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": PARTITION,
        "from_case_id": "cval-au-02-partition-native-bridge",
        "to_case_id": "frontier-02-partition-unary-boundary",
        "classification": "unary_numeric_demotion",
        "reason": BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": JOB_SEQUENCING,
        "from_case_id": "chld-au-02-job-sequencing-native",
        "to_case_id": "r1-pub-09-job-sequencing-unary-boundary",
        "classification": "unary_numeric_zero_weight_boundary",
        "reason": BOUNDARY_FAILURE,
    },
    {
        "canonical_problem": FEEDBACK_ARC_SET,
        "from_case_id": "frontier-01-feedback-arc-set",
        "to_case_id": "chld-au-09-feedback-arc-set",
        "classification": "frontier_to_scored_authoring",
        "reason": "typed_dependent_composition_now_in_scope",
    },
    {
        "canonical_problem": THREE_DIMENSIONAL_MATCHING,
        "from_case_id": "frontier-02-three-dimensional-matching",
        "to_case_id": "chld-au-10-three-dimensional-matching",
        "classification": "frontier_to_scored_authoring",
        "reason": "typed_direct_tm_authoring_now_in_scope",
    },
    {
        "canonical_problem": ZERO_ONE_IP_BINARY,
        "from_case_id": "r1-pub-09-zero-one-ip-binary",
        "to_case_id": "cval-er-05-zero-one-ip-binary",
        "classification": "zero_weight_to_scored_existing",
        "reason": "frozen_public_forward_route_promoted_to_c0_existing",
    },
    {
        "canonical_problem": SEEING_SET,
        "from_case_id": "chld-au-05-seeing-set",
        "to_case_id": "cval-au-03-seeing-set",
        "classification": "split_rebalance",
        "reason": "heldout_authoring_capacity_reserved_for_new_h_j_families",
    },
)


def _read(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _sha256(path: Path, *, tagged: bool = False) -> str:
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    return f"sha256:{digest}" if tagged else digest


def _relative(path: Path) -> str:
    return str(path.resolve().relative_to(ROOT))


def _reference(path: Path, *, tagged: bool = False) -> dict[str, str]:
    return {"file": _relative(path), "sha256": _sha256(path, tagged=tagged)}


def _assert_exact_keys(value: Mapping[str, Any], expected: set[str], label: str) -> None:
    if set(value) != expected:
        raise ValueError(
            f"{label} keys drifted: missing={sorted(expected - set(value))}, "
            f"extra={sorted(set(value) - expected)}"
        )


def _v1_assets() -> list[Path]:
    return [
        V1_MANIFEST,
        V1_MATRIX,
        V1_SCOPE_POLICY,
        V1_ORACLE,
        V1_R1,
        *V1_SUITES.values(),
    ]


def _validate_v1_contract() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, dict[str, Any]],
    dict[str, Any],
]:
    manifest = _read(V1_MANIFEST)
    matrix = _read(V1_MATRIX)
    oracle = _read(V1_ORACLE)
    suites = {split: _read(path) for split, path in V1_SUITES.items()}
    r1 = _read(V1_R1)
    if manifest.get("schema_version") != "hardness_np_hard_capability_manifest_v1":
        raise ValueError("historical v1 capability manifest schema drifted")
    if oracle.get("schema_version") != "hardness_np_hard_capability_oracle_v1":
        raise ValueError("historical v1 capability oracle schema drifted")
    if matrix.get("identity_count") != 44 or len(matrix.get("identities", [])) != 44:
        raise ValueError("historical target matrix is not the frozen 44-identity universe")
    if len(oracle.get("cases", [])) != 34:
        raise ValueError("historical capability oracle is not a 34-case contract")
    for split, path in V1_SUITES.items():
        ref = manifest["suites"][split]
        if ref["file"] != _relative(path) or ref["sha256"] != _sha256(path):
            raise ValueError(f"historical manifest no longer binds {split} suite")
    for key, path in (
        ("oracle", V1_ORACLE),
        ("target_matrix", V1_MATRIX),
        ("scope_policy", V1_SCOPE_POLICY),
    ):
        ref = manifest[key]
        if ref["file"] != _relative(path) or ref["sha256"] != _sha256(path):
            raise ValueError(f"historical manifest no longer binds {key}")
    return manifest, matrix, oracle, suites, r1


def _matrix_by_problem(matrix: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        str(row["canonical_declaration"]): row
        for row in matrix["identities"]
    }


def _public_case(
    *,
    case_id: str,
    module: str,
    problem: str,
    family: str,
    budget_profile: str,
) -> dict[str, Any]:
    return {
        "case_id": case_id,
        "module": module,
        "problem": problem,
        "family": family,
        "budget_profile": budget_profile,
    }


def _oracle_case(
    *,
    case_id: str,
    split: str,
    family: str,
    identity: Mapping[str, Any],
    tier: str,
    outcome_class: str,
    level: str,
    scored: bool,
    requires_model: bool,
    expected_public_status: str,
    expected_failure_codes: list[str],
    route_length: int | None,
    difficulty_axes: list[str],
    blocker_bucket: str | None = None,
    required_authoring_motif: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    result = {
        "blocker_bucket": blocker_bucket,
        "canonical_identity": identity["identity_id"],
        "canonical_problem": identity["canonical_declaration"],
        "case_id": case_id,
        "difficulty_axes": difficulty_axes,
        "expected_failure_codes": expected_failure_codes,
        "expected_public_status": expected_public_status,
        "family": family,
        "level": level,
        "level_bucket": level.split("-")[0],
        "matrix_disposition": identity["disposition"],
        "outcome_class": outcome_class,
        "requires_model": requires_model,
        "route_length": route_length,
        "scored": scored,
        "split": split,
        "tier": tier,
    }
    if required_authoring_motif is not None:
        result["required_authoring_motif"] = deepcopy(required_authoring_motif)
    return result


def _build_scope_policy(
    *, v1_scope: Mapping[str, Any], matrix_by_problem: Mapping[str, Mapping[str, Any]]
) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    for raw in v1_scope["entries"]:
        entry = deepcopy(raw)
        entry["schema_version"] = SCOPE_ENTRY_SCHEMA
        entry["failure_code"] = None
        entries.append(entry)
    for problem, spec in BOUNDARY_SPECS.items():
        identity = matrix_by_problem[problem]
        entries.append(
            {
                "schema_version": SCOPE_ENTRY_SCHEMA,
                "identity_id": identity["identity_id"],
                "canonical_declaration": problem,
                "canonical_module": spec["canonical_module"],
                "problem_node_id": identity["problem_node_id"],
                "representation_node_id": identity["representation_node_id"],
                "disposition": BOUNDARY_DISPOSITION,
                "category": BOUNDARY_BUCKET,
                "rationale": spec["rationale"],
                "public_source_file": spec["source_file"],
                "semantic_evidence_declaration": spec["semantic_evidence"],
                "failure_code": BOUNDARY_FAILURE,
            }
        )
    entries.sort(key=lambda row: (row["canonical_declaration"], row["identity_id"]))
    return {
        "schema_version": SCOPE_SCHEMA,
        "description": (
            "Exact-identity production scope policy for public non-targets and "
            "encoding-complexity boundaries.  Boundary rows record the absence of "
            "an admissible polynomial reverse representation bridge; they do not "
            "assert that the underlying decision predicate is tractable."
        ),
        "entries": entries,
    }


def _build_matrix(
    *, v1_matrix: Mapping[str, Any], scope_policy_object: Any
) -> dict[str, Any]:
    matrix = deepcopy(v1_matrix)
    matrix["schema_version"] = MATRIX_SCHEMA
    policy_rows = {
        row["identity_id"]: row
        for row in scope_policy_object.to_dict(root=ROOT)["entries"]
    }
    for row in matrix["identities"]:
        row["schema_version"] = MATRIX_ROW_SCHEMA
        policy = policy_rows.get(row["identity_id"])
        row["scope_policy"] = deepcopy(policy) if policy is not None else None
        if row["canonical_declaration"] in BOUNDARY_SPECS:
            row["basis"] = "formal_encoding_complexity_policy"
            row["basis_reason"] = BOUNDARY_SPECS[row["canonical_declaration"]][
                "rationale"
            ]
            row["blocker"] = BOUNDARY_BUCKET
            row["can_form_typed_authoring_dag"] = False
            row["disposition"] = BOUNDARY_DISPOSITION
            row["in_scope_np_hard"] = False
            row["missing_formal_prerequisite"] = [
                "polynomial_binary_to_unary_encoding_bridge"
            ]
            row["next_action"] = (
                "remain zero-model boundary evidence until an independent "
                "polynomial hardness construction for the exact unary endpoint exists"
            )
            row["planner"] = {
                "capability_dag_node_count": 0,
                "explanation": BOUNDARY_SPECS[row["canonical_declaration"]][
                    "rationale"
                ],
                "failure_code": BOUNDARY_FAILURE,
                "gap_node_count": 0,
                "missing_capabilities": [
                    "polynomial_binary_to_unary_encoding_bridge"
                ],
                "model_calls": 0,
                "plan_id": sha256_id(
                    {
                        "canonical_identity": row["identity_id"],
                        "disposition": BOUNDARY_DISPOSITION,
                        "failure_code": BOUNDARY_FAILURE,
                    }
                ),
                "selected_hub": None,
                "status": "BLOCKED",
                "task_class": None,
            }
            row["production_entry_failure_code"] = BOUNDARY_FAILURE
            row["production_entry_model_calls"] = 0
            row["production_entry_status"] = "blocked_missing_prerequisite"
            row["production_entry_verified"] = False
            row["verified_artifact"] = None
    disposition_counts: dict[str, int] = {}
    for row in matrix["identities"]:
        disposition = str(row["disposition"])
        disposition_counts[disposition] = disposition_counts.get(disposition, 0) + 1
    matrix["disposition_counts"] = dict(sorted(disposition_counts.items()))
    matrix["blocked_count"] = sum(
        disposition_counts.get(name, 0)
        for name in (
            "blocked_missing_formal_prerequisite",
            BOUNDARY_DISPOSITION,
        )
    )
    matrix["auxiliary_count"] = disposition_counts.get("auxiliary_or_non_target", 0)
    matrix["in_scope_count"] = disposition_counts.get("in_scope_np_hard", 0)
    matrix["scope_policy"] = scope_policy_object.to_dict(root=ROOT)
    matrix["matrix_id"] = sha256_id(
        {key: value for key, value in matrix.items() if key != "matrix_id"}
    )
    return matrix


def _v1_capability_rows(
    *, oracle: Mapping[str, Any], suites: Mapping[str, Mapping[str, Any]]
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    public_by_case: dict[str, dict[str, Any]] = {}
    for split in SPLITS:
        suite = suites[split]
        for row in suite["cases"]:
            public_by_case[row["case_id"]] = {**deepcopy(row), "_split": split}
    oracle_by_case = {row["case_id"]: deepcopy(row) for row in oracle["cases"]}
    if set(public_by_case) != set(oracle_by_case):
        raise ValueError("v1 public suites and scorer oracle case IDs drifted")
    return public_by_case, oracle_by_case


def _unchanged_case(
    *, case_id: str, public_by_case: Mapping[str, Mapping[str, Any]], oracle_by_case: Mapping[str, Mapping[str, Any]]
) -> tuple[dict[str, Any], dict[str, Any]]:
    public = {key: public_by_case[case_id][key] for key in PUBLIC_CASE_FIELDS}
    oracle = deepcopy(oracle_by_case[case_id])
    oracle["blocker_bucket"] = None
    return public, oracle


def _build_capability_contract(
    *,
    v1_oracle: Mapping[str, Any],
    v1_suites: Mapping[str, Mapping[str, Any]],
    v2_matrix_by_problem: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, list[dict[str, Any]]], list[dict[str, Any]]]:
    public_by_case, oracle_by_case = _v1_capability_rows(
        oracle=v1_oracle, suites=v1_suites
    )
    split_case_ids = {
        "dev": [row["case_id"] for row in v1_suites["dev"]["cases"]],
        "validation": [
            "cval-er-01-zero-one-ip-direct",
            "cval-er-02-exact-cover-two-hop",
            "cval-er-03-knapsack-binary-three-hop",
            "cval-er-04-job-sequencing-binary-four-hop",
            "cval-er-05-zero-one-ip-binary",
            "cval-au-03-seeing-set",
            "cval-sf-01-role-graph-ir-internal",
            "cval-sf-02-graph-wellformed-policy",
        ],
        "heldout": [
            "chld-er-01-chromatic-number",
            "chld-er-02-node-deletion-bipartite",
            "chld-er-03-partition-binary-long",
            "chld-er-04-two-disjoint-paths-max-route",
            "chld-au-01-feedback-node-set",
            "chld-au-03-max-cut-structured",
            "chld-au-04-max-cut-binary",
            "chld-au-06-hitting-set",
            "chld-au-07-set-covering",
            "chld-au-08-set-packing",
            "chld-au-09-feedback-arc-set",
            "chld-au-10-three-dimensional-matching",
            "chld-sf-01-role-graph-wellformed",
            "chld-sf-02-set-system-wellformed",
            "chld-sf-03-graph-atoms-wellformed",
            "chld-sf-04-two-cnf-tractable",
        ],
        "frontier": [
            "frontier-01-knapsack-unary-boundary",
            "frontier-02-partition-unary-boundary",
        ],
    }
    generated: dict[str, tuple[dict[str, Any], dict[str, Any]]] = {}
    renamed_old_cases = {
        "cval-au-01-knapsack-native-bridge",
        "cval-au-02-partition-native-bridge",
        "chld-au-02-job-sequencing-native",
        "chld-au-05-seeing-set",
        "frontier-01-feedback-arc-set",
        "frontier-02-three-dimensional-matching",
    }
    for case_id in sorted(set(public_by_case) - renamed_old_cases):
        generated[case_id] = _unchanged_case(
            case_id=case_id,
            public_by_case=public_by_case,
            oracle_by_case=oracle_by_case,
        )

    zero_identity = v2_matrix_by_problem[ZERO_ONE_IP_BINARY]
    generated["cval-er-05-zero-one-ip-binary"] = (
        _public_case(
            case_id="cval-er-05-zero-one-ip-binary",
            module="ComplexityReduction.Presentation.ZeroOneIPBinary",
            problem=ZERO_ONE_IP_BINARY,
            family="numeric",
            budget_profile="formal-default",
        ),
        _oracle_case(
            case_id="cval-er-05-zero-one-ip-binary",
            split="validation",
            family="numeric",
            identity=zero_identity,
            tier="C0-existing",
            outcome_class="existing-route",
            level="L2",
            scored=True,
            requires_model=False,
            expected_public_status="VERIFIED",
            expected_failure_codes=[],
            route_length=2,
            difficulty_axes=["route-composition", "binary-encoding"],
        ),
    )

    seeing_public = public_by_case["chld-au-05-seeing-set"]
    seeing_oracle = deepcopy(oracle_by_case["chld-au-05-seeing-set"])
    seeing_public_v2 = {
        **{key: seeing_public[key] for key in PUBLIC_CASE_FIELDS},
        "case_id": "cval-au-03-seeing-set",
    }
    seeing_oracle.update(
        {
            "blocker_bucket": None,
            "case_id": "cval-au-03-seeing-set",
            "required_authoring_motif": deepcopy(
                SEEING_SET_REQUIRED_AUTHORING_MOTIF
            ),
            "split": "validation",
        }
    )
    generated["cval-au-03-seeing-set"] = (seeing_public_v2, seeing_oracle)

    for old_case_id, new_case_id, problem, level, axes in (
        (
            "frontier-01-feedback-arc-set",
            "chld-au-09-feedback-arc-set",
            FEEDBACK_ARC_SET,
            "L5",
            ["new-gadget", "mapping-invariant", "semantic-iff", "polynomial-bound"],
        ),
        (
            "frontier-02-three-dimensional-matching",
            "chld-au-10-three-dimensional-matching",
            THREE_DIMENSIONAL_MATCHING,
            "L5",
            ["family-heldout", "new-gadget", "semantic-iff", "polynomial-bound"],
        ),
    ):
        old_public = public_by_case[old_case_id]
        identity = v2_matrix_by_problem[problem]
        generated[new_case_id] = (
            _public_case(
                case_id=new_case_id,
                module=old_public["module"],
                problem=problem,
                family=old_public["family"],
                budget_profile="formal-default",
            ),
            _oracle_case(
                case_id=new_case_id,
                split="heldout",
                family=old_public["family"],
                identity=identity,
                tier="C0-authoring",
                outcome_class="first-authoring",
                level=level,
                scored=True,
                requires_model=True,
                expected_public_status="VERIFIED",
                expected_failure_codes=[],
                route_length=None,
                difficulty_axes=axes,
                required_authoring_motif=REQUIRED_AUTHORING_MOTIFS.get(
                    new_case_id
                ),
            ),
        )

    for old_case_id, new_case_id, problem in (
        (
            "cval-au-01-knapsack-native-bridge",
            "frontier-01-knapsack-unary-boundary",
            KNAPSACK,
        ),
        (
            "cval-au-02-partition-native-bridge",
            "frontier-02-partition-unary-boundary",
            PARTITION,
        ),
    ):
        old_public = public_by_case[old_case_id]
        identity = v2_matrix_by_problem[problem]
        generated[new_case_id] = (
            _public_case(
                case_id=new_case_id,
                module=old_public["module"],
                problem=problem,
                family=old_public["family"],
                budget_profile="frontier-default",
            ),
            _oracle_case(
                case_id=new_case_id,
                split="frontier",
                family=old_public["family"],
                identity=identity,
                tier="F0-frontier",
                outcome_class="frontier",
                level="L6",
                scored=False,
                requires_model=False,
                expected_public_status="BLOCKED_MISSING_PREREQUISITE",
                expected_failure_codes=[BOUNDARY_FAILURE],
                route_length=None,
                difficulty_axes=[
                    "encoding-direction",
                    "binary-to-unary-expansion",
                    "polynomial-bound",
                    "formal-prerequisite",
                ],
                blocker_bucket=BOUNDARY_BUCKET,
            ),
        )

    for case_id, motif in REQUIRED_AUTHORING_MOTIFS.items():
        if case_id not in generated:
            raise ValueError(f"required authoring motif case is absent: {case_id}")
        generated[case_id][1]["required_authoring_motif"] = deepcopy(motif)

    public_splits: dict[str, list[dict[str, Any]]] = {}
    oracle_cases: list[dict[str, Any]] = []
    for split in SPLITS:
        rows: list[dict[str, Any]] = []
        for case_id in split_case_ids[split]:
            public, oracle = generated[case_id]
            if oracle["split"] != split:
                raise ValueError(f"generated case {case_id} has the wrong split")
            _assert_exact_keys(public, set(PUBLIC_CASE_FIELDS), f"public case {case_id}")
            rows.append(public)
            oracle_cases.append(oracle)
        if len(rows) != SPLIT_COUNTS[split]:
            raise ValueError(f"v2 split {split} count drifted")
        public_splits[split] = rows
    if len({row["canonical_identity"] for row in oracle_cases}) != 34:
        raise ValueError("v2 capability contract does not contain 34 unique identities")
    return public_splits, oracle_cases


def _build_r1(
    *,
    v1_r1: Mapping[str, Any],
    v1_matrix_by_problem: Mapping[str, Mapping[str, Any]],
    v2_capability_identities: set[str],
) -> dict[str, Any]:
    cases: list[dict[str, Any]] = []
    for row in v1_r1["cases"]:
        if row["problem"] == ZERO_ONE_IP_BINARY:
            continue
        cases.append(
            {
                "case_id": row["case_id"],
                "module": row["module"],
                "problem": row["problem"],
                "family": row["family"],
                "budget_profile": "formal-default",
            }
        )
    job_identity = v1_matrix_by_problem[JOB_SEQUENCING]
    cases.insert(
        8,
        {
            "case_id": "r1-pub-09-job-sequencing-unary-boundary",
            "module": "ComplexityReduction.Presentation.JobSequencing",
            "problem": JOB_SEQUENCING,
            "family": "numeric",
            "budget_profile": "frontier-default",
        },
    )
    if len(cases) != 10:
        raise ValueError("v2 R1 suite must contain ten cases")
    r1_identities = {
        v1_matrix_by_problem[row["problem"]]["identity_id"] for row in cases
    }
    if len(r1_identities) != 10 or r1_identities & v2_capability_identities:
        raise ValueError("v2 R1 suite is not a disjoint ten-identity partition")
    if job_identity["identity_id"] not in r1_identities:
        raise ValueError("v2 R1 suite lost the unary Job Sequencing boundary")
    for row in cases:
        _assert_exact_keys(row, set(PUBLIC_CASE_FIELDS), f"R1 case {row['case_id']}")
    return {
        "schema_version": R1_SCHEMA,
        "suite_id": "np-hard-public-r1-coverage-v2",
        "cases": cases,
    }


def _contract_counts() -> dict[str, Any]:
    return {
        "case_count": 34,
        "unique_identity_count": 34,
        "split_counts": dict(SPLIT_COUNTS),
        "expected_case_buckets": [
            {"split": "dev", "tier": "C0-existing", "outcome_class": "existing-route", "scored": True, "count": 4},
            {"split": "dev", "tier": "C0-authoring", "outcome_class": "first-authoring", "scored": True, "count": 2},
            {"split": "dev", "tier": "C0-safety", "outcome_class": "safety", "scored": True, "count": 2},
            {"split": "validation", "tier": "C0-existing", "outcome_class": "existing-route", "scored": True, "count": 5},
            {"split": "validation", "tier": "C0-authoring", "outcome_class": "first-authoring", "scored": True, "count": 1},
            {"split": "validation", "tier": "C0-safety", "outcome_class": "safety", "scored": True, "count": 2},
            {"split": "heldout", "tier": "C0-existing", "outcome_class": "existing-route", "scored": True, "count": 4},
            {"split": "heldout", "tier": "C0-authoring", "outcome_class": "first-authoring", "scored": True, "count": 8},
            {"split": "heldout", "tier": "C0-safety", "outcome_class": "safety", "scored": True, "count": 4},
            {"split": "frontier", "tier": "F0-frontier", "outcome_class": "frontier", "scored": False, "count": 2},
        ],
        "blocker_bucket_counts": {BOUNDARY_BUCKET: 2},
    }


def _build_manifest(*, suite_refs: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": MANIFEST_SCHEMA,
        "benchmark_id": BENCHMARK_ID,
        "objective": "target-hardness",
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard input",
        "suites": dict(suite_refs),
        "oracle": {
            **_reference(V2_ORACLE),
            "runner_access": "forbidden",
        },
        "target_matrix": _reference(V2_MATRIX),
        "scope_policy": _reference(V2_SCOPE_POLICY),
        "required_model_profile": {
            "provider": "DeepSeek",
            "base_url": "https://api.deepseek.com",
            "model": "deepseek-v4-flash",
            "reasoning_effort": "low",
            "temperature": 0.0,
            "max_tokens": 16000,
            "timeout_seconds": 300,
            "max_retries": 0,
        },
        "budget_profiles": {
            "formal-default": {
                "attempt_budget": 4,
                "call_budget": "typed-dag-auto",
                "lean_timeout_seconds": 600,
            },
            "frontier-default": {
                "attempt_budget": 4,
                "call_budget": "typed-dag-auto",
                "lean_timeout_seconds": 600,
            },
        },
        "split_policy": {
            "canonical_identity_disjoint": True,
            "family_heldout": ["other"],
            "capability_node_heldout": ["new-gadget", "polynomial-bound"],
            "counts": dict(SPLIT_COUNTS),
        },
        "reserve_policy": {
            "promote_threshold": 0.9,
            "promote_consecutive_versions": 2,
            "intermediate_case_threshold": 0.1,
        },
        "public_suite_case_fields": list(PUBLIC_CASE_FIELDS),
        "forbidden_runner_paths": [
            "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
            "Benchmark/Hardness/Evaluation",
            "problems.7z",
            "problems",
            "problems.json",
            "problems_clean.json",
        ],
        "contract_counts": _contract_counts(),
    }


def _normalized_outcome(value: str) -> str:
    return {
        "existing-route": "existing_route",
        "first-authoring": "first_authoring",
        "existing": "existing_route",
        "authoring": "first_authoring",
    }.get(value, value)


def _capability_placements(
    *, oracle: Mapping[str, Any], matrix_by_problem: Mapping[str, Mapping[str, Any]]
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for row in oracle["cases"]:
        identity_id = row["canonical_identity"]
        identity = matrix_by_problem[row["canonical_problem"]]
        result[identity_id] = {
            "partition": "capability",
            "case_id": row["case_id"],
            "split": row["split"],
            "family": row["family"],
            "canonical_identity": identity_id,
            "canonical_problem": identity["canonical_declaration"],
            "canonical_module": identity["canonical_module"],
            "tier": row["tier"],
            "outcome_class": _normalized_outcome(row["outcome_class"]),
            "scored": row["scored"],
            "requires_model": row["requires_model"],
            "expected_public_status": row["expected_public_status"],
            "expected_failure_codes": list(row["expected_failure_codes"]),
        }
    return result


def _r1_placements(
    *, suite: Mapping[str, Any], matrix_by_problem: Mapping[str, Mapping[str, Any]]
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for row in suite["cases"]:
        identity = matrix_by_problem[row["problem"]]
        identity_id = identity["identity_id"]
        result[identity_id] = {
            "partition": "R1-zero-weight",
            "case_id": row["case_id"],
            "split": "r1-public",
            "family": row["family"],
            "canonical_identity": identity_id,
            "canonical_problem": identity["canonical_declaration"],
            "canonical_module": identity["canonical_module"],
            "tier": "R1-zero-weight",
            "outcome_class": "zero_weight_control",
            "scored": False,
            "requires_model": False,
        }
    return result


def _contract_asset_record(
    *,
    epoch: str,
    manifest_path: Path,
    oracle_path: Path,
    suite_paths: Mapping[str, Path],
    matrix_path: Path,
    r1_path: Path,
) -> dict[str, Any]:
    matrix = _read(matrix_path)
    return {
        "contract_epoch": epoch,
        "manifest": _reference(manifest_path, tagged=True),
        "oracle": {**_reference(oracle_path, tagged=True), "runner_access": "forbidden"},
        "suites": {
            split: _reference(suite_paths[split]) for split in SPLITS
        },
        "target_matrix": {
            **_reference(matrix_path, tagged=True),
            "matrix_id": matrix.get("matrix_id"),
        },
        "r1_suite": _reference(r1_path, tagged=True),
        "case_count": 34,
        "r1_case_count": 10,
        "identity_partition_count": 44,
    }


def _historical_h_i_evidence() -> dict[str, Any]:
    report = _read(H_I_REPORT)
    if report.get("report_id") != H_I_REPORT_ID or report.get("passed") is not True:
        raise ValueError("historical H-I full report identity/pass state drifted")
    source_files = report["source_control"]["files"]
    expected_current = {
        _relative(V1_MANIFEST): _sha256(V1_MANIFEST),
        _relative(V1_ORACLE): _sha256(V1_ORACLE),
        _relative(V1_MATRIX): _sha256(V1_MATRIX),
        _relative(V1_R1): _sha256(V1_R1),
    }
    for relative, digest in expected_current.items():
        if source_files.get(relative) != digest:
            raise ValueError(f"historical H-I report no longer binds {relative}")
    raw_pairs: list[dict[str, Any]] = []
    for split_row in report["capability_baseline"]["split_reports"]:
        run = split_row["run"]
        score = split_row["score"]
        run_path = Path(run["file"])
        score_path = Path(score["file"])
        if not run_path.is_absolute():
            run_path = ROOT / run_path
        if not score_path.is_absolute():
            score_path = ROOT / score_path
        if _sha256(run_path, tagged=True) != run["sha256"]:
            raise ValueError(f"historical H-I raw run hash drifted: {run_path}")
        if _sha256(score_path, tagged=True) != score["sha256"]:
            raise ValueError(f"historical H-I score hash drifted: {score_path}")
        raw_pairs.append(
            {
                "split": split_row["split"],
                "run": {
                    **_reference(run_path, tagged=True),
                    "run_id": run["run_id"],
                    "run_valid": run["run_valid"],
                    "case_count": run["case_count"],
                },
                "score": {
                    **_reference(score_path, tagged=True),
                    "score_id": score["score_id"],
                    "score_valid": score["score_valid"],
                },
            }
        )
    return {
        "evidence_kind": "historical_real_run_file_references_only",
        "case_rows_copied_or_synthesized": False,
        "full_report": {
            **_reference(H_I_REPORT, tagged=True),
            "report_id": report["report_id"],
            "schema_version": report["schema_version"],
            "passed": report["passed"],
        },
        "real_deepseek_summary": {
            "real_deepseek_http_calls": report["stage_benchmarks"][
                "real_deepseek_http_calls"
            ],
            "http_200_count": report["stage_benchmarks"]["http_200_count"],
            "all_concurrency_drained": report["stage_benchmarks"][
                "all_concurrency_drained"
            ],
        },
        "capability_raw_score_pairs": raw_pairs,
    }


def _build_migration_report(
    *,
    v1_matrix: Mapping[str, Any],
    v2_matrix: Mapping[str, Any],
    v1_oracle: Mapping[str, Any],
    v2_oracle: Mapping[str, Any],
    v1_r1: Mapping[str, Any],
    v2_r1: Mapping[str, Any],
) -> dict[str, Any]:
    v1_by_problem = _matrix_by_problem(v1_matrix)
    v2_by_problem = _matrix_by_problem(v2_matrix)
    v1_ids = {row["identity_id"]: row for row in v1_matrix["identities"]}
    v2_ids = {row["identity_id"]: row for row in v2_matrix["identities"]}
    if set(v1_ids) != set(v2_ids) or len(v1_ids) != 44:
        raise ValueError("v2 migration changed the canonical identity universe")
    v1_capability = _capability_placements(
        oracle=v1_oracle, matrix_by_problem=v1_by_problem
    )
    v2_capability = _capability_placements(
        oracle=v2_oracle, matrix_by_problem=v2_by_problem
    )
    v1_r1_rows = _r1_placements(suite=v1_r1, matrix_by_problem=v1_by_problem)
    v2_r1_rows = _r1_placements(suite=v2_r1, matrix_by_problem=v2_by_problem)
    if not (
        len(v1_capability) == len(v2_capability) == 34
        and len(v1_r1_rows) == len(v2_r1_rows) == 10
        and not set(v1_capability) & set(v1_r1_rows)
        and not set(v2_capability) & set(v2_r1_rows)
        and set(v1_capability) | set(v1_r1_rows) == set(v1_ids)
        and set(v2_capability) | set(v2_r1_rows) == set(v2_ids)
    ):
        raise ValueError("v1/v2 capability+R1 assignments are not exhaustive 34+10 partitions")
    v1_placements = {**v1_capability, **v1_r1_rows}
    v2_placements = {**v2_capability, **v2_r1_rows}
    transition_by_problem = {row["canonical_problem"]: row for row in TRANSITIONS}
    identity_rows: list[dict[str, Any]] = []
    approved: list[dict[str, Any]] = []
    for identity_id in sorted(v1_ids):
        before_identity = v1_ids[identity_id]
        after_identity = v2_ids[identity_id]
        for key in ("canonical_declaration", "canonical_module", "family"):
            if before_identity[key] != after_identity[key]:
                raise ValueError(f"canonical identity metadata drifted for {identity_id}")
        problem = before_identity["canonical_declaration"]
        before = v1_placements[identity_id]
        after = v2_placements[identity_id]
        transition = transition_by_problem.get(problem)
        if transition is None:
            if before != after:
                raise ValueError(f"unapproved assignment transition for {problem}")
            classification = "unchanged"
            reason = None
        else:
            if (
                before["case_id"] != transition["from_case_id"]
                or after["case_id"] != transition["to_case_id"]
            ):
                raise ValueError(f"frozen migration mapping drifted for {problem}")
            classification = transition["classification"]
            reason = transition["reason"]
            approved.append(
                {
                    **transition,
                    "canonical_identity": identity_id,
                    "family": before_identity["family"],
                    "v1": deepcopy(before),
                    "v2": deepcopy(after),
                    "accepted_without_failure": classification.startswith(
                        "unary_numeric_"
                    ),
                }
            )
        identity_rows.append(
            {
                "canonical_identity": identity_id,
                "canonical_problem": problem,
                "canonical_module": before_identity["canonical_module"],
                "family": before_identity["family"],
                "classification": classification,
                "reason": reason,
                "v1": deepcopy(before),
                "v2": deepcopy(after),
            }
        )
    if len(approved) != 7 or sum(row["classification"] == "unchanged" for row in identity_rows) != 37:
        raise ValueError("migration must contain exactly seven transitions and 37 unchanged identities")
    demotions = [
        row for row in approved if row["classification"].startswith("unary_numeric_")
    ]
    audit: dict[str, Any] = {
        "schema_version": MIGRATION_SCHEMA,
        "passed": True,
        "contracts": {
            "v1": _contract_asset_record(
                epoch="v1",
                manifest_path=V1_MANIFEST,
                oracle_path=V1_ORACLE,
                suite_paths=V1_SUITES,
                matrix_path=V1_MATRIX,
                r1_path=V1_R1,
            ),
            "v2": _contract_asset_record(
                epoch="v2",
                manifest_path=V2_MANIFEST,
                oracle_path=V2_ORACLE,
                suite_paths=V2_SUITES,
                matrix_path=V2_MATRIX,
                r1_path=V2_R1,
            ),
        },
        "stage_contract_epochs": {
            "h-j.1-adapter": "v1",
            "h-j.2-tmkarp": "v1",
            "h-j.3-dependent": "v1",
            "h-j.4-direct-tm": "v2",
            "h-j.5-gadget": "v2",
        },
        "identity_universe": {
            "count": 44,
            "canonical_identity_set_preserved": True,
            "canonical_declaration_module_family_preserved": True,
            "unchanged_count": 37,
            "approved_transition_count": 7,
            "crosswalk": identity_rows,
        },
        "capability_denominator": {
            "v1_count": 34,
            "v2_count": 34,
            "shared_identity_count": len(set(v1_capability) & set(v2_capability)),
            "departed_to_r1": sorted(set(v1_capability) - set(v2_capability)),
            "introduced_from_r1": sorted(set(v2_capability) - set(v1_capability)),
            "canonical_identity_crosswalk_count": 34,
            "canonical_identity_crosswalk": [
                row for row in identity_rows if row["canonical_identity"] in v2_capability
            ],
        },
        "r1_zero_weight_partition": {
            "v1_count": 10,
            "v2_count": 10,
            "shared_identity_count": len(set(v1_r1_rows) & set(v2_r1_rows)),
            "crosswalk": [
                row
                for row in identity_rows
                if row["canonical_identity"] in set(v1_r1_rows) | set(v2_r1_rows)
            ],
        },
        "approved_transitions": sorted(approved, key=lambda row: row["from_case_id"]),
        "accepted_unary_numeric_demotions": sorted(
            demotions, key=lambda row: row["from_case_id"]
        ),
        "cross_epoch_metric_policy": {
            "stage_curves_directly_comparable": False,
            "note": "H-J.1-.3 are native v1 evidence; H-J.4-.5 are native v2 evidence",
            "final_gate_contract_epoch": "v2",
        },
        "historical_h_i_raw_evidence": _historical_h_i_evidence(),
    }
    audit["audit_id"] = sha256_id(audit)
    return audit


def _validate_static_outputs(
    *, matrix: Mapping[str, Any], oracle_cases: list[Mapping[str, Any]], r1: Mapping[str, Any]
) -> None:
    matrix_identities = {row["identity_id"] for row in matrix["identities"]}
    capability_identities = {row["canonical_identity"] for row in oracle_cases}
    by_problem = _matrix_by_problem(matrix)
    r1_identities = {by_problem[row["problem"]]["identity_id"] for row in r1["cases"]}
    if len(matrix_identities) != 44:
        raise ValueError("v2 matrix identity count is not 44")
    if len(capability_identities) != 34 or len(r1_identities) != 10:
        raise ValueError("v2 contract is not a 34 capability + 10 R1 partition")
    observed_motifs = {
        str(row["case_id"]): row["required_authoring_motif"]
        for row in oracle_cases
        if row.get("required_authoring_motif") is not None
    }
    if observed_motifs != REQUIRED_AUTHORING_MOTIFS:
        raise ValueError(
            "v2 scorer oracle does not freeze exactly the ten accepted authoring motifs"
        )
    if capability_identities & r1_identities or capability_identities | r1_identities != matrix_identities:
        raise ValueError("v2 capability/R1 identities are not disjoint and exhaustive")
    bucket_counts: dict[tuple[str, str, str, bool], int] = {}
    blocker_counts: dict[str, int] = {}
    for row in oracle_cases:
        key = (row["split"], row["tier"], row["outcome_class"], row["scored"])
        bucket_counts[key] = bucket_counts.get(key, 0) + 1
        if row["blocker_bucket"] is not None:
            blocker_counts[row["blocker_bucket"]] = blocker_counts.get(row["blocker_bucket"], 0) + 1
    expected = {
        (row["split"], row["tier"], row["outcome_class"], row["scored"]): row["count"]
        for row in _contract_counts()["expected_case_buckets"]
    }
    if bucket_counts != expected or blocker_counts != {BOUNDARY_BUCKET: 2}:
        raise ValueError("v2 capability bucket contract drifted")
    boundary_rows = [row for row in oracle_cases if row["blocker_bucket"] is not None]
    if not all(
        row["requires_model"] is False
        and row["expected_public_status"] == "BLOCKED_MISSING_PREREQUISITE"
        and row["expected_failure_codes"] == [BOUNDARY_FAILURE]
        for row in boundary_rows
    ):
        raise ValueError("v2 encoding boundaries are not exact zero-model blockers")
    r1_rows = {row["problem"]: row for row in r1["cases"]}
    if set(r1_rows) & {KNAPSACK, PARTITION}:
        raise ValueError("scorer-only F0 encoding boundaries leaked into R1")
    if set(r1_rows) & {ZERO_ONE_IP_BINARY}:
        raise ValueError("promoted ZeroOneIPBinary identity remained in R1")
    if JOB_SEQUENCING not in r1_rows:
        raise ValueError("R1 lost the unary Job Sequencing boundary")
    if by_problem[JOB_SEQUENCING]["disposition"] != BOUNDARY_DISPOSITION:
        raise ValueError("R1 Job Sequencing is not policy-backed boundary evidence")
    existing_r1 = [
        row for problem, row in r1_rows.items() if problem != JOB_SEQUENCING
    ]
    if len(existing_r1) != 9 or any(
        by_problem[row["problem"]].get("has_forward_route") is not True
        for row in existing_r1
    ):
        raise ValueError("v2 R1 must contain exactly nine existing-route controls")


def main() -> int:
    immutable_before = {path: _sha256(path) for path in _v1_assets()}
    v1_manifest, v1_matrix, v1_oracle, v1_suites, v1_r1 = _validate_v1_contract()
    del v1_manifest
    v1_matrix_by_problem = _matrix_by_problem(v1_matrix)
    v1_scope = _read(V1_SCOPE_POLICY)

    scope = _build_scope_policy(
        v1_scope=v1_scope, matrix_by_problem=v1_matrix_by_problem
    )
    _write(V2_SCOPE_POLICY, scope)
    scope_object = load_np_hard_scope_policy(root=ROOT, path=V2_SCOPE_POLICY)
    if len(scope_object.entries) != 11:
        raise ValueError("v2 scope policy must contain 8 safety + 3 boundary identities")

    matrix = _build_matrix(v1_matrix=v1_matrix, scope_policy_object=scope_object)
    _write(V2_MATRIX, matrix)
    matrix_by_problem = _matrix_by_problem(matrix)

    public_splits, oracle_cases = _build_capability_contract(
        v1_oracle=v1_oracle,
        v1_suites=v1_suites,
        v2_matrix_by_problem=matrix_by_problem,
    )
    suite_refs: dict[str, dict[str, str]] = {}
    for split in SPLITS:
        _write(
            V2_SUITES[split],
            {
                "schema_version": SUITE_SCHEMA,
                "suite_id": f"np-hard-capability-{split}-v2",
                "split": split,
                "cases": public_splits[split],
            },
        )
        suite_refs[split] = _reference(V2_SUITES[split])
    oracle = {
        "schema_version": ORACLE_SCHEMA,
        "benchmark_id": BENCHMARK_ID,
        "cases": oracle_cases,
    }
    _write(V2_ORACLE, oracle)

    capability_identities = {row["canonical_identity"] for row in oracle_cases}
    r1 = _build_r1(
        v1_r1=v1_r1,
        v1_matrix_by_problem=v1_matrix_by_problem,
        v2_capability_identities=capability_identities,
    )
    _write(V2_R1, r1)

    manifest = _build_manifest(suite_refs=suite_refs)
    _write(V2_MANIFEST, manifest)
    _validate_static_outputs(matrix=matrix, oracle_cases=oracle_cases, r1=r1)

    migration = _build_migration_report(
        v1_matrix=v1_matrix,
        v2_matrix=matrix,
        v1_oracle=v1_oracle,
        v2_oracle=oracle,
        v1_r1=v1_r1,
        v2_r1=r1,
    )
    _write(MIGRATION_REPORT, migration)

    immutable_after = {path: _sha256(path) for path in _v1_assets()}
    if immutable_before != immutable_after:
        changed = [
            _relative(path)
            for path in immutable_before
            if immutable_before[path] != immutable_after[path]
        ]
        raise ValueError(f"v2 generator modified historical v1 assets: {changed}")

    print(
        canonical_json(
            {
                "manifest": _reference(V2_MANIFEST),
                "oracle": _reference(V2_ORACLE),
                "target_matrix": _reference(V2_MATRIX),
                "scope_policy": _reference(V2_SCOPE_POLICY),
                "r1_suite": _reference(V2_R1),
                "migration_report": {
                    **_reference(MIGRATION_REPORT),
                    "audit_id": migration["audit_id"],
                },
                "split_counts": SPLIT_COUNTS,
                "capability_identity_count": 34,
                "r1_identity_count": 10,
                "migration_transition_count": 7,
                "historical_v1_assets_unchanged": True,
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
