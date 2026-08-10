#!/usr/bin/env python3
"""Build the checked-in NP-hard benchmark migration taxonomy."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "Gate/NP_HARD_UNIFIED_BENCHMARK_REGISTRY.json"
OUTPUT_PATH = ROOT / "Gate/BENCHMARK_TAXONOMY.json"
SUITE_ROOTS = (ROOT / "Benchmark/Hardness/Suites", ROOT / "Gate/Suites")

C0_TARGET_SUITES = {
    "np_hard_capability_dev_v1.json",
    "np_hard_capability_validation_v1.json",
    "np_hard_capability_heldout_v1.json",
}
EXACT_EDGE_SUITES = {
    "exact_reduction_edge_dev_v1.json",
    "exact_reduction_edge_validation_v1.json",
    "exact_reduction_edge_heldout_v1.json",
}
FRONTIER_SUITE = "np_hard_capability_frontier_v1.json"
PUBLIC_R1_SUITE = "np_hard_public_r1_coverage_v1.json"


def _read(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def _case_id(case: dict[str, Any]) -> str:
    value = case.get("case_id", case.get("id"))
    if not isinstance(value, str) or not value:
        raise ValueError("suite case lacks case_id/id")
    return value


def _public_values(case: dict[str, Any]) -> list[str]:
    keys = {
        "problem",
        "problem_declaration",
        "production_endpoint",
        "source",
        "target",
        "input_declaration",
    }
    return [str(case[key]) for key in keys if isinstance(case.get(key), str)]


def _classification(filename: str) -> tuple[str, bool]:
    if filename in C0_TARGET_SUITES or filename in EXACT_EDGE_SUITES:
        return "C0", True
    if filename == FRONTIER_SUITE:
        return "F0", False
    if filename == PUBLIC_R1_SUITE:
        return "R1", False
    return "R0/R1", False


def main() -> int:
    registry = _read(REGISTRY_PATH)
    alias_metadata: dict[tuple[str, str], tuple[str, str]] = {}
    case_tier_by_id: dict[str, str] = {}
    migrations: list[dict[str, Any]] = []
    for logical in registry["logical_cases"]:
        logical_id = str(logical["logical_case_id"])
        tier = str(logical["tier"])
        for alias in logical["compatibility_aliases"]:
            key = (str(alias["view"]), str(alias["case_id"]))
            alias_metadata[key] = (logical_id, tier)
            case_tier_by_id[key[1]] = tier
            migrations.append(
                {
                    "compatibility_view": key[0],
                    "case_id": key[1],
                    "logical_case_id": logical_id,
                    "tier": tier,
                    "capability_weight": 0,
                }
            )

    suite_inventory: list[dict[str, Any]] = []
    ownership: list[dict[str, str]] = []
    for suite_path in sorted(
        [path for root in SUITE_ROOTS for path in root.glob("*.json")]
    ):
        suite = _read(suite_path)
        filename = suite_path.name
        default_tier, default_scored = _classification(filename)
        cases: list[dict[str, Any]] = []
        raw_cases = suite.get("cases", [])
        if not isinstance(raw_cases, list):
            raise ValueError(f"{suite_path} cases must be a list")
        for raw_case in raw_cases:
            if not isinstance(raw_case, dict):
                raise ValueError(f"{suite_path} contains a non-object case")
            case_id = _case_id(raw_case)
            tier = case_tier_by_id.get(case_id, default_tier)
            is_capability = default_scored
            if filename in C0_TARGET_SUITES | EXACT_EDGE_SUITES | {PUBLIC_R1_SUITE}:
                public_problem = True
                fixture = False
            else:
                identity_values = _public_values(raw_case)
                public_problem = any(
                    value.startswith("ComplexityReduction.") for value in identity_values
                ) or str(raw_case.get("module", "")).startswith("ComplexityReduction.")
                fixture = any(
                    value.startswith("Benchmark.Hardness.Inputs.")
                    for value in identity_values
                ) or (
                    str(raw_case.get("module", "")).startswith("Benchmark.Hardness.Inputs.")
                    and not public_problem
                )
            if is_capability:
                purpose = (
                    "Exact public reduction-edge capability measurement."
                    if filename in EXACT_EDGE_SUITES
                    else "Public target-hardness capability boundary measurement."
                )
                reason = "Answer-free public C0 input; scored only by its isolated scorer/oracle."
            elif tier == "F0":
                purpose = "Open frontier measurement without a pass-all threshold."
                reason = "Answer-free public F0 input; retained to expose the next missing capability."
            elif filename == PUBLIC_R1_SUITE:
                purpose = "Production existing-route replay, endpoint, axiom, and shortest-route audit."
                reason = "Public R1 coverage is regression-only because its route motif is controlled by C0."
            elif case_id in case_tier_by_id:
                purpose = "Unified legacy R0/R1 regression compatibility case."
                reason = "Historical benchmark behavior is retained with zero capability weight."
            else:
                purpose = "Program, protocol, fixture, mutation, or historical production regression."
                reason = "Existing suite remains regression evidence and cannot contribute to capability score."
            cases.append(
                {
                    "case_id": case_id,
                    "tier": tier,
                    "purpose": purpose,
                    "fixture": fixture,
                    "public_problem": public_problem,
                    "capability_scored": is_capability,
                    "capability_weight": 1 if is_capability else 0,
                    "migration_reason": reason,
                }
            )
            if filename in C0_TARGET_SUITES | {FRONTIER_SUITE, PUBLIC_R1_SUITE}:
                ownership.append(
                    {
                        "case_id": case_id,
                        "suite_file": str(suite_path.relative_to(ROOT)),
                        "tier": tier,
                        "public_identity": str(raw_case["problem"]),
                    }
                )
        suite_inventory.append(
            {
                "suite_file": str(suite_path.relative_to(ROOT)),
                "schema_version": str(suite.get("schema_version", "")),
                "suite_id": str(suite.get("suite_id", suite.get("benchmark_id", filename))),
                "tier": default_tier,
                "purpose": "Complete migration inventory for this checked-in suite asset.",
                "capability_weight": 1 if default_scored else 0,
                "migration_reason": (
                    "C0 cases use their isolated capability scorer."
                    if default_scored
                    else "This suite is non-scoring R0/R1 or F0 evidence."
                ),
                "cases": cases,
            }
        )

    value = {
        "schema_version": "hardness_np_hard_benchmark_taxonomy_v1",
        "benchmark_id": "np-hard-regression-v2",
        "registry": str(REGISTRY_PATH.relative_to(ROOT)),
        "tiers": {
            "R0": "Code, fixture, mutation, blocker, state-machine, and protocol regression; capability weight is zero.",
            "R1": "Production-entry, real-model, fresh-artifact, replay, and audit regression; capability weight is zero.",
            "R0/R1": "A safety contract exercised through the production entry; capability weight is zero.",
            "C0": "Answer-free public capability boundary benchmark with an isolated scorer/oracle.",
            "F0": "Answer-free open frontier benchmark without a pass-all completion threshold.",
        },
        "assets": [
            {
                "asset_id": "legacy-regression-45",
                "classification": ["R0", "R1"],
                "case_count": 45,
                "fixture_case_count": 45,
                "public_identity_case_count": 0,
                "public_capability_case_count": 0,
                "ir_feasibility_case_count": 12,
                "negative_lane_case_count": 15,
                "model_synthesis_case_count": 1,
                "capability_weight": 0,
                "disposition": "compatibility_view_only",
                "migration_reason": "All inputs are fixtures and contribute no public capability score.",
            },
            {
                "asset_id": "legacy-release-reliability-12",
                "classification": ["R0", "R1"],
                "case_count": 12,
                "fixture_case_count": 10,
                "public_identity_case_count": 2,
                "public_capability_case_count": 0,
                "existing_route_case_count": 5,
                "model_authoring_case_count": 5,
                "safety_negative_case_count": 2,
                "historical_round_count": 3,
                "unified_execution_round_count": 1,
                "capability_weight": 0,
                "disposition": "compatibility_view_only",
                "migration_reason": "The former stability suite is one de-duplicated fresh production round.",
            },
            {
                "asset_id": "public-existing-route-coverage-v1",
                "classification": ["R1"],
                "case_count": 10,
                "public_identity_case_count": 10,
                "public_capability_case_count": 0,
                "capability_weight": 0,
                "disposition": "unified_production_lane",
                "migration_reason": "Public route coverage is retained as zero-weight production regression.",
            },
        ],
        "case_migrations": migrations,
        "suite_inventory": suite_inventory,
        "public_identity_ownership": ownership,
    }
    temporary = OUTPUT_PATH.with_suffix(OUTPUT_PATH.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(OUTPUT_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
