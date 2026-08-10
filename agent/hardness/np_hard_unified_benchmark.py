"""Unified R0/R1 registry and runner for NP-hard regression assets.

The historical 45-case benchmark and the 12-case release reliability suite
remain compatibility views only.  This module gives them one stable logical
case registry, selects each logical case at most once, and routes executions
through either the legacy contract runner or one fresh production round.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from threading import Lock
from typing import Any, Callable, Iterable, Mapping

from .benchmark import load_benchmark_manifest, select_benchmark_cases
from .lean_runner import sha256_file
from .model_client import DeepSeekConfig
from .np_hard_generalization import load_np_hard_generalization_suite
from .np_hard_existing_route_qualification import _inventory_identities, _qualify_one
from .np_hard_production import (
    FORMAL_BASE_URL,
    FORMAL_MAX_RETRIES,
    FORMAL_MAX_TOKENS,
    FORMAL_MODEL,
    FORMAL_REASONING_EFFORT,
    FORMAL_TIMEOUT_SECONDS,
    is_formal_np_hard_qualification_config,
)
from .np_hard_release_benchmark import run_np_hard_release_real_round
from .np_hard_target_matrix import load_np_hard_target_matrix


UNIFIED_REGISTRY_SCHEMA_V1 = "hardness_np_hard_unified_registry_v1"
UNIFIED_TAXONOMY_SCHEMA_V1 = "hardness_np_hard_benchmark_taxonomy_v1"
UNIFIED_REPORT_SCHEMA_V1 = "hardness_np_hard_unified_benchmark_report_v1"
UNIFIED_BENCHMARK_ID = "np-hard-regression-v2"
PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V1 = (
    "hardness_np_hard_public_r1_coverage_suite_v1"
)
PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V2 = (
    "hardness_np_hard_public_r1_coverage_suite_v2"
)
PUBLIC_R1_COVERAGE_SUITE_ID = "public-existing-route-coverage-v1"
PUBLIC_R1_COVERAGE_SUITE_ID_V2 = "np-hard-public-r1-coverage-v2"

SELECTORS = {"contract", "production", "all"}
CASE_SELECTORS = {"contract", "production"}
TIERS = {"R0", "R1", "R0/R1"}
MODEL_REQUIREMENTS = {"forbidden", "required"}
FRESHNESS_POLICIES = {"isolated_case", "fresh_production_job"}
EXECUTION_BACKENDS = {
    "legacy_main45",
    "release_real_round",
    "public_existing_route",
}
COMPATIBILITY_VIEWS = {
    "legacy-regression-45": ("legacy_main45", 45),
    "legacy-release-reliability-12": ("release_real_round", 12),
}
CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9._-]*")


class UnifiedBenchmarkError(ValueError):
    """Stable fail-closed error raised by the unified benchmark."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class CompatibilityAlias:
    view: str
    case_id: str


@dataclass(frozen=True)
class UnifiedLogicalCase:
    logical_case_id: str
    tier: str
    capability_weight: int
    fixture: bool
    public_identity: str | None
    model_requirement: str
    freshness: str
    audits: tuple[str, ...]
    selector: str
    execution_backend: str
    source_case_id: str
    semantic_motif: str
    migration_reason: str
    compatibility_aliases: tuple[CompatibilityAlias, ...]


@dataclass(frozen=True)
class UnifiedRegistry:
    benchmark_id: str
    registry_path: Path
    default_jobs: int
    cases: tuple[UnifiedLogicalCase, ...]


LegacyExecutor = Callable[..., Mapping[str, Any]]
ProductionExecutor = Callable[..., Mapping[str, Any]]
PublicCoverageExecutor = Callable[..., Mapping[str, Any]]


def _expect_object(value: Any, *, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise UnifiedBenchmarkError("invalid_unified_registry", f"{label} must be an object")
    return value


def _expect_string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"{label} must be a non-empty string"
        )
    return value


def _expect_string_list(value: Any, *, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not value:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"{label} must be a non-empty list"
        )
    rows = tuple(_expect_string(item, label=f"{label}[]") for item in value)
    if len(set(rows)) != len(rows):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"{label} contains duplicates"
        )
    return rows


def _read_json(path: Path, *, code: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise UnifiedBenchmarkError(code, f"missing file: {path}") from error
    except json.JSONDecodeError as error:
        raise UnifiedBenchmarkError(
            code, f"{path}:{error.lineno}:{error.colno}: {error.msg}"
        ) from error
    return _expect_object(value, label=str(path))


def _parse_case(value: Any, *, index: int) -> UnifiedLogicalCase:
    row = _expect_object(value, label=f"logical_cases[{index}]")
    required_keys = {
        "logical_case_id",
        "tier",
        "capability_weight",
        "fixture",
        "public_identity",
        "model_requirement",
        "freshness",
        "audits",
        "selector",
        "execution_backend",
        "source_case_id",
        "semantic_motif",
        "migration_reason",
        "compatibility_aliases",
    }
    if set(row) != required_keys:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"logical_cases[{index}] keys must exactly equal {sorted(required_keys)}",
        )
    logical_case_id = _expect_string(
        row["logical_case_id"], label=f"logical_cases[{index}].logical_case_id"
    )
    if not CASE_ID_RE.fullmatch(logical_case_id):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid logical case ID: {logical_case_id}"
        )
    tier = _expect_string(row["tier"], label=f"{logical_case_id}.tier")
    if tier not in TIERS:
        raise UnifiedBenchmarkError("invalid_unified_registry", f"invalid tier for {logical_case_id}")
    capability_weight = row["capability_weight"]
    if capability_weight != 0:
        raise UnifiedBenchmarkError(
            "invalid_capability_weight",
            f"regression case {logical_case_id} must have capability_weight 0",
        )
    fixture = row["fixture"]
    if not isinstance(fixture, bool):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"{logical_case_id}.fixture must be boolean"
        )
    public_identity = row["public_identity"]
    if public_identity is not None:
        public_identity = _expect_string(
            public_identity, label=f"{logical_case_id}.public_identity"
        )
        if not public_identity.startswith("ComplexityReduction."):
            raise UnifiedBenchmarkError(
                "invalid_unified_registry",
                f"{logical_case_id}.public_identity is not a public declaration",
            )
    if fixture == (public_identity is not None):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"{logical_case_id} must be exactly one of fixture or public identity",
        )
    model_requirement = _expect_string(
        row["model_requirement"], label=f"{logical_case_id}.model_requirement"
    )
    if model_requirement not in MODEL_REQUIREMENTS:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid model requirement for {logical_case_id}"
        )
    freshness = _expect_string(row["freshness"], label=f"{logical_case_id}.freshness")
    if freshness not in FRESHNESS_POLICIES:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid freshness for {logical_case_id}"
        )
    audits = _expect_string_list(row["audits"], label=f"{logical_case_id}.audits")
    selector = _expect_string(row["selector"], label=f"{logical_case_id}.selector")
    if selector not in CASE_SELECTORS:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid selector for {logical_case_id}"
        )
    execution_backend = _expect_string(
        row["execution_backend"], label=f"{logical_case_id}.execution_backend"
    )
    if execution_backend not in EXECUTION_BACKENDS:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid backend for {logical_case_id}"
        )
    if execution_backend == "release_real_round" and selector != "production":
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", "release real-round cases must use production"
        )
    if selector == "contract" and (tier != "R0" or model_requirement != "forbidden"):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"contract case {logical_case_id} must be R0 and model-forbidden",
        )
    source_case_id = _expect_string(
        row["source_case_id"], label=f"{logical_case_id}.source_case_id"
    )
    if not CASE_ID_RE.fullmatch(source_case_id):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry", f"invalid source case ID: {source_case_id}"
        )
    semantic_motif = _expect_string(
        row["semantic_motif"], label=f"{logical_case_id}.semantic_motif"
    )
    migration_reason = _expect_string(
        row["migration_reason"], label=f"{logical_case_id}.migration_reason"
    )
    raw_aliases = row["compatibility_aliases"]
    if not isinstance(raw_aliases, list):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"{logical_case_id}.compatibility_aliases must be a list",
        )
    aliases: list[CompatibilityAlias] = []
    for alias_index, raw_alias in enumerate(raw_aliases):
        alias = _expect_object(
            raw_alias, label=f"{logical_case_id}.compatibility_aliases[{alias_index}]"
        )
        if set(alias) != {"view", "case_id"}:
            raise UnifiedBenchmarkError(
                "invalid_unified_registry", f"invalid alias fields for {logical_case_id}"
            )
        view = _expect_string(alias["view"], label=f"{logical_case_id}.alias.view")
        case_id = _expect_string(
            alias["case_id"], label=f"{logical_case_id}.alias.case_id"
        )
        if view not in COMPATIBILITY_VIEWS:
            raise UnifiedBenchmarkError("invalid_unified_registry", f"unknown view {view}")
        aliases.append(CompatibilityAlias(view=view, case_id=case_id))
    expected_view = {
        "legacy_main45": "legacy-regression-45",
        "release_real_round": "legacy-release-reliability-12",
    }.get(execution_backend)
    if expected_view is not None:
        if not any(
            alias.view == expected_view and alias.case_id == source_case_id
            for alias in aliases
        ):
            raise UnifiedBenchmarkError(
                "invalid_unified_registry",
                f"{logical_case_id} lacks its executable compatibility alias",
            )
    elif aliases:
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"native unified case {logical_case_id} must not invent a compatibility alias",
        )
    if execution_backend == "public_existing_route" and not (
        selector == "production"
        and tier == "R1"
        and fixture is False
        and public_identity is not None
        and model_requirement == "forbidden"
        and freshness == "fresh_production_job"
    ):
        raise UnifiedBenchmarkError(
            "invalid_unified_registry",
            f"public coverage case {logical_case_id} violates the R1 production contract",
        )
    return UnifiedLogicalCase(
        logical_case_id=logical_case_id,
        tier=tier,
        capability_weight=capability_weight,
        fixture=fixture,
        public_identity=public_identity,
        model_requirement=model_requirement,
        freshness=freshness,
        audits=audits,
        selector=selector,
        execution_backend=execution_backend,
        source_case_id=source_case_id,
        semantic_motif=semantic_motif,
        migration_reason=migration_reason,
        compatibility_aliases=tuple(aliases),
    )


def load_unified_registry(path: Path, *, root: Path | None = None) -> UnifiedRegistry:
    """Load the single stable registry and verify both compatibility views."""

    registry_path = path.resolve()
    value = _read_json(registry_path, code="unified_registry_not_found")
    if value.get("schema_version") != UNIFIED_REGISTRY_SCHEMA_V1:
        raise UnifiedBenchmarkError("unsupported_unified_registry", str(value.get("schema_version")))
    if set(value) != {
        "schema_version",
        "benchmark_id",
        "default_jobs",
        "selectors",
        "compatibility_views",
        "logical_cases",
    }:
        raise UnifiedBenchmarkError("invalid_unified_registry", "unexpected top-level fields")
    if value.get("benchmark_id") != UNIFIED_BENCHMARK_ID:
        raise UnifiedBenchmarkError("invalid_unified_registry", "benchmark_id drifted")
    default_jobs = value.get("default_jobs")
    if isinstance(default_jobs, bool) or not isinstance(default_jobs, int) or not 1 <= default_jobs <= 4:
        raise UnifiedBenchmarkError("invalid_unified_registry", "default_jobs must be in 1..4")
    selectors = _expect_object(value.get("selectors"), label="selectors")
    if set(selectors) != SELECTORS:
        raise UnifiedBenchmarkError("invalid_unified_registry", "selector vocabulary drifted")
    compatibility_views = _expect_object(
        value.get("compatibility_views"), label="compatibility_views"
    )
    if set(compatibility_views) != set(COMPATIBILITY_VIEWS):
        raise UnifiedBenchmarkError("invalid_unified_registry", "compatibility views drifted")
    raw_cases = value.get("logical_cases")
    if not isinstance(raw_cases, list) or not raw_cases:
        raise UnifiedBenchmarkError("invalid_unified_registry", "logical_cases must be non-empty")
    cases = tuple(_parse_case(row, index=index) for index, row in enumerate(raw_cases))
    logical_ids = [case.logical_case_id for case in cases]
    if len(set(logical_ids)) != len(logical_ids):
        raise UnifiedBenchmarkError("duplicate_logical_case", "logical case IDs must be unique")
    alias_keys = [
        (alias.view, alias.case_id)
        for case in cases
        for alias in case.compatibility_aliases
    ]
    if len(set(alias_keys)) != len(alias_keys):
        raise UnifiedBenchmarkError("duplicate_compatibility_alias", "compatibility alias repeated")
    source_keys = [(case.execution_backend, case.source_case_id) for case in cases]
    if len(set(source_keys)) != len(source_keys):
        raise UnifiedBenchmarkError(
            "duplicate_execution_source", "an executable source case is registered twice"
        )
    for view, (_, expected_count) in COMPATIBILITY_VIEWS.items():
        declared = _expect_object(compatibility_views[view], label=view)
        if declared.get("case_count") != expected_count:
            raise UnifiedBenchmarkError("invalid_unified_registry", f"{view} count drifted")
        actual = sum(alias.view == view for case in cases for alias in case.compatibility_aliases)
        if actual != expected_count:
            raise UnifiedBenchmarkError(
                "compatibility_view_incomplete", f"{view}: expected {expected_count}, found {actual}"
            )
    registry = UnifiedRegistry(
        benchmark_id=UNIFIED_BENCHMARK_ID,
        registry_path=registry_path,
        default_jobs=default_jobs,
        cases=cases,
    )
    if root is not None:
        validate_registry_against_sources(root=root, registry=registry)
    return registry


def load_public_r1_coverage_suite(path: Path) -> tuple[dict[str, str], ...]:
    """Load the frozen, answer-free ten-case public R1 coverage suite."""

    value = _read_json(path.resolve(), code="public_r1_coverage_suite_not_found")
    schema_version = value.get("schema_version")
    if schema_version not in {
        PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V1,
        PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V2,
    }:
        raise UnifiedBenchmarkError(
            "unsupported_public_r1_coverage_suite", str(schema_version)
        )
    if set(value) != {"schema_version", "suite_id", "cases"}:
        raise UnifiedBenchmarkError(
            "oracle_field_in_public_suite",
            "public R1 coverage suite contains non-input top-level fields",
        )
    expected_suite_id = (
        PUBLIC_R1_COVERAGE_SUITE_ID
        if schema_version == PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V1
        else PUBLIC_R1_COVERAGE_SUITE_ID_V2
    )
    if value.get("suite_id") != expected_suite_id:
        raise UnifiedBenchmarkError(
            "invalid_public_r1_coverage_suite", "suite_id drifted"
        )
    raw_cases = value.get("cases")
    if not isinstance(raw_cases, list) or len(raw_cases) != 10:
        raise UnifiedBenchmarkError(
            "invalid_public_r1_coverage_suite", "suite must contain exactly 10 cases"
        )
    allowed_fields = {"case_id", "module", "problem", "family"}
    if schema_version == PUBLIC_R1_COVERAGE_SUITE_SCHEMA_V2:
        allowed_fields = allowed_fields | {"budget_profile"}
    cases: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    seen_problems: set[str] = set()
    for index, raw_case in enumerate(raw_cases):
        case = _expect_object(raw_case, label=f"public_r1.cases[{index}]")
        if set(case) != allowed_fields:
            raise UnifiedBenchmarkError(
                "oracle_field_in_public_suite",
                f"public R1 case {index} fields must exactly equal {sorted(allowed_fields)}",
            )
        normalized = {
            field: _expect_string(case[field], label=f"public_r1.cases[{index}].{field}")
            for field in sorted(allowed_fields)
        }
        if not CASE_ID_RE.fullmatch(normalized["case_id"]):
            raise UnifiedBenchmarkError(
                "invalid_public_r1_coverage_suite",
                f"invalid case ID {normalized['case_id']}",
            )
        if not normalized["module"].startswith("ComplexityReduction.") or not normalized[
            "problem"
        ].startswith("ComplexityReduction."):
            raise UnifiedBenchmarkError(
                "fixture_in_public_r1_coverage",
                f"{normalized['case_id']} is not a public ComplexityReduction identity",
            )
        if normalized["case_id"] in seen_ids or normalized["problem"] in seen_problems:
            raise UnifiedBenchmarkError(
                "duplicate_public_r1_identity", normalized["case_id"]
            )
        seen_ids.add(normalized["case_id"])
        seen_problems.add(normalized["problem"])
        cases.append(normalized)
    return tuple(cases)


def validate_registry_against_sources(*, root: Path, registry: UnifiedRegistry) -> None:
    """Reject drift between compatibility aliases and their historical manifests."""

    root = root.resolve()
    main_manifest = load_benchmark_manifest(root / "Gate/MANIFEST.json")
    main_selection = select_benchmark_cases(main_manifest, agent_phase=7)
    main_ids = {case.id for case in main_selection.runnable}
    release_suite = load_np_hard_generalization_suite(
        root / "Gate/Suites/np_hard_generalization.json", root=root
    )
    release_ids = {case.id for case in release_suite.cases}
    public_suite = load_public_r1_coverage_suite(
        root / "Gate/Suites/np_hard_public_r1_coverage_v1.json"
    )
    public_ids = {case["case_id"] for case in public_suite}
    registry_main = {
        alias.case_id
        for case in registry.cases
        for alias in case.compatibility_aliases
        if alias.view == "legacy-regression-45"
    }
    registry_release = {
        alias.case_id
        for case in registry.cases
        for alias in case.compatibility_aliases
        if alias.view == "legacy-release-reliability-12"
    }
    registry_public = {
        case.source_case_id
        for case in registry.cases
        if case.execution_backend == "public_existing_route"
    }
    if registry_main != main_ids:
        raise UnifiedBenchmarkError(
            "legacy_regression_alias_drift",
            f"missing={sorted(main_ids - registry_main)}, extra={sorted(registry_main - main_ids)}",
        )
    if registry_release != release_ids:
        raise UnifiedBenchmarkError(
            "legacy_release_alias_drift",
            f"missing={sorted(release_ids - registry_release)}, extra={sorted(registry_release - release_ids)}",
        )
    if registry_public != public_ids:
        raise UnifiedBenchmarkError(
            "public_r1_registry_drift",
            f"missing={sorted(public_ids - registry_public)}, extra={sorted(registry_public - public_ids)}",
        )
    suite_by_id = {case["case_id"]: case for case in public_suite}
    for case in registry.cases:
        if case.execution_backend != "public_existing_route":
            continue
        suite_case = suite_by_id[case.source_case_id]
        if case.public_identity != suite_case["problem"]:
            raise UnifiedBenchmarkError(
                "public_r1_registry_drift",
                f"{case.source_case_id} public identity drifted",
            )


def discover_suite_case_inventory(root: Path) -> dict[str, tuple[str, ...]]:
    """Return every explicit case ID from every JSON asset in ``Suites``."""

    root = root.resolve()
    inventory: dict[str, tuple[str, ...]] = {}
    for suite_path in sorted(list((root / "Benchmark/Hardness/Suites").glob("*.json")) + list((root / "Gate/Suites").glob("*.json"))):
        value = _read_json(suite_path, code="benchmark_suite_not_found")
        raw_cases = value.get("cases", [])
        if not isinstance(raw_cases, list):
            raise UnifiedBenchmarkError(
                "invalid_benchmark_taxonomy", f"{suite_path} cases must be a list"
            )
        case_ids: list[str] = []
        for index, raw_case in enumerate(raw_cases):
            case = _expect_object(raw_case, label=f"{suite_path}.cases[{index}]")
            case_id = case.get("case_id", case.get("id"))
            case_ids.append(
                _expect_string(case_id, label=f"{suite_path}.cases[{index}].case_id")
            )
        if len(set(case_ids)) != len(case_ids):
            raise UnifiedBenchmarkError(
                "invalid_benchmark_taxonomy", f"{suite_path} repeats a case ID"
            )
        relative = str(suite_path.resolve().relative_to(root))
        inventory[relative] = tuple(case_ids)
    return inventory


def _expected_public_identity_ownership(root: Path) -> dict[str, tuple[str, str, str]]:
    suite_tiers = {
        "Gate/Suites/np_hard_capability_dev_v1.json": "C0",
        "Gate/Suites/np_hard_capability_validation_v1.json": "C0",
        "Gate/Suites/np_hard_capability_heldout_v1.json": "C0",
        "Gate/Suites/np_hard_capability_frontier_v1.json": "F0",
        "Gate/Suites/np_hard_public_r1_coverage_v1.json": "R1",
    }
    expected: dict[str, tuple[str, str, str]] = {}
    seen_identities: set[str] = set()
    for relative, tier in suite_tiers.items():
        suite = _read_json(root / relative, code="benchmark_suite_not_found")
        for raw_case in suite.get("cases", []):
            case = _expect_object(raw_case, label=f"{relative}.cases[]")
            case_id = _expect_string(
                case.get("case_id", case.get("id")), label=f"{relative}.case_id"
            )
            identity = _expect_string(case.get("problem"), label=f"{relative}.problem")
            if case_id in expected or identity in seen_identities:
                raise UnifiedBenchmarkError(
                    "duplicate_public_identity_ownership", case_id
                )
            expected[case_id] = (relative, tier, identity)
            seen_identities.add(identity)
    if len(expected) != 44:
        raise UnifiedBenchmarkError(
            "public_identity_ownership_incomplete", f"expected 44, found {len(expected)}"
        )
    return expected


def load_unified_taxonomy(
    path: Path, *, registry: UnifiedRegistry, root: Path | None = None
) -> dict[str, Any]:
    """Load migrations and prove full suite/case and 44-identity coverage."""

    taxonomy_path = path.resolve()
    value = _read_json(taxonomy_path, code="benchmark_taxonomy_not_found")
    if value.get("schema_version") != UNIFIED_TAXONOMY_SCHEMA_V1:
        raise UnifiedBenchmarkError("unsupported_benchmark_taxonomy", str(value.get("schema_version")))
    if value.get("benchmark_id") != registry.benchmark_id:
        raise UnifiedBenchmarkError("invalid_benchmark_taxonomy", "benchmark_id drifted")
    migrations = value.get("case_migrations")
    if not isinstance(migrations, list):
        raise UnifiedBenchmarkError("invalid_benchmark_taxonomy", "case_migrations must be a list")
    expected = {
        (alias.view, alias.case_id): (case.logical_case_id, case.tier)
        for case in registry.cases
        for alias in case.compatibility_aliases
    }
    actual: dict[tuple[str, str], tuple[str, str]] = {}
    for row in migrations:
        migration = _expect_object(row, label="case_migrations[]")
        key = (str(migration.get("compatibility_view")), str(migration.get("case_id")))
        if key in actual:
            raise UnifiedBenchmarkError("invalid_benchmark_taxonomy", f"duplicate migration {key}")
        if migration.get("capability_weight") != 0:
            raise UnifiedBenchmarkError("invalid_capability_weight", f"taxonomy case {key}")
        actual[key] = (str(migration.get("logical_case_id")), str(migration.get("tier")))
    if actual != expected:
        raise UnifiedBenchmarkError("invalid_benchmark_taxonomy", "taxonomy and registry differ")
    if root is None:
        root = taxonomy_path.parents[2]
    root = root.resolve()
    expected_suites = discover_suite_case_inventory(root)
    raw_inventory = value.get("suite_inventory")
    if not isinstance(raw_inventory, list):
        raise UnifiedBenchmarkError(
            "invalid_benchmark_taxonomy", "suite_inventory must be a list"
        )
    actual_suites: dict[str, tuple[str, ...]] = {}
    taxonomy_cases: dict[tuple[str, str], dict[str, Any]] = {}
    allowed_tiers = {*TIERS, "C0", "F0"}
    for raw_suite in raw_inventory:
        suite = _expect_object(raw_suite, label="suite_inventory[]")
        suite_file = _expect_string(suite.get("suite_file"), label="suite_file")
        if suite_file in actual_suites:
            raise UnifiedBenchmarkError(
                "invalid_benchmark_taxonomy", f"duplicate suite inventory {suite_file}"
            )
        raw_cases = suite.get("cases")
        if not isinstance(raw_cases, list):
            raise UnifiedBenchmarkError(
                "invalid_benchmark_taxonomy", f"{suite_file}.cases must be a list"
            )
        ids: list[str] = []
        for raw_case in raw_cases:
            case = _expect_object(raw_case, label=f"{suite_file}.cases[]")
            case_id = _expect_string(case.get("case_id"), label=f"{suite_file}.case_id")
            tier = _expect_string(case.get("tier"), label=f"{suite_file}.{case_id}.tier")
            if tier not in allowed_tiers:
                raise UnifiedBenchmarkError(
                    "invalid_benchmark_taxonomy", f"invalid tier for {suite_file}:{case_id}"
                )
            fixture = case.get("fixture")
            public_problem = case.get("public_problem")
            scored = case.get("capability_scored")
            weight = case.get("capability_weight")
            if not all(isinstance(flag, bool) for flag in (fixture, public_problem, scored)):
                raise UnifiedBenchmarkError(
                    "invalid_benchmark_taxonomy", f"invalid flags for {suite_file}:{case_id}"
                )
            if isinstance(weight, bool) or not isinstance(weight, int) or weight not in {0, 1}:
                raise UnifiedBenchmarkError(
                    "invalid_capability_weight", f"taxonomy case {suite_file}:{case_id}"
                )
            if scored != (weight == 1) or (scored and (fixture or not public_problem or tier != "C0")):
                raise UnifiedBenchmarkError(
                    "invalid_capability_weight", f"taxonomy case {suite_file}:{case_id}"
                )
            _expect_string(case.get("purpose"), label=f"{suite_file}.{case_id}.purpose")
            _expect_string(
                case.get("migration_reason"),
                label=f"{suite_file}.{case_id}.migration_reason",
            )
            ids.append(case_id)
            taxonomy_cases[(suite_file, case_id)] = case
        actual_suites[suite_file] = tuple(ids)
    if actual_suites != expected_suites:
        raise UnifiedBenchmarkError(
            "suite_taxonomy_incomplete", "taxonomy does not exactly cover Suites/*.json"
        )
    expected_ownership = _expected_public_identity_ownership(root)
    raw_ownership = value.get("public_identity_ownership")
    if not isinstance(raw_ownership, list):
        raise UnifiedBenchmarkError(
            "invalid_benchmark_taxonomy", "public_identity_ownership must be a list"
        )
    actual_ownership: dict[str, tuple[str, str, str]] = {}
    for raw_owner in raw_ownership:
        owner = _expect_object(raw_owner, label="public_identity_ownership[]")
        case_id = _expect_string(owner.get("case_id"), label="ownership.case_id")
        actual_ownership[case_id] = (
            _expect_string(owner.get("suite_file"), label="ownership.suite_file"),
            _expect_string(owner.get("tier"), label="ownership.tier"),
            _expect_string(owner.get("public_identity"), label="ownership.public_identity"),
        )
    if actual_ownership != expected_ownership:
        raise UnifiedBenchmarkError(
            "public_identity_ownership_incomplete",
            "expected the frozen 32 C0 + 2 F0 + 10 R1 identity partition",
        )
    for case_id, (suite_file, tier, _) in actual_ownership.items():
        taxonomy_case = taxonomy_cases.get((suite_file, case_id))
        if taxonomy_case is None or taxonomy_case["tier"] != tier:
            raise UnifiedBenchmarkError(
                "public_identity_ownership_incomplete", case_id
            )
    return value


def select_unified_cases(
    registry: UnifiedRegistry, *, selector: str
) -> tuple[UnifiedLogicalCase, ...]:
    """Select and de-duplicate logical cases, with production winning in ``all``."""

    if selector not in SELECTORS:
        raise UnifiedBenchmarkError("unknown_unified_selector", selector)
    candidates = (
        registry.cases
        if selector == "all"
        else tuple(case for case in registry.cases if case.selector == selector)
    )
    selected: dict[str, UnifiedLogicalCase] = {}
    for case in candidates:
        previous = selected.get(case.logical_case_id)
        if previous is None or (previous.selector == "contract" and case.selector == "production"):
            selected[case.logical_case_id] = case
    return tuple(selected[case_id] for case_id in sorted(selected))


def require_formal_profile(config: DeepSeekConfig, *, require_api_key: bool) -> None:
    if not is_formal_np_hard_qualification_config(config):
        raise UnifiedBenchmarkError(
            "qualification_model_profile_mismatch",
            "unified production requires official deepseek-v4-flash/low/0/16000/300s/retries0",
        )
    if require_api_key and not config.api_key:
        raise UnifiedBenchmarkError(
            "model_provider_unavailable", "production selector requires DEEPSEEK_API_KEY"
        )


def _formal_subprocess_environment(config: DeepSeekConfig) -> dict[str, str]:
    environment = dict(os.environ)
    environment.update(
        {
            "DEEPSEEK_BASE_URL": FORMAL_BASE_URL,
            "DEEPSEEK_MODEL": FORMAL_MODEL,
            "DEEPSEEK_TIMEOUT_SECONDS": str(FORMAL_TIMEOUT_SECONDS),
            "DEEPSEEK_MAX_TOKENS": str(FORMAL_MAX_TOKENS),
            "DEEPSEEK_MAX_RETRIES": str(FORMAL_MAX_RETRIES),
            "DEEPSEEK_REASONING_EFFORT": FORMAL_REASONING_EFFORT,
        }
    )
    if config.api_key:
        environment["DEEPSEEK_API_KEY"] = config.api_key
    else:
        environment.pop("DEEPSEEK_API_KEY", None)
    return environment


def _execute_legacy_cases(
    *,
    root: Path,
    case_ids: tuple[str, ...],
    output_root: Path,
    jobs: int,
    env_file: Path,
    deepseek: DeepSeekConfig,
) -> Mapping[str, Any]:
    command = [
        sys.executable,
        str(root / "scripts/run_hardness_benchmark.py"),
        "--manifest",
        str(root / "Gate/MANIFEST.json"),
        "--agent-phase",
        "7",
        "--planner",
        "deterministic",
        "--jobs",
        str(jobs),
        "--env-file",
        str(env_file),
        "--output-root",
        str(output_root),
    ]
    for case_id in case_ids:
        command.extend(("--case", case_id))
    completed = subprocess.run(
        command,
        cwd=root,
        env=_formal_subprocess_environment(deepseek),
        capture_output=True,
        text=True,
        check=False,
    )
    report_path = output_root / "report.json"
    if not report_path.is_file():
        detail = deepseek.redact((completed.stderr or completed.stdout)[-2000:])
        raise UnifiedBenchmarkError(
            "legacy_contract_runner_failed", detail or f"exit code {completed.returncode}"
        )
    report = _read_json(report_path, code="legacy_contract_report_missing")
    report["process_exit_code"] = completed.returncode
    return report


def _execute_production_round(
    *,
    root: Path,
    output_root: Path,
    report_path: Path,
    suite_path: Path,
    jobs: int,
    deepseek: DeepSeekConfig,
) -> Mapping[str, Any]:
    return run_np_hard_release_real_round(
        root=root,
        suite_path=suite_path,
        output_root=output_root,
        report_path=report_path,
        deepseek=deepseek,
        round_index=1,
        jobs=jobs,
    )


def _execute_public_r1_coverage(
    *,
    root: Path,
    output_root: Path,
    report_path: Path,
    suite_path: Path,
    matrix_path: Path,
    inventory_path: Path,
    jobs: int,
    lean_timeout_seconds: int = 900,
) -> Mapping[str, Any]:
    """Run the ten public R1 identities once through the H-H production audits."""

    cases = load_public_r1_coverage_suite(suite_path)
    matrix = load_np_hard_target_matrix(matrix_path)
    matrix_by_problem = {
        str(row["canonical_declaration"]): dict(row)
        for row in matrix["identities"]
        if row.get("has_forward_certified_reduction_route") is True
    }
    inventory_by_id = _inventory_identities(inventory_path)
    selected: list[tuple[dict[str, str], dict[str, Any]]] = []
    for case in cases:
        row = matrix_by_problem.get(case["problem"])
        if row is None:
            raise UnifiedBenchmarkError(
                "public_r1_identity_not_existing_route", case["case_id"]
            )
        if row.get("canonical_module") != case["module"] or row.get("family") != case["family"]:
            raise UnifiedBenchmarkError(
                "public_r1_identity_matrix_drift", case["case_id"]
            )
        selected.append((case, row))

    _fresh_directory(output_root)
    lock = Lock()
    active = 0
    maximum_active = 0
    started = time.monotonic()

    def qualify(case: dict[str, str], row: dict[str, Any]) -> dict[str, Any]:
        nonlocal active, maximum_active
        with lock:
            active += 1
            maximum_active = max(maximum_active, active)
        try:
            inventory_row = inventory_by_id.get(str(row["identity_id"]))
            if inventory_row is None:
                raise UnifiedBenchmarkError(
                    "public_r1_identity_inventory_drift", case["case_id"]
                )
            result = _qualify_one(
                root=root,
                row=row,
                inventory_row=inventory_row,
                output_root=output_root,
                lean_timeout_seconds=lean_timeout_seconds,
                heldout_ids={case["problem"]: case["case_id"]},
            )
            return {"case_id": case["case_id"], **result}
        finally:
            with lock:
                active -= 1

    rows: list[dict[str, Any]] = []
    if jobs == 1:
        rows = [qualify(case, row) for case, row in selected]
    else:
        with ThreadPoolExecutor(
            max_workers=min(jobs, len(selected)),
            thread_name_prefix="np-hard-public-r1",
        ) as executor:
            pending = {
                executor.submit(qualify, case, row): case["case_id"]
                for case, row in selected
            }
            for future in as_completed(pending):
                rows.append(future.result())
        rows.sort(key=lambda row: row["case_id"])
    parallel = {
        "configured_jobs": jobs,
        "submitted_case_tasks": len(selected),
        "maximum_concurrent_case_tasks": maximum_active,
        "final_active_case_tasks": active,
        "wall_duration_seconds": round(time.monotonic() - started, 6),
        "observed_parallelism": (
            jobs == 1 or len(selected) <= 1 or maximum_active >= min(2, jobs, len(selected))
        ),
    }
    report = {
        "schema_version": "hardness_np_hard_public_r1_coverage_report_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-I-public-existing-route-coverage",
        "passed": all(row["matched"] for row in rows),
        "fresh_output": True,
        "resume": False,
        "metrics": {
            "case_count": len(rows),
            "matched_case_count": sum(row["matched"] for row in rows),
            "model_calls": sum(int(row["model_calls"]) for row in rows),
            "independent_replay_count": sum(
                row["independent_replay"].get("passed") is True for row in rows
            ),
            "standard_axiom_audit_count": sum(
                row["axiom_audit"].get("passed") is True for row in rows
            ),
            "endpoint_equality_audit_count": sum(
                row["endpoint_audit"].get("passed") is True for row in rows
            ),
            "shortest_route_audit_count": sum(
                row["route_audit"].get("passed") is True for row in rows
            ),
        },
        "parallel_execution": parallel,
        "cases": rows,
    }
    report["passed"] = bool(rows) and report["passed"] and report["metrics"] == {
        "case_count": 10,
        "matched_case_count": 10,
        "model_calls": 0,
        "independent_replay_count": 10,
        "standard_axiom_audit_count": 10,
        "endpoint_equality_audit_count": 10,
        "shortest_route_audit_count": 10,
    } and parallel["observed_parallelism"] is True and active == 0
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def _fresh_directory(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise UnifiedBenchmarkError(
            "unified_output_not_fresh", f"output directory must be fresh: {path}"
        )
    path.mkdir(parents=True, exist_ok=True)


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _legacy_result_rows(
    *, report: Mapping[str, Any], cases: Mapping[str, UnifiedLogicalCase]
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for result in report.get("results", []):
        case_id = str(result.get("id"))
        case = cases.get(case_id)
        if case is None:
            raise UnifiedBenchmarkError(
                "unexpected_case_execution", f"legacy runner executed {case_id}"
            )
        if case_id in seen:
            raise UnifiedBenchmarkError("duplicate_case_execution", case_id)
        seen.add(case_id)
        rows.append(
            {
                "logical_case_id": case.logical_case_id,
                "source_case_id": case_id,
                "execution_backend": case.execution_backend,
                "selector": case.selector,
                "tier": case.tier,
                "capability_weight": case.capability_weight,
                "fixture": case.fixture,
                "public_identity": case.public_identity,
                "model_requirement": case.model_requirement,
                "freshness": case.freshness,
                "audits": list(case.audits),
                "status": result.get("actual_status"),
                "failure_code": result.get("actual_failure_code"),
                "matched": result.get("passed") is True,
                "model_calls": int(result.get("model_call_count", 0)),
                "compatibility_aliases": [alias.__dict__ for alias in case.compatibility_aliases],
                "source_report": result.get("report"),
            }
        )
    if seen != set(cases):
        raise UnifiedBenchmarkError(
            "missing_case_execution", f"legacy runner omitted {sorted(set(cases) - seen)}"
        )
    return rows


def _production_result_rows(
    *, report: Mapping[str, Any], cases: Mapping[str, UnifiedLogicalCase]
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for result in report.get("cases", []):
        case_id = str(result.get("case_id"))
        case = cases.get(case_id)
        if case is None:
            raise UnifiedBenchmarkError(
                "unexpected_case_execution", f"production runner executed {case_id}"
            )
        if case_id in seen:
            raise UnifiedBenchmarkError("duplicate_case_execution", case_id)
        seen.add(case_id)
        runtime = result.get("runtime") or {}
        result_payload = result.get("result") or {}
        rows.append(
            {
                "logical_case_id": case.logical_case_id,
                "source_case_id": case_id,
                "execution_backend": case.execution_backend,
                "selector": case.selector,
                "tier": case.tier,
                "capability_weight": case.capability_weight,
                "fixture": case.fixture,
                "public_identity": case.public_identity,
                "model_requirement": case.model_requirement,
                "freshness": case.freshness,
                "audits": list(case.audits),
                "status": result.get("status") or result_payload.get("status") or runtime.get("status"),
                "failure_code": result.get("failure_code") or result_payload.get("failure_code"),
                "matched": result.get("matched") is True,
                "model_calls": int(result.get("model_calls", runtime.get("model_calls", 0))),
                "compatibility_aliases": [alias.__dict__ for alias in case.compatibility_aliases],
                "source_report": report.get("stage"),
            }
        )
    if seen != set(cases):
        raise UnifiedBenchmarkError(
            "missing_case_execution", f"production runner omitted {sorted(set(cases) - seen)}"
        )
    return rows


def _public_r1_result_rows(
    *, report: Mapping[str, Any], cases: Mapping[str, UnifiedLogicalCase]
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for result in report.get("cases", []):
        case_id = str(result.get("case_id"))
        case = cases.get(case_id)
        if case is None:
            raise UnifiedBenchmarkError(
                "unexpected_case_execution", f"public R1 runner executed {case_id}"
            )
        if case_id in seen:
            raise UnifiedBenchmarkError("duplicate_case_execution", case_id)
        seen.add(case_id)
        rows.append(
            {
                "logical_case_id": case.logical_case_id,
                "source_case_id": case_id,
                "execution_backend": case.execution_backend,
                "selector": case.selector,
                "tier": case.tier,
                "capability_weight": case.capability_weight,
                "fixture": case.fixture,
                "public_identity": case.public_identity,
                "model_requirement": case.model_requirement,
                "freshness": case.freshness,
                "audits": list(case.audits),
                "status": result.get("status"),
                "failure_code": result.get("failure_code"),
                "matched": result.get("matched") is True,
                "model_calls": int(result.get("model_calls", 0)),
                "compatibility_aliases": [],
                "source_report": report.get("stage"),
            }
        )
    if seen != set(cases):
        raise UnifiedBenchmarkError(
            "missing_case_execution", f"public R1 runner omitted {sorted(set(cases) - seen)}"
        )
    return rows


def run_unified_benchmark(
    *,
    root: Path,
    registry_path: Path,
    taxonomy_path: Path,
    selector: str,
    output_root: Path,
    report_path: Path,
    env_file: Path,
    deepseek: DeepSeekConfig,
    jobs: int = 4,
    legacy_executor: LegacyExecutor | None = None,
    production_executor: ProductionExecutor | None = None,
    public_coverage_executor: PublicCoverageExecutor | None = None,
) -> dict[str, Any]:
    """Execute one de-duplicated unified R0/R1 selection."""

    root = root.resolve()
    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= 4:
        raise UnifiedBenchmarkError("invalid_unified_jobs", "jobs must be in 1..4")
    registry = load_unified_registry(registry_path, root=root)
    taxonomy = load_unified_taxonomy(taxonomy_path, registry=registry, root=root)
    selected = select_unified_cases(registry, selector=selector)
    requires_model = any(case.model_requirement == "required" for case in selected)
    require_formal_profile(deepseek, require_api_key=requires_model)
    output_root = output_root.resolve()
    _fresh_directory(output_root)

    legacy_cases = {
        case.source_case_id: case
        for case in selected
        if case.execution_backend == "legacy_main45"
    }
    release_cases = {
        case.source_case_id: case
        for case in selected
        if case.execution_backend == "release_real_round"
    }
    public_cases = {
        case.source_case_id: case
        for case in selected
        if case.execution_backend == "public_existing_route"
    }
    rows: list[dict[str, Any]] = []
    legacy_report: Mapping[str, Any] | None = None
    production_report: Mapping[str, Any] | None = None
    public_report: Mapping[str, Any] | None = None
    if legacy_cases:
        execute_legacy = legacy_executor or _execute_legacy_cases
        legacy_report = execute_legacy(
            root=root,
            case_ids=tuple(sorted(legacy_cases)),
            output_root=output_root / "legacy",
            jobs=jobs,
            env_file=env_file.resolve(),
            deepseek=deepseek,
        )
        rows.extend(_legacy_result_rows(report=legacy_report, cases=legacy_cases))
    if release_cases:
        release_suite = root / "Gate/Suites/np_hard_generalization.json"
        expected_release_ids = {
            case.id
            for case in load_np_hard_generalization_suite(release_suite, root=root).cases
        }
        if set(release_cases) != expected_release_ids:
            raise UnifiedBenchmarkError(
                "partial_production_round_forbidden",
                "production backend must execute the complete de-duplicated 12-case round",
            )
        execute_production = production_executor or _execute_production_round
        production_report = execute_production(
            root=root,
            output_root=output_root / "production",
            report_path=output_root / "production-round-report.json",
            suite_path=release_suite,
            jobs=jobs,
            deepseek=deepseek,
        )
        rows.extend(_production_result_rows(report=production_report, cases=release_cases))
    if public_cases:
        public_suite = (
            root / "Gate/Suites/np_hard_public_r1_coverage_v1.json"
        )
        expected_public_ids = {
            case["case_id"] for case in load_public_r1_coverage_suite(public_suite)
        }
        if set(public_cases) != expected_public_ids:
            raise UnifiedBenchmarkError(
                "partial_public_r1_coverage_forbidden",
                "public production backend must execute the complete 10-case coverage lane",
            )
        execute_public = public_coverage_executor or _execute_public_r1_coverage
        public_report = execute_public(
            root=root,
            output_root=output_root / "public-r1",
            report_path=output_root / "public-r1-report.json",
            suite_path=public_suite,
            matrix_path=root / "Gate/NP_HARD_TARGET_MATRIX.json",
            inventory_path=root / "Gate/NP_HARD_H_F_INVENTORY.json",
            jobs=jobs,
        )
        rows.extend(_public_r1_result_rows(report=public_report, cases=public_cases))

    logical_ids = [row["logical_case_id"] for row in rows]
    if len(set(logical_ids)) != len(logical_ids):
        raise UnifiedBenchmarkError(
            "duplicate_logical_case_execution", "one logical case executed more than once"
        )
    if set(logical_ids) != {case.logical_case_id for case in selected}:
        raise UnifiedBenchmarkError("missing_case_execution", "selection and execution differ")
    logical_case_count = len(selected)
    case_execution_count = len(rows)
    if case_execution_count > logical_case_count:
        raise UnifiedBenchmarkError(
            "duplicate_logical_case_execution", "case executions exceed logical case count"
        )

    production_parallel = dict((production_report or {}).get("parallel_execution") or {})
    public_parallel = dict((public_report or {}).get("parallel_execution") or {})
    model_calls = sum(int(row["model_calls"]) for row in rows)
    component_reports_passed = all(
        report is None or report.get("passed") is not False
        for report in (legacy_report, production_report, public_report)
    )
    passed = bool(rows) and all(row["matched"] for row in rows) and component_reports_passed
    report = {
        "schema_version": UNIFIED_REPORT_SCHEMA_V1,
        "benchmark_id": registry.benchmark_id,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "selector": selector,
        "run_valid": True,
        "passed": passed,
        "formal_profile_matched": True,
        "model_configuration": deepseek.to_public_dict(),
        "counts": {
            "logical_cases": logical_case_count,
            "case_executions": case_execution_count,
            "matched_executions": sum(row["matched"] for row in rows),
            "failed_executions": sum(not row["matched"] for row in rows),
            "model_calls": model_calls,
            "fixture_executions": sum(row["fixture"] for row in rows),
            "public_identity_executions": sum(not row["fixture"] for row in rows),
            "capability_weight": sum(row["capability_weight"] for row in rows),
        },
        "compatibility_views": {
            view: sum(
                alias.view == view
                for case in selected
                for alias in case.compatibility_aliases
            )
            for view in COMPATIBILITY_VIEWS
        },
        "tier_counts": {
            tier: sum(case.tier == tier for case in selected) for tier in sorted(TIERS)
        },
        "regression_asset_inventory": {
            str(asset["asset_id"]): dict(asset)
            for asset in taxonomy.get("assets", [])
            if isinstance(asset, dict) and asset.get("asset_id")
        },
        "parallel_execution": {
            "configured_jobs": jobs,
            "components_sequential": True,
            "legacy_configured_jobs": (
                legacy_report.get("jobs") if legacy_report is not None else None
            ),
            "legacy_observed_maximum_concurrency": None,
            "production_configured_jobs": production_parallel.get("configured_jobs"),
            "production_maximum_concurrent_case_tasks": production_parallel.get(
                "maximum_concurrent_case_tasks"
            ),
            "production_final_active_case_tasks": production_parallel.get(
                "final_active_case_tasks", 0
            ),
            "public_r1_configured_jobs": public_parallel.get("configured_jobs"),
            "public_r1_maximum_concurrent_case_tasks": public_parallel.get(
                "maximum_concurrent_case_tasks"
            ),
            "public_r1_final_active_case_tasks": public_parallel.get(
                "final_active_case_tasks", 0
            ),
            "maximum_concurrent_case_tasks": max(
                int(production_parallel.get("maximum_concurrent_case_tasks") or 0),
                int(public_parallel.get("maximum_concurrent_case_tasks") or 0),
            ),
            "final_active_case_tasks": 0,
        },
        "reproducibility": {
            "registry_file": str(registry.registry_path),
            "registry_sha256": sha256_file(registry.registry_path),
            "taxonomy_file": str(taxonomy_path.resolve()),
            "taxonomy_sha256": sha256_file(taxonomy_path.resolve()),
            "legacy_manifest_sha256": sha256_file(root / "Gate/MANIFEST.json"),
            "release_suite_sha256": sha256_file(
                root / "Gate/Suites/np_hard_generalization.json"
            ),
            "public_r1_suite_sha256": sha256_file(
                root / "Gate/Suites/np_hard_public_r1_coverage_v1.json"
            ),
            "taxonomy_asset_count": len(taxonomy.get("assets", [])),
        },
        "component_reports": {
            "legacy": (
                str(output_root / "legacy/report.json") if legacy_report is not None else None
            ),
            "production": (
                str(output_root / "production-round-report.json")
                if production_report is not None
                else None
            ),
            "public_r1": (
                str(output_root / "public-r1-report.json")
                if public_report is not None
                else None
            ),
        },
        "results": sorted(rows, key=lambda row: row["logical_case_id"]),
        "trust_boundary": {
            "capability_weight_zero": all(row["capability_weight"] == 0 for row in rows),
            "production_round_count": 1 if production_report is not None else 0,
            "public_r1_identity_count": len(public_cases),
            "public_r1_zero_model_calls": all(
                row["model_calls"] == 0
                for row in rows
                if row["execution_backend"] == "public_existing_route"
            ),
            "compatibility_views_are_aliases_only": True,
            "logical_case_deduplication": True,
            "formal_model_profile_fail_closed": True,
            "component_reports_passed": component_reports_passed,
        },
    }
    _write_json(report_path.resolve(), report)
    if report_path.resolve() != (output_root / "report.json").resolve():
        _write_json(output_root / "report.json", report)
    return report


def registry_aliases(
    cases: Iterable[UnifiedLogicalCase], *, view: str
) -> tuple[str, ...]:
    """Return sorted compatibility IDs for static inspection and tests."""

    return tuple(
        sorted(
            alias.case_id
            for case in cases
            for alias in case.compatibility_aliases
            if alias.view == view
        )
    )


__all__ = [
    "UNIFIED_BENCHMARK_ID",
    "UNIFIED_REGISTRY_SCHEMA_V1",
    "UNIFIED_REPORT_SCHEMA_V1",
    "UNIFIED_TAXONOMY_SCHEMA_V1",
    "UnifiedBenchmarkError",
    "UnifiedLogicalCase",
    "UnifiedRegistry",
    "discover_suite_case_inventory",
    "load_public_r1_coverage_suite",
    "load_unified_registry",
    "load_unified_taxonomy",
    "registry_aliases",
    "require_formal_profile",
    "run_unified_benchmark",
    "select_unified_cases",
    "validate_registry_against_sources",
]
