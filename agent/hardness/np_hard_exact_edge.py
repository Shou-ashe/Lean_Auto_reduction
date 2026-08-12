"""Exact source-to-target reduction capability benchmark infrastructure.

Public suites are deliberately answer-free.  They freeze only an import
module, exact ``PresentedProblem`` endpoints, a rewritten statement, and a
budget profile.  Scoring policy and archive provenance live in a separate
oracle that is loaded only after the production run has completed.

The production executor reuses :class:`HardnessAgent` with the fixed
``reduce_to`` objective.  The wrapper adds exact endpoint/direction checks,
fresh replay/axiom/dependency evidence collection, a physically restricted
workspace view, parallel case isolation, and report semantics where
``run_valid`` describes protocol validity rather than all-cases success.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterator, Mapping, Sequence

from .authoring import DISABLED_MODE, MODEL_AUTO_MODE, MODEL_REQUIRED_MODE
from .lean_runner import (
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .model_client import DeepSeekClient, DeepSeekConfig
from .models import AgentResult, sha256_id
from .np_hard_exact_edge_authoring import (
    EXACT_EDGE_AUTHORING_TASK_CLASS,
    EXACT_EDGE_RUNTIME_MODULE,
    EXACT_EDGE_STAGED_RESULT_SCHEMA_V1,
    build_typed_exact_edge_task,
    run_exact_edge_staged_construction,
)
from .np_hard_production import is_formal_np_hard_qualification_config
from .runner import HardnessAgent, HardnessAgentConfig


EXACT_EDGE_SUITE_SCHEMA_V1 = "hardness_exact_reduction_edge_input_suite_v1"
EXACT_EDGE_MANIFEST_SCHEMA_V1 = "hardness_exact_reduction_edge_manifest_v1"
EXACT_EDGE_ORACLE_SCHEMA_V1 = "hardness_exact_reduction_edge_oracle_v1"
EXACT_EDGE_MANIFEST_SCHEMA_V2 = "hardness_complexity_reduction_benchmark_v1"
EXACT_EDGE_ORACLE_SCHEMA_V2 = "hardness_complexity_reduction_benchmark_oracle_v1"
EXACT_EDGE_RUN_REPORT_SCHEMA_V1 = "hardness_exact_reduction_edge_run_report_v1"
EXACT_EDGE_CASE_RESULT_SCHEMA_V1 = "hardness_exact_reduction_edge_case_result_v1"
EXACT_EDGE_SCORE_REPORT_SCHEMA_V1 = "hardness_exact_reduction_edge_score_report_v1"
EXACT_EDGE_IDENTITY_SCHEMA_V1 = "hardness_exact_reduction_edge_identity_v1"

PUBLIC_CASE_FIELDS = {
    "case_id",
    "module",
    "source",
    "target",
    "statement",
    "statement_hash",
    "budget_profile",
    "construction_policy",
    "endpoint_contract_version",
}
PUBLIC_SUITE_FIELDS_V1 = {"schema_version", "split", "cases"}
CONSTRUCTION_POLICY_MODE_RECONSTRUCTION = "existing_edge_reconstruction"
CONSTRUCTION_POLICY_MODE_NEW = "direct_new_edge"
CONSTRUCTION_POLICY_MODES = frozenset(
    {
        CONSTRUCTION_POLICY_MODE_RECONSTRUCTION,
        CONSTRUCTION_POLICY_MODE_NEW,
    }
)
CONSTRUCTION_POLICY_FIELDS = {
    "mode",
    "allow_composition",
    "require_new_primitive",
}
EXACT_EDGE_ENDPOINT_CONTRACT_VERSION = "exact-edge-endpoint-v1"
ORACLE_CASE_FIELDS_V1 = {
    "case_id",
    "split",
    "archive_id",
    "canonical_direction",
    "status",
    "allow_composition",
    "require_new_primitive",
    "forbidden_route_imports",
    "required_audits",
    "existing_route",
}
ORACLE_CASE_FIELDS_V2 = ORACLE_CASE_FIELDS_V1 - {"split"}
MANIFEST_FIELDS_V1 = {
    "schema_version",
    "benchmark_id",
    "splits",
    "budget_profiles",
    "execution",
    "scoring",
}
MANIFEST_FIELDS_V2 = {
    "schema_version",
    "benchmark_id",
    "cases",
    "budget_profiles",
    "execution",
    "scoring",
}
MANIFEST_SPLITS = ("dev", "validation", "heldout")
UNGROUPED_BENCHMARK_KEY = "benchmark"
ORACLE_STATUSES = {
    "ready",
    "blocked_endpoint_formalization",
    "quarantined_source_error",
}
SUPPORTED_REQUIRED_AUDITS = {
    "kernel",
    "replay",
    "axiom",
    "endpoint",
    "dependency",
    "program_direct_tm_coherence",
    "semantic_iff",
    "polynomial_bound",
}
SUPPORTED_AUTHORING_MODES = {DISABLED_MODE, MODEL_AUTO_MODE, MODEL_REQUIRED_MODE}
MAX_EXACT_EDGE_CASE_JOBS = 4
DEFAULT_EXACT_EDGE_CASE_JOBS = 4
EXACT_EDGE_CAPABILITY_HEAD = "ComplexityReduction.Certificate.CertifiedReduction"
EXACT_EDGE_CAPABILITY_DECLARATION = (
    "ComplexityReduction.Agent.Hardness.ExactEdge.certifiedReduction"
)

_CASE_ID_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*\Z")
_PROFILE_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*\Z")
_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
_IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")
_ANSWER_HEADING_RE = re.compile(
    r"(?im)^\s*(?:#{1,6}\s*)?(?:solution|answer|hint)\s*:\s*"
)
_FORBIDDEN_PUBLIC_KEYS = {
    "expected",
    "expected_status",
    "gold",
    "gold_route",
    "oracle",
    "solution",
    "hint",
    "route",
    "task_class",
    "gap_nodes",
    "difficulty",
    "difficulty_level",
    "level",
    "status",
    "outcome",
    "archive_id",
    "source_file",
    "provenance",
    "forbidden_route_imports",
    "required_audits",
    "existing_route",
}
_FORBIDDEN_PUBLIC_TEXT = (
    "problems.7z",
    "problems_clean.json",
    "problems/problems.json",
    "active_agent_improvement_plan.md",
    "benchmark/hardness/evaluation/",
    '"solution":',
    '"hint":',
    '"expected_status":',
    '"gold_route":',
    "exact_reduction_edge_oracle",
    "np_hard_capability_oracle",
)
_FORBIDDEN_OUTPUT_TEXT = _FORBIDDEN_PUBLIC_TEXT + (
    "np_hard_capability_oracle",
    "exact_reduction_edge_oracle",
)


class ExactEdgeContractError(ValueError):
    """Stable fail-closed error for exact-edge schema or execution drift."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise ExactEdgeContractError(code, message)


def _tagged_file_sha256(path: Path) -> str:
    return "sha256:" + sha256_file(path)


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        _fail(
            "exact_edge_schema_invalid",
            f"{label} keys drifted; missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}",
        )


def _walk_json(value: Any, *, path: str = "$") -> Iterator[tuple[str, str, Any]]:
    if isinstance(value, Mapping):
        for key, nested in value.items():
            yield path, str(key), nested
            yield from _walk_json(nested, path=f"{path}.{key}")
    elif isinstance(value, list):
        for index, nested in enumerate(value):
            yield from _walk_json(nested, path=f"{path}[{index}]")


def _assert_answer_free(value: Mapping[str, Any]) -> None:
    for path, key, _ in _walk_json(value):
        if key.lower() in _FORBIDDEN_PUBLIC_KEYS:
            _fail(
                "oracle_field_in_public_suite",
                f"answer-bearing field {key!r} appears at {path}",
            )
    serialized = json.dumps(value, ensure_ascii=False, sort_keys=True).lower()
    marker = next((token for token in _FORBIDDEN_PUBLIC_TEXT if token in serialized), None)
    if marker is not None:
        _fail(
            "oracle_field_in_public_suite",
            f"public suite references quarantined material: {marker}",
        )


def _validate_statement(statement: Any) -> str:
    if not isinstance(statement, str) or not statement.strip():
        _fail("exact_edge_schema_invalid", "public edge statement must be non-empty")
    if len(statement) > 20_000:
        _fail("exact_edge_schema_invalid", "public edge statement exceeds 20,000 characters")
    lowered = statement.lower()
    marker = next((token for token in _FORBIDDEN_PUBLIC_TEXT if token in lowered), None)
    if marker is not None or _ANSWER_HEADING_RE.search(statement):
        _fail(
            "archive_solution_in_public_suite",
            "public statement contains an answer heading or quarantined archive reference",
        )
    return statement


@dataclass(frozen=True)
class ExactEdgeConstructionPolicy:
    """Public construction policy required for every exact-edge case.

    This policy is a task requirement, not an answer leak: it must be visible
    before any model call so the runner can reject route reuse, composition,
    and non-new primitives during generation.  Exact forbidden declarations,
    gold route bindings, and scorer mutations stay in the hidden oracle.
    """

    mode: str
    allow_composition: bool
    require_new_primitive: bool

    def to_dict(self) -> dict[str, bool | str]:
        return {
            "mode": self.mode,
            "allow_composition": self.allow_composition,
            "require_new_primitive": self.require_new_primitive,
        }


@dataclass(frozen=True)
class ExactEdgeCase:
    case_id: str
    module: str
    source: str
    target: str
    statement: str
    statement_hash: str
    budget_profile: str
    construction_policy: ExactEdgeConstructionPolicy
    endpoint_contract_version: str
    split: str

    @property
    def edge_id(self) -> str:
        return sha256_id(
            {
                "schema_version": EXACT_EDGE_IDENTITY_SCHEMA_V1,
                "source": self.source,
                "target": self.target,
            }
        )

    def to_public_dict(self) -> dict[str, str | dict[str, bool | str]]:
        return {
            "case_id": self.case_id,
            "module": self.module,
            "source": self.source,
            "target": self.target,
            "statement": self.statement,
            "statement_hash": self.statement_hash,
            "budget_profile": self.budget_profile,
            "construction_policy": self.construction_policy.to_dict(),
            "endpoint_contract_version": self.endpoint_contract_version,
        }


@dataclass(frozen=True)
class ExactEdgeSuite:
    split: str
    cases: tuple[ExactEdgeCase, ...]
    file: Path
    sha256: str

    @property
    def suite_id(self) -> str:
        return sha256_id(
            {
                "schema_version": EXACT_EDGE_SUITE_SCHEMA_V1,
                "split": self.split,
                "case_edge_ids": [case.edge_id for case in self.cases],
                "file_sha256": self.sha256,
            }
        )


@dataclass(frozen=True)
class ExactEdgeBudgetProfile:
    name: str
    authoring_mode: str
    authoring_attempt_budget: int
    lean_timeout_seconds: int


@dataclass(frozen=True)
class ExactEdgeManifest:
    benchmark_id: str
    suites: Mapping[str, ExactEdgeSuite]
    budget_profiles: Mapping[str, ExactEdgeBudgetProfile]
    max_jobs: int
    isolate_workspace: bool
    runtime_prebuilt: bool
    oracle_sha256: str
    file: Path
    sha256: str


@dataclass(frozen=True)
class ExactEdgeOracleCase:
    case_id: str
    split: str
    archive_id: str
    canonical_source: str
    canonical_target: str
    status: str
    allow_composition: bool
    require_new_primitive: bool
    forbidden_route_imports: tuple[str, ...]
    required_audits: tuple[str, ...]
    existing_route: str | None


@dataclass(frozen=True)
class ExactEdgeOracle:
    cases: Mapping[str, ExactEdgeOracleCase]
    file: Path
    sha256: str


def _load_exact_edge_cases(
    raw_cases: Any, *, benchmark_key: str
) -> tuple[ExactEdgeCase, ...]:
    if not isinstance(raw_cases, list) or not raw_cases:
        _fail("exact_edge_schema_invalid", "exact-edge benchmark must contain cases")
    cases: list[ExactEdgeCase] = []
    seen_case_ids: set[str] = set()
    seen_edges: set[str] = set()
    for raw_case in raw_cases:
        if not isinstance(raw_case, dict):
            _fail("exact_edge_schema_invalid", "public exact-edge case must be an object")
        _exact_keys(raw_case, PUBLIC_CASE_FIELDS, label="public exact-edge case")
        case_id = raw_case["case_id"]
        module = raw_case["module"]
        source = raw_case["source"]
        target = raw_case["target"]
        budget_profile = raw_case["budget_profile"]
        if not isinstance(case_id, str) or not _CASE_ID_RE.fullmatch(case_id):
            _fail("exact_edge_schema_invalid", f"invalid exact-edge case ID: {case_id!r}")
        if case_id in seen_case_ids:
            _fail("duplicate_exact_edge_case", f"duplicate case ID: {case_id}")
        if not isinstance(budget_profile, str) or not _PROFILE_RE.fullmatch(budget_profile):
            _fail("exact_edge_schema_invalid", "invalid exact-edge budget profile")
        if not all(isinstance(value, str) for value in (module, source, target)):
            _fail("exact_edge_schema_invalid", "exact-edge endpoint fields must be strings")
        try:
            validate_module_name(module)
            validate_declaration_name(source, label="exact-edge source")
            validate_declaration_name(target, label="exact-edge target")
        except ValueError as error:
            _fail("exact_edge_schema_invalid", str(error))
        if not (
            module.startswith("ComplexityReduction.")
            or module.startswith("Benchmark.Hardness.Inputs.ExactReductionEdgeV1.")
        ):
            _fail("fixture_in_capability_suite", "exact-edge import is outside public scope")
        if not source.startswith("ComplexityReduction.") or not target.startswith(
            "ComplexityReduction."
        ):
            _fail("fixture_in_capability_suite", "exact-edge endpoint is outside public scope")
        if source == target:
            _fail("exact_edge_schema_invalid", "exact-edge source and target are identical")
        statement = _validate_statement(raw_case["statement"])
        statement_hash = raw_case["statement_hash"]
        expected_statement_hash = sha256_id({"statement": statement})
        if (
            not isinstance(statement_hash, str)
            or _HASH_RE.fullmatch(statement_hash) is None
            or statement_hash != expected_statement_hash
        ):
            _fail(
                "exact_edge_schema_invalid",
                "public statement hash does not bind the exact public statement",
            )
        raw_policy = raw_case["construction_policy"]
        if not isinstance(raw_policy, dict):
            _fail("exact_edge_schema_invalid", "construction policy must be an object")
        _exact_keys(raw_policy, CONSTRUCTION_POLICY_FIELDS, label="construction policy")
        mode = raw_policy["mode"]
        allow_composition = raw_policy["allow_composition"]
        require_new_primitive = raw_policy["require_new_primitive"]
        if mode not in CONSTRUCTION_POLICY_MODES:
            _fail("exact_edge_schema_invalid", f"unsupported construction policy mode: {mode!r}")
        if isinstance(allow_composition, bool) is False or isinstance(
            require_new_primitive, bool
        ) is False:
            _fail("exact_edge_schema_invalid", "construction policy booleans are invalid")
        if mode == CONSTRUCTION_POLICY_MODE_NEW and not require_new_primitive:
            _fail(
                "exact_edge_schema_invalid",
                "direct-new-edge policy must require a new primitive",
            )
        if mode == CONSTRUCTION_POLICY_MODE_RECONSTRUCTION and require_new_primitive:
            _fail(
                "exact_edge_schema_invalid",
                "existing-edge reconstruction must not require a new primitive",
            )
        endpoint_contract_version = raw_case["endpoint_contract_version"]
        if endpoint_contract_version != EXACT_EDGE_ENDPOINT_CONTRACT_VERSION:
            _fail(
                "exact_edge_schema_invalid",
                "unsupported exact-edge endpoint contract version",
            )
        case = ExactEdgeCase(
            case_id=case_id,
            module=module,
            source=source,
            target=target,
            statement=statement,
            statement_hash=statement_hash,
            budget_profile=budget_profile,
            construction_policy=ExactEdgeConstructionPolicy(
                mode=mode,
                allow_composition=allow_composition,
                require_new_primitive=require_new_primitive,
            ),
            endpoint_contract_version=endpoint_contract_version,
            split=benchmark_key,
        )
        if case.edge_id in seen_edges:
            _fail("duplicate_canonical_direction", f"suite repeats edge {source} -> {target}")
        seen_case_ids.add(case_id)
        seen_edges.add(case.edge_id)
        cases.append(case)
    return tuple(cases)


def load_exact_edge_suite(path: Path) -> ExactEdgeSuite:
    """Load the legacy split suite used by compatibility runners."""

    resolved = path.resolve()
    raw = json.loads(resolved.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        _fail("exact_edge_schema_invalid", "exact-edge suite must be an object")
    _exact_keys(raw, PUBLIC_SUITE_FIELDS_V1, label="public suite")
    if raw["schema_version"] != EXACT_EDGE_SUITE_SCHEMA_V1:
        _fail("exact_edge_schema_invalid", "unsupported exact-edge suite schema")
    _assert_answer_free(raw)
    split = raw["split"]
    if split not in MANIFEST_SPLITS:
        _fail("exact_edge_schema_invalid", f"unsupported exact-edge split: {split!r}")
    cases = _load_exact_edge_cases(raw["cases"], benchmark_key=split)
    return ExactEdgeSuite(
        split=split,
        cases=cases,
        file=resolved,
        sha256=_tagged_file_sha256(resolved),
    )


def _safe_manifest_relative(base: Path, value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value:
        _fail("exact_edge_manifest_invalid", f"{label} must be a relative path")
    pure = PurePosixPath(value)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        _fail("exact_edge_manifest_invalid", f"unsafe manifest path: {value!r}")
    resolved = (base / pure).resolve()
    try:
        resolved.relative_to(base.resolve())
    except ValueError:
        _fail("exact_edge_manifest_invalid", f"manifest path escaped its root: {value}")
    lowered = value.lower()
    if "evaluation" in lowered or "oracle" in lowered or "gold" in lowered:
        _fail("oracle_field_in_public_suite", "manifest suite path enters scorer-only data")
    return resolved


def _manifest_repository_root(path: Path) -> Path:
    for parent in (path.parent, *path.parents):
        if (parent / "Lean").is_dir() and (parent / "Benchmark/Hardness").is_dir():
            return parent.resolve()
    _fail("exact_edge_manifest_invalid", "manifest is outside an NP-hard repository")


def load_exact_edge_manifest(path: Path) -> ExactEdgeManifest:
    resolved = path.resolve()
    repository_root = _manifest_repository_root(resolved)
    raw = json.loads(resolved.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        _fail("exact_edge_manifest_invalid", "exact-edge manifest must be an object")
    schema_version = raw.get("schema_version")
    if schema_version == EXACT_EDGE_MANIFEST_SCHEMA_V1:
        _exact_keys(raw, MANIFEST_FIELDS_V1, label="exact-edge manifest")
    elif schema_version == EXACT_EDGE_MANIFEST_SCHEMA_V2:
        _exact_keys(raw, MANIFEST_FIELDS_V2, label="complexity-reduction benchmark")
    else:
        _fail("exact_edge_manifest_invalid", "unsupported exact-edge manifest schema")
    _assert_answer_free(raw)
    benchmark_id = raw["benchmark_id"]
    if not isinstance(benchmark_id, str) or not _PROFILE_RE.fullmatch(benchmark_id):
        _fail("exact_edge_manifest_invalid", "invalid exact-edge benchmark ID")
    suites: dict[str, ExactEdgeSuite] = {}
    if schema_version == EXACT_EDGE_MANIFEST_SCHEMA_V2:
        cases = _load_exact_edge_cases(
            raw["cases"], benchmark_key=UNGROUPED_BENCHMARK_KEY
        )
        suites[UNGROUPED_BENCHMARK_KEY] = ExactEdgeSuite(
            split=UNGROUPED_BENCHMARK_KEY,
            cases=cases,
            file=resolved,
            sha256=sha256_id(
                {
                    "schema_version": EXACT_EDGE_MANIFEST_SCHEMA_V2,
                    "cases": [case.to_public_dict() for case in cases],
                }
            ),
        )
    else:
        raw_splits = raw["splits"]
        if not isinstance(raw_splits, dict) or set(raw_splits) != set(MANIFEST_SPLITS):
            _fail("exact_edge_manifest_invalid", "manifest must freeze dev/validation/heldout")
        all_case_ids: set[str] = set()
        all_edge_ids: set[str] = set()
        for split in MANIFEST_SPLITS:
            entry = raw_splits[split]
            if not isinstance(entry, dict):
                _fail("exact_edge_manifest_invalid", "manifest split must be an object")
            _exact_keys(entry, {"suite", "sha256"}, label=f"manifest split {split}")
            expected_hash = entry["sha256"]
            if not isinstance(expected_hash, str) or not _HASH_RE.fullmatch(expected_hash):
                _fail("exact_edge_manifest_invalid", f"invalid suite hash for {split}")
            suite_value = entry["suite"]
            suite_base = (
                repository_root
                if isinstance(suite_value, str)
                and PurePosixPath(suite_value).parts[:1] == ("Benchmark",)
                else resolved.parent
            )
            suite_path = _safe_manifest_relative(suite_base, suite_value, label=split)
            suite = load_exact_edge_suite(suite_path)
            if suite.split != split or suite.sha256 != expected_hash:
                _fail("candidate_dependency_stale", f"manifest binding changed for split {split}")
            case_ids = {case.case_id for case in suite.cases}
            edge_ids = {case.edge_id for case in suite.cases}
            if all_case_ids.intersection(case_ids):
                _fail("duplicate_exact_edge_case", "case ID appears in multiple splits")
            if all_edge_ids.intersection(edge_ids):
                _fail("exact_edge_split_overlap", "canonical direction appears in multiple splits")
            all_case_ids.update(case_ids)
            all_edge_ids.update(edge_ids)
            suites[split] = suite
    raw_profiles = raw["budget_profiles"]
    if not isinstance(raw_profiles, dict) or not raw_profiles:
        _fail("exact_edge_manifest_invalid", "manifest has no budget profiles")
    budget_profiles: dict[str, ExactEdgeBudgetProfile] = {}
    for name, entry in raw_profiles.items():
        if not isinstance(name, str) or not _PROFILE_RE.fullmatch(name):
            _fail("exact_edge_manifest_invalid", "invalid budget profile name")
        if not isinstance(entry, dict):
            _fail("exact_edge_manifest_invalid", "budget profile must be an object")
        _exact_keys(
            entry,
            {"authoring_mode", "authoring_attempt_budget", "lean_timeout_seconds"},
            label=f"budget profile {name}",
        )
        mode = entry["authoring_mode"]
        attempts = entry["authoring_attempt_budget"]
        timeout = entry["lean_timeout_seconds"]
        if mode not in SUPPORTED_AUTHORING_MODES:
            _fail("exact_edge_manifest_invalid", f"unsupported authoring mode: {mode!r}")
        if isinstance(attempts, bool) or not isinstance(attempts, int) or not 1 <= attempts <= 4:
            _fail("exact_edge_manifest_invalid", "authoring attempt budget must be in 1..4")
        if isinstance(timeout, bool) or not isinstance(timeout, int) or timeout <= 0:
            _fail("exact_edge_manifest_invalid", "Lean timeout must be positive")
        budget_profiles[name] = ExactEdgeBudgetProfile(name, mode, attempts, timeout)
    for suite in suites.values():
        unknown = sorted(
            {case.budget_profile for case in suite.cases} - set(budget_profiles)
        )
        if unknown:
            _fail("exact_edge_manifest_invalid", f"unknown budget profiles: {unknown!r}")
    execution = raw["execution"]
    if not isinstance(execution, dict):
        _fail("exact_edge_manifest_invalid", "execution policy must be an object")
    _exact_keys(
        execution,
        {"max_jobs", "isolate_workspace", "runtime_prebuilt"},
        label="exact-edge execution policy",
    )
    jobs = execution["max_jobs"]
    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= MAX_EXACT_EDGE_CASE_JOBS:
        _fail("exact_edge_manifest_invalid", "exact-edge jobs must be in 1..4")
    if not isinstance(execution["isolate_workspace"], bool) or not isinstance(
        execution["runtime_prebuilt"], bool
    ):
        _fail("exact_edge_manifest_invalid", "execution booleans are invalid")
    scoring = raw["scoring"]
    if not isinstance(scoring, dict):
        _fail("exact_edge_manifest_invalid", "scoring binding must be an object")
    _exact_keys(scoring, {"oracle_sha256"}, label="exact-edge scoring binding")
    oracle_sha256 = scoring["oracle_sha256"]
    if not isinstance(oracle_sha256, str) or not _HASH_RE.fullmatch(oracle_sha256):
        _fail(
            "exact_edge_manifest_invalid",
            "scorer oracle must be bound by a tagged SHA-256 digest",
        )
    return ExactEdgeManifest(
        benchmark_id=benchmark_id,
        suites=suites,
        budget_profiles=budget_profiles,
        max_jobs=jobs,
        isolate_workspace=execution["isolate_workspace"],
        runtime_prebuilt=execution["runtime_prebuilt"],
        oracle_sha256=oracle_sha256,
        file=resolved,
        sha256=_tagged_file_sha256(resolved),
    )


def combine_exact_edge_suites(suites: Sequence[ExactEdgeSuite]) -> ExactEdgeSuite:
    materialized = tuple(suites)
    if not materialized:
        _fail("exact_edge_schema_invalid", "at least one exact-edge suite is required")
    cases = tuple(case for suite in materialized for case in suite.cases)
    if len({case.case_id for case in cases}) != len(cases):
        _fail("duplicate_exact_edge_case", "combined suites repeat a case ID")
    if len({case.edge_id for case in cases}) != len(cases):
        _fail("exact_edge_split_overlap", "combined suites repeat a canonical direction")
    combined_hash = sha256_id(
        {"suite_hashes": [suite.sha256 for suite in materialized]}
    )
    return ExactEdgeSuite(
        split="combined",
        cases=cases,
        file=materialized[0].file.parent,
        sha256=combined_hash,
    )


def load_exact_edge_oracle(path: Path) -> ExactEdgeOracle:
    resolved = path.resolve()
    raw = json.loads(resolved.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        _fail("exact_edge_oracle_invalid", "exact-edge oracle must be an object")
    _exact_keys(raw, {"schema_version", "cases"}, label="exact-edge oracle")
    schema_version = raw["schema_version"]
    if schema_version not in {
        EXACT_EDGE_ORACLE_SCHEMA_V1,
        EXACT_EDGE_ORACLE_SCHEMA_V2,
    }:
        _fail("exact_edge_oracle_invalid", "unsupported exact-edge oracle schema")
    raw_cases = raw["cases"]
    if not isinstance(raw_cases, list) or not raw_cases:
        _fail("exact_edge_oracle_invalid", "exact-edge oracle must contain cases")
    cases: dict[str, ExactEdgeOracleCase] = {}
    for raw_case in raw_cases:
        if not isinstance(raw_case, dict):
            _fail("exact_edge_oracle_invalid", "oracle case must be an object")
        expected_fields = (
            ORACLE_CASE_FIELDS_V1
            if schema_version == EXACT_EDGE_ORACLE_SCHEMA_V1
            else ORACLE_CASE_FIELDS_V2
        )
        _exact_keys(raw_case, expected_fields, label="exact-edge oracle case")
        case_id = raw_case["case_id"]
        if not isinstance(case_id, str) or not _CASE_ID_RE.fullmatch(case_id) or case_id in cases:
            _fail("exact_edge_oracle_invalid", "oracle case IDs are invalid or duplicated")
        split = raw_case.get("split", UNGROUPED_BENCHMARK_KEY)
        archive_id = raw_case["archive_id"]
        status = raw_case["status"]
        if split not in {*MANIFEST_SPLITS, UNGROUPED_BENCHMARK_KEY} or not isinstance(
            archive_id, str
        ) or not archive_id:
            _fail("exact_edge_oracle_invalid", "oracle split/archive ID is invalid")
        if status not in ORACLE_STATUSES:
            _fail("exact_edge_oracle_invalid", f"unsupported oracle status: {status!r}")
        direction = raw_case["canonical_direction"]
        if not isinstance(direction, dict):
            _fail("exact_edge_oracle_invalid", "canonical direction must be an object")
        _exact_keys(direction, {"source", "target"}, label="canonical direction")
        source = direction["source"]
        target = direction["target"]
        if not isinstance(source, str) or not isinstance(target, str) or source == target:
            _fail("exact_edge_oracle_invalid", "canonical direction endpoints are invalid")
        try:
            validate_declaration_name(source, label="oracle canonical source")
            validate_declaration_name(target, label="oracle canonical target")
        except ValueError as error:
            _fail("exact_edge_oracle_invalid", str(error))
        forbidden = raw_case["forbidden_route_imports"]
        audits = raw_case["required_audits"]
        if not isinstance(forbidden, list) or not all(
            isinstance(value, str) and value for value in forbidden
        ):
            _fail("exact_edge_oracle_invalid", "forbidden route imports must be strings")
        if len(set(forbidden)) != len(forbidden):
            _fail("exact_edge_oracle_invalid", "forbidden route imports repeat")
        if not isinstance(audits, list) or not audits or not all(
            isinstance(value, str) and value in SUPPORTED_REQUIRED_AUDITS for value in audits
        ):
            _fail("exact_edge_oracle_invalid", "required audit list is invalid")
        if len(set(audits)) != len(audits):
            _fail("exact_edge_oracle_invalid", "required audit list repeats")
        existing_route = raw_case["existing_route"]
        if existing_route is not None:
            if not isinstance(existing_route, str):
                _fail("exact_edge_oracle_invalid", "existing route must be a declaration or null")
            try:
                validate_declaration_name(existing_route, label="oracle existing route")
            except ValueError as error:
                _fail("exact_edge_oracle_invalid", str(error))
        if not isinstance(raw_case["allow_composition"], bool) or not isinstance(
            raw_case["require_new_primitive"], bool
        ):
            _fail("exact_edge_oracle_invalid", "oracle edge policy booleans are invalid")
        cases[case_id] = ExactEdgeOracleCase(
            case_id=case_id,
            split=split,
            archive_id=archive_id,
            canonical_source=source,
            canonical_target=target,
            status=status,
            allow_composition=raw_case["allow_composition"],
            require_new_primitive=raw_case["require_new_primitive"],
            forbidden_route_imports=tuple(forbidden),
            required_audits=tuple(audits),
            existing_route=existing_route,
        )
    return ExactEdgeOracle(cases=cases, file=resolved, sha256=_tagged_file_sha256(resolved))


_QUARANTINED_WORKSPACE_PARTS = {
    "benchmark",
    "gold",
    "goldproofs",
    "oracles",
    "inputs",
    "evaluation",
}


def _clone_or_copy_tree(
    source: Path, destination: Path, *, verify_links: bool = True
) -> None:
    """Create a physically separate tree, using APFS clones when available."""

    destination.parent.mkdir(parents=True, exist_ok=True)
    clone = subprocess.run(
        ["cp", "-cR", str(source), str(destination)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if clone.returncode != 0:
        shutil.copytree(source, destination, symlinks=False)
    if verify_links:
        link_check = subprocess.run(
            ["find", str(destination), "-type", "l", "-print"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if link_check.returncode != 0:
            _fail(
                "exact_edge_workspace_invalid",
                "could not audit the physical workspace copy for symlinks",
            )
        for raw_link in link_check.stdout.splitlines():
            link = Path(raw_link)
            try:
                target = link.resolve(strict=True)
                target.relative_to(destination.resolve())
            except (OSError, ValueError):
                _fail(
                    "exact_edge_workspace_invalid",
                    f"workspace symlink escapes or has no target: {link}",
                )
            temporary = link.with_name(link.name + ".materialized")
            if target.is_file():
                shutil.copy2(target, temporary)
                link.unlink()
                temporary.replace(link)
            elif target.is_dir():
                shutil.copytree(target, temporary, symlinks=False)
                link.unlink()
                temporary.replace(link)
            else:
                _fail(
                    "exact_edge_workspace_invalid",
                    f"unsupported workspace symlink target: {link}",
                )
        residual = subprocess.run(
            ["find", str(destination), "-type", "l", "-print", "-quit"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if residual.returncode != 0 or residual.stdout.strip():
            _fail(
                "exact_edge_workspace_invalid",
                "physical workspace copy retained a symlink after materialization",
            )


def _copy_public_lean_workspace(source_lean: Path, destination_lean: Path) -> None:
    destination_lean.mkdir(parents=True, exist_ok=False)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        source = source_lean / name
        if not source.is_file():
            _fail("exact_edge_workspace_invalid", f"Lean configuration is absent: {source}")
        shutil.copy2(source, destination_lean / name)

    public_source = source_lean / "Reference/ComplexityReduction"
    if not public_source.is_dir():
        _fail("exact_edge_workspace_invalid", "public ComplexityReduction source is absent")
    _clone_or_copy_tree(
        public_source,
        destination_lean / "Reference/ComplexityReduction",
    )

    packages = source_lean / ".lake/packages"
    if not packages.is_dir():
        _fail("exact_edge_workspace_invalid", "third-party Lake packages are absent")
    _clone_or_copy_tree(packages, destination_lean / ".lake/packages")

    # Runtime-prebuilt mode needs only the compiled public library.  Never copy
    # the sibling Benchmark cache, which may contain hidden inputs or oracles.
    public_build = source_lean / ".lake/build/lib/lean/ComplexityReduction"
    if public_build.is_dir():
        _clone_or_copy_tree(
            public_build,
            destination_lean / ".lake/build/lib/lean/ComplexityReduction",
        )


def _workspace_quarantine_violations(workspace: Path) -> list[str]:
    violations: list[str] = []
    repository_markers = {
        "active_agent_improvement_plan.md",
        "problems.7z",
        "problems_clean.json",
    }
    for marker in repository_markers:
        if (workspace / marker).exists() or (workspace / "Lean" / marker).exists():
            violations.append(marker)
    reference = workspace / "Lean/Reference"
    build_root = workspace / "Lean/.lake/build/lib/lean"
    scan_roots = [reference, build_root]
    for path in (
        nested
        for scan_root in scan_roots
        if scan_root.exists()
        for nested in scan_root.rglob("*")
    ):
        lowered_name = path.name.lower()
        if lowered_name in repository_markers:
            violations.append(str(path))
            continue
        # Third-party packages may legitimately contain directories called
        # Archive or Benchmark.  The quarantine applies to project-owned
        # material under the copied Reference root and the local build cache.
        try:
            relative = path.relative_to(reference)
        except ValueError:
            relative = None
        if relative is not None:
            safe_generated_wrapper = relative.parts == ("Benchmark",) or (
                relative.parts[:2] == ("Benchmark", "ExactEdgePublic")
            )
            if not safe_generated_wrapper and any(
                part.lower() in _QUARANTINED_WORKSPACE_PARTS
                for part in relative.parts
            ):
                violations.append(str(path))
            continue
        try:
            build_relative = path.relative_to(build_root)
        except ValueError:
            build_relative = None
        if build_relative is not None and build_relative.parts:
            safe_public_build = build_relative.parts[0] == "ComplexityReduction"
            safe_generated_build = build_relative.parts == ("Benchmark",) or (
                build_relative.parts[:2] == ("Benchmark", "ExactEdgePublic")
            )
            if not (safe_public_build or safe_generated_build):
                violations.append(str(path))
    return violations


@contextmanager
def isolated_exact_edge_workspace(root: Path, *, enabled: bool = True) -> Iterator[Path]:
    """Expose a physical, answer-free Lean workspace to production code."""

    resolved = root.resolve()
    lean_root = resolved / "Lean"
    if not lean_root.is_dir():
        _fail("exact_edge_workspace_invalid", f"Lean workspace is absent: {lean_root}")
    if not enabled:
        yield resolved
        return
    with tempfile.TemporaryDirectory(prefix="np-hard-exact-edge-workspace-") as directory:
        isolated = Path(directory).resolve()
        _copy_public_lean_workspace(lean_root, isolated / "Lean")
        entries = {path.name for path in isolated.iterdir()}
        violations = _workspace_quarantine_violations(isolated)
        if entries != {"Lean"} or violations:
            _fail(
                "exact_edge_workspace_invalid",
                "isolated workspace contains quarantined or extra project material",
            )
        yield isolated


def _fresh_output(path: Path, *, resume: bool = False) -> Path:
    resolved = path.resolve()
    if resolved.exists():
        if not resolved.is_dir() or (not resume and any(resolved.iterdir())):
            _fail("exact_edge_output_not_fresh", f"output directory is not empty: {resolved}")
    resolved.mkdir(parents=True, exist_ok=True)
    return resolved


def _read_command_ok(path: Path) -> bool:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return (
        isinstance(raw, dict)
        and raw.get("exit_code") == 0
        and raw.get("timed_out") is False
    )


def _artifact_path(payload: Mapping[str, Any], case_output: Path) -> Path | None:
    value = payload.get("artifact_file")
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    if not path.is_absolute():
        path = case_output / path
    return path.resolve()


def _within(path: Path, parent: Path) -> bool:
    try:
        path.resolve().relative_to(parent.resolve())
    except ValueError:
        return False
    return True


def _scan_output_security(
    output: Path, *, secret: str | None
) -> dict[str, Any]:
    detected: list[str] = []
    secret_detected = False
    scanned_files = 0
    scanned_bytes = 0
    if not output.is_dir():
        return {
            "scanned_file_count": 0,
            "scanned_bytes": 0,
            "quarantined_material_detected": False,
            "detected_markers": [],
            "secret_detected": False,
            "archive_solution_accessed": False,
        }
    for path in sorted(output.rglob("*")):
        if not path.is_file() or path.suffix.lower() not in {".json", ".txt", ".lean"}:
            continue
        if scanned_bytes >= 16 * 1024 * 1024:
            break
        try:
            data = path.read_bytes()[:512_000]
        except OSError:
            continue
        scanned_files += 1
        scanned_bytes += len(data)
        text = data.decode("utf-8", errors="replace")
        lowered = text.lower()
        for marker in _FORBIDDEN_OUTPUT_TEXT:
            if marker in lowered and marker not in detected:
                detected.append(marker)
        if _ANSWER_HEADING_RE.search(text) and "model/" in path.as_posix().lower():
            detected.append("answer_heading_in_model_material")
        if secret and secret in text:
            secret_detected = True
    return {
        "scanned_file_count": scanned_files,
        "scanned_bytes": scanned_bytes,
        "quarantined_material_detected": bool(detected),
        "detected_markers": sorted(set(detected)),
        "secret_detected": secret_detected,
        "archive_solution_accessed": bool(detected),
    }


def _agent_payload(value: Any) -> dict[str, Any]:
    if isinstance(value, AgentResult):
        return value.to_dict()
    if isinstance(value, Mapping):
        return dict(value)
    _fail("exact_edge_runner_invalid_result", "case executor returned an unsupported result")


def _endpoint_module(declaration: str) -> str:
    module = declaration.rsplit(".", 1)[0]
    validate_module_name(module)
    return module


def _prepare_case_wrapper(
    *,
    workspace_root: Path,
    case_output: Path,
    case: ExactEdgeCase,
    timeout_seconds: int,
) -> tuple[ExactEdgeCase | None, dict[str, Any]]:
    """Generate one answer-free public input module for a case.

    The public statement is stored in the input module itself, so the normal
    production authoring-context builder necessarily includes it before any
    model call.  Missing endpoint modules are a protocol-level boundary result,
    not an infrastructure exception.
    """

    lean_root = workspace_root / "Lean"
    endpoint_modules = tuple(
        dict.fromkeys((_endpoint_module(case.source), _endpoint_module(case.target)))
    )
    missing = [
        module
        for module in endpoint_modules
        if not (lean_root / "Reference" / Path(*module.split("."))).with_suffix(
            ".lean"
        ).is_file()
    ]
    context = {
        "declared_module": case.module,
        "statement_sha256": sha256_id({"statement": case.statement}),
        "statement_hash": case.statement_hash,
        "construction_policy": case.construction_policy.to_dict(),
        "endpoint_contract_version": case.endpoint_contract_version,
        "endpoint_modules": list(endpoint_modules),
        "missing_endpoint_modules": missing,
        "wrapper_module": None,
        "wrapper_file": None,
        "wrapper_evidence_file": None,
        "wrapper_sha256": None,
        "wrapper_compile_ok": False,
    }
    if missing:
        return None, context

    module_suffix = case.edge_id.removeprefix("sha256:")[:24]
    wrapper_module = f"Benchmark.ExactEdgePublic.Case{module_suffix}"
    wrapper_file = (
        lean_root / "Reference" / Path(*wrapper_module.split("."))
    ).with_suffix(".lean")
    wrapper_file.parent.mkdir(parents=True, exist_ok=True)
    statement_literal = json.dumps(case.statement, ensure_ascii=False)
    wrapper_source = (
        "\n".join(f"import {module}" for module in endpoint_modules)
        + "\n\n/-! Answer-free exact-edge production context. -/\n\n"
        + f"namespace Benchmark.ExactEdgePublic.Case{module_suffix}\n\n"
        + f"def publicStatement : String := {statement_literal}\n\n"
        + f"end Benchmark.ExactEdgePublic.Case{module_suffix}\n"
    )
    wrapper_file.write_text(wrapper_source, encoding="utf-8")
    wrapper_evidence = case_output / "public-context/Case.lean"
    wrapper_evidence.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(wrapper_file, wrapper_evidence)
    wrapper_olean = (
        lean_root / ".lake/build/lib/lean" / Path(*wrapper_module.split("."))
    ).with_suffix(".olean")
    wrapper_olean.parent.mkdir(parents=True, exist_ok=True)
    compile_result = run_command(
        ["lake", "env", "lean", "-o", str(wrapper_olean), str(wrapper_file)],
        cwd=lean_root,
        timeout_seconds=timeout_seconds,
    )
    compile_evidence = case_output / "commands/public-wrapper.json"
    _write_json(compile_evidence, compile_result.to_dict())
    context.update(
        {
            "wrapper_module": wrapper_module,
            "wrapper_file": str(wrapper_file.resolve()),
            "wrapper_evidence_file": str(wrapper_evidence.resolve()),
            "wrapper_sha256": _tagged_file_sha256(wrapper_file),
            "wrapper_compile_ok": compile_result.ok and wrapper_olean.is_file(),
            "wrapper_compile_evidence_file": str(compile_evidence.resolve()),
            "wrapper_compile_evidence_sha256": _tagged_file_sha256(compile_evidence),
        }
    )
    if not context["wrapper_compile_ok"]:
        return None, context
    return replace(case, module=wrapper_module), context


def _endpoint_preflight_payload(
    *, case: ExactEdgeCase, context: Mapping[str, Any]
) -> dict[str, Any]:
    missing = context.get("missing_endpoint_modules") or []
    wrapper_failed = not missing and context.get("wrapper_compile_ok") is False
    code = (
        "exact_edge_public_wrapper_invalid"
        if wrapper_failed
        else "exact_edge_endpoint_unavailable"
    )
    evidence = (
        "public answer-free endpoint wrapper failed to compile"
        if wrapper_failed
        else "missing public endpoint modules: " + ", ".join(missing)
    )
    return {
        "schema_version": "hardness_agent_result_v1",
        "status": "BLOCKED",
        "goal": {
            "objective": "reduce_to",
            "source_declaration": case.source,
            "target_declaration": case.target,
        },
        "selected_route": None,
        "authoring_attempts": [],
        "model_calls": [],
        "authored_candidate_declaration": None,
        "authored_route_declaration": None,
        "artifact_file": None,
        "failures": [
            {
                "phase": "public_endpoint_preflight",
                "code": code,
                "retryable": False,
                "evidence": evidence,
            }
        ],
    }


def _execute_with_hardness_agent(
    *,
    workspace_root: Path,
    case: ExactEdgeCase,
    profile: ExactEdgeBudgetProfile,
    case_output: Path,
    deepseek: DeepSeekConfig | None,
    model_client: object | None,
    runtime_prebuilt: bool,
    resume: bool = False,
) -> AgentResult:
    return HardnessAgent(
        HardnessAgentConfig(
            root=workspace_root,
            input_module=case.module,
            source_declaration=case.source,
            target_declaration=case.target,
            objective="reduce_to",
            output_dir=case_output,
            lean_timeout_seconds=profile.lean_timeout_seconds,
            deepseek=deepseek,
            model_client=model_client,
            runtime_prebuilt=runtime_prebuilt,
            authoring_mode=profile.authoring_mode,
            authoring_attempt_budget=profile.authoring_attempt_budget,
            resume=resume,
        )
    ).run()


def _endpoint_public_source_files(case: ExactEdgeCase) -> tuple[str, ...]:
    return tuple(
        dict.fromkeys(
            f"Lean/Reference/{'/'.join(_endpoint_module(declaration).split('.'))}.lean"
            for declaration in (case.source, case.target)
        )
    )


def _execute_exact_edge_staged(
    *,
    workspace_root: Path,
    case: ExactEdgeCase,
    profile: ExactEdgeBudgetProfile,
    case_output: Path,
    deepseek: DeepSeekConfig | None,
    model_client: object | None,
    runtime_prebuilt: bool,
) -> dict[str, Any]:
    """Execute one ``direct_new_edge`` case through the typed multi-node DAG."""

    if case.construction_policy.mode != CONSTRUCTION_POLICY_MODE_NEW:
        _fail(
            "exact_edge_policy_mismatch",
            "staged executor is restricted to direct-new-edge policy",
        )
    task = build_typed_exact_edge_task(
        root=workspace_root,
        input_module=case.module,
        source_declaration=case.source,
        target_declaration=case.target,
        policy=case.construction_policy.to_dict(),
        public_source_files=_endpoint_public_source_files(case),
        attempt_budget=profile.authoring_attempt_budget,
        timeout_seconds=profile.lean_timeout_seconds,
        max_output_tokens=(deepseek.max_tokens if deepseek is not None else 3_000),
    )
    active_model_client = model_client
    model_name: str | None = None
    if active_model_client is None and deepseek is not None and deepseek.api_key:
        active_model_client = DeepSeekClient(deepseek)
        model_name = deepseek.model
    resume_checkpoint = case_output / "checkpoint.json"
    return run_exact_edge_staged_construction(
        workspace_root=workspace_root,
        case_output=case_output,
        task=task,
        policy=case.construction_policy.to_dict(),
        statement=case.statement,
        statement_hash=case.statement_hash,
        model_client=active_model_client,
        model_name=model_name,
        timeout_seconds=profile.lean_timeout_seconds,
        case_id=case.case_id,
        attempt_budget=profile.authoring_attempt_budget,
        resume_checkpoint=(
            resume_checkpoint if resume_checkpoint.is_file() else None
        ),
    )


def _policy_dispatch_executor(
    *,
    workspace_root: Path,
    case: ExactEdgeCase,
    profile: ExactEdgeBudgetProfile,
    case_output: Path,
    deepseek: DeepSeekConfig | None,
    model_client: object | None,
    runtime_prebuilt: bool,
    resume: bool = False,
) -> Any:
    if case.construction_policy.mode == CONSTRUCTION_POLICY_MODE_NEW:
        return _execute_exact_edge_staged(
            workspace_root=workspace_root,
            case=case,
            profile=profile,
            case_output=case_output,
            deepseek=deepseek,
            model_client=model_client,
            runtime_prebuilt=runtime_prebuilt,
        )
    return _execute_with_hardness_agent(
        workspace_root=workspace_root,
        case=case,
        profile=profile,
        case_output=case_output,
        deepseek=deepseek,
        model_client=model_client,
        runtime_prebuilt=runtime_prebuilt,
        resume=resume,
    )


def _case_failure_code(payload: Mapping[str, Any]) -> str | None:
    failures = payload.get("failures")
    if isinstance(failures, list) and failures:
        last = failures[-1]
        if isinstance(last, Mapping) and isinstance(last.get("code"), str):
            return str(last["code"])
    value = payload.get("failure_code")
    return str(value) if isinstance(value, str) and value else None


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _evidence_file(
    value: Any, *, case_output: Path
) -> tuple[Path | None, dict[str, Any]]:
    if not isinstance(value, str) or not value:
        return None, {
            "path": None,
            "exists": False,
            "inside_case": False,
            "sha256": None,
        }
    path = Path(value)
    if not path.is_absolute():
        path = case_output / path
    resolved = path.resolve()
    inside = _within(resolved, case_output)
    exists = resolved.is_file()
    return resolved, {
        "path": str(resolved),
        "exists": exists,
        "inside_case": inside,
        "sha256": _tagged_file_sha256(resolved) if exists and inside else None,
    }


def _model_call_ledger(
    rows: Sequence[Any],
    *,
    case_output: Path,
    case_id: str,
    statement: str,
) -> tuple[list[dict[str, Any]], list[str], bool]:
    safe: list[dict[str, Any]] = []
    issues: list[str] = []
    statement_prompted = False
    for index, raw in enumerate(rows, start=1):
        if not isinstance(raw, Mapping):
            issues.append(f"model_call_{index}:not_an_object")
            continue
        call_number = raw.get("call")
        if call_number != index:
            issues.append(f"model_call_{index}:noncanonical_call_number")
        raw_case_id = raw.get("case_id")
        if raw_case_id is not None and raw_case_id != case_id:
            issues.append(f"model_call_{index}:case_identity_mismatch")
        attempt = raw.get("attempt")
        if attempt is not None and (
            isinstance(attempt, bool) or not isinstance(attempt, int) or attempt <= 0
        ):
            issues.append(f"model_call_{index}:attempt_invalid")
        request_id = raw.get("request_id")
        task_id = raw.get("task_id")
        node_id = raw.get("node_id", raw.get("stage"))
        if raw_case_id is not None:
            expected_request_id = sha256_id(
                {
                    "task_request_id": task_id,
                    "case_id": case_id,
                    "node_id": node_id,
                    "attempt": attempt,
                }
            )
            if request_id != expected_request_id:
                issues.append(f"model_call_{index}:request_identity_mismatch")
        usage = raw.get("usage")
        safe_usage = (
            {
                str(name): value
                for name, value in usage.items()
                if isinstance(name, str)
                and isinstance(value, int)
                and not isinstance(value, bool)
                and value >= 0
            }
            if isinstance(usage, Mapping)
            else None
        )
        if isinstance(usage, Mapping) and any(
            not isinstance(value, (int, Mapping)) or isinstance(value, bool)
            for value in usage.values()
        ):
            issues.append(f"model_call_{index}:invalid_usage")

        prompt_path, prompt_evidence = _evidence_file(
            raw.get("prompt_file"), case_output=case_output
        )
        response_path, response_evidence = _evidence_file(
            raw.get("response_file"), case_output=case_output
        )
        patch_path, patch_evidence = _evidence_file(
            raw.get("patch_file"), case_output=case_output
        )
        called = raw.get("called") is True
        protocol_accepted = raw.get("protocol_accepted") is True
        if called and not (
            prompt_evidence["exists"]
            and prompt_evidence["inside_case"]
            and response_evidence["exists"]
            and response_evidence["inside_case"]
        ):
            issues.append(f"model_call_{index}:missing_prompt_or_response_file")
        if protocol_accepted and not (
            patch_evidence["exists"] and patch_evidence["inside_case"]
        ):
            issues.append(f"model_call_{index}:accepted_patch_file_missing")

        prompt_hash_valid = False
        if prompt_path is not None and prompt_path.is_file() and prompt_evidence["inside_case"]:
            prompt_text = prompt_path.read_text(encoding="utf-8")
            prompt_hash_valid = _sha256_text(prompt_text) == raw.get("prompt_sha256")
            statement_prompted = statement_prompted or statement in prompt_text
        if called and not prompt_hash_valid:
            issues.append(f"model_call_{index}:prompt_hash_mismatch")

        response_hash_valid = False
        response_usage_valid = not called
        if (
            response_path is not None
            and response_path.is_file()
            and response_evidence["inside_case"]
        ):
            try:
                response_payload = json.loads(response_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, json.JSONDecodeError):
                response_payload = None
            if isinstance(response_payload, Mapping) and isinstance(
                response_payload.get("content"), str
            ):
                response_hash_valid = (
                    _sha256_text(str(response_payload["content"]))
                    == raw.get("response_sha256")
                )
                response_usage = response_payload.get("usage")
                response_usage_valid = (
                    response_usage is None and safe_usage is None
                ) or (
                    isinstance(response_usage, Mapping)
                    and {
                        str(name): value
                        for name, value in response_usage.items()
                        if isinstance(name, str)
                        and isinstance(value, int)
                        and not isinstance(value, bool)
                        and value >= 0
                    }
                    == safe_usage
                )
        if called and not response_hash_valid:
            issues.append(f"model_call_{index}:response_hash_mismatch")
        if called and not response_usage_valid:
            issues.append(f"model_call_{index}:response_usage_mismatch")

        patch_hash_valid: bool | None = None
        if protocol_accepted:
            patch_hash_valid = False
            if patch_path is not None and patch_path.is_file() and patch_evidence["inside_case"]:
                try:
                    patch_payload = json.loads(patch_path.read_text(encoding="utf-8"))
                except (OSError, UnicodeError, json.JSONDecodeError):
                    patch_payload = None
                replacement = (
                    patch_payload.get("replacement_body")
                    if isinstance(patch_payload, Mapping)
                    and isinstance(patch_payload.get("replacement_body"), str)
                    else patch_payload.get("replacement")
                    if isinstance(patch_payload, Mapping)
                    else None
                )
                if isinstance(replacement, str):
                    patch_hash_valid = (
                        _sha256_text(replacement) == raw.get("patch_sha256")
                    )
            if not patch_hash_valid:
                issues.append(f"model_call_{index}:patch_hash_mismatch")

        safe.append(
            {
                "call": call_number,
                "request_id": request_id,
                "case_id": raw.get("case_id"),
                "task_id": task_id,
                "node": raw.get("stage"),
                "node_id": node_id,
                "attempt": attempt,
                "editable_file": raw.get("editable_file"),
                "model": raw.get("model"),
                "base_url": raw.get("base_url"),
                "called": called,
                "ok": raw.get("ok") is True,
                "protocol_accepted": protocol_accepted,
                "status_code": raw.get("status_code"),
                "http_attempts": raw.get("http_attempts"),
                "finish_reason": raw.get("finish_reason"),
                "duration_seconds": raw.get("duration_seconds"),
                "prompt_sha256": raw.get("prompt_sha256"),
                "response_sha256": raw.get("response_sha256"),
                "diagnostics_sha256": raw.get("diagnostics_sha256"),
                "patch_sha256": raw.get("patch_sha256"),
                "usage": safe_usage,
                "files": {
                    "prompt": prompt_evidence,
                    "response": response_evidence,
                    "patch": patch_evidence,
                },
                "evidence_valid": (
                    (
                        not called
                        or (
                            prompt_hash_valid
                            and response_hash_valid
                            and response_usage_valid
                        )
                    )
                    and (not protocol_accepted or patch_hash_valid is True)
                ),
            }
        )
    return safe, sorted(set(issues)), statement_prompted


def _authoring_attempt_ledger(
    rows: Any, *, case_output: Path
) -> tuple[list[dict[str, Any]], list[str]]:
    if not isinstance(rows, list):
        return [], ["authoring_attempts:not_a_list"]
    safe: list[dict[str, Any]] = []
    issues: list[str] = []
    for index, raw in enumerate(rows, start=1):
        if not isinstance(raw, Mapping):
            issues.append(f"authoring_attempt_{index}:not_an_object")
            continue
        attempt = raw.get("attempt")
        if attempt != index:
            issues.append(f"authoring_attempt_{index}:noncanonical_number")
        candidate_path, candidate_evidence = _evidence_file(
            raw.get("candidate_file"), case_output=case_output
        )
        expected_candidate_hash = raw.get("candidate_sha256")
        direct_candidate_hash_valid = (
            candidate_path is not None
            and candidate_path.is_file()
            and candidate_evidence["inside_case"]
            and isinstance(expected_candidate_hash, str)
            and expected_candidate_hash
            and sha256_file(candidate_path) == expected_candidate_hash
        )
        stages: list[dict[str, Any]] = []
        stage_paths: list[Path] = []
        stage_hash_validities: list[bool] = []
        raw_stages = raw.get("stage_attempts")
        for stage_index, stage in enumerate(
            raw_stages if isinstance(raw_stages, list) else [], start=1
        ):
            if not isinstance(stage, Mapping):
                issues.append(
                    f"authoring_attempt_{index}:stage_{stage_index}:not_an_object"
                )
                continue
            stage_path, stage_evidence = _evidence_file(
                stage.get("candidate_file"), case_output=case_output
            )
            expected_stage_hash = stage.get("candidate_sha256")
            stage_hash_valid = (
                stage_path is not None
                and stage_path.is_file()
                and stage_evidence["inside_case"]
                and isinstance(expected_stage_hash, str)
                and expected_stage_hash
                and sha256_file(stage_path) == expected_stage_hash
            )
            if not stage_hash_valid:
                issues.append(
                    f"authoring_attempt_{index}:stage_{stage_index}:file_hash_mismatch"
                )
            if stage_path is not None:
                stage_paths.append(stage_path)
            stage_hash_validities.append(stage_hash_valid)
            stages.append(
                {
                    "node": stage.get("stage"),
                    "module": stage.get("module"),
                    "declaration": stage.get("declaration"),
                    "accepted": stage.get("accepted") is True,
                    "source_origin": stage.get("source_origin"),
                    "candidate_sha256": expected_stage_hash,
                    "file": stage_evidence,
                    "file_hash_valid": stage_hash_valid,
                }
            )
        candidate_hash_valid = direct_candidate_hash_valid
        if stages:
            candidate_hash_valid = (
                bool(stage_hash_validities)
                and all(stage_hash_validities)
                and candidate_path is not None
                and bool(stage_paths)
                and candidate_path.resolve() == stage_paths[-1].resolve()
                and isinstance(expected_candidate_hash, str)
                and bool(expected_candidate_hash)
            )
        # Protocol-rejected attempts can have no materialized candidate hash;
        # every other attempt must retain its candidate evidence.
        if raw.get("source_origin") != "model_rejected" and not candidate_hash_valid:
            issues.append(f"authoring_attempt_{index}:candidate_file_hash_mismatch")
        model_numbers = raw.get("model_call_numbers")
        safe.append(
            {
                "attempt": attempt,
                "accepted": raw.get("accepted") is True,
                "source_origin": raw.get("source_origin"),
                "candidate_module": raw.get("candidate_module"),
                "candidate_declaration": raw.get("candidate_declaration"),
                "route_declaration": raw.get("route_declaration"),
                "candidate_sha256": expected_candidate_hash,
                "candidate_file": candidate_evidence,
                "candidate_hash_valid": candidate_hash_valid,
                "model_call_numbers": (
                    list(model_numbers)
                    if isinstance(model_numbers, list)
                    and all(isinstance(value, int) for value in model_numbers)
                    else []
                ),
                "nodes": stages,
            }
        )
    return safe, sorted(set(issues))


def _token_usage(call_rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in call_rows:
        usage = call.get("usage")
        if not isinstance(usage, Mapping):
            continue
        for name, value in usage.items():
            if isinstance(name, str) and isinstance(value, int):
                totals[name] = totals.get(name, 0) + value
    return dict(sorted(totals.items()))


def build_exact_edge_artifact_source(
    *, producer_source: str, source: str, target: str
) -> str:
    """Promote the producer's selected path to the exact accepted capability.

    ``HardnessAgent`` deliberately publishes a ``CertifiedPath`` plus a typed
    protocol result.  Exact-edge qualification has a narrower contract: its
    final kernel object must itself have type ``CertifiedReduction source
    target``.  The producer artifact is therefore inlined and the path is
    projected in a separately compiled job-local file.
    """

    source_declaration = validate_declaration_name(source, label="exact-edge source")
    target_declaration = validate_declaration_name(target, label="exact-edge target")
    if not isinstance(producer_source, str) or not producer_source.strip():
        raise ValueError("exact-edge producer artifact is empty")
    selected_path = (
        "ComplexityReduction.Agent.Hardness.GeneratedArtifact.selectedPath"
    )
    if selected_path not in producer_source:
        raise ValueError("producer artifact does not define the selected CertifiedPath")
    return (
        producer_source.rstrip()
        + f"""

namespace ComplexityReduction.Agent.Hardness.ExactEdge

noncomputable def certifiedReduction :
    ComplexityReduction.Certificate.CertifiedReduction
      {source_declaration}
      {target_declaration} :=
  {selected_path}.toCertifiedReduction

end ComplexityReduction.Agent.Hardness.ExactEdge

assert_standard_axioms {EXACT_EDGE_CAPABILITY_DECLARATION}
"""
    )


def _run_exact_edge_artifact(
    *,
    workspace_root: Path,
    case_output: Path,
    producer_source: str,
    source: str,
    target: str,
    timeout_seconds: int,
) -> tuple[Path, str, dict[str, dict[str, Any]]]:
    exact_path = case_output / "ExactEdge.lean"
    exact_source = build_exact_edge_artifact_source(
        producer_source=producer_source,
        source=source,
        target=target,
    )
    exact_path.write_text(exact_source, encoding="utf-8")
    work_root = case_output / "work"
    environment = {"LEAN_PATH": str(work_root)} if work_root.is_dir() else None
    audit_sources = {
        "kernel": (exact_path, exact_source),
        "replay": (exact_path, exact_source),
        "axiom": (
            case_output / "ExactEdgeAxiomAudit.lean",
            exact_source
            + f"\nassert_standard_axioms {EXACT_EDGE_CAPABILITY_DECLARATION}\n",
        ),
        "program_direct_tm_coherence": (
            case_output / "ExactEdgeProgramCoherenceAudit.lean",
            exact_source
            + "\n#check ComplexityReduction.Certificate.CertifiedReduction."
            + "endpoint_exact_compile_coherence "
            + EXACT_EDGE_CAPABILITY_DECLARATION
            + "\n",
        ),
        "semantic_iff": (
            case_output / "ExactEdgeSemanticIffAudit.lean",
            exact_source + f"\n#check {EXACT_EDGE_CAPABILITY_DECLARATION}.correct\n",
        ),
        "polynomial_bound": (
            case_output / "ExactEdgePolynomialBoundAudit.lean",
            exact_source
            + f"\n#check {EXACT_EDGE_CAPABILITY_DECLARATION}.directTM\n"
            + f"#check {EXACT_EDGE_CAPABILITY_DECLARATION}.compatibilityCost\n",
        ),
    }
    audits: dict[str, dict[str, Any]] = {}
    for name, (audit_path, audit_source) in audit_sources.items():
        if audit_path != exact_path:
            audit_path.write_text(audit_source, encoding="utf-8")
        command = ["lake", "env", "lean", str(audit_path)]
        result = run_command(
            command,
            cwd=workspace_root / "Lean",
            timeout_seconds=timeout_seconds,
            env_overrides=environment,
        )
        evidence_path = case_output / f"commands/exact-edge-{name.replace('_', '-')}.json"
        _write_json(evidence_path, result.to_dict())
        audits[name] = {
            "status": "passed" if result.ok else "failed",
            "ok": result.ok,
            "evidence_file": str(evidence_path.resolve()),
            "evidence_sha256": _tagged_file_sha256(evidence_path),
            "audit_artifact_file": str(audit_path.resolve()),
            "audit_artifact_sha256": _tagged_file_sha256(audit_path),
            "blocker": None if result.ok else "lean_audit_command_failed",
        }
    return exact_path.resolve(), exact_source, audits


def _unsupported_audit(name: str, blocker: str) -> dict[str, Any]:
    return {
        "status": "unsupported",
        "ok": False,
        "evidence_file": None,
        "evidence_sha256": None,
        "audit_artifact_file": None,
        "audit_artifact_sha256": None,
        "blocker": blocker,
        "audit": name,
    }


def _boolean_audit(
    *, name: str, ok: bool, evidence_file: Path | None, blocker: str
) -> dict[str, Any]:
    valid_file = evidence_file is not None and evidence_file.is_file()
    accepted = ok and valid_file
    return {
        "status": "passed" if accepted else "failed",
        "ok": accepted,
        "evidence_file": str(evidence_file.resolve()) if valid_file else None,
        "evidence_sha256": _tagged_file_sha256(evidence_file) if valid_file else None,
        "audit_artifact_file": None,
        "audit_artifact_sha256": None,
        "blocker": None if accepted else blocker,
        "audit": name,
    }


def _audit_staged_case_payload(
    *,
    case: ExactEdgeCase,
    profile: ExactEdgeBudgetProfile,
    payload: Mapping[str, Any],
    case_output: Path,
    workspace_root: Path,
    deepseek: DeepSeekConfig | None,
    producer_payload_file: Path,
    public_context: Mapping[str, Any],
) -> dict[str, Any]:
    """Re-audit one typed exact-edge staged construction result independently."""

    staged_status = payload.get("status")
    if staged_status not in {"VERIFIED", "CHECKPOINTED", "FAILED"}:
        staged_status = "FAILED"
    goal = payload.get("goal") if isinstance(payload.get("goal"), Mapping) else {}
    candidate_source = goal.get("source_declaration")
    candidate_target = goal.get("target_declaration")
    objective = goal.get("objective")
    model_calls = payload.get("model_calls")
    model_call_rows = model_calls if isinstance(model_calls, list) else []
    safe_model_calls, model_ledger_issues, statement_prompted = _model_call_ledger(
        model_call_rows,
        case_output=case_output,
        case_id=case.case_id,
        statement=case.statement,
    )
    attempt_ledger, attempt_ledger_issues = _authoring_attempt_ledger(
        payload.get("authoring_attempts"), case_output=case_output
    )
    model_call_count = sum(call.get("called") is True for call in safe_model_calls)
    http_ok_model_calls = sum(
        call.get("called") is True
        and call.get("ok") is True
        and call.get("status_code") == 200
        for call in safe_model_calls
    )
    authored_declaration = payload.get("authored_candidate_declaration")
    authored_route = payload.get("authored_route_declaration")
    artifact_path = _artifact_path(payload, case_output)
    artifact_inside_job = artifact_path is None or _within(artifact_path, case_output)
    artifact_text = ""
    if artifact_path is not None and artifact_path.is_file() and artifact_inside_job:
        artifact_text = artifact_path.read_text(encoding="utf-8")
    endpoint_exact = (
        objective == "reduce_to"
        and candidate_source == case.source
        and candidate_target == case.target
        and (
            staged_status != "VERIFIED"
            or (
                isinstance(authored_declaration, str)
                and authored_declaration
                and case.source in artifact_text
                and case.target in artifact_text
                and ".authoredForwardReduction" in artifact_text
            )
        )
    )
    audits = payload.get("audits") if isinstance(payload.get("audits"), Mapping) else {}
    required_verified_audits = (
        "kernel",
        "replay",
        "axiom",
        "endpoint",
        "dependency",
        "program_direct_tm_coherence",
        "semantic_iff",
        "polynomial_bound",
    )
    verified_protocol = (
        staged_status == "VERIFIED"
        and endpoint_exact
        and artifact_inside_job
        and all(
            isinstance(audits.get(name), Mapping) and audits[name].get("ok") is True
            for name in required_verified_audits
        )
    )
    status = "VERIFIED" if verified_protocol else staged_status
    if status == "CHECKPOINTED":
        status = "BLOCKED"
    accepted_node_ids = [
        str(item.get("node_id"))
        for item in (payload.get("accepted_nodes") or [])
        if isinstance(item, Mapping)
    ]
    failure_code = payload.get("failure_code")
    original_failure_code = failure_code
    if verified_protocol:
        outcome_class = "new_edge_verified"
        final_failure_code = None
    elif staged_status == "FAILED":
        outcome_class = "failed"
        final_failure_code = failure_code or "exact_edge_staged_authoring_failed"
    else:
        outcome_class = "blocked_exact_edge_authoring_incomplete"
        final_failure_code = failure_code or "exact_edge_staged_incomplete"
    ledger_payload = {
        "schema_version": "hardness_exact_edge_model_ledger_v1",
        "case_id": case.case_id,
        "edge_id": case.edge_id,
        "budget": {
            "profile": profile.name,
            "authoring_mode": profile.authoring_mode,
            "authoring_attempt_budget": profile.authoring_attempt_budget,
            "lean_timeout_seconds": profile.lean_timeout_seconds,
            "attempts_used": len(attempt_ledger),
            "model_calls_used": model_call_count,
            "http_attempts_used": sum(
                int(call.get("http_attempts") or 0)
                for call in safe_model_calls
                if isinstance(call.get("http_attempts"), int)
            ),
        },
        "attempts": attempt_ledger,
        "calls": safe_model_calls,
        "token_usage": _token_usage(safe_model_calls),
        "issues": sorted(set(model_ledger_issues + attempt_ledger_issues)),
    }
    ledger_file = case_output / "exact-edge-model-ledger.json"
    _write_json(ledger_file, ledger_payload)
    security = _scan_output_security(
        case_output, secret=deepseek.api_key if deepseek is not None else None
    )
    security["cross_job_artifact"] = not artifact_inside_job
    security["public_statement_context"] = (
        "not_applicable"
        if model_call_count == 0
        else ("prompted" if statement_prompted else "missing")
    )
    security["public_statement_sha256"] = public_context.get("statement_sha256")
    security["model_ledger_issues"] = ledger_payload["issues"]
    if status == "VERIFIED":
        block = None
    else:
        block = {
            "code": final_failure_code,
            "source": case.source,
            "target": case.target,
            "detail": str(payload.get("failure_message") or final_failure_code),
        }
    return {
        "schema_version": EXACT_EDGE_CASE_RESULT_SCHEMA_V1,
        "case_dir": str(case_output.resolve()),
        "case_id": case.case_id,
        "split": case.split,
        "edge_id": case.edge_id,
        "source": candidate_source,
        "target": candidate_target,
        "status": status,
        "producer_status": staged_status,
        "outcome_class": outcome_class,
        "failure_code": final_failure_code,
        "original_failure_code": original_failure_code,
        "protocol_valid": (
            status == "VERIFIED"
            and verified_protocol
            and not security["quarantined_material_detected"]
            and not security["secret_detected"]
            and not ledger_payload["issues"]
            and (model_call_count == 0 or statement_prompted)
        )
        or (
            status != "VERIFIED"
            and not security["quarantined_material_detected"]
            and not security["secret_detected"]
            and not ledger_payload["issues"]
            and (model_call_count == 0 or statement_prompted)
        ),
        "accepted_capability_head": (
            EXACT_EDGE_CAPABILITY_HEAD if status == "VERIFIED" else None
        ),
        "accepted_capability_declaration": (
            authored_declaration if status == "VERIFIED" else None
        ),
        "authoring_protocol": EXACT_EDGE_AUTHORING_TASK_CLASS,
        "resumed": payload.get("resumed") is True,
        "resumed_node_count": int(payload.get("resumed_node_count") or 0),
        "new_node_count": int(payload.get("new_node_count") or 0),
        "accepted_node_ids": accepted_node_ids,
        "exact_artifact_generated": artifact_path is not None,
        "selected_route_id": None,
        "selected_route_atoms": [],
        "route_atom_count": 0,
        "artifact_imports": list(_IMPORT_RE.findall(artifact_text)),
        "artifact_file": str(artifact_path.resolve()) if artifact_path is not None else None,
        "artifact_sha256": (
            _tagged_file_sha256(artifact_path)
            if artifact_path is not None
            and artifact_path.is_file()
            and artifact_inside_job
            else None
        ),
        "producer_artifact_file": (
            str(artifact_path.resolve()) if artifact_path is not None else None
        ),
        "producer_artifact_sha256": (
            _tagged_file_sha256(artifact_path)
            if artifact_path is not None
            and artifact_path.is_file()
            and artifact_inside_job
            else None
        ),
        "authored_candidate_declaration": (
            authored_declaration if status == "VERIFIED" else None
        ),
        "authored_route_declaration": authored_route,
        "public_context": dict(public_context),
        "budget": {
            "profile": profile.name,
            "authoring_mode": profile.authoring_mode,
            "authoring_attempt_budget": profile.authoring_attempt_budget,
            "lean_timeout_seconds": profile.lean_timeout_seconds,
            "attempts_used": len(attempt_ledger),
            "model_calls_used": model_call_count,
            "http_attempts_used": sum(
                int(call.get("http_attempts") or 0)
                for call in safe_model_calls
                if isinstance(call.get("http_attempts"), int)
            ),
        },
        "authoring_attempt_ledger": attempt_ledger,
        "first_accepted_attempt": next(
            (
                attempt["attempt"]
                for attempt in attempt_ledger
                if attempt.get("accepted") is True
            ),
            None,
        ),
        "model_calls": model_call_count,
        "http_ok_model_calls": http_ok_model_calls,
        "model_call_ledger": safe_model_calls,
        "model_call_ledger_file": str(ledger_file.resolve()),
        "model_call_ledger_sha256": _tagged_file_sha256(ledger_file),
        "model_call_ledger_content_sha256": sha256_id(ledger_payload),
        "token_usage": _token_usage(safe_model_calls),
        "audits": audits,
        "security": security,
        "blocker": block,
        "producer_payload_file": str(producer_payload_file.resolve()),
        "producer_payload_sha256": _tagged_file_sha256(producer_payload_file),
        "raw_result_sha256": _tagged_file_sha256(producer_payload_file),
    }


def _audit_case_payload(
    *,
    case: ExactEdgeCase,
    profile: ExactEdgeBudgetProfile,
    payload: Mapping[str, Any],
    case_output: Path,
    workspace_root: Path,
    deepseek: DeepSeekConfig | None,
    producer_payload_file: Path,
    public_context: Mapping[str, Any],
) -> dict[str, Any]:
    if payload.get("schema_version") == EXACT_EDGE_CASE_RESULT_SCHEMA_V1:
        row = dict(payload)
        row.setdefault("case_id", case.case_id)
        row.setdefault("edge_id", case.edge_id)
        row.setdefault("split", case.split)
        row["case_dir"] = str(case_output.resolve())
        row["producer_payload_file"] = str(producer_payload_file.resolve())
        row["producer_payload_sha256"] = _tagged_file_sha256(producer_payload_file)
        row["public_context"] = dict(public_context)
        return row
    if payload.get("schema_version") == EXACT_EDGE_STAGED_RESULT_SCHEMA_V1:
        return _audit_staged_case_payload(
            case=case,
            profile=profile,
            payload=payload,
            case_output=case_output,
            workspace_root=workspace_root,
            deepseek=deepseek,
            producer_payload_file=producer_payload_file,
            public_context=public_context,
        )
    producer_status = payload.get("status")
    if producer_status not in {"VERIFIED", "BLOCKED", "FAILED"}:
        producer_status = "FAILED"
    goal = payload.get("goal") if isinstance(payload.get("goal"), Mapping) else {}
    candidate_source = goal.get("source_declaration")
    candidate_target = goal.get("target_declaration")
    objective = goal.get("objective")
    selected = payload.get("selected_route")
    selected_route = selected if isinstance(selected, Mapping) else {}
    route_atoms = tuple(
        value
        for value in (selected_route.get("atoms") or [])
        if isinstance(value, str)
    )
    model_calls = payload.get("model_calls")
    model_call_rows = model_calls if isinstance(model_calls, list) else []
    safe_model_calls, model_ledger_issues, statement_prompted = _model_call_ledger(
        model_call_rows,
        case_output=case_output,
        case_id=case.case_id,
        statement=case.statement,
    )
    attempt_ledger, attempt_ledger_issues = _authoring_attempt_ledger(
        payload.get("authoring_attempts"), case_output=case_output
    )
    model_call_count = sum(
        call.get("called") is True for call in safe_model_calls
    )
    authored_declaration = payload.get("authored_candidate_declaration")
    authored_route = payload.get("authored_route_declaration")
    producer_artifact = _artifact_path(payload, case_output)
    producer_artifact_inside_job = producer_artifact is None or _within(
        producer_artifact, case_output
    )
    producer_artifact_text = ""
    if (
        producer_artifact is not None
        and producer_artifact.is_file()
        and producer_artifact_inside_job
    ):
        producer_artifact_text = producer_artifact.read_text(encoding="utf-8")
    endpoint_exact = (
        objective == "reduce_to"
        and candidate_source == case.source
        and candidate_target == case.target
        and (
            producer_status != "VERIFIED"
            or (
                selected_route.get("target_declaration") == case.target
                and case.source in producer_artifact_text
                and case.target in producer_artifact_text
                and ".reduceTo" in producer_artifact_text
            )
        )
    )
    producer_compile = _read_command_ok(case_output / "commands/artifact.json")
    producer_replay = _read_command_ok(
        case_output / "commands/deterministic-replay.json"
    )
    dependency = _read_command_ok(case_output / "commands/registry-revalidation.json")
    exact_artifact: Path | None = None
    exact_artifact_text = ""
    exact_audits: dict[str, dict[str, Any]] = {}
    exact_artifact_error: str | None = None
    if (
        producer_status == "VERIFIED"
        and producer_compile
        and producer_replay
        and endpoint_exact
        and producer_artifact_inside_job
        and producer_artifact_text
    ):
        try:
            (
                exact_artifact,
                exact_artifact_text,
                exact_audits,
            ) = _run_exact_edge_artifact(
                workspace_root=workspace_root,
                case_output=case_output,
                producer_source=producer_artifact_text,
                source=case.source,
                target=case.target,
                timeout_seconds=profile.lean_timeout_seconds,
            )
        except (OSError, UnicodeError, ValueError) as error:
            exact_artifact_error = f"{type(error).__name__}: {error}"[:2000]
    exact_artifact_inside_job = exact_artifact is None or _within(
        exact_artifact, case_output
    )
    artifact_imports = tuple(_IMPORT_RE.findall(exact_artifact_text))
    endpoint_evidence = (
        Path(str(public_context["wrapper_evidence_file"]))
        if isinstance(public_context.get("wrapper_evidence_file"), str)
        else producer_payload_file
    )
    audits: dict[str, dict[str, Any]] = {
        name: exact_audits.get(
            name,
            _unsupported_audit(name, "exact_artifact_not_available"),
        )
        for name in (
            "kernel",
            "replay",
            "axiom",
            "program_direct_tm_coherence",
            "semantic_iff",
            "polynomial_bound",
        )
    }
    audits["endpoint"] = _boolean_audit(
        name="endpoint",
        ok=endpoint_exact,
        evidence_file=endpoint_evidence,
        blocker="exact_endpoint_binding_failed",
    )
    dependency_evidence = case_output / "commands/registry-revalidation.json"
    audits["dependency"] = (
        _boolean_audit(
            name="dependency",
            ok=dependency,
            evidence_file=dependency_evidence,
            blocker="registry_revalidation_failed",
        )
        if producer_status == "VERIFIED"
        else _unsupported_audit("dependency", "producer_did_not_verify")
    )
    required_verified_audits = (
        "kernel",
        "replay",
        "axiom",
        "endpoint",
        "dependency",
        "program_direct_tm_coherence",
        "semantic_iff",
        "polynomial_bound",
    )
    exact_verified = (
        producer_status == "VERIFIED"
        and exact_artifact_inside_job
        and all(audits[name].get("ok") is True for name in required_verified_audits)
    )
    status = (
        "VERIFIED"
        if exact_verified
        else ("FAILED" if producer_status == "VERIFIED" else producer_status)
    )
    exact_head = EXACT_EDGE_CAPABILITY_HEAD if exact_verified else None
    budget = {
        "profile": profile.name,
        "authoring_mode": profile.authoring_mode,
        "authoring_attempt_budget": profile.authoring_attempt_budget,
        "lean_timeout_seconds": profile.lean_timeout_seconds,
        "attempts_used": len(attempt_ledger),
        "model_calls_used": model_call_count,
        "http_attempts_used": sum(
            int(call.get("http_attempts") or 0)
            for call in safe_model_calls
            if isinstance(call.get("http_attempts"), int)
        ),
    }
    ledger_payload = {
        "schema_version": "hardness_exact_edge_model_ledger_v1",
        "case_id": case.case_id,
        "edge_id": case.edge_id,
        "budget": budget,
        "attempts": attempt_ledger,
        "calls": safe_model_calls,
        "token_usage": _token_usage(safe_model_calls),
        "issues": sorted(set(model_ledger_issues + attempt_ledger_issues)),
    }
    ledger_file = case_output / "exact-edge-model-ledger.json"
    _write_json(ledger_file, ledger_payload)
    security = _scan_output_security(
        case_output, secret=deepseek.api_key if deepseek is not None else None
    )
    security["cross_job_artifact"] = not (
        producer_artifact_inside_job and exact_artifact_inside_job
    )
    security["public_statement_context"] = (
        "not_applicable"
        if model_call_count == 0
        else ("prompted" if statement_prompted else "missing")
    )
    security["public_statement_sha256"] = public_context.get("statement_sha256")
    security["model_ledger_issues"] = ledger_payload["issues"]
    original_failure_code = _case_failure_code(payload)
    no_safe_authoring_dag = (
        producer_status == "BLOCKED"
        and not route_atoms
        and profile.authoring_mode in {MODEL_AUTO_MODE, MODEL_REQUIRED_MODE}
        and not payload.get("authoring_attempts")
        and authored_declaration is None
        and model_call_count == 0
        and original_failure_code
        not in {
            "required_model_unavailable",
            "exact_edge_endpoint_unavailable",
            "exact_edge_public_wrapper_invalid",
        }
    )
    if no_safe_authoring_dag:
        failure_code = "exact_edge_authoring_dag_unavailable"
    elif producer_status == "VERIFIED" and not exact_verified:
        failure_code = "exact_edge_exact_artifact_rejected"
    else:
        failure_code = original_failure_code
    if status == "VERIFIED":
        outcome_class = (
            "new_edge_verified"
            if authored_declaration is not None or authored_route is not None
            else "existing_edge_reconstructed"
        )
    elif no_safe_authoring_dag:
        outcome_class = "blocked_exact_edge_authoring_dag_unavailable"
    elif status == "BLOCKED":
        outcome_class = "blocked"
    else:
        outcome_class = "failed"
    verified_protocol = all(
        audits[name].get("ok") is True for name in required_verified_audits
    )
    public_preflight_valid = bool(
        public_context.get("missing_endpoint_modules")
    ) or public_context.get("wrapper_compile_ok") is True
    protocol_valid = (
        endpoint_exact
        and public_preflight_valid
        and producer_artifact_inside_job
        and exact_artifact_inside_job
        and not security["quarantined_material_detected"]
        and not security["secret_detected"]
        and not ledger_payload["issues"]
        and (model_call_count == 0 or statement_prompted)
        and (status != "VERIFIED" or verified_protocol)
    )
    artifact_sha256 = (
        _tagged_file_sha256(exact_artifact)
        if exact_artifact is not None
        and exact_artifact.is_file()
        and exact_artifact_inside_job
        else None
    )
    return {
        "schema_version": EXACT_EDGE_CASE_RESULT_SCHEMA_V1,
        "case_dir": str(case_output.resolve()),
        "case_id": case.case_id,
        "split": case.split,
        "edge_id": case.edge_id,
        "source": candidate_source,
        "target": candidate_target,
        "status": status,
        "producer_status": producer_status,
        "outcome_class": outcome_class,
        "failure_code": failure_code,
        "original_failure_code": original_failure_code,
        "protocol_valid": protocol_valid,
        "accepted_capability_head": exact_head,
        "accepted_capability_declaration": (
            EXACT_EDGE_CAPABILITY_DECLARATION if exact_verified else None
        ),
        "exact_artifact_generated": exact_artifact is not None,
        "selected_route_id": selected_route.get("route_id"),
        "selected_route_atoms": list(route_atoms),
        "route_atom_count": len(route_atoms),
        "artifact_imports": list(artifact_imports),
        "artifact_file": str(exact_artifact) if exact_artifact is not None else None,
        "artifact_sha256": artifact_sha256,
        "producer_artifact_file": (
            str(producer_artifact) if producer_artifact is not None else None
        ),
        "producer_artifact_sha256": (
            _tagged_file_sha256(producer_artifact)
            if producer_artifact is not None
            and producer_artifact.is_file()
            and producer_artifact_inside_job
            else None
        ),
        "authored_candidate_declaration": authored_declaration,
        "authored_route_declaration": authored_route,
        "public_context": dict(public_context),
        "budget": budget,
        "authoring_attempt_ledger": attempt_ledger,
        "first_accepted_attempt": next(
            (
                attempt["attempt"]
                for attempt in attempt_ledger
                if attempt.get("accepted") is True
            ),
            None,
        ),
        "model_calls": model_call_count,
        "http_ok_model_calls": sum(
            call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            for call in safe_model_calls
        ),
        "model_call_ledger": safe_model_calls,
        "model_call_ledger_file": str(ledger_file.resolve()),
        "model_call_ledger_sha256": _tagged_file_sha256(ledger_file),
        "model_call_ledger_content_sha256": sha256_id(ledger_payload),
        "token_usage": _token_usage(safe_model_calls),
        "audits": audits,
        "security": security,
        "blocker": (
            {
                "code": failure_code,
                "source": case.source,
                "target": case.target,
                "detail": (
                    "the production reduce-to planner emitted no safe exact-edge authoring DAG; "
                    "no model call was made"
                    if no_safe_authoring_dag
                    else exact_artifact_error
                ),
            }
            if status != "VERIFIED"
            else None
        ),
        "producer_payload_file": str(producer_payload_file.resolve()),
        "producer_payload_sha256": _tagged_file_sha256(producer_payload_file),
        "raw_result_sha256": _tagged_file_sha256(producer_payload_file),
    }


CaseExecutor = Callable[..., Any]


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _content_sha256(value: Mapping[str, Any]) -> str:
    payload = dict(value)
    payload.pop("content_sha256", None)
    return sha256_id(payload)


def run_exact_reduction_edge_benchmark(
    *,
    root: Path,
    suite: ExactEdgeSuite,
    budget_profiles: Mapping[str, ExactEdgeBudgetProfile],
    output_root: Path,
    deepseek: DeepSeekConfig | None = None,
    model_client: object | None = None,
    jobs: int = DEFAULT_EXACT_EDGE_CASE_JOBS,
    isolate_workspace: bool = True,
    runtime_prebuilt: bool = True,
    case_executor: CaseExecutor | None = None,
    manifest_sha256: str | None = None,
    expected_oracle_sha256: str | None = None,
    resume: bool = False,
) -> dict[str, Any]:
    """Run an answer-free exact-edge suite and preserve real failures."""

    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= MAX_EXACT_EDGE_CASE_JOBS:
        _fail("exact_edge_jobs_invalid", "exact-edge jobs must be in 1..4")
    unknown_profiles = sorted(
        {case.budget_profile for case in suite.cases} - set(budget_profiles)
    )
    if unknown_profiles:
        _fail("exact_edge_manifest_invalid", f"unknown budget profiles: {unknown_profiles!r}")
    runtime_build: dict[str, Any] | None = None
    if case_executor is None and any(
        case.construction_policy.mode == CONSTRUCTION_POLICY_MODE_NEW
        for case in suite.cases
    ):
        build = run_command(
            ["lake", "build", EXACT_EDGE_RUNTIME_MODULE],
            cwd=root.resolve() / "Lean",
            timeout_seconds=max(
                budget_profiles[case.budget_profile].lean_timeout_seconds
                for case in suite.cases
            ),
        )
        runtime_build = {
            **build.to_dict(),
            "command": list(build.command),
        }
        if not build.ok:
            _fail(
                "exact_edge_runtime_build_failed",
                "the route-free exact-edge runtime did not prebuild",
            )
    output = _fresh_output(output_root, resume=resume)
    started_at = datetime.now(timezone.utc).isoformat()
    run_id = sha256_id(
        {
            "schema_version": "hardness_exact_edge_run_identity_v1",
            "suite_id": suite.suite_id,
            "output_root": str(output),
            "started_at": started_at,
            "nonce": os.urandom(32).hex(),
        }
    )
    if case_executor is None:
        def executor(**kwargs: Any) -> Any:
            return _policy_dispatch_executor(**kwargs, resume=resume)
    else:
        executor = case_executor
    model_profile_required = any(
        budget_profiles[case.budget_profile].authoring_mode
        in {MODEL_AUTO_MODE, MODEL_REQUIRED_MODE}
        for case in suite.cases
    )
    formal_model_configuration = (
        not model_profile_required
        or (
            deepseek is not None
            and bool(deepseek.api_key)
            and is_formal_np_hard_qualification_config(deepseek)
        )
    )
    lock = threading.Lock()
    active = 0
    maximum_active = 0
    started = time.monotonic()
    workspace_physical_valid = False
    workspace_lean_root_symlink = True

    with isolated_exact_edge_workspace(root, enabled=isolate_workspace) as workspace:
        workspace_entries = sorted(path.name for path in workspace.iterdir())

        def run_case(case: ExactEdgeCase) -> dict[str, Any]:
            nonlocal active, maximum_active
            with lock:
                active += 1
                maximum_active = max(maximum_active, active)
            case_output = output / "cases" / case.case_id
            case_output.mkdir(parents=True, exist_ok=True)
            profile = budget_profiles[case.budget_profile]
            try:
                if not isolate_workspace and case_executor is not None:
                    wrapper_evidence = case_output / "public-context/Case.txt"
                    wrapper_evidence.parent.mkdir(parents=True, exist_ok=True)
                    wrapper_evidence.write_text(case.statement, encoding="utf-8")
                    execution_case = case
                    public_context = {
                        "declared_module": case.module,
                        "statement_sha256": sha256_id(
                            {"statement": case.statement}
                        ),
                        "statement_hash": case.statement_hash,
                        "construction_policy": case.construction_policy.to_dict(),
                        "endpoint_contract_version": case.endpoint_contract_version,
                        "endpoint_modules": [],
                        "missing_endpoint_modules": [],
                        "wrapper_module": case.module,
                        "wrapper_file": str(wrapper_evidence.resolve()),
                        "wrapper_evidence_file": str(wrapper_evidence.resolve()),
                        "wrapper_sha256": _tagged_file_sha256(wrapper_evidence),
                        "wrapper_compile_ok": True,
                    }
                else:
                    execution_case, public_context = _prepare_case_wrapper(
                        workspace_root=workspace,
                        case_output=case_output,
                        case=case,
                        timeout_seconds=profile.lean_timeout_seconds,
                    )
                if execution_case is None:
                    payload = _endpoint_preflight_payload(
                        case=case, context=public_context
                    )
                else:
                    value = executor(
                        workspace_root=workspace,
                        case=execution_case,
                        profile=profile,
                        case_output=case_output,
                        deepseek=deepseek,
                        model_client=model_client,
                        runtime_prebuilt=runtime_prebuilt,
                    )
                    payload = _agent_payload(value)
                producer_payload_file = case_output / "producer-payload.json"
                _write_json(producer_payload_file, payload)
                row = _audit_case_payload(
                    case=case,
                    profile=profile,
                    payload=payload,
                    case_output=case_output,
                    workspace_root=workspace,
                    deepseek=deepseek,
                    producer_payload_file=producer_payload_file,
                    public_context=public_context,
                )
                if case.split == UNGROUPED_BENCHMARK_KEY:
                    row.pop("split", None)
                row["run_id"] = run_id
                row["content_sha256"] = _content_sha256(row)
                return row
            except Exception as error:  # Per-case infra failures invalidate, not abort, the run.
                case_output.mkdir(parents=True, exist_ok=True)
                failure_payload = {
                    "schema_version": "hardness_exact_edge_runner_exception_v1",
                    "case_id": case.case_id,
                    "error_type": type(error).__name__,
                    "error": str(error)[:2000],
                }
                producer_payload_file = case_output / "producer-payload.json"
                _write_json(producer_payload_file, failure_payload)
                ledger_payload = {
                    "schema_version": "hardness_exact_edge_model_ledger_v1",
                    "case_id": case.case_id,
                    "edge_id": case.edge_id,
                    "budget": {
                        "profile": profile.name,
                        "authoring_attempt_budget": profile.authoring_attempt_budget,
                    },
                    "attempts": [],
                    "calls": [],
                    "token_usage": {},
                    "issues": ["runner_exception"],
                }
                ledger_file = case_output / "exact-edge-model-ledger.json"
                _write_json(ledger_file, ledger_payload)
                row = {
                    "schema_version": EXACT_EDGE_CASE_RESULT_SCHEMA_V1,
                    "run_id": run_id,
                    "case_dir": str(case_output.resolve()),
                    "case_id": case.case_id,
                    "split": case.split,
                    "edge_id": case.edge_id,
                    "source": case.source,
                    "target": case.target,
                    "status": "FAILED",
                    "producer_status": "FAILED",
                    "outcome_class": "infra_error",
                    "failure_code": "exact_edge_runner_exception",
                    "original_failure_code": None,
                    "protocol_valid": False,
                    "accepted_capability_head": None,
                    "accepted_capability_declaration": None,
                    "exact_artifact_generated": False,
                    "selected_route_id": None,
                    "selected_route_atoms": [],
                    "route_atom_count": 0,
                    "artifact_imports": [],
                    "artifact_file": None,
                    "artifact_sha256": None,
                    "producer_artifact_file": None,
                    "producer_artifact_sha256": None,
                    "authored_candidate_declaration": None,
                    "authored_route_declaration": None,
                    "public_context": {},
                    "budget": ledger_payload["budget"],
                    "authoring_attempt_ledger": [],
                    "first_accepted_attempt": None,
                    "model_calls": 0,
                    "http_ok_model_calls": 0,
                    "model_call_ledger": [],
                    "model_call_ledger_file": str(ledger_file.resolve()),
                    "model_call_ledger_sha256": _tagged_file_sha256(ledger_file),
                    "model_call_ledger_content_sha256": sha256_id(ledger_payload),
                    "token_usage": {},
                    "audits": {
                        name: _unsupported_audit(name, "runner_exception")
                        for name in SUPPORTED_REQUIRED_AUDITS
                    },
                    "security": {
                        "quarantined_material_detected": False,
                        "secret_detected": False,
                        "archive_solution_accessed": False,
                        "cross_job_artifact": False,
                    },
                    "blocker": {
                        "code": "exact_edge_runner_exception",
                        "source": case.source,
                        "target": case.target,
                        "detail": f"{type(error).__name__}: {error}"[:2000],
                    },
                    "producer_payload_file": str(producer_payload_file.resolve()),
                    "producer_payload_sha256": _tagged_file_sha256(
                        producer_payload_file
                    ),
                    "raw_result_sha256": _tagged_file_sha256(producer_payload_file),
                }
                if case.split == UNGROUPED_BENCHMARK_KEY:
                    row.pop("split", None)
                row["content_sha256"] = _content_sha256(row)
                return row
            finally:
                with lock:
                    active -= 1

        rows: dict[str, dict[str, Any]] = {}
        if jobs == 1 or len(suite.cases) <= 1:
            for case in suite.cases:
                rows[case.case_id] = run_case(case)
        else:
            with ThreadPoolExecutor(
                max_workers=min(jobs, len(suite.cases)),
                thread_name_prefix="np-hard-exact-edge",
            ) as pool:
                pending = {pool.submit(run_case, case): case.case_id for case in suite.cases}
                for future in as_completed(pending):
                    rows[pending[future]] = future.result()
        workspace_lean_root_symlink = (workspace / "Lean").is_symlink()
        workspace_physical_valid = (
            workspace_entries == ["Lean"]
            and not workspace_lean_root_symlink
            and not _workspace_quarantine_violations(workspace)
        )

    ordered = [rows[case.case_id] for case in suite.cases]
    total_model_calls = sum(
        row.get("model_calls", 0)
        for row in ordered
        if isinstance(row.get("model_calls"), int)
    )
    all_model_calls = [
        call
        for row in ordered
        for call in (row.get("model_call_ledger") or [])
        if isinstance(call, Mapping)
    ]
    parallel = {
        "configured_jobs": jobs,
        "submitted_case_tasks": len(suite.cases),
        "maximum_concurrent_case_tasks": maximum_active,
        "final_active_case_tasks": active,
        "wall_duration_seconds": round(time.monotonic() - started, 6),
        "observed_parallelism": (
            jobs == 1
            or len(suite.cases) <= 1
            or maximum_active >= min(2, jobs, len(suite.cases))
        ),
    }
    isolation_valid = (
        workspace_physical_valid
        if isolate_workspace
        else case_executor is not None
    )
    run_valid = (
        isolation_valid
        and parallel["final_active_case_tasks"] == 0
        and all(row.get("protocol_valid") is True for row in ordered)
        and (formal_model_configuration or case_executor is not None)
    )
    report = {
        "schema_version": EXACT_EDGE_RUN_REPORT_SCHEMA_V1,
        "run_id": run_id,
        "generated_at": started_at,
        **(
            {"benchmark_lane": "exact-reduction-edge"}
            if suite.split != UNGROUPED_BENCHMARK_KEY
            else {"evaluation_kind": "benchmark"}
        ),
        "run_valid": run_valid,
        "resume": resume,
        "output_root": str(output),
        "report_file": str((output / "report.json").resolve()),
        "manifest_sha256": manifest_sha256,
        "expected_oracle_sha256": expected_oracle_sha256,
        "suite": {
            **(
                {"split": suite.split}
                if suite.split != UNGROUPED_BENCHMARK_KEY
                else {}
            ),
            "suite_id": suite.suite_id,
            "sha256": suite.sha256,
            "case_count": len(suite.cases),
            "answer_free": True,
        },
        "model": deepseek.to_public_dict() if deepseek is not None else None,
        "formal_model_configuration": formal_model_configuration,
        "runtime_build": runtime_build,
        "metrics": {
            "case_count": len(ordered),
            "unique_directions": len({case.edge_id for case in suite.cases}),
            "verified_count": sum(row["status"] == "VERIFIED" for row in ordered),
            "blocked_count": sum(row["status"] == "BLOCKED" for row in ordered),
            "failed_count": sum(row["status"] == "FAILED" for row in ordered),
            "existing_edge_reconstructed": sum(
                row["outcome_class"] == "existing_edge_reconstructed" for row in ordered
            ),
            "new_edge_verified": sum(
                row["outcome_class"] == "new_edge_verified" for row in ordered
            ),
            "exact_edge_authoring_dag_unavailable": sum(
                row["failure_code"] == "exact_edge_authoring_dag_unavailable"
                for row in ordered
            ),
            "model_calls": total_model_calls,
            "http_ok_model_calls": sum(
                call.get("called") is True
                and call.get("ok") is True
                and call.get("status_code") == 200
                for call in all_model_calls
            ),
            "token_usage": _token_usage(all_model_calls),
        },
        "parallel_execution": parallel,
        "isolation": {
            "enabled": isolate_workspace,
            "valid": isolation_valid,
            "physical_copy": isolate_workspace and workspace_physical_valid,
            "lean_root_symlink": workspace_lean_root_symlink,
            "workspace_entries": workspace_entries,
            "archive_present": False if isolation_valid else None,
            "plan_present": False if isolation_valid else None,
            "oracle_present": False if isolation_valid else None,
        },
        "cases": ordered,
    }
    report["content_sha256"] = _content_sha256(report)
    _write_json(output / "report.json", report)
    return report


def _forbidden_route_used(row: Mapping[str, Any], forbidden: Sequence[str]) -> bool:
    atoms = [value for value in (row.get("selected_route_atoms") or []) if isinstance(value, str)]
    imports = [value for value in (row.get("artifact_imports") or []) if isinstance(value, str)]
    for prefix in forbidden:
        for value in (*atoms, *imports):
            if value == prefix or value.startswith(prefix + "."):
                return True
    return False


def _selected_existing_path_evidence(row: Mapping[str, Any]) -> dict[str, Any]:
    atoms = [
        value
        for value in (row.get("selected_route_atoms") or [])
        if isinstance(value, str) and value
    ]
    route_id = row.get("selected_route_id")
    exact_path = Path(str(row.get("artifact_file") or ""))
    producer_path = Path(str(row.get("producer_artifact_file") or ""))
    try:
        exact_source = exact_path.read_text(encoding="utf-8")
        producer_source = producer_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        exact_source = ""
        producer_source = ""
    atom_bindings = {
        atom: atom in exact_source and atom in producer_source for atom in atoms
    }
    no_authored_capability = not (
        row.get("authored_candidate_declaration")
        or row.get("authored_route_declaration")
    )
    ok = (
        bool(atoms)
        and isinstance(route_id, str)
        and _HASH_RE.fullmatch(route_id) is not None
        and all(atom_bindings.values())
        and no_authored_capability
        and row.get("outcome_class") == "existing_edge_reconstructed"
    )
    return {
        "ok": ok,
        "selected_route_id": route_id,
        "atoms": atoms,
        "atom_artifact_bindings": atom_bindings,
        "no_authored_capability": no_authored_capability,
    }


def _existing_route_declaration_audit(
    *,
    manifest: ExactEdgeManifest,
    case: ExactEdgeCase,
    declaration: str,
) -> dict[str, Any]:
    repository_root: Path | None = None
    for parent in (manifest.file.parent, *manifest.file.parents):
        if (parent / "Lean/Reference/ComplexityReduction").is_dir():
            repository_root = parent.resolve()
            break
    if repository_root is None:
        return {
            "ok": False,
            "declaration": declaration,
            "failure_code": "existing_route_repository_unavailable",
        }
    namespace = declaration.rsplit(".", 1)[0]
    relative_namespace = Path(*namespace.split("."))
    reference = repository_root / "Lean/Reference"
    candidates = (
        (reference / relative_namespace).with_suffix(".lean"),
        reference / relative_namespace / "Unified.lean",
    )
    source_file = next((path for path in candidates if path.is_file()), None)
    if source_file is None:
        return {
            "ok": False,
            "declaration": declaration,
            "failure_code": "existing_route_source_unavailable",
            "candidate_files": [str(path) for path in candidates],
        }
    module = ".".join(source_file.relative_to(reference).with_suffix("").parts)
    audit_source = (
        f"import {module}\n\n"
        + f"#check ({declaration} :\n"
        + "  ComplexityReduction.Certificate.CertifiedReduction\n"
        + f"    {case.source}\n"
        + f"    {case.target})\n"
    )
    with tempfile.TemporaryDirectory(prefix="np-hard-existing-route-audit-") as directory:
        audit_file = Path(directory) / "ExistingRouteAudit.lean"
        audit_file.write_text(audit_source, encoding="utf-8")
        command = run_command(
            ["lake", "env", "lean", str(audit_file)],
            cwd=repository_root / "Lean",
            timeout_seconds=120,
        )
    return {
        "ok": command.ok,
        "declaration": declaration,
        "module": module,
        "source_file": str(source_file.resolve()),
        "source_sha256": _tagged_file_sha256(source_file),
        "audit_source_sha256": sha256_id({"source": audit_source}),
        "command": {
            "exit_code": command.exit_code,
            "timed_out": command.timed_out,
            "stdout_sha256": sha256_id({"stdout": command.stdout}),
            "stderr_sha256": sha256_id({"stderr": command.stderr}),
        },
        "failure_code": None if command.ok else "existing_route_type_audit_failed",
    }


def _file_binding_valid(
    *, path_value: Any, sha256_value: Any, case_dir: Path
) -> bool:
    if not isinstance(path_value, str) or not isinstance(sha256_value, str):
        return False
    path = Path(path_value).resolve()
    return (
        _within(path, case_dir)
        and path.is_file()
        and _HASH_RE.fullmatch(sha256_value) is not None
        and _tagged_file_sha256(path) == sha256_value
    )


def _case_filesystem_issues(row: Mapping[str, Any], *, run_id: str) -> list[str]:
    issues: list[str] = []
    if row.get("run_id") != run_id:
        issues.append("case_run_identity_forged")
    if row.get("content_sha256") != _content_sha256(row):
        issues.append("case_content_hash_mismatch")
    case_dir_value = row.get("case_dir")
    if not isinstance(case_dir_value, str):
        return sorted(set(issues + ["case_directory_missing"]))
    case_dir = Path(case_dir_value).resolve()
    if not case_dir.is_dir():
        return sorted(set(issues + ["case_directory_missing"]))

    if not _file_binding_valid(
        path_value=row.get("producer_payload_file"),
        sha256_value=row.get("producer_payload_sha256"),
        case_dir=case_dir,
    ):
        issues.append("producer_payload_binding_invalid")

    ledger_path_value = row.get("model_call_ledger_file")
    if not _file_binding_valid(
        path_value=ledger_path_value,
        sha256_value=row.get("model_call_ledger_sha256"),
        case_dir=case_dir,
    ):
        issues.append("model_ledger_file_binding_invalid")
        ledger_payload: Any = None
    else:
        try:
            ledger_payload = json.loads(Path(str(ledger_path_value)).read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            ledger_payload = None
    if not isinstance(ledger_payload, Mapping):
        issues.append("model_ledger_invalid")
    else:
        if row.get("model_call_ledger_content_sha256") != sha256_id(ledger_payload):
            issues.append("model_ledger_content_hash_mismatch")
        if ledger_payload.get("case_id") != row.get("case_id") or ledger_payload.get(
            "edge_id"
        ) != row.get("edge_id"):
            issues.append("model_ledger_identity_mismatch")
        if ledger_payload.get("calls") != row.get("model_call_ledger"):
            issues.append("model_ledger_calls_mismatch")
        if ledger_payload.get("attempts") != row.get("authoring_attempt_ledger"):
            issues.append("model_ledger_attempts_mismatch")
        if ledger_payload.get("budget") != row.get("budget"):
            issues.append("model_ledger_budget_mismatch")
        if ledger_payload.get("token_usage") != row.get("token_usage"):
            issues.append("model_ledger_usage_mismatch")
        if ledger_payload.get("issues"):
            issues.append("model_ledger_contains_issues")

    calls = row.get("model_call_ledger")
    call_rows = calls if isinstance(calls, list) else []
    if not isinstance(calls, list):
        issues.append("model_ledger_calls_invalid")
    called_count = sum(
        isinstance(call, Mapping) and call.get("called") is True for call in call_rows
    )
    http_ok_count = sum(
        isinstance(call, Mapping)
        and call.get("called") is True
        and call.get("ok") is True
        and call.get("status_code") == 200
        for call in call_rows
    )
    if row.get("model_calls") != called_count:
        issues.append("model_call_count_mismatch")
    if row.get("http_ok_model_calls") != http_ok_count:
        issues.append("model_http_status_count_mismatch")
    if row.get("token_usage") != _token_usage(
        [call for call in call_rows if isinstance(call, Mapping)]
    ):
        issues.append("model_usage_total_mismatch")
    seen_request_ids: set[str] = set()
    seen_call_keys: set[tuple[str, str, int]] = set()
    for index, call in enumerate(call_rows, start=1):
        if not isinstance(call, Mapping):
            issues.append(f"model_call_{index}_invalid")
            continue
        if call.get("call") != index or call.get("evidence_valid") is not True:
            issues.append(f"model_call_{index}_evidence_invalid")
        if row.get("authoring_protocol") == EXACT_EDGE_AUTHORING_TASK_CLASS:
            request_id = call.get("request_id")
            task_id = call.get("task_id")
            call_case_id = call.get("case_id")
            node_id = call.get("node_id")
            attempt = call.get("attempt")
            if (
                not isinstance(request_id, str)
                or not isinstance(task_id, str)
                or call_case_id != row.get("case_id")
                or not isinstance(node_id, str)
                or not node_id
                or isinstance(attempt, bool)
                or not isinstance(attempt, int)
                or attempt <= 0
            ):
                issues.append(f"model_call_{index}_identity_invalid")
            else:
                expected_request_id = sha256_id(
                    {
                        "task_request_id": task_id,
                        "case_id": call_case_id,
                        "node_id": node_id,
                        "attempt": attempt,
                    }
                )
                if request_id != expected_request_id:
                    issues.append(f"model_call_{index}_request_hash_invalid")
                call_key = (str(call_case_id), node_id, attempt)
                if request_id in seen_request_ids or call_key in seen_call_keys:
                    issues.append(f"model_call_{index}_identity_reused")
                seen_request_ids.add(request_id)
                seen_call_keys.add(call_key)
        if call.get("called") is True:
            status = call.get("status_code")
            if status is not None and (
                isinstance(status, bool) or not isinstance(status, int)
            ):
                issues.append(f"model_call_{index}_status_invalid")
            files = call.get("files") if isinstance(call.get("files"), Mapping) else {}
            for name in ("prompt", "response"):
                evidence = files.get(name)
                if not isinstance(evidence, Mapping) or not _file_binding_valid(
                    path_value=evidence.get("path"),
                    sha256_value=evidence.get("sha256"),
                    case_dir=case_dir,
                ):
                    issues.append(f"model_call_{index}_{name}_file_invalid")
            if call.get("protocol_accepted") is True:
                evidence = files.get("patch")
                if not isinstance(evidence, Mapping) or not _file_binding_valid(
                    path_value=evidence.get("path"),
                    sha256_value=evidence.get("sha256"),
                    case_dir=case_dir,
                ):
                    issues.append(f"model_call_{index}_patch_file_invalid")
            if call.get("ok") is True and call.get("status_code") == 200:
                usage = call.get("usage")
                if not isinstance(usage, Mapping) or not usage:
                    issues.append(f"model_call_{index}_usage_missing")

    if row.get("status") == "VERIFIED":
        if not _file_binding_valid(
            path_value=row.get("artifact_file"),
            sha256_value=row.get("artifact_sha256"),
            case_dir=case_dir,
        ):
            issues.append("exact_artifact_file_binding_invalid")
        if not _file_binding_valid(
            path_value=row.get("producer_artifact_file"),
            sha256_value=row.get("producer_artifact_sha256"),
            case_dir=case_dir,
        ):
            issues.append("producer_artifact_file_binding_invalid")

        audits = row.get("audits") if isinstance(row.get("audits"), Mapping) else {}
        evidence_files: list[str] = []
        for name in SUPPORTED_REQUIRED_AUDITS:
            audit = audits.get(name)
            if not isinstance(audit, Mapping):
                issues.append(f"audit_evidence_invalid:{name}")
                continue
            if audit.get("status") != "passed" or audit.get("ok") is not True:
                issues.append(f"audit_evidence_invalid:{name}")
            if not _file_binding_valid(
                path_value=audit.get("evidence_file"),
                sha256_value=audit.get("evidence_sha256"),
                case_dir=case_dir,
            ):
                issues.append(f"audit_evidence_file_invalid:{name}")
            elif isinstance(audit.get("evidence_file"), str):
                evidence_files.append(str(Path(str(audit["evidence_file"])).resolve()))
            artifact_file = audit.get("audit_artifact_file")
            if artifact_file is not None and not _file_binding_valid(
                path_value=artifact_file,
                sha256_value=audit.get("audit_artifact_sha256"),
                case_dir=case_dir,
            ):
                issues.append(f"audit_artifact_file_invalid:{name}")
        if len(evidence_files) != len(set(evidence_files)):
            issues.append("required_audits_share_evidence")
    return sorted(set(issues))


def _mutation_issues(
    *,
    case: ExactEdgeCase,
    oracle: ExactEdgeOracleCase,
    row: Mapping[str, Any],
    existing_route_audit: Mapping[str, Any] | None,
) -> list[str]:
    issues: list[str] = []
    source = row.get("source")
    target = row.get("target")
    if source == case.target and target == case.source:
        issues.append("candidate_wrong_direction")
    elif source != case.source or target != case.target:
        issues.append("candidate_wrong_endpoint")
    if row.get("edge_id") != case.edge_id:
        issues.append("result_edge_identity_forged")
    public_context = (
        row.get("public_context")
        if isinstance(row.get("public_context"), Mapping)
        else {}
    )
    if public_context.get("statement_sha256") != sha256_id(
        {"statement": case.statement}
    ):
        issues.append("public_statement_binding_missing")
    if public_context.get("statement_hash") != case.statement_hash:
        issues.append("public_statement_hash_mismatch")
    if public_context.get("declared_module") != case.module:
        issues.append("public_module_binding_missing")
    policy = case.construction_policy
    expected_mode = (
        CONSTRUCTION_POLICY_MODE_RECONSTRUCTION
        if oracle.existing_route is not None
        else CONSTRUCTION_POLICY_MODE_NEW
    )
    if policy.mode != expected_mode:
        issues.append("public_policy_oracle_mismatch")
    if policy.allow_composition != oracle.allow_composition:
        issues.append("public_policy_oracle_mismatch")
    if policy.require_new_primitive != oracle.require_new_primitive:
        issues.append("public_policy_oracle_mismatch")
    if public_context.get("construction_policy") != policy.to_dict():
        issues.append("public_construction_policy_binding_missing")
    if public_context.get("endpoint_contract_version") != case.endpoint_contract_version:
        issues.append("public_endpoint_contract_binding_missing")
    if row.get("status") == "VERIFIED" and row.get("accepted_capability_head") != (
        EXACT_EDGE_CAPABILITY_HEAD
    ):
        if row.get("accepted_capability_head") == (
            "ComplexityReduction.Certificate.NativeTMNPHard"
        ):
            issues.append("target_hardness_only_not_exact_edge")
        else:
            issues.append("candidate_exact_type_mismatch")
    staged_protocol = row.get("authoring_protocol") == EXACT_EDGE_AUTHORING_TASK_CLASS
    if row.get("status") == "VERIFIED" and (
        (
            row.get("accepted_capability_declaration") != EXACT_EDGE_CAPABILITY_DECLARATION
            and not (
                staged_protocol
                and isinstance(row.get("accepted_capability_declaration"), str)
                and row["accepted_capability_declaration"].endswith(
                    ".authoredForwardReduction"
                )
            )
        )
        or row.get("exact_artifact_generated") is not True
        or Path(str(row.get("artifact_file") or "")).name != "ExactEdge.lean"
    ):
        issues.append("candidate_exact_artifact_missing")
    if row.get("status") == "VERIFIED":
        audits = row.get("audits") if isinstance(row.get("audits"), Mapping) else {}
        for name in ("kernel", "replay", "axiom", "endpoint", "dependency"):
            audit = audits.get(name)
            if not isinstance(audit, Mapping) or audit.get("ok") is not True:
                issues.append(f"exact_artifact_audit_failed:{name}")
    if not oracle.allow_composition and int(row.get("route_atom_count") or 0) > 1:
        issues.append("forbidden_composition")
    if oracle.require_new_primitive and row.get("status") == "VERIFIED" and not (
        row.get("authored_candidate_declaration") or row.get("authored_route_declaration")
    ):
        issues.append("required_new_primitive_bypassed")
    if (
        oracle.require_new_primitive
        and row.get("status") == "VERIFIED"
        and (row.get("authored_candidate_declaration") or row.get("authored_route_declaration"))
        and int(row.get("http_ok_model_calls") or 0) == 0
    ):
        issues.append("new_primitive_without_real_model_call")
    if _forbidden_route_used(row, oracle.forbidden_route_imports):
        issues.append("forbidden_route_import")
    if oracle.existing_route is not None and row.get("status") == "VERIFIED":
        declaration_evidence = (
            existing_route_audit.get("declaration")
            if isinstance(existing_route_audit, Mapping)
            else None
        )
        selected_path_evidence = (
            existing_route_audit.get("selected_path")
            if isinstance(existing_route_audit, Mapping)
            else None
        )
        declaration_ok = (
            isinstance(declaration_evidence, Mapping)
            and declaration_evidence.get("ok") is True
        )
        selected_path_ok = (
            isinstance(selected_path_evidence, Mapping)
            and selected_path_evidence.get("ok") is True
        )
        if not (declaration_ok and selected_path_ok):
            issues.append("existing_route_not_observed")
        if row.get("outcome_class") != "existing_edge_reconstructed":
            issues.append("existing_route_outcome_mismatch")
    if (
        oracle.existing_route is None
        and row.get("status") == "VERIFIED"
        and row.get("outcome_class") == "existing_edge_reconstructed"
    ):
        issues.append("unexpected_existing_route_classification")
    security = row.get("security") if isinstance(row.get("security"), Mapping) else {}
    if security.get("archive_solution_accessed") is True or security.get(
        "quarantined_material_detected"
    ) is True:
        issues.append("archive_solution_access")
    if security.get("cross_job_artifact") is True:
        issues.append("cross_job_candidate")
    if security.get("secret_detected") is True:
        issues.append("secret_in_exact_edge_output")
    if row.get("status") == "VERIFIED":
        audits = row.get("audits") if isinstance(row.get("audits"), Mapping) else {}
        for name in oracle.required_audits:
            audit = audits.get(name)
            if not isinstance(audit, Mapping) or audit.get("ok") is not True:
                issues.append(f"required_audit_failed:{name}")
    return sorted(set(issues))


def score_exact_reduction_edge_run(
    *,
    manifest: ExactEdgeManifest,
    suite: ExactEdgeSuite,
    oracle: ExactEdgeOracle,
    run_report: Mapping[str, Any],
) -> dict[str, Any]:
    """Independently score a completed run without rerunning production code."""

    if run_report.get("schema_version") != EXACT_EDGE_RUN_REPORT_SCHEMA_V1:
        _fail("exact_edge_result_invalid", "unsupported exact-edge run report")
    if not manifest.file.is_file() or _tagged_file_sha256(manifest.file) != manifest.sha256:
        _fail("candidate_dependency_stale", "manifest file/hash binding is invalid")
    if not oracle.file.is_file() or _tagged_file_sha256(oracle.file) != oracle.sha256:
        _fail("candidate_dependency_stale", "oracle file/hash binding is invalid")
    if oracle.sha256 != manifest.oracle_sha256:
        _fail(
            "candidate_dependency_stale",
            "scorer oracle does not match the content-addressed manifest binding",
        )
    manifest_case_bindings = {
        case.case_id: (case.to_public_dict(), case.split, frozen_suite.sha256)
        for frozen_suite in manifest.suites.values()
        for case in frozen_suite.cases
    }
    for case in suite.cases:
        binding = manifest_case_bindings.get(case.case_id)
        if (
            binding is None
            or binding[0] != case.to_public_dict()
            or binding[1] != case.split
        ):
            _fail(
                "candidate_dependency_stale",
                f"public case {case.case_id} is outside the frozen manifest",
            )
    suite_payload = run_report.get("suite")
    if not isinstance(suite_payload, Mapping) or suite_payload.get("sha256") != suite.sha256:
        _fail("candidate_dependency_stale", "run report is bound to another public suite")
    expected_ids = {case.case_id for case in suite.cases}
    if not expected_ids.issubset(oracle.cases):
        _fail("exact_edge_oracle_invalid", "oracle lacks public suite case IDs")
    report_integrity_issues: list[str] = []
    if run_report.get("manifest_sha256") != manifest.sha256:
        report_integrity_issues.append("manifest_binding_mismatch")
    if run_report.get("expected_oracle_sha256") != manifest.oracle_sha256:
        report_integrity_issues.append("oracle_binding_mismatch")
    run_id = run_report.get("run_id")
    if not isinstance(run_id, str) or _HASH_RE.fullmatch(run_id) is None:
        report_integrity_issues.append("run_identity_invalid")
        run_id = ""
    if run_report.get("content_sha256") != _content_sha256(run_report):
        report_integrity_issues.append("run_report_content_hash_mismatch")
    output_root_value = run_report.get("output_root")
    report_file_value = run_report.get("report_file")
    if not isinstance(output_root_value, str) or not isinstance(report_file_value, str):
        report_integrity_issues.append("run_report_file_binding_missing")
    else:
        output_root = Path(output_root_value).resolve()
        report_file = Path(report_file_value).resolve()
        if not _within(report_file, output_root) or not report_file.is_file():
            report_integrity_issues.append("run_report_file_binding_invalid")
        else:
            try:
                persisted_report = json.loads(report_file.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, json.JSONDecodeError):
                persisted_report = None
            if persisted_report != dict(run_report):
                report_integrity_issues.append("run_report_persistence_mismatch")
    raw_rows = run_report.get("cases")
    if not isinstance(raw_rows, list):
        _fail("exact_edge_result_invalid", "run report has no case rows")
    by_id: dict[str, Mapping[str, Any]] = {}
    for row in raw_rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("case_id"), str):
            _fail("exact_edge_result_invalid", "run case row is invalid")
        case_id = str(row["case_id"])
        if case_id in by_id:
            _fail("exact_edge_result_forged", "run report repeats a case ID")
        by_id[case_id] = row
    if set(by_id) != expected_ids:
        _fail("exact_edge_result_forged", "run report case IDs differ from the suite")
    scored_rows: list[dict[str, Any]] = []
    all_issues: list[str] = list(report_integrity_issues)
    existing_route_declaration_cache: dict[str, dict[str, Any]] = {}
    for case in suite.cases:
        policy = oracle.cases[case.case_id]
        if (
            policy.split != case.split
            or policy.canonical_source != case.source
            or policy.canonical_target != case.target
        ):
            _fail("exact_edge_oracle_invalid", f"oracle endpoint drift for {case.case_id}")
        row = by_id[case.case_id]
        existing_route_audit: dict[str, Any] | None = None
        if policy.existing_route is not None:
            declaration_audit = existing_route_declaration_cache.get(
                policy.existing_route
            )
            if declaration_audit is None:
                declaration_audit = _existing_route_declaration_audit(
                    manifest=manifest,
                    case=case,
                    declaration=policy.existing_route,
                )
                existing_route_declaration_cache[policy.existing_route] = (
                    declaration_audit
                )
            existing_route_audit = {
                "expected": policy.existing_route,
                "declaration": declaration_audit,
                "selected_path": _selected_existing_path_evidence(row),
            }
        issues = sorted(
            set(
                _mutation_issues(
                    case=case,
                    oracle=policy,
                    row=row,
                    existing_route_audit=existing_route_audit,
                )
                + _case_filesystem_issues(row, run_id=run_id)
            )
        )
        all_issues.extend(issues)
        eligible = policy.status == "ready"
        verified = eligible and row.get("status") == "VERIFIED" and not issues
        scored_rows.append(
            {
                "case_id": case.case_id,
                **(
                    {"split": case.split}
                    if case.split != UNGROUPED_BENCHMARK_KEY
                    else {}
                ),
                "edge_id": case.edge_id,
                "archive_id": policy.archive_id,
                "oracle_status": policy.status,
                "eligible": eligible,
                "verified": verified,
                "outcome_class": row.get("outcome_class"),
                "failure_code": row.get("failure_code"),
                "model_calls": row.get("model_calls", 0),
                "first_accepted_attempt": row.get("first_accepted_attempt"),
                "first_attempt_verified": (
                    verified and row.get("first_accepted_attempt") == 1
                ),
                "cost": {
                    "authoring_attempts": (
                        row.get("budget", {}).get("attempts_used")
                        if isinstance(row.get("budget"), Mapping)
                        else None
                    ),
                    "model_calls": row.get("model_calls", 0),
                    "http_ok_model_calls": row.get("http_ok_model_calls", 0),
                    "token_usage": row.get("token_usage", {}),
                },
                "existing_route_audit": existing_route_audit,
                "mutation_rejections": issues,
            }
        )
    eligible_rows = [row for row in scored_rows if row["eligible"]]
    verified_rows = [row for row in eligible_rows if row["verified"]]
    mutation_counts: dict[str, int] = {}
    for issue in all_issues:
        mutation_counts[issue] = mutation_counts.get(issue, 0) + 1
    run_valid = run_report.get("run_valid") is True and not all_issues
    score = {
        "schema_version": EXACT_EDGE_SCORE_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "run_valid": run_valid,
        "run_id": run_id,
        "manifest_sha256": manifest.sha256,
        "suite_sha256": suite.sha256,
        "oracle_sha256": oracle.sha256,
        "scorecard": {
            "unique_directions": len(suite.cases),
            "endpoint_ready": len(eligible_rows),
            "edge_verified_at_budget": (
                len(verified_rows) / len(eligible_rows) if eligible_rows else None
            ),
            "verified_count": len(verified_rows),
            "existing_edge_reconstructed": sum(
                row["verified"] and row["outcome_class"] == "existing_edge_reconstructed"
                for row in scored_rows
            ),
            "new_edge_verified": sum(
                row["verified"] and row["outcome_class"] == "new_edge_verified"
                for row in scored_rows
            ),
            "model_calls": sum(
                int(row["model_calls"])
                for row in scored_rows
                if isinstance(row["model_calls"], int)
            ),
            "first_attempt_verified_count": sum(
                row["first_attempt_verified"] for row in scored_rows
            ),
            "token_usage": _token_usage(
                [
                    call
                    for case_row in run_report.get("cases", [])
                    if isinstance(case_row, Mapping)
                    for call in (case_row.get("model_call_ledger") or [])
                    if isinstance(call, Mapping)
                ]
            ),
            "mutation_rejection_counts": dict(sorted(mutation_counts.items())),
        },
        "cases": scored_rows,
    }
    return score


def write_exact_edge_report(path: Path, report: Mapping[str, Any]) -> None:
    schema = report.get("schema_version")
    if schema not in {EXACT_EDGE_RUN_REPORT_SCHEMA_V1, EXACT_EDGE_SCORE_REPORT_SCHEMA_V1}:
        _fail("exact_edge_result_invalid", "refusing to write an unsupported report")
    _write_json(path, report)
