"""H-I target-hardness capability benchmark contracts, runner, and scorer.

The production runner intentionally never opens the scorer oracle.  It loads
only the public manifest, answer-free suites, and the canonical target matrix,
then executes each case through :class:`NPHardOrchestratorV2` in an isolated
workspace.  Scoring is a separate operation which verifies the stored raw
evidence before opening the content-addressed oracle.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import threading
import time
from typing import Any, Callable, Iterable, Mapping, Sequence

from .lean_runner import build_module_command, run_command, sha256_file
from .model_client import DeepSeekConfig
from .models import sha256_id
from .np_hard_authoring import (
    NP_HARD_AUTHORING_TASK_CLASSES_V2,
    NPHardAuthoringContractError,
    NPHardAuthoringTaskV2,
    deletion_command_matches_declaration_v2,
    validate_successor_only_authoritative_evidence_v2,
)
from .np_hard_input import NPHardInputError
from .np_hard_input import (
    NP_HARD_INPUT_REGISTRY_PATH,
    NP_HARD_TARGET_MATRIX_PATH,
)
from .np_hard_orchestrator import (
    NP_HARD_PROOF_RESULT_SCHEMA_V2,
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorError,
    NPHardOrchestratorV2,
    NPHardProofResultV2,
)
from .np_hard_production import (
    FORMAL_BASE_URL,
    FORMAL_MAX_TOKENS,
    FORMAL_MODEL,
    FORMAL_PROVIDER,
    FORMAL_REASONING_EFFORT,
    FORMAL_TEMPERATURE,
    FORMAL_TIMEOUT_SECONDS,
    PUBLIC_STATUSES,
    is_formal_np_hard_qualification_config,
    public_np_hard_status,
)
from .np_hard_target_matrix import load_np_hard_target_matrix


CAPABILITY_MANIFEST_SCHEMA_V1 = "hardness_np_hard_capability_manifest_v1"
CAPABILITY_SUITE_SCHEMA_V1 = "hardness_np_hard_capability_suite_v1"
CAPABILITY_ORACLE_SCHEMA_V1 = "hardness_np_hard_capability_oracle_v1"
CAPABILITY_RUN_SCHEMA_V1 = "hardness_np_hard_capability_run_v1"
CAPABILITY_SCORE_SCHEMA_V1 = "hardness_np_hard_capability_score_v1"
CAPABILITY_MANIFEST_SCHEMA_V2 = "hardness_np_hard_capability_manifest_v2"
CAPABILITY_SUITE_SCHEMA_V2 = "hardness_np_hard_capability_suite_v2"
CAPABILITY_ORACLE_SCHEMA_V2 = "hardness_np_hard_capability_oracle_v2"
CAPABILITY_RUN_SCHEMA_V2 = "hardness_np_hard_capability_run_v2"
CAPABILITY_SCORE_SCHEMA_V2 = "hardness_np_hard_capability_score_v2"
CAPABILITY_ISOLATION_SCHEMA_V1 = "hardness_np_hard_capability_isolation_v1"
CAPABILITY_BENCHMARK_ID_V1 = "np-hard-capability-v1"
CAPABILITY_BENCHMARK_ID_V2 = "np-hard-capability-v2"
# Backwards-compatible public alias used by the frozen H-I v1 tests/builders.
CAPABILITY_BENCHMARK_ID = CAPABILITY_BENCHMARK_ID_V1
CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS = 1200

CAPABILITY_SPLITS = ("dev", "validation", "heldout", "frontier")
CAPABILITY_SPLIT_COUNTS = {
    "dev": 8,
    "validation": 8,
    "heldout": 16,
    "frontier": 2,
}
CAPABILITY_FAMILIES = frozenset(
    {"graph", "numeric", "set-system", "sat-csp", "other"}
)
PUBLIC_CASE_FIELDS = frozenset(
    {"case_id", "module", "problem", "family", "budget_profile"}
)
PUBLIC_ORACLE_KEYS = frozenset(
    {
        "answer",
        "authoring_kind",
        "blocker_bucket",
        "canonical_identity",
        "difficulty",
        "difficulty_level",
        "disposition",
        "expected",
        "expected_failure_code",
        "expected_failure_codes",
        "expected_public_status",
        "expected_status",
        "failure_code",
        "gap_count",
        "gap_nodes",
        "gold",
        "gold_route",
        "hint",
        "hub",
        "level",
        "oracle",
        "outcome_class",
        "requires_model",
        "required_authoring_motif",
        "route",
        "route_length",
        "scored",
        "solution",
        "task_class",
        "terminal_node_id",
        "final_program_node_id",
        "tier",
        "validation_mode",
    }
)
ORACLE_REQUIRED_CASE_FIELDS = frozenset(
    {
        "case_id",
        "tier",
        "outcome_class",
        "canonical_identity",
        "level",
        "scored",
        "requires_model",
        "expected_public_status",
        "expected_failure_codes",
        "route_length",
    }
)
ORACLE_REQUIRED_CASE_FIELDS_V2 = ORACLE_REQUIRED_CASE_FIELDS | {
    "split",
    "blocker_bucket",
}
REQUIRED_AUTHORING_MOTIF_FIELDS = frozenset(
    {"task_class", "nodes", "terminal_node_id", "final_program_node_id"}
)
REQUIRED_AUTHORING_MOTIF_NODE_FIELDS = frozenset(
    {"node_id", "capability", "depends_on"}
)
CAPABILITY_TIERS = frozenset(
    {"C0-existing", "C0-authoring", "C0-safety", "F0-frontier"}
)
OUTCOME_CLASS_ALIASES = {
    "existing": "existing_route",
    "existing-route": "existing_route",
    "existing_route": "existing_route",
    "authoring": "first_authoring",
    "first-authoring": "first_authoring",
    "first_authoring": "first_authoring",
    "safety": "safety",
    "frontier": "frontier",
}
TIER_OUTCOME_CLASSES = {
    "C0-existing": "existing_route",
    "C0-authoring": "first_authoring",
    "C0-safety": "safety",
    "F0-frontier": "frontier",
}
NAMED_BUDGET_PROFILES: Mapping[str, Mapping[str, int | None]] = {
    "formal-default": {
        "attempt_budget": 4,
        "call_budget": None,
        "lean_timeout_seconds": 600,
    },
    "frontier-default": {
        "attempt_budget": 4,
        "call_budget": None,
        "lean_timeout_seconds": 600,
    },
}
MANIFEST_BUDGET_PROFILES = {
    name: {
        **profile,
        "call_budget": (
            "typed-dag-auto" if profile["call_budget"] is None else profile["call_budget"]
        ),
    }
    for name, profile in NAMED_BUDGET_PROFILES.items()
}
MODEL_PROFILE_FIELDS = frozenset(
    {
        "provider",
        "base_url",
        "model",
        "timeout_seconds",
        "temperature",
        "max_tokens",
        "max_retries",
        "reasoning_effort",
    }
)
FORMAL_PUBLIC_PROFILE = {
    "provider": FORMAL_PROVIDER,
    "base_url": FORMAL_BASE_URL,
    "model": FORMAL_MODEL,
    "timeout_seconds": FORMAL_TIMEOUT_SECONDS,
    "temperature": FORMAL_TEMPERATURE,
    "max_tokens": FORMAL_MAX_TOKENS,
    "max_retries": 0,
    "reasoning_effort": FORMAL_REASONING_EFFORT,
}
LEGACY_FORMAL_PUBLIC_PROFILE = {
    "provider": "DeepSeek",
    "base_url": "https://api.deepseek.com",
    "model": "deepseek-v4-flash",
    "timeout_seconds": 300,
    "temperature": 0.0,
    "max_tokens": 16_000,
    "max_retries": 0,
    "reasoning_effort": "low",
}
MANIFEST_FIELDS_V1 = frozenset(
    {
        "schema_version",
        "benchmark_id",
        "objective",
        "final_lean_type",
        "budget_profiles",
        "split_policy",
        "reserve_policy",
        "public_suite_case_fields",
        "forbidden_runner_paths",
        "suites",
        "oracle",
        "scope_policy",
        "target_matrix",
        "required_model_profile",
    }
)
MANIFEST_FIELDS_V2 = MANIFEST_FIELDS_V1 | {"contract_counts"}
CONTRACT_COUNT_FIELDS = frozenset(
    {
        "case_count",
        "unique_identity_count",
        "split_counts",
        "expected_case_buckets",
        "blocker_bucket_counts",
    }
)
EXPECTED_CASE_BUCKET_FIELDS = frozenset(
    {"split", "tier", "outcome_class", "scored", "count"}
)
BLOCKER_BUCKET_RE = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")
FROZEN_SPLIT_POLICY = {
    "counts": dict(CAPABILITY_SPLIT_COUNTS),
    "canonical_identity_disjoint": True,
    "family_heldout": ["other"],
    "capability_node_heldout": ["new-gadget", "polynomial-bound"],
}
FROZEN_RESERVE_POLICY = {
    "promote_threshold": 0.9,
    "promote_consecutive_versions": 2,
    "intermediate_case_threshold": 0.1,
}
FROZEN_FORBIDDEN_RUNNER_PATHS = frozenset(
    {
        "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        "Benchmark/Hardness/Evaluation",
        "problems.7z",
        "problems",
        "problems.json",
        "problems_clean.json",
    }
)
FROZEN_FORBIDDEN_RUNNER_PATHS_V1 = frozenset(
    {
        "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        "Evaluation",
        "problems.7z",
        "problems",
        "problems.json",
        "problems_clean.json",
    }
)
CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*\Z")
DECLARATION_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"
)
LEVEL_RE = re.compile(r"L[0-6](?:(?:-|/)(?:L)?[0-6]|-high)?\Z")
SHA256_RE = re.compile(r"(?:sha256:)?[0-9a-f]{64}\Z")
FORBIDDEN_ISOLATION_NAMES = frozenset(
    {
        "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        "problems.7z",
        "problems.json",
        "problems_clean.json",
    }
)
FORBIDDEN_ISOLATION_COMPONENTS = frozenset(
    {"Evaluation", "Oracles", "Gold", "GoldProofs", "HiddenTargets", "problems"}
)
RUN_CASE_FIELDS = frozenset(
    {
        "case_id",
        "suite_id",
        "split",
        "module",
        "problem",
        "family",
        "budget_profile",
        "canonical_identity_id",
        "canonical_problem",
        "canonical_module",
        "output_dir",
        "wall_duration_seconds",
        "internal_status",
        "public_status",
        "failure_code",
        "model_calls",
        "token_usage",
        "first_attempt_verified",
        "protocol_valid",
        "result_file",
        "result_file_sha256",
        "raw_result",
        "evidence_sha256",
    }
)


class NPHardCapabilityError(ValueError):
    """Stable fail-closed error for capability benchmark contracts."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardCapabilityError(code, message)


def _exact_keys(value: Mapping[str, Any], expected: set[str] | frozenset[str], *, label: str) -> None:
    actual = set(value)
    if actual != set(expected):
        _fail(
            "invalid_capability_schema",
            f"{label} keys drifted; missing={sorted(set(expected) - actual)!r}, "
            f"extra={sorted(actual - set(expected))!r}",
        )


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        _fail("capability_file_missing", f"{label} is missing: {path}")
        raise AssertionError from error
    except json.JSONDecodeError as error:
        _fail(
            "invalid_capability_json",
            f"{label} is invalid JSON at {error.lineno}:{error.colno}",
        )
        raise AssertionError from error
    if not isinstance(value, dict):
        _fail("invalid_capability_schema", f"{label} must be an object")
    return value


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _tagged_sha256(path: Path) -> str:
    return "sha256:" + sha256_file(path)


def _normalize_sha256(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not SHA256_RE.fullmatch(value):
        _fail("invalid_capability_schema", f"{label} must be a SHA-256 digest")
    return value if value.startswith("sha256:") else "sha256:" + value


def _verify_sha256(path: Path, expected: str, *, label: str) -> None:
    resolved = _relocate_content_addressed(path, expected)
    actual = _tagged_sha256(resolved)
    if actual != expected:
        _fail(
            "capability_hash_mismatch",
            f"{label} hash mismatch; expected={expected}, actual={actual}",
        )


def _relocate_content_addressed(path: Path, expected: str) -> Path:
    """Resolve a frozen reference whose physical file moved after the migration.

    Historical manifests are content-addressed evidence and cannot be edited.
    When the recorded path is absent, the recorded digest is the authority:
    a bounded repository scan locates the unique file with that exact digest.
    """

    if path.is_file():
        return path
    try:
        repository_root = _repository_root(path)
    except ValueError:
        return path
    scan_roots = tuple(
        candidate
        for candidate in (
            repository_root / "Gate",
            repository_root / "Evaluation",
            repository_root / "Archive",
            repository_root / "Benchmark/Hardness",
        )
        if candidate.is_dir()
    )
    for candidate in scan_roots:
        for nested in candidate.rglob("*"):
            if not nested.is_file() or nested.suffix not in {".json", ".lean"}:
                continue
            try:
                if _tagged_sha256(nested) == expected:
                    return nested
            except OSError:
                continue
    return path


def _repository_root(path: Path) -> Path:
    for parent in (path.parent, *path.parents):
        if (parent / "Lean").is_dir() and (parent / "Benchmark/Hardness").is_dir():
            return parent
    raise ValueError(f"no repository root above {path}")


def _relative_reference(root: Path, base: Path, value: Any, *, label: str) -> Path:
    if not isinstance(value, str) or not value.strip():
        _fail("invalid_capability_schema", f"{label}.file must be a non-empty string")
    relative = Path(value)
    if relative.is_absolute() or ".." in relative.parts:
        _fail("capability_path_escape", f"{label}.file is not repository-relative")
    # Manifest paths are repository-relative so the same content-addressed
    # manifest has identical meaning regardless of its own directory.
    path = (root / relative).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError:
        _fail("capability_path_escape", f"{label}.file escaped the repository")
    return path


@dataclass(frozen=True)
class CapabilityFileReference:
    file: str
    path: Path
    sha256: str
    runner_access: str | None = None


@dataclass(frozen=True)
class CapabilityContractCounts:
    """Manifest-frozen denominator and scorer bucket allocation.

    The public runner may see only aggregate counts.  Per-case tier, outcome,
    scoreability, and blocker assignments remain exclusively in the oracle.
    """

    case_count: int
    unique_identity_count: int
    split_counts: Mapping[str, int]
    expected_case_buckets: Mapping[tuple[str, str, str, bool], int]
    blocker_bucket_counts: Mapping[str, int]

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "case_count": self.case_count,
            "unique_identity_count": self.unique_identity_count,
            "split_counts": dict(self.split_counts),
            "expected_case_buckets": [
                {
                    "split": split,
                    "tier": tier,
                    "outcome_class": outcome_class,
                    "scored": scored,
                    "count": count,
                }
                for (split, tier, outcome_class, scored), count in sorted(
                    self.expected_case_buckets.items()
                )
            ],
            "blocker_bucket_counts": dict(sorted(self.blocker_bucket_counts.items())),
        }


@dataclass(frozen=True)
class CapabilityBudgetProfile:
    name: str | None
    attempt_budget: int
    call_budget: int | None
    lean_timeout_seconds: int

    def to_public_value(self) -> str | dict[str, int | None]:
        if self.name is not None:
            return self.name
        return {
            "attempt_budget": self.attempt_budget,
            "call_budget": self.call_budget,
            "lean_timeout_seconds": self.lean_timeout_seconds,
        }


@dataclass(frozen=True)
class CapabilityCase:
    case_id: str
    module: str
    problem: str
    family: str
    budget_profile: CapabilityBudgetProfile
    split: str
    suite_id: str


@dataclass(frozen=True)
class CapabilitySuite:
    suite_id: str
    split: str
    cases: tuple[CapabilityCase, ...]
    path: Path


@dataclass(frozen=True)
class CapabilityManifest:
    path: Path
    schema_version: str
    suite_schema_version: str
    oracle_schema_version: str
    run_schema_version: str
    score_schema_version: str
    benchmark_id: str
    suites: Mapping[str, CapabilityFileReference]
    oracle: CapabilityFileReference
    scope_policy: CapabilityFileReference
    target_matrix: CapabilityFileReference
    required_model_profile: Mapping[str, Any]
    objective: str
    final_lean_type: str
    budget_profiles: Mapping[str, Mapping[str, Any]]
    split_policy: Mapping[str, Any]
    reserve_policy: Mapping[str, Any]
    forbidden_runner_paths: tuple[str, ...]
    contract_counts: CapabilityContractCounts


@dataclass(frozen=True)
class CapabilityBundle:
    root: Path
    manifest: CapabilityManifest
    suites: Mapping[str, CapabilitySuite]
    target_matrix: Mapping[str, Any]
    identity_by_declaration: Mapping[str, Mapping[str, Any]]
    case_identity: Mapping[str, Mapping[str, Any]]

    @property
    def cases(self) -> tuple[CapabilityCase, ...]:
        return tuple(
            case
            for split in CAPABILITY_SPLITS
            for case in self.suites[split].cases
        )


@dataclass(frozen=True)
class CapabilityOracleCase:
    case_id: str
    tier: str
    outcome_class: str
    canonical_identity: str
    level: str
    scored: bool
    requires_model: bool
    expected_public_status: str
    expected_failure_codes: tuple[str, ...]
    route_length: int | None
    metadata: Mapping[str, Any]
    required_authoring_motif: Mapping[str, Any] | None = None
    blocker_bucket: str | None = None


def _normalize_required_authoring_motif(
    value: Any,
    *,
    label: str,
    error_code: str = "invalid_capability_oracle",
) -> dict[str, Any]:
    """Validate and canonicalize one scorer-only authored DAG motif."""

    if not isinstance(value, Mapping):
        _fail(error_code, f"{label} must be an object")
    actual = set(value)
    if actual != set(REQUIRED_AUTHORING_MOTIF_FIELDS):
        _fail(
            error_code,
            f"{label} keys drifted; "
            f"missing={sorted(set(REQUIRED_AUTHORING_MOTIF_FIELDS) - actual)!r}, "
            f"extra={sorted(actual - set(REQUIRED_AUTHORING_MOTIF_FIELDS))!r}",
        )
    task_class = value["task_class"]
    if (
        not isinstance(task_class, str)
        or task_class not in NP_HARD_AUTHORING_TASK_CLASSES_V2
    ):
        _fail(error_code, f"{label}.task_class is invalid")
    nodes_value = value["nodes"]
    if not isinstance(nodes_value, list) or not nodes_value:
        _fail(error_code, f"{label}.nodes must be a non-empty list")
    nodes: list[dict[str, Any]] = []
    prior: set[str] = set()
    for index, raw_node in enumerate(nodes_value):
        node_label = f"{label}.nodes[{index}]"
        if not isinstance(raw_node, Mapping):
            _fail(error_code, f"{node_label} must be an object")
        node_actual = set(raw_node)
        if node_actual != set(REQUIRED_AUTHORING_MOTIF_NODE_FIELDS):
            _fail(
                error_code,
                f"{node_label} keys drifted; "
                f"missing={sorted(set(REQUIRED_AUTHORING_MOTIF_NODE_FIELDS) - node_actual)!r}, "
                f"extra={sorted(node_actual - set(REQUIRED_AUTHORING_MOTIF_NODE_FIELDS))!r}",
            )
        node_id = raw_node["node_id"]
        capability = raw_node["capability"]
        depends_on = raw_node["depends_on"]
        if not isinstance(node_id, str) or not node_id or node_id in prior:
            _fail(error_code, f"{node_label}.node_id is invalid or duplicated")
        if not isinstance(capability, str) or not capability:
            _fail(error_code, f"{node_label}.capability is invalid")
        if (
            not isinstance(depends_on, list)
            or not all(isinstance(item, str) and item for item in depends_on)
            or len(depends_on) != len(set(depends_on))
            or any(item not in prior for item in depends_on)
        ):
            _fail(
                error_code,
                f"{node_label}.depends_on is invalid or not topologically ordered",
            )
        nodes.append(
            {
                "node_id": node_id,
                "capability": capability,
                "depends_on": list(depends_on),
            }
        )
        prior.add(node_id)
    terminal_node_id = value["terminal_node_id"]
    final_program_node_id = value["final_program_node_id"]
    if not isinstance(terminal_node_id, str) or terminal_node_id not in prior:
        _fail(error_code, f"{label}.terminal_node_id is invalid")
    if final_program_node_id is not None and (
        not isinstance(final_program_node_id, str)
        or final_program_node_id not in prior
    ):
        _fail(error_code, f"{label}.final_program_node_id is invalid")
    depended_on = {
        dependency for node in nodes for dependency in node["depends_on"]
    }
    if prior - depended_on != {terminal_node_id}:
        _fail(error_code, f"{label} must have exactly its declared terminal sink")
    return {
        "task_class": task_class,
        "nodes": nodes,
        "terminal_node_id": terminal_node_id,
        "final_program_node_id": final_program_node_id,
    }


def _authoring_task_motif(value: Any) -> tuple[dict[str, Any], NPHardAuthoringTaskV2]:
    """Parse a content-addressed authored task and retain only its frozen motif."""

    if not isinstance(value, Mapping):
        _fail("candidate_dependency_stale", "capability DAG is missing or invalid")
    try:
        task = NPHardAuthoringTaskV2.from_dict(value)
    except NPHardAuthoringContractError as error:
        _fail(
            "candidate_dependency_stale",
            f"capability DAG failed its typed contract: {error.code}",
        )
    motif = {
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
    }
    return motif, task


def _parse_file_reference(
    *,
    root: Path,
    base: Path,
    value: Any,
    label: str,
    runner_access: bool = False,
) -> CapabilityFileReference:
    if not isinstance(value, Mapping):
        _fail("invalid_capability_schema", f"{label} must be an object")
    expected = {"file", "sha256", "runner_access"} if runner_access else {"file", "sha256"}
    _exact_keys(value, expected, label=label)
    path = _relative_reference(root, base, value["file"], label=label)
    access = value.get("runner_access")
    if runner_access and access != "forbidden":
        _fail("oracle_leakage", "capability oracle must forbid runner access")
    return CapabilityFileReference(
        file=str(value["file"]),
        path=path,
        sha256=_normalize_sha256(value["sha256"], label=f"{label}.sha256"),
        runner_access=(str(access) if access is not None else None),
    )


def _validate_required_model_profile(
    value: Any, *, schema_version: str
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        _fail("invalid_capability_schema", "required_model_profile must be an object")
    _exact_keys(value, MODEL_PROFILE_FIELDS, label="required_model_profile")
    normalized = dict(value)
    expected = (
        LEGACY_FORMAL_PUBLIC_PROFILE
        if schema_version == CAPABILITY_MANIFEST_SCHEMA_V1
        else FORMAL_PUBLIC_PROFILE
    )
    if normalized != expected:
        _fail(
            "qualification_model_profile_mismatch",
            "capability manifest does not freeze the accepted DeepSeek V4 Flash profile",
        )
    return normalized


def _schema_contract(schema_version: str) -> dict[str, str]:
    contracts = {
        CAPABILITY_MANIFEST_SCHEMA_V1: {
            "benchmark_id": CAPABILITY_BENCHMARK_ID_V1,
            "suite_schema_version": CAPABILITY_SUITE_SCHEMA_V1,
            "oracle_schema_version": CAPABILITY_ORACLE_SCHEMA_V1,
            "run_schema_version": CAPABILITY_RUN_SCHEMA_V1,
            "score_schema_version": CAPABILITY_SCORE_SCHEMA_V1,
        },
        CAPABILITY_MANIFEST_SCHEMA_V2: {
            "benchmark_id": CAPABILITY_BENCHMARK_ID_V2,
            "suite_schema_version": CAPABILITY_SUITE_SCHEMA_V2,
            "oracle_schema_version": CAPABILITY_ORACLE_SCHEMA_V2,
            "run_schema_version": CAPABILITY_RUN_SCHEMA_V2,
            "score_schema_version": CAPABILITY_SCORE_SCHEMA_V2,
        },
    }
    contract = contracts.get(schema_version)
    if contract is None:
        _fail("invalid_capability_schema", "unsupported capability manifest schema")
    return contract


def _v1_contract_counts() -> CapabilityContractCounts:
    expected_buckets = {
        ("dev", "C0-existing", "existing_route", True): 4,
        ("dev", "C0-authoring", "first_authoring", True): 2,
        ("dev", "C0-safety", "safety", True): 2,
        ("validation", "C0-existing", "existing_route", True): 4,
        ("validation", "C0-authoring", "first_authoring", True): 2,
        ("validation", "C0-safety", "safety", True): 2,
        ("heldout", "C0-existing", "existing_route", True): 4,
        ("heldout", "C0-authoring", "first_authoring", True): 8,
        ("heldout", "C0-safety", "safety", True): 4,
        ("frontier", "F0-frontier", "frontier", False): 2,
    }
    return CapabilityContractCounts(
        case_count=sum(CAPABILITY_SPLIT_COUNTS.values()),
        unique_identity_count=sum(CAPABILITY_SPLIT_COUNTS.values()),
        split_counts=dict(CAPABILITY_SPLIT_COUNTS),
        expected_case_buckets=expected_buckets,
        blocker_bucket_counts={},
    )


def _positive_contract_count(value: Any, *, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        _fail("invalid_capability_schema", f"{label} must be a positive integer")
    return value


def _parse_contract_counts(value: Any) -> CapabilityContractCounts:
    if not isinstance(value, Mapping):
        _fail("invalid_capability_schema", "contract_counts must be an object")
    _exact_keys(value, CONTRACT_COUNT_FIELDS, label="contract_counts")
    case_count = _positive_contract_count(
        value["case_count"], label="contract_counts.case_count"
    )
    unique_identity_count = _positive_contract_count(
        value["unique_identity_count"],
        label="contract_counts.unique_identity_count",
    )
    if unique_identity_count != case_count:
        _fail(
            "invalid_capability_schema",
            "capability contract must assign one unique identity per case",
        )

    split_counts_value = value["split_counts"]
    if not isinstance(split_counts_value, Mapping) or set(split_counts_value) != set(
        CAPABILITY_SPLITS
    ):
        _fail(
            "invalid_capability_schema",
            f"contract split_counts must be exactly {list(CAPABILITY_SPLITS)!r}",
        )
    split_counts = {
        split: _positive_contract_count(
            split_counts_value[split],
            label=f"contract_counts.split_counts.{split}",
        )
        for split in CAPABILITY_SPLITS
    }
    if sum(split_counts.values()) != case_count:
        _fail(
            "invalid_capability_schema",
            "contract split counts do not sum to case_count",
        )

    buckets_value = value["expected_case_buckets"]
    if not isinstance(buckets_value, list) or not buckets_value:
        _fail(
            "invalid_capability_schema",
            "contract expected_case_buckets must be a non-empty list",
        )
    expected_case_buckets: dict[tuple[str, str, str, bool], int] = {}
    observed_split_counts = {split: 0 for split in CAPABILITY_SPLITS}
    for index, raw in enumerate(buckets_value):
        label = f"contract_counts.expected_case_buckets[{index}]"
        if not isinstance(raw, Mapping):
            _fail("invalid_capability_schema", f"{label} must be an object")
        _exact_keys(raw, EXPECTED_CASE_BUCKET_FIELDS, label=label)
        split = raw["split"]
        tier = raw["tier"]
        outcome_raw = raw["outcome_class"]
        scored = raw["scored"]
        if split not in CAPABILITY_SPLITS:
            _fail("invalid_capability_schema", f"{label}.split is invalid")
        if tier not in CAPABILITY_TIERS:
            _fail("invalid_capability_schema", f"{label}.tier is invalid")
        if not isinstance(outcome_raw, str) or outcome_raw not in OUTCOME_CLASS_ALIASES:
            _fail("invalid_capability_schema", f"{label}.outcome_class is invalid")
        outcome_class = OUTCOME_CLASS_ALIASES[outcome_raw]
        if TIER_OUTCOME_CLASSES[tier] != outcome_class:
            _fail("invalid_capability_schema", f"{label} tier/outcome drifted")
        if not isinstance(scored, bool):
            _fail("invalid_capability_schema", f"{label}.scored must be boolean")
        if (tier == "F0-frontier") == scored:
            _fail(
                "invalid_capability_schema",
                f"{label} must score C0 and leave F0 unscored",
            )
        count = _positive_contract_count(raw["count"], label=f"{label}.count")
        key = (str(split), str(tier), outcome_class, scored)
        if key in expected_case_buckets:
            _fail("invalid_capability_schema", f"{label} repeats a contract bucket")
        expected_case_buckets[key] = count
        observed_split_counts[str(split)] += count
    if observed_split_counts != split_counts:
        _fail(
            "invalid_capability_schema",
            "contract case buckets do not match split_counts",
        )
    if sum(expected_case_buckets.values()) != case_count:
        _fail(
            "invalid_capability_schema",
            "contract case buckets do not sum to case_count",
        )

    blocker_counts_value = value["blocker_bucket_counts"]
    if not isinstance(blocker_counts_value, Mapping):
        _fail(
            "invalid_capability_schema",
            "contract blocker_bucket_counts must be an object",
        )
    blocker_bucket_counts: dict[str, int] = {}
    for raw_name, raw_count in blocker_counts_value.items():
        if not isinstance(raw_name, str) or not BLOCKER_BUCKET_RE.fullmatch(raw_name):
            _fail(
                "invalid_capability_schema",
                "contract blocker bucket name is invalid",
            )
        blocker_bucket_counts[raw_name] = _positive_contract_count(
            raw_count,
            label=f"contract_counts.blocker_bucket_counts.{raw_name}",
        )
    unscored_count = sum(
        count
        for bucket, count in expected_case_buckets.items()
        if not bucket[3]
    )
    if sum(blocker_bucket_counts.values()) != unscored_count:
        _fail(
            "invalid_capability_schema",
            "v2 blocker bucket counts must exactly partition unscored cases",
        )
    return CapabilityContractCounts(
        case_count=case_count,
        unique_identity_count=unique_identity_count,
        split_counts=split_counts,
        expected_case_buckets=expected_case_buckets,
        blocker_bucket_counts=blocker_bucket_counts,
    )


def load_capability_manifest(
    path: Path,
    *,
    root: Path,
    verify_oracle: bool = False,
) -> CapabilityManifest:
    """Load the public manifest without opening the oracle by default."""

    root = root.resolve()
    path = path.resolve()
    value = _read_json(path, label="capability manifest")
    schema_version = value.get("schema_version")
    if not isinstance(schema_version, str):
        _fail("invalid_capability_schema", "capability manifest lacks schema_version")
    schema = _schema_contract(schema_version)
    manifest_fields = (
        MANIFEST_FIELDS_V1
        if schema_version == CAPABILITY_MANIFEST_SCHEMA_V1
        else MANIFEST_FIELDS_V2
    )
    _exact_keys(value, manifest_fields, label="capability manifest")
    if value["benchmark_id"] != schema["benchmark_id"]:
        _fail("invalid_capability_schema", "unexpected capability benchmark_id")
    contract_counts = (
        _v1_contract_counts()
        if schema_version == CAPABILITY_MANIFEST_SCHEMA_V1
        else _parse_contract_counts(value["contract_counts"])
    )
    if value["objective"] != "target-hardness":
        _fail("invalid_capability_schema", "capability objective must be target-hardness")
    if value["final_lean_type"] != "ComplexityReduction.Certificate.NativeTMNPHard input":
        _fail("invalid_capability_schema", "capability final Lean type drifted")
    if value["budget_profiles"] != MANIFEST_BUDGET_PROFILES:
        _fail("invalid_capability_schema", "capability budget profiles drifted")
    expected_split_policy = deepcopy(FROZEN_SPLIT_POLICY)
    expected_split_policy["counts"] = dict(contract_counts.split_counts)
    if value["split_policy"] != expected_split_policy:
        _fail("invalid_capability_schema", "capability split policy drifted")
    if value["reserve_policy"] != FROZEN_RESERVE_POLICY:
        _fail("invalid_capability_schema", "capability reserve policy drifted")
    if value["public_suite_case_fields"] != [
        "case_id",
        "module",
        "problem",
        "family",
        "budget_profile",
    ]:
        _fail("invalid_capability_schema", "public suite field allowlist drifted")
    forbidden = value["forbidden_runner_paths"]
    expected_forbidden = (
        FROZEN_FORBIDDEN_RUNNER_PATHS_V1
        if schema_version == CAPABILITY_MANIFEST_SCHEMA_V1
        else FROZEN_FORBIDDEN_RUNNER_PATHS
    )
    if not isinstance(forbidden, list) or set(forbidden) != set(expected_forbidden):
        _fail("invalid_capability_schema", "forbidden runner path policy drifted")
    suites_value = value["suites"]
    if not isinstance(suites_value, Mapping) or set(suites_value) != set(CAPABILITY_SPLITS):
        _fail(
            "invalid_capability_schema",
            f"manifest suites must be exactly {list(CAPABILITY_SPLITS)!r}",
        )
    suites = {
        split: _parse_file_reference(
            root=root,
            base=path.parent,
            value=suites_value[split],
            label=f"suites.{split}",
        )
        for split in CAPABILITY_SPLITS
    }
    oracle = _parse_file_reference(
        root=root,
        base=path.parent,
        value=value["oracle"],
        label="oracle",
        runner_access=True,
    )
    if "Evaluation" not in oracle.path.parts:
        _fail("invalid_capability_schema", "oracle must live under Evaluation")
    target_matrix = _parse_file_reference(
        root=root,
        base=path.parent,
        value=value["target_matrix"],
        label="target_matrix",
    )
    scope_policy = _parse_file_reference(
        root=root,
        base=path.parent,
        value=value["scope_policy"],
        label="scope_policy",
    )
    for split, reference in suites.items():
        _verify_sha256(reference.path, reference.sha256, label=f"suite {split}")
    _verify_sha256(target_matrix.path, target_matrix.sha256, label="target matrix")
    _verify_sha256(scope_policy.path, scope_policy.sha256, label="scope policy")
    if verify_oracle:
        _verify_sha256(oracle.path, oracle.sha256, label="capability oracle")
    return CapabilityManifest(
        path=path,
        schema_version=schema_version,
        suite_schema_version=schema["suite_schema_version"],
        oracle_schema_version=schema["oracle_schema_version"],
        run_schema_version=schema["run_schema_version"],
        score_schema_version=schema["score_schema_version"],
        benchmark_id=str(value["benchmark_id"]),
        suites=suites,
        oracle=oracle,
        scope_policy=scope_policy,
        target_matrix=target_matrix,
        required_model_profile=_validate_required_model_profile(
            value["required_model_profile"], schema_version=schema_version
        ),
        objective=str(value["objective"]),
        final_lean_type=str(value["final_lean_type"]),
        budget_profiles=deepcopy(value["budget_profiles"]),
        split_policy=deepcopy(value["split_policy"]),
        reserve_policy=deepcopy(value["reserve_policy"]),
        forbidden_runner_paths=tuple(str(item) for item in forbidden),
        contract_counts=contract_counts,
    )


def _contains_oracle_metadata(value: Any) -> bool:
    if isinstance(value, Mapping):
        return any(
            str(key).lower() in PUBLIC_ORACLE_KEYS
            or _contains_oracle_metadata(item)
            for key, item in value.items()
        )
    if isinstance(value, (list, tuple)):
        return any(_contains_oracle_metadata(item) for item in value)
    if isinstance(value, str):
        lowered = value.lower()
        return any(
            marker in lowered
            for marker in (
                "/evaluation/",
                "\\evaluation\\",
                "problems.7z",
                "problems_clean.json",
                "active_agent_improvement_plan.md",
                ".oracles.",
                ".gold.",
                "goldproof",
                "hiddentarget",
            )
        )
    return False


def _parse_budget_profile(value: Any, *, case_id: str) -> CapabilityBudgetProfile:
    if isinstance(value, str):
        profile = NAMED_BUDGET_PROFILES.get(value)
        if profile is None:
            _fail(
                "invalid_capability_schema",
                f"case {case_id} uses unknown budget profile {value!r}",
            )
        return CapabilityBudgetProfile(name=value, **profile)
    if not isinstance(value, Mapping):
        _fail(
            "invalid_capability_schema",
            f"case {case_id} budget_profile must be a name or object",
        )
    _exact_keys(
        value,
        {"attempt_budget", "call_budget", "lean_timeout_seconds"},
        label=f"case {case_id}.budget_profile",
    )
    attempt = value["attempt_budget"]
    call_budget = value["call_budget"]
    lean_timeout = value["lean_timeout_seconds"]
    if isinstance(attempt, bool) or not isinstance(attempt, int) or not 1 <= attempt <= 4:
        _fail("invalid_capability_schema", f"case {case_id} attempt budget is invalid")
    if (
        call_budget is not None
        and (
            isinstance(call_budget, bool)
            or not isinstance(call_budget, int)
            or not 0 <= call_budget <= 64
        )
    ):
        _fail("invalid_capability_schema", f"case {case_id} call budget is invalid")
    if (
        isinstance(lean_timeout, bool)
        or not isinstance(lean_timeout, int)
        or not 1 <= lean_timeout <= 3600
    ):
        _fail("invalid_capability_schema", f"case {case_id} Lean timeout is invalid")
    return CapabilityBudgetProfile(
        name=None,
        attempt_budget=attempt,
        call_budget=call_budget,
        lean_timeout_seconds=lean_timeout,
    )


def _parse_public_case(
    value: Any, *, split: str, suite_id: str
) -> CapabilityCase:
    if not isinstance(value, Mapping):
        _fail("invalid_capability_schema", f"{suite_id} case must be an object")
    extra = set(value) - set(PUBLIC_CASE_FIELDS)
    if extra and (
        any(str(key).lower() in PUBLIC_ORACLE_KEYS for key in extra)
        or _contains_oracle_metadata({key: value[key] for key in extra})
    ):
        _fail(
            "oracle_field_in_public_suite",
            f"public case contains scorer-only fields: {sorted(extra)!r}",
        )
    _exact_keys(value, PUBLIC_CASE_FIELDS, label=f"{suite_id} case")
    if _contains_oracle_metadata(value):
        _fail("oracle_field_in_public_suite", "public case leaks scorer/oracle material")
    case_id = value["case_id"]
    module = value["module"]
    problem = value["problem"]
    family = value["family"]
    if not isinstance(case_id, str) or not CASE_ID_RE.fullmatch(case_id):
        _fail("invalid_capability_schema", "capability case_id is invalid")
    if (
        not isinstance(module, str)
        or not MODULE_RE.fullmatch(module)
        or not module.startswith("ComplexityReduction.")
    ):
        _fail(
            "fixture_in_capability_suite",
            f"case {case_id} is outside public ComplexityReduction scope",
        )
    if not isinstance(problem, str) or not DECLARATION_RE.fullmatch(problem):
        _fail("invalid_capability_schema", f"case {case_id} problem is invalid")
    if family not in CAPABILITY_FAMILIES:
        _fail("invalid_capability_schema", f"case {case_id} family is invalid")
    return CapabilityCase(
        case_id=case_id,
        module=module,
        problem=problem,
        family=family,
        budget_profile=_parse_budget_profile(value["budget_profile"], case_id=case_id),
        split=split,
        suite_id=suite_id,
    )


def load_capability_suite(
    path: Path,
    *,
    expected_split: str,
    expected_schema_version: str = CAPABILITY_SUITE_SCHEMA_V1,
    expected_count: int | None = None,
) -> CapabilitySuite:
    value = _read_json(path.resolve(), label=f"capability {expected_split} suite")
    _exact_keys(
        value,
        {"schema_version", "suite_id", "split", "cases"},
        label=f"capability {expected_split} suite",
    )
    if expected_schema_version not in {
        CAPABILITY_SUITE_SCHEMA_V1,
        CAPABILITY_SUITE_SCHEMA_V2,
    }:
        _fail("invalid_capability_schema", "unsupported expected suite schema")
    if value["schema_version"] != expected_schema_version:
        _fail("invalid_capability_schema", "unsupported capability suite schema")
    if value["split"] != expected_split:
        _fail("invalid_capability_schema", "capability suite split drifted")
    suite_id = value["suite_id"]
    if not isinstance(suite_id, str) or not CASE_ID_RE.fullmatch(suite_id):
        _fail("invalid_capability_schema", "capability suite_id is invalid")
    cases_value = value["cases"]
    if not isinstance(cases_value, list):
        _fail("invalid_capability_schema", "capability suite cases must be a list")
    cases = tuple(
        _parse_public_case(case, split=expected_split, suite_id=suite_id)
        for case in cases_value
    )
    frozen_count = (
        CAPABILITY_SPLIT_COUNTS[expected_split]
        if expected_count is None
        else expected_count
    )
    if len(cases) != frozen_count:
        _fail(
            "invalid_capability_split_count",
            f"{expected_split} must contain {frozen_count} cases",
        )
    if len({case.case_id for case in cases}) != len(cases):
        _fail("duplicate_capability_case_id", f"{expected_split} repeats a case_id")
    return CapabilitySuite(
        suite_id=suite_id, split=expected_split, cases=cases, path=path.resolve()
    )


def _identity_maps(
    matrix: Mapping[str, Any]
) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]]]:
    identities = matrix.get("identities")
    if not isinstance(identities, list) or not identities:
        _fail("invalid_target_matrix", "target matrix has no identities")
    by_declaration: dict[str, Mapping[str, Any]] = {}
    by_id: dict[str, Mapping[str, Any]] = {}
    for raw in identities:
        if not isinstance(raw, Mapping):
            _fail("invalid_target_matrix", "target matrix identity is invalid")
        identity_id = raw.get("identity_id")
        canonical = raw.get("canonical_declaration")
        members = raw.get("member_declarations")
        if not isinstance(identity_id, str) or not isinstance(canonical, str):
            _fail("invalid_target_matrix", "target matrix identity lacks canonical fields")
        if not isinstance(members, list) or not all(isinstance(item, str) for item in members):
            _fail("invalid_target_matrix", "target matrix member declarations are invalid")
        if identity_id in by_id:
            _fail("duplicate_canonical_identity", "target matrix repeats an identity_id")
        by_id[identity_id] = raw
        for declaration in dict.fromkeys((canonical, *members)):
            previous = by_declaration.get(declaration)
            if previous is not None and previous.get("identity_id") != identity_id:
                _fail(
                    "duplicate_canonical_identity",
                    "one declaration belongs to multiple canonical identities",
                )
            by_declaration[declaration] = raw
    return by_declaration, by_id


def _identity_conflict_code(
    occurrences: Sequence[tuple[str, str, str]]
) -> str | None:
    """Return the stable error for duplicate ``(identity, split, case)`` rows."""

    first: dict[str, tuple[str, str]] = {}
    for identity_id, split, case_id in occurrences:
        previous = first.get(identity_id)
        if previous is None:
            first[identity_id] = (split, case_id)
            continue
        if previous[0] != split:
            return "capability_split_overlap"
        return "duplicate_canonical_identity"
    return None


def _validate_identity_assignments(
    suites: Mapping[str, CapabilitySuite],
    matrix: Mapping[str, Any],
) -> tuple[dict[str, Mapping[str, Any]], dict[str, Mapping[str, Any]]]:
    by_declaration, _ = _identity_maps(matrix)
    case_identity: dict[str, Mapping[str, Any]] = {}
    occurrences: list[tuple[str, str, str]] = []
    seen_case_ids: set[str] = set()
    for split in CAPABILITY_SPLITS:
        suite = suites[split]
        for case in suite.cases:
            if case.case_id in seen_case_ids:
                _fail("duplicate_capability_case_id", "case_id repeats across splits")
            seen_case_ids.add(case.case_id)
            identity = by_declaration.get(case.problem)
            if identity is None:
                _fail(
                    "capability_identity_not_found",
                    f"case {case.case_id} is absent from the canonical target matrix",
                )
            if identity.get("family") != case.family:
                _fail(
                    "capability_family_mismatch",
                    f"case {case.case_id} family differs from its canonical identity",
                )
            canonical = identity.get("canonical_declaration")
            canonical_module = identity.get("canonical_module")
            if case.problem == canonical and case.module != canonical_module:
                _fail(
                    "candidate_wrong_endpoint",
                    f"case {case.case_id} canonical module drifted",
                )
            identity_id = str(identity["identity_id"])
            occurrences.append((identity_id, split, case.case_id))
            case_identity[case.case_id] = identity
    conflict = _identity_conflict_code(occurrences)
    if conflict is not None:
        _fail(conflict, "capability suites repeat a canonical identity")

    development_families = {case.family for case in suites["dev"].cases}
    validation_families = {case.family for case in suites["validation"].cases}
    heldout_families = {case.family for case in suites["heldout"].cases}
    if "other" in development_families or "other" in validation_families:
        _fail(
            "family_heldout_violation",
            "the frozen other family may appear only in heldout/frontier",
        )
    if heldout_families != set(CAPABILITY_FAMILIES):
        _fail(
            "family_heldout_violation",
            "heldout must cover graph/numeric/set-system/sat-csp/other",
        )
    if "other" not in heldout_families:
        _fail("family_heldout_violation", "heldout lacks the frozen other family")
    return by_declaration, case_identity


def load_capability_bundle(
    manifest_path: Path,
    *,
    root: Path,
    verify_oracle: bool = False,
) -> CapabilityBundle:
    manifest = load_capability_manifest(
        manifest_path, root=root, verify_oracle=verify_oracle
    )
    suites = {
        split: load_capability_suite(
            reference.path,
            expected_split=split,
            expected_schema_version=manifest.suite_schema_version,
            expected_count=manifest.contract_counts.split_counts[split],
        )
        for split, reference in manifest.suites.items()
    }
    matrix = load_np_hard_target_matrix(
        _relocate_content_addressed(
            manifest.target_matrix.path, manifest.target_matrix.sha256
        )
    )
    by_declaration, case_identity = _validate_identity_assignments(suites, matrix)
    if len(case_identity) != manifest.contract_counts.case_count:
        _fail(
            "invalid_capability_split_count",
            "loaded capability cases differ from the manifest-frozen denominator",
        )
    if len({str(row["identity_id"]) for row in case_identity.values()}) != (
        manifest.contract_counts.unique_identity_count
    ):
        _fail(
            "duplicate_canonical_identity",
            "loaded capability identities differ from the manifest-frozen denominator",
        )
    return CapabilityBundle(
        root=root.resolve(),
        manifest=manifest,
        suites=suites,
        target_matrix=matrix,
        identity_by_declaration=by_declaration,
        case_identity=case_identity,
    )


def load_capability_oracle(
    path: Path,
    *,
    bundle: CapabilityBundle,
) -> dict[str, CapabilityOracleCase]:
    value = _read_json(path.resolve(), label="capability scorer oracle")
    _exact_keys(
        value,
        {"schema_version", "benchmark_id", "cases"},
        label="capability oracle",
    )
    if value["schema_version"] != bundle.manifest.oracle_schema_version:
        _fail("invalid_capability_oracle", "unsupported capability oracle schema")
    if value["benchmark_id"] != bundle.manifest.benchmark_id:
        _fail("invalid_capability_oracle", "capability oracle benchmark_id drifted")
    cases_value = value["cases"]
    if not isinstance(cases_value, list):
        _fail("invalid_capability_oracle", "capability oracle cases must be a list")
    public_cases = {case.case_id: case for case in bundle.cases}
    result: dict[str, CapabilityOracleCase] = {}
    required_case_fields = (
        ORACLE_REQUIRED_CASE_FIELDS_V2
        if bundle.manifest.oracle_schema_version == CAPABILITY_ORACLE_SCHEMA_V2
        else ORACLE_REQUIRED_CASE_FIELDS
    )
    for raw in cases_value:
        if not isinstance(raw, Mapping):
            _fail("invalid_capability_oracle", "oracle case must be an object")
        missing = required_case_fields - set(raw)
        if missing:
            _fail(
                "invalid_capability_oracle",
                f"oracle case misses fields: {sorted(missing)!r}",
            )
        case_id = raw["case_id"]
        if not isinstance(case_id, str) or case_id not in public_cases:
            _fail("invalid_capability_oracle", "oracle references an unknown case_id")
        if case_id in result:
            _fail("invalid_capability_oracle", "oracle repeats a case_id")
        tier = raw["tier"]
        if tier not in CAPABILITY_TIERS:
            _fail("invalid_capability_oracle", f"case {case_id} tier is invalid")
        outcome_raw = raw["outcome_class"]
        if not isinstance(outcome_raw, str) or outcome_raw not in OUTCOME_CLASS_ALIASES:
            _fail("invalid_capability_oracle", f"case {case_id} outcome_class is invalid")
        outcome_class = OUTCOME_CLASS_ALIASES[outcome_raw]
        if TIER_OUTCOME_CLASSES[tier] != outcome_class:
            _fail("invalid_capability_oracle", f"case {case_id} tier/outcome drifted")
        canonical_identity = raw["canonical_identity"]
        if not isinstance(canonical_identity, str):
            _fail("invalid_capability_oracle", "canonical_identity must be a string")
        identity = bundle.case_identity[case_id]
        if canonical_identity not in {
            identity.get("identity_id"),
            identity.get("canonical_declaration"),
        }:
            _fail(
                "invalid_capability_oracle",
                f"case {case_id} oracle canonical identity drifted",
            )
        level = raw["level"]
        if not isinstance(level, str) or not LEVEL_RE.fullmatch(level):
            _fail("invalid_capability_oracle", f"case {case_id} level is invalid")
        scored = raw["scored"]
        requires_model = raw["requires_model"]
        if not isinstance(scored, bool) or not isinstance(requires_model, bool):
            _fail("invalid_capability_oracle", "oracle booleans are invalid")
        if (tier == "F0-frontier") == scored:
            _fail(
                "invalid_capability_oracle",
                "C0 cases must be scored and F0 cases must be unscored",
            )
        if tier in {"C0-existing", "C0-safety"} and requires_model:
            _fail(
                "invalid_capability_oracle",
                f"case {case_id} existing/safety case cannot require a model",
            )
        if tier == "C0-authoring" and not requires_model:
            _fail(
                "invalid_capability_oracle",
                f"case {case_id} authoring case must require a model",
            )
        expected_status = raw["expected_public_status"]
        if expected_status not in PUBLIC_STATUSES:
            _fail("invalid_capability_oracle", "expected_public_status is invalid")
        failure_codes = raw["expected_failure_codes"]
        if not isinstance(failure_codes, list) or not all(
            isinstance(item, str) and item for item in failure_codes
        ):
            _fail("invalid_capability_oracle", "expected_failure_codes is invalid")
        route_length = raw["route_length"]
        if route_length is not None and (
            isinstance(route_length, bool)
            or not isinstance(route_length, int)
            or route_length < 0
        ):
            _fail("invalid_capability_oracle", "route_length is invalid")
        if tier == "C0-existing" and route_length is None:
            _fail("invalid_capability_oracle", "existing route case lacks route_length")
        public_case = public_cases[case_id]
        expected_split = public_case.split
        if tier == "F0-frontier" and public_case.split != "frontier":
            _fail("invalid_capability_oracle", "F0 case is outside frontier split")
        if tier != "F0-frontier" and public_case.split == "frontier":
            _fail("invalid_capability_oracle", "C0 case is in frontier split")
        if "split" in raw and raw["split"] != expected_split:
            _fail("invalid_capability_oracle", f"case {case_id} split drifted")
        if "family" in raw and raw["family"] != public_case.family:
            _fail("invalid_capability_oracle", f"case {case_id} family drifted")
        blocker_bucket: str | None = None
        if bundle.manifest.oracle_schema_version == CAPABILITY_ORACLE_SCHEMA_V2:
            blocker_raw = raw["blocker_bucket"]
            if blocker_raw is not None and (
                not isinstance(blocker_raw, str)
                or not BLOCKER_BUCKET_RE.fullmatch(blocker_raw)
            ):
                _fail(
                    "invalid_capability_oracle",
                    f"case {case_id} blocker_bucket is invalid",
                )
            blocker_bucket = blocker_raw
            if tier == "F0-frontier":
                if blocker_bucket is None:
                    _fail(
                        "invalid_capability_oracle",
                        f"case {case_id} frontier lacks an explicit blocker bucket",
                    )
                if requires_model:
                    _fail(
                        "invalid_capability_oracle",
                        f"case {case_id} deterministic frontier cannot require a model",
                    )
                if expected_status != "BLOCKED_MISSING_PREREQUISITE":
                    _fail(
                        "invalid_capability_oracle",
                        f"case {case_id} frontier must expect a precise prerequisite blocker",
                    )
                if not failure_codes:
                    _fail(
                        "invalid_capability_oracle",
                        f"case {case_id} frontier lacks a stable failure code",
                    )
            elif blocker_bucket is not None:
                _fail(
                    "invalid_capability_oracle",
                    f"case {case_id} assigns a blocker bucket outside F0",
                )
        motif_raw = raw.get("required_authoring_motif")
        if (
            bundle.manifest.oracle_schema_version != CAPABILITY_ORACLE_SCHEMA_V2
            and motif_raw is not None
        ):
            _fail(
                "invalid_capability_oracle",
                f"historical case {case_id} cannot carry a v2 authoring motif",
            )
        required_authoring_motif = (
            _normalize_required_authoring_motif(
                motif_raw,
                label=f"oracle case {case_id}.required_authoring_motif",
            )
            if motif_raw is not None
            else None
        )
        if required_authoring_motif is not None and tier != "C0-authoring":
            _fail(
                "invalid_capability_oracle",
                f"case {case_id} carries an authoring motif outside C0-authoring",
            )
        result[case_id] = CapabilityOracleCase(
            case_id=case_id,
            tier=tier,
            outcome_class=outcome_class,
            canonical_identity=canonical_identity,
            level=level,
            scored=scored,
            requires_model=requires_model,
            expected_public_status=expected_status,
            expected_failure_codes=tuple(failure_codes),
            route_length=route_length,
            metadata={key: deepcopy(item) for key, item in raw.items()},
            required_authoring_motif=required_authoring_motif,
            blocker_bucket=blocker_bucket,
        )
    if set(result) != set(public_cases):
        _fail(
            "invalid_capability_oracle",
            "oracle and public suites do not contain the same case IDs",
        )
    observed_buckets: dict[tuple[str, str, str, bool], int] = {}
    for case_id, oracle_case in result.items():
        key = (
            public_cases[case_id].split,
            oracle_case.tier,
            oracle_case.outcome_class,
            oracle_case.scored,
        )
        observed_buckets[key] = observed_buckets.get(key, 0) + 1
    if observed_buckets != dict(bundle.manifest.contract_counts.expected_case_buckets):
        _fail("invalid_capability_oracle", "frozen split/outcome allocation drifted")
    observed_blocker_buckets: dict[str, int] = {}
    for oracle_case in result.values():
        if oracle_case.blocker_bucket is None:
            continue
        observed_blocker_buckets[oracle_case.blocker_bucket] = (
            observed_blocker_buckets.get(oracle_case.blocker_bucket, 0) + 1
        )
    if observed_blocker_buckets != dict(
        bundle.manifest.contract_counts.blocker_bucket_counts
    ):
        _fail("invalid_capability_oracle", "frozen blocker bucket allocation drifted")

    # The capability-node policy is held out from development (validation may
    # exercise an intermediate polynomial-bound bridge) and must be observable
    # in heldout.  Keeping the check scorer-side avoids exposing difficulty
    # axes in the public suite or production prompt.
    development_axes: set[str] = set()
    heldout_axes: set[str] = set()
    for case_id, oracle_case in result.items():
        axes = oracle_case.metadata.get("difficulty_axes")
        if not isinstance(axes, list) or not all(isinstance(axis, str) for axis in axes):
            _fail("invalid_capability_oracle", "oracle difficulty_axes are invalid")
        split = public_cases[case_id].split
        if split == "dev":
            development_axes.update(axes)
        elif split == "heldout":
            heldout_axes.update(axes)
    heldout_nodes = set(bundle.manifest.split_policy["capability_node_heldout"])
    if development_axes & heldout_nodes or not heldout_nodes <= heldout_axes:
        _fail("capability_node_heldout_violation", "capability-node heldout policy drifted")
    return result


def _fresh_directory(path: Path, *, label: str) -> None:
    if path.exists() and any(path.iterdir()):
        _fail("capability_output_not_fresh", f"{label} must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _copy_file(source: Path, target: Path) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def _forbidden_isolation_name(name: str) -> bool:
    if name in FORBIDDEN_ISOLATION_NAMES or name in FORBIDDEN_ISOLATION_COMPONENTS:
        return True
    lowered = name.lower()
    if lowered.startswith(
        (
            "active_agent_improvement_plan.md",
            "problems.7z",
            "problems.json",
            "problems_clean.json",
        )
    ):
        return True
    # Preserve the public Lean namespace ``Problems`` while rejecting common
    # lowercase extracted/archive-copy directory names.
    if name.startswith(("Evaluation-", "Evaluation_", "Evaluation.")):
        return True
    return name.startswith(("problems-", "problems_", "problems."))


def _copy_public_lean_tree(source: Path, target: Path) -> None:
    def ignored(_directory: str, names: list[str]) -> set[str]:
        return {
            name
            for name in names
            if _forbidden_isolation_name(name)
            or name in {".DS_Store", "__pycache__"}
        }

    shutil.copytree(source, target, ignore=ignored)


def _isolation_forbidden_paths(root: Path) -> list[str]:
    forbidden: list[str] = []
    for path in root.rglob("*"):
        relative = path.relative_to(root)
        if _forbidden_isolation_name(path.name) or any(
            _forbidden_isolation_name(part) for part in relative.parts
        ):
            forbidden.append(str(relative))
        if path.name.lower().endswith(".7z"):
            forbidden.append(str(relative))
    return sorted(set(forbidden))


def build_capability_isolated_workspace(
    *,
    root: Path,
    destination: Path,
    target_matrix_path: Path,
    scope_policy_path: Path,
) -> dict[str, Any]:
    """Build the public-only filesystem used by the production orchestrator.

    Only third-party Lake packages are linked from the source checkout.  The
    repository's own compiled Benchmark artifacts are not linked, so fixture
    modules cannot be imported from the isolated job.
    """

    root = root.resolve()
    destination = destination.resolve()
    _fresh_directory(destination, label="capability isolation workspace")
    lean_target = destination / "Lean"
    lean_target.mkdir(parents=True, exist_ok=False)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        _copy_file(root / "Lean" / name, lean_target / name)
    _copy_public_lean_tree(
        root / "Lean" / "Reference" / "ComplexityReduction",
        lean_target / "Reference" / "ComplexityReduction",
    )
    source_packages = root / "Lean" / ".lake" / "packages"
    linked_packages = False
    if source_packages.is_dir():
        packages_parent = lean_target / ".lake"
        packages_parent.mkdir(parents=True, exist_ok=True)
        (packages_parent / "packages").symlink_to(source_packages, target_is_directory=True)
        linked_packages = True

    _copy_file(
        root / NP_HARD_INPUT_REGISTRY_PATH,
        destination / NP_HARD_INPUT_REGISTRY_PATH,
    )
    _copy_file(
        target_matrix_path.resolve(),
        destination / NP_HARD_TARGET_MATRIX_PATH,
    )
    _copy_file(
        scope_policy_path.resolve(),
        destination / "agent" / "hardness" / "data" / "np_hard_scope_policy.json",
    )
    forbidden = _isolation_forbidden_paths(destination)
    if forbidden:
        _fail(
            "capability_isolation_leak",
            f"isolated workspace contains forbidden paths: {forbidden!r}",
        )
    copied_files = {
        str(path.relative_to(destination)): _tagged_sha256(path)
        for path in sorted(destination.rglob("*"))
        if path.is_file() and not path.is_symlink()
    }
    manifest = {
        "schema_version": CAPABILITY_ISOLATION_SCHEMA_V1,
        "root": str(destination),
        "public_lean_source_only": True,
        "benchmark_fixture_source_present": False,
        "active_plan_present": False,
        "evaluation_oracle_present": False,
        "problem_archive_present": False,
        "problem_archive_copy_present": False,
        "third_party_lake_packages_linked": linked_packages,
        "allowed_external_symlinks": (
            [
                {
                    "path": "Lean/.lake/packages",
                    "target": str(source_packages.resolve()),
                    "purpose": "third-party Lake dependencies only",
                }
            ]
            if linked_packages
            else []
        ),
        "copied_file_count": len(copied_files),
        "copied_files_sha256": sha256_id(copied_files),
        "forbidden_paths": forbidden,
        "passed": not forbidden,
    }
    _write_json(destination / "isolation-manifest.json", manifest)
    return manifest


def _validate_formal_profile(
    *, deepseek: DeepSeekConfig, required_profile: Mapping[str, Any]
) -> None:
    if not deepseek.api_key:
        _fail("model_provider_unavailable", "formal capability run requires an API key")
    expected = dict(required_profile)
    if expected != FORMAL_PUBLIC_PROFILE and expected != LEGACY_FORMAL_PUBLIC_PROFILE:
        _fail(
            "qualification_model_profile_mismatch",
            "capability manifest requires an unsupported model profile",
        )
    if expected == FORMAL_PUBLIC_PROFILE and not is_formal_np_hard_qualification_config(
        deepseek
    ):
        _fail(
            "qualification_model_profile_mismatch",
            "capability run requires the accepted DeepSeek V4 Flash profile",
        )
    public = deepseek.to_public_dict()
    actual = {
        "provider": "DeepSeek",
        **{key: value for key, value in public.items() if key != "api_key_configured"},
    }
    if expected != actual:
        _fail(
            "qualification_model_profile_mismatch",
            "runtime model profile differs from the content-addressed manifest",
        )


def _token_usage(ledger: Iterable[Mapping[str, Any]]) -> dict[str, int | float]:
    totals: dict[str, int | float] = {}
    for call in ledger:
        usage = call.get("usage")
        if not isinstance(usage, Mapping):
            continue
        for key, value in usage.items():
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                totals[key] = totals.get(key, 0) + value
    return totals


def _public_status(*, status: str, failure_code: str | None, model_calls: int) -> str:
    if status == "FAILED" and failure_code == "candidate_dependency_stale":
        return "INPUT_ERROR"
    return public_np_hard_status(
        internal_status=status, failure_code=failure_code, model_calls=model_calls
    )


def _case_evidence_payload(row: Mapping[str, Any]) -> dict[str, Any]:
    return {key: deepcopy(value) for key, value in row.items() if key != "evidence_sha256"}


def _first_attempt_verified(payload: Mapping[str, Any]) -> bool:
    if payload.get("status") != "VERIFIED":
        return False
    ledger = payload.get("model_call_ledger") or []
    if not ledger:
        return True
    return all(item.get("attempt") == 1 for item in ledger if isinstance(item, Mapping))


def _raw_protocol_valid(raw: Mapping[str, Any]) -> bool:
    """Recompute whether a case reached the validated V2 production protocol."""

    schema = raw.get("schema_version")
    if schema == NP_HARD_PROOF_RESULT_SCHEMA_V2:
        try:
            NPHardProofResultV2.from_dict(raw)
        except (KeyError, TypeError, ValueError) as error:
            code = getattr(error, "code", type(error).__name__)
            _fail("result_forgery", f"invalid V2 case result: {code}")
        return True
    if schema == "hardness_np_hard_capability_case_error_v1":
        expected = {
            "schema_version",
            "status",
            "failure_code",
            "explanation",
            "input_identity",
            "model_calls",
            "model_call_ledger",
        }
        if set(raw) != expected:
            _fail("result_forgery", "capability error result schema drifted")
        if (
            raw.get("status") != "FAILED"
            or not isinstance(raw.get("failure_code"), str)
            or not raw.get("failure_code")
            or raw.get("input_identity") is not None
            or raw.get("model_calls") != 0
            or raw.get("model_call_ledger") != []
        ):
            _fail("result_forgery", "capability error result is inconsistent")
        return False
    _fail("result_forgery", "case raw_result uses an unsupported schema")


def _run_capability_case(
    *,
    workspace_root: Path,
    output_root: Path,
    case: CapabilityCase,
    identity: Mapping[str, Any],
    deepseek: DeepSeekConfig,
    model_client: object | None = None,
) -> dict[str, Any]:
    case_output = (output_root / "cases" / case.case_id).resolve()
    started = time.monotonic()
    raw_result: dict[str, Any]
    protocol_valid = True
    try:
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=workspace_root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=case_output,
                lean_timeout_seconds=case.budget_profile.lean_timeout_seconds,
                authoring_policy="model-auto",
                attempt_budget=case.budget_profile.attempt_budget,
                call_budget=case.budget_profile.call_budget,
                deepseek=deepseek,
                runtime_prebuilt=True,
                preflight_path=case_output / "preflight.json",
                formal_qualification=True,
                qualification_force_authoring=False,
            ),
            model_client=model_client,
        ).run()
        raw_result = result.to_dict()
    except (NPHardInputError, NPHardOrchestratorError) as error:
        raw_result = {
            "schema_version": "hardness_np_hard_capability_case_error_v1",
            "status": "FAILED",
            "failure_code": error.code,
            "explanation": error.message,
            "input_identity": None,
            "model_calls": 0,
            "model_call_ledger": [],
        }
        protocol_valid = False
    except Exception as error:  # infrastructure exceptions are evidence, never hidden
        raw_result = {
            "schema_version": "hardness_np_hard_capability_case_error_v1",
            "status": "FAILED",
            "failure_code": "capability_runner_exception",
            "explanation": f"{type(error).__name__}: {error}",
            "input_identity": None,
            "model_calls": 0,
            "model_call_ledger": [],
        }
        protocol_valid = False
    ledger = list(raw_result.get("model_call_ledger") or [])
    model_calls = int(raw_result.get("model_calls") or len(ledger))
    internal_status = str(raw_result.get("status") or "FAILED")
    failure_value = raw_result.get("failure_code")
    failure_code = str(failure_value) if failure_value else None
    result_file = case_output / "report.json"
    row: dict[str, Any] = {
        "case_id": case.case_id,
        "suite_id": case.suite_id,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "family": case.family,
        "budget_profile": case.budget_profile.to_public_value(),
        "canonical_identity_id": identity["identity_id"],
        "canonical_problem": identity["canonical_declaration"],
        "canonical_module": identity["canonical_module"],
        "output_dir": str(case_output),
        "wall_duration_seconds": round(time.monotonic() - started, 6),
        "internal_status": internal_status,
        "public_status": _public_status(
            status=internal_status,
            failure_code=failure_code,
            model_calls=model_calls,
        ),
        "failure_code": failure_code,
        "model_calls": model_calls,
        "token_usage": _token_usage(ledger),
        "first_attempt_verified": _first_attempt_verified(raw_result),
        "protocol_valid": protocol_valid,
        "result_file": str(result_file) if result_file.is_file() else None,
        "result_file_sha256": (
            _tagged_sha256(result_file) if result_file.is_file() else None
        ),
        "raw_result": raw_result,
    }
    row["evidence_sha256"] = sha256_id(_case_evidence_payload(row))
    return row


def _run_case_tasks(
    tasks: Sequence[tuple[str, Callable[[], dict[str, Any]]]],
    *,
    jobs: int,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= 32:
        _fail("invalid_capability_jobs", "jobs must be in 1..32")
    if len({case_id for case_id, _ in tasks}) != len(tasks):
        _fail("duplicate_capability_case_id", "parallel task list repeats a case_id")
    lock = threading.Lock()
    active = 0
    maximum_active = 0
    started = time.monotonic()

    def tracked(run: Callable[[], dict[str, Any]]) -> dict[str, Any]:
        nonlocal active, maximum_active
        with lock:
            active += 1
            maximum_active = max(maximum_active, active)
        try:
            return run()
        finally:
            with lock:
                active -= 1

    results: dict[str, dict[str, Any]] = {}
    if jobs == 1 or len(tasks) <= 1:
        for case_id, run in tasks:
            results[case_id] = tracked(run)
    else:
        with ThreadPoolExecutor(
            max_workers=min(jobs, len(tasks)),
            thread_name_prefix="np-hard-capability",
        ) as executor:
            pending = {
                executor.submit(tracked, run): case_id for case_id, run in tasks
            }
            for future in as_completed(pending):
                results[pending[future]] = future.result()
    parallel = {
        "configured_jobs": jobs,
        "submitted_case_tasks": len(tasks),
        "maximum_concurrent_case_tasks": maximum_active,
        "final_active_case_tasks": active,
        "wall_duration_seconds": round(time.monotonic() - started, 6),
        "observed_parallelism": bool(
            jobs == 1
            or len(tasks) <= 1
            or maximum_active >= min(2, jobs, len(tasks))
        ),
    }
    return results, parallel


def _secret_absent(root: Path, secret: str | None) -> bool:
    if not secret:
        return True
    encoded = secret.encode("utf-8")
    for path in root.rglob("*"):
        if not path.is_file() or path.is_symlink():
            continue
        try:
            if encoded in path.read_bytes():
                return False
        except OSError:
            return False
    return True


def _selected_cases(
    bundle: CapabilityBundle,
    selected_splits: Sequence[str],
    selected_case_ids: Sequence[str] | None = None,
) -> tuple[CapabilityCase, ...]:
    if not selected_splits:
        selected_splits = CAPABILITY_SPLITS
    if len(set(selected_splits)) != len(selected_splits):
        _fail("invalid_capability_split", "selected split repeats")
    unknown = set(selected_splits) - set(CAPABILITY_SPLITS)
    if unknown:
        _fail("invalid_capability_split", f"unknown splits: {sorted(unknown)!r}")
    cases = tuple(
        case
        for split in CAPABILITY_SPLITS
        if split in selected_splits
        for case in bundle.suites[split].cases
    )
    if selected_case_ids is None:
        return cases
    if len(set(selected_case_ids)) != len(selected_case_ids):
        _fail("invalid_capability_split", "selected case id repeats")
    by_id = {case.case_id: case for case in cases}
    unknown_ids = sorted(set(selected_case_ids) - set(by_id))
    if unknown_ids:
        _fail(
            "invalid_capability_split",
            f"selected case ids are not in the selected splits: {unknown_ids!r}",
        )
    return tuple(by_id[case_id] for case_id in selected_case_ids)


def run_np_hard_capability_benchmark(
    *,
    root: Path,
    manifest_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
    selected_splits: Sequence[str] = CAPABILITY_SPLITS,
    selected_case_ids: Sequence[str] | None = None,
    jobs: int = 4,
    model_client: object | None = None,
) -> dict[str, Any]:
    """Run answer-free target-hardness cases through the production entrypoint."""

    root = root.resolve()
    bundle = load_capability_bundle(
        manifest_path.resolve(), root=root, verify_oracle=False
    )
    _validate_formal_profile(
        deepseek=deepseek,
        required_profile=bundle.manifest.required_model_profile,
    )
    normalized_splits = tuple(selected_splits) or CAPABILITY_SPLITS
    cases = _selected_cases(
        bundle,
        normalized_splits,
        selected_case_ids=(
            None if selected_case_ids is None else tuple(selected_case_ids)
        ),
    )
    output_root = output_root.resolve()
    _fresh_directory(output_root, label="capability output root")
    isolation_root = output_root / "isolated-workspace"
    isolation = build_capability_isolated_workspace(
        root=root,
        destination=isolation_root,
        target_matrix_path=bundle.manifest.target_matrix.path,
        scope_policy_path=bundle.manifest.scope_policy.path,
    )
    preflight = run_command(
        build_module_command(case.module for case in cases),
        cwd=isolation_root / "Lean",
        timeout_seconds=CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS,
    )
    rows: list[dict[str, Any]] = []
    parallel = {
        "configured_jobs": jobs,
        "submitted_case_tasks": 0,
        "maximum_concurrent_case_tasks": 0,
        "final_active_case_tasks": 0,
        "wall_duration_seconds": 0.0,
        "observed_parallelism": True,
    }
    if preflight.ok:
        tasks = [
            (
                case.case_id,
                lambda case=case: _run_capability_case(
                    workspace_root=isolation_root,
                    output_root=output_root,
                    case=case,
                    identity=bundle.case_identity[case.case_id],
                    deepseek=deepseek,
                    model_client=model_client,
                ),
            )
            for case in cases
        ]
        by_id, parallel = _run_case_tasks(tasks, jobs=jobs)
        rows = [by_id[case.case_id] for case in cases]
    secret_absent = _secret_absent(output_root, deepseek.api_key)
    run_valid = bool(
        preflight.ok
        and len(rows) == len(cases)
        and len({row["case_id"] for row in rows}) == len(rows)
        and all(row["protocol_valid"] for row in rows)
        and parallel["final_active_case_tasks"] == 0
        and parallel["observed_parallelism"] is True
        and isolation["passed"] is True
        and secret_absent
    )
    payload: dict[str, Any] = {
        "schema_version": bundle.manifest.run_schema_version,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "benchmark_id": bundle.manifest.benchmark_id,
        "run_valid": run_valid,
        "output_root": str(output_root),
        "selected_splits": [
            split for split in CAPABILITY_SPLITS if split in normalized_splits
        ],
        "selected_case_ids": [case.case_id for case in cases],
        "manifest": {
            "file": str(bundle.manifest.path),
            "sha256": _tagged_sha256(bundle.manifest.path),
            "oracle_reference_present": True,
            "oracle_opened_by_runner": False,
        },
        "suites": {
            split: {
                "file": str(bundle.manifest.suites[split].path),
                "sha256": bundle.manifest.suites[split].sha256,
            }
            for split in CAPABILITY_SPLITS
        },
        "target_matrix": {
            "file": str(bundle.manifest.target_matrix.path),
            "sha256": bundle.manifest.target_matrix.sha256,
            "matrix_id": bundle.target_matrix.get("matrix_id"),
        },
        "scope_policy": {
            "file": str(bundle.manifest.scope_policy.path),
            "sha256": bundle.manifest.scope_policy.sha256,
        },
        "model": deepseek.to_public_dict(),
        "preflight": preflight.to_dict(),
        "isolation": isolation,
        "parallel_execution": parallel,
        "metrics": {
            "case_count": len(rows),
            "verified_count": sum(row["public_status"] == "VERIFIED" for row in rows),
            "blocked_not_target_count": sum(
                row["public_status"] == "BLOCKED_NOT_TARGET" for row in rows
            ),
            "blocked_missing_prerequisite_count": sum(
                row["public_status"] == "BLOCKED_MISSING_PREREQUISITE"
                for row in rows
            ),
            "failed_model_count": sum(
                row["public_status"] == "FAILED_MODEL" for row in rows
            ),
            "failed_lean_count": sum(
                row["public_status"] == "FAILED_LEAN" for row in rows
            ),
            "model_calls": sum(row["model_calls"] for row in rows),
            "token_usage": _token_usage(
                call
                for row in rows
                for call in (row["raw_result"].get("model_call_ledger") or [])
            ),
        },
        "security": {
            "formal_model_profile_matched": True,
            "api_key_or_authorization_absent": secret_absent,
            "fixture_model_used": False,
            "cached_or_recorded_response_used": False,
            "oracle_opened_by_runner": False,
            "oracle_passed_to_orchestrator": False,
            "active_plan_present_in_isolation": False,
            "evaluation_present_in_isolation": False,
            "problem_archive_present_in_isolation": False,
        },
        "cases": rows,
    }
    payload["run_id"] = sha256_id(payload)
    _write_json(report_path.resolve(), payload)
    canonical_report = output_root / "report.json"
    if canonical_report.resolve() != report_path.resolve():
        _write_json(canonical_report, payload)
    return payload


def _validate_run_id(report: Mapping[str, Any]) -> None:
    claimed = report.get("run_id")
    if not isinstance(claimed, str):
        _fail("result_forgery", "capability report lacks run_id")
    payload = {key: deepcopy(value) for key, value in report.items() if key != "run_id"}
    if claimed != sha256_id(payload):
        _fail("result_forgery", "capability report content hash does not match run_id")


def _path_within(path_value: Any, root: Path) -> bool:
    if not isinstance(path_value, str):
        return False
    try:
        Path(path_value).resolve().relative_to(root.resolve())
    except ValueError:
        return False
    return True


def _deletion_command_matches_declaration(
    command: Mapping[str, Any], declaration: str
) -> bool:
    return deletion_command_matches_declaration_v2(command, declaration)


def _validate_required_authoring_motif_evidence(
    *,
    raw: Mapping[str, Any],
    required_authoring_motif: Mapping[str, Any],
    case_output: Path,
    require_files: bool,
) -> None:
    """Bind a v2 authored result to its scorer-only exact DAG motif."""

    expected = _normalize_required_authoring_motif(
        required_authoring_motif,
        label="required authoring motif",
        error_code="candidate_dependency_stale",
    )
    observed, task = _authoring_task_motif(raw.get("capability_dag"))
    if observed != expected:
        _fail(
            "candidate_dependency_stale",
            "capability DAG task class or exact required node motif drifted",
        )
    if raw.get("status") != "VERIFIED":
        return

    expected_ids = [node["node_id"] for node in expected["nodes"]]
    task_nodes = {node.node_id: node for node in task.gap_nodes}
    runtime = raw.get("authoring_runtime")
    if not isinstance(runtime, Mapping) or runtime.get("status") != "VERIFIED":
        _fail(
            "candidate_dependency_stale",
            "verified authored case lacks its exact verified runtime ledger",
        )
    runtime_result = runtime.get("result")
    if (
        runtime.get("task_request_id") != task.request_id
        or runtime.get("accepted_nodes") != expected_ids
        or not isinstance(runtime_result, Mapping)
        or runtime_result.get("accepted_nodes") != expected_ids
    ):
        _fail(
            "candidate_dependency_stale",
            "verified runtime accepted nodes differ from the required motif",
        )
    try:
        validate_successor_only_authoritative_evidence_v2(
            task=task,
            runtime=runtime,
            case_output=case_output,
            require_files=require_files,
        )
    except NPHardAuthoringContractError as error:
        _fail(
            error.code,
            "verified successor-only runtime lacks authoritative Lean evidence: "
            + error.message,
        )

    fresh_core = raw.get("fresh_core")
    fresh_count = fresh_core.get("count") if isinstance(fresh_core, Mapping) else None
    if (
        not isinstance(fresh_core, Mapping)
        or fresh_core.get("passed") is not True
        or isinstance(fresh_count, bool)
        or not isinstance(fresh_count, int)
        or fresh_count != len(expected_ids)
        or runtime.get("fresh_core_rediscoveries") != fresh_count
    ):
        _fail(
            "fresh_core_resolve_failed",
            "verified authored case did not fresh-resolve exactly every motif node",
        )

    deletion = raw.get("deletion_audit")
    deletion_nodes = deletion.get("nodes") if isinstance(deletion, Mapping) else None
    if (
        not isinstance(deletion, Mapping)
        or deletion.get("passed") is not True
        or isinstance(deletion.get("node_count"), bool)
        or not isinstance(deletion.get("node_count"), int)
        or deletion.get("node_count") != len(expected_ids)
        or not isinstance(deletion_nodes, list)
        or len(deletion_nodes) != len(expected_ids)
        or runtime.get("deletion_audits") != deletion_nodes
    ):
        _fail(
            "deletion_audit_failed",
            "verified authored case lacks one deletion audit per required motif node",
        )
    for node_id, audit in zip(expected_ids, deletion_nodes, strict=True):
        task_node = task_nodes[node_id]
        if not isinstance(audit, Mapping):
            _fail("deletion_audit_failed", "deletion audit node is invalid")
        declaration = audit.get("declaration")
        command = audit.get("command")
        if (
            audit.get("node_id") != node_id
            or declaration != task_node.declaration
            or audit.get("diagnostic_matched") is not True
            or audit.get("passed") is not True
            or not isinstance(command, Mapping)
            or not _deletion_command_matches_declaration(command, task_node.declaration)
        ):
            _fail(
                "deletion_audit_failed",
                "deletion audit did not fail on the exact required motif declaration",
            )
        if require_files:
            audit_file = audit.get("audit_file")
            if not _path_within(audit_file, case_output):
                _fail(
                    "cross_job_candidate",
                    "deletion audit escaped its case output directory",
                )
            audit_path = Path(str(audit_file))
            if (
                not audit_path.is_file()
                or audit.get("audit_file_sha256") != _tagged_sha256(audit_path)
            ):
                _fail("result_forgery", "deletion audit file/hash drifted")


def _validate_observed_evidence(
    *,
    row: Mapping[str, Any],
    canonical_problem: str,
    case_output: Path,
    require_files: bool,
    strict_deletion_diagnostics: bool = False,
    required_authoring_motif: Mapping[str, Any] | None = None,
) -> None:
    raw = row.get("raw_result")
    if not isinstance(raw, Mapping):
        _fail("result_forgery", "case raw_result is missing")
    status = raw.get("status")
    input_identity = raw.get("input_identity")
    if isinstance(input_identity, Mapping):
        observed = input_identity.get("canonical_problem")
        if observed is not None and observed != canonical_problem:
            _fail("candidate_dependency_stale", "normalized canonical endpoint drifted")
    capability_dag = raw.get("capability_dag")
    if isinstance(capability_dag, Mapping):
        direction = capability_dag.get("required_direction")
        if direction is not None and direction != "source_to_target":
            _fail("candidate_wrong_direction", "capability DAG reversed the direction")
        target = capability_dag.get("target_problem")
        if isinstance(target, Mapping) and target.get("term") != canonical_problem:
            _fail("candidate_wrong_endpoint", "capability DAG targets another endpoint")
    artifact = raw.get("artifact")
    if artifact is not None:
        if not isinstance(artifact, Mapping) or artifact.get("endpoint") != canonical_problem:
            _fail("candidate_wrong_endpoint", "artifact endpoint differs from the case")
        artifact_file = artifact.get("file")
        if not _path_within(artifact_file, case_output):
            _fail("cross_job_candidate", "artifact escaped its case output directory")
        if require_files:
            artifact_path = Path(str(artifact_file))
            if not artifact_path.is_file():
                _fail("result_forgery", "artifact file is missing")
            if artifact.get("sha256") != _tagged_sha256(artifact_path):
                _fail("result_forgery", "artifact content hash drifted")
    if status == "VERIFIED":
        replay = raw.get("independent_replay")
        axiom = raw.get("axiom_audit")
        if not isinstance(replay, Mapping) or replay.get("passed") is not True:
            _fail("independent_replay_failed", "verified case lacks independent replay")
        if not isinstance(axiom, Mapping) or axiom.get("passed") is not True:
            _fail("candidate_nonstandard_axiom", "verified case failed the axiom gate")
        deletion = raw.get("deletion_audit")
        if deletion is not None and (
            not isinstance(deletion, Mapping) or deletion.get("passed") is not True
        ):
            _fail("deletion_audit_failed", "verified authored case failed deletion audit")
        authored_runtime = raw.get("authoring_runtime")
        if require_files and strict_deletion_diagnostics and authored_runtime is not None:
            if not isinstance(authored_runtime, Mapping) or not isinstance(
                deletion, Mapping
            ):
                _fail(
                    "deletion_audit_failed",
                    "verified v2 authored case lacks its deletion audit ledger",
                )
            _observed_motif, authored_task = _authoring_task_motif(capability_dag)
            expected_nodes = list(authored_task.gap_nodes)
            nodes = deletion.get("nodes")
            if (
                not isinstance(nodes, list)
                or isinstance(deletion.get("node_count"), bool)
                or not isinstance(deletion.get("node_count"), int)
                or deletion.get("node_count") != len(expected_nodes)
                or len(nodes) != len(expected_nodes)
                or authored_runtime.get("deletion_audits") != nodes
            ):
                _fail(
                    "deletion_audit_failed",
                    "verified authored case lacks a complete deletion audit ledger",
                )
            for expected_node, node in zip(expected_nodes, nodes, strict=True):
                if not isinstance(node, Mapping):
                    _fail("deletion_audit_failed", "deletion audit node is invalid")
                declaration = node.get("declaration")
                command = node.get("command")
                audit_file = node.get("audit_file")
                if (
                    node.get("node_id") != expected_node.node_id
                    or declaration != expected_node.declaration
                    or not isinstance(command, Mapping)
                    or node.get("diagnostic_matched") is not True
                    or node.get("passed") is not True
                    or not _deletion_command_matches_declaration(
                        command, expected_node.declaration
                    )
                    or not _path_within(audit_file, case_output)
                ):
                    _fail(
                        "deletion_audit_failed",
                        "deletion audit did not fail on the exact removed declaration",
                    )
                audit_path = Path(str(audit_file))
                if (
                    not audit_path.is_file()
                    or node.get("audit_file_sha256") != _tagged_sha256(audit_path)
                ):
                    _fail("result_forgery", "deletion audit file/hash drifted")
        replay_file = replay.get("file") if isinstance(replay, Mapping) else None
        if require_files and replay_file is not None:
            if not _path_within(replay_file, case_output):
                _fail("cross_job_candidate", "replay artifact escaped its case output")
            replay_path = Path(str(replay_file))
            if not replay_path.is_file() or replay.get("sha256") != _tagged_sha256(
                replay_path
            ):
                _fail("result_forgery", "independent replay content hash drifted")
    if required_authoring_motif is not None:
        _validate_required_authoring_motif_evidence(
            raw=raw,
            required_authoring_motif=required_authoring_motif,
            case_output=case_output,
            require_files=require_files,
        )


def _validate_run_case(
    *,
    row: Mapping[str, Any],
    case: CapabilityCase,
    identity: Mapping[str, Any],
    output_root: Path,
    strict_deletion_diagnostics: bool = False,
    required_authoring_motif: Mapping[str, Any] | None = None,
) -> None:
    _exact_keys(row, RUN_CASE_FIELDS, label=f"run case {case.case_id}")
    if row.get("case_id") != case.case_id or row.get("split") != case.split:
        _fail("result_forgery", "run case identity differs from the public suite")
    if row.get("suite_id") != case.suite_id:
        _fail("result_forgery", "run case suite_id differs from the public suite")
    if row.get("module") != case.module or row.get("problem") != case.problem:
        _fail("result_forgery", "run case endpoint differs from the public suite")
    if row.get("family") != case.family:
        _fail("result_forgery", "run case family differs from the public suite")
    if row.get("budget_profile") != case.budget_profile.to_public_value():
        _fail("result_forgery", "run case budget profile differs from the public suite")
    if row.get("canonical_identity_id") != identity.get("identity_id"):
        _fail("result_forgery", "run case canonical identity was substituted")
    if row.get("canonical_problem") != identity.get("canonical_declaration"):
        _fail("result_forgery", "run case canonical declaration was substituted")
    if row.get("canonical_module") != identity.get("canonical_module"):
        _fail("result_forgery", "run case canonical module was substituted")
    if row.get("evidence_sha256") != sha256_id(_case_evidence_payload(row)):
        _fail("result_forgery", "case evidence hash does not match its raw result")
    case_output = Path(str(row.get("output_dir"))).resolve()
    expected_output = (output_root / "cases" / case.case_id).resolve()
    if case_output != expected_output:
        _fail("cross_job_candidate", "case output directory differs from its job identity")
    result_file = row.get("result_file")
    result_hash = row.get("result_file_sha256")
    if result_file is not None:
        if not _path_within(result_file, case_output):
            _fail("cross_job_candidate", "case report escaped its output directory")
        path = Path(str(result_file))
        if not path.is_file() or result_hash != _tagged_sha256(path):
            _fail("result_forgery", "stored case report hash is stale or missing")
        try:
            stored_result = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            _fail("result_forgery", "stored case report is unreadable")
        if stored_result != row.get("raw_result"):
            _fail("result_forgery", "stored case report differs from raw evidence")
    raw = row["raw_result"]
    if not isinstance(raw, Mapping):
        _fail("result_forgery", "run case raw_result is not an object")
    protocol_valid = _raw_protocol_valid(raw)
    model_calls = int(raw.get("model_calls") or 0)
    ledger = raw.get("model_call_ledger") or []
    if not isinstance(ledger, list) or model_calls != len(ledger):
        _fail("result_forgery", "model call ledger count drifted")
    for call in ledger:
        if not isinstance(call, Mapping):
            _fail("result_forgery", "model ledger entry is invalid")
        for key in ("prompt_sha256", "response_sha256"):
            if not isinstance(call.get(key), str) or not SHA256_RE.fullmatch(call[key]):
                _fail("result_forgery", f"model ledger {key} is invalid")
        prompt_file = call.get("prompt_file")
        response_file = call.get("response_file")
        if not _path_within(prompt_file, case_output) or not _path_within(
            response_file, case_output
        ):
            _fail("cross_job_candidate", "model evidence escaped its case output")
        prompt_path = Path(str(prompt_file))
        response_path = Path(str(response_file))
        if not prompt_path.is_file() or not response_path.is_file():
            _fail("result_forgery", "model prompt/response evidence is missing")
        try:
            prompt = prompt_path.read_text(encoding="utf-8")
            response_record = json.loads(response_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            _fail("result_forgery", "model prompt/response evidence is unreadable")
        if call["prompt_sha256"] != sha256_id(prompt):
            _fail("result_forgery", "model prompt hash drifted")
        if not isinstance(response_record, Mapping) or call[
            "response_sha256"
        ] != sha256_id(response_record.get("content")):
            _fail("result_forgery", "model response hash drifted")
    if (
        isinstance(row.get("model_calls"), bool)
        or row.get("model_calls") != model_calls
    ):
        _fail("result_forgery", "run case model_calls differs from raw evidence")
    token_usage = _token_usage(ledger)
    if row.get("token_usage") != token_usage:
        _fail("result_forgery", "run case token_usage differs from raw evidence")
    first_attempt = _first_attempt_verified(raw)
    if row.get("first_attempt_verified") is not first_attempt:
        _fail(
            "result_forgery",
            "run case first_attempt_verified differs from raw evidence",
        )
    if row.get("protocol_valid") is not protocol_valid:
        _fail("result_forgery", "run case protocol_valid differs from raw evidence")
    internal = str(raw.get("status") or "FAILED")
    failure = raw.get("failure_code")
    normalized_failure = str(failure) if failure else None
    expected_public = _public_status(
        status=internal,
        failure_code=normalized_failure,
        model_calls=model_calls,
    )
    if row.get("failure_code") != normalized_failure:
        _fail("result_forgery", "run case failure_code differs from raw evidence")
    if row.get("internal_status") != internal or row.get("public_status") != expected_public:
        _fail("result_forgery", "reported public/internal status differs from raw evidence")
    _validate_observed_evidence(
        row=row,
        canonical_problem=str(identity["canonical_declaration"]),
        case_output=case_output,
        require_files=True,
        strict_deletion_diagnostics=strict_deletion_diagnostics,
        required_authoring_motif=required_authoring_motif,
    )


def _route_length(row: Mapping[str, Any]) -> int | None:
    raw = row["raw_result"]
    deterministic = raw.get("deterministic_result")
    if not isinstance(deterministic, Mapping):
        return None
    route = deterministic.get("route")
    if not isinstance(route, Mapping):
        return None
    atoms = route.get("atoms")
    return len(atoms) if isinstance(atoms, list) else None


def _strict_case_success(
    row: Mapping[str, Any], oracle: CapabilityOracleCase
) -> tuple[bool, bool]:
    public_status = row["public_status"]
    failure_code = row.get("failure_code")
    raw = row["raw_result"]
    canonical = row["canonical_problem"]
    artifact = raw.get("artifact")
    endpoint_exact = bool(
        isinstance(artifact, Mapping) and artifact.get("endpoint") == canonical
    )
    replay = raw.get("independent_replay")
    axiom = raw.get("axiom_audit")
    audits = bool(
        isinstance(replay, Mapping)
        and replay.get("passed") is True
        and isinstance(axiom, Mapping)
        and axiom.get("passed") is True
    )
    if oracle.blocker_bucket is not None:
        success = bool(
            public_status == oracle.expected_public_status
            and failure_code in oracle.expected_failure_codes
            and row["model_calls"] == 0
            and row.get("protocol_valid") is True
        )
        return success, success
    if oracle.tier == "C0-safety":
        success = bool(
            public_status == oracle.expected_public_status
            and failure_code in oracle.expected_failure_codes
            and row["model_calls"] == 0
        )
        return success, success
    verified = bool(
        public_status == "VERIFIED"
        and failure_code is None
        and endpoint_exact
        and audits
    )
    if oracle.tier == "C0-existing":
        verified = bool(
            verified
            and row["model_calls"] == 0
            and _route_length(row) == oracle.route_length
        )
    if oracle.tier == "C0-authoring" and oracle.requires_model:
        verified = bool(verified and row["model_calls"] > 0)
    if oracle.tier == "F0-frontier":
        return verified, bool(row.get("protocol_valid"))
    return verified, verified


def _required_verified_authoring_motif(
    *,
    oracle_schema_version: str,
    oracle_case: CapabilityOracleCase,
    raw_result: Any,
) -> Mapping[str, Any] | None:
    """Reject v2 verified authoring until the scorer oracle freezes its motif."""

    if (
        oracle_schema_version == CAPABILITY_ORACLE_SCHEMA_V2
        and oracle_case.tier == "C0-authoring"
        and isinstance(raw_result, Mapping)
        and raw_result.get("status") == "VERIFIED"
        and oracle_case.required_authoring_motif is None
    ):
        _fail(
            "candidate_dependency_stale",
            "verified v2 authoring case lacks a scorer-frozen required motif",
        )
    return oracle_case.required_authoring_motif


def _rate(numerator: int, denominator: int) -> float | None:
    return round(numerator / denominator, 6) if denominator else None


def _macro(group_rows: Mapping[str, Sequence[Mapping[str, Any]]]) -> dict[str, Any]:
    groups: dict[str, Any] = {}
    rates: list[float] = []
    for name, rows in sorted(group_rows.items()):
        success = sum(bool(row["capability_success"]) for row in rows)
        rate = _rate(success, len(rows))
        groups[name] = {"count": len(rows), "success": success, "rate": rate}
        if rate is not None:
            rates.append(rate)
    return {
        "groups": groups,
        "macro_score": round(sum(rates) / len(rates), 6) if rates else None,
    }


def _level_number(level: str) -> int:
    values = [int(value) for value in re.findall(r"[0-6]", level)]
    return max(values) if values else -1


def _failure_layer(row: Mapping[str, Any]) -> str | None:
    if row["public_status"] == "VERIFIED":
        return None
    code = str(row.get("failure_code") or "")
    if "budget" in code or "exhaust" in code:
        return "budget"
    if row["public_status"] == "FAILED_MODEL":
        return "model"
    if row["public_status"] == "FAILED_LEAN":
        return "lean"
    return "blocker"


def _boundary(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    positive = [
        row
        for row in rows
        if row["scored"] and row["outcome_class"] in {"existing_route", "first_authoring"}
    ]
    by_number: dict[int, list[Mapping[str, Any]]] = {}
    for row in positive:
        by_number.setdefault(_level_number(str(row["level"])), []).append(row)
    level_rates = {
        f"L{level}": _rate(
            sum(bool(row["capability_success"]) for row in level_rows),
            len(level_rows),
        )
        for level, level_rows in sorted(by_number.items())
        if level >= 0
    }
    stable = [
        int(level[1:])
        for level, rate in level_rates.items()
        if rate is not None and rate >= 0.8
    ]
    failing = [
        int(level[1:])
        for level, rate in level_rates.items()
        if rate is not None and rate <= 0.5
    ]
    blocker_distribution: dict[str, int] = {}
    layer_distribution: dict[str, int] = {}
    for row in rows:
        if row["capability_success"]:
            continue
        code = str(row.get("failure_code") or "unknown")
        blocker_distribution[code] = blocker_distribution.get(code, 0) + 1
        layer = _failure_layer(row)
        if layer is not None:
            layer_distribution[layer] = layer_distribution.get(layer, 0) + 1
    return {
        "method": {
            "stable_level_threshold": 0.8,
            "significant_failure_threshold": 0.5,
            "level_ranges_use_their_highest_axis": True,
        },
        "level_success_rates": level_rates,
        "highest_stable_level": f"L{max(stable)}" if stable else None,
        "first_significant_failure_level": f"L{min(failing)}" if failing else None,
        "failure_code_distribution": dict(sorted(blocker_distribution.items())),
        "failure_layer_distribution": dict(sorted(layer_distribution.items())),
    }


def _synthetic_verified_row(canonical_problem: str) -> dict[str, Any]:
    case_output = Path("/isolated-output/cases/synthetic")
    raw = {
        "status": "VERIFIED",
        "failure_code": None,
        "input_identity": {"canonical_problem": canonical_problem},
        "capability_dag": {
            "required_direction": "source_to_target",
            "target_problem": {"term": canonical_problem},
        },
        "artifact": {
            "endpoint": canonical_problem,
            "file": str(case_output / "Artifact.lean"),
        },
        "independent_replay": {"passed": True},
        "axiom_audit": {"passed": True},
        "deletion_audit": {"passed": True},
    }
    return {"raw_result": raw}


def _expect_error(action: Callable[[], Any], code: str) -> dict[str, Any]:
    try:
        action()
    except NPHardCapabilityError as error:
        return {
            "expected_code": code,
            "observed_code": error.code,
            "passed": error.code == code,
        }
    return {"expected_code": code, "observed_code": None, "passed": False}


def run_capability_r0_mutation_audit(bundle: CapabilityBundle) -> dict[str, Any]:
    """Exercise the eight frozen H-I fail-closed mutation contracts in memory."""

    first = bundle.cases[0]
    identity = bundle.case_identity[first.case_id]
    canonical = str(identity["canonical_declaration"])
    case_output = Path("/isolated-output/cases/synthetic")

    leaked_case = {
        "case_id": "r0-leak",
        "module": first.module,
        "problem": first.problem,
        "family": first.family,
        "budget_profile": "formal-default",
        "expected_status": "VERIFIED",
    }
    audits: dict[str, dict[str, Any]] = {}
    audits["r0-score-01-oracle-field-in-suite"] = _expect_error(
        lambda: _parse_public_case(
            leaked_case, split="dev", suite_id="r0-mutation"
        ),
        "oracle_field_in_public_suite",
    )
    duplicate_occurrences = [
        (str(identity["identity_id"]), "dev", "one"),
        (str(identity["identity_id"]), "dev", "alias"),
    ]
    observed_duplicate = _identity_conflict_code(duplicate_occurrences)
    audits["r0-score-02-alias-double-count"] = {
        "expected_code": "duplicate_canonical_identity",
        "observed_code": observed_duplicate,
        "passed": observed_duplicate == "duplicate_canonical_identity",
    }
    overlap_occurrences = [
        (str(identity["identity_id"]), "dev", "one"),
        (str(identity["identity_id"]), "heldout", "alias"),
    ]
    observed_overlap = _identity_conflict_code(overlap_occurrences)
    audits["r0-score-03-cross-split-overlap"] = {
        "expected_code": "capability_split_overlap",
        "observed_code": observed_overlap,
        "passed": observed_overlap == "capability_split_overlap",
    }

    wrong_direction = _synthetic_verified_row(canonical)
    wrong_direction["raw_result"]["capability_dag"]["required_direction"] = (
        "target_to_source"
    )
    audits["r0-score-04-direction-reversal"] = _expect_error(
        lambda: _validate_observed_evidence(
            row=wrong_direction,
            canonical_problem=canonical,
            case_output=case_output,
            require_files=False,
        ),
        "candidate_wrong_direction",
    )
    wrong_endpoint = _synthetic_verified_row(canonical)
    wrong_endpoint["raw_result"]["artifact"]["endpoint"] = canonical + "Other"
    audits["r0-score-05-endpoint-substitution"] = _expect_error(
        lambda: _validate_observed_evidence(
            row=wrong_endpoint,
            canonical_problem=canonical,
            case_output=case_output,
            require_files=False,
        ),
        "candidate_wrong_endpoint",
    )
    stale = _synthetic_verified_row(canonical)
    stale["raw_result"]["input_identity"]["canonical_problem"] = canonical + "Stale"
    audits["r0-score-06-stale-normalization"] = _expect_error(
        lambda: _validate_observed_evidence(
            row=stale,
            canonical_problem=canonical,
            case_output=case_output,
            require_files=False,
        ),
        "candidate_dependency_stale",
    )
    nonstandard = _synthetic_verified_row(canonical)
    nonstandard["raw_result"]["axiom_audit"]["passed"] = False
    audits["r0-score-07-nonstandard-axiom"] = _expect_error(
        lambda: _validate_observed_evidence(
            row=nonstandard,
            canonical_problem=canonical,
            case_output=case_output,
            require_files=False,
        ),
        "candidate_nonstandard_axiom",
    )
    cross_job = _synthetic_verified_row(canonical)
    cross_job["raw_result"]["artifact"]["file"] = "/other-job/Artifact.lean"
    audits["r0-score-08-cross-job-artifact"] = _expect_error(
        lambda: _validate_observed_evidence(
            row=cross_job,
            canonical_problem=canonical,
            case_output=case_output,
            require_files=False,
        ),
        "cross_job_candidate",
    )
    return {
        "schema_version": "hardness_np_hard_capability_r0_mutation_audit_v1",
        "audit_count": len(audits),
        "passed_count": sum(item["passed"] for item in audits.values()),
        "passed": all(item["passed"] for item in audits.values()),
        "audits": audits,
    }


def score_np_hard_capability_benchmark(
    *,
    root: Path,
    manifest_path: Path,
    run_report_path: Path,
    score_report_path: Path,
) -> dict[str, Any]:
    """Verify raw evidence, then score it with the scorer-only oracle."""

    root = root.resolve()
    bundle = load_capability_bundle(
        manifest_path.resolve(), root=root, verify_oracle=True
    )
    oracle = load_capability_oracle(bundle.manifest.oracle.path, bundle=bundle)
    report = _read_json(run_report_path.resolve(), label="capability run report")
    if report.get("schema_version") != bundle.manifest.run_schema_version:
        _fail("result_forgery", "unsupported capability run report schema")
    _validate_run_id(report)
    if report.get("benchmark_id") != bundle.manifest.benchmark_id:
        _fail("result_forgery", "run report benchmark_id drifted")
    manifest_record = report.get("manifest")
    if not isinstance(manifest_record, Mapping) or manifest_record.get(
        "sha256"
    ) != _tagged_sha256(bundle.manifest.path):
        _fail("result_forgery", "run report manifest hash drifted")
    if Path(str(manifest_record.get("file"))).resolve() != bundle.manifest.path:
        _fail("result_forgery", "run report manifest path drifted")
    if manifest_record.get("oracle_opened_by_runner") is not False:
        _fail("oracle_leakage", "production runner opened the scorer oracle")
    suite_records = report.get("suites")
    if not isinstance(suite_records, Mapping) or set(suite_records) != set(
        CAPABILITY_SPLITS
    ):
        _fail("result_forgery", "run report suite provenance is invalid")
    for split, reference in bundle.manifest.suites.items():
        record = suite_records[split]
        if not isinstance(record, Mapping) or record.get("sha256") != reference.sha256:
            _fail("result_forgery", f"run report {split} suite hash drifted")
        if Path(str(record.get("file"))).resolve() != reference.path:
            _fail("result_forgery", f"run report {split} suite path drifted")
    target_record = report.get("target_matrix")
    if (
        not isinstance(target_record, Mapping)
        or target_record.get("sha256") != bundle.manifest.target_matrix.sha256
        or Path(str(target_record.get("file"))).resolve()
        != bundle.manifest.target_matrix.path
        or target_record.get("matrix_id") != bundle.target_matrix.get("matrix_id")
    ):
        _fail("result_forgery", "run report target matrix provenance drifted")
    scope_record = report.get("scope_policy")
    if (
        not isinstance(scope_record, Mapping)
        or scope_record.get("sha256") != bundle.manifest.scope_policy.sha256
        or Path(str(scope_record.get("file"))).resolve()
        != bundle.manifest.scope_policy.path
    ):
        _fail("result_forgery", "run report scope policy provenance drifted")
    model = report.get("model")
    expected_model = {
        key: value
        for key, value in bundle.manifest.required_model_profile.items()
        if key != "provider"
    }
    expected_model["api_key_configured"] = True
    if model != expected_model:
        _fail("qualification_model_profile_mismatch", "run report model profile drifted")
    selected_splits = report.get("selected_splits")
    if not isinstance(selected_splits, list) or not all(
        isinstance(split, str) and split in CAPABILITY_SPLITS
        for split in selected_splits
    ):
        _fail("result_forgery", "run report selected_splits are invalid")
    recorded_case_ids = report.get("selected_case_ids")
    if recorded_case_ids is not None and (
        not isinstance(recorded_case_ids, list)
        or not all(isinstance(item, str) and item for item in recorded_case_ids)
        or len(recorded_case_ids) != len(set(recorded_case_ids))
    ):
        _fail("result_forgery", "run report selected_case_ids are invalid")
    expected_cases = {
        case.case_id: case
        for case in _selected_cases(
            bundle,
            tuple(selected_splits),
            selected_case_ids=(
                tuple(recorded_case_ids) if recorded_case_ids is not None else None
            ),
        )
    }
    rows_value = report.get("cases")
    if not isinstance(rows_value, list) or not all(
        isinstance(row, Mapping) for row in rows_value
    ):
        _fail("result_forgery", "run report cases are invalid")
    rows_by_id = {str(row.get("case_id")): row for row in rows_value}
    if len(rows_by_id) != len(rows_value) or set(rows_by_id) != set(expected_cases):
        _fail("result_forgery", "run report did not execute each selected case exactly once")
    output_root = Path(str(report.get("output_root"))).resolve()
    scored_rows: list[dict[str, Any]] = []
    for case_id, case in expected_cases.items():
        row = rows_by_id[case_id]
        identity = bundle.case_identity[case_id]
        oracle_case = oracle[case_id]
        required_authoring_motif = _required_verified_authoring_motif(
            oracle_schema_version=bundle.manifest.oracle_schema_version,
            oracle_case=oracle_case,
            raw_result=row.get("raw_result"),
        )
        _validate_run_case(
            row=row,
            case=case,
            identity=identity,
            output_root=output_root,
            strict_deletion_diagnostics=(
                bundle.manifest.run_schema_version == CAPABILITY_RUN_SCHEMA_V2
            ),
            required_authoring_motif=required_authoring_motif,
        )
        capability_success, expected_outcome_matched = _strict_case_success(
            row, oracle_case
        )
        scored_row = {
            "case_id": case_id,
            "split": case.split,
            "family": case.family,
            "tier": oracle_case.tier,
            "outcome_class": oracle_case.outcome_class,
            "level": oracle_case.level,
            "scored": oracle_case.scored,
            "requires_model": oracle_case.requires_model,
            "public_status": row["public_status"],
            "failure_code": row.get("failure_code"),
            "model_calls": row["model_calls"],
            "token_usage": deepcopy(row["token_usage"]),
            "wall_duration_seconds": row["wall_duration_seconds"],
            "first_attempt_verified": bool(row["first_attempt_verified"]),
            "capability_success": capability_success,
            "expected_outcome_matched": expected_outcome_matched,
            "evidence_sha256": row["evidence_sha256"],
        }
        if bundle.manifest.oracle_schema_version == CAPABILITY_ORACLE_SCHEMA_V2:
            scored_row["blocker_bucket"] = oracle_case.blocker_bucket
        scored_rows.append(scored_row)

    preflight = report.get("preflight")
    isolation = report.get("isolation")
    parallel_record = report.get("parallel_execution")
    security = report.get("security")
    if not isinstance(preflight, Mapping) or not isinstance(isolation, Mapping):
        _fail("result_forgery", "run preflight/isolation evidence is invalid")
    if not isinstance(parallel_record, Mapping) or not isinstance(security, Mapping):
        _fail("result_forgery", "run parallel/security evidence is invalid")
    preflight_ok = bool(
        preflight.get("exit_code") == 0 and preflight.get("timed_out") is False
    )
    isolation_ok = bool(
        isolation.get("passed") is True
        and isolation.get("forbidden_paths") == []
        and isolation.get("active_plan_present") is False
        and isolation.get("evaluation_oracle_present") is False
        and isolation.get("problem_archive_present") is False
        and isolation.get("problem_archive_copy_present") is False
    )
    parallel_ok = bool(
        parallel_record.get("submitted_case_tasks") == len(expected_cases)
        and parallel_record.get("final_active_case_tasks") == 0
        and parallel_record.get("observed_parallelism") is True
    )
    security_ok = bool(
        security.get("formal_model_profile_matched") is True
        and security.get("api_key_or_authorization_absent") is True
        and security.get("fixture_model_used") is False
        and security.get("cached_or_recorded_response_used") is False
        and security.get("oracle_opened_by_runner") is False
        and security.get("oracle_passed_to_orchestrator") is False
        and security.get("active_plan_present_in_isolation") is False
        and security.get("evaluation_present_in_isolation") is False
        and security.get("problem_archive_present_in_isolation") is False
    )
    recomputed_run_valid = bool(
        preflight_ok
        and isolation_ok
        and parallel_ok
        and security_ok
        and all(bool(row.get("protocol_valid")) for row in rows_value)
    )
    if bool(report.get("run_valid")) != recomputed_run_valid:
        _fail("result_forgery", "run_valid differs from independently verified evidence")

    positive = [
        row
        for row in scored_rows
        if row["scored"] and row["outcome_class"] in {"existing_route", "first_authoring"}
    ]
    safety_rows = [row for row in scored_rows if row["tier"] == "C0-safety"]
    blocker_rows = [
        row for row in scored_rows if row.get("blocker_bucket") is not None
    ]
    scored = [row for row in scored_rows if row["scored"]]
    family_rows: dict[str, list[Mapping[str, Any]]] = {}
    level_rows: dict[str, list[Mapping[str, Any]]] = {}
    existing_rows: dict[str, list[Mapping[str, Any]]] = {}
    authoring_rows: dict[str, list[Mapping[str, Any]]] = {}
    for row in positive:
        family_rows.setdefault(str(row["family"]), []).append(row)
        level_rows.setdefault(str(row["level"]), []).append(row)
        target = existing_rows if row["outcome_class"] == "existing_route" else authoring_rows
        target.setdefault(str(row["family"]), []).append(row)
    family_macro = _macro(family_rows)
    level_macro = _macro(level_rows)
    existing_macro = _macro(existing_rows)
    authoring_macro = _macro(authoring_rows)
    positive_model_calls = sum(int(row["model_calls"]) for row in positive)
    token_totals: dict[str, int | float] = {}
    for row in positive:
        for key, value in row["token_usage"].items():
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                token_totals[key] = token_totals.get(key, 0) + value
    verified_count = sum(bool(row["capability_success"]) for row in positive)
    safety_correct = sum(bool(row["capability_success"]) for row in safety_rows)
    blocker_bucket_scorecard: dict[str, Any] = {}
    for bucket in sorted(
        {str(row["blocker_bucket"]) for row in blocker_rows}
    ):
        bucket_rows = [row for row in blocker_rows if row["blocker_bucket"] == bucket]
        correct = sum(bool(row["capability_success"]) for row in bucket_rows)
        status_counts: dict[str, int] = {}
        failure_counts: dict[str, int] = {}
        for row in bucket_rows:
            status = str(row["public_status"])
            status_counts[status] = status_counts.get(status, 0) + 1
            failure = str(row.get("failure_code") or "none")
            failure_counts[failure] = failure_counts.get(failure, 0) + 1
        blocker_bucket_scorecard[bucket] = {
            "count": len(bucket_rows),
            "correct": correct,
            "rate": _rate(correct, len(bucket_rows)),
            "zero_model_call_count": sum(
                int(row["model_calls"]) == 0 for row in bucket_rows
            ),
            "public_status_counts": dict(sorted(status_counts.items())),
            "failure_code_counts": dict(sorted(failure_counts.items())),
        }
    wrong_endpoint_acceptance = sum(
        row["public_status"] == "VERIFIED"
        and row.get("failure_code") == "candidate_wrong_endpoint"
        for row in scored_rows
    )
    wrong_direction_acceptance = sum(
        row["public_status"] == "VERIFIED"
        and row.get("failure_code") == "candidate_wrong_direction"
        for row in scored_rows
    )
    erroneous_non_target = sum(
        row["tier"] != "C0-safety" and row["public_status"] == "BLOCKED_NOT_TARGET"
        for row in scored_rows
    )
    nonstandard_axiom_acceptance = sum(
        row["public_status"] == "VERIFIED"
        and row.get("failure_code") == "candidate_nonstandard_axiom"
        for row in scored_rows
    )
    outcome_matrix: dict[str, dict[str, int]] = {}
    for row in scored_rows:
        statuses = outcome_matrix.setdefault(str(row["tier"]), {})
        status = str(row["public_status"])
        statuses[status] = statuses.get(status, 0) + 1
    mutations = run_capability_r0_mutation_audit(bundle)
    oracle_leakage_count = 0
    if not isinstance(security, Mapping) or security.get("oracle_opened_by_runner") is not False:
        oracle_leakage_count = 1
    integrity = {
        "run_id_valid": True,
        "case_evidence_hashes_valid": True,
        "case_result_files_valid": True,
        "manifest_hash_valid": True,
        "suite_hashes_valid": True,
        "oracle_hash_valid": True,
        "target_matrix_hash_valid": True,
        "oracle_opened_only_by_scorer": oracle_leakage_count == 0,
        "r0_mutations_passed": mutations["passed"],
    }
    score_valid = bool(all(integrity.values()))
    score: dict[str, Any] = {
        "schema_version": bundle.manifest.score_schema_version,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "benchmark_id": bundle.manifest.benchmark_id,
        "run_id": report["run_id"],
        "run_valid": bool(report.get("run_valid")),
        "score_valid": score_valid,
        "integrity": integrity,
        "metrics": {
            "scored_case_count": len(scored),
            "positive_case_count": len(positive),
            "verified_at_budget_count": verified_count,
            "verified_at_budget_rate": _rate(verified_count, len(positive)),
            "verified_at_first_attempt_count": sum(
                bool(row["capability_success"] and row["first_attempt_verified"])
                for row in positive
            ),
            "verified_at_first_attempt_rate": _rate(
                sum(
                    bool(row["capability_success"] and row["first_attempt_verified"])
                    for row in positive
                ),
                len(positive),
            ),
            "family_macro_verified_at_budget": family_macro["macro_score"],
            "level_macro_verified_at_budget": level_macro["macro_score"],
            "existing_route_family_macro": existing_macro["macro_score"],
            "first_authoring_family_macro": authoring_macro["macro_score"],
            "safety_correct_count": safety_correct,
            "safety_correct_rate": _rate(safety_correct, len(safety_rows)),
            "cost_scope": "scored_c0_positive",
            "cost_case_count": len(positive),
            "model_calls": positive_model_calls,
            "token_usage": dict(sorted(token_totals.items())),
            "wall_duration_seconds": round(
                sum(float(row["wall_duration_seconds"]) for row in positive), 6
            ),
            "model_calls_per_verified_positive": (
                round(positive_model_calls / verified_count, 6)
                if verified_count
                else None
            ),
        },
        "family_scorecard": family_macro,
        "level_scorecard": level_macro,
        "existing_route_scorecard": existing_macro,
        "first_authoring_scorecard": authoring_macro,
        "outcome_matrix": {
            tier: dict(sorted(statuses.items()))
            for tier, statuses in sorted(outcome_matrix.items())
        },
        "safety": {
            "correct_blocker_count": safety_correct,
            "wrong_direction_acceptance_count": wrong_direction_acceptance,
            "wrong_endpoint_acceptance_count": wrong_endpoint_acceptance,
            "erroneous_non_target_count": erroneous_non_target,
            "nonstandard_axiom_acceptance_count": nonstandard_axiom_acceptance,
            "oracle_leakage_count": oracle_leakage_count,
        },
        "boundary": _boundary(scored_rows),
        "r0_mutation_audit": mutations,
        "cases": scored_rows,
        "provenance": {
            "manifest": {
                "file": str(bundle.manifest.path),
                "sha256": _tagged_sha256(bundle.manifest.path),
            },
            "oracle": {
                "file": str(bundle.manifest.oracle.path),
                "sha256": bundle.manifest.oracle.sha256,
                "opened_by": "independent scorer only",
            },
            "run_report": {
                "file": str(run_report_path.resolve()),
                "sha256": _tagged_sha256(run_report_path.resolve()),
            },
        },
    }
    if bundle.manifest.score_schema_version == CAPABILITY_SCORE_SCHEMA_V2:
        score["metrics"].update(
            {
                "blocker_bucket_case_count": len(blocker_rows),
                "blocker_bucket_correct_count": sum(
                    bool(row["capability_success"]) for row in blocker_rows
                ),
                "blocker_bucket_correct_rate": _rate(
                    sum(bool(row["capability_success"]) for row in blocker_rows),
                    len(blocker_rows),
                ),
            }
        )
        score["blocker_bucket_scorecard"] = blocker_bucket_scorecard
    score["score_id"] = sha256_id(score)
    _write_json(score_report_path.resolve(), score)
    return score


__all__ = [
    "CAPABILITY_BENCHMARK_ID",
    "CAPABILITY_BENCHMARK_ID_V1",
    "CAPABILITY_BENCHMARK_ID_V2",
    "CAPABILITY_MANIFEST_SCHEMA_V1",
    "CAPABILITY_MANIFEST_SCHEMA_V2",
    "CAPABILITY_ORACLE_SCHEMA_V1",
    "CAPABILITY_ORACLE_SCHEMA_V2",
    "CAPABILITY_RUN_SCHEMA_V1",
    "CAPABILITY_RUN_SCHEMA_V2",
    "CAPABILITY_SCORE_SCHEMA_V1",
    "CAPABILITY_SCORE_SCHEMA_V2",
    "CAPABILITY_SPLITS",
    "CAPABILITY_SUITE_SCHEMA_V1",
    "CAPABILITY_SUITE_SCHEMA_V2",
    "CAPABILITY_WORKSPACE_PREFLIGHT_BUILD_TIMEOUT_SECONDS",
    "CapabilityBundle",
    "CapabilityCase",
    "CapabilityContractCounts",
    "CapabilityManifest",
    "CapabilityOracleCase",
    "CapabilitySuite",
    "NPHardCapabilityError",
    "build_capability_isolated_workspace",
    "load_capability_bundle",
    "load_capability_manifest",
    "load_capability_oracle",
    "load_capability_suite",
    "run_capability_r0_mutation_audit",
    "run_np_hard_capability_benchmark",
    "score_np_hard_capability_benchmark",
]
