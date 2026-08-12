"""Versioned benchmark manifests for the hardness agent.

The benchmark manifest is orchestration metadata only.  It never grants a
Lean capability: every runnable case is still checked by ``HardnessAgent``
against an importable module under ``Lean/Reference``.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping

from .catalog import CATALOG_MODES, FULL_CATALOG


MANIFEST_V1 = "hardness_benchmark_v1"
MANIFEST_V2 = "hardness_benchmark_v2"
SUITE_V1 = "hardness_benchmark_suite_v1"
RESULT_V2 = "hardness_benchmark_result_v2"

LEGACY_SCHEMAS = {
    "lean_auto_reduction_v2_hardness_benchmark_v1",
    "opencode_decision_problem_benchmark_manifest_v1",
}

CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9._-]*")
MODULE_RE = re.compile(r"[A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*")
DECLARATION_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

OBJECTIVES = {
    "reduce_to",
    "reduce_to_known_np",
    "reduce_to_known_hardness",
    "prove_in_np",
    "prove_np_complete",
}
PLANNERS = {"deterministic"}
OBJECTIVE_DIRECTIONS = {"source_to_target"}
EXECUTION_LAYERS = {"core_reuse", "optional_authoring", "release_audit"}
VERIFICATION_PROFILES = {"core", "strict-release"}
AUTHORING_MODES = {
    "disabled",
    "deterministic-template",
    "model-auto",
    "model-required",
}
EVALUATION_LANES = {
    "existing_route",
    "deterministic_fixture",
    "model_synthesis",
    "ir_feasibility",
    "input_grounding",
    "open_target",
    "predicate_open_target",
    "stage_i_expansion",
    "frontier_efficiency",
    "core_generalization",
    "typed_authoring",
    "stage_o",
    "quals_completeness",
    "quals_adversarial",
    "representation_comparison",
    "negative",
}
STATUSES = {"VERIFIED", "BLOCKED", "FAILED"}
TARGET_POLICIES = {"fixed", "open"}
REQUIRED_HARDNESS_VALUES = {
    "native_np",
    "native_np_hard",
    "native_np_complete",
}
TARGET_EVIDENCE_KINDS = {
    "native_membership",
    "native_completeness",
    "native_completeness_projection",
    "transported_native_hardness",
    "transported_native_completeness",
}
# Stage G/H known-NP artifacts can consume only membership or completeness.
# Stage I's known-hardness artifact additionally supports hardness transported
# along a Lean-certified path.  Keep the lane vocabularies separate so adding a
# new artifact capability cannot silently widen an older benchmark ABI.
OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS = frozenset(
    {"native_membership", "native_completeness"}
)
KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS = frozenset(
    {"native_completeness", "transported_native_hardness"}
)
INPUT_KINDS = {
    "presented_problem",
    "predicate",
    "parameterized_predicate",
    "closed_prop",
    "open_or_polymorphic",
    "unsupported",
}

ORACLE_MARKERS = (
    ".Oracles.",
    ".Expected.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    ".Legacy.",
)


class BenchmarkManifestError(ValueError):
    """A stable, machine-readable benchmark manifest rejection."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class BenchmarkExpected:
    final_status: str
    final_failure_code: str | None = None
    baseline_status: str | None = None
    baseline_failure_code: str | None = None


@dataclass(frozen=True)
class BenchmarkCase:
    id: str
    suite_id: str
    module: str
    source: str
    objective: str
    expected: BenchmarkExpected
    input_declaration: str | None = None
    input_kind: str = "presented_problem"
    membership: str | None = None
    target: str | None = None
    target_policy: str = "open"
    required_hardness: str | None = None
    allowed_target_evidence: tuple[str, ...] = ()
    minimum_route_atoms: int = 0
    maximum_route_atoms: int | None = None
    maximum_dependencies: int | None = None
    allow_reflexive_target: bool = False
    require_simple_path: bool = False
    planner: str = "deterministic"
    objective_direction: str = "source_to_target"
    execution_layer: str = "core_reuse"
    verification_profile: str = "core"
    catalog_mode: str = FULL_CATALOG
    enabled: bool = True
    min_agent_phase: int = 1
    disabled_reason: str | None = None
    authoring_policy: Mapping[str, Any] = field(default_factory=dict)
    typed_authoring: Mapping[str, Any] = field(default_factory=dict)
    stage_o: Mapping[str, Any] = field(default_factory=dict)
    coverage: Mapping[str, Any] = field(default_factory=dict)
    resources: Mapping[str, Any] = field(default_factory=dict)
    tags: tuple[str, ...] = ()
    legacy_provenance: Mapping[str, Any] | None = None
    group_id: str | None = None
    source_manifest: str = ""
    evaluation_lane: str = "existing_route"
    matched_pair_id: str | None = None
    comparison_group_id: str | None = None
    family_id: str | None = None
    source_form_id: str | None = None
    target_form_id: str | None = None
    hub_ids: tuple[str, ...] = ()

    @property
    def is_positive(self) -> bool:
        return self.expected.final_status == "VERIFIED"

    @property
    def effective_input_declaration(self) -> str:
        return self.input_declaration or self.source

    @property
    def requires_authoring(self) -> bool:
        return bool(self.authoring_policy.get("enabled", False))

    @property
    def resume_from_case(self) -> str | None:
        value = self.authoring_policy.get("resume_from_case")
        return value if isinstance(value, str) else None

    @property
    def remove_candidate_before_resume(self) -> bool:
        return bool(self.authoring_policy.get("remove_candidate_before_resume", False))


@dataclass(frozen=True)
class BenchmarkSuite:
    id: str
    description: str
    cases: tuple[BenchmarkCase, ...]
    source_file: str


@dataclass(frozen=True)
class BenchmarkManifest:
    schema_version: str
    benchmark_id: str
    manifest_file: Path
    suites: tuple[BenchmarkSuite, ...]
    migration_ledger_file: Path | None = None

    @property
    def cases(self) -> tuple[BenchmarkCase, ...]:
        return tuple(case for suite in self.suites for case in suite.cases)


@dataclass(frozen=True)
class SkippedCase:
    case: BenchmarkCase
    code: str
    reason: str


@dataclass(frozen=True)
class BenchmarkSelection:
    runnable: tuple[BenchmarkCase, ...]
    skipped: tuple[SkippedCase, ...]


def _expect_object(value: Any, *, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BenchmarkManifestError("invalid_schema", f"{label} must be a JSON object")
    return value


def _expect_string(value: Any, *, label: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value.strip()):
        raise BenchmarkManifestError("invalid_schema", f"{label} must be a non-empty string")
    return value


def _expect_string_list(value: Any, *, label: str, allow_empty: bool = True) -> tuple[str, ...]:
    if not isinstance(value, list) or (not allow_empty and not value):
        qualifier = "non-empty " if not allow_empty else ""
        raise BenchmarkManifestError("invalid_schema", f"{label} must be a {qualifier}list")
    result: list[str] = []
    for index, item in enumerate(value):
        result.append(_expect_string(item, label=f"{label}[{index}]"))
    return tuple(result)


def _read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise BenchmarkManifestError("manifest_not_found", str(path)) from error
    except json.JSONDecodeError as error:
        raise BenchmarkManifestError(
            "invalid_json", f"{path}:{error.lineno}:{error.colno}: {error.msg}"
        ) from error
    return _expect_object(value, label=str(path))


def _repository_root(manifest_path: Path) -> Path:
    for parent in (manifest_path.parent, *manifest_path.parents):
        if (parent / "Lean" / "Reference").is_dir() and (parent / "Benchmark").is_dir():
            return parent
    raise BenchmarkManifestError(
        "repository_root_not_found",
        f"could not find Lean/Reference above {manifest_path}",
    )


def _relative_file(base: Path, value: str, *, label: str) -> Path:
    path = Path(value)
    if path.is_absolute():
        raise BenchmarkManifestError("unsafe_manifest_path", f"{label} escapes benchmark root")
    if ".." in path.parts:
        repository = _repository_root(base)
        resolved = (base / path).resolve()
        try:
            resolved.relative_to(repository.resolve())
        except ValueError as error:
            raise BenchmarkManifestError(
                "unsafe_manifest_path", f"{label} escapes benchmark root"
            ) from error
        if "Legacy" in resolved.parts:
            raise BenchmarkManifestError(
                "legacy_suite_forbidden", f"active suite cannot be loaded from {resolved}"
            )
        return resolved
    if path.parts and path.parts[0] in ("Benchmark", "Lean"):
        root = _repository_root(base)
        resolved = (root / path).resolve()
        try:
            resolved.relative_to(root.resolve())
        except ValueError as error:
            raise BenchmarkManifestError(
                "unsafe_manifest_path", f"{label} escapes benchmark root"
            ) from error
    else:
        resolved = (base / path).resolve()
        try:
            resolved.relative_to(base.resolve())
        except ValueError as error:
            raise BenchmarkManifestError(
                "unsafe_manifest_path", f"{label} escapes benchmark root"
            ) from error
    if "Legacy" in resolved.parts:
        raise BenchmarkManifestError(
            "legacy_suite_forbidden", f"active suite cannot be loaded from {resolved}"
        )
    return resolved


def _validate_identifier(value: str, *, label: str, pattern: re.Pattern[str]) -> str:
    if not pattern.fullmatch(value):
        raise BenchmarkManifestError("invalid_identifier", f"invalid {label}: {value!r}")
    return value


def _validate_public_lean_name(value: str, *, label: str, module: bool = False) -> str:
    pattern = MODULE_RE if module else DECLARATION_RE
    _validate_identifier(value, label=label, pattern=pattern)
    if any(marker in f".{value}." for marker in ORACLE_MARKERS):
        raise BenchmarkManifestError(
            "oracle_reference_forbidden", f"{label} references non-public benchmark data: {value}"
        )
    return value


def _parse_expected(raw: Any, *, label: str) -> BenchmarkExpected:
    value = _expect_object(raw, label=label)
    final_status = _expect_string(value.get("final_status"), label=f"{label}.final_status")
    if final_status not in STATUSES:
        raise BenchmarkManifestError(
            "invalid_schema", f"{label}.final_status must be one of {sorted(STATUSES)}"
        )
    final_failure_code = value.get("final_failure_code")
    if final_failure_code is not None:
        final_failure_code = _expect_string(
            final_failure_code, label=f"{label}.final_failure_code"
        )
    if final_status != "VERIFIED" and not final_failure_code:
        raise BenchmarkManifestError(
            "invalid_schema", f"{label}.final_failure_code is required for {final_status}"
        )
    baseline_status = value.get("baseline_status")
    if baseline_status is not None:
        baseline_status = _expect_string(baseline_status, label=f"{label}.baseline_status")
        if baseline_status not in STATUSES:
            raise BenchmarkManifestError(
                "invalid_schema", f"{label}.baseline_status must be one of {sorted(STATUSES)}"
            )
    baseline_failure_code = value.get("baseline_failure_code")
    if baseline_failure_code is not None:
        baseline_failure_code = _expect_string(
            baseline_failure_code, label=f"{label}.baseline_failure_code"
        )
        if baseline_status is None:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"{label}.baseline_status is required with baseline_failure_code",
            )
    return BenchmarkExpected(
        final_status=final_status,
        final_failure_code=final_failure_code,
        baseline_status=baseline_status,
        baseline_failure_code=baseline_failure_code,
    )


def _mapping(value: Any, *, label: str) -> Mapping[str, Any]:
    if value is None:
        return {}
    return _expect_object(value, label=label)


def _positive_int(value: Any, *, label: str, default: int) -> int:
    if value is None:
        return default
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise BenchmarkManifestError("invalid_schema", f"{label} must be a positive integer")
    return value


def _optional_nonnegative_int(value: Any, *, label: str) -> int | None:
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise BenchmarkManifestError(
            "invalid_schema", f"{label} must be a non-negative integer"
        )
    return value


def _parse_v2_case(
    raw: Any,
    *,
    suite_id: str,
    source_manifest: Path,
    repository_root: Path,
) -> BenchmarkCase:
    value = _expect_object(raw, label=f"case in {source_manifest}")
    case_id = _validate_identifier(
        _expect_string(value.get("id"), label="case.id"), label="case id", pattern=CASE_ID_RE
    )
    module = _validate_public_lean_name(
        _expect_string(value.get("module"), label=f"case {case_id}.module"),
        label=f"case {case_id} module",
        module=True,
    )
    if not module.startswith("Benchmark.Hardness.Inputs."):
        raise BenchmarkManifestError(
            "non_public_input_module",
            f"case {case_id} module must be under Benchmark.Hardness.Inputs",
        )
    input_file = repository_root / "Lean" / "Reference" / Path(*module.split(".")).with_suffix(".lean")
    if not input_file.is_file():
        raise BenchmarkManifestError(
            "input_module_not_found", f"case {case_id} module has no local file: {module}"
        )

    source = _validate_public_lean_name(
        _expect_string(value.get("source"), label=f"case {case_id}.source"),
        label=f"case {case_id} source",
    )
    input_declaration = _validate_public_lean_name(
        _expect_string(
            value.get("input_declaration", source),
            label=f"case {case_id}.input_declaration",
        ),
        label=f"case {case_id} input declaration",
    )
    input_kind = _expect_string(
        value.get("input_kind", "presented_problem"),
        label=f"case {case_id}.input_kind",
    )
    if input_kind not in INPUT_KINDS:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.input_kind must be one of {sorted(INPUT_KINDS)}",
        )
    membership_raw = value.get("membership")
    membership = (
        _validate_public_lean_name(
            _expect_string(membership_raw, label=f"case {case_id}.membership"),
            label=f"case {case_id} membership",
        )
        if membership_raw is not None
        else None
    )
    target_raw = value.get("target")
    target = (
        _validate_public_lean_name(
            _expect_string(target_raw, label=f"case {case_id}.target"),
            label=f"case {case_id} target",
        )
        if target_raw is not None
        else None
    )

    objective = _expect_string(value.get("objective"), label=f"case {case_id}.objective")
    if objective not in OBJECTIVES:
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id}.objective must be one of {sorted(OBJECTIVES)}"
        )
    objective_direction = _expect_string(
        value.get("objective_direction", "source_to_target"),
        label=f"case {case_id}.objective_direction",
    )
    if objective_direction not in OBJECTIVE_DIRECTIONS:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.objective_direction must be one of "
            f"{sorted(OBJECTIVE_DIRECTIONS)}",
        )
    target_policy = _expect_string(
        value.get("target_policy", "fixed" if target else "open"),
        label=f"case {case_id}.target_policy",
    )
    if target_policy not in TARGET_POLICIES:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.target_policy must be one of {sorted(TARGET_POLICIES)}",
        )
    if objective == "reduce_to" and (target_policy != "fixed" or not target):
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id} reduce_to requires a fixed target"
        )
    if objective in {"prove_in_np", "prove_np_complete"} and target is not None:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} {objective} uses source as the exact problem and forbids target",
        )
    if target_policy == "fixed" and not target:
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id} fixed target_policy requires target"
        )

    required_hardness_raw = value.get("required_hardness")
    required_hardness = (
        _expect_string(
            required_hardness_raw, label=f"case {case_id}.required_hardness"
        )
        if required_hardness_raw is not None
        else None
    )
    if (
        required_hardness is not None
        and required_hardness not in REQUIRED_HARDNESS_VALUES
    ):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.required_hardness must be one of "
            f"{sorted(REQUIRED_HARDNESS_VALUES)}",
        )
    allowed_target_evidence_raw = value.get("allowed_target_evidence")
    allowed_target_evidence = (
        _expect_string_list(
            allowed_target_evidence_raw,
            label=f"case {case_id}.allowed_target_evidence",
            allow_empty=False,
        )
        if allowed_target_evidence_raw is not None
        else ()
    )
    unknown_target_evidence = set(allowed_target_evidence) - TARGET_EVIDENCE_KINDS
    if unknown_target_evidence:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.allowed_target_evidence contains unsupported values: "
            f"{sorted(unknown_target_evidence)}",
        )
    if len(set(allowed_target_evidence)) != len(allowed_target_evidence):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.allowed_target_evidence must not contain duplicates",
        )
    minimum_route_atoms = _optional_nonnegative_int(
        value.get("minimum_route_atoms", 0),
        label=f"case {case_id}.minimum_route_atoms",
    )
    assert minimum_route_atoms is not None
    maximum_route_atoms = _optional_nonnegative_int(
        value.get("maximum_route_atoms"),
        label=f"case {case_id}.maximum_route_atoms",
    )
    maximum_dependencies = _optional_nonnegative_int(
        value.get("maximum_dependencies"),
        label=f"case {case_id}.maximum_dependencies",
    )
    allow_reflexive_target = value.get("allow_reflexive_target", False)
    if not isinstance(allow_reflexive_target, bool):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.allow_reflexive_target must be boolean",
        )
    require_simple_path = value.get("require_simple_path", False)
    if not isinstance(require_simple_path, bool):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.require_simple_path must be boolean",
        )
    if maximum_route_atoms is not None and minimum_route_atoms > maximum_route_atoms:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.minimum_route_atoms exceeds maximum_route_atoms",
        )

    planner = _expect_string(
        value.get("planner", "deterministic"), label=f"case {case_id}.planner"
    )
    if planner not in PLANNERS:
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id}.planner must be one of {sorted(PLANNERS)}"
        )
    catalog_mode = _expect_string(
        value.get("catalog_mode", FULL_CATALOG), label=f"case {case_id}.catalog_mode"
    )
    if catalog_mode not in CATALOG_MODES:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.catalog_mode must be one of {sorted(CATALOG_MODES)}",
        )
    enabled = value.get("enabled", True)
    if not isinstance(enabled, bool):
        raise BenchmarkManifestError("invalid_schema", f"case {case_id}.enabled must be boolean")
    min_agent_phase = _positive_int(
        value.get("min_agent_phase"), label=f"case {case_id}.min_agent_phase", default=1
    )
    disabled_reason = value.get("disabled_reason")
    if disabled_reason is not None:
        disabled_reason = _expect_string(
            disabled_reason, label=f"case {case_id}.disabled_reason"
        )
    if not enabled and not disabled_reason:
        raise BenchmarkManifestError(
            "invalid_schema", f"disabled case {case_id} requires disabled_reason"
        )
    expected = _parse_expected(value.get("expected"), label=f"case {case_id}.expected")

    resources = _mapping(value.get("resources"), label=f"case {case_id}.resources")
    coverage = _mapping(value.get("coverage"), label=f"case {case_id}.coverage")
    typed_authoring = _mapping(
        value.get("typed_authoring"), label=f"case {case_id}.typed_authoring"
    )
    stage_o = _mapping(value.get("stage_o"), label=f"case {case_id}.stage_o")
    for resource_name in (
        "lean_timeout_seconds",
        "model_timeout_seconds",
        "model_max_tokens",
        "max_model_calls",
    ):
        if resource_name in resources:
            _positive_int(
                resources[resource_name],
                label=f"case {case_id}.resources.{resource_name}",
                default=1,
            )
    authoring_policy = _mapping(
        value.get("authoring_policy"), label=f"case {case_id}.authoring_policy"
    )
    authoring_enabled = authoring_policy.get("enabled", False)
    if not isinstance(authoring_enabled, bool):
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id}.authoring_policy.enabled must be boolean"
        )
    authoring_mode = authoring_policy.get(
        "mode", "deterministic-template" if authoring_enabled else "disabled"
    )
    if not isinstance(authoring_mode, str) or authoring_mode not in AUTHORING_MODES:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.authoring_policy.mode must be one of "
            f"{sorted(AUTHORING_MODES)}",
        )
    if authoring_enabled and authoring_mode == "disabled":
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} enables authoring but selects disabled mode",
        )
    if not authoring_enabled and authoring_mode != "disabled":
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} selects {authoring_mode} but does not enable authoring",
        )
    if "attempt_budget" in authoring_policy:
        _positive_int(
            authoring_policy["attempt_budget"],
            label=f"case {case_id}.authoring_policy.attempt_budget",
            default=1,
        )
    resume_from_case = authoring_policy.get("resume_from_case")
    if resume_from_case is not None:
        resume_from_case = _validate_identifier(
            _expect_string(
                resume_from_case,
                label=f"case {case_id}.authoring_policy.resume_from_case",
            ),
            label=f"case {case_id} resume source",
            pattern=CASE_ID_RE,
        )
        if authoring_enabled or authoring_mode != "disabled":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} resume audit must disable new authoring",
            )
    remove_candidate_before_resume = authoring_policy.get(
        "remove_candidate_before_resume", False
    )
    if not isinstance(remove_candidate_before_resume, bool):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.authoring_policy.remove_candidate_before_resume must be boolean",
        )
    if remove_candidate_before_resume and resume_from_case is None:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} removes a candidate without resume_from_case",
        )
    execution_layer_default = (
        "optional_authoring"
        if authoring_enabled or resume_from_case is not None
        else "core_reuse"
    )
    execution_layer = _expect_string(
        value.get("execution_layer", execution_layer_default),
        label=f"case {case_id}.execution_layer",
    )
    if execution_layer not in EXECUTION_LAYERS:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.execution_layer must be one of {sorted(EXECUTION_LAYERS)}",
        )
    if execution_layer == "core_reuse" and (authoring_enabled or resume_from_case is not None):
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id} core_reuse must disable authoring"
        )
    if execution_layer == "optional_authoring" and not (
        authoring_enabled or resume_from_case is not None
    ):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} optional_authoring requires authoring or a resume audit",
        )
    verification_profile = _expect_string(
        value.get(
            "verification_profile",
            "strict-release" if execution_layer != "core_reuse" else "core",
        ),
        label=f"case {case_id}.verification_profile",
    )
    if verification_profile not in VERIFICATION_PROFILES:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.verification_profile must be one of "
            f"{sorted(VERIFICATION_PROFILES)}",
        )
    if catalog_mode != FULL_CATALOG:
        if objective != "reduce_to" or target_policy != "fixed":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} non-full catalog modes require fixed-target reduce_to",
            )
        if execution_layer != "core_reuse" or authoring_enabled:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} flat/IR catalog modes require core_reuse with authoring disabled",
            )
    evaluation_lane = value.get("evaluation_lane")
    if evaluation_lane is None:
        if authoring_mode in {"model-auto", "model-required"}:
            evaluation_lane = "model_synthesis"
        elif authoring_enabled:
            evaluation_lane = "deterministic_fixture"
        elif expected.final_status == "VERIFIED":
            evaluation_lane = "existing_route"
        else:
            evaluation_lane = "negative"
    evaluation_lane = _expect_string(
        evaluation_lane, label=f"case {case_id}.evaluation_lane"
    )
    if evaluation_lane not in EVALUATION_LANES:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id}.evaluation_lane must be one of {sorted(EVALUATION_LANES)}",
        )
    if evaluation_lane == "model_synthesis" and authoring_mode not in {
        "model-auto",
        "model-required",
    }:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} model_synthesis lane requires model authoring mode",
        )
    if evaluation_lane in {
        "open_target",
        "predicate_open_target",
        "stage_i_expansion",
        "frontier_efficiency",
    }:
        required_open_target_fields = {
            "required_hardness",
            "allowed_target_evidence",
            "maximum_route_atoms",
            "maximum_dependencies",
            "allow_reflexive_target",
        }
        missing_open_target_fields = sorted(required_open_target_fields - set(value))
        if missing_open_target_fields:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} {evaluation_lane} requires "
                f"{', '.join(missing_open_target_fields)}",
            )
        allowed_input_kinds = (
            {"presented_problem"}
            if evaluation_lane == "open_target"
            else (
                {"predicate", "closed_prop"}
                if evaluation_lane == "predicate_open_target"
                else {"presented_problem", "predicate", "closed_prop"}
            )
        )
        expected_objective = (
            "reduce_to_known_hardness"
            if evaluation_lane in {"stage_i_expansion", "frontier_efficiency"}
            else "reduce_to_known_np"
        )
        if (
            objective != expected_objective
            or objective_direction != "source_to_target"
            or target_policy != "open"
            or target is not None
            or membership is not None
            or catalog_mode != FULL_CATALOG
            or input_kind not in allowed_input_kinds
            or execution_layer != "core_reuse"
            or verification_profile != "core"
            or authoring_enabled
            or authoring_mode != "disabled"
            or required_hardness is None
            or not allowed_target_evidence
            or not set(allowed_target_evidence).issubset(
                KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS
                if evaluation_lane in {"stage_i_expansion", "frontier_efficiency"}
                else OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS
            )
            or maximum_route_atoms is None
            or maximum_dependencies is None
            or (
                evaluation_lane in {"stage_i_expansion", "frontier_efficiency"}
                and (
                    required_hardness != "native_np_hard"
                    or "transported_native_hardness"
                    not in allowed_target_evidence
                    or minimum_route_atoms <= 0
                    or not require_simple_path
                )
            )
        ):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} is outside the {evaluation_lane} lane ABI",
            )
    elif evaluation_lane == "core_generalization":
        if (
            objective_direction != "source_to_target"
            or catalog_mode != FULL_CATALOG
            or input_kind not in {"presented_problem", "predicate", "closed_prop"}
            or execution_layer != "core_reuse"
            or verification_profile != "core"
            or authoring_enabled
            or authoring_mode != "disabled"
            or maximum_route_atoms is None
            or maximum_dependencies is None
            or not require_simple_path
        ):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} is outside the core_generalization lane ABI",
            )
        if objective == "reduce_to" and (
            target_policy != "fixed"
            or target is None
            or required_hardness is not None
            or allowed_target_evidence
        ):
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} has an invalid fixed reduction request"
            )
        if objective in {"reduce_to_known_np", "reduce_to_known_hardness"} and (
            target_policy != "open"
            or target is not None
            or required_hardness is None
            or not allowed_target_evidence
        ):
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} has an invalid open reduction request"
            )
        if objective in {"prove_in_np", "prove_np_complete"} and (
            target_policy != "open"
            or target is not None
            or required_hardness is not None
            or allowed_target_evidence
        ):
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} has an invalid exact evidence request"
            )
    elif evaluation_lane == "stage_o":
        if not stage_o:
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id}.stage_o contract is required"
            )
        if typed_authoring:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} must use the versioned Stage O contract instead of Stage M typed_authoring",
            )
        if (
            objective_direction != "source_to_target"
            or catalog_mode != FULL_CATALOG
            or input_kind
            not in {"presented_problem", "predicate", "parameterized_predicate"}
            or verification_profile != "strict-release"
            or maximum_route_atoms is None
            or maximum_dependencies is None
            or not require_simple_path
        ):
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} is outside the stage_o lane ABI"
            )
        if execution_layer == "core_reuse" and authoring_enabled:
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} core Stage O case enables authoring"
            )
        if execution_layer == "optional_authoring" and not authoring_enabled:
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} Stage O authoring case disables authoring"
            )
    elif evaluation_lane in {"typed_authoring", "quals_completeness"}:
        required_request_keys = {
            "schema_version",
            "active_node",
            "expected_capability_head",
            "allowed_packet_kinds",
            "required_checker_combinators",
            "witness_shape",
            "model_selection_required",
        }
        if set(typed_authoring) != required_request_keys:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring keys must exactly equal "
                f"{sorted(required_request_keys)}",
            )
        if typed_authoring.get("schema_version") != "hardness_typed_authoring_request_v1":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring uses an unsupported schema",
            )
        active_node = _expect_string(
            typed_authoring.get("active_node"),
            label=f"case {case_id}.typed_authoring.active_node",
        )
        if active_node not in {
            "presentation_capability",
            "reduction_capability",
            "membership_capability",
        }:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring.active_node is unsupported",
            )
        expected_head = _validate_public_lean_name(
            _expect_string(
                typed_authoring.get("expected_capability_head"),
                label=f"case {case_id}.typed_authoring.expected_capability_head",
            ),
            label=f"case {case_id} typed authoring capability head",
        )
        packet_kinds = _expect_string_list(
            typed_authoring.get("allowed_packet_kinds"),
            label=f"case {case_id}.typed_authoring.allowed_packet_kinds",
            allow_empty=False,
        )
        allowed_packet_kinds = {
            "route_packet",
            "gadget_packet",
            "membership_packet",
            "tm_certificate_packet",
        }
        if not set(packet_kinds).issubset(allowed_packet_kinds) or len(
            set(packet_kinds)
        ) != len(packet_kinds):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring.allowed_packet_kinds is invalid",
            )
        checker_combinators = _expect_string_list(
            typed_authoring.get("required_checker_combinators"),
            label=f"case {case_id}.typed_authoring.required_checker_combinators",
            allow_empty=True,
        )
        if len(set(checker_combinators)) != len(checker_combinators):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring.required_checker_combinators contains duplicates",
            )
        witness_shape = _expect_string(
            typed_authoring.get("witness_shape"),
            label=f"case {case_id}.typed_authoring.witness_shape",
        )
        model_selection_required = typed_authoring.get("model_selection_required")
        if not isinstance(model_selection_required, bool):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring.model_selection_required must be boolean",
            )
        expected_head_by_node = {
            "presentation_capability": (
                "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
            ),
            "reduction_capability": (
                "ComplexityReduction.Certificate.CertifiedReduction"
            ),
            "membership_capability": (
                "ComplexityReduction.Certificate.NativeTMInNP"
            ),
        }
        if expected_head != expected_head_by_node[active_node]:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id}.typed_authoring capability head does not match active_node",
            )
        if evaluation_lane == "quals_completeness":
            objective_valid = (
                (
                    objective == "prove_np_complete"
                    and target_policy == "open"
                    and target is None
                    and active_node == "membership_capability"
                )
                or (
                    objective == "reduce_to"
                    and target_policy == "fixed"
                    and target is not None
                    and active_node == "reduction_capability"
                )
            )
        else:
            objective_valid = (
                objective in {"reduce_to", "prove_in_np"}
                and (active_node == "membership_capability")
                == (objective == "prove_in_np")
                and (
                    objective != "reduce_to"
                    or (target_policy == "fixed" and target is not None)
                )
                and (
                    objective != "prove_in_np"
                    or (target_policy == "open" and target is None)
                )
            )
        if (
            objective_direction != "source_to_target"
            or catalog_mode != FULL_CATALOG
            or input_kind != "presented_problem"
            or execution_layer != "optional_authoring"
            or verification_profile != "strict-release"
            or not authoring_enabled
            or authoring_mode == "disabled"
            or target_policy not in {"fixed", "open"}
            or not objective_valid
            or not witness_shape
        ):
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} is outside the {evaluation_lane} lane ABI",
            )
    elif typed_authoring or stage_o:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} uses authoring contract fields outside their versioned lane",
        )
    elif any(
        field_name in value
        for field_name in (
            "required_hardness",
            "allowed_target_evidence",
            "minimum_route_atoms",
            "maximum_route_atoms",
            "maximum_dependencies",
            "allow_reflexive_target",
            "require_simple_path",
        )
    ):
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} uses open-target policy fields outside the open_target lane",
        )
    tags = _expect_string_list(
        value.get("tags", []), label=f"case {case_id}.tags", allow_empty=False
    )
    group_id = value.get("group_id")
    if group_id is not None:
        group_id = _validate_identifier(
            _expect_string(group_id, label=f"case {case_id}.group_id"),
            label=f"case {case_id} group id",
            pattern=CASE_ID_RE,
        )

    def optional_case_identifier(field_name: str) -> str | None:
        raw_value = value.get(field_name)
        if raw_value is None:
            return None
        return _validate_identifier(
            _expect_string(raw_value, label=f"case {case_id}.{field_name}"),
            label=f"case {case_id} {field_name}",
            pattern=CASE_ID_RE,
        )

    matched_pair_id = optional_case_identifier("matched_pair_id")
    comparison_group_id = optional_case_identifier("comparison_group_id")
    family_id = optional_case_identifier("family_id")
    source_form_id = optional_case_identifier("source_form_id")
    target_form_id = optional_case_identifier("target_form_id")
    hub_ids = tuple(
        _validate_identifier(
            hub_id,
            label=f"case {case_id} hub id",
            pattern=CASE_ID_RE,
        )
        for hub_id in _expect_string_list(
            value.get("hub_ids", []), label=f"case {case_id}.hub_ids", allow_empty=True
        )
    )
    if len(set(hub_ids)) != len(hub_ids):
        raise BenchmarkManifestError(
            "invalid_schema", f"case {case_id}.hub_ids must not contain duplicates"
        )
    if evaluation_lane == "ir_feasibility":
        required_study_fields = {
            "matched_pair_id": matched_pair_id,
            "family_id": family_id,
            "source_form_id": source_form_id,
            "target_form_id": target_form_id,
        }
        missing = [name for name, field_value in required_study_fields.items() if not field_value]
        if missing:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} ir_feasibility requires {', '.join(missing)}",
            )
        if not hub_ids:
            raise BenchmarkManifestError(
                "invalid_schema", f"case {case_id} ir_feasibility requires hub_ids"
            )
        if catalog_mode == FULL_CATALOG:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} ir_feasibility requires flat_api or ir_components",
            )
        if execution_layer != "core_reuse" or verification_profile != "core":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} ir_feasibility must use core_reuse/core",
            )
        if coverage.get("forbid_model_call") is not True:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} ir_feasibility must explicitly forbid model calls",
            )
        if catalog_mode == "flat_api" and coverage.get(
            "required_resolution_class"
        ) != "direct_or_final_facade":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} flat_api must require direct_or_final_facade resolution",
            )
        if catalog_mode == "ir_components" and coverage.get("forbid_final_facade") is not True:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} ir_components must explicitly forbid final facades",
            )
    elif evaluation_lane == "representation_comparison":
        if not comparison_group_id:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} representation_comparison requires comparison_group_id",
            )
        if matched_pair_id is not None and matched_pair_id != comparison_group_id:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} matched_pair_id must equal comparison_group_id when both are set",
            )
        if catalog_mode == FULL_CATALOG:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} representation_comparison requires flat_api or ir_components",
            )
        if execution_layer != "core_reuse" or verification_profile != "core":
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} representation_comparison must use core_reuse/core",
            )
        if coverage.get("forbid_model_call") is True:
            raise BenchmarkManifestError(
                "invalid_schema",
                f"case {case_id} representation_comparison must permit model calls",
            )
    elif catalog_mode != FULL_CATALOG:
        raise BenchmarkManifestError(
            "invalid_schema",
            f"case {case_id} non-full catalog mode requires ir_feasibility or "
            "representation_comparison lane",
        )

    legacy_provenance = value.get("legacy_provenance")
    if legacy_provenance is not None:
        legacy_provenance = _expect_object(
            legacy_provenance, label=f"case {case_id}.legacy_provenance"
        )
    return BenchmarkCase(
        id=case_id,
        suite_id=suite_id,
        module=module,
        source=source,
        input_declaration=input_declaration,
        input_kind=input_kind,
        membership=membership,
        target=target,
        objective=objective,
        objective_direction=objective_direction,
        target_policy=target_policy,
        required_hardness=required_hardness,
        allowed_target_evidence=allowed_target_evidence,
        minimum_route_atoms=minimum_route_atoms,
        maximum_route_atoms=maximum_route_atoms,
        maximum_dependencies=maximum_dependencies,
        allow_reflexive_target=allow_reflexive_target,
        require_simple_path=require_simple_path,
        planner=planner,
        execution_layer=execution_layer,
        verification_profile=verification_profile,
        catalog_mode=catalog_mode,
        enabled=enabled,
        min_agent_phase=min_agent_phase,
        disabled_reason=disabled_reason,
        authoring_policy=authoring_policy,
        typed_authoring=typed_authoring,
        stage_o=stage_o,
        expected=expected,
        coverage=coverage,
        resources=resources,
        tags=tags,
        legacy_provenance=legacy_provenance,
        group_id=group_id,
        source_manifest=str(source_manifest),
        evaluation_lane=evaluation_lane,
        matched_pair_id=matched_pair_id,
        comparison_group_id=comparison_group_id,
        family_id=family_id,
        source_form_id=source_form_id,
        target_form_id=target_form_id,
        hub_ids=hub_ids,
    )


def _parse_v1_cases(
    raw_cases: Any, *, manifest_path: Path, repository_root: Path
) -> tuple[BenchmarkCase, ...]:
    if not isinstance(raw_cases, list):
        raise BenchmarkManifestError("invalid_schema", "v1 cases must be a list")
    cases: list[BenchmarkCase] = []
    for raw in raw_cases:
        value = _expect_object(raw, label="v1 case")
        converted = {
            "id": value.get("id"),
            "module": value.get("module"),
            "source": value.get("source"),
            "membership": value.get("membership"),
            "target": value.get("target"),
            "objective": value.get("objective"),
            "target_policy": "fixed" if value.get("target") else "open",
            "planner": "deterministic",
            "min_agent_phase": 1,
            "enabled": True,
            "expected": {
                "final_status": value.get("expected_status"),
                "final_failure_code": value.get("expected_failure_code"),
            },
            "tags": ["compatibility-v1"],
        }
        # Historical v1 blocked cases did not carry a failure code.  Preserve
        # compatibility while still making the normalized record explicit.
        if converted["expected"]["final_status"] != "VERIFIED" and not converted["expected"][
            "final_failure_code"
        ]:
            converted["expected"]["final_failure_code"] = "no_registry_path"
        cases.append(
            _parse_v2_case(
                converted,
                suite_id="compatibility-v1",
                source_manifest=manifest_path,
                repository_root=repository_root,
            )
        )
    return tuple(cases)


def _resume_goal_signature(case: BenchmarkCase) -> tuple[Any, ...]:
    return (
        case.module,
        case.source,
        case.membership,
        case.target,
        case.objective,
        case.objective_direction,
        case.target_policy,
        case.required_hardness,
        case.allowed_target_evidence,
        case.minimum_route_atoms,
        case.maximum_route_atoms,
        case.maximum_dependencies,
        case.allow_reflexive_target,
        case.require_simple_path,
        case.catalog_mode,
    )


def _validate_resume_dependencies(cases: Iterable[BenchmarkCase]) -> None:
    case_list = tuple(cases)
    by_id = {case.id: case for case in case_list}
    used_sources: set[str] = set()
    for case in case_list:
        source_id = case.resume_from_case
        if source_id is None:
            continue
        source = by_id.get(source_id)
        if source is None:
            raise BenchmarkManifestError(
                "unknown_resume_source", f"case {case.id} references {source_id}"
            )
        if source.resume_from_case is not None:
            raise BenchmarkManifestError(
                "invalid_resume_dependency",
                f"case {case.id} cannot resume from another resume audit",
            )
        if source_id in used_sources:
            raise BenchmarkManifestError(
                "duplicate_resume_audit",
                f"multiple cases try to consume candidate state from {source_id}",
            )
        used_sources.add(source_id)
        if source.suite_id != case.suite_id or not case.group_id or source.group_id != case.group_id:
            raise BenchmarkManifestError(
                "invalid_resume_dependency",
                f"case {case.id} and {source_id} must share one suite and non-empty group_id",
            )
        if _resume_goal_signature(source) != _resume_goal_signature(case):
            raise BenchmarkManifestError(
                "resume_goal_mismatch",
                f"case {case.id} does not have the same content-addressed goal as {source_id}",
            )
        if source.expected.final_status != "VERIFIED" or not source.requires_authoring:
            raise BenchmarkManifestError(
                "invalid_resume_dependency",
                f"resume source {source_id} must be an expected VERIFIED authoring case",
            )
        if case.expected.final_status != "BLOCKED" or not case.remove_candidate_before_resume:
            raise BenchmarkManifestError(
                "invalid_resume_dependency",
                f"case {case.id} must remove the candidate and expect BLOCKED",
            )


def _ir_matched_signature(case: BenchmarkCase) -> tuple[Any, ...]:
    return (
        case.suite_id,
        case.group_id,
        case.module,
        case.source,
        case.membership,
        case.target,
        case.objective,
        case.objective_direction,
        case.target_policy,
        case.required_hardness,
        case.allowed_target_evidence,
        case.minimum_route_atoms,
        case.maximum_route_atoms,
        case.maximum_dependencies,
        case.allow_reflexive_target,
        case.require_simple_path,
        case.planner,
        case.execution_layer,
        case.verification_profile,
        case.enabled,
        case.min_agent_phase,
        dict(case.authoring_policy),
        dict(case.resources),
        case.family_id,
        case.source_form_id,
        case.target_form_id,
        case.hub_ids,
        case.expected,
    )


def _validate_ir_matched_pairs(cases: Iterable[BenchmarkCase]) -> None:
    pairs: dict[str, list[BenchmarkCase]] = {}
    for case in cases:
        if case.evaluation_lane != "ir_feasibility":
            continue
        assert case.matched_pair_id is not None
        if case.expected.final_status != "VERIFIED":
            raise BenchmarkManifestError(
                "invalid_ir_matched_pair",
                f"case {case.id} ir_feasibility is reserved for expected VERIFIED pairs",
            )
        pairs.setdefault(case.matched_pair_id, []).append(case)

    for pair_id, pair_cases in sorted(pairs.items()):
        if len(pair_cases) != 2:
            raise BenchmarkManifestError(
                "invalid_ir_matched_pair",
                f"matched pair {pair_id} must contain exactly flat_api and ir_components",
            )
        by_mode = {case.catalog_mode: case for case in pair_cases}
        if set(by_mode) != {"flat_api", "ir_components"}:
            raise BenchmarkManifestError(
                "invalid_ir_matched_pair",
                f"matched pair {pair_id} must contain one flat_api and one ir_components case",
            )
        flat = by_mode["flat_api"]
        ir = by_mode["ir_components"]
        if _ir_matched_signature(flat) != _ir_matched_signature(ir):
            raise BenchmarkManifestError(
                "ir_matched_pair_mismatch",
                f"matched pair {pair_id} changes fields other than id/catalog_mode",
            )


def load_benchmark_suite(path: Path) -> BenchmarkSuite:
    """Load one active suite without adding it to the main benchmark manifest."""

    suite_path = path.resolve()
    suite_raw = _read_json(suite_path)
    suite_schema = _expect_string(
        suite_raw.get("schema_version"), label=f"{suite_path}.schema_version"
    )
    if suite_schema != SUITE_V1:
        raise BenchmarkManifestError(
            "unsupported_suite_schema",
            f"{suite_path} uses {suite_schema!r}, expected {SUITE_V1!r}",
        )
    repository_root = _repository_root(suite_path)
    suite_id = _validate_identifier(
        _expect_string(suite_raw.get("suite_id"), label=f"{suite_path}.suite_id"),
        label="suite id",
        pattern=CASE_ID_RE,
    )
    description = _expect_string(
        suite_raw.get("description", ""),
        label=f"suite {suite_id}.description",
        allow_empty=True,
    )
    raw_cases = suite_raw.get("cases")
    if not isinstance(raw_cases, list):
        raise BenchmarkManifestError(
            "invalid_schema", f"suite {suite_id}.cases must be a list"
        )
    cases: list[BenchmarkCase] = []
    seen_case_ids: set[str] = set()
    for raw_case in raw_cases:
        case = _parse_v2_case(
            raw_case,
            suite_id=suite_id,
            source_manifest=suite_path,
            repository_root=repository_root,
        )
        if case.id in seen_case_ids:
            raise BenchmarkManifestError("duplicate_case_id", case.id)
        seen_case_ids.add(case.id)
        cases.append(case)
    materialized = tuple(cases)
    _validate_resume_dependencies(materialized)
    _validate_ir_matched_pairs(materialized)
    return BenchmarkSuite(
        id=suite_id,
        description=description,
        cases=materialized,
        source_file=str(suite_path),
    )


def load_benchmark_manifest(path: Path) -> BenchmarkManifest:
    """Load and strictly validate a v1 compatibility or v2 suite manifest."""

    manifest_path = path.resolve()
    if manifest_path.suffix.lower() in {".yaml", ".yml"}:
        try:
            header = manifest_path.read_text(encoding="utf-8")[:4096]
        except FileNotFoundError as error:
            raise BenchmarkManifestError("manifest_not_found", str(manifest_path)) from error
        match = re.search(r"^schema_version:\s*([^\s#]+)", header, flags=re.MULTILINE)
        schema = match.group(1) if match else "unknown-yaml"
        if schema in LEGACY_SCHEMAS or schema.startswith("opencode_"):
            raise BenchmarkManifestError(
                "unsupported_legacy_benchmark",
                f"legacy schema {schema!r} is quarantined and cannot be executed",
            )
        raise BenchmarkManifestError(
            "unsupported_benchmark_schema", "current benchmark manifests must be JSON"
        )
    raw = _read_json(manifest_path)
    schema = _expect_string(raw.get("schema_version"), label="manifest.schema_version")
    if schema in LEGACY_SCHEMAS or schema.startswith("opencode_"):
        raise BenchmarkManifestError(
            "unsupported_legacy_benchmark",
            f"legacy schema {schema!r} is quarantined and cannot be executed",
        )
    repository_root = _repository_root(manifest_path)
    if schema == MANIFEST_V1:
        suite = BenchmarkSuite(
            id="compatibility-v1",
            description="Compatibility view of the Phase 1 smoke manifest",
            cases=_parse_v1_cases(
                raw.get("cases"), manifest_path=manifest_path, repository_root=repository_root
            ),
            source_file=str(manifest_path),
        )
        return BenchmarkManifest(
            schema_version=schema,
            benchmark_id="hardness-v1-compatibility",
            manifest_file=manifest_path,
            suites=(suite,),
            migration_ledger_file=None,
        )
    if schema != MANIFEST_V2:
        raise BenchmarkManifestError(
            "unsupported_benchmark_schema", f"unsupported schema {schema!r}"
        )

    benchmark_id = _validate_identifier(
        _expect_string(raw.get("benchmark_id"), label="manifest.benchmark_id"),
        label="benchmark id",
        pattern=CASE_ID_RE,
    )
    migration_ledger_file: Path | None = None
    migration_ledger_reference = raw.get("migration_ledger")
    if migration_ledger_reference is not None:
        migration_ledger_file = _relative_file(
            manifest_path.parent,
            _expect_string(
                migration_ledger_reference, label="manifest.migration_ledger"
            ),
            label="manifest.migration_ledger",
        )
        if not migration_ledger_file.is_file():
            raise BenchmarkManifestError(
                "migration_ledger_not_found", str(migration_ledger_file)
            )
    suite_files = _expect_string_list(
        raw.get("suites"), label="manifest.suites", allow_empty=False
    )
    suites: list[BenchmarkSuite] = []
    seen_suite_ids: set[str] = set()
    seen_case_ids: set[str] = set()
    for suite_reference in suite_files:
        suite_path = _relative_file(
            manifest_path.parent, suite_reference, label=f"suite {suite_reference!r}"
        )
        suite_raw = _read_json(suite_path)
        suite_schema = _expect_string(
            suite_raw.get("schema_version"), label=f"{suite_path}.schema_version"
        )
        if suite_schema != SUITE_V1:
            raise BenchmarkManifestError(
                "unsupported_suite_schema",
                f"{suite_path} uses {suite_schema!r}, expected {SUITE_V1!r}",
            )
        suite_id = _validate_identifier(
            _expect_string(suite_raw.get("suite_id"), label=f"{suite_path}.suite_id"),
            label="suite id",
            pattern=CASE_ID_RE,
        )
        if suite_id in seen_suite_ids:
            raise BenchmarkManifestError("duplicate_suite_id", suite_id)
        seen_suite_ids.add(suite_id)
        description = _expect_string(
            suite_raw.get("description", ""),
            label=f"suite {suite_id}.description",
            allow_empty=True,
        )
        raw_cases = suite_raw.get("cases")
        if not isinstance(raw_cases, list):
            raise BenchmarkManifestError(
                "invalid_schema", f"suite {suite_id}.cases must be a list"
            )
        cases: list[BenchmarkCase] = []
        for raw_case in raw_cases:
            case = _parse_v2_case(
                raw_case,
                suite_id=suite_id,
                source_manifest=suite_path,
                repository_root=repository_root,
            )
            if case.id in seen_case_ids:
                raise BenchmarkManifestError("duplicate_case_id", case.id)
            seen_case_ids.add(case.id)
            cases.append(case)
        suites.append(
            BenchmarkSuite(
                id=suite_id,
                description=description,
                cases=tuple(cases),
                source_file=str(suite_path),
            )
        )
    all_cases = tuple(case for suite in suites for case in suite.cases)
    _validate_resume_dependencies(all_cases)
    _validate_ir_matched_pairs(all_cases)
    return BenchmarkManifest(
        schema_version=schema,
        benchmark_id=benchmark_id,
        manifest_file=manifest_path,
        suites=tuple(suites),
        migration_ledger_file=migration_ledger_file,
    )


def select_benchmark_cases(
    manifest: BenchmarkManifest,
    *,
    suite_ids: Iterable[str] = (),
    case_ids: Iterable[str] = (),
    agent_phase: int = 1,
) -> BenchmarkSelection:
    """Select runnable cases and retain phase/disabled cases as explicit skips."""

    requested_suites = set(suite_ids)
    requested_cases = set(case_ids)
    known_suites = {suite.id for suite in manifest.suites}
    known_cases = {case.id for case in manifest.cases}
    unknown_suites = requested_suites - known_suites
    unknown_cases = requested_cases - known_cases
    if unknown_suites:
        raise BenchmarkManifestError(
            "unknown_suite", ", ".join(sorted(unknown_suites))
        )
    if unknown_cases:
        raise BenchmarkManifestError("unknown_case", ", ".join(sorted(unknown_cases)))
    if requested_cases:
        by_id = {case.id: case for case in manifest.cases}
        by_matched_pair: dict[str, tuple[BenchmarkCase, ...]] = {}
        by_comparison_group: dict[str, tuple[BenchmarkCase, ...]] = {}
        for case in manifest.cases:
            if case.matched_pair_id:
                by_matched_pair.setdefault(case.matched_pair_id, ())
                by_matched_pair[case.matched_pair_id] += (case,)
            if case.comparison_group_id:
                by_comparison_group.setdefault(case.comparison_group_id, ())
                by_comparison_group[case.comparison_group_id] += (case,)
        expanded_cases = set(requested_cases)
        pending = list(requested_cases)
        while pending:
            case = by_id[pending.pop()]
            if case.resume_from_case and case.resume_from_case not in expanded_cases:
                expanded_cases.add(case.resume_from_case)
                pending.append(case.resume_from_case)
            if case.matched_pair_id:
                for peer in by_matched_pair[case.matched_pair_id]:
                    if peer.id not in expanded_cases:
                        expanded_cases.add(peer.id)
                        pending.append(peer.id)
            if case.comparison_group_id:
                for peer in by_comparison_group[case.comparison_group_id]:
                    if peer.id not in expanded_cases:
                        expanded_cases.add(peer.id)
                        pending.append(peer.id)
        requested_cases = expanded_cases
    if agent_phase <= 0:
        raise BenchmarkManifestError("invalid_agent_phase", str(agent_phase))

    runnable: list[BenchmarkCase] = []
    skipped: list[SkippedCase] = []
    for case in manifest.cases:
        if requested_suites and case.suite_id not in requested_suites:
            continue
        if requested_cases and case.id not in requested_cases:
            continue
        if not case.enabled:
            skipped.append(
                SkippedCase(
                    case=case,
                    code="disabled",
                    reason=case.disabled_reason or "case disabled by manifest",
                )
            )
        elif case.min_agent_phase > agent_phase:
            skipped.append(
                SkippedCase(
                    case=case,
                    code="phase_gate",
                    reason=(
                        f"requires agent phase {case.min_agent_phase}; current phase is {agent_phase}"
                    ),
                )
            )
        else:
            runnable.append(case)
    return BenchmarkSelection(runnable=tuple(runnable), skipped=tuple(skipped))


def _rate(numerator: int, denominator: int) -> float | None:
    if denominator == 0:
        return None
    return round(numerator / denominator, 6)


def _compression_ratio(*, flat_count: int | None, ir_count: int | None) -> float | None:
    if flat_count is None or ir_count is None or flat_count <= 0:
        return None
    return round(1 - (ir_count / flat_count), 6)


def _average(values: Iterable[int | float]) -> float | None:
    materialized = tuple(values)
    if not materialized:
        return None
    return round(sum(materialized) / len(materialized), 6)


def _catalog_entry_key(entry: Any) -> str | None:
    if not isinstance(entry, dict):
        return None
    entry_id = entry.get("entry_id")
    if isinstance(entry_id, str) and entry_id:
        return entry_id
    declaration = entry.get("declaration")
    role = entry.get("component_role")
    if not isinstance(declaration, str) or not declaration:
        return None
    return json.dumps(
        {
            "declaration": declaration,
            "component_role": role if isinstance(role, str) else "unannotated",
            "is_final_facade": entry.get("is_final_facade") is True,
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def _mode_interface_summary(rows: Iterable[dict[str, Any]]) -> dict[str, Any]:
    materialized = tuple(rows)
    catalog_entries_present = any("catalog_entries" in row for row in materialized)
    catalog_entries: dict[str, dict[str, Any]] = {}
    if catalog_entries_present:
        for row in materialized:
            entries = row.get("catalog_entries", [])
            if not isinstance(entries, list):
                continue
            for entry in entries:
                key = _catalog_entry_key(entry)
                if key is not None and isinstance(entry, dict):
                    catalog_entries.setdefault(key, entry)
        agent_interface_count: int | None = len(catalog_entries)
        count_basis = "catalog_entry_union"
    else:
        reported_counts = sorted(
            {
                int(row["agent_interface_count"])
                for row in materialized
                if isinstance(row.get("agent_interface_count"), int)
                and not isinstance(row.get("agent_interface_count"), bool)
                and int(row["agent_interface_count"]) >= 0
            }
        )
        agent_interface_count = max(reported_counts) if reported_counts else None
        count_basis = "reported_catalog_count_max" if reported_counts else "unavailable"

    selected_interfaces: set[str] = set()
    selected_semantic_atoms: set[str] = set()
    selected_final_facades: set[str] = set()
    semantic_atom_uses: dict[str, int] = {}
    route_atom_counts: list[int] = []
    for row in materialized:
        atoms = row.get("route_atoms", [])
        roles = row.get("route_roles", [])
        if not isinstance(atoms, list):
            atoms = []
        if not isinstance(roles, list):
            roles = []
        case_semantic_atoms: set[str] = set()
        for index, atom in enumerate(atoms):
            if not isinstance(atom, str) or not atom:
                continue
            role = roles[index] if index < len(roles) and isinstance(roles[index], str) else "unannotated"
            selected_interfaces.add(atom)
            if role == "finalComposition":
                selected_final_facades.add(atom)
            else:
                selected_semantic_atoms.add(atom)
                case_semantic_atoms.add(atom)
        for atom in case_semantic_atoms:
            semantic_atom_uses[atom] = semantic_atom_uses.get(atom, 0) + 1
        atom_count = row.get("route_atom_count")
        if isinstance(atom_count, int) and not isinstance(atom_count, bool) and atom_count >= 0:
            route_atom_counts.append(atom_count)

    reused_semantic_atoms = sorted(
        atom for atom, uses in semantic_atom_uses.items() if uses > 1
    )
    return {
        "case_count": len(materialized),
        "verified_case_count": sum(
            1
            for row in materialized
            if row.get("actual_status") == "VERIFIED" and row.get("passed") is True
        ),
        "catalog_ids": sorted(
            {
                value
                for row in materialized
                if isinstance((value := row.get("catalog_id")), str) and value
            }
        ),
        "agent_interface_count": agent_interface_count,
        "agent_interface_count_basis": count_basis,
        "catalog_entry_ids": sorted(catalog_entries),
        "selected_interface_count": len(selected_interfaces),
        "selected_interfaces": sorted(selected_interfaces),
        "selected_semantic_atomic_interface_count": len(selected_semantic_atoms),
        "selected_semantic_atomic_interfaces": sorted(selected_semantic_atoms),
        "selected_final_facade_count": len(selected_final_facades),
        "selected_final_facades": sorted(selected_final_facades),
        "reused_semantic_atomic_interfaces": reused_semantic_atoms,
        "average_route_atom_count": _average(route_atom_counts),
    }


def _interface_comparison(
    rows: Iterable[dict[str, Any]], *, eligible_pair_count: int
) -> dict[str, Any]:
    materialized = tuple(rows)
    by_mode = {
        mode: _mode_interface_summary(
            row for row in materialized if row.get("catalog_mode") == mode
        )
        for mode in ("flat_api", "ir_components")
    }
    flat = by_mode["flat_api"]
    ir = by_mode["ir_components"]
    ir_semantic_count = int(ir["selected_semantic_atomic_interface_count"])
    return {
        "eligible_matched_pair_count": eligible_pair_count,
        "modes": by_mode,
        "agent_interface_compression_ratio": _compression_ratio(
            flat_count=flat["agent_interface_count"],
            ir_count=ir["agent_interface_count"],
        ),
        "selected_semantic_atomic_compression_ratio": _compression_ratio(
            flat_count=flat["selected_semantic_atomic_interface_count"],
            ir_count=ir["selected_semantic_atomic_interface_count"],
        ),
        "ir_component_reuse_factor": (
            round(eligible_pair_count / ir_semantic_count, 6)
            if eligible_pair_count > 0 and ir_semantic_count > 0
            else None
        ),
        "average_route_atom_overhead": (
            round(
                float(ir["average_route_atom_count"])
                - float(flat["average_route_atom_count"]),
                6,
            )
            if ir["average_route_atom_count"] is not None
            and flat["average_route_atom_count"] is not None
            else None
        ),
    }


def _summarize_ir_feasibility(results: Iterable[dict[str, Any]]) -> dict[str, Any]:
    study_rows = tuple(
        row for row in results if row.get("evaluation_lane") == "ir_feasibility"
    )
    by_pair: dict[str, list[dict[str, Any]]] = {}
    for row in study_rows:
        pair_id = row.get("matched_pair_id")
        if isinstance(pair_id, str) and pair_id:
            by_pair.setdefault(pair_id, []).append(row)

    pair_summaries: list[dict[str, Any]] = []
    complete_pair_ids: set[str] = set()
    eligible_pair_ids: set[str] = set()
    for pair_id, pair_rows in sorted(by_pair.items()):
        modes = [row.get("catalog_mode") for row in pair_rows]
        complete = (
            len(pair_rows) == 2
            and sorted(modes) == ["flat_api", "ir_components"]
        )
        both_verified = complete and all(
            row.get("actual_status") == "VERIFIED" and row.get("passed") is True
            for row in pair_rows
        )
        if complete:
            complete_pair_ids.add(pair_id)
        if both_verified:
            eligible_pair_ids.add(pair_id)
        family_ids = {
            row.get("family_id")
            for row in pair_rows
            if isinstance(row.get("family_id"), str) and row.get("family_id")
        }
        pair_summaries.append(
            {
                "matched_pair_id": pair_id,
                "family_id": next(iter(family_ids)) if len(family_ids) == 1 else None,
                "case_ids": sorted(
                    row["id"]
                    for row in pair_rows
                    if isinstance(row.get("id"), str)
                ),
                "catalog_modes": sorted(
                    mode for mode in modes if isinstance(mode, str)
                ),
                "complete": complete,
                "both_verified": both_verified,
            }
        )

    complete_pairs = [
        pair for pair in pair_summaries if pair["matched_pair_id"] in complete_pair_ids
    ]
    family_ids = sorted(
        {
            row.get("family_id")
            for row in study_rows
            if isinstance(row.get("family_id"), str) and row.get("family_id")
        }
    )
    families: list[dict[str, Any]] = []
    for family_id in family_ids:
        family_pairs = [
            pair for pair in complete_pairs if pair.get("family_id") == family_id
        ]
        family_eligible_ids = {
            str(pair["matched_pair_id"])
            for pair in family_pairs
            if pair.get("both_verified") is True
        }
        family_rows = [
            row
            for row in study_rows
            if row.get("family_id") == family_id
            and row.get("matched_pair_id") in family_eligible_ids
        ]
        families.append(
            {
                "family_id": family_id,
                "complete_matched_pair_count": len(family_pairs),
                "both_verified_matched_pair_count": len(family_eligible_ids),
                "matched_pair_both_verified_rate": _rate(
                    len(family_eligible_ids), len(family_pairs)
                ),
                **_interface_comparison(
                    family_rows, eligible_pair_count=len(family_eligible_ids)
                ),
            }
        )

    eligible_rows = [
        row for row in study_rows if row.get("matched_pair_id") in eligible_pair_ids
    ]
    both_verified_count = len(eligible_pair_ids)
    return {
        "logical_matched_pair_count": len(by_pair),
        "complete_matched_pair_count": len(complete_pair_ids),
        "both_verified_matched_pair_count": both_verified_count,
        "matched_pair_both_verified_rate": _rate(
            both_verified_count, len(complete_pair_ids)
        ),
        "incomplete_matched_pair_ids": sorted(set(by_pair) - complete_pair_ids),
        "pairs": pair_summaries,
        "families": families,
        "aggregate": _interface_comparison(
            eligible_rows, eligible_pair_count=both_verified_count
        ),
    }


def summarize_benchmark_results(
    *,
    results: list[dict[str, Any]],
    skipped: Iterable[SkippedCase] = (),
) -> dict[str, Any]:
    """Compute outcome, positive, negative, authoring, axiom, and replay metrics."""

    positive = [result for result in results if result["expected_status"] == "VERIFIED"]
    negative = [result for result in results if result["expected_status"] != "VERIFIED"]
    positive_reduction_authoring = [
        result
        for result in results
        if result["expected_status"] == "VERIFIED"
        and result.get("requires_authoring", False)
        and result.get("objective") in {"reduce_to", "reduce_to_known_np"}
    ]
    membership_positive = [
        result
        for result in results
        if result.get("objective") == "prove_in_np"
        and result["expected_status"] == "VERIFIED"
    ]
    completeness_positive = [
        result
        for result in results
        if result.get("objective") == "prove_np_complete"
        and result["expected_status"] == "VERIFIED"
    ]
    verified = [result for result in results if result["actual_status"] == "VERIFIED"]
    groups: dict[str, list[dict[str, Any]]] = {}
    for result in results:
        group_id = result.get("group_id")
        if group_id:
            groups.setdefault(group_id, []).append(result)
    group_summary = [
        {
            "id": group_id,
            "total": len(group_results),
            "passed": sum(1 for result in group_results if result["passed"]),
            "passed_all": all(result["passed"] for result in group_results),
        }
        for group_id, group_results in sorted(groups.items())
    ]
    lane_summary: dict[str, dict[str, Any]] = {}
    for lane in sorted(EVALUATION_LANES):
        lane_results = [
            result for result in results if result.get("evaluation_lane") == lane
        ]
        lane_positive = [
            result
            for result in lane_results
            if result.get("expected_status") == "VERIFIED"
        ]
        lane_negative = [
            result
            for result in lane_results
            if result.get("expected_status") != "VERIFIED"
        ]
        lane_authoring_positive = [
            result
            for result in lane_positive
            if result.get("requires_authoring", False)
        ]
        lane_model_usage: dict[str, int | float] = {}
        for result in lane_results:
            usage = result.get("model_usage")
            if not isinstance(usage, dict):
                continue
            for key, value in usage.items():
                if isinstance(value, (int, float)) and not isinstance(value, bool):
                    lane_model_usage[key] = lane_model_usage.get(key, 0) + value
        lane_summary[lane] = {
            "total": len(lane_results),
            "passed": sum(1 for result in lane_results if result.get("passed")),
            "outcome_accuracy": _rate(
                sum(1 for result in lane_results if result.get("passed")),
                len(lane_results),
            ),
            "positive_verified_rate": _rate(
                sum(
                    1
                    for result in lane_positive
                    if result.get("actual_status") == "VERIFIED"
                ),
                len(lane_positive),
            ),
            "negative_block_accuracy": _rate(
                sum(1 for result in lane_negative if result.get("passed")),
                len(lane_negative),
            ),
            "model_call_count": sum(
                int(result.get("model_call_count", 0)) for result in lane_results
            ),
            "model_request_count": sum(
                int(result.get("model_request_count", 0)) for result in lane_results
            ),
            "model_duration_seconds": round(
                sum(
                    float(call.get("duration_seconds", 0.0))
                    for result in lane_results
                    for call in result.get("model_calls", [])
                    if call.get("called") is True
                ),
                3,
            ),
            "model_usage": lane_model_usage or None,
            "authoring_attempt_count": sum(
                int(result.get("authoring_attempt_count", 0))
                for result in lane_results
            ),
            "capability_closure_rate": _rate(
                sum(
                    1
                    for result in lane_authoring_positive
                    if result.get("actual_status") == "VERIFIED"
                    and (
                        result.get("new_certified_reduction", False)
                        or result.get("new_native_membership", False)
                    )
                ),
                len(lane_authoring_positive),
            ),
        }
    skipped_list = list(skipped)
    ir_feasibility = _summarize_ir_feasibility(results)
    return {
        "total": len(results),
        "passed": sum(1 for result in results if result["passed"]),
        "failed": sum(1 for result in results if not result["passed"]),
        "skipped": len(skipped_list),
        "metrics": {
            "case_outcome_accuracy": _rate(
                sum(1 for result in results if result["passed"]), len(results)
            ),
            "positive_final_verified_rate": _rate(
                sum(1 for result in positive if result["actual_status"] == "VERIFIED"),
                len(positive),
            ),
            "negative_block_accuracy": _rate(
                sum(1 for result in negative if result["passed"]), len(negative)
            ),
            "full_reduction_authored_rate": _rate(
                sum(
                    1
                    for result in positive_reduction_authoring
                    if result["actual_status"] == "VERIFIED"
                    and result.get("new_certified_reduction", False)
                ),
                len(positive_reduction_authoring),
            ),
            "native_membership_rate": _rate(
                sum(
                    1
                    for result in membership_positive
                    if result["actual_status"] == "VERIFIED"
                ),
                len(membership_positive),
            ),
            "native_completeness_rate": _rate(
                sum(
                    1
                    for result in completeness_positive
                    if result["actual_status"] == "VERIFIED"
                ),
                len(completeness_positive),
            ),
            "axiom_clean_rate": _rate(
                sum(1 for result in verified if result.get("axiom_clean", False)),
                len(verified),
            ),
            "deterministic_replay_rate": _rate(
                sum(1 for result in verified if result.get("deterministic_replay", False)),
                len(verified),
            ),
            "matched_pair_both_verified_rate": ir_feasibility[
                "matched_pair_both_verified_rate"
            ],
        },
        "groups": group_summary,
        "evaluation_lanes": lane_summary,
        "ir_feasibility": ir_feasibility,
    }
