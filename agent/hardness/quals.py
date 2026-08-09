"""Stage-N Quals formalization contracts and milestone validation."""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from .benchmark import BenchmarkCase, DECLARATION_RE, MODULE_RE
from .lean_runner import sha256_file
from .typed_authoring import (
    TypedAuthoringArtifactCase,
    TypedAuthoringRequest,
    build_typed_authoring_batch_artifact_source,
)


FORMALIZATION_SUITE_SCHEMA = "hardness_quals_formalization_suite_v1"
MANUAL_VALIDATION_SCHEMA = "hardness_quals_manual_validation_v1"
QUALS_REPORT_SCHEMA = "hardness_quals_completeness_report_v1"

N_A_FORMALIZATION_IDS = ("spring2015-exactly-one-neighbor-formalization",)
N_A_PRIMARY_IDS = ("spring2015-exactly-one-neighbor",)
N_A_ADVERSARIAL_IDS = (
    "spring2015-exactly-one-neighbor-missing-membership",
    "spring2015-exactly-one-neighbor-reversed-reduction",
    "spring2015-exactly-one-neighbor-wrong-endpoint",
)

N_B_FORMALIZATION_IDS = (
    "spring2015-exactly-one-neighbor-formalization",
    "uiuc2022-seeing-set-formalization",
    "fall2016-node-deletion-bipartite-formalization",
)
N_B_PRIMARY_IDS = (
    "spring2015-exactly-one-neighbor",
    "uiuc2022-seeing-set",
    "fall2016-node-deletion-bipartite",
)
N_B_ADVERSARIAL_IDS = (
    "spring2015-exactly-one-neighbor-missing-membership",
    "spring2015-exactly-one-neighbor-reversed-reduction",
    "spring2015-exactly-one-neighbor-wrong-endpoint",
    "uiuc2022-seeing-set-missing-reduction",
    "fall2016-node-deletion-bipartite-missing-membership",
)

N_C_FORMALIZATION_IDS = N_B_FORMALIZATION_IDS + (
    "fall2014-most-neighbors-formalization",
    "uiuc2020-two-disjoint-bounded-paths-formalization",
)
N_C_PRIMARY_IDS = N_B_PRIMARY_IDS + (
    "fall2014-most-neighbors",
    "uiuc2020-two-disjoint-bounded-paths",
)
N_C_ADVERSARIAL_IDS = N_B_ADVERSARIAL_IDS + (
    "fall2014-most-neighbors-missing-membership",
    "uiuc2020-two-disjoint-bounded-paths-missing-membership",
)

ORACLE_MARKERS = (
    ".Oracles.",
    ".Expected.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    ".Legacy.",
)

SOURCE_ORACLE_MARKERS = tuple(marker for marker in ORACLE_MARKERS if marker != ".Legacy.")


class QualsContractError(ValueError):
    """Stable fail-closed error for a Stage-N contract violation."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class QualsFormalizationCase:
    id: str
    module: str
    problem_declaration: str
    production_endpoint: str
    representation_declaration: str
    semantic_theorem: str
    validation_record: Path
    expected_status: str
    public_module_file: Path
    validation: Mapping[str, Any]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["validation_record"] = str(self.validation_record.resolve())
        value["public_module_file"] = str(self.public_module_file.resolve())
        return value


@dataclass(frozen=True)
class QualsFormalizationSuite:
    id: str
    milestone: str
    description: str
    cases: tuple[QualsFormalizationCase, ...]
    source_file: Path


def _object(value: Any, *, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise QualsContractError("invalid_schema", f"{label} must be an object")
    return value


def _string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise QualsContractError("invalid_schema", f"{label} must be a non-empty string")
    return value


def _bool(value: Any, *, label: str) -> bool:
    if not isinstance(value, bool):
        raise QualsContractError("invalid_schema", f"{label} must be boolean")
    return value


def _read_json(path: Path) -> dict[str, Any]:
    try:
        return _object(json.loads(path.read_text(encoding="utf-8")), label=str(path))
    except FileNotFoundError as error:
        raise QualsContractError("contract_not_found", str(path)) from error
    except json.JSONDecodeError as error:
        raise QualsContractError(
            "invalid_json", f"{path}:{error.lineno}:{error.colno}: {error.msg}"
        ) from error


def _repository_root(path: Path) -> Path:
    for parent in (path.parent, *path.parents):
        if (parent / "Lean" / "Reference").is_dir() and (parent / "Benchmark").is_dir():
            return parent
    raise QualsContractError("repository_root_not_found", str(path))


def _public_name(value: Any, *, label: str, module: bool = False) -> str:
    name = _string(value, label=label)
    pattern = MODULE_RE if module else DECLARATION_RE
    if not pattern.fullmatch(name):
        raise QualsContractError("invalid_identifier", f"invalid {label}: {name!r}")
    if any(marker in f".{name}." for marker in ORACLE_MARKERS):
        raise QualsContractError("oracle_reference_forbidden", f"{label}: {name}")
    return name


def _root_relative_file(root: Path, value: Any, *, label: str) -> Path:
    raw = Path(_string(value, label=label))
    if raw.is_absolute() or ".." in raw.parts:
        raise QualsContractError("unsafe_contract_path", f"{label} escapes the repository")
    path = (root / raw).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError as error:
        raise QualsContractError("unsafe_contract_path", f"{label} escapes the repository") from error
    if not path.is_file():
        raise QualsContractError("contract_file_not_found", str(path))
    return path


def _load_manual_validation(path: Path, *, case_id: str, module_hash: str) -> dict[str, Any]:
    value = _read_json(path)
    if value.get("schema_version") != MANUAL_VALIDATION_SCHEMA:
        raise QualsContractError("invalid_schema", f"unsupported validation record: {path}")
    if value.get("case_id") != case_id:
        raise QualsContractError("validation_case_mismatch", str(path))
    if value.get("validation_kind") != "independent_manual_validation":
        raise QualsContractError("invalid_validation_kind", str(path))
    if value.get("review_status") != "accepted":
        raise QualsContractError("formalization_not_accepted", str(path))
    if value.get("public_module_sha256") != module_hash:
        raise QualsContractError("stale_formalization_validation", str(path))
    required_false = (
        "oracle_visible_to_model",
        "gold_route_visible_to_model",
        "production_aggregate_imported",
        "catalog_entry_created_by_validation",
    )
    for key in required_false:
        if _bool(value.get(key), label=f"{path}.{key}"):
            raise QualsContractError("formalization_isolation_violation", f"{path}: {key}")
    checks = _object(value.get("checks"), label=f"{path}.checks")
    required_checks = {
        "natural_language_semantics_reviewed",
        "exact_presented_problem_reviewed",
        "lawful_structured_encoding_reviewed",
        "predicate_equivalence_reviewed",
        "benchmark_feasibility_reviewed",
    }
    if set(checks) != required_checks or not all(
        _bool(checks[key], label=f"{path}.checks.{key}") for key in required_checks
    ):
        raise QualsContractError("incomplete_manual_validation", str(path))
    return value


def load_quals_formalization_suite(path: Path) -> QualsFormalizationSuite:
    """Load the separate, non-scoring natural-language-to-Lean prerequisite."""

    suite_path = path.resolve()
    root = _repository_root(suite_path)
    value = _read_json(suite_path)
    if value.get("schema_version") != FORMALIZATION_SUITE_SCHEMA:
        raise QualsContractError("invalid_schema", f"unsupported formalization suite: {path}")
    suite_id = _string(value.get("suite_id"), label="suite_id")
    milestone = _string(value.get("milestone"), label="milestone")
    description = _string(value.get("description"), label="description")
    raw_cases = value.get("cases")
    if not isinstance(raw_cases, list) or not raw_cases:
        raise QualsContractError("invalid_schema", "formalization cases must be non-empty")
    cases: list[QualsFormalizationCase] = []
    for index, raw_case in enumerate(raw_cases):
        case = _object(raw_case, label=f"cases[{index}]")
        case_id = _string(case.get("id"), label=f"cases[{index}].id")
        module = _public_name(case.get("module"), label=f"{case_id}.module", module=True)
        if not module.startswith("Benchmark.Hardness.Inputs.Quals."):
            raise QualsContractError("non_quals_module", module)
        module_file = root / "Lean" / "Reference" / Path(*module.split(".")).with_suffix(".lean")
        if not module_file.is_file():
            raise QualsContractError("input_module_not_found", module)
        source = module_file.read_text(encoding="utf-8")
        if "EncodedType.raw" in source:
            raise QualsContractError("raw_encoding_forbidden", str(module_file))
        import_lines = "\n".join(
            line.strip() for line in source.splitlines() if line.lstrip().startswith("import ")
        )
        if any(marker in import_lines for marker in SOURCE_ORACLE_MARKERS):
            raise QualsContractError("oracle_import_forbidden", str(module_file))
        validation_path = _root_relative_file(
            root, case.get("validation_record"), label=f"{case_id}.validation_record"
        )
        validation = _load_manual_validation(
            validation_path,
            case_id=case_id,
            module_hash=sha256_file(module_file),
        )
        expected = _object(case.get("expected"), label=f"{case_id}.expected")
        cases.append(
            QualsFormalizationCase(
                id=case_id,
                module=module,
                problem_declaration=_public_name(
                    case.get("problem_declaration"), label=f"{case_id}.problem_declaration"
                ),
                production_endpoint=_public_name(
                    case.get("production_endpoint"), label=f"{case_id}.production_endpoint"
                ),
                representation_declaration=_public_name(
                    case.get("representation_declaration"),
                    label=f"{case_id}.representation_declaration",
                ),
                semantic_theorem=_public_name(
                    case.get("semantic_theorem"), label=f"{case_id}.semantic_theorem"
                ),
                validation_record=validation_path,
                expected_status=_string(expected.get("status"), label=f"{case_id}.expected.status"),
                public_module_file=module_file,
                validation=validation,
            )
        )
    result = QualsFormalizationSuite(
        id=suite_id,
        milestone=milestone,
        description=description,
        cases=tuple(cases),
        source_file=suite_path,
    )
    validate_quals_formalization_suite(result)
    return result


def validate_quals_formalization_suite(suite: QualsFormalizationSuite) -> None:
    if suite.id != "quals-formalization" or suite.milestone != "N-C":
        raise QualsContractError("wrong_milestone", f"{suite.id}/{suite.milestone}")
    if tuple(case.id for case in suite.cases) != N_C_FORMALIZATION_IDS:
        raise QualsContractError("formalization_matrix_changed", str(suite.source_file))
    if any(case.expected_status != "VERIFIED" for case in suite.cases):
        raise QualsContractError("invalid_expected_status", str(suite.source_file))


def _lean_identifier(value: str) -> str:
    identifier = re.sub(r"[^A-Za-z0-9_]", "_", value)
    return f"case_{identifier}" if not identifier or identifier[0].isdigit() else identifier


def build_quals_formalization_gate_source(
    cases: Sequence[QualsFormalizationCase],
) -> str:
    imports = {"ComplexityReduction.AxiomGate", *(case.module for case in cases)}
    lines = [
        *(f"import {module}" for module in sorted(imports)),
        "",
        "namespace Benchmark.Hardness.Quals.FormalizationGate",
        "",
        "open ComplexityReduction.Encoding",
        "",
    ]
    audited: list[str] = []
    for case in cases:
        name = _lean_identifier(case.id)
        lines.extend(
            [
                f"abbrev {name}_problem : PresentedProblem := {case.problem_declaration}",
                "",
                f"theorem {name}_exact_endpoint :",
                f"    {name}_problem = {case.production_endpoint} := rfl",
                "",
                f"theorem {name}_exact_representation :",
                f"    {name}_problem.representation = {case.representation_declaration} := rfl",
                "",
                f"#check {case.semantic_theorem}",
                "",
            ]
        )
        audited.extend(
            [
                f"Benchmark.Hardness.Quals.FormalizationGate.{name}_problem",
                f"Benchmark.Hardness.Quals.FormalizationGate.{name}_exact_endpoint",
                f"Benchmark.Hardness.Quals.FormalizationGate.{name}_exact_representation",
                case.semantic_theorem,
            ]
        )
    lines.extend(
        [
            "end Benchmark.Hardness.Quals.FormalizationGate",
            "",
            "assert_standard_axioms",
            "  " + ",\n  ".join(audited),
            "",
        ]
    )
    return "\n".join(lines)


def validate_quals_completeness_suite(cases: Sequence[BenchmarkCase]) -> None:
    if tuple(case.id for case in cases) != N_C_PRIMARY_IDS:
        raise QualsContractError("primary_matrix_changed", str(tuple(case.id for case in cases)))
    contracts = {
        "spring2015-exactly-one-neighbor": {
            "formalization": "spring2015-exactly-one-neighbor-formalization",
            "objective": "prove_np_complete",
            "target_policy": "open",
            "baseline_failure": "missing_native_membership",
            "active_node": "membership_capability",
            "head": "ComplexityReduction.Certificate.NativeTMInNP",
            "packet": "membership_packet",
            "witness_shape": "list_nat",
            "new_reduction": False,
            "finite_witness": True,
        },
        "uiuc2022-seeing-set": {
            "formalization": "uiuc2022-seeing-set-formalization",
            "objective": "reduce_to",
            "target_policy": "fixed",
            "baseline_failure": "no_registry_path",
            "active_node": "reduction_capability",
            "head": "ComplexityReduction.Certificate.CertifiedReduction",
            "packet": "tm_certificate_packet",
            "witness_shape": "none",
            "new_reduction": True,
            "finite_witness": False,
        },
        "fall2016-node-deletion-bipartite": {
            "formalization": "fall2016-node-deletion-bipartite-formalization",
            "objective": "prove_np_complete",
            "target_policy": "open",
            "baseline_failure": "missing_native_membership",
            "active_node": "membership_capability",
            "head": "ComplexityReduction.Certificate.NativeTMInNP",
            "packet": "membership_packet",
            "witness_shape": "deletion_coloring",
            "new_reduction": False,
            "finite_witness": True,
        },
        "fall2014-most-neighbors": {
            "formalization": "fall2014-most-neighbors-formalization",
            "objective": "prove_np_complete",
            "target_policy": "open",
            "baseline_failure": "missing_native_membership",
            "active_node": "membership_capability",
            "head": "ComplexityReduction.Certificate.NativeTMInNP",
            "packet": "membership_packet",
            "witness_shape": "list_nat",
            "new_reduction": False,
            "finite_witness": True,
        },
        "uiuc2020-two-disjoint-bounded-paths": {
            "formalization": "uiuc2020-two-disjoint-bounded-paths-formalization",
            "objective": "prove_np_complete",
            "target_policy": "open",
            "baseline_failure": "missing_native_membership",
            "active_node": "membership_capability",
            "head": "ComplexityReduction.Certificate.NativeTMInNP",
            "packet": "membership_packet",
            "witness_shape": "pair_list",
            "new_reduction": False,
            "finite_witness": True,
        },
    }
    required_tracks = {"lower_bound", "membership", "completeness"}
    for case in cases:
        contract = contracts[case.id]
        request = TypedAuthoringRequest.from_case(case)
        target_contract_ok = (
            case.target is not None
            if contract["target_policy"] == "fixed"
            else case.target is None
        )
        if (
            case.evaluation_lane != "quals_completeness"
            or case.objective != contract["objective"]
            or case.target_policy != contract["target_policy"]
            or not target_contract_ok
            or case.execution_layer != "optional_authoring"
            or case.verification_profile != "strict-release"
            or case.expected.baseline_status != "BLOCKED"
            or case.expected.baseline_failure_code != contract["baseline_failure"]
            or case.expected.final_status != "VERIFIED"
            or request.active_node != contract["active_node"]
            or request.expected_capability_head != contract["head"]
            or contract["packet"] not in request.allowed_packet_kinds
            or request.witness_shape != contract["witness_shape"]
            or not request.model_selection_required
            or case.coverage.get("new_reduction_edge_expected")
            is not contract["new_reduction"]
            or case.coverage.get("finite_witness_membership_expected")
            is not contract["finite_witness"]
        ):
            raise QualsContractError("invalid_primary_contract", case.id)
        if set(case.coverage.get("capability_tracks", [])) != required_tracks:
            raise QualsContractError("invalid_primary_tracks", case.id)
        if case.coverage.get("formalization_case_id") != contract["formalization"]:
            raise QualsContractError("formalization_link_missing", case.id)


def validate_quals_adversarial_suite(cases: Sequence[BenchmarkCase]) -> None:
    if tuple(case.id for case in cases) != N_C_ADVERSARIAL_IDS:
        raise QualsContractError(
            "adversarial_matrix_changed", str(tuple(case.id for case in cases))
        )
    contracts = {
        "spring2015-exactly-one-neighbor-missing-membership": (
            "missing_membership",
            "spring2015-exactly-one-neighbor-formalization",
            "missing_native_membership",
        ),
        "spring2015-exactly-one-neighbor-reversed-reduction": (
            "reversed_reduction",
            "spring2015-exactly-one-neighbor-formalization",
            "no_registry_path",
        ),
        "spring2015-exactly-one-neighbor-wrong-endpoint": (
            "wrong_endpoint",
            "spring2015-exactly-one-neighbor-formalization",
            "missing_native_membership",
        ),
        "uiuc2022-seeing-set-missing-reduction": (
            "missing_reduction",
            "uiuc2022-seeing-set-formalization",
            "no_registry_path",
        ),
        "fall2016-node-deletion-bipartite-missing-membership": (
            "missing_membership",
            "fall2016-node-deletion-bipartite-formalization",
            "missing_native_membership",
        ),
        "fall2014-most-neighbors-missing-membership": (
            "missing_membership",
            "fall2014-most-neighbors-formalization",
            "missing_native_membership",
        ),
        "uiuc2020-two-disjoint-bounded-paths-missing-membership": (
            "missing_membership",
            "uiuc2020-two-disjoint-bounded-paths-formalization",
            "missing_native_membership",
        ),
    }
    for case in cases:
        negative_class, formalization_id, failure_code = contracts[case.id]
        if (
            case.evaluation_lane != "quals_adversarial"
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.requires_authoring
            or case.expected.final_status != "BLOCKED"
            or case.expected.baseline_status != "BLOCKED"
            or case.expected.final_failure_code != failure_code
            or case.expected.baseline_failure_code != failure_code
            or case.coverage.get("negative_class") != negative_class
            or case.coverage.get("formalization_case_id") != formalization_id
        ):
            raise QualsContractError("invalid_adversarial_contract", case.id)


def build_quals_batch_artifact_source(
    cases: Sequence[TypedAuthoringArtifactCase],
) -> str:
    """Render one final Lean file while keeping the Stage-N namespace distinct."""

    source = build_typed_authoring_batch_artifact_source(cases)
    return source.replace(
        "Benchmark.Hardness.TypedAuthoring.Final", "Benchmark.Hardness.Quals.Final"
    )


def quals_report_skeleton(
    *,
    formalization_suite_file: Path,
    completeness_suite_file: Path,
    adversarial_suite_file: Path,
    output_root: Path,
) -> dict[str, Any]:
    return {
        "schema_version": QUALS_REPORT_SCHEMA,
        "stage": "N",
        "milestone": "N-C",
        "formalization_suite_file": str(formalization_suite_file.resolve()),
        "completeness_suite_file": str(completeness_suite_file.resolve()),
        "adversarial_suite_file": str(adversarial_suite_file.resolve()),
        "output_root": str(output_root.resolve()),
        "published": False,
        "status": "RUNNING",
        "formalization": {},
        "cases": [],
        "process_counts": {
            "formalization": 0,
            "setup_build": 0,
            "core_baseline": 0,
            "authoring_local": 0,
            "final_combined_lean": 0,
            "release_replay": 0,
        },
    }
