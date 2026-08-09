"""Strict inventory and suite contracts for NP-hard generalization work.

This module is intentionally read-only.  It freezes which exact Lean endpoints
belong to the release benchmark and rejects a suite that silently loses one of
the planned coverage or isolation properties.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


NP_HARD_INVENTORY_SCHEMA_V1 = "hardness_np_hard_inventory_v1"
NP_HARD_GENERALIZATION_SUITE_SCHEMA_V1 = (
    "hardness_np_hard_generalization_suite_v1"
)
NP_HARD_GENERALIZATION_SUITE_ID_V1 = "np_hard_generalization_v1"

_FAMILIES = {"graph", "set-system", "numeric", "sat-csp", "other"}
_PRESENTATION_KINDS = {"presented", "alias", "wrapper"}
_ROUTE_KINDS = {"none", "single-edge", "multi-edge"}
_GAP_CLASSES = {
    "none",
    "semantic-proof",
    "program-composition",
    "program-synthesis",
    "multi-gap",
}
_CASE_KINDS = {"existing_route", "model_authoring", "safety_negative"}
_TASK_CLASSES = {"semantic_proof", "program_composition", "program_synthesis"}
_NEGATIVE_KINDS = {
    "wrong_direction",
    "endpoint_mutation",
    "forbidden_axiom",
    "unavailable_presentation",
}


@dataclass(frozen=True)
class NPHardInventoryEntryV1:
    problem_id: str
    lean_module: str
    problem_term: str
    family: str
    presentation_kind: str
    native_hardness_seed: bool
    existing_forward_route: str
    known_reverse_only: bool
    membership_available: bool
    authoring_gap_class: str


@dataclass(frozen=True)
class NPHardInventoryV1:
    inventory_id: str
    scope: str
    entries: tuple[NPHardInventoryEntryV1, ...]

    def by_problem_id(self) -> dict[str, NPHardInventoryEntryV1]:
        return {entry.problem_id: entry for entry in self.entries}


@dataclass(frozen=True)
class NPHardGeneralizationCaseV1:
    id: str
    kind: str
    problem_id: str
    module: str
    problem: str
    family: str
    presentation_kind: str
    membership_available: bool
    initial_expected_status: str
    initial_expected_failure_code: str | None
    expected_status: str
    expected_failure_code: str | None
    route: Mapping[str, Any] | None
    authoring: Mapping[str, Any] | None
    negative: Mapping[str, Any] | None
    public_source_files: tuple[str, ...]


@dataclass(frozen=True)
class NPHardGeneralizationSuiteV1:
    inventory_path: str
    public_input_root: str
    gold_root: str
    cases: tuple[NPHardGeneralizationCaseV1, ...]

    def by_id(self) -> dict[str, NPHardGeneralizationCaseV1]:
        return {case.id: case for case in self.cases}


def _read_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object: {path}")
    return value


def _required_string(value: Mapping[str, Any], key: str, *, context: str) -> str:
    result = value.get(key)
    if not isinstance(result, str) or not result:
        raise ValueError(f"{context} requires non-empty string field {key!r}")
    return result


def _required_bool(value: Mapping[str, Any], key: str, *, context: str) -> bool:
    result = value.get(key)
    if not isinstance(result, bool):
        raise ValueError(f"{context} requires Boolean field {key!r}")
    return result


def _optional_string(value: Mapping[str, Any], key: str, *, context: str) -> str | None:
    result = value.get(key)
    if result is not None and (not isinstance(result, str) or not result):
        raise ValueError(f"{context} has invalid optional string field {key!r}")
    return result


def _module_file(root: Path, module: str) -> Path:
    return root / "Lean" / "Reference" / Path(*module.split(".")).with_suffix(".lean")


def load_np_hard_inventory(path: Path, *, root: Path | None = None) -> NPHardInventoryV1:
    raw = _read_object(path)
    if raw.get("schema_version") != NP_HARD_INVENTORY_SCHEMA_V1:
        raise ValueError("unsupported NP-hard inventory schema")
    inventory_id = _required_string(raw, "inventory_id", context="NP-hard inventory")
    scope = _required_string(raw, "scope", context="NP-hard inventory")
    raw_entries = raw.get("entries")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise ValueError("NP-hard inventory entries must be a non-empty list")

    entries: list[NPHardInventoryEntryV1] = []
    seen_ids: set[str] = set()
    seen_endpoints: set[tuple[str, str]] = set()
    for index, value in enumerate(raw_entries):
        context = f"NP-hard inventory entry {index}"
        if not isinstance(value, dict):
            raise ValueError(f"{context} must be an object")
        entry = NPHardInventoryEntryV1(
            problem_id=_required_string(value, "problem_id", context=context),
            lean_module=_required_string(value, "lean_module", context=context),
            problem_term=_required_string(value, "problem_term", context=context),
            family=_required_string(value, "family", context=context),
            presentation_kind=_required_string(value, "presentation_kind", context=context),
            native_hardness_seed=_required_bool(value, "native_hardness_seed", context=context),
            existing_forward_route=_required_string(
                value, "existing_forward_route", context=context
            ),
            known_reverse_only=_required_bool(value, "known_reverse_only", context=context),
            membership_available=_required_bool(
                value, "membership_available", context=context
            ),
            authoring_gap_class=_required_string(
                value, "authoring_gap_class", context=context
            ),
        )
        if entry.problem_id in seen_ids:
            raise ValueError(f"duplicate NP-hard inventory problem id: {entry.problem_id}")
        endpoint = (entry.lean_module, entry.problem_term)
        if endpoint in seen_endpoints:
            raise ValueError(f"duplicate NP-hard inventory endpoint: {entry.problem_term}")
        if entry.family not in _FAMILIES:
            raise ValueError(f"invalid NP-hard inventory family: {entry.family}")
        if entry.presentation_kind not in _PRESENTATION_KINDS:
            raise ValueError(
                f"invalid NP-hard presentation kind: {entry.presentation_kind}"
            )
        if entry.existing_forward_route not in _ROUTE_KINDS:
            raise ValueError(
                f"invalid NP-hard route kind: {entry.existing_forward_route}"
            )
        if entry.authoring_gap_class not in _GAP_CLASSES:
            raise ValueError(
                f"invalid NP-hard authoring gap class: {entry.authoring_gap_class}"
            )
        if entry.known_reverse_only and entry.existing_forward_route != "none":
            raise ValueError("reverse-only inventory entry declares a forward route")
        if root is not None and not _module_file(root, entry.lean_module).is_file():
            raise ValueError(f"inventory Lean module is missing: {entry.lean_module}")
        seen_ids.add(entry.problem_id)
        seen_endpoints.add(endpoint)
        entries.append(entry)

    return NPHardInventoryV1(
        inventory_id=inventory_id,
        scope=scope,
        entries=tuple(entries),
    )


def _validate_gap_dag(authoring: Mapping[str, Any], *, case_id: str) -> None:
    raw_nodes = authoring.get("gap_nodes")
    if not isinstance(raw_nodes, list) or not raw_nodes:
        raise ValueError(f"model-authoring case {case_id} has no gap nodes")
    seen: set[str] = set()
    for node in raw_nodes:
        if not isinstance(node, dict):
            raise ValueError(f"model-authoring case {case_id} has a non-object gap node")
        node_id = _required_string(node, "id", context=f"gap node in {case_id}")
        _required_string(node, "reason", context=f"gap node {node_id} in {case_id}")
        dependencies = node.get("depends_on")
        if not isinstance(dependencies, list) or not all(
            isinstance(dependency, str) and dependency for dependency in dependencies
        ):
            raise ValueError(f"gap node {node_id} in {case_id} has invalid dependencies")
        if node_id in seen:
            raise ValueError(f"duplicate gap node {node_id} in {case_id}")
        if any(dependency not in seen for dependency in dependencies):
            raise ValueError(f"gap DAG in {case_id} is not topologically ordered")
        seen.add(node_id)


def _validate_case_shape(case: NPHardGeneralizationCaseV1) -> None:
    if case.kind not in _CASE_KINDS:
        raise ValueError(f"invalid NP-hard generalization case kind: {case.kind}")
    if case.family not in _FAMILIES:
        raise ValueError(f"invalid family in case {case.id}: {case.family}")
    if case.presentation_kind not in _PRESENTATION_KINDS:
        raise ValueError(f"invalid presentation kind in case {case.id}")
    if case.initial_expected_status not in {"VERIFIED", "BLOCKED"}:
        raise ValueError(f"invalid initial status in case {case.id}")
    if case.expected_status not in {"VERIFIED", "BLOCKED"}:
        raise ValueError(f"invalid final status in case {case.id}")
    if case.initial_expected_status == "VERIFIED" and case.initial_expected_failure_code:
        raise ValueError(f"verified initial case {case.id} declares a failure")
    if case.initial_expected_status == "BLOCKED" and not case.initial_expected_failure_code:
        raise ValueError(f"blocked initial case {case.id} omits a failure")
    if case.expected_status == "VERIFIED" and case.expected_failure_code:
        raise ValueError(f"verified final case {case.id} declares a failure")
    if case.expected_status == "BLOCKED" and not case.expected_failure_code:
        raise ValueError(f"blocked final case {case.id} omits a failure")
    if not case.public_source_files:
        raise ValueError(f"case {case.id} has no public source files")

    if case.kind == "existing_route":
        if case.route is None or case.authoring is not None or case.negative is not None:
            raise ValueError(f"existing-route case {case.id} has the wrong contract")
        if case.initial_expected_status != "VERIFIED" or case.expected_status != "VERIFIED":
            raise ValueError(f"existing-route case {case.id} is not verified")
        minimum = case.route.get("minimum_atoms")
        maximum = case.route.get("maximum_atoms")
        if not isinstance(minimum, int) or not isinstance(maximum, int):
            raise ValueError(f"existing-route case {case.id} has invalid atom bounds")
        if minimum < 0 or maximum < minimum:
            raise ValueError(f"existing-route case {case.id} has inconsistent atom bounds")
    elif case.kind == "model_authoring":
        if case.authoring is None or case.route is not None or case.negative is not None:
            raise ValueError(f"model-authoring case {case.id} has the wrong contract")
        if case.initial_expected_failure_code != "no_forward_path_from_hardness_seed":
            raise ValueError(f"model-authoring case {case.id} does not start at the real blocker")
        if case.expected_status != "VERIFIED":
            raise ValueError(f"model-authoring case {case.id} does not target verification")
        task_class = _required_string(case.authoring, "task_class", context=case.id)
        if task_class not in _TASK_CLASSES:
            raise ValueError(f"invalid authoring task class in {case.id}: {task_class}")
        _required_string(case.authoring, "hub_module", context=case.id)
        _required_string(case.authoring, "hub", context=case.id)
        program_reference = case.authoring.get("program_reference")
        if program_reference is not None and (
            not isinstance(program_reference, str) or not program_reference
        ):
            raise ValueError(f"invalid public program reference in {case.id}")
        mapping_invariant = case.authoring.get("mapping_invariant")
        if mapping_invariant is not None and (
            not isinstance(mapping_invariant, str) or not mapping_invariant
        ):
            raise ValueError(f"invalid mapping invariant in {case.id}")
        allowed_primitives = case.authoring.get("allowed_primitives")
        if not isinstance(allowed_primitives, list) or not all(
            isinstance(primitive, str) and primitive for primitive in allowed_primitives
        ):
            raise ValueError(f"invalid allowed primitive list in {case.id}")
        _required_bool(case.authoring, "requires_nontrivial_semantics", context=case.id)
        _required_bool(case.authoring, "requires_multi_gap", context=case.id)
        _required_string(case.authoring, "gold_module", context=case.id)
        _required_string(case.authoring, "gold_file", context=case.id)
        _validate_gap_dag(case.authoring, case_id=case.id)
    else:
        if case.negative is None or case.route is not None or case.authoring is not None:
            raise ValueError(f"safety-negative case {case.id} has the wrong contract")
        negative_kind = _required_string(case.negative, "kind", context=case.id)
        if negative_kind not in _NEGATIVE_KINDS:
            raise ValueError(f"invalid safety-negative kind in {case.id}: {negative_kind}")
        _optional_string(case.negative, "base_case_id", context=case.id)
        _optional_string(case.negative, "candidate_module", context=case.id)


def _validate_release_matrix(cases: tuple[NPHardGeneralizationCaseV1, ...]) -> None:
    if len(cases) != 12:
        raise ValueError("NP-hard generalization suite must contain exactly 12 cases")
    by_kind = {
        kind: [case for case in cases if case.kind == kind] for kind in _CASE_KINDS
    }
    expected_counts = {"existing_route": 5, "model_authoring": 5, "safety_negative": 2}
    actual_counts = {kind: len(values) for kind, values in by_kind.items()}
    if actual_counts != expected_counts:
        raise ValueError(
            f"invalid NP-hard generalization case matrix: {actual_counts!r}"
        )
    if len({case.family for case in cases}) < 4:
        raise ValueError("NP-hard generalization suite covers fewer than four families")

    existing = by_kind["existing_route"]
    if sum((case.route or {}).get("minimum_atoms", 0) >= 2 for case in existing) < 2:
        raise ValueError("existing-route matrix needs at least two multi-edge cases")
    if not any(not case.membership_available for case in existing):
        raise ValueError("existing-route matrix lacks a membership-free hardness case")

    authored = by_kind["model_authoring"]
    task_counts = {
        task: sum((case.authoring or {}).get("task_class") == task for case in authored)
        for task in _TASK_CLASSES
    }
    if task_counts != {
        "semantic_proof": 2,
        "program_composition": 2,
        "program_synthesis": 1,
    }:
        raise ValueError(f"invalid model-authoring task matrix: {task_counts!r}")
    if sum(
        (case.authoring or {}).get("requires_nontrivial_semantics") is True
        for case in authored
    ) < 2:
        raise ValueError("model-authoring matrix needs two nontrivial semantic cases")
    if not any(
        (case.authoring or {}).get("requires_multi_gap") is True for case in authored
    ):
        raise ValueError("model-authoring matrix lacks a multi-gap case")

    negative_kinds = {
        (case.negative or {}).get("kind") for case in by_kind["safety_negative"]
    }
    if "wrong_direction" not in negative_kinds or not (
        negative_kinds
        & {"endpoint_mutation", "forbidden_axiom", "unavailable_presentation"}
    ):
        raise ValueError("safety-negative matrix lacks the required rejection classes")


def _validate_filesystem_isolation(
    *, root: Path, suite: NPHardGeneralizationSuiteV1
) -> None:
    public_root = (root / suite.public_input_root).resolve()
    gold_root = (root / suite.gold_root).resolve()
    if not public_root.is_dir():
        raise ValueError(f"public NP-hard input root is missing: {public_root}")
    if not gold_root.is_dir():
        raise ValueError(f"isolated NP-hard gold root is missing: {gold_root}")
    if public_root == gold_root or public_root in gold_root.parents or gold_root in public_root.parents:
        raise ValueError("public input and gold roots are not isolated")

    for case in suite.cases:
        module_file = _module_file(root, case.module)
        if not module_file.is_file():
            raise ValueError(f"case Lean module is missing: {case.module}")
        for source_name in case.public_source_files:
            source = (root / source_name).resolve()
            if not source.is_file():
                raise ValueError(f"public source is missing for {case.id}: {source_name}")
            if gold_root == source or gold_root in source.parents:
                raise ValueError(f"case {case.id} exposes a gold file as public input")
            text = source.read_text(encoding="utf-8")
            if "Benchmark.Hardness.Gold" in text or "Benchmark.Hardness.Oracles" in text:
                raise ValueError(f"public source imports hidden proof material: {source_name}")
        if case.authoring is not None:
            gold_file = (root / str(case.authoring["gold_file"])).resolve()
            if not gold_file.is_file() or not (gold_root == gold_file or gold_root in gold_file.parents):
                raise ValueError(f"authoring gold is not isolated for {case.id}")


def load_np_hard_generalization_suite(
    path: Path, *, root: Path | None = None
) -> NPHardGeneralizationSuiteV1:
    raw = _read_object(path)
    if raw.get("schema_version") != NP_HARD_GENERALIZATION_SUITE_SCHEMA_V1:
        raise ValueError("unsupported NP-hard generalization suite schema")
    if raw.get("suite_id") != NP_HARD_GENERALIZATION_SUITE_ID_V1:
        raise ValueError("invalid NP-hard generalization suite identity")
    if raw.get("objective") != "prove_np_hard":
        raise ValueError("NP-hard generalization suite has the wrong objective")
    if raw.get("direction") != "hardness_seed_to_problem":
        raise ValueError("NP-hard generalization suite has the wrong direction")
    if raw.get("final_lean_type") != "ComplexityReduction.Certificate.NativeTMNPHard":
        raise ValueError("NP-hard generalization suite has the wrong final Lean type")

    raw_cases = raw.get("cases")
    if not isinstance(raw_cases, list):
        raise ValueError("NP-hard generalization cases must be a list")
    cases: list[NPHardGeneralizationCaseV1] = []
    seen_ids: set[str] = set()
    for index, value in enumerate(raw_cases):
        context = f"NP-hard generalization case {index}"
        if not isinstance(value, dict):
            raise ValueError(f"{context} must be an object")
        raw_sources = value.get("public_source_files")
        if not isinstance(raw_sources, list) or not all(
            isinstance(source, str) and source for source in raw_sources
        ):
            raise ValueError(f"{context} has invalid public source files")
        case = NPHardGeneralizationCaseV1(
            id=_required_string(value, "id", context=context),
            kind=_required_string(value, "kind", context=context),
            problem_id=_required_string(value, "problem_id", context=context),
            module=_required_string(value, "module", context=context),
            problem=_required_string(value, "problem", context=context),
            family=_required_string(value, "family", context=context),
            presentation_kind=_required_string(value, "presentation_kind", context=context),
            membership_available=_required_bool(
                value, "membership_available", context=context
            ),
            initial_expected_status=_required_string(
                value, "initial_expected_status", context=context
            ),
            initial_expected_failure_code=_optional_string(
                value, "initial_expected_failure_code", context=context
            ),
            expected_status=_required_string(value, "expected_status", context=context),
            expected_failure_code=_optional_string(
                value, "expected_failure_code", context=context
            ),
            route=value.get("route"),
            authoring=value.get("authoring"),
            negative=value.get("negative"),
            public_source_files=tuple(raw_sources),
        )
        if case.id in seen_ids:
            raise ValueError(f"duplicate NP-hard generalization case id: {case.id}")
        for optional_object, label in (
            (case.route, "route"),
            (case.authoring, "authoring"),
            (case.negative, "negative"),
        ):
            if optional_object is not None and not isinstance(optional_object, dict):
                raise ValueError(f"case {case.id} has a non-object {label} contract")
        _validate_case_shape(case)
        seen_ids.add(case.id)
        cases.append(case)

    suite = NPHardGeneralizationSuiteV1(
        inventory_path=_required_string(raw, "inventory", context="suite"),
        public_input_root=_required_string(raw, "public_input_root", context="suite"),
        gold_root=_required_string(raw, "gold_root", context="suite"),
        cases=tuple(cases),
    )
    _validate_release_matrix(suite.cases)

    if root is not None:
        inventory = load_np_hard_inventory(root / suite.inventory_path, root=root)
        inventory_by_id = inventory.by_problem_id()
        for case in suite.cases:
            entry = inventory_by_id.get(case.problem_id)
            if entry is None:
                raise ValueError(f"case {case.id} references an unknown inventory problem")
            if (
                entry.lean_module != case.module
                or entry.problem_term != case.problem
                or entry.family != case.family
                or entry.presentation_kind != case.presentation_kind
                or entry.membership_available != case.membership_available
            ):
                raise ValueError(f"case {case.id} disagrees with its inventory endpoint")
        referenced = {case.problem_id for case in suite.cases}
        if referenced != set(inventory_by_id):
            raise ValueError("NP-hard inventory contains unreferenced or missing endpoints")
        _validate_filesystem_isolation(root=root, suite=suite)

    return suite
