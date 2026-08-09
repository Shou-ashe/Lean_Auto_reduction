"""Deterministic, Lean-observed planning for NP-hard model authoring.

The planner accepts only an exact input module/declaration plus budgets.  A
nonce-bound Lean command classifies the input import closure plus globally
validated hardness seeds and reduction edges by elaborated types and controlled
definitional equality.  Python turns those observations
into the immutable V2 task; it never asks a model to select endpoints, task
class, primitives, or dependency edges.
"""

from __future__ import annotations

import json
import secrets
from dataclasses import asdict, dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Iterable, Mapping

from .lean_runner import (
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .models import CommandResult, sha256_id
from .np_hard_authoring import (
    NPHardAuthoringTaskV2,
    build_np_hard_authoring_task_v2,
)


NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1 = (
    "hardness_np_hard_authoring_observation_v2"
)
NP_HARD_AUTHORING_PLAN_SCHEMA_V2 = "hardness_np_hard_authoring_plan_v2"
NP_HARD_AUTHORING_PLANNER_MODULE = (
    "ComplexityReduction.Agent.Hardness.AuthoringPlanner"
)
_MARKER = "HARDNESS_NP_HARD_PLAN"
_HASH_PREFIX = "sha256:"
_FORBIDDEN_TEXT = (
    '"case_id"',
    '"expected"',
    '"gold"',
    '"hidden_gold"',
    ".gold.",
    ".oracles.",
    ".hiddentargets.",
)


class NPHardAuthoringPlannerError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardAuthoringPlannerError(code, message)


def _tagged_file_hash(path: Path) -> str:
    return _HASH_PREFIX + sha256_file(path)


def _assert_public(value: str, *, label: str) -> None:
    lowered = value.lower()
    if any(token in lowered for token in _FORBIDDEN_TEXT):
        _fail("oracle_or_gold_import", f"{label} contains benchmark-only metadata")


def _ilean_roots(root: Path) -> tuple[Path, ...]:
    lean_root = root.resolve() / "Lean"
    roots = [lean_root / ".lake" / "build" / "lib" / "lean"]
    package_root = lean_root / ".lake" / "packages"
    if package_root.is_dir():
        roots.extend(
            sorted(package_root.glob("*/.lake/build/lib/lean"), key=str)
        )
    return tuple(path for path in roots if path.is_dir())


def _ilean_file(root: Path, module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".ilean")
    for build_root in _ilean_roots(root):
        candidate = build_root / relative
        if candidate.is_file():
            return candidate
    return None


@lru_cache(maxsize=64)
def lean_import_closure(
    *, root: Path, input_module: str
) -> tuple[tuple[str, ...], str]:
    """Return a compiled, content-addressed transitive import closure.

    Project/package ``.ilean`` metadata is authoritative for direct imports.
    Modules supplied by the Lean toolchain may not have a workspace artifact;
    their names remain in the closure and the exact toolchain file is bound
    separately by the observation.
    """

    input_module = validate_module_name(input_module)
    pending = [input_module]
    visited: set[str] = set()
    artifacts: dict[str, str | None] = {}
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        artifact = _ilean_file(root, module)
        if artifact is None:
            artifacts[module] = None
            continue
        artifacts[module] = _tagged_file_hash(artifact)
        try:
            metadata = json.loads(artifact.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            _fail(
                "authoring_catalog_dependency_invalid",
                f"cannot read compiled import metadata for {module}: {error}",
            )
        direct_imports = metadata.get("directImports")
        if not isinstance(direct_imports, list):
            _fail(
                "authoring_catalog_dependency_invalid",
                f"compiled module {module} has no direct import table",
            )
        for row in direct_imports:
            if (
                not isinstance(row, list)
                or not row
                or not isinstance(row[0], str)
                or not row[0]
            ):
                _fail(
                    "authoring_catalog_dependency_invalid",
                    f"compiled module {module} has a malformed import row",
                )
            pending.append(validate_module_name(row[0]))
    modules = tuple(sorted(visited))
    closure_hash = sha256_id(
        {
            "schema_version": "hardness_lean_import_closure_v1",
            "input_module": input_module,
            "artifacts": {module: artifacts[module] for module in modules},
        }
    )
    return modules, closure_hash


def _catalog_scan_modules(import_modules: Iterable[str]) -> tuple[str, ...]:
    selected = tuple(
        sorted(
            module
            for module in set(import_modules)
            if module.startswith(("ComplexityReduction.", "Benchmark."))
        )
    )
    if not selected:
        _fail(
            "authoring_catalog_dependency_invalid",
            "input import closure has no mounted Complexity Reduction modules",
        )
    return selected


@dataclass(frozen=True)
class PlannerProblemV1:
    declaration: str
    endpoint_node: str
    representation_node: str
    rendered_endpoint: str
    rendered_representation: str
    module: str


@dataclass(frozen=True)
class PlannerPolyProgramV1:
    declaration: str
    source: str
    target: str
    source_representation_node: str
    target_representation_node: str
    exact_type: str
    module: str


@dataclass(frozen=True)
class PlannerMappingRelationV1:
    declaration: str
    source: str
    target: str
    exact_type: str
    module: str


@dataclass(frozen=True)
class PlannerGapV1:
    declaration: str
    reason: str
    failure_code: str
    role: str
    source: str
    target: str
    capability_head: str
    source_node: str
    target_node: str
    module: str


@dataclass(frozen=True)
class PlannerBuiltinV1:
    declaration: str
    exact_type: str
    module: str


@dataclass(frozen=True)
class PlannerHardnessSeedV1:
    problem: str
    endpoint_node: str
    evidence: str
    evidence_kind: str
    exact_type: str
    module: str

    @property
    def seed_id(self) -> str:
        return sha256_id(asdict(self))


@dataclass(frozen=True)
class PlannerPrimitiveV1:
    declaration: str
    source: str
    target: str
    source_representation_node: str
    target_representation_node: str
    exact_type: str
    module: str


@dataclass(frozen=True)
class PlannerCertifiedReductionV1:
    declaration: str
    lean_term: str
    capability: str
    direction: str
    role: str
    source: str
    target: str
    source_node: str
    target_node: str
    exact_type: str
    module: str

    @property
    def edge_id(self) -> str:
        return sha256_id(asdict(self))


@dataclass(frozen=True)
class NPHardAuthoringObservationV1:
    nonce: str
    input_module: str
    input_declaration: str
    input_node: str
    owner_namespace: str
    declaration_module: str
    registry_fingerprint: str
    import_modules: tuple[str, ...]
    import_closure_sha256: str
    toolchain: str
    lake_manifest_sha256: str
    problems: tuple[PlannerProblemV1, ...]
    poly_programs: tuple[PlannerPolyProgramV1, ...]
    mapping_relations: tuple[PlannerMappingRelationV1, ...]
    gaps: tuple[PlannerGapV1, ...]
    builtins: tuple[PlannerBuiltinV1, ...]
    hardness_seeds: tuple[PlannerHardnessSeedV1, ...]
    primitives: tuple[PlannerPrimitiveV1, ...]
    certified_reductions: tuple[PlannerCertifiedReductionV1, ...]
    complete_problem_count: int
    schema_version: str = NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1

    @property
    def observation_id(self) -> str:
        payload = self.to_dict(include_id=False)
        payload.pop("nonce", None)
        return sha256_id(payload)

    def to_dict(self, *, include_id: bool = True) -> dict[str, Any]:
        payload = {
            "schema_version": self.schema_version,
            "nonce": self.nonce,
            "input_module": self.input_module,
            "input_declaration": self.input_declaration,
            "input_node": self.input_node,
            "owner_namespace": self.owner_namespace,
            "declaration_module": self.declaration_module,
            "registry_fingerprint": self.registry_fingerprint,
            "import_modules": list(self.import_modules),
            "import_closure_sha256": self.import_closure_sha256,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "problems": [asdict(item) for item in self.problems],
            "poly_programs": [asdict(item) for item in self.poly_programs],
            "mapping_relations": [asdict(item) for item in self.mapping_relations],
            "gaps": [asdict(item) for item in self.gaps],
            "builtins": [asdict(item) for item in self.builtins],
            "hardness_seeds": [
                {**asdict(item), "seed_id": item.seed_id}
                for item in self.hardness_seeds
            ],
            "primitives": [asdict(item) for item in self.primitives],
            "certified_reductions": [
                {**asdict(item), "edge_id": item.edge_id}
                for item in self.certified_reductions
            ],
            "complete_problem_count": self.complete_problem_count,
        }
        if include_id:
            payload["observation_id"] = self.observation_id
        return payload


def _marker_rows(*, stdout: str, stderr: str, nonce: str) -> list[list[str]]:
    rows: list[list[str]] = []
    for line in (stdout + "\n" + stderr).splitlines():
        marker_index = line.find(_MARKER + "\t")
        if marker_index < 0:
            continue
        fields = line[marker_index:].split("\t")
        if len(fields) < 5:
            _fail("invalid_authoring_planner_observation", "truncated Lean planner row")
        if fields[0] != _MARKER or fields[1] != NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1:
            _fail("invalid_authoring_planner_observation", "planner marker/schema drifted")
        if fields[2] != nonce:
            continue
        rows.append(fields[3:])
    if not rows:
        _fail("authoring_planner_probe_failed", "Lean emitted no nonce-bound planner rows")
    return rows


def parse_np_hard_authoring_observation(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    input_module: str,
    input_declaration: str,
    import_modules: tuple[str, ...],
    import_closure_sha256: str,
    toolchain: str,
    lake_manifest_sha256: str,
) -> NPHardAuthoringObservationV1:
    validate_module_name(input_module)
    validate_declaration_name(input_declaration, label="planner input")
    rows = _marker_rows(stdout=stdout, stderr=stderr, nonce=nonce)
    inputs: list[list[str]] = []
    problems: list[PlannerProblemV1] = []
    programs: list[PlannerPolyProgramV1] = []
    relations: list[PlannerMappingRelationV1] = []
    gaps: list[PlannerGapV1] = []
    builtins: list[PlannerBuiltinV1] = []
    seeds: list[PlannerHardnessSeedV1] = []
    primitives: list[PlannerPrimitiveV1] = []
    reductions: list[PlannerCertifiedReductionV1] = []
    completes: list[list[str]] = []
    fingerprints: set[str] = set()
    for row in rows:
        kind, *fields = row
        expected_fields = {
            "input": 5,
            "problem": 7,
            "poly_program": 8,
            "mapping_relation": 6,
            "gap": 11,
            "builtin": 4,
            "hardness_seed": 7,
            "primitive": 8,
            "certified_reduction": 12,
            "complete": 2,
        }
        if kind not in expected_fields or len(fields) != expected_fields[kind]:
            _fail(
                "invalid_authoring_planner_observation",
                f"unexpected {kind!r} planner row shape",
            )
        fingerprint = fields[-1]
        if not fingerprint.startswith("lean:"):
            _fail("invalid_authoring_planner_observation", "missing Lean registry fingerprint")
        fingerprints.add(fingerprint)
        if kind == "input":
            inputs.append(fields)
        elif kind == "problem":
            problems.append(PlannerProblemV1(*fields[:-1]))
        elif kind == "poly_program":
            programs.append(PlannerPolyProgramV1(*fields[:-1]))
        elif kind == "mapping_relation":
            relations.append(PlannerMappingRelationV1(*fields[:-1]))
        elif kind == "gap":
            gaps.append(PlannerGapV1(*fields[:-1]))
        elif kind == "builtin":
            builtins.append(PlannerBuiltinV1(*fields[:-1]))
        elif kind == "hardness_seed":
            seeds.append(PlannerHardnessSeedV1(*fields[:-1]))
        elif kind == "primitive":
            primitives.append(PlannerPrimitiveV1(*fields[:-1]))
        elif kind == "certified_reduction":
            reductions.append(PlannerCertifiedReductionV1(*fields[:-1]))
        elif kind == "complete":
            completes.append(fields)
    if len(inputs) != 1 or len(completes) != 1 or len(fingerprints) != 1:
        _fail(
            "invalid_authoring_planner_observation",
            "planner output is incomplete or mixes Lean environments",
        )
    declaration, input_node, owner_namespace, declaration_module, fingerprint = inputs[0]
    if declaration != input_declaration:
        _fail("candidate_wrong_endpoint", "planner returned a substituted input endpoint")
    if not input_node.startswith("lean-whnf:"):
        _fail("invalid_authoring_planner_observation", "input has no exact Lean node")
    if not any(problem.declaration == input_declaration for problem in problems):
        _fail("candidate_wrong_endpoint", "input is absent from the local exact problem set")
    if len({item.declaration for item in problems}) != len(problems):
        _fail("invalid_authoring_planner_observation", "duplicate exact problem observation")
    for collection in (programs, relations, gaps, builtins, primitives):
        if len({item.declaration for item in collection}) != len(collection):
            _fail("invalid_authoring_planner_observation", "duplicate capability observation")
    if len({item.seed_id for item in seeds}) != len(seeds) or len(
        {item.edge_id for item in reductions}
    ) != len(reductions):
        _fail("invalid_authoring_planner_observation", "duplicate registered capability")
    problem_names = {problem.declaration for problem in problems}
    for program in programs:
        if program.source not in problem_names or program.target not in problem_names:
            _fail("candidate_wrong_endpoint", "PolyProg endpoint escaped the exact problem set")
    for relation in relations:
        if relation.source not in problem_names or relation.target not in problem_names:
            _fail("candidate_wrong_endpoint", "mapping relation endpoint escaped the problem set")
    for gap in gaps:
        if gap.source not in problem_names or gap.target not in problem_names:
            _fail("candidate_wrong_endpoint", "typed gap endpoint escaped the problem set")
    for primitive in primitives:
        if primitive.source not in problem_names or primitive.target not in problem_names:
            _fail("candidate_wrong_endpoint", "primitive endpoint escaped the problem set")
    for reduction in reductions:
        if reduction.source not in problem_names or reduction.target not in problem_names:
            _fail("candidate_wrong_endpoint", "certified edge escaped the problem set")
        if reduction.direction not in {"forward", "backward"}:
            _fail("candidate_wrong_direction", "certified edge direction is invalid")
    for seed in seeds:
        if seed.problem not in problem_names:
            _fail("fabricated_hardness_seed", "hardness seed endpoint escaped the problem set")
        if seed.evidence_kind not in {
            "native_hardness",
            "native_completeness_projection",
        }:
            _fail("fabricated_hardness_seed", "hardness seed kind is invalid")
    closure_set = set(import_modules)
    if declaration_module not in closure_set:
        _fail("authoring_catalog_dependency_stale", "input declaration escaped its import closure")
    for capability in (*programs, *relations, *gaps):
        if capability.module not in closure_set:
            _fail(
                "authoring_catalog_dependency_stale",
                f"closure capability escaped its import graph: {capability.declaration}",
            )
    if not import_closure_sha256.startswith(_HASH_PREFIX):
        _fail("authoring_catalog_dependency_stale", "import closure is not content addressed")
    if not toolchain or not lake_manifest_sha256.startswith(_HASH_PREFIX):
        _fail("authoring_catalog_dependency_stale", "catalog build metadata is incomplete")
    try:
        complete_count = int(completes[0][0])
    except ValueError:
        _fail("invalid_authoring_planner_observation", "invalid completion count")
    if complete_count != len(problems):
        _fail("invalid_authoring_planner_observation", "Lean completion count drifted")
    observation = NPHardAuthoringObservationV1(
        nonce=nonce,
        input_module=input_module,
        input_declaration=input_declaration,
        input_node=input_node,
        owner_namespace=owner_namespace,
        declaration_module=declaration_module,
        registry_fingerprint=fingerprint,
        import_modules=tuple(sorted(import_modules)),
        import_closure_sha256=import_closure_sha256,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        problems=tuple(sorted(problems, key=lambda item: item.declaration)),
        poly_programs=tuple(sorted(programs, key=lambda item: item.declaration)),
        mapping_relations=tuple(sorted(relations, key=lambda item: item.declaration)),
        gaps=tuple(sorted(gaps, key=lambda item: item.declaration)),
        builtins=tuple(sorted(builtins, key=lambda item: item.declaration)),
        hardness_seeds=tuple(sorted(seeds, key=lambda item: item.seed_id)),
        primitives=tuple(sorted(primitives, key=lambda item: item.declaration)),
        certified_reductions=tuple(
            sorted(reductions, key=lambda item: item.edge_id)
        ),
        complete_problem_count=complete_count,
    )
    serialized = json.dumps(observation.to_dict(), sort_keys=True)
    _assert_public(serialized, label="Lean authoring observation")
    return observation


@dataclass(frozen=True)
class PlannerCapabilityNodeV2:
    node_id: str
    capability: str
    declaration: str
    exact_type: str
    depends_on: tuple[str, ...]
    authority: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "node_id": self.node_id,
            "capability": self.capability,
            "declaration": self.declaration,
            "exact_type": self.exact_type,
            "depends_on": list(self.depends_on),
            "authority": self.authority,
        }


@dataclass(frozen=True)
class NPHardAuthoringPlanV2:
    status: str
    failure_code: str | None
    missing_capabilities: tuple[str, ...]
    observation: NPHardAuthoringObservationV1
    task: NPHardAuthoringTaskV2 | None
    final_program_declaration: str | None
    capability_dag: tuple[PlannerCapabilityNodeV2, ...]
    commands: tuple[CommandResult, ...]
    selected_hub: str | None = None
    ranked_hubs: tuple[str, ...] = ()
    rejected_hubs: tuple[Mapping[str, Any], ...] = ()
    model_calls: int = 0
    schema_version: str = NP_HARD_AUTHORING_PLAN_SCHEMA_V2

    @property
    def plan_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "status": self.status,
                "failure_code": self.failure_code,
                "missing_capabilities": list(self.missing_capabilities),
                "observation_id": self.observation.observation_id,
                "task_request_id": self.task.request_id if self.task is not None else None,
                "final_program_declaration": self.final_program_declaration,
                "capability_dag": [node.to_dict() for node in self.capability_dag],
                "selected_hub": self.selected_hub,
                "ranked_hubs": list(self.ranked_hubs),
                "rejected_hubs": [dict(item) for item in self.rejected_hubs],
                "model_calls": self.model_calls,
            }
        )

    def to_dict(self, *, include_plan_id: bool = True) -> dict[str, Any]:
        payload = {
            "schema_version": self.schema_version,
            "status": self.status,
            "failure_code": self.failure_code,
            "missing_capabilities": list(self.missing_capabilities),
            "observation": self.observation.to_dict(),
            "task": self.task.to_dict() if self.task is not None else None,
            "final_program_declaration": self.final_program_declaration,
            "capability_dag": [node.to_dict() for node in self.capability_dag],
            "commands": [command.to_dict() for command in self.commands],
            "selected_hub": self.selected_hub,
            "ranked_hubs": list(self.ranked_hubs),
            "rejected_hubs": [dict(item) for item in self.rejected_hubs],
            "model_calls": self.model_calls,
        }
        if include_plan_id:
            payload["plan_id"] = self.plan_id
        return payload


def _shortest_program_path(
    programs: Iterable[PlannerPolyProgramV1],
    *,
    problems: Mapping[str, PlannerProblemV1],
    source: str,
    target: str,
) -> tuple[PlannerPolyProgramV1, ...] | None:
    source_problem = problems[source]
    target_problem = problems[target]
    adjacency: dict[str, list[PlannerPolyProgramV1]] = {}
    for program in programs:
        adjacency.setdefault(program.source_representation_node, []).append(program)
    for edges in adjacency.values():
        edges.sort(
            key=lambda edge: (edge.target_representation_node, edge.declaration)
        )
    queue: list[tuple[str, tuple[PlannerPolyProgramV1, ...], frozenset[str]]] = [
        (
            source_problem.representation_node,
            (),
            frozenset({source_problem.representation_node}),
        )
    ]
    while queue:
        endpoint, path, visited = queue.pop(0)
        if endpoint == target_problem.representation_node:
            return path
        for edge in adjacency.get(endpoint, []):
            if edge.target_representation_node in visited:
                continue
            queue.append(
                (
                    edge.target_representation_node,
                    path + (edge,),
                    visited | {edge.target_representation_node},
                )
            )
    return None


def _shortest_hardness_route(
    *,
    seeds: Iterable[PlannerHardnessSeedV1],
    reductions: Iterable[PlannerCertifiedReductionV1],
    target_node: str,
) -> tuple[PlannerHardnessSeedV1, tuple[PlannerCertifiedReductionV1, ...]] | None:
    adjacency: dict[str, list[PlannerCertifiedReductionV1]] = {}
    for reduction in reductions:
        adjacency.setdefault(reduction.source_node, []).append(reduction)
    for edges in adjacency.values():
        edges.sort(
            key=lambda edge: (
                edge.target_node,
                edge.declaration,
                edge.direction,
                edge.lean_term,
            )
        )
    queue: list[
        tuple[
            str,
            PlannerHardnessSeedV1,
            tuple[PlannerCertifiedReductionV1, ...],
            frozenset[str],
        ]
    ] = [
        (seed.endpoint_node, seed, (), frozenset({seed.endpoint_node}))
        for seed in sorted(seeds, key=lambda item: item.seed_id)
    ]
    candidates: list[
        tuple[PlannerHardnessSeedV1, tuple[PlannerCertifiedReductionV1, ...]]
    ] = []
    while queue:
        endpoint, seed, path, visited = queue.pop(0)
        if endpoint == target_node:
            candidates.append((seed, path))
            continue
        if len(path) >= 8:
            continue
        for edge in adjacency.get(endpoint, []):
            if edge.target_node in visited:
                continue
            queue.append(
                (
                    edge.target_node,
                    seed,
                    path + (edge,),
                    visited | {edge.target_node},
                )
            )
    if not candidates:
        return None
    return min(
        candidates,
        key=lambda item: (
            len(item[1]),
            sum(edge.role == "finalComposition" for edge in item[1]),
            len({edge.declaration for edge in item[1]}),
            item[0].seed_id,
            tuple(edge.edge_id for edge in item[1]),
        ),
    )


def _task_gap_nodes(
    *, task_class: str, has_mapping_relation: bool
) -> tuple[Mapping[str, Any], ...]:
    if task_class == "semantic_proof":
        if has_mapping_relation:
            return (
                {"id": "mapping-invariant", "reason": "semanticProof", "depends_on": []},
                {
                    "id": "semantic-iff",
                    "reason": "semanticProof",
                    "depends_on": ["mapping-invariant"],
                },
            )
        return ({"id": "semantic-proof", "reason": "semanticProof", "depends_on": []},)
    if task_class == "program_composition":
        return (
            {
                "id": "composed-program",
                "reason": "executableRelationContract",
                "depends_on": [],
            },
            {
                "id": "semantic-proof",
                "reason": "semanticProof",
                "depends_on": ["composed-program"],
            },
        )
    if task_class == "program_synthesis":
        return (
            {"id": "reduction-executable", "reason": "primitive", "depends_on": []},
            {
                "id": "poly-program",
                "reason": "executableRelationContract",
                "depends_on": ["reduction-executable"],
            },
            {
                "id": "program-run-coherence",
                "reason": "executableRelationContract",
                "depends_on": ["poly-program"],
            },
            {
                "id": "mapping-invariant",
                "reason": "semanticProof",
                "depends_on": ["program-run-coherence"],
            },
            {
                "id": "semantic-iff",
                "reason": "semanticProof",
                "depends_on": ["mapping-invariant"],
            },
        )
    _fail("authoring_plan_unsupported", f"unsupported task class: {task_class}")


def _full_capability_dag(
    *,
    task: NPHardAuthoringTaskV2,
    hardness_seed: PlannerHardnessSeedV1,
    hardness_route: tuple[PlannerCertifiedReductionV1, ...],
    existing_programs: tuple[PlannerPolyProgramV1, ...],
    mapping_relation: PlannerMappingRelationV1 | None,
    final_program_declaration: str,
) -> tuple[PlannerCapabilityNodeV2, ...]:
    nodes: list[PlannerCapabilityNodeV2] = [
        PlannerCapabilityNodeV2(
            node_id="native-hardness-seed",
            capability="native_hardness_seed",
            declaration=hardness_seed.evidence,
            exact_type=hardness_seed.exact_type,
            depends_on=(),
            authority="lean_registry_exact_type_observation",
        )
    ]
    previous_hardness = "native-hardness-seed"
    for index, reduction in enumerate(hardness_route, start=1):
        node_id = f"public-certified-reduction-{index}"
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id=node_id,
                capability="certified_reduction_route",
                declaration=reduction.lean_term,
                exact_type=reduction.exact_type,
                depends_on=(previous_hardness,),
                authority="lean_registry_exact_type_and_direction",
            )
        )
        previous_hardness = node_id
    previous_existing: str | None = None
    for index, program in enumerate(existing_programs, start=1):
        node_id = f"public-poly-program-{index}"
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id=node_id,
                capability="poly_program",
                declaration=program.declaration,
                exact_type=program.exact_type,
                depends_on=((previous_existing,) if previous_existing else ()),
                authority="lean_exact_type_observation",
            )
        )
        previous_existing = node_id
    if mapping_relation is not None:
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id="public-mapping-relation",
                capability="mapping_invariant_specification",
                declaration=mapping_relation.declaration,
                exact_type=mapping_relation.exact_type,
                depends_on=(),
                authority="lean_exact_type_observation",
            )
        )
    for obligation in task.gap_nodes:
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id=obligation.node_id,
                capability=obligation.capability,
                declaration=obligation.declaration,
                exact_type=obligation.exact_type,
                depends_on=obligation.depends_on,
                authority="model_body_plus_lean_kernel",
            )
        )
    semantic_node = task.gap_nodes[-1].node_id
    semantic_declaration = task.gap_nodes[-1].declaration
    nodes.extend(
        (
            PlannerCapabilityNodeV2(
                node_id="semantic-forward-implication",
                capability="semantic_forward_implication",
                declaration=semantic_declaration,
                exact_type=f"forward projection of {task.gap_nodes[-1].exact_type}",
                depends_on=(semantic_node,),
                authority="lean_iff_projection",
            ),
            PlannerCapabilityNodeV2(
                node_id="semantic-reverse-implication",
                capability="semantic_reverse_implication",
                declaration=semantic_declaration,
                exact_type=f"reverse projection of {task.gap_nodes[-1].exact_type}",
                depends_on=(semantic_node,),
                authority="lean_iff_projection",
            ),
            PlannerCapabilityNodeV2(
                node_id="certified-reduction",
                capability="certified_reduction",
                declaration=task.final_candidate_declaration,
                exact_type=task.final_exact_type,
                depends_on=(semantic_node, previous_hardness),
                authority=f"runner_owned_assembly_with_program:{final_program_declaration}",
            ),
            PlannerCapabilityNodeV2(
                node_id="native-tm-np-hard",
                capability="native_tm_np_hard",
                declaration=f"{task.candidate_module}.authoredExactNPHardness",
                exact_type=(
                    "ComplexityReduction.Certificate.NativeTMNPHard "
                    f"{task.target_problem.term}"
                ),
                depends_on=("certified-reduction",),
                authority="closed_resolver_plus_lean_kernel",
            ),
        )
    )
    node_ids: set[str] = set()
    for node in nodes:
        if node.node_id in node_ids or any(dep not in node_ids for dep in node.depends_on):
            _fail("authoring_plan_cycle", "capability DAG is cyclic or not topologically ordered")
        node_ids.add(node.node_id)
    return tuple(nodes)


def plan_np_hard_authoring_from_observation(
    *,
    root: Path,
    input_module: str,
    input_problem_declaration: str,
    observation: NPHardAuthoringObservationV1,
    commands: tuple[CommandResult, ...] = (),
    attempt_budget: int = 4,
    timeout_seconds: int = 60,
    max_output_tokens: int = 3000,
) -> NPHardAuthoringPlanV2:
    validate_module_name(input_module)
    validate_declaration_name(input_problem_declaration, label="planner target")
    if observation.input_module != input_module:
        _fail("authoring_catalog_dependency_stale", "observation belongs to another module")
    current_modules, current_closure = lean_import_closure(
        root=root.resolve(), input_module=input_module
    )
    current_toolchain = (root.resolve() / "Lean" / "lean-toolchain").read_text(
        encoding="utf-8"
    ).strip()
    current_manifest = _tagged_file_hash(root.resolve() / "Lean" / "lake-manifest.json")
    if (
        observation.import_modules != current_modules
        or observation.import_closure_sha256 != current_closure
        or observation.toolchain != current_toolchain
        or observation.lake_manifest_sha256 != current_manifest
    ):
        _fail(
            "authoring_catalog_dependency_stale",
            "authoring catalog no longer matches source, toolchain, or lake manifest",
        )
    if observation.input_declaration != input_problem_declaration:
        _fail("candidate_wrong_endpoint", "observation does not belong to the requested input")
    target = input_problem_declaration
    problems = {problem.declaration: problem for problem in observation.problems}
    target_problem = problems.get(target)
    if target_problem is None:
        _fail("candidate_wrong_endpoint", "target is absent from the exact problem catalog")

    def problem_node(declaration: str) -> str:
        return problems[declaration].endpoint_node

    target_node = target_problem.endpoint_node
    gap_source_names = {
        gap.source
        for gap in observation.gaps
        if gap.target_node == target_node and gap.source_node != target_node
    }
    incoming_program_sources: set[str] = set()
    for program in observation.poly_programs:
        if program.source not in problems:
            continue
        path = _shortest_program_path(
            observation.poly_programs,
            problems=problems,
            source=program.source,
            target=target,
        )
        if path:
            incoming_program_sources.add(program.source)
    candidate_names = gap_source_names or incoming_program_sources
    if not candidate_names:
        return NPHardAuthoringPlanV2(
            status="BLOCKED",
            failure_code="authoring_plan_missing_capability",
            missing_capabilities=("forward_hardness_hub", "typed_forward_gap"),
            observation=observation,
            task=None,
            final_program_declaration=None,
            capability_dag=(),
            commands=commands,
        )

    # Definitionally equal aliases are one hub.  Prefer the exact name carried
    # by a typed gap, then use a deterministic declaration tie-break.
    by_endpoint: dict[str, list[str]] = {}
    for name in candidate_names:
        by_endpoint.setdefault(problem_node(name), []).append(name)
    canonical_candidates = tuple(
        min(
            names,
            key=lambda name: (name not in gap_source_names, len(name), name),
        )
        for _, names in sorted(by_endpoint.items())
        if _ != target_node
    )

    ranked: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    reverse_observed = False
    expected_builtins = {
        "ComplexityReduction.Program.PolyProg.const",
        "ComplexityReduction.Program.PolyProg.id",
        "ComplexityReduction.Program.PolyProg.pair",
    }
    builtin_names = {builtin.declaration for builtin in observation.builtins}
    for hub in canonical_candidates:
        hub_problem = problems[hub]
        hardness = _shortest_hardness_route(
            seeds=observation.hardness_seeds,
            reductions=observation.certified_reductions,
            target_node=hub_problem.endpoint_node,
        )
        if hardness is None:
            rejected.append(
                {
                    "hub": hub,
                    "endpoint_node": hub_problem.endpoint_node,
                    "code": "no_forward_path_from_hardness_seed",
                    "missing_capabilities": ["hardness_seed_reachability"],
                }
            )
            continue
        path = _shortest_program_path(
            observation.poly_programs,
            problems=problems,
            source=hub,
            target=target,
        )
        reverse = _shortest_program_path(
            observation.poly_programs,
            problems=problems,
            source=target,
            target=hub,
        )
        reverse_observed = reverse_observed or bool(reverse)
        gap_reasons = {
            gap.reason
            for gap in observation.gaps
            if gap.source_node == hub_problem.endpoint_node
            and gap.target_node == target_node
        }
        relation = next(
            (
                item
                for item in observation.mapping_relations
                if problem_node(item.source) == hub_problem.endpoint_node
                and problem_node(item.target) == target_node
            ),
            None,
        )
        missing: list[str] = []
        if path is not None and len(path) == 1:
            task_class = "semantic_proof"
            selected_programs = path
            risk_rank = 1
        elif path is not None and len(path) >= 2:
            task_class = "program_composition"
            selected_programs = path
            risk_rank = 2
        elif {"primitive", "executableRelationContract", "semanticProof"}.issubset(
            gap_reasons
        ):
            task_class = "program_synthesis"
            selected_programs = ()
            risk_rank = 3
            if relation is None:
                missing.append("mapping_invariant")
            if not expected_builtins.issubset(builtin_names):
                missing.append("poly_program_synthesis_primitives")
        else:
            task_class = "unsupported"
            selected_programs = ()
            risk_rank = 4
            if path is None:
                missing.append("poly_program")
            if "semanticProof" not in gap_reasons:
                missing.append("semantic_proof_gap")
        if missing or task_class == "unsupported":
            rejected.append(
                {
                    "hub": hub,
                    "endpoint_node": hub_problem.endpoint_node,
                    "code": "wrong_direction_only" if reverse and not path else "authoring_plan_missing_capability",
                    "missing_capabilities": sorted(set(missing or ["closed_capability_dag"])),
                }
            )
            continue
        node_count = len(
            _task_gap_nodes(
                task_class=task_class, has_mapping_relation=relation is not None
            )
        )
        seed, hardness_route = hardness
        safety_rank = (
            node_count,
            risk_rank,
            len(hardness_route),
            len(selected_programs),
            len({edge.declaration for edge in hardness_route}),
        )
        ranked.append(
            {
                "hub": hub,
                "endpoint_node": hub_problem.endpoint_node,
                "task_class": task_class,
                "programs": selected_programs,
                "relation": relation,
                "seed": seed,
                "hardness_route": hardness_route,
                "safety_rank": safety_rank,
                "stable_rank": (*safety_rank, hub_problem.module, hub),
            }
        )
    ranked.sort(key=lambda item: item["stable_rank"])
    if not ranked:
        missing = tuple(
            sorted(
                {
                    capability
                    for item in rejected
                    for capability in item["missing_capabilities"]
                }
                or {"closed_capability_dag"}
            )
        )
        return NPHardAuthoringPlanV2(
            status="BLOCKED",
            failure_code=("wrong_direction_only" if reverse_observed else "authoring_plan_missing_capability"),
            missing_capabilities=missing,
            observation=observation,
            task=None,
            final_program_declaration=None,
            capability_dag=(),
            commands=commands,
            ranked_hubs=(),
            rejected_hubs=tuple(rejected),
        )
    best_safety_rank = ranked[0]["safety_rank"]
    equally_best_nodes = {
        item["endpoint_node"]
        for item in ranked
        if item["safety_rank"] == best_safety_rank
    }
    if len(equally_best_nodes) > 1:
        return NPHardAuthoringPlanV2(
            status="BLOCKED",
            failure_code="ambiguous_authoring_hub",
            missing_capabilities=("unique_optimal_forward_hub",),
            observation=observation,
            task=None,
            final_program_declaration=None,
            capability_dag=(),
            commands=commands,
            ranked_hubs=tuple(item["hub"] for item in ranked),
            rejected_hubs=tuple(rejected),
        )
    selected = ranked[0]
    hub = selected["hub"]
    hub_problem = problems[hub]
    task_class = selected["task_class"]
    selected_programs = selected["programs"]
    relation = selected["relation"]
    hardness_seed = selected["seed"]
    hardness_route = selected["hardness_route"]
    direct = selected_programs[0] if task_class == "semantic_proof" else None
    if task_class == "program_synthesis":
        compatible_primitives = tuple(
            primitive.declaration
            for primitive in observation.primitives
            if primitive.source_representation_node == hub_problem.representation_node
            and primitive.target_representation_node == target_problem.representation_node
        )
        allowed_primitives = tuple(
            dict.fromkeys(
                (
                    *sorted(builtin.declaration for builtin in observation.builtins),
                    *sorted(compatible_primitives),
                    *((relation.declaration,) if relation is not None else ()),
                )
            )
        )
        program_reference = None
    else:
        allowed_primitives = tuple(program.declaration for program in selected_programs)
        if task_class == "semantic_proof" and relation is not None:
            allowed_primitives += (relation.declaration,)
        program_reference = direct.declaration if direct is not None else None
    public_modules = {
        input_module,
        observation.declaration_module,
        hub_problem.module,
        *(program.module for program in selected_programs),
        *((relation.module,) if relation is not None else ()),
        *(
            gap.module
            for gap in observation.gaps
            if gap.source_node == hub_problem.endpoint_node
            and gap.target_node == target_node
        ),
    }
    public_files = tuple(
        sorted(
            str(module_file(root.resolve() / "Lean", module).relative_to(root.resolve()))
            for module in public_modules
        )
    )
    task = build_np_hard_authoring_task_v2(
        root=root,
        input_module=input_module,
        input_problem_declaration=target,
        hub_module=hub_problem.module,
        hub_declaration=hub,
        task_class=task_class,
        gap_nodes=_task_gap_nodes(
            task_class=task_class, has_mapping_relation=relation is not None
        ),
        public_source_files=public_files,
        allowed_primitives=allowed_primitives,
        program_reference=program_reference,
        mapping_invariant=relation.declaration if relation is not None else None,
        additional_dependency_hashes={
            "content:lean-planner-observation": observation.observation_id,
            "content:lean-registry-fingerprint": sha256_id(
                observation.registry_fingerprint
            ),
            "content:lean-import-closure": observation.import_closure_sha256,
            "content:lean-toolchain": _tagged_file_hash(
                root.resolve() / "Lean" / "lean-toolchain"
            ),
            "content:lake-manifest": observation.lake_manifest_sha256,
        },
        attempt_budget=attempt_budget,
        timeout_seconds=timeout_seconds,
        max_output_tokens=max_output_tokens,
    )
    if task_class == "semantic_proof":
        assert direct is not None
        final_program = direct.declaration
    elif task_class == "program_composition":
        final_program = f"{task.candidate_module}.composedProgram"
    else:
        final_program = f"{task.candidate_module}.synthesizedProgram"
    dag = _full_capability_dag(
        task=task,
        hardness_seed=hardness_seed,
        hardness_route=hardness_route,
        existing_programs=selected_programs,
        mapping_relation=relation,
        final_program_declaration=final_program,
    )
    plan = NPHardAuthoringPlanV2(
        status="PLANNED",
        failure_code=None,
        missing_capabilities=(),
        observation=observation,
        task=task,
        final_program_declaration=final_program,
        capability_dag=dag,
        commands=commands,
        selected_hub=hub,
        ranked_hubs=tuple(item["hub"] for item in ranked),
        rejected_hubs=tuple(rejected),
    )
    _assert_public(
        json.dumps(
            {
                "task": task.to_dict(),
                "capability_dag": [node.to_dict() for node in dag],
            },
            sort_keys=True,
        ),
        label="authoring plan",
    )
    return plan


def build_np_hard_authoring_observation_source(
    *,
    input_module: str,
    input_problem_declaration: str,
    nonce: str,
    allowed_modules: tuple[str, ...],
) -> str:
    validate_module_name(input_module)
    validate_declaration_name(input_problem_declaration, label="planner input")
    if not nonce or any(character not in "0123456789abcdef" for character in nonce):
        _fail("invalid_authoring_planner_observation", "planner nonce is invalid")
    canonical_modules = tuple(
        sorted(dict.fromkeys(validate_module_name(module) for module in allowed_modules))
    )
    if input_module not in canonical_modules:
        _fail("authoring_catalog_dependency_invalid", "catalog scope omits the input module")
    module_payload = ",".join(canonical_modules)
    return (
        f"import {NP_HARD_AUTHORING_PLANNER_MODULE}\n"
        f"import {input_module}\n\n"
        f'#hardness_np_hard_authoring_observe "{nonce}" '
        f"{input_problem_declaration} {json.dumps(module_payload, ensure_ascii=True)}\n"
    )


class NPHardAuthoringPlannerV2:
    def __init__(
        self,
        *,
        root: Path,
        input_module: str,
        input_problem_declaration: str,
        output_dir: Path,
        attempt_budget: int = 4,
        timeout_seconds: int = 60,
        max_output_tokens: int = 3000,
        lean_timeout_seconds: int = 600,
    ):
        self.root = root.resolve()
        self.input_module = validate_module_name(input_module)
        self.input_problem_declaration = validate_declaration_name(
            input_problem_declaration, label="planner input"
        )
        self.output_dir = output_dir.resolve()
        self.attempt_budget = attempt_budget
        self.timeout_seconds = timeout_seconds
        self.max_output_tokens = max_output_tokens
        self.lean_timeout_seconds = lean_timeout_seconds

    def plan(self) -> NPHardAuthoringPlanV2:
        self.output_dir.mkdir(parents=True, exist_ok=True)
        nonce = secrets.token_hex(16)
        build = run_command(
            [
                "lake",
                "build",
                NP_HARD_AUTHORING_PLANNER_MODULE,
                self.input_module,
            ],
            cwd=self.root / "Lean",
            timeout_seconds=self.lean_timeout_seconds,
            output_limit=16 * 1024 * 1024,
        )
        if not build.ok:
            _fail(
                "authoring_planner_probe_failed",
                build.stderr or build.stdout or "planner prebuild failed",
            )
        import_modules, import_closure_sha256 = lean_import_closure(
            root=self.root, input_module=self.input_module
        )
        allowed_modules = _catalog_scan_modules(import_modules)
        source = build_np_hard_authoring_observation_source(
            input_module=self.input_module,
            input_problem_declaration=self.input_problem_declaration,
            nonce=nonce,
            allowed_modules=allowed_modules,
        )
        _assert_public(source, label="planner probe source")
        source_path = self.output_dir / "AuthoringPlanProbe.lean"
        source_path.write_text(source, encoding="utf-8")
        probe = run_command(
            ["lake", "env", "lean", str(source_path)],
            cwd=self.root / "Lean",
            timeout_seconds=self.lean_timeout_seconds,
            output_limit=16 * 1024 * 1024,
        )
        if not probe.ok:
            _fail(
                "authoring_planner_probe_failed",
                probe.stderr or probe.stdout or "planner observation failed",
            )
        observation = parse_np_hard_authoring_observation(
            stdout=probe.stdout,
            stderr=probe.stderr,
            nonce=nonce,
            input_module=self.input_module,
            input_declaration=self.input_problem_declaration,
            import_modules=import_modules,
            import_closure_sha256=import_closure_sha256,
            toolchain=(self.root / "Lean" / "lean-toolchain")
            .read_text(encoding="utf-8")
            .strip(),
            lake_manifest_sha256=_tagged_file_hash(
                self.root / "Lean" / "lake-manifest.json"
            ),
        )
        plan = plan_np_hard_authoring_from_observation(
            root=self.root,
            input_module=self.input_module,
            input_problem_declaration=self.input_problem_declaration,
            observation=observation,
            commands=(build, probe),
            attempt_budget=self.attempt_budget,
            timeout_seconds=self.timeout_seconds,
            max_output_tokens=self.max_output_tokens,
        )
        (self.output_dir / "observation.json").write_text(
            json.dumps(observation.to_dict(), ensure_ascii=True, indent=2, sort_keys=True)
            + "\n",
            encoding="utf-8",
        )
        (self.output_dir / "plan.json").write_text(
            json.dumps(plan.to_dict(), ensure_ascii=True, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return plan
