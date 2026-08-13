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
import re
import secrets
from dataclasses import asdict, dataclass, replace
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
    _NP_HARD_CERTIFIED_REDUCTION_HEAD_V2,
    _exact_certified_reduction_endpoints_v2,
    _exact_gadget_packet_endpoints_v2,
    _exact_tmkarp_reduction_endpoints_v2,
    _successor_only_observer_chain_payload_v2,
    build_np_hard_authoring_task_v2,
)


NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V3 = (
    "hardness_np_hard_authoring_observation_v3"
)
# Compatibility export for callers that imported the pre-H-J constant name.
NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1 = NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V3
NP_HARD_AUTHORING_PLAN_SCHEMA_V2 = "hardness_np_hard_authoring_plan_v2"
NP_HARD_AUTHORING_PLANNER_MODULE = (
    "ComplexityReduction.Agent.Hardness.AuthoringPlanner"
)
_MARKER = "HARDNESS_NP_HARD_PLAN"
_DECLARATION_TYPE_MARKER = "HARDNESS_NP_HARD_DECL_TYPE"
_DECLARATION_TYPE_SCHEMA_V1 = (
    "hardness_np_hard_declaration_type_observation_v1"
)
_HASH_PREFIX = "sha256:"
_TYPED_CAPABILITY_ROW_FIELD_COUNT = 11
_TYPED_CAPABILITY_KINDS = frozenset(
    {
        "forward_representation_adapter",
        "forward_tmkarp_admission",
        "forward_successor_only_tmkarp_admission",
        "forward_certified_successor",
        "forward_program_indexed_admission",
        "forward_gadget_indexed_admission",
    }
)
_TYPED_CAPABILITY_AUTHORITIES = {
    "forward_representation_adapter": "lean_exact_type_defeq",
    "forward_tmkarp_admission": "lean_exact_tmkarp_public_source",
    "forward_successor_only_tmkarp_admission": (
        "lean_exact_successor_only_tmkarp_shared_source"
    ),
    "forward_certified_successor": "lean_registry_exact_certified_successor",
    "forward_program_indexed_admission": (
        "lean_exact_program_indexed_public_packet"
    ),
    "forward_gadget_indexed_admission": (
        "lean_exact_gadget_indexed_shared_packet"
    ),
}
_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.AuthoringSources"
)
_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources"
)
_PROGRAM_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources"
)
_GADGET_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources"
)
_BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold"
)
_BOOLEAN_CSP_NAE3_PUBLIC_SUPPORT_MODULES = (
    "ComplexityReduction.Presentation.NAEThreeSAT",
    "ComplexityReduction.Presentation.NAEThreeSATTM",
    "ComplexityReduction.Presentation.SatisfiabilityTM",
    "ComplexityReduction.Domain.BooleanCSP.CSPInstance",
    "ComplexityReduction.Legacy.ComplexityReduction.SAT.Literal",
    "ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SAT",
    "ComplexityReduction.Legacy.ComplexityReduction.CSP.Formula",
    "ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic",
    "ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations",
    "ComplexityReduction.Program.List",
    "ComplexityReduction.Program.EncodingTransport",
    "ComplexityReduction.Presentation.FiniteDomainCSPTable",
)
_BOOLEAN_CSP_NAE3_CONSTRUCTION_PRIMITIVES = (
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".threeSATToNAEThreeSATIngress.executable",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraint",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literalKey",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".complementLiteral",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".referenceExecutableFromClauseGadget",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".executableFromReference",
)
_BOOLEAN_CSP_NAE3_DIRECT_TM_PRIMITIVES = (
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".threeSATToNAEThreeSATIngress.executableDirectTM",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".clausePayload_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".clauseFirst_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".clauseSecond_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".clauseThird_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".complementLiteral_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literalKey_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literalKeyAfter_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".complementLiteralAfter_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".complementKeyAfter_tmPolyTime",
    "ComplexityReduction.TMPolyTimeMap.list_nil",
    "ComplexityReduction.TMPolyTimeMap.list_singleton_of",
    "ComplexityReduction.TMPolyTimeMap.list_cons_of",
    "ComplexityReduction.TMPolyTimeMap.transport_output",
    "ComplexityReduction.TMPolyTimeMap.comp",
    "ComplexityReduction.TMPolyTimeMap.prod_mk",
    "ComplexityReduction.TMPolyTimeMap.fst",
    "ComplexityReduction.TMPolyTimeMap.snd",
    "ComplexityReduction.TMPolyTimeMap.list_map",
    "ComplexityReduction.Program.listFlatten_tmPolyTime",
    "ComplexityReduction.Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".constraintPayload_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraintCode_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".referenceExecutableFromClauseGadget_tmPolyTime",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".executableFromReference_tmPolyTime",
)
_BOOLEAN_CSP_NAE3_SEMANTIC_PRIMITIVES = (
    "ComplexityReduction.SAT.Literal.eval",
    "ComplexityReduction.SAT.Literal.positive",
    "ComplexityReduction.SAT.Literal.negative",
    "ComplexityReduction.SAT.Literal.eval_positive",
    "ComplexityReduction.SAT.Literal.eval_negative",
    "ComplexityReduction.SAT.Clause.negate",
    "ComplexityReduction.SAT.Clause.negate_eval_true_iff",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".complementLiteral_eval",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literalAssignment",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literalAssignment_literalKey",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".positiveKeyAssignment",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literal_eval_positiveKeyAssignment",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".literal_eval_positiveKeyAssignment_of_complement",
    "ComplexityReduction.CSP.StandardRelations.tripleTuple",
    "ComplexityReduction.CSP.StandardRelations.notAllEqual3Rel_holds_triple_iff",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraint_satisfies_iff",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".bool_ne_iff_eq_not",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraint_repeat_satisfies_iff",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraint_repeat_first_satisfies_iff",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".ternaryConstraint_repeat_second_satisfies_iff",
    "ComplexityReduction.NAEThreeSAT.Clause.Satisfies",
    "ComplexityReduction.NAEThreeSAT.Formula.Satisfies",
    "ComplexityReduction.NAEThreeSAT.Formula.Satisfiable",
    "ComplexityReduction.NAEThreeSAT.Formula.satisfies_cons",
    "ComplexityReduction.NAEThreeSAT.Formula.satisfies_append",
    "ComplexityReduction.CSP.Constraint.assignmentTuple",
    "ComplexityReduction.CSP.Constraint.Satisfies",
    "ComplexityReduction.CSP.Formula.Satisfies",
    "ComplexityReduction.CSP.Formula.Satisfiable",
    "ComplexityReduction.CSP.Formula.satisfies_cons",
    "ComplexityReduction.CSP.Formula.satisfies_append",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim",
    "ComplexityReduction.CSP.BoolRel.Holds",
    "ComplexityReduction.CSP.BoolRel.holds_ofPredicate_iff",
    "ComplexityReduction.Domain.BooleanCSP.cspOf_accepts",
    "ComplexityReduction.Domain.ThreeSATToNAEThreeSAT.literalKey_injective",
    "ComplexityReduction.CSP.StandardRelations.notAllEqualRel",
    "ComplexityReduction.CSP.StandardRelations.notAllEqual3Rel",
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE
    + ".threeSATToNAEThreeSATIngress.executableCorrect",
)
_BOOLEAN_CSP_NAE3_SCAFFOLD_PRIMITIVES = (
    *_BOOLEAN_CSP_NAE3_CONSTRUCTION_PRIMITIVES,
    *_BOOLEAN_CSP_NAE3_DIRECT_TM_PRIMITIVES,
    *_BOOLEAN_CSP_NAE3_SEMANTIC_PRIMITIVES,
)

_BOOLEAN_CSP_NAE4_AUTHORING_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPNAE4ReductionScaffold"
)
_BOOLEAN_CSP_NAE5_AUTHORING_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPNAE5ReductionScaffold"
)

_BOOLEAN_CSP_SHARED_DIRECT_TM_PRIMITIVES = (
    "ComplexityReduction.TMPolyTimeMap.list_nil",
    "ComplexityReduction.TMPolyTimeMap.list_singleton_of",
    "ComplexityReduction.TMPolyTimeMap.list_cons_of",
    "ComplexityReduction.TMPolyTimeMap.transport_output",
    "ComplexityReduction.TMPolyTimeMap.comp",
    "ComplexityReduction.TMPolyTimeMap.prod_mk",
    "ComplexityReduction.TMPolyTimeMap.fst",
    "ComplexityReduction.TMPolyTimeMap.snd",
    "ComplexityReduction.TMPolyTimeMap.list_map",
    "ComplexityReduction.Program.listFlatten_tmPolyTime",
    "ComplexityReduction.Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code",
)

_BOOLEAN_CSP_SHARED_SEMANTIC_HEAD_PRIMITIVES = (
    "ComplexityReduction.SAT.Literal.eval",
    "ComplexityReduction.SAT.Literal.positive",
    "ComplexityReduction.SAT.Literal.negative",
    "ComplexityReduction.SAT.Literal.eval_positive",
    "ComplexityReduction.SAT.Literal.eval_negative",
    "ComplexityReduction.SAT.Clause.negate",
    "ComplexityReduction.SAT.Clause.negate_eval_true_iff",
)

_BOOLEAN_CSP_SHARED_SEMANTIC_TAIL_PRIMITIVES = (
    "ComplexityReduction.NAEThreeSAT.Clause.Satisfies",
    "ComplexityReduction.NAEThreeSAT.Formula.Satisfies",
    "ComplexityReduction.NAEThreeSAT.Formula.Satisfiable",
    "ComplexityReduction.NAEThreeSAT.Formula.satisfies_cons",
    "ComplexityReduction.NAEThreeSAT.Formula.satisfies_append",
    "ComplexityReduction.CSP.Constraint.assignmentTuple",
    "ComplexityReduction.CSP.Constraint.Satisfies",
    "ComplexityReduction.CSP.Formula.Satisfies",
    "ComplexityReduction.CSP.Formula.Satisfiable",
    "ComplexityReduction.CSP.Formula.satisfies_cons",
    "ComplexityReduction.CSP.Formula.satisfies_append",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro",
    "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim",
    "ComplexityReduction.CSP.BoolRel.Holds",
    "ComplexityReduction.CSP.BoolRel.holds_ofPredicate_iff",
    "ComplexityReduction.Domain.BooleanCSP.cspOf_accepts",
    "ComplexityReduction.Domain.ThreeSATToNAEThreeSAT.literalKey_injective",
    "ComplexityReduction.CSP.StandardRelations.notAllEqualRel",
)


def _nae_k_scaffold_primitives(
    scaffold_module: str,
    *,
    constraint_constructor: str,
    constraint_code_tm: str,
    satisfies_lemma: str,
    clause_constructor: str,
    clause_satisfies_lemma: str,
    repeat_lemma: str,
    tuple_builder: str,
    relation_holds_lemma: str,
    relation_name: str,
) -> dict[str, tuple[str, ...]]:
    """Build the three primitive layers for one positive NAE-k scaffold."""

    construction = (
        f"{scaffold_module}.threeSATToNAEThreeSATIngress.executable",
        f"{scaffold_module}.{constraint_constructor}",
        f"{scaffold_module}.{clause_constructor}",
        f"{scaffold_module}.literalKey",
        f"{scaffold_module}.complementLiteral",
        f"{scaffold_module}.referenceExecutableFromClauseGadget",
        f"{scaffold_module}.executableFromReference",
    )
    direct_tm = (
        f"{scaffold_module}.threeSATToNAEThreeSATIngress.executableDirectTM",
        f"{scaffold_module}.clausePayload_tmPolyTime",
        f"{scaffold_module}.clauseFirst_tmPolyTime",
        f"{scaffold_module}.clauseSecond_tmPolyTime",
        f"{scaffold_module}.clauseThird_tmPolyTime",
        f"{scaffold_module}.complementLiteral_tmPolyTime",
        f"{scaffold_module}.literalKey_tmPolyTime",
        f"{scaffold_module}.literalKeyAfter_tmPolyTime",
        f"{scaffold_module}.complementLiteralAfter_tmPolyTime",
        f"{scaffold_module}.complementKeyAfter_tmPolyTime",
        *_BOOLEAN_CSP_SHARED_DIRECT_TM_PRIMITIVES,
        f"{scaffold_module}.constraintPayload_tmPolyTime",
        f"{scaffold_module}.{constraint_code_tm}",
        f"{scaffold_module}.referenceExecutableFromClauseGadget_tmPolyTime",
        f"{scaffold_module}.executableFromReference_tmPolyTime",
    )
    semantic = (
        *_BOOLEAN_CSP_SHARED_SEMANTIC_HEAD_PRIMITIVES,
        f"{scaffold_module}.complementLiteral_eval",
        f"{scaffold_module}.literalAssignment",
        f"{scaffold_module}.literalAssignment_literalKey",
        f"{scaffold_module}.positiveKeyAssignment",
        f"{scaffold_module}.literal_eval_positiveKeyAssignment",
        f"{scaffold_module}.literal_eval_positiveKeyAssignment_of_complement",
        tuple_builder,
        relation_holds_lemma,
        f"{scaffold_module}.{satisfies_lemma}",
        f"{scaffold_module}.{clause_satisfies_lemma}",
        f"{scaffold_module}.bool_ne_iff_eq_not",
        f"{scaffold_module}.{repeat_lemma}",
        *_BOOLEAN_CSP_SHARED_SEMANTIC_TAIL_PRIMITIVES,
        relation_name,
        f"{scaffold_module}.threeSATToNAEThreeSATIngress.executableCorrect",
    )
    return {
        "construction": construction,
        "direct_tm": direct_tm,
        "semantic": semantic,
    }


_BOOLEAN_CSP_NAE4_SCAFFOLD_LAYERS = _nae_k_scaffold_primitives(
    _BOOLEAN_CSP_NAE4_AUTHORING_SCAFFOLD_MODULE,
    constraint_constructor="quaternaryConstraint",
    constraint_code_tm="quaternaryConstraintCode_tmPolyTime",
    satisfies_lemma="quaternaryConstraint_satisfies_iff",
    clause_constructor="clauseConstraint",
    clause_satisfies_lemma="clauseConstraint_satisfies_iff",
    repeat_lemma="quaternaryConstraint_repeat_satisfies_iff",
    tuple_builder="ComplexityReduction.CSP.StandardRelations.quadTuple",
    relation_holds_lemma=(
        "ComplexityReduction.CSP.StandardRelations.notAllEqual4Rel_holds_quad_iff"
    ),
    relation_name="ComplexityReduction.CSP.StandardRelations.notAllEqualRel",
)

_BOOLEAN_CSP_NAE5_SCAFFOLD_LAYERS = _nae_k_scaffold_primitives(
    _BOOLEAN_CSP_NAE5_AUTHORING_SCAFFOLD_MODULE,
    constraint_constructor="pentaryConstraint",
    constraint_code_tm="pentaryConstraintCode_tmPolyTime",
    satisfies_lemma="pentaryConstraint_satisfies_iff",
    clause_constructor="clauseConstraint",
    clause_satisfies_lemma="clauseConstraint_satisfies_iff",
    repeat_lemma="pentaryConstraint_repeat_satisfies_iff",
    tuple_builder="ComplexityReduction.CSP.StandardRelations.quintTuple",
    relation_holds_lemma=(
        "ComplexityReduction.CSP.StandardRelations.notAllEqual5Rel_holds_quint_iff"
    ),
    relation_name="ComplexityReduction.CSP.StandardRelations.notAllEqualRel",
)

_BOOLEAN_CSP_SCAFFOLD_LAYERS_BY_MODULE: dict[str, dict[str, tuple[str, ...]]] = {
    _BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE: {
        "construction": _BOOLEAN_CSP_NAE3_CONSTRUCTION_PRIMITIVES,
        "direct_tm": _BOOLEAN_CSP_NAE3_DIRECT_TM_PRIMITIVES,
        "semantic": _BOOLEAN_CSP_NAE3_SEMANTIC_PRIMITIVES,
    },
    _BOOLEAN_CSP_NAE4_AUTHORING_SCAFFOLD_MODULE: _BOOLEAN_CSP_NAE4_SCAFFOLD_LAYERS,
    _BOOLEAN_CSP_NAE5_AUTHORING_SCAFFOLD_MODULE: _BOOLEAN_CSP_NAE5_SCAFFOLD_LAYERS,
}


def _primitive_layers(
    allowed_primitives: tuple[str, ...], *, scaffold_module: str | None
) -> dict[str, tuple[str, ...]]:
    """Partition the immutable declaration surface into four prompt layers."""

    explicit: dict[str, str] = {}
    if scaffold_module is not None:
        layers_by_name = _BOOLEAN_CSP_SCAFFOLD_LAYERS_BY_MODULE[scaffold_module]
        for layer_name in ("construction", "direct_tm", "semantic"):
            explicit.update(
                (primitive, layer_name)
                for primitive in layers_by_name[layer_name]
            )
    layers: dict[str, list[str]] = {
        "core": [],
        "construction": [],
        "direct_tm": [],
        "semantic": [],
    }
    for primitive in allowed_primitives:
        layer = explicit.get(primitive)
        lowered = primitive.lower()
        if layer is None and any(
            token in lowered
            for token in ("semantic", "satisfies", "satisfiable", ".eval", "correct")
        ):
            layer = "semantic"
        if layer is None and any(
            token in lowered
            for token in ("tmpolytime", "directtm", "direct_tm", "transport_output")
        ):
            layer = "direct_tm"
        if layer is None and any(
            token in lowered
            for token in ("executable", "gadget", "constraint", "literal")
        ):
            layer = "construction"
        layers[layer or "core"].append(primitive)
    return {name: tuple(items) for name, items in layers.items()}
_TYPED_CAPABILITY_REQUIRED_WITNESS_TERMS = (
    "PolyProg.const",
    "PolyProg.id",
    "false",
)
_TYPED_CAPABILITY_PAIR_WITNESS_TERMS = ("PolyProg.pair", ").pair", ".pair (")
_TYPED_CAPABILITY_FORBIDDEN_WITNESS_TERMS = ("PolyProg.snd",)
_FORBIDDEN_TEXT = (
    '"case_id"',
    '"expected"',
    '"gold"',
    '"hidden_gold"',
    ".gold.",
    ".oracles.",
    ".hiddentargets.",
)
_SOURCE_CONTEXT_STOP_WORDS = {
    "agent",
    "complexity",
    "core",
    "domain",
    "hardness",
    "input",
    "karp",
    "legacy",
    "presentation",
    "problem",
    "problems",
    "reduction",
    "route",
    "routes",
    "runtime",
    "source",
    "structured",
    "target",
    "the",
    "to",
}


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


def _identifier_tokens(value: str) -> set[str]:
    expanded = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return {
        token
        for token in re.findall(r"[A-Za-z0-9]+", expanded.lower())
        if len(token) >= 3 and token not in _SOURCE_CONTEXT_STOP_WORDS
    }


def _canonical_lean_text(value: str) -> str:
    return " ".join(value.split())


def _whole_reduction_authoring_seed_modules(
    *, root: Path, input_module: str, task_class: str
) -> tuple[str, ...]:
    """Select small public reference stages from the exact input definition."""

    if task_class != "whole_reduction_synthesis":
        return ()
    input_source = module_file(root.resolve() / "Lean", input_module).read_text(
        encoding="utf-8"
    )
    if "Domain.BooleanCSP" not in input_source:
        return ()
    if "StandardRelations.notAllEqual3Rel" in input_source:
        return (_BOOLEAN_CSP_NAE3_AUTHORING_SCAFFOLD_MODULE,)
    if "StandardRelations.notAllEqualRel 4" in input_source:
        return (_BOOLEAN_CSP_NAE4_AUTHORING_SCAFFOLD_MODULE,)
    if "StandardRelations.notAllEqualRel 5" in input_source:
        return (_BOOLEAN_CSP_NAE5_AUTHORING_SCAFFOLD_MODULE,)
    return ()


def _relevant_direct_public_sources(
    *,
    root: Path,
    source_files: Iterable[Path],
    query_values: Iterable[str],
    max_depth: int = 1,
    max_files: int = 2,
) -> tuple[Path, ...]:
    """Select bounded, content-addressed public context from relevant imports."""

    query_tokens = set().union(*(_identifier_tokens(value) for value in query_values))
    if max_depth < 1 or max_files < 1:
        return ()
    known = set(source_files)
    frontier = tuple(sorted(known, key=str))
    selected: list[Path] = []
    per_depth_limit = max(1, (max_files + max_depth - 1) // max_depth)
    for _ in range(max_depth):
        ranked: dict[Path, tuple[int, str]] = {}
        for source_file in frontier:
            source_lines = source_file.read_text(encoding="utf-8").splitlines()
            local_tokens = query_tokens | _identifier_tokens(
                "\n".join(
                    line
                    for line in source_lines
                    if not line.strip().startswith("import ")
                )
            )
            for line in source_lines:
                stripped = line.strip()
                if not stripped.startswith("import "):
                    continue
                imported = stripped.removeprefix("import ").strip()
                if not imported or any(
                    token in imported.lower() for token in _FORBIDDEN_TEXT
                ):
                    continue
                score = len(local_tokens & _identifier_tokens(imported))
                input_owned = (
                    "Benchmark" in source_file.parts
                    and "Inputs" in source_file.parts
                )
                if score <= 0 and not input_owned:
                    continue
                if input_owned:
                    score += 3
                try:
                    imported_file = module_file(root / "Lean", imported).resolve()
                    imported_file.relative_to(root)
                except (ValueError, OSError):
                    continue
                if imported_file.is_file() and imported_file not in known:
                    ranked[imported_file] = max(
                        ranked.get(imported_file, (0, imported)),
                        (score, imported),
                    )
        additions = tuple(
            path
            for path, _ in sorted(
                ranked.items(), key=lambda item: (-item[1][0], item[1][1])
            )[: min(per_depth_limit, max_files - len(selected))]
        )
        if not additions:
            break
        selected.extend(additions)
        known.update(additions)
        frontier = additions
        if len(selected) >= max_files:
            break
    return tuple(selected)


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
class PlannerTypedCapabilityV3:
    capability_kind: str
    capability_id: str
    source: str
    target: str
    source_node: str
    target_node: str
    witness: str
    exact_type: str
    module: str
    authority: str

    @property
    def observation_key(self) -> tuple[str, str, str, str]:
        return (
            self.capability_kind,
            self.source_node,
            self.target_node,
            self.capability_id,
        )

    def to_dict(self) -> dict[str, str]:
        return {
            "capability_kind": self.capability_kind,
            "id": self.capability_id,
            "source": self.source,
            "target": self.target,
            "source_node": self.source_node,
            "target_node": self.target_node,
            "witness": self.witness,
            "exact_type": self.exact_type,
            "module": self.module,
            "authority": self.authority,
        }


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
    typed_capabilities: tuple[PlannerTypedCapabilityV3, ...]
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
            "typed_capabilities": [
                item.to_dict() for item in self.typed_capabilities
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
    typed_capabilities: list[PlannerTypedCapabilityV3] = []
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
            "typed_capability": _TYPED_CAPABILITY_ROW_FIELD_COUNT,
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
        elif kind == "typed_capability":
            typed_capabilities.append(PlannerTypedCapabilityV3(*fields[:-1]))
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
    if len({item.capability_id for item in typed_capabilities}) != len(
        typed_capabilities
    ):
        _fail(
            "invalid_authoring_planner_observation",
            "duplicate typed capability identifier",
        )
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
    problems_by_name = {problem.declaration: problem for problem in problems}
    for capability in typed_capabilities:
        if capability.capability_kind not in _TYPED_CAPABILITY_KINDS:
            _fail(
                "invalid_authoring_planner_observation",
                f"unsupported typed capability kind: {capability.capability_kind}",
            )
        if capability.authority != _TYPED_CAPABILITY_AUTHORITIES[
            capability.capability_kind
        ]:
            _fail(
                "invalid_authoring_planner_observation",
                "typed capability authority differs from its closed Lean observation kind",
            )
        if not capability.capability_id.strip() or len(capability.capability_id) > 12_000:
            _fail(
                "invalid_authoring_planner_observation",
                "typed capability identifier is invalid",
            )
        source = problems_by_name.get(capability.source)
        target = problems_by_name.get(capability.target)
        if source is None or target is None:
            _fail(
                "candidate_wrong_endpoint",
                "typed capability endpoint escaped the exact problem set",
            )
        if capability.capability_kind == "forward_representation_adapter":
            if source.module not in import_modules or target.module not in import_modules:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "representation adapter endpoint escaped the input import closure",
                )
        elif target.module not in import_modules:
            dependent_successors = tuple(
                successor
                for successor in typed_capabilities
                if capability.capability_kind
                in {
                    "forward_tmkarp_admission",
                    "forward_successor_only_tmkarp_admission",
                }
                and successor.capability_kind
                in {
                    "forward_certified_successor",
                    "forward_program_indexed_admission",
                }
                and successor.source_node == capability.target_node
                and successor.target_node == input_node
            )
            if len(dependent_successors) != 1:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "typed forward capability target escaped the input import closure without one exact successor",
                )
        if (
            capability.source_node != source.endpoint_node
            or capability.target_node != target.endpoint_node
        ):
            _fail(
                "candidate_wrong_endpoint",
                "typed capability endpoint node does not match its Lean problem",
            )
        if capability.source_node == capability.target_node:
            _fail(
                "candidate_wrong_direction",
                "typed capability collapsed source and target endpoint nodes",
            )
        if not capability.witness.strip() or not capability.exact_type.strip():
            _fail(
                "invalid_authoring_planner_observation",
                "typed capability lacks its exact public witness or type",
            )
        if capability.capability_kind == "forward_representation_adapter":
            if capability.module != target.module:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "representation adapter owner differs from its target problem module",
                )
            if "PolyProg" not in capability.exact_type:
                _fail(
                    "invalid_authoring_planner_observation",
                    "forward representation adapter is not an exact PolyProg",
                )
            source_representation_index = capability.exact_type.find(
                source.rendered_representation
            )
            target_representation_index = capability.exact_type.rfind(
                target.rendered_representation
            )
            if (
                source_representation_index < 0
                or target_representation_index < 0
                or source_representation_index >= target_representation_index
            ):
                _fail(
                    "candidate_wrong_direction",
                    "forward representation adapter exact type reverses its representations",
                )
            if any(
                token not in capability.witness
                for token in _TYPED_CAPABILITY_REQUIRED_WITNESS_TERMS
            ) or not any(
                token in capability.witness
                for token in _TYPED_CAPABILITY_PAIR_WITNESS_TERMS
            ) or any(
                token in capability.witness
                for token in _TYPED_CAPABILITY_FORBIDDEN_WITNESS_TERMS
            ):
                _fail(
                    "candidate_wrong_direction",
                    "forward representation adapter witness has the wrong structural direction",
                )
        elif capability.capability_kind in {
            "forward_tmkarp_admission",
            "forward_successor_only_tmkarp_admission",
        }:
            expected_module = (
                _TMKARP_ADMISSION_MODULE
                if capability.capability_kind == "forward_tmkarp_admission"
                else _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
            )
            if capability.module != expected_module:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "TMKarp admission witness escaped its closed public source authority",
                )
            try:
                validate_declaration_name(
                    capability.witness, label="typed TMKarp admission witness"
                )
            except ValueError as error:
                _fail("invalid_authoring_planner_observation", str(error))
            if not capability.witness.startswith(capability.module + "."):
                _fail(
                    "authoring_catalog_dependency_stale",
                    "TMKarp admission witness is not owned by its observed public module",
                )
            source_endpoint = (
                source.rendered_endpoint + ".toEncodedDecisionProblem"
            )
            target_endpoint = (
                target.rendered_endpoint + ".toEncodedDecisionProblem"
            )
            if _exact_tmkarp_reduction_endpoints_v2(
                capability.exact_type
            ) != (source_endpoint, target_endpoint):
                _fail(
                    "candidate_wrong_direction",
                    "TMKarp admission exact type reverses or substitutes its endpoints",
                )
        elif capability.capability_kind == "forward_program_indexed_admission":
            if capability.module != _PROGRAM_INDEXED_ADMISSION_MODULE:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "program-indexed packet escaped the closed public source module",
                )
            try:
                validate_declaration_name(
                    capability.witness,
                    label="typed program-indexed admission witness",
                )
            except ValueError as error:
                _fail("invalid_authoring_planner_observation", str(error))
            if not capability.witness.startswith(capability.module + "."):
                _fail(
                    "authoring_catalog_dependency_stale",
                    "program-indexed packet is not owned by its observed public module",
                )
            if "ProgramIndexedAdmissionPacket" not in capability.exact_type:
                _fail(
                    "invalid_authoring_planner_observation",
                    "program-indexed admission lacks its exact packet type",
                )
            source_index = capability.exact_type.find(source.rendered_endpoint)
            target_index = capability.exact_type.rfind(target.rendered_endpoint)
            if (
                source_index < 0
                or target_index < 0
                or source_index >= target_index
            ):
                _fail(
                    "candidate_wrong_direction",
                    "program-indexed packet exact type reverses or substitutes its endpoints",
                )
        elif capability.capability_kind == "forward_gadget_indexed_admission":
            if capability.module != _GADGET_INDEXED_ADMISSION_MODULE:
                _fail(
                    "authoring_catalog_dependency_stale",
                    "gadget-indexed packet escaped the closed public source module",
                )
            try:
                validate_declaration_name(
                    capability.witness,
                    label="typed gadget-indexed admission witness",
                )
            except ValueError as error:
                _fail("invalid_authoring_planner_observation", str(error))
            if not capability.witness.startswith(capability.module + "."):
                _fail(
                    "authoring_catalog_dependency_stale",
                    "gadget-indexed packet is not owned by its observed public module",
                )
            packet_endpoints = _exact_gadget_packet_endpoints_v2(
                capability.exact_type
            )
            reference_matches = tuple(
                problem
                for problem in problems
                if problem.declaration not in {source.declaration, target.declaration}
                and packet_endpoints
                == (
                    source.rendered_endpoint,
                    problem.rendered_endpoint,
                    target.rendered_endpoint,
                )
            )
            if len(reference_matches) != 1:
                _fail(
                    "candidate_wrong_direction",
                    "gadget-indexed packet does not bind one ordered source/reference/target triple",
                )
        else:
            try:
                validate_module_name(capability.module)
                validate_declaration_name(
                    capability.witness, label="typed certified successor witness"
                )
            except ValueError as error:
                _fail("invalid_authoring_planner_observation", str(error))
            if _exact_certified_reduction_endpoints_v2(
                capability.exact_type
            ) is None:
                _fail(
                    "invalid_authoring_planner_observation",
                    "forward certified successor lacks an exact CertifiedReduction type",
                )
            matching_registered_edges = tuple(
                reduction
                for reduction in reductions
                if reduction.direction == "forward"
                and reduction.role not in {"ingress", "finalComposition"}
                and reduction.source_node == capability.source_node
                and reduction.target_node == capability.target_node
                and reduction.module == capability.module
                and _canonical_lean_text(reduction.exact_type)
                == _canonical_lean_text(capability.exact_type)
                and capability.witness
                in {reduction.declaration, reduction.lean_term}
            )
            if len(matching_registered_edges) != 1:
                _fail(
                    "invalid_authoring_planner_observation",
                    "certified successor is not one unique forward exportValidated registry edge",
                )
        for label, value in {
            "typed capability ID": capability.capability_id,
            "typed capability witness": capability.witness,
            "typed capability exact type": capability.exact_type,
            "typed capability module": capability.module,
        }.items():
            _assert_public(value, label=label)
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
            capability_name = getattr(
                capability,
                "declaration",
                getattr(capability, "capability_id", "unknown-capability"),
            )
            _fail(
                "authoring_catalog_dependency_stale",
                f"closure capability escaped its import graph: {capability_name}",
            )
    for capability in typed_capabilities:
        if (
            capability.capability_kind == "forward_representation_adapter"
            and capability.module not in closure_set
        ):
            _fail(
                "authoring_catalog_dependency_stale",
                "representation adapter escaped its input import graph",
            )
        if (
            capability.capability_kind == "forward_tmkarp_admission"
            and capability.module != _TMKARP_ADMISSION_MODULE
        ):
            _fail(
                "authoring_catalog_dependency_stale",
                "TMKarp admission escaped the closed public source module",
            )
        if (
            capability.capability_kind
            == "forward_successor_only_tmkarp_admission"
            and capability.module != _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
        ):
            _fail(
                "authoring_catalog_dependency_stale",
                "successor-only TMKarp admission escaped its closed public source module",
            )
        if (
            capability.capability_kind == "forward_program_indexed_admission"
            and capability.module != _PROGRAM_INDEXED_ADMISSION_MODULE
        ):
            _fail(
                "authoring_catalog_dependency_stale",
                "program-indexed packet escaped the closed public source module",
            )
        if (
            capability.capability_kind == "forward_gadget_indexed_admission"
            and capability.module != _GADGET_INDEXED_ADMISSION_MODULE
        ):
            _fail(
                "authoring_catalog_dependency_stale",
                "gadget-indexed packet escaped the closed public source module",
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
        typed_capabilities=tuple(
            sorted(typed_capabilities, key=lambda item: item.observation_key)
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
    terminal_node_id: str | None = None
    final_program_node_id: str | None = None
    final_node_id: str | None = None
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
                "terminal_node_id": self.terminal_node_id,
                "final_program_node_id": self.final_program_node_id,
                "final_node_id": self.final_node_id,
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
            "terminal_node_id": self.terminal_node_id,
            "final_program_node_id": self.final_program_node_id,
            "final_node_id": self.final_node_id,
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
    if task_class == "whole_reduction_synthesis":
        return (
            {
                "id": "reduction-executable",
                "reason": "openReductionConstruction",
                "depends_on": [],
            },
            {
                "id": "direct-tm",
                "reason": "directTMPolynomialTime",
                "depends_on": ["reduction-executable"],
            },
            {
                "id": "reduction-primitive",
                "reason": "directTMPrimitive",
                "depends_on": ["reduction-executable", "direct-tm"],
            },
            {
                "id": "poly-program",
                "reason": "directTMProgram",
                "depends_on": ["reduction-primitive"],
            },
            {
                "id": "program-run-coherence",
                "reason": "executableRelationContract",
                "depends_on": ["poly-program", "reduction-executable"],
            },
            {
                "id": "semantic-forward",
                "reason": "semanticForwardImplication",
                "depends_on": ["poly-program", "program-run-coherence"],
            },
            {
                "id": "semantic-reverse",
                "reason": "semanticReverseImplication",
                "depends_on": ["poly-program", "program-run-coherence"],
            },
            {
                "id": "semantic-iff",
                "reason": "semanticIff",
                "depends_on": ["semantic-forward", "semantic-reverse"],
            },
        )
    if task_class == "typed_capability_dag":
        return (
            {
                "id": "representation-adapter",
                "reason": "representationAdapter",
                "depends_on": [],
            },
            {
                "id": "semantic-forward",
                "reason": "semanticForwardImplication",
                "depends_on": ["representation-adapter"],
            },
            {
                "id": "semantic-reverse",
                "reason": "semanticReverseImplication",
                "depends_on": ["representation-adapter"],
            },
            {
                "id": "semantic-iff",
                "reason": "semanticIff",
                "depends_on": ["semantic-forward", "semantic-reverse"],
            },
        )
    if task_class == "typed_tmkarp_admission_dag":
        return (
            {
                "id": "tmkarp-primitive",
                "reason": "tmKarpPrimitiveAdmission",
                "depends_on": [],
            },
            {
                "id": "tmkarp-program",
                "reason": "tmKarpProgramAssembly",
                "depends_on": ["tmkarp-primitive"],
            },
            {
                "id": "tmkarp-semantic-iff",
                "reason": "tmKarpSemanticIff",
                "depends_on": ["tmkarp-program"],
            },
        )
    if task_class == "typed_tmkarp_dependent_composition_dag":
        return (
            {
                "id": "tmkarp-primitive",
                "reason": "tmKarpPrimitiveAdmission",
                "depends_on": [],
            },
            {
                "id": "tmkarp-program",
                "reason": "tmKarpProgramAssembly",
                "depends_on": ["tmkarp-primitive"],
            },
            {
                "id": "tmkarp-semantic-iff",
                "reason": "tmKarpSemanticIff",
                "depends_on": ["tmkarp-program"],
            },
            {
                "id": "composed-program",
                "reason": "dependentProgramComposition",
                "depends_on": ["tmkarp-program"],
            },
            {
                "id": "composed-semantic-iff",
                "reason": "dependentSemanticComposition",
                "depends_on": ["tmkarp-semantic-iff", "composed-program"],
            },
        )
    if task_class == "typed_program_indexed_admission_dag":
        return (
            {
                "id": "program-executable",
                "reason": "programIndexedExecutable",
                "depends_on": [],
            },
            {
                "id": "program-primitive",
                "reason": "programIndexedPrimitive",
                "depends_on": ["program-executable"],
            },
            {
                "id": "program",
                "reason": "programIndexedProgram",
                "depends_on": ["program-primitive"],
            },
            {
                "id": "program-run-coherence-direct-tm",
                "reason": "programRunCoherenceDirectTM",
                "depends_on": ["program"],
            },
            {
                "id": "program-semantic-iff",
                "reason": "programIndexedSemanticIff",
                "depends_on": ["program-run-coherence-direct-tm"],
            },
        )
    if task_class == "typed_tmkarp_program_indexed_composition_dag":
        return (
            {
                "id": "tmkarp-primitive",
                "reason": "tmKarpPrimitiveAdmission",
                "depends_on": [],
            },
            {
                "id": "tmkarp-program",
                "reason": "tmKarpProgramAssembly",
                "depends_on": ["tmkarp-primitive"],
            },
            {
                "id": "tmkarp-semantic-iff",
                "reason": "tmKarpSemanticIff",
                "depends_on": ["tmkarp-program"],
            },
            {
                "id": "program-executable",
                "reason": "programIndexedExecutable",
                "depends_on": [],
            },
            {
                "id": "program-primitive",
                "reason": "programIndexedPrimitive",
                "depends_on": ["program-executable"],
            },
            {
                "id": "program",
                "reason": "programIndexedProgram",
                "depends_on": ["program-primitive"],
            },
            {
                "id": "program-run-coherence-direct-tm",
                "reason": "programRunCoherenceDirectTM",
                "depends_on": ["program"],
            },
            {
                "id": "program-semantic-iff",
                "reason": "programIndexedSemanticIff",
                "depends_on": ["program-run-coherence-direct-tm"],
            },
            {
                "id": "composed-program",
                "reason": "tmKarpProgramIndexedComposition",
                "depends_on": ["tmkarp-program", "program"],
            },
            {
                "id": "composed-semantic-iff",
                "reason": "tmKarpProgramIndexedSemanticComposition",
                "depends_on": [
                    "tmkarp-semantic-iff",
                    "program-semantic-iff",
                    "composed-program",
                ],
            },
        )
    if task_class == "typed_gadget_indexed_admission_dag":
        return (
            {
                "id": "gadget-reference-audit",
                "reason": "gadgetReferenceAudit",
                "depends_on": [],
            },
            {
                "id": "gadget-normalization-audit",
                "reason": "gadgetNormalizationAudit",
                "depends_on": ["gadget-reference-audit"],
            },
            {
                "id": "gadget-executable",
                "reason": "gadgetExecutable",
                "depends_on": [
                    "gadget-reference-audit",
                    "gadget-normalization-audit",
                ],
            },
            {
                "id": "gadget-parameter-audit",
                "reason": "gadgetParameterAudit",
                "depends_on": ["gadget-executable"],
            },
            {
                "id": "gadget-semantic-forward",
                "reason": "gadgetSemanticForward",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                ],
            },
            {
                "id": "gadget-semantic-reverse",
                "reason": "gadgetSemanticReverse",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                ],
            },
            {
                "id": "gadget-direct-tm",
                "reason": "gadgetDirectTM",
                "depends_on": [
                    "gadget-executable",
                    "gadget-parameter-audit",
                    "gadget-semantic-forward",
                    "gadget-semantic-reverse",
                ],
            },
            {
                "id": "gadget-program",
                "reason": "gadgetProgramAssembly",
                "depends_on": ["gadget-executable", "gadget-direct-tm"],
            },
            {
                "id": "gadget-composed-program",
                "reason": "gadgetProgramComposition",
                "depends_on": ["gadget-program"],
            },
            {
                "id": "gadget-composed-semantic-iff",
                "reason": "gadgetSemanticComposition",
                "depends_on": [
                    "gadget-semantic-forward",
                    "gadget-semantic-reverse",
                    "gadget-program",
                    "gadget-composed-program",
                ],
            },
        )
    if task_class == "typed_exact_edge_construction_dag":
        return (
            {
                "id": "parameter-normalization",
                "reason": "parameterNormalization",
                "depends_on": [],
            },
            {
                "id": "reduction-primitive",
                "reason": "reductionPrimitive",
                "depends_on": ["parameter-normalization"],
            },
            {
                "id": "gadget-definitions",
                "reason": "gadgetDefinitions",
                "depends_on": ["reduction-primitive"],
            },
            {
                "id": "output-wellformed",
                "reason": "outputWellformed",
                "depends_on": [
                    "parameter-normalization",
                    "reduction-primitive",
                    "gadget-definitions",
                ],
            },
            {
                "id": "polynomial-bound",
                "reason": "polynomialBound",
                "depends_on": ["reduction-primitive"],
            },
            {
                "id": "poly-program",
                "reason": "polyProgram",
                "depends_on": ["reduction-primitive", "polynomial-bound"],
            },
            {
                "id": "program-direct-tm-coherence",
                "reason": "programDirectTMCoherence",
                "depends_on": ["poly-program", "reduction-primitive"],
            },
            {
                "id": "semantic-forward",
                "reason": "semanticForwardImplication",
                "depends_on": ["poly-program"],
            },
            {
                "id": "semantic-reverse",
                "reason": "semanticReverseImplication",
                "depends_on": ["poly-program"],
            },
            {
                "id": "semantic-iff",
                "reason": "semanticIff",
                "depends_on": ["semantic-forward", "semantic-reverse"],
            },
            {
                "id": "certified-reduction",
                "reason": "certifiedReduction",
                "depends_on": [
                    "parameter-normalization",
                    "reduction-primitive",
                    "gadget-definitions",
                    "output-wellformed",
                    "polynomial-bound",
                    "poly-program",
                    "program-direct-tm-coherence",
                    "semantic-forward",
                    "semantic-reverse",
                    "semantic-iff",
                ],
            },
        )
    _fail("authoring_plan_unsupported", f"unsupported task class: {task_class}")


def _positive_nae3_whole_reduction_gap_nodes() -> tuple[Mapping[str, Any], ...]:
    """Stage a new NAE3-to-CSP bridge without exposing a final bridge theorem."""

    return (
        {
            "id": "clause-constraint",
            "reason": "newClauseConstraintConstruction",
            "depends_on": [],
        },
        {
            "id": "complement-constraint",
            "reason": "newComplementConstraintConstruction",
            "depends_on": [],
        },
        {
            "id": "clause-gadget",
            "reason": "newClauseGadgetAssembly",
            "depends_on": ["clause-constraint", "complement-constraint"],
        },
        {
            "id": "reference-executable",
            "reason": "referenceExecutableConstruction",
            "depends_on": ["clause-gadget"],
        },
        {
            "id": "reduction-executable",
            "reason": "openReductionConstruction",
            "depends_on": ["reference-executable"],
        },
        {
            "id": "clause-gadget-direct-tm",
            "reason": "clauseGadgetDirectTM",
            "depends_on": ["clause-gadget"],
        },
        {
            "id": "reference-direct-tm",
            "reason": "referenceBridgeDirectTM",
            "depends_on": ["reference-executable", "clause-gadget-direct-tm"],
        },
        {
            "id": "direct-tm",
            "reason": "directTMPolynomialTime",
            "depends_on": ["reduction-executable", "reference-direct-tm"],
        },
        {
            "id": "reduction-primitive",
            "reason": "directTMPrimitive",
            "depends_on": ["reduction-executable", "direct-tm"],
        },
        {
            "id": "poly-program",
            "reason": "directTMProgram",
            "depends_on": ["reduction-primitive"],
        },
        {
            "id": "program-run-coherence",
            "reason": "executableRelationContract",
            "depends_on": ["poly-program", "reduction-executable"],
        },
        {
            "id": "reference-semantic-forward",
            "reason": "referenceSemanticForwardImplication",
            "depends_on": ["clause-gadget", "reference-executable"],
        },
        {
            "id": "reference-semantic-reverse",
            "reason": "referenceSemanticReverseImplication",
            "depends_on": ["clause-gadget", "reference-executable"],
        },
        {
            "id": "semantic-forward",
            "reason": "semanticForwardImplication",
            "depends_on": [
                "reduction-executable",
                "program-run-coherence",
                "reference-semantic-forward",
            ],
        },
        {
            "id": "semantic-reverse",
            "reason": "semanticReverseImplication",
            "depends_on": [
                "reduction-executable",
                "program-run-coherence",
                "reference-semantic-reverse",
            ],
        },
        {
            "id": "semantic-iff",
            "reason": "semanticIff",
            "depends_on": ["semantic-forward", "semantic-reverse"],
        },
    )


def _gadget_reference_problem(
    *,
    capability: PlannerTypedCapabilityV3,
    problems: Mapping[str, PlannerProblemV1],
) -> PlannerProblemV1:
    """Recover the packet's unique middle endpoint from its exact Lean type."""

    source = problems[capability.source]
    target = problems[capability.target]
    source_index = capability.exact_type.find(source.rendered_endpoint)
    target_index = capability.exact_type.rfind(target.rendered_endpoint)
    candidates = tuple(
        problem
        for problem in problems.values()
        if problem.declaration not in {source.declaration, target.declaration}
        and source_index
        < capability.exact_type.find(problem.rendered_endpoint, source_index + 1)
        < target_index
    )
    if source_index < 0 or target_index < 0 or len(candidates) != 1:
        _fail(
            "candidate_wrong_endpoint",
            "gadget packet does not determine one exact reference endpoint",
        )
    return candidates[0]


def _full_capability_dag(
    *,
    task: NPHardAuthoringTaskV2,
    hardness_seed: PlannerHardnessSeedV1,
    hardness_route: tuple[PlannerCertifiedReductionV1, ...],
    existing_programs: tuple[PlannerPolyProgramV1, ...],
    mapping_relation: PlannerMappingRelationV1 | None,
    typed_capability: PlannerTypedCapabilityV3 | None,
    successor_capability: PlannerTypedCapabilityV3 | None,
    program_packet_capability: PlannerTypedCapabilityV3 | None,
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
    typed_capability_node: str | None = None
    typed_capability_binding_node: str | None = None
    if typed_capability is not None:
        if typed_capability.capability_kind == "forward_representation_adapter":
            typed_capability_node = "public-forward-representation-adapter"
            typed_capability_binding_node = task.final_program_node_id
        elif (
            typed_capability.capability_kind
            == "forward_program_indexed_admission"
        ):
            typed_capability_node = "public-forward-program-indexed-packet"
            typed_capability_binding_node = "program-executable"
        elif (
            typed_capability.capability_kind
            == "forward_gadget_indexed_admission"
        ):
            typed_capability_node = "public-forward-gadget-indexed-packet"
            typed_capability_binding_node = "gadget-reference-audit"
        else:
            typed_capability_node = "public-forward-tmkarp-admission"
            typed_capability_binding_node = "tmkarp-primitive"
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id=typed_capability_node,
                capability=typed_capability.capability_kind,
                declaration=typed_capability.witness,
                exact_type=typed_capability.exact_type,
                depends_on=(),
                authority=typed_capability.authority,
            )
        )
    successor_binding_node: str | None = None
    if successor_capability is not None:
        successor_binding_node = "composed-program"
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id="public-forward-certified-successor",
                capability=successor_capability.capability_kind,
                declaration=successor_capability.witness,
                exact_type=successor_capability.exact_type,
                depends_on=(),
                authority=successor_capability.authority,
            )
        )
    program_packet_binding_node: str | None = None
    if program_packet_capability is not None:
        program_packet_binding_node = "program-executable"
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id="public-forward-program-indexed-packet",
                capability=program_packet_capability.capability_kind,
                declaration=program_packet_capability.witness,
                exact_type=program_packet_capability.exact_type,
                depends_on=(),
                authority=program_packet_capability.authority,
            )
        )
    for obligation in task.gap_nodes:
        dependencies = list(obligation.depends_on)
        if obligation.node_id == typed_capability_binding_node:
            if typed_capability_node is not None:
                dependencies.append(typed_capability_node)
        elif (
            obligation.node_id == task.final_program_node_id
            and typed_capability_binding_node is None
        ):
            if previous_existing is not None:
                dependencies.append(previous_existing)
        if obligation.node_id == successor_binding_node:
            dependencies.append("public-forward-certified-successor")
        if obligation.node_id == program_packet_binding_node:
            dependencies.append("public-forward-program-indexed-packet")
        if obligation.capability == "mapping_invariant" and mapping_relation is not None:
            dependencies.append("public-mapping-relation")
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id=obligation.node_id,
                capability=obligation.capability,
                declaration=obligation.declaration,
                exact_type=obligation.exact_type,
                depends_on=tuple(dict.fromkeys(dependencies)),
                authority="model_body_plus_lean_kernel",
            )
        )
    semantic = next(
        node for node in task.gap_nodes if node.node_id == task.terminal_node_id
    )
    semantic_node = semantic.node_id
    semantic_declaration = semantic.declaration
    explicit_capabilities = {node.capability for node in task.gap_nodes}
    if "semantic_forward" not in explicit_capabilities:
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id="semantic-forward-implication",
                capability="semantic_forward_implication",
                declaration=semantic_declaration,
                exact_type=f"forward projection of {semantic.exact_type}",
                depends_on=(semantic_node,),
                authority="lean_iff_projection",
            )
        )
    if "semantic_reverse" not in explicit_capabilities:
        nodes.append(
            PlannerCapabilityNodeV2(
                node_id="semantic-reverse-implication",
                capability="semantic_reverse_implication",
                declaration=semantic_declaration,
                exact_type=f"reverse projection of {semantic.exact_type}",
                depends_on=(semantic_node,),
                authority="lean_iff_projection",
            )
        )
    final_dependencies = [semantic_node, previous_hardness]
    if task.final_program_node_id is not None:
        final_dependencies.append(task.final_program_node_id)
    elif previous_existing is not None:
        final_dependencies.append(previous_existing)
    nodes.extend(
        (
            PlannerCapabilityNodeV2(
                node_id="certified-reduction",
                capability="certified_reduction",
                declaration=task.final_candidate_declaration,
                exact_type=task.final_exact_type,
                depends_on=tuple(dict.fromkeys(final_dependencies)),
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
    direct_typed_capability_sources = {
        capability.source
        for capability in observation.typed_capabilities
        if capability.target_node == target_node
        and capability.source_node != target_node
        and capability.capability_kind
        in {
            "forward_representation_adapter",
            "forward_tmkarp_admission",
            "forward_program_indexed_admission",
            "forward_gadget_indexed_admission",
        }
    }
    successor_capabilities = tuple(
        capability
        for capability in observation.typed_capabilities
        if capability.capability_kind == "forward_certified_successor"
        and capability.target_node == target_node
        and capability.source_node != target_node
    )
    dependent_chains = tuple(
        (admission, successor)
        for successor in successor_capabilities
        for admission in observation.typed_capabilities
        if admission.capability_kind
        in {
            "forward_tmkarp_admission",
            "forward_successor_only_tmkarp_admission",
        }
        and admission.target_node == successor.source_node
        and admission.source_node != successor.target_node
    )
    dependent_capability_sources = {
        admission.source for admission, _ in dependent_chains
    }
    program_packet_capabilities = tuple(
        capability
        for capability in observation.typed_capabilities
        if capability.capability_kind == "forward_program_indexed_admission"
        and capability.target_node == target_node
        and capability.source_node != target_node
    )
    tmkarp_program_packet_chains = tuple(
        (admission, packet)
        for packet in program_packet_capabilities
        for admission in observation.typed_capabilities
        if admission.capability_kind == "forward_tmkarp_admission"
        and admission.target_node == packet.source_node
        and admission.source_node != packet.target_node
    )
    tmkarp_program_packet_sources = {
        admission.source for admission, _ in tmkarp_program_packet_chains
    }
    open_synthesis_sources = {
        seed.problem
        for seed in observation.hardness_seeds
        if seed.problem in problems and problem_node(seed.problem) != target_node
    }
    open_synthesis_nodes = {
        problem_node(source) for source in open_synthesis_sources
    }
    candidate_names = (
        gap_source_names
        | incoming_program_sources
        | direct_typed_capability_sources
        | dependent_capability_sources
        | tmkarp_program_packet_sources
        | open_synthesis_sources
    )
    if not candidate_names:
        return NPHardAuthoringPlanV2(
            status="BLOCKED",
            failure_code="authoring_plan_missing_hardness_seed",
            missing_capabilities=("trusted_np_hard_source_seed",),
            observation=observation,
            task=None,
            final_program_declaration=None,
            capability_dag=(),
            commands=commands,
        )

    # Definitionally equal aliases are one hub. Prefer exact typed evidence,
    # then a declared gap/program name, with a deterministic declaration
    # tie-break only inside one already-equal endpoint node.
    by_endpoint: dict[str, list[str]] = {}
    for name in candidate_names:
        by_endpoint.setdefault(problem_node(name), []).append(name)
    canonical_candidates = tuple(
        min(
            names,
            key=lambda name: (
                name not in direct_typed_capability_sources
                and name not in dependent_capability_sources,
                name not in tmkarp_program_packet_sources,
                name not in gap_source_names,
                name not in incoming_program_sources,
                name not in open_synthesis_sources,
                len(name),
                name,
            ),
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
        typed_matches = tuple(
            sorted(
                (
                    capability
                    for capability in observation.typed_capabilities
                    if capability.source_node == hub_problem.endpoint_node
                    and capability.target_node == target_node
                    and capability.capability_kind
                    in {
                        "forward_representation_adapter",
                    "forward_tmkarp_admission",
                    "forward_program_indexed_admission",
                    "forward_gadget_indexed_admission",
                    }
                ),
                key=lambda item: item.observation_key,
            )
        )
        dependent_matches = tuple(
            sorted(
                (
                    (admission, successor)
                    for admission, successor in dependent_chains
                    if admission.source_node == hub_problem.endpoint_node
                ),
                key=lambda item: (
                    item[0].observation_key,
                    item[1].observation_key,
                ),
            )
        )
        program_packet_matches = tuple(
            sorted(
                (
                    (admission, packet)
                    for admission, packet in tmkarp_program_packet_chains
                    if admission.source_node == hub_problem.endpoint_node
                ),
                key=lambda item: (
                    item[0].observation_key,
                    item[1].observation_key,
                ),
            )
        )
        if (
            len(typed_matches)
            + len(dependent_matches)
            + len(program_packet_matches)
            > 1
        ):
            rejected.append(
                {
                    "hub": hub,
                    "endpoint_node": hub_problem.endpoint_node,
                    "code": "ambiguous_authoring_capability",
                    "missing_capabilities": [
                        "unique_forward_typed_capability"
                    ],
                    "candidate_capability_ids": [
                        item.capability_id for item in typed_matches
                    ]
                    + [
                        f"{admission.capability_id}+{successor.capability_id}"
                        for admission, successor in dependent_matches
                    ]
                    + [
                        f"{admission.capability_id}+{packet.capability_id}"
                        for admission, packet in program_packet_matches
                    ],
                }
            )
            continue
        program_packet_capability = None
        if program_packet_matches:
            typed_capability, program_packet_capability = (
                program_packet_matches[0]
            )
            successor_capability = None
        elif dependent_matches:
            typed_capability, successor_capability = dependent_matches[0]
        else:
            typed_capability = typed_matches[0] if typed_matches else None
            successor_capability = None
        if successor_capability is not None and path is not None:
            rejected.append(
                {
                    "hub": hub,
                    "endpoint_node": hub_problem.endpoint_node,
                    "code": "ambiguous_authoring_capability",
                    "missing_capabilities": [
                        "unique_dependent_composition_route"
                    ],
                    "candidate_capability_ids": [
                        typed_capability.capability_id,
                        successor_capability.capability_id,
                        *[program.declaration for program in path],
                    ],
                }
            )
            continue
        missing: list[str] = []
        if path is not None and len(path) == 1:
            task_class = "semantic_proof"
            selected_programs = path
            risk_rank = 1
        elif path is not None and len(path) >= 2:
            task_class = "program_composition"
            selected_programs = path
            risk_rank = 2
        elif typed_capability is not None:
            task_class = (
                "typed_tmkarp_program_indexed_composition_dag"
                if program_packet_capability is not None
                else (
                    "typed_tmkarp_dependent_composition_dag"
                    if successor_capability is not None
                    else {
                    "forward_representation_adapter": "typed_capability_dag",
                    "forward_tmkarp_admission": "typed_tmkarp_admission_dag",
                    "forward_program_indexed_admission": (
                        "typed_program_indexed_admission_dag"
                    ),
                    "forward_gadget_indexed_admission": (
                        "typed_gadget_indexed_admission_dag"
                    ),
                    }[typed_capability.capability_kind]
                )
            )
            selected_programs = ()
            risk_rank = 3
        elif {"primitive", "executableRelationContract", "semanticProof"}.issubset(
            gap_reasons
        ):
            selected_programs = ()
            closed_synthesis_ready = (
                relation is not None
                and expected_builtins.issubset(builtin_names)
            )
            if closed_synthesis_ready:
                task_class = "program_synthesis"
                risk_rank = 4
            elif hub_problem.endpoint_node in open_synthesis_nodes:
                task_class = "whole_reduction_synthesis"
                risk_rank = 5
            else:
                task_class = "program_synthesis"
                risk_rank = 4
                if relation is None:
                    missing.append("mapping_invariant")
                if not expected_builtins.issubset(builtin_names):
                    missing.append("poly_program_synthesis_primitives")
        elif hub_problem.endpoint_node in open_synthesis_nodes:
            task_class = "whole_reduction_synthesis"
            selected_programs = ()
            risk_rank = 5
        else:
            task_class = "unsupported"
            selected_programs = ()
            risk_rank = 6
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
                "typed_capability": typed_capability,
                "successor_capability": successor_capability,
                "program_packet_capability": program_packet_capability,
                "seed": seed,
                "hardness_route": hardness_route,
                "safety_rank": safety_rank,
                "stable_rank": (*safety_rank, hub_problem.module, hub),
            }
        )
    ranked.sort(key=lambda item: item["stable_rank"])
    ambiguous_rejections = tuple(
        item
        for item in rejected
        if item["code"] == "ambiguous_authoring_capability"
    )
    if ambiguous_rejections:
        return NPHardAuthoringPlanV2(
            status="BLOCKED",
            failure_code="ambiguous_authoring_capability",
            missing_capabilities=tuple(
                sorted(
                    {
                        capability
                        for item in ambiguous_rejections
                        for capability in item["missing_capabilities"]
                    }
                )
            ),
            observation=observation,
            task=None,
            final_program_declaration=None,
            capability_dag=(),
            commands=commands,
            ranked_hubs=tuple(item["hub"] for item in ranked),
            rejected_hubs=tuple(rejected),
        )
    if not ranked:
        ambiguous_capability = any(
            item["code"] == "ambiguous_authoring_capability" for item in rejected
        )
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
            failure_code=(
                "ambiguous_authoring_capability"
                if ambiguous_capability
                else (
                    "wrong_direction_only"
                    if reverse_observed
                    else "authoring_plan_missing_capability"
                )
            ),
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
    if (
        len(equally_best_nodes) > 1
        and ranked[0]["task_class"] != "whole_reduction_synthesis"
    ):
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
    typed_capability = selected["typed_capability"]
    successor_capability = selected["successor_capability"]
    program_packet_capability = selected["program_packet_capability"]
    hardness_seed = selected["seed"]
    hardness_route = selected["hardness_route"]
    direct = selected_programs[0] if task_class == "semantic_proof" else None
    composition_intermediate_problem: PlannerProblemV1 | None = None
    composition_successor_source: str | None = None
    composition_successor_target: str | None = None
    composition_admission_observation: dict[str, str] | None = None
    composition_successor_observation: dict[str, str] | None = None
    if task_class == "whole_reduction_synthesis":
        allowed_primitives = tuple(
            dict.fromkeys(
                (
                    *sorted(builtin.declaration for builtin in observation.builtins),
                    "ComplexityReduction.Program.Primitive.ofTMPolyTime",
                    "ComplexityReduction.Program.PolyProg.atom",
                )
            )
        )
        program_reference = None
        observed_capability_terms = {}
        observed_capability_exact_types = {}
        representation_adapter_exact_type = None
    elif task_class == "program_synthesis":
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
        observed_capability_terms: dict[str, str] = {}
        observed_capability_exact_types: dict[str, str] = {}
        representation_adapter_exact_type = None
    elif task_class == "typed_capability_dag":
        assert typed_capability is not None
        allowed_primitives = tuple(
            sorted(builtin.declaration for builtin in observation.builtins)
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "representation-adapter": typed_capability.witness
        }
        representation_adapter_exact_type = typed_capability.exact_type
        observed_capability_exact_types: dict[str, str] = {}
    elif task_class == "typed_tmkarp_admission_dag":
        assert typed_capability is not None
        allowed_primitives = (
            typed_capability.witness,
            "ComplexityReduction.Program.Primitive.ofTMPolyTime",
            "ComplexityReduction.Program.PolyProg.atom",
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "tmkarp-primitive": typed_capability.witness
        }
        observed_capability_exact_types = {
            "tmkarp-primitive": typed_capability.exact_type
        }
        representation_adapter_exact_type = None
    elif task_class == "typed_tmkarp_dependent_composition_dag":
        assert typed_capability is not None and successor_capability is not None
        composition_intermediate_problem = problems.get(typed_capability.target)
        if (
            composition_intermediate_problem is None
            or composition_intermediate_problem.endpoint_node
            != successor_capability.source_node
            or typed_capability.target_node != successor_capability.source_node
        ):
            _fail(
                "candidate_wrong_endpoint",
                "dependent composition capabilities do not share one exact intermediate endpoint",
            )
        allowed_primitives = (
            typed_capability.witness,
            successor_capability.witness,
            "ComplexityReduction.Program.Primitive.ofTMPolyTime",
            "ComplexityReduction.Program.PolyProg.atom",
            "ComplexityReduction.Program.PolyProg.comp",
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "tmkarp-primitive": typed_capability.witness,
            "composed-program": successor_capability.witness,
        }
        successor_exact_type = successor_capability.exact_type
        if (
            typed_capability.capability_kind
            == "forward_successor_only_tmkarp_admission"
        ):
            composition_successor_source = successor_capability.source
            composition_successor_target = successor_capability.target
            composition_admission_observation = {
                **typed_capability.to_dict(),
                "registry_fingerprint": observation.registry_fingerprint,
            }
            successor_exact_type = (
                f"{_NP_HARD_CERTIFIED_REDUCTION_HEAD_V2} "
                f"{composition_successor_source} {composition_successor_target}"
            )
            composition_successor_observation = {
                **successor_capability.to_dict(),
                "exact_type": successor_exact_type,
                "registry_fingerprint": observation.registry_fingerprint,
            }
        observed_capability_exact_types = {
            "tmkarp-primitive": typed_capability.exact_type,
            "composed-program": successor_exact_type,
        }
        representation_adapter_exact_type = None
    elif task_class == "typed_tmkarp_program_indexed_composition_dag":
        assert typed_capability is not None and program_packet_capability is not None
        composition_intermediate_problem = problems.get(typed_capability.target)
        if (
            composition_intermediate_problem is None
            or composition_intermediate_problem.endpoint_node
            != program_packet_capability.source_node
            or typed_capability.target_node
            != program_packet_capability.source_node
            or program_packet_capability.target_node != target_problem.endpoint_node
        ):
            _fail(
                "candidate_wrong_endpoint",
                "TMKarp/program-indexed capabilities do not share one exact intermediate endpoint",
            )
        packet_namespace = (
            "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources."
            "ProgramIndexedAdmissionPacket"
        )
        allowed_primitives = (
            typed_capability.witness,
            program_packet_capability.witness,
            "ComplexityReduction.Program.Primitive.ofTMPolyTime",
            "ComplexityReduction.Program.PolyProg.atom",
            "ComplexityReduction.Program.PolyProg.comp",
            f"{packet_namespace}.toExecutable",
            f"{packet_namespace}.toPrimitive",
            f"{packet_namespace}.toProgram",
            f"{packet_namespace}.ProgramRunCoherenceDirectTM.ofProgram",
            f"{packet_namespace}.toSemanticProof",
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "tmkarp-primitive": typed_capability.witness,
            "program-executable": program_packet_capability.witness,
        }
        observed_capability_exact_types = {
            "tmkarp-primitive": typed_capability.exact_type,
            "program-executable": program_packet_capability.exact_type,
        }
        representation_adapter_exact_type = None
    elif task_class == "typed_program_indexed_admission_dag":
        assert typed_capability is not None
        packet_namespace = (
            "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources."
            "ProgramIndexedAdmissionPacket"
        )
        allowed_primitives = (
            typed_capability.witness,
            f"{packet_namespace}.toExecutable",
            f"{packet_namespace}.toPrimitive",
            f"{packet_namespace}.toProgram",
            f"{packet_namespace}.ProgramRunCoherenceDirectTM.ofProgram",
            f"{packet_namespace}.toSemanticProof",
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "program-executable": typed_capability.witness
        }
        observed_capability_exact_types = {
            "program-executable": typed_capability.exact_type
        }
        representation_adapter_exact_type = None
    elif task_class == "typed_gadget_indexed_admission_dag":
        assert typed_capability is not None
        composition_intermediate_problem = _gadget_reference_problem(
            capability=typed_capability, problems=problems
        )
        packet_namespace = (
            "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources."
            "GadgetIndexedAdmissionPacket"
        )
        allowed_primitives = (
            typed_capability.witness,
            f"{packet_namespace}.toReferenceAudit",
            f"{packet_namespace}.toNormalizationAudit",
            f"{packet_namespace}.toGadgetExecutable",
            f"{packet_namespace}.toParameterAudit",
            f"{packet_namespace}.toSemanticForward",
            f"{packet_namespace}.toSemanticReverse",
            f"{packet_namespace}.toGadgetDirectTM",
            f"{packet_namespace}.toGadgetProgram",
            f"{packet_namespace}.toComposedProgram",
            f"{packet_namespace}.toComposedSemanticProof",
        )
        program_reference = typed_capability.witness
        observed_capability_terms = {
            "gadget-reference-audit": typed_capability.witness
        }
        observed_capability_exact_types = {
            "gadget-reference-audit": typed_capability.exact_type
        }
        representation_adapter_exact_type = None
    else:
        allowed_primitives = tuple(program.declaration for program in selected_programs)
        if task_class == "semantic_proof" and relation is not None:
            allowed_primitives += (relation.declaration,)
        program_reference = direct.declaration if direct is not None else None
        observed_capability_terms = {}
        observed_capability_exact_types = {}
        representation_adapter_exact_type = None
    authoring_seed_modules = _whole_reduction_authoring_seed_modules(
        root=root,
        input_module=input_module,
        task_class=task_class,
    )
    scaffold_module = next(
        (
            module
            for module in authoring_seed_modules
            if module in _BOOLEAN_CSP_SCAFFOLD_LAYERS_BY_MODULE
        ),
        None,
    )
    if scaffold_module is not None:
        allowed_primitives += tuple(
            dict.fromkeys(
                sum(
                    (
                        _BOOLEAN_CSP_SCAFFOLD_LAYERS_BY_MODULE[
                            scaffold_module
                        ][layer_name]
                        for layer_name in (
                            "construction",
                            "direct_tm",
                            "semantic",
                        )
                    ),
                    (),
                )
            )
        )
    allowed_primitives = tuple(dict.fromkeys(allowed_primitives))
    allowed_primitive_layers = _primitive_layers(
        allowed_primitives,
        scaffold_module=scaffold_module,
    )
    capability_source_modules = tuple(
        capability.module
        for capability in (
            typed_capability,
            successor_capability,
            program_packet_capability,
        )
        if capability is not None
        and capability.capability_kind
        in {
            "forward_tmkarp_admission",
            "forward_successor_only_tmkarp_admission",
            "forward_certified_successor",
            "forward_program_indexed_admission",
            "forward_gadget_indexed_admission",
        }
    )
    public_modules = {
        input_module,
        observation.declaration_module,
        hub_problem.module,
        *authoring_seed_modules,
        *(
            _BOOLEAN_CSP_NAE3_PUBLIC_SUPPORT_MODULES
            if scaffold_module is not None
            else ()
        ),
        *(program.module for program in selected_programs),
        *((relation.module,) if relation is not None else ()),
        *((typed_capability.module,) if typed_capability is not None else ()),
        *((successor_capability.module,) if successor_capability is not None else ()),
        *((program_packet_capability.module,) if program_packet_capability is not None else ()),
        *((composition_intermediate_problem.module,) if composition_intermediate_problem else ()),
        *(
            gap.module
            for gap in observation.gaps
            if gap.source_node == hub_problem.endpoint_node
            and gap.target_node == target_node
        ),
    }
    public_paths = {
        module_file(root.resolve() / "Lean", module).resolve()
        for module in public_modules
    }
    # Typed public packets are the complete model-visible admission surface.
    # Their implementation modules remain compiler dependencies, but exposing
    # those source files here would reveal the legacy template/gadget that the
    # staged authoring task is required to reconstruct node by node.
    if task_class not in {
        "typed_tmkarp_admission_dag",
        "typed_tmkarp_dependent_composition_dag",
        "typed_program_indexed_admission_dag",
        "typed_tmkarp_program_indexed_composition_dag",
        "typed_gadget_indexed_admission_dag",
    }:
        public_paths.update(
            _relevant_direct_public_sources(
                root=root.resolve(),
                source_files=public_paths,
                query_values=(
                    hub,
                    target,
                    *(program.declaration for program in selected_programs),
                    *allowed_primitives,
                    *((typed_capability.capability_id,) if typed_capability else ()),
                    *((typed_capability.witness,) if typed_capability else ()),
                ),
                max_depth=(5 if task_class == "whole_reduction_synthesis" else 1),
                max_files=(25 if task_class == "whole_reduction_synthesis" else 2),
            )
        )
    public_files = tuple(
        sorted(str(path.relative_to(root.resolve())) for path in public_paths)
    )
    task = build_np_hard_authoring_task_v2(
        root=root,
        input_module=input_module,
        input_problem_declaration=target,
        hub_module=hub_problem.module,
        hub_declaration=hub,
        task_class=task_class,
        gap_nodes=(
            _positive_nae3_whole_reduction_gap_nodes()
            if scaffold_module is not None
            else _task_gap_nodes(
                task_class=task_class,
                has_mapping_relation=relation is not None,
            )
        ),
        public_source_files=public_files,
        allowed_primitives=allowed_primitives,
        allowed_primitive_layers=allowed_primitive_layers,
        program_reference=program_reference,
        program_packet_reference=(
            program_packet_capability.witness
            if program_packet_capability is not None
            else (
                typed_capability.witness
                if typed_capability is not None
                and typed_capability.capability_kind
                == "forward_program_indexed_admission"
                else None
            )
        ),
        mapping_invariant=relation.declaration if relation is not None else None,
        observed_capability_terms=observed_capability_terms,
        observed_capability_exact_types=observed_capability_exact_types,
        representation_adapter_exact_type=representation_adapter_exact_type,
        composition_intermediate_module=(
            composition_intermediate_problem.module
            if composition_intermediate_problem is not None
            else None
        ),
        composition_intermediate_declaration=(
            composition_intermediate_problem.declaration
            if composition_intermediate_problem is not None
            else None
        ),
        composition_successor_module=(
            successor_capability.module
            if successor_capability is not None
            else (
                program_packet_capability.module
                if program_packet_capability is not None
                else None
            )
        ),
        composition_successor_source=composition_successor_source,
        composition_successor_target=composition_successor_target,
        composition_admission_observation=composition_admission_observation,
        composition_successor_observation=composition_successor_observation,
        additional_allowed_imports=tuple(
            dict.fromkeys(
                (*authoring_seed_modules, *capability_source_modules)
            )
        ),
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
            **(
                {
                    "content:lean-typed-capability": sha256_id(
                        typed_capability.to_dict()
                    )
                }
                if typed_capability is not None
                else {}
            ),
            **(
                {
                    "content:lean-gadget-indexed-packet": sha256_id(
                        typed_capability.to_dict()
                    )
                }
                if typed_capability is not None
                and typed_capability.capability_kind
                == "forward_gadget_indexed_admission"
                else {}
            ),
            **(
                {
                    "content:lean-successor-only-tmkarp-admission": sha256_id(
                        composition_admission_observation
                    )
                }
                if typed_capability is not None
                and typed_capability.capability_kind
                == "forward_successor_only_tmkarp_admission"
                else {}
            ),
            **(
                {
                    "content:lean-certified-successor": sha256_id(
                        composition_successor_observation
                        if composition_successor_observation is not None
                        else successor_capability.to_dict()
                    ),
                    "content:lean-typed-capability-chain": sha256_id(
                        _successor_only_observer_chain_payload_v2(
                            admission=composition_admission_observation,
                            successor=composition_successor_observation,
                            canonical_successor_source=(
                                composition_successor_source
                            ),
                            canonical_successor_target=(
                                composition_successor_target
                            ),
                        )
                        if composition_admission_observation is not None
                        and composition_successor_observation is not None
                        and composition_successor_source is not None
                        and composition_successor_target is not None
                        else {
                            "admission": typed_capability.to_dict(),
                            "successor": successor_capability.to_dict(),
                        }
                    ),
                }
                if typed_capability is not None
                and successor_capability is not None
                else {}
            ),
            **(
                {
                    "content:lean-program-indexed-packet": sha256_id(
                        program_packet_capability.to_dict()
                    ),
                    "content:lean-tmkarp-program-indexed-chain": sha256_id(
                        {
                            "admission": typed_capability.to_dict(),
                            "packet": program_packet_capability.to_dict(),
                        }
                    ),
                }
                if typed_capability is not None
                and program_packet_capability is not None
                else {}
            ),
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
    elif task_class == "typed_capability_dag":
        final_program = f"{task.candidate_module}.representationAdapter"
    elif task_class == "typed_tmkarp_admission_dag":
        final_program = f"{task.candidate_module}.tmKarpProgram"
    elif task_class == "typed_tmkarp_dependent_composition_dag":
        final_program = f"{task.candidate_module}.composedProgram"
    elif task_class == "typed_program_indexed_admission_dag":
        final_program = f"{task.candidate_module}.programIndexedProgram"
    elif task_class == "typed_tmkarp_program_indexed_composition_dag":
        final_program = f"{task.candidate_module}.composedProgram"
    elif task_class == "typed_gadget_indexed_admission_dag":
        final_program = f"{task.candidate_module}.gadgetComposedProgram"
    else:
        final_program = f"{task.candidate_module}.synthesizedProgram"
    dag = _full_capability_dag(
        task=task,
        hardness_seed=hardness_seed,
        hardness_route=hardness_route,
        existing_programs=selected_programs,
        mapping_relation=relation,
        typed_capability=typed_capability,
        successor_capability=successor_capability,
        program_packet_capability=program_packet_capability,
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
        terminal_node_id=task.terminal_node_id,
        final_program_node_id=(
            task.final_program_node_id
            if task.final_program_node_id is not None
            else next(
                (
                    node.node_id
                    for node in reversed(dag)
                    if node.declaration == final_program
                    and node.capability
                    in {"poly_program", "forward_representation_adapter"}
                ),
                None,
            )
        ),
        final_node_id="native-tm-np-hard",
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


def build_np_hard_declaration_type_observation_source(
    *,
    nonce: str,
    allowed_imports: tuple[str, ...],
    declarations: tuple[str, ...],
) -> str:
    if not nonce or any(character not in "0123456789abcdef" for character in nonce):
        _fail("invalid_authoring_planner_observation", "type-observer nonce is invalid")
    imports = tuple(
        dict.fromkeys(
            (
                NP_HARD_AUTHORING_PLANNER_MODULE,
                *(validate_module_name(module) for module in allowed_imports),
            )
        )
    )
    checked_declarations = tuple(
        validate_declaration_name(declaration, label="typed allowed primitive")
        for declaration in declarations
    )
    if not checked_declarations:
        _fail(
            "invalid_authoring_planner_observation",
            "type observer received an empty primitive allowlist",
        )
    source = "\n".join(f"import {module}" for module in imports)
    source += "\n\n" + "\n".join(
        "#hardness_np_hard_declaration_type "
        f"{json.dumps(nonce, ensure_ascii=True)} "
        f"{json.dumps(declaration, ensure_ascii=True)} {declaration}"
        for declaration in checked_declarations
    )
    source += "\n"
    _assert_public(source, label="allowed primitive type probe")
    return source


def parse_np_hard_declaration_type_observation(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    declarations: tuple[str, ...],
) -> tuple[tuple[str, str], ...]:
    observed: dict[str, str] = {}
    for line in (stdout + "\n" + stderr).splitlines():
        marker_index = line.find(_DECLARATION_TYPE_MARKER + "\t")
        if marker_index < 0:
            continue
        fields = line[marker_index:].split("\t")
        if len(fields) != 5:
            _fail(
                "invalid_authoring_planner_observation",
                "malformed allowed primitive type row",
            )
        marker, schema, row_nonce, declaration, exact_type = fields
        if marker != _DECLARATION_TYPE_MARKER or schema != _DECLARATION_TYPE_SCHEMA_V1:
            _fail(
                "invalid_authoring_planner_observation",
                "allowed primitive type marker/schema drifted",
            )
        if row_nonce != nonce:
            continue
        validate_declaration_name(declaration, label="observed allowed primitive")
        _assert_public(exact_type, label=f"observed type for {declaration}")
        if declaration in observed:
            _fail(
                "invalid_authoring_planner_observation",
                f"duplicate observed type for {declaration}",
            )
        observed[declaration] = exact_type
    expected = set(declarations)
    if set(observed) != expected:
        missing = sorted(expected - set(observed))
        unexpected = sorted(set(observed) - expected)
        _fail(
            "invalid_authoring_planner_observation",
            "allowed primitive type coverage mismatch: "
            f"missing={missing!r}, unexpected={unexpected!r}",
        )
    return tuple(sorted(observed.items()))


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
        if plan.task is not None:
            type_nonce = secrets.token_hex(16)
            type_source = build_np_hard_declaration_type_observation_source(
                nonce=type_nonce,
                allowed_imports=plan.task.allowed_imports,
                declarations=plan.task.allowed_primitives,
            )
            type_source_path = self.output_dir / "AllowedPrimitiveTypes.lean"
            type_source_path.write_text(type_source, encoding="utf-8")
            type_build = run_command(
                ["lake", "build", *plan.task.allowed_imports],
                cwd=self.root / "Lean",
                timeout_seconds=self.lean_timeout_seconds,
                output_limit=16 * 1024 * 1024,
            )
            if not type_build.ok:
                _fail(
                    "authoring_planner_probe_failed",
                    type_build.stderr
                    or type_build.stdout
                    or "allowed primitive type prebuild failed",
                )
            type_probe = run_command(
                ["lake", "env", "lean", str(type_source_path)],
                cwd=self.root / "Lean",
                timeout_seconds=self.lean_timeout_seconds,
                output_limit=16 * 1024 * 1024,
            )
            if not type_probe.ok:
                _fail(
                    "authoring_planner_probe_failed",
                    type_probe.stderr
                    or type_probe.stdout
                    or "allowed primitive type observation failed",
                )
            primitive_types = parse_np_hard_declaration_type_observation(
                stdout=type_probe.stdout,
                stderr=type_probe.stderr,
                nonce=type_nonce,
                declarations=plan.task.allowed_primitives,
            )
            dependency_hashes = dict(plan.task.dependency_hashes)
            dependency_hashes["content:lean-allowed-primitive-exact-types"] = (
                sha256_id(dict(primitive_types))
            )
            provisional_task = replace(
                plan.task,
                request_id="sha256:" + "0" * 64,
                allowed_primitive_exact_types=primitive_types,
                dependency_hashes=tuple(sorted(dependency_hashes.items())),
            )
            enriched_task = replace(
                provisional_task,
                request_id=provisional_task.computed_request_id,
            )
            enriched_task.validate()
            plan = replace(
                plan,
                task=enriched_task,
                commands=plan.commands + (type_build, type_probe),
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


def exact_edge_construction_gap_nodes() -> tuple[Mapping[str, Any], ...]:
    """Freeze the public exact-edge typed construction DAG.

    This is the planner's public-policy path for ``direct_new_edge`` cases.
    It derives the DAG only from the frozen node motif; it never reads a
    solution, oracle, gold route, or conversion plan.
    """

    nodes = _task_gap_nodes(
        task_class="typed_exact_edge_construction_dag",
        has_mapping_relation=False,
    )
    if not nodes:
        _fail("authoring_plan_unsupported", "exact-edge construction DAG is empty")
    return nodes
