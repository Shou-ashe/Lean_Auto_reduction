"""Typed metadata for the reusable finite-witness combinator registry."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Iterable

from .models import sha256_id


FINITE_WITNESS_REGISTRY_SCHEMA = "hardness_finite_witness_registry_v1"


@dataclass(frozen=True)
class FiniteWitnessCombinator:
    name: str
    category: str
    lean_declaration: str
    witness_shapes: tuple[str, ...]
    producer: str = "stage_m_finite_witness_registry"

    @property
    def combinator_id(self) -> str:
        return sha256_id(
            {
                "schema_version": FINITE_WITNESS_REGISTRY_SCHEMA,
                **asdict(self),
            }
        )

    def to_dict(self) -> dict[str, object]:
        value = asdict(self)
        value["combinator_id"] = self.combinator_id
        return value


COMBINATORS = (
    FiniteWitnessCombinator(
        "list_nat",
        "witness_shape",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.natListPresentation",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "nodup",
        "subset_constraint",
        "List.Nodup",
        ("bounded_subset",),
    ),
    FiniteWitnessCombinator(
        "vertices_within_bounds",
        "subset_constraint",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.VerticesWithinBounds",
        ("bounded_subset", "pair_list"),
    ),
    FiniteWitnessCombinator(
        "cardinality_budget",
        "budget",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.cardinalityBudgetChecker",
        ("bounded_subset",),
    ),
    FiniteWitnessCombinator(
        "pair_list",
        "witness_shape",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.pairListView",
        ("pair_list",),
    ),
    FiniteWitnessCombinator(
        "edge",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.adjacencyChecker",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "adjacency",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.adjacencyChecker",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "external_neighborhood",
        "local_graph_checker",
        "ComplexityReduction.Program.ContextListAny.executable",
        ("list_nat",),
    ),
    FiniteWitnessCombinator(
        "cover",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.coverChecker",
        ("bounded_subset",),
    ),
    FiniteWitnessCombinator(
        "coloring",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.coloringChecker",
        ("list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "deletion_coloring",
        "witness_shape",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.DeletionColoring",
        ("deletion_coloring",),
    ),
    FiniteWitnessCombinator(
        "path_legality",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.pathLegalityChecker",
        ("pair_list", "list_nat"),
    ),
    FiniteWitnessCombinator(
        "edge_index_path",
        "local_graph_checker",
        "ComplexityReduction.Program.PairOfPaths.edgeIndexPathBool",
        ("pair_list",),
    ),
    FiniteWitnessCombinator(
        "binary_path_cost",
        "budget",
        "ComplexityReduction.Program.PairOfPaths.boundedCostBool",
        ("pair_list",),
    ),
    FiniteWitnessCombinator(
        "disjointness",
        "local_graph_checker",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.pairListDisjointChecker",
        ("pair_list",),
    ),
    FiniteWitnessCombinator(
        "list_sum",
        "budget",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.listSum",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "nat_budget",
        "budget",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.natBudgetChecker",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
    FiniteWitnessCombinator(
        "int_budget",
        "budget",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.intBudgetChecker",
        ("bounded_subset", "pair_list", "list_nat"),
    ),
    FiniteWitnessCombinator(
        "local_predicate",
        "local_predicate",
        "ComplexityReduction.Agent.Hardness.FiniteWitness.localPredicateChecker",
        ("bounded_subset", "pair_list", "list_nat", "deletion_coloring"),
    ),
)

COMBINATOR_BY_NAME = {entry.name: entry for entry in COMBINATORS}


def missing_combinators(required: Iterable[str]) -> tuple[str, ...]:
    return tuple(name for name in required if name not in COMBINATOR_BY_NAME)


def precise_finite_witness_blocker(
    *, required: Iterable[str], witness_bound: bool = True, soundness: bool = True
) -> str | None:
    missing = missing_combinators(required)
    if missing:
        return f"missing_checker_combinator:{missing[0]}"
    if not witness_bound:
        return "missing_witness_bound"
    if not soundness:
        return "missing_soundness_lemma"
    return None


def finite_witness_registry() -> dict[str, object]:
    return {
        "schema_version": FINITE_WITNESS_REGISTRY_SCHEMA,
        "registry_id": sha256_id(
            {
                "schema_version": FINITE_WITNESS_REGISTRY_SCHEMA,
                "combinator_ids": [entry.combinator_id for entry in COMBINATORS],
            }
        ),
        "combinators": [entry.to_dict() for entry in COMBINATORS],
    }
