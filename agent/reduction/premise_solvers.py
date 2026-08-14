"""Lean-source premise solvers used by the first NP-hard research core."""

from __future__ import annotations

from dataclasses import dataclass

from .models import TheoremCandidate


@dataclass(frozen=True)
class PremisePlan:
    solver: str
    proof_lines: tuple[str, ...]


SCHAEFER_NONEMPTY_SOLVER = (
    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
    "gammaRelationsNonempty_of_decide_eq_true",
    "    decide",
)
SCHAEFER_HARD_SIDE_SOLVER = (
    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
    "gammaNotSchaeferTractable_of_decide_eq_false",
    "    decide",
)


def plans_for(candidate: TheoremCandidate) -> tuple[PremisePlan, ...]:
    """Return type-driven solver plans for a theorem's open premises."""

    if candidate.is_schaefer_schema:
        plans: list[PremisePlan] = []
        for premise in candidate.premises:
            if ".Nonempty" in premise:
                plans.append(
                    PremisePlan(
                        "finite-reflection:relations-nonempty",
                        SCHAEFER_NONEMPTY_SOLVER,
                    )
                )
            elif "IsSchaeferTractable" in premise:
                plans.append(
                    PremisePlan(
                        "finite-reflection:not-schaefer-tractable",
                        SCHAEFER_HARD_SIDE_SOLVER,
                    )
                )
            else:
                return ()
        return tuple(plans)
    if candidate.premise_count == 0:
        return ()
    return ()
