"""Registry for type-driven, Lean-checked premise solvers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, Sequence

from .models import GoalKind, TheoremPremise


@dataclass(frozen=True)
class PremiseSolution:
    solver: str
    proof_lines: tuple[str, ...]
    proof_term: str | None
    confidence: float
    requires_lean_check: bool = True


class PremiseSolver(Protocol):
    name: str

    def supports(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> float: ...

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None: ...


class PremiseSolverRegistry:
    def __init__(self, solvers: Sequence[PremiseSolver] = ()):
        self._solvers: list[PremiseSolver] = []
        for solver in solvers:
            self.register(solver)

    @property
    def solvers(self) -> tuple[PremiseSolver, ...]:
        return tuple(self._solvers)

    def register(self, solver: PremiseSolver) -> None:
        if any(existing.name == solver.name for existing in self._solvers):
            raise ValueError(f"premise solver already registered: {solver.name}")
        self._solvers.append(solver)

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str] = ()
    ) -> PremiseSolution | None:
        ranked = sorted(
            (
                (solver.supports(premise, local_context), index, solver)
                for index, solver in enumerate(self._solvers)
            ),
            key=lambda item: (-item[0], item[1]),
        )
        for confidence, _, solver in ranked:
            if confidence <= 0:
                continue
            proposed = solver.propose(premise, local_context)
            if proposed is not None:
                return proposed
        return None

    def coverage(
        self,
        premises: Sequence[TheoremPremise],
        local_context: Sequence[str] = (),
    ) -> tuple[tuple[TheoremPremise, PremiseSolution], tuple[TheoremPremise, ...]]:
        solved: list[tuple[TheoremPremise, PremiseSolution]] = []
        residual: list[TheoremPremise] = []
        for premise in premises:
            proposal = self.propose(premise, local_context)
            if proposal is None:
                residual.append(premise)
            else:
                solved.append((premise, proposal))
        return tuple(solved), tuple(residual)


def default_registry() -> PremiseSolverRegistry:
    from .premise_solvers.definitional import DefinitionalSolver
    from .premise_solvers.finite_reflection import GenericFiniteReflectionSolver
    from .premise_solvers.lean_tactic import BoundedLeanTacticSolver
    from .premise_solvers.local_context import LocalContextSolver
    from .premise_solvers.polynomial import PolynomialCombinatorSolver
    from .premise_solvers.reduction_graph import ReductionGraphSolver
    from .premise_solvers.recursive_theorem import RecursiveTheoremSolver
    from .premise_solvers.simp import SimpSolver
    from .premise_solvers.typeclass import TypeclassSolver

    return PremiseSolverRegistry(
        (
            LocalContextSolver(),
            DefinitionalSolver(),
            TypeclassSolver(),
            SimpSolver(),
            GenericFiniteReflectionSolver(),
            ReductionGraphSolver(),
            PolynomialCombinatorSolver(),
            BoundedLeanTacticSolver(),
            RecursiveTheoremSolver(),
        )
    )


def goal_kind_for_premise(premise: TheoremPremise) -> GoalKind:
    from .goal_kind_adapters import classify_goal

    return classify_goal(premise.exact_type, premise_kind=premise.kind.value)


__all__ = [
    "PremiseSolution",
    "PremiseSolver",
    "PremiseSolverRegistry",
    "default_registry",
    "goal_kind_for_premise",
]
