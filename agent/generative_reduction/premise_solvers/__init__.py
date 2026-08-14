"""Built-in family-independent premise solvers."""

from .definitional import DefinitionalSolver
from .finite_reflection import GenericFiniteReflectionSolver
from .lean_tactic import BoundedLeanTacticSolver
from .local_context import LocalContextSolver
from .polynomial import PolynomialCombinatorSolver
from .recursive_theorem import RecursiveTheoremSolver
from .reduction_graph import ReductionGraphSolver
from .simp import SimpSolver
from .typeclass import TypeclassSolver

__all__ = [
    "BoundedLeanTacticSolver",
    "DefinitionalSolver",
    "GenericFiniteReflectionSolver",
    "LocalContextSolver",
    "PolynomialCombinatorSolver",
    "RecursiveTheoremSolver",
    "ReductionGraphSolver",
    "SimpSolver",
    "TypeclassSolver",
]
