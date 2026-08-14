"""Optional graph-domain ranking hooks; the core remains usable without it."""

from __future__ import annotations

from ..premise_registry import PremiseSolverRegistry
from .registry import Plugin


def _register(registry: PremiseSolverRegistry) -> None:
    # Graph-specific proof rules are discovered from Lean by the typed index.
    # No Python theorem-name allowlist is installed here.
    del registry


PLUGIN = Plugin(
    name="graph",
    register=_register,
    public_capabilities=("vertex/edge observations", "graph component hints"),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.GraphHelpers",
    ),
)

__all__ = ["PLUGIN"]
