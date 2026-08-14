"""Optional numeric/encoding ranking hooks."""

from __future__ import annotations

from ..premise_registry import PremiseSolverRegistry
from .registry import Plugin


def _register(registry: PremiseSolverRegistry) -> None:
    del registry


PLUGIN = Plugin(
    name="numeric",
    register=_register,
    public_capabilities=("bit/list encoding hints", "bounded arithmetic hints"),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.NumericHelpers",
    ),
)

__all__ = ["PLUGIN"]
