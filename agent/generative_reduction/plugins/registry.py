"""Removable domain-plugin registry.

Plugins may register premise solvers and ranking hints, but they do not own a
proof frontier or alter final verification.
"""

from __future__ import annotations

from dataclasses import dataclass
from importlib import import_module
from typing import Callable

from ..finite_synthesis import FiniteSynthesisPlugin
from ..premise_registry import PremiseSolverRegistry


@dataclass(frozen=True)
class Plugin:
    name: str
    register: Callable[[PremiseSolverRegistry], None]
    public_capabilities: tuple[str, ...]
    lean_imports: tuple[str, ...] = ()
    finite_synthesis_plugins: tuple[FiniteSynthesisPlugin, ...] = ()


PLUGIN_MODULES = {
    "boolean_csp": "agent.generative_reduction.plugins.boolean_csp",
    "graph": "agent.generative_reduction.plugins.graph",
    "numeric": "agent.generative_reduction.plugins.numeric",
}


def load_plugin(name: str) -> Plugin:
    module_name = PLUGIN_MODULES.get(name)
    if module_name is None:
        raise ValueError(f"unknown generative-reduction plugin: {name!r}")
    module = import_module(module_name)
    plugin = getattr(module, "PLUGIN", None)
    if not isinstance(plugin, Plugin) or plugin.name != name:
        raise ValueError(f"invalid generative-reduction plugin module: {module_name}")
    return plugin


def install_plugins(registry: PremiseSolverRegistry, names: tuple[str, ...]) -> tuple[Plugin, ...]:
    loaded: list[Plugin] = []
    for name in dict.fromkeys(names):
        plugin = load_plugin(name)
        plugin.register(registry)
        loaded.append(plugin)
    return tuple(loaded)


__all__ = ["PLUGIN_MODULES", "Plugin", "install_plugins", "load_plugin"]
