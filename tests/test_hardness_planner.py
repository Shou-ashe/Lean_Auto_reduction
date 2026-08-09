import pytest

from agent.hardness.models import RouteCandidate
from agent.hardness.planner import choose_route


def route(name: str, *, final_edges: int = 0) -> RouteCandidate:
    return RouteCandidate(
        target_declaration=f"Target.{name}",
        membership_declaration=f"Target.{name}Membership",
        atoms=(f"Edge.{name}",),
        roles=("finalComposition" if final_edges else "sharedGadget",),
        final_composition_edges=final_edges,
        registry_fingerprint="registry",
    )


def test_deterministic_planner_prefers_no_final_composition() -> None:
    atomic = route("Atomic")
    final = route("Final", final_edges=1)
    result = choose_route(
        routes=(final, atomic), mode="deterministic", target_declaration=None
    )
    assert result.route == atomic
    assert result.decision.model_called is False
    assert result.decision.model_usage is None


def test_deterministic_planner_filters_the_exact_requested_target() -> None:
    first = route("First")
    second = route("Second")
    result = choose_route(
        routes=(first, second), target_declaration=second.target_declaration
    )
    assert result.route == second


@pytest.mark.parametrize("legacy_mode", ["auto", "model-required", "deepseek"])
def test_legacy_model_route_modes_are_rejected(legacy_mode: str) -> None:
    with pytest.raises(ValueError, match="model route reranking was removed"):
        choose_route(
            routes=(route("Only"),),
            mode=legacy_mode,
            target_declaration=None,
        )


def test_no_routes_preserves_the_exact_route_gap_without_model_metadata() -> None:
    result = choose_route(routes=(), target_declaration=None)
    assert result.route is None
    assert result.decision.mode == "deterministic"
    assert result.decision.model_called is False
    assert result.decision.model_error is None
    assert result.decision.reason == "no validated route matches the requested target"
