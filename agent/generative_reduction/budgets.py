"""Resource budgets and monotone usage accounting."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from threading import Lock


@dataclass(frozen=True)
class SearchBudget:
    max_search_rounds: int = 96
    max_search_depth: int = 16
    max_expanded_states: int = 512
    max_frontier_width: int = 24
    max_capability_plans: int = 256
    max_exact_closure_candidates: int = 16
    max_guidance_candidates_per_goal: int = 12
    max_guidance_plans_per_goal: int = 8
    max_actions_per_provider: int = 16
    max_theorem_expansions_before_synthesis: int = 12
    min_synthesis_action_expansions: int = 2
    min_synthesis_materializations: int = 1
    synthesis_activation_deadline: int = 12
    stagnation_window: int = 8
    max_lean_checks: int = 256
    max_model_calls: int = 20
    max_strategy_calls: int = 4
    max_authoring_calls: int = 16
    max_synthesis_designs: int = 8
    max_authoring_attempts_per_stage: int = 4
    max_generated_files: int = 24
    max_branching_per_expansion: int = 3
    max_application_frames: int = 64
    max_data_witness_candidates: int = 12
    max_dependent_reinstantiations: int = 128
    max_action_failures_per_goal: int = 32
    max_frame_verification_checks: int = 64
    max_reconstruction_repairs: int = 4
    max_context_expansions_per_design: int = 3
    max_repairs_per_design: int = 3
    max_duplicate_candidate_rejections: int = 4
    max_same_diagnostic_repetitions: int = 2
    max_finite_candidates: int = 64
    max_cegis_rounds: int = 8
    max_structural_depth: int = 8
    max_requeues_per_state: int = 256
    max_recursive_substep_plans: int = 256
    wall_clock_timeout_seconds: int = 1800

    def validate(self) -> None:
        for name, value in asdict(self).items():
            if not isinstance(value, int) or value < 0:
                raise ValueError(f"{name} must be a non-negative integer")
        positive = (
            "max_search_rounds",
            "max_search_depth",
            "max_frontier_width",
            "max_exact_closure_candidates",
            "max_guidance_candidates_per_goal",
            "max_guidance_plans_per_goal",
            "max_actions_per_provider",
            "max_branching_per_expansion",
            "max_application_frames",
            "max_data_witness_candidates",
            "max_dependent_reinstantiations",
            "max_action_failures_per_goal",
            "max_frame_verification_checks",
            "max_reconstruction_repairs",
            "max_context_expansions_per_design",
            "max_repairs_per_design",
            "max_duplicate_candidate_rejections",
            "max_same_diagnostic_repetitions",
            "max_finite_candidates",
            "max_cegis_rounds",
            "max_structural_depth",
            "max_requeues_per_state",
            "max_recursive_substep_plans",
            "wall_clock_timeout_seconds",
        )
        for name in positive:
            if getattr(self, name) == 0:
                raise ValueError(f"{name} must be positive")
        if self.max_strategy_calls + self.max_authoring_calls < self.max_model_calls:
            raise ValueError(
                "strategy and authoring call ceilings must cover max_model_calls"
            )


@dataclass
class BudgetUsage:
    search_rounds: int = 0
    expanded_states: int = 0
    capability_plans: int = 0
    theorem_expansions: int = 0
    synthesis_action_expansions: int = 0
    synthesis_materializations: int = 0
    lean_checks: int = 0
    model_calls: int = 0
    strategy_calls: int = 0
    authoring_calls: int = 0
    synthesis_designs: int = 0
    generated_files: int = 0
    application_frames: int = 0
    dependent_reinstantiations: int = 0
    frame_verification_checks: int = 0
    reconstruction_repairs: int = 0
    context_expansions: int = 0
    duplicate_candidate_rejections: int = 0
    repeated_diagnostics: int = 0
    finite_candidates: int = 0
    finite_counterexamples: int = 0
    finite_certificates: int = 0
    generated_lean_checks: int = 0
    generated_lean_successes: int = 0
    capability_registrations: int = 0
    requeues: int = 0
    recursive_substep_plans: int = 0


class BudgetExhausted(RuntimeError):
    def __init__(self, resource: str):
        super().__init__(f"budget exhausted: {resource}")
        self.resource = resource


class BudgetTracker:
    """Thread-safe monotone counters with named limits."""

    _LIMITS = {
        "search_rounds": "max_search_rounds",
        "expanded_states": "max_expanded_states",
        "capability_plans": "max_capability_plans",
        "lean_checks": "max_lean_checks",
        "model_calls": "max_model_calls",
        "strategy_calls": "max_strategy_calls",
        "authoring_calls": "max_authoring_calls",
        "synthesis_designs": "max_synthesis_designs",
        "generated_files": "max_generated_files",
        "application_frames": "max_application_frames",
        "dependent_reinstantiations": "max_dependent_reinstantiations",
        "frame_verification_checks": "max_frame_verification_checks",
        "reconstruction_repairs": "max_reconstruction_repairs",
        "duplicate_candidate_rejections": "max_duplicate_candidate_rejections",
        "finite_candidates": "max_finite_candidates",
        "finite_counterexamples": "max_cegis_rounds",
        "requeues": "max_requeues_per_state",
        "recursive_substep_plans": "max_recursive_substep_plans",
    }

    def __init__(self, budget: SearchBudget):
        budget.validate()
        self.budget = budget
        self.usage = BudgetUsage()
        self._lock = Lock()

    def remaining(self, resource: str) -> int | None:
        limit_name = self._LIMITS.get(resource)
        if limit_name is None:
            return None
        return max(0, getattr(self.budget, limit_name) - getattr(self.usage, resource))

    def consume(self, resource: str, amount: int = 1) -> None:
        if amount < 0:
            raise ValueError("budget consumption must be non-negative")
        with self._lock:
            limit_name = self._LIMITS.get(resource)
            current = getattr(self.usage, resource)
            if limit_name is not None and current + amount > getattr(self.budget, limit_name):
                raise BudgetExhausted(resource)
            setattr(self.usage, resource, current + amount)

    def to_dict(self) -> dict[str, object]:
        return {
            "budget": asdict(self.budget),
            "usage": asdict(self.usage),
            "remaining": {
                resource: self.remaining(resource) for resource in self._LIMITS
            },
        }


__all__ = ["BudgetExhausted", "BudgetTracker", "BudgetUsage", "SearchBudget"]
