from __future__ import annotations

from agent.reduction.models import ReductionResult, RootGoal
from agent.reduction.orchestrator import public_status
from agent.reduction.profiles import PROFILE_NAMES, get_profile


def test_profiles_share_search_semantics_and_only_add_audits() -> None:
    assert PROFILE_NAMES == ("research", "strict-release", "benchmark")
    assert get_profile("research").independent_replay is False
    assert get_profile("strict-release").independent_replay is True
    assert get_profile("benchmark").independent_replay is True
    assert get_profile("research").benchmark_audits is False
    assert get_profile("benchmark").benchmark_audits is True


def test_public_status_uses_the_existing_hardness_vocabulary() -> None:
    result = ReductionResult(
        status="VERIFIED",
        profile="research",
        root_goal=RootGoal.for_problem(
            input_module="Example.Input",
            problem_declaration="Example.Input.problem",
            endpoint_fingerprint="lean:test",
        ),
        output_dir="/tmp/example",
        kernel_verified=True,
    )
    assert public_status(result) == "VERIFIED"
