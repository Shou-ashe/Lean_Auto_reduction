import json
from pathlib import Path

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.input_planner import ObservedInputPlannerResult
from agent.hardness.model_client import ModelResponse
from scripts.run_deepseek_core_generalization_benchmark import (
    interaction_metrics,
    normalize_action_payload,
    request_for_case,
    submitted_objective_term,
)


ROOT = Path(__file__).resolve().parents[1]


def response(payload: object) -> ModelResponse:
    return ModelResponse(
        called=True,
        ok=True,
        content=json.dumps(payload),
        error=None,
        status_code=200,
        duration_seconds=0.1,
        usage={"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
        attempts=1,
        finish_reason="stop",
    )


def test_runner_normalizes_nested_stage_l_actions() -> None:
    assert normalize_action_payload(
        {"finish": {"membership_lean_term": "Evidence.member"}}
    ) == {
        "action": "finish",
        "membership_lean_term": "Evidence.member",
    }


def test_runner_preserves_the_raw_objective_specific_model_term() -> None:
    result = ObservedInputPlannerResult(
        plan=None,
        lean_term=None,
        problem_match=None,
        selected_connection=None,
        reduction_declarations=(),
        explanation="test",
        model_responses=(
            response(
                {
                    "finish": {
                        "completeness_lean_term": "  Evidence.complete  "
                    }
                }
            ),
        ),
    )
    assert submitted_objective_term(result, "prove_np_complete") == (
        "  Evidence.complete  "
    )


def test_runner_audits_repeated_search_and_ignored_terminal_guidance() -> None:
    prompts = (
        json.dumps(
            {
                "terminal_guidance": {"mode": "stop_now"},
            }
        ),
        json.dumps({}),
    )
    responses = (
        response(
            {
                "action": "search_reductions",
                "searches": [{"source_node_ids": ["lean-whnf:1"]}],
            }
        ),
        response(
            {
                "action": "search_reductions",
                "searches": [{"source_node_ids": ["lean-whnf:1"]}],
            }
        ),
    )
    assert interaction_metrics(prompts, responses) == {
        "terminal_guidance_ignored_count": 1,
        "repeated_reduction_search_count": 1,
    }


def test_runner_builds_all_five_objective_request_variants() -> None:
    suite = load_benchmark_suite(
        ROOT / "Gate" / "Suites" / "core_generalization.json"
    )
    requests = {case.objective: request_for_case(case) for case in suite.cases}
    assert requests["reduce_to"].payload_kind == "reduction"
    assert requests["reduce_to_known_np"].required_hardness == "native_np"
    assert requests["reduce_to_known_hardness"].required_hardness == "native_np_hard"
    assert requests["prove_in_np"].payload_kind == "membership"
    assert requests["prove_np_complete"].payload_kind == "completeness"

