from agent.hardness.benchmark import summarize_benchmark_results


def test_outcome_accuracy_requires_status_and_failure_code_match() -> None:
    results = [
        {
            "id": "positive",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "axiom_clean": True,
            "deterministic_replay": True,
        },
        {
            "id": "negative",
            "expected_status": "BLOCKED",
            "actual_status": "BLOCKED",
            "actual_failure_code": "wrong-code",
            "passed": False,
        },
    ]
    summary = summarize_benchmark_results(results=results)
    assert summary["passed"] == 1
    assert summary["metrics"]["case_outcome_accuracy"] == 0.5
    assert summary["metrics"]["negative_block_accuracy"] == 0.0
