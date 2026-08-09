from agent.hardness.benchmark import summarize_benchmark_results


def test_group_success_requires_every_exact_case() -> None:
    results = [
        {
            "id": "graph-tail",
            "group_id": "forked",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "axiom_clean": True,
            "deterministic_replay": True,
        },
        {
            "id": "numeric-tail",
            "group_id": "forked",
            "expected_status": "VERIFIED",
            "actual_status": "BLOCKED",
            "passed": False,
        },
    ]
    groups = summarize_benchmark_results(results=results)["groups"]
    assert groups == [{"id": "forked", "total": 2, "passed": 1, "passed_all": False}]
