from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys

from agent.hardness.model_client import DeepSeekConfig


ROOT = Path(__file__).resolve().parents[1]
SUITE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "boolean_csp_np_hard_public_v1.json"
)
ORACLE = ROOT / "Evaluation" / "boolean_csp_np_hard_oracle_v1.json"
LEAN_ROOT = (
    ROOT
    / "Lean"
    / "Reference"
    / "Benchmark"
    / "Hardness"
    / "Inputs"
    / "BooleanCSPNPHard"
)


def test_public_suite_has_twenty_isolated_answer_free_cases() -> None:
    from agent.hardness.boolean_csp_np_hard_benchmark import load_suite

    suite = load_suite(SUITE)
    assert SUITE.parent == ROOT / "Benchmark" / "Hardness" / "Suites"
    assert not (
        ROOT / "Benchmark" / "Hardness" / "Experimental" / "BooleanCSP"
    ).exists()
    assert len(suite.cases) == 20
    assert {case.split for case in suite.cases} == {"dev", "validation", "heldout"}
    assert sum(case.split == "dev" for case in suite.cases) == 4
    assert sum(case.split == "validation" for case in suite.cases) == 6
    assert sum(case.split == "heldout" for case in suite.cases) == 10
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    forbidden = {
        "answer",
        "expected",
        "expected_public_status",
        "gold",
        "hint",
        "oracle",
        "route",
        "solution",
    }
    for case in raw["cases"]:
        assert forbidden.isdisjoint(case)


def test_each_case_owns_one_closed_lean_problem_module() -> None:
    from agent.hardness.boolean_csp_np_hard_benchmark import load_suite

    suite = load_suite(SUITE)
    for case in suite.cases:
        leaf = case.module.rsplit(".", 1)[-1]
        path = LEAN_ROOT / f"{leaf}.lean"
        assert path.exists(), case.case_id
        source = path.read_text(encoding="utf-8")
        assert "def problem : Encoding.PresentedProblem" in source or (
            "abbrev problem : Encoding.PresentedProblem" in source
        )
        assert "NativeTMNPHard" not in source
        assert "complexity_reduction_ir_typed_edge" not in source


def test_authored_cases_do_not_import_the_canonical_hard_endpoint() -> None:
    from agent.hardness.boolean_csp_np_hard_benchmark import load_suite

    suite = load_suite(SUITE)
    common_source = (LEAN_ROOT / "Common.lean").read_text(encoding="utf-8")
    assert "Presentation.ThreeSATLike" not in common_source
    assert "Hardness.ThreeSATLike" not in common_source
    for case in suite.cases[1:]:
        leaf = case.module.rsplit(".", 1)[-1]
        source = (LEAN_ROOT / f"{leaf}.lean").read_text(encoding="utf-8")
        assert "ThreeSATLike" not in source, case.case_id


def test_oracle_matches_public_case_set_and_all_targets_are_np_complete() -> None:
    from agent.hardness.boolean_csp_np_hard_benchmark import load_oracle, load_suite

    suite = load_suite(SUITE)
    oracle = load_oracle(ORACLE, suite=suite)
    assert {case["case_id"] for case in oracle["cases"]} == {
        case.case_id for case in suite.cases
    }
    assert all(case["mathematical_class"] == "NP-complete" for case in oracle["cases"])
    assert sum(not case["requires_model"] for case in oracle["cases"]) == 1


def test_only_runner_lists_boolean_csp_inside_the_78_case_registry() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    value = json.loads(completed.stdout)
    assert value["case_count"]["boolean_csp"] == 20
    assert value["case_count"]["total"] == 78
    assert len(value["lanes"]["boolean_csp"]) == 20


def test_case_without_preinstalled_route_reaches_whole_reduction_generation(
    tmp_path: Path,
) -> None:
    from agent.hardness.np_hard_authoring import NPHardAuthoringTaskV2
    from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2
    from agent.hardness.np_hard_gap_runtime import (
        NP_HARD_NODE_PROMPT_MAX_SOURCE_FILES,
        NP_HARD_NODE_PROMPT_SOURCE_CHAR_BUDGET,
        _node_request,
        build_np_hard_node_prompt_v1,
    )

    module = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4"
    problem = f"{module}.problem"
    plan = NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=module,
        input_problem_declaration=problem,
        output_dir=tmp_path / "case-02-plan",
    ).plan()

    assert plan.status == "PLANNED"
    assert plan.failure_code is None
    assert plan.model_calls == 0
    assert plan.task.task_class == "whole_reduction_synthesis"
    assert plan.task.final_program_node_id == "poly-program"
    assert plan.task.terminal_node_id == "semantic-iff"
    assert [node.capability for node in plan.task.gap_nodes] == [
        "reduction_executable",
        "direct_tm",
        "reduction_primitive",
        "poly_program",
        "program_run_coherence",
        "semantic_forward",
        "semantic_reverse",
        "semantic_iff",
    ]
    assert not plan.task.observed_capability_terms
    assert any(
        path.endswith("ComplexityReduction/Domain/BooleanCSP.lean")
        for path in plan.task.public_source_files
    )
    assert any(
        path.endswith("ComplexityReduction/CSP/StandardRelations.lean")
        for path in plan.task.public_source_files
    )
    assert NPHardAuthoringTaskV2.from_dict(plan.task.to_dict()) == plan.task

    request = _node_request(
        task=plan.task,
        node_ordinal=1,
        dependency_snapshot=plan.task.dependency_hashes,
        accepted=(),
        total_model_calls=0,
        instance_call_budget=64,
    )
    prompt = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=plan.task,
            request=request,
            accepted_bodies={},
            diagnostic=None,
        )
    )
    sources = prompt["public_sources"]
    context = prompt["public_source_context"]
    assert len(json.dumps(prompt, ensure_ascii=True)) < 65_000
    assert len(sources) <= NP_HARD_NODE_PROMPT_MAX_SOURCE_FILES
    assert sum(len(source) for source in sources.values()) <= (
        NP_HARD_NODE_PROMPT_SOURCE_CHAR_BUDGET
    )
    assert context["mode"] == "node_retrieved_source_excerpts_v1"
    assert context["omitted_file_count"] > 0
    assert any(path.endswith("Case02PositiveNAE4.lean") for path in sources)
    assert any(path.endswith("Satisfiability.lean") for path in sources)
    assert any("notAllEqualRel 4" in source for source in sources.values())
    assert any("threeSATStructuredProblem" in source for source in sources.values())

    repair_prompt = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=plan.task,
            request=request,
            accepted_bodies={},
            diagnostic="repeated Lean diagnostic " * 1_000,
        )
    )
    assert repair_prompt["public_sources"] == sources
    assert len(repair_prompt["lean_diagnostic"]) == 4_000


def test_boolean_csp_backend_calls_the_orchestrator_library_directly(
    tmp_path: Path, monkeypatch
) -> None:
    import agent.hardness.boolean_csp_np_hard_benchmark as backend

    captured = []

    class FakeResult:
        status = "VERIFIED"
        failure_code = None
        model_calls = 1

        def to_dict(self):
            problem = (
                "Benchmark.Hardness.Inputs.BooleanCSPNPHard."
                "Case01Canonical.problem"
            )
            return {
                "input_identity": {
                    "canonical_problem": problem,
                    "requested_declaration": problem,
                    "normalization_certificate": "lean-checked-artifact",
                },
                "artifact": {"endpoint": problem},
                "independent_replay": {"passed": True},
                "axiom_audit": {"passed": True},
            }

    class FakeOrchestrator:
        def __init__(self, config):
            captured.append(config)

        def run(self):
            return FakeResult()

    monkeypatch.setattr(backend, "NPHardOrchestratorV2", FakeOrchestrator)
    monkeypatch.setattr(
        backend,
        "load_np_hard_production_model_config",
        lambda **_kwargs: DeepSeekConfig(api_key="test-only"),
    )

    report = backend.run_suite(
        root=ROOT,
        suite_path=SUITE,
        output_root=tmp_path / "boolean-direct",
        case_ids=("q-b01-canonical-three-sat-like",),
    )

    assert len(captured) == 1
    assert captured[0].problem_declaration.endswith("Case01Canonical.problem")
    assert report["cases"][0]["status"] == "VERIFIED"
    assert report["cases"][0]["endpoint_equality_audit_passed"] is True


def test_scorer_requires_all_three_formal_audits(tmp_path: Path) -> None:
    from agent.hardness.boolean_csp_np_hard_benchmark import load_suite, score_run

    suite = load_suite(SUITE)
    case = suite.cases[0]
    run = {
        "schema_version": "boolean_csp_np_hard_run_v1",
        "suite_id": suite.suite_id,
        "suite_sha256": suite.sha256,
        "oracle_accessed": False,
        "cases": [
            {
                "case_id": case.case_id,
                "status": "VERIFIED",
                "failure_code": None,
                "model_calls": 0,
                "independent_replay_passed": True,
                "axiom_audit_passed": True,
                "endpoint_equality_audit_passed": False,
            }
        ],
    }
    run_path = tmp_path / "run.json"
    score_path = tmp_path / "score.json"
    run_path.write_text(json.dumps(run), encoding="utf-8")
    score = score_run(
        suite_path=SUITE,
        oracle_path=ORACLE,
        run_report_path=run_path,
        score_report_path=score_path,
    )
    assert score["passed_case_count"] == 0
    assert score["completion_rate"] == 0.0
    assert score_path.exists()
