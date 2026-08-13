from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

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
        "clause_constraint",
        "complement_constraint",
        "clause_gadget",
        "reference_executable",
        "reduction_executable",
        "clause_gadget_direct_tm",
        "reference_direct_tm",
        "direct_tm",
        "reduction_primitive",
        "poly_program",
        "program_run_coherence",
        "reference_semantic_forward",
        "reference_semantic_reverse",
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
    nae4_scaffold = (
        "ComplexityReduction.Agent.Hardness.BooleanCSPNAE4ReductionScaffold"
    )
    assert nae4_scaffold in plan.task.allowed_imports
    assert any(
        path.endswith("BooleanCSPNAE4ReductionScaffold.lean")
        for path in plan.task.public_source_files
    )
    assert f"{nae4_scaffold}.clauseConstraint" in plan.task.allowed_primitives
    assert f"{nae4_scaffold}.quaternaryConstraint" in plan.task.allowed_primitives
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
    assert any(path.endswith("BooleanCSPNAE4ReductionScaffold.lean") for path in sources)
    assert any(path.endswith("ThreeSATToNAEThreeSAT.lean") for path in sources)
    assert any("clauseConstraint" in source for source in sources.values())
    assert any("notAllEqualRel 4" in source for source in sources.values())
    assert any("threeSATStructuredProblem" in source for source in sources.values())
    assert prompt["active_capability_guidance"].startswith(
        "Construct only the main padded NAE4 constraint"
    )

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


def test_positive_nae3_authoring_stages_a_new_reference_bridge(
    tmp_path: Path,
) -> None:
    from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2
    from agent.hardness.np_hard_gap_runtime import (
        AcceptedCapabilityNodeV1,
        NP_HARD_REFERENCE_STAGE_PROMPT_SOURCE_CHAR_BUDGET,
        _node_request,
        _recommended_first_body,
        build_np_hard_node_prompt_v1,
    )
    from agent.hardness.models import sha256_id

    module = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3"
    problem = f"{module}.problem"
    scaffold_module = (
        "ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold"
    )
    hidden_proof_module = (
        "ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources"
    )
    scaffold_file = (
        "Lean/Reference/ComplexityReduction/Agent/Hardness/"
        "BooleanCSPReductionScaffold.lean"
    )
    nae_tm_file = (
        "Lean/Reference/ComplexityReduction/Presentation/NAEThreeSATTM.lean"
    )
    sat_tm_file = (
        "Lean/Reference/ComplexityReduction/Presentation/SatisfiabilityTM.lean"
    )
    list_file = "Lean/Reference/ComplexityReduction/Program/List.lean"
    encoding_transport_file = (
        "Lean/Reference/ComplexityReduction/Program/EncodingTransport.lean"
    )
    finite_domain_file = (
        "Lean/Reference/ComplexityReduction/Presentation/FiniteDomainCSPTable.lean"
    )
    plan = NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=module,
        input_problem_declaration=problem,
        output_dir=tmp_path / "case-03-plan",
    ).plan()

    assert plan.status == "PLANNED"
    assert plan.task.task_class == "whole_reduction_synthesis"
    assert scaffold_module in plan.task.allowed_imports
    assert hidden_proof_module not in plan.task.allowed_imports
    assert scaffold_file in plan.task.public_source_files
    assert nae_tm_file in plan.task.public_source_files
    assert sat_tm_file in plan.task.public_source_files
    assert list_file in plan.task.public_source_files
    assert encoding_transport_file in plan.task.public_source_files
    assert finite_domain_file in plan.task.public_source_files
    assert {
        f"{scaffold_module}.clauseFirst_tmPolyTime",
        f"{scaffold_module}.clauseSecond_tmPolyTime",
        f"{scaffold_module}.clauseThird_tmPolyTime",
        f"{scaffold_module}.complementLiteral_tmPolyTime",
        f"{scaffold_module}.literalKeyAfter_tmPolyTime",
        f"{scaffold_module}.complementKeyAfter_tmPolyTime",
        f"{scaffold_module}.ternaryConstraintCode_tmPolyTime",
        "ComplexityReduction.TMPolyTimeMap.list_singleton_of",
        "ComplexityReduction.TMPolyTimeMap.list_cons_of",
        "ComplexityReduction.Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code",
    }.issubset(plan.task.allowed_primitives)
    assert all(
        hidden_proof_module not in item
        for item in (
            *plan.task.allowed_primitives,
            *plan.task.public_source_files,
        )
    )
    assert [node.node_id for node in plan.task.gap_nodes] == [
        "clause-constraint",
        "complement-constraint",
        "clause-gadget",
        "reference-executable",
        "reduction-executable",
        "clause-gadget-direct-tm",
        "reference-direct-tm",
        "direct-tm",
        "reduction-primitive",
        "poly-program",
        "program-run-coherence",
        "reference-semantic-forward",
        "reference-semantic-reverse",
        "semantic-forward",
        "semantic-reverse",
        "semantic-iff",
    ]
    primitive_layers = dict(plan.task.allowed_primitive_layers)
    assert tuple(primitive_layers) == (
        "construction",
        "core",
        "direct_tm",
        "semantic",
    )
    assert set().union(*(set(items) for items in primitive_layers.values())) == set(
        plan.task.allowed_primitives
    )
    assert sum(len(items) for items in primitive_layers.values()) == len(
        plan.task.allowed_primitives
    )
    assert f"{scaffold_module}.ternaryConstraint" in primitive_layers[
        "construction"
    ]
    assert "ComplexityReduction.TMPolyTimeMap.fst" in primitive_layers[
        "direct_tm"
    ]
    assert "ComplexityReduction.SAT.Literal.eval" in primitive_layers["semantic"]
    assert "ComplexityReduction.CSP.Formula.Satisfies" in primitive_layers[
        "semantic"
    ]

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
    assert scaffold_file in prompt["public_sources"]
    assert prompt["public_source_context"]["source_character_budget"] == (
        NP_HARD_REFERENCE_STAGE_PROMPT_SOURCE_CHAR_BUDGET
    )
    assert not any(
        path.endswith("Problems/Karp21/Satisfiability.lean")
        for path in prompt["public_sources"]
    )
    scaffold_source = prompt["public_sources"][scaffold_file]
    assert "referenceExecutableFromClauseGadget" in scaffold_source
    assert (
        f"{scaffold_module}.threeSATToNAEThreeSATIngress.executable"
        in prompt["allowed_primitive_exact_types"]
    )
    assert "theorem clausePayload_tmPolyTime" not in scaffold_source
    assert "PositiveNAE3CSP.executable" not in scaffold_source
    assert "PositiveNAE3CSP.executable_tmPolyTime" not in scaffold_source
    assert "PositiveNAE3CSP.executable_correct" not in scaffold_source
    assert prompt["recommended_first_body"] is None
    assert prompt["active_primitive_layers"] == ["core", "construction"]
    assert set(prompt["node_request"]["allowed_primitives"]) == (
        set(primitive_layers["core"]) | set(primitive_layers["construction"])
    )
    assert "ComplexityReduction.TMPolyTimeMap.fst" not in prompt[
        "allowed_primitive_exact_types"
    ]
    assert "ComplexityReduction.SAT.Literal.eval" not in prompt[
        "allowed_primitive_exact_types"
    ]

    accepted_bodies = {
        node.declaration: f"by\n  -- accepted {node.node_id}\n  trivial\n"
        for node in plan.task.gap_nodes[:5]
    }
    accepted = tuple(
        AcceptedCapabilityNodeV1(
            node_id=node.node_id,
            declaration=node.declaration,
            body_sha256=sha256_id(accepted_bodies[node.declaration]),
            cumulative_source_sha256="sha256:" + "1" * 64,
            publication_manifest_sha256="sha256:" + "2" * 64,
            worker_evidence_sha256="sha256:" + "3" * 64,
            fresh_core_evidence_sha256="sha256:" + "4" * 64,
        )
        for node in plan.task.gap_nodes[:5]
    )
    direct_tm_request = _node_request(
        task=plan.task,
        node_ordinal=6,
        dependency_snapshot=plan.task.dependency_hashes,
        accepted=accepted,
        total_model_calls=5,
        instance_call_budget=64,
    )
    direct_tm_prompt = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=plan.task,
            request=direct_tm_request,
            accepted_bodies=accepted_bodies,
            diagnostic=None,
        )
    )
    direct_tm_scaffold = direct_tm_prompt["public_sources"][scaffold_file]
    for stable_entry in (
        "clauseFirst_tmPolyTime",
        "clauseSecond_tmPolyTime",
        "clauseThird_tmPolyTime",
        "literalKeyAfter_tmPolyTime",
        "complementKeyAfter_tmPolyTime",
        "constraintPayload_tmPolyTime",
        "ternaryConstraintCode_tmPolyTime",
        "list_singleton_of",
        "list_cons_of",
        "formula_tmPolyTime_of_code",
    ):
        assert any(
            stable_entry in source
            for source in direct_tm_prompt["public_sources"].values()
        )
    observed_fst_type = direct_tm_prompt["allowed_primitive_exact_types"][
        "ComplexityReduction.TMPolyTimeMap.fst"
    ]
    assert "ComplexityReduction.EncodedType" in observed_fst_type
    assert "ComplexityReduction.TMPolyTimeMap" in observed_fst_type
    assert "clauseFirst_tmPolyTime" in direct_tm_prompt[
        "active_capability_guidance"
    ]
    assert "by intro input; rfl" in direct_tm_prompt[
        "active_capability_guidance"
    ]
    assert direct_tm_prompt["active_primitive_layers"] == [
        "core",
        "construction",
        "direct_tm",
    ]
    assert "ComplexityReduction.SAT.Literal.eval" not in direct_tm_prompt[
        "allowed_primitive_exact_types"
    ]
    assert "ComplexityReduction.CSP.Formula.Satisfies" not in direct_tm_prompt[
        "allowed_primitive_exact_types"
    ]

    semantic_bodies = {
        node.declaration: f"by\n  -- accepted {node.node_id}\n  trivial\n"
        for node in plan.task.gap_nodes[:11]
    }
    semantic_accepted = tuple(
        AcceptedCapabilityNodeV1(
            node_id=node.node_id,
            declaration=node.declaration,
            body_sha256=sha256_id(semantic_bodies[node.declaration]),
            cumulative_source_sha256="sha256:" + "5" * 64,
            publication_manifest_sha256="sha256:" + "6" * 64,
            worker_evidence_sha256="sha256:" + "7" * 64,
            fresh_core_evidence_sha256="sha256:" + "8" * 64,
        )
        for node in plan.task.gap_nodes[:11]
    )
    semantic_request = _node_request(
        task=plan.task,
        node_ordinal=12,
        dependency_snapshot=plan.task.dependency_hashes,
        accepted=semantic_accepted,
        total_model_calls=11,
        instance_call_budget=64,
    )
    from agent.hardness.np_hard_authoring import NPHardSemanticPlanV1
    from agent.hardness.np_hard_semantic_planner import (
        build_semantic_planner_prompt,
    )

    semantic_plan_prompt, _ = build_semantic_planner_prompt(
        root=ROOT,
        task=plan.task,
        accepted_bodies=semantic_bodies,
    )
    semantic_plan = NPHardSemanticPlanV1.from_dict(
        json.loads(semantic_plan_prompt)["output_template"]
    )

    semantic_prompt = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=plan.task,
            request=semantic_request,
            accepted_bodies=semantic_bodies,
            diagnostic=None,
            semantic_plan=semantic_plan,
        )
    )
    assert semantic_prompt["active_primitive_layers"] == [
        "core",
        "construction",
        "semantic",
    ]
    assert "Follow the checked semantic_plan exactly" in semantic_prompt[
        "active_capability_guidance"
    ]
    assert "Formula.Satisfies" in semantic_prompt[
        "active_capability_guidance"
    ]
    assert "literal" in semantic_prompt[
        "active_capability_guidance"
    ]
    assert "introduction_lemma" in semantic_prompt[
        "active_capability_guidance"
    ]
    semantic_types = semantic_prompt["allowed_primitive_exact_types"]
    for semantic_entry in (
        "ComplexityReduction.SAT.Literal.eval",
        "ComplexityReduction.SAT.Literal.positive",
        "ComplexityReduction.CSP.Constraint.Satisfies",
        "ComplexityReduction.CSP.Formula.Satisfies",
        "ComplexityReduction.Domain.ThreeSATToNAEThreeSAT.literalKey_injective",
        f"{scaffold_module}.complementLiteral_eval",
        f"{scaffold_module}.ternaryConstraint_satisfies_iff",
        f"{scaffold_module}.ternaryConstraint_repeat_satisfies_iff",
        f"{scaffold_module}.ternaryConstraint_repeat_first_satisfies_iff",
        f"{scaffold_module}.ternaryConstraint_repeat_second_satisfies_iff",
        f"{scaffold_module}.bool_ne_iff_eq_not",
        f"{scaffold_module}.literalAssignment_literalKey",
        "ComplexityReduction.NAEThreeSAT.Formula.satisfies_cons",
        "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro",
        "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim",
    ):
        assert semantic_entry in semantic_types
    assert "ComplexityReduction.CSP.Formula.satisfies_cons" not in semantic_types
    assert "ComplexityReduction.CSP.Formula.satisfies_flatMap" not in semantic_types
    assert f"{scaffold_module}.literal_eval_positiveKeyAssignment" not in semantic_types
    assert "ComplexityReduction.TMPolyTimeMap.fst" not in semantic_types
    serialized_semantic_prompt = json.dumps(semantic_prompt, sort_keys=True)
    for excluded in (
        "TMPolyTimeMap",
        "formulaCode",
        "constraintCode",
        "Primitive",
        "PolyProg",
        "clause-gadget-direct-tm",
        "reference-direct-tm",
        "direct-tm",
        "program-run-coherence",
    ):
        assert excluded not in serialized_semantic_prompt
    assert semantic_prompt["public_source_context"][
        "complete_dependency_hashes_remain_in_node_request"
    ] is False
    assert (
        "ComplexityReduction.Presentation.FiniteDomainCSPTable."
        "formula_tmPolyTime_of_code"
    ) not in semantic_types
    assert "ComplexityReduction.TMPolyTimeMap.fst" not in semantic_prompt[
        "node_request"
    ]["allowed_primitives"]
    assert len(semantic_types) < len(plan.task.allowed_primitive_exact_types)
    assert all(
        hidden_proof_module not in source
        for source in semantic_prompt["public_sources"].values()
    )
    assert all(
        "theorem clausePayload_tmPolyTime" not in source
        and "theorem formula_tmPolyTime" not in source
        for source in semantic_prompt["public_sources"].values()
    )

    model_authored_capabilities = {
        "clause_constraint",
        "complement_constraint",
        "clause_gadget",
        "reference_executable",
        "reduction_executable",
        "clause_gadget_direct_tm",
        "reference_direct_tm",
        "direct_tm",
        "reference_semantic_forward",
        "reference_semantic_reverse",
        "semantic_forward",
        "semantic_reverse",
    }
    for node in plan.task.gap_nodes:
        body = _recommended_first_body(
            task=plan.task,
            request=SimpleNamespace(node=node),
            public_sources={},
        )
        if node.capability in model_authored_capabilities:
            assert body is None


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
