from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.lean_runner import module_file, sha256_file
from agent.hardness.np_hard_authoring import (
    NP_HARD_AUTHORING_PATCH_SCHEMA_V2,
    NP_HARD_AUTHORING_RESULT_SCHEMA_V2,
    NP_HARD_AUTHORING_TASK_SCHEMA_V2,
    NPHardAuthoringContractError,
    NPHardAuthoringResultV2,
    NPHardAuthoringTaskV2,
    accepted_np_hard_authoring_result_v2,
    build_np_hard_authoring_prompt_v2,
    build_np_hard_authoring_tasks_v2,
    parse_np_hard_authoring_patch_v2,
)
from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Gate" / "Suites" / "np_hard_generalization.json"
H_J_5_CASES = (
    (
        "ComplexityReduction.Presentation.MaxCut",
        "ComplexityReduction.Presentation.MaxCut.structuredProblem",
    ),
    (
        "ComplexityReduction.Presentation.MaxCutBinary",
        "ComplexityReduction.Presentation.MaxCutBinary.binaryStructuredProblem",
    ),
)


@pytest.fixture(scope="module")
def tasks() -> tuple[NPHardAuthoringTaskV2, ...]:
    return build_np_hard_authoring_tasks_v2(root=ROOT, suite_path=SUITE)


@pytest.fixture(scope="module")
def h_j_5_tasks(tmp_path_factory) -> tuple[NPHardAuthoringTaskV2, ...]:
    output = tmp_path_factory.mktemp("np-hard-h-j-5-authoring")
    return tuple(
        NPHardAuthoringPlannerV2(
            root=ROOT,
            input_module=module,
            input_problem_declaration=problem,
            output_dir=output / f"case-{index}",
        ).plan().task
        for index, (module, problem) in enumerate(H_J_5_CASES)
    )


def _reissue_task(task: NPHardAuthoringTaskV2, **changes) -> NPHardAuthoringTaskV2:
    provisional = replace(
        task,
        **changes,
        request_id="sha256:" + "0" * 64,
    )
    return replace(provisional, request_id=provisional.computed_request_id)


def _patch_payload(task: NPHardAuthoringTaskV2) -> dict:
    return {
        "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V2,
        "action": "submit_patch",
        "request_id": task.request_id,
        "task_class": task.task_class,
        "required_direction": task.required_direction,
        "source_problem": task.source_problem.to_dict(),
        "target_problem": task.target_problem.to_dict(),
        "dependency_fingerprint": task.dependency_fingerprint,
        "replacement_bodies": {
            declaration: "by\n  simp" for declaration in task.editable_declarations
        },
    }


def test_v2_projects_exact_b1_b2_b3_matrix(tasks) -> None:
    assert len(tasks) == 5
    assert [task.task_class for task in tasks] == [
        "semantic_proof",
        "semantic_proof",
        "program_composition",
        "program_composition",
        "program_synthesis",
    ]
    assert [len(task.gap_nodes) for task in tasks] == [1, 2, 2, 2, 5]
    assert [task.terminal_node_id for task in tasks] == [
        "semantic-proof",
        "semantic-iff",
        "semantic-proof",
        "semantic-proof",
        "semantic-iff",
    ]
    assert [task.final_program_node_id for task in tasks] == [
        None,
        None,
        "composed-program",
        "composed-program",
        "poly-program",
    ]
    assert all(not task.observed_capability_terms for task in tasks)
    assert all(not task.observed_capability_exact_types for task in tasks)
    synthesis = tasks[-1]
    assert [node.capability for node in synthesis.gap_nodes] == [
        "reduction_executable",
        "poly_program",
        "program_run_coherence",
        "mapping_invariant",
        "semantic_proof",
    ]
    assert synthesis.final_exact_type == (
        "ComplexityReduction.Certificate.CertifiedReduction "
        f"{synthesis.source_problem.term} {synthesis.target_problem.term}"
    )


def test_v2_task_and_result_round_trip(tasks) -> None:
    for task in tasks:
        payload = task.to_dict()
        assert payload["schema_version"] == NP_HARD_AUTHORING_TASK_SCHEMA_V2
        assert not {
            "observed_capability_terms",
            "observed_capability_exact_types",
            "terminal_node_id",
            "final_program_node_id",
        } & set(payload)
        restored = NPHardAuthoringTaskV2.from_dict(json.loads(json.dumps(payload)))
        assert restored == task

        hashes = {node.node_id: sha256_id(node.declaration) for node in task.gap_nodes}
        result = accepted_np_hard_authoring_result_v2(
            task=task,
            candidate_hashes=hashes,
            final_certificate=sha256_id("final:" + task.request_id),
            replay_certificate=sha256_id("replay:" + task.request_id),
        )
        result_payload = result.to_dict(task)
        assert result_payload["schema_version"] == NP_HARD_AUTHORING_RESULT_SCHEMA_V2
        assert NPHardAuthoringResultV2.from_dict(result_payload, task=task) == result


def test_h_j_5_exact_staged_tasks_round_trip(h_j_5_tasks) -> None:
    structured, binary = h_j_5_tasks
    assert structured.task_class == "typed_gadget_indexed_admission_dag"
    assert binary.task_class == "typed_tmkarp_dependent_composition_dag"
    assert len(structured.gap_nodes) == 10
    assert len(binary.gap_nodes) == 5
    assert structured.terminal_node_id == "gadget-composed-semantic-iff"
    assert structured.final_program_node_id == "gadget-composed-program"
    assert binary.terminal_node_id == "composed-semantic-iff"
    assert binary.final_program_node_id == "composed-program"
    assert binary.composition_intermediate is not None
    assert binary.composition_successor_source == binary.composition_intermediate.term
    assert binary.composition_successor_target == binary.target_problem.term
    admission_observation = dict(binary.composition_admission_observation or ())
    successor_observation = dict(binary.composition_successor_observation or ())
    assert admission_observation["target"] == binary.composition_intermediate.term
    assert successor_observation["source"] == binary.composition_intermediate.term
    assert successor_observation["target"] == binary.target_problem.term
    assert (
        admission_observation["target_node"]
        == successor_observation["source_node"]
    )
    for task in h_j_5_tasks:
        payload = task.to_dict()
        restored = NPHardAuthoringTaskV2.from_dict(
            json.loads(json.dumps(payload))
        )
        assert restored == task
        assert restored.request_id == task.request_id


def test_h_j_5_contract_rejects_coherent_successor_and_motif_mutations(
    h_j_5_tasks,
) -> None:
    structured, binary = h_j_5_tasks
    exact_types = dict(binary.observed_capability_exact_types)
    exact = exact_types["composed-program"]
    head, source, target = exact.split()

    def mutate_exact(value: str) -> NPHardAuthoringTaskV2:
        observed = dict(binary.observed_capability_exact_types)
        observed["composed-program"] = value
        dependencies = dict(binary.dependency_hashes)
        dependencies[
            "content:observed-capability-exact-type:composed-program"
        ] = sha256_id(value)
        return _reissue_task(
            binary,
            observed_capability_exact_types=tuple(sorted(observed.items())),
            dependency_hashes=tuple(sorted(dependencies.items())),
        )

    invalid_exact_types = (
        f"{head} {target} {source}",
        f"{head} Example.Wrong.sourceProblem {target}",
        f"{head} {source} Example.Wrong.targetProblem",
        f"Example.Wrapper ({exact})",
    )
    for mutated_exact_type in invalid_exact_types:
        with pytest.raises(NPHardAuthoringContractError) as captured:
            mutate_exact(mutated_exact_type).validate()
        assert captured.value.code == "candidate_exact_type_mismatch"

    primitive_exact_types = dict(binary.observed_capability_exact_types)
    primitive_exact = primitive_exact_types["tmkarp-primitive"]
    primitive_head, primitive_source, primitive_target = primitive_exact.split()

    def mutate_tmkarp_exact(value: str) -> NPHardAuthoringTaskV2:
        observed = dict(binary.observed_capability_exact_types)
        observed["tmkarp-primitive"] = value
        dependencies = dict(binary.dependency_hashes)
        dependencies[
            "content:observed-capability-exact-type:tmkarp-primitive"
        ] = sha256_id(value)
        return _reissue_task(
            binary,
            observed_capability_exact_types=tuple(sorted(observed.items())),
            dependency_hashes=tuple(sorted(dependencies.items())),
        )

    invalid_tmkarp_types = (
        f"{primitive_head} {primitive_target} {primitive_source}",
        (
            f"{primitive_head} {primitive_target} {primitive_source} "
            f"{primitive_source} {primitive_target}"
        ),
        f"Example.Wrapper ({primitive_exact})",
    )
    for mutated_exact_type in invalid_tmkarp_types:
        with pytest.raises(NPHardAuthoringContractError) as captured:
            mutate_tmkarp_exact(mutated_exact_type).validate()
        assert captured.value.code == "candidate_exact_type_mismatch"

    gadget_exact_types = dict(structured.observed_capability_exact_types)
    gadget_exact = gadget_exact_types["gadget-reference-audit"]
    gadget_head, gadget_source, gadget_reference, gadget_target = (
        gadget_exact.split()
    )

    def mutate_gadget_exact(value: str) -> NPHardAuthoringTaskV2:
        observed = dict(structured.observed_capability_exact_types)
        observed["gadget-reference-audit"] = value
        dependencies = dict(structured.dependency_hashes)
        dependencies[
            "content:observed-capability-exact-type:gadget-reference-audit"
        ] = sha256_id(value)
        return _reissue_task(
            structured,
            observed_capability_exact_types=tuple(sorted(observed.items())),
            dependency_hashes=tuple(sorted(dependencies.items())),
        )

    invalid_gadget_types = (
        f"{gadget_head} {gadget_target} {gadget_reference} {gadget_source}",
        (
            f"{gadget_head} {gadget_target} {gadget_reference} {gadget_source} "
            f"{gadget_source} {gadget_reference} {gadget_target}"
        ),
        f"Example.Wrapper ({gadget_exact})",
    )
    for mutated_exact_type in invalid_gadget_types:
        with pytest.raises(NPHardAuthoringContractError) as captured:
            mutate_gadget_exact(mutated_exact_type).validate()
        assert captured.value.code == "candidate_exact_type_mismatch"

    observed_terms = dict(binary.observed_capability_terms)
    old_successor = observed_terms["composed-program"]
    fake_successor = "Example.Unrelated.fakeCertifiedReduction"
    observed_terms["composed-program"] = fake_successor
    dependencies = dict(binary.dependency_hashes)
    dependencies["content:observed-capability-term:composed-program"] = sha256_id(
        fake_successor
    )
    fake_witness_task = _reissue_task(
        binary,
        observed_capability_terms=tuple(sorted(observed_terms.items())),
        dependency_hashes=tuple(sorted(dependencies.items())),
        allowed_primitives=tuple(
            fake_successor if item == old_successor else item
            for item in binary.allowed_primitives
        ),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        fake_witness_task.validate()
    assert captured.value.code == "fabricated_declaration_handle"

    assert structured.composition_intermediate is not None
    unrelated_intermediate = structured.composition_intermediate
    observed = dict(binary.observed_capability_exact_types)
    unrelated_tmkarp_exact = (
        f"{primitive_head} {primitive_source} "
        f"{unrelated_intermediate.term}.toEncodedDecisionProblem"
    )
    observed["tmkarp-primitive"] = unrelated_tmkarp_exact
    dependencies = dict(binary.dependency_hashes)
    dependencies[
        "content:observed-capability-exact-type:tmkarp-primitive"
    ] = sha256_id(unrelated_tmkarp_exact)
    dependencies[f"module:{unrelated_intermediate.module}"] = (
        "sha256:" + "0" * 64
    )
    unrelated_chain = _reissue_task(
        binary,
        composition_intermediate=unrelated_intermediate,
        observed_capability_exact_types=tuple(sorted(observed.items())),
        dependency_hashes=tuple(sorted(dependencies.items())),
        allowed_imports=tuple(
            dict.fromkeys((*binary.allowed_imports, unrelated_intermediate.module))
        ),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        unrelated_chain.validate()
    assert captured.value.code == "candidate_outside_edit_boundary"

    admission_observation = dict(binary.composition_admission_observation or ())
    admission_observation["target"] = "Example.Wrong.intermediate"
    stale_observer_record = _reissue_task(
        binary,
        composition_admission_observation=tuple(
            sorted(admission_observation.items())
        ),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        stale_observer_record.validate()
    assert captured.value.code == "candidate_dependency_stale"

    dependencies = dict(binary.dependency_hashes)
    dependencies["content:lean-typed-capability-chain"] = (
        "sha256:" + "0" * 64
    )
    stale_chain_hash = _reissue_task(
        binary,
        dependency_hashes=tuple(sorted(dependencies.items())),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        stale_chain_hash.validate()
    assert captured.value.code == "candidate_dependency_stale"


def test_h_j_5_contract_rejects_extra_staged_surfaces(h_j_5_tasks) -> None:
    structured, binary = h_j_5_tasks

    def with_extra_import(
        task: NPHardAuthoringTaskV2, module: str
    ) -> NPHardAuthoringTaskV2:
        dependencies = dict(task.dependency_hashes)
        dependencies[f"module:{module}"] = (
            "sha256:" + sha256_file(module_file(ROOT / "Lean", module))
        )
        return _reissue_task(
            task,
            allowed_imports=(*task.allowed_imports, module),
            dependency_hashes=tuple(sorted(dependencies.items())),
        )

    for module in (
        "ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources",
        "ComplexityReduction.Presentation.MaxCutBinary",
        "ComplexityReduction.Domain.NAEThreeSATToMaxCut",
    ):
        with pytest.raises(NPHardAuthoringContractError) as captured:
            with_extra_import(structured, module).validate()
        assert captured.value.code == "candidate_outside_edit_boundary"

    raw_domain_source = (
        "Lean/Reference/ComplexityReduction/Domain/NAEThreeSATToMaxCut.lean"
    )
    dependencies = dict(structured.dependency_hashes)
    dependencies[f"public:{raw_domain_source}"] = (
        "sha256:" + sha256_file(ROOT / raw_domain_source)
    )
    extra_public_source = _reissue_task(
        structured,
        public_source_files=(*structured.public_source_files, raw_domain_source),
        dependency_hashes=tuple(sorted(dependencies.items())),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        extra_public_source.validate()
    assert captured.value.code == "candidate_outside_edit_boundary"

    for module in (
        "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources",
        "ComplexityReduction.Domain.NAEThreeSATToMaxCut",
    ):
        with pytest.raises(NPHardAuthoringContractError) as captured:
            with_extra_import(binary, module).validate()
        assert captured.value.code == "candidate_outside_edit_boundary"

    parameter_node = "gadget-parameter-audit"
    gadget_nodes = tuple(
        replace(
            node,
            depends_on=tuple(
                dependency
                for dependency in node.depends_on
                if dependency != parameter_node
            ),
        )
        for node in structured.gap_nodes
        if node.node_id != parameter_node
    )
    nine_node_gadget = _reissue_task(
        structured,
        gap_nodes=gadget_nodes,
        editable_declarations=tuple(node.declaration for node in gadget_nodes),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        nine_node_gadget.validate()
    assert captured.value.code == "candidate_dependency_stale"

    semantic_node = "tmkarp-semantic-iff"
    dependent_nodes = tuple(
        replace(
            node,
            depends_on=tuple(
                dependency
                for dependency in node.depends_on
                if dependency != semantic_node
            ),
        )
        for node in binary.gap_nodes
        if node.node_id != semantic_node
    )
    four_node_dependent = _reissue_task(
        binary,
        gap_nodes=dependent_nodes,
        editable_declarations=tuple(node.declaration for node in dependent_nodes),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        four_node_dependent.validate()
    assert captured.value.code == "candidate_dependency_stale"


def test_v2_rejects_unknown_request_and_result_versions(tasks) -> None:
    task = tasks[0]
    task_payload = task.to_dict()
    task_payload["schema_version"] = "hardness_np_hard_authoring_task_v999"
    with pytest.raises(NPHardAuthoringContractError) as task_error:
        NPHardAuthoringTaskV2.from_dict(task_payload)
    assert task_error.value.code == "invalid_np_hard_authoring_v2_schema"

    result = accepted_np_hard_authoring_result_v2(
        task=task,
        candidate_hashes={node.node_id: sha256_id(node.node_id) for node in task.gap_nodes},
        final_certificate=sha256_id("final"),
        replay_certificate=sha256_id("replay"),
    ).to_dict(task)
    result["schema_version"] = "hardness_np_hard_authoring_result_v999"
    with pytest.raises(NPHardAuthoringContractError) as result_error:
        NPHardAuthoringResultV2.from_dict(result, task=task)
    assert result_error.value.code == "invalid_np_hard_authoring_v2_schema"


def test_v2_prompt_contains_only_public_contract_data(tasks) -> None:
    for task in tasks:
        prompt = build_np_hard_authoring_prompt_v2(task=task, root=ROOT)
        lowered = prompt.lower()
        assert '"case_id"' not in lowered
        assert '"expected"' not in lowered
        assert ".gold." not in lowered
        assert ".oracles." not in lowered
        assert "goldproof" not in lowered
        assert json.loads(prompt)["task"]["request_id"] == task.request_id


def test_v2_patch_accepts_only_exact_editable_declarations(tasks) -> None:
    task = tasks[-1]
    patch = parse_np_hard_authoring_patch_v2(
        content=json.dumps(_patch_payload(task)), task=task
    )
    assert tuple(name for name, _ in patch.replacement_bodies) == task.editable_declarations
    assert all(body.endswith("\n") for _, body in patch.replacement_bodies)


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    (
        ("direction", "candidate_wrong_direction"),
        ("source", "candidate_wrong_endpoint"),
        ("target", "candidate_wrong_endpoint"),
        ("dependency", "candidate_dependency_stale"),
        ("extra_declaration", "candidate_outside_edit_boundary"),
        ("missing_declaration", "candidate_outside_edit_boundary"),
        ("import", "import_not_allowlisted"),
        ("axiom", "candidate_nonstandard_axiom"),
        ("gold", "oracle_or_gold_import"),
    ),
)
def test_v2_patch_mutations_fail_closed(tasks, mutation: str, expected_code: str) -> None:
    task = tasks[-1]
    payload = _patch_payload(task)
    if mutation == "direction":
        payload["required_direction"] = "target_to_source"
    elif mutation == "source":
        payload["source_problem"]["term"] = "Example.Other.source"
    elif mutation == "target":
        payload["target_problem"]["term"] = "Example.Other.target"
    elif mutation == "dependency":
        payload["dependency_fingerprint"] = "sha256:" + "0" * 64
    elif mutation == "extra_declaration":
        payload["replacement_bodies"]["Generated.Escape.extra"] = "by\n  trivial"
    elif mutation == "missing_declaration":
        payload["replacement_bodies"].pop(task.editable_declarations[0])
    elif mutation == "import":
        payload["replacement_bodies"][task.editable_declarations[0]] = (
            "by\n  import Untrusted.Module"
        )
    elif mutation == "axiom":
        payload["replacement_bodies"][task.editable_declarations[0]] = (
            "by\n  axiom injected : False"
        )
    else:
        payload["replacement_bodies"][task.editable_declarations[0]] = (
            "by\n  exact Benchmark.Hardness.Gold.Secret.answer"
        )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        parse_np_hard_authoring_patch_v2(content=json.dumps(payload), task=task)
    assert captured.value.code == expected_code


def test_v2_task_rejects_forbidden_import_and_stale_dependency(tasks) -> None:
    task = tasks[0]
    forbidden = replace(
        task,
        allowed_imports=task.allowed_imports + ("Benchmark.Hardness.Gold.Secret",),
    )
    with pytest.raises(NPHardAuthoringContractError) as import_error:
        forbidden.validate()
    assert import_error.value.code == "oracle_or_gold_import"

    name, _ = task.dependency_hashes[0]
    stale = replace(
        task,
        dependency_hashes=((name, "sha256:" + "0" * 64),) + task.dependency_hashes[1:],
    )
    with pytest.raises(NPHardAuthoringContractError) as stale_error:
        stale.validate()
    assert stale_error.value.code == "candidate_dependency_stale"


def test_v2_task_terminal_and_final_program_nodes_fail_closed(tasks) -> None:
    composition = tasks[2]
    with pytest.raises(NPHardAuthoringContractError) as terminal_error:
        replace(
            composition,
            terminal_node_id=composition.final_program_node_id,
        ).validate()
    assert terminal_error.value.code == "candidate_dependency_stale"

    with pytest.raises(NPHardAuthoringContractError) as program_error:
        replace(
            composition,
            final_program_node_id=composition.terminal_node_id,
        ).validate()
    assert program_error.value.code == "candidate_exact_type_mismatch"


def test_v2_result_cannot_accept_partial_dag(tasks) -> None:
    task = tasks[-1]
    partial = NPHardAuthoringResultV2(
        request_id=task.request_id,
        outcome="accepted",
        accepted_nodes=(task.gap_nodes[0].node_id,),
        remaining_nodes=tuple(node.node_id for node in task.gap_nodes[1:]),
        candidate_hashes=((task.gap_nodes[0].node_id, sha256_id("candidate")),),
        lean_diagnostics=(),
        policy_diagnostics=(),
        model_calls=(),
        final_certificate=sha256_id("final"),
        replay_certificate=sha256_id("replay"),
    )
    with pytest.raises(NPHardAuthoringContractError) as captured:
        partial.validate(task)
    assert captured.value.code == "candidate_dependency_stale"


def test_formal_v2_contract_report_records_all_task_classes() -> None:
    report_path = ROOT / "Reports" / "NP_HARD_AUTHORING_V2_CONTRACT_REPORT.json"
    if not report_path.is_file():
        pytest.skip("formal G-B report is generated by its dedicated runner")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["passed"] is True
    assert report["metrics"]["task_class_counts"] == {
        "semantic_proof": 2,
        "program_composition": 2,
        "program_synthesis": 1,
    }
    assert report["metrics"]["exact_endpoint_final_count"] == 5
    assert report["metrics"]["independent_replay_count"] == 5
    assert report["metrics"]["prompt_safe_count"] == 5
    assert report["metrics"]["model_calls"] == 0


def test_legacy_v2_request_ids_remain_byte_semantic_compatible(tasks) -> None:
    report = json.loads(
        (
            ROOT
            / "Reports/NP_HARD_AUTHORING_V2_CONTRACT_REPORT.json"
        ).read_text(encoding="utf-8")
    )
    assert [task.request_id for task in tasks] == [
        case["request_id"] for case in report["cases"]
    ]
