from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
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


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "np_hard_generalization.json"


@pytest.fixture(scope="module")
def tasks() -> tuple[NPHardAuthoringTaskV2, ...]:
    return build_np_hard_authoring_tasks_v2(root=ROOT, suite_path=SUITE)


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
    report_path = ROOT / "Benchmark" / "Hardness" / "NP_HARD_AUTHORING_V2_CONTRACT_REPORT.json"
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

