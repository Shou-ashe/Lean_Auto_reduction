from __future__ import annotations

import json
from pathlib import Path

import pytest

from agent.hardness.models import CommandResult, sha256_id
from agent.hardness.np_hard_authoring import (
    _NP_HARD_EXACT_STAGED_TASK_BOUNDARIES_V2,
    _NP_HARD_EXACT_STAGED_TASK_MOTIFS_V2,
)
from agent.hardness.np_hard_authoring_planner import (
    NPHardAuthoringPlannerError,
    exact_edge_construction_gap_nodes,
)
from agent.hardness.np_hard_exact_edge_authoring import (
    EXACT_EDGE_AUTHORING_TASK_CLASS,
    EXACT_EDGE_NODE_CHECKPOINT_SCHEMA_V1,
    EXACT_EDGE_NODE_PATCH_SCHEMA_V1,
    EXACT_EDGE_NODE_PROMPT_SCHEMA_V1,
    EXACT_EDGE_STAGED_RESULT_SCHEMA_V1,
    ExactEdgeAuthoringError,
    build_exact_edge_node_prompt,
    build_typed_exact_edge_task,
    exact_edge_candidate_source,
    load_exact_edge_checkpoint,
    parse_exact_edge_node_patch,
    run_exact_edge_staged_construction,
    write_exact_edge_checkpoint,
)

import agent.hardness.np_hard_exact_edge_authoring as authoring_module  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]

SOURCE = "ComplexityReduction.Presentation.UndirectedHamiltonianCircuit.structuredProblem"
TARGET = "ComplexityReduction.Presentation.DirectedHamiltonianCircuit.structuredProblem"
PUBLIC_SOURCES = (
    "Lean/Reference/ComplexityReduction/Presentation/UndirectedHamiltonianCircuit.lean",
    "Lean/Reference/ComplexityReduction/Presentation/DirectedHamiltonianCircuit.lean",
)
POLICY = {
    "mode": "direct_new_edge",
    "allow_composition": False,
    "require_new_primitive": True,
}
STATEMENT = (
    "Construct a certified reduction from structured Undirected Hamiltonian "
    "Circuit to structured Directed Hamiltonian Circuit."
)
STATEMENT_HASH = "sha256:" + "0" * 64


def _task() -> object:
    return build_typed_exact_edge_task(
        root=ROOT,
        input_module="ComplexityReduction.Presentation.DirectedHamiltonianCircuit",
        source_declaration=SOURCE,
        target_declaration=TARGET,
        policy=POLICY,
        public_source_files=PUBLIC_SOURCES,
        timeout_seconds=60,
    )


class FakeModel:
    def __init__(self, bodies: dict[str, str] | None = None, *, always: str | None = None):
        self.bodies = bodies or {}
        self.always = always
        self.calls: list[str] = []

    def complete_json(self, *, system: str, prompt: str):
        payload = json.loads(prompt)
        node_id = payload["node"]["node_id"]
        self.calls.append(node_id)
        body = self.always if self.always is not None else self.bodies[node_id]
        return type(
            "Response",
            (),
            {
                "called": True,
                "ok": True,
                "content": json.dumps(
                    {
                        "schema_version": EXACT_EDGE_NODE_PATCH_SCHEMA_V1,
                        "action": "submit_node_patch",
                        "request_id": payload["response_template"]["request_id"],
                        "node_id": node_id,
                        "declaration": payload["response_template"]["declaration"],
                        "dependency_fingerprint": payload["response_template"][
                            "dependency_fingerprint"
                        ],
                        "replacement_body": body,
                    }
                ),
                "error": None,
                "status_code": 200,
                "duration_seconds": 0.1,
                "usage": {"prompt_tokens": 100, "completion_tokens": 50, "total_tokens": 150},
                "attempts": 1,
                "finish_reason": "stop",
            },
        )()


def _ok_command() -> CommandResult:
    return CommandResult(
        command=["lake", "env", "lean", "x.lean"],
        exit_code=0,
        timed_out=False,
        stdout="ok",
        stderr="",
        duration_seconds=0.1,
    )


def _fail_command(declaration: str) -> CommandResult:
    return CommandResult(
        command=["lake", "env", "lean", "x.lean"],
        exit_code=1,
        timed_out=False,
        stdout="",
        stderr=f"error: unknown identifier {declaration}",
        duration_seconds=0.1,
    )


def test_planner_freezes_exact_edge_construction_dag() -> None:
    nodes = exact_edge_construction_gap_nodes()
    ids = [node["id"] for node in nodes]
    assert ids == [
        "parameter-normalization",
        "reduction-primitive",
        "gadget-definitions",
        "output-wellformed",
        "polynomial-bound",
        "poly-program",
        "program-direct-tm-coherence",
        "semantic-forward",
        "semantic-reverse",
        "semantic-iff",
        "certified-reduction",
    ]
    motif = tuple(
        (node["id"], node["depends_on"]) for node in nodes
    )
    expected_motif = _NP_HARD_EXACT_STAGED_TASK_MOTIFS_V2[
        EXACT_EDGE_AUTHORING_TASK_CLASS
    ]
    assert motif == tuple((node_id, list(depends)) for node_id, _, depends in expected_motif)
    depended_on = {dependency for node in nodes for dependency in node["depends_on"]}
    assert set(ids) - depended_on == {"certified-reduction"}


def test_exact_edge_task_validation_freezes_single_sink_terminal() -> None:
    task = _task()
    assert task.task_class == EXACT_EDGE_AUTHORING_TASK_CLASS
    assert task.terminal_node_id == "certified-reduction"
    assert task.final_program_node_id == "poly-program"
    assert task.final_candidate_declaration.endswith(".authoredForwardReduction")
    assert _NP_HARD_EXACT_STAGED_TASK_BOUNDARIES_V2[
        EXACT_EDGE_AUTHORING_TASK_CLASS
    ] == ("certified-reduction", "poly-program")


def test_exact_edge_prompt_is_answer_free_and_binds_case() -> None:
    task = _task()
    prompt = build_exact_edge_node_prompt(
        task=task,
        node=task.gap_nodes[0],
        accepted_bodies={},
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        diagnostic="previous lean failure",
        attempt=1,
        remaining_attempts=3,
        timeout_seconds=60,
    )
    payload = json.loads(prompt)
    assert payload["schema_version"] == EXACT_EDGE_NODE_PROMPT_SCHEMA_V1
    assert "recommended_first_body" not in prompt.lower()
    assert payload["case"]["statement"] == STATEMENT
    assert payload["case"]["statement_hash"] == STATEMENT_HASH
    assert payload["node"]["node_id"] == "parameter-normalization"
    assert payload["policy"]["route_import_forbidden"] is True
    assert payload["policy"]["no_answer_material_in_prompt"] is True
    for forbidden in ("solution", "hint", "gold", "oracle", "problems.7z"):
        assert forbidden not in prompt.lower()


def test_exact_edge_prompt_rejects_oracle_material_in_statement() -> None:
    task = _task()
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        build_exact_edge_node_prompt(
            task=task,
            node=task.gap_nodes[0],
            accepted_bodies={},
            policy=POLICY,
            statement="Use the archived solution from problems.7z.",
            statement_hash=STATEMENT_HASH,
            diagnostic=None,
            attempt=1,
            remaining_attempts=3,
            timeout_seconds=60,
        )
    assert raised.value.code == "oracle_or_gold_import"


def test_exact_edge_node_patch_parser_fail_closed() -> None:
    task = _task()
    node = task.gap_nodes[1]
    body = "fun input => input"
    valid = {
        "schema_version": EXACT_EDGE_NODE_PATCH_SCHEMA_V1,
        "action": "submit_node_patch",
        "request_id": task.request_id,
        "node_id": node.node_id,
        "declaration": node.declaration,
        "dependency_fingerprint": task.dependency_fingerprint,
        "replacement_body": body,
    }
    assert parse_exact_edge_node_patch(content=json.dumps(valid), task=task, node=node) == body

    mutated = {**valid, "node_id": "certified-reduction"}
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        parse_exact_edge_node_patch(content=json.dumps(mutated), task=task, node=node)
    assert raised.value.code == "candidate_dependency_stale"

    mutated = {**valid, "replacement_body": "by sorry"}
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        parse_exact_edge_node_patch(content=json.dumps(mutated), task=task, node=node)
    assert raised.value.code == "candidate_nonstandard_axiom"

    mutated = {**valid, "request_id": "sha256:" + "1" * 64}
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        parse_exact_edge_node_patch(content=json.dumps(mutated), task=task, node=node)
    assert raised.value.code == "candidate_dependency_stale"

    mutated = {**valid, "extra_field": 1}
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        parse_exact_edge_node_patch(content=json.dumps(mutated), task=task, node=node)
    assert raised.value.code == "invalid_np_hard_exact_edge_schema"


def test_exact_edge_candidate_source_renders_package_and_final_wrapper() -> None:
    task = _task()
    bodies = {node.declaration: "fun input => input" for node in task.gap_nodes}
    source = exact_edge_candidate_source(task=task, bodies=bodies, include_final=True)
    assert "structure CertifiedReductionPackage where" in source
    assert "noncomputable def certifiedReduction :" in source
    assert "authoredForwardReduction" in source
    assert f"CertifiedReduction\n      {SOURCE}\n      {TARGET}" in source
    assert "assert_standard_axioms" in source
    assert source.count("noncomputable def") == len(task.gap_nodes) + 1


def test_exact_edge_checkpoint_round_trip_and_tamper_detection(tmp_path: Path) -> None:
    task = _task()
    path = tmp_path / "checkpoint.json"
    checkpoint_sha = write_exact_edge_checkpoint(
        path=path, task=task, accepted=[], bodies={}, calls=[]
    )
    accepted, bodies, calls = load_exact_edge_checkpoint(path=path, task=task)
    assert accepted == () and bodies == {} and calls == ()
    assert checkpoint_sha.startswith("sha256:")

    raw = json.loads(path.read_text(encoding="utf-8"))
    raw["accepted_nodes"] = [
        {
            "node_id": "reduction-primitive",
            "declaration": task.gap_nodes[1].declaration,
            "body_sha256": sha256_id("x"),
            "cumulative_source_sha256": "sha256:" + "0" * 64,
            "workspace_sha256": "sha256:" + "0" * 64,
            "command_exit_code": 0,
        }
    ]
    path.write_text(json.dumps(raw), encoding="utf-8")
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        load_exact_edge_checkpoint(path=path, task=task)
    assert raised.value.code == "checkpoint_tampered"


def _monkeypatch_compile(monkeypatch, *, ok: bool = True):
    def fake_run_command(command, *, cwd, timeout_seconds, **kwargs):
        assert command[:3] == ["lake", "env", "lean"]
        source = Path(command[3])
        if "deletion-audits" in source.as_posix() and "without-" in source.name:
            node_id = source.stem.removeprefix("without-")
            node = next(
                (n for n in _task().gap_nodes if n.node_id == node_id), None
            )
            return _fail_command(node.declaration if node is not None else "Missing")
        if not source.is_file():
            return _fail_command("Missing")
        return _ok_command() if ok else _fail_command("Generated.Missing")

    monkeypatch.setattr(authoring_module, "run_command", fake_run_command)


def test_staged_executor_verifies_with_per_node_real_calls(tmp_path: Path, monkeypatch) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    case_output = tmp_path / "out"
    model = FakeModel(bodies={node.node_id: "fun input => input" for node in task.gap_nodes})
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
    )
    assert payload["schema_version"] == EXACT_EDGE_STAGED_RESULT_SCHEMA_V1
    assert payload["status"] == "VERIFIED"
    assert payload["failure_code"] is None
    assert len(model.calls) == 11
    assert model.calls == [node.node_id for node in task.gap_nodes]
    ledger = payload["model_calls"]
    assert all(call["called"] is True for call in ledger)
    assert all(call["protocol_accepted"] is True for call in ledger)
    assert all(call["status_code"] == 200 for call in ledger)
    for call in ledger:
        prompt_file = Path(call["prompt_file"])
        response_file = Path(call["response_file"])
        assert prompt_file.is_file() and response_file.is_file()
    assert payload["authored_candidate_declaration"].endswith(".authoredForwardReduction")
    assert (case_output / "ExactEdge.lean").is_file()
    assert (case_output / "checkpoint.json").is_file()
    audits = payload["audits"]
    assert all(audits[name]["ok"] is True for name in (
        "kernel", "replay", "axiom", "endpoint", "dependency",
        "program_direct_tm_coherence", "semantic_iff", "polynomial_bound",
    ))


def test_staged_executor_exhausts_node_attempt_budget(tmp_path: Path, monkeypatch) -> None:
    def fake_run_command(command, *, cwd, timeout_seconds, **kwargs):
        return _fail_command("Generated.Missing")

    monkeypatch.setattr(authoring_module, "run_command", fake_run_command)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    case_output = tmp_path / "out"
    model = FakeModel(bodies={node.node_id: "fun input => input" for node in task.gap_nodes})
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        attempt_budget=4,
    )
    assert payload["status"] == "FAILED"
    assert len(model.calls) == 4
    assert payload["accepted_nodes"] == []
    ledger = payload["model_calls"]
    assert sum(call["called"] is True for call in ledger) == 4
    assert all(call["protocol_accepted"] is False for call in ledger)


def test_staged_executor_rejects_route_import_without_compromise(tmp_path: Path, monkeypatch) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    case_output = tmp_path / "out"
    bodies = {node.node_id: "fun input => input" for node in task.gap_nodes}
    bodies[task.gap_nodes[1].node_id] = (
        "import ComplexityReduction.Routes.ThreeSATToClique\nfun input => input"
    )
    model = FakeModel(bodies=bodies)
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
    )
    assert payload["status"] == "FAILED"
    assert payload["failure_code"] == "exact_edge_route_import_forbidden"


def test_staged_executor_blocks_without_model_client(tmp_path: Path, monkeypatch) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=tmp_path / "out",
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=None,
        model_name=None,
        timeout_seconds=60,
    )
    assert payload["status"] == "FAILED"
    assert payload["failure_code"] == "model_provider_unavailable"
    assert payload["model_calls"] == []
