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
    EXACT_EDGE_RUNTIME_MODULE,
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
    assert EXACT_EDGE_RUNTIME_MODULE in task.allowed_imports
    assert "ComplexityReduction.Agent.Hardness.Runtime" not in task.allowed_imports


def test_exact_edge_runtime_surface_is_route_free() -> None:
    pending = [EXACT_EDGE_RUNTIME_MODULE]
    visited: set[str] = set()
    while pending:
        module = pending.pop()
        if module in visited or not module.startswith("ComplexityReduction."):
            continue
        visited.add(module)
        path = ROOT / "Lean/Reference" / (module.replace(".", "/") + ".lean")
        source = path.read_text(encoding="utf-8")
        imports = [
            line.split(maxsplit=1)[1]
            for line in source.splitlines()
            if line.startswith("import ")
        ]
        assert not any(name.startswith("ComplexityReduction.Routes.") for name in imports)
        assert "ComplexityReduction.Registry.HardnessAggregate" not in imports
        pending.extend(imports)


def test_public_complexity_catalog_is_source_bound_and_answer_free() -> None:
    interfaces = authoring_module._public_complexity_interfaces(
        workspace_root=ROOT, task=_task()
    )
    declarations = {
        item["declaration"]
        for interface in interfaces
        for item in interface["answer_free_public_signatures"]
    }
    assert "ComplexityReduction.TMPolyTimeMap.comp" in declarations
    assert "ComplexityReduction.TMPolyTimeMap.list_map" in declarations
    assert "ComplexityReduction.Program.Primitive.ofTMPolyTime" in declarations
    assert "ComplexityReduction.Program.PolyProg" in declarations
    assert all(interface["source_sha256"].startswith("sha256:") for interface in interfaces)
    serialized = json.dumps(interfaces).lower()
    assert "complexityreduction.routes." not in serialized
    assert "recommended_first_body" not in serialized

    task = _task()
    polynomial = next(node for node in task.gap_nodes if node.node_id == "polynomial-bound")
    prompt = json.loads(
        build_exact_edge_node_prompt(
            task=task,
            node=polynomial,
            accepted_bodies={},
            policy=POLICY,
            statement=STATEMENT,
            statement_hash=STATEMENT_HASH,
            diagnostic=None,
            attempt=1,
            remaining_attempts=3,
            timeout_seconds=60,
            public_complexity_interfaces=interfaces,
        )
    )
    exposed = {
        item["declaration"]
        for interface in prompt["public_complexity_interfaces"]
        for item in interface["answer_free_public_signatures"]
    }
    assert "ComplexityReduction.Presentation.GraphTM.mk" in exposed
    assert "ComplexityReduction.Presentation.GraphTM.appendMapEdges" in exposed
    assert "ComplexityReduction.Program.PolyProg" not in exposed


def test_public_endpoint_interface_exposes_semantics_only_to_semantic_nodes() -> None:
    task = _task()
    interfaces = authoring_module._public_endpoint_interfaces(
        workspace_root=ROOT, task=task
    )
    assert all(interface["semantic_interfaces"] for interface in interfaces)
    assert len(json.dumps(interfaces)) < 20_000
    semantic_declarations = {
        item["declaration"].rsplit(".", 1)[-1]
        for interface in interfaces
        for item in interface["semantic_interfaces"]
    }
    assert {
        "DirectedHamiltonianCircuit",
        "UndirectedHamiltonianCircuit",
        "OrderedDirectedCycleSteps",
        "OrderedUndirectedCycleSteps",
        "HasDirectedEdge",
        "HasUndirectedEdge",
    } <= semantic_declarations
    forward = next(node for node in task.gap_nodes if node.node_id == "semantic-forward")
    forward_prompt = json.loads(
        build_exact_edge_node_prompt(
            task=task,
            node=forward,
            accepted_bodies={},
            policy=POLICY,
            statement=STATEMENT,
            statement_hash=STATEMENT_HASH,
            diagnostic=None,
            attempt=1,
            remaining_attempts=3,
            timeout_seconds=60,
            public_endpoint_interfaces=interfaces,
        )
    )
    assert all(
        interface.get("semantic_interfaces")
        for interface in forward_prompt["public_endpoint_interfaces"]
    )
    primitive = next(node for node in task.gap_nodes if node.node_id == "reduction-primitive")
    primitive_prompt = json.loads(
        build_exact_edge_node_prompt(
            task=task,
            node=primitive,
            accepted_bodies={},
            policy=POLICY,
            statement=STATEMENT,
            statement_hash=STATEMENT_HASH,
            diagnostic=None,
            attempt=1,
            remaining_attempts=3,
            timeout_seconds=60,
            public_endpoint_interfaces=interfaces,
        )
    )
    assert all(
        "semantic_interfaces" not in interface
        for interface in primitive_prompt["public_endpoint_interfaces"]
    )


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

    repair_prompt = build_exact_edge_node_prompt(
        task=task,
        node=task.gap_nodes[0],
        accepted_bodies={},
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        diagnostic="application type mismatch\nhint: simplify the expected public type",
        attempt=2,
        remaining_attempts=2,
        timeout_seconds=60,
    )
    assert "hint: simplify" in repair_prompt

    polynomial = next(node for node in task.gap_nodes if node.node_id == "polynomial-bound")
    normalization = next(
        node for node in task.gap_nodes if node.node_id == "parameter-normalization"
    )
    primitive = next(node for node in task.gap_nodes if node.node_id == "reduction-primitive")
    dependency_prompt = json.loads(
        build_exact_edge_node_prompt(
            task=task,
            node=polynomial,
            accepted_bodies={
                normalization.declaration: "fun input => input",
                primitive.declaration: "fun input => input",
            },
            policy=POLICY,
            statement=STATEMENT,
            statement_hash=STATEMENT_HASH,
            diagnostic=None,
            attempt=1,
            remaining_attempts=3,
            timeout_seconds=60,
        )
    )
    assert [
        item["declaration"]
        for item in dependency_prompt["accepted_dependency_bodies"]
    ] == [normalization.declaration, primitive.declaration]


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
    monkeypatch.setattr(
        authoring_module, "_public_endpoint_interfaces", lambda **kwargs: ()
    )
    monkeypatch.setattr(
        authoring_module, "_public_complexity_interfaces", lambda **kwargs: ()
    )


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
    monkeypatch.setattr(
        authoring_module, "_public_endpoint_interfaces", lambda **kwargs: ()
    )
    monkeypatch.setattr(
        authoring_module, "_public_complexity_interfaces", lambda **kwargs: ()
    )
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


def test_staged_executor_retries_http_200_length_response(
    tmp_path: Path, monkeypatch
) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)

    class LengthThenBodyModel(FakeModel):
        def complete_json(self, *, system: str, prompt: str):
            if not self.calls:
                payload = json.loads(prompt)
                self.calls.append(payload["node"]["node_id"])
                return type(
                    "Response",
                    (),
                    {
                        "called": True,
                        "ok": False,
                        "content": "",
                        "error": "empty assistant content (finish_reason=length)",
                        "status_code": 200,
                        "duration_seconds": 0.1,
                        "usage": {"prompt_tokens": 100, "completion_tokens": 4000},
                        "attempts": 1,
                        "finish_reason": "length",
                    },
                )()
            return super().complete_json(system=system, prompt=prompt)

    model = LengthThenBodyModel(always="fun input => input")
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=tmp_path / "out",
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        max_new_nodes=1,
    )
    assert payload["status"] == "CHECKPOINTED"
    assert len(model.calls) == 2
    assert [call["attempt"] for call in payload["model_calls"]] == [1, 2]
    assert payload["model_calls"][0]["ok"] is False
    assert payload["model_calls"][1]["protocol_accepted"] is True


def test_staged_executor_retries_transient_http_failure(
    tmp_path: Path, monkeypatch
) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)

    class HttpFailureThenBodyModel(FakeModel):
        def complete_json(self, *, system: str, prompt: str):
            if not self.calls:
                payload = json.loads(prompt)
                self.calls.append(payload["node"]["node_id"])
                return type(
                    "Response",
                    (),
                    {
                        "called": True,
                        "ok": False,
                        "content": "",
                        "error": "HTTP 551",
                        "status_code": 551,
                        "duration_seconds": 0.1,
                        "usage": None,
                        "attempts": 1,
                        "finish_reason": None,
                    },
                )()
            return super().complete_json(system=system, prompt=prompt)

    model = HttpFailureThenBodyModel(always="fun input => input")
    payload = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=tmp_path / "out",
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        max_new_nodes=1,
    )
    assert payload["status"] == "CHECKPOINTED"
    assert len(model.calls) == 2
    assert [call["attempt"] for call in payload["model_calls"]] == [1, 2]
    assert payload["model_calls"][0]["status_code"] == 551
    assert payload["model_calls"][0]["usage"] is None
    assert payload["model_calls"][1]["protocol_accepted"] is True


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


def test_staged_executor_resume_replays_prefix_before_new_calls(
    tmp_path: Path, monkeypatch
) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    case_output = tmp_path / "out"
    bodies = {node.node_id: "fun input => input" for node in task.gap_nodes}
    first_model = FakeModel(bodies=bodies)
    first = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=first_model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        case_id="edge-resume-test",
        max_new_nodes=2,
    )
    assert first["status"] == "CHECKPOINTED"
    assert len(first_model.calls) == 2

    second_model = FakeModel(bodies=bodies)
    resumed = run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=second_model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        case_id="edge-resume-test",
        resume_checkpoint=case_output / "checkpoint.json",
    )
    assert resumed["status"] == "VERIFIED"
    assert resumed["resumed"] is True
    assert resumed["resumed_node_count"] == 2
    assert resumed["new_node_count"] == len(task.gap_nodes) - 2
    assert len(second_model.calls) == len(task.gap_nodes) - 2
    assert len(resumed["model_calls"]) == len(task.gap_nodes)
    assert all(call["case_id"] == "edge-resume-test" for call in resumed["model_calls"])
    assert all(call["request_id"].startswith("sha256:") for call in resumed["model_calls"])
    assert len(list((case_output / "commands/resume-prefix").glob("*.json"))) == 2


def test_staged_executor_resume_rejects_stale_compiled_prefix(
    tmp_path: Path, monkeypatch
) -> None:
    _monkeypatch_compile(monkeypatch)
    task = _task()
    workspace = tmp_path / "workspace"
    (workspace / "Lean").mkdir(parents=True)
    case_output = tmp_path / "out"
    model = FakeModel(
        bodies={node.node_id: "fun input => input" for node in task.gap_nodes}
    )
    run_exact_edge_staged_construction(
        workspace_root=workspace,
        case_output=case_output,
        task=task,
        policy=POLICY,
        statement=STATEMENT,
        statement_hash=STATEMENT_HASH,
        model_client=model,
        model_name="deepseek-v4-flash",
        timeout_seconds=60,
        case_id="edge-resume-test",
        max_new_nodes=1,
    )
    checkpoint = case_output / "checkpoint.json"
    raw = json.loads(checkpoint.read_text(encoding="utf-8"))
    raw["accepted_nodes"][0]["cumulative_source_sha256"] = "sha256:" + "0" * 64
    raw["checkpoint_sha256"] = sha256_id(
        {key: value for key, value in raw.items() if key != "checkpoint_sha256"}
    )
    checkpoint.write_text(json.dumps(raw), encoding="utf-8")
    with pytest.raises(ExactEdgeAuthoringError) as raised:
        run_exact_edge_staged_construction(
            workspace_root=workspace,
            case_output=case_output,
            task=task,
            policy=POLICY,
            statement=STATEMENT,
            statement_hash=STATEMENT_HASH,
            model_client=model,
            model_name="deepseek-v4-flash",
            timeout_seconds=60,
            case_id="edge-resume-test",
            resume_checkpoint=checkpoint,
        )
    assert raised.value.code == "candidate_dependency_stale"
