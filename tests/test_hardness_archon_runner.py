"""Contract tests for the Archon-loop model client (no Archon, no Lean)."""

from __future__ import annotations

import json
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

import pytest

from agent.hardness.archon_runner import (
    ArchonModelClient,
    ArchonModelClientError,
    BODY_END_MARKER,
    BODY_START_MARKER,
    _common_candidate_module,
    _collect_archon_usage,
    _dedent_two,
    _extract_marked_body,
    _indent_two,
    _jsonl_offsets,
    _render_scaffold,
)


def _node_prompt(
    *,
    declaration: str = "ComplexityReduction.Agent.Hardness.Sample.Edge",
    exact_type: str = "p → q",
    node_id: str = "N1",
    module: str = "ComplexityReduction.Agent.Hardness.Sample",
    imports: tuple[str, ...] = (),
) -> str:
    request = {
        "schema_version": "hardness_np_hard_node_request_v1",
        "objective": "prove_np_hard",
        "task_class": "typed_node_dag",
        "node_request": {
            "request_id": "sha256:" + "0" * 64,
            "task_request_id": "sha256:" + "0" * 64,
            "node_ordinal": 1,
            "node": {
                "node_id": node_id,
                "declaration": declaration,
                "capability": "semantic_proof",
                "exact_type": exact_type,
                "depends_on": (),
            },
            "source_problem": {"module": "Problems.Karp21.X", "term": "X"},
            "target_problem": {"module": "ComputerScience.NP.ThreeSat", "term": "3SAT"},
            "required_direction": "source_to_target",
            "dependency_snapshot": {},
            "accepted_nodes": {},
            "allowed_imports": list(imports),
            "allowed_primitives": [],
            "node_attempt_budget": 2,
            "instance_call_budget_remaining": 4,
        },
        "accepted_dependency_bodies": {},
        "public_sources": {},
        "recommended_first_body": "",
        "lean_diagnostic": "",
        "policy": {},
        "response_template": {
            "schema_version": "hardness_np_hard_node_patch_v1",
            "action": "submit_node_patch",
            "request_id": "sha256:" + "0" * 64,
            "node_id": node_id,
            "declaration": declaration,
            "dependency_fingerprint": "sha256:" + "1" * 64,
            "replacement_body": "Lean term body only",
        },
    }
    return json.dumps(request)


def _synthetic_lean_root(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    (root / "Lean").mkdir(parents=True)
    (root / "Lean" / "lakefile.toml").write_text("[lean]\n", encoding="utf-8")
    (root / "Lean" / "lean-toolchain").write_text("leanprover/lean4:v4.17.0", encoding="utf-8")
    (root / "Lean" / "lake-manifest.json").write_text("{}", encoding="utf-8")
    reference = root / "Lean" / "Reference" / "ComplexityReduction"
    (reference / "A").mkdir(parents=True)
    (reference / "A" / "B.lean").write_text("def x : Nat := 1\n", encoding="utf-8")
    (
        root
        / "Lean"
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "ComplexityReduction"
    ).mkdir(parents=True)
    return root


def test_common_candidate_module_prefixes_declarations() -> None:
    declarations = [
        "ComplexityReduction.Agent.Hardness.Gen.A",
        "ComplexityReduction.Agent.Hardness.Gen.B",
        "ComplexityReduction.Agent.Hardness.Gen.C",
    ]
    assert (
        _common_candidate_module(declarations)
        == "ComplexityReduction.Agent.Hardness.Gen"
    )


def test_common_candidate_module_single_declaration() -> None:
    assert (
        _common_candidate_module(["ComplexityReduction.Agent.Hardness.Gen.A"])
        == "ComplexityReduction.Agent.Hardness.Gen"
    )


def test_scaffold_renders_imports_namespace_markers_and_end() -> None:
    scaffold = _render_scaffold(
        module="ComplexityReduction.Agent.Hardness.Gen",
        imports=("Mathlib",),
        opens=("ComplexityReduction",),
        dependencies=[("Dep", "by\n  linarith")],
        target_short="Goal",
        target_exact_type="p → q",
        current_body="by\n  sorry",
    )
    lines = scaffold.splitlines()
    assert lines[0] == "import Mathlib"
    assert lines[2] == "namespace ComplexityReduction.Agent.Hardness.Gen"
    assert "open ComplexityReduction" in lines
    assert "noncomputable def Dep :=" in lines
    assert "  by" in lines
    assert "    linarith" in lines
    assert "  by" in scaffold
    assert "    sorry" in scaffold
    assert BODY_START_MARKER in lines
    assert BODY_END_MARKER in lines
    assert scaffold.rstrip().endswith("end ComplexityReduction.Agent.Hardness.Gen")


def test_dedent_and_indent_roundtrip() -> None:
    body = "by\n  simp [x]\n  omega"
    assert _dedent_two(_indent_two(body)) == body


def test_extract_marked_body() -> None:
    source = "def x :=\n" + BODY_START_MARKER + "\n  by\n    omega\n" + BODY_END_MARKER + "\nend x"
    assert _extract_marked_body(source) == "by\n  omega"


def test_extract_marked_body_missing_fence_raises() -> None:
    with pytest.raises(ArchonModelClientError):
        _extract_marked_body("def x := by sorry\n")


def test_missing_archon_cli_returns_clean_failure(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)
    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli=None,
    )
    with patch("agent.hardness.archon_runner.shutil.which", return_value=None):
        response = client.complete_json(system="s", prompt=_node_prompt())
    assert response.called is True
    assert response.ok is False
    assert "archon CLI is not installed" in response.error
    assert response.usage is None


def test_unsupported_prompt_shape_returns_clean_failure(tmp_path: Path) -> None:
    client = ArchonModelClient(
        root=_synthetic_lean_root(tmp_path),
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
    )
    response = client.complete_json(system="s", prompt="not a known prompt")
    assert response.called is True
    assert response.ok is False
    assert "unsupported model prompt shape" in response.error


def test_node_prompt_roundtrip_with_fake_archon_loop(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)

    def fake_loop(command, *, cwd, env, stdout, stderr, timeout, start_new_session, check):
        assert "--max-iterations" in command
        assert "--no-dashboard" in command
        assert env["DEEPSEEK_API_KEY"] == "secret-key"
        target = list((Path(cwd) / "Reference" / "ComplexityReduction" / "Agent" / "Hardness" / "ArchonWorker").glob("*.lean"))
        assert len(target) == 1
        target_path = target[0]
        source = target_path.read_text(encoding="utf-8")
        assert "by\n    sorry" in source
        start = source.index(BODY_START_MARKER) + len(BODY_START_MARKER)
        end = source.index(BODY_END_MARKER)
        replacement = (
            source[:start]
            + "\n  by\n    rfl\n"
            + source[end:]
        )
        target_path.write_text(replacement, encoding="utf-8")
        stdout.write("archon loop finished\n")

    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        max_iterations=2,
        report_config=__import__(
            "agent.hardness.model_client", fromlist=["DeepSeekConfig"]
        ).DeepSeekConfig(api_key="secret-key"),
    )
    with patch(
        "agent.hardness.archon_runner.subprocess.run", side_effect=fake_loop
    ):
        response = client.complete_json(
            system="system", prompt=_node_prompt(imports=("A.B",))
        )
    assert response.called is True
    assert response.ok is True
    assert response.error is None
    envelope = json.loads(response.content)
    assert envelope["schema_version"] == "hardness_np_hard_node_patch_v1"
    assert envelope["action"] == "submit_node_patch"
    assert envelope["replacement_body"] == "by\n  rfl"
    worker = tmp_path / "out" / "work" / "archon"
    assert (worker / "Lean" / ".archon" / "config.json").is_file()
    assert (worker / "Lean" / ".archon" / "PROGRESS.md").is_file()


def test_benchmark_recommended_body_is_not_exposed_to_archon(tmp_path: Path) -> None:
    prompt = json.loads(_node_prompt(imports=("A.B",)))
    prompt["recommended_first_body"] = "by\n  exact recommendedProof"
    seen: dict[str, str] = {}

    def fake_loop(command, *, cwd, env, stdout, stderr, timeout, start_new_session, check):
        target = next(
            (Path(cwd) / "Reference" / "ComplexityReduction" / "Agent" / "Hardness" / "ArchonWorker").glob("*.lean")
        )
        seen["source"] = target.read_text(encoding="utf-8")
        seen["hints"] = (Path(cwd) / ".archon" / "USER_HINTS.md").read_text(
            encoding="utf-8"
        )
        start = seen["source"].index(BODY_START_MARKER) + len(BODY_START_MARKER)
        end = seen["source"].index(BODY_END_MARKER)
        target.write_text(
            seen["source"][:start] + "\n  by\n    rfl\n" + seen["source"][end:],
            encoding="utf-8",
        )
        stdout.write("ok\n")

    client = ArchonModelClient(
        root=_synthetic_lean_root(tmp_path),
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
    )
    with patch("agent.hardness.archon_runner.subprocess.run", side_effect=fake_loop):
        response = client.complete_json(system="s", prompt=json.dumps(prompt))
    assert response.ok is True
    assert "recommendedProof" not in seen["source"]
    assert "by\n    sorry" in seen["source"]
    assert "recommendedProof" not in seen["hints"]


def test_case_level_blackbox_starts_at_prover_and_resets_visible_sources(
    tmp_path: Path,
) -> None:
    root = _synthetic_lean_root(tmp_path)
    observations: list[dict[str, object]] = []

    def fake_loop(command, *, cwd, env, stdout, stderr, timeout, start_new_session, check):
        lean_root = Path(cwd)
        targets = sorted(lean_root.rglob("*.lean"))
        observations.append(
            {
                "command": tuple(command),
                "env": dict(env),
                "targets": [str(path.relative_to(lean_root)) for path in targets],
                "hints": (lean_root / ".archon" / "USER_HINTS.md").read_text(
                    encoding="utf-8"
                ),
                "progress": (lean_root / ".archon" / "PROGRESS.md").read_text(
                    encoding="utf-8"
                ),
            }
        )
        assert len(targets) == 1
        target = targets[0]
        source = target.read_text(encoding="utf-8")
        start = source.index(BODY_START_MARKER) + len(BODY_START_MARKER)
        end = source.index(BODY_END_MARKER)
        target.write_text(
            source[:start] + "\n  by\n    trivial\n" + source[end:],
            encoding="utf-8",
        )
        stdout.write("ok\n")

    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        worker_count=1,
    )
    with patch("agent.hardness.archon_runner.subprocess.run", side_effect=fake_loop):
        first = client.prove_case(
            case_id="public-case-one",
            statement="Prove the public problem is NP-hard.",
            requirement="Produce a complete proof of NP-hardness.",
            imports=(),
            exact_type="True",
        )
        second = client.prove_case(
            case_id="public-case-two",
            statement="Prove the second public problem is NP-hard.",
            requirement="Produce a complete proof of NP-hardness.",
            imports=(),
            exact_type="True",
        )

    assert first.ok is True and second.ok is True
    assert first.body == "by\n  trivial"
    assert second.body == "by\n  trivial"
    assert len(observations) == 2
    for observation in observations:
        assert observation["targets"] and len(observation["targets"]) == 1
        assert "--from" in observation["command"]
        assert "prover" in observation["command"]
        assert observation["env"]["ARCHON_BENCHMARK_BODY_FENCE_ONLY"] == "1"
        assert observation["env"]["ARCHON_DISABLE_WEB_TOOLS"] == "1"
        assert observation["env"]["ARCHON_BENCHMARK_MAX_TOOL_ROUNDS"] == "16"
        assert "recommended" not in str(observation["hints"]).lower()
        assert ".lean`" in str(observation["progress"])


def test_authoring_prompt_roundtrip_with_fake_archon_loop(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)
    request = {
        "schema_version": "hardness_model_authoring_request_v1",
        "task_id": "sha256:abc",
        "gap_reason": "TGT",
        "stage": "semantic_proof",
        "editable_file": "Lean/Reference/ComplexityReduction/A/Generated.lean",
        "candidate_module": "ComplexityReduction.Agent.Hardness.GeneratedE",
        "candidate_declaration": "ComplexityReduction.Agent.Hardness.GeneratedE.proof",
        "source_declaration": "X",
        "target_declaration": "3SAT",
        "expected_type": "ReductionX p",
        "allowed_imports": ["A.B"],
        "current_editable_body": "  by\n    sorry",
        "current_lean_diagnostics": "",
    }
    shape = {
        "schema_version": "hardness_model_patch_v1",
        "task_id": "sha256:abc",
        "stage": "semantic_proof",
        "editable_file": "Lean/Reference/ComplexityReduction/A/Generated.lean",
        "replacement": "  by\n    -- complete Lean term body\n",
    }
    prompt = (
        "AUTHORING_REQUEST_JSON\n"
        + json.dumps(request)
        + "\n\nRETURN_EXACT_JSON_SHAPE\n"
        + json.dumps(shape)
    )

    def fake_loop(command, *, cwd, env, stdout, stderr, timeout, start_new_session, check):
        target = list((Path(cwd) / "Reference" / "ComplexityReduction" / "Agent" / "Hardness" / "ArchonWorker").glob("*.lean"))
        assert len(target) == 1
        target_path = target[0]
        source = target_path.read_text(encoding="utf-8")
        start = source.index(BODY_START_MARKER) + len(BODY_START_MARKER)
        end = source.index(BODY_END_MARKER)
        target_path.write_text(
            source[:start] + "\n  by\n    intro h; rfl\n" + source[end:],
            encoding="utf-8",
        )
        stdout.write("ok\n")

    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
    )
    with patch(
        "agent.hardness.archon_runner.subprocess.run", side_effect=fake_loop
    ):
        response = client.complete_json(system="s", prompt=prompt)
    assert response.ok is True
    envelope = json.loads(response.content)
    assert envelope["schema_version"] == "hardness_model_patch_v1"
    assert envelope["replacement"] == "  by\n    intro h; rfl"
    assert envelope["task_id"] == "sha256:abc"


def test_loop_timeout_returns_clean_failure(tmp_path: Path) -> None:
    import subprocess as subprocess_module

    client = ArchonModelClient(
        root=_synthetic_lean_root(tmp_path),
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        loop_timeout_seconds=1,
    )
    with patch(
        "agent.hardness.archon_runner.subprocess.run",
        side_effect=subprocess_module.TimeoutExpired("archon loop", 1),
    ):
        response = client.complete_json(system="s", prompt=_node_prompt())
    assert response.called is True
    assert response.ok is False
    assert "exceeded 1s" in response.error


def test_report_config_is_reused_for_public_model_name(tmp_path: Path) -> None:
    from agent.hardness.model_client import DeepSeekConfig

    client = ArchonModelClient(
        root=_synthetic_lean_root(tmp_path),
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        report_config=DeepSeekConfig(api_key="k", model="deepseek-v4-flash"),
    )
    assert client.config.model == "deepseek-v4-flash"
    assert client.config.public_base_url


def test_worker_copies_shipped_archon_state_templates(tmp_path: Path) -> None:
    repo = Path(__file__).resolve().parents[1]
    cli = repo / "compare" / "Archon" / ".venv" / "bin" / "archon"
    if not cli.is_file():
        pytest.skip("bundled Archon venv is absent")
    client = ArchonModelClient(
        root=_synthetic_lean_root(tmp_path),
        output_dir=tmp_path / "out",
        archon_cli=cli,
    )
    client._ensure_worker()
    state = client.worker_dir / "Lean" / ".archon"
    assert (state / "config.json").is_file()
    assert (state / "AGENTS.md").is_file()
    assert (state / "prompts" / "plan.md").is_file()
    assert (state / "prover-modes" / "prove.md").is_file()
    progress = state / "PROGRESS.md"
    assert progress.is_file() or not progress.exists()


def test_worker_hides_complexity_reduction_sources(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)
    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
    )
    client._ensure_worker()
    worker = client.worker_dir / "Lean"
    assert not (worker / "Reference" / "ComplexityReduction" / "A" / "B.lean").exists()
    visible_sources = sorted((worker / "Reference").rglob("*.lean"))
    assert visible_sources == []
    environment = client._loop_environment()
    assert environment["ARCHON_RESTRICT_PROJECT_ROOT"] == "1"
    assert environment["ARCHON_DISABLE_WEB_TOOLS"] == "1"
    assert environment["LEAN_PATH"].split(":", 1)[0].endswith(
        "/.lake/build/lib/lean"
    )


def _fence_replacing_fake_loop(command, *, cwd, env, stdout, stderr, timeout,
                               start_new_session, check):
    targets = sorted(
        (Path(cwd) / "Reference" / "ComplexityReduction" / "Agent" / "Hardness" / "ArchonWorker").glob("*.lean")
    )
    assert targets, "no staged objective file"
    target_path = targets[-1]
    source = target_path.read_text(encoding="utf-8")
    start = source.index(BODY_START_MARKER) + len(BODY_START_MARKER)
    end = source.index(BODY_END_MARKER)
    target_path.write_text(
        source[:start] + "\n  by\n    rfl\n" + source[end:], encoding="utf-8"
    )
    stdout.write("archon loop finished\n")


def _staged_lean_files(client: ArchonModelClient) -> list[Path]:
    return sorted(
        client.worker_dir.rglob(
            "Reference/ComplexityReduction/Agent/Hardness/ArchonWorker/*.lean"
        )
    )


def test_multi_worker_pool_runs_calls_concurrently(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)
    barrier = threading.Barrier(2)
    state_lock = threading.Lock()
    active = 0
    peak = 0

    def fake_loop(command, *, cwd, env, stdout, stderr, timeout, start_new_session, check):
        nonlocal active, peak
        with state_lock:
            active += 1
            peak = max(peak, active)
        barrier.wait(timeout=15)
        try:
            _fence_replacing_fake_loop(
                command, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                timeout=timeout, start_new_session=start_new_session, check=check,
            )
        finally:
            with state_lock:
                active -= 1

    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        worker_count=2,
    )
    with patch("agent.hardness.archon_runner.subprocess.run", side_effect=fake_loop):
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = [
                pool.submit(
                    client.complete_json, system="s", prompt=_node_prompt()
                )
                for _ in range(2)
            ]
            responses = [future.result(timeout=60) for future in futures]
    assert all(response.ok for response in responses)
    assert peak >= 2, "the two archon loops must run concurrently"
    staged = _staged_lean_files(client)
    assert len(staged) == 2
    assert (client.worker_dir / "worker-1").is_dir()
    lean_dirs = {path.parents[5] for path in staged}
    assert len(lean_dirs) == 2


def test_multi_worker_pool_reuses_slots_round_robin(tmp_path: Path) -> None:
    root = _synthetic_lean_root(tmp_path)
    client = ArchonModelClient(
        root=root,
        output_dir=tmp_path / "out",
        archon_cli="/usr/bin/true",
        worker_count=2,
    )
    with patch(
        "agent.hardness.archon_runner.subprocess.run",
        side_effect=_fence_replacing_fake_loop,
    ):
        responses = [
            client.complete_json(system="s", prompt=_node_prompt())
            for _ in range(3)
        ]
    assert all(response.ok for response in responses)
    staged = _staged_lean_files(client)
    assert len(staged) == 3
    lean_dirs = {path.parents[5] for path in staged}
    assert len(lean_dirs) == 2


def test_worker_count_must_be_positive(tmp_path: Path) -> None:
    with pytest.raises(ValueError):
        ArchonModelClient(
            root=_synthetic_lean_root(tmp_path),
            output_dir=tmp_path / "out",
            archon_cli="/usr/bin/true",
            worker_count=0,
        )


def test_archon_usage_is_collected_from_new_session_end_rows(tmp_path: Path) -> None:
    logs = tmp_path / "logs"
    path = logs / "iter-001" / "plan.jsonl"
    path.parent.mkdir(parents=True)
    path.write_text('{"event":"session_end","input_tokens":10,"output_tokens":2,"total_cost_usd":0.1}\n', encoding="utf-8")
    offsets = _jsonl_offsets(logs)
    with path.open("a", encoding="utf-8") as handle:
        handle.write('{"event":"session_end","input_tokens":30,"output_tokens":4,"total_cost_usd":0.2}\n')
    assert _collect_archon_usage(logs, offsets) == {
        "prompt_tokens": 30,
        "completion_tokens": 4,
        "total_tokens": 34,
        "archon_loop": True,
        "archon_sessions": 1,
        "estimated_cost_usd": 0.2,
    }
