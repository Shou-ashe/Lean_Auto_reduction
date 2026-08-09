"""Offline G-C qualification for the sequential NP-hard capability runtime."""

from __future__ import annotations

import json
import shutil
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from .model_client import ModelResponse
from .models import sha256_id
from .np_hard_authoring import build_np_hard_authoring_tasks_v2
from .np_hard_gap_runtime import (
    NP_HARD_NODE_PATCH_SCHEMA_V1,
    NPHardGapRuntimeError,
    NPHardGapRuntimeV1,
)
from .np_hard_generalization import load_np_hard_generalization_suite
from .lean_runner import sha256_file


NP_HARD_GAP_BENCHMARK_REPORT_SCHEMA_V1 = "hardness_np_hard_gap_runtime_report_v1"


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _fixture_bodies(task, authoring: Mapping[str, Any]) -> dict[str, str]:
    module = task.candidate_module
    source = task.source_problem.term
    primitives = tuple(authoring["allowed_primitives"])
    if task.task_class == "semantic_proof":
        if authoring.get("mapping_invariant") is None:
            return {"semantic-proof": "by\n  intro input\n  rfl\n"}
        return {
            "mapping-invariant": (
                "by\n"
                "  intro input\n"
                "  change false = false ∧ input = input\n"
                "  exact ⟨rfl, rfl⟩\n"
            ),
            "semantic-iff": (
                "by\n"
                "  intro input\n"
                f"  change {source}.accepts input ↔ false = false ∧ {source}.accepts input\n"
                "  constructor\n"
                "  · intro accepted\n"
                "    exact ⟨rfl, accepted⟩\n"
                "  · intro accepted\n"
                "    exact accepted.2\n"
            ),
        }
    if task.task_class == "program_composition":
        first, second = primitives
        if "NumericProgramComposition" in task.target_problem.module:
            semantic = (
                "by\n"
                "  intro input\n"
                f"  change {source}.accepts input ↔ false = false ∧ {source}.accepts input\n"
                "  exact ⟨fun accepted => ⟨rfl, accepted⟩, fun accepted => accepted.2⟩\n"
            )
        else:
            semantic = "by\n  intro input\n  rfl\n"
        return {
            "composed-program": f"by\n  exact .comp {second} {first}\n",
            "semantic-proof": semantic,
        }
    if task.task_class == "program_synthesis":
        program = f"{module}.synthesizedProgram"
        executable = f"{module}.synthesizedExecutable"
        coherence = f"{module}.programRunCoherence"
        return {
            "reduction-executable": "fun input => (false, input)\n",
            "poly-program": (
                "by\n"
                "  exact .pair\n"
                f"    (.const {source}.representation StandardInstances.bool false)\n"
                f"    (.id {source}.representation)\n"
            ),
            "program-run-coherence": "by\n  intro input\n  rfl\n",
            "mapping-invariant": (
                "by\n"
                "  intro input\n"
                f"  rw [{coherence} input]\n"
                "  change false = false ∧ input = input\n"
                "  exact ⟨rfl, rfl⟩\n"
            ),
            "semantic-iff": (
                "by\n"
                "  intro input\n"
                f"  change {source}.accepts input ↔ false = false ∧ {source}.accepts input\n"
                "  constructor\n"
                "  · intro accepted\n"
                f"    have invariant := {module}.mappingInvariantProof input\n"
                "    exact ⟨invariant.1, accepted⟩\n"
                "  · intro accepted\n"
                "    exact accepted.2\n"
            ),
        }
    raise ValueError(f"unsupported fixture task class: {task.task_class}")


def _final_program(task, authoring: Mapping[str, Any]) -> str:
    if task.task_class == "semantic_proof":
        return str(authoring["program_reference"])
    suffix = "composedProgram" if task.task_class == "program_composition" else "synthesizedProgram"
    return f"{task.candidate_module}.{suffix}"


class _OfflineNodeModel:
    """Benchmark-only deterministic stand-in; never exposed to the agent prompt."""

    def __init__(self, bodies: Mapping[str, str]):
        self.bodies = dict(bodies)
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        del system
        self.calls += 1
        request = json.loads(prompt)["node_request"]
        node = request["node"]
        body = self.bodies[node["node_id"]]
        content = json.dumps(
            {
                "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
                "action": "submit_node_patch",
                "request_id": request["request_id"],
                "node_id": node["node_id"],
                "declaration": node["declaration"],
                "dependency_fingerprint": sha256_id(request["dependency_snapshot"]),
                "replacement_body": body,
            },
            sort_keys=True,
        )
        return ModelResponse(
            called=True,
            ok=True,
            content=content,
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


def _expect_runtime_error(action, code: str) -> bool:
    try:
        action()
    except NPHardGapRuntimeError as error:
        return error.code == code
    return False


def _tamper_audits(
    *, root: Path, output_root: Path, task, authoring: Mapping[str, Any], completed
) -> dict[str, bool]:
    checkpoint_path = Path(completed.checkpoint_path)
    checkpoint_hash = completed.checkpoint_file_sha256
    assert checkpoint_hash is not None

    byte_root = output_root / "tamper-checkpoint-byte"
    shutil.copytree(checkpoint_path.parent, byte_root)
    byte_checkpoint = byte_root / "checkpoint.json"
    byte_checkpoint.write_bytes(byte_checkpoint.read_bytes() + b" ")
    byte_runtime = NPHardGapRuntimeV1(
        root=root,
        task=task,
        output_root=byte_root,
        model=_OfflineNodeModel(_fixture_bodies(task, authoring)),
        final_program_declaration=_final_program(task, authoring),
    )
    checkpoint_byte_rejected = _expect_runtime_error(
        lambda: byte_runtime.run(
            resume_checkpoint_path=byte_checkpoint,
            expected_checkpoint_file_sha256=checkpoint_hash,
        ),
        "checkpoint_tampered",
    )

    candidate_root = output_root / "tamper-candidate"
    shutil.copytree(checkpoint_path.parent, candidate_root)
    candidate_checkpoint = candidate_root / "checkpoint.json"
    value = json.loads(candidate_checkpoint.read_text(encoding="utf-8"))
    publication_hash = value["accepted_nodes"][0]["cumulative_source_sha256"]
    candidate_body = candidate_root / "published" / publication_hash.removeprefix("sha256:") / "body.lean"
    candidate_body.write_text(candidate_body.read_text(encoding="utf-8") + "\n", encoding="utf-8")
    candidate_runtime = NPHardGapRuntimeV1(
        root=root,
        task=task,
        output_root=candidate_root,
        model=_OfflineNodeModel(_fixture_bodies(task, authoring)),
        final_program_declaration=_final_program(task, authoring),
    )
    candidate_rejected = _expect_runtime_error(
        lambda: candidate_runtime.run(
            resume_checkpoint_path=candidate_checkpoint,
            expected_checkpoint_file_sha256=f"sha256:{sha256_file(candidate_checkpoint)}",
        ),
        "candidate_tampered",
    )

    dependency_root = output_root / "tamper-dependency"
    shutil.copytree(checkpoint_path.parent, dependency_root)
    dependency_checkpoint = dependency_root / "checkpoint.json"
    dependency_value = json.loads(dependency_checkpoint.read_text(encoding="utf-8"))
    first_dependency = sorted(dependency_value["dependency_snapshot"])[0]
    dependency_value["dependency_snapshot"][first_dependency] = "sha256:" + "f" * 64
    content = {
        key: dependency_value[key]
        for key in dependency_value
        if key != "checkpoint_hash"
    }
    dependency_value["checkpoint_hash"] = sha256_id(content)
    _write_json(dependency_checkpoint, dependency_value)
    dependency_runtime = NPHardGapRuntimeV1(
        root=root,
        task=task,
        output_root=dependency_root,
        model=_OfflineNodeModel(_fixture_bodies(task, authoring)),
        final_program_declaration=_final_program(task, authoring),
    )
    dependency_rejected = _expect_runtime_error(
        lambda: dependency_runtime.run(
            resume_checkpoint_path=dependency_checkpoint,
            expected_checkpoint_file_sha256=f"sha256:{sha256_file(dependency_checkpoint)}",
        ),
        "candidate_dependency_stale",
    )
    return {
        "checkpoint_byte_rejected": checkpoint_byte_rejected,
        "candidate_byte_rejected": candidate_rejected,
        "dependency_snapshot_rejected": dependency_rejected,
    }


def run_np_hard_gap_runtime_benchmark(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError(f"G-C benchmark output must be fresh: {output_root}")
    output_root.mkdir(parents=True, exist_ok=True)
    suite = load_np_hard_generalization_suite(suite_path, root=root)
    cases = [case for case in suite.cases if case.kind == "model_authoring"]
    tasks = build_np_hard_authoring_tasks_v2(root=root, suite_path=suite_path)
    rows: list[dict[str, Any]] = []
    resumed_case = None
    resumed_task = None
    resumed_authoring = None
    resumed_result = None
    for case, task in zip(cases, tasks, strict=True):
        authoring = case.authoring
        assert authoring is not None
        model = _OfflineNodeModel(_fixture_bodies(task, authoring))
        case_root = output_root / "cases" / case.id
        runtime = NPHardGapRuntimeV1(
            root=root,
            task=task,
            output_root=case_root,
            model=model,
            final_program_declaration=_final_program(task, authoring),
            timeout_seconds=300,
        )
        if task.task_class == "program_synthesis":
            interrupted = runtime.run(max_new_nodes=2)
            if interrupted.status != "CHECKPOINTED":
                raise ValueError("G-C synthesis case did not stop at a valid checkpoint")
            resumed = runtime.run(
                resume_checkpoint_path=Path(interrupted.checkpoint_path),
                expected_checkpoint_file_sha256=interrupted.checkpoint_file_sha256,
            )
            result = resumed
            resumed_case = case
            resumed_task = task
            resumed_authoring = authoring
            resumed_result = resumed
            interrupted_row = interrupted.to_dict(task)
        else:
            result = runtime.run()
            interrupted_row = None
        rows.append(
            {
                "case_id": case.id,
                "task_class": task.task_class,
                "gap_node_count": len(task.gap_nodes),
                "requires_multi_gap": bool(authoring["requires_multi_gap"]),
                "requires_nontrivial_semantics": bool(
                    authoring["requires_nontrivial_semantics"]
                ),
                "interrupted": interrupted_row,
                "runtime": result.to_dict(task),
                "matched": (
                    result.status == "VERIFIED"
                    and result.accepted_nodes
                    == tuple(node.node_id for node in task.gap_nodes)
                    and result.fresh_core_rediscoveries
                    >= len(task.gap_nodes)
                    and result.result is not None
                ),
            }
        )
    if resumed_case is None or resumed_task is None or resumed_result is None:
        raise ValueError("G-C benchmark lacks a resumed multi-gap case")
    tamper = _tamper_audits(
        root=root,
        output_root=output_root,
        task=resumed_task,
        authoring=resumed_authoring,
        completed=resumed_result,
    )
    passed = all(row["matched"] for row in rows) and all(tamper.values())
    report = {
        "schema_version": NP_HARD_GAP_BENCHMARK_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "G-C",
        "qualification_scope": "sequential_multi_gap_runtime_offline_fixture_model",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "metrics": {
            "task_count": len(rows),
            "verified_task_count": sum(row["matched"] for row in rows),
            "accepted_node_count": sum(len(row["runtime"]["accepted_nodes"]) for row in rows),
            "multi_gap_verified_count": sum(
                row["matched"] and row["gap_node_count"] >= 2 for row in rows
            ),
            "program_synthesis_verified_count": sum(
                row["matched"] and row["task_class"] == "program_synthesis" for row in rows
            ),
            "nontrivial_semantic_verified_count": sum(
                row["matched"] and row["requires_nontrivial_semantics"] for row in rows
            ),
            "fresh_core_rediscovery_count": sum(
                row["runtime"]["fresh_core_rediscoveries"] for row in rows
            ),
            "checkpoint_resume_verified_count": sum(
                row["runtime"]["resumed"] and row["matched"] for row in rows
            ),
            "persistent_worker_count_per_session": 1,
            "worker_fallback_count": sum(
                item["fallback_used"]
                for row in rows
                for item in row["runtime"]["worker_results"]
            ),
            "model_calls": sum(row["runtime"]["model_calls"] for row in rows),
            "compiler_inserted_math_token_count": 0,
            "exact_native_np_hard_final_count": sum(
                row["runtime"]["status"] == "VERIFIED" for row in rows
            ),
            "independent_replay_count": sum(
                row["runtime"]["status"] == "VERIFIED" for row in rows
            ),
        },
        "tamper_audits": tamper,
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
