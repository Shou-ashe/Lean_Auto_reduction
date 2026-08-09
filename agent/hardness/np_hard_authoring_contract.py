"""G-B offline replay for versioned NP-hard authoring contracts."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import build_module_command, run_command, sha256_file
from .models import sha256_id
from .np_hard_authoring import (
    NP_HARD_AUTHORING_TASK_SCHEMA_V2,
    accepted_np_hard_authoring_result_v2,
    build_np_hard_authoring_prompt_v2,
    build_np_hard_authoring_tasks_v2,
)
from .np_hard_generalization import load_np_hard_generalization_suite


NP_HARD_AUTHORING_CONTRACT_REPORT_SCHEMA_V1 = (
    "hardness_np_hard_authoring_v2_contract_report_v1"
)


def _fresh_directory(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"NP-hard authoring contract output must be fresh: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _audit_source(
    *, gold_module: str, gold_certificate: str, task, namespace_suffix: str
) -> str:
    return f"""import {gold_module}
import ComplexityReduction.AxiomGate

namespace Benchmark.Hardness.NPHardAuthoringV2Replay.{namespace_suffix}

open ComplexityReduction.Certificate

noncomputable def exactEndpointReduction :
    {task.final_exact_type} :=
  {gold_certificate}

assert_standard_axioms exactEndpointReduction

end Benchmark.Hardness.NPHardAuthoringV2Replay.{namespace_suffix}
"""


def run_np_hard_authoring_v2_contract_replay(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    _fresh_directory(output_root)
    suite = load_np_hard_generalization_suite(suite_path, root=root)
    authoring_cases = [case for case in suite.cases if case.kind == "model_authoring"]
    tasks = build_np_hard_authoring_tasks_v2(root=root, suite_path=suite_path)
    if len(tasks) != len(authoring_cases):
        raise ValueError("NP-hard v2 task projection lost an authoring case")

    gold_modules = tuple(str(case.authoring["gold_module"]) for case in authoring_cases)
    prebuild = run_command(
        build_module_command(gold_modules),
        cwd=root / "Lean",
        timeout_seconds=900,
    )
    if not prebuild.ok:
        raise ValueError("NP-hard v2 isolated Gold prebuild failed")

    rows: list[dict[str, Any]] = []
    for index, (case, task) in enumerate(zip(authoring_cases, tasks, strict=True), start=1):
        authoring = case.authoring
        assert authoring is not None
        gold_module = str(authoring["gold_module"])
        gold_file = root / str(authoring["gold_file"])
        gold_certificate = f"{gold_module}.certifiedReduction"
        prompt = build_np_hard_authoring_prompt_v2(task=task, root=root)
        prompt_lower = prompt.lower()
        prompt_safe = (
            case.id not in prompt
            and ".gold." not in prompt_lower
            and ".oracles." not in prompt_lower
            and '"expected"' not in prompt_lower
            and '"case_id"' not in prompt_lower
        )

        final_path = output_root / f"Final{index}.lean"
        replay_path = output_root / f"Replay{index}.lean"
        final_source = _audit_source(
            gold_module=gold_module,
            gold_certificate=gold_certificate,
            task=task,
            namespace_suffix=f"Final{index}",
        )
        replay_source = _audit_source(
            gold_module=gold_module,
            gold_certificate=gold_certificate,
            task=task,
            namespace_suffix=f"Replay{index}",
        )
        final_path.write_text(final_source, encoding="utf-8")
        replay_path.write_text(replay_source, encoding="utf-8")
        final_command = run_command(
            ["lake", "env", "lean", str(final_path)],
            cwd=root / "Lean",
            timeout_seconds=600,
        )
        replay_command = run_command(
            ["lake", "env", "lean", str(replay_path)],
            cwd=root / "Lean",
            timeout_seconds=600,
        )
        gold_hash = "sha256:" + sha256_file(gold_file)
        result = None
        if final_command.ok and replay_command.ok and prompt_safe:
            result = accepted_np_hard_authoring_result_v2(
                task=task,
                candidate_hashes={node.node_id: gold_hash for node in task.gap_nodes},
                final_certificate=sha256_id(final_command.to_dict()),
                replay_certificate=sha256_id(replay_command.to_dict()),
                lean_diagnostics=("isolated exact-endpoint Gold replay accepted",),
                policy_diagnostics=("public task and prompt contain no Gold metadata",),
                model_calls=(),
            )
        matched = result is not None
        rows.append(
            {
                "task_class": task.task_class,
                "request_id": task.request_id,
                "source_problem": task.source_problem.to_dict(),
                "target_problem": task.target_problem.to_dict(),
                "gap_node_count": len(task.gap_nodes),
                "editable_declaration_count": len(task.editable_declarations),
                "task": task.to_dict(),
                "prompt_sha256": sha256_id(prompt),
                "prompt_safe": prompt_safe,
                "gold_module": gold_module,
                "gold_source_sha256": gold_hash,
                "final_command": final_command.to_dict(),
                "replay_command": replay_command.to_dict(),
                "result": result.to_dict(task) if result is not None else None,
                "matched_contract": matched,
            }
        )

    task_counts = {
        task_class: sum(row["task_class"] == task_class for row in rows)
        for task_class in ("semantic_proof", "program_composition", "program_synthesis")
    }
    passed = prebuild.ok and all(row["matched_contract"] for row in rows) and task_counts == {
        "semantic_proof": 2,
        "program_composition": 2,
        "program_synthesis": 1,
    }
    report = {
        "schema_version": NP_HARD_AUTHORING_CONTRACT_REPORT_SCHEMA_V1,
        "task_schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V2,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "G-B",
        "qualification_scope": "contract_and_isolated_gold_replay_not_multi_gap_runtime",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "prebuild": prebuild.to_dict(),
        "metrics": {
            "task_count": len(rows),
            "task_class_counts": task_counts,
            "request_round_trip_count": len(tasks),
            "exact_endpoint_final_count": sum(
                row["final_command"]["exit_code"] == 0 for row in rows
            ),
            "independent_replay_count": sum(
                row["replay_command"]["exit_code"] == 0 for row in rows
            ),
            "prompt_safe_count": sum(row["prompt_safe"] for row in rows),
            "model_calls": 0,
            "compiler_inserted_math_token_count": 0,
        },
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report

