from __future__ import annotations

import json
import sys
from pathlib import Path

from agent.hardness.models import CommandResult
import scripts.run_stage_p_offline_benchmark as runner


def test_offline_runner_publishes_24_and_72_reports(
    tmp_path: Path, monkeypatch
) -> None:
    worker_report = tmp_path / "worker.json"
    worker_report.write_text(
        json.dumps(
            {
                "status": "VERIFIED",
                "gates": {"worker": True},
                "performance": {"warm_p50_seconds": 0.1},
                "isolation": {"pass_rate": 1.0},
            }
        ),
        encoding="utf-8",
    )
    output_root = tmp_path / "output"
    canonical = tmp_path / "canonical.json"
    monkeypatch.setattr(
        runner,
        "run_command",
        lambda command, **kwargs: CommandResult(
            command=tuple(command),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.01,
        ),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_stage_p_offline_benchmark.py",
            "--worker-report",
            str(worker_report),
            "--output-root",
            str(output_root),
            "--canonical-report",
            str(canonical),
        ],
    )

    assert runner.main() == 0
    report = json.loads(canonical.read_text(encoding="utf-8"))
    assert report["status"] == "VERIFIED"
    assert report["summary"]["protocol_expected_count"] == 24
    assert report["summary"]["mutation_expected_count"] == 72
    assert report["summary"]["model_generated_case_count"] == 0
    assert report["summary"]["aggregate_candidate_declaration_count"] == 24
    assert all(report["gates"].values())
