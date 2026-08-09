from __future__ import annotations

import hashlib
import json
from pathlib import Path

import scripts.run_deepseek_stage_p_open_world_benchmark as runner
import scripts.build_stage_p_stability_aggregate as aggregate
from agent.hardness.stage_p_contract import StagePContractError
from agent.hardness.stage_p_real_benchmark import _failed_row
from agent.hardness.stage_p_real_benchmark import _render_worker_diagnostics


def test_real_runner_shortcut_audit_resolves_own_path() -> None:
    audit = runner._implementation_shortcut_audit()
    runner_name = "scripts/run_deepseek_stage_p_open_world_benchmark.py"
    assert runner_name in audit["files"]
    assert audit["case_specific_branch_count"] == 0
    assert audit["family_specific_branch_count"] == 0
    assert Path(runner.ROOT / runner_name).is_file()


def test_render_worker_diagnostics_includes_position_and_full_message() -> None:
    diagnostics = [
        {
            "severity": 1,
            "message": "Type mismatch\n  True\nhas type\n  Prop\nbut is expected to have type\n  programProbe",
            "range": {
                "start": {"line": 6, "character": 4},
                "end": {"line": 6, "character": 14},
            },
        }
    ]
    rendered = _render_worker_diagnostics(
        diagnostics, source_path=Path("Generated/StageP/Capability.lean")
    )
    assert rendered.startswith("Capability.lean:7:5: error: Type mismatch")
    assert "but is expected to have type" in rendered
    assert "programProbe" in rendered


def test_render_worker_diagnostics_passthrough_without_range() -> None:
    diagnostics = [{"severity": 1, "message": "Candidate.lean:8:2: error: unsolved goals"}]
    assert _render_worker_diagnostics(diagnostics) == "Candidate.lean:8:2: error: unsolved goals"


def test_semantic_source_hashes_are_bare_64_char_digests() -> None:
    hashes = runner.semantic_source_hashes()
    assert set(hashes) == {
        "stage_p_input_source_sha256",
        "producer_support_source_sha256",
        "exact_cover_standard_helper_sha256",
        "hidden_semantic_feasibility_sha256",
    }
    for key, value in hashes.items():
        assert len(value) == 64
        assert int(value, 16) >= 0
    # Frozen P-A contract evidence uses the same bare byte sha256 digests.
    expected = hashlib.sha256(runner.STAGE_P_INPUT_SOURCE.read_bytes()).hexdigest()
    assert hashes["stage_p_input_source_sha256"] == expected


def test_stability_aggregate_accepts_three_independent_verified_runs(tmp_path: Path) -> None:
    import json

    source = json.loads(
        runner.ROOT.joinpath(
            "Benchmark/Hardness/STAGE_P_IMPLEMENTATION_REAL_REPORT.json"
        ).read_text(encoding="utf-8")
    )
    paths = []
    for index in range(1, 4):
        report = json.loads(json.dumps(source))
        report["run_id"] = f"stage-p-real-stability-{index}"
        report["output_root"] = f"/tmp/stage-p-stability-output-{index}"
        report["started_at"] = f"2026-08-05T12:0{index}:00.000000+00:00"
        path = tmp_path / f"stability-{index}.json"
        path.write_text(json.dumps(report), encoding="utf-8")
        paths.append(path)
    output = tmp_path / "aggregate.json"
    import sys

    sys.argv = [
        "build_stage_p_stability_aggregate.py",
        *(str(path) for path in paths),
        "--output",
        str(output),
    ]
    assert aggregate.main() == 0
    payload = json.loads(output.read_text(encoding="utf-8"))
    assert payload["status"] == "VERIFIED"
    assert payload["summary"]["outcomes_stable"] is True
    assert payload["summary"]["gap_sequences_stable"] is True
    assert payload["summary"]["source_provenance_stable"] is True
    assert payload["summary"]["per_run_lean_replay_security_stable"] is True


def test_failed_row_reconstructs_audit_evidence(tmp_path: Path, monkeypatch) -> None:
    case_root = tmp_path / "cases" / "p-x"
    call_dir = case_root / "calls" / "g01"
    call_dir.mkdir(parents=True)
    (call_dir / "attempt-01-prompt.json").write_text('{"prompt": "p"}', encoding="utf-8")
    (call_dir / "attempt-01-response.json").write_text(
        '{"ok": true, "called": true, "status_code": 200, "content": "{}"}',
        encoding="utf-8",
    )
    published = case_root / "published" / "cafebabe"
    published.mkdir(parents=True)
    (published / "manifest.json").write_text(
        json.dumps(
            {
                "candidate_source_sha256": "sha256:source",
                "patch_sha256": "sha256:patch",
                "model_response_sha256": "sha256:response",
                "gap_ordinal": 1,
            }
        ),
        encoding="utf-8",
    )
    (case_root / "candidates").mkdir()
    (case_root / "candidates" / "gap-01-diagnostics-1.json").write_text(
        '{"primary_error": "Type mismatch"}', encoding="utf-8"
    )

    class FakeCase:
        id = "p-x"
        stage_p = {"protocol_role": "authoring"}
        objective = "reduce_to"
        coverage = {"family": "graph", "secondary_family": None, "gap_depth": 1}
        expected = type("E", (), {"final_status": "VERIFIED", "final_failure_code": None})()

    row = _failed_row(
        1,
        FakeCase(),
        StagePContractError("authoring_diagnostics_repeated", "repeated"),
        case_root,
    )
    assert row["status"] == "FAILED"
    assert row["failure_code"] == "authoring_diagnostics_repeated"
    assert len(row["calls"]) == 1
    assert row["calls"][0]["gap_ordinal"] == 1
    assert len(row["publications"]) == 1
    assert row["last_accepted_source_sha256"] == "sha256:source"
    assert row["last_accepted_patch_sha256"] == "sha256:patch"
    assert row["last_model_response_sha256"] == "sha256:response"
    assert row["last_diagnostics"]["primary_error"] == "Type mismatch"
