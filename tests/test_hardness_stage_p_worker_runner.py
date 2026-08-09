from __future__ import annotations

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.stage_p_contract import StagePContractError
import scripts.run_stage_p_worker_benchmark as runner


def test_worker_benchmark_source_and_key_are_exact_and_content_addressed(
    tmp_path: Path,
) -> None:
    lean_root = tmp_path / "Lean"
    lean_root.mkdir()
    (lean_root / "lean-toolchain").write_text("leanprover/lean4:test\n", encoding="utf-8")
    (lean_root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    source = runner.build_benchmark_source()
    key = runner.build_worker_key(
        lean_root=lean_root,
        source=source,
        session_id=sha256_id("session"),
    )
    key.validate()
    assert f"namespace {runner.NAMESPACE}" in source
    assert "ContractProbes.proofProbe" in source
    assert key.complete_source_sha256 == sha256_id(source)
    assert key.editable_allowlist == ("candidate_body",)


def test_worker_benchmark_requires_a_fresh_output_root(tmp_path: Path) -> None:
    root = tmp_path / "output"
    root.mkdir()
    (root / "old.json").write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError):
        runner.prepare_fresh_output_root(root)


def test_worker_benchmark_runner_publishes_only_when_all_gates_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    class FakePool:
        def __init__(self, **kwargs: object):
            del kwargs
            self.cache_entries = 0
            self.hit = False

        def start_session(self, *, owner: str, namespace: str) -> str:
            assert owner == "worker-qualification"
            assert namespace == runner.NAMESPACE
            return sha256_id("fake-session")

        def microbenchmark(self, **kwargs: object) -> dict[str, object]:
            assert kwargs["repeat_count"] == 20
            assert kwargs["cold_parallelism"] == 2
            return {
                "cold_p50_seconds": 10.0,
                "warm_p50_seconds": 1.0,
                "gates": {
                    "warm_p50_over_cold_p50": True,
                    "wall_time_reduction": True,
                    "worker_count_within_limit": True,
                },
                "pool": {"cold_fallback_count": 0, "worker_crash_count": 0},
            }

        def validate(self, **kwargs: object) -> SimpleNamespace:
            key = kwargs["key"]
            source_path = Path(kwargs["source_path"])
            if kwargs["owner"] != "worker-qualification":
                raise StagePContractError("lean_worker_session_leak", "foreign owner")
            if key.namespace != runner.NAMESPACE:
                raise StagePContractError("lean_worker_session_leak", "foreign namespace")
            if tuple(kwargs["dependency_sha256"]) != key.dependency_sha256:
                raise StagePContractError("lean_worker_stale_result", "dependency drift")
            if not source_path.is_file():
                raise StagePContractError("lean_worker_stale_result", "deleted source")
            if sha256_id(source_path.read_text(encoding="utf-8")) != key.complete_source_sha256:
                raise StagePContractError("lean_worker_stale_result", "source drift")
            cache_hit = self.hit
            if kwargs.get("use_cache", True):
                self.hit = True
                self.cache_entries = 1
            return SimpleNamespace(verified=True, cache_hit=cache_hit)

        def restart_all(self) -> None:
            self.cache_entries = 0

        def to_dict(self) -> dict[str, int]:
            return {
                "cache_entry_count": self.cache_entries,
                "cold_fallback_count": 0,
                "worker_crash_count": 0,
            }

        def close(self) -> None:
            pass

    output_root = tmp_path / "output"
    canonical = tmp_path / "canonical.json"
    monkeypatch.setattr(runner, "StagePLeanWorkerPool", FakePool)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_stage_p_worker_benchmark.py",
            "--output-root",
            str(output_root),
            "--canonical-report",
            str(canonical),
            "--cold-parallelism",
            "2",
        ],
    )

    assert runner.main() == 0
    report = json.loads(canonical.read_text(encoding="utf-8"))
    assert report["status"] == "VERIFIED"
    assert report["isolation"]["pass_rate"] == 1.0
    assert all(report["gates"].values())
