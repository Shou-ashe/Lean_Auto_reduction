from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "scripts" / "run_hardness_benchmark.py"
PROVER = ROOT / "scripts" / "prove_np_hard.py"
GENERAL_PROVER = ROOT / "scripts" / "prove_np_hard_general.py"


def test_repository_has_exactly_one_benchmark_runner_script() -> None:
    assert sorted((ROOT / "scripts").glob("*.py")) == [
        PROVER,
        GENERAL_PROVER,
        RUNNER,
    ]
    run_scripts = sorted((ROOT / "scripts").rglob("run_*.py"))
    assert run_scripts == [RUNNER]
    assert not (ROOT / "scripts" / "Legacy").exists()
    assert not (ROOT / "Gate").exists()
    assert not (ROOT / "compare" / "OneShotLLM" / "run_benchmark.py").exists()


def test_runner_does_not_delegate_to_python_scripts() -> None:
    source = RUNNER.read_text(encoding="utf-8")
    assert "subprocess" not in source
    assert "sys.executable" not in source
    assert "runpy" not in source
    assert ".py\"" not in source
    assert ".py'" not in source

    boolean_backend = (
        ROOT / "agent" / "hardness" / "boolean_csp_np_hard_benchmark.py"
    ).read_text(encoding="utf-8")
    assert "scripts/" not in boolean_backend
    assert "subprocess" not in boolean_backend


def test_only_runner_lists_exactly_all_78_suite_cases() -> None:
    completed = subprocess.run(
        [sys.executable, str(RUNNER), "--list"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["case_count"] == {
        "capability": 32,
        "frontier": 2,
        "exact_edge": 24,
        "boolean_csp": 20,
        "total": 78,
    }
    listed = [case_id for cases in payload["lanes"].values() for case_id in cases]
    assert len(listed) == len(set(listed)) == 78

    suite_cases: set[str] = set()
    for path in (ROOT / "Benchmark" / "Hardness" / "Suites").glob("*.json"):
        value = json.loads(path.read_text(encoding="utf-8"))
        suite_cases.update(
            str(case["case_id"])
            for case in value.get("cases", ())
            if isinstance(case, dict) and "case_id" in case
        )
    assert set(listed) == suite_cases
