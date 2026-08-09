import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_cli_help_exposes_declaration_only_interface() -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "run_hardness_agent.py"), "--help"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    for flag in (
        "--module",
        "--source",
        "--membership",
        "--target",
        "--planner",
        "--catalog-mode",
        "--authoring",
        "--authoring-attempts",
        "--resume",
    ):
        assert flag in completed.stdout
    assert "model-auto" in completed.stdout
    assert "model-required" in completed.stdout
    assert "ir_components" in completed.stdout
    assert "component_catalog" in completed.stdout


def test_deepseek_smoke_help_is_independent_of_lean() -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "run_deepseek_smoke.py"), "--help"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    assert "without starting Lean" in completed.stdout


def test_model_trials_help_defaults_to_three_isolated_repetitions() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_model_trials.py"),
            "--help",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    assert "model-auto" in completed.stdout
    assert "model-required" in completed.stdout
    assert "--repetitions" in completed.stdout


def test_benchmark_cli_lists_v2_suites_without_running_lean() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    assert '"benchmark_id": "hardness-agent-e2e"' in completed.stdout
    assert '"knapsack-native-cook-levin"' in completed.stdout
    assert '"code": "phase_gate"' in completed.stdout

    phase_two = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "2",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_two.returncode == 0
    assert '"knapsack-native-cook-levin-clique"' in phase_two.stdout
    assert '"representation-mismatch-gap"' in phase_two.stdout
    assert '"code": "phase_gate"' in phase_two.stdout

    phase_three = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "3",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_three.returncode == 0
    assert '"missing-native-membership-gap"' in phase_three.stdout
    assert '"closed-family-template-authoring"' in phase_three.stdout
    assert '"code": "phase_gate"' in phase_three.stdout

    phase_four = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "4",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_four.returncode == 0
    assert '"closed-family-template-authoring"' in phase_four.stdout
    assert '"program-indexed-reduction-authoring"' in phase_four.stdout
    assert '"code": "phase_gate"' in phase_four.stdout

    phase_five = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "5",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_five.returncode == 0
    assert '"program-indexed-reduction-authoring"' in phase_five.stdout
    assert '"exact-registered-native-membership"' in phase_five.stdout
    assert '"code": "phase_gate"' in phase_five.stdout

    phase_six = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "6",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_six.returncode == 0
    assert '"native-membership-deterministic-authoring"' in phase_six.stdout
    assert '"backend-completeness-cannot-pass-native-gate"' in phase_six.stdout
    assert '"model-semantic-proof-authoring"' in phase_six.stdout

    phase_seven = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "7",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_seven.returncode == 0
    assert '"model-semantic-proof-authoring"' in phase_seven.stdout
    assert '"authoring-lawful-presentation"' in phase_seven.stdout
    assert '"code": "phase_gate"' in phase_seven.stdout

    phase_thirteen = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "13",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_thirteen.returncode == 0
    assert '"authoring-pair-list-membership"' in phase_thirteen.stdout
    assert '"spring2015-exactly-one-neighbor"' in phase_thirteen.stdout
    assert '"code": "phase_gate"' in phase_thirteen.stdout

    phase_fourteen = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_hardness_benchmark.py"),
            "--list",
            "--agent-phase",
            "14",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert phase_fourteen.returncode == 0
    assert '"spring2015-exactly-one-neighbor"' in phase_fourteen.stdout
    assert '"spring2015-exactly-one-neighbor-wrong-endpoint"' in phase_fourteen.stdout
    assert '"skipped_cases": []' in phase_fourteen.stdout
