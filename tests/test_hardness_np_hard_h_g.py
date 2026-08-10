from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from agent.hardness.np_hard_input import discover_np_hard_input_module
from agent.hardness.np_hard_production import (
    FORMAL_MAX_RETRIES,
    FORMAL_MAX_TOKENS,
    FORMAL_MODEL,
    FORMAL_REASONING_EFFORT,
    FORMAL_TIMEOUT_SECONDS,
    is_formal_np_hard_qualification_config,
    load_np_hard_production_model_config,
    public_np_hard_status,
    required_model_call_budget,
)


ROOT = Path(__file__).resolve().parents[1]


def test_production_model_precedence_is_cli_over_env_over_formal_defaults(tmp_path) -> None:
    env_file = tmp_path / ".env"
    env_file.write_text(
        "DEEPSEEK_MODEL=dotenv-model\n"
        "DEEPSEEK_TIMEOUT_SECONDS=222\n"
        "DEEPSEEK_MAX_TOKENS=12000\n"
        "DEEPSEEK_MAX_RETRIES=1\n"
        "DEEPSEEK_REASONING_EFFORT=medium\n",
        encoding="utf-8",
    )
    from_env = load_np_hard_production_model_config(
        env_file=env_file,
        environ={"DEEPSEEK_MODEL": "environment-model"},
    )
    assert from_env.model == "environment-model"
    assert from_env.timeout_seconds == 222
    assert from_env.max_tokens == 12000
    assert from_env.max_retries == 1
    assert from_env.reasoning_effort == "medium"

    explicit = load_np_hard_production_model_config(
        env_file=env_file,
        environ={"DEEPSEEK_MODEL": "environment-model"},
        model="cli-model",
        timeout_seconds=333,
        max_tokens=15000,
        max_retries=0,
        reasoning_effort="low",
    )
    assert explicit.model == "cli-model"
    assert explicit.timeout_seconds == 333
    assert explicit.max_tokens == 15000
    assert explicit.max_retries == 0
    assert explicit.reasoning_effort == "low"

    defaults = load_np_hard_production_model_config(env_file=None, environ={})
    assert defaults.model == FORMAL_MODEL
    assert defaults.timeout_seconds == FORMAL_TIMEOUT_SECONDS
    assert defaults.max_tokens == FORMAL_MAX_TOKENS
    assert defaults.max_retries == FORMAL_MAX_RETRIES
    assert defaults.reasoning_effort == FORMAL_REASONING_EFFORT
    assert is_formal_np_hard_qualification_config(defaults)


def test_call_budget_reserves_every_attempt_for_every_dag_node() -> None:
    assert required_model_call_budget(gap_node_count=0, attempt_budget=4) == 0
    assert required_model_call_budget(gap_node_count=5, attempt_budget=4) == 20


def test_public_cli_statuses_are_disjoint() -> None:
    assert public_np_hard_status(internal_status="VERIFIED", failure_code=None) == "VERIFIED"
    assert public_np_hard_status(
        internal_status="BLOCKED", failure_code="auxiliary_or_non_target"
    ) == "BLOCKED_NOT_TARGET"
    assert public_np_hard_status(
        internal_status="BLOCKED", failure_code="no_forward_path_from_hardness_seed"
    ) == "BLOCKED_MISSING_PREREQUISITE"
    assert public_np_hard_status(
        internal_status="BLOCKED", failure_code="model_provider_unavailable"
    ) == "FAILED_MODEL"
    assert public_np_hard_status(
        internal_status="FAILED", failure_code="independent_replay_failed"
    ) == "FAILED_LEAN"
    assert public_np_hard_status(
        internal_status="FAILED", failure_code="ambiguous_lawful_presentation"
    ) == "INPUT_ERROR"


def test_full_public_problem_discovers_its_module() -> None:
    declaration = (
        "ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem"
    )
    assert discover_np_hard_input_module(
        root=ROOT, requested_term=declaration
    ) == "ComplexityReduction.Problems.Karp21.GraphAtoms"


def test_shortest_cli_command_no_longer_requires_module_or_budget_flags() -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts/prove_np_hard.py"), "--help"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    assert "--module MODULE" in completed.stdout
    assert "optional public module override" in completed.stdout
    assert "auto mode reserves attempts" in completed.stdout
    assert "--qualification-authoring" in completed.stdout


def test_production_runners_contain_no_deepseek_chat_default() -> None:
    production_files = [
        ROOT / "scripts/prove_np_hard.py",
        ROOT / "scripts/run_np_hard_release_stability.py",
        ROOT / "scripts/run_np_hard_h_e_heldout.py",
        ROOT / "scripts/run_np_hard_h_f_heldout.py",
    ]
    assert all("deepseek-chat" not in path.read_text(encoding="utf-8") for path in production_files)


def test_release_stability_cli_exposes_parallel_case_workers() -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "scripts/run_np_hard_release_stability.py"), "--help"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0
    assert "--jobs JOBS" in completed.stdout
    assert "parallel case workers within each stability round" in completed.stdout
