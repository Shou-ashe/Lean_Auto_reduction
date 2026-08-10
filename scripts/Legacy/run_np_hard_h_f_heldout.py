#!/usr/bin/env python3
# H-F: qualification held-out through the production entry orchestrator.
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_h_f_benchmark import run_np_hard_h_f_qualification_heldout  # noqa: E402
from agent.hardness.np_hard_production import (  # noqa: E402
    is_formal_np_hard_qualification_config,
    load_np_hard_production_model_config,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate/Suites/np_hard_h_f_qualification_inputs.json",
    )
    parser.add_argument(
        "--oracle",
        type=Path,
        default=ROOT / "Evaluation/np_hard_h_f_qualification_oracle.json",
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=ROOT / "Gate/NP_HARD_H_F_INVENTORY.json",
    )
    parser.add_argument(
        "--matrix",
        type=Path,
        default=ROOT / "Gate/NP_HARD_TARGET_MATRIX.json",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports/NP_HARD_H_F_QUALIFICATION_HELDOUT_REPORT.json",
    )
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    arguments = parser.parse_args()
    deepseek = load_np_hard_production_model_config(
        env_file=arguments.env_file,
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
    )
    if not is_formal_np_hard_qualification_config(deepseek):
        print(json.dumps({"passed": False, "failure_code": "qualification_model_profile_mismatch"}))
        return 2
    report = run_np_hard_h_f_qualification_heldout(
        root=ROOT,
        suite_path=arguments.suite,
        oracle_path=arguments.oracle,
        output_root=arguments.output_root,
        report_path=arguments.report,
        inventory_path=arguments.inventory,
        matrix_path=arguments.matrix,
        deepseek=deepseek,
        publish_matrix=True,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
