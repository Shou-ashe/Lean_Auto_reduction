#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.model_client import DeepSeekConfig  # noqa: E402
from agent.hardness.np_hard_h_e_benchmark import run_np_hard_h_e_heldout  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate/Suites/np_hard_h_e_heldout_inputs.json",
    )
    parser.add_argument(
        "--oracle",
        type=Path,
        default=ROOT / "Evaluation/np_hard_h_e_heldout_oracle.json",
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=ROOT / "Gate/NP_HARD_H_E_INVENTORY.json",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports/NP_HARD_H_E_HELDOUT_REPORT.json",
    )
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default="deepseek-v4-flash")
    parser.add_argument("--model-timeout", type=int, default=300)
    parser.add_argument("--model-max-tokens", type=int, default=16000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    arguments = parser.parse_args()
    deepseek = replace(
        DeepSeekConfig.from_environment(env_file=arguments.env_file),
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
    )
    report = run_np_hard_h_e_heldout(
        root=ROOT,
        suite_path=arguments.suite,
        oracle_path=arguments.oracle,
        output_root=arguments.output_root,
        report_path=arguments.report,
        inventory_path=arguments.inventory,
        deepseek=deepseek,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
