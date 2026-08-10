#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_production import load_np_hard_production_model_config  # noqa: E402
from agent.hardness.np_hard_release_benchmark import run_np_hard_h_d_heldout  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports/NP_HARD_H_D_HELDOUT_REPORT.json",
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
    report = run_np_hard_h_d_heldout(
        root=ROOT,
        output_root=arguments.output_root,
        report_path=arguments.report,
        deepseek=deepseek,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
