#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_release_benchmark import (  # noqa: E402
    DEFAULT_RELEASE_CASE_JOBS,
    run_np_hard_release_stability,
)
from agent.hardness.np_hard_production import (  # noqa: E402
    is_formal_np_hard_qualification_config,
    load_np_hard_production_model_config,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=ROOT / "Reports/NP_HARD_RELEASE_STABILITY_AGGREGATE.json")
    parser.add_argument("--suite", type=Path, default=ROOT / "Gate/Suites/np_hard_generalization.json")
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument(
        "--jobs",
        type=int,
        default=DEFAULT_RELEASE_CASE_JOBS,
        help="parallel case workers within each stability round (1..4; formal gate requires >=2)",
    )
    args = parser.parse_args()
    config = load_np_hard_production_model_config(
        env_file=args.env_file,
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
        max_retries=args.model_max_retries,
        reasoning_effort=args.reasoning_effort,
    )
    if not is_formal_np_hard_qualification_config(config):
        print(json.dumps({"passed": False, "failure_code": "qualification_model_profile_mismatch"}))
        return 2
    report = run_np_hard_release_stability(
        root=ROOT,
        suite_path=args.suite,
        output_root=args.output_root,
        report_path=args.report,
        deepseek=config,
        round_count=3,
        jobs=args.jobs,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
