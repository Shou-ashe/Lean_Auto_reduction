#!/usr/bin/env python3
"""Run the answer-free public target-hardness capability benchmark."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_capability import (  # noqa: E402
    CAPABILITY_SPLITS,
    NPHardCapabilityError,
    run_np_hard_capability_benchmark,
)
from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run public NativeTMNPHard capability cases without opening the "
            "scorer-only oracle"
        )
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Archive/CAPABILITY_MANIFEST.json",
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="defaults to <output-root>/report.json",
    )
    parser.add_argument(
        "--split",
        action="append",
        choices=CAPABILITY_SPLITS,
        help="repeat to select splits; defaults to dev/validation/heldout/frontier",
    )
    parser.add_argument(
        "--case-ids",
        action="append",
        default=[],
        help="repeat to restrict to exact case ids within the selected splits",
    )
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    output_root = arguments.output_root.resolve()
    report_path = (
        arguments.report.resolve()
        if arguments.report is not None
        else output_root / "report.json"
    )
    try:
        deepseek = load_np_hard_production_model_config(
            env_file=arguments.env_file,
            model=arguments.model,
            timeout_seconds=arguments.model_timeout,
            max_tokens=arguments.model_max_tokens,
            max_retries=arguments.model_max_retries,
            reasoning_effort=arguments.reasoning_effort,
        )
        report = run_np_hard_capability_benchmark(
            root=ROOT,
            manifest_path=arguments.manifest,
            output_root=output_root,
            report_path=report_path,
            deepseek=deepseek,
            selected_splits=tuple(arguments.split or CAPABILITY_SPLITS),
            selected_case_ids=tuple(arguments.case_ids) or None,
            jobs=arguments.jobs,
        )
    except (NPHardCapabilityError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": getattr(
                        error, "code", "np_hard_capability_runner_failed"
                    ),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "run_valid": report["run_valid"],
                "run_id": report["run_id"],
                "metrics": report["metrics"],
                "parallel_execution": report["parallel_execution"],
                "report": str(report_path),
            },
            ensure_ascii=False,
        )
    )
    return 0 if report["run_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
