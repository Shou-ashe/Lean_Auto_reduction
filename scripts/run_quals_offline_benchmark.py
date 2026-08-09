#!/usr/bin/env python3
"""Run the Stage-N N-C 12-case Quals suite with deterministic model fixtures."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.quals_benchmark import (  # noqa: E402
    DEFAULT_ADVERSARIAL_SUITE,
    DEFAULT_COMPLETENESS_SUITE,
    DEFAULT_FORMALIZATION_SUITE,
    run_full_suite,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--formalization-suite", type=Path, default=DEFAULT_FORMALIZATION_SUITE)
    command.add_argument("--completeness-suite", type=Path, default=DEFAULT_COMPLETENESS_SUITE)
    command.add_argument("--adversarial-suite", type=Path, default=DEFAULT_ADVERSARIAL_SUITE)
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "quals-n-c-offline",
    )
    command.add_argument("--jobs", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1800)
    command.add_argument("--run-label", default="stage-n-c-quals-full-offline")
    return command


def main() -> int:
    args = parser().parse_args()
    report, code = run_full_suite(
        formalization_suite_file=args.formalization_suite,
        completeness_suite_file=args.completeness_suite,
        adversarial_suite_file=args.adversarial_suite,
        output_root=args.output_root,
        jobs=args.jobs,
        real=False,
        deepseek_config=None,
        canonical_report=None,
        lean_timeout_seconds=args.lean_timeout,
        run_label=args.run_label,
    )
    print(json.dumps({"status": report["status"], "report": str(args.output_root / "report.json")}))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
