#!/usr/bin/env python3
"""Run the full 8-case Stage-M suite without external HTTP calls."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.typed_authoring_benchmark import DEFAULT_SUITE, run_full_suite  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--suite", type=Path, default=DEFAULT_SUITE)
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "typed-authoring-offline",
    )
    command.add_argument("--jobs", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1800)
    command.add_argument("--run-label", default="stage-m-typed-authoring-offline")
    return command


def main() -> int:
    args = parser().parse_args()
    report, code = run_full_suite(
        suite_file=args.suite,
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
