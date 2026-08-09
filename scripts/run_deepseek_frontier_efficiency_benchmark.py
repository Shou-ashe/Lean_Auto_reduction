#!/usr/bin/env python3
"""Run all Stage-J cases with fresh DeepSeek calls and one final Lean gate."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_deepseek_stage_i_expansion_benchmark import main  # noqa: E402


def _has_option(arguments: list[str], name: str) -> bool:
    return name in arguments or any(item.startswith(name + "=") for item in arguments)


if __name__ == "__main__":
    arguments = sys.argv[1:]
    defaults = {
        "--suite": ROOT / "Benchmark" / "Hardness" / "Suites" / "frontier_efficiency.json",
        "--snapshots-root": ROOT / ".reduction-agent" / "frontier-efficiency-snapshots",
        "--output-root": ROOT / ".reduction-agent" / "deepseek-frontier-efficiency-full",
        "--canonical-report": ROOT / "Benchmark" / "Hardness" / "FRONTIER_EFFICIENCY_REPORT.json",
        "--run-label": "stage-j-frontier-efficiency-full-real-deepseek",
    }
    injected: list[str] = []
    for option, value in defaults.items():
        if not _has_option(arguments, option):
            injected.extend((option, str(value)))
    sys.argv = [sys.argv[0], *injected, *arguments]
    raise SystemExit(main())
