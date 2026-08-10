#!/usr/bin/env python3
"""Build fresh same-fingerprint snapshots for the Stage-J contract."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_stage_i_expansion_snapshots import main  # noqa: E402


def _has_option(arguments: list[str], name: str) -> bool:
    return name in arguments or any(item.startswith(name + "=") for item in arguments)


if __name__ == "__main__":
    arguments = sys.argv[1:]
    defaults = {
        "--suite": ROOT / "Gate" / "Suites" / "frontier_efficiency.json",
        "--output-root": ROOT / ".reduction-agent" / "frontier-efficiency-snapshots",
    }
    injected: list[str] = []
    for option, value in defaults.items():
        if not _has_option(arguments, option):
            injected.extend((option, str(value)))
    sys.argv = [sys.argv[0], *injected, *arguments]
    raise SystemExit(main())
