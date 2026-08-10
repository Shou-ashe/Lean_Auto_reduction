#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_inventory import build_np_hard_library_inventory  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Gate/NP_HARD_H_E_INVENTORY.json",
    )
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
    parser.add_argument("--timeout", type=int, default=1800)
    arguments = parser.parse_args()
    report = build_np_hard_library_inventory(
        root=ROOT,
        report_path=arguments.report,
        suite_path=arguments.suite,
        oracle_path=arguments.oracle,
        timeout_seconds=arguments.timeout,
    )
    print(
        json.dumps(
            {
                "inventory_id": report["inventory_id"],
                "module_count": report["module_count"],
                "presented_problem_count": report["presented_problem_count"],
                "known_forward_route_count": report["known_forward_route_count"],
            }
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
