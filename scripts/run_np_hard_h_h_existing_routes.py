#!/usr/bin/env python3
"""Qualify every public existing-route identity through the production entrypoint."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_existing_route_qualification import (  # noqa: E402
    run_public_existing_route_qualification,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--matrix",
        type=Path,
        default=ROOT / "Gate/NP_HARD_TARGET_MATRIX.json",
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=ROOT / "Gate/NP_HARD_H_F_INVENTORY.json",
    )
    parser.add_argument(
        "--heldout-suite",
        type=Path,
        default=ROOT / "Gate/Suites/np_hard_h_h_existing_route_inputs.json",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports/PUBLIC_EXISTING_ROUTE_QUALIFICATION_REPORT.json",
    )
    parser.add_argument("--lean-timeout", type=int, default=900)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--publish-matrix", action="store_true")
    arguments = parser.parse_args()
    report = run_public_existing_route_qualification(
        root=ROOT,
        matrix_path=arguments.matrix,
        inventory_path=arguments.inventory,
        heldout_suite_path=arguments.heldout_suite,
        output_root=arguments.output_root,
        report_path=arguments.report,
        lean_timeout_seconds=arguments.lean_timeout,
        jobs=max(1, arguments.jobs),
        publish_matrix=arguments.publish_matrix,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

