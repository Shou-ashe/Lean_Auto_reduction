#!/usr/bin/env python3
"""H-F: build the identity-level NP-hard target matrix for the public library.

Rebuilds the Lean-exported library inventory at identity granularity, runs the
same production normalization/catalog/route-search/deterministic-planner
qualification for every unique ``problem_node_id + representation_node_id``
identity, and writes a content-addressed ``NP_HARD_TARGET_MATRIX.json``.
No benchmark oracle or model is consulted during qualification.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_inventory import build_np_hard_library_inventory  # noqa: E402
from agent.hardness.np_hard_target_matrix import (  # noqa: E402
    build_np_hard_target_matrix,
    load_np_hard_target_matrix,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark/Hardness/NP_HARD_H_F_INVENTORY.json",
    )
    parser.add_argument(
        "--matrix",
        type=Path,
        default=ROOT / "Benchmark/Hardness/NP_HARD_TARGET_MATRIX.json",
    )
    parser.add_argument(
        "--output-root", type=Path, default=ROOT / ".reduction-agent" / "h-f-qualification"
    )
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument("--skip-inventory-build", action="store_true")
    arguments = parser.parse_args()

    if arguments.skip_inventory_build:
        inventory = json.loads(arguments.report.read_text(encoding="utf-8"))
    else:
        inventory = build_np_hard_library_inventory(
            root=ROOT,
            report_path=arguments.report,
            timeout_seconds=arguments.timeout,
        )
    matrix = build_np_hard_target_matrix(
        root=ROOT,
        inventory_rows=inventory["entries"],
        matrix_path=arguments.matrix,
        work_root=arguments.output_root,
        lean_timeout_seconds=arguments.timeout,
        jobs=max(1, arguments.jobs),
    )
    merged = build_np_hard_library_inventory(
        root=ROOT,
        report_path=arguments.report,
        matrix_path=arguments.matrix,
        timeout_seconds=arguments.timeout,
    )
    print(
        json.dumps(
            {
                "matrix_id": matrix["matrix_id"],
                "identity_count": matrix["identity_count"],
                "disposition_counts": matrix["disposition_counts"],
                "unclassified_count": matrix["unclassified_count"],
                "inventory_id": merged["inventory_id"],
                "presented_problem_count": merged["presented_problem_count"],
                "unique_problem_identity_count": merged["unique_problem_identity_count"],
                "known_forward_route_count": merged["known_forward_route_count"],
            }
        )
    )
    return 0 if matrix["unclassified_count"] == 0 else 3


if __name__ == "__main__":
    raise SystemExit(main())