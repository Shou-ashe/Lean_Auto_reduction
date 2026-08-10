#!/usr/bin/env python3
"""Build the hash-only audit for ``problems.7z``."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_archive_audit import (  # noqa: E402
    ProblemArchiveAuditError,
    build_problem_archive_audit,
    validate_problem_archive_audit,
    write_problem_archive_audit,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Audit the bundled reduction archive without exposing answers"
    )
    command.add_argument("--archive", type=Path, default=ROOT / "problems.7z")
    command.add_argument(
        "--selection",
        type=Path,
        default=(
            ROOT
            / "Evaluation/np_hard_problem_archive_selection_v1.json"
        ),
        help="frozen scorer-only archive selection/readiness annotations",
    )
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Reports/PROBLEM_ARCHIVE_AUDIT.json",
    )
    command.add_argument("--bsdtar", type=Path, default=None)
    return command


def main() -> int:
    arguments = parser().parse_args()
    try:
        report = build_problem_archive_audit(
            archive_path=arguments.archive,
            selection_path=arguments.selection,
            bsdtar=arguments.bsdtar,
        )
        validate_problem_archive_audit(report)
        write_problem_archive_audit(arguments.output, report)
    except (OSError, UnicodeError, json.JSONDecodeError, ProblemArchiveAuditError) as error:
        code = getattr(error, "code", "archive_audit_failed")
        print(json.dumps({"written": False, "failure_code": code, "error": str(error)}))
        return 1
    print(
        json.dumps(
            {
                "written": True,
                "output": str(arguments.output.resolve()),
                "audit_id": report["audit_id"],
                "metrics": report["metrics"],
            },
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
