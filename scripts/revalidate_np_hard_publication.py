#!/usr/bin/env python3
"""Revalidate active publications and fail closed on dependency drift."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_publication_activation import (  # noqa: E402
    NPHardPublicationActivationError,
    PUBLICATION_CATALOG_RELATIVE,
    revalidate_publication_catalog,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="mark drifted publications stale and regenerate the active aggregate"
    )
    command.add_argument("--repo-root", type=Path, default=ROOT)
    command.add_argument(
        "--catalog",
        type=Path,
        default=ROOT / PUBLICATION_CATALOG_RELATIVE,
    )
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Publications/H_K_4_PUBLICATION_AUDIT_REPORT.json",
    )
    return command


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        report = revalidate_publication_catalog(
            repo_root=args.repo_root,
            catalog_path=args.catalog,
            output_report=args.output,
        )
    except NPHardPublicationActivationError as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "failure_code": error.code,
                    "failure_message": error.message,
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 2
    print(
        json.dumps(
            {
                "passed": report["passed"],
                "report_id": report["report_id"],
                "active_count": report["active_count"],
                "stale_count": report["stale_count"],
                "superseded_count": report["superseded_count"],
                "report": str(args.output.resolve()),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
