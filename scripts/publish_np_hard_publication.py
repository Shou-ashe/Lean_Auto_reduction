#!/usr/bin/env python3
"""Explicitly commit H-K.1 reviewed candidates into the production catalog."""

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
    publish_reviewed_candidates,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "commit exact reviewed candidate content IDs, rebuild the generated "
            "hardness aggregate, and verify production catalog discovery"
        )
    )
    command.add_argument("--review-report", type=Path, required=True)
    command.add_argument(
        "--candidate-id",
        action="append",
        required=True,
        help="exact reviewed candidate_content_id; repeat for each commit",
    )
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Publications/H_K_2_PUBLICATION_ACTIVATION_REPORT.json",
    )
    command.add_argument("--repo-root", type=Path, default=ROOT)
    command.add_argument("--timeout-seconds", type=int, default=1200)
    command.add_argument(
        "--skip-production-catalog-rebuild",
        action="store_true",
        help="development-only: do not claim production resolver discovery",
    )
    return command


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        report = publish_reviewed_candidates(
            review_report=args.review_report,
            candidate_ids=args.candidate_id,
            repo_root=args.repo_root,
            output_report=args.output,
            timeout_seconds=args.timeout_seconds,
            rebuild_production_catalogs=not args.skip_production_catalog_rebuild,
        )
    except NPHardPublicationActivationError as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "failure_code": error.code,
                    "failure_message": error.message,
                    "publication_activation_performed": False,
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
                "passed": True,
                "report_id": report["report_id"],
                "published_count": report["published_count"],
                "publication_catalog_id": report["publication_catalog"]["catalog_id"],
                "publication_activation_performed": True,
                "report": str(args.output.resolve()),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
