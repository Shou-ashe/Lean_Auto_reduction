#!/usr/bin/env python3
"""Review H-J authored reductions in an isolated H-K shadow workspace.

This command never writes the public ``Lean/Reference/.../Generated`` tree and
never activates the hardness registry.  Until ``MAIN_H_J_FULL_REPORT.json`` is
available, callers may provide an explicit run/score pair; that mode remains a
non-publishable implementation probe even when every shadow audit passes.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_publication import (  # noqa: E402
    NPHardPublicationError,
    SUPPORTED_PUBLICATION_CASES,
    load_h_j_publication_evidence,
    review_publication_candidates,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "extract reduction-only H-J candidates and clean-build them in an "
            "isolated H-K shadow workspace without registry activation"
        )
    )
    evidence = parser.add_mutually_exclusive_group(required=True)
    evidence.add_argument(
        "--h-j-report",
        type=Path,
        help="passing Reports/MAIN_H_J_FULL_REPORT.json",
    )
    evidence.add_argument(
        "--run-report",
        type=Path,
        help="temporary explicit v2 capability run (requires --score-report)",
    )
    parser.add_argument(
        "--score-report",
        type=Path,
        help="temporary explicit v2 capability score",
    )
    parser.add_argument(
        "--case-id",
        action="append",
        choices=tuple(SUPPORTED_PUBLICATION_CASES),
        help="supported public authoring case; repeat to select multiple",
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    parser.add_argument("--lean-root", type=Path, default=ROOT / "Lean")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.run_report is not None and args.score_report is None:
        parser.error("--run-report requires --score-report")
    if args.h_j_report is not None and args.score_report is not None:
        parser.error("--score-report is only valid with --run-report")
    case_ids = args.case_id or list(SUPPORTED_PUBLICATION_CASES)
    try:
        evidence = load_h_j_publication_evidence(
            h_j_report=args.h_j_report,
            run_report=args.run_report,
            score_report=args.score_report,
        )
        report = review_publication_candidates(
            evidence=evidence,
            case_ids=case_ids,
            output_root=args.output_root,
            repo_root=args.repo_root,
            lean_root=args.lean_root,
            timeout_seconds=args.timeout_seconds,
        )
    except NPHardPublicationError as error:
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
                "review_id": report["review_id"],
                "candidate_count": report["candidate_count"],
                "evidence_mode": report["evidence_mode"],
                "publication_eligible": report["publication_eligible"],
                "publication_activation_performed": False,
                "report": str((args.output_root / "review-report.json").resolve()),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
