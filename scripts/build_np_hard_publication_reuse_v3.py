#!/usr/bin/env python3
"""Freeze the H-K.3 34-case reuse manifest against an active catalog."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_publication_reuse import (  # noqa: E402
    NPHardPublicationReuseError,
    build_publication_reuse_manifest,
)
from agent.hardness.np_hard_publication_activation import (  # noqa: E402
    PUBLICATION_CATALOG_RELATIVE,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--base-manifest",
        type=Path,
        default=ROOT / "Benchmark/Hardness/CAPABILITY_MANIFEST_V2.json",
    )
    parser.add_argument(
        "--publication-catalog",
        type=Path,
        default=ROOT / PUBLICATION_CATALOG_RELATIVE,
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Publications/PUBLICATION_REUSE_MANIFEST_V3.json",
    )
    parser.add_argument("--repo-root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    try:
        manifest = build_publication_reuse_manifest(
            root=args.repo_root,
            base_manifest_path=args.base_manifest,
            publication_catalog_path=args.publication_catalog,
            output_path=args.output,
        )
    except (NPHardPublicationReuseError, OSError, ValueError) as error:
        print(
            json.dumps(
                {
                    "passed": False,
                    "failure_code": getattr(error, "code", "reuse_manifest_failed"),
                    "error": str(error),
                },
                ensure_ascii=False,
            ),
            file=sys.stderr,
        )
        return 2
    print(
        json.dumps(
            {
                "passed": True,
                "manifest_id": manifest["manifest_id"],
                "case_count": manifest["case_count"],
                "direct_reuse_count": len(manifest["reuse_policy"]["direct"]),
                "transitive_reuse_count": len(
                    manifest["reuse_policy"]["transitive"]
                ),
                "output": str(args.output.resolve()),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
