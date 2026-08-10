#!/usr/bin/env python3
"""Run the full H-K.3 publication reuse benchmark with real DeepSeek fallback."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)
from agent.hardness.np_hard_publication_reuse import (  # noqa: E402
    NPHardPublicationReuseError,
    run_publication_reuse_benchmark,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Publications/PUBLICATION_REUSE_MANIFEST_V3.json",
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=None)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    args = parser.parse_args(argv)
    report = args.report or args.output_root / "report.json"
    try:
        deepseek = load_np_hard_production_model_config(
            env_file=args.env_file,
            model=args.model,
            timeout_seconds=args.model_timeout,
            max_tokens=args.model_max_tokens,
            max_retries=args.model_max_retries,
            reasoning_effort=args.reasoning_effort,
        )
        result = run_publication_reuse_benchmark(
            root=ROOT,
            manifest_path=args.manifest,
            output_root=args.output_root,
            report_path=report,
            deepseek=deepseek,
            jobs=args.jobs,
        )
    except (NPHardPublicationReuseError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": getattr(error, "code", "reuse_runner_failed"),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "run_valid": result["run_valid"],
                "run_id": result["run_id"],
                "reuse_execution": result["reuse_execution"],
                "metrics": result["metrics"],
                "report": str(report.resolve()),
            },
            ensure_ascii=False,
        )
    )
    return 0 if result["run_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
