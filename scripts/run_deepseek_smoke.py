#!/usr/bin/env python3
"""Run the Phase-7 DeepSeek connectivity smoke without invoking Lean."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Call DeepSeek once and report status/usage without starting Lean"
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument("--timeout", type=int, default=None)
    command.add_argument("--max-tokens", type=int, default=96)
    command.add_argument("--output", type=Path)
    return command


def main() -> int:
    arguments = parser().parse_args()
    config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
    if arguments.timeout is not None:
        if arguments.timeout <= 0:
            parser().error("--timeout must be positive")
        config = replace(config, timeout_seconds=arguments.timeout)
    if arguments.max_tokens <= 0:
        parser().error("--max-tokens must be positive")
    config = replace(config, max_tokens=arguments.max_tokens)
    result = DeepSeekClient(config).smoke()
    report = result.to_dict()
    encoded = json.dumps(report, ensure_ascii=False, sort_keys=True)
    if arguments.output is not None:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    print(encoded)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
