#!/usr/bin/env python3
"""Materialize a reusable IR catalog snapshot from one successful Lean probe.

This is an offline maintenance command.  Normal DeepSeek benchmark runs consume
the resulting JSON and therefore do not start Lean before final validation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import (  # noqa: E402
    load_benchmark_manifest,
    select_benchmark_cases,
)
from agent.hardness.catalog import build_all_catalogs  # noqa: E402
from agent.hardness.probe import parse_probe_output  # noqa: E402


PROBE_RE = re.compile(
    r'^#hardness_probe_to_(flat|ir) "([0-9a-f]+)" ([A-Za-z0-9_.\']+) '
    r"([A-Za-z0-9_.']+)$"
)


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description="Create the offline IR catalog snapshot")
    command.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Gate" / "MANIFEST.json",
    )
    command.add_argument("--probe-source", type=Path, required=True)
    command.add_argument(
        "--probe-command",
        type=Path,
        help=(
            "reuse a previously recorded successful probe command; when omitted, "
            "run the supplied probe source against the compiled Lean library"
        ),
    )
    command.add_argument(
        "--probe-command-output",
        type=Path,
        help="optionally record a directly executed probe command as JSON",
    )
    command.add_argument(
        "--lean-root",
        type=Path,
        default=ROOT / "Lean",
        help="Lake project used when --probe-command is omitted",
    )
    command.add_argument("--lean-timeout", type=int, default=900)
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Reports" / "IR_CATALOG_SNAPSHOT.json",
    )
    return command


def run_probe_source(*, source: Path, lean_root: Path, timeout: int) -> dict[str, Any]:
    started = time.monotonic()
    command = ["lake", "env", "lean", str(source.resolve())]
    try:
        completed = subprocess.run(
            command,
            cwd=lean_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        return {
            "command": command,
            "duration_seconds": round(time.monotonic() - started, 3),
            "exit_code": completed.returncode,
            "stdout": completed.stdout,
            "stderr": completed.stderr,
            "timed_out": False,
        }
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout if isinstance(error.stdout, str) else ""
        stderr = error.stderr if isinstance(error.stderr, str) else ""
        return {
            "command": command,
            "duration_seconds": round(time.monotonic() - started, 3),
            "exit_code": 124,
            "stdout": stdout,
            "stderr": stderr,
            "timed_out": True,
        }


def main() -> int:
    arguments = parser().parse_args()
    manifest = load_benchmark_manifest(arguments.manifest)
    selection = select_benchmark_cases(
        manifest, suite_ids=("ir-feasibility",), agent_phase=1
    )
    cases = selection.runnable
    by_key = {
        (case.catalog_mode, case.source, case.target): case
        for case in cases
    }
    nonce_by_case: dict[str, str] = {}
    probe_source_text = arguments.probe_source.read_text(encoding="utf-8")
    for line in probe_source_text.splitlines():
        match = PROBE_RE.fullmatch(line.strip())
        if match is None:
            continue
        short_mode, nonce, source, target = match.groups()
        mode = "flat_api" if short_mode == "flat" else "ir_components"
        case = by_key.get((mode, source, target))
        if case is None:
            raise ValueError(f"probe line does not match the benchmark manifest: {line}")
        nonce_by_case[case.id] = nonce
    if set(nonce_by_case) != {case.id for case in cases}:
        raise ValueError("probe source does not contain every IR feasibility case")

    if arguments.probe_command is None:
        command = run_probe_source(
            source=arguments.probe_source,
            lean_root=arguments.lean_root,
            timeout=arguments.lean_timeout,
        )
        if arguments.probe_command_output is not None:
            write_json(arguments.probe_command_output, command)
    else:
        command = json.loads(arguments.probe_command.read_text(encoding="utf-8"))
    if command.get("exit_code") != 0 or command.get("timed_out") is not False:
        raise ValueError("catalog snapshot requires a successful Lean probe command")
    stdout = command.get("stdout")
    stderr = command.get("stderr")
    if not isinstance(stdout, str) or not isinstance(stderr, str):
        raise ValueError("probe command JSON does not contain textual stdout/stderr")

    probes: dict[str, Any] = {}
    fingerprints: set[str] = set()
    inventory_ids: set[tuple[str, ...]] = set()
    for case in cases:
        probe = parse_probe_output(
            stdout=stdout,
            stderr=stderr,
            nonce=nonce_by_case[case.id],
        )
        probes[case.id] = probe
        fingerprints.add(probe.registry_fingerprint)
        inventory_ids.add(tuple(entry.entry_id for entry in probe.inventory_entries))
    if len(fingerprints) != 1 or len(inventory_ids) != 1:
        raise ValueError("probe observations do not share one stable inventory")

    first = probes[cases[0].id]
    catalogs = build_all_catalogs(
        first.inventory_entries,
        registry_fingerprint=first.registry_fingerprint,
    )
    snapshot = {
        "schema_version": "hardness_ir_catalog_snapshot_v2",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": {
            "kind": "successful_compiled_library_probe",
            "probe_stdout_sha256": hashlib.sha256(stdout.encode("utf-8")).hexdigest(),
            "probe_duration_seconds": command.get("duration_seconds"),
        },
        "registry_fingerprint": first.registry_fingerprint,
        "endpoint_topology": {
            "schema_version": "hardness_endpoint_topology_v1",
            "producer": "lean_whnf_endpoint_hash",
            "registry_fingerprint": first.registry_fingerprint,
        },
        "inventory_entry_count": len(first.inventory_entries),
        "inventory_entries": [entry.to_dict() for entry in first.inventory_entries],
        "catalogs": {
            mode: catalogs[mode].to_dict()
            for mode in ("flat_api", "ir_components")
        },
        "cases": [
            {
                "id": case.id,
                "catalog_mode": case.catalog_mode,
                "source_declaration": case.source,
                "source_display": probes[case.id].source_display,
                "source_node_id": probes[case.id].source_node_id,
                "target_declaration": case.target,
                "target_display": next(
                    target.display
                    for target in probes[case.id].targets
                    if target.target_declaration == case.target
                ),
                "target_node_id": next(
                    target.node_id
                    for target in probes[case.id].targets
                    if target.target_declaration == case.target
                ),
            }
            for case in cases
        ],
    }
    write_json(arguments.output, snapshot)
    print(
        json.dumps(
            {
                "status": "WRITTEN",
                "output": str(arguments.output.resolve()),
                "inventory_entry_count": len(first.inventory_entries),
                "registry_fingerprint": first.registry_fingerprint,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
