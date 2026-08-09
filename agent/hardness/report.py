"""Report serialization kept separate from proof-producing Lean source."""

from __future__ import annotations

from pathlib import Path

from .models import AgentResult
from .state import JobStore


def write_report(store: JobStore, result: AgentResult, *, root: Path) -> Path:
    report = store.directory / "report.json"
    try:
        result.report_file = str(report.resolve().relative_to(root.resolve()))
    except ValueError:
        result.report_file = str(report.resolve())
    store.write_json("report.json", result.to_dict())
    return report
