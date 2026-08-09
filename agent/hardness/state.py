"""Content-addressed job identity and append-only state events."""

from __future__ import annotations

import json
import fcntl
import os
import secrets
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .models import RESULT_SCHEMA, canonical_json, sha256_id


STATES = (
    "RECEIVED",
    "INPUT_VALIDATED",
    "CAPABILITIES_SCANNED",
    "PLAN_SELECTED",
    "AUTHORING",
    "CANDIDATE_COMPILED",
    "REGISTRY_REVALIDATED",
    "FINAL_RESOLVED",
    "AXIOM_AUDITED",
    "VERIFIED",
    "BLOCKED",
    "FAILED",
    "CANCELLED",
)


def compute_job_id(payload: dict[str, Any]) -> str:
    return sha256_id(payload)


@dataclass
class JobStore:
    directory: Path

    @property
    def events_path(self) -> Path:
        return self.directory / "events.jsonl"

    @property
    def state_path(self) -> Path:
        return self.directory / "state.json"

    def initialize(self) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)

    @contextmanager
    def exclusive_run(self):
        """Fail closed when two processes target the same writable job directory."""

        self.initialize()
        lock_path = self.directory / ".run.lock"
        token = secrets.token_hex(16)
        payload = canonical_json(
            {
                "schema_version": "hardness_job_lock_v1",
                "pid": os.getpid(),
                "time": datetime.now(timezone.utc).isoformat(),
                "token": token,
            }
        )
        with lock_path.open("a+", encoding="utf-8") as lock:
            try:
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise ValueError(
                    "concurrent hardness job already owns the requested output directory"
                ) from error
            lock.seek(0)
            lock.truncate()
            lock.write(payload)
            lock.flush()
            os.fsync(lock.fileno())
            try:
                yield
            finally:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)

    def path(self, relative_path: str) -> Path:
        relative = Path(relative_path)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("job path must remain inside the job directory")
        path = (self.directory / relative).resolve()
        try:
            path.relative_to(self.directory.resolve())
        except ValueError as error:
            raise ValueError("job path escapes the job directory") from error
        return path

    def write_text(self, relative_path: str, value: str) -> Path:
        path = self.path(relative_path)
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_text(value, encoding="utf-8")
        temporary.replace(path)
        return path

    def write_json(self, relative_path: str, value: Any) -> Path:
        return self.write_text(relative_path, json.dumps(value, indent=2, sort_keys=True) + "\n")

    def transition(self, status: str, *, details: dict[str, Any] | None = None) -> None:
        if status not in STATES:
            raise ValueError(f"unknown hardness job state: {status}")
        current: dict[str, Any] | None = None
        if self.state_path.is_file():
            current = json.loads(self.state_path.read_text(encoding="utf-8"))
        requested_details = details or {}
        if current and current.get("status") == status and current.get("details") == requested_details:
            return
        normal_states = STATES[: STATES.index("VERIFIED") + 1]
        if current and current.get("status") in normal_states and status in normal_states:
            current_index = normal_states.index(current["status"])
            requested_index = normal_states.index(status)
            if current_index >= requested_index:
                return
        event = {
            "schema_version": "hardness_event_v1",
            "time": datetime.now(timezone.utc).isoformat(),
            "status": status,
            "details": requested_details,
        }
        with self.events_path.open("a", encoding="utf-8") as events:
            events.write(canonical_json(event) + "\n")
        self.write_json("state.json", event)


@dataclass(frozen=True)
class ResumeCheckpoint:
    job_id: str
    status: str
    authored_candidate_sha256: str | None
    artifact_sha256: str | None


def _optional_sha256(value: Any, *, label: str) -> str | None:
    if value is None:
        return None
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"resume report has invalid {label}")
    return value


def load_resume_checkpoint(store: JobStore, *, expected_job_id: str) -> ResumeCheckpoint:
    """Load only the minimal, non-authoritative facts needed to audit a resume.

    Paths and declaration names from the old report are deliberately ignored.
    Candidate paths are re-derived from the current typed gap and content-addressed
    job layout before they can affect execution.
    """

    report_path = store.path("report.json")
    if not report_path.is_file():
        raise ValueError("resume requested but the job has no report.json")
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise ValueError("resume report is not valid JSON") from error
    if not isinstance(report, dict) or report.get("schema_version") != RESULT_SCHEMA:
        raise ValueError("resume report has an unsupported schema")
    if report.get("job_id") != expected_job_id:
        raise ValueError("resume report belongs to a different content-addressed job")
    status = report.get("status")
    if status not in STATES:
        raise ValueError("resume report has an invalid job status")
    return ResumeCheckpoint(
        job_id=expected_job_id,
        status=status,
        authored_candidate_sha256=_optional_sha256(
            report.get("authored_candidate_sha256"), label="candidate SHA-256"
        ),
        artifact_sha256=_optional_sha256(
            report.get("artifact_sha256"), label="artifact SHA-256"
        ),
    )
