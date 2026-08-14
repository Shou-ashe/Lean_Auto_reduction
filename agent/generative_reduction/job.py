"""Idempotent job-local state and checkpoint storage."""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import secrets
from typing import Any, Mapping

from .models import stable_json


STATES = (
    "RECEIVED",
    "INPUT_VALIDATED",
    "ENVIRONMENT_FROZEN",
    "FAST_PATH_CHECKED",
    "INDEX_READY",
    "SEARCHING",
    "SYNTHESIZING",
    "CANDIDATE_VERIFIED",
    "PROOF_RECONSTRUCTED",
    "AXIOM_AUDITED",
    "PROOF_VERIFIED",
    "GENERATION_CLASSIFIED",
    "PROFILE_EVALUATED",
    "COMPLETED",
    "BLOCKED",
    "FAILED_MODEL",
    "FAILED_LEAN",
    "INPUT_ERROR",
    "BUDGET_EXHAUSTED",
    "CANCELLED",
)


@dataclass
class GeneralJobStore:
    directory: Path

    @property
    def events_path(self) -> Path:
        return self.directory / "events.jsonl"

    def initialize(self) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)

    @contextmanager
    def exclusive_run(self):
        self.initialize()
        lock_path = self.directory / ".run.lock"
        with lock_path.open("a+", encoding="utf-8") as lock:
            try:
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise ValueError("another process owns this general reduction job") from error
            lock.seek(0)
            lock.truncate()
            lock.write(
                stable_json(
                    {
                        "pid": os.getpid(),
                        "token": secrets.token_hex(16),
                        "time": datetime.now(timezone.utc).isoformat(),
                    }
                )
            )
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
        path.relative_to(self.directory.resolve())
        return path

    def write_text(self, relative_path: str, value: str) -> Path:
        path = self.path(relative_path)
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_text(value, encoding="utf-8")
        temporary.replace(path)
        return path

    def write_json(self, relative_path: str, value: Mapping[str, Any]) -> Path:
        return self.write_text(
            relative_path,
            json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        )

    def transition(self, status: str, *, details: Mapping[str, Any] | None = None) -> None:
        if status not in STATES:
            raise ValueError(f"unknown general reduction job status: {status}")
        event = {
            "schema_version": "general_np_hard_event_v1",
            "time": datetime.now(timezone.utc).isoformat(),
            "status": status,
            "details": dict(details or {}),
        }
        state_path = self.path("state.json")
        if state_path.is_file():
            current = json.loads(state_path.read_text(encoding="utf-8"))
            if current.get("status") == status and current.get("details") == event["details"]:
                return
        with self.events_path.open("a", encoding="utf-8") as events:
            events.write(stable_json(event) + "\n")
        self.write_json("state.json", event)


__all__ = ["GeneralJobStore", "STATES"]
