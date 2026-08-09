"""Run-scoped, session-isolated Lean validation cache for Stage O."""

from __future__ import annotations

import concurrent.futures
import hashlib
import statistics
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping

from .lean_runner import BANNED_SOURCE_RE, ORACLE_SOURCE_MARKERS, run_command
from .models import CommandResult, sha256_id
from .stage_o_contract import LeanValidationCacheKey, StageOContractError


LEAN_VALIDATION_RESULT_SCHEMA = "hardness_stage_o_lean_validation_result_v1"
STAGE_O_COLD_PROCESS_JOBS = 4


def sha256_text(value: str) -> str:
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class LeanValidationResult:
    session_id: str
    owner: str
    cache_key: str
    source_sha256: str
    dependency_sha256: tuple[str, ...]
    cache_hit: bool
    verified: bool
    command: CommandResult | None
    wall_duration_seconds: float
    diagnostics_sha256: str
    schema_version: str = LEAN_VALIDATION_RESULT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            **asdict(self),
            "command": self.command.to_dict() if self.command is not None else None,
        }


@dataclass(frozen=True)
class _Session:
    session_id: str
    owner: str
    namespace: str


class LeanValidationService:
    """Caches only successful, content-addressed local Lean validations."""

    def __init__(self, *, lean_root: Path, service_root: Path, timeout_seconds: int = 300):
        self.lean_root = lean_root.resolve()
        self.service_root = service_root.resolve()
        self.timeout_seconds = timeout_seconds
        self.service_root.mkdir(parents=True, exist_ok=False)
        self._sessions: dict[str, _Session] = {}
        self._cache: dict[str, LeanValidationResult] = {}
        self._state_lock = threading.Lock()
        self.hit_count = 0
        self.miss_count = 0
        self.invalidation_count = 0
        self.restart_count = 0

    def start_session(self, *, owner: str, namespace: str) -> str:
        if not owner or not namespace:
            raise StageOContractError("lean_service_session_leak", "session owner/namespace is empty")
        session_id = sha256_id(
            {
                "schema_version": "hardness_stage_o_lean_session_v1",
                "owner": owner,
                "namespace": namespace,
                "ordinal": len(self._sessions),
            }
        )
        self._sessions[session_id] = _Session(session_id, owner, namespace)
        return session_id

    def close_session(self, *, session_id: str, owner: str) -> None:
        self._session(session_id=session_id, owner=owner)
        del self._sessions[session_id]

    def _session(self, *, session_id: str, owner: str) -> _Session:
        session = self._sessions.get(session_id)
        if session is None or session.owner != owner:
            raise StageOContractError(
                "lean_service_session_leak", "validation session is absent or belongs to another case"
            )
        return session

    def validate(
        self,
        *,
        session_id: str,
        owner: str,
        key: LeanValidationCacheKey,
        source: str,
        dependency_sha256: tuple[str, ...],
        use_cache: bool = True,
    ) -> LeanValidationResult:
        started = time.monotonic()
        session = self._session(session_id=session_id, owner=owner)
        key.validate()
        if key.namespace != session.namespace:
            raise StageOContractError(
                "lean_service_session_leak", "cache-key namespace differs from session ownership"
            )
        source_hash = sha256_text(source)
        if source_hash != key.complete_source_sha256:
            raise StageOContractError("lean_cache_stale_hit", "source differs from cache-key content hash")
        if tuple(dependency_sha256) != key.dependency_sha256:
            raise StageOContractError(
                "lean_cache_stale_hit", "dependency state differs from cache-key dependency hash"
            )
        if BANNED_SOURCE_RE.search(source) or any(marker in source for marker in ORACLE_SOURCE_MARKERS):
            raise StageOContractError(
                "oracle_or_nonstandard_axiom", "local validation source is outside the editable policy"
            )
        cache_key = key.cache_key
        cached = self._cache.get(cache_key)
        if use_cache and cached is not None:
            if cached.source_sha256 != source_hash or cached.dependency_sha256 != dependency_sha256:
                raise StageOContractError("lean_cache_stale_hit", "cached validation is stale")
            self.hit_count += 1
            return LeanValidationResult(
                session_id=cached.session_id,
                owner=cached.owner,
                cache_key=cached.cache_key,
                source_sha256=cached.source_sha256,
                dependency_sha256=cached.dependency_sha256,
                cache_hit=True,
                verified=cached.verified,
                command=cached.command,
                wall_duration_seconds=round(time.monotonic() - started, 6),
                diagnostics_sha256=cached.diagnostics_sha256,
            )

        with self._state_lock:
            self.miss_count += 1
            miss_ordinal = self.miss_count
        session_root = self.service_root / session_id.removeprefix("sha256:")
        session_root.mkdir(parents=True, exist_ok=True)
        source_path = session_root / f"Validation_{miss_ordinal}.lean"
        source_path.write_text(source, encoding="utf-8")
        command = run_command(
            ["lake", "env", "lean", str(source_path)],
            cwd=self.lean_root,
            timeout_seconds=self.timeout_seconds,
        )
        diagnostics = command.stdout + "\n" + command.stderr
        result = LeanValidationResult(
            session_id=session_id,
            owner=owner,
            cache_key=cache_key,
            source_sha256=source_hash,
            dependency_sha256=tuple(dependency_sha256),
            cache_hit=False,
            verified=command.exit_code == 0 and not command.timed_out,
            command=command,
            wall_duration_seconds=round(time.monotonic() - started, 6),
            diagnostics_sha256=sha256_text(diagnostics),
        )
        if result.verified and use_cache:
            self._cache[cache_key] = result
        return result

    def invalidate(self, *, cache_key: str) -> bool:
        removed = self._cache.pop(cache_key, None) is not None
        if removed:
            self.invalidation_count += 1
        return removed

    def restart(self) -> None:
        self._sessions.clear()
        self._cache.clear()
        self.restart_count += 1

    def microbenchmark(
        self,
        *,
        owner: str,
        namespace: str,
        key: LeanValidationCacheKey,
        source: str,
        dependency_sha256: tuple[str, ...],
        repeat_count: int = 20,
    ) -> dict[str, Any]:
        if repeat_count != 20:
            raise StageOContractError("invalid_schema", "Stage O microbenchmark requires 20 repeats")
        session_id = self.start_session(owner=owner, namespace=namespace)
        cold: list[float] = []
        warm: list[float] = []
        def cold_validation(_: int) -> LeanValidationResult:
            return self.validate(
                session_id=session_id,
                owner=owner,
                key=key,
                source=source,
                dependency_sha256=dependency_sha256,
                use_cache=False,
            )

        with concurrent.futures.ThreadPoolExecutor(
            max_workers=min(STAGE_O_COLD_PROCESS_JOBS, repeat_count)
        ) as executor:
            cold_results = list(executor.map(cold_validation, range(repeat_count)))
        for result in cold_results:
            if not result.verified:
                raise StageOContractError("final_lean_failed", "cold Lean microbenchmark failed")
            cold.append(result.wall_duration_seconds)
        priming = self.validate(
            session_id=session_id,
            owner=owner,
            key=key,
            source=source,
            dependency_sha256=dependency_sha256,
            use_cache=True,
        )
        if not priming.verified:
            raise StageOContractError("final_lean_failed", "warm-cache priming failed")
        for _ in range(repeat_count):
            result = self.validate(
                session_id=session_id,
                owner=owner,
                key=key,
                source=source,
                dependency_sha256=dependency_sha256,
                use_cache=True,
            )
            if not result.cache_hit:
                raise StageOContractError("lean_cache_stale_hit", "warm validation missed its cache")
            warm.append(result.wall_duration_seconds)
        cold_p50 = statistics.median(cold)
        warm_p50 = statistics.median(warm)
        ratio = warm_p50 / cold_p50 if cold_p50 else 0.0
        self.close_session(session_id=session_id, owner=owner)
        return {
            "repeat_count": repeat_count,
            "cold_process_jobs": min(STAGE_O_COLD_PROCESS_JOBS, repeat_count),
            "cold_seconds": cold,
            "warm_seconds": warm,
            "cold_p50_seconds": round(cold_p50, 6),
            "warm_p50_seconds": round(warm_p50, 6),
            "warm_p50_over_cold_p50": round(ratio, 6),
            "gate": ratio <= 0.5,
            "service": self.to_dict(),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "service_root": str(self.service_root),
            "active_session_count": len(self._sessions),
            "cache_entry_count": len(self._cache),
            "hit_count": self.hit_count,
            "miss_count": self.miss_count,
            "invalidation_count": self.invalidation_count,
            "restart_count": self.restart_count,
        }
