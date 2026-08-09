"""Persistent, session-isolated Lean LSP validation workers for Stage P."""

from __future__ import annotations

import concurrent.futures
import json
import queue
import re
import statistics
import subprocess
import threading
import time
from dataclasses import asdict, dataclass, field, replace
from pathlib import Path
from typing import Any, Callable, Mapping, Protocol

from .lean_runner import (
    ORACLE_SOURCE_MARKERS,
    assert_generated_source_is_safe,
    run_command,
    validate_module_name,
)
from .models import CommandResult, sha256_id
from .stage_p_contract import SHA256_RE, STAGE_P_WORKER_SCHEMA, StagePContractError


STAGE_P_WORKER_KEY_SCHEMA = "hardness_stage_p_lean_worker_key_v1"
STAGE_P_WORKER_RESULT_SCHEMA = "hardness_stage_p_lean_worker_result_v1"
STAGE_P_MAX_WORKERS = 4
STAGE_P_WORKER_PROFILE = "stage_p_isolated_v1"
EXTRA_UNSAFE_SOURCE_RE = re.compile(
    r"\b(?:unsafe|run_tac|include_str|include_bytes|unsafeCast|implemented_by)\b"
)


def _require_hash(value: str, *, label: str) -> None:
    if not isinstance(value, str) or not SHA256_RE.fullmatch(value):
        raise StagePContractError("lean_worker_stale_result", f"{label} is not a content hash")


def _source_sha256(source: str) -> str:
    return sha256_id(source)


def _diagnostics_sha256(diagnostics: list[dict[str, Any]]) -> str:
    return sha256_id(diagnostics)


@dataclass(frozen=True)
class StagePLeanWorkerKey:
    toolchain: str
    lake_manifest_sha256: str
    base_registry_fingerprint: str
    complete_source_sha256: str
    dependency_sha256: tuple[str, ...]
    namespace: str
    session_id: str
    editable_allowlist: tuple[str, ...]
    validation_profile: str = STAGE_P_WORKER_PROFILE
    schema_version: str = STAGE_P_WORKER_KEY_SCHEMA

    def validate(self) -> None:
        if self.schema_version != STAGE_P_WORKER_KEY_SCHEMA:
            raise StagePContractError("lean_worker_stale_result", "worker key schema drifted")
        if not self.toolchain.strip():
            raise StagePContractError("lean_worker_stale_result", "worker key toolchain is empty")
        for label, value in {
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "base_registry_fingerprint": self.base_registry_fingerprint,
            "complete_source_sha256": self.complete_source_sha256,
            "session_id": self.session_id,
            **{
                f"dependency_sha256[{index}]": dependency
                for index, dependency in enumerate(self.dependency_sha256)
            },
        }.items():
            _require_hash(value, label=label)
        if not self.dependency_sha256 or len(set(self.dependency_sha256)) != len(
            self.dependency_sha256
        ):
            raise StagePContractError(
                "lean_worker_stale_result", "worker dependencies are empty or duplicated"
            )
        try:
            validate_module_name(self.namespace)
        except ValueError as error:
            raise StagePContractError("lean_worker_session_leak", str(error)) from error
        if not self.editable_allowlist or len(set(self.editable_allowlist)) != len(
            self.editable_allowlist
        ):
            raise StagePContractError(
                "lean_worker_stale_result", "worker editable allowlist is empty or duplicated"
            )
        if self.validation_profile != STAGE_P_WORKER_PROFILE:
            raise StagePContractError(
                "lean_worker_stale_result", "worker validation profile is not Stage P strict"
            )

    @property
    def cache_key(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})


@dataclass(frozen=True)
class StagePLeanWorkerResult:
    session_id: str
    owner: str
    worker_index: int
    worker_generation: int
    cache_key: str
    source_path: str
    source_sha256: str
    dependency_sha256: tuple[str, ...]
    cache_hit: bool
    fallback_used: bool
    verified: bool
    diagnostics: tuple[Mapping[str, Any], ...]
    diagnostics_sha256: str
    wall_duration_seconds: float
    command: CommandResult | None = None
    schema_version: str = STAGE_P_WORKER_RESULT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            **asdict(self),
            "dependency_sha256": list(self.dependency_sha256),
            "diagnostics": [dict(item) for item in self.diagnostics],
            "command": self.command.to_dict() if self.command is not None else None,
        }


@dataclass(frozen=True)
class _WorkerSession:
    session_id: str
    owner: str
    namespace: str
    worker_index: int
    worker_generation: int


class _PersistentWorker(Protocol):
    generation: int

    def start(self) -> None: ...

    def validate(self, *, source_path: Path, source: str, timeout_seconds: int) -> list[dict[str, Any]]: ...

    def is_alive(self) -> bool: ...

    def close(self) -> None: ...


class LeanLSPWorker:
    """One persistent `lean --server` process with serialized document checks."""

    def __init__(self, *, worker_index: int, lean_root: Path, generation: int = 1):
        self.worker_index = worker_index
        self.lean_root = lean_root.resolve()
        self.generation = generation
        self._process: subprocess.Popen[bytes] | None = None
        self._messages: queue.Queue[dict[str, Any]] = queue.Queue()
        self._write_lock = threading.Lock()
        self._validation_lock = threading.Lock()
        self._reader_thread: threading.Thread | None = None
        self._stderr_thread: threading.Thread | None = None
        self._stderr_lines: list[str] = []
        self._request_id = 0
        self._open_uri: str | None = None
        self._open_version = 0

    def is_alive(self) -> bool:
        return self._process is not None and self._process.poll() is None

    def _next_request_id(self) -> int:
        self._request_id += 1
        return self._request_id

    def _send(self, message: Mapping[str, Any]) -> None:
        process = self._process
        if process is None or process.stdin is None or process.poll() is not None:
            raise StagePContractError("lean_worker_crashed", "Lean worker is not alive")
        payload = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        frame = f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii") + payload
        try:
            with self._write_lock:
                process.stdin.write(frame)
                process.stdin.flush()
        except (BrokenPipeError, OSError) as error:
            raise StagePContractError("lean_worker_crashed", "Lean worker pipe closed") from error

    @staticmethod
    def _read_exact(stream: Any, length: int) -> bytes:
        chunks: list[bytes] = []
        remaining = length
        while remaining:
            chunk = stream.read(remaining)
            if not chunk:
                raise EOFError("Lean worker stdout closed")
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _reader(self) -> None:
        process = self._process
        assert process is not None and process.stdout is not None
        stream = process.stdout
        try:
            while True:
                headers: dict[str, str] = {}
                while True:
                    line = stream.readline()
                    if not line:
                        raise EOFError("Lean worker stdout closed")
                    if line in {b"\r\n", b"\n"}:
                        break
                    name, separator, value = line.decode("ascii").partition(":")
                    if not separator:
                        raise ValueError("invalid Lean LSP header")
                    headers[name.strip().lower()] = value.strip()
                length = int(headers["content-length"])
                message = json.loads(self._read_exact(stream, length).decode("utf-8"))
                if (
                    isinstance(message, dict)
                    and "id" in message
                    and "method" in message
                    and "result" not in message
                ):
                    self._send(
                        {
                            "jsonrpc": "2.0",
                            "id": message["id"],
                            "result": None,
                        }
                    )
                    continue
                if isinstance(message, dict):
                    self._messages.put(message)
        except Exception as error:
            self._messages.put(
                {
                    "__worker_eof__": True,
                    "error": f"{type(error).__name__}: {error}",
                }
            )

    def _stderr_reader(self) -> None:
        process = self._process
        assert process is not None and process.stderr is not None
        for raw in iter(process.stderr.readline, b""):
            text = raw.decode("utf-8", errors="replace").rstrip()
            if text:
                self._stderr_lines.append(text)
                del self._stderr_lines[:-100]

    def _wait_for_response(
        self,
        request_id: int,
        *,
        timeout_seconds: int,
        diagnostics_uri: str | None = None,
        diagnostics_version: int | None = None,
    ) -> list[dict[str, Any]]:
        deadline = time.monotonic() + timeout_seconds
        latest_diagnostics: list[dict[str, Any]] = []
        observed_messages: list[str] = []
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                stderr = "\n".join(self._stderr_lines[-20:])
                observed = ", ".join(observed_messages[-20:])
                raise StagePContractError(
                    "lean_worker_crashed",
                    (
                        "Lean worker response timed out"
                        + (f"; observed={observed}" if observed else "")
                        + (f"\nstderr:\n{stderr}" if stderr else "")
                    ),
                )
            try:
                message = self._messages.get(timeout=remaining)
            except queue.Empty as error:
                stderr = "\n".join(self._stderr_lines[-20:])
                observed = ", ".join(observed_messages[-20:])
                raise StagePContractError(
                    "lean_worker_crashed",
                    (
                        "Lean worker response timed out"
                        + (f"; observed={observed}" if observed else "")
                        + (f"\nstderr:\n{stderr}" if stderr else "")
                    ),
                ) from error
            if message.get("__worker_eof__"):
                stderr = "\n".join(self._stderr_lines[-20:])
                raise StagePContractError(
                    "lean_worker_crashed",
                    f"Lean worker exited: {message.get('error', '')}\n{stderr}".strip(),
                )
            if message.get("method") == "textDocument/publishDiagnostics":
                observed_messages.append("textDocument/publishDiagnostics")
                params = message.get("params")
                if isinstance(params, Mapping) and (
                    (diagnostics_uri is None or params.get("uri") == diagnostics_uri)
                    and (
                        diagnostics_version is None
                        or params.get("version") == diagnostics_version
                    )
                ):
                    raw = params.get("diagnostics", [])
                    if isinstance(raw, list):
                        latest_diagnostics = [
                            dict(item) for item in raw if isinstance(item, Mapping)
                        ]
                continue
            if isinstance(message.get("method"), str):
                observed_messages.append(str(message["method"]))
            elif "id" in message:
                observed_messages.append(f"response:{message.get('id')}")
            if message.get("id") != request_id:
                continue
            if "error" in message:
                raise StagePContractError(
                    "lean_worker_crashed", f"Lean worker JSON-RPC error: {message['error']}"
                )
            return latest_diagnostics

    def start(self) -> None:
        if self.is_alive():
            return
        self._process = subprocess.Popen(
            [
                "lake",
                "env",
                "lean",
                "--server",
                "-DstderrAsMessages=false",
                "-Dexperimental.module=true",
            ],
            cwd=self.lean_root,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        self._reader_thread = threading.Thread(
            target=self._reader,
            name=f"stage-p-lean-reader-{self.worker_index}",
            daemon=True,
        )
        self._stderr_thread = threading.Thread(
            target=self._stderr_reader,
            name=f"stage-p-lean-stderr-{self.worker_index}",
            daemon=True,
        )
        self._reader_thread.start()
        self._stderr_thread.start()
        request_id = self._next_request_id()
        self._send(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": "initialize",
                "params": {
                    "processId": None,
                    "rootUri": self.lean_root.as_uri(),
                    "capabilities": {
                        "workspace": {
                            "didChangeWatchedFiles": {"dynamicRegistration": False}
                        },
                        "lean": {"silentDiagnosticSupport": True},
                    },
                    "initializationOptions": {"hasWidgets": False},
                },
            }
        )
        self._wait_for_response(request_id, timeout_seconds=60)
        self._send(
            {
                "jsonrpc": "2.0",
                "method": "initialized",
                "params": {},
            }
        )

    def validate(
        self,
        *,
        source_path: Path,
        source: str,
        timeout_seconds: int,
    ) -> list[dict[str, Any]]:
        with self._validation_lock:
            self.start()
            uri = source_path.resolve().as_uri()
            if self._open_uri != uri:
                if self._open_uri is not None:
                    self._send(
                        {
                            "jsonrpc": "2.0",
                            "method": "textDocument/didClose",
                            "params": {"textDocument": {"uri": self._open_uri}},
                        }
                    )
                version = 1
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "method": "textDocument/didOpen",
                        "params": {
                            "textDocument": {
                                "uri": uri,
                                "languageId": "lean",
                                "version": version,
                                "text": source,
                            },
                            "dependencyBuildMode": "never",
                        },
                    }
                )
                self._open_uri = uri
                self._open_version = version
            else:
                version = self._open_version + 1
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "method": "textDocument/didChange",
                        "params": {
                            "textDocument": {"uri": uri, "version": version},
                            "contentChanges": [{"text": source}],
                        },
                    }
                )
                self._open_version = version
            request_id = self._next_request_id()
            self._send(
                {
                    "jsonrpc": "2.0",
                    "id": request_id,
                    "method": "textDocument/waitForDiagnostics",
                    "params": {"uri": uri, "version": version},
                }
            )
            return self._wait_for_response(
                request_id,
                timeout_seconds=timeout_seconds,
                diagnostics_uri=uri,
                diagnostics_version=version,
            )

    def close(self) -> None:
        process = self._process
        if process is None:
            return
        if process.poll() is None:
            try:
                if self._open_uri is not None:
                    self._send(
                        {
                            "jsonrpc": "2.0",
                            "method": "textDocument/didClose",
                            "params": {"textDocument": {"uri": self._open_uri}},
                        }
                    )
                self._open_uri = None
                self._open_version = 0
                request_id = self._next_request_id()
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "id": request_id,
                        "method": "shutdown",
                        "params": None,
                    }
                )
                self._wait_for_response(request_id, timeout_seconds=10)
                self._send(
                    {
                        "jsonrpc": "2.0",
                        "method": "exit",
                        "params": None,
                    }
                )
                process.wait(timeout=10)
            except Exception:
                process.kill()
                process.wait(timeout=10)
        self._open_uri = None
        self._open_version = 0
        self._process = None


class StagePLeanWorkerPool:
    """At most four persistent workers with exact-key successful-result caching."""

    def __init__(
        self,
        *,
        lean_root: Path,
        workspace_root: Path,
        service_root: Path,
        maximum_workers: int = STAGE_P_MAX_WORKERS,
        timeout_seconds: int = 300,
        worker_factory: Callable[[int, int], _PersistentWorker] | None = None,
    ):
        if isinstance(maximum_workers, bool) or not 1 <= maximum_workers <= STAGE_P_MAX_WORKERS:
            raise ValueError("Stage P worker count must be between one and four")
        self.lean_root = lean_root.resolve()
        self.workspace_root = workspace_root.resolve()
        self.service_root = service_root.resolve()
        self.maximum_workers = maximum_workers
        self.timeout_seconds = timeout_seconds
        self.service_root.mkdir(parents=True, exist_ok=False)
        self._worker_factory = worker_factory or (
            lambda index, generation: LeanLSPWorker(
                worker_index=index,
                lean_root=self.lean_root,
                generation=generation,
            )
        )
        self._workers: list[_PersistentWorker | None] = [None] * maximum_workers
        self._worker_generations: list[int] = [1] * maximum_workers
        self._sessions: dict[str, _WorkerSession] = {}
        self._cache: dict[str, StagePLeanWorkerResult] = {}
        self._cache_worker: dict[str, int] = {}
        self._state_lock = threading.RLock()
        self._next_worker = 0
        self.worker_start_count = 0
        self.worker_restart_count = 0
        self.worker_crash_count = 0
        self.cache_hit_count = 0
        self.cache_miss_count = 0
        self.invalidation_count = 0
        self.cold_fallback_count = 0

    def _worker(self, index: int) -> _PersistentWorker:
        with self._state_lock:
            worker = self._workers[index]
            if worker is None:
                worker = self._worker_factory(index, self._worker_generations[index])
                worker.start()
                self._workers[index] = worker
                self.worker_start_count += 1
            return worker

    def start_session(self, *, owner: str, namespace: str) -> str:
        if not owner.strip():
            raise StagePContractError("lean_worker_session_leak", "session owner is empty")
        try:
            validate_module_name(namespace)
        except ValueError as error:
            raise StagePContractError("lean_worker_session_leak", str(error)) from error
        with self._state_lock:
            worker_index = self._next_worker
            self._next_worker = (self._next_worker + 1) % self.maximum_workers
            generation = self._worker_generations[worker_index]
            session_id = sha256_id(
                {
                    "schema_version": STAGE_P_WORKER_SCHEMA,
                    "owner": owner,
                    "namespace": namespace,
                    "worker_index": worker_index,
                    "worker_generation": generation,
                    "ordinal": len(self._sessions),
                }
            )
            self._sessions[session_id] = _WorkerSession(
                session_id=session_id,
                owner=owner,
                namespace=namespace,
                worker_index=worker_index,
                worker_generation=generation,
            )
        self._worker(worker_index)
        return session_id

    def _session(self, *, session_id: str, owner: str) -> _WorkerSession:
        with self._state_lock:
            session = self._sessions.get(session_id)
        if session is None or session.owner != owner:
            raise StagePContractError(
                "lean_worker_session_leak", "worker session is absent or belongs to another case"
            )
        return session

    def close_session(self, *, session_id: str, owner: str) -> None:
        self._session(session_id=session_id, owner=owner)
        with self._state_lock:
            del self._sessions[session_id]

    def _source_text(self, source_path: Path) -> tuple[Path, str]:
        resolved = source_path.resolve()
        try:
            resolved.relative_to(self.workspace_root)
        except ValueError as error:
            raise StagePContractError(
                "lean_worker_session_leak", "candidate source escaped the workspace root"
            ) from error
        if not resolved.is_file():
            raise StagePContractError(
                "lean_worker_stale_result", "candidate source was deleted before validation"
            )
        source = resolved.read_text(encoding="utf-8")
        if EXTRA_UNSAFE_SOURCE_RE.search(source):
            raise StagePContractError(
                "sorry_axiom_or_unsafe_candidate", "worker source contains an unsafe token"
            )
        if any(marker in source for marker in ORACLE_SOURCE_MARKERS):
            raise StagePContractError(
                "oracle_or_gold_import", "worker source imports quarantined data"
            )
        try:
            assert_generated_source_is_safe(source)
        except ValueError as error:
            message = str(error)
            code = (
                "oracle_or_gold_import"
                if "quarantined" in message
                else "sorry_axiom_or_unsafe_candidate"
            )
            raise StagePContractError(code, message) from error
        return resolved, source

    @staticmethod
    def _assert_namespace(source: str, namespace: str) -> None:
        escaped = re.escape(namespace)
        if not re.search(rf"(?m)^\s*namespace\s+{escaped}\s*$", source) or not re.search(
            rf"(?m)^\s*end\s+{escaped}\s*$", source
        ):
            raise StagePContractError(
                "lean_worker_session_leak", "candidate source does not own the session namespace"
            )

    @staticmethod
    def _verified(diagnostics: list[dict[str, Any]]) -> bool:
        return not any(item.get("severity") == 1 for item in diagnostics)

    def _restart_worker(self, index: int) -> None:
        with self._state_lock:
            worker = self._workers[index]
            if worker is not None:
                worker.close()
            self._workers[index] = None
            self._worker_generations[index] += 1
            generation = self._worker_generations[index]
            stale_keys = [key for key, worker_index in self._cache_worker.items() if worker_index == index]
            for key in stale_keys:
                self._cache.pop(key, None)
                self._cache_worker.pop(key, None)
                self.invalidation_count += 1
            for session_id, session in list(self._sessions.items()):
                if session.worker_index == index:
                    self._sessions[session_id] = replace(
                        session, worker_generation=generation
                    )
            self.worker_restart_count += 1

    def validate(
        self,
        *,
        session_id: str,
        owner: str,
        key: StagePLeanWorkerKey,
        source_path: Path,
        dependency_sha256: tuple[str, ...],
        use_cache: bool = True,
        allow_cold_fallback: bool = True,
    ) -> StagePLeanWorkerResult:
        started = time.monotonic()
        session = self._session(session_id=session_id, owner=owner)
        key.validate()
        if key.session_id != session_id or key.namespace != session.namespace:
            raise StagePContractError(
                "lean_worker_session_leak", "worker key differs from session ownership"
            )
        resolved, source = self._source_text(source_path)
        self._assert_namespace(source, session.namespace)
        source_hash = _source_sha256(source)
        if source_hash != key.complete_source_sha256:
            raise StagePContractError(
                "lean_worker_stale_result", "candidate source differs from worker key"
            )
        if tuple(dependency_sha256) != key.dependency_sha256:
            raise StagePContractError(
                "lean_worker_stale_result", "dependency state differs from worker key"
            )
        cache_key = key.cache_key
        with self._state_lock:
            cached = self._cache.get(cache_key)
        if use_cache and cached is not None:
            current_session = self._session(session_id=session_id, owner=owner)
            if (
                cached.worker_index != current_session.worker_index
                or cached.worker_generation != current_session.worker_generation
                or cached.source_sha256 != source_hash
                or cached.source_path != str(resolved)
                or cached.dependency_sha256 != dependency_sha256
            ):
                raise StagePContractError(
                    "lean_worker_stale_result", "cached worker result is stale"
                )
            self.cache_hit_count += 1
            return replace(
                cached,
                cache_hit=True,
                wall_duration_seconds=round(time.monotonic() - started, 6),
            )

        self.cache_miss_count += 1
        worker = self._worker(session.worker_index)
        try:
            diagnostics = worker.validate(
                source_path=resolved,
                source=source,
                timeout_seconds=self.timeout_seconds,
            )
            current_session = self._session(session_id=session_id, owner=owner)
            result = StagePLeanWorkerResult(
                session_id=session_id,
                owner=owner,
                worker_index=current_session.worker_index,
                worker_generation=current_session.worker_generation,
                cache_key=cache_key,
                source_path=str(resolved),
                source_sha256=source_hash,
                dependency_sha256=tuple(dependency_sha256),
                cache_hit=False,
                fallback_used=False,
                verified=self._verified(diagnostics),
                diagnostics=tuple(diagnostics),
                diagnostics_sha256=_diagnostics_sha256(diagnostics),
                wall_duration_seconds=round(time.monotonic() - started, 6),
            )
        except Exception as error:
            self.worker_crash_count += 1
            self._restart_worker(session.worker_index)
            if not allow_cold_fallback:
                if isinstance(error, StagePContractError):
                    raise
                raise StagePContractError("lean_worker_crashed", str(error)) from error
            command = run_command(
                ["lake", "env", "lean", str(resolved)],
                cwd=self.lean_root,
                timeout_seconds=self.timeout_seconds,
            )
            self.cold_fallback_count += 1
            diagnostics_text = command.stdout + "\n" + command.stderr
            diagnostics = (
                []
                if command.exit_code == 0 and not command.timed_out
                else [{"severity": 1, "message": diagnostics_text[-8_000:]}]
            )
            current_session = self._session(session_id=session_id, owner=owner)
            result = StagePLeanWorkerResult(
                session_id=session_id,
                owner=owner,
                worker_index=current_session.worker_index,
                worker_generation=current_session.worker_generation,
                cache_key=cache_key,
                source_path=str(resolved),
                source_sha256=source_hash,
                dependency_sha256=tuple(dependency_sha256),
                cache_hit=False,
                fallback_used=True,
                verified=command.exit_code == 0 and not command.timed_out,
                diagnostics=tuple(diagnostics),
                diagnostics_sha256=_diagnostics_sha256(diagnostics),
                wall_duration_seconds=round(time.monotonic() - started, 6),
                command=command,
            )
        if result.verified and use_cache and not result.fallback_used:
            with self._state_lock:
                self._cache[cache_key] = result
                self._cache_worker[cache_key] = result.worker_index
        return result

    def invalidate(self, cache_key: str) -> bool:
        with self._state_lock:
            removed = self._cache.pop(cache_key, None) is not None
            self._cache_worker.pop(cache_key, None)
            if removed:
                self.invalidation_count += 1
            return removed

    def restart_all(self) -> None:
        for index in range(self.maximum_workers):
            if self._workers[index] is not None:
                self._restart_worker(index)

    def microbenchmark(
        self,
        *,
        session_id: str,
        owner: str,
        key: StagePLeanWorkerKey,
        source_path: Path,
        dependency_sha256: tuple[str, ...],
        repeat_count: int = 20,
        cold_parallelism: int | None = None,
    ) -> dict[str, Any]:
        if repeat_count != 20:
            raise StagePContractError("lean_worker_stale_result", "microbenchmark requires 20 repeats")
        if cold_parallelism is None:
            cold_parallelism = self.maximum_workers
        if (
            isinstance(cold_parallelism, bool)
            or not 1 <= cold_parallelism <= self.maximum_workers
        ):
            raise StagePContractError(
                "lean_worker_stale_result",
                "cold benchmark parallelism must be within the configured worker bound",
            )
        resolved, _ = self._source_text(source_path)

        def cold(_: int) -> CommandResult:
            return run_command(
                ["lake", "env", "lean", str(resolved)],
                cwd=self.lean_root,
                timeout_seconds=self.timeout_seconds,
            )

        cold_started = time.monotonic()
        with concurrent.futures.ThreadPoolExecutor(max_workers=cold_parallelism) as executor:
            cold_results = list(executor.map(cold, range(repeat_count)))
        cold_wall = time.monotonic() - cold_started
        if any(result.exit_code != 0 or result.timed_out for result in cold_results):
            raise StagePContractError("final_lean_failed", "forced-cold worker benchmark failed")
        cold_seconds = [result.duration_seconds for result in cold_results]

        self.invalidate(key.cache_key)
        priming = self.validate(
            session_id=session_id,
            owner=owner,
            key=key,
            source_path=resolved,
            dependency_sha256=dependency_sha256,
            use_cache=False,
            allow_cold_fallback=False,
        )
        if not priming.verified:
            raise StagePContractError("final_lean_failed", "persistent worker priming failed")
        persistent_started = time.monotonic()
        warm_results = [
            self.validate(
                session_id=session_id,
                owner=owner,
                key=key,
                source_path=resolved,
                dependency_sha256=dependency_sha256,
                use_cache=False,
                allow_cold_fallback=False,
            )
            for _ in range(repeat_count)
        ]
        persistent_wall = time.monotonic() - persistent_started
        if any(not result.verified or result.fallback_used for result in warm_results):
            raise StagePContractError(
                "lean_worker_stale_result", "persistent warm validation failed"
            )
        warm_seconds = [result.wall_duration_seconds for result in warm_results]
        cold_p50 = statistics.median(cold_seconds)
        warm_p50 = statistics.median(warm_seconds)
        warm_ratio = warm_p50 / cold_p50 if cold_p50 else 0.0
        wall_reduction = 1.0 - (persistent_wall / cold_wall) if cold_wall else 0.0
        return {
            "repeat_count": repeat_count,
            "maximum_workers": self.maximum_workers,
            "cold_parallelism": cold_parallelism,
            "forced_cold_seconds": cold_seconds,
            "persistent_warm_seconds": warm_seconds,
            "forced_cold_wall_seconds": round(cold_wall, 6),
            "persistent_priming_seconds": priming.wall_duration_seconds,
            "persistent_wall_seconds": round(persistent_wall, 6),
            "cold_p50_seconds": round(cold_p50, 6),
            "warm_p50_seconds": round(warm_p50, 6),
            "warm_p50_over_cold_p50": round(warm_ratio, 6),
            "wall_time_reduction": round(wall_reduction, 6),
            "gates": {
                "warm_p50_over_cold_p50": warm_ratio <= 0.5,
                "wall_time_reduction": wall_reduction >= 0.5,
                "worker_count_within_limit": self.worker_start_count <= self.maximum_workers,
            },
            "pool": self.to_dict(),
        }

    def close(self) -> None:
        for worker in self._workers:
            if worker is not None:
                worker.close()
        self._workers = [None] * self.maximum_workers

    def to_dict(self) -> dict[str, Any]:
        return {
            "service_root": str(self.service_root),
            "maximum_workers": self.maximum_workers,
            "worker_start_count": self.worker_start_count,
            "worker_restart_count": self.worker_restart_count,
            "worker_crash_count": self.worker_crash_count,
            "active_session_count": len(self._sessions),
            "cache_entry_count": len(self._cache),
            "cache_hit_count": self.cache_hit_count,
            "cache_miss_count": self.cache_miss_count,
            "invalidation_count": self.invalidation_count,
            "cold_fallback_count": self.cold_fallback_count,
            "workers_alive": [
                worker is not None and worker.is_alive() for worker in self._workers
            ],
        }
