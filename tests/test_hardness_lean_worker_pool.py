import threading
import time
from dataclasses import replace
from pathlib import Path

import pytest

import agent.hardness.lean_worker_pool as worker_module
from agent.hardness.authoring_contract import HardnessContractError
from agent.hardness.lean_worker_pool import (
    LeanLSPWorker,
    LeanWorkerKey,
    LeanWorkerPool,
)
from agent.hardness.models import CommandResult, sha256_id


NAMESPACE = "HardnessValidation.SessionA"
SOURCE = (
    f"namespace {NAMESPACE}\n"
    "#check True\n"
    f"end {NAMESPACE}\n"
)


def digest(value: int) -> str:
    return f"sha256:{value:064x}"


class FakeWorker:
    def __init__(
        self,
        *,
        worker_index: int,
        generation: int,
        diagnostics: list[dict[str, object]] | None = None,
        crash: bool = False,
        delay: float = 0.0,
    ):
        self.worker_index = worker_index
        self.generation = generation
        self.diagnostics = diagnostics or []
        self.crash = crash
        self.delay = delay
        self.started = False
        self.validate_count = 0

    def start(self) -> None:
        self.started = True

    def validate(
        self, *, source_path: Path, source: str, timeout_seconds: int
    ) -> list[dict[str, object]]:
        del source_path, source, timeout_seconds
        self.validate_count += 1
        if self.delay:
            time.sleep(self.delay)
        if self.crash:
            raise RuntimeError("simulated worker crash")
        return list(self.diagnostics)

    def is_alive(self) -> bool:
        return self.started

    def close(self) -> None:
        self.started = False


def source_file(tmp_path: Path, source: str = SOURCE) -> Path:
    path = tmp_path / "workspace" / "Generated" / "Validation.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    return path


def pool(
    tmp_path: Path,
    *,
    maximum_workers: int = 1,
    diagnostics: list[dict[str, object]] | None = None,
    crash: bool = False,
    delay: float = 0.0,
) -> tuple[LeanWorkerPool, list[FakeWorker]]:
    workers: list[FakeWorker] = []

    def factory(index: int, generation: int) -> FakeWorker:
        worker = FakeWorker(
            worker_index=index,
            generation=generation,
            diagnostics=diagnostics,
            crash=crash,
            delay=delay,
        )
        workers.append(worker)
        return worker

    lean_root = tmp_path / "workspace" / "Lean"
    lean_root.mkdir(parents=True)
    instance = LeanWorkerPool(
        lean_root=lean_root,
        workspace_root=tmp_path / "workspace",
        service_root=tmp_path / "worker-service",
        maximum_workers=maximum_workers,
        timeout_seconds=30,
        worker_factory=factory,
    )
    return instance, workers


def key(
    *,
    session_id: str,
    source: str = SOURCE,
    namespace: str = NAMESPACE,
    toolchain: str = "leanprover/lean4:test",
    registry: str = digest(2),
    dependencies: tuple[str, ...] = (digest(3),),
) -> LeanWorkerKey:
    return LeanWorkerKey(
        toolchain=toolchain,
        lake_manifest_sha256=digest(1),
        base_registry_fingerprint=registry,
        complete_source_sha256=sha256_id(source),
        dependency_sha256=dependencies,
        namespace=namespace,
        session_id=session_id,
        editable_allowlist=("candidate_body",),
    )


def test_worker_pool_reuses_only_an_exact_live_source_key(tmp_path: Path) -> None:
    instance, workers = pool(tmp_path)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    first = instance.validate(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
    )
    second = instance.validate(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
    )
    assert first.verified and not first.cache_hit
    assert second.verified and second.cache_hit
    assert workers[0].validate_count == 1
    path.unlink()
    with pytest.raises(HardnessContractError) as captured:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=cache_key,
            source_path=path,
            dependency_sha256=cache_key.dependency_sha256,
        )
    assert captured.value.code == "lean_worker_stale_result"
    instance.close()


def test_lsp_worker_keeps_documents_open_and_uses_monotonic_versions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lean_root = tmp_path / "Lean"
    lean_root.mkdir()
    path = source_file(tmp_path)
    worker = LeanLSPWorker(worker_index=0, lean_root=lean_root)
    sent: list[dict[str, object]] = []

    monkeypatch.setattr(worker, "start", lambda: None)
    monkeypatch.setattr(worker, "_send", lambda message: sent.append(dict(message)))
    monkeypatch.setattr(worker, "_wait_for_response", lambda *args, **kwargs: [])

    worker.validate(source_path=path, source=SOURCE, timeout_seconds=30)
    worker.validate(source_path=path, source=SOURCE, timeout_seconds=30)

    methods = [message.get("method") for message in sent]
    assert methods == [
        "textDocument/didOpen",
        "textDocument/waitForDiagnostics",
        "textDocument/didChange",
        "textDocument/waitForDiagnostics",
    ]
    assert sent[0]["params"]["textDocument"]["version"] == 1
    assert sent[1]["params"]["version"] == 1
    assert sent[2]["params"]["textDocument"]["version"] == 2
    assert sent[3]["params"]["version"] == 2


def test_lsp_worker_closes_the_previous_document_before_switching_cases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lean_root = tmp_path / "Lean"
    lean_root.mkdir()
    first_path = source_file(tmp_path)
    second_path = first_path.with_name("Second.lean")
    second_path.write_text(SOURCE, encoding="utf-8")
    worker = LeanLSPWorker(worker_index=0, lean_root=lean_root)
    sent: list[dict[str, object]] = []

    monkeypatch.setattr(worker, "start", lambda: None)
    monkeypatch.setattr(worker, "_send", lambda message: sent.append(dict(message)))
    monkeypatch.setattr(worker, "_wait_for_response", lambda *args, **kwargs: [])

    worker.validate(source_path=first_path, source=SOURCE, timeout_seconds=30)
    worker.validate(source_path=second_path, source=SOURCE, timeout_seconds=30)

    methods = [message.get("method") for message in sent]
    assert methods == [
        "textDocument/didOpen",
        "textDocument/waitForDiagnostics",
        "textDocument/didClose",
        "textDocument/didOpen",
        "textDocument/waitForDiagnostics",
    ]
    assert sent[2]["params"]["textDocument"]["uri"] == first_path.resolve().as_uri()
    assert sent[3]["params"]["textDocument"]["version"] == 1


def test_lsp_worker_ignores_diagnostics_from_a_stale_document_version(
    tmp_path: Path,
) -> None:
    worker = LeanLSPWorker(worker_index=0, lean_root=tmp_path)
    uri = (tmp_path / "Candidate.lean").as_uri()
    worker._messages.put(
        {
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": {
                "uri": uri,
                "version": 1,
                "diagnostics": [{"severity": 1, "message": "stale"}],
            },
        }
    )
    worker._messages.put(
        {
            "jsonrpc": "2.0",
            "method": "textDocument/publishDiagnostics",
            "params": {
                "uri": uri,
                "version": 2,
                "diagnostics": [{"severity": 2, "message": "current"}],
            },
        }
    )
    worker._messages.put({"jsonrpc": "2.0", "id": 7, "result": {}})

    diagnostics = worker._wait_for_response(
        7,
        timeout_seconds=1,
        diagnostics_uri=uri,
        diagnostics_version=2,
    )
    assert diagnostics == [{"severity": 2, "message": "current"}]


def test_session_owner_and_namespace_are_isolated(tmp_path: Path) -> None:
    instance, _ = pool(tmp_path)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    with pytest.raises(HardnessContractError) as owner_error:
        instance.validate(
            session_id=session_id,
            owner="case-b",
            key=cache_key,
            source_path=path,
            dependency_sha256=cache_key.dependency_sha256,
        )
    assert owner_error.value.code == "lean_worker_session_leak"
    with pytest.raises(HardnessContractError) as namespace_error:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=replace(cache_key, namespace="HardnessValidation.SessionB"),
            source_path=path,
            dependency_sha256=cache_key.dependency_sha256,
        )
    assert namespace_error.value.code == "lean_worker_session_leak"
    instance.close()


def test_source_dependency_registry_and_toolchain_changes_miss_or_reject_cache(
    tmp_path: Path,
) -> None:
    instance, workers = pool(tmp_path)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    base = key(session_id=session_id)
    instance.validate(
        session_id=session_id,
        owner="case-a",
        key=base,
        source_path=path,
        dependency_sha256=base.dependency_sha256,
    )
    changed_source = SOURCE.replace("#check True", "#check False")
    path.write_text(changed_source, encoding="utf-8")
    with pytest.raises(HardnessContractError) as source_error:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=base,
            source_path=path,
            dependency_sha256=base.dependency_sha256,
        )
    assert source_error.value.code == "lean_worker_stale_result"
    path.write_text(SOURCE, encoding="utf-8")
    with pytest.raises(HardnessContractError) as dependency_error:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=base,
            source_path=path,
            dependency_sha256=(digest(999),),
        )
    assert dependency_error.value.code == "lean_worker_stale_result"
    toolchain_key = replace(base, toolchain="leanprover/lean4:changed")
    registry_key = replace(base, base_registry_fingerprint=digest(998))
    for changed_key in (toolchain_key, registry_key):
        result = instance.validate(
            session_id=session_id,
            owner="case-a",
            key=changed_key,
            source_path=path,
            dependency_sha256=changed_key.dependency_sha256,
        )
        assert result.verified and not result.cache_hit
    assert workers[0].validate_count == 3
    instance.close()


def test_source_must_declare_and_close_the_session_namespace(tmp_path: Path) -> None:
    instance, _ = pool(tmp_path)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    wrong = SOURCE.replace(NAMESPACE, "HardnessValidation.Other")
    path = source_file(tmp_path, wrong)
    wrong_key = key(session_id=session_id, source=wrong)
    with pytest.raises(HardnessContractError) as captured:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=wrong_key,
            source_path=path,
            dependency_sha256=wrong_key.dependency_sha256,
        )
    assert captured.value.code == "lean_worker_session_leak"
    instance.close()


def test_error_diagnostics_are_not_cached_as_capabilities(tmp_path: Path) -> None:
    diagnostics = [{"severity": 1, "message": "unknown identifier"}]
    instance, workers = pool(tmp_path, diagnostics=diagnostics)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    first = instance.validate(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
    )
    second = instance.validate(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
    )
    assert not first.verified and not second.verified
    assert not first.cache_hit and not second.cache_hit
    assert workers[0].validate_count == 2
    instance.close()


def test_worker_crash_uses_one_audited_cold_fallback(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def fake_run_command(*args: object, **kwargs: object) -> CommandResult:
        del args, kwargs
        return CommandResult(
            command=("lake", "env", "lean", "Candidate.lean"),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.01,
        )

    monkeypatch.setattr(worker_module, "run_command", fake_run_command)
    instance, _ = pool(tmp_path, crash=True)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    result = instance.validate(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
    )
    assert result.verified and result.fallback_used
    assert instance.worker_crash_count == 1
    assert instance.worker_restart_count == 1
    assert instance.cold_fallback_count == 1
    assert instance.to_dict()["cache_entry_count"] == 0
    instance.close()


def test_worker_crash_without_fallback_fails_closed(tmp_path: Path) -> None:
    instance, _ = pool(tmp_path, crash=True)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    with pytest.raises(HardnessContractError) as captured:
        instance.validate(
            session_id=session_id,
            owner="case-a",
            key=cache_key,
            source_path=path,
            dependency_sha256=cache_key.dependency_sha256,
            allow_cold_fallback=False,
        )
    assert captured.value.code == "lean_worker_crashed"
    instance.close()


def test_pool_never_starts_more_than_four_workers(tmp_path: Path) -> None:
    instance, workers = pool(tmp_path, maximum_workers=4)
    for index in range(12):
        namespace = f"HardnessValidation.Session{index}"
        instance.start_session(owner=f"case-{index}", namespace=namespace)
    assert len(workers) == 4
    assert instance.worker_start_count == 4
    assert all(worker.started for worker in workers)
    instance.close()


def test_restart_invalidates_only_the_affected_worker_cache(tmp_path: Path) -> None:
    instance, _ = pool(tmp_path, maximum_workers=2)
    session_a = instance.start_session(owner="case-a", namespace=NAMESPACE)
    namespace_b = "HardnessValidation.SessionB"
    session_b = instance.start_session(owner="case-b", namespace=namespace_b)
    path_a = source_file(tmp_path)
    source_b = SOURCE.replace(NAMESPACE, namespace_b)
    path_b = tmp_path / "workspace" / "Generated" / "ValidationB.lean"
    path_b.write_text(source_b, encoding="utf-8")
    key_a = key(session_id=session_a)
    key_b = key(session_id=session_b, source=source_b, namespace=namespace_b)
    for owner, session_id, cache_key, path in (
        ("case-a", session_a, key_a, path_a),
        ("case-b", session_b, key_b, path_b),
    ):
        instance.validate(
            session_id=session_id,
            owner=owner,
            key=cache_key,
            source_path=path,
            dependency_sha256=cache_key.dependency_sha256,
        )
    assert instance.to_dict()["cache_entry_count"] == 2
    instance._restart_worker(0)
    assert instance.to_dict()["cache_entry_count"] == 1
    cached_b = instance.validate(
        session_id=session_b,
        owner="case-b",
        key=key_b,
        source_path=path_b,
        dependency_sha256=key_b.dependency_sha256,
    )
    assert cached_b.cache_hit
    instance.close()


def test_twenty_repeat_microbenchmark_observes_parallel_cold_and_fast_warm_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lock = threading.Lock()
    active = 0
    max_active = 0

    def fake_run_command(*args: object, **kwargs: object) -> CommandResult:
        nonlocal active, max_active
        del args, kwargs
        with lock:
            active += 1
            max_active = max(max_active, active)
        time.sleep(0.02)
        with lock:
            active -= 1
        return CommandResult(
            command=("lake", "env", "lean", "Candidate.lean"),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.02,
        )

    monkeypatch.setattr(worker_module, "run_command", fake_run_command)
    instance, _ = pool(tmp_path, maximum_workers=4, delay=0.001)
    session_id = instance.start_session(owner="case-a", namespace=NAMESPACE)
    path = source_file(tmp_path)
    cache_key = key(session_id=session_id)
    result = instance.microbenchmark(
        session_id=session_id,
        owner="case-a",
        key=cache_key,
        source_path=path,
        dependency_sha256=cache_key.dependency_sha256,
        cold_parallelism=2,
    )
    assert result["repeat_count"] == 20
    assert result["cold_parallelism"] == 2
    assert len(result["forced_cold_seconds"]) == 20
    assert len(result["persistent_warm_seconds"]) == 20
    assert result["persistent_priming_seconds"] >= 0
    assert 2 <= max_active <= 4
    assert all(result["gates"].values())
    instance.close()
