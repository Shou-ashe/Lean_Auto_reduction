"""Archon-loop model client for the NP-hard benchmark lanes.

This module contains both the legacy ``ArchonModelClient`` adapter and the
case-level black-box entrypoint used for fair agent comparison.  The legacy
adapter implements the same ``complete_json`` contract as
:class:`agent.hardness.model_client.DeepSeekClient`; the black-box entrypoint
is :meth:`ArchonModelClient.prove_case`.

The client understands exactly two prompt shapes (everything else is a
clean protocol error):

- the V2 node prompt (``hardness_np_hard_node_request_v1`` with a
  ``response_template`` whose ``action`` is ``submit_node_patch``), used by
  ``NPHardGapRuntimeV1``;
- the legacy model-authoring prompt
  (``AUTHORING_REQUEST_JSON``...``RETURN_EXACT_JSON_SHAPE``), used by the
  exact-edge ``HardnessAgent``.

Each black-box call creates a fresh target module inside a source-hidden worker
under ``output_dir/work/archon``.  The worker contains only the generated
objective source and Archon's own state; the project ``ComplexityReduction``
sources are not copied.  Lean receives already-built dependency ``.olean``
files via ``LEAN_PATH`` so the kernel can check the proof without exposing the
library implementation to the model.  No recommended body, oracle, route,
typed DAG, dependency body, or previous-case state is staged.

``worker_count`` (default 1) sizes the worker pool: concurrent
``complete_json`` calls each reserve their own worker (own Lean tree,
``.archon`` state, and logs), so parallel benchmark jobs share concurrent
Archon loops instead of serializing behind one lock.  Worker 0 keeps the
legacy layout (``output_dir/work/archon/Lean``); workers 1..N-1 live in
``output_dir/work/archon/worker-<i>/``.

The caller's Lean gates stay authoritative: the returned body is validated
and compiled by the unmodified gap runtime / authoring worker, exactly as a
DeepSeek response would be.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import threading
import time
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .model_client import DeepSeekConfig, ModelResponse

NODE_REQUEST_SCHEMA = "hardness_np_hard_node_request_v1"
NODE_PATCH_SCHEMA = "hardness_np_hard_node_patch_v1"
MODEL_PATCH_SCHEMA = "hardness_model_patch_v1"

AUTHORING_PROMPT_HEADER = "AUTHORING_REQUEST_JSON"
AUTHORING_SHAPE_MARKER = "RETURN_EXACT_JSON_SHAPE"

BODY_START_MARKER = "/- ARCHON_BODY_START -/"
BODY_END_MARKER = "/- ARCHON_BODY_END -/"

WORKER_RELATIVE = "work/archon"


class ArchonModelClientError(Exception):
    """Protocol error raised by the archon model client."""


@dataclass(frozen=True)
class ArchonGoalResult:
    """One source-hidden, case-level Archon proof attempt."""

    ok: bool
    body: str | None
    error: str | None
    duration_seconds: float
    usage: dict[str, Any] | None
    objective_source: str
    user_hints: str
    worker_index: int
    call_index: int
    log_file: str | None
    archon_exit_code: int | None
    visible_lean_sources: tuple[str, ...]


@dataclass(frozen=True)
class PublicCaseMaterial:
    """The complete benchmark-owned task material exposed to comparison arms.

    Archon receives these two strings as ``USER_HINTS.md`` and its only Lean
    source file.  The direct one-shot LLM baseline serializes the exact same
    strings into one chat request, so neither arm receives extra task facts.
    """

    objective_source: str
    user_hints: str


class _ArchonWorker:
    """One isolated Archon loop workspace (own Lean tree, state, and logs)."""

    __slots__ = ("index", "dir", "lock", "call_counter", "last_usage")

    def __init__(self, *, index: int, dir: Path):
        self.index = index
        self.dir = dir
        self.lock = threading.Lock()
        self.call_counter = 0
        self.last_usage: dict[str, Any] | None = None

    @property
    def lean_dir(self) -> Path:
        return self.dir / "Lean"

    @property
    def logs_dir(self) -> Path:
        return self.dir / "logs"


def _resolve_archon_cli(value: str | Path | None) -> str | None:
    if value is None:
        return shutil.which("archon")
    resolved = Path(value).expanduser()
    if not resolved.is_file():
        return str(resolved)
    return str(resolved.resolve())


def _archon_template_dir(archon_cli: str | None) -> Path | None:
    """Locate the shipped ``archon-template`` state-file directory.

    Works for both a source checkout (compare/Archon/.venv/bin/archon) and a
    regular site-packages install; returns None when the layout is unknown so
    the worker falls back to hand-written minimal state files.
    """

    if not archon_cli:
        return None
    cli = Path(archon_cli).resolve()
    candidates = [
        cli.parent.parent.parent / "src" / "archon" / ".archon-src" / "archon-template",
    ]
    site_packages = cli.parent.parent / "lib"
    if site_packages.is_dir():
        for package_dir in site_packages.glob("python*/site-packages/archon"):
            candidates.append(package_dir / ".archon-src" / "archon-template")
    for candidate in candidates:
        if candidate.is_dir() and (candidate / "AGENTS.md").is_file():
            return candidate
    return None


def _module_for_path(relative: Path) -> str:
    components = list(relative.parts)
    if components and components[0].endswith(".lean"):
        components[0] = components[0][: -len(".lean")]
    return ".".join(components)


def _sanitize_component(value: str, *, fallback: str) -> str:
    cleaned = "".join(character for character in value if character.isalnum() or character == "_")
    if not cleaned:
        return fallback
    if cleaned[0].isdigit():
        cleaned = "N" + cleaned
    return cleaned


def _common_candidate_module(declarations: list[str]) -> str:
    """Longest common namespace of full declaration names."""
    components = [declaration.split(".") for declaration in declarations]
    prefix = components[0][:-1]
    for candidate in components[1:]:
        limit = min(len(prefix), len(candidate) - 1)
        while limit > 0 and prefix[:limit] != candidate[:limit]:
            limit -= 1
        prefix = prefix[:limit]
    return ".".join(prefix)


def _namespace_ladder(module: str) -> list[str]:
    return [component for component in module.split(".") if component]


def _dedent_two(source: str) -> str:
    lines = [line[2:] if line.startswith("  ") else line for line in source.splitlines()]
    return "\n".join(lines).strip()


def _indent_two(source: str) -> str:
    return "\n".join(
        f"  {line}" if line.strip() else line for line in source.splitlines()
    )


def _extract_marked_body(source: str) -> str:
    start = source.find(BODY_START_MARKER)
    end = source.find(BODY_END_MARKER)
    if start < 0 or end < 0 or end <= start:
        raise ArchonModelClientError(
            "archon loop removed the scaffold body fence markers"
        )
    body = source[start + len(BODY_START_MARKER) : end]
    body = _dedent_two(body)
    if not body:
        raise ArchonModelClientError("archon loop left the scaffold body empty")
    return body


def _visible_worker_sources(worker: _ArchonWorker) -> tuple[str, ...]:
    """Lean sources readable by the benchmark model (Archon snapshots excluded)."""

    return tuple(
        sorted(
            str(path.relative_to(worker.lean_dir))
            for path in worker.lean_dir.rglob("*.lean")
            if path.is_file() and ".archon" not in path.relative_to(worker.lean_dir).parts
        )
    )


class ArchonModelClient:
    """Run the Archon CLI prove-loop to produce one model-client response."""

    def __init__(
        self,
        *,
        root: Path,
        output_dir: Path,
        archon_cli: str | Path | None = None,
        max_iterations: int = 8,
        loop_timeout_seconds: int = 7200,
        report_config: DeepSeekConfig | None = None,
        worker_count: int = 1,
        benchmark_tool_rounds: int = 16,
    ):
        self.root = Path(root).resolve()
        self.output_dir = Path(output_dir).resolve()
        self.archon_cli = _resolve_archon_cli(archon_cli)
        self.max_iterations = _positive_int(max_iterations, label="archon max iterations")
        self.loop_timeout_seconds = _positive_int(
            loop_timeout_seconds, label="archon loop timeout"
        )
        self.config = report_config or DeepSeekConfig(api_key=None)
        self.worker_count = _positive_int(worker_count, label="worker count")
        self.benchmark_tool_rounds = _positive_int(
            benchmark_tool_rounds, label="benchmark tool rounds"
        )
        if self.benchmark_tool_rounds > 60:
            raise ValueError("benchmark tool rounds must be at most 60")
        self.worker_dir = self.output_dir / WORKER_RELATIVE
        self._workers = [
            _ArchonWorker(
                index=i,
                dir=self.worker_dir if i == 0 else self.worker_dir / f"worker-{i}",
            )
            for i in range(self.worker_count)
        ]
        self._allocation_lock = threading.Lock()
        self._cursor = -1

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        started = time.monotonic()
        worker, call_index = self._acquire_worker()
        try:
            return self._complete_locked(
                started=started, prompt=prompt, worker=worker, call_index=call_index
            )
        finally:
            worker.lock.release()

    def prove_case(
        self,
        *,
        case_id: str,
        statement: str,
        requirement: str,
        imports: tuple[str, ...],
        exact_type: str,
    ) -> ArchonGoalResult:
        """Ask Archon to solve one whole public case with no benchmark hints.

        The worker is reset before every call.  Its only Lean source is a
        single definition with a fenced ``by sorry`` body.  The first Archon
        iteration starts directly at the prover phase so an Archon planner
        cannot enrich the task from benchmark-owned state.
        """

        started = time.monotonic()
        worker, call_index = self._acquire_worker()
        objective_source = ""
        user_hints = ""
        log_file: str | None = None
        exit_code: int | None = None
        visible_sources: tuple[str, ...] = ()
        target_file: Path | None = None
        try:
            material = render_public_case_material(
                case_id=case_id,
                statement=statement,
                requirement=requirement,
                imports=imports,
                exact_type=exact_type,
            )
            safe_case = _sanitize_component(case_id, fallback="Case")
            module = f"Generated.ArchonBenchmark.{safe_case}"
            objective_source = material.objective_source
            user_hints = material.user_hints
            _, target_file = self._stage_call(
                worker=worker,
                call_index=call_index,
                module=module,
                target_short=safe_case,
                scaffold=objective_source,
                hints=user_hints,
                fresh=True,
            )
            loop_log, exit_code = self._run_archon_loop(
                worker=worker,
                call_index=call_index,
                target_file=target_file,
                from_prover=True,
            )
            log_file = str(loop_log)
            objective_source = target_file.read_text(encoding="utf-8")
            body = _extract_marked_body(objective_source)
            visible_sources = _visible_worker_sources(worker)
            return ArchonGoalResult(
                ok=True,
                body=body,
                error=None,
                duration_seconds=round(time.monotonic() - started, 3),
                usage=worker.last_usage,
                objective_source=objective_source,
                user_hints=user_hints,
                worker_index=worker.index,
                call_index=call_index,
                log_file=log_file,
                archon_exit_code=exit_code,
                visible_lean_sources=visible_sources,
            )
        except Exception as error:
            if target_file is not None and target_file.is_file():
                try:
                    objective_source = target_file.read_text(encoding="utf-8")
                except OSError:
                    pass
            if worker.lean_dir.is_dir():
                visible_sources = _visible_worker_sources(worker)
            return ArchonGoalResult(
                ok=False,
                body=None,
                error=self.config.redact(
                    f"{type(error).__name__}: {error}"
                ),
                duration_seconds=round(time.monotonic() - started, 3),
                usage=worker.last_usage,
                objective_source=objective_source,
                user_hints=user_hints,
                worker_index=worker.index,
                call_index=call_index,
                log_file=log_file,
                archon_exit_code=exit_code,
                visible_lean_sources=visible_sources,
            )
        finally:
            worker.lock.release()

    def _complete_locked(
        self,
        *,
        started: float,
        prompt: str,
        worker: _ArchonWorker,
        call_index: int,
    ) -> ModelResponse:
        try:
            content = self._respond(prompt=prompt, worker=worker, call_index=call_index)
        except ArchonModelClientError as error:
            return self._failure(
                started=started,
                error=self.config.redact(str(error)),
            )
        except Exception as error:
            return self._failure(
                started=started,
                error=self.config.redact(
                    f"archon model client raised {type(error).__name__}: {error}"
                ),
            )
        if content is None:
            return self._failure(
                started=started,
                error="unsupported model prompt shape for the archon client",
            )
        usage = worker.last_usage or {
            "prompt_tokens": max(1, len(prompt) // 4),
            "completion_tokens": max(1, len(content) // 4),
            "total_tokens": max(2, len(prompt) // 4 + len(content) // 4),
            "archon_loop": True,
            "archon_usage_fallback": True,
        }
        return ModelResponse(
            called=True,
            ok=True,
            content=content,
            error=None,
            status_code=200,
            duration_seconds=round(time.monotonic() - started, 3),
            usage=usage,
            attempts=1,
            finish_reason="archon-loop",
        )

    def _failure(self, *, started: float, error: str) -> ModelResponse:
        return ModelResponse(
            called=True,
            ok=False,
            content="",
            error=error,
            status_code=None,
            duration_seconds=round(time.monotonic() - started, 3),
            usage=None,
            attempts=1,
        )

    def _respond(
        self, *, prompt: str, worker: _ArchonWorker, call_index: int
    ) -> str | None:
        if prompt.lstrip().startswith("{"):
            try:
                payload = json.loads(prompt)
            except json.JSONDecodeError:
                return None
            if not isinstance(payload, dict):
                return None
            if payload.get("schema_version") != NODE_REQUEST_SCHEMA:
                return None
            template = payload.get("response_template")
            if not isinstance(template, dict):
                return None
            if template.get("action") != "submit_node_patch":
                return None
            return self._node_patch(
                payload=payload, worker=worker, call_index=call_index
            )
        if prompt.lstrip().startswith(AUTHORING_PROMPT_HEADER):
            return self._authoring_patch(
                prompt=prompt, worker=worker, call_index=call_index
            )
        return None

    # ── prompts ───────────────────────────────────────────────────────

    def _node_patch(
        self,
        *,
        payload: Mapping[str, Any],
        worker: _ArchonWorker,
        call_index: int,
    ) -> str:
        node_request = payload.get("node_request")
        if not isinstance(node_request, dict):
            raise ArchonModelClientError("node prompt is missing node_request")
        node = node_request.get("node")
        if not isinstance(node, dict):
            raise ArchonModelClientError("node request is missing its node")
        template = payload["response_template"]
        dependency_bodies = payload.get("accepted_dependency_bodies")
        if not isinstance(dependency_bodies, dict):
            raise ArchonModelClientError(
                "node prompt is missing accepted_dependency_bodies"
            )
        declarations = [str(node.get("declaration") or "")]
        for declaration in dependency_bodies:
            declarations.append(str(declaration))
        module = _common_candidate_module(declarations)
        if not module:
            raise ArchonModelClientError(
                "cannot derive the candidate module from the node declarations"
            )
        imports = tuple(
            str(name) for name in (node_request.get("allowed_imports") or ())
        )
        source_problem = node_request.get("source_problem") or {}
        target_problem = node_request.get("target_problem") or {}
        target_declaration = str(node.get("declaration") or "")
        target_short = target_declaration.removeprefix(module + ".")
        target_exact_type = str(node.get("exact_type") or "").strip()
        current_body = "by\n  sorry"
        ordering = _gap_order(
            module=module, dependency_bodies=dependency_bodies, target=target_declaration
        )
        scaffold = _render_scaffold(
            module=module,
            imports=imports,
            opens=(
                "ComplexityReduction",
                "ComplexityReduction.Certificate",
                "ComplexityReduction.Encoding",
                "ComplexityReduction.Program",
                str(source_problem.get("module") or ""),
                str(target_problem.get("module") or ""),
            ),
            dependencies=ordering,
            target_short=target_short,
            target_exact_type=target_exact_type,
            current_body=current_body,
        )
        user_hints = _node_user_hints(
            module=module,
            target_declaration=target_declaration,
            target_short=target_short,
            target_exact_type=target_exact_type,
        )
        call_index, target_file = self._stage_call(
            worker=worker,
            call_index=call_index,
            module=module,
            target_short=target_short,
            scaffold=scaffold,
            hints=user_hints,
        )
        self._run_archon_loop(worker=worker, call_index=call_index)
        body = _extract_marked_body(target_file.read_text(encoding="utf-8"))
        envelope = dict(template)
        envelope["replacement_body"] = body
        return json.dumps(envelope, ensure_ascii=False)

    def _authoring_patch(
        self, *, prompt: str, worker: _ArchonWorker, call_index: int
    ) -> str:
        marker = AUTHORING_SHAPE_MARKER + "\n"
        suffix = prompt.split(marker, 1)[-1]
        try:
            shape = json.loads(suffix)
        except json.JSONDecodeError:
            raise ArchonModelClientError(
                "authoring prompt has no parseable RETURN_EXACT_JSON_SHAPE payload"
            ) from None
        if not isinstance(shape, dict):
            raise ArchonModelClientError(
                "authoring response shape is not one JSON object"
            )
        header = prompt.split("\n", 1)[1].split("\n\n", 1)[0]
        request = json.loads(header)
        if not isinstance(request, dict):
            raise ArchonModelClientError("authoring request JSON is invalid")
        module = str(request.get("candidate_module") or "")
        declaration = str(request.get("candidate_declaration") or "")
        expected_type = str(request.get("expected_type") or "").strip()
        imports = tuple(str(name) for name in (request.get("allowed_imports") or ()))
        short = declaration.removeprefix(module + ".")
        current_body = "by\n  sorry"
        scaffold = _render_scaffold(
            module=module,
            imports=imports,
            opens=(),
            dependencies=(),
            target_short=short,
            target_exact_type=expected_type,
            current_body=current_body,
        )
        user_hints = _authoring_user_hints(
            module=module,
            target_declaration=declaration,
            target_short=short,
            expected_type=expected_type,
        )
        call_index, target_file = self._stage_call(
            worker=worker,
            call_index=call_index,
            module=module,
            target_short=short,
            scaffold=scaffold,
            hints=user_hints,
        )
        self._run_archon_loop(worker=worker, call_index=call_index)
        body = _extract_marked_body(target_file.read_text(encoding="utf-8"))
        envelope = dict(shape)
        envelope["replacement"] = _indent_two(body)
        return json.dumps(envelope, ensure_ascii=False)

    # ── worker lifecycle ──────────────────────────────────────────────

    def _acquire_worker(self) -> tuple[_ArchonWorker, int]:
        """Reserve the next free worker slot, round-robin across the pool.

        Returns ``(worker, call_index)``; the caller must release
        ``worker.lock`` when done.  When every worker is busy the call
        blocks until one frees up.
        """
        with self._allocation_lock:
            for _ in range(self.worker_count):
                self._cursor = (self._cursor + 1) % self.worker_count
                worker = self._workers[self._cursor]
                if worker.lock.acquire(blocking=False):
                    worker.call_counter += 1
                    return worker, worker.call_counter
        worker = self._workers[self._cursor]
        worker.lock.acquire()
        worker.call_counter += 1
        return worker, worker.call_counter

    def _ensure_worker(self, worker: _ArchonWorker | None = None) -> None:
        if worker is None:
            worker = self._workers[0]
        lean_target = worker.lean_dir
        if lean_target.is_dir() and (lean_target / ".archon").is_dir():
            return
        source = self.root / "Lean"
        if not (source / "lakefile.toml").is_file() or not (
            source / "Reference" / "ComplexityReduction"
        ).is_dir():
            raise ArchonModelClientError(
                f"archon worker needs a Lean library at {source}"
            )
        compiled = self._compiled_lean_path()
        if compiled is None:
            raise ArchonModelClientError(
                "archon worker needs prebuilt Lean dependencies; run the "
                "benchmark preflight or build the root Lean project first"
            )
        worker.dir.mkdir(parents=True, exist_ok=True)
        if lean_target.exists():
            shutil.rmtree(lean_target)
        lean_target.mkdir(parents=True, exist_ok=False)
        for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
            shutil.copy2(source / name, lean_target / name)
        # Deliberately do not copy any project source.  The only Lean source
        # visible in the worker is the per-call scaffold created by
        # ``_stage_call`` below.  Imports resolve through the prebuilt olean
        # path installed in ``_loop_environment``.
        (
            lean_target
            / "Reference"
            / "ComplexityReduction"
            / "Agent"
            / "Hardness"
            / "ArchonWorker"
        ).mkdir(parents=True, exist_ok=True)
        packages = source / ".lake" / "packages"
        if packages.is_dir():
            lake_parent = lean_target / ".lake"
            lake_parent.mkdir(parents=True, exist_ok=True)
            (lake_parent / "packages").symlink_to(
                packages, target_is_directory=True
            )
        self._write_worker_config(worker)

    def _reset_worker(self, worker: _ArchonWorker) -> None:
        """Remove all model-visible state from the preceding case."""

        if worker.lean_dir.exists():
            shutil.rmtree(worker.lean_dir)
        self._ensure_worker(worker)

    def _compiled_lean_path(self) -> Path | None:
        """Return the trusted prebuilt olean directory, never a source tree."""
        candidates = (
            self.output_dir
            / "isolated-workspace"
            / "Lean"
            / ".lake"
            / "build"
            / "lib"
            / "lean",
            self.root / "Lean" / ".lake" / "build" / "lib" / "lean",
        )
        for candidate in candidates:
            if candidate.is_dir() and (candidate / "ComplexityReduction").is_dir():
                return candidate.resolve()
        return None

    def _write_worker_config(self, worker: _ArchonWorker) -> None:
        lean_root = worker.lean_dir
        archon_root = lean_root / ".archon"
        archon_root.mkdir(parents=True, exist_ok=True)
        config = {
            "loop": {
                "harness": "deepseek",
                "parallel": False,
                "max_parallel": 1,
                "max_objectives": 1,
            }
        }
        (archon_root / "config.json").write_text(
            json.dumps(config, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        (archon_root / "prompts").mkdir(exist_ok=True)
        template_dir = _archon_template_dir(self.archon_cli)
        if template_dir is not None:
            for name in (
                "AGENTS.md",
                "ARCHON_MEMORY.md",
                "STRATEGY.md",
                "task_pending.md",
                "task_done.md",
                "USER_HINTS.md",
            ):
                source = template_dir / name
                if source.is_file() and not (archon_root / name).exists():
                    shutil.copy2(source, archon_root / name)
            data_root = template_dir.parent
            for name in ("prompts", "prover-modes"):
                source_dir = data_root / name
                if source_dir.is_dir():
                    shutil.copytree(
                        source_dir,
                        archon_root / name,
                        dirs_exist_ok=True,
                    )
        project = lean_root / "PROJECT.md"
        project.write_text(
            "\n".join(
                [
                    "# Archon Worker Project",
                    "",
                    "Source-hidden formal benchmark worker. The only project",
                    "source visible here is the single fenced objective file.",
                    "ComplexityReduction dependencies are available to Lean only",
                    "as compiled .olean files; their source code is intentionally",
                    "absent and access outside this worker is blocked. Finish the fenced body",
                    "with real Lean terms only: sorry, admit, axiom and unsafe",
                    "code are forbidden.",
                    "",
                ]
            ),
            encoding="utf-8",
        )

    def _stage_call(
        self,
        *,
        worker: _ArchonWorker,
        call_index: int,
        module: str,
        target_short: str,
        scaffold: str,
        hints: str,
        fresh: bool = False,
    ) -> tuple[int, Path]:
        if fresh:
            self._reset_worker(worker)
        else:
            self._ensure_worker(worker)
        safe_short = _sanitize_component(target_short, fallback="Target")
        relative = (
            Path("Reference")
            / "ComplexityReduction"
            / "Agent"
            / "Hardness"
            / "ArchonWorker"
            / f"{safe_short}-Run-{call_index:03d}.lean"
        )
        target_file = worker.lean_dir / relative
        target_file.parent.mkdir(parents=True, exist_ok=True)
        target_file.write_text(scaffold, encoding="utf-8")
        hints_path = worker.lean_dir / ".archon" / "USER_HINTS.md"
        hints_path.write_text(hints, encoding="utf-8")
        progress = worker.lean_dir / ".archon" / "PROGRESS.md"
        progress.write_text(
            PROGRESS_SEED.format(objective_file=relative.as_posix()) + "\n",
            encoding="utf-8",
        )
        return call_index, target_file

    def _run_archon_loop(
        self,
        *,
        worker: _ArchonWorker,
        call_index: int,
        target_file: Path | None = None,
        from_prover: bool = False,
    ) -> tuple[Path, int]:
        if self.archon_cli is None:
            raise ArchonModelClientError(
                "archon CLI is not installed; pass --archon-cli or install "
                "'archon' on PATH"
            )
        worker.logs_dir.mkdir(parents=True, exist_ok=True)
        log_path = worker.logs_dir / f"loop-{call_index:03d}.txt"
        command = [
            self.archon_cli,
            "loop",
            str(worker.lean_dir),
            "--max-iterations",
            str(self.max_iterations),
            "--serial",
            "--no-dashboard",
            "--no-finalize",
            "--no-git-commit",
            "--no-blueprint-web",
        ]
        if from_prover:
            command.extend(("--from", "prover"))
        environment = self._loop_environment(
            objective_file=target_file,
            worker=worker,
        )
        usage_offsets = _jsonl_offsets(worker.lean_dir / ".archon" / "logs")
        worker.last_usage = None
        started = time.monotonic()
        with log_path.open("w", encoding="utf-8") as output:
            try:
                completed = subprocess.run(
                    command,
                    cwd=worker.lean_dir,
                    env=environment,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    timeout=self.loop_timeout_seconds,
                    start_new_session=True,
                    check=False,
                )
            except subprocess.TimeoutExpired:
                raise ArchonModelClientError(
                    f"archon loop exceeded {self.loop_timeout_seconds}s; "
                    f"log: {log_path}"
                ) from None
        if log_path.stat().st_size == 0:
            raise ArchonModelClientError(
                f"archon loop produced no output; command: {' '.join(command)}"
            )
        worker.last_usage = _collect_archon_usage(
            worker.lean_dir / ".archon" / "logs", usage_offsets
        )
        return log_path, int(getattr(completed, "returncode", 0) or 0)

    def _loop_environment(
        self,
        *,
        objective_file: Path | None = None,
        worker: _ArchonWorker | None = None,
    ) -> dict[str, str]:
        environment = dict(os.environ)
        compiled = self._compiled_lean_path()
        if compiled is None:
            raise ArchonModelClientError(
                "prebuilt Lean dependency path disappeared before archon loop"
            )
        inherited_lean_path = environment.get("LEAN_PATH")
        environment["LEAN_PATH"] = (
            f"{compiled}{os.pathsep}{inherited_lean_path}"
            if inherited_lean_path
            else str(compiled)
        )
        environment["ARCHON_RESTRICT_PROJECT_ROOT"] = "1"
        environment["ARCHON_DISABLE_WEB_TOOLS"] = "1"
        if objective_file is not None:
            if worker is None:
                raise ArchonModelClientError(
                    "objective-scoped environment requires its worker"
                )
            environment["ARCHON_BENCHMARK_OBJECTIVE_FILE"] = (
                objective_file.resolve().relative_to(worker.lean_dir.resolve()).as_posix()
            )
            environment["ARCHON_BENCHMARK_BODY_FENCE_ONLY"] = "1"
            environment["ARCHON_BENCHMARK_MAX_TOOL_ROUNDS"] = str(
                self.benchmark_tool_rounds
            )
        if self.config.api_key:
            environment["DEEPSEEK_API_KEY"] = self.config.api_key
        environment["DEEPSEEK_BASE_URL"] = self.config.base_url
        environment["DEEPSEEK_MODEL"] = self.config.model
        environment["DEEPSEEK_TIMEOUT_SECONDS"] = str(self.config.timeout_seconds)
        environment["DEEPSEEK_MAX_TOKENS"] = str(self.config.max_tokens)
        environment["DEEPSEEK_MAX_RETRIES"] = str(self.config.max_retries)
        if self.config.reasoning_effort:
            environment["DEEPSEEK_REASONING_EFFORT"] = self.config.reasoning_effort
        return environment


def _positive_int(value: int, *, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{label} must be a positive integer")
    return value


def _gap_order(
    *,
    module: str,
    dependency_bodies: Mapping[str, Any],
    target: str,
) -> list[tuple[str, str]]:
    """Dependency declarations in prompt order, as (short_name, body)."""
    ordered: list[tuple[str, str]] = []
    for declaration, body in dependency_bodies.items():
        declaration = str(declaration)
        if declaration == target:
            continue
        if not isinstance(body, str):
            continue
        ordered.append((declaration.removeprefix(module + "."), body))
    return ordered


def _render_scaffold(
    *,
    module: str,
    imports: tuple[str, ...],
    opens: tuple[str, ...],
    dependencies: list[tuple[str, str]],
    target_short: str,
    target_exact_type: str,
    current_body: str,
) -> str:
    lines: list[str] = [f"import {name}" for name in imports if name]
    lines.append("")
    lines.append(f"namespace {module}")
    lines.append("")
    for opened in opens:
        if opened:
            lines.append(f"open {opened}")
    lines.append("")
    for short_name, body in dependencies:
        rendered = "\n".join(f"  {line}" for line in body.rstrip().splitlines())
        lines.append(f"noncomputable def {short_name} :=\n{rendered}")
        lines.append("")
    lines.append(f"noncomputable def {target_short} :")
    lines.append(f"    {target_exact_type} :=")
    lines.append(BODY_START_MARKER)
    lines.append(_indent_two(current_body.rstrip()))
    lines.append(BODY_END_MARKER)
    lines.append(f"end {module}")
    lines.append("")
    return "\n".join(lines)


def _node_user_hints(
    *,
    module: str,
    target_declaration: str,
    target_short: str,
    target_exact_type: str,
) -> str:
    lines = [
            "# USER_HINTS",
            "",
            f"- Edit ONLY the fenced body of `{target_short}` in the objective file.",
            f"- Target: `{target_declaration}`.",
            f"- Required type: `{target_exact_type}`.",
            "- Keep the `/- ARCHON_BODY_START -/` and `/- ARCHON_BODY_END -/`",
            "  comment fences exactly where they are; only the text between them",
            "  may change.",
            "- Every other file in this module tree is read-only and already",
            "  compiles. Never change dependency bodies or add import lines.",
            "- `sorry`, `admit`, `axiom` and `unsafe` are forbidden. The final",
            "  body must be a complete Lean term of the required type.",
        ]
    lines.append("")
    return "\n".join(lines)


def _authoring_user_hints(
    *,
    module: str,
    target_declaration: str,
    target_short: str,
    expected_type: str,
) -> str:
    lines = [
            "# USER_HINTS",
            "",
            f"- Edit ONLY the fenced body of `{target_short}` in the objective file.",
            f"- Target: `{target_declaration}`.",
            f"- Required type: `{expected_type}`.",
            "- Keep the `/- ARCHON_BODY_START -/` and `/- ARCHON_BODY_END -/`",
            "  comment fences exactly where they are; only the text between them",
            "  may change.",
            "- Everything outside the fences is read-only. Do not add imports.",
            "- `sorry`, `admit`, `axiom` and `unsafe` are forbidden.",
        ]
    lines.append("")
    return "\n".join(lines)


def _case_user_hints(*, statement: str, requirement: str) -> str:
    """Render the complete benchmark-owned input visible to Archon."""

    return "\n".join(
        [
            "# USER_HINTS",
            "",
            "## Problem statement",
            statement.strip(),
            "",
            "## Requirement",
            requirement.strip(),
            "",
            "The only Lean source file in this project is the formal goal.",
            "Edit only the body between `/- ARCHON_BODY_START -/` and",
            "`/- ARCHON_BODY_END -/`; preserve both markers and everything",
            "outside them. Check the goal with `lake env lean <goal-file>`.",
            "Search/suggestion commands and tactics such as `#check`, `exact?`,",
            "`apply?`, `simp?`, `library_search`, and meta-environment inspection",
            "are disabled; solve only from the stated input.",
            "Do not use `sorry`, `admit`, `axiom`, or `unsafe`.",
            "",
        ]
    )


def render_public_case_material(
    *,
    case_id: str,
    statement: str,
    requirement: str,
    imports: tuple[str, ...],
    exact_type: str,
) -> PublicCaseMaterial:
    """Render the exact public task material shared by Archon and one-shot LLM."""

    safe_case = _sanitize_component(case_id, fallback="Case")
    return PublicCaseMaterial(
        objective_source=_render_scaffold(
            module=f"Generated.ArchonBenchmark.{safe_case}",
            imports=imports,
            opens=(),
            dependencies=[],
            target_short="result",
            target_exact_type=exact_type,
            current_body="by\n  sorry",
        ),
        user_hints=_case_user_hints(
            statement=statement,
            requirement=requirement,
        ),
    )


def _jsonl_offsets(log_root: Path) -> dict[Path, int]:
    if not log_root.is_dir():
        return {}
    return {
        path: path.stat().st_size
        for path in log_root.rglob("*.jsonl")
        if path.is_file()
    }


def _collect_archon_usage(
    log_root: Path, offsets: dict[Path, int]
) -> dict[str, Any] | None:
    input_tokens = 0
    output_tokens = 0
    estimated_cost_usd = 0.0
    sessions = 0
    if not log_root.is_dir():
        return None
    for path in log_root.rglob("*.jsonl"):
        if not path.is_file():
            continue
        try:
            with path.open("rb") as handle:
                handle.seek(offsets.get(path, 0))
                for raw_line in handle:
                    try:
                        row = json.loads(raw_line.decode("utf-8"))
                    except (UnicodeDecodeError, json.JSONDecodeError):
                        continue
                    if row.get("event") != "session_end":
                        continue
                    sessions += 1
                    input_tokens += int(row.get("input_tokens") or 0)
                    output_tokens += int(row.get("output_tokens") or 0)
                    estimated_cost_usd += float(row.get("total_cost_usd") or 0.0)
        except OSError:
            continue
    if sessions == 0:
        return None
    return {
        "prompt_tokens": input_tokens,
        "completion_tokens": output_tokens,
        "total_tokens": input_tokens + output_tokens,
        "archon_loop": True,
        "archon_sessions": sessions,
        "estimated_cost_usd": round(estimated_cost_usd, 9),
    }


PROGRESS_SEED = """# PROGRESS

## Current Stage

prover

## Stages

- prover: active

## Current Objectives
1. **`{objective_file}`** — Complete the single fenced proof body.

## AUTO_NOTES
- Only the public statement, formal goal, and proof requirement are provided.
- ComplexityReduction source files and benchmark solution material are absent.

## Blocked On
(none)
"""
