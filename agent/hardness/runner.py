"""End-to-end deterministic hardness-agent orchestration."""

from __future__ import annotations

import hashlib
import secrets
from dataclasses import dataclass, replace
from pathlib import Path

from .catalog import CATALOG_MODES, FULL_CATALOG, build_all_catalogs
from .authoring import (
    DISABLED_MODE,
    MODEL_MODES,
    MODEL_REQUIRED_MODE,
    NATIVE_MEMBERSHIP_TEMPLATE_KIND,
    PROGRAM_INDEXED_MODEL_TEMPLATE_KIND,
    PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND,
    SUPPORTED_MODES,
    plan_authoring,
    render_deterministic_candidate,
)
from .lean_runner import (
    assert_candidate_source_fences,
    assert_generated_source_is_safe,
    build_artifact_source,
    build_candidate_validation_source,
    build_goal_source,
    build_module_command,
    build_probe_source,
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .model_client import DeepSeekClient, DeepSeekConfig, ModelResponse
from .model_authoring import (
    MODEL_SYSTEM_PROMPT,
    apply_model_patch,
    build_model_authoring_prompt,
    model_stage_for_task,
    parse_model_patch,
    sha256_text,
)
from .models import (
    AgentResult,
    AuthoringAttempt,
    AuthoringStageAttempt,
    AuthoringTaskPacket,
    CommandResult,
    ExactAuthoringTemplateCandidate,
    FailureRecord,
    FamilyInstantiationCandidate,
    HardnessGoal,
    ModelCallRecord,
)
from .planner import choose_route
from .probe import parse_probe_output
from .report import write_report
from .state import JobStore, compute_job_id, load_resume_checkpoint


@dataclass(frozen=True)
class HardnessAgentConfig:
    root: Path
    input_module: str
    source_declaration: str
    objective: str = "reduce_to_known_np"
    membership_declaration: str | None = None
    target_declaration: str | None = None
    planner_mode: str = "deterministic"
    catalog_mode: str = FULL_CATALOG
    output_dir: Path | None = None
    lean_timeout_seconds: int = 300
    deepseek: DeepSeekConfig | None = None
    model_client: object | None = None
    runtime_prebuilt: bool = False
    authoring_mode: str = DISABLED_MODE
    authoring_attempt_budget: int = 1
    authoring_candidate_id: str | None = None
    defer_final_verification: bool = False
    resume: bool = False


@dataclass(frozen=True)
class _RunIdentity:
    input_path: Path
    input_hash: str
    toolchain: str
    manifest_hash: str
    toolchain_hash: str
    job_id: str
    output_dir: Path


def _display(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def _candidate_bundle_sha256(store: JobStore, layout: object) -> str | None:
    source_relatives = tuple(getattr(layout, "source_relatives"))
    paths = tuple(store.path(relative) for relative in source_relatives)
    if any(not path.is_file() for path in paths):
        return None
    hashes = tuple(sha256_file(path) for path in paths)
    if len(hashes) == 1:
        return hashes[0]
    digest = hashlib.sha256()
    for relative, value in zip(source_relatives, hashes, strict=True):
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(value.encode("ascii"))
        digest.update(b"\0")
    return digest.hexdigest()


def _candidate_stage_hashes(store: JobStore, layout: object) -> tuple[str, ...]:
    return tuple(
        sha256_file(store.path(relative))
        for relative in tuple(getattr(layout, "source_relatives"))
    )


def _authoring_prompt_diagnostics(
    *, last_lean_diagnostics: str, diagnostics: list[str]
) -> str:
    """Keep compiler evidence across transient model or protocol failures."""

    if last_lean_diagnostics:
        return last_lean_diagnostics
    return next((value for value in reversed(diagnostics) if value), "")


class HardnessAgent:
    def __init__(self, config: HardnessAgentConfig):
        self.config = config
        self.root = config.root.resolve()
        self.lean_root = self.root / "Lean"

    def _failure(
        self,
        result: AgentResult,
        *,
        store: JobStore,
        status: str,
        phase: str,
        code: str,
        evidence: str,
        retryable: bool = False,
    ) -> AgentResult:
        result.status = status
        result.failures.append(
            FailureRecord(
                phase=phase,
                code=code,
                retryable=retryable,
                evidence=evidence[:4000],
            )
        )
        store.transition(status, details={"phase": phase, "code": code})
        write_report(store, result, root=self.root)
        return result

    def _initial_context(self) -> tuple[Path, str, str, str, str]:
        validate_module_name(self.config.input_module)
        validate_declaration_name(self.config.source_declaration, label="source")
        if self.config.membership_declaration:
            validate_declaration_name(self.config.membership_declaration, label="membership")
        if self.config.target_declaration:
            validate_declaration_name(self.config.target_declaration, label="target")
        if self.config.objective not in {
            "reduce_to",
            "reduce_to_known_np",
            "prove_in_np",
            "prove_np_complete",
        }:
            raise ValueError(f"unsupported objective: {self.config.objective}")
        if self.config.objective == "reduce_to" and not self.config.target_declaration:
            raise ValueError("reduce-to requires --target")
        if self.config.objective in {"prove_in_np", "prove_np_complete"} and (
            self.config.target_declaration is not None
        ):
            raise ValueError(
                "membership and completeness objectives use --source as the exact problem and accept no target"
            )
        if self.config.planner_mode != "deterministic":
            raise ValueError("route planning is deterministic; model route reranking was removed")
        if self.config.catalog_mode not in CATALOG_MODES:
            raise ValueError(f"unsupported typed catalog mode: {self.config.catalog_mode}")
        if self.config.catalog_mode != FULL_CATALOG and self.config.objective != "reduce_to":
            raise ValueError(
                "non-full catalog modes currently require fixed-target reduce-to"
            )
        if self.config.authoring_mode not in SUPPORTED_MODES:
            raise ValueError(f"unsupported authoring mode: {self.config.authoring_mode}")
        if self.config.catalog_mode != FULL_CATALOG and self.config.authoring_mode != DISABLED_MODE:
            raise ValueError("flat/IR catalog experiments must disable capability authoring")
        if self.config.authoring_attempt_budget <= 0:
            raise ValueError("authoring attempt budget must be positive")
        if self.config.authoring_candidate_id is not None:
            candidate_id = self.config.authoring_candidate_id
            if (
                not candidate_id.startswith("sha256:")
                or len(candidate_id) != 71
                or any(character not in "0123456789abcdef" for character in candidate_id[7:])
            ):
                raise ValueError("selected authoring candidate id must be canonical SHA-256")
            if self.config.authoring_mode == DISABLED_MODE:
                raise ValueError("a selected authoring candidate requires authoring to be enabled")
        input_path = module_file(self.lean_root, self.config.input_module)
        toolchain_path = self.lean_root / "lean-toolchain"
        manifest_path = self.lean_root / "lake-manifest.json"
        return (
            input_path,
            sha256_file(input_path),
            toolchain_path.read_text(encoding="utf-8").strip(),
            sha256_file(manifest_path),
            sha256_file(toolchain_path),
        )

    def _run_identity(self) -> _RunIdentity:
        input_path, input_hash, toolchain, manifest_hash, toolchain_hash = self._initial_context()
        job_payload = {
            "schema_major": 1,
            "input_module": self.config.input_module,
            "input_sha256": input_hash,
            "source_declaration": self.config.source_declaration,
            "membership_declaration": self.config.membership_declaration,
            "target_declaration": self.config.target_declaration,
            "objective": self.config.objective,
            "catalog_mode": self.config.catalog_mode,
            "presentation_policy": "exact_user",
            "toolchain_sha256": toolchain_hash,
            "lake_manifest_sha256": manifest_hash,
        }
        job_id = compute_job_id(job_payload)
        output_dir = (
            self.config.output_dir.resolve()
            if self.config.output_dir
            else self.root / ".reduction-agent" / "jobs" / job_id.removeprefix("sha256:")
        )
        return _RunIdentity(
            input_path=input_path,
            input_hash=input_hash,
            toolchain=toolchain,
            manifest_hash=manifest_hash,
            toolchain_hash=toolchain_hash,
            job_id=job_id,
            output_dir=output_dir,
        )

    def run(self) -> AgentResult:
        identity = self._run_identity()
        store = JobStore(identity.output_dir)
        with store.exclusive_run():
            return self._run_locked(identity=identity, store=store)

    def _run_locked(self, *, identity: _RunIdentity, store: JobStore) -> AgentResult:
        input_path = identity.input_path
        input_hash = identity.input_hash
        toolchain = identity.toolchain
        manifest_hash = identity.manifest_hash
        job_id = identity.job_id
        output_dir = identity.output_dir
        resume_checkpoint = (
            load_resume_checkpoint(store, expected_job_id=job_id)
            if self.config.resume
            else None
        )
        goal = HardnessGoal(
            job_id=job_id,
            input_module=self.config.input_module,
            source_declaration=self.config.source_declaration,
            membership_declaration=self.config.membership_declaration,
            target_declaration=self.config.target_declaration,
            objective=self.config.objective,
            toolchain=toolchain,
            input_sha256=input_hash,
            lake_manifest_sha256=manifest_hash,
        )
        result = AgentResult(
            job_id=job_id,
            status="RECEIVED",
            goal=goal,
            output_dir=_display(output_dir, self.root),
            route_policy=self.config.planner_mode,
            catalog_mode=self.config.catalog_mode,
            authoring_policy=self.config.authoring_mode,
            authoring_attempt_budget=self.config.authoring_attempt_budget,
            model_configuration=(
                self.config.deepseek.to_public_dict() if self.config.deepseek else None
            ),
            resume_requested=self.config.resume,
            resumed_from_status=(resume_checkpoint.status if resume_checkpoint else None),
        )
        store.transition("RECEIVED", details={"job_id": job_id})
        store.write_json("goal.json", goal.to_dict())
        goal_path = store.write_text(
            "Goal.lean",
            build_goal_source(
                input_module=self.config.input_module,
                source_declaration=self.config.source_declaration,
                membership_declaration=self.config.membership_declaration,
                target_declaration=self.config.target_declaration,
            ),
        )

        if not self.config.runtime_prebuilt:
            build = run_command(
                build_module_command([self.config.input_module]),
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            result.commands.append(build)
            store.write_json("commands/build-runtime.json", build.to_dict())
            if not build.ok:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="input_gate",
                    code="runtime_build_failed",
                    evidence=build.stderr or build.stdout,
                    retryable=build.timed_out,
                )

        input_gate = run_command(
            ["lake", "env", "lean", str(goal_path)],
            cwd=self.lean_root,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        result.commands.append(input_gate)
        store.write_json("commands/input-gate.json", input_gate.to_dict())
        if not input_gate.ok:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="input_gate",
                code="input_declaration_rejected",
                evidence=input_gate.stderr or input_gate.stdout,
                retryable=input_gate.timed_out,
            )
        store.transition("INPUT_VALIDATED")

        nonce = secrets.token_hex(16)
        probe_source = build_probe_source(
            input_module=self.config.input_module,
            nonce=nonce,
            source_declaration=self.config.source_declaration,
            membership_declaration=self.config.membership_declaration,
            objective=self.config.objective,
            target_declaration=self.config.target_declaration,
            catalog_mode=self.config.catalog_mode,
        )
        probe_path = store.write_text("Probe.lean", probe_source)
        probe_command = run_command(
            ["lake", "env", "lean", str(probe_path)],
            cwd=self.lean_root,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        result.commands.append(probe_command)
        store.write_json("commands/probe.json", probe_command.to_dict())
        if not probe_command.ok:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="probe",
                code="input_or_probe_rejected",
                evidence=probe_command.stderr or probe_command.stdout,
                retryable=probe_command.timed_out,
            )
        try:
            probe = parse_probe_output(
                stdout=probe_command.stdout, stderr=probe_command.stderr, nonce=nonce
            )
        except ValueError as error:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="probe",
                code="probe_protocol_error",
                evidence=str(error),
            )
        result.probe = probe
        store.write_json("capability-snapshot.json", probe.to_dict())
        catalogs = build_all_catalogs(
            probe.inventory_entries,
            registry_fingerprint=probe.registry_fingerprint,
        )
        result.selected_catalog = catalogs[self.config.catalog_mode]
        store.write_json(
            "index/typed-inventory.json",
            {
                "schema_version": "hardness_typed_inventory_v1",
                "registry_fingerprint": probe.registry_fingerprint,
                "entry_count": len(probe.inventory_entries),
                "entries": [entry.to_dict() for entry in probe.inventory_entries],
            },
        )
        for mode, catalog in catalogs.items():
            store.write_json(f"index/catalog-{mode}.json", catalog.to_dict())
        store.write_json("index/selected-catalog.json", result.selected_catalog.to_dict())
        store.transition(
            "CAPABILITIES_SCANNED",
            details={
                "registry_fingerprint": probe.registry_fingerprint,
                "catalog_mode": self.config.catalog_mode,
                "catalog_id": result.selected_catalog.catalog_id,
            },
        )

        if sha256_file(input_path) != input_hash or sha256_file(
            self.lean_root / "lake-manifest.json"
        ) != manifest_hash:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="probe",
                code="stale_snapshot",
                evidence="input module or Lake manifest changed after the capability scan",
                retryable=True,
            )

        client = self.config.model_client
        if client is None and self.config.authoring_mode in MODEL_MODES and self.config.deepseek:
            client = DeepSeekClient(self.config.deepseek)
        client_ready = client is not None and (
            self.config.model_client is not None
            or bool(getattr(getattr(client, "config", None), "api_key", ""))
        )
        plan = choose_route(
            routes=probe.routes,
            mode="deterministic",
            target_declaration=self.config.target_declaration,
        )
        result.planner = plan.decision
        selected_route = plan.route
        active_probe = probe
        active_probe_path = probe_path
        candidate_imports: tuple[str, ...] = ()
        command_environment: dict[str, str] | None = None
        accepted_candidate_paths: tuple[Path, ...] = ()
        if selected_route is None:
            if not probe.gaps:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="gap_classification",
                    code="missing_lean_gap_record",
                    evidence=(
                        "Lean reported no validated route but emitted no typed gap for the "
                        "current exact request"
                    ),
                )
            gap = probe.gaps[0]
            gap_revalidation = run_command(
                ["lake", "env", "lean", str(probe_path)],
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            result.commands.append(gap_revalidation)
            store.write_json("commands/gap-revalidation.json", gap_revalidation.to_dict())
            if not gap_revalidation.ok:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="gap_revalidation",
                    code="gap_revalidation_failed",
                    evidence=gap_revalidation.stderr or gap_revalidation.stdout,
                    retryable=gap_revalidation.timed_out,
                )
            try:
                revalidated_probe = parse_probe_output(
                    stdout=gap_revalidation.stdout,
                    stderr=gap_revalidation.stderr,
                    nonce=nonce,
                )
            except ValueError as error:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="gap_revalidation",
                    code="probe_protocol_error",
                    evidence=str(error),
                )
            revalidated_gap_ids = {candidate.gap_id for candidate in revalidated_probe.gaps}
            if (
                revalidated_probe.registry_fingerprint != probe.registry_fingerprint
                or gap.gap_id not in revalidated_gap_ids
            ):
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="gap_revalidation",
                    code="stale_snapshot",
                    evidence="registry fingerprint or typed gap changed after planning",
                    retryable=True,
                )
            result.gap = gap
            store.write_json("gap.json", gap.to_dict())
            authoring_plan = plan_authoring(
                gap=gap,
                probe=revalidated_probe,
                job_id=job_id,
                input_module=self.config.input_module,
                attempt_budget=self.config.authoring_attempt_budget,
                mode=self.config.authoring_mode,
                model_available=(
                    self.config.authoring_mode == MODEL_REQUIRED_MODE
                    or client_ready
                ),
            )
            if self.config.authoring_candidate_id is not None:
                if authoring_plan is None:
                    return self._failure(
                        result,
                        store=store,
                        status="FAILED",
                        phase="gap_planning",
                        code="selected_authoring_candidate_unavailable",
                        evidence="the selected typed packet has no matching authoring plan",
                    )
                selected_candidates = tuple(
                    candidate
                    for candidate in authoring_plan.candidates
                    if candidate.candidate_id == self.config.authoring_candidate_id
                )
                if len(selected_candidates) != 1:
                    return self._failure(
                        result,
                        store=store,
                        status="FAILED",
                        phase="gap_planning",
                        code="selected_authoring_candidate_unavailable",
                        evidence=(
                            "the selected typed packet candidate is absent or ambiguous in "
                            "the fresh Lean-matched authoring observations"
                        ),
                    )
                authoring_plan = replace(authoring_plan, candidates=selected_candidates)
            task = (
                authoring_plan.task
                if authoring_plan is not None
                else AuthoringTaskPacket.from_gap(gap)
            )
            result.authoring_task = task
            store.write_json("authoring-task.json", task.to_dict())
            store.transition("PLAN_SELECTED", details={"gap_id": gap.gap_id})
            blocker_evidence = (
                f"Lean classified {gap.reason} at "
                f"{gap.source_declaration} -> {gap.target_declaration}; "
                f"expected {gap.expected_capability_head}"
            )
            if (
                resume_checkpoint is not None
                and resume_checkpoint.status == "VERIFIED"
                and resume_checkpoint.authored_candidate_sha256 is not None
            ):
                if authoring_plan is None:
                    candidate_integrity = "unavailable"
                    actual_candidate_sha256 = None
                else:
                    actual_candidate_sha256 = _candidate_bundle_sha256(
                        store, authoring_plan.layout
                    )
                    if actual_candidate_sha256 is None:
                        candidate_integrity = "missing"
                    else:
                        candidate_integrity = (
                            "intact"
                            if actual_candidate_sha256
                            == resume_checkpoint.authored_candidate_sha256
                            else "changed"
                        )
                result.resume_candidate_integrity = candidate_integrity
                store.write_json(
                    "resume.json",
                    {
                        "schema_version": "hardness_resume_audit_v1",
                        "resumed_from_status": resume_checkpoint.status,
                        "candidate_integrity": candidate_integrity,
                        "expected_candidate_sha256": (
                            resume_checkpoint.authored_candidate_sha256
                        ),
                        "actual_candidate_sha256": actual_candidate_sha256,
                        "current_gap_id": gap.gap_id,
                    },
                )
                if candidate_integrity != "intact":
                    return self._failure(
                        result,
                        store=store,
                        status="BLOCKED",
                        phase="resume",
                        code=gap.failure_code,
                        evidence=(
                            f"previous VERIFIED job-local candidate is {candidate_integrity}; "
                            "the current Lean environment re-established the exact typed blocker "
                            "and resume will not silently re-author or reuse stale compiled output"
                        ),
                    )
            if (
                self.config.authoring_mode == DISABLED_MODE
                or authoring_plan is None
                or not authoring_plan.candidates
            ):
                if self.config.authoring_mode != DISABLED_MODE:
                    blocker_evidence += (
                        "; no Lean-matched safe authoring skeleton is available"
                    )
                return self._failure(
                    result,
                    store=store,
                    status="BLOCKED",
                    phase="gap_planning",
                    code=gap.failure_code,
                    evidence=blocker_evidence,
                )
            if self.config.authoring_mode == MODEL_REQUIRED_MODE and (
                not client_ready
            ):
                return self._failure(
                    result,
                    store=store,
                    status="BLOCKED",
                    phase="authoring",
                    code="required_model_unavailable",
                    evidence=(
                        f"{blocker_evidence}; model-required authoring has no configured "
                        "DEEPSEEK_API_KEY"
                    ),
                )

            store.transition("AUTHORING", details={"task_id": task.task_id})
            work_root = store.path("work")
            work_root.mkdir(parents=True, exist_ok=True)
            command_environment = {"LEAN_PATH": str(work_root)}
            diagnostics: list[str] = []
            last_lean_diagnostics = ""
            reusable_prefix_hashes: dict[str, str] = {}
            model_mode = self.config.authoring_mode in MODEL_MODES
            model_target_stage = model_stage_for_task(task) if model_mode else None
            if model_mode and model_target_stage is None:
                return self._failure(
                    result,
                    store=store,
                    status="BLOCKED",
                    phase="gap_planning",
                    code=gap.failure_code,
                    evidence=(
                        f"{blocker_evidence}; the typed gap has no fenced model-editable stage"
                    ),
                )
            if model_mode:
                deterministic_candidate = authoring_plan.candidates[0]
                attempt_candidates = (deterministic_candidate,) * (
                    self.config.authoring_attempt_budget
                )
            else:
                attempt_candidates = authoring_plan.candidates[
                    : self.config.authoring_attempt_budget
                ]
            public_context = ""
            if model_mode:
                context_paths: list[Path] = [input_path]
                context_declarations = [gap.source_declaration, gap.target_declaration]
                first_candidate = authoring_plan.candidates[0]
                if isinstance(first_candidate, ExactAuthoringTemplateCandidate):
                    context_declarations.extend(first_candidate.component_declarations)
                for declaration in context_declarations:
                    if "." not in declaration:
                        continue
                    candidate_module = declaration.rsplit(".", 1)[0]
                    try:
                        candidate_path = module_file(self.lean_root, candidate_module)
                    except ValueError:
                        continue
                    if candidate_path not in context_paths:
                        context_paths.append(candidate_path)
                public_context = "\n\n".join(
                    f"PUBLIC_FILE {path.relative_to(self.lean_root / 'Reference')}\n"
                    + path.read_text(encoding="utf-8")
                    for path in context_paths
                )
            for attempt_number, authoring_candidate in enumerate(
                attempt_candidates, start=1
            ):
                attempt_model_calls: list[int] = []
                attempt_source_origin = "deterministic_fixture"
                protocol_rejection: str | None = None
                family_candidate = (
                    authoring_candidate
                    if isinstance(authoring_candidate, FamilyInstantiationCandidate)
                    else None
                )
                template_candidate = (
                    authoring_candidate
                    if isinstance(authoring_candidate, ExactAuthoringTemplateCandidate)
                    else None
                )
                try:
                    rendered_stages = render_deterministic_candidate(
                        plan=authoring_plan,
                        authoring_candidate=authoring_candidate,
                        input_module=self.config.input_module,
                        gap=gap,
                    )
                    boundaries = {boundary.stage: boundary for boundary in task.stage_boundaries}
                    if boundaries and set(boundaries) != {
                        stage.layout.stage for stage in rendered_stages
                    }:
                        raise ValueError("candidate stages changed after task creation")
                    for stage in rendered_stages:
                        if stage.layout.source_relative not in task.editable_files:
                            raise ValueError(
                                f"{stage.layout.stage} file is outside the task editable-file allowlist"
                            )
                        boundary = boundaries.get(stage.layout.stage)
                        if boundary is not None and (
                            stage.candidate.fixed_header_sha256
                            != boundary.fixed_header_sha256
                            or stage.candidate.fixed_footer_sha256
                            != boundary.fixed_footer_sha256
                            or stage.layout.module != boundary.module
                            or stage.layout.declaration != boundary.declaration
                        ):
                            raise ValueError(
                                f"{stage.layout.stage} skeleton fence changed after task creation"
                            )
                        assert_generated_source_is_safe(stage.candidate.source)
                    final_candidate = rendered_stages[-1].candidate
                    if not boundaries and (
                        final_candidate.fixed_header_sha256 != task.fixed_header_sha256
                        or final_candidate.fixed_footer_sha256 != task.fixed_footer_sha256
                    ):
                        raise ValueError("candidate skeleton fence hash changed after task creation")
                except ValueError as error:
                    return self._failure(
                        result,
                        store=store,
                        status="FAILED",
                        phase="authoring",
                        code="invalid_authoring_template",
                        evidence=str(error),
                    )

                if model_mode and client is not None:
                    target_stage = next(
                        (
                            stage
                            for stage in rendered_stages
                            if stage.layout.stage == model_target_stage
                        ),
                        None,
                    )
                    if target_stage is None:
                        return self._failure(
                            result,
                            store=store,
                            status="FAILED",
                            phase="authoring",
                            code="invalid_authoring_template",
                            evidence=(
                                f"model-editable stage {model_target_stage!r} is absent from "
                                "the deterministic task skeleton"
                            ),
                        )
                    boundary = boundaries.get(target_stage.layout.stage)
                    prompt_diagnostics = _authoring_prompt_diagnostics(
                        last_lean_diagnostics=last_lean_diagnostics,
                        diagnostics=diagnostics,
                    )
                    prompt = build_model_authoring_prompt(
                        task=task,
                        boundary=boundary,
                        stage=target_stage.layout.stage,
                        editable_file=target_stage.layout.source_relative,
                        current_body=target_stage.candidate.editable_body,
                        diagnostics=prompt_diagnostics,
                        public_context=public_context,
                        remaining_calls=(
                            self.config.authoring_attempt_budget - attempt_number + 1
                        ),
                        fixed_header=target_stage.candidate.fixed_header,
                        fixed_footer=target_stage.candidate.fixed_footer,
                    )
                    if (
                        client.config.api_key
                        and client.config.api_key in prompt
                    ):
                        return self._failure(
                            result,
                            store=store,
                            status="FAILED",
                            phase="authoring",
                            code="secret_in_model_prompt",
                            evidence="the generated model prompt contained the configured API key",
                        )
                    call_number = len(result.model_calls) + 1
                    prompt_path = store.write_text(
                        f"model/call-{call_number:02d}-prompt.txt", prompt
                    )
                    try:
                        response = client.complete_json(
                            system=MODEL_SYSTEM_PROMPT,
                            prompt=prompt,
                        )
                    except Exception as error:
                        response = ModelResponse(
                            called=True,
                            ok=False,
                            content="",
                            error=client.config.redact(
                                f"model client raised {type(error).__name__}: {error}"
                            ),
                            status_code=None,
                            duration_seconds=0.0,
                            usage=None,
                            attempts=1,
                        )
                    response_content = response.content
                    secret_echoed = bool(
                        client.config.api_key
                        and client.config.api_key in response_content
                    )
                    audited_response_content = (
                        response_content.replace(client.config.api_key, "[REDACTED]")
                        if secret_echoed and client.config.api_key
                        else response_content
                    )
                    response_path = store.write_json(
                        f"model/call-{call_number:02d}-response.json",
                        {
                            "schema_version": "hardness_model_raw_response_v1",
                            "called": response.called,
                            "ok": response.ok,
                            "content": audited_response_content,
                            "error": response.error,
                            "status_code": response.status_code,
                            "finish_reason": response.finish_reason,
                            "duration_seconds": response.duration_seconds,
                            "usage": response.usage,
                            "attempts": response.attempts,
                        },
                    )
                    patch = None
                    patch_error = (
                        "model response contained the configured API key"
                        if secret_echoed
                        else response.error
                    )
                    patch_path: Path | None = None
                    if response.ok and not secret_echoed:
                        try:
                            patch = parse_model_patch(
                                response.content,
                                task=task,
                                stage=target_stage.layout.stage,
                                editable_file=target_stage.layout.source_relative,
                            )
                            patch_path = store.write_json(
                                f"model/call-{call_number:02d}-patch.json",
                                patch.to_dict(),
                            )
                            rendered_stages = tuple(
                                replace(
                                    stage,
                                    candidate=apply_model_patch(stage.candidate, patch),
                                )
                                if stage.layout.stage == target_stage.layout.stage
                                else stage
                                for stage in rendered_stages
                            )
                            attempt_source_origin = "model_generated"
                            patch_error = None
                        except ValueError as error:
                            patch_error = str(error)
                    result.model_calls.append(
                        ModelCallRecord(
                            call=call_number,
                            task_id=task.task_id,
                            stage=target_stage.layout.stage,
                            editable_file=target_stage.layout.source_relative,
                            model=client.config.model,
                            base_url=client.config.public_base_url,
                            called=response.called,
                            ok=response.ok,
                            protocol_accepted=patch is not None,
                            prompt_sha256=sha256_text(prompt),
                            response_sha256=sha256_text(response_content),
                            duration_seconds=response.duration_seconds,
                            http_attempts=response.attempts,
                            status_code=response.status_code,
                            finish_reason=response.finish_reason,
                            usage=response.usage,
                            error=patch_error,
                            diagnostics_sha256=(
                                sha256_text(prompt_diagnostics)
                                if prompt_diagnostics
                                else None
                            ),
                            patch_sha256=(patch.patch_sha256 if patch else None),
                            prompt_file=_display(prompt_path, self.root),
                            response_file=_display(response_path, self.root),
                            patch_file=(
                                _display(patch_path, self.root) if patch_path else None
                            ),
                        )
                    )
                    attempt_model_calls.append(call_number)
                    if patch is None:
                        diagnostics.append(patch_error or "model authoring request failed")
                        if self.config.authoring_mode == MODEL_REQUIRED_MODE:
                            if (
                                not response.called
                                or response.status_code is None
                                or response.status_code >= 400
                            ):
                                return self._failure(
                                    result,
                                    store=store,
                                    status="BLOCKED",
                                    phase="authoring",
                                    code="required_model_unavailable",
                                    evidence=(
                                        f"{blocker_evidence}; "
                                        f"{patch_error or 'DeepSeek request failed'}"
                                    ),
                                    retryable=True,
                                )
                            protocol_rejection = patch_error or (
                                "model response violated the patch protocol"
                            )

                model_target_position = next(
                    (
                        index
                        for index, stage in enumerate(rendered_stages)
                        if stage.layout.stage == model_target_stage
                    ),
                    -1,
                )
                reusable_prefix_stages = {
                    stage.layout.stage
                    for stage in rendered_stages[:model_target_position]
                }
                for stage_layout in authoring_plan.layout.all_stages:
                    can_keep_checkpoint = (
                        model_mode
                        and attempt_number > 1
                        and stage_layout.stage in reusable_prefix_stages
                        and stage_layout.stage in reusable_prefix_hashes
                    )
                    if not can_keep_checkpoint:
                        store.path(stage_layout.source_relative).unlink(missing_ok=True)
                        olean_path = store.path(stage_layout.olean_relative)
                        olean_path.parent.mkdir(parents=True, exist_ok=True)
                        olean_path.unlink(missing_ok=True)

                if protocol_rejection is not None:
                    rejected_stage = next(
                        stage
                        for stage in rendered_stages
                        if stage.layout.stage == model_target_stage
                    )
                    protocol_command = CommandResult(
                        command=("deepseek", "authoring-patch-protocol"),
                        exit_code=1,
                        stdout="",
                        stderr=protocol_rejection,
                        duration_seconds=0.0,
                    )
                    attempt = AuthoringAttempt(
                        attempt=attempt_number,
                        family_candidate=family_candidate,
                        template_candidate=template_candidate,
                        candidate_module=authoring_plan.layout.module,
                        candidate_declaration=authoring_plan.layout.declaration,
                        route_declaration=authoring_plan.layout.route_declaration,
                        primary_capability_head=authoring_plan.primary_capability_head,
                        candidate_file=_display(
                            store.path(rejected_stage.layout.source_relative), self.root
                        ),
                        candidate_sha256="",
                        fixed_header_sha256=(
                            rejected_stage.candidate.fixed_header_sha256
                        ),
                        fixed_footer_sha256=(
                            rejected_stage.candidate.fixed_footer_sha256
                        ),
                        compile_command=protocol_command,
                        source_origin="model_rejected",
                        model_call_numbers=tuple(attempt_model_calls),
                    )
                    result.authoring_attempts.append(attempt)
                    store.write_json(
                        f"attempts/{attempt_number:02d}.json", attempt.to_dict()
                    )
                    continue

                stage_attempts: list[AuthoringStageAttempt] = []
                written_paths: list[Path] = []
                stage_failure = False
                for stage_index, stage in enumerate(rendered_stages, start=1):
                    candidate_path = store.path(stage.layout.source_relative)
                    olean_path = store.path(stage.layout.olean_relative)
                    expected_stage_sha256 = sha256_text(stage.candidate.source)
                    checkpoint_reused = bool(
                        model_mode
                        and attempt_number > 1
                        and stage.layout.stage in reusable_prefix_stages
                        and reusable_prefix_hashes.get(stage.layout.stage)
                        == expected_stage_sha256
                        and candidate_path.is_file()
                        and olean_path.is_file()
                    )
                    if checkpoint_reused:
                        try:
                            checkpoint_reused = (
                                sha256_file(candidate_path) == expected_stage_sha256
                            )
                        except OSError:
                            checkpoint_reused = False
                    if not checkpoint_reused:
                        candidate_path = store.write_text(
                            stage.layout.source_relative, stage.candidate.source
                        )
                    written_paths.append(candidate_path)
                    try:
                        actual_candidate_source = candidate_path.read_text(encoding="utf-8")
                        assert_candidate_source_fences(actual_candidate_source, stage.candidate)
                        assert_generated_source_is_safe(actual_candidate_source)
                    except (OSError, UnicodeError, ValueError) as error:
                        return self._failure(
                            result,
                            store=store,
                            status="FAILED",
                            phase="authoring",
                            code="candidate_boundary_violation",
                            evidence=str(error),
                        )
                    stage_sha256 = sha256_file(candidate_path)
                    if checkpoint_reused:
                        compile_command = CommandResult(
                            command=(
                                "reuse-content-addressed-authoring-checkpoint",
                                stage.layout.stage,
                            ),
                            exit_code=0,
                            stdout=(
                                "reused an unchanged prefix checkpoint compiled earlier "
                                "in this locked authoring job"
                            ),
                            stderr="",
                            duration_seconds=0.0,
                        )
                    else:
                        compile_command = run_command(
                            [
                                "lake",
                                "env",
                                "lean",
                                "-R",
                                str(work_root),
                                "-o",
                                str(olean_path),
                                str(candidate_path),
                            ],
                            cwd=self.lean_root,
                            timeout_seconds=self.config.lean_timeout_seconds,
                            env_overrides=command_environment,
                        )
                    result.commands.append(compile_command)
                    store.write_json(
                        f"commands/authoring-attempt-{attempt_number}-{stage.layout.stage}-compile.json",
                        compile_command.to_dict(),
                    )
                    source_unchanged = sha256_file(candidate_path) == stage_sha256
                    if not source_unchanged:
                        return self._failure(
                            result,
                            store=store,
                            status="FAILED",
                            phase="authoring",
                            code="candidate_changed_during_compile",
                            evidence=(
                                f"{stage.layout.stage} source hash changed during Lean compilation"
                            ),
                            retryable=True,
                        )
                    stage_accepted = compile_command.ok and olean_path.is_file()
                    stage_attempt = AuthoringStageAttempt(
                        stage=stage.layout.stage,
                        module=stage.layout.module,
                        declaration=stage.layout.declaration,
                        candidate_file=_display(candidate_path, self.root),
                        candidate_sha256=stage_sha256,
                        fixed_header_sha256=stage.candidate.fixed_header_sha256,
                        fixed_footer_sha256=stage.candidate.fixed_footer_sha256,
                        compile_command=compile_command,
                        accepted=stage_accepted,
                        source_origin=(
                            attempt_source_origin
                            if stage.layout.stage == model_target_stage
                            else "deterministic_fixture"
                        ),
                        checkpoint_reused=checkpoint_reused,
                    )
                    stage_attempts.append(stage_attempt)
                    store.write_json(
                        f"checkpoints/attempt-{attempt_number:02d}/{stage_index:02d}-{stage.layout.stage}.json",
                        stage_attempt.to_dict(),
                    )
                    if not stage_accepted:
                        stage_failure = True
                        last_lean_diagnostics = (
                            compile_command.stderr or compile_command.stdout
                        )
                        diagnostics.append(last_lean_diagnostics)
                        break
                    if stage.layout.stage in reusable_prefix_stages:
                        reusable_prefix_hashes[stage.layout.stage] = stage_sha256

                if stage_failure:
                    last_stage = stage_attempts[-1]
                    attempt = AuthoringAttempt(
                        attempt=attempt_number,
                        family_candidate=family_candidate,
                        template_candidate=template_candidate,
                        candidate_module=authoring_plan.layout.module,
                        candidate_declaration=authoring_plan.layout.declaration,
                        route_declaration=authoring_plan.layout.route_declaration,
                        primary_capability_head=authoring_plan.primary_capability_head,
                        candidate_file=last_stage.candidate_file,
                        candidate_sha256=last_stage.candidate_sha256,
                        fixed_header_sha256=last_stage.fixed_header_sha256,
                        fixed_footer_sha256=last_stage.fixed_footer_sha256,
                        compile_command=last_stage.compile_command,
                        stage_attempts=tuple(stage_attempts),
                        source_origin=attempt_source_origin,
                        model_call_numbers=tuple(attempt_model_calls),
                    )
                    result.authoring_attempts.append(attempt)
                    store.write_json(f"attempts/{attempt_number:02d}.json", attempt.to_dict())
                    continue

                candidate_sha256 = _candidate_bundle_sha256(store, authoring_plan.layout)
                if candidate_sha256 is None:
                    return self._failure(
                        result,
                        store=store,
                        status="FAILED",
                        phase="authoring",
                        code="candidate_bundle_incomplete",
                        evidence="one or more staged candidate sources disappeared after compilation",
                        retryable=True,
                    )

                validation_source = build_candidate_validation_source(
                    candidate_module=authoring_plan.layout.module,
                    nonce=nonce,
                    candidate_declaration=authoring_plan.layout.declaration,
                    route_declaration=authoring_plan.layout.route_declaration,
                    template_kind=task.template_kind,
                    stage_declarations=(
                        {stage.layout.stage: stage.layout.declaration for stage in rendered_stages}
                        if task.template_kind
                        in {
                            PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND,
                            PROGRAM_INDEXED_MODEL_TEMPLATE_KIND,
                            NATIVE_MEMBERSHIP_TEMPLATE_KIND,
                        }
                        else None
                    ),
                    source_declaration=gap.source_declaration,
                    target_declaration=gap.target_declaration,
                )
                validation_path = store.write_text(
                    authoring_plan.layout.validation_relative, validation_source
                )
                validation_command = run_command(
                    ["lake", "env", "lean", str(validation_path)],
                    cwd=self.lean_root,
                    timeout_seconds=self.config.lean_timeout_seconds,
                    env_overrides=command_environment,
                )
                result.commands.append(validation_command)
                store.write_json(
                    f"commands/authoring-attempt-{attempt_number}-validation.json",
                    validation_command.to_dict(),
                )
                accepted = (
                    validation_command.ok
                    and _candidate_bundle_sha256(store, authoring_plan.layout)
                    == candidate_sha256
                )
                final_stage = stage_attempts[-1]
                attempt = AuthoringAttempt(
                    attempt=attempt_number,
                    family_candidate=family_candidate,
                    template_candidate=template_candidate,
                    candidate_module=authoring_plan.layout.module,
                    candidate_declaration=authoring_plan.layout.declaration,
                    route_declaration=authoring_plan.layout.route_declaration,
                    primary_capability_head=authoring_plan.primary_capability_head,
                    candidate_file=final_stage.candidate_file,
                    candidate_sha256=candidate_sha256,
                    fixed_header_sha256=final_stage.fixed_header_sha256,
                    fixed_footer_sha256=final_stage.fixed_footer_sha256,
                    compile_command=final_stage.compile_command,
                    validation_command=validation_command,
                    accepted=accepted,
                    stage_attempts=tuple(stage_attempts),
                    source_origin=attempt_source_origin,
                    model_call_numbers=tuple(attempt_model_calls),
                )
                result.authoring_attempts.append(attempt)
                store.write_json(f"attempts/{attempt_number:02d}.json", attempt.to_dict())
                if not accepted:
                    last_lean_diagnostics = (
                        validation_command.stderr or validation_command.stdout
                    )
                    diagnostics.append(last_lean_diagnostics)
                    continue
                accepted_candidate_paths = tuple(written_paths)
                candidate_imports = (authoring_plan.layout.module,)
                result.authored_candidate_module = authoring_plan.layout.module
                result.authored_candidate_declaration = authoring_plan.layout.declaration
                result.authored_route_declaration = authoring_plan.layout.route_declaration
                result.authored_capability_head = authoring_plan.primary_capability_head
                result.authored_source_origin = attempt_source_origin
                result.authored_candidate_file = _display(written_paths[-1], self.root)
                result.authored_candidate_sha256 = candidate_sha256
                result.authored_stage_files = tuple(
                    _display(path, self.root) for path in written_paths
                )
                result.authored_stage_sha256 = _candidate_stage_hashes(
                    store, authoring_plan.layout
                )
                store.transition(
                    "CANDIDATE_COMPILED",
                    details={
                        "candidate": authoring_plan.layout.declaration,
                        "candidate_sha256": candidate_sha256,
                    },
                )
                break

            if not accepted_candidate_paths:
                diagnostic_summary = _authoring_prompt_diagnostics(
                    last_lean_diagnostics=last_lean_diagnostics,
                    diagnostics=diagnostics,
                )
                if not diagnostic_summary:
                    diagnostic_summary = "authoring exhausted its bounded attempts"
                exhausted_model_budget = model_mode and bool(result.model_calls) and (
                    self.config.authoring_mode == MODEL_REQUIRED_MODE
                    or any(call.protocol_accepted for call in result.model_calls)
                )
                return self._failure(
                    result,
                    store=store,
                    status="BLOCKED",
                    phase="authoring",
                    code=(
                        "authoring_budget_exhausted"
                        if exhausted_model_budget
                        else gap.failure_code
                    ),
                    evidence=f"{blocker_evidence}; {diagnostic_summary}",
                )

            post_probe_source = build_probe_source(
                input_module=self.config.input_module,
                nonce=nonce,
                source_declaration=self.config.source_declaration,
                membership_declaration=self.config.membership_declaration,
                objective=self.config.objective,
                target_declaration=self.config.target_declaration,
                catalog_mode=self.config.catalog_mode,
                extra_imports=candidate_imports,
            )
            active_probe_path = store.write_text(
                authoring_plan.layout.post_probe_relative, post_probe_source
            )
            post_probe_command = run_command(
                ["lake", "env", "lean", str(active_probe_path)],
                cwd=self.lean_root,
                timeout_seconds=self.config.lean_timeout_seconds,
                env_overrides=command_environment,
            )
            result.commands.append(post_probe_command)
            store.write_json("commands/post-authoring-probe.json", post_probe_command.to_dict())
            if not post_probe_command.ok:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="post_authoring_probe",
                    code="candidate_probe_rejected",
                    evidence=post_probe_command.stderr or post_probe_command.stdout,
                    retryable=post_probe_command.timed_out,
                )
            try:
                active_probe = parse_probe_output(
                    stdout=post_probe_command.stdout,
                    stderr=post_probe_command.stderr,
                    nonce=nonce,
                )
            except ValueError as error:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="post_authoring_probe",
                    code="probe_protocol_error",
                    evidence=str(error),
                )
            result.post_authoring_probe = active_probe
            store.write_json("post-authoring-capability-snapshot.json", active_probe.to_dict())
            authored_plan = choose_route(
                routes=active_probe.routes,
                mode="deterministic",
                target_declaration=self.config.target_declaration,
            )
            if authored_plan.route is None:
                return self._failure(
                    result,
                    store=store,
                    status="FAILED",
                    phase="post_authoring_probe",
                    code="validated_candidate_not_resolved",
                    evidence="canonical candidate validation passed but no exact route was discovered",
                )
            selected_route = authored_plan.route
            result.planner = authored_plan.decision

        assert selected_route is not None
        result.selected_route = selected_route
        store.write_json("route.json", selected_route.to_dict())
        store.transition("PLAN_SELECTED", details={"route_id": selected_route.route_id})

        if accepted_candidate_paths and (
            _candidate_bundle_sha256(store, authoring_plan.layout)
            != result.authored_candidate_sha256
        ):
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="registry_revalidation",
                code="candidate_changed_after_validation",
                evidence="job-local candidate source changed after canonical validation",
                retryable=True,
            )
        revalidation = run_command(
            ["lake", "env", "lean", str(active_probe_path)],
            cwd=self.lean_root,
            timeout_seconds=self.config.lean_timeout_seconds,
            env_overrides=command_environment,
        )
        result.commands.append(revalidation)
        store.write_json("commands/registry-revalidation.json", revalidation.to_dict())
        if not revalidation.ok:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="registry_revalidation",
                code="registry_revalidation_failed",
                evidence=revalidation.stderr or revalidation.stdout,
                retryable=revalidation.timed_out,
            )
        try:
            revalidated_probe = parse_probe_output(
                stdout=revalidation.stdout, stderr=revalidation.stderr, nonce=nonce
            )
        except ValueError as error:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="registry_revalidation",
                code="probe_protocol_error",
                evidence=str(error),
            )
        revalidated_route_ids = {route.route_id for route in revalidated_probe.routes}
        if (
            revalidated_probe.registry_fingerprint != active_probe.registry_fingerprint
            or selected_route.route_id not in revalidated_route_ids
        ):
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="registry_revalidation",
                code="stale_snapshot",
                evidence="registry fingerprint or selected route changed after planning",
                retryable=True,
            )
        store.transition(
            "REGISTRY_REVALIDATED",
            details={"registry_fingerprint": revalidated_probe.registry_fingerprint},
        )

        artifact_source = build_artifact_source(
            input_module=self.config.input_module,
            source_declaration=self.config.source_declaration,
            membership_declaration=self.config.membership_declaration,
            objective=self.config.objective,
            route=selected_route,
            extra_imports=candidate_imports,
        )
        try:
            assert_generated_source_is_safe(artifact_source)
        except ValueError as error:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="artifact",
                code="forbidden_generated_source",
                evidence=str(error),
            )
        artifact_path = store.write_text("Artifact.lean", artifact_source)
        result.artifact_file = _display(artifact_path, self.root)
        if accepted_candidate_paths and (
            _candidate_bundle_sha256(store, authoring_plan.layout)
            != result.authored_candidate_sha256
        ):
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="artifact",
                code="candidate_changed_before_final_resolution",
                evidence="job-local candidate source changed before final resolution",
                retryable=True,
            )
        if self.config.defer_final_verification:
            result.artifact_sha256 = sha256_file(artifact_path)
            result.status = "REGISTRY_REVALIDATED"
            write_report(store, result, root=self.root)
            return result
        artifact_command = run_command(
            ["lake", "env", "lean", str(artifact_path)],
            cwd=self.lean_root,
            timeout_seconds=self.config.lean_timeout_seconds,
            env_overrides=command_environment,
        )
        result.commands.append(artifact_command)
        store.write_json("commands/artifact.json", artifact_command.to_dict())
        if not artifact_command.ok:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="final_resolution",
                code="artifact_rejected",
                evidence=artifact_command.stderr or artifact_command.stdout,
                retryable=artifact_command.timed_out,
            )
        store.transition("FINAL_RESOLVED")
        store.transition("AXIOM_AUDITED")

        if accepted_candidate_paths and (
            _candidate_bundle_sha256(store, authoring_plan.layout)
            != result.authored_candidate_sha256
        ):
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="replay",
                code="candidate_changed_before_replay",
                evidence="job-local candidate source changed before deterministic replay",
                retryable=True,
            )
        replay = run_command(
            ["lake", "env", "lean", str(artifact_path)],
            cwd=self.lean_root,
            timeout_seconds=self.config.lean_timeout_seconds,
            env_overrides=command_environment,
        )
        result.commands.append(replay)
        store.write_json("commands/deterministic-replay.json", replay.to_dict())
        if not replay.ok:
            return self._failure(
                result,
                store=store,
                status="FAILED",
                phase="replay",
                code="deterministic_replay_failed",
                evidence=replay.stderr or replay.stdout,
                retryable=replay.timed_out,
            )
        result.artifact_sha256 = sha256_file(artifact_path)
        result.status = "VERIFIED"
        store.transition(
            "VERIFIED",
            details={
                "artifact_sha256": result.artifact_sha256,
                "registry_fingerprint": active_probe.registry_fingerprint,
            },
        )
        write_report(store, result, root=self.root)
        return result
