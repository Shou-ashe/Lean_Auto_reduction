"""General NP-hard-first orchestrator with typed reuse and open synthesis hooks."""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict, dataclass
import secrets
from pathlib import Path
from typing import Any, Mapping, Sequence

from agent.hardness.lean_runner import (
    build_module_command,
    run_command,
    sha256_file,
    validate_declaration_name,
)
from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig
from agent.hardness.np_hard import build_np_hard_probe_source, parse_np_hard_probe_output
from agent.hardness.np_hard_input import (
    NPHardInputError,
    certify_np_hard_input,
    resolve_np_hard_input_reference,
)

from .baseline import verify_stable_entrypoints
from .budgets import BudgetExhausted, BudgetTracker, SearchBudget
from .capability_planner import CapabilityPlanner
from .exact_closure_probe import ClosureCheck
from .job import GeneralJobStore
from .lean_bridge import run_lean_file, snapshot_environment
from .model import propose_implementation, propose_strategy
from .models import (
    ActionDisposition,
    GeneralNPHardRequest,
    GeneralNPHardResult,
    GenerationEvidence,
    ModelCallRecord,
    ModelPolicy,
    ProofStatus,
    ProofStep,
    ProviderKind,
    ProviderStatistics,
    QualificationStatus,
    RootGoal,
    SolutionClassification,
    Strategy,
    TheoremIndexEntry,
    stable_sha256,
)
from .plugins import install_plugins
from .premise_registry import PremiseSolution, default_registry
from .profiles import get_profile
from .proof_state import ProofState
from .reconstruction import (
    build_authored_artifact_source,
    build_resolver_artifact_source,
    build_theorem_artifact_source,
)
from .reporting import write_result
from .theorem_index import project_module_catalog, query_theorem_index
from .verification import (
    classify_generation,
    evidence_from_generated_source,
    initial_qualification_status,
    verify_core_artifact,
)


@dataclass(frozen=True)
class GenerativeReductionConfig:
    root: Path
    input_module: str
    problem_declaration: str
    output_dir: Path
    strategy: Strategy = Strategy.REUSE_FIRST
    profile: str = "research"
    model_policy: ModelPolicy = ModelPolicy.AUTO
    plugins: tuple[str, ...] = ()
    forbidden_declarations: tuple[str, ...] = ()
    budget: SearchBudget = SearchBudget()
    lean_timeout_seconds: int = 600
    deepseek: DeepSeekConfig | None = None
    runtime_prebuilt: bool = False


class GenerativeReductionOrchestrator:
    def __init__(self, config: GenerativeReductionConfig):
        self.config = config
        self.root = config.root.resolve()
        self.output_dir = config.output_dir.resolve()
        self.profile = get_profile(config.profile)
        config.budget.validate()
        if config.lean_timeout_seconds < 1:
            raise ValueError("Lean timeout must be positive")
        self.forbidden_declarations = tuple(
            dict.fromkeys(
                validate_declaration_name(item, label="forbidden declaration")
                for item in config.forbidden_declarations
            )
        )

    @staticmethod
    def _command(command: Any) -> dict[str, Any]:
        return command.to_dict()

    @staticmethod
    def _planner_decisions(substep_plans) -> tuple[dict[str, Any], ...]:
        return tuple(
            {
                "goal_key": plan.goal_key.fingerprint,
                "plan_fingerprint": plan.plan_fingerprint,
                "recommended_action_id": plan.recommended_action_id,
            }
            for plan in substep_plans
        )

    @staticmethod
    def _generated_declarations(evidence: GenerationEvidence) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (
                    *evidence.new_helper_declarations,
                    *evidence.new_intermediate_declarations,
                    *evidence.new_program_declarations,
                    *evidence.new_semantic_proofs,
                    *evidence.new_complexity_proofs,
                    *evidence.new_certified_reductions,
                )
            )
        )

    def _write_result(
        self, store: GeneralJobStore, result: GeneralNPHardResult
    ) -> GeneralNPHardResult:
        write_result(store.path("report.json"), result)
        return result

    def _requested_root(self) -> RootGoal:
        return RootGoal.for_problem(
            input_module=self.config.input_module,
            problem_declaration=self.config.problem_declaration,
            endpoint_fingerprint="unvalidated",
        )

    def _failure_result(
        self,
        *,
        store: GeneralJobStore,
        proof_status: ProofStatus,
        root_goal: RootGoal,
        job_id: str,
        code: str,
        explanation: str,
        commands: Sequence[Mapping[str, Any]] = (),
        model_calls: Sequence[ModelCallRecord] = (),
        candidates: Sequence[TheoremIndexEntry] = (),
        substep_plans=(),
        input_identity: Mapping[str, Any] | None = None,
        environment_snapshot: Mapping[str, Any] | None = None,
        evidence: GenerationEvidence = GenerationEvidence(),
    ) -> GeneralNPHardResult:
        store.transition(proof_status.value, details={"code": code})
        return self._write_result(
            store,
            GeneralNPHardResult(
                proof_status=proof_status,
                solution_classification=SolutionClassification.NONE,
                qualification_status=initial_qualification_status(self.profile),
                root_goal=root_goal,
                strategy=self.config.strategy,
                profile=self.profile.name,
                output_dir=str(self.output_dir),
                job_id=job_id,
                theorem_candidates=tuple(candidates),
                capability_planner_decisions=self._planner_decisions(substep_plans),
                substep_plans=tuple(substep_plans),
                model_calls=tuple(model_calls),
                lean_commands=tuple(commands),
                blocker={"code": code, "explanation": explanation},
                generation_evidence=evidence,
                generated_declarations=self._generated_declarations(evidence),
                input_identity=input_identity,
                environment_snapshot=environment_snapshot,
            ),
        )

    def run(self) -> GeneralNPHardResult:
        store = GeneralJobStore(self.output_dir)
        request = GeneralNPHardRequest(
            input_module=self.config.input_module,
            problem_declaration=self.config.problem_declaration,
            strategy=self.config.strategy,
            profile=self.profile.name,
            model_policy=self.config.model_policy,
            plugins=self.config.plugins,
            forbidden_declarations=self.forbidden_declarations,
        )
        provisional_job_id = request.fingerprint
        with store.exclusive_run():
            store.write_json(
                "request.json",
                {
                    **request.canonical_dict(),
                    "budget": asdict(self.config.budget),
                    "lean_timeout_seconds": self.config.lean_timeout_seconds,
                },
            )
            store.transition("RECEIVED")
            try:
                stable_hashes = verify_stable_entrypoints(self.root)
                store.write_json(
                    "receipts/stable-entrypoints.json",
                    {"schema_version": "general_stable_entrypoint_guard_v1", "hashes": stable_hashes},
                )
                return self._run_validated(store=store, request=request)
            except NPHardInputError as error:
                return self._failure_result(
                    store=store,
                    proof_status=ProofStatus.INPUT_ERROR,
                    root_goal=self._requested_root(),
                    job_id=provisional_job_id,
                    code=error.code,
                    explanation=error.message,
                    commands=(self._command(error.command),) if error.command else (),
                )
            except BudgetExhausted as error:
                return self._failure_result(
                    store=store,
                    proof_status=ProofStatus.BUDGET_EXHAUSTED,
                    root_goal=self._requested_root(),
                    job_id=provisional_job_id,
                    code="budget_exhausted",
                    explanation=str(error),
                )
            except (ImportError, OSError, RuntimeError, TypeError, ValueError) as error:
                return self._failure_result(
                    store=store,
                    proof_status=ProofStatus.FAILED_LEAN,
                    root_goal=self._requested_root(),
                    job_id=provisional_job_id,
                    code="general_agent_infrastructure_error",
                    explanation=str(error),
                )

    def _run_validated(
        self, *, store: GeneralJobStore, request: GeneralNPHardRequest
    ) -> GeneralNPHardResult:
        commands: list[dict[str, Any]] = []
        model_calls: list[ModelCallRecord] = []
        tracker = BudgetTracker(self.config.budget)
        reference = resolve_np_hard_input_reference(
            root=self.root,
            input_module=self.config.input_module,
            requested_term=self.config.problem_declaration,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        toolchain = (self.root / "Lean" / "lean-toolchain").read_text(
            encoding="utf-8"
        ).strip()
        identity, input_command = certify_np_hard_input(
            root=self.root,
            reference=reference,
            certificate_path=store.path("GoalProbe.lean"),
            toolchain=toolchain,
            lake_manifest_sha256=sha256_file(self.root / "Lean" / "lake-manifest.json"),
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        commands.append(self._command(input_command))
        root_goal = RootGoal.for_problem(
            input_module=reference.input_module,
            problem_declaration=reference.problem_declaration,
            endpoint_fingerprint=identity.normalized_problem_node,
        )
        store.transition("INPUT_VALIDATED", details={"endpoint": root_goal.endpoint_fingerprint})

        modules = project_module_catalog(self.root)
        snapshot = snapshot_environment(
            root=self.root,
            imported_modules=(
                reference.input_module,
                "ComplexityReduction.Agent.Hardness.Runtime",
                "ComplexityReduction.Agent.GenerativeReduction.FinalCheck",
                *modules,
            ),
            axiom_policy="assert_standard_axioms",
        )
        store.write_json("environment.json", snapshot.to_dict())
        store.transition("ENVIRONMENT_FROZEN", details={"snapshot": snapshot.snapshot_hash})
        job_id = stable_sha256(
            {
                "request": request.canonical_dict(),
                "input_source_hash": identity.normalization_certificate_sha256,
                "endpoint": root_goal.endpoint_fingerprint,
                "toolchain": snapshot.lean_toolchain,
                "manifest": snapshot.lake_manifest_sha256,
                "schema": request.schema_version,
            }
        )

        if not self.config.runtime_prebuilt:
            build = run_command(
                build_module_command([reference.input_module]),
                cwd=self.root / "Lean",
                timeout_seconds=self.config.lean_timeout_seconds,
                output_limit=16 * 1024 * 1024,
            )
            commands.append(self._command(build))
            if not build.ok:
                return self._failure_result(
                    store=store,
                    proof_status=ProofStatus.FAILED_LEAN,
                    root_goal=root_goal,
                    job_id=job_id,
                    code="lean_input_build_failed",
                    explanation=build.stderr or build.stdout,
                    commands=commands,
                    input_identity=identity.to_dict(),
                    environment_snapshot=snapshot.to_dict(),
                )

        deterministic, fast_command = self._closed_resolver_probe(
            store=store, reference=reference
        )
        commands.append(self._command(fast_command))
        resolution = deterministic.resolution
        fast_route_declarations = tuple(
            dict.fromkeys(
                (
                    *((resolution.atoms if resolution is not None else ())),
                    *((resolution.hardness_declaration,) if resolution and resolution.hardness_declaration else ()),
                    *((resolution.completeness_declaration,) if resolution and resolution.completeness_declaration else ()),
                )
            )
        )
        forbidden_fast_path_hits = tuple(
            item for item in fast_route_declarations if item in self.forbidden_declarations
        )
        closed_resolver_payload = deterministic.to_dict()
        closed_resolver_payload["route_policy"] = {
            "forbidden_declarations": list(self.forbidden_declarations),
            "forbidden_hits": list(forbidden_fast_path_hits),
            "eligible": not forbidden_fast_path_hits,
        }
        store.write_json("planner/closed-resolver.json", closed_resolver_payload)
        store.transition(
            "FAST_PATH_CHECKED",
            details={
                "closed": resolution is not None,
                "forbidden_hit_count": len(forbidden_fast_path_hits),
            },
        )
        if (
            resolution is not None
            and not forbidden_fast_path_hits
            and self.config.strategy != Strategy.SYNTHESIS_REQUIRED
        ):
            source = build_resolver_artifact_source(
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                forbidden_declarations=self.forbidden_declarations,
            )
            return self._finalize_verified_source(
                store=store,
                source=source,
                root_goal=root_goal,
                job_id=job_id,
                commands=commands,
                model_calls=model_calls,
                identity=identity.to_dict(),
                snapshot=snapshot.to_dict(),
                selected_route=tuple(resolution.atoms),
                proof_step=ProofStep(
                    action_id="closed-resolver-fast-path",
                    provider=ProviderKind.REUSE,
                    disposition=ActionDisposition.CLOSED,
                    goal_id="goal-root",
                    exact_type=root_goal.exact_type,
                    declaration=(
                        resolution.hardness_declaration
                        or resolution.completeness_declaration
                    ),
                ),
                candidates=(),
                substep_plans=(),
                generation_evidence=GenerationEvidence(
                    attempted=False,
                    environment_snapshot_hash=snapshot.snapshot_hash,
                    classification="no-generation-needed",
                ),
                provider_statistics={
                    ProviderKind.REUSE.value: ProviderStatistics(
                        candidate_count=1,
                        expanded_action_count=1,
                        lean_checks=1,
                        successful_closures=1,
                    )
                },
            )

        indexed_candidates, index_command = query_theorem_index(
            root=self.root,
            input_module=reference.input_module,
            problem_declaration=reference.problem_declaration,
            modules=modules,
            output_path=store.path("TheoremIndexProbe.lean"),
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        commands.append(self._command(index_command))
        candidates = tuple(
            candidate
            for candidate in indexed_candidates
            if candidate.declaration not in self.forbidden_declarations
        )
        excluded_candidates = tuple(
            candidate
            for candidate in indexed_candidates
            if candidate.declaration in self.forbidden_declarations
        )
        store.write_json(
            "planner/theorem-index.json",
            {
                "modules": list(modules),
                "candidates": [_as_json_mapping(candidate) for candidate in candidates],
                "route_policy": {
                    "forbidden_declarations": list(self.forbidden_declarations),
                    "excluded_candidates": [
                        candidate.declaration for candidate in excluded_candidates
                    ],
                    "raw_candidate_count": len(indexed_candidates),
                    "eligible_candidate_count": len(candidates),
                },
            },
        )
        store.transition(
            "INDEX_READY",
            details={
                "candidate_count": len(candidates),
                "excluded_candidate_count": len(excluded_candidates),
            },
        )

        registry = default_registry()
        installed_plugins = install_plugins(registry, self.config.plugins)
        plugin_imports = tuple(
            imported
            for plugin in installed_plugins
            for imported in plugin.lean_imports
        )
        checked_sources: dict[str, str] = {}

        def checker(goal, candidate, solved):
            del goal
            tracker.consume("lean_checks")
            solutions = tuple(solution for _, solution in solved)
            source = build_theorem_artifact_source(
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                candidate=candidate,
                premise_solutions=solutions,
                plugin_imports=plugin_imports,
                forbidden_declarations=self.forbidden_declarations,
            )
            candidate_path = store.write_text(
                f"work/candidates/{candidate.candidate_id.removeprefix('sha256:')}.lean",
                source,
            )
            command = run_lean_file(
                root=self.root,
                path=candidate_path,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            commands.append(self._command(command))
            if command.ok:
                checked_sources[candidate.declaration] = source
                return ClosureCheck(ok=True, proof_term=candidate.declaration)
            return ClosureCheck(
                ok=False,
                diagnostic=(command.stderr or command.stdout)[-4000:],
            )

        planner = CapabilityPlanner(
            solver_registry=registry,
            tracker=tracker,
            checker=checker,
        )
        state = ProofState.initial(
            root_goal,
            import_closure_fingerprint=snapshot.import_closure_fingerprint,
        )
        goal = state.select_open_goal()
        store.transition("SEARCHING")
        plan = planner.plan(
            goal=goal,
            candidates=candidates,
            fragments=(),
            environment_fingerprint=snapshot.snapshot_hash,
            capability_fingerprint=stable_sha256(
                {
                    "candidates": [candidate.candidate_id for candidate in candidates],
                    "forbidden_declarations": self.forbidden_declarations,
                }
            ),
            failure_memory_fingerprint=stable_sha256(()),
            strategy=self.config.strategy,
            is_root=True,
            target_handle=reference.problem_declaration,
            forbidden_declarations=self.forbidden_declarations,
        )
        store.write_json("planner/root-substep-plan.json", _as_json_mapping(plan))
        closed_actions = tuple(
            action
            for action in plan.candidate_actions
            if action.disposition == ActionDisposition.CLOSED and action.lean_verified
        )
        if closed_actions:
            declaration = plan.exact_closure_result.declaration
            source = checked_sources.get(declaration or "")
            if source is None:
                raise RuntimeError("closed theorem candidate lost its checked source")
            closed_action = closed_actions[0]
            statistics = _provider_statistics(plan)
            statistics[ProviderKind.REUSE.value].expanded_action_count += 1
            statistics[ProviderKind.REUSE.value].lean_checks += tracker.usage.lean_checks
            statistics[ProviderKind.REUSE.value].successful_closures += 1
            return self._finalize_verified_source(
                store=store,
                source=source,
                root_goal=root_goal,
                job_id=job_id,
                commands=commands,
                model_calls=model_calls,
                identity=identity.to_dict(),
                snapshot=snapshot.to_dict(),
                selected_route=(declaration,) if declaration else (),
                proof_step=ProofStep(
                    action_id=closed_action.action_id,
                    provider=closed_action.provider,
                    disposition=closed_action.disposition,
                    goal_id="goal-root",
                    exact_type=root_goal.exact_type,
                    declaration=declaration,
                ),
                candidates=candidates,
                substep_plans=(plan,),
                generation_evidence=GenerationEvidence(
                    attempted=False,
                    environment_snapshot_hash=snapshot.snapshot_hash,
                    classification="no-generation-needed",
                ),
                provider_statistics=statistics,
            )

        return self._attempt_open_synthesis(
            store=store,
            reference=reference,
            root_goal=root_goal,
            job_id=job_id,
            commands=commands,
            model_calls=model_calls,
            identity=identity.to_dict(),
            snapshot=snapshot.to_dict(),
            snapshot_hash=snapshot.snapshot_hash,
            candidates=candidates,
            plan=plan,
            tracker=tracker,
            plugin_imports=plugin_imports,
        )

    def _closed_resolver_probe(self, *, store, reference):
        nonce = secrets.token_hex(16)
        path = store.write_text(
            "FastPathProbe.lean",
            build_np_hard_probe_source(
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                nonce=nonce,
            ),
        )
        command = run_lean_file(
            root=self.root,
            path=path,
            timeout_seconds=self.config.lean_timeout_seconds,
        )
        if not command.ok:
            raise RuntimeError(command.stderr or command.stdout)
        return (
            parse_np_hard_probe_output(
                stdout=command.stdout,
                stderr=command.stderr,
                nonce=nonce,
                problem_declaration=reference.problem_declaration,
            ),
            command,
        )

    def _attempt_open_synthesis(
        self,
        *,
        store,
        reference,
        root_goal,
        job_id,
        commands,
        model_calls,
        identity,
        snapshot,
        snapshot_hash,
        candidates,
        plan,
        tracker,
        plugin_imports,
    ) -> GeneralNPHardResult:
        contract = plan.construction_contract
        evidence = GenerationEvidence(
            attempted=contract is not None,
            environment_snapshot_hash=snapshot_hash,
            classification=(
                "generation-attempted-blocked" if contract is not None else "no-generation-needed"
            ),
        )
        if contract is None:
            return self._failure_result(
                store=store,
                proof_status=ProofStatus.BLOCKED,
                root_goal=root_goal,
                job_id=job_id,
                code="no_safe_action",
                explanation="Capability Planner returned no exact closure or construction contract",
                commands=commands,
                candidates=candidates,
                substep_plans=(plan,),
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=evidence,
            )
        if self.config.model_policy == ModelPolicy.DISABLED:
            return self._failure_result(
                store=store,
                proof_status=ProofStatus.BLOCKED,
                root_goal=root_goal,
                job_id=job_id,
                code="authoring_disabled",
                explanation="typed construction contract exists but model authoring is disabled",
                commands=commands,
                candidates=candidates,
                substep_plans=(plan,),
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=evidence,
            )
        if self.config.deepseek is None or not self.config.deepseek.api_key:
            status = (
                ProofStatus.FAILED_MODEL
                if self.config.model_policy == ModelPolicy.REQUIRED
                else ProofStatus.BLOCKED
            )
            return self._failure_result(
                store=store,
                proof_status=status,
                root_goal=root_goal,
                job_id=job_id,
                code="model_provider_unavailable",
                explanation="open synthesis needs a configured model provider",
                commands=commands,
                candidates=candidates,
                substep_plans=(plan,),
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=evidence,
            )

        client = DeepSeekClient(self.config.deepseek)
        tracker.consume("model_calls")
        tracker.consume("strategy_calls")
        proposal, strategy_record = propose_strategy(
            model=client,
            goal=ProofState.initial(root_goal).select_open_goal(),
            plan=plan,
        )
        model_calls.append(strategy_record)
        if not strategy_record.ok and self.config.model_policy == ModelPolicy.REQUIRED:
            return self._failure_result(
                store=store,
                proof_status=ProofStatus.FAILED_MODEL,
                root_goal=root_goal,
                job_id=job_id,
                code="strategy_model_failed",
                explanation=strategy_record.error or "strategy model failed",
                commands=commands,
                model_calls=model_calls,
                candidates=candidates,
                substep_plans=(plan,),
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=evidence,
            )

        store.transition("SYNTHESIZING", details={"contract": contract.contract_id})
        diagnostics: str | None = None
        authored_source: str | None = None
        candidate_modules = tuple(
            dict.fromkeys(candidate.module for candidate in candidates[:12])
        )
        extra_imports = (*candidate_modules, *plugin_imports)
        attempts = min(
            self.config.budget.max_authoring_attempts_per_stage,
            self.config.budget.max_authoring_calls,
        )
        for attempt in range(attempts):
            tracker.consume("model_calls")
            tracker.consume("authoring_calls")
            authoring, record = propose_implementation(
                model=client,
                contract=contract,
                guidance=plan.ranked_proof_guidance,
                diagnostics=diagnostics,
            )
            model_calls.append(record)
            if authoring is None:
                diagnostics = record.error or "authoring protocol failed"
                continue
            try:
                source = build_authored_artifact_source(
                    input_module=reference.input_module,
                    problem_declaration=reference.problem_declaration,
                    implementation=authoring.implementation or "",
                    extra_imports=extra_imports,
                    forbidden_declarations=self.forbidden_declarations,
                )
            except ValueError as error:
                diagnostics = str(error)
                continue
            tracker.consume("lean_checks")
            tracker.consume("generated_files")
            path = store.write_text(f"work/Generated/Attempt{attempt + 1}.lean", source)
            command = run_lean_file(
                root=self.root,
                path=path,
                timeout_seconds=self.config.lean_timeout_seconds,
            )
            commands.append(self._command(command))
            if command.ok:
                authored_source = source
                break
            diagnostics = (command.stderr or command.stdout)[-4000:]

        if authored_source is None:
            attempted = GenerationEvidence(
                attempted=True,
                strategy_call_count=tracker.usage.strategy_calls,
                authoring_call_count=tracker.usage.authoring_calls,
                environment_snapshot_hash=snapshot_hash,
                classification="generation-attempted-blocked",
            )
            status = (
                ProofStatus.FAILED_MODEL
                if model_calls and all(not record.ok for record in model_calls)
                else ProofStatus.BLOCKED
            )
            return self._failure_result(
                store=store,
                proof_status=status,
                root_goal=root_goal,
                job_id=job_id,
                code="open_synthesis_not_verified",
                explanation=diagnostics or "no authored candidate passed Lean",
                commands=commands,
                model_calls=model_calls,
                candidates=candidates,
                substep_plans=(plan,),
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=attempted,
            )

        generated_evidence = evidence_from_generated_source(
            source=authored_source,
            environment_snapshot_hash=snapshot_hash,
            strategy_call_count=tracker.usage.strategy_calls,
            authoring_call_count=tracker.usage.authoring_calls,
            core_verified=True,
        )
        statistics = _provider_statistics(plan)
        statistics[ProviderKind.SYNTHESIS.value].expanded_action_count += 1
        statistics[ProviderKind.SYNTHESIS.value].model_calls += len(model_calls)
        statistics[ProviderKind.SYNTHESIS.value].lean_checks += tracker.usage.lean_checks
        statistics[ProviderKind.SYNTHESIS.value].successful_closures += 1
        return self._finalize_verified_source(
            store=store,
            source=authored_source,
            root_goal=root_goal,
            job_id=job_id,
            commands=commands,
            model_calls=model_calls,
            identity=identity,
            snapshot=snapshot,
            selected_route=("job-local-authored-candidate",),
            proof_step=ProofStep(
                action_id=(proposal.action_id if proposal and proposal.action_id else "open-synthesis"),
                provider=ProviderKind.SYNTHESIS,
                disposition=ActionDisposition.CLOSED,
                goal_id="goal-root",
                exact_type=root_goal.exact_type,
                declaration="ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard",
            ),
            candidates=candidates,
            substep_plans=(plan,),
            generation_evidence=generated_evidence,
            provider_statistics=statistics,
        )

    def _finalize_verified_source(
        self,
        *,
        store,
        source,
        root_goal,
        job_id,
        commands,
        model_calls,
        identity,
        snapshot,
        selected_route,
        proof_step,
        candidates,
        substep_plans,
        generation_evidence,
        provider_statistics,
    ) -> GeneralNPHardResult:
        artifact_path = store.write_text("Artifact.lean", source)
        store.transition("PROOF_RECONSTRUCTED")
        check, replay, verification, digest = verify_core_artifact(
            root=self.root,
            artifact_path=artifact_path,
            timeout_seconds=self.config.lean_timeout_seconds,
            replay=self.profile.independent_replay,
        )
        commands.append(self._command(check))
        if replay is not None:
            commands.append(self._command(replay))
        verified = verification.kernel_verified and verification.independent_replay_passed
        if not verified:
            return self._failure_result(
                store=store,
                proof_status=ProofStatus.FAILED_LEAN,
                root_goal=root_goal,
                job_id=job_id,
                code="final_artifact_failed",
                explanation=check.stderr or check.stdout,
                commands=commands,
                model_calls=model_calls,
                candidates=candidates,
                substep_plans=substep_plans,
                input_identity=identity,
                environment_snapshot=snapshot,
                evidence=generation_evidence,
            )
        store.transition("PROOF_VERIFIED")
        classification = classify_generation(generation_evidence)
        store.transition("GENERATION_CLASSIFIED", details={"classification": classification.value})
        qualification = initial_qualification_status(self.profile)
        store.transition("PROFILE_EVALUATED", details={"qualification": qualification.value})
        result = GeneralNPHardResult(
            proof_status=ProofStatus.VERIFIED,
            solution_classification=classification,
            qualification_status=qualification,
            root_goal=root_goal,
            strategy=self.config.strategy,
            profile=self.profile.name,
            output_dir=str(self.output_dir),
            job_id=job_id,
            selected_proof_route=tuple(selected_route),
            proof_tree=(proof_step,),
            capability_planner_decisions=self._planner_decisions(substep_plans),
            substep_plans=tuple(substep_plans),
            action_provider_statistics=provider_statistics,
            theorem_candidates=tuple(candidates),
            generated_declarations=self._generated_declarations(generation_evidence),
            model_calls=tuple(model_calls),
            lean_commands=tuple(commands),
            verification=verification,
            generation_evidence=generation_evidence,
            artifact_file=str(artifact_path),
            artifact_sha256=digest,
            input_identity=identity,
            environment_snapshot=snapshot,
        )
        store.transition("COMPLETED")
        return self._write_result(store, result)


def _provider_statistics(plan) -> dict[str, ProviderStatistics]:
    counts = Counter(action.provider.value for action in plan.candidate_actions)
    return {
        kind.value: ProviderStatistics(candidate_count=counts.get(kind.value, 0))
        for kind in ProviderKind
    }


def _as_json_mapping(value: Any) -> dict[str, Any]:
    from .models import _jsonable

    mapped = _jsonable(value)
    if not isinstance(mapped, dict):
        raise TypeError("expected a JSON object")
    return mapped


def public_status(result: GeneralNPHardResult) -> str:
    return result.display_status or result.proof_status.value


__all__ = [
    "GenerativeReductionConfig",
    "GenerativeReductionOrchestrator",
    "public_status",
]
