"""General NP-hard-first orchestrator with typed reuse and open synthesis hooks."""

from __future__ import annotations

from collections import Counter
from dataclasses import asdict, dataclass, replace
import secrets
from pathlib import Path
from typing import Any, Mapping, Sequence

from agent.hardness.lean_runner import (
    build_module_command,
    run_command,
    sha256_file,
    validate_declaration_name,
)
from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.np_hard import build_np_hard_probe_source, parse_np_hard_probe_output
from agent.hardness.np_hard_input import (
    NPHardInputError,
    certify_np_hard_input,
    resolve_np_hard_input_reference,
)

from .baseline import verify_stable_entrypoints
from .budgets import BudgetExhausted, BudgetTracker, SearchBudget
from .job import GeneralJobStore
from .lean_bridge import run_lean_file, snapshot_environment
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
from .recursive_runtime import RecursiveSearchRuntime
from .reconstruction import (
    build_resolver_artifact_source,
    build_search_artifact_source,
)
from .reporting import write_result
from .search import SearchCoordinator
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
    excluded_candidate_declarations: tuple[str, ...] = ()
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
        self.excluded_candidate_declarations = tuple(
            dict.fromkeys(
                validate_declaration_name(item, label="excluded candidate declaration")
                for item in config.excluded_candidate_declarations
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

    @staticmethod
    def _reachable_generated_declarations(
        final_state: ProofState | None,
    ) -> frozenset[str]:
        """Follow the generated-declaration graph from the verified root proof.

        The final artifact intentionally contains every preserved capability, so
        source-file membership alone would incorrectly classify an abandoned
        branch helper as final-used.  This bounded graph walk starts from the
        actual root proof term and follows only referenced generated bodies.
        """

        if final_state is None or final_state.root_fragment is None:
            return frozenset()
        by_declaration = {
            capability.declaration: capability
            for capability in final_state.generated_capabilities
        }
        pending = [
            declaration
            for declaration in by_declaration
            if declaration in final_state.root_fragment.proof_term
        ]
        reachable: set[str] = set()
        while pending:
            declaration = pending.pop()
            if declaration in reachable:
                continue
            reachable.add(declaration)
            implementation = by_declaration[declaration].implementation
            pending.extend(
                dependency
                for dependency in by_declaration
                if dependency not in reachable and dependency in implementation
            )
        return frozenset(reachable)

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
        provider_statistics: Mapping[str, ProviderStatistics] | None = None,
        proof_tree: Sequence[ProofStep] = (),
        search_outcome=None,
        final_state: ProofState | None = None,
        synthesis_designs: Sequence[Mapping[str, Any]] = (),
        context_capsules: Sequence[Mapping[str, Any]] = (),
        repair_lineage: Sequence[Mapping[str, Any]] = (),
        capability_plans=(),
        theorem_application_plans=(),
        generator_briefs=(),
        generator_results=(),
        contribution_receipts=(),
        planner_effect_receipts=(),
        typed_capability_plans: Sequence[Mapping[str, Any]] = (),
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
                proof_tree=tuple(proof_tree),
                capability_planner_decisions=self._planner_decisions(substep_plans),
                substep_plans=tuple(substep_plans),
                action_provider_statistics=dict(provider_statistics or {}),
                synthesis_designs=tuple(synthesis_designs),
                context_capsules=tuple(context_capsules),
                repair_lineage=tuple(repair_lineage),
                capability_plans=tuple(capability_plans),
                theorem_application_plans=tuple(theorem_application_plans),
                generator_briefs=tuple(generator_briefs),
                generator_results=tuple(generator_results),
                contribution_receipts=tuple(contribution_receipts),
                planner_effect_receipts=tuple(planner_effect_receipts),
                typed_capability_plans=tuple(typed_capability_plans),
                model_calls=tuple(model_calls),
                lean_commands=tuple(commands),
                blocker={
                    "code": code,
                    "explanation": explanation,
                    "frontier_exhaustion_receipt": (
                        getattr(search_outcome, "frontier_exhaustion_receipt", None)
                    ),
                },
                generation_evidence=evidence,
                generated_declarations=self._generated_declarations(evidence),
                input_identity=input_identity,
                environment_snapshot=environment_snapshot,
                expanded_state_count=getattr(search_outcome, "expanded_states", 0),
                requeued_failure_state_count=getattr(
                    search_outcome, "requeued_failure_states", 0
                ),
                pruned_cycle_count=getattr(search_outcome, "pruned_cycles", 0),
                max_observed_search_depth=getattr(
                    search_outcome, "max_observed_depth", 0
                ),
                application_frame_count=(
                    len(final_state.application_frames) if final_state else 0
                ),
                verified_application_frame_count=(
                    sum(
                        frame.status.value == "verified"
                        for frame in final_state.application_frames
                    )
                    if final_state
                    else 0
                ),
                data_binding_count=(final_state.data_binding_count if final_state else 0),
                dependent_goal_activation_count=(
                    final_state.dependent_goal_activation_count if final_state else 0
                ),
                recursive_substep_plan_count=(
                    len(final_state.substep_plans) if final_state else len(tuple(substep_plans))
                ),
                generated_capability_count=(
                    len(final_state.generated_capabilities) if final_state else 0
                ),
                final_frontier_size=getattr(search_outcome, "final_frontier_size", 0),
                frontier_exhaustion_receipt=getattr(
                    search_outcome, "frontier_exhaustion_receipt", None
                ),
                per_goal_attempted_actions=(
                    {
                        goal.goal_id: goal.attempted_actions
                        for goal in final_state.open_goals
                    }
                    if final_state
                    else {}
                ),
                strategy_valid_proposal_count=getattr(
                    search_outcome, "strategy_valid_proposals", 0
                ),
                strategy_applied_decision_count=getattr(
                    search_outcome, "strategy_applied_decisions", 0
                ),
                strategy_fallback_count=getattr(
                    search_outcome, "strategy_fallbacks", 0
                ),
                strategy_rejected_count=getattr(
                    search_outcome, "strategy_rejections", 0
                ),
                unused_strategy_call_count=max(
                    0,
                    sum(
                        bool(call.called) and call.purpose == "strategy-proposal"
                        for call in model_calls
                    )
                    - getattr(search_outcome, "strategy_applied_decisions", 0)
                    - getattr(search_outcome, "strategy_fallbacks", 0)
                    - getattr(search_outcome, "strategy_rejections", 0),
                ),
                strategy_effect_receipts=getattr(
                    search_outcome, "strategy_effect_receipts", ()
                ),
                finite_candidate_count=getattr(
                    search_outcome, "finite_candidate_count", 0
                ),
                finite_counterexample_count=getattr(
                    search_outcome, "finite_counterexample_count", 0
                ),
                finite_certificate_count=getattr(
                    search_outcome, "finite_certificate_count", 0
                ),
                capability_compiler_candidate_count=getattr(
                    search_outcome, "capability_compiler_candidate_count", 0
                ),
                capability_compiler_certificate_count=getattr(
                    search_outcome, "capability_compiler_certificate_count", 0
                ),
                generated_lean_check_count=getattr(
                    search_outcome, "generated_lean_check_count", 0
                ),
                generated_lean_success_count=getattr(
                    search_outcome, "generated_lean_success_count", 0
                ),
                capability_registration_count=getattr(
                    search_outcome, "capability_registration_count", 0
                ),
                synthesis_design_count=getattr(
                    search_outcome, "synthesis_design_count", len(synthesis_designs)
                ),
                context_expansion_count=getattr(
                    search_outcome, "context_expansion_count", 0
                ),
                repair_authoring_count=sum(
                    bool(call.called) and call.purpose == "lean-authoring-repair"
                    for call in model_calls
                ),
                duplicate_candidate_rejection_count=getattr(
                    search_outcome, "duplicate_candidate_rejection_count", 0
                ),
                repeated_diagnostic_count=getattr(
                    search_outcome, "repeated_diagnostic_count", 0
                ),
                context_insufficient_count=getattr(
                    search_outcome, "context_insufficient_count", 0
                ),
                unresolved_probe_handle_count=getattr(
                    search_outcome, "unresolved_probe_handle_count", 0
                ),
                rejected_nonexecutable_design_count=getattr(
                    search_outcome, "rejected_nonexecutable_design_count", 0
                ),
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
            excluded_candidate_declarations=self.excluded_candidate_declarations,
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
        excluded_fast_path_hits = tuple(
            item
            for item in fast_route_declarations
            if item in self.excluded_candidate_declarations
        )
        closed_resolver_payload = deterministic.to_dict()
        closed_resolver_payload["route_policy"] = {
            "forbidden_declarations": list(self.forbidden_declarations),
            "forbidden_hits": list(forbidden_fast_path_hits),
            "excluded_candidate_declarations": list(
                self.excluded_candidate_declarations
            ),
            "excluded_candidate_hits": list(excluded_fast_path_hits),
            "eligible": not forbidden_fast_path_hits and not excluded_fast_path_hits,
        }
        store.write_json("planner/closed-resolver.json", closed_resolver_payload)
        store.transition(
            "FAST_PATH_CHECKED",
            details={
                "closed": resolution is not None,
                "forbidden_hit_count": len(forbidden_fast_path_hits),
                "excluded_candidate_hit_count": len(excluded_fast_path_hits),
            },
        )
        if (
            resolution is not None
            and not forbidden_fast_path_hits
            and not excluded_fast_path_hits
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
            and candidate.declaration not in self.excluded_candidate_declarations
        )
        excluded_candidates = tuple(
            candidate
            for candidate in indexed_candidates
            if candidate.declaration in self.forbidden_declarations
            or candidate.declaration in self.excluded_candidate_declarations
        )
        store.write_json(
            "planner/theorem-index.json",
            {
                "modules": list(modules),
                "candidates": [_as_json_mapping(candidate) for candidate in candidates],
                "route_policy": {
                    "forbidden_declarations": list(self.forbidden_declarations),
                    "excluded_candidate_declarations": list(
                        self.excluded_candidate_declarations
                    ),
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
        finite_plugins = tuple(
            finite
            for plugin in installed_plugins
            for finite in plugin.finite_synthesis_plugins
        )
        plugin_imports = tuple(
            imported
            for plugin in installed_plugins
            for imported in plugin.lean_imports
        )
        initial_state = ProofState.initial(
            root_goal,
            import_closure_fingerprint=snapshot.import_closure_fingerprint,
        )
        runtime = RecursiveSearchRuntime(
            root=self.root,
            store=store,
            input_module=reference.input_module,
            modules=modules,
            plugin_imports=plugin_imports,
            forbidden_declarations=self.forbidden_declarations,
            excluded_candidate_declarations=self.excluded_candidate_declarations,
            tracker=tracker,
            solver_registry=registry,
            model_policy=self.config.model_policy,
            deepseek=self.config.deepseek,
            lean_timeout_seconds=self.config.lean_timeout_seconds,
            commands=commands,
            model_calls=model_calls,
            event_sink=lambda name, details: store.append_event(name, details=details),
            finite_plugins=finite_plugins,
        )
        runtime.seed_candidates(initial_state, root_goal.exact_type, candidates)
        coordinator = SearchCoordinator(
            planner=runtime.planner,
            tracker=tracker,
            strategy=self.config.strategy,
            environment_fingerprint=snapshot.snapshot_hash,
            capability_fingerprint=lambda state: state.capability_fingerprint,
            candidate_lookup=runtime.candidate_lookup,
            action_executor=runtime.execute,
            dead_end_handler=runtime.dead_end,
            strategy_decider=runtime.decide_strategy,
            forbidden_declarations=self.forbidden_declarations,
            event_sink=lambda name, details: store.append_event(name, details=details),
        )
        store.transition("SEARCHING")
        outcome = coordinator.run(initial_state)
        best_state = outcome.best_state
        synthesis_designs = runtime.synthesis_design_receipts()
        context_capsules = runtime.context_capsule_receipts()
        repair_lineage = runtime.repair_lineage_receipts()
        capability_plans = runtime.capability_plan_receipts()
        theorem_application_plans = runtime.theorem_application_plan_receipts()
        generator_briefs = runtime.generator_brief_receipts()
        generator_results = runtime.generator_result_receipts()
        contribution_receipts = runtime.contribution_receipts()
        planner_effect_receipts = runtime.planner_effect_receipts()
        typed_capability_plans = runtime.typed_plan_receipts()
        store.write_json(
            "planner/search-outcome.json",
            {
                "status": outcome.status,
                "blocker": outcome.blocker,
                "expanded_states": outcome.expanded_states,
                "requeued_failure_states": outcome.requeued_failure_states,
                "pruned_cycles": outcome.pruned_cycles,
                "max_observed_depth": outcome.max_observed_depth,
                "final_frontier_size": outcome.final_frontier_size,
                "frontier_exhaustion_receipt": outcome.frontier_exhaustion_receipt,
                "strategy_valid_proposals": outcome.strategy_valid_proposals,
                "strategy_applied_decisions": outcome.strategy_applied_decisions,
                "strategy_fallbacks": outcome.strategy_fallbacks,
                "strategy_rejections": outcome.strategy_rejections,
                "strategy_effect_receipts": [
                    asdict(receipt) for receipt in outcome.strategy_effect_receipts
                ],
                "finite_candidate_count": outcome.finite_candidate_count,
                "finite_counterexample_count": outcome.finite_counterexample_count,
                "finite_certificate_count": outcome.finite_certificate_count,
                "capability_compiler_candidate_count": (
                    outcome.capability_compiler_candidate_count
                ),
                "capability_compiler_certificate_count": (
                    outcome.capability_compiler_certificate_count
                ),
                "generated_lean_check_count": outcome.generated_lean_check_count,
                "generated_lean_success_count": outcome.generated_lean_success_count,
                "capability_registration_count": outcome.capability_registration_count,
                "synthesis_design_count": outcome.synthesis_design_count,
                "context_expansion_count": outcome.context_expansion_count,
                "duplicate_candidate_rejection_count": (
                    outcome.duplicate_candidate_rejection_count
                ),
                "repeated_diagnostic_count": outcome.repeated_diagnostic_count,
                "synthesis_designs": list(synthesis_designs),
                "context_capsules": list(context_capsules),
                "repair_lineage": list(repair_lineage),
                "capability_plans": [asdict(item) for item in capability_plans],
                "theorem_application_plans": [
                    asdict(item) for item in theorem_application_plans
                ],
                "generator_briefs": [asdict(item) for item in generator_briefs],
                "generator_results": [asdict(item) for item in generator_results],
                "contribution_receipts": [
                    asdict(item) for item in contribution_receipts
                ],
                "planner_effect_receipts": [
                    asdict(item) for item in planner_effect_receipts
                ],
                "typed_capability_plans": list(typed_capability_plans),
                "budget": tracker.to_dict(),
                "best_state": _as_json_mapping(best_state),
            },
        )
        if outcome.completed_state is not None:
            completed = outcome.completed_state
            source = build_search_artifact_source(
                completed_state=completed,
                input_module=reference.input_module,
                problem_declaration=reference.problem_declaration,
                forbidden_declarations=self.forbidden_declarations,
                extra_imports=plugin_imports,
            )
            evidence = (
                evidence_from_generated_source(
                    source=source,
                    environment_snapshot_hash=snapshot.snapshot_hash,
                    strategy_call_count=tracker.usage.strategy_calls,
                    authoring_call_count=tracker.usage.authoring_calls,
                    core_verified=True,
                )
                if completed.generated_capabilities
                else GenerationEvidence(
                    attempted=False,
                    environment_snapshot_hash=snapshot.snapshot_hash,
                    classification="no-generation-needed",
                )
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
                selected_route=tuple(
                    dict.fromkeys(
                        frame.declaration for frame in completed.application_frames
                    )
                ),
                proof_step=None,
                proof_tree=completed.proof_skeleton,
                candidates=candidates,
                substep_plans=completed.substep_plans,
                generation_evidence=evidence,
                provider_statistics=outcome.provider_statistics,
                search_outcome=outcome,
                final_state=completed,
                synthesis_designs=synthesis_designs,
                context_capsules=context_capsules,
                repair_lineage=repair_lineage,
                capability_plans=capability_plans,
                theorem_application_plans=theorem_application_plans,
                generator_briefs=generator_briefs,
                generator_results=generator_results,
                contribution_receipts=contribution_receipts,
                planner_effect_receipts=planner_effect_receipts,
                typed_capability_plans=typed_capability_plans,
            )

        proof_status = (
            ProofStatus.BUDGET_EXHAUSTED
            if outcome.status == ProofStatus.BUDGET_EXHAUSTED.value
            else ProofStatus.BLOCKED
        )
        model_failure_codes = {
            "model_provider_unavailable",
            "strategy_model_failed",
            "child_synthesis_not_verified",
        }
        failure_codes = {
            str(item.get("blocker_code")) for item in best_state.failure_memory
        }
        if (
            proof_status == ProofStatus.BLOCKED
            and self.config.model_policy == ModelPolicy.REQUIRED
            and failure_codes
            and failure_codes <= model_failure_codes
        ):
            proof_status = ProofStatus.FAILED_MODEL
        return self._failure_result(
            store=store,
            proof_status=proof_status,
            root_goal=root_goal,
            job_id=job_id,
            code=(
                "budget_exhausted"
                if proof_status == ProofStatus.BUDGET_EXHAUSTED
                else "global_frontier_exhausted"
            ),
            explanation=outcome.blocker or "global proof frontier exhausted",
            commands=commands,
            model_calls=model_calls,
            candidates=candidates,
            substep_plans=best_state.substep_plans,
            input_identity=identity.to_dict(),
            environment_snapshot=snapshot.to_dict(),
            evidence=GenerationEvidence(
                attempted=bool(model_calls),
                strategy_call_count=tracker.usage.strategy_calls,
                authoring_call_count=tracker.usage.authoring_calls,
                generated_source_hashes=tuple(
                    item.source_hash for item in best_state.generated_capabilities
                ),
                environment_snapshot_hash=snapshot.snapshot_hash,
                classification="generation-attempted-blocked",
            ),
            provider_statistics=outcome.provider_statistics,
            proof_tree=best_state.proof_skeleton,
            search_outcome=outcome,
            final_state=best_state,
            synthesis_designs=synthesis_designs,
            context_capsules=context_capsules,
            repair_lineage=repair_lineage,
            capability_plans=capability_plans,
            theorem_application_plans=theorem_application_plans,
            generator_briefs=generator_briefs,
            generator_results=generator_results,
            contribution_receipts=contribution_receipts,
            planner_effect_receipts=planner_effect_receipts,
            typed_capability_plans=typed_capability_plans,
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
        proof_tree=(),
        search_outcome=None,
        final_state: ProofState | None = None,
        synthesis_designs: Sequence[Mapping[str, Any]] = (),
        context_capsules: Sequence[Mapping[str, Any]] = (),
        repair_lineage: Sequence[Mapping[str, Any]] = (),
        capability_plans=(),
        theorem_application_plans=(),
        generator_briefs=(),
        generator_results=(),
        contribution_receipts=(),
        planner_effect_receipts=(),
        typed_capability_plans: Sequence[Mapping[str, Any]] = (),
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
                provider_statistics=provider_statistics,
                proof_tree=proof_tree or ((proof_step,) if proof_step else ()),
                search_outcome=search_outcome,
                final_state=final_state,
                synthesis_designs=synthesis_designs,
                context_capsules=context_capsules,
                repair_lineage=repair_lineage,
                capability_plans=capability_plans,
                theorem_application_plans=theorem_application_plans,
                generator_briefs=generator_briefs,
                generator_results=generator_results,
                contribution_receipts=contribution_receipts,
                planner_effect_receipts=planner_effect_receipts,
                typed_capability_plans=typed_capability_plans,
            )
        store.transition("PROOF_VERIFIED")
        classification = classify_generation(generation_evidence)
        store.transition("GENERATION_CLASSIFIED", details={"classification": classification.value})
        qualification = initial_qualification_status(self.profile)
        store.transition("PROFILE_EVALUATED", details={"qualification": qualification.value})
        reachable_generated = self._reachable_generated_declarations(final_state)
        finalized_contributions = tuple(
            replace(
                receipt,
                final_artifact_used=(
                    receipt.capability_declaration in reachable_generated
                ),
                independent_lean_passed=(
                    receipt.independent_lean_passed
                    and verification.independent_replay_passed
                ),
            )
            for receipt in contribution_receipts
        )
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
            proof_tree=tuple(proof_tree or ((proof_step,) if proof_step else ())),
            capability_planner_decisions=self._planner_decisions(substep_plans),
            substep_plans=tuple(substep_plans),
            action_provider_statistics=provider_statistics,
            theorem_candidates=tuple(candidates),
            synthesis_designs=tuple(synthesis_designs),
            context_capsules=tuple(context_capsules),
            repair_lineage=tuple(repair_lineage),
            capability_plans=tuple(capability_plans),
            theorem_application_plans=tuple(theorem_application_plans),
            generator_briefs=tuple(generator_briefs),
            generator_results=tuple(generator_results),
            contribution_receipts=finalized_contributions,
            planner_effect_receipts=tuple(planner_effect_receipts),
            typed_capability_plans=tuple(typed_capability_plans),
            generated_declarations=tuple(
                dict.fromkeys(
                    (
                        *self._generated_declarations(generation_evidence),
                        *(
                            capability.declaration
                            for capability in (
                                final_state.generated_capabilities if final_state else ()
                            )
                        ),
                    )
                )
            ),
            model_calls=tuple(model_calls),
            lean_commands=tuple(commands),
            verification=verification,
            generation_evidence=generation_evidence,
            artifact_file=str(artifact_path),
            artifact_sha256=digest,
            input_identity=identity,
            environment_snapshot=snapshot,
            expanded_state_count=getattr(search_outcome, "expanded_states", 0),
            requeued_failure_state_count=getattr(
                search_outcome, "requeued_failure_states", 0
            ),
            pruned_cycle_count=getattr(search_outcome, "pruned_cycles", 0),
            max_observed_search_depth=getattr(
                search_outcome, "max_observed_depth", 0
            ),
            application_frame_count=(
                len(final_state.application_frames) if final_state else 0
            ),
            verified_application_frame_count=(
                sum(
                    frame.status.value == "verified"
                    for frame in final_state.application_frames
                )
                if final_state
                else 0
            ),
            data_binding_count=(final_state.data_binding_count if final_state else 0),
            dependent_goal_activation_count=(
                final_state.dependent_goal_activation_count if final_state else 0
            ),
            recursive_substep_plan_count=(
                len(final_state.substep_plans) if final_state else len(tuple(substep_plans))
            ),
            generated_capability_count=(
                len(final_state.generated_capabilities) if final_state else 0
            ),
            final_frontier_size=getattr(search_outcome, "final_frontier_size", 0),
            frontier_exhaustion_receipt=getattr(
                search_outcome, "frontier_exhaustion_receipt", None
            ),
            per_goal_attempted_actions=(
                {
                    goal.goal_id: goal.attempted_actions
                    for goal in final_state.open_goals
                }
                if final_state
                else {}
            ),
            final_route_audit_receipt={
                "forbidden_declarations": list(self.forbidden_declarations),
                "transitive_audit_emitted": bool(self.forbidden_declarations),
                "passed": verification.kernel_verified,
            },
            strategy_valid_proposal_count=getattr(
                search_outcome, "strategy_valid_proposals", 0
            ),
            strategy_applied_decision_count=getattr(
                search_outcome, "strategy_applied_decisions", 0
            ),
            strategy_fallback_count=getattr(
                search_outcome, "strategy_fallbacks", 0
            ),
            strategy_rejected_count=getattr(
                search_outcome, "strategy_rejections", 0
            ),
            unused_strategy_call_count=max(
                0,
                sum(
                    bool(call.called) and call.purpose == "strategy-proposal"
                    for call in model_calls
                )
                - getattr(search_outcome, "strategy_applied_decisions", 0)
                - getattr(search_outcome, "strategy_fallbacks", 0)
                - getattr(search_outcome, "strategy_rejections", 0),
            ),
            strategy_effect_receipts=getattr(
                search_outcome, "strategy_effect_receipts", ()
            ),
            finite_candidate_count=getattr(
                search_outcome, "finite_candidate_count", 0
            ),
            finite_counterexample_count=getattr(
                search_outcome, "finite_counterexample_count", 0
            ),
            finite_certificate_count=getattr(
                search_outcome, "finite_certificate_count", 0
            ),
            capability_compiler_candidate_count=getattr(
                search_outcome, "capability_compiler_candidate_count", 0
            ),
            capability_compiler_certificate_count=getattr(
                search_outcome, "capability_compiler_certificate_count", 0
            ),
            generated_lean_check_count=getattr(
                search_outcome, "generated_lean_check_count", 0
            ),
            generated_lean_success_count=getattr(
                search_outcome, "generated_lean_success_count", 0
            ),
            capability_registration_count=getattr(
                search_outcome, "capability_registration_count", 0
            ),
            synthesis_design_count=getattr(
                search_outcome, "synthesis_design_count", len(synthesis_designs)
            ),
            context_expansion_count=getattr(
                search_outcome, "context_expansion_count", 0
            ),
            repair_authoring_count=sum(
                bool(call.called) and call.purpose == "lean-authoring-repair"
                for call in model_calls
            ),
            duplicate_candidate_rejection_count=getattr(
                search_outcome, "duplicate_candidate_rejection_count", 0
            ),
            repeated_diagnostic_count=getattr(
                search_outcome, "repeated_diagnostic_count", 0
            ),
            context_insufficient_count=getattr(
                search_outcome, "context_insufficient_count", 0
            ),
            unresolved_probe_handle_count=getattr(
                search_outcome, "unresolved_probe_handle_count", 0
            ),
            rejected_nonexecutable_design_count=getattr(
                search_outcome, "rejected_nonexecutable_design_count", 0
            ),
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
