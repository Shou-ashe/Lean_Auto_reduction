"""Recursive action execution for the global generative proof frontier.

Every theorem application and dependent re-instantiation is checked by Lean.
The runtime only moves immutable receipts, fragments, and branch-local source
between proof states.
"""

from __future__ import annotations

from dataclasses import asdict, replace
from pathlib import Path
from typing import Callable, Mapping, MutableSequence, Sequence

from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig

from .budgets import BudgetTracker
from .capability_planner import CapabilityPlanner
from .context_capsule import ContextCapsule, build_context_capsule
from .exact_closure_probe import ClosureCheck
from .finite_synthesis import FiniteSynthesisPlugin
from .goal_kind_adapters import classify_goal
from .job import GeneralJobStore
from .lean_bridge import (
    RuleInstantiationReceipt,
    RuleSlotReceipt,
    run_lean_file,
    run_rule_instantiation_probe,
)
from .model import (
    implementation_sha256,
    propose_initial_implementation,
    propose_repair,
    propose_strategy,
    validate_strategy_proposal,
)
from .models import (
    ActionDisposition,
    ApplicationFrame,
    BinderSlot,
    CandidateAction,
    FrameStatus,
    GeneratedCapability,
    GoalKind,
    ModelCallRecord,
    ModelPolicy,
    OpenGoal,
    PremiseKind,
    PremiseSlot,
    ProofGuidance,
    ProofStep,
    ProviderKind,
    ReusableFragment,
    SlotStatus,
    StrategyDecision,
    SubstepPlan,
    TheoremIndexEntry,
    stable_sha256,
)
from .premise_registry import PremiseSolverRegistry
from .proof_state import ProofState, contains_unresolved_metavariable
from .reconstruction import (
    build_authored_capability_source,
    build_frame_check_source,
    build_goal_fragment_check_source,
)
from .synthesis import (
    SynthesisDesign,
    classify_lean_diagnostic,
    record_diagnostic,
    source_window,
)
from .theorem_index import is_runtime_candidate_declaration, query_typed_goal_index


EventSink = Callable[[str, Mapping[str, object]], None]


def _same_type(first: str, second: str) -> bool:
    return " ".join(first.split()) == " ".join(second.split())


def _slot_exact_type(slot: BinderSlot | PremiseSlot) -> str | None:
    if isinstance(slot, BinderSlot):
        return slot.exact_type
    return slot.instantiated_exact_type


class RecursiveSearchRuntime:
    def __init__(
        self,
        *,
        root: Path,
        store: GeneralJobStore,
        input_module: str,
        modules: Sequence[str],
        plugin_imports: Sequence[str],
        forbidden_declarations: Sequence[str],
        tracker: BudgetTracker,
        solver_registry: PremiseSolverRegistry,
        model_policy: ModelPolicy,
        deepseek: DeepSeekConfig | None,
        lean_timeout_seconds: int,
        commands: MutableSequence[Mapping[str, object]],
        model_calls: MutableSequence[ModelCallRecord],
        event_sink: EventSink | None = None,
        finite_plugins: Sequence[FiniteSynthesisPlugin] = (),
    ):
        self.root = root.resolve()
        self.store = store
        self.input_module = input_module
        self.modules = tuple(dict.fromkeys((*modules, input_module)))
        self.plugin_imports = tuple(plugin_imports)
        self.forbidden_declarations = tuple(forbidden_declarations)
        self.tracker = tracker
        self.model_policy = model_policy
        self.deepseek = deepseek
        self.lean_timeout_seconds = lean_timeout_seconds
        self.commands = commands
        self.model_calls = model_calls
        self.event_sink = event_sink
        self._finite_plugins = {plugin.name: plugin for plugin in finite_plugins}
        self._candidate_cache: dict[str, tuple[TheoremIndexEntry, ...]] = {}
        self._data_witness_rank_cache: dict[str, tuple[str, ...]] = {}
        self._lookahead_closure_cache: dict[str, bool] = {}
        self._finite_lookahead_cache: dict[str, bool] = {}
        self._candidate_entries: dict[str, TheoremIndexEntry] = {}
        self._planning_state: ProofState | None = None
        self._last_candidates_by_goal: dict[str, tuple[TheoremIndexEntry, ...]] = {}
        self._frame_actions: dict[str, CandidateAction] = {}
        self._strategy_decisions: dict[str, StrategyDecision] = {}
        self._candidate_source_hashes: set[str] = set()
        self._synthesis_designs: dict[str, SynthesisDesign] = {}
        self._context_capsules: dict[str, ContextCapsule] = {}
        self._repair_lineage: list[Mapping[str, object]] = []
        self._client = (
            DeepSeekClient(deepseek)
            if deepseek is not None and bool(deepseek.api_key)
            else None
        )
        self.planner = CapabilityPlanner(
            solver_registry=solver_registry,
            tracker=tracker,
            checker=self.check_closure,
            finite_plugins=finite_plugins,
        )

    def _event(self, name: str, **details: object) -> None:
        if self.event_sink is not None:
            self.event_sink(name, details)

    def _record_command(self, command) -> None:
        self.commands.append(command.to_dict())

    def _record_model_call(self, record: ModelCallRecord) -> ModelCallRecord:
        enriched = replace(
            record,
            provider="deepseek",
            model=(self.deepseek.model if self.deepseek is not None else None),
        )
        self.model_calls.append(enriched)
        return enriched

    def synthesis_design_receipts(self) -> tuple[Mapping[str, object], ...]:
        return tuple(asdict(item) for item in self._synthesis_designs.values())

    def context_capsule_receipts(self) -> tuple[Mapping[str, object], ...]:
        return tuple(capsule.to_dict() for capsule in self._context_capsules.values())

    def repair_lineage_receipts(self) -> tuple[Mapping[str, object], ...]:
        return tuple(self._repair_lineage)

    def _store_design(self, design: SynthesisDesign) -> SynthesisDesign:
        previous = self._synthesis_designs.get(design.design_id)
        self._synthesis_designs[design.design_id] = design
        if previous is None:
            self.tracker.consume("synthesis_designs")
            self._event(
                "SYNTHESIS_DESIGN_CREATED",
                design_id=design.design_id,
                contract_id=design.contract_id,
                parent_goal_id=design.parent_goal_id,
                design_kind=design.design_kind,
                mode=design.mode,
            )
        elif previous.stage != design.stage or previous.status != design.status:
            self._event(
                "SYNTHESIS_DESIGN_TRANSITION",
                design_id=design.design_id,
                from_stage=previous.stage,
                to_stage=design.stage,
                status=design.status,
                terminal_reason=design.terminal_reason,
            )
        return design

    def _design_for_action(
        self,
        *,
        goal: OpenGoal,
        contract,
        action: CandidateAction,
    ) -> SynthesisDesign:
        design_id = str(action.metadata.get("design_id") or "")
        existing = self._synthesis_designs.get(design_id)
        if existing is not None:
            return existing
        mode = str(action.metadata.get("construction_mode") or "direct-authoring")
        design = SynthesisDesign.for_contract(
            contract,
            mode=mode,
            parent_goal_id=goal.goal_id,
        )
        if design_id and design.design_id != design_id:
            design = replace(design, design_id=design_id)
        design = replace(
            design,
            constructor_skeleton=(
                str(action.metadata["constructor_skeleton"])
                if action.metadata.get("constructor_skeleton")
                else None
            ),
            strategy_decision_id=(
                str(action.metadata["strategy_decision_id"])
                if action.metadata.get("strategy_decision_id")
                else None
            ),
        )
        return self._store_design(design)

    def _build_context_capsule(
        self,
        *,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        diagnostics: str | None,
        expansion_ordinal: int,
    ) -> ContextCapsule:
        capsule = build_context_capsule(
            goal=goal,
            candidates=self._last_candidates_by_goal.get(goal.goal_id, ()),
            guidance=plan.ranked_proof_guidance,
            generated_capabilities=state.generated_capabilities,
            imports=(*self.modules, *self.plugin_imports, *state.imports),
            environment_fingerprint=stable_sha256(
                {
                    "imports": goal.key.import_closure_fingerprint,
                    "capabilities": state.capability_fingerprint,
                }
            ),
            diagnostics=diagnostics,
            expansion_ordinal=expansion_ordinal,
        )
        if capsule.capsule_id not in self._context_capsules:
            self._context_capsules[capsule.capsule_id] = capsule
            self.store.write_json(
                f"work/context/{capsule.capsule_id}.json", capsule.to_dict()
            )
            self._event(
                "CONTEXT_CAPSULE_READY",
                capsule_id=capsule.capsule_id,
                goal_id=goal.goal_id,
                token_estimate=capsule.token_estimate,
                diagnostic_fingerprint=capsule.diagnostic_fingerprint,
                expansion_ordinal=expansion_ordinal,
            )
        return capsule

    def _query_index(
        self, state: ProofState, exact_type: str, *, purpose: str
    ) -> tuple[TheoremIndexEntry, ...]:
        cache_key = self._candidate_cache_key(state, exact_type)
        cached = self._candidate_cache.get(cache_key)
        if cached is not None:
            return cached
        self.tracker.consume("lean_checks")
        digest = cache_key.removeprefix("sha256:")[:20]
        try:
            entries, command = query_typed_goal_index(
                root=self.root,
                exact_goal=exact_type,
                modules=(*self.modules, *state.imports, *self.plugin_imports),
                output_path=self.store.path(f"work/index/{purpose}-{digest}.lean"),
                timeout_seconds=self.lean_timeout_seconds,
            )
        except RuntimeError:
            self._candidate_cache[cache_key] = ()
            return ()
        self._record_command(command)
        filtered = tuple(
            entry
            for entry in entries
            if entry.declaration not in self.forbidden_declarations
            and is_runtime_candidate_declaration(entry.declaration)
        )
        self.seed_candidates(state, exact_type, filtered)
        return filtered

    def dead_end(
        self, state: ProofState, goal: OpenGoal, reason: str
    ) -> ProofState | None:
        if not goal.producer_frame_id:
            return None
        try:
            frame = state.frame(goal.producer_frame_id)
        except KeyError:
            return None
        if goal.producer_slot_id:
            rebound = state.reopen_dependent_data_slot(
                frame_id=frame.frame_id,
                dependent_slot_id=goal.producer_slot_id,
            )
            if rebound is not None:
                rebound_frame = rebound.frame(frame.frame_id)
                ready_binder_slot_ids = {
                    slot.slot_id
                    for slot in rebound_frame.binder_slots
                    if slot.status == SlotStatus.READY
                }
                rebind_action = CandidateAction(
                    action_id=(
                        "dependent-data-rebind-"
                        + stable_sha256(
                            {
                                "frame": frame.frame_id,
                                "slot": goal.producer_slot_id,
                                "reason": " ".join(reason.split()),
                            }
                        ).removeprefix("sha256:")[:20]
                    ),
                    provider=ProviderKind.THEOREM,
                    disposition=ActionDisposition.DECOMPOSED,
                    goal_key=goal.key,
                    estimated_cost=0.0,
                    declaration=frame.declaration,
                )
                restored_goal = next(
                    (
                        item
                        for item in rebound.open_goals
                        if item.producer_frame_id == frame.frame_id
                        and item.producer_slot_id in ready_binder_slot_ids
                    ),
                    None,
                )
                if restored_goal is not None:
                    rebound = rebound.remember_failure(
                        action=rebind_action,
                        diagnostic=reason,
                        blocker_code="dependent_branch_exhausted_rebind",
                        goal_id=restored_goal.goal_id,
                    )
                    self._event(
                        "DATA_BINDING_REOPENED",
                        frame_id=frame.frame_id,
                        failed_slot_id=goal.producer_slot_id,
                        restored_goal_id=restored_goal.goal_id,
                        attempted_actions=restored_goal.attempted_actions,
                    )
                    return rebound
                self._event(
                    "DATA_BINDING_REOPEN_FAILED",
                    frame_id=frame.frame_id,
                    failed_slot_id=goal.producer_slot_id,
                    ready_binder_slot_ids=sorted(ready_binder_slot_ids),
                )
        action = self._frame_actions.get(frame.frame_id)
        if action is None:
            action = CandidateAction(
                action_id=frame.action_id,
                provider=ProviderKind.THEOREM,
                disposition=ActionDisposition.DECOMPOSED,
                goal_key=goal.key,
                estimated_cost=0.0,
                declaration=frame.declaration,
                guidance_id=frame.guidance_id,
            )
        return state.rollback_application_frame(
            frame_id=frame.frame_id,
            action=action,
            diagnostic=reason,
            blocker_code="child_goal_exhausted",
        )

    def _candidate_cache_key(self, state: ProofState, exact_type: str) -> str:
        return stable_sha256(
            {
                "goal": exact_type.strip(),
                "capabilities": state.capability_fingerprint,
                "imports": state.imports,
                "failures": state.normalized_failure_fingerprints,
                "forbidden": self.forbidden_declarations,
            }
        )

    @staticmethod
    def _strategy_cache_key(
        *,
        state: ProofState,
        goal: OpenGoal,
        actions: Sequence[CandidateAction],
        plan: SubstepPlan,
        remaining_model_calls: int | None = None,
    ) -> str:
        design_ids = sorted(
            str(action.metadata["design_id"])
            for action in actions
            if action.metadata.get("design_id")
        )
        return stable_sha256(
            {
                "state": state.fingerprint,
                "goal": goal.key.fingerprint,
                "goal_id": goal.goal_id,
                "actions": sorted(action.action_id for action in actions),
                "designs": design_ids,
                "plan": plan.plan_fingerprint,
                "failures": state.normalized_failure_fingerprints,
                "capabilities": state.capability_fingerprint,
                "bindings": [
                    (
                        frame.frame_id,
                        tuple(
                            (
                                slot.slot_id,
                                slot.status.value,
                                getattr(slot, "bound_declaration", None),
                            )
                            for slot in frame.binder_slots
                        ),
                    )
                    for frame in state.application_frames
                ],
                "remaining_model_calls_bucket": (
                    None
                    if remaining_model_calls is None
                    else remaining_model_calls // 2
                ),
            }
        )

    def decide_strategy(
        self,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        actions: Sequence[CandidateAction],
    ) -> StrategyDecision | None:
        """Call the strategy model only when its result can control execution."""

        if self.model_policy == ModelPolicy.DISABLED or self._client is None:
            return None
        if self.tracker.remaining("strategy_calls") == 0:
            return None
        if self.tracker.remaining("model_calls") == 0:
            return None
        key = self._strategy_cache_key(
            state=state,
            goal=goal,
            actions=actions,
            plan=plan,
            remaining_model_calls=self.tracker.remaining("model_calls"),
        )
        cached = self._strategy_decisions.get(key)
        if cached is not None:
            return cached
        self.tracker.consume("strategy_calls")
        self.tracker.consume("model_calls")
        proposal, record = propose_strategy(
            model=self._client,
            goal=goal,
            plan=plan,
            actions=actions,
        )
        record = self._record_model_call(record)
        decision = validate_strategy_proposal(
            proposal=proposal,
            state_fingerprint=state.fingerprint,
            goal=goal,
            actions=actions,
            error=record.error,
        )
        self._strategy_decisions[key] = decision
        return decision

    def seed_candidates(
        self,
        state: ProofState,
        exact_type: str,
        entries: Sequence[TheoremIndexEntry],
    ) -> None:
        filtered = tuple(
            entry
            for entry in entries
            if entry.declaration not in self.forbidden_declarations
            and is_runtime_candidate_declaration(entry.declaration)
        )
        self._candidate_cache[self._candidate_cache_key(state, exact_type)] = filtered
        for entry in filtered:
            self._candidate_entries[entry.declaration] = entry

    def candidate_lookup(
        self, state: ProofState, goal: OpenGoal
    ) -> Sequence[TheoremIndexEntry]:
        self._planning_state = state
        entries = self._query_index(state, goal.exact_type, purpose="goal")
        has_dependent_sibling = False
        if goal.producer_frame_id and goal.producer_slot_id:
            try:
                producer = state.frame(goal.producer_frame_id)
                has_dependent_sibling = any(
                    goal.producer_slot_id in slot.dependency_slot_ids
                    for slot in producer.slots
                    if slot.slot_id != goal.producer_slot_id
                )
            except KeyError:
                has_dependent_sibling = False
        if goal.kind == GoalKind.DATA and has_dependent_sibling:
            entries = self._rank_data_witnesses(state, goal, entries)
        self._last_candidates_by_goal[goal.goal_id] = tuple(entries)
        return entries

    def _rank_data_witnesses(
        self,
        state: ProofState,
        goal: OpenGoal,
        entries: Sequence[TheoremIndexEntry],
    ) -> tuple[TheoremIndexEntry, ...]:
        zero_premise = [entry for entry in entries if not entry.premises]
        if len(zero_premise) < 2:
            return tuple(entries)
        frame = state.frame(goal.producer_frame_id)
        rank_key = stable_sha256(
            {
                "frame_declaration": frame.declaration,
                "parent_exact_type": frame.parent_exact_type,
                "slot_id": goal.producer_slot_id,
                "goal": goal.exact_type,
                "candidate_ids": [entry.candidate_id for entry in entries],
                "capabilities": state.capability_fingerprint,
                "forbidden": self.forbidden_declarations,
            }
        )
        cached_order = self._data_witness_rank_cache.get(rank_key)
        if cached_order is not None:
            by_id = {entry.candidate_id: entry for entry in entries}
            return tuple(
                by_id[candidate_id]
                for candidate_id in cached_order
                if candidate_id in by_id
            )
        limit = self.tracker.budget.max_data_witness_candidates
        scored: list[tuple[tuple[int, int, int, int, str], TheoremIndexEntry]] = []
        for entry in zero_premise[:limit]:
            direct_closures = 0
            downstream_candidates = 0
            self_loop = 0
            evaluated_siblings = 0
            finite_supported_siblings = 0
            try:
                receipt = self._probe_with_temporary_binding(
                    state=state,
                    goal=goal,
                    fragment=ReusableFragment(
                        exact_type=goal.exact_type,
                        proof_term=entry.declaration,
                        declaration=entry.declaration,
                        module=entry.module,
                        imports=(entry.module,),
                        provenance=entry.provenance,
                    ),
                    purpose="lookahead",
                )
                for slot in receipt.slots:
                    if slot.status != "ready":
                        continue
                    if _same_type(slot.exact_type, frame.parent_exact_type):
                        self_loop += 1
                        continue
                    evaluated_siblings += 1
                    if self._finite_plugins:
                        lookahead_goal = OpenGoal.create(
                            goal_id=(
                                "finite-lookahead-"
                                + stable_sha256(
                                    {
                                        "slot": slot.exact_type,
                                        "candidate": entry.candidate_id,
                                    }
                                ).removeprefix("sha256:")[:16]
                            ),
                            exact_type=slot.exact_type,
                            local_context=goal.local_context,
                            import_closure_fingerprint=(
                                goal.key.import_closure_fingerprint
                            ),
                            kind=classify_goal(
                                slot.exact_type, premise_kind=slot.kind.value
                            ),
                        )
                        supported_plugins = tuple(
                            plugin
                            for plugin in self._finite_plugins.values()
                            if plugin.supports(lookahead_goal).supported
                        )
                        supported_by = tuple(
                            plugin.name for plugin in supported_plugins
                        )
                        if supported_by:
                            self._event(
                                "data_witness_lookahead_finite_support",
                                exact_type=slot.exact_type,
                                declaration=entry.declaration,
                                plugins=supported_by,
                            )
                            verified_by = tuple(
                                plugin.name
                                for plugin in supported_plugins
                                if self._finite_lookahead_closes(
                                    state=state,
                                    parent_goal=goal,
                                    goal=lookahead_goal,
                                    plugin=plugin,
                                )
                            )
                            if verified_by:
                                direct_closures += 1
                                finite_supported_siblings += 1
                                downstream_candidates += len(verified_by)
                            continue
                        # Unsupported witnesses stay in the candidate tail and
                        # remain available after verified finite branches fail.
                        continue
                    sibling = self._query_index(
                        state,
                        slot.exact_type,
                        purpose="lookahead-sibling",
                    )
                    downstream_candidates += min(8, len(sibling))
                    if any(
                        self._lookahead_candidate_closes(
                            state=state,
                            parent_goal=goal,
                            exact_type=slot.exact_type,
                            candidate=candidate,
                        )
                        for candidate in sibling[:8]
                    ):
                        direct_closures += 1
            except (KeyError, RuntimeError, TypeError, ValueError):
                self_loop += 4
            full_downstream_closure = int(
                evaluated_siblings > 0
                and self_loop == 0
                and (
                    finite_supported_siblings > 0
                    or direct_closures == evaluated_siblings
                )
            )
            input_module_penalty = int(entry.module == self.input_module)
            score = (
                full_downstream_closure,
                direct_closures,
                downstream_candidates,
                -(10 * self_loop + input_module_penalty),
                entry.declaration,
            )
            scored.append((score, entry))
            if full_downstream_closure:
                break
        ranked = [entry for _, entry in sorted(scored, key=lambda item: item[0], reverse=True)]
        ranked_ids = {entry.candidate_id for entry in ranked}
        result = tuple(
            (*ranked, *(entry for entry in entries if entry.candidate_id not in ranked_ids))
        )
        self._data_witness_rank_cache[rank_key] = tuple(
            entry.candidate_id for entry in result
        )
        return result

    def _finite_lookahead_closes(
        self,
        *,
        state: ProofState,
        parent_goal: OpenGoal,
        goal: OpenGoal,
        plugin: FiniteSynthesisPlugin,
    ) -> bool:
        """Lean-check one finite candidate before promoting a data witness.

        A plugin's ``supports`` receipt is intentionally only a typed-shape
        claim.  Data-witness ordering must not treat that claim as proof that
        the concrete candidate works for the current dependent goal.  This
        preflight uses the same source fences and independent Lean checker as
        normal capability materialization, without registering the temporary
        declaration as a reusable capability.
        """

        cache_key = stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "parent_goal": parent_goal.key.fingerprint,
                "plugin": plugin.name,
                "imports": state.imports,
                "capabilities": state.capability_fingerprint,
                "forbidden": self.forbidden_declarations,
            }
        )
        cached = self._finite_lookahead_cache.get(cache_key)
        if cached is not None:
            return cached

        digest = cache_key.removeprefix("sha256:")[:20]
        declaration_name = f"capability_{digest}"
        namespace = (
            "ComplexityReduction.Agent.GenerativeReduction.FiniteLookahead."
            f"C{digest}"
        )
        verified = False
        diagnostic = "finite synthesis plugin emitted no lookahead candidate"
        source_hash: str | None = None
        try:
            candidates = tuple(
                plugin.enumerate(
                    goal,
                    declaration_name=declaration_name,
                    limit=1,
                    counterexamples=(),
                )
            )
        except (RuntimeError, TypeError, ValueError) as error:
            candidates = ()
            diagnostic = str(error)

        for ordinal, candidate in enumerate(candidates, start=1):
            if candidate.counterexample is not None:
                diagnostic = "finite lookahead candidate failed executable semantics"
                continue
            try:
                source, _ = build_authored_capability_source(
                    input_module=self.input_module,
                    exact_type=goal.exact_type,
                    namespace=namespace,
                    declaration_name=declaration_name,
                    implementation=candidate.implementation,
                    extra_imports=(
                        *candidate.imports,
                        *self.plugin_imports,
                        *state.imports,
                    ),
                    generated_capabilities=state.generated_capabilities,
                    forbidden_declarations=self.forbidden_declarations,
                )
            except ValueError as error:
                diagnostic = str(error)
                continue
            source_hash = stable_sha256(source)
            self.tracker.consume("lean_checks")
            path = self.store.write_text(
                f"work/lookahead/finite-{digest}-{ordinal}.lean",
                source,
            )
            command = run_lean_file(
                root=self.root,
                path=path,
                timeout_seconds=self.lean_timeout_seconds,
            )
            self._record_command(command)
            if command.ok:
                verified = True
                diagnostic = ""
                break
            diagnostic = (command.stderr or command.stdout)[-4000:]

        self._finite_lookahead_cache[cache_key] = verified
        classified = classify_lean_diagnostic(diagnostic) if diagnostic else None
        self._event(
            "data_witness_lookahead_finite_check",
            exact_type=goal.exact_type,
            plugin=plugin.name,
            verified=verified,
            source_hash=source_hash,
            diagnostic_class=(classified.code if classified is not None else None),
            diagnostic_fingerprint=(
                classified.fingerprint if classified is not None else None
            ),
        )
        return verified

    def _lookahead_candidate_closes(
        self,
        *,
        state: ProofState,
        parent_goal: OpenGoal,
        exact_type: str,
        candidate: TheoremIndexEntry,
    ) -> bool:
        """Lean-check a solver-covered downstream candidate for witness ranking."""

        solved, residual = self.planner.solver_registry.coverage(
            candidate.premises,
            parent_goal.local_context,
        )
        if residual:
            return False
        cache_key = stable_sha256(
            {
                "exact_type": exact_type,
                "candidate": candidate.candidate_id,
                "local_context": parent_goal.local_context,
                "imports": state.imports,
                "capabilities": state.capability_fingerprint,
            }
        )
        cached = self._lookahead_closure_cache.get(cache_key)
        if cached is not None:
            return cached
        lookahead_goal = OpenGoal.create(
            goal_id="lookahead-" + cache_key.removeprefix("sha256:")[:16],
            exact_type=exact_type,
            local_context=parent_goal.local_context,
            import_closure_fingerprint=parent_goal.key.import_closure_fingerprint,
            kind=classify_goal(exact_type),
        )
        previous_state = self._planning_state
        self._planning_state = state
        try:
            result = self.check_closure(lookahead_goal, candidate, solved).ok
        finally:
            self._planning_state = previous_state
        self._lookahead_closure_cache[cache_key] = result
        self._event(
            "data_witness_lookahead_closure",
            exact_type=exact_type,
            declaration=candidate.declaration,
            closed=result,
        )
        return result

    def check_closure(self, goal, candidate, solved) -> ClosureCheck:
        state = self._planning_state
        if state is None:
            return ClosureCheck(ok=False, diagnostic="recursive runtime has no planning state")
        self.tracker.consume("lean_checks")
        solutions = tuple(solution for _, solution in solved)
        try:
            source, proof_term = build_goal_fragment_check_source(
                input_module=self.input_module,
                exact_type=goal.exact_type,
                candidate=candidate,
                premise_solutions=solutions,
                extra_imports=(*self.plugin_imports, *state.imports),
                generated_capabilities=state.generated_capabilities,
            )
        except ValueError as error:
            return ClosureCheck(ok=False, diagnostic=str(error))
        digest = stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "candidate": candidate.candidate_id,
                "capabilities": state.capability_fingerprint,
            }
        ).removeprefix("sha256:")[:20]
        path = self.store.write_text(f"work/closure/{digest}.lean", source)
        command = run_lean_file(
            root=self.root,
            path=path,
            timeout_seconds=self.lean_timeout_seconds,
        )
        self._record_command(command)
        if command.ok:
            return ClosureCheck(ok=True, proof_term=proof_term)
        return ClosureCheck(
            ok=False, diagnostic=(command.stderr or command.stdout)[-4000:]
        )

    def execute(
        self,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        action: CandidateAction,
    ) -> Sequence[ProofState]:
        if action.action_id in goal.attempted_actions:
            return ()
        if action.provider == ProviderKind.PLUGIN:
            return (self._execute_plugin(state, goal, action),)
        if action.provider == ProviderKind.STRUCTURAL:
            return (self._execute_structural(state, goal, plan, action),)
        if action.disposition == ActionDisposition.CLOSED:
            return (self._execute_closed(state, goal, action),)
        if action.disposition == ActionDisposition.DECOMPOSED:
            return (self._execute_decomposed(state, goal, plan, action),)
        if action.disposition == ActionDisposition.SYNTHESIS_REQUIRED:
            return (self._execute_synthesis(state, goal, plan, action),)
        return (
            self._fail_action(
                state,
                goal,
                action,
                "planner emitted a blocked action",
                "blocked_action",
            ),
        )

    def _execute_structural(
        self,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        action: CandidateAction,
    ) -> ProofState:
        if state.depth >= self.tracker.budget.max_structural_depth:
            return self._fail_action(
                state,
                goal,
                action,
                "maximum structural decomposition depth reached",
                "structural_depth_exhausted",
            )
        contract = plan.construction_contract
        design = None
        if contract is not None:
            design = self._design_for_action(
                goal=goal, contract=contract, action=action
            )
            design = self._store_design(
                design.transition(
                    "materializing",
                    status="materializing",
                    constructor_skeleton=(
                        str(action.metadata["constructor_skeleton"])
                        if action.metadata.get("constructor_skeleton")
                        else design.constructor_skeleton
                    ),
                )
            )
        failures_before = len(state.failure_memory)
        child = self._execute_decomposed(state, goal, plan, action)
        if design is not None:
            if len(child.failure_memory) > failures_before:
                self._store_design(
                    design.transition(
                        "lean-failed",
                        status="abandoned",
                        terminal_reason="typed structural rule instantiation failed",
                    )
                )
            else:
                staged = tuple(
                    item.goal_id
                    for item in child.open_goals
                    if item.producer_frame_id
                    and item.parent_rule == action.declaration
                )
                self._store_design(
                    design.transition(
                        "materializing",
                        status="materializing",
                        staged_goal_ids=staged,
                    )
                )
        return child

    def _fail_action(
        self,
        state: ProofState,
        goal: OpenGoal,
        action: CandidateAction,
        diagnostic: str,
        blocker_code: str,
    ) -> ProofState:
        state = state.mark_action_attempted(goal.goal_id, action.action_id)
        return state.remember_failure(
            action=action,
            diagnostic=diagnostic,
            blocker_code=blocker_code,
            goal_id=goal.goal_id,
        )

    def _execute_closed(
        self, state: ProofState, goal: OpenGoal, action: CandidateAction
    ) -> ProofState:
        if not action.lean_verified or not action.proof_term:
            return self._fail_action(
                state,
                goal,
                action,
                "closed action lacks a Lean-verified proof term",
                "unverified_closed_action",
            )
        state = state.mark_action_attempted(goal.goal_id, action.action_id)
        entry = self._candidate_entries.get(action.declaration or "")
        existing = next(
            (
                fragment
                for fragment in (
                    *state.completed_fragments,
                    *state.verified_frame_fragments,
                )
                if fragment.lean_verified
                and _same_type(fragment.exact_type, goal.exact_type)
                and fragment.proof_term.strip() == action.proof_term.strip()
            ),
            None,
        )
        fragment = existing or ReusableFragment(
            exact_type=goal.exact_type,
            proof_term=action.proof_term,
            declaration=action.declaration,
            module=(entry.module if entry is not None else None),
            imports=((entry.module,) if entry is not None else ()),
            provenance=action.provenance,
            lean_verified=True,
        )
        state = state.close_goal(
            goal_id=goal.goal_id,
            action=action,
            fragment=fragment,
            step=ProofStep(
                action_id=action.action_id,
                provider=action.provider,
                disposition=action.disposition,
                goal_id=goal.goal_id,
                exact_type=goal.exact_type,
                declaration=action.declaration,
            ),
        )
        self._event("GOAL_CLOSED", goal_id=goal.goal_id, action_id=action.action_id)
        if goal.producer_frame_id and goal.producer_slot_id:
            return self._fill_frame_slot(
                state,
                frame_id=goal.producer_frame_id,
                slot_id=goal.producer_slot_id,
                fragment=fragment,
                attempted_actions=tuple(
                    dict.fromkeys((*goal.attempted_actions, action.action_id))
                ),
            )
        return state

    def _guidance_for(
        self, plan: SubstepPlan, action: CandidateAction
    ) -> ProofGuidance | None:
        return next(
            (
                guidance
                for guidance in plan.ranked_proof_guidance
                if guidance.guidance_id == action.guidance_id
            ),
            None,
        )

    def _execute_decomposed(
        self,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        action: CandidateAction,
    ) -> ProofState:
        guidance = self._guidance_for(plan, action)
        if guidance is None or not action.declaration:
            return self._fail_action(
                state,
                goal,
                action,
                "theorem action lost its typed guidance",
                "missing_guidance",
            )
        residual_types = tuple(item.exact_type for item in guidance.residual_obligations)
        if len(residual_types) == 1 and _same_type(residual_types[0], goal.exact_type):
            return state.prune_non_progressing_action(
                goal_id=goal.goal_id,
                action=action,
                reason="theorem application reproduces the parent goal without a binding delta",
            )
        state = state.mark_action_attempted(goal.goal_id, action.action_id)
        try:
            self.tracker.consume("application_frames")
            receipt, command = self._run_rule_probe(
                state=state,
                declaration=action.declaration,
                exact_target=goal.exact_type,
                assignments={},
                purpose="decompose",
            )
            self._record_command(command)
            frame = self._initial_frame(state, goal, action, guidance, receipt)
            active_goals = self._goals_for_frame(
                state=state,
                frame=frame,
                previous_goals=(),
            )
            if self._non_progressing_frame(goal, frame, active_goals):
                return state.prune_non_progressing_action(
                    goal_id=goal.goal_id,
                    action=action,
                    reason="Lean rule instantiation made no typed progress",
                )
            self._frame_actions[frame.frame_id] = action
            state = state.add_application_frame(
                goal_id=goal.goal_id,
                action=action,
                guidance=guidance,
                frame=frame,
                activated_goals=active_goals,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=action.provider,
                    disposition=action.disposition,
                    goal_id=goal.goal_id,
                    exact_type=goal.exact_type,
                    declaration=action.declaration,
                    status="decomposed",
                ),
            )
            self._event(
                "GOAL_DECOMPOSED",
                goal_id=goal.goal_id,
                frame_id=frame.frame_id,
                declaration=frame.declaration,
                active_goal_count=len(active_goals),
            )
            return state
        except (RuntimeError, TypeError, ValueError) as error:
            return self._fail_action(
                state,
                goal,
                action,
                str(error),
                "rule_instantiation_failed",
            )

    def _run_rule_probe(
        self,
        *,
        state: ProofState,
        declaration: str,
        exact_target: str,
        assignments: Mapping[int, ReusableFragment],
        purpose: str,
    ):
        self.tracker.consume("lean_checks")
        self.tracker.consume("dependent_reinstantiations")
        digest = stable_sha256(
            {
                "declaration": declaration,
                "target": exact_target,
                "assignments": [
                    (
                        ordinal,
                        fragment.exact_type,
                        fragment.declaration,
                        fragment.source_hash,
                        stable_sha256(fragment.proof_term),
                    )
                    for ordinal, fragment in sorted(assignments.items())
                ],
                "capabilities": state.capability_fingerprint,
            }
        ).removeprefix("sha256:")[:20]
        return run_rule_instantiation_probe(
            root=self.root,
            modules=(*self.modules, *state.imports, *self.plugin_imports),
            declaration=declaration,
            exact_target=exact_target,
            assignments=assignments,
            generated_capabilities=state.generated_capabilities,
            output_path=self.store.path(f"work/rules/{purpose}-{digest}.lean"),
            timeout_seconds=self.lean_timeout_seconds,
        )

    def _probe_with_temporary_binding(
        self,
        *,
        state: ProofState,
        goal: OpenGoal,
        fragment: ReusableFragment,
        purpose: str,
    ) -> RuleInstantiationReceipt:
        if not goal.producer_frame_id or not goal.producer_slot_id:
            raise ValueError("data lookahead requires a producer frame slot")
        frame = state.frame(goal.producer_frame_id)
        ordinal = next(
            slot.ordinal for slot in frame.slots if slot.slot_id == goal.producer_slot_id
        )
        assignments = self._frame_assignments(frame)
        assignments[ordinal] = fragment
        receipt, command = self._run_rule_probe(
            state=state,
            declaration=frame.declaration,
            exact_target=frame.parent_exact_type,
            assignments=assignments,
            purpose=purpose,
        )
        self._record_command(command)
        return receipt

    def _initial_frame(
        self,
        state: ProofState,
        goal: OpenGoal,
        action: CandidateAction,
        guidance: ProofGuidance,
        receipt: RuleInstantiationReceipt,
    ) -> ApplicationFrame:
        frame_digest = stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "action": action.action_id,
                "declaration": action.declaration,
                "receipt": receipt.receipt_hash,
            }
        )
        frame_id = f"frame-{frame_digest.removeprefix('sha256:')[:20]}"
        binders: list[BinderSlot] = []
        premises: list[PremiseSlot] = []
        for slot in receipt.slots:
            slot_id = f"{frame_id}:slot:{slot.ordinal}"
            dependencies = tuple(
                f"{frame_id}:slot:{ordinal}" for ordinal in slot.dependency_ordinals
            )
            status = SlotStatus(slot.status)
            if slot.kind == PremiseKind.DATA:
                binders.append(
                    BinderSlot(
                        slot_id=slot_id,
                        ordinal=slot.ordinal,
                        binder_name=f"slot{slot.ordinal}",
                        binder_kind=slot.kind,
                        exact_type=slot.exact_type,
                        dependency_slot_ids=dependencies,
                        status=status,
                        type_template_receipt=stable_sha256(
                            {"type": slot.exact_type, "hash": slot.type_hash}
                        ),
                    )
                )
            else:
                premises.append(
                    PremiseSlot(
                        slot_id=slot_id,
                        ordinal=slot.ordinal,
                        premise_kind=slot.kind,
                        type_template_receipt=stable_sha256(
                            {"type": slot.exact_type, "hash": slot.type_hash}
                        ),
                        dependency_slot_ids=dependencies,
                        instantiated_exact_type=(
                            slot.exact_type if status != SlotStatus.DORMANT else None
                        ),
                        child_goal_id=f"goal-{frame_id}-{slot.ordinal}",
                        status=status,
                    )
                )
        frame_status = (
            FrameStatus.ACTIVE
            if any(slot.status == SlotStatus.READY for slot in (*binders, *premises))
            else FrameStatus.WAITING_BINDINGS
        )
        entry = self._candidate_entries.get(action.declaration or "")
        return ApplicationFrame(
            frame_id=frame_id,
            parent_goal_id=goal.goal_id,
            parent_exact_type=goal.exact_type,
            parent_local_context=goal.local_context,
            parent_import_closure_fingerprint=goal.key.import_closure_fingerprint,
            parent_kind=goal.kind,
            parent_attempted_actions=tuple(
                dict.fromkeys((*goal.attempted_actions, action.action_id))
            ),
            parent_depth=state.depth,
            action_id=action.action_id,
            declaration=action.declaration or guidance.candidate_declaration,
            declaration_module=(entry.module if entry is not None else guidance.declaration_provenance),
            guidance_id=guidance.guidance_id,
            application_skeleton=guidance.application_skeleton,
            binder_slots=tuple(binders),
            premise_slots=tuple(premises),
            status=frame_status,
            lean_receipt_hash=receipt.receipt_hash,
            parent_producer_frame_id=goal.producer_frame_id,
            parent_producer_slot_id=goal.producer_slot_id,
        )

    def _goals_for_frame(
        self,
        *,
        state: ProofState,
        frame: ApplicationFrame,
        previous_goals: Sequence[OpenGoal],
    ) -> tuple[OpenGoal, ...]:
        previous_by_slot = {
            goal.producer_slot_id: goal for goal in previous_goals if goal.producer_slot_id
        }
        goals: list[OpenGoal] = []
        for slot in frame.slots:
            if slot.status != SlotStatus.READY:
                continue
            exact_type = _slot_exact_type(slot)
            if not exact_type or contains_unresolved_metavariable(exact_type):
                raise ValueError("ready frame slot contains an unresolved Lean metavariable")
            existing = previous_by_slot.get(slot.slot_id)
            if existing is not None and _same_type(existing.exact_type, exact_type):
                goals.append(existing)
                continue
            premise_kind = (
                slot.binder_kind.value
                if isinstance(slot, BinderSlot)
                else slot.premise_kind.value
            )
            goals.append(
                OpenGoal.create(
                    goal_id=f"goal-{frame.frame_id}-{slot.ordinal}",
                    exact_type=exact_type,
                    local_context=frame.parent_local_context,
                    import_closure_fingerprint=(
                        frame.parent_import_closure_fingerprint
                    ),
                    parent_rule=frame.declaration,
                    producer_frame_id=frame.frame_id,
                    producer_slot_id=slot.slot_id,
                    dependency_slot_ids=slot.dependency_slot_ids,
                    ready=True,
                    kind=classify_goal(exact_type, premise_kind=premise_kind),
                )
            )
        return tuple(goals)

    def _non_progressing_frame(
        self,
        parent: OpenGoal,
        frame: ApplicationFrame,
        goals: Sequence[OpenGoal],
    ) -> bool:
        if len(goals) != 1:
            return False
        if any(slot.status == SlotStatus.DORMANT for slot in frame.slots):
            return False
        return _same_type(goals[0].exact_type, parent.exact_type)

    def _frame_assignments(
        self, frame: ApplicationFrame
    ) -> dict[int, ReusableFragment]:
        assignments: dict[int, ReusableFragment] = {}
        for slot in frame.slots:
            if slot.status not in {SlotStatus.BOUND, SlotStatus.VERIFIED}:
                continue
            if isinstance(slot, BinderSlot):
                if slot.bound_term is None:
                    continue
                assignments[slot.ordinal] = ReusableFragment(
                    exact_type=slot.exact_type,
                    proof_term=slot.bound_term,
                    declaration=slot.bound_declaration,
                    module=slot.module,
                    imports=slot.imports,
                    provenance=slot.provenance or "verified-fragment",
                )
            elif slot.instantiated_exact_type and slot.proof_term:
                assignments[slot.ordinal] = ReusableFragment(
                    exact_type=slot.instantiated_exact_type,
                    proof_term=slot.proof_term,
                    declaration=slot.declaration,
                    module=slot.module,
                    imports=slot.imports,
                    provenance=slot.provenance or "verified-fragment",
                )
        return assignments

    def _refresh_frame(
        self,
        frame: ApplicationFrame,
        receipt: RuleInstantiationReceipt,
        assignments: Mapping[int, ReusableFragment],
        attempted_actions: Mapping[int, tuple[str, ...]] | None = None,
    ) -> ApplicationFrame:
        attempted_actions = attempted_actions or {}
        old_by_ordinal = {slot.ordinal: slot for slot in frame.slots}
        binders: list[BinderSlot] = []
        premises: list[PremiseSlot] = []
        for item in receipt.slots:
            old = old_by_ordinal[item.ordinal]
            fragment = assignments.get(item.ordinal)
            status = SlotStatus.BOUND if fragment is not None else SlotStatus(item.status)
            dependencies = old.dependency_slot_ids or tuple(
                f"{frame.frame_id}:slot:{ordinal}"
                for ordinal in item.dependency_ordinals
            )
            template = stable_sha256({"type": item.exact_type, "hash": item.type_hash})
            if item.kind == PremiseKind.DATA:
                binders.append(
                    BinderSlot(
                        slot_id=old.slot_id,
                        ordinal=item.ordinal,
                        binder_name=(
                            old.binder_name if isinstance(old, BinderSlot) else f"slot{item.ordinal}"
                        ),
                        binder_kind=item.kind,
                        exact_type=(fragment.exact_type if fragment else item.exact_type),
                        dependency_slot_ids=dependencies,
                        bound_term=(fragment.proof_term if fragment else None),
                        bound_declaration=(fragment.declaration if fragment else None),
                        module=(fragment.module if fragment else None),
                        imports=(fragment.imports if fragment else ()),
                        provenance=(fragment.provenance if fragment else None),
                        attempted_actions=attempted_actions.get(
                            item.ordinal, old.attempted_actions
                        ),
                        status=status,
                        type_template_receipt=template,
                    )
                )
            else:
                premises.append(
                    PremiseSlot(
                        slot_id=old.slot_id,
                        ordinal=item.ordinal,
                        premise_kind=item.kind,
                        type_template_receipt=template,
                        dependency_slot_ids=dependencies,
                        instantiated_exact_type=(
                            fragment.exact_type
                            if fragment
                            else item.exact_type
                            if status != SlotStatus.DORMANT
                            else None
                        ),
                        child_goal_id=(
                            old.child_goal_id
                            if isinstance(old, PremiseSlot)
                            else f"goal-{frame.frame_id}-{item.ordinal}"
                        ),
                        proof_term=(fragment.proof_term if fragment else None),
                        declaration=(fragment.declaration if fragment else None),
                        module=(fragment.module if fragment else None),
                        imports=(fragment.imports if fragment else ()),
                        provenance=(fragment.provenance if fragment else None),
                        attempted_actions=attempted_actions.get(
                            item.ordinal, old.attempted_actions
                        ),
                        status=status,
                    )
                )
        all_slots = (*binders, *premises)
        if all(slot.status in {SlotStatus.BOUND, SlotStatus.VERIFIED} for slot in all_slots):
            status = FrameStatus.SATURATED
        elif any(slot.status == SlotStatus.READY for slot in all_slots):
            status = FrameStatus.ACTIVE
        else:
            status = FrameStatus.WAITING_BINDINGS
        return replace(
            frame,
            binder_slots=tuple(binders),
            premise_slots=tuple(premises),
            status=status,
            lean_receipt_hash=receipt.receipt_hash,
        )

    def _fill_frame_slot(
        self,
        state: ProofState,
        *,
        frame_id: str,
        slot_id: str,
        fragment: ReusableFragment,
        attempted_actions: tuple[str, ...] = (),
    ) -> ProofState:
        frame = state.frame(frame_id)
        slot = next(item for item in frame.slots if item.slot_id == slot_id)
        exact_type = _slot_exact_type(slot)
        if exact_type is None or not _same_type(exact_type, fragment.exact_type):
            raise ValueError("child fragment does not match its producer frame slot")
        assignments = self._frame_assignments(frame)
        assignments[slot.ordinal] = fragment
        receipt, command = self._run_rule_probe(
            state=state,
            declaration=frame.declaration,
            exact_target=frame.parent_exact_type,
            assignments=assignments,
            purpose="refresh",
        )
        self._record_command(command)
        refreshed = self._refresh_frame(
            frame,
            receipt,
            assignments,
            attempted_actions={slot.ordinal: attempted_actions},
        )
        previous = tuple(
            goal for goal in state.open_goals if goal.producer_frame_id == frame_id
        )
        frame_goals = self._goals_for_frame(
            state=state, frame=refreshed, previous_goals=previous
        )
        other_goals = tuple(
            goal for goal in state.open_goals if goal.producer_frame_id != frame_id
        )
        old_ready = {
            item.slot_id for item in frame.slots if item.status == SlotStatus.READY
        }
        new_ready = {
            item.slot_id for item in refreshed.slots if item.status == SlotStatus.READY
        }
        activated = len(new_ready - old_ready)
        state = state.refresh_frame_and_goals(
            frame=refreshed,
            goals=(*other_goals, *frame_goals),
            activated_goal_count=activated,
            data_binding_delta=int(isinstance(slot, BinderSlot)),
        )
        self._event(
            "BINDER_BOUND" if isinstance(slot, BinderSlot) else "GOAL_CLOSED",
            frame_id=frame_id,
            slot_id=slot_id,
            declaration=fragment.declaration,
        )
        for activated_goal in frame_goals:
            if activated_goal.producer_slot_id in new_ready - old_ready:
                self._event(
                    "DEPENDENT_GOAL_ACTIVATED",
                    frame_id=frame_id,
                    goal_id=activated_goal.goal_id,
                    exact_type=activated_goal.exact_type,
                )
        if refreshed.status == FrameStatus.SATURATED:
            self._event("FRAME_SATURATED", frame_id=frame_id)
            return self._verify_frame(state, refreshed)
        return state

    def _verify_frame(
        self, state: ProofState, frame: ApplicationFrame
    ) -> ProofState:
        assignments = self._frame_assignments(frame)
        self.tracker.consume("lean_checks")
        self.tracker.consume("frame_verification_checks")
        source, proof_term = build_frame_check_source(
            input_module=self.input_module,
            frame=frame,
            slot_fragments=assignments,
            generated_capabilities=state.generated_capabilities,
            extra_imports=(*self.plugin_imports, *state.imports),
        )
        path = self.store.write_text(
            f"work/frames/{frame.frame_id.removeprefix('frame-')}.lean", source
        )
        command = run_lean_file(
            root=self.root,
            path=path,
            timeout_seconds=self.lean_timeout_seconds,
        )
        self._record_command(command)
        action = self._frame_actions.get(frame.frame_id)
        if not command.ok:
            if action is not None and action.metadata.get("design_id"):
                design = self._synthesis_designs.get(str(action.metadata["design_id"]))
                if design is not None:
                    classified = classify_lean_diagnostic(
                        command.stderr or command.stdout
                    )
                    self._store_design(
                        record_diagnostic(design, classified).transition(
                            "lean-failed",
                            status="abandoned",
                            terminal_reason="structural frame failed final Lean verification",
                        )
                    )
            if action is None:
                raise RuntimeError(command.stderr or command.stdout)
            return state.rollback_application_frame(
                frame_id=frame.frame_id,
                action=action,
                diagnostic=(command.stderr or command.stdout)[-4000:],
            )
        imports = tuple(
            dict.fromkeys(
                (
                    *((frame.declaration_module,) if frame.declaration_module else ()),
                    *(module for fragment in assignments.values() for module in fragment.imports),
                    *(fragment.module for fragment in assignments.values() if fragment.module),
                )
            )
        )
        fragment = ReusableFragment(
            exact_type=frame.parent_exact_type,
            proof_term=proof_term,
            declaration=None,
            module=frame.declaration_module,
            imports=imports,
            provenance="verified-application-frame",
            lean_verified=True,
            source_hash=stable_sha256(source),
        )
        verified = replace(
            frame,
            result_proof_term=proof_term,
            status=FrameStatus.VERIFIED,
            lean_receipt_hash=stable_sha256(command.to_dict()),
        )
        state = state.add_verified_frame_fragment(frame=verified, fragment=fragment)
        if action is not None and action.metadata.get("design_id"):
            design = self._synthesis_designs.get(str(action.metadata["design_id"]))
            if design is not None:
                self._store_design(
                    design.transition(
                        "verified",
                        status="verified",
                        verified_capabilities=(
                            *design.verified_capabilities,
                            frame.frame_id,
                        ),
                    )
                )
        self._event("FRAME_VERIFIED", frame_id=frame.frame_id)
        if frame.parent_producer_frame_id and frame.parent_producer_slot_id:
            return self._fill_frame_slot(
                state,
                frame_id=frame.parent_producer_frame_id,
                slot_id=frame.parent_producer_slot_id,
                fragment=fragment,
                attempted_actions=frame.parent_attempted_actions,
            )
        return state

    def _execute_plugin(
        self,
        state: ProofState,
        goal: OpenGoal,
        action: CandidateAction,
    ) -> ProofState:
        state = state.mark_action_attempted(goal.goal_id, action.action_id)
        plugin_name = str(action.metadata.get("plugin_name") or "")
        plugin = self._finite_plugins.get(plugin_name)
        if plugin is None:
            return state.remember_failure(
                action=action,
                diagnostic=f"finite synthesis plugin is unavailable: {plugin_name}",
                blocker_code="finite_plugin_unavailable",
                goal_id=goal.goal_id,
            )
        support = plugin.supports(goal)
        if not support.supported:
            return state.remember_failure(
                action=action,
                diagnostic=support.reason,
                blocker_code="finite_plugin_support_stale",
                goal_id=goal.goal_id,
            )
        digest = stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "action": action.action_id,
                "plugin": plugin_name,
                "capabilities": state.capability_fingerprint,
            }
        ).removeprefix("sha256:")[:20]
        declaration_name = f"capability_{digest}"
        namespace = (
            "ComplexityReduction.Agent.GenerativeReduction.GeneratedCapabilities."
            f"C{digest}"
        )
        remaining = self.tracker.remaining("finite_candidates")
        limit = min(
            self.tracker.budget.max_finite_candidates,
            remaining if remaining is not None else self.tracker.budget.max_finite_candidates,
        )
        candidates = tuple(
            plugin.enumerate(
                goal,
                declaration_name=declaration_name,
                limit=limit,
                counterexamples=(),
            )
        )
        diagnostics = "finite synthesis plugin emitted no candidate"
        for ordinal, candidate in enumerate(candidates, start=1):
            self.tracker.consume("finite_candidates")
            self._event(
                "FINITE_CANDIDATE_CHECKED",
                goal_id=goal.goal_id,
                action_id=action.action_id,
                plugin=plugin_name,
                witness_id=candidate.witness_id,
                executable_status=candidate.executable_status,
                check_receipt=dict(candidate.check_receipt),
            )
            if candidate.counterexample is not None:
                self.tracker.consume("finite_counterexamples")
                self._event(
                    "FINITE_COUNTEREXAMPLE_FOUND",
                    goal_id=goal.goal_id,
                    witness_id=candidate.witness_id,
                    counterexample=dict(candidate.counterexample),
                )
                diagnostics = "finite candidate was rejected by executable semantics"
                continue
            try:
                source, declaration = build_authored_capability_source(
                    input_module=self.input_module,
                    exact_type=goal.exact_type,
                    namespace=namespace,
                    declaration_name=declaration_name,
                    implementation=candidate.implementation,
                    extra_imports=(
                        *candidate.imports,
                        *self.plugin_imports,
                        *state.imports,
                    ),
                    generated_capabilities=state.generated_capabilities,
                    forbidden_declarations=self.forbidden_declarations,
                )
            except ValueError as error:
                diagnostics = str(error)
                continue
            source_hash = stable_sha256(source)
            if source_hash in self._candidate_source_hashes:
                self.tracker.consume("duplicate_candidate_rejections")
                self._event(
                    "CANDIDATE_DEDUPLICATED",
                    goal_id=goal.goal_id,
                    source_hash=source_hash,
                    witness_id=candidate.witness_id,
                )
                diagnostics = "finite plugin repeated a previously checked source"
                continue
            self._candidate_source_hashes.add(source_hash)
            self.tracker.consume("lean_checks")
            self.tracker.consume("generated_lean_checks")
            self.tracker.consume("generated_files")
            self.tracker.consume("synthesis_materializations")
            path = self.store.write_text(
                "work/generated/"
                f"{digest}-finite-{ordinal}-{source_hash.removeprefix('sha256:')[:12]}.lean",
                source,
            )
            command = run_lean_file(
                root=self.root,
                path=path,
                timeout_seconds=self.lean_timeout_seconds,
            )
            self._record_command(command)
            if not command.ok:
                diagnostics = (command.stderr or command.stdout)[-4000:]
                continue
            self.tracker.consume("generated_lean_successes")
            self.tracker.consume("finite_certificates")
            self.tracker.consume("capability_registrations")
            implementation = candidate.implementation.strip()
            capability = GeneratedCapability(
                capability_id=f"capability-{digest}",
                exact_type=goal.exact_type,
                declaration=declaration,
                namespace=namespace,
                implementation=implementation,
                source_hash=source_hash,
                action_id=action.action_id,
                provenance=f"finite-synthesis-plugin:{plugin_name}",
            )
            fragment = ReusableFragment(
                exact_type=goal.exact_type,
                proof_term=declaration,
                declaration=declaration,
                imports=tuple(candidate.imports),
                provenance=f"finite-synthesis-plugin:{plugin_name}",
                lean_verified=True,
                source_hash=source_hash,
            )
            state = state.add_generated_capability(capability, fragment)
            self.planner.invalidate_for_new_capability(state.capability_fingerprint)
            state = state.close_goal(
                goal_id=goal.goal_id,
                action=action,
                fragment=fragment,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=ProviderKind.PLUGIN,
                    disposition=ActionDisposition.CLOSED,
                    goal_id=goal.goal_id,
                    exact_type=goal.exact_type,
                    declaration=declaration,
                    solver=plugin_name,
                ),
            )
            self._event(
                "FINITE_CERTIFICATE_MATERIALIZED",
                goal_id=goal.goal_id,
                witness_id=candidate.witness_id,
                declaration=declaration,
                source_hash=source_hash,
            )
            self._event(
                "GENERATED_CAPABILITY_REGISTERED",
                goal_id=goal.goal_id,
                declaration=declaration,
                source_hash=source_hash,
                provider=plugin_name,
            )
            if goal.producer_frame_id and goal.producer_slot_id:
                return self._fill_frame_slot(
                    state,
                    frame_id=goal.producer_frame_id,
                    slot_id=goal.producer_slot_id,
                    fragment=fragment,
                    attempted_actions=tuple(
                        dict.fromkeys((*goal.attempted_actions, action.action_id))
                    ),
                )
            return state
        return state.remember_failure(
            action=action,
            diagnostic=diagnostics,
            blocker_code="finite_synthesis_not_verified",
            goal_id=goal.goal_id,
        )

    def _execute_synthesis(
        self,
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        action: CandidateAction,
    ) -> ProofState:
        state = state.mark_action_attempted(goal.goal_id, action.action_id)
        contract = plan.construction_contract
        if contract is None or contract.contract_id != action.contract_id:
            return state.remember_failure(
                action=action,
                diagnostic="synthesis action lost its exact construction contract",
                blocker_code="missing_construction_contract",
                goal_id=goal.goal_id,
            )
        if self.model_policy == ModelPolicy.DISABLED:
            return state.remember_failure(
                action=action,
                diagnostic="child capability authoring is disabled",
                blocker_code="authoring_disabled",
                goal_id=goal.goal_id,
            )
        if self._client is None:
            return state.remember_failure(
                action=action,
                diagnostic="configured model provider is unavailable",
                blocker_code="model_provider_unavailable",
                goal_id=goal.goal_id,
            )
        design = self._design_for_action(goal=goal, contract=contract, action=action)
        if design.design_kind == "constructor-first":
            design = self._store_design(
                design.transition(
                    "abandoned",
                    status="abandoned",
                    terminal_reason=(
                        "constructor-first is executable only through a Lean-typed "
                        "structural action"
                    ),
                )
            )
            return state.remember_failure(
                action=action,
                diagnostic=design.terminal_reason or "structural design unavailable",
                blocker_code="structural_design_unavailable",
                goal_id=goal.goal_id,
            )

        mode = design.mode
        helper_obligation = (
            min(contract.residual_obligations, key=lambda item: item.estimated_cost)
            if design.design_kind in {"helper-first", "theorem-composition"}
            and contract.residual_obligations
            else None
        )
        if design.design_kind in {"helper-first", "theorem-composition"} and helper_obligation is None:
            design = self._store_design(
                design.transition(
                    "abandoned",
                    status="abandoned",
                    terminal_reason="helper-first design has no exact residual helper goal",
                )
            )
            return state.remember_failure(
                action=action,
                diagnostic=design.terminal_reason or "helper design unavailable",
                blocker_code="helper_design_unavailable",
                goal_id=goal.goal_id,
            )

        authored_type = (
            helper_obligation.exact_type if helper_obligation is not None else goal.exact_type
        )
        selected_contract = replace(
            contract,
            exact_expected_lean_type=authored_type,
            allowed_construction_modes=(mode,),
            residual_obligations=(
                () if helper_obligation is not None else contract.residual_obligations
            ),
        )
        digest = stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "action": action.action_id,
                "mode": mode,
                "design": design.design_id,
                "authored_type": authored_type,
                "capabilities": state.capability_fingerprint,
            }
        ).removeprefix("sha256:")[:20]
        declaration_name = (
            f"helper_{digest}" if helper_obligation is not None else f"capability_{digest}"
        )
        namespace = (
            "ComplexityReduction.Agent.GenerativeReduction.GeneratedCapabilities."
            f"C{digest}"
        )
        diagnostics: str | None = None
        classified = None
        previous_implementation: str | None = None
        previous_source: str | None = None
        previous_implementation_hash: str | None = None
        failed_source_hashes: list[str] = []
        attempts = min(
            self.tracker.budget.max_authoring_attempts_per_stage,
            1 + self.tracker.budget.max_repairs_per_design,
        )
        candidate_modules = tuple(
            dict.fromkeys(
                entry.module
                for entry in self._last_candidates_by_goal.get(goal.goal_id, ())
            )
        )
        authored_goal = goal
        if helper_obligation is not None:
            authored_goal = OpenGoal.create(
                goal_id=f"{goal.goal_id}:{design.design_id}:helper",
                exact_type=authored_type,
                local_context=goal.local_context,
                import_closure_fingerprint=goal.key.import_closure_fingerprint,
                parent_rule=goal.parent_rule,
                kind=classify_goal(authored_type),
            )
            helper_candidates = self._query_index(
                state, authored_type, purpose="helper-context"
            )
            self._last_candidates_by_goal[authored_goal.goal_id] = helper_candidates
            candidate_modules = tuple(
                dict.fromkeys((*candidate_modules, *(item.module for item in helper_candidates)))
        )

        for attempt in range(attempts):
            if attempt > self.tracker.budget.max_context_expansions_per_design:
                design = self._store_design(
                    design.transition(
                        "abandoned",
                        status="abandoned",
                        terminal_reason="context expansion budget exhausted for design",
                    )
                )
                break
            if attempt > 0:
                self.tracker.consume("context_expansions")
            capsule = self._build_context_capsule(
                state=state,
                goal=authored_goal,
                plan=plan,
                diagnostics=diagnostics,
                expansion_ordinal=attempt,
            )
            design = self._store_design(
                design.transition(
                    "context-ready",
                    status="context-ready",
                    context_capsule_id=capsule.capsule_id,
                    staged_goal_ids=(
                        (authored_goal.goal_id,)
                        if helper_obligation is not None
                        else design.staged_goal_ids
                    ),
                )
            )
            self.tracker.consume("authoring_calls")
            self.tracker.consume("model_calls")
            design = self._store_design(
                design.transition("materializing", status="materializing")
            )
            if previous_implementation is None:
                proposal, record = propose_initial_implementation(
                    model=self._client,
                    contract=selected_contract,
                    guidance=plan.ranked_proof_guidance,
                    context_capsule=capsule,
                    required_declaration=declaration_name,
                    design=asdict(design),
                )
            else:
                if previous_implementation_hash is None or classified is None:
                    raise RuntimeError("repair state lost its base implementation receipt")
                proposal, record = propose_repair(
                    model=self._client,
                    contract=selected_contract,
                    guidance=plan.ranked_proof_guidance,
                    context_capsule=capsule,
                    required_declaration=declaration_name,
                    design=asdict(design),
                    previous_implementation=previous_implementation,
                    base_sha256=previous_implementation_hash,
                    diagnostic_classification=classified.code,
                    normalized_diagnostics=classified.normalized,
                    source_window=source_window(previous_source or "", classified),
                    failed_source_hashes=tuple(failed_source_hashes),
                )
            record = self._record_model_call(record)
            if proposal is None:
                diagnostics = record.error or "authoring protocol failed"
                continue
            implementation = (proposal.implementation or "").strip()
            implementation_hash = implementation_sha256(implementation)
            if implementation_hash in design.candidate_implementation_hashes:
                self.tracker.consume("duplicate_candidate_rejections")
                diagnostics = "repair repeated an already rejected implementation hash"
                self._repair_lineage.append(
                    {
                        "design_id": design.design_id,
                        "attempt": attempt + 1,
                        "kind": "repair" if previous_implementation is not None else "initial",
                        "capsule_id": capsule.capsule_id,
                        "implementation_hash": implementation_hash,
                        "status": "duplicate-implementation-rejected-before-lean",
                        "base_sha256": proposal.base_sha256,
                    }
                )
                continue
            try:
                source, declaration = build_authored_capability_source(
                    input_module=self.input_module,
                    exact_type=authored_type,
                    namespace=namespace,
                    declaration_name=declaration_name,
                    implementation=implementation,
                    extra_imports=(
                        *candidate_modules,
                        *self.plugin_imports,
                        *state.imports,
                    ),
                    generated_capabilities=state.generated_capabilities,
                    forbidden_declarations=self.forbidden_declarations,
                )
            except ValueError as error:
                diagnostics = str(error)
                classified = classify_lean_diagnostic(diagnostics)
                previous_implementation = implementation
                previous_implementation_hash = implementation_hash
                previous_source = implementation
                design = record_diagnostic(
                    replace(
                        design,
                        previous_implementation=implementation,
                        candidate_implementation_hashes=(
                            *design.candidate_implementation_hashes,
                            implementation_hash,
                        ),
                        repair_attempts=design.repair_attempts + int(attempt > 0),
                    ),
                    classified,
                )
                design = self._store_design(design)
                self._repair_lineage.append(
                    {
                        "design_id": design.design_id,
                        "attempt": attempt + 1,
                        "kind": "repair" if attempt > 0 else "initial",
                        "capsule_id": capsule.capsule_id,
                        "implementation_hash": implementation_hash,
                        "status": "authoring-fence-rejected",
                        "diagnostic_code": classified.code,
                        "diagnostic_fingerprint": classified.fingerprint,
                        "base_sha256": proposal.base_sha256,
                    }
                )
                continue
            source_hash = stable_sha256(source)
            if (
                source_hash in design.candidate_source_hashes
                or source_hash in self._candidate_source_hashes
            ):
                self.tracker.consume("duplicate_candidate_rejections")
                diagnostics = "candidate source hash was already Lean-checked"
                self._repair_lineage.append(
                    {
                        "design_id": design.design_id,
                        "attempt": attempt + 1,
                        "kind": "repair" if attempt > 0 else "initial",
                        "capsule_id": capsule.capsule_id,
                        "implementation_hash": implementation_hash,
                        "source_hash": source_hash,
                        "status": "duplicate-source-rejected-before-lean",
                        "base_sha256": proposal.base_sha256,
                    }
                )
                continue
            self._candidate_source_hashes.add(source_hash)
            self.tracker.consume("lean_checks")
            self.tracker.consume("generated_lean_checks")
            self.tracker.consume("generated_files")
            self.tracker.consume("synthesis_materializations")
            file_stem = (
                f"{design.design_id}-attempt-{attempt + 1}-"
                f"{implementation_hash.removeprefix('sha256:')[:10]}-"
                f"{source_hash.removeprefix('sha256:')[:10]}"
            )
            path = self.store.write_text(
                f"work/generated/{file_stem}.lean", source
            )
            command = run_lean_file(
                root=self.root,
                path=path,
                timeout_seconds=self.lean_timeout_seconds,
            )
            self._record_command(command)
            design = replace(
                design,
                previous_implementation=implementation,
                previous_source_hash=source_hash,
                candidate_implementation_hashes=(
                    *design.candidate_implementation_hashes,
                    implementation_hash,
                ),
                candidate_source_hashes=(
                    *design.candidate_source_hashes,
                    source_hash,
                ),
                generated_files=(*design.generated_files, str(path)),
                materialization_attempts=design.materialization_attempts + 1,
                repair_attempts=design.repair_attempts + int(attempt > 0),
            )
            if not command.ok:
                diagnostics = (command.stderr or command.stdout)[-4000:]
                classified = classify_lean_diagnostic(diagnostics)
                previous_implementation = implementation
                previous_implementation_hash = implementation_hash
                previous_source = source
                failed_source_hashes.append(source_hash)
                design = self._store_design(record_diagnostic(design, classified))
                repetition_count = design.diagnostic_fingerprints.count(
                    classified.fingerprint
                )
                self._repair_lineage.append(
                    {
                        "design_id": design.design_id,
                        "attempt": attempt + 1,
                        "kind": "repair" if attempt > 0 else "initial",
                        "capsule_id": capsule.capsule_id,
                        "implementation_hash": implementation_hash,
                        "source_hash": source_hash,
                        "file": str(path),
                        "status": "lean-failed",
                        "diagnostic_code": classified.code,
                        "diagnostic_fingerprint": classified.fingerprint,
                        "base_sha256": proposal.base_sha256,
                    }
                )
                if repetition_count >= self.tracker.budget.max_same_diagnostic_repetitions:
                    self.tracker.consume("repeated_diagnostics")
                    design = self._store_design(
                        design.transition(
                            "abandoned",
                            status="abandoned",
                            terminal_reason=(
                                "same Lean diagnostic fingerprint repeated beyond policy"
                            ),
                        )
                    )
                    break
                continue
            self.tracker.consume("generated_lean_successes")
            self.tracker.consume("capability_registrations")
            capability = GeneratedCapability(
                capability_id=f"capability-{digest}",
                exact_type=authored_type,
                declaration=declaration,
                namespace=namespace,
                implementation=implementation,
                source_hash=source_hash,
                action_id=action.action_id,
            )
            fragment = ReusableFragment(
                exact_type=authored_type,
                proof_term=declaration,
                declaration=declaration,
                imports=candidate_modules,
                provenance="job-local-generated",
                lean_verified=True,
                source_hash=source_hash,
            )
            state = state.add_generated_capability(capability, fragment)
            self.planner.invalidate_for_new_capability(state.capability_fingerprint)
            design = self._store_design(
                design.transition(
                    "verified",
                    status="verified",
                    helper_declarations=(
                        (*design.helper_declarations, declaration)
                        if helper_obligation is not None
                        else design.helper_declarations
                    ),
                    declarations=(*design.declarations, declaration),
                    verified_capabilities=(
                        *design.verified_capabilities,
                        declaration,
                    ),
                )
            )
            self._repair_lineage.append(
                {
                    "design_id": design.design_id,
                    "attempt": attempt + 1,
                    "kind": "repair" if attempt > 0 else "initial",
                    "capsule_id": capsule.capsule_id,
                    "implementation_hash": implementation_hash,
                    "source_hash": source_hash,
                    "file": str(path),
                    "status": "lean-verified",
                    "declaration": declaration,
                    "base_sha256": proposal.base_sha256,
                    "addressed_diagnostic_codes": list(
                        proposal.addressed_diagnostic_codes
                    ),
                }
            )
            if helper_obligation is not None:
                self._event(
                    "HELPER_CAPABILITY_REGISTERED",
                    goal_id=goal.goal_id,
                    helper_goal_id=authored_goal.goal_id,
                    design_id=design.design_id,
                    declaration=declaration,
                    exact_type=authored_type,
                    source_hash=source_hash,
                )
                return state
            state = state.close_goal(
                goal_id=goal.goal_id,
                action=action,
                fragment=fragment,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=ProviderKind.SYNTHESIS,
                    disposition=ActionDisposition.CLOSED,
                    goal_id=goal.goal_id,
                    exact_type=goal.exact_type,
                    declaration=declaration,
                ),
            )
            self._event(
                "GENERATED_CAPABILITY_REGISTERED",
                goal_id=goal.goal_id,
                declaration=declaration,
                source_hash=source_hash,
                design_id=design.design_id,
                context_capsule_id=capsule.capsule_id,
            )
            if goal.producer_frame_id and goal.producer_slot_id:
                return self._fill_frame_slot(
                    state,
                    frame_id=goal.producer_frame_id,
                    slot_id=goal.producer_slot_id,
                    fragment=fragment,
                    attempted_actions=tuple(
                        dict.fromkeys((*goal.attempted_actions, action.action_id))
                    ),
                )
            return state
        if design.status != "abandoned":
            design = self._store_design(
                design.transition(
                    "abandoned",
                    status="abandoned",
                    terminal_reason=(
                        diagnostics or "no child capability candidate passed Lean"
                    )[-1000:],
                )
            )
        return state.remember_failure(
            action=action,
            diagnostic=(
                design.terminal_reason
                or diagnostics
                or "no child capability candidate passed Lean"
            ),
            blocker_code="child_synthesis_not_verified",
            goal_id=goal.goal_id,
        )


__all__ = ["RecursiveSearchRuntime"]
