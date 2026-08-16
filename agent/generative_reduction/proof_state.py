"""Immutable, reconstructible AND/OR proof-search state.

Lean metavariable identifiers never cross the process boundary.  Dependent
applications are represented by stable frame/slot identifiers and are
re-instantiated by Lean whenever a binder is filled.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
import re
from typing import Any, Mapping, Sequence

from .goal_kind_adapters import classify_goal
from .models import (
    ApplicationFrame,
    BinderSlot,
    CandidateAction,
    ConstructionContract,
    FrameStatus,
    GeneratedCapability,
    GoalKind,
    OpenGoal,
    PremiseSlot,
    ProofGuidance,
    ProofStep,
    ReusableFragment,
    RootGoal,
    SlotStatus,
    SubstepPlan,
    GoalKey,
    PremiseKind,
    ProviderKind,
    ActionDisposition,
    _jsonable,
    stable_sha256,
)


_UNRESOLVED_META_RE = re.compile(r"(?:\?[A-Za-z_Γ][A-Za-z0-9_Γ']*|\?m(?:\.|_)?\d+)")


def contains_unresolved_metavariable(exact_type: str) -> bool:
    return "⋯" in exact_type or bool(_UNRESOLVED_META_RE.search(exact_type))


def _diagnostic_fingerprint(diagnostic: str, blocker_code: str) -> str:
    normalized = " ".join(diagnostic.strip().split())[-2000:]
    return stable_sha256({"blocker_code": blocker_code, "diagnostic": normalized})


@dataclass(frozen=True)
class ProofState:
    state_id: str
    root_goal: RootGoal
    open_goals: tuple[OpenGoal, ...]
    application_frames: tuple[ApplicationFrame, ...] = ()
    generated_capabilities: tuple[GeneratedCapability, ...] = ()
    verified_frame_fragments: tuple[ReusableFragment, ...] = ()
    root_fragment: ReusableFragment | None = None
    proof_skeleton: tuple[ProofStep, ...] = ()
    planner_decisions: tuple[Mapping[str, Any], ...] = ()
    substep_plans: tuple[SubstepPlan, ...] = ()
    completed_fragments: tuple[ReusableFragment, ...] = ()
    verified_paths: tuple[str, ...] = ()
    construction_contracts: tuple[ConstructionContract, ...] = ()
    generated_modules: tuple[str, ...] = ()
    imports: tuple[str, ...] = ()
    depth: int = 0
    total_cost: float = 0.0
    lean_check_count: int = 0
    model_call_count: int = 0
    synthesis_round_count: int = 0
    cycle_fingerprints: frozenset[str] = field(default_factory=frozenset)
    failure_memory: tuple[Mapping[str, Any], ...] = ()
    normalized_failure_fingerprints: tuple[str, ...] = ()
    requeue_count: int = 0
    pruned_cycle_count: int = 0
    data_binding_count: int = 0
    dependent_goal_activation_count: int = 0

    @classmethod
    def initial(
        cls, root_goal: RootGoal, *, import_closure_fingerprint: str = ""
    ) -> "ProofState":
        open_goal = OpenGoal.create(
            goal_id="goal-root",
            exact_type=root_goal.exact_type,
            import_closure_fingerprint=import_closure_fingerprint,
            kind=classify_goal(root_goal.exact_type),
        )
        fingerprint = stable_sha256(
            {"root": root_goal.exact_type, "endpoint": root_goal.endpoint_fingerprint}
        )
        return cls(
            state_id=f"state-{fingerprint.removeprefix('sha256:')[:16]}",
            root_goal=root_goal,
            open_goals=(open_goal,),
            cycle_fingerprints=frozenset({fingerprint}),
        )

    def to_dict(self) -> dict[str, Any]:
        value = _jsonable(self)
        if not isinstance(value, dict):
            raise TypeError("proof state did not serialize to an object")
        return value

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ProofState":
        def fragment(item: Mapping[str, Any] | None) -> ReusableFragment | None:
            return None if item is None else ReusableFragment(**item)

        def open_goal(item: Mapping[str, Any]) -> OpenGoal:
            return OpenGoal(
                **{
                    **item,
                    "key": GoalKey(**item["key"]),
                    "kind": GoalKind(item["kind"]),
                    "local_context": tuple(item.get("local_context", ())),
                    "dependency_slot_ids": tuple(item.get("dependency_slot_ids", ())),
                    "attempted_actions": tuple(item.get("attempted_actions", ())),
                }
            )

        def binder(item: Mapping[str, Any]) -> BinderSlot:
            return BinderSlot(
                **{
                    **item,
                    "binder_kind": PremiseKind(item["binder_kind"]),
                    "status": SlotStatus(item["status"]),
                    "dependency_slot_ids": tuple(item.get("dependency_slot_ids", ())),
                    "imports": tuple(item.get("imports", ())),
                    "attempted_actions": tuple(item.get("attempted_actions", ())),
                }
            )

        def premise(item: Mapping[str, Any]) -> PremiseSlot:
            return PremiseSlot(
                **{
                    **item,
                    "premise_kind": PremiseKind(item["premise_kind"]),
                    "status": SlotStatus(item["status"]),
                    "dependency_slot_ids": tuple(item.get("dependency_slot_ids", ())),
                    "imports": tuple(item.get("imports", ())),
                    "attempted_actions": tuple(item.get("attempted_actions", ())),
                }
            )

        def frame(item: Mapping[str, Any]) -> ApplicationFrame:
            return ApplicationFrame(
                **{
                    **item,
                    "parent_kind": GoalKind(item["parent_kind"]),
                    "parent_local_context": tuple(item.get("parent_local_context", ())),
                    "parent_attempted_actions": tuple(
                        item.get("parent_attempted_actions", ())
                    ),
                    "binder_slots": tuple(
                        binder(slot) for slot in item.get("binder_slots", ())
                    ),
                    "premise_slots": tuple(
                        premise(slot) for slot in item.get("premise_slots", ())
                    ),
                    "status": FrameStatus(item["status"]),
                }
            )

        def step(item: Mapping[str, Any]) -> ProofStep:
            return ProofStep(
                **{
                    **item,
                    "provider": ProviderKind(item["provider"]),
                    "disposition": ActionDisposition(item["disposition"]),
                }
            )

        return cls(
            state_id=str(value["state_id"]),
            root_goal=RootGoal(**value["root_goal"]),
            open_goals=tuple(open_goal(item) for item in value.get("open_goals", ())),
            application_frames=tuple(
                frame(item) for item in value.get("application_frames", ())
            ),
            generated_capabilities=tuple(
                GeneratedCapability(**item)
                for item in value.get("generated_capabilities", ())
            ),
            verified_frame_fragments=tuple(
                fragment(item) for item in value.get("verified_frame_fragments", ())
            ),
            root_fragment=fragment(value.get("root_fragment")),
            proof_skeleton=tuple(step(item) for item in value.get("proof_skeleton", ())),
            planner_decisions=tuple(value.get("planner_decisions", ())),
            substep_plans=(),
            completed_fragments=tuple(
                fragment(item) for item in value.get("completed_fragments", ())
            ),
            verified_paths=tuple(value.get("verified_paths", ())),
            construction_contracts=(),
            generated_modules=tuple(value.get("generated_modules", ())),
            imports=tuple(value.get("imports", ())),
            depth=int(value.get("depth", 0)),
            total_cost=float(value.get("total_cost", 0.0)),
            lean_check_count=int(value.get("lean_check_count", 0)),
            model_call_count=int(value.get("model_call_count", 0)),
            synthesis_round_count=int(value.get("synthesis_round_count", 0)),
            cycle_fingerprints=frozenset(value.get("cycle_fingerprints", ())),
            failure_memory=tuple(value.get("failure_memory", ())),
            normalized_failure_fingerprints=tuple(
                value.get("normalized_failure_fingerprints", ())
            ),
            requeue_count=int(value.get("requeue_count", 0)),
            pruned_cycle_count=int(value.get("pruned_cycle_count", 0)),
            data_binding_count=int(value.get("data_binding_count", 0)),
            dependent_goal_activation_count=int(
                value.get("dependent_goal_activation_count", 0)
            ),
        )

    @property
    def complete(self) -> bool:
        return (
            not self.open_goals
            and self.root_fragment is not None
            and self.root_fragment.lean_verified
            and self.root_fragment.exact_type.strip() == self.root_goal.exact_type.strip()
            and all(frame.status == FrameStatus.VERIFIED for frame in self.application_frames)
        )

    @property
    def fingerprint(self) -> str:
        return stable_sha256(
            {
                "root": self.root_goal.exact_type,
                "open": [
                    {
                        "goal_key": goal.key.fingerprint,
                        "producer_frame_id": goal.producer_frame_id,
                        "producer_slot_id": goal.producer_slot_id,
                        "dependencies": goal.dependency_slot_ids,
                        "ready": goal.ready,
                        "attempted_actions": goal.attempted_actions,
                        "diagnostic": goal.normalized_last_diagnostic_hash,
                    }
                    for goal in sorted(self.open_goals, key=lambda item: item.goal_id)
                ],
                "frames": [
                    {
                        "frame_id": frame.frame_id,
                        "declaration": frame.declaration,
                        "status": frame.status,
                        "slots": [
                            {
                                "slot_id": slot.slot_id,
                                "ordinal": slot.ordinal,
                                "status": slot.status,
                                "dependencies": slot.dependency_slot_ids,
                                "exact_type": (
                                    slot.exact_type
                                    if isinstance(slot, BinderSlot)
                                    else slot.instantiated_exact_type
                                ),
                                "term": (
                                    slot.bound_term
                                    if isinstance(slot, BinderSlot)
                                    else slot.proof_term
                                ),
                                "declaration": slot.declaration
                                if isinstance(slot, PremiseSlot)
                                else slot.bound_declaration,
                                "module": slot.module,
                                "imports": slot.imports,
                                "attempted_actions": slot.attempted_actions,
                            }
                            for slot in frame.slots
                        ],
                        "receipt": frame.lean_receipt_hash,
                    }
                    for frame in sorted(self.application_frames, key=lambda item: item.frame_id)
                ],
                "generated_capabilities": [
                    {
                        "exact_type": item.exact_type,
                        "declaration": item.declaration,
                        "module": item.module,
                        "source_hash": item.source_hash,
                    }
                    for item in self.generated_capabilities
                ],
                "imports": self.imports,
                "generated_modules": self.generated_modules,
                "failures": self.normalized_failure_fingerprints,
                "verified_fragments": [
                    {
                        "exact_type": fragment.exact_type,
                        "proof_term": stable_sha256(fragment.proof_term),
                        "declaration": fragment.declaration,
                        "source_hash": fragment.source_hash,
                    }
                    for fragment in (*self.completed_fragments, *self.verified_frame_fragments)
                    if fragment.lean_verified
                ],
                "root_fragment": (
                    None
                    if self.root_fragment is None
                    else {
                        "exact_type": self.root_fragment.exact_type,
                        "proof_term": stable_sha256(self.root_fragment.proof_term),
                    }
                ),
            }
        )

    @property
    def capability_fingerprint(self) -> str:
        return stable_sha256(
            {
                "generated": [
                    (item.exact_type, item.declaration, item.module, item.source_hash)
                    for item in self.generated_capabilities
                ],
                "fragments": [
                    (item.exact_type, item.declaration, stable_sha256(item.proof_term))
                    for item in (*self.completed_fragments, *self.verified_frame_fragments)
                    if item.lean_verified
                ],
                "imports": self.imports,
            }
        )

    def _evolve(self, tag: str, **changes: Any) -> "ProofState":
        next_id = stable_sha256(
            {"previous": self.state_id, "tag": tag, "changes": changes}
        )
        return replace(
            self,
            state_id=f"state-{next_id.removeprefix('sha256:')[:16]}",
            **changes,
        )

    def goal(self, goal_id: str) -> OpenGoal:
        for goal in self.open_goals:
            if goal.goal_id == goal_id:
                return goal
        raise KeyError(goal_id)

    def frame(self, frame_id: str) -> ApplicationFrame:
        for frame in self.application_frames:
            if frame.frame_id == frame_id:
                return frame
        raise KeyError(frame_id)

    def select_open_goal(self) -> OpenGoal:
        ready = tuple(goal for goal in self.open_goals if goal.ready)
        if not ready:
            raise LookupError("proof state has no ready open goals")
        kind_rank = {
            GoalKind.DATA: 0,
            GoalKind.TYPECLASS: 1,
            GoalKind.PROPOSITION: 2,
            GoalKind.HARDNESS: 3,
        }
        return min(
            ready,
            key=lambda goal: (
                kind_rank.get(goal.kind, 4),
                goal.estimated_cost,
                goal.goal_id,
                goal.exact_type,
            ),
        )

    def record_plan(self, plan: SubstepPlan) -> "ProofState":
        return self._evolve(
            "record-plan",
            substep_plans=(*self.substep_plans, plan),
            planner_decisions=(
                *self.planner_decisions,
                {
                    "goal_key": plan.goal_key.fingerprint,
                    "plan_fingerprint": plan.plan_fingerprint,
                    "recommended_action_id": plan.recommended_action_id,
                },
            ),
            construction_contracts=(
                self.construction_contracts
                if plan.construction_contract is None
                else (*self.construction_contracts, plan.construction_contract)
            ),
        )

    def mark_action_attempted(self, goal_id: str, action_id: str) -> "ProofState":
        goal = self.goal(goal_id)
        if action_id in goal.attempted_actions:
            return self
        updated = replace(
            goal, attempted_actions=(*goal.attempted_actions, action_id)
        )
        goals = tuple(updated if item.goal_id == goal_id else item for item in self.open_goals)
        return self._evolve("mark-action-attempted", open_goals=goals)

    def release_action_for_replan(
        self, *, goal_id: str, action_id: str, diagnostic: str
    ) -> "ProofState":
        """Requeue one generator action after an explicit typed replan request."""

        goal = self.goal(goal_id)
        fingerprint = _diagnostic_fingerprint(
            diagnostic, "generator_requested_replan"
        )
        updated = replace(
            goal,
            attempted_actions=tuple(
                item for item in goal.attempted_actions if item != action_id
            ),
            last_lean_diagnostics=diagnostic[-4000:],
            normalized_last_diagnostic_hash=fingerprint,
        )
        goals = tuple(
            updated if item.goal_id == goal_id else item for item in self.open_goals
        )
        return self._evolve(
            "release-action-for-replan",
            open_goals=goals,
            failure_memory=(
                *self.failure_memory,
                {
                    "goal_id": goal_id,
                    "action_id": action_id,
                    "declaration": None,
                    "blocker_code": "generator_requested_replan",
                    "diagnostic_hash": fingerprint,
                    "diagnostic": diagnostic[-4000:],
                },
            ),
            normalized_failure_fingerprints=(
                *self.normalized_failure_fingerprints,
                fingerprint,
            ),
            requeue_count=self.requeue_count + 1,
        )

    def replace_frame(self, frame: ApplicationFrame) -> "ProofState":
        if not any(item.frame_id == frame.frame_id for item in self.application_frames):
            raise KeyError(frame.frame_id)
        frames = tuple(
            frame if item.frame_id == frame.frame_id else item
            for item in self.application_frames
        )
        return self._evolve("replace-frame", application_frames=frames)

    def refresh_frame_and_goals(
        self,
        *,
        frame: ApplicationFrame,
        goals: Sequence[OpenGoal],
        activated_goal_count: int = 0,
        data_binding_delta: int = 0,
    ) -> "ProofState":
        if not any(item.frame_id == frame.frame_id for item in self.application_frames):
            raise KeyError(frame.frame_id)
        frames = tuple(
            frame if item.frame_id == frame.frame_id else item
            for item in self.application_frames
        )
        return self._evolve(
            "refresh-frame-and-goals",
            application_frames=frames,
            open_goals=tuple(goals),
            dependent_goal_activation_count=(
                self.dependent_goal_activation_count + activated_goal_count
            ),
            data_binding_count=self.data_binding_count + data_binding_delta,
        )

    def add_application_frame(
        self,
        *,
        goal_id: str,
        action: CandidateAction,
        guidance: ProofGuidance,
        frame: ApplicationFrame,
        activated_goals: Sequence[OpenGoal],
        step: ProofStep,
    ) -> "ProofState":
        self.goal(goal_id)
        if any(item.frame_id == frame.frame_id for item in self.application_frames):
            raise ValueError(f"duplicate application frame: {frame.frame_id}")
        remaining = tuple(goal for goal in self.open_goals if goal.goal_id != goal_id)
        return self._evolve(
            "add-application-frame",
            open_goals=(*remaining, *tuple(activated_goals)),
            application_frames=(*self.application_frames, frame),
            proof_skeleton=(*self.proof_skeleton, step),
            depth=self.depth + 1,
            total_cost=self.total_cost + action.estimated_cost,
            dependent_goal_activation_count=(
                self.dependent_goal_activation_count + len(tuple(activated_goals))
            ),
        )

    def replace_open_goals(self, goals: Sequence[OpenGoal], *, tag: str) -> "ProofState":
        return self._evolve(tag, open_goals=tuple(goals))

    def close_goal(
        self,
        *,
        goal_id: str,
        action: CandidateAction,
        fragment: ReusableFragment,
        step: ProofStep,
    ) -> "ProofState":
        goal = self.goal(goal_id)
        remaining = tuple(item for item in self.open_goals if item.goal_id != goal_id)
        root_fragment = self.root_fragment
        if goal.producer_frame_id is None and goal_id == "goal-root":
            root_fragment = fragment
        completed_fragments = self.completed_fragments
        if not any(
            item.exact_type.strip() == fragment.exact_type.strip()
            and item.proof_term.strip() == fragment.proof_term.strip()
            for item in completed_fragments
        ):
            completed_fragments = (*completed_fragments, fragment)
        imports = tuple(
            dict.fromkeys(
                (
                    *self.imports,
                    *((fragment.module,) if fragment.module else ()),
                    *fragment.imports,
                )
            )
        )
        return self._evolve(
            "close-goal",
            open_goals=remaining,
            proof_skeleton=(*self.proof_skeleton, step),
            completed_fragments=completed_fragments,
            imports=imports,
            root_fragment=root_fragment,
            depth=self.depth + 1,
            total_cost=self.total_cost + action.estimated_cost,
        )

    def decompose_goal(
        self,
        *,
        goal_id: str,
        action: CandidateAction,
        residual_types: Sequence[str],
        guidance: ProofGuidance,
        step: ProofStep,
    ) -> "ProofState":
        """Compatibility helper for independent, non-dependent residuals.

        Production recursive execution uses ``ApplicationFrame``.  This method
        deliberately rejects rendered metavariables so they cannot become
        orphaned Python goals.
        """
        if any(contains_unresolved_metavariable(item) for item in residual_types):
            raise ValueError("unresolved Lean metavariable cannot enter OpenGoal")
        parent = self.goal(goal_id)
        remaining = [goal for goal in self.open_goals if goal.goal_id != goal_id]
        for ordinal, exact_type in enumerate(residual_types):
            remaining.append(
                OpenGoal.create(
                    goal_id=f"{goal_id}.{ordinal + 1}",
                    exact_type=exact_type,
                    local_context=parent.local_context,
                    import_closure_fingerprint=parent.key.import_closure_fingerprint,
                    parent_rule=guidance.candidate_declaration,
                    kind=classify_goal(exact_type),
                )
            )
        return self._evolve(
            "legacy-decompose-goal",
            open_goals=tuple(remaining),
            proof_skeleton=(*self.proof_skeleton, step),
            depth=self.depth + 1,
            total_cost=self.total_cost + action.estimated_cost,
        )

    def add_generated_capability(
        self, capability: GeneratedCapability, fragment: ReusableFragment
    ) -> "ProofState":
        if any(
            item.capability_id == capability.capability_id
            for item in self.generated_capabilities
        ):
            return self
        modules = self.generated_modules
        if capability.module:
            modules = tuple(dict.fromkeys((*modules, capability.module)))
        return self._evolve(
            "add-generated-capability",
            generated_capabilities=(*self.generated_capabilities, capability),
            completed_fragments=(*self.completed_fragments, fragment),
            generated_modules=modules,
        )

    def add_verified_frame_fragment(
        self, *, frame: ApplicationFrame, fragment: ReusableFragment
    ) -> "ProofState":
        verified = replace(frame, status=FrameStatus.VERIFIED)
        frames = tuple(
            verified if item.frame_id == frame.frame_id else item
            for item in self.application_frames
        )
        root_fragment = self.root_fragment
        if frame.parent_producer_frame_id is None and frame.parent_goal_id == "goal-root":
            root_fragment = fragment
        return self._evolve(
            "verify-frame",
            application_frames=frames,
            verified_frame_fragments=(*self.verified_frame_fragments, fragment),
            completed_fragments=(*self.completed_fragments, fragment),
            root_fragment=root_fragment,
        )

    def reopen_dependent_data_slot(
        self, *, frame_id: str, dependent_slot_id: str
    ) -> "ProofState | None":
        """Undo one binding whose dependent branch has been exhausted.

        The theorem application itself remains active.  Only the selected data
        witness, slots whose types depend on it, and their descendant frames
        are reset.  The restored binder goal retains its attempted action IDs,
        so the next frontier round must choose a different witness.
        """

        frame = self.frame(frame_id)
        try:
            dependent = next(
                slot for slot in frame.slots if slot.slot_id == dependent_slot_id
            )
        except StopIteration:
            return None
        candidates = [
            slot
            for slot in frame.binder_slots
            if slot.slot_id in dependent.dependency_slot_ids
            and slot.status in {SlotStatus.BOUND, SlotStatus.VERIFIED}
        ]
        if not candidates:
            return None
        binder = max(candidates, key=lambda item: item.ordinal)

        affected_slot_ids = {binder.slot_id}
        changed = True
        while changed:
            changed = False
            for slot in frame.slots:
                if slot.slot_id in affected_slot_ids:
                    continue
                if any(
                    dependency in affected_slot_ids
                    for dependency in slot.dependency_slot_ids
                ):
                    affected_slot_ids.add(slot.slot_id)
                    changed = True

        reset_binders: list[BinderSlot] = []
        for slot in frame.binder_slots:
            if slot.slot_id not in affected_slot_ids:
                reset_binders.append(slot)
                continue
            reset_binders.append(
                replace(
                    slot,
                    bound_term=None,
                    bound_declaration=None,
                    module=None,
                    imports=(),
                    provenance=None,
                    attempted_actions=(
                        slot.attempted_actions if slot.slot_id == binder.slot_id else ()
                    ),
                    status=(
                        SlotStatus.READY
                        if slot.slot_id == binder.slot_id
                        else SlotStatus.DORMANT
                    ),
                )
            )
        reset_premises = tuple(
            slot
            if slot.slot_id not in affected_slot_ids
            else replace(
                slot,
                instantiated_exact_type=None,
                proof_term=None,
                declaration=None,
                module=None,
                imports=(),
                provenance=None,
                attempted_actions=(),
                status=SlotStatus.DORMANT,
            )
            for slot in frame.premise_slots
        )
        reset_frame = replace(
            frame,
            binder_slots=tuple(reset_binders),
            premise_slots=reset_premises,
            result_proof_term=None,
            status=FrameStatus.ACTIVE,
        )

        removed_frame_ids: set[str] = set()
        changed = True
        while changed:
            changed = False
            for item in self.application_frames:
                if item.frame_id == frame_id or item.frame_id in removed_frame_ids:
                    continue
                directly_affected = (
                    item.parent_producer_frame_id == frame_id
                    and item.parent_producer_slot_id in affected_slot_ids
                )
                descendant = item.parent_producer_frame_id in removed_frame_ids
                if directly_affected or descendant:
                    removed_frame_ids.add(item.frame_id)
                    changed = True

        frames = tuple(
            reset_frame
            if item.frame_id == frame_id
            else item
            for item in self.application_frames
            if item.frame_id not in removed_frame_ids
        )
        goals = tuple(
            goal
            for goal in self.open_goals
            if goal.producer_frame_id not in removed_frame_ids
            and not (
                goal.producer_frame_id == frame_id
                and goal.producer_slot_id in affected_slot_ids
            )
        )
        restored = OpenGoal.create(
            goal_id=f"goal-{frame.frame_id}-{binder.ordinal}",
            exact_type=binder.exact_type,
            local_context=frame.parent_local_context,
            import_closure_fingerprint=frame.parent_import_closure_fingerprint,
            parent_rule=frame.declaration,
            producer_frame_id=frame.frame_id,
            producer_slot_id=binder.slot_id,
            dependency_slot_ids=binder.dependency_slot_ids,
            ready=True,
            kind=classify_goal(binder.exact_type, premise_kind=binder.binder_kind.value),
        )
        restored = replace(restored, attempted_actions=binder.attempted_actions)
        affected_goal_ids = {
            f"goal-{frame.frame_id}-{slot.ordinal}"
            for slot in frame.slots
            if slot.slot_id in affected_slot_ids
        }
        affected_goal_ids.update(
            item.parent_goal_id
            for item in self.application_frames
            if item.frame_id in removed_frame_ids
        )
        return self._evolve(
            "reopen-dependent-data-slot",
            application_frames=frames,
            open_goals=(*goals, restored),
            root_fragment=None,
            proof_skeleton=tuple(
                step
                for step in self.proof_skeleton
                if step.goal_id not in affected_goal_ids
            ),
            depth=frame.parent_depth + 1,
        )

    def rollback_application_frame(
        self,
        *,
        frame_id: str,
        action: CandidateAction,
        diagnostic: str,
        blocker_code: str = "frame_verification_failed",
    ) -> "ProofState":
        frame = self.frame(frame_id)
        removed_frame_ids = {frame_id}
        changed = True
        while changed:
            changed = False
            for item in self.application_frames:
                if (
                    item.frame_id not in removed_frame_ids
                    and item.parent_producer_frame_id in removed_frame_ids
                ):
                    removed_frame_ids.add(item.frame_id)
                    changed = True
        remaining_frames = tuple(
            item
            for item in self.application_frames
            if item.frame_id not in removed_frame_ids
        )
        remaining_goals = tuple(
            goal
            for goal in self.open_goals
            if goal.producer_frame_id not in removed_frame_ids
        )
        restored = OpenGoal.create(
            goal_id=frame.parent_goal_id,
            exact_type=frame.parent_exact_type,
            local_context=frame.parent_local_context,
            import_closure_fingerprint=frame.parent_import_closure_fingerprint,
            parent_rule=None,
            producer_frame_id=frame.parent_producer_frame_id,
            producer_slot_id=frame.parent_producer_slot_id,
            kind=frame.parent_kind,
        )
        restored = replace(
            restored,
            attempted_actions=tuple(
                dict.fromkeys((*frame.parent_attempted_actions, action.action_id))
            ),
        )
        state = self._evolve(
            "rollback-application-frame",
            application_frames=remaining_frames,
            open_goals=(*remaining_goals, restored),
            root_fragment=None if frame.parent_goal_id == "goal-root" else self.root_fragment,
            depth=frame.parent_depth,
            proof_skeleton=tuple(
                step for step in self.proof_skeleton if step.action_id != frame.action_id
            ),
        )
        return state.remember_failure(
            action=action,
            diagnostic=diagnostic,
            blocker_code=blocker_code,
            goal_id=restored.goal_id,
        )

    def remember_failure(
        self,
        *,
        action: CandidateAction,
        diagnostic: str,
        blocker_code: str = "action_failed",
        goal_id: str | None = None,
        requeued: bool = True,
    ) -> "ProofState":
        fingerprint = _diagnostic_fingerprint(diagnostic, blocker_code)
        goals = self.open_goals
        if goal_id is not None:
            try:
                goal = self.goal(goal_id)
            except KeyError:
                pass
            else:
                updated = replace(
                    goal,
                    last_lean_diagnostics=diagnostic[-4000:],
                    normalized_last_diagnostic_hash=fingerprint,
                )
                goals = tuple(
                    updated if item.goal_id == goal_id else item
                    for item in self.open_goals
                )
        return self._evolve(
            "remember-failure",
            open_goals=goals,
            failure_memory=(
                *self.failure_memory,
                {
                    "goal_id": goal_id,
                    "action_id": action.action_id,
                    "declaration": action.declaration,
                    "blocker_code": blocker_code,
                    "diagnostic_hash": fingerprint,
                    "diagnostic": diagnostic[-4000:],
                },
            ),
            normalized_failure_fingerprints=(
                *self.normalized_failure_fingerprints,
                fingerprint,
            ),
            requeue_count=self.requeue_count + int(requeued),
        )

    def prune_non_progressing_action(
        self, *, goal_id: str, action: CandidateAction, reason: str
    ) -> "ProofState":
        state = self.mark_action_attempted(goal_id, action.action_id)
        state = state.remember_failure(
            action=action,
            diagnostic=reason,
            blocker_code="non_progressing_decomposition",
            goal_id=goal_id,
        )
        return state._evolve(
            "prune-non-progressing-action",
            pruned_cycle_count=state.pruned_cycle_count + 1,
        )


__all__ = ["ProofState", "contains_unresolved_metavariable"]
