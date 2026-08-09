"""Execution-profile projections for backend-neutral hardness plans.

Profiles may reject otherwise valid plans because a particular benchmark or
backend cannot execute them.  Keeping these restrictions outside ``plan``
prevents a temporary Lean wrapper from becoming the long-term Agent ABI.
"""

from __future__ import annotations

from dataclasses import dataclass

from .models import TypedCatalog
from .plan import HardnessPlan, PlanValidationError


EXISTING_REDUCTION_PROFILE = "existing_reduction_path_codegen_v1"
EXISTING_REDUCTION_OUTPUT_ID = "selected_path"


@dataclass(frozen=True)
class ExistingReductionPathView:
    """Executable view used only by the current IR-feasibility backend."""

    declarations: tuple[str, ...]
    roles: tuple[str, ...]
    lean_term: str
    expected_type: str


def validate_existing_reduction_profile(
    plan: HardnessPlan,
    *,
    catalog: TypedCatalog,
    source_declaration: str,
    target_declaration: str,
    maximum_steps: int,
    require_single_step: bool,
) -> ExistingReductionPathView:
    """Project a general plan into the current existing-route benchmark profile."""

    if plan.objective != "reduce_to":
        raise PlanValidationError("existing-reduction profile requires reduce_to")
    if (
        plan.source_declaration != source_declaration
        or plan.target_declaration != target_declaration
    ):
        raise PlanValidationError("plan endpoints do not match the exact benchmark goal")
    if plan.registry_fingerprint != catalog.registry_fingerprint:
        raise PlanValidationError("plan registry fingerprint does not match the catalog")
    if plan.catalog_id != catalog.catalog_id:
        raise PlanValidationError("plan catalog ID does not match the selected catalog")
    if not plan.steps or len(plan.steps) > maximum_steps:
        raise PlanValidationError(
            f"existing-reduction profile requires 1..{maximum_steps} steps"
        )
    if require_single_step and len(plan.steps) != 1:
        raise PlanValidationError("flat existing-reduction profile requires one step")
    entries = {
        entry.declaration: entry
        for entry in catalog.entries
        if entry.capability_kind == "certified_reduction"
    }
    declarations: list[str] = []
    roles: list[str] = []
    for step in plan.steps:
        if step.action_kind != "reuse.certified_reduction":
            raise PlanValidationError(
                "existing-reduction profile accepts only reuse.certified_reduction steps"
            )
        if step.capability_kind not in {None, "certified_reduction"}:
            raise PlanValidationError("plan step capability kind is not a reduction")
        if not step.declaration or step.declaration not in entries:
            raise PlanValidationError(
                "plan step declaration is outside the reduction catalog"
            )
        entry = entries[step.declaration]
        if step.role is not None and step.role != entry.component_role:
            raise PlanValidationError("plan step role disagrees with catalog metadata")
        declarations.append(step.declaration)
        roles.append(entry.component_role)
    if len(declarations) != len(set(declarations)):
        raise PlanValidationError("existing-reduction profile repeats a declaration")
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedPath "
        f"{source_declaration} {target_declaration}"
    )
    candidates = [
        output
        for output in plan.outputs
        if output.output_id == EXISTING_REDUCTION_OUTPUT_ID
        and output.output_kind == "lean.term"
        and output.expected_type == expected_type
        and output.lean_code is not None
    ]
    if len(plan.outputs) != 1 or len(candidates) != 1:
        raise PlanValidationError(
            "existing-reduction profile requires exactly one selected_path Lean term output"
        )
    output = candidates[0]
    if output.producer_steps != tuple(step.step_id for step in plan.steps):
        raise PlanValidationError(
            "selected-path output must list every reduction step in plan order"
        )
    lean_term = output.lean_code or ""
    if any(declaration not in lean_term for declaration in declarations):
        raise PlanValidationError(
            "selected-path Lean term does not reference every planned declaration"
        )
    return ExistingReductionPathView(
        declarations=tuple(declarations),
        roles=tuple(roles),
        lean_term=lean_term,
        expected_type=expected_type,
    )
