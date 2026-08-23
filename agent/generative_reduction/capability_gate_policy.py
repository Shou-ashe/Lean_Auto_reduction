"""Stable, hash-bound capability-gate policies for the generative agent."""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable, Sequence

from .boolean_csp_gadget_authoring import (
    GADGET_AUTHORING_ALLOWED_SOURCE_CORES,
    GADGET_AUTHORING_GENERATOR_NAME,
    GADGET_AUTHORING_GENERATOR_VERSION,
    GADGET_PLAN_SCHEMA,
    GADGET_RENDERER_NAME,
    GADGET_RENDERER_VERSION,
    GADGET_SEMANTIC_CHECKER_NAME,
    GADGET_SEMANTIC_CHECKER_VERSION,
    GADGET_TRUTH_TABLE_CONTEXT_VERSION,
)
from .models import CapabilityKind, ContributionClass, stable_sha256


FINITE_GADGET_NAMESPACE = (
    "ComplexityReduction.Agent.GenerativeReduction.Plugins."
    "BooleanCSPFiniteGadget."
)

BOOLEAN_CSP_GADGET_AUTHORING_ANCHOR_CASE_IDS = (
    "q-b01-canonical-three-sat-like",
    "q-b03-positive-nae3",
    "q-b04-positive-exactly-one3",
)

BOOLEAN_CSP_GADGET_AUTHORING_REQUIRED_CASE_IDS = (
    "q-b02-positive-nae4",
    "q-b05-or2-even-parity3",
    "q-b06-positive-nae5",
    "q-b07-positive-exactly-two3",
    "q-b08-positive-exactly-one4",
    "q-b09-positive-exactly-two4",
    "q-b10-positive-exactly-three4",
    "q-b11-positive-exactly-one5",
    "q-b12-positive-exactly-two5",
    "q-b13-positive-exactly-three5",
    "q-b14-positive-exactly-four5",
    "q-b15-positive-exactly-one6",
    "q-b16-positive-exactly-two6",
    "q-b17-positive-exactly-three6",
    "q-b18-positive-exactly-four6",
    "q-b19-positive-exactly-five6",
    "q-b20-or3-xor2",
    "q-b21-random-table-a",
    "q-b22-random-table-b",
    "q-b23-random-table-c",
    "q-b24-random-table-d",
    "q-b25-random-table-e",
    "q-b26-random-table-f",
    "q-b27-random-table-g",
    "q-b28-random-table-h",
    "q-b29-random-table-i",
    "q-b30-random-table-j",
)

BOOLEAN_CSP_GADGET_AUTHORING_DEV_CASE_IDS = (
    "q-b02-positive-nae4",
    "ga-dev-random-hard4",
    "ga-dev-dual-exactly-five7",
    "ga-dev-mixed-nand2-or3",
)

BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_CASE_IDS = (
    "q-b05-or2-even-parity3",
    "q-b06-positive-nae5",
    "q-b07-positive-exactly-two3",
    "q-b08-positive-exactly-one4",
    "q-b09-positive-exactly-two4",
    "q-b10-positive-exactly-three4",
)

BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_CASE_IDS = (
    "q-b11-positive-exactly-one5",
    "q-b12-positive-exactly-two5",
    "q-b13-positive-exactly-three5",
    "q-b14-positive-exactly-four5",
    "q-b15-positive-exactly-one6",
    "q-b16-positive-exactly-two6",
    "q-b17-positive-exactly-three6",
    "q-b18-positive-exactly-four6",
    "q-b19-positive-exactly-five6",
    "q-b20-or3-xor2",
    "q-b21-random-table-a",
    "q-b22-random-table-b",
    "q-b23-random-table-c",
    "q-b24-random-table-d",
    "q-b25-random-table-e",
    "q-b26-random-table-f",
    "q-b27-random-table-g",
    "q-b28-random-table-h",
    "q-b29-random-table-i",
    "q-b30-random-table-j",
)

GADGET_AUTHORING_DISABLED_FINITE_PLUGINS = (
    "boolean-csp-explicit-finite-gadget",
    "boolean-csp-canonical-database",
)

GADGET_AUTHORING_BASE_MAX_TOKENS = 16_000
GADGET_AUTHORING_ESCALATED_MAX_TOKENS = 64_000
GADGET_AUTHORING_REASONING_EFFORT = "low"
GADGET_AUTHORING_MAX_TOKEN_ESCALATIONS_PER_ATTEMPT = 1

NO_LIBRARY_THEOREM_NAMESPACE_PREFIXES = ("ComplexityReduction",)
NO_LIBRARY_AUTHORED_THEOREM_NAMESPACE_PREFIXES = (
    "ComplexityReduction.Agent.GenerativeReduction.Generated",
    "ComplexityReduction.Agent.GenerativeReduction.GeneratedCapabilities",
)

GADGET_AUTHORING_ALLOWED_CERTIFICATE_DECLARATIONS = (
    FINITE_GADGET_NAMESPACE + "FiniteConstraint",
    FINITE_GADGET_NAMESPACE + "FiniteConstraint.decidableHolds",
    FINITE_GADGET_NAMESPACE + "FiniteConstraint.Satisfies",
    FINITE_GADGET_NAMESPACE + "FiniteConstraint.toConstraint",
    FINITE_GADGET_NAMESPACE + "FiniteFormula",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.Satisfies",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.toFormula",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.extend",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.restrict",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.extend_apply",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.satisfies_extend_iff",
    FINITE_GADGET_NAMESPACE + "FiniteFormula.satisfies_restrict_iff",
    FINITE_GADGET_NAMESPACE + "Spec",
    FINITE_GADGET_NAMESPACE + "Spec.Correct",
    FINITE_GADGET_NAMESPACE + "Spec.toGadget",
)

GADGET_AUTHORING_FORBIDDEN_DISCOVERY_DECLARATIONS = tuple(
    FINITE_GADGET_NAMESPACE + name
    for name in (
        "AnyCorrect",
        "anyCorrectDecidable",
        "chooseCorrect",
        "gadgetOfCandidates",
        "plannedMappedVariable",
        "plannedConstraintOfMapping",
        "firstOutputs",
        "firstOutputs_injective",
        "plannedSpecOfFormula",
        "plannedFormulasForTemplate",
        "plannedSpecs",
        "TruthTableCounterexample",
        "firstPlannedCounterexample?",
        "renderPlannedCounterexample",
        "gadgetOfPlannedSearch",
        "mappedVariable",
        "constraintOfMapping",
        "firstThreeOutputs",
        "firstThreeOutputs_injective",
        "specOfFormula",
        "formulasForTemplate",
        "templates",
        "defaultSpecs",
        "gadgetOfDefaultSearch",
    )
)

GADGET_AUTHORING_BASE_FORBIDDEN_DECLARATIONS = (
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable_with_oneInThree",
    "ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.oneInThreeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.naeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase.gadget",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.exactlyOne_closed_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.nae_closed_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeGadgetOfExactlyTwo3",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3InterpretsOneInThree",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3CoreNPHard_of_oneInThree",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3CoreNPHard",
    *(
        declaration
        for declaration in GADGET_AUTHORING_FORBIDDEN_DISCOVERY_DECLARATIONS
        if not declaration.endswith("?")
    ),
)


@dataclass(frozen=True)
class CapabilityGatePolicy:
    name: str
    policy_version: str
    required_case_ids: tuple[str, ...]
    anchor_case_ids: tuple[str, ...]
    required_capability_kind: CapabilityKind
    required_contribution_classes: tuple[ContributionClass, ...]
    disabled_finite_synthesis_plugins: tuple[str, ...] = ()
    forbidden_declarations: tuple[str, ...] = ()
    excluded_candidate_declarations: tuple[str, ...] = ()
    allowed_certificate_declarations: tuple[str, ...] = ()
    require_model_semantic_payload: bool = False
    require_final_artifact_use: bool = True
    require_independent_lean: bool = True
    require_zero_forbidden_dependencies: bool = True
    semantic_payload_schema: str | None = None
    generator_name: str | None = None
    generator_version: str | None = None
    renderer_name: str | None = None
    renderer_version: str | None = None
    checker_name: str | None = None
    checker_version: str | None = None
    truth_table_context_version: str | None = None
    allowed_gadget_source_declarations: tuple[str, ...] = ()
    max_gadget_variable_count: int | None = None
    max_gadget_constraint_count: int | None = None
    max_gadget_repairs: int = 0
    gadget_authoring_base_max_tokens: int | None = None
    gadget_authoring_escalated_max_tokens: int | None = None
    gadget_authoring_reasoning_effort: str | None = None
    max_gadget_token_escalations_per_attempt: int = 0
    disable_closed_resolver: bool = False
    disable_theorem_index: bool = False
    forbidden_theorem_namespace_prefixes: tuple[str, ...] = ()
    allowed_authored_theorem_namespace_prefixes: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.name or not self.policy_version:
            raise ValueError("capability gate policy name and version are required")
        if len(self.required_case_ids) != len(set(self.required_case_ids)):
            raise ValueError("capability gate policy repeats a required case ID")
        if len(self.anchor_case_ids) != len(set(self.anchor_case_ids)):
            raise ValueError("capability gate policy repeats an anchor case ID")
        overlap = set(self.required_case_ids).intersection(self.anchor_case_ids)
        if overlap:
            raise ValueError(
                f"capability gate required/anchor cases overlap: {sorted(overlap)!r}"
            )
        if not self.required_contribution_classes:
            raise ValueError("capability gate needs an accepted contribution class")
        if len(self.disabled_finite_synthesis_plugins) != len(
            set(self.disabled_finite_synthesis_plugins)
        ):
            raise ValueError("capability gate repeats a disabled plugin name")
        if self.max_gadget_repairs < 0:
            raise ValueError("capability gate gadget repair bound cannot be negative")
        if self.max_gadget_token_escalations_per_attempt < 0:
            raise ValueError(
                "capability gate gadget token escalation bound cannot be negative"
            )
        if len(self.allowed_gadget_source_declarations) != len(
            set(self.allowed_gadget_source_declarations)
        ):
            raise ValueError("capability gate repeats an allowed gadget source")
        if len(self.forbidden_theorem_namespace_prefixes) != len(
            set(self.forbidden_theorem_namespace_prefixes)
        ):
            raise ValueError("capability gate repeats a forbidden theorem namespace")
        if len(self.allowed_authored_theorem_namespace_prefixes) != len(
            set(self.allowed_authored_theorem_namespace_prefixes)
        ):
            raise ValueError("capability gate repeats an authored theorem namespace")
        if self.disable_theorem_index and not self.disable_closed_resolver:
            raise ValueError(
                "disabling the theorem index also requires disabling the closed resolver"
            )
        if (
            self.allowed_authored_theorem_namespace_prefixes
            and not self.forbidden_theorem_namespace_prefixes
        ):
            raise ValueError(
                "authored theorem namespace exceptions require a forbidden namespace"
            )
        for label, value in (
            ("max_gadget_variable_count", self.max_gadget_variable_count),
            ("max_gadget_constraint_count", self.max_gadget_constraint_count),
            (
                "gadget_authoring_base_max_tokens",
                self.gadget_authoring_base_max_tokens,
            ),
            (
                "gadget_authoring_escalated_max_tokens",
                self.gadget_authoring_escalated_max_tokens,
            ),
        ):
            if value is not None and value < 1:
                raise ValueError(f"capability gate {label} must be positive")
        if (
            self.gadget_authoring_base_max_tokens is not None
            and self.gadget_authoring_escalated_max_tokens is not None
            and self.max_gadget_token_escalations_per_attempt > 0
            and self.gadget_authoring_base_max_tokens
            >= self.gadget_authoring_escalated_max_tokens
        ):
            raise ValueError(
                "capability gate escalated token profile must exceed the base profile"
            )
        if self.require_model_semantic_payload:
            if not self.allowed_gadget_source_declarations:
                raise ValueError(
                    "model semantic payload policy omitted allowed gadget sources"
                )
            required = {
                "semantic_payload_schema": self.semantic_payload_schema,
                "generator_name": self.generator_name,
                "generator_version": self.generator_version,
                "renderer_name": self.renderer_name,
                "renderer_version": self.renderer_version,
                "checker_name": self.checker_name,
                "checker_version": self.checker_version,
                "truth_table_context_version": self.truth_table_context_version,
                "allowed_gadget_source_declarations": (
                    self.allowed_gadget_source_declarations
                ),
                "max_gadget_variable_count": self.max_gadget_variable_count,
                "max_gadget_constraint_count": self.max_gadget_constraint_count,
                "gadget_authoring_base_max_tokens": (
                    self.gadget_authoring_base_max_tokens
                ),
                "gadget_authoring_escalated_max_tokens": (
                    self.gadget_authoring_escalated_max_tokens
                ),
                "gadget_authoring_reasoning_effort": (
                    self.gadget_authoring_reasoning_effort
                ),
            }
            missing = tuple(key for key, value in required.items() if value is None)
            if missing:
                raise ValueError(
                    "model semantic payload policy omitted fields: "
                    + ", ".join(missing)
                )
            if self.max_gadget_token_escalations_per_attempt != 1:
                raise ValueError(
                    "model semantic payload policy requires exactly one bounded "
                    "token escalation per logical attempt"
                )
            if not self.gadget_authoring_reasoning_effort.strip():
                raise ValueError(
                    "model semantic payload policy reasoning effort must be nonempty"
                )

    @property
    def selected_case_ids(self) -> tuple[str, ...]:
        return (*self.anchor_case_ids, *self.required_case_ids)

    def canonical_dict(self) -> dict[str, object]:
        return {
            "name": self.name,
            "policy_version": self.policy_version,
            "required_case_ids": list(self.required_case_ids),
            "anchor_case_ids": list(self.anchor_case_ids),
            "required_capability_kind": self.required_capability_kind.value,
            "required_contribution_classes": [
                item.value for item in self.required_contribution_classes
            ],
            "disabled_finite_synthesis_plugins": list(
                self.disabled_finite_synthesis_plugins
            ),
            "forbidden_declarations": list(self.forbidden_declarations),
            "excluded_candidate_declarations": list(
                self.excluded_candidate_declarations
            ),
            "allowed_certificate_declarations": list(
                self.allowed_certificate_declarations
            ),
            "require_model_semantic_payload": self.require_model_semantic_payload,
            "require_final_artifact_use": self.require_final_artifact_use,
            "require_independent_lean": self.require_independent_lean,
            "require_zero_forbidden_dependencies": (
                self.require_zero_forbidden_dependencies
            ),
            "semantic_payload_schema": self.semantic_payload_schema,
            "generator_name": self.generator_name,
            "generator_version": self.generator_version,
            "renderer_name": self.renderer_name,
            "renderer_version": self.renderer_version,
            "checker_name": self.checker_name,
            "checker_version": self.checker_version,
            "truth_table_context_version": self.truth_table_context_version,
            "allowed_gadget_source_declarations": list(
                self.allowed_gadget_source_declarations
            ),
            "max_gadget_variable_count": self.max_gadget_variable_count,
            "max_gadget_constraint_count": self.max_gadget_constraint_count,
            "max_gadget_repairs": self.max_gadget_repairs,
            "gadget_authoring_base_max_tokens": (
                self.gadget_authoring_base_max_tokens
            ),
            "gadget_authoring_escalated_max_tokens": (
                self.gadget_authoring_escalated_max_tokens
            ),
            "gadget_authoring_reasoning_effort": (
                self.gadget_authoring_reasoning_effort
            ),
            "max_gadget_token_escalations_per_attempt": (
                self.max_gadget_token_escalations_per_attempt
            ),
            "disable_closed_resolver": self.disable_closed_resolver,
            "disable_theorem_index": self.disable_theorem_index,
            "forbidden_theorem_namespace_prefixes": list(
                self.forbidden_theorem_namespace_prefixes
            ),
            "allowed_authored_theorem_namespace_prefixes": list(
                self.allowed_authored_theorem_namespace_prefixes
            ),
        }

    @property
    def policy_sha256(self) -> str:
        return stable_sha256(self.canonical_dict())

    def to_report_dict(self) -> dict[str, object]:
        return {**self.canonical_dict(), "policy_sha256": self.policy_sha256}

    def validate_case_ids(self, available_case_ids: Sequence[str]) -> None:
        available = tuple(available_case_ids)
        if len(available) != len(set(available)):
            raise ValueError("available capability-gate case IDs are not unique")
        selected = set(self.selected_case_ids)
        unknown = selected.difference(available)
        if unknown:
            raise ValueError(f"capability gate contains unknown cases: {sorted(unknown)!r}")
        omitted = set(available).difference(selected)
        if omitted:
            raise ValueError(f"capability gate omits suite cases: {sorted(omitted)!r}")

    def validate_finite_plugin_names(self, installed_names: Sequence[str]) -> None:
        installed = set(installed_names)
        unknown = set(self.disabled_finite_synthesis_plugins).difference(installed)
        if unknown:
            raise ValueError(
                f"capability gate disables unknown finite plugins: {sorted(unknown)!r}"
            )

    @staticmethod
    def _matches_namespace_prefix(declaration: str, prefix: str) -> bool:
        return declaration == prefix or declaration.startswith(prefix + ".")

    def library_theorem_declaration_allowed(
        self, declaration: str, declaration_kind: str | None
    ) -> bool:
        if declaration_kind not in {"theorem", "axiom"}:
            return True
        if any(
            self._matches_namespace_prefix(declaration, prefix)
            for prefix in self.allowed_authored_theorem_namespace_prefixes
        ):
            return True
        return not any(
            self._matches_namespace_prefix(declaration, prefix)
            for prefix in self.forbidden_theorem_namespace_prefixes
        )

    def candidate_declaration_allowed(
        self, declaration: str, declaration_kind: str | None = None
    ) -> bool:
        if declaration in self.forbidden_declarations:
            return False
        if not self.library_theorem_declaration_allowed(
            declaration, declaration_kind
        ):
            return False
        if not declaration.startswith(FINITE_GADGET_NAMESPACE):
            return True
        if declaration in self.allowed_certificate_declarations:
            return True
        generated_structure_members = {
            FINITE_GADGET_NAMESPACE + "FiniteConstraint.mk",
            FINITE_GADGET_NAMESPACE + "FiniteConstraint.symbol",
            FINITE_GADGET_NAMESPACE + "FiniteConstraint.vars",
            FINITE_GADGET_NAMESPACE + "Spec.mk",
            FINITE_GADGET_NAMESPACE + "Spec.formula",
            FINITE_GADGET_NAMESPACE + "Spec.outputs",
            FINITE_GADGET_NAMESPACE + "Spec.outputs_injective",
        }
        if declaration in generated_structure_members:
            return True
        return False

    def excluded_by_namespace_allowlist(
        self, declarations: Iterable[str]
    ) -> tuple[str, ...]:
        return tuple(
            declaration
            for declaration in declarations
            if declaration.startswith(FINITE_GADGET_NAMESPACE)
            and not self.candidate_declaration_allowed(declaration)
        )


def gadget_authoring_policy() -> CapabilityGatePolicy:
    return CapabilityGatePolicy(
        name="gadget-authoring",
        policy_version="gadget-authoring-policy-v7",
        required_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_REQUIRED_CASE_IDS,
        anchor_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_ANCHOR_CASE_IDS,
        required_capability_kind=CapabilityKind.GADGET,
        required_contribution_classes=(ContributionClass.MODEL_GENERATED_CAPABILITY,),
        disabled_finite_synthesis_plugins=(
            GADGET_AUTHORING_DISABLED_FINITE_PLUGINS
        ),
        forbidden_declarations=GADGET_AUTHORING_BASE_FORBIDDEN_DECLARATIONS,
        excluded_candidate_declarations=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThree_ppDefined_by_exactlyTwo3",
            "ComplexityReduction.Domain.BooleanCSP.Hardness.nPHard_exactlyTwo3_of_oneInThree",
        ),
        allowed_certificate_declarations=(
            GADGET_AUTHORING_ALLOWED_CERTIFICATE_DECLARATIONS
        ),
        require_model_semantic_payload=True,
        semantic_payload_schema=GADGET_PLAN_SCHEMA,
        generator_name=GADGET_AUTHORING_GENERATOR_NAME,
        generator_version=GADGET_AUTHORING_GENERATOR_VERSION,
        renderer_name=GADGET_RENDERER_NAME,
        renderer_version=GADGET_RENDERER_VERSION,
        checker_name=GADGET_SEMANTIC_CHECKER_NAME,
        checker_version=GADGET_SEMANTIC_CHECKER_VERSION,
        truth_table_context_version=GADGET_TRUTH_TABLE_CONTEXT_VERSION,
        allowed_gadget_source_declarations=(
            GADGET_AUTHORING_ALLOWED_SOURCE_CORES
        ),
        max_gadget_variable_count=12,
        max_gadget_constraint_count=24,
        max_gadget_repairs=5,
        gadget_authoring_base_max_tokens=GADGET_AUTHORING_BASE_MAX_TOKENS,
        gadget_authoring_escalated_max_tokens=(
            GADGET_AUTHORING_ESCALATED_MAX_TOKENS
        ),
        gadget_authoring_reasoning_effort=GADGET_AUTHORING_REASONING_EFFORT,
        max_gadget_token_escalations_per_attempt=(
            GADGET_AUTHORING_MAX_TOKEN_ESCALATIONS_PER_ATTEMPT
        ),
    )


def gadget_authoring_validation_policy() -> CapabilityGatePolicy:
    return replace(
        gadget_authoring_policy(),
        policy_version="gadget-authoring-validation-policy-v2",
        required_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_CASE_IDS,
        anchor_case_ids=(),
    )


def gadget_authoring_no_library_theorems_policy() -> CapabilityGatePolicy:
    """Ablation policy that exposes definitions but no pre-existing project theorem."""

    return replace(
        gadget_authoring_policy(),
        policy_version="gadget-authoring-no-library-theorems-policy-v1",
        disable_closed_resolver=True,
        disable_theorem_index=True,
        forbidden_theorem_namespace_prefixes=(
            NO_LIBRARY_THEOREM_NAMESPACE_PREFIXES
        ),
        allowed_authored_theorem_namespace_prefixes=(
            NO_LIBRARY_AUTHORED_THEOREM_NAMESPACE_PREFIXES
        ),
    )


def gadget_authoring_heldout_policy() -> CapabilityGatePolicy:
    return replace(
        gadget_authoring_policy(),
        policy_version="gadget-authoring-heldout-policy-v2",
        required_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_CASE_IDS,
        anchor_case_ids=(),
    )


def gadget_authoring_dev_policy() -> CapabilityGatePolicy:
    return CapabilityGatePolicy(
        name="gadget-authoring",
        policy_version="gadget-authoring-dev-policy-v4",
        required_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_DEV_CASE_IDS,
        anchor_case_ids=(),
        required_capability_kind=CapabilityKind.GADGET,
        required_contribution_classes=(ContributionClass.MODEL_GENERATED_CAPABILITY,),
        disabled_finite_synthesis_plugins=(
            GADGET_AUTHORING_DISABLED_FINITE_PLUGINS
        ),
        forbidden_declarations=GADGET_AUTHORING_BASE_FORBIDDEN_DECLARATIONS,
        excluded_candidate_declarations=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThree_ppDefined_by_exactlyTwo3",
            "ComplexityReduction.Domain.BooleanCSP.Hardness.nPHard_exactlyTwo3_of_oneInThree",
        ),
        allowed_certificate_declarations=(
            GADGET_AUTHORING_ALLOWED_CERTIFICATE_DECLARATIONS
        ),
        require_model_semantic_payload=True,
        semantic_payload_schema=GADGET_PLAN_SCHEMA,
        generator_name=GADGET_AUTHORING_GENERATOR_NAME,
        generator_version=GADGET_AUTHORING_GENERATOR_VERSION,
        renderer_name=GADGET_RENDERER_NAME,
        renderer_version=GADGET_RENDERER_VERSION,
        checker_name=GADGET_SEMANTIC_CHECKER_NAME,
        checker_version=GADGET_SEMANTIC_CHECKER_VERSION,
        truth_table_context_version=GADGET_TRUTH_TABLE_CONTEXT_VERSION,
        allowed_gadget_source_declarations=(
            GADGET_AUTHORING_ALLOWED_SOURCE_CORES
        ),
        max_gadget_variable_count=8,
        max_gadget_constraint_count=16,
        max_gadget_repairs=5,
        gadget_authoring_base_max_tokens=GADGET_AUTHORING_BASE_MAX_TOKENS,
        gadget_authoring_escalated_max_tokens=(
            GADGET_AUTHORING_ESCALATED_MAX_TOKENS
        ),
        gadget_authoring_reasoning_effort=GADGET_AUTHORING_REASONING_EFFORT,
        max_gadget_token_escalations_per_attempt=(
            GADGET_AUTHORING_MAX_TOKEN_ESCALATIONS_PER_ATTEMPT
        ),
    )


__all__ = [
    "BOOLEAN_CSP_GADGET_AUTHORING_ANCHOR_CASE_IDS",
    "BOOLEAN_CSP_GADGET_AUTHORING_DEV_CASE_IDS",
    "BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_CASE_IDS",
    "BOOLEAN_CSP_GADGET_AUTHORING_REQUIRED_CASE_IDS",
    "BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_CASE_IDS",
    "CapabilityGatePolicy",
    "FINITE_GADGET_NAMESPACE",
    "GADGET_AUTHORING_ALLOWED_CERTIFICATE_DECLARATIONS",
    "GADGET_AUTHORING_BASE_MAX_TOKENS",
    "GADGET_AUTHORING_BASE_FORBIDDEN_DECLARATIONS",
    "GADGET_AUTHORING_DISABLED_FINITE_PLUGINS",
    "GADGET_AUTHORING_ESCALATED_MAX_TOKENS",
    "GADGET_AUTHORING_FORBIDDEN_DISCOVERY_DECLARATIONS",
    "GADGET_AUTHORING_MAX_TOKEN_ESCALATIONS_PER_ATTEMPT",
    "GADGET_AUTHORING_REASONING_EFFORT",
    "NO_LIBRARY_AUTHORED_THEOREM_NAMESPACE_PREFIXES",
    "NO_LIBRARY_THEOREM_NAMESPACE_PREFIXES",
    "gadget_authoring_policy",
    "gadget_authoring_dev_policy",
    "gadget_authoring_heldout_policy",
    "gadget_authoring_no_library_theorems_policy",
    "gadget_authoring_validation_policy",
]
