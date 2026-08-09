"""Generic final Lean artifact generation for accepted hardness plans."""

from __future__ import annotations

import re
import textwrap
from collections.abc import Iterable
from dataclasses import dataclass

from .benchmark import (
    KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS,
    OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS,
)
from .lean_runner import RUNTIME_MODULE, validate_declaration_name, validate_module_name


CASE_PART_RE = re.compile(r"[^A-Za-z0-9]+")


def case_namespace(case_id: str) -> str:
    parts = [part for part in CASE_PART_RE.split(case_id) if part]
    if not parts:
        raise ValueError("artifact case id has no Lean identifier content")
    rendered = "".join(part[:1].upper() + part[1:] for part in parts)
    if rendered[0].isdigit():
        rendered = "Case" + rendered
    return "Case" + rendered


@dataclass(frozen=True)
class CertifiedPathArtifactCase:
    case_id: str
    input_module: str
    source_declaration: str
    target_declaration: str
    lean_term: str


@dataclass(frozen=True)
class OpenTargetArtifactCase:
    """One model-selected path together with its Lean-exported target evidence."""

    case_id: str
    input_module: str
    source_declaration: str
    target_declaration: str
    lean_term: str
    required_hardness: str
    target_evidence_kind: str
    target_evidence_lean_term: str
    predicate_declaration: str | None = None


@dataclass(frozen=True)
class CoreGeneralizationArtifactCase:
    """One accepted Stage-L objective term for the single final Lean batch."""

    case_id: str
    input_module: str
    objective: str
    source_declaration: str
    proof_term: str
    target_declaration: str | None = None
    predicate_declaration: str | None = None
    target_evidence_kind: str | None = None
    target_evidence_term: str | None = None
    target_membership_term: str | None = None


def build_certified_path_batch_artifact_source(
    cases: Iterable[CertifiedPathArtifactCase],
    *,
    root_namespace: str = "Benchmark.Hardness.InputReductionBatch",
) -> str:
    """Wrap accepted model terms and audit all results in one Lean process."""

    materialized = tuple(cases)
    if not materialized:
        raise ValueError("batch artifact requires at least one accepted path")
    root = validate_declaration_name(root_namespace, label="artifact root namespace")
    modules = sorted(
        {validate_module_name(case.input_module) for case in materialized}
    )
    imports = "".join(
        f"import {module}\n" for module in (RUNTIME_MODULE, *modules)
    )
    blocks: list[str] = []
    audited: list[str] = []
    namespaces: set[str] = set()
    for case in materialized:
        source = validate_declaration_name(case.source_declaration, label="source")
        target = validate_declaration_name(case.target_declaration, label="target")
        if not isinstance(case.lean_term, str) or not case.lean_term.strip():
            raise ValueError(f"artifact case {case.case_id} has no Lean path term")
        namespace = case_namespace(case.case_id)
        if namespace in namespaces:
            raise ValueError("batch artifact has colliding case namespaces")
        namespaces.add(namespace)
        rendered_term = textwrap.indent(case.lean_term.strip(), "  ")
        blocks.append(
            f"""namespace {namespace}

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := .reduceTo {source} {target}

noncomputable def selectedPath :
    ComplexityReduction.Certificate.CertifiedPath {source} {target} :=
{rendered_term}

noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath
    policy (by rfl) selectedPath

end {namespace}
"""
        )
        audited.extend(
            (
                f"{root}.{namespace}.selectedPath",
                f"{root}.{namespace}.result",
            )
        )
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace {root}

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

{''.join(blocks)}
end

end {root}

assert_standard_axioms
  {audit}
"""


def build_open_target_batch_artifact_source(
    cases: Iterable[OpenTargetArtifactCase],
    *,
    root_namespace: str = "Benchmark.Hardness.OpenTargetBatch",
) -> str:
    """Audit dynamic targets, their native evidence, and all paths in one Lean file."""

    materialized = tuple(cases)
    if not materialized:
        raise ValueError("open-target artifact requires at least one accepted path")
    root = validate_declaration_name(root_namespace, label="artifact root namespace")
    modules = sorted(
        {validate_module_name(case.input_module) for case in materialized}
    )
    imports = "".join(
        f"import {module}\n" for module in (RUNTIME_MODULE, *modules)
    )
    blocks: list[str] = []
    audited: list[str] = []
    namespaces: set[str] = set()
    valid_policies = {"native_np", "native_np_hard", "native_np_complete"}
    membership_kinds = {"native_membership"}
    completeness_kinds = {"native_completeness"}
    hardness_kinds = {"transported_native_hardness"}
    for case in materialized:
        source = validate_declaration_name(case.source_declaration, label="source")
        target = validate_declaration_name(case.target_declaration, label="target")
        predicate = (
            validate_declaration_name(
                case.predicate_declaration,
                label="input predicate",
            )
            if case.predicate_declaration is not None
            else None
        )
        if case.required_hardness not in valid_policies:
            raise ValueError(
                f"artifact case {case.case_id} has unsupported target policy"
            )
        emittable_evidence = (
            KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS
            if case.required_hardness == "native_np_hard"
            else OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS
        )
        if case.target_evidence_kind not in emittable_evidence:
            raise ValueError(
                f"artifact case {case.case_id} has unsupported target evidence kind"
            )
        if not isinstance(case.lean_term, str) or not case.lean_term.strip():
            raise ValueError(f"artifact case {case.case_id} has no Lean path term")
        if (
            not isinstance(case.target_evidence_lean_term, str)
            or not case.target_evidence_lean_term.strip()
        ):
            raise ValueError(
                f"artifact case {case.case_id} has no Lean target evidence term"
            )
        namespace = case_namespace(case.case_id)
        if namespace in namespaces:
            raise ValueError("open-target artifact has colliding case namespaces")
        namespaces.add(namespace)
        rendered_path = textwrap.indent(case.lean_term.strip(), "  ")
        rendered_evidence = textwrap.indent(
            case.target_evidence_lean_term.strip(), "  "
        )
        if case.required_hardness == "native_np_hard":
            request_objective = f".reduceTo {source} {target}"
            result_constructor = (
                "ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath\n"
                "    policy (by rfl) selectedPath"
            )
            if case.target_evidence_kind in hardness_kinds:
                evidence_block = f"""noncomputable def targetHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {target} :=
{rendered_evidence}
"""
                evidence_audits = [f"{root}.{namespace}.targetHardness"]
            elif case.target_evidence_kind in completeness_kinds:
                evidence_block = f"""noncomputable def targetCompleteness :
    ComplexityReduction.Certificate.NativeTMNPComplete {target} :=
{rendered_evidence}

noncomputable def targetHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {target} :=
  ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness
    targetCompleteness
"""
                evidence_audits = [
                    f"{root}.{namespace}.targetCompleteness",
                    f"{root}.{namespace}.targetHardness",
                ]
            else:
                raise ValueError(
                    f"artifact case {case.case_id} has no native-hardness evidence"
                )
        else:
            request_objective = f".reduceToKnownNP {source} {target}"
            result_constructor = (
                "ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToKnownNPPath\n"
                "    policy (by rfl) selectedPath targetMembership"
            )
            if case.target_evidence_kind in membership_kinds:
                if case.required_hardness == "native_np_complete":
                    raise ValueError(
                        f"artifact case {case.case_id} has membership but requires completeness"
                    )
                evidence_block = f"""noncomputable def targetMembership :
    ComplexityReduction.Certificate.NativeTMInNP {target} :=
{rendered_evidence}
"""
                evidence_audits = [f"{root}.{namespace}.targetMembership"]
            elif case.target_evidence_kind in completeness_kinds:
                evidence_block = f"""noncomputable def targetCompleteness :
    ComplexityReduction.Certificate.NativeTMNPComplete {target} :=
{rendered_evidence}

noncomputable def targetMembership :
    ComplexityReduction.Certificate.NativeTMInNP {target} :=
  ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership
    targetCompleteness
"""
                evidence_audits = [
                    f"{root}.{namespace}.targetCompleteness",
                    f"{root}.{namespace}.targetMembership",
                ]
            else:
                raise ValueError(
                    f"artifact case {case.case_id} has hardness-only evidence for a known-NP request"
                )
        if predicate is None:
            grounding_block = ""
            grounding_audits: list[str] = []
        else:
            grounding_block = f"""theorem inputPredicateGrounding :
    ∀ input, {predicate} input ↔ {source}.accepts input :=
  fun _ => Iff.rfl

"""
            grounding_audits = [f"{root}.{namespace}.inputPredicateGrounding"]
        blocks.append(
            f"""namespace {namespace}

{grounding_block}def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := {request_objective}

noncomputable def selectedPath :
    ComplexityReduction.Certificate.CertifiedPath {source} {target} :=
{rendered_path}

{evidence_block}
noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  {result_constructor}

end {namespace}
"""
        )
        audited.extend(grounding_audits)
        audited.append(f"{root}.{namespace}.selectedPath")
        audited.extend(evidence_audits)
        audited.append(f"{root}.{namespace}.result")
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace {root}

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

{''.join(blocks)}
end

end {root}

assert_standard_axioms
  {audit}
"""


def build_core_generalization_batch_artifact_source(
    cases: Iterable[CoreGeneralizationArtifactCase],
    *,
    root_namespace: str = "Benchmark.Hardness.CoreGeneralizationBatch",
) -> str:
    """Emit reduction, membership, and completeness results in one Lean file."""

    materialized = tuple(cases)
    if not materialized:
        raise ValueError("Core-generalization artifact requires accepted positive cases")
    root = validate_declaration_name(root_namespace, label="artifact root namespace")
    modules = sorted(
        {validate_module_name(case.input_module) for case in materialized}
    )
    imports = "".join(
        f"import {module}\n" for module in (RUNTIME_MODULE, *modules)
    )
    blocks: list[str] = []
    audited: list[str] = []
    namespaces: set[str] = set()
    reduction_objectives = {
        "reduce_to",
        "reduce_to_known_np",
        "reduce_to_known_hardness",
    }
    for case in materialized:
        if case.objective not in {
            *reduction_objectives,
            "prove_in_np",
            "prove_np_complete",
        }:
            raise ValueError(
                f"artifact case {case.case_id} has unsupported objective {case.objective}"
            )
        source = validate_declaration_name(case.source_declaration, label="source")
        target = (
            validate_declaration_name(case.target_declaration, label="target")
            if case.target_declaration is not None
            else None
        )
        predicate = (
            validate_declaration_name(
                case.predicate_declaration,
                label="input predicate",
            )
            if case.predicate_declaration is not None
            else None
        )
        if not isinstance(case.proof_term, str) or not case.proof_term.strip():
            raise ValueError(f"artifact case {case.case_id} has no objective term")
        namespace = case_namespace(case.case_id)
        if namespace in namespaces:
            raise ValueError("Core-generalization artifact has colliding namespaces")
        namespaces.add(namespace)
        rendered_proof = textwrap.indent(case.proof_term.strip(), "  ")
        if predicate is None:
            grounding_block = ""
            grounding_audits: list[str] = []
        else:
            grounding_block = f"""theorem inputPredicateGrounding :
    ∀ input, {predicate} input ↔ {source}.accepts input :=
  fun _ => Iff.rfl

"""
            grounding_audits = [f"{root}.{namespace}.inputPredicateGrounding"]

        if case.objective in reduction_objectives:
            if target is None:
                raise ValueError(
                    f"artifact reduction case {case.case_id} has no target"
                )
            selected_block = f"""noncomputable def selectedPath :
    ComplexityReduction.Certificate.CertifiedPath {source} {target} :=
{rendered_proof}
"""
            objective_audits = [f"{root}.{namespace}.selectedPath"]
            if case.objective == "reduce_to":
                request_objective = f".reduceTo {source} {target}"
                evidence_block = ""
                result_term = (
                    "ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath\n"
                    "    policy (by rfl) selectedPath"
                )
            elif case.objective == "reduce_to_known_np":
                membership = case.target_membership_term
                if not isinstance(membership, str) or not membership.strip():
                    raise ValueError(
                        f"artifact case {case.case_id} has no exact target membership"
                    )
                rendered_membership = textwrap.indent(membership.strip(), "  ")
                request_objective = f".reduceToKnownNP {source} {target}"
                evidence_block = f"""noncomputable def targetMembership :
    ComplexityReduction.Certificate.NativeTMInNP {target} :=
{rendered_membership}
"""
                objective_audits.append(f"{root}.{namespace}.targetMembership")
                result_term = (
                    "ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToKnownNPPath\n"
                    "    policy (by rfl) selectedPath targetMembership"
                )
            else:
                evidence_term = case.target_evidence_term
                if not isinstance(evidence_term, str) or not evidence_term.strip():
                    raise ValueError(
                        f"artifact case {case.case_id} has no native-hardness evidence"
                    )
                rendered_evidence = textwrap.indent(evidence_term.strip(), "  ")
                request_objective = f".reduceTo {source} {target}"
                if case.target_evidence_kind == "transported_native_hardness":
                    evidence_block = f"""noncomputable def targetHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {target} :=
{rendered_evidence}
"""
                    objective_audits.append(f"{root}.{namespace}.targetHardness")
                elif case.target_evidence_kind == "native_completeness":
                    evidence_block = f"""noncomputable def targetCompleteness :
    ComplexityReduction.Certificate.NativeTMNPComplete {target} :=
{rendered_evidence}

noncomputable def targetHardness :
    ComplexityReduction.Certificate.NativeTMNPHard {target} :=
  ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness
    targetCompleteness
"""
                    objective_audits.extend(
                        (
                            f"{root}.{namespace}.targetCompleteness",
                            f"{root}.{namespace}.targetHardness",
                        )
                    )
                else:
                    raise ValueError(
                        f"artifact case {case.case_id} has wrong hardness evidence kind"
                    )
                result_term = (
                    "ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath\n"
                    "    policy (by rfl) selectedPath"
                )
            request_block = f"""def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := {request_objective}
"""
            result_block = f"""noncomputable def result :
    ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  {result_term}
"""
        elif case.objective == "prove_in_np":
            if target is not None or case.predicate_declaration is not None:
                raise ValueError(
                    f"artifact membership case {case.case_id} must use one exact PresentedProblem"
                )
            request_block = f"""def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := .proveInNP {source}
"""
            selected_block = f"""noncomputable def nativeMembership :
    ComplexityReduction.Certificate.NativeTMInNP {source} :=
{rendered_proof}
"""
            evidence_block = ""
            result_block = """noncomputable def result :
    ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  ComplexityReduction.Protocol.TypedAutoReductionResult.proveInNP
    policy (by rfl) nativeMembership
"""
            objective_audits = [f"{root}.{namespace}.nativeMembership"]
        else:
            if target is not None or case.predicate_declaration is not None:
                raise ValueError(
                    f"artifact completeness case {case.case_id} must use one exact PresentedProblem"
                )
            request_block = f"""def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := .proveNPComplete {source}
"""
            selected_block = f"""noncomputable def nativeCompleteness :
    ComplexityReduction.Certificate.NativeTMNPComplete {source} :=
{rendered_proof}
"""
            evidence_block = ""
            result_block = """noncomputable def result :
    ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  ComplexityReduction.Protocol.TypedAutoReductionResult.proveNPComplete
    policy (by rfl) nativeCompleteness
"""
            objective_audits = [f"{root}.{namespace}.nativeCompleteness"]

        blocks.append(
            f"""namespace {namespace}

{grounding_block}{request_block}

{selected_block}
{evidence_block}
{result_block}
end {namespace}
"""
        )
        audited.extend(grounding_audits)
        audited.extend(objective_audits)
        audited.append(f"{root}.{namespace}.result")
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace {root}

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

{''.join(blocks)}end

end {root}

assert_standard_axioms
  {audit}
"""
