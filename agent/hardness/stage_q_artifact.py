"""Lean artifact emission for the versioned Stage-Q ``prove_in_p`` contract."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable
import textwrap

from .artifact import RUNTIME_MODULE, case_namespace
from .lean_runner import validate_declaration_name, validate_module_name


@dataclass(frozen=True)
class StageQInPArtifactCase:
    case_id: str
    input_module: str
    source_declaration: str
    membership_lean_term: str


def build_stage_q_in_p_batch_artifact_source(
    cases: Iterable[StageQInPArtifactCase],
    *,
    root_namespace: str = "Benchmark.Hardness.StageQInPBatch",
) -> str:
    materialized = tuple(cases)
    if not materialized:
        raise ValueError("Stage-Q P artifact requires at least one accepted case")
    root = validate_declaration_name(root_namespace, label="artifact root namespace")
    modules = sorted({validate_module_name(case.input_module) for case in materialized})
    imports = "".join(
        f"import {module}\n"
        for module in (
            RUNTIME_MODULE,
            "ComplexityReduction.Protocol.InP",
            *modules,
        )
    )
    blocks: list[str] = []
    audited: list[str] = []
    namespaces: set[str] = set()
    for case in materialized:
        source = validate_declaration_name(case.source_declaration, label="source")
        if not isinstance(case.membership_lean_term, str) or not case.membership_lean_term.strip():
            raise ValueError(f"Stage-Q case {case.case_id} has no NativeTMInP term")
        namespace = case_namespace(case.case_id)
        if namespace in namespaces:
            raise ValueError("Stage-Q artifact has colliding case namespaces")
        namespaces.add(namespace)
        proof = textwrap.indent(case.membership_lean_term.strip(), "  ")
        blocks.append(
            f"""namespace {namespace}

def request : ComplexityReduction.Protocol.TypedInPRequestV1 where
  source := .fromPresented {source}
  policy := policy
  objective := .proveInP {source}

noncomputable def deterministicMembership :
    ComplexityReduction.Certificate.NativeTMInP {source} :=
{proof}

noncomputable def result : ComplexityReduction.Protocol.TypedInPResultV1 request :=
  ComplexityReduction.Protocol.TypedInPResultV1.proveInP
    policy (by rfl) deterministicMembership

end {namespace}
"""
        )
        audited.extend(
            (
                f"{root}.{namespace}.deterministicMembership",
                f"{root}.{namespace}.result",
            )
        )
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace {root}

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := false }}

{''.join(blocks)}end

end {root}

assert_standard_axioms
  {audit}
"""


__all__ = ["StageQInPArtifactCase", "build_stage_q_in_p_batch_artifact_source"]
