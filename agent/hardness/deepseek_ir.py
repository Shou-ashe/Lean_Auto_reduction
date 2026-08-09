"""Batch sources for the experimental DeepSeek IR route-selection study."""

from __future__ import annotations

import textwrap
from collections.abc import Iterable, Mapping

from .benchmark import BenchmarkCase
from .artifact import case_namespace
from .catalog import FLAT_API_CATALOG, IR_COMPONENTS_CATALOG
from .lean_runner import RUNTIME_MODULE, validate_declaration_name, validate_module_name
from .models import RouteCandidate


def build_batch_probe_source(
    cases: Iterable[BenchmarkCase], *, nonces: Mapping[str, str]
) -> str:
    materialized = tuple(cases)
    modules = sorted({validate_module_name(case.module) for case in materialized})
    imports = "".join(f"import {module}\n" for module in (RUNTIME_MODULE, *modules))
    commands: list[str] = []
    for case in materialized:
        if case.objective != "reduce_to" or not case.target:
            raise ValueError("DeepSeek IR batch accepts only fixed-target reduce_to cases")
        source = validate_declaration_name(case.source, label="source")
        target = validate_declaration_name(case.target, label="target")
        nonce = nonces.get(case.id)
        if not nonce:
            raise ValueError(f"missing nonce for DeepSeek benchmark case {case.id}")
        commands_by_mode = {
            FLAT_API_CATALOG: "#hardness_probe_to_flat",
            IR_COMPONENTS_CATALOG: "#hardness_probe_to_ir",
        }
        command = commands_by_mode.get(case.catalog_mode)
        if command is None:
            raise ValueError("DeepSeek IR batch requires flat_api or ir_components catalog")
        commands.append(f'{command} "{nonce}" {source} {target}')
    return imports + "\n" + "\n".join(commands) + "\n"


def certified_path_term(route: RouteCandidate, *, source_declaration: str) -> str:
    atoms = tuple(validate_declaration_name(atom, label="route atom") for atom in route.atoms)
    if not atoms:
        source = validate_declaration_name(source_declaration, label="source")
        return f"ComplexityReduction.Certificate.CertifiedPath.refl {source}"
    path = f"ComplexityReduction.Certificate.CertifiedPath.step {atoms[0]}"
    for atom in atoms[1:]:
        path = (
            "ComplexityReduction.Certificate.CertifiedPath.cons\n"
            f"      ({path})\n"
            f"      {atom}"
        )
    return path


def build_batch_artifact_source(
    selections: Iterable[tuple[BenchmarkCase, RouteCandidate]],
) -> str:
    materialized = tuple(selections)
    if not materialized:
        raise ValueError("DeepSeek batch artifact requires at least one selected route")
    modules = sorted({validate_module_name(case.module) for case, _ in materialized})
    imports = "".join(f"import {module}\n" for module in (RUNTIME_MODULE, *modules))
    blocks: list[str] = []
    audited: list[str] = []
    used_namespaces: set[str] = set()
    for case, route in materialized:
        if not case.target:
            raise ValueError("DeepSeek batch artifact requires a fixed target")
        source = validate_declaration_name(case.source, label="source")
        target = validate_declaration_name(case.target, label="target")
        namespace = case_namespace(case.id)
        if namespace in used_namespaces:
            raise ValueError("DeepSeek batch artifact has colliding case namespaces")
        used_namespaces.add(namespace)
        path_term = certified_path_term(route, source_declaration=source)
        blocks.append(
            f"""namespace {namespace}

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented {source}
  policy := policy
  objective := .reduceTo {source} {target}

noncomputable def selectedPath :
    ComplexityReduction.Certificate.CertifiedPath {source} {target} :=
  {path_term}

noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath
    policy (by rfl) selectedPath

end {namespace}
"""
        )
        audited.extend(
            (
                f"Benchmark.Hardness.DeepSeekIRBatch.{namespace}.selectedPath",
                f"Benchmark.Hardness.DeepSeekIRBatch.{namespace}.result",
            )
        )
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace Benchmark.Hardness.DeepSeekIRBatch

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

{''.join(blocks)}
end

end Benchmark.Hardness.DeepSeekIRBatch

assert_standard_axioms
  {audit}
"""


def build_batch_codegen_artifact_source(
    selections: Iterable[tuple[BenchmarkCase, str]],
) -> str:
    """Wrap model-authored ``CertifiedPath`` terms in one final Lean artifact."""

    materialized = tuple(selections)
    if not materialized:
        raise ValueError("DeepSeek codegen artifact requires at least one Lean term")
    modules = sorted({validate_module_name(case.module) for case, _ in materialized})
    imports = "".join(f"import {module}\n" for module in (RUNTIME_MODULE, *modules))
    blocks: list[str] = []
    audited: list[str] = []
    used_namespaces: set[str] = set()
    for case, lean_term in materialized:
        if case.objective != "reduce_to" or not case.target:
            raise ValueError("DeepSeek codegen requires a fixed-target reduce_to case")
        source = validate_declaration_name(case.source, label="source")
        target = validate_declaration_name(case.target, label="target")
        if not isinstance(lean_term, str) or not lean_term.strip():
            raise ValueError(f"DeepSeek case {case.id} has no Lean path term")
        namespace = case_namespace(case.id)
        if namespace in used_namespaces:
            raise ValueError("DeepSeek codegen artifact has colliding case namespaces")
        used_namespaces.add(namespace)
        rendered_term = textwrap.indent(lean_term.strip(), "  ")
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
                f"Benchmark.Hardness.DeepSeekIRCodegen.{namespace}.selectedPath",
                f"Benchmark.Hardness.DeepSeekIRCodegen.{namespace}.result",
            )
        )
    audit = ",\n  ".join(audited)
    return f"""{imports}
namespace Benchmark.Hardness.DeepSeekIRCodegen

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  {{ presentation := .exactUser, requireNativeNP := true }}

{''.join(blocks)}
end

end Benchmark.Hardness.DeepSeekIRCodegen

assert_standard_axioms
  {audit}
"""
