"""Final artifact construction and Lean-kernel verification."""

from __future__ import annotations

from pathlib import Path

from agent.hardness.lean_runner import (
    assert_generated_source_is_safe,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)

from .models import TheoremCandidate
from .premise_solvers import PremisePlan


def build_theorem_artifact_source(
    *,
    input_module: str,
    problem_declaration: str,
    candidate: TheoremCandidate,
    premise_plans: tuple[PremisePlan, ...],
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    theorem = validate_declaration_name(candidate.declaration, label="theorem")
    theorem_module = validate_module_name(candidate.module)
    if len(premise_plans) != candidate.premise_count:
        raise ValueError("premise solver plan does not match the typed theorem telescope")
    body = [f"  apply_reduction_theorem {theorem}"]
    for plan in premise_plans:
        body.extend(plan.proof_lines)
    source = f"""import {module}
import {theorem_module}
import ComplexityReduction.Agent.Reduction.RuleApplication
import ComplexityReduction.Agent.Reduction.Reflection
import ComplexityReduction.Agent.Reduction.FinalCheck

namespace ComplexityReduction.Agent.Reduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in

theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} := by
{chr(10).join(body)}

end ComplexityReduction.Agent.Reduction.Generated

assert_standard_axioms ComplexityReduction.Agent.Reduction.Generated.problemIsNPHard
"""
    assert_generated_source_is_safe(source)
    return source


def build_direct_artifact_source(*, input_module: str, problem_declaration: str) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    source = f"""import {module}
import ComplexityReduction.Agent.Hardness.Runtime
import ComplexityReduction.Agent.Reduction.FinalCheck

namespace ComplexityReduction.Agent.Reduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

noncomputable def request : ComplexityReduction.Protocol.TypedNPHardRequestV1 where
  problem := {problem}

noncomputable def result :
    ComplexityReduction.Protocol.TypedNPHardResultV1 request :=
  by_np_hard_resolver

theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} :=
  result.extractNativeHardness

end ComplexityReduction.Agent.Reduction.Generated

assert_standard_axioms
  ComplexityReduction.Agent.Reduction.Generated.result,
  ComplexityReduction.Agent.Reduction.Generated.problemIsNPHard
"""
    assert_generated_source_is_safe(source)
    return source


def verify_artifact(
    *, root: Path, artifact_path: Path, timeout_seconds: int, replay: bool
):
    first = run_command(
        ["lake", "env", "lean", str(artifact_path)],
        cwd=root.resolve() / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=16 * 1024 * 1024,
    )
    second = None
    if first.ok and replay:
        second = run_command(
            ["lake", "env", "lean", str(artifact_path)],
            cwd=root.resolve() / "Lean",
            timeout_seconds=timeout_seconds,
            output_limit=16 * 1024 * 1024,
        )
    return first, second, sha256_file(artifact_path) if first.ok else None
