"""Independent final artifact reconstruction."""

from __future__ import annotations

import re
from typing import Sequence

from agent.hardness.lean_runner import (
    assert_generated_source_is_safe,
    validate_declaration_name,
    validate_module_name,
)

from .models import TheoremIndexEntry
from .premise_registry import PremiseSolution


ROUTE_AUDIT_MODULE = (
    "ComplexityReduction.Agent.GenerativeReduction.RouteAudit"
)


def _validated_forbidden_declarations(
    forbidden_declarations: Sequence[str],
) -> tuple[str, ...]:
    return tuple(
        dict.fromkeys(
            validate_declaration_name(item, label="forbidden declaration")
            for item in forbidden_declarations
        )
    )


def _route_audit_commands(
    *, root_declaration: str, forbidden_declarations: Sequence[str]
) -> str:
    forbidden = _validated_forbidden_declarations(forbidden_declarations)
    return "".join(
        "#generative_reduction_assert_not_transitive_dependency "
        f'{root_declaration} "{declaration}"\n'
        for declaration in forbidden
    )


def _assert_authored_source_avoids_forbidden(
    source: str, forbidden_declarations: Sequence[str]
) -> None:
    for declaration in _validated_forbidden_declarations(forbidden_declarations):
        names = (declaration, declaration.rsplit(".", 1)[-1])
        if any(
            re.search(
                rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
                source,
            )
            for name in names
        ):
            raise ValueError(
                f"authored implementation referenced forbidden declaration {declaration}"
            )


def build_resolver_artifact_source(
    *,
    input_module: str,
    problem_declaration: str,
    forbidden_declarations: Sequence[str] = (),
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    source = f"""import {module}
import ComplexityReduction.Agent.Hardness.Runtime
import ComplexityReduction.Agent.GenerativeReduction.FinalCheck
import {ROUTE_AUDIT_MODULE}

namespace ComplexityReduction.Agent.GenerativeReduction.Generated

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

end ComplexityReduction.Agent.GenerativeReduction.Generated

{_route_audit_commands(
    root_declaration="ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard",
    forbidden_declarations=forbidden_declarations,
)}
assert_standard_axioms
  ComplexityReduction.Agent.GenerativeReduction.Generated.result,
  ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard
"""
    assert_generated_source_is_safe(source)
    return source


def build_theorem_artifact_source(
    *,
    input_module: str,
    problem_declaration: str,
    candidate: TheoremIndexEntry,
    premise_solutions: Sequence[PremiseSolution],
    plugin_imports: Sequence[str] = (),
    forbidden_declarations: Sequence[str] = (),
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    theorem = validate_declaration_name(candidate.declaration, label="theorem")
    theorem_module = validate_module_name(candidate.module)
    if len(premise_solutions) != candidate.premise_count:
        raise ValueError("premise solutions do not match the typed theorem telescope")
    imports = tuple(
        dict.fromkeys(
            (
                module,
                theorem_module,
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                "ComplexityReduction.Agent.GenerativeReduction.FinalCheck",
                ROUTE_AUDIT_MODULE,
                *map(validate_module_name, plugin_imports),
            )
        )
    )
    body = [f"  apply_generative_rule {theorem}"]
    for solution in premise_solutions:
        body.extend(solution.proof_lines)
    source = "".join(f"import {item}\n" for item in imports) + f"""

namespace ComplexityReduction.Agent.GenerativeReduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in

theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} := by
{chr(10).join(body)}

end ComplexityReduction.Agent.GenerativeReduction.Generated

{_route_audit_commands(
    root_declaration="ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard",
    forbidden_declarations=forbidden_declarations,
)}
assert_standard_axioms
  ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard
"""
    assert_generated_source_is_safe(source)
    return source


def build_authored_artifact_source(
    *,
    input_module: str,
    problem_declaration: str,
    implementation: str,
    extra_imports: Sequence[str] = (),
    forbidden_declarations: Sequence[str] = (),
) -> str:
    module = validate_module_name(input_module)
    problem = validate_declaration_name(problem_declaration, label="problem")
    required_signature = (
        "theorem problemIsNPHard :\n"
        f"    ComplexityReduction.Certificate.NativeTMNPHard {problem} := by"
    )
    normalized = "\n".join(line.rstrip() for line in implementation.strip().splitlines())
    _assert_authored_source_avoids_forbidden(normalized, forbidden_declarations)
    compact_required = " ".join(required_signature.split())
    compact_actual = " ".join(normalized.split())
    if compact_required not in compact_actual:
        raise ValueError("authored implementation omitted the frozen root declaration")
    forbidden_commands = (
        "import ",
        "namespace ",
        "end ",
        "axiom ",
        "unsafe ",
        "set_option ",
    )
    if any(
        line.lstrip().startswith(forbidden_commands)
        for line in normalized.splitlines()
    ):
        raise ValueError("authored implementation crossed the editable fence")
    imports = tuple(
        dict.fromkeys(
            (
                module,
                "ComplexityReduction.Agent.GenerativeReduction.FinalCheck",
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                ROUTE_AUDIT_MODULE,
                *map(validate_module_name, extra_imports),
            )
        )
    )
    source = "".join(f"import {item}\n" for item in imports) + f"""

namespace ComplexityReduction.Agent.GenerativeReduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

{normalized}

end ComplexityReduction.Agent.GenerativeReduction.Generated

{_route_audit_commands(
    root_declaration="ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard",
    forbidden_declarations=forbidden_declarations,
)}
assert_standard_axioms
  ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard
"""
    assert_generated_source_is_safe(source)
    return source


__all__ = [
    "build_authored_artifact_source",
    "build_resolver_artifact_source",
    "build_theorem_artifact_source",
]
