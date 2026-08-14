"""Independent final artifact reconstruction."""

from __future__ import annotations

import re
from typing import Mapping, Sequence

from agent.hardness.lean_runner import (
    assert_generated_source_is_safe,
    validate_declaration_name,
    validate_module_name,
)

from .lean_bridge import RECURSIVE_ELABORATION_OPTIONS, render_generated_capabilities
from .models import (
    ApplicationFrame,
    GeneratedCapability,
    ReusableFragment,
    TheoremIndexEntry,
)
from .proof_state import ProofState
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


def _safe_exact_type(exact_type: str) -> str:
    value = exact_type.strip()
    if not value or any(marker in value for marker in ("\n", "\r", ";", "#", "import ")):
        raise ValueError("exact Lean type must be one safe term")
    return value


def _proof_body(candidate: TheoremIndexEntry, premise_solutions: Sequence[PremiseSolution]) -> str:
    body = [f"  apply_generative_rule {candidate.declaration}"]
    for solution in premise_solutions:
        body.extend(solution.proof_lines)
    return "\n".join(body)


def _indent_block(value: str, spaces: int) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line else prefix for line in value.splitlines())


def build_goal_fragment_check_source(
    *,
    input_module: str,
    exact_type: str,
    candidate: TheoremIndexEntry,
    premise_solutions: Sequence[PremiseSolution],
    extra_imports: Sequence[str] = (),
    generated_capabilities: Sequence[GeneratedCapability] = (),
) -> tuple[str, str]:
    if len(premise_solutions) != candidate.premise_count:
        raise ValueError("premise solutions do not match the typed theorem telescope")
    imports = tuple(
        dict.fromkeys(
            (
                validate_module_name(input_module),
                validate_module_name(candidate.module),
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                *map(validate_module_name, extra_imports),
            )
        )
    )
    proof_term = "by\n" + _proof_body(candidate, premise_solutions)
    source = (
        "".join(f"import {module}\n" for module in imports)
        + "\n"
        + RECURSIVE_ELABORATION_OPTIONS
        + "\n"
        + render_generated_capabilities(generated_capabilities)
        + "\nnamespace ComplexityReduction.Agent.GenerativeReduction.FragmentCheck\n\n"
        + "noncomputable def checkedFragment : "
        + _safe_exact_type(exact_type)
        + " := by\n"
        + _proof_body(candidate, premise_solutions)
        + "\n\nend ComplexityReduction.Agent.GenerativeReduction.FragmentCheck\n"
    )
    assert_generated_source_is_safe(source)
    return source, proof_term


def build_frame_check_source(
    *,
    input_module: str,
    frame: ApplicationFrame,
    slot_fragments: Mapping[int, ReusableFragment],
    generated_capabilities: Sequence[GeneratedCapability] = (),
    extra_imports: Sequence[str] = (),
) -> tuple[str, str]:
    missing = [slot.ordinal for slot in frame.slots if slot.ordinal not in slot_fragments]
    if missing:
        raise ValueError(f"application frame has unfilled slots: {missing!r}")
    imports = tuple(
        dict.fromkeys(
            (
                validate_module_name(input_module),
                *(
                    (validate_module_name(frame.declaration_module),)
                    if frame.declaration_module
                    else ()
                ),
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                *map(validate_module_name, extra_imports),
                *(
                    validate_module_name(fragment.module)
                    for fragment in slot_fragments.values()
                    if fragment.module
                ),
                *(
                    validate_module_name(module)
                    for fragment in slot_fragments.values()
                    for module in fragment.imports
                ),
            )
        )
    )
    proof_lines = ["by", f"  apply_generative_rule_exact {frame.declaration} ["]
    for ordinal in range(len(frame.slots)):
        proof = slot_fragments[ordinal].proof_term.strip()
        suffix = "," if ordinal + 1 < len(frame.slots) else ""
        proof_lines.append("    (")
        proof_lines.append(_indent_block(proof, 6))
        proof_lines.append(f"    ){suffix}")
    proof_lines.append("  ]")
    proof_term = "\n".join(proof_lines)
    check_name = "frame_" + re.sub(r"[^A-Za-z0-9_]", "_", frame.frame_id)
    source = (
        "".join(f"import {module}\n" for module in imports)
        + "\n"
        + RECURSIVE_ELABORATION_OPTIONS
        + "\n"
        + render_generated_capabilities(generated_capabilities)
        + "\nnamespace ComplexityReduction.Agent.GenerativeReduction.FrameCheck\n\n"
        + f"noncomputable def {check_name} : {_safe_exact_type(frame.parent_exact_type)} :=\n"
        + _indent_block(proof_term, 2)
        + "\n\nend ComplexityReduction.Agent.GenerativeReduction.FrameCheck\n"
    )
    assert_generated_source_is_safe(source)
    return source, proof_term


def build_search_artifact_source(
    *,
    completed_state: ProofState,
    input_module: str,
    problem_declaration: str,
    forbidden_declarations: Sequence[str] = (),
    extra_imports: Sequence[str] = (),
) -> str:
    if not completed_state.complete or completed_state.root_fragment is None:
        raise ValueError("search artifact requires a complete, frame-verified state")
    root_fragment = completed_state.root_fragment
    if root_fragment.exact_type.strip() != completed_state.root_goal.exact_type.strip():
        raise ValueError("root fragment exact type does not match the frozen root goal")
    imports = tuple(
        dict.fromkeys(
            (
                validate_module_name(input_module),
                "ComplexityReduction.Agent.GenerativeReduction.FinalCheck",
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                ROUTE_AUDIT_MODULE,
                *map(validate_module_name, extra_imports),
                *(
                    validate_module_name(frame.declaration_module)
                    for frame in completed_state.application_frames
                    if frame.declaration_module
                ),
                *(
                    validate_module_name(fragment.module)
                    for fragment in completed_state.completed_fragments
                    if fragment.module
                ),
                *(
                    validate_module_name(module)
                    for fragment in completed_state.completed_fragments
                    for module in fragment.imports
                ),
            )
        )
    )
    problem = validate_declaration_name(problem_declaration, label="problem")
    generated = render_generated_capabilities(completed_state.generated_capabilities)
    source = "".join(f"import {module}\n" for module in imports) + f"""

{RECURSIVE_ELABORATION_OPTIONS}
{generated}

namespace ComplexityReduction.Agent.GenerativeReduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard {problem} :=
{_indent_block(root_fragment.proof_term.strip(), 2)}

end ComplexityReduction.Agent.GenerativeReduction.Generated

{_route_audit_commands(
    root_declaration="ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard",
    forbidden_declarations=forbidden_declarations,
)}
assert_standard_axioms
  ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard
"""
    _assert_authored_source_avoids_forbidden(generated, forbidden_declarations)
    assert_generated_source_is_safe(source)
    return source


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

{RECURSIVE_ELABORATION_OPTIONS}
namespace ComplexityReduction.Agent.GenerativeReduction.Generated

open ComplexityReduction
open ComplexityReduction.Certificate

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

{RECURSIVE_ELABORATION_OPTIONS}
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


def build_authored_capability_source(
    *,
    input_module: str,
    exact_type: str,
    namespace: str,
    declaration_name: str,
    implementation: str,
    extra_imports: Sequence[str] = (),
    generated_capabilities: Sequence[GeneratedCapability] = (),
    forbidden_declarations: Sequence[str] = (),
) -> tuple[str, str]:
    module = validate_module_name(input_module)
    namespace = validate_declaration_name(namespace, label="generated namespace")
    declaration_name = validate_declaration_name(
        declaration_name, label="generated capability"
    )
    if "." in declaration_name:
        raise ValueError("generated capability name must be namespace-local")
    expected = _safe_exact_type(exact_type)
    normalized = "\n".join(line.rstrip() for line in implementation.strip().splitlines())
    required_signature = f"noncomputable def {declaration_name} : {expected} := by"
    if " ".join(required_signature.split()) not in " ".join(normalized.split()):
        raise ValueError("authored implementation omitted the frozen child capability declaration")
    _assert_authored_source_avoids_forbidden(normalized, forbidden_declarations)
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
        raise ValueError("authored child capability crossed the editable fence")
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
    full_declaration = f"{namespace}.{declaration_name}"
    source = "".join(f"import {item}\n" for item in imports) + f"""

{RECURSIVE_ELABORATION_OPTIONS}
{render_generated_capabilities(generated_capabilities)}

namespace {namespace}

open ComplexityReduction
open ComplexityReduction.Certificate

{normalized}

end {namespace}

{_route_audit_commands(
    root_declaration=full_declaration,
    forbidden_declarations=forbidden_declarations,
)}
assert_standard_axioms {full_declaration}
"""
    assert_generated_source_is_safe(source)
    return source, full_declaration


__all__ = [
    "build_authored_capability_source",
    "build_authored_artifact_source",
    "build_frame_check_source",
    "build_goal_fragment_check_source",
    "build_resolver_artifact_source",
    "build_search_artifact_source",
    "build_theorem_artifact_source",
]
