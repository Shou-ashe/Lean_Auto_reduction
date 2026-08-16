"""Read-only Lean probes and environment snapshots."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
import secrets
from typing import Iterable, Mapping, Sequence

from agent.hardness.lean_runner import (
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)

from .models import GeneratedCapability, PremiseKind, ReusableFragment, stable_sha256


RULE_MARKER = "GENERAL_REDUCTION_RULE_INSTANTIATION"
RULE_SCHEMA = "general_reduction_rule_instantiation_v1"
RULE_PROBE_NAMESPACE = (
    "ComplexityReduction.Agent.GenerativeReduction.RuleInstantiationProbe."
)
RECURSIVE_ELABORATION_OPTIONS = (
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 10000000\n"
)


@dataclass(frozen=True)
class EnvironmentSnapshot:
    lean_toolchain: str
    lake_manifest_sha256: str
    imported_modules: tuple[str, ...]
    import_closure_fingerprint: str
    axiom_policy: str
    snapshot_hash: str

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True)
class RuleSlotReceipt:
    ordinal: int
    kind: PremiseKind
    dependency_ordinals: tuple[int, ...]
    status: str
    exact_type: str
    bound_declaration: str | None
    type_hash: str


@dataclass(frozen=True)
class RuleInstantiationReceipt:
    declaration: str
    target_exact_type: str
    slots: tuple[RuleSlotReceipt, ...]
    receipt_hash: str


def snapshot_environment(
    *, root: Path, imported_modules: Iterable[str], axiom_policy: str
) -> EnvironmentSnapshot:
    root = root.resolve()
    modules = tuple(dict.fromkeys(imported_modules))
    toolchain = (root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_hash = sha256_file(root / "Lean" / "lake-manifest.json")
    closure = stable_sha256({"modules": modules, "toolchain": toolchain})
    snapshot_hash = stable_sha256(
        {
            "toolchain": toolchain,
            "manifest": manifest_hash,
            "closure": closure,
            "axiom_policy": axiom_policy,
        }
    )
    return EnvironmentSnapshot(
        lean_toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
        imported_modules=modules,
        import_closure_fingerprint=closure,
        axiom_policy=axiom_policy,
        snapshot_hash=snapshot_hash,
    )


def run_lean_file(
    *, root: Path, path: Path, timeout_seconds: int, output_limit: int = 16 * 1024 * 1024
):
    return run_command(
        ["lake", "env", "lean", str(path.resolve())],
        cwd=root.resolve() / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=output_limit,
    )


def build_type_defeq_probe_source(
    *,
    modules: Iterable[str],
    first_type: str,
    second_type: str,
    generated_capabilities: Sequence[GeneratedCapability] = (),
) -> str:
    """Build a proof-only bidirectional definitional-equality check."""

    imports = tuple(dict.fromkeys(validate_module_name(item) for item in modules))
    first = _safe_exact_type(first_type)
    second = _safe_exact_type(second_type)
    source = "".join(f"import {module}\n" for module in imports) + f"""

{RECURSIVE_ELABORATION_OPTIONS}
{render_generated_capabilities(generated_capabilities)}

namespace ComplexityReduction.Agent.GenerativeReduction.TypeDefeqProbe

example (value : {first}) : {second} := value
example (value : {second}) : {first} := value

end ComplexityReduction.Agent.GenerativeReduction.TypeDefeqProbe
"""
    return source


def _safe_exact_type(exact_type: str) -> str:
    # Pretty-printed dependent goals routinely span several lines.  Treat
    # whitespace as layout, while retaining the command-level fence against
    # tokens that could escape the parenthesized term supplied by callers.
    value = " ".join(exact_type.split())
    lowered = value.lower()
    if not value or any(marker in value for marker in (";", "#")) or "import " in lowered:
        raise ValueError("exact Lean type must be one safe term")
    return value


def render_generated_capabilities(
    capabilities: Sequence[GeneratedCapability],
) -> str:
    rendered: list[str] = []
    for capability in capabilities:
        namespace = validate_declaration_name(
            capability.namespace, label="generated namespace"
        )
        rendered.append(
            f"namespace {namespace}\n\n{capability.implementation.strip()}\n\nend {namespace}\n"
        )
    return "\n".join(rendered)


def contains_rule_instantiation_probe(value: str) -> bool:
    return RULE_PROBE_NAMESPACE in value


def stable_binding_declaration(fragment: ReusableFragment) -> str | None:
    """Return a stable declaration only when the proof is exactly that declaration."""

    if not fragment.declaration:
        return None
    declaration = validate_declaration_name(
        fragment.declaration, label="bound declaration"
    )
    normalized = " ".join(fragment.proof_term.split())
    if normalized in {
        declaration,
        f"by exact {declaration}",
    }:
        return declaration
    return None


def build_rule_instantiation_probe_source(
    *,
    modules: Iterable[str],
    declaration: str,
    exact_target: str,
    assignments: Mapping[int, ReusableFragment],
    generated_capabilities: Sequence[GeneratedCapability] = (),
    nonce: str,
) -> str:
    theorem = validate_declaration_name(declaration, label="rule declaration")
    target = _safe_exact_type(exact_target)
    imports = tuple(
        dict.fromkeys(
            (
                "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
                *map(validate_module_name, modules),
                *(
                    validate_module_name(fragment.module)
                    for fragment in assignments.values()
                    if fragment.module
                ),
                *(
                    validate_module_name(module)
                    for fragment in assignments.values()
                    for module in fragment.imports
                ),
            )
        )
    )
    namespace = RULE_PROBE_NAMESPACE + f"N{nonce}"
    definitions: list[str] = []
    assignment_rows: list[str] = []
    for ordinal, fragment in sorted(assignments.items()):
        if not fragment.lean_verified:
            raise ValueError("rule binding requires a Lean-verified fragment")
        direct_declaration = stable_binding_declaration(fragment)
        if direct_declaration:
            assignment_rows.append(
                f"{ordinal}=" + direct_declaration
            )
        else:
            bound_name = f"bound{ordinal}"
            definitions.append(
                "noncomputable def "
                f"{bound_name} : {_safe_exact_type(fragment.exact_type)} :=\n"
                f"  {fragment.proof_term.strip()}"
            )
            assignment_rows.append(f"{ordinal}={namespace}.{bound_name}")
    generated = render_generated_capabilities(generated_capabilities)
    return (
        "".join(f"import {module}\n" for module in imports)
        + "\n"
        + RECURSIVE_ELABORATION_OPTIONS
        + "\n"
        + generated
        + f"\nnamespace {namespace}\n\n"
        + "\n\n".join(definitions)
        + f"\n\nend {namespace}\n\n"
        + f'#generative_reduction_probe_rule "{nonce}" {theorem} '
        + f"({target}) \"{','.join(assignment_rows)}\"\n"
    )


def parse_rule_instantiation_output(
    *, stdout: str, stderr: str, nonce: str
) -> RuleInstantiationReceipt:
    prefix = f"{RULE_MARKER}\t{RULE_SCHEMA}\t{nonce}\t"
    declaration: str | None = None
    target: str | None = None
    expected_slot_count: int | None = None
    slots: list[RuleSlotReceipt] = []
    for raw_line in (stdout + "\n" + stderr).splitlines():
        marker_at = raw_line.find(prefix)
        if marker_at < 0:
            continue
        fields = raw_line[marker_at:].split("\t")
        if len(fields) < 5:
            raise ValueError("rule instantiation probe emitted a truncated row")
        if fields[3] == "frame":
            if len(fields) != 7:
                raise ValueError("rule instantiation probe emitted an invalid frame row")
            declaration = validate_declaration_name(fields[4], label="rule declaration")
            target = fields[5]
            expected_slot_count = int(fields[6])
            continue
        if fields[3] != "slot" or len(fields) != 11:
            raise ValueError("rule instantiation probe emitted an invalid slot row")
        dependencies = tuple(
            int(value) for value in fields[6].split(",") if value
        )
        slots.append(
            RuleSlotReceipt(
                ordinal=int(fields[4]),
                kind=PremiseKind(fields[5]),
                dependency_ordinals=dependencies,
                status=fields[7],
                exact_type=fields[8],
                bound_declaration=(fields[9] or None),
                type_hash=fields[10],
            )
        )
    if declaration is None or target is None or expected_slot_count is None:
        raise ValueError("rule instantiation probe emitted no frame row")
    slots.sort(key=lambda item: item.ordinal)
    if len(slots) != expected_slot_count:
        raise ValueError("rule instantiation probe lost slot alignment")
    if tuple(item.ordinal for item in slots) != tuple(range(expected_slot_count)):
        raise ValueError("rule instantiation probe emitted unstable slot ordinals")
    return RuleInstantiationReceipt(
        declaration=declaration,
        target_exact_type=target,
        slots=tuple(slots),
        receipt_hash=stable_sha256(
            {
                "declaration": declaration,
                "target": target,
                "slots": slots,
            }
        ),
    )


def run_rule_instantiation_probe(
    *,
    root: Path,
    modules: Iterable[str],
    declaration: str,
    exact_target: str,
    assignments: Mapping[int, ReusableFragment],
    generated_capabilities: Sequence[GeneratedCapability],
    output_path: Path,
    timeout_seconds: int,
):
    nonce = secrets.token_hex(12)
    source = build_rule_instantiation_probe_source(
        modules=modules,
        declaration=declaration,
        exact_target=exact_target,
        assignments=assignments,
        generated_capabilities=generated_capabilities,
        nonce=nonce,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=root, path=output_path, timeout_seconds=timeout_seconds)
    if not command.ok:
        diagnostic = command.stderr or command.stdout
        if not diagnostic:
            diagnostic = (
                "Lean rule instantiation probe failed without output "
                f"(exit_code={command.exit_code}, timed_out={command.timed_out}, "
                f"duration_seconds={command.duration_seconds:.3f}, "
                f"path={output_path})"
            )
        raise RuntimeError(diagnostic)
    return (
        parse_rule_instantiation_output(
            stdout=command.stdout, stderr=command.stderr, nonce=nonce
        ),
        command,
    )


__all__ = [
    "EnvironmentSnapshot",
    "RULE_MARKER",
    "RULE_SCHEMA",
    "RECURSIVE_ELABORATION_OPTIONS",
    "RULE_PROBE_NAMESPACE",
    "RuleInstantiationReceipt",
    "RuleSlotReceipt",
    "build_rule_instantiation_probe_source",
    "build_type_defeq_probe_source",
    "contains_rule_instantiation_probe",
    "parse_rule_instantiation_output",
    "render_generated_capabilities",
    "run_lean_file",
    "run_rule_instantiation_probe",
    "snapshot_environment",
    "stable_binding_declaration",
]
