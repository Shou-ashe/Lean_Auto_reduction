"""Lean-typed construction-basis discovery for independent generators."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
import secrets
from typing import Any, Iterable, Sequence

from agent.hardness.lean_runner import validate_declaration_name, validate_module_name

from .lean_bridge import (
    RECURSIVE_ELABORATION_OPTIONS,
    render_generated_capabilities,
    run_lean_file,
)
from .models import GeneratedCapability, stable_sha256


MARKER = "GENERAL_REDUCTION_CONSTRUCTION_BASIS"
SCHEMA = "general_reduction_construction_basis_v1"
CORE_MODULE = "ComplexityReduction.Agent.GenerativeReduction.ConstructionBasis"
RULE_APPLICATION_MODULE = (
    "ComplexityReduction.Agent.GenerativeReduction.RuleApplication"
)


@dataclass(frozen=True)
class ConstructionBasisEntry:
    declaration: str
    module: str
    declaration_kind: str
    role: str
    dependency_distance: int
    overlap_count: int
    exact_type: str
    definition: str | None = None

    @property
    def basis_id(self) -> str:
        return stable_sha256(
            {
                "declaration": self.declaration,
                "exact_type": self.exact_type,
                "role": self.role,
                "distance": self.dependency_distance,
            }
        )


@dataclass(frozen=True)
class ConstructionBasisReceipt:
    goal_head: str
    goal_head_module: str
    goal_head_kind: str
    goal_head_type: str
    goal_head_definition: str | None
    entries: tuple[ConstructionBasisEntry, ...]
    receipt_hash: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def build_probe_source(
    *,
    modules: Iterable[str],
    exact_goal: str,
    nonce: str,
    generated_capabilities: Sequence[GeneratedCapability] = (),
) -> str:
    # Lean's pretty-printer deliberately wraps large dependent types.  Newlines
    # are therefore normal data here, not command separators.  Collapse all
    # whitespace before embedding the already-parenthesized term and retain the
    # command-level fence for tokens that could escape the probe invocation.
    goal = " ".join(exact_goal.split())
    lowered = goal.lower()
    if not goal or any(marker in goal for marker in (";", "#")) or "import " in lowered:
        raise ValueError("construction-basis goal must be one safe Lean term")
    imports = tuple(
        dict.fromkeys(
            (
                CORE_MODULE,
                RULE_APPLICATION_MODULE,
                *map(validate_module_name, modules),
            )
        )
    )
    return (
        "".join(f"import {module}\n" for module in imports)
        + "\n"
        + RECURSIVE_ELABORATION_OPTIONS
        + "\n"
        + render_generated_capabilities(generated_capabilities)
        + "\n#generative_reduction_probe_construction_basis "
        f'"{nonce}" ({goal})\n'
    )


def build_named_probe_source(
    *,
    modules: Iterable[str],
    declarations: Iterable[str],
    nonce: str,
    generated_capabilities: Sequence[GeneratedCapability] = (),
) -> str:
    imports = tuple(
        dict.fromkeys(
            (
                CORE_MODULE,
                RULE_APPLICATION_MODULE,
                *map(validate_module_name, modules),
            )
        )
    )
    names = tuple(
        dict.fromkeys(
            validate_declaration_name(item, label="requested lookup declaration")
            for item in declarations
        )
    )
    if not names:
        raise ValueError("named construction lookup requires at least one declaration")
    return (
        "".join(f"import {module}\n" for module in imports)
        + "\n"
        + RECURSIVE_ELABORATION_OPTIONS
        + "\n"
        + render_generated_capabilities(generated_capabilities)
        + "\n#generative_reduction_probe_named_declarations "
        f'"{nonce}" "{",".join(names)}"\n'
    )


def parse_probe_output(
    *, stdout: str, stderr: str, nonce: str
) -> ConstructionBasisReceipt:
    prefix = f"{MARKER}\t{SCHEMA}\t{nonce}\t"
    head: tuple[str, str, str, str, str | None] | None = None
    entries: list[ConstructionBasisEntry] = []
    for raw_line in (stdout + "\n" + stderr).splitlines():
        marker_at = raw_line.find(prefix)
        if marker_at < 0:
            continue
        fields = raw_line[marker_at:].split("\t")
        if len(fields) < 5:
            raise ValueError("construction-basis probe emitted a truncated row")
        if fields[3] == "head":
            if len(fields) != 9:
                raise ValueError("construction-basis probe emitted an invalid head row")
            head = (
                validate_declaration_name(fields[4], label="construction goal head"),
                validate_module_name(fields[5]),
                fields[6],
                fields[7],
                fields[8] or None,
            )
            continue
        if fields[3] != "entry" or len(fields) != 12:
            raise ValueError("construction-basis probe emitted an invalid entry row")
        try:
            declaration = validate_declaration_name(
                fields[4], label="construction-basis declaration"
            )
            module = validate_module_name(fields[5])
        except ValueError:
            continue
        entries.append(
            ConstructionBasisEntry(
                declaration=declaration,
                module=module,
                declaration_kind=fields[6],
                role=fields[7],
                dependency_distance=int(fields[8]),
                overlap_count=int(fields[9]),
                exact_type=fields[10],
                definition=fields[11] or None,
            )
        )
    if head is None:
        raise ValueError("construction-basis probe emitted no head row")
    payload = {
        "goal_head": head[0],
        "goal_head_module": head[1],
        "goal_head_kind": head[2],
        "goal_head_type": head[3],
        "goal_head_definition": head[4],
        "entries": entries,
    }
    return ConstructionBasisReceipt(
        **payload,
        receipt_hash=stable_sha256(payload),
    )


def parse_named_probe_output(
    *, stdout: str, stderr: str, nonce: str
) -> tuple[ConstructionBasisEntry, ...]:
    prefix = f"{MARKER}\t{SCHEMA}\t{nonce}\t"
    entries: list[ConstructionBasisEntry] = []
    for raw_line in (stdout + "\n" + stderr).splitlines():
        marker_at = raw_line.find(prefix)
        if marker_at < 0:
            continue
        fields = raw_line[marker_at:].split("\t")
        if len(fields) >= 5 and fields[3] == "missing":
            continue
        if len(fields) != 12 or fields[3] != "named":
            raise ValueError("named construction-basis probe emitted an invalid row")
        entries.append(
            ConstructionBasisEntry(
                declaration=validate_declaration_name(
                    fields[4], label="named construction-basis declaration"
                ),
                module=validate_module_name(fields[5]),
                declaration_kind=fields[6],
                role=fields[7],
                dependency_distance=int(fields[8]),
                overlap_count=int(fields[9]),
                exact_type=fields[10],
                definition=fields[11] or None,
            )
        )
    return tuple(entries)


def query_construction_basis(
    *,
    root: Path,
    exact_goal: str,
    modules: Iterable[str],
    output_path: Path,
    timeout_seconds: int,
    generated_capabilities: Sequence[GeneratedCapability] = (),
):
    nonce = secrets.token_hex(16)
    source = build_probe_source(
        modules=modules,
        exact_goal=exact_goal,
        nonce=nonce,
        generated_capabilities=generated_capabilities,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=root, path=output_path, timeout_seconds=timeout_seconds)
    if not command.ok:
        diagnostic = command.stderr or command.stdout
        if not diagnostic:
            diagnostic = (
                "Lean construction-basis probe failed without output "
                f"(exit_code={command.exit_code}, timed_out={command.timed_out}, "
                f"duration_seconds={command.duration_seconds:.3f}, path={output_path})"
            )
        raise RuntimeError(diagnostic)
    return (
        parse_probe_output(stdout=command.stdout, stderr=command.stderr, nonce=nonce),
        command,
    )


def query_named_declarations(
    *,
    root: Path,
    declarations: Iterable[str],
    modules: Iterable[str],
    output_path: Path,
    timeout_seconds: int,
    generated_capabilities: Sequence[GeneratedCapability] = (),
):
    nonce = secrets.token_hex(16)
    source = build_named_probe_source(
        modules=modules,
        declarations=declarations,
        nonce=nonce,
        generated_capabilities=generated_capabilities,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=root, path=output_path, timeout_seconds=timeout_seconds)
    if not command.ok:
        diagnostic = command.stderr or command.stdout
        if not diagnostic:
            diagnostic = (
                "Lean named construction lookup failed without output "
                f"(exit_code={command.exit_code}, timed_out={command.timed_out}, "
                f"duration_seconds={command.duration_seconds:.3f}, path={output_path})"
            )
        raise RuntimeError(diagnostic)
    return (
        parse_named_probe_output(
            stdout=command.stdout, stderr=command.stderr, nonce=nonce
        ),
        command,
    )


__all__ = [
    "CORE_MODULE",
    "MARKER",
    "SCHEMA",
    "ConstructionBasisEntry",
    "ConstructionBasisReceipt",
    "build_probe_source",
    "build_named_probe_source",
    "parse_probe_output",
    "parse_named_probe_output",
    "query_construction_basis",
    "query_named_declarations",
]
