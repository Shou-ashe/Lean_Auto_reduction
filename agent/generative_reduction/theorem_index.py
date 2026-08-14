"""Python adapter for the general Lean typed theorem index."""

from __future__ import annotations

import re
import secrets
from pathlib import Path
from typing import Iterable

from agent.hardness.lean_runner import validate_declaration_name, validate_module_name

from .lean_bridge import run_lean_file
from .models import PremiseKind, TheoremIndexEntry, TheoremPremise


MARKER = "GENERAL_REDUCTION_THEOREM_INDEX"
SCHEMA = "general_reduction_theorem_index_v1"
CAPABILITY_RE = re.compile(
    r"\b(?:NativeTMNPHard|NativeTMNPComplete|CertifiedReduction|CertifiedPath|"
    r"CertifiedEquiv|CertifiedPresentationChange)\b"
)
EXCLUDED_PARTS = frozenset(
    {
        "Legacy",
        "Oracles",
        "Oracle",
        "Gold",
        "GoldProofs",
        "HiddenTargets",
        "Regression",
        "Experimental",
    }
)
CORE_IMPORTS = (
    "ComplexityReduction.Agent.GenerativeReduction.TheoremIndex",
    "ComplexityReduction.Agent.GenerativeReduction.RuleApplication",
    "ComplexityReduction.Agent.GenerativeReduction.FinalCheck",
    "ComplexityReduction.Agent.Hardness.Runtime",
)


def _module_for_path(root: Path, path: Path) -> str:
    reference = root.resolve() / "Lean" / "Reference"
    relative = path.resolve().relative_to(reference).with_suffix("")
    return ".".join(relative.parts)


def project_module_catalog(root: Path) -> tuple[str, ...]:
    base = root.resolve() / "Lean" / "Reference" / "ComplexityReduction"
    modules: list[str] = []
    generative_root = (
        base / "Agent" / "GenerativeReduction"
    ).resolve()
    for path in sorted(base.rglob("*.lean")):
        relative = path.relative_to(base).with_suffix("")
        if any(part in EXCLUDED_PARTS for part in relative.parts):
            continue
        if relative.parts[:2] in {("Agent", "Hardness"), ("Agent", "Reduction")}:
            continue
        try:
            path.resolve().relative_to(generative_root)
        except ValueError:
            pass
        else:
            continue
        try:
            source = path.read_text(encoding="utf-8")
        except OSError:
            continue
        if CAPABILITY_RE.search(source):
            modules.append(_module_for_path(root, path))
    return tuple(dict.fromkeys(modules))


def build_probe_source(
    *, input_module: str, problem_declaration: str, modules: Iterable[str], nonce: str
) -> str:
    input_module = validate_module_name(input_module)
    problem_declaration = validate_declaration_name(problem_declaration, label="problem")
    imports = tuple(
        dict.fromkeys([*CORE_IMPORTS, *map(validate_module_name, modules), input_module])
    )
    return "".join(f"import {module}\n" for module in imports) + (
        "\n#generative_reduction_probe_np_hard_theorems "
        f'"{nonce}" {problem_declaration}\n'
    )


def build_typed_goal_probe_source(
    *, modules: Iterable[str], exact_goal: str, nonce: str
) -> str:
    goal = exact_goal.strip()
    if not goal or any(marker in goal for marker in ("\n", "\r", ";", "#", "import ")):
        raise ValueError("typed goal must be one safe Lean term")
    imports = tuple(
        dict.fromkeys([*CORE_IMPORTS, *map(validate_module_name, modules)])
    )
    return "".join(f"import {module}\n" for module in imports) + (
        "\n#generative_reduction_probe_typed_goal "
        f'"{nonce}" ({goal})\n'
    )


def _parse_premises(text: str) -> tuple[TheoremPremise, ...]:
    values: list[TheoremPremise] = []
    for ordinal, raw in enumerate(
        (part.strip() for part in text.split(" || ") if part.strip())
    ):
        kind_text, separator, exact_type = raw.partition("=>")
        if not separator:
            raise ValueError("typed theorem index emitted an invalid premise row")
        try:
            kind = PremiseKind(kind_text)
        except ValueError as error:
            raise ValueError(f"unknown theorem premise kind: {kind_text!r}") from error
        values.append(
            TheoremPremise.create(
                ordinal=ordinal, exact_type=exact_type.strip(), kind=kind
            )
        )
    return tuple(values)


def parse_probe_output(
    *, stdout: str, stderr: str, nonce: str
) -> tuple[TheoremIndexEntry, ...]:
    candidates: list[TheoremIndexEntry] = []
    prefix = f"{MARKER}\t{SCHEMA}\t{nonce}\t"
    saw_goal = False
    for raw_line in (stdout + "\n" + stderr).splitlines():
        marker_at = raw_line.find(prefix)
        if marker_at < 0:
            continue
        fields = raw_line[marker_at:].split("\t")
        if len(fields) < 5:
            raise ValueError("typed theorem index emitted a truncated row")
        kind = fields[3]
        if kind == "goal":
            if len(fields) != 8:
                raise ValueError("typed theorem index emitted an invalid goal row")
            saw_goal = True
            continue
        if kind != "candidate" or len(fields) != 14:
            raise ValueError("typed theorem index emitted an invalid candidate row")
        premises = _parse_premises(fields[9])
        if int(fields[7]) != len(premises):
            raise ValueError("typed theorem index lost premise alignment")
        universes = tuple(item for item in fields[6].split(",") if item)
        candidates.append(
            TheoremIndexEntry(
                declaration=validate_declaration_name(
                    fields[4], label="theorem candidate"
                ),
                module=validate_module_name(fields[5]),
                universe_parameters=universes,
                declaration_type=fields[8],
                premises=premises,
                conclusion_type=fields[10],
                result_fingerprint=fields[11],
                conclusion_head=fields[12],
                provenance=fields[13],
                role_hints=("typed-unified",),
            )
        )
    if not saw_goal:
        raise ValueError("typed theorem index emitted no goal row")
    return tuple(candidates)


def query_theorem_index(
    *,
    root: Path,
    input_module: str,
    problem_declaration: str,
    modules: Iterable[str],
    output_path: Path,
    timeout_seconds: int,
):
    nonce = secrets.token_hex(16)
    source = build_probe_source(
        input_module=input_module,
        problem_declaration=problem_declaration,
        modules=modules,
        nonce=nonce,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")
    command = run_lean_file(
        root=root, path=output_path, timeout_seconds=timeout_seconds
    )
    if not command.ok:
        raise RuntimeError(command.stderr or command.stdout)
    return parse_probe_output(stdout=command.stdout, stderr=command.stderr, nonce=nonce), command


def query_typed_goal_index(
    *,
    root: Path,
    exact_goal: str,
    modules: Iterable[str],
    output_path: Path,
    timeout_seconds: int,
):
    nonce = secrets.token_hex(16)
    source = build_typed_goal_probe_source(
        modules=modules, exact_goal=exact_goal, nonce=nonce
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")
    command = run_lean_file(
        root=root, path=output_path, timeout_seconds=timeout_seconds
    )
    if not command.ok:
        raise RuntimeError(command.stderr or command.stdout)
    return parse_probe_output(stdout=command.stdout, stderr=command.stderr, nonce=nonce), command


__all__ = [
    "CORE_IMPORTS",
    "MARKER",
    "SCHEMA",
    "build_probe_source",
    "build_typed_goal_probe_source",
    "parse_probe_output",
    "project_module_catalog",
    "query_theorem_index",
    "query_typed_goal_index",
]
