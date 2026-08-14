"""Python adapter for the Lean typed theorem index and module catalog."""

from __future__ import annotations

import re
import secrets
from pathlib import Path
from typing import Iterable

from agent.hardness.lean_runner import (
    run_command,
    validate_declaration_name,
    validate_module_name,
)

from .models import TheoremCandidate


MARKER = "REDUCTION_THEOREM_INDEX"
SCHEMA = "reduction_theorem_index_v1"
NATIVE_HARDNESS_RE = re.compile(r"\bNativeTMNPHard\b")
EXCLUDED_PARTS = frozenset(
    {"Legacy", "Oracles", "Oracle", "Gold", "GoldProofs", "HiddenTargets", "Regression"}
)
CORE_IMPORTS = (
    "ComplexityReduction.Agent.Reduction.TheoremIndex",
    "ComplexityReduction.Agent.Reduction.RuleApplication",
    "ComplexityReduction.Agent.Reduction.Reflection",
    "ComplexityReduction.Agent.Hardness.Runtime",
)


def _module_for_path(root: Path, path: Path) -> str:
    reference = root / "Lean" / "Reference"
    relative = path.resolve().relative_to(reference.resolve()).with_suffix("")
    return ".".join(relative.parts)


def project_module_catalog(root: Path) -> tuple[str, ...]:
    """Recall public modules which may export an NP-hard rule.

    This is deliberately a broad textual recall layer.  Lean re-imports every
    hit and performs the authoritative telescope/unification check.
    """

    base = root.resolve() / "Lean" / "Reference" / "ComplexityReduction"
    modules: list[str] = []
    for path in sorted(base.rglob("*.lean")):
        if any(part in EXCLUDED_PARTS for part in path.parts):
            continue
        if path.parent.name == "Reduction" and path.parent.parent.name == "Agent":
            continue
        try:
            source = path.read_text(encoding="utf-8")
        except OSError:
            continue
        if NATIVE_HARDNESS_RE.search(source):
            modules.append(_module_for_path(root, path))
    return tuple(dict.fromkeys(modules))


def build_probe_source(
    *, input_module: str, problem_declaration: str, modules: Iterable[str], nonce: str
) -> str:
    input_module = validate_module_name(input_module)
    problem_declaration = validate_declaration_name(problem_declaration, label="problem")
    imports = tuple(
        dict.fromkeys(
            [*CORE_IMPORTS, *map(validate_module_name, modules), input_module]
        )
    )
    return "".join(f"import {module}\n" for module in imports) + (
        f"\n#reduction_probe_np_hard_theorems \"{nonce}\" {problem_declaration}\n"
    )


def parse_probe_output(*, stdout: str, stderr: str, nonce: str) -> tuple[TheoremCandidate, ...]:
    candidates: list[TheoremCandidate] = []
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
        if kind != "candidate" or len(fields) != 11:
            raise ValueError("typed theorem index emitted an invalid candidate row")
        premise_text = fields[8]
        premises = tuple(part.strip() for part in premise_text.split(" || ") if part.strip())
        candidate = TheoremCandidate(
            declaration=validate_declaration_name(fields[4], label="theorem candidate"),
            module=validate_module_name(fields[5]),
            premise_count=int(fields[6]),
            declaration_type=fields[7],
            premises=premises,
            result_type=fields[9],
            result_fingerprint=fields[10],
        )
        if candidate.premise_count != len(candidate.premises):
            raise ValueError("typed theorem index lost premise alignment")
        candidates.append(candidate)
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
    command = run_command(
        ["lake", "env", "lean", str(output_path)],
        cwd=root.resolve() / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=16 * 1024 * 1024,
    )
    if not command.ok:
        raise RuntimeError(command.stderr or command.stdout)
    return parse_probe_output(stdout=command.stdout, stderr=command.stderr, nonce=nonce), command
