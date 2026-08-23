"""Isolated loader for the non-scoring Boolean-CSP gadget-authoring canary."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from typing import Any, Mapping

from .boolean_csp_np_hard_benchmark import (
    BooleanCSPBenchmarkError,
    BooleanCSPCase,
    BooleanCSPSuite,
)


SUITE_SCHEMA = "boolean_csp_gadget_authoring_dev_suite_v1"
SUITE_ID = "boolean-csp-gadget-authoring-dev-v1"
CASE_COUNT = 4
CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9-]*")
DECL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
PUBLIC_CASE_FIELDS = frozenset(
    {"case_id", "split", "module", "problem", "budget_profile"}
)
FORBIDDEN_PUBLIC_KEYS = frozenset(
    {
        "answer",
        "expected",
        "expected_public_status",
        "gold",
        "hint",
        "oracle",
        "route",
        "solution",
    }
)


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise BooleanCSPBenchmarkError(
            f"{label} fields differ: missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}"
        )


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def load_gadget_authoring_dev_suite(path: Path) -> BooleanCSPSuite:
    """Load the four-case, answer-free development canary outside scoring."""

    resolved = path.resolve()
    try:
        with resolved.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, json.JSONDecodeError) as error:
        raise BooleanCSPBenchmarkError(
            f"cannot read Boolean-CSP gadget-authoring development suite: {resolved}"
        ) from error
    if not isinstance(value, dict):
        raise BooleanCSPBenchmarkError(
            "Boolean-CSP gadget-authoring development suite must be a JSON object"
        )
    _exact_keys(
        value,
        {"schema_version", "suite_id", "objective", "final_lean_type", "cases"},
        label="Boolean-CSP gadget-authoring development suite",
    )
    if value["schema_version"] != SUITE_SCHEMA or value["suite_id"] != SUITE_ID:
        raise BooleanCSPBenchmarkError(
            "unsupported Boolean-CSP gadget-authoring development suite identity"
        )
    if value["objective"] != "prove_np_hard":
        raise BooleanCSPBenchmarkError(
            "Boolean-CSP development suite objective must be prove_np_hard"
        )
    if value["final_lean_type"] != (
        "ComplexityReduction.Certificate.NativeTMNPHard input"
    ):
        raise BooleanCSPBenchmarkError(
            "Boolean-CSP development suite changed its final Lean type"
        )

    raw_cases = value["cases"]
    if not isinstance(raw_cases, list) or len(raw_cases) != CASE_COUNT:
        raise BooleanCSPBenchmarkError(
            f"Boolean-CSP gadget-authoring development suite must contain exactly "
            f"{CASE_COUNT} cases"
        )
    cases: list[BooleanCSPCase] = []
    for index, raw in enumerate(raw_cases):
        if not isinstance(raw, dict):
            raise BooleanCSPBenchmarkError(f"development case {index} must be an object")
        _exact_keys(raw, set(PUBLIC_CASE_FIELDS), label=f"development case {index}")
        if FORBIDDEN_PUBLIC_KEYS.intersection(raw):
            raise BooleanCSPBenchmarkError(
                f"development case {index} leaks oracle material"
            )
        case_id = raw["case_id"]
        module = raw["module"]
        problem = raw["problem"]
        if not isinstance(case_id, str) or CASE_ID_RE.fullmatch(case_id) is None:
            raise BooleanCSPBenchmarkError(
                f"development case {index} has an invalid case_id"
            )
        if raw["split"] != "dev":
            raise BooleanCSPBenchmarkError(
                f"development case {case_id} must use the dev split"
            )
        if (
            not isinstance(module, str)
            or DECL_RE.fullmatch(module) is None
            or not module.startswith("Benchmark.Hardness.Inputs.BooleanCSPNPHard.")
        ):
            raise BooleanCSPBenchmarkError(
                f"development case {case_id} has an invalid module"
            )
        if (
            not isinstance(problem, str)
            or DECL_RE.fullmatch(problem) is None
            or not problem.startswith(module + ".")
        ):
            raise BooleanCSPBenchmarkError(
                f"development case {case_id} has an invalid problem"
            )
        if raw["budget_profile"] != "formal-default":
            raise BooleanCSPBenchmarkError(
                f"development case {case_id} has an invalid budget profile"
            )
        cases.append(
            BooleanCSPCase(
                case_id=case_id,
                split="dev",
                module=module,
                problem=problem,
                budget_profile="formal-default",
            )
        )

    ids = [case.case_id for case in cases]
    modules = [case.module for case in cases]
    problems = [case.problem for case in cases]
    if len(set(ids)) != CASE_COUNT:
        raise BooleanCSPBenchmarkError(
            "Boolean-CSP gadget-authoring development suite repeats a case_id"
        )
    if len(set(modules)) != CASE_COUNT or len(set(problems)) != CASE_COUNT:
        raise BooleanCSPBenchmarkError(
            "each gadget-authoring development case needs an isolated module/problem"
        )
    return BooleanCSPSuite(
        suite_id=value["suite_id"],
        objective=value["objective"],
        final_lean_type=value["final_lean_type"],
        cases=tuple(cases),
        path=resolved,
        sha256=_sha256_file(resolved),
    )


__all__ = ["load_gadget_authoring_dev_suite"]
