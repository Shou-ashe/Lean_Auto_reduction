"""Reproducible random hard-side Boolean-CSP supplement generation.

The public benchmark inputs contain only fixed truth tables.  This module
replays the deterministic sampling process and independently checks Schaefer's
six tractable classes, retaining one concrete closure counterexample for every
failed class.  It deliberately does not construct a reduction certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
from itertools import product
import json
from pathlib import Path
from typing import Any, Iterable, Sequence


SCHEMA_VERSION = "boolean_csp_random_supplement_v1"
SAMPLER_VERSION = "splitmix64-conditional-hard-side-v1"
SEED = 20_260_820
CLASS_NAMES = (
    "zero_valid",
    "one_valid",
    "horn",
    "dual_horn",
    "bijunctive",
    "affine",
)


@dataclass(frozen=True)
class RelationSpec:
    arity: int
    mask: int

    def __post_init__(self) -> None:
        if self.arity < 1 or self.arity > 5:
            raise ValueError("random supplement relation arity must be between 1 and 5")
        if self.mask < 0 or self.mask >= 1 << (1 << self.arity):
            raise ValueError("truth-table mask does not fit its relation arity")

    @property
    def accepted_rows(self) -> tuple[int, ...]:
        return tuple(
            row
            for row in range(1 << self.arity)
            if self.mask & (1 << row)
        )

    @property
    def accepted_count(self) -> int:
        return len(self.accepted_rows)

    @property
    def mask_hex(self) -> str:
        width = ((1 << self.arity) + 3) // 4
        return f"0x{self.mask:0{width}X}"

    def row_bits(self, row: int) -> str:
        return f"{row:0{self.arity}b}"


@dataclass(frozen=True)
class CaseProfile:
    ordinal: int
    label: str
    kind: str
    arities: tuple[int, ...]

    @property
    def case_id(self) -> str:
        return f"q-b{self.ordinal:02d}-random-table-{self.label.lower()}"

    @property
    def leaf_module(self) -> str:
        return f"Case{self.ordinal:02d}RandomTable{self.label}"

    @property
    def module(self) -> str:
        return (
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard."
            + self.leaf_module
        )

    @property
    def problem(self) -> str:
        return self.module + ".problem"


@dataclass(frozen=True)
class GeneratedCase:
    profile: CaseProfile
    attempts: int
    relations: tuple[RelationSpec, ...]


PROFILES = (
    CaseProfile(21, "A", "singleton", (4,)),
    CaseProfile(22, "B", "singleton", (5,)),
    CaseProfile(23, "C", "singleton", (4,)),
    CaseProfile(24, "D", "singleton", (5,)),
    CaseProfile(25, "E", "singleton", (4,)),
    CaseProfile(26, "F", "mixed_pair", (3, 3)),
    CaseProfile(27, "G", "mixed_pair", (3, 4)),
    CaseProfile(28, "H", "mixed_pair", (4, 4)),
    CaseProfile(29, "I", "mixed_pair", (4, 5)),
    CaseProfile(30, "J", "mixed_pair", (5, 3)),
)


class SplitMix64:
    """Small version-stable PRNG used instead of Python's global RNG."""

    _MASK = (1 << 64) - 1

    def __init__(self, seed: int) -> None:
        self.state = seed & self._MASK

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & self._MASK
        value = self.state
        value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & self._MASK
        value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & self._MASK
        return value ^ (value >> 31)

    def relation(self, arity: int) -> RelationSpec:
        mask = self.next_u64() & ((1 << (1 << arity)) - 1)
        return RelationSpec(arity=arity, mask=mask)


def _closure_failure(
    relation: RelationSpec,
    *,
    input_count: int,
    operation,
) -> dict[str, Any] | None:
    for inputs in product(relation.accepted_rows, repeat=input_count):
        output = operation(inputs)
        if not relation.mask & (1 << output):
            return {"inputs": tuple(inputs), "output": output}
    return None


def analyze_relation(relation: RelationSpec) -> dict[str, Any]:
    """Return all six class bits and first lexicographic failure witnesses."""

    all_ones = (1 << relation.arity) - 1
    flags = {
        "zero_valid": bool(relation.mask & 1),
        "one_valid": bool(relation.mask & (1 << all_ones)),
    }
    failures: dict[str, dict[str, Any]] = {}
    if not flags["zero_valid"]:
        failures["zero_valid"] = {"inputs": (), "output": 0}
    if not flags["one_valid"]:
        failures["one_valid"] = {"inputs": (), "output": all_ones}

    operations = {
        "horn": (2, lambda values: values[0] & values[1]),
        "dual_horn": (2, lambda values: values[0] | values[1]),
        "bijunctive": (
            3,
            lambda values: (
                (values[0] & values[1])
                | (values[0] & values[2])
                | (values[1] & values[2])
            ),
        ),
        "affine": (3, lambda values: values[0] ^ values[1] ^ values[2]),
    }
    for name, (input_count, operation) in operations.items():
        failure = _closure_failure(
            relation,
            input_count=input_count,
            operation=operation,
        )
        flags[name] = failure is None
        if failure is not None:
            failures[name] = failure
    return {"classes": flags, "failures": failures}


def analyze_language(relations: Sequence[RelationSpec]) -> dict[str, Any]:
    if not relations:
        raise ValueError("a Boolean CSP language must contain a relation")
    relation_analyses = tuple(analyze_relation(relation) for relation in relations)
    classes = {
        name: all(analysis["classes"][name] for analysis in relation_analyses)
        for name in CLASS_NAMES
    }
    failures: dict[str, dict[str, Any]] = {}
    for name in CLASS_NAMES:
        if classes[name]:
            continue
        relation_index = next(
            index
            for index, analysis in enumerate(relation_analyses)
            if not analysis["classes"][name]
        )
        failures[name] = {
            "relation_index": relation_index,
            **relation_analyses[relation_index]["failures"][name],
        }
    return {
        "relations_nonempty": all(relation.accepted_rows for relation in relations),
        "classes": classes,
        "hard_side": not any(classes.values()),
        "failures": failures,
        "relation_analyses": relation_analyses,
    }


def _density_ok(relation: RelationSpec) -> bool:
    row_count = 1 << relation.arity
    margin = max(2, row_count // 4)
    return margin <= relation.accepted_count <= row_count - margin


def _matches_profile(
    profile: CaseProfile,
    relations: tuple[RelationSpec, ...],
) -> bool:
    if any(not _density_ok(relation) for relation in relations):
        return False
    analysis = analyze_language(relations)
    if not analysis["relations_nonempty"] or not analysis["hard_side"]:
        return False
    relation_analyses = analysis["relation_analyses"]
    if profile.kind == "singleton":
        classes = relation_analyses[0]["classes"]
        return not classes["zero_valid"] and not classes["one_valid"]
    if profile.kind == "mixed_pair":
        first = relation_analyses[0]["classes"]
        second = relation_analyses[1]["classes"]
        return (
            first["zero_valid"]
            and not first["one_valid"]
            and second["one_valid"]
            and not second["zero_valid"]
        )
    raise ValueError(f"unknown random Boolean-CSP profile kind: {profile.kind}")


def sample_hard_languages(
    *,
    seed: int = SEED,
    profiles: Iterable[CaseProfile] = PROFILES,
) -> tuple[GeneratedCase, ...]:
    rng = SplitMix64(seed)
    generated: list[GeneratedCase] = []
    seen: set[tuple[tuple[int, int], ...]] = set()
    for profile in profiles:
        for attempts in range(1, 100_001):
            relations = tuple(rng.relation(arity) for arity in profile.arities)
            signature = tuple((relation.arity, relation.mask) for relation in relations)
            if signature in seen or not _matches_profile(profile, relations):
                continue
            seen.add(signature)
            generated.append(
                GeneratedCase(
                    profile=profile,
                    attempts=attempts,
                    relations=relations,
                )
            )
            break
        else:
            raise RuntimeError(f"sampling budget exhausted for {profile.case_id}")
    return tuple(generated)


def _serialized_failure(
    relations: Sequence[RelationSpec],
    failure: dict[str, Any],
) -> dict[str, Any]:
    relation = relations[int(failure["relation_index"])]
    return {
        "relation_index": int(failure["relation_index"]),
        "inputs": [relation.row_bits(int(row)) for row in failure["inputs"]],
        "output": relation.row_bits(int(failure["output"])),
    }


def build_audit_payload(cases: Sequence[GeneratedCase] | None = None) -> dict[str, Any]:
    selected = tuple(cases) if cases is not None else sample_hard_languages()
    rows = []
    for case in selected:
        analysis = analyze_language(case.relations)
        rows.append(
            {
                "case_id": case.profile.case_id,
                "module": case.profile.module,
                "kind": case.profile.kind,
                "sampling_attempts": case.attempts,
                "relations": [
                    {
                        "arity": relation.arity,
                        "mask": relation.mask_hex,
                        "accepted_count": relation.accepted_count,
                        "classes": dict(
                            analysis["relation_analyses"][index]["classes"]
                        ),
                    }
                    for index, relation in enumerate(case.relations)
                ],
                "language_classes": dict(analysis["classes"]),
                "relations_nonempty": bool(analysis["relations_nonempty"]),
                "schaefer_hard_side": bool(analysis["hard_side"]),
                "mathematical_class": "NP-complete",
                "failure_witnesses": {
                    name: _serialized_failure(case.relations, analysis["failures"][name])
                    for name in CLASS_NAMES
                },
            }
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "sampler_version": SAMPLER_VERSION,
        "seed": SEED,
        "selection_rule": {
            "all_relations_nonempty": True,
            "accepted_density_interval": "[1/4, 3/4] with a two-row margin",
            "language_schaefer_class_intersection": [],
            "singleton_endpoints_rejected": ["all-zero", "all-one"],
            "mixed_pair_condition": (
                "first is 0-valid and not 1-valid; "
                "second is 1-valid and not 0-valid"
            ),
        },
        "cases": rows,
    }


def render_case_source(case: GeneratedCase) -> str:
    profile = case.profile
    lines = [
        "import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common",
        "",
        f"/-! Q-B{profile.ordinal:02d}: fixed-seed random Boolean-CSP truth-table language {profile.label}. -/",
        "",
        f"namespace {profile.module}",
        "",
        "open ComplexityReduction",
        "open ComplexityReduction.CSP",
        "open ComplexityReduction.Domain.BooleanCSP",
        "open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common",
        "",
        "noncomputable section",
        "",
    ]
    if profile.kind == "singleton":
        relation = case.relations[0]
        lines.extend(
            (
                f"def relation : BoolRel := truthTableRel {relation.arity} {relation.mask_hex}",
                "",
                "def gamma : Gamma := singletonGamma relation",
            )
        )
    else:
        first, second = case.relations
        lines.extend(
            (
                f"def relationA : BoolRel := truthTableRel {first.arity} {first.mask_hex}",
                f"def relationB : BoolRel := truthTableRel {second.arity} {second.mask_hex}",
                "",
                "def gamma : Gamma := pairGamma relationA relationB",
            )
        )
    lines.extend(
        (
            "def problem : Encoding.PresentedProblem := cspOf gamma",
            "",
            "end",
            f"end {profile.module}",
            "",
            "",
        )
    )
    return "\n".join(lines)


def validate_workspace(root: Path) -> tuple[str, ...]:
    errors: list[str] = []
    cases = sample_hard_languages()
    lean_root = (
        root
        / "Lean"
        / "Reference"
        / "Benchmark"
        / "Hardness"
        / "Inputs"
        / "BooleanCSPNPHard"
    )
    for case in cases:
        path = lean_root / f"{case.profile.leaf_module}.lean"
        expected = render_case_source(case)
        if not path.is_file() or path.read_text(encoding="utf-8") != expected:
            errors.append(f"generated Lean case drifted: {path}")
    receipt_path = root / "Evaluation" / "boolean_csp_random_supplement_v1.json"
    if not receipt_path.is_file():
        errors.append(f"missing random supplement audit receipt: {receipt_path}")
    else:
        actual = json.loads(receipt_path.read_text(encoding="utf-8"))
        if actual != build_audit_payload(cases):
            errors.append(f"random supplement audit receipt drifted: {receipt_path}")
    return tuple(errors)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Replay and audit the fixed-seed random Boolean-CSP supplement"
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    parser.add_argument("--print-audit", action="store_true")
    arguments = parser.parse_args(argv)
    if arguments.print_audit:
        print(json.dumps(build_audit_payload(), ensure_ascii=False, indent=2))
        return 0
    errors = validate_workspace(arguments.root.resolve())
    print(
        json.dumps(
            {
                "schema_version": SCHEMA_VERSION,
                "case_count": len(PROFILES),
                "seed": SEED,
                "passed": not errors,
                "errors": list(errors),
            },
            ensure_ascii=False,
            indent=2,
        )
    )
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "CLASS_NAMES",
    "PROFILES",
    "SCHEMA_VERSION",
    "SEED",
    "GeneratedCase",
    "RelationSpec",
    "analyze_language",
    "analyze_relation",
    "build_audit_payload",
    "render_case_source",
    "sample_hard_languages",
    "validate_workspace",
]
