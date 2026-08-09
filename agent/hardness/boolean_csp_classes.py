"""Finite Boolean-CSP languages and Schaefer-class classification.

This module is intentionally independent from benchmark expected outcomes.  A
``Gamma`` value is a finite, canonical set of finite truth tables; classification
is computed from the tables themselves.  The SHA-256 fingerprint is therefore a
stable input identity, not a human supplied label.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import hashlib
import json
from itertools import product
from types import MappingProxyType
from typing import Iterable, Mapping, Sequence


class BooleanCSPContractError(ValueError):
    """A stable rejection at the class-level Boolean-CSP boundary."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


BoolRow = tuple[bool, ...]


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("ascii")


def _freeze_json(value: object) -> object:
    if isinstance(value, dict):
        return MappingProxyType({key: _freeze_json(child) for key, child in value.items()})
    if isinstance(value, list):
        return tuple(_freeze_json(child) for child in value)
    return value


def _thaw_json(value: object) -> object:
    if isinstance(value, Mapping):
        return {key: _thaw_json(child) for key, child in value.items()}
    if isinstance(value, tuple):
        return [_thaw_json(child) for child in value]
    return value


@dataclass(frozen=True, order=True)
class BooleanRelation:
    """A Boolean relation represented by its complete finite accepting table."""

    arity: int
    rows: tuple[BoolRow, ...]

    def __post_init__(self) -> None:
        if isinstance(self.arity, bool) or not isinstance(self.arity, int):
            raise BooleanCSPContractError("invalid_relation", "arity must be an integer")
        if self.arity < 0:
            raise BooleanCSPContractError("invalid_relation", "arity must be nonnegative")
        if not isinstance(self.rows, tuple):
            raise BooleanCSPContractError(
                "nonfinite_relation", "rows must be a materialized finite tuple"
            )
        normalized: list[BoolRow] = []
        for index, row in enumerate(self.rows):
            if not isinstance(row, tuple):
                raise BooleanCSPContractError(
                    "nonfinite_relation",
                    f"row {index} must be a materialized finite tuple",
                )
            if len(row) != self.arity:
                raise BooleanCSPContractError(
                    "invalid_relation",
                    f"row {index} has length {len(row)}, expected {self.arity}",
                )
            if any(type(value) is not bool for value in row):
                raise BooleanCSPContractError(
                    "invalid_relation", f"row {index} contains a non-Boolean value"
                )
            normalized.append(row)
        canonical = tuple(sorted(set(normalized)))
        if canonical != self.rows:
            object.__setattr__(self, "rows", canonical)

    @classmethod
    def from_rows(cls, arity: int, rows: Sequence[Sequence[bool]]) -> "BooleanRelation":
        if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes, bytearray)):
            raise BooleanCSPContractError(
                "nonfinite_relation", "rows must be a finite sequence"
            )
        return cls(arity, tuple(tuple(row) for row in rows))

    @property
    def row_set(self) -> frozenset[BoolRow]:
        return frozenset(self.rows)

    def holds(self, row: Sequence[bool]) -> bool:
        materialized = tuple(row)
        if len(materialized) != self.arity or any(type(value) is not bool for value in materialized):
            raise BooleanCSPContractError(
                "invalid_tuple", f"expected a Boolean tuple of arity {self.arity}"
            )
        return materialized in self.row_set

    @property
    def table_bits(self) -> str:
        accepted = self.row_set
        return "".join(
            "1" if row in accepted else "0"
            for row in product((False, True), repeat=self.arity)
        )

    @property
    def canonical_payload(self) -> Mapping[str, object]:
        return MappingProxyType({"arity": self.arity, "table_bits": self.table_bits})

    @property
    def fingerprint(self) -> str:
        return "sha256:" + hashlib.sha256(_canonical_json(dict(self.canonical_payload))).hexdigest()

    @property
    def is_zero_valid(self) -> bool:
        return (False,) * self.arity in self.row_set

    @property
    def is_one_valid(self) -> bool:
        return (True,) * self.arity in self.row_set

    def _closed_under_binary(self, operation) -> bool:
        rows = self.row_set
        return all(
            tuple(operation(left[i], right[i]) for i in range(self.arity)) in rows
            for left in rows
            for right in rows
        )

    def _closed_under_ternary(self, operation) -> bool:
        rows = self.row_set
        return all(
            tuple(operation(first[i], second[i], third[i]) for i in range(self.arity))
            in rows
            for first in rows
            for second in rows
            for third in rows
        )

    @property
    def is_horn(self) -> bool:
        # Boolean relations definable by Horn CNF are exactly meet-closed relations.
        return self._closed_under_binary(lambda left, right: left and right)

    @property
    def is_dual_horn(self) -> bool:
        return self._closed_under_binary(lambda left, right: left or right)

    @property
    def is_bijunctive(self) -> bool:
        return self._closed_under_ternary(
            lambda first, second, third: (first and second) or (first and third) or (second and third)
        )

    @property
    def is_affine(self) -> bool:
        return self._closed_under_ternary(
            lambda first, second, third: first ^ second ^ third
        )


class SchaeferClass(str, Enum):
    ZERO_VALID = "zero_valid"
    ONE_VALID = "one_valid"
    HORN = "horn"
    DUAL_HORN = "dual_horn"
    BIJUNCTIVE = "bijunctive"
    AFFINE = "affine"


@dataclass(frozen=True)
class GammaClassification:
    classes: frozenset[SchaeferClass]

    @property
    def tractable(self) -> bool:
        return bool(self.classes)

    def contains(self, class_name: SchaeferClass | str) -> bool:
        return SchaeferClass(class_name) in self.classes


@dataclass(frozen=True)
class Gamma:
    """A finite relation *set* Γ with a canonical order and identity."""

    relations: tuple[BooleanRelation, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.relations, tuple):
            raise BooleanCSPContractError(
                "infinite_gamma",
                "Gamma must be a materialized finite tuple, not an iterable or predicate",
            )
        if any(not isinstance(relation, BooleanRelation) for relation in self.relations):
            raise BooleanCSPContractError(
                "invalid_gamma", "every Gamma member must be a BooleanRelation"
            )
        canonical = tuple(sorted(set(self.relations)))
        if canonical != self.relations:
            object.__setattr__(self, "relations", canonical)

    @classmethod
    def finite(cls, relations: Sequence[BooleanRelation]) -> "Gamma":
        if not isinstance(relations, Sequence) or isinstance(
            relations, (str, bytes, bytearray)
        ):
            raise BooleanCSPContractError(
                "infinite_gamma", "Gamma must be supplied as a finite sequence"
            )
        return cls(tuple(relations))

    @property
    def canonical_payload(self) -> Mapping[str, object]:
        return MappingProxyType(
            {
                "schema_version": "boolean_csp_gamma_v1",
                "relations": [dict(relation.canonical_payload) for relation in self.relations],
            }
        )

    @property
    def fingerprint(self) -> str:
        digest = hashlib.sha256(_canonical_json(dict(self.canonical_payload))).hexdigest()
        return "sha256:" + digest

    def classify(self) -> GammaClassification:
        checks = {
            SchaeferClass.ZERO_VALID: all(r.is_zero_valid for r in self.relations),
            SchaeferClass.ONE_VALID: all(r.is_one_valid for r in self.relations),
            SchaeferClass.HORN: all(r.is_horn for r in self.relations),
            SchaeferClass.DUAL_HORN: all(r.is_dual_horn for r in self.relations),
            SchaeferClass.BIJUNCTIVE: all(r.is_bijunctive for r in self.relations),
            SchaeferClass.AFFINE: all(r.is_affine for r in self.relations),
        }
        return GammaClassification(frozenset(name for name, holds in checks.items() if holds))


@dataclass(frozen=True)
class BooleanCSPProblemClass:
    """A class-level benchmark input, including structural restrictions."""

    class_id: str
    gamma: Gamma
    structural_constraints: Mapping[str, object] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not isinstance(self.class_id, str) or not self.class_id.strip():
            raise BooleanCSPContractError("invalid_problem_class", "class_id is required")
        if not isinstance(self.gamma, Gamma):
            raise BooleanCSPContractError("invalid_problem_class", "gamma must be finite")
        if not isinstance(self.structural_constraints, Mapping):
            raise BooleanCSPContractError(
                "invalid_problem_class", "structural_constraints must be a mapping"
            )
        try:
            normalized = json.loads(
                json.dumps(self.structural_constraints, sort_keys=True, separators=(",", ":"))
            )
        except (TypeError, ValueError) as error:
            raise BooleanCSPContractError(
                "invalid_problem_class", "structural constraints must be canonical JSON data"
            ) from error
        object.__setattr__(self, "structural_constraints", _freeze_json(normalized))

    @property
    def canonical_payload(self) -> Mapping[str, object]:
        return MappingProxyType(
            {
                "schema_version": "boolean_csp_problem_class_v1",
                "gamma_fingerprint": self.gamma.fingerprint,
                "structural_constraints": _thaw_json(self.structural_constraints),
            }
        )

    @property
    def fingerprint(self) -> str:
        return "sha256:" + hashlib.sha256(
            _canonical_json(dict(self.canonical_payload))
        ).hexdigest()


class RegisteredComplexity(str, Enum):
    P = "P"
    NPC = "NPC"


@dataclass(frozen=True)
class GammaRegistration:
    fingerprint: str
    complexity: RegisteredComplexity
    evidence_id: str


class GammaClassificationRegistry:
    """Run-local single-class registry; opposite P/NPC claims fail closed."""

    def __init__(self) -> None:
        self._registrations: dict[str, GammaRegistration] = {}

    def register(
        self,
        problem_class: BooleanCSPProblemClass,
        complexity: RegisteredComplexity | str,
        *,
        evidence_id: str,
    ) -> GammaRegistration:
        if not isinstance(problem_class, BooleanCSPProblemClass):
            raise BooleanCSPContractError(
                "single_instance_disguised_as_class",
                "registry entries require a BooleanCSPProblemClass",
            )
        try:
            selected = RegisteredComplexity(complexity)
        except ValueError as error:
            raise BooleanCSPContractError(
                "invalid_classification", f"unsupported complexity class {complexity!r}"
            ) from error
        if not isinstance(evidence_id, str) or not evidence_id.strip():
            raise BooleanCSPContractError("missing_evidence", "evidence_id is required")
        fingerprint = problem_class.fingerprint
        existing = self._registrations.get(fingerprint)
        if existing is not None:
            if existing.complexity != selected:
                raise BooleanCSPContractError(
                    "p_npc_double_registration",
                    f"{fingerprint} is already registered as {existing.complexity.value}",
                )
            if existing.evidence_id != evidence_id:
                raise BooleanCSPContractError(
                    "duplicate_class_registration",
                    f"{fingerprint} already has evidence {existing.evidence_id}",
                )
            return existing
        if selected is RegisteredComplexity.NPC and problem_class.gamma.classify().tractable:
            raise BooleanCSPContractError(
                "tractable_gamma_registered_npc",
                "a Gamma contained in a Schaefer tractable class cannot be registered NPC",
            )
        registration = GammaRegistration(fingerprint, selected, evidence_id)
        self._registrations[fingerprint] = registration
        return registration

    def lookup(self, fingerprint: str) -> GammaRegistration | None:
        return self._registrations.get(fingerprint)

    @property
    def registrations(self) -> tuple[GammaRegistration, ...]:
        return tuple(self._registrations[key] for key in sorted(self._registrations))


def gamma_class_decider(gamma: Gamma) -> GammaClassification:
    if not isinstance(gamma, Gamma):
        raise BooleanCSPContractError("infinite_gamma", "expected a finite Gamma")
    return gamma.classify()


__all__ = [
    "BoolRow",
    "BooleanCSPContractError",
    "BooleanCSPProblemClass",
    "BooleanRelation",
    "Gamma",
    "GammaClassification",
    "GammaClassificationRegistry",
    "GammaRegistration",
    "RegisteredComplexity",
    "SchaeferClass",
    "gamma_class_decider",
]
