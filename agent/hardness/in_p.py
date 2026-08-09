"""Exact ``prove_in_p`` evidence and executable Boolean-CSP P algorithms."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Callable, Generic, Iterable, Mapping, Sequence, TypeVar

from .boolean_csp_classes import BooleanRelation, Gamma, SchaeferClass


InstanceT = TypeVar("InstanceT")


def _is_sha256_fingerprint(value: object) -> bool:
    if not isinstance(value, str) or len(value) != 71 or not value.startswith("sha256:"):
        return False
    return all(character in "0123456789abcdef" for character in value[7:])


class InPContractError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class PolynomialTimeBound:
    degree: int
    coefficient: int
    constant: int
    theorem: str

    def __post_init__(self) -> None:
        for label, value in (
            ("degree", self.degree),
            ("coefficient", self.coefficient),
            ("constant", self.constant),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise InPContractError("invalid_polytime_bound", f"{label} must be nonnegative")
        if not isinstance(self.theorem, str) or not self.theorem.strip():
            raise InPContractError("missing_polytime", "a polytime theorem handle is required")

    def evaluate(self, input_size: int) -> int:
        if isinstance(input_size, bool) or not isinstance(input_size, int) or input_size < 0:
            raise InPContractError("invalid_input_size", "input size must be nonnegative")
        return self.coefficient * input_size**self.degree + self.constant


@dataclass(frozen=True)
class PredicateEquivalence:
    problem_fingerprint: str
    algorithm_id: str
    theorem: str

    def __post_init__(self) -> None:
        if not _is_sha256_fingerprint(self.problem_fingerprint):
            raise InPContractError("predicate_mismatch", "equivalence lacks an exact fingerprint")
        if not self.algorithm_id:
            raise InPContractError("predicate_mismatch", "equivalence lacks an algorithm id")
        if not self.theorem:
            raise InPContractError("missing_correctness", "a correctness theorem is required")


@dataclass(frozen=True)
class InPCertificate(Generic[InstanceT]):
    """A P certificate whose three dependent pieces remain exactly bound."""

    problem_fingerprint: str
    algorithm_id: str
    algorithm: Callable[[InstanceT], bool]
    equivalence: PredicateEquivalence
    polytime: PolynomialTimeBound

    def __post_init__(self) -> None:
        if not _is_sha256_fingerprint(self.problem_fingerprint):
            raise InPContractError("invalid_fingerprint", "certificate requires SHA-256 identity")
        if not isinstance(self.algorithm_id, str) or not self.algorithm_id.strip():
            raise InPContractError("missing_algorithm", "algorithm_id is required")
        if not callable(self.algorithm):
            raise InPContractError("missing_algorithm", "certificate requires an executable algorithm")
        if not isinstance(self.equivalence, PredicateEquivalence):
            raise InPContractError("missing_correctness", "predicate equivalence is required")
        if not isinstance(self.polytime, PolynomialTimeBound):
            raise InPContractError("missing_polytime", "polytime evidence is required")
        if self.equivalence.problem_fingerprint != self.problem_fingerprint:
            raise InPContractError(
                "predicate_mismatch", "correctness theorem is indexed by another problem"
            )
        if self.equivalence.algorithm_id != self.algorithm_id:
            raise InPContractError(
                "algorithm_mismatch", "correctness theorem is indexed by another algorithm"
            )


@dataclass(frozen=True)
class InPValidationReceipt:
    problem_fingerprint: str
    algorithm_id: str
    checked_instances: int
    correctness_theorem: str
    polytime_theorem: str


def validate_in_p_certificate(
    certificate: InPCertificate[InstanceT],
    *,
    predicate: Callable[[InstanceT], bool],
    validation_instances: Sequence[InstanceT],
) -> InPValidationReceipt:
    """Validate executable/predicate agreement on an explicit closed test domain.

    Lean remains the proof authority.  This runtime gate catches missing or
    cross-bound evidence before artifact emission and produces no capability on
    the strength of a Boolean flag alone.
    """

    if not isinstance(certificate, InPCertificate):
        raise InPContractError("invalid_certificate", "expected an InPCertificate")
    if not callable(predicate):
        raise InPContractError("missing_predicate", "an exact predicate is required")
    if not isinstance(validation_instances, Sequence) or isinstance(
        validation_instances, (str, bytes, bytearray)
    ):
        raise InPContractError("unbounded_validation", "validation domain must be finite")
    if not validation_instances:
        raise InPContractError("empty_validation", "at least one validation instance is required")
    for index, instance in enumerate(validation_instances):
        result = certificate.algorithm(instance)
        if type(result) is not bool:
            raise InPContractError(
                "nonboolean_algorithm", f"algorithm returned non-Boolean output at instance {index}"
            )
        expected = predicate(instance)
        if type(expected) is not bool:
            raise InPContractError(
                "nonboolean_predicate", f"predicate returned non-Boolean output at instance {index}"
            )
        if result != expected:
            raise InPContractError(
                "predicate_mismatch", f"algorithm disagrees with predicate at instance {index}"
            )
    return InPValidationReceipt(
        certificate.problem_fingerprint,
        certificate.algorithm_id,
        len(validation_instances),
        certificate.equivalence.theorem,
        certificate.polytime.theorem,
    )


@dataclass(frozen=True)
class CSPConstraint:
    relation: BooleanRelation
    variables: tuple[int, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.relation, BooleanRelation):
            raise InPContractError("invalid_constraint", "constraint relation is required")
        if not isinstance(self.variables, tuple) or len(self.variables) != self.relation.arity:
            raise InPContractError(
                "invalid_constraint", "variable scope must match relation arity"
            )
        if any(isinstance(v, bool) or not isinstance(v, int) or v < 0 for v in self.variables):
            raise InPContractError("invalid_constraint", "variables must be natural numbers")


@dataclass(frozen=True)
class BooleanCSPInstance:
    gamma: Gamma
    constraints: tuple[CSPConstraint, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.gamma, Gamma):
            raise InPContractError("infinite_gamma", "instance requires a finite Gamma")
        if not isinstance(self.constraints, tuple):
            raise InPContractError("nonfinite_instance", "constraints must be a finite tuple")
        if any(not isinstance(constraint, CSPConstraint) for constraint in self.constraints):
            raise InPContractError(
                "invalid_constraint", "every instance constraint must be a CSPConstraint"
            )
        allowed = frozenset(self.gamma.relations)
        if any(constraint.relation not in allowed for constraint in self.constraints):
            raise InPContractError("relation_outside_gamma", "constraint relation is not in Gamma")

    @property
    def variables(self) -> tuple[int, ...]:
        return tuple(sorted({v for constraint in self.constraints for v in constraint.variables}))

    def satisfies(self, assignment: Mapping[int, bool]) -> bool:
        if not isinstance(assignment, Mapping):
            raise InPContractError("invalid_assignment", "assignment must be a mapping")
        missing = tuple(variable for variable in self.variables if variable not in assignment)
        if missing:
            raise InPContractError(
                "invalid_assignment", f"assignment is missing variables {missing}"
            )
        if any(type(assignment[variable]) is not bool for variable in self.variables):
            raise InPContractError(
                "invalid_assignment", "assignment values must be Boolean"
            )
        return all(
            constraint.relation.holds(tuple(assignment[v] for v in constraint.variables))
            for constraint in self.constraints
        )


def zero_one_valid_decide(instance: BooleanCSPInstance, *, value: bool) -> bool:
    selected = SchaeferClass.ONE_VALID if value else SchaeferClass.ZERO_VALID
    if not instance.gamma.classify().contains(selected):
        raise InPContractError("class_mismatch", f"Gamma is not {selected.value}")
    return True


@dataclass(frozen=True)
class _HornImplication:
    antecedent: frozenset[int]
    head: int | None


def _powerset(values: tuple[int, ...]) -> Iterable[frozenset[int]]:
    for size in range(len(values) + 1):
        for selected in combinations(values, size):
            yield frozenset(selected)


def _relation_horn_basis(relation: BooleanRelation) -> tuple[_HornImplication, ...]:
    if not relation.is_horn:
        raise InPContractError("class_mismatch", "Horn algorithm received a non-Horn relation")
    coordinates = tuple(range(relation.arity))
    implications: set[_HornImplication] = set()
    for antecedent in _powerset(coordinates):
        extensions = [
            row for row in relation.rows if all(row[index] for index in antecedent)
        ]
        if not extensions:
            implications.add(_HornImplication(antecedent, None))
            continue
        for head in coordinates:
            if head not in antecedent and all(row[head] for row in extensions):
                implications.add(_HornImplication(antecedent, head))
    return tuple(
        sorted(
            implications,
            key=lambda implication: (
                len(implication.antecedent),
                tuple(sorted(implication.antecedent)),
                -1 if implication.head is None else implication.head,
            ),
        )
    )


def horn_unit_propagation(instance: BooleanCSPInstance) -> bool:
    """Decide a finite Horn Boolean CSP by least-model forward chaining."""

    if not instance.gamma.classify().contains(SchaeferClass.HORN):
        raise InPContractError("class_mismatch", "Gamma is not Horn")
    implications: list[_HornImplication] = []
    for constraint in instance.constraints:
        for local in _relation_horn_basis(constraint.relation):
            antecedent = frozenset(constraint.variables[index] for index in local.antecedent)
            head = None if local.head is None else constraint.variables[local.head]
            implications.append(_HornImplication(antecedent, head))
    forced: set[int] = set()
    changed = True
    while changed:
        changed = False
        for implication in implications:
            if implication.antecedent.issubset(forced):
                if implication.head is None:
                    return False
                if implication.head not in forced:
                    forced.add(implication.head)
                    changed = True
    assignment = {variable: variable in forced for variable in instance.variables}
    if not instance.satisfies(assignment):
        raise InPContractError(
            "horn_solver_invariant", "least-model closure failed its relation-table check"
        )
    return True


__all__ = [
    "BooleanCSPInstance",
    "CSPConstraint",
    "InPCertificate",
    "InPContractError",
    "InPValidationReceipt",
    "PolynomialTimeBound",
    "PredicateEquivalence",
    "horn_unit_propagation",
    "validate_in_p_certificate",
    "zero_one_valid_decide",
]
