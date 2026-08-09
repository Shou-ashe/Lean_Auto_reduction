"""Validated observations of one Lean input declaration.

The observation is produced by Lean and is intentionally non-authoritative.
It supplies facts for later retrieval, while the final generated artifact
still has to elaborate against the original declaration.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping

from .models import sha256_id


INPUT_OBSERVATION_SCHEMA = "hardness_input_observation_v2"
INPUT_OBSERVATION_SCHEMA_V1 = "hardness_input_observation_v1"
PREDICATE_PRESENTATION_MATCH_SCHEMA = "hardness_predicate_presentation_match_v1"
SUPPORTED_INPUT_OBSERVATION_SCHEMAS = {
    INPUT_OBSERVATION_SCHEMA_V1,
    INPUT_OBSERVATION_SCHEMA,
}
MARKER = "HARDNESS_AGENT"
DECLARATION_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
SUPPORTED_INPUT_KINDS = {
    "presented_problem",
    "predicate",
    "closed_prop",
    "open_or_polymorphic",
    "unsupported",
}


class InputObservationError(ValueError):
    """A malformed, stale, or contradictory Lean input observation."""


def _parse_bool(value: str, *, label: str) -> bool:
    normalized = value.strip().lower()
    if normalized == "true":
        return True
    if normalized == "false":
        return False
    raise InputObservationError(f"{label} must be true or false")


def _split_names(value: str) -> tuple[str, ...]:
    return tuple(item.strip() for item in value.split(",") if item.strip())


def _validate_node_id(value: str, *, label: str) -> str:
    if not value.startswith("lean-whnf:"):
        raise InputObservationError(f"{label} is not a Lean whnf node")
    return value


@dataclass(frozen=True)
class PredicatePresentationMatch:
    """One nonce-bound Lean confirmation of a predicate presentation.

    The row confirms that the observed predicate/domain are definitionally
    equal to the candidate's ``accepts``/domain.  The exported candidate nodes
    are repeated here so Python can reject a stale or substituted catalog.
    """

    candidate_declaration: str
    problem_node_id: str
    accepts_node_id: str
    domain_node_id: str
    representation_node_id: str
    encoder_bound_identity_node_id: str
    registry_fingerprint: str
    schema_version: str = PREDICATE_PRESENTATION_MATCH_SCHEMA

    @property
    def match_id(self) -> str:
        return sha256_id(self.to_dict(include_match_id=False))

    def to_dict(self, *, include_match_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        if include_match_id:
            value["match_id"] = self.match_id
        return value


# The longer name is useful to callers that distinguish this record from the
# later ProblemMatch selected by the planner.
LeanPredicatePresentationMatch = PredicatePresentationMatch


def _validate_predicate_presentation_match(
    match: PredicatePresentationMatch,
) -> PredicatePresentationMatch:
    if match.schema_version != PREDICATE_PRESENTATION_MATCH_SCHEMA:
        raise InputObservationError("unsupported predicate presentation match schema")
    if not DECLARATION_RE.fullmatch(match.candidate_declaration):
        raise InputObservationError(
            "predicate presentation candidate is not a fully-qualified Lean name"
        )
    for label, value in (
        ("predicate presentation problem node", match.problem_node_id),
        ("predicate presentation accepts node", match.accepts_node_id),
        ("predicate presentation domain node", match.domain_node_id),
        ("predicate presentation representation node", match.representation_node_id),
        (
            "predicate presentation encoder-bound identity node",
            match.encoder_bound_identity_node_id,
        ),
    ):
        _validate_node_id(value, label=label)
    if not match.registry_fingerprint:
        raise InputObservationError(
            "predicate presentation match has no registry fingerprint"
        )
    return match


def _predicate_presentation_match_from_dict(
    value: Mapping[str, Any],
    *,
    index: int,
) -> PredicatePresentationMatch:
    def required_string(key: str) -> str:
        item = value.get(key)
        if not isinstance(item, str) or not item.strip():
            raise InputObservationError(
                f"predicate_presentation_matches[{index}].{key} must be a non-empty string"
            )
        return item.strip()

    match = PredicatePresentationMatch(
        candidate_declaration=required_string("candidate_declaration"),
        problem_node_id=required_string("problem_node_id"),
        accepts_node_id=required_string("accepts_node_id"),
        domain_node_id=required_string("domain_node_id"),
        representation_node_id=required_string("representation_node_id"),
        encoder_bound_identity_node_id=required_string(
            "encoder_bound_identity_node_id"
        ),
        registry_fingerprint=required_string("registry_fingerprint"),
        schema_version=required_string("schema_version"),
    )
    _validate_predicate_presentation_match(match)
    recorded_id = value.get("match_id")
    if recorded_id is not None and recorded_id != match.match_id:
        raise InputObservationError(
            f"predicate presentation match {index} content ID does not match its payload"
        )
    return match


@dataclass(frozen=True)
class LeanInputObservation:
    input_module: str
    input_declaration: str
    declaration_kind: str
    supported: bool
    input_kind: str
    elaborated_type: str
    whnf_type: str
    closed: bool
    universe_parameters: tuple[str, ...]
    has_metavariables: bool
    presented_problem_compatible: bool
    predicate_domain: str | None
    normalized_problem_node_id: str | None
    referenced_constants: tuple[str, ...]
    semantic_summary: str | None
    representation_summary: str | None
    predicate_summary: str | None
    accepts_summary: str | None
    registry_fingerprint: str
    failure_code: str | None
    explanation: str | None
    input_module_sha256: str = ""
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    predicate_domain_node_id: str | None = None
    predicate_node_id: str | None = None
    predicate_presentation_matches: tuple[PredicatePresentationMatch, ...] = ()
    schema_version: str = INPUT_OBSERVATION_SCHEMA

    @property
    def observation_id(self) -> str:
        return sha256_id(self.to_dict(include_observation_id=False))

    def to_dict(self, *, include_observation_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value["universe_parameters"] = list(self.universe_parameters)
        value["referenced_constants"] = list(self.referenced_constants)
        if self.schema_version == INPUT_OBSERVATION_SCHEMA_V1:
            # Preserve the exact v1 payload shape so existing snapshot content
            # IDs remain valid after loading through the v2 implementation.
            value.pop("predicate_domain_node_id", None)
            value.pop("predicate_node_id", None)
            value.pop("predicate_presentation_matches", None)
        else:
            value["predicate_presentation_matches"] = [
                match.to_dict() for match in self.predicate_presentation_matches
            ]
        if include_observation_id:
            value["observation_id"] = self.observation_id
        return value


def _validate_observation(observation: LeanInputObservation) -> LeanInputObservation:
    if observation.schema_version not in SUPPORTED_INPUT_OBSERVATION_SCHEMAS:
        raise InputObservationError("unsupported input observation schema")
    if not DECLARATION_RE.fullmatch(observation.input_declaration):
        raise InputObservationError("input declaration is not a fully-qualified Lean name")
    if observation.input_kind not in SUPPORTED_INPUT_KINDS:
        raise InputObservationError(f"unsupported input kind: {observation.input_kind}")
    if not observation.registry_fingerprint:
        raise InputObservationError("input observation has no registry fingerprint")
    if not observation.elaborated_type or not observation.whnf_type:
        raise InputObservationError("input observation has no elaborated type")
    if observation.has_metavariables and observation.closed:
        raise InputObservationError("input with metavariables cannot be closed")

    if observation.schema_version == INPUT_OBSERVATION_SCHEMA_V1:
        if (
            observation.predicate_domain_node_id
            or observation.predicate_node_id
            or observation.predicate_presentation_matches
        ):
            raise InputObservationError(
                "v1 input observation unexpectedly contains predicate node evidence"
            )

    if observation.supported:
        if observation.failure_code or observation.explanation:
            raise InputObservationError("supported input unexpectedly contains a failure")
        if observation.input_kind == "presented_problem":
            if not observation.presented_problem_compatible:
                raise InputObservationError(
                    "supported input is not Lean-confirmed as a PresentedProblem"
                )
            if not observation.normalized_problem_node_id:
                raise InputObservationError("supported input has no normalized problem node")
            _validate_node_id(
                observation.normalized_problem_node_id,
                label="normalized problem node",
            )
            if not observation.accepts_summary:
                raise InputObservationError("supported input has no bounded accepts summary")
            if observation.predicate_presentation_matches:
                raise InputObservationError(
                    "PresentedProblem input unexpectedly contains predicate matches"
                )
        elif (
            observation.schema_version == INPUT_OBSERVATION_SCHEMA
            and observation.input_kind == "predicate"
        ):
            if not observation.closed or observation.universe_parameters:
                raise InputObservationError(
                    "supported predicate must be a closed monomorphic declaration"
                )
            if observation.has_metavariables:
                raise InputObservationError(
                    "supported predicate must not contain metavariables"
                )
            if observation.presented_problem_compatible:
                raise InputObservationError(
                    "predicate input cannot claim PresentedProblem compatibility"
                )
            if observation.normalized_problem_node_id:
                raise InputObservationError(
                    "predicate input must not claim a PresentedProblem node"
                )
            if not observation.predicate_domain_node_id:
                raise InputObservationError("predicate observation has no domain node")
            if not observation.predicate_node_id:
                raise InputObservationError("predicate observation has no predicate node")
            _validate_node_id(
                observation.predicate_domain_node_id,
                label="predicate domain node",
            )
            _validate_node_id(
                observation.predicate_node_id,
                label="predicate node",
            )
        else:
            raise InputObservationError(
                "only a PresentedProblem or closed predicate can be supported"
            )
    else:
        if not observation.failure_code or not observation.explanation:
            raise InputObservationError(
                "rejected input must include a failure code and natural-language explanation"
            )
        if observation.normalized_problem_node_id:
            raise InputObservationError("rejected input must not claim a problem node")
        if observation.predicate_presentation_matches:
            raise InputObservationError(
                "rejected input must not claim predicate presentation matches"
            )

    if observation.input_kind == "predicate":
        if not observation.predicate_domain:
            raise InputObservationError("predicate observation has no domain")
        if not observation.predicate_summary:
            raise InputObservationError("predicate observation has no bounded definition summary")

    matches_by_declaration: dict[str, PredicatePresentationMatch] = {}
    for match in observation.predicate_presentation_matches:
        _validate_predicate_presentation_match(match)
        if observation.input_kind != "predicate" or not observation.supported:
            raise InputObservationError(
                "predicate presentation match belongs to a non-predicate input"
            )
        if match.registry_fingerprint != observation.registry_fingerprint:
            raise InputObservationError(
                "predicate presentation match registry fingerprint differs from observation"
            )
        previous = matches_by_declaration.get(match.candidate_declaration)
        if previous is not None:
            if previous == match:
                raise InputObservationError(
                    "Lean output contained a duplicate predicate presentation match"
                )
            raise InputObservationError(
                "Lean output contained conflicting predicate presentation matches"
            )
        matches_by_declaration[match.candidate_declaration] = match
    return observation


def observation_from_dict(value: Mapping[str, Any]) -> LeanInputObservation:
    """Validate a serialized observation and its optional content ID."""

    schema_version = value.get("schema_version")
    if schema_version not in SUPPORTED_INPUT_OBSERVATION_SCHEMAS:
        raise InputObservationError("unsupported input observation schema")

    def required_string(key: str) -> str:
        item = value.get(key)
        if not isinstance(item, str) or not item.strip():
            raise InputObservationError(f"{key} must be a non-empty string")
        return item.strip()

    def optional_string(key: str) -> str | None:
        item = value.get(key)
        if item is None or item == "":
            return None
        if not isinstance(item, str):
            raise InputObservationError(f"{key} must be a string or null")
        return item

    def string_tuple(key: str) -> tuple[str, ...]:
        item = value.get(key, [])
        if not isinstance(item, list) or any(
            not isinstance(element, str) or not element.strip() for element in item
        ):
            raise InputObservationError(f"{key} must be a string list")
        return tuple(element.strip() for element in item)

    def required_bool(key: str) -> bool:
        item = value.get(key)
        if not isinstance(item, bool):
            raise InputObservationError(f"{key} must be boolean")
        return item

    raw_matches = value.get("predicate_presentation_matches", [])
    if not isinstance(raw_matches, list):
        raise InputObservationError("predicate_presentation_matches must be a list")
    predicate_matches: list[PredicatePresentationMatch] = []
    for index, raw_match in enumerate(raw_matches):
        if not isinstance(raw_match, Mapping):
            raise InputObservationError(
                f"predicate_presentation_matches[{index}] must be an object"
            )
        predicate_matches.append(
            _predicate_presentation_match_from_dict(raw_match, index=index)
        )

    observation = LeanInputObservation(
        input_module=required_string("input_module"),
        input_declaration=required_string("input_declaration"),
        declaration_kind=required_string("declaration_kind"),
        supported=required_bool("supported"),
        input_kind=required_string("input_kind"),
        elaborated_type=required_string("elaborated_type"),
        whnf_type=required_string("whnf_type"),
        closed=required_bool("closed"),
        universe_parameters=string_tuple("universe_parameters"),
        has_metavariables=required_bool("has_metavariables"),
        presented_problem_compatible=required_bool("presented_problem_compatible"),
        predicate_domain=optional_string("predicate_domain"),
        normalized_problem_node_id=optional_string("normalized_problem_node_id"),
        referenced_constants=string_tuple("referenced_constants"),
        semantic_summary=optional_string("semantic_summary"),
        representation_summary=optional_string("representation_summary"),
        predicate_summary=optional_string("predicate_summary"),
        accepts_summary=optional_string("accepts_summary"),
        registry_fingerprint=required_string("registry_fingerprint"),
        failure_code=optional_string("failure_code"),
        explanation=optional_string("explanation"),
        input_module_sha256=optional_string("input_module_sha256") or "",
        toolchain=optional_string("toolchain") or "",
        lake_manifest_sha256=optional_string("lake_manifest_sha256") or "",
        predicate_domain_node_id=optional_string("predicate_domain_node_id"),
        predicate_node_id=optional_string("predicate_node_id"),
        predicate_presentation_matches=tuple(predicate_matches),
        schema_version=schema_version,
    )
    _validate_observation(observation)
    recorded_id = value.get("observation_id")
    if recorded_id is not None and recorded_id != observation.observation_id:
        raise InputObservationError("input observation content ID does not match its payload")
    return observation


def load_input_observation_snapshot(
    path: Path,
    *,
    expected_input_module: str | None = None,
    expected_input_declaration: str | None = None,
    expected_input_module_sha256: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
    expected_registry_fingerprint: str | None = None,
) -> LeanInputObservation:
    """Load one snapshot and reject any requested stale-context mismatch."""

    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise InputObservationError(f"input observation snapshot not found: {path}") from error
    except json.JSONDecodeError as error:
        raise InputObservationError(f"invalid input observation JSON: {error}") from error
    if not isinstance(raw, dict):
        raise InputObservationError("input observation snapshot must be a JSON object")
    observation = observation_from_dict(raw)
    expected = {
        "input module": (expected_input_module, observation.input_module),
        "input declaration": (
            expected_input_declaration,
            observation.input_declaration,
        ),
        "input module SHA-256": (
            expected_input_module_sha256,
            observation.input_module_sha256,
        ),
        "toolchain": (expected_toolchain, observation.toolchain),
        "lake manifest SHA-256": (
            expected_lake_manifest_sha256,
            observation.lake_manifest_sha256,
        ),
        "registry fingerprint": (
            expected_registry_fingerprint,
            observation.registry_fingerprint,
        ),
    }
    for label, (expected_value, actual_value) in expected.items():
        if expected_value is not None and expected_value != actual_value:
            raise InputObservationError(
                f"stale input observation: {label} does not match the current request"
            )
    return observation


def parse_input_observation(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    input_module: str,
    input_module_sha256: str = "",
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> LeanInputObservation:
    """Parse exactly one nonce-bound observation and its predicate match rows."""

    input_rows: list[list[str]] = []
    predicate_match_rows: list[list[str]] = []
    for line in f"{stdout}\n{stderr}".splitlines():
        position = line.find(MARKER + "\t")
        if position < 0:
            continue
        fields = line[position:].split("\t")
        if (
            len(fields) < 4
            or fields[1] not in SUPPORTED_INPUT_OBSERVATION_SCHEMAS
            or fields[2] != nonce
        ):
            continue
        if fields[3] == "input":
            input_rows.append(fields)
        elif fields[3] == "predicate_match":
            predicate_match_rows.append(fields)
    if not input_rows:
        raise InputObservationError(
            "Lean output did not contain this request's input observation"
        )
    if len(input_rows) != 1:
        raise InputObservationError("Lean output contained duplicate input observations")

    fields = input_rows[0]
    schema_version = fields[1]
    minimum_fields = 26 if schema_version == INPUT_OBSERVATION_SCHEMA else 24
    if len(fields) < minimum_fields:
        raise InputObservationError("Lean emitted a truncated input observation row")

    predicate_matches: list[PredicatePresentationMatch] = []
    if schema_version == INPUT_OBSERVATION_SCHEMA_V1 and predicate_match_rows:
        raise InputObservationError(
            "v1 Lean observation unexpectedly emitted predicate presentation matches"
        )
    for match_fields in predicate_match_rows:
        if match_fields[1] != schema_version:
            raise InputObservationError(
                "Lean output mixed input observation schemas for one nonce"
            )
        if len(match_fields) < 11:
            raise InputObservationError(
                "Lean emitted a truncated predicate presentation match row"
            )
        predicate_matches.append(
            PredicatePresentationMatch(
                candidate_declaration=match_fields[4].strip(),
                problem_node_id=match_fields[5].strip(),
                accepts_node_id=match_fields[6].strip(),
                domain_node_id=match_fields[7].strip(),
                representation_node_id=match_fields[8].strip(),
                encoder_bound_identity_node_id=match_fields[9].strip(),
                registry_fingerprint=match_fields[10].strip(),
            )
        )

    observation = LeanInputObservation(
        input_module=input_module,
        input_declaration=fields[4].strip(),
        declaration_kind=fields[5].strip(),
        supported=_parse_bool(fields[6], label="supported"),
        input_kind=fields[7].strip(),
        elaborated_type=fields[8].strip(),
        whnf_type=fields[9].strip(),
        closed=_parse_bool(fields[10], label="closed"),
        universe_parameters=_split_names(fields[11]),
        has_metavariables=_parse_bool(fields[12], label="has_metavariables"),
        presented_problem_compatible=_parse_bool(
            fields[13], label="presented_problem_compatible"
        ),
        predicate_domain=fields[14].strip() or None,
        normalized_problem_node_id=fields[15].strip() or None,
        referenced_constants=_split_names(fields[16]),
        semantic_summary=fields[17].strip() or None,
        representation_summary=fields[18].strip() or None,
        predicate_summary=fields[19].strip() or None,
        accepts_summary=fields[20].strip() or None,
        registry_fingerprint=fields[21].strip(),
        failure_code=fields[22].strip() or None,
        explanation=fields[23].strip() or None,
        input_module_sha256=input_module_sha256,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        predicate_domain_node_id=(
            fields[24].strip() or None
            if schema_version == INPUT_OBSERVATION_SCHEMA
            else None
        ),
        predicate_node_id=(
            fields[25].strip() or None
            if schema_version == INPUT_OBSERVATION_SCHEMA
            else None
        ),
        predicate_presentation_matches=tuple(
            sorted(
                predicate_matches,
                key=lambda item: (
                    item.candidate_declaration,
                    item.encoder_bound_identity_node_id,
                ),
            )
        ),
        schema_version=schema_version,
    )
    return _validate_observation(observation)
