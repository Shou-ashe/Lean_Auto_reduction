"""Audited, content-addressed scope policy for the NP-hard production lane.

H-F must distinguish a genuine missing proof from a decision problem that the
library deliberately excludes from the NP-hard success denominator.  The
classification in this module is exact-identity based: a policy row is accepted
only when its Lean-observed problem and representation nodes still match the
current inventory.  Names are retained for human audit, but never act as a
substring classifier.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

from .lean_runner import sha256_file, validate_declaration_name, validate_module_name
from .models import sha256_id


NP_HARD_SCOPE_POLICY_SCHEMA_V1 = "hardness_np_hard_scope_policy_v1"
NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V1 = "hardness_np_hard_scope_policy_entry_v1"
NP_HARD_SCOPE_POLICY_SCHEMA_V2 = "hardness_np_hard_scope_policy_v2"
NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2 = "hardness_np_hard_scope_policy_entry_v2"
DEFAULT_SCOPE_POLICY = Path("agent/hardness/data/np_hard_scope_policy.json")
POLICY_DISPOSITION_AUXILIARY = "auxiliary_or_non_target"
POLICY_DISPOSITION_ENCODING_COMPLEXITY_FRONTIER = "encoding_complexity_frontier"
POLICY_DISPOSITIONS = {
    POLICY_DISPOSITION_AUXILIARY,
    POLICY_DISPOSITION_ENCODING_COMPLEXITY_FRONTIER,
}
POLICY_CATEGORIES = {
    "encoding_complexity_boundary",
    "encoding_well_formedness_predicate",
    "internal_catalog_helper",
    "tractable_syntactic_class",
}


class NPHardScopePolicyError(ValueError):
    """A malformed, stale, or contradictory production scope policy."""


@dataclass(frozen=True)
class NPHardScopePolicyEntryV1:
    identity_id: str
    canonical_declaration: str
    canonical_module: str
    problem_node_id: str
    representation_node_id: str
    disposition: str
    category: str
    rationale: str
    public_source_file: str
    semantic_evidence_declaration: str
    failure_code: str | None = None
    schema_version: str = NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V1

    def validate(self, *, root: Path) -> None:
        if self.schema_version not in {
            NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V1,
            NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2,
        }:
            raise NPHardScopePolicyError("unsupported NP-hard scope policy entry schema")
        if not (
            self.identity_id.startswith("sha256:")
            and len(self.identity_id) == 71
            and all(character in "0123456789abcdef" for character in self.identity_id[7:])
        ):
            raise NPHardScopePolicyError("scope policy identity_id is not a tagged SHA-256")
        validate_declaration_name(
            self.canonical_declaration, label="scope policy canonical declaration"
        )
        validate_module_name(self.canonical_module)
        validate_declaration_name(
            self.semantic_evidence_declaration,
            label="scope policy semantic evidence declaration",
        )
        if not self.problem_node_id.startswith("lean-whnf:"):
            raise NPHardScopePolicyError("scope policy problem node is not Lean-observed")
        if not self.representation_node_id.startswith("lean-whnf:"):
            raise NPHardScopePolicyError(
                "scope policy representation node is not Lean-observed"
            )
        if self.disposition not in POLICY_DISPOSITIONS:
            raise NPHardScopePolicyError("scope policy disposition is not in the closed vocabulary")
        if self.category not in POLICY_CATEGORIES:
            raise NPHardScopePolicyError("scope policy category is not in the closed vocabulary")
        if self.disposition == POLICY_DISPOSITION_AUXILIARY:
            if self.category == "encoding_complexity_boundary" or self.failure_code is not None:
                raise NPHardScopePolicyError(
                    "audited non-target policy rows cannot carry a complexity-boundary blocker"
                )
        else:
            if self.schema_version != NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2:
                raise NPHardScopePolicyError(
                    "encoding-complexity boundary rows require the v2 entry schema"
                )
            if self.category != "encoding_complexity_boundary":
                raise NPHardScopePolicyError(
                    "encoding-complexity frontier has the wrong policy category"
                )
            if self.failure_code != "encoding_polynomial_reverse_bridge_unavailable":
                raise NPHardScopePolicyError(
                    "encoding-complexity frontier lacks the frozen production blocker"
                )
        if not self.rationale.strip():
            raise NPHardScopePolicyError("scope policy rationale is empty")
        relative = Path(self.public_source_file)
        if relative.is_absolute() or ".." in relative.parts:
            raise NPHardScopePolicyError("scope policy source file escapes the workspace")
        if relative.parts[:3] != ("Lean", "Reference", "ComplexityReduction"):
            raise NPHardScopePolicyError("scope policy evidence is outside the public library")
        source = root.resolve() / relative
        if not source.is_file():
            raise NPHardScopePolicyError(
                f"scope policy evidence file is missing: {self.public_source_file}"
            )

    def to_dict(self, *, root: Path) -> dict[str, Any]:
        self.validate(root=root)
        result = {
            "schema_version": self.schema_version,
            "identity_id": self.identity_id,
            "canonical_declaration": self.canonical_declaration,
            "canonical_module": self.canonical_module,
            "problem_node_id": self.problem_node_id,
            "representation_node_id": self.representation_node_id,
            "disposition": self.disposition,
            "category": self.category,
            "rationale": self.rationale,
            "public_source_file": self.public_source_file,
            "public_source_sha256": "sha256:"
            + sha256_file(root.resolve() / self.public_source_file),
            "semantic_evidence_declaration": self.semantic_evidence_declaration,
        }
        if self.schema_version == NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2:
            result["failure_code"] = self.failure_code
        return result


@dataclass(frozen=True)
class NPHardScopePolicyV1:
    entries: tuple[NPHardScopePolicyEntryV1, ...]
    source_file: str
    schema_version: str = NP_HARD_SCOPE_POLICY_SCHEMA_V1

    @property
    def policy_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "entries": [
                    {
                        "identity_id": entry.identity_id,
                        "canonical_declaration": entry.canonical_declaration,
                        "canonical_module": entry.canonical_module,
                        "problem_node_id": entry.problem_node_id,
                        "representation_node_id": entry.representation_node_id,
                        "disposition": entry.disposition,
                        "category": entry.category,
                        "rationale": entry.rationale,
                        "public_source_file": entry.public_source_file,
                        "semantic_evidence_declaration": (
                            entry.semantic_evidence_declaration
                        ),
                        **(
                            {"failure_code": entry.failure_code}
                            if entry.schema_version
                            == NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2
                            else {}
                        ),
                    }
                    for entry in self.entries
                ],
            }
        )

    def by_identity(self) -> dict[str, NPHardScopePolicyEntryV1]:
        return {entry.identity_id: entry for entry in self.entries}

    def to_dict(self, *, root: Path) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "policy_id": self.policy_id,
            "source_file": self.source_file,
            "entries": [entry.to_dict(root=root) for entry in self.entries],
        }


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise NPHardScopePolicyError(
            f"{label} keys drifted; missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}"
        )


def load_np_hard_scope_policy(
    *, root: Path, path: Path | None = None
) -> NPHardScopePolicyV1:
    root = root.resolve()
    policy_path = (path or (root / DEFAULT_SCOPE_POLICY)).resolve()
    try:
        relative_policy = str(policy_path.relative_to(root))
    except ValueError as error:
        raise NPHardScopePolicyError("scope policy is outside the workspace") from error
    value = json.loads(policy_path.read_text(encoding="utf-8"))
    if not isinstance(value, Mapping):
        raise NPHardScopePolicyError("scope policy must be an object")
    _exact_keys(value, {"schema_version", "description", "entries"}, label="scope policy")
    policy_schema = value["schema_version"]
    if policy_schema not in {
        NP_HARD_SCOPE_POLICY_SCHEMA_V1,
        NP_HARD_SCOPE_POLICY_SCHEMA_V2,
    }:
        raise NPHardScopePolicyError("unsupported NP-hard scope policy schema")
    raw_entries = value["entries"]
    if not isinstance(raw_entries, list):
        raise NPHardScopePolicyError("scope policy entries must be a list")
    expected_entry_keys = {
        "schema_version",
        "identity_id",
        "canonical_declaration",
        "canonical_module",
        "problem_node_id",
        "representation_node_id",
        "disposition",
        "category",
        "rationale",
        "public_source_file",
        "semantic_evidence_declaration",
    }
    if policy_schema == NP_HARD_SCOPE_POLICY_SCHEMA_V2:
        expected_entry_keys.add("failure_code")
    entries: list[NPHardScopePolicyEntryV1] = []
    seen_identities: set[str] = set()
    seen_declarations: set[str] = set()
    for raw in raw_entries:
        if not isinstance(raw, Mapping):
            raise NPHardScopePolicyError("scope policy entry must be an object")
        _exact_keys(raw, expected_entry_keys, label="scope policy entry")
        entry = NPHardScopePolicyEntryV1(**dict(raw))
        expected_entry_schema = (
            NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V2
            if policy_schema == NP_HARD_SCOPE_POLICY_SCHEMA_V2
            else NP_HARD_SCOPE_POLICY_ENTRY_SCHEMA_V1
        )
        if entry.schema_version != expected_entry_schema:
            raise NPHardScopePolicyError(
                "scope policy and entry schema versions do not match"
            )
        entry.validate(root=root)
        if entry.identity_id in seen_identities:
            raise NPHardScopePolicyError("scope policy repeats an identity")
        if entry.canonical_declaration in seen_declarations:
            raise NPHardScopePolicyError("scope policy repeats a canonical declaration")
        seen_identities.add(entry.identity_id)
        seen_declarations.add(entry.canonical_declaration)
        entries.append(entry)
    entries.sort(key=lambda entry: (entry.canonical_declaration, entry.identity_id))
    return NPHardScopePolicyV1(
        entries=tuple(entries),
        source_file=relative_policy,
        schema_version=policy_schema,
    )


def validate_scope_policy_against_inventory(
    *,
    policy: NPHardScopePolicyV1,
    inventory_rows: Iterable[Mapping[str, Any]],
) -> None:
    """Fail closed when a formal policy row no longer names the exact identity."""

    groups: dict[str, list[Mapping[str, Any]]] = {}
    for row in inventory_rows:
        groups.setdefault(str(row["identity_id"]), []).append(row)
    for entry in policy.entries:
        members = groups.get(entry.identity_id)
        if not members:
            raise NPHardScopePolicyError(
                f"scope policy identity disappeared: {entry.identity_id}"
            )
        declarations = {str(member["declaration"]) for member in members}
        if entry.canonical_declaration not in declarations:
            raise NPHardScopePolicyError(
                "scope policy canonical declaration is no longer a member of its identity"
            )
        exact_member = next(
            member
            for member in members
            if member["declaration"] == entry.canonical_declaration
        )
        if (
            exact_member["problem_node_id"] != entry.problem_node_id
            or exact_member["representation_node_id"] != entry.representation_node_id
        ):
            raise NPHardScopePolicyError(
                f"scope policy Lean identity drifted: {entry.canonical_declaration}"
            )


def scope_policy_entry_for_identity(
    *, root: Path, identity_id: str, path: Path | None = None
) -> NPHardScopePolicyEntryV1 | None:
    return load_np_hard_scope_policy(root=root, path=path).by_identity().get(identity_id)


def scope_policy_entry_for_input_reference(
    *, root: Path, reference: Any, path: Path | None = None
) -> NPHardScopePolicyEntryV1 | None:
    """Resolve exact policy metadata for a normalized production input."""

    candidate = next(
        (
            item
            for item in reference.normalization_observation.candidates
            if item.declaration == reference.canonical_problem
        ),
        None,
    )
    if candidate is None:
        raise NPHardScopePolicyError(
            "normalized input has no canonical candidate for scope-policy matching"
        )
    identity_id = sha256_id(
        {
            "problem_node_id": candidate.problem_node,
            "representation_node_id": candidate.representation_node,
        }
    )
    entry = scope_policy_entry_for_identity(
        root=root, identity_id=identity_id, path=path
    )
    if entry is None:
        return None
    if (
        entry.canonical_declaration != reference.canonical_problem
        or entry.problem_node_id != candidate.problem_node
        or entry.representation_node_id != candidate.representation_node
    ):
        raise NPHardScopePolicyError(
            "normalized input conflicts with its exact scope-policy identity"
        )
    return entry
