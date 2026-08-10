"""Lean-certified input normalization for the ``prove_np_hard`` entrypoint."""

from __future__ import annotations

import json
import re
import secrets
import tempfile
from dataclasses import asdict, dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any

from .input_observation import InputObservationError, parse_input_observation
from .lean_runner import (
    build_input_observation_source,
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .models import CommandResult, sha256_id
from .np_hard_authoring_planner import lean_import_closure


NP_HARD_INPUT_REGISTRY_SCHEMA_V1 = "hardness_np_hard_input_registry_v1"
NP_HARD_INPUT_IDENTITY_SCHEMA_V1 = "hardness_np_hard_input_identity_v2"
NP_HARD_INPUT_NORMALIZATION_OBSERVATION_SCHEMA_V1 = (
    "hardness_np_hard_input_normalization_observation_v1"
)
NP_HARD_INPUT_NORMALIZATION_MODULE = (
    "ComplexityReduction.Agent.Hardness.InputNormalization"
)
_NORMALIZATION_MARKER = "HARDNESS_NP_HARD_INPUT"
_HASH_PREFIX = "sha256:"
_STABLE_ID_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*\Z")
_LEAN_DECLARATION_RE_TEMPLATE = r"\b(?:abbrev|def|theorem)\s+{name}\b"


class NPHardInputError(ValueError):
    def __init__(
        self,
        code: str,
        message: str,
        *,
        command: CommandResult | None = None,
        candidates: tuple[str, ...] = (),
    ):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message
        self.command = command
        self.candidates = candidates


@dataclass(frozen=True)
class NPHardPresentationCandidateV1:
    declaration: str
    module: str
    problem_node: str
    representation_node: str
    representation_matches: bool
    problem_matches_input: bool

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class NPHardInputNormalizationObservationV1:
    nonce: str
    input_module: str
    input_declaration: str
    declaration_module: str
    input_kind: str
    input_node: str
    registry_fingerprint: str
    import_modules: tuple[str, ...]
    import_closure_sha256: str
    toolchain: str
    lake_manifest_sha256: str
    candidates: tuple[NPHardPresentationCandidateV1, ...]
    definitionally_equal_problem_pairs: tuple[tuple[str, str], ...]
    complete_problem_count: int
    representation_match_count: int
    schema_version: str = NP_HARD_INPUT_NORMALIZATION_OBSERVATION_SCHEMA_V1

    @property
    def observation_id(self) -> str:
        payload = self.to_dict(include_observation_id=False)
        payload.pop("nonce", None)
        return sha256_id(payload)

    @property
    def catalog_id(self) -> str:
        return sha256_id(
            {
                "schema_version": "hardness_np_hard_presentation_index_v1",
                "input_module": self.input_module,
                "import_modules": list(self.import_modules),
                "import_closure_sha256": self.import_closure_sha256,
                "toolchain": self.toolchain,
                "lake_manifest_sha256": self.lake_manifest_sha256,
                "registry_fingerprint": self.registry_fingerprint,
                "candidates": [candidate.to_dict() for candidate in self.candidates],
                "definitionally_equal_problem_pairs": [
                    list(pair) for pair in self.definitionally_equal_problem_pairs
                ],
            }
        )

    def to_dict(self, *, include_observation_id: bool = True) -> dict[str, Any]:
        payload = {
            "schema_version": self.schema_version,
            "nonce": self.nonce,
            "input_module": self.input_module,
            "input_declaration": self.input_declaration,
            "declaration_module": self.declaration_module,
            "input_kind": self.input_kind,
            "input_node": self.input_node,
            "registry_fingerprint": self.registry_fingerprint,
            "import_modules": list(self.import_modules),
            "import_closure_sha256": self.import_closure_sha256,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "candidates": [candidate.to_dict() for candidate in self.candidates],
            "definitionally_equal_problem_pairs": [
                list(pair) for pair in self.definitionally_equal_problem_pairs
            ],
            "complete_problem_count": self.complete_problem_count,
            "representation_match_count": self.representation_match_count,
            "catalog_id": self.catalog_id,
        }
        if include_observation_id:
            payload["observation_id"] = self.observation_id
        return payload


@dataclass(frozen=True)
class NPHardInputReferenceV1:
    requested_term: str
    input_module: str
    requested_declaration: str
    problem_declaration: str
    canonical_module: str
    canonical_problem: str
    resolved_encoding: str
    normalization_kind: str
    stable_id: str | None
    supported: bool
    normalization_observation: NPHardInputNormalizationObservationV1


@dataclass(frozen=True)
class NPHardInputIdentityV1:
    requested_term: str
    input_module: str
    requested_declaration: str
    problem_declaration: str
    canonical_module: str
    canonical_problem: str
    resolved_encoding: str
    normalization_kind: str
    normalization_relation: str
    normalization_certificate: str
    normalization_certificate_file: str
    normalization_certificate_sha256: str
    normalized_problem_node: str
    canonical_problem_node: str
    normalization_catalog_id: str
    normalization_observation_id: str
    import_modules: tuple[str, ...]
    import_closure_sha256: str
    toolchain: str
    lake_manifest_sha256: str
    normalization_candidates: tuple[str, ...]
    registry_fingerprint: str
    observation_id: str
    stable_id: str | None
    schema_version: str = NP_HARD_INPUT_IDENTITY_SCHEMA_V1

    @property
    def identity_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["import_modules"] = list(self.import_modules)
        payload["normalization_candidates"] = list(self.normalization_candidates)
        return {**payload, "identity_id": self.identity_id}


def _registry(root: Path) -> tuple[dict[str, Any], ...]:
    path = root / "Gate" / "np_hard_input_registry.json"
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict) or raw.get("schema_version") != NP_HARD_INPUT_REGISTRY_SCHEMA_V1:
        raise ValueError("unsupported NP-hard input registry schema")
    entries = raw.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("NP-hard input registry is empty")
    required = {
        "stable_id", "module", "problem", "canonical_module", "canonical_problem",
        "normalization_kind", "supported",
    }
    seen_ids: set[str] = set()
    seen_terms: set[tuple[str, str]] = set()
    normalized: list[dict[str, Any]] = []
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != required:
            raise ValueError("invalid NP-hard input registry entry")
        if not isinstance(entry["stable_id"], str) or not _STABLE_ID_RE.fullmatch(entry["stable_id"]):
            raise ValueError("invalid NP-hard input stable ID")
        if entry["stable_id"] in seen_ids:
            raise ValueError("duplicate NP-hard input stable ID")
        for key in ("module", "canonical_module"):
            validate_module_name(entry[key])
        for key in ("problem", "canonical_problem"):
            validate_declaration_name(entry[key], label=key)
        if entry["normalization_kind"] not in {"exact", "alias", "wrapper"}:
            raise ValueError("invalid NP-hard input normalization kind")
        if not isinstance(entry["supported"], bool):
            raise ValueError("invalid NP-hard input support flag")
        term = (entry["module"], entry["problem"])
        if term in seen_terms:
            raise ValueError("duplicate NP-hard input registry endpoint")
        seen_ids.add(entry["stable_id"])
        seen_terms.add(term)
        normalized.append(entry)
    return tuple(normalized)


def _public_module_path(root: Path, module: str) -> Path:
    return (
        root
        / "Lean"
        / "Reference"
        / Path(*module.split(".")).with_suffix(".lean")
    )


def _target_matrix_canonical(
    *, root: Path, declarations: set[str]
) -> tuple[str, str] | None:
    """Read the content-addressed H-F canonical identity when available.

    The Lean normalization observation remains the authority: a matrix choice
    is used only when that declaration is present in the current import
    closure and definitionally equal to the requested problem.
    """

    path = root / "Gate" / "NP_HARD_TARGET_MATRIX.json"
    if not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if value.get("schema_version") not in {
        "hardness_np_hard_target_matrix_v1",
        "hardness_np_hard_target_matrix_v2",
    }:
        return None
    for row in value.get("identities", []):
        members = set(row.get("member_declarations") or [])
        canonical = row.get("canonical_declaration")
        module = row.get("canonical_module")
        if (
            declarations.intersection(members)
            and isinstance(canonical, str)
            and canonical in declarations
            and isinstance(module, str)
        ):
            return canonical, module
    return None


def _inventory_module_candidates(*, root: Path, declaration: str) -> set[str]:
    candidates: set[str] = set()
    inventory_path = root / "Gate" / "NP_HARD_H_F_INVENTORY.json"
    if inventory_path.is_file():
        try:
            inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            inventory = {}
        for row in inventory.get("entries", []):
            if row.get("declaration") == declaration and isinstance(
                row.get("declaration_module"), str
            ):
                candidates.add(row["declaration_module"])
        for identity in inventory.get("identities", []):
            for member in identity.get("members", []):
                if member.get("declaration") == declaration and isinstance(
                    member.get("module"), str
                ):
                    candidates.add(member["module"])
            if identity.get("canonical_declaration") == declaration and isinstance(
                identity.get("canonical_module"), str
            ):
                candidates.add(identity["canonical_module"])

    # Most declarations live in a module matching their namespace.
    namespace = declaration.rpartition(".")[0]
    components = namespace.split(".")
    for end in range(len(components), 0, -1):
        candidates.add(".".join(components[:end]))

    # Namespace and physical module occasionally differ (for example
    # ``Domain.Core`` modules).  A source-level leaf search only proposes
    # candidates; Lean validates the winning import below.
    leaf = re.escape(declaration.rpartition(".")[2])
    declaration_re = re.compile(_LEAN_DECLARATION_RE_TEMPLATE.format(name=leaf))
    reference = root / "Lean" / "Reference"
    public_root = reference / "ComplexityReduction"
    if public_root.is_dir():
        for path in public_root.rglob("*.lean"):
            try:
                text = path.read_text(encoding="utf-8")
            except OSError:
                continue
            if declaration_re.search(text):
                candidates.add(".".join(path.relative_to(reference).with_suffix("").parts))
    return {
        module
        for module in candidates
        if module.startswith("ComplexityReduction.")
        and _public_module_path(root, module).is_file()
    }


def discover_np_hard_input_module(
    *, root: Path, requested_term: str, timeout_seconds: int = 600
) -> str:
    """Discover the public module for a stable ID or full declaration.

    Discovery never guesses between multiple valid owners.  Every proposed
    source module is checked by the same Lean normalization observation used
    by the production entrypoint.
    """

    root = root.resolve()
    entries = _registry(root)
    if _STABLE_ID_RE.fullmatch(requested_term):
        entry = next(
            (item for item in entries if item["stable_id"] == requested_term), None
        )
        if entry is None:
            raise NPHardInputError(
                "input_problem_not_found",
                f"unknown registered encoding stable ID: {requested_term}",
            )
        return str(entry["module"])

    validate_declaration_name(requested_term, label="problem")
    if not requested_term.startswith("ComplexityReduction."):
        raise NPHardInputError(
            "input_problem_not_found",
            "automatic module discovery is restricted to public ComplexityReduction declarations",
        )
    candidates = {
        str(entry["module"])
        for entry in entries
        if entry["problem"] == requested_term
    }
    candidates.update(_inventory_module_candidates(root=root, declaration=requested_term))
    valid: list[tuple[str, int]] = []
    first_semantic_error: NPHardInputError | None = None
    for module in sorted(candidates):
        try:
            observation = observe_np_hard_input_normalization(
                root=root,
                input_module=module,
                input_declaration=requested_term,
                timeout_seconds=timeout_seconds,
            )
        except NPHardInputError as error:
            if error.code != "input_problem_not_found" and first_semantic_error is None:
                first_semantic_error = error
            continue
        valid.append((module, len(observation.import_modules)))
    if not valid:
        if first_semantic_error is not None:
            raise first_semantic_error
        raise NPHardInputError(
            "input_problem_not_found",
            "no public module exports the requested declaration",
            candidates=tuple(sorted(candidates)),
        )
    # Prefer the most specific module; importing a broader umbrella is valid
    # but is not the declaration's owning public module.
    valid.sort(key=lambda item: (item[1], -len(item[0].split(".")), item[0]))
    best_closure_size = valid[0][1]
    most_specific = len(valid[0][0].split("."))
    winners = [
        module
        for module, closure_size in valid
        if closure_size == best_closure_size
        and len(module.split(".")) == most_specific
    ]
    if len(winners) > 1:
        raise NPHardInputError(
            "ambiguous_input_module",
            "multiple public modules export the requested declaration",
            candidates=tuple(winners),
        )
    return winners[0]


def _tagged_file_hash(path: Path) -> str:
    return _HASH_PREFIX + sha256_file(path)


def _parse_bool(value: str, *, label: str) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise NPHardInputError(
        "lean_infrastructure_error", f"{label} is not a Lean boolean"
    )


def _local_catalog_modules(
    *, root: Path, import_modules: tuple[str, ...], input_module: str
) -> tuple[str, ...]:
    lean_reference = root / "Lean" / "Reference"
    modules = tuple(
        sorted(
            module
            for module in set(import_modules) | {input_module}
            if (lean_reference / Path(*module.split(".")).with_suffix(".lean")).is_file()
        )
    )
    if input_module not in modules:
        raise NPHardInputError(
            "input_problem_not_found", "input module is not a local importable module"
        )
    return modules


def _normalization_closure_id(
    *,
    root: Path,
    input_module: str,
    compiled_import_closure_sha256: str,
    local_modules: tuple[str, ...],
) -> str:
    lean_reference = root / "Lean" / "Reference"
    return sha256_id(
        {
            "schema_version": "hardness_np_hard_input_source_closure_v1",
            "input_module": input_module,
            "compiled_import_closure_sha256": compiled_import_closure_sha256,
            "local_source_sha256": {
                module: _tagged_file_hash(
                    lean_reference / Path(*module.split(".")).with_suffix(".lean")
                )
                for module in local_modules
            },
        }
    )


def build_np_hard_input_normalization_observation_source(
    *,
    input_module: str,
    input_declaration: str,
    nonce: str,
    allowed_modules: tuple[str, ...],
) -> str:
    validate_module_name(input_module)
    validate_declaration_name(input_declaration, label="normalization input")
    if not nonce or any(character not in "0123456789abcdef" for character in nonce):
        raise NPHardInputError("lean_infrastructure_error", "invalid normalization nonce")
    if input_module not in allowed_modules:
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization scope omits the input module"
        )
    module_payload = ",".join(sorted(set(allowed_modules)))
    return (
        f"import {NP_HARD_INPUT_NORMALIZATION_MODULE}\n"
        f"import {input_module}\n\n"
        f'#hardness_normalize_np_hard_input "{nonce}" {input_declaration} '
        f"{json.dumps(module_payload, ensure_ascii=True)}\n"
    )


def parse_np_hard_input_normalization_observation(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    input_module: str,
    input_declaration: str,
    import_modules: tuple[str, ...],
    import_closure_sha256: str,
    toolchain: str,
    lake_manifest_sha256: str,
) -> NPHardInputNormalizationObservationV1:
    rows: dict[str, list[list[str]]] = {}
    for line in f"{stdout}\n{stderr}".splitlines():
        position = line.find(_NORMALIZATION_MARKER + "\t")
        if position < 0:
            continue
        fields = line[position:].split("\t")
        if (
            len(fields) < 4
            or fields[1] != NP_HARD_INPUT_NORMALIZATION_OBSERVATION_SCHEMA_V1
            or fields[2] != nonce
        ):
            continue
        rows.setdefault(fields[3], []).append(fields)
    inputs = rows.get("input", [])
    completes = rows.get("complete", [])
    if len(inputs) != 1 or len(completes) != 1:
        raise NPHardInputError(
            "lean_infrastructure_error",
            "normalization observation lacks one exact input/completion row",
        )
    input_row = inputs[0]
    complete_row = completes[0]
    if len(input_row) < 9 or len(complete_row) < 7:
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization observation is truncated"
        )
    observed_declaration = input_row[4]
    input_kind = input_row[5]
    declaration_module = input_row[6]
    input_node = input_row[7]
    fingerprint = input_row[8]
    if observed_declaration != input_declaration:
        raise NPHardInputError(
            "candidate_wrong_endpoint", "normalization observed another declaration"
        )
    if input_kind not in {"presented_problem", "encoding", "unsupported"}:
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization input kind is invalid"
        )
    if declaration_module not in import_modules:
        raise NPHardInputError(
            "input_problem_not_found", "input declaration escaped the import closure"
        )
    if not input_node.startswith("lean-whnf:") or not fingerprint:
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization input identity is incomplete"
        )
    candidates: list[NPHardPresentationCandidateV1] = []
    seen: set[str] = set()
    for row in rows.get("problem", []):
        if len(row) < 11:
            raise NPHardInputError(
                "lean_infrastructure_error", "normalization problem row is truncated"
            )
        declaration, module = row[4], row[5]
        validate_declaration_name(declaration, label="presentation candidate")
        validate_module_name(module)
        if declaration in seen or module not in import_modules or row[10] != fingerprint:
            raise NPHardInputError(
                "authoring_catalog_dependency_stale",
                "normalization problem catalog is duplicated or escaped its closure",
            )
        if not row[6].startswith("lean-whnf:") or not row[7].startswith("lean-whnf:"):
            raise NPHardInputError(
                "lean_infrastructure_error", "normalization problem node is invalid"
            )
        seen.add(declaration)
        candidates.append(
            NPHardPresentationCandidateV1(
                declaration=declaration,
                module=module,
                problem_node=row[6],
                representation_node=row[7],
                representation_matches=_parse_bool(
                    row[8], label="representation_matches"
                ),
                problem_matches_input=_parse_bool(
                    row[9], label="problem_matches_input"
                ),
            )
        )
    defeq_pairs: list[tuple[str, str]] = []
    for row in rows.get("problem_defeq", []):
        if len(row) < 7 or row[6] != fingerprint:
            raise NPHardInputError(
                "lean_infrastructure_error", "normalization equality row is invalid"
            )
        first, second = row[4], row[5]
        if first not in seen or second not in seen or first >= second:
            raise NPHardInputError(
                "lean_infrastructure_error", "normalization equality escaped its catalog"
            )
        defeq_pairs.append((first, second))
    try:
        problem_count = int(complete_row[4])
        match_count = int(complete_row[5])
    except ValueError as error:
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization completion count is invalid"
        ) from error
    if (
        complete_row[6] != fingerprint
        or problem_count != len(candidates)
        or match_count != sum(candidate.representation_matches for candidate in candidates)
    ):
        raise NPHardInputError(
            "lean_infrastructure_error", "normalization completion count drifted"
        )
    return NPHardInputNormalizationObservationV1(
        nonce=nonce,
        input_module=input_module,
        input_declaration=input_declaration,
        declaration_module=declaration_module,
        input_kind=input_kind,
        input_node=input_node,
        registry_fingerprint=fingerprint,
        import_modules=tuple(sorted(import_modules)),
        import_closure_sha256=import_closure_sha256,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        candidates=tuple(sorted(candidates, key=lambda item: item.declaration)),
        definitionally_equal_problem_pairs=tuple(sorted(set(defeq_pairs))),
        complete_problem_count=problem_count,
        representation_match_count=match_count,
    )


@lru_cache(maxsize=64)
def _observe_np_hard_input_normalization_cached(
    *,
    root_string: str,
    input_module: str,
    input_declaration: str,
    import_modules: tuple[str, ...],
    allowed_modules: tuple[str, ...],
    import_closure_sha256: str,
    toolchain: str,
    lake_manifest_sha256: str,
    timeout_seconds: int,
) -> NPHardInputNormalizationObservationV1:
    root = Path(root_string)
    nonce = secrets.token_hex(16)
    source = build_np_hard_input_normalization_observation_source(
        input_module=input_module,
        input_declaration=input_declaration,
        nonce=nonce,
        allowed_modules=allowed_modules,
    )
    with tempfile.TemporaryDirectory(prefix="np-hard-input-normalization-") as directory:
        source_path = Path(directory) / "InputNormalizationProbe.lean"
        source_path.write_text(source, encoding="utf-8")
        command = run_command(
            ["lake", "env", "lean", str(source_path)],
            cwd=root / "Lean",
            timeout_seconds=timeout_seconds,
            output_limit=16 * 1024 * 1024,
        )
    if not command.ok:
        lowered = f"{command.stdout}\n{command.stderr}".lower()
        code = (
            "input_problem_not_found"
            if "unknown identifier" in lowered or "unknown constant" in lowered
            else "lean_infrastructure_error"
        )
        raise NPHardInputError(code, command.stderr or command.stdout, command=command)
    return parse_np_hard_input_normalization_observation(
        stdout=command.stdout,
        stderr=command.stderr,
        nonce=nonce,
        input_module=input_module,
        input_declaration=input_declaration,
        import_modules=allowed_modules,
        import_closure_sha256=import_closure_sha256,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
    )


def observe_np_hard_input_normalization(
    *,
    root: Path,
    input_module: str,
    input_declaration: str,
    timeout_seconds: int = 600,
) -> NPHardInputNormalizationObservationV1:
    root = root.resolve()
    validate_module_name(input_module)
    validate_declaration_name(input_declaration, label="normalization input")
    module_file(root / "Lean", input_module)
    build = run_command(
        ["lake", "build", NP_HARD_INPUT_NORMALIZATION_MODULE, input_module],
        cwd=root / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=16 * 1024 * 1024,
    )
    if not build.ok:
        lowered = f"{build.stdout}\n{build.stderr}".lower()
        code = "input_problem_not_found" if "unknown" in lowered else "lean_infrastructure_error"
        raise NPHardInputError(code, build.stderr or build.stdout, command=build)
    lean_import_closure.cache_clear()
    import_modules, compiled_import_closure_sha256 = lean_import_closure(
        root=root, input_module=input_module
    )
    allowed_modules = _local_catalog_modules(
        root=root, import_modules=import_modules, input_module=input_module
    )
    import_closure_sha256 = _normalization_closure_id(
        root=root,
        input_module=input_module,
        compiled_import_closure_sha256=compiled_import_closure_sha256,
        local_modules=allowed_modules,
    )
    return _observe_np_hard_input_normalization_cached(
        root_string=str(root),
        input_module=input_module,
        input_declaration=input_declaration,
        import_modules=import_modules,
        allowed_modules=allowed_modules,
        import_closure_sha256=import_closure_sha256,
        toolchain=(root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip(),
        lake_manifest_sha256=_tagged_file_hash(root / "Lean" / "lake-manifest.json"),
        timeout_seconds=timeout_seconds,
    )


def _encoding_problem_groups(
    observation: NPHardInputNormalizationObservationV1,
) -> tuple[tuple[NPHardPresentationCandidateV1, ...], ...]:
    matches = {
        candidate.declaration: candidate
        for candidate in observation.candidates
        if candidate.representation_matches
    }
    parents = {declaration: declaration for declaration in matches}

    def find(declaration: str) -> str:
        while parents[declaration] != declaration:
            parents[declaration] = parents[parents[declaration]]
            declaration = parents[declaration]
        return declaration

    def union(first: str, second: str) -> None:
        first_root, second_root = find(first), find(second)
        if first_root != second_root:
            smaller, larger = sorted((first_root, second_root))
            parents[larger] = smaller

    for first, second in observation.definitionally_equal_problem_pairs:
        if first in matches and second in matches:
            union(first, second)
    groups: dict[str, list[NPHardPresentationCandidateV1]] = {}
    for declaration, candidate in matches.items():
        groups.setdefault(find(declaration), []).append(candidate)
    return tuple(
        tuple(sorted(group, key=lambda item: item.declaration))
        for _, group in sorted(groups.items())
    )


def resolve_np_hard_input_reference(
    *,
    root: Path,
    input_module: str | None,
    requested_term: str,
    timeout_seconds: int = 600,
) -> NPHardInputReferenceV1:
    root = root.resolve()
    entries = _registry(root)
    by_id = {entry["stable_id"]: entry for entry in entries}
    entry = None
    if _STABLE_ID_RE.fullmatch(requested_term):
        entry = by_id.get(requested_term)
        if entry is None:
            raise NPHardInputError(
                "input_problem_not_found", f"unknown registered encoding stable ID: {requested_term}"
            )
        if input_module and input_module != entry["module"]:
            raise NPHardInputError(
                "input_problem_not_found",
                "the supplied module does not own the registered encoding stable ID",
            )
        input_module = entry["module"]
        requested_declaration = entry["problem"]
    else:
        if not input_module:
            input_module = discover_np_hard_input_module(
                root=root,
                requested_term=requested_term,
                timeout_seconds=timeout_seconds,
            )
        validate_module_name(input_module)
        validate_declaration_name(requested_term, label="problem")
        requested_declaration = requested_term
        entry = next(
            (
                item
                for item in entries
                if item["module"] == input_module and item["problem"] == requested_term
            ),
            None,
        )
    observation = observe_np_hard_input_normalization(
        root=root,
        input_module=input_module,
        input_declaration=requested_declaration,
        timeout_seconds=timeout_seconds,
    )
    candidates = {candidate.declaration: candidate for candidate in observation.candidates}
    if observation.input_kind == "unsupported":
        raise NPHardInputError(
            "input_not_presented_problem",
            "input is neither an exact PresentedProblem nor a LawfulEncodedType",
        )
    if observation.input_kind == "presented_problem":
        matching_declarations = {
            candidate.declaration
            for candidate in observation.candidates
            if candidate.problem_matches_input
        }
        matrix_canonical = _target_matrix_canonical(
            root=root, declarations=matching_declarations
        )
        canonical_problem = (
            entry["canonical_problem"]
            if entry
            else (
                matrix_canonical[0]
                if matrix_canonical is not None
                else requested_declaration
            )
        )
        canonical = candidates.get(canonical_problem)
        if canonical is None or not canonical.problem_matches_input:
            raise NPHardInputError(
                "input_not_presented_problem",
                "registered alias/wrapper does not normalize to its canonical PresentedProblem",
            )
        canonical_module = canonical.module
        normalization_kind = (
            entry["normalization_kind"]
            if entry
            else ("exact" if canonical_problem == requested_declaration else "alias")
        )
        resolved_encoding = f"{canonical_problem}.representation"
        normalization_candidates = tuple(
            sorted(
                candidate.declaration
                for candidate in observation.candidates
                if candidate.problem_matches_input
            )
        )
    else:
        groups = _encoding_problem_groups(observation)
        if not groups:
            raise NPHardInputError(
                "missing_lawful_presentation",
                "the encoding has no definitionally equal PresentedProblem in its import closure",
            )
        if len(groups) > 1:
            handles = sorted(candidate.declaration for group in groups for candidate in group)
            raise NPHardInputError(
                "ambiguous_lawful_presentation",
                "the encoding has multiple non-definitionally-equal PresentedProblem candidates: "
                + ", ".join(handles),
                candidates=tuple(handles),
            )
        group = groups[0]
        preferred = {
            item["canonical_problem"]
            for item in entries
            if item["canonical_problem"] in {candidate.declaration for candidate in group}
        }
        matrix_canonical = _target_matrix_canonical(
            root=root,
            declarations={candidate.declaration for candidate in group},
        )
        registered_canonical = (
            entry["canonical_problem"]
            if entry
            else (matrix_canonical[0] if matrix_canonical is not None else None)
        )
        canonical = min(
            group,
            key=lambda candidate: (
                candidate.declaration != registered_canonical,
                candidate.declaration not in preferred,
                len(candidate.declaration),
                candidate.declaration,
            ),
        )
        canonical_problem = canonical.declaration
        canonical_module = canonical.module
        normalization_kind = "encoding"
        resolved_encoding = requested_declaration
        normalization_candidates = tuple(candidate.declaration for candidate in group)
    return NPHardInputReferenceV1(
        requested_term=requested_term,
        input_module=input_module,
        requested_declaration=requested_declaration,
        problem_declaration=canonical_problem,
        canonical_module=canonical_module,
        canonical_problem=canonical_problem,
        resolved_encoding=resolved_encoding,
        normalization_kind=normalization_kind,
        stable_id=entry["stable_id"] if entry else None,
        supported=True,
        normalization_observation=observation,
    )


def build_np_hard_input_certificate_source(
    *, reference: NPHardInputReferenceV1, nonce: str
) -> str:
    source = build_input_observation_source(
        input_module=reference.input_module,
        nonce=nonce,
        input_declaration=reference.problem_declaration,
    )
    canonical_import = (
        f"import {reference.canonical_module}\n"
        if reference.canonical_module != reference.input_module
        else ""
    )
    if reference.normalization_kind == "encoding":
        relation = (
            f"{reference.requested_declaration} = "
            f"{reference.canonical_problem}.representation"
        )
    else:
        relation = (
            f"{reference.requested_declaration} = {reference.canonical_problem}"
        )
    equality = f"\nexample : {relation} := by\n  rfl\n"
    return canonical_import + source + equality


def certify_np_hard_input(
    *,
    root: Path,
    reference: NPHardInputReferenceV1,
    certificate_path: Path,
    toolchain: str,
    lake_manifest_sha256: str,
    timeout_seconds: int,
) -> tuple[NPHardInputIdentityV1, CommandResult]:
    normalization = reference.normalization_observation
    lean_import_closure.cache_clear()
    current_modules, current_compiled_closure = lean_import_closure(
        root=root.resolve(), input_module=reference.input_module
    )
    current_local_modules = _local_catalog_modules(
        root=root.resolve(),
        import_modules=current_modules,
        input_module=reference.input_module,
    )
    current_closure = _normalization_closure_id(
        root=root.resolve(),
        input_module=reference.input_module,
        compiled_import_closure_sha256=current_compiled_closure,
        local_modules=current_local_modules,
    )
    if (
        normalization.import_modules != current_local_modules
        or normalization.import_closure_sha256 != current_closure
        or normalization.toolchain != toolchain
        or normalization.lake_manifest_sha256
        != _HASH_PREFIX + lake_manifest_sha256.removeprefix(_HASH_PREFIX)
    ):
        raise NPHardInputError(
            "candidate_dependency_stale",
            "normalization catalog no longer matches source, toolchain, or lake manifest",
        )
    nonce = secrets.token_hex(16)
    certificate_path.parent.mkdir(parents=True, exist_ok=True)
    certificate_path.write_text(
        build_np_hard_input_certificate_source(reference=reference, nonce=nonce),
        encoding="utf-8",
    )
    command = run_command(
        ["lake", "env", "lean", str(certificate_path)],
        cwd=root / "Lean",
        timeout_seconds=timeout_seconds,
    )
    if not command.ok:
        lowered = (command.stdout + "\n" + command.stderr).lower()
        code = (
            "input_problem_not_found"
            if "unknown identifier" in lowered or "unknown constant" in lowered
            else "input_not_presented_problem"
        )
        raise NPHardInputError(code, command.stderr or command.stdout, command=command)
    try:
        observation = parse_input_observation(
            stdout=command.stdout,
            stderr=command.stderr,
            nonce=nonce,
            input_module=reference.input_module,
            input_module_sha256=sha256_file(module_file(root / "Lean", reference.input_module)),
            toolchain=toolchain,
            lake_manifest_sha256=lake_manifest_sha256,
        )
    except InputObservationError as error:
        raise NPHardInputError("lean_infrastructure_error", str(error), command=command) from error
    if not observation.presented_problem_compatible:
        raise NPHardInputError(
            "input_not_presented_problem",
            observation.explanation or "input is not a PresentedProblem",
            command=command,
        )
    assert observation.normalized_problem_node_id is not None
    canonical = next(
        (
            candidate
            for candidate in normalization.candidates
            if candidate.declaration == reference.canonical_problem
        ),
        None,
    )
    if canonical is None or canonical.problem_node != observation.normalized_problem_node_id:
        raise NPHardInputError(
            "candidate_dependency_stale",
            "normalization certificate endpoint differs from the content-addressed catalog",
            command=command,
        )
    if observation.registry_fingerprint != normalization.registry_fingerprint:
        raise NPHardInputError(
            "candidate_dependency_stale",
            "normalization certificate registry fingerprint is stale",
            command=command,
        )
    observation_path = certificate_path.with_name("InputNormalizationObservation.json")
    observation_path.write_text(
        json.dumps(normalization.to_dict(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    normalization_relation = (
        "encoding_defeq_canonical_representation"
        if reference.normalization_kind == "encoding"
        else "presented_problem_defeq_canonical"
    )
    return (
        NPHardInputIdentityV1(
            requested_term=reference.requested_term,
            input_module=reference.input_module,
            requested_declaration=reference.requested_declaration,
            problem_declaration=reference.problem_declaration,
            canonical_module=reference.canonical_module,
            canonical_problem=reference.canonical_problem,
            resolved_encoding=reference.resolved_encoding,
            normalization_kind=reference.normalization_kind,
            normalization_relation=normalization_relation,
            normalization_certificate="lean-checked-artifact",
            normalization_certificate_file=str(certificate_path),
            normalization_certificate_sha256=sha256_file(certificate_path),
            normalized_problem_node=observation.normalized_problem_node_id,
            canonical_problem_node=canonical.problem_node,
            normalization_catalog_id=normalization.catalog_id,
            normalization_observation_id=normalization.observation_id,
            import_modules=normalization.import_modules,
            import_closure_sha256=normalization.import_closure_sha256,
            toolchain=normalization.toolchain,
            lake_manifest_sha256=normalization.lake_manifest_sha256,
            normalization_candidates=tuple(
                sorted(
                    candidate.declaration
                    for candidate in normalization.candidates
                    if (
                        candidate.problem_matches_input
                        if normalization.input_kind == "presented_problem"
                        else candidate.representation_matches
                    )
                )
            ),
            registry_fingerprint=normalization.registry_fingerprint,
            observation_id=observation.observation_id,
            stable_id=reference.stable_id,
        ),
        command,
    )
