"""Shared safety contract for generated Lean authoring and validation."""

from __future__ import annotations

import re
from dataclasses import dataclass

from .lean_runner import assert_generated_source_is_safe, validate_module_name
from .models import sha256_id


LEAN_WORKER_SESSION_SCHEMA = "hardness_lean_worker_session_v1"
CONTENT_SHA256_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
BANNED_BODY_RE = re.compile(
    r"(?:```|\b(?:sorry|admit|axiom|unsafe|run_tac)\b|#(?:eval|check|print)|"
    r"\b(?:import|namespace|section|end|theorem|lemma|def|abbrev|structure|class)\b)",
    re.IGNORECASE,
)
IMPORT_RE = re.compile(
    r"(?m)^\s*import\s+([A-Z][A-Za-z0-9_']*(?:\.[A-ZA-Za-z0-9_']+)*)\s*$"
)
ORACLE_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)


class HardnessContractError(ValueError):
    """Stable, machine-readable rejection from the hardness authoring runtime."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _assert_no_oracle_text(value: str, *, code: str) -> None:
    lowered = value.lower()
    if any(marker.lower() in lowered for marker in ORACLE_MARKERS):
        raise HardnessContractError(
            code, "quarantined oracle text entered authoring context"
        )


@dataclass(frozen=True)
class CandidateSource:
    """A Lean source file whose model-editable term body has immutable fences."""

    fixed_header: str
    editable_body: str
    fixed_footer: str
    allowed_imports: tuple[str, ...]

    @property
    def source(self) -> str:
        return self.fixed_header + self.editable_body + self.fixed_footer

    @property
    def source_sha256(self) -> str:
        return sha256_id(self.source)

    @property
    def fixed_header_sha256(self) -> str:
        return sha256_id(self.fixed_header)

    @property
    def fixed_footer_sha256(self) -> str:
        return sha256_id(self.fixed_footer)

    @property
    def editable_body_sha256(self) -> str:
        return sha256_id(self.editable_body)

    @property
    def compiler_inserted_math_token_count(self) -> int:
        return 0

    def validate(self) -> None:
        if not self.fixed_header.endswith(":=\n"):
            raise HardnessContractError(
                "candidate_static_policy_failed",
                "fixed declaration header must end immediately before the Lean term body",
            )
        if not self.editable_body.strip():
            raise HardnessContractError(
                "candidate_static_policy_failed", "candidate editable body is empty"
            )
        if BANNED_BODY_RE.search(self.editable_body):
            raise HardnessContractError(
                "sorry_axiom_or_unsafe_candidate",
                "candidate editable body contains a forbidden Lean command or trust token",
            )
        if len(set(self.allowed_imports)) != len(self.allowed_imports):
            raise HardnessContractError(
                "import_not_allowlisted", "allowed import list has duplicates"
            )
        for module in self.allowed_imports:
            try:
                validate_module_name(module)
            except ValueError as error:
                raise HardnessContractError("import_not_allowlisted", str(error)) from error
        imported = tuple(IMPORT_RE.findall(self.fixed_header))
        declared_import_lines = sum(
            1
            for line in self.fixed_header.splitlines()
            if line.lstrip().startswith("import ")
        )
        if declared_import_lines != len(imported):
            raise HardnessContractError(
                "import_not_allowlisted", "fixed header has a malformed import"
            )
        if not set(imported).issubset(self.allowed_imports):
            raise HardnessContractError(
                "import_not_allowlisted", "fixed header imports an unlisted module"
            )
        _assert_no_oracle_text(self.source, code="oracle_or_gold_import")
        try:
            assert_generated_source_is_safe(self.source)
        except ValueError as error:
            message = str(error)
            code = (
                "oracle_or_gold_import"
                if "quarantined" in message
                else "sorry_axiom_or_unsafe_candidate"
            )
            raise HardnessContractError(code, message) from error

    def replace_body(self, body: str) -> "CandidateSource":
        candidate = CandidateSource(
            fixed_header=self.fixed_header,
            editable_body=body if body.endswith("\n") else body + "\n",
            fixed_footer=self.fixed_footer,
            allowed_imports=self.allowed_imports,
        )
        candidate.validate()
        if (
            candidate.fixed_header_sha256 != self.fixed_header_sha256
            or candidate.fixed_footer_sha256 != self.fixed_footer_sha256
        ):
            raise HardnessContractError(
                "patch_outside_editable_region",
                "fixed candidate source changed during replacement",
            )
        return candidate
