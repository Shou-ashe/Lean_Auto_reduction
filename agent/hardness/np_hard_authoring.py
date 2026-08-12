"""Fenced model authoring for one exact forward NP-hardness reduction gap.

The model may replace only the term body of a runner-owned declaration whose
type is ``CertifiedReduction hardnessHub request.problem``.  Candidate Lean,
fresh resolver reconstruction, the axiom gate, and release replay remain the
authorities; model output is never interpreted as evidence by Python.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol

from .authoring_contract import BANNED_BODY_RE, CandidateSource
from .lean_runner import (
    RUNTIME_MODULE,
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
    validate_declaration_name,
    validate_module_name,
)
from .lean_worker_pool import (
    LeanWorkerKey,
    LeanWorkerPool,
    LeanWorkerResult,
)
from .model_client import ModelResponse, extract_json_object
from .models import CommandResult, sha256_id
from .np_hard_production import FORMAL_MAX_TOKENS


NP_HARD_AUTHORING_TASK_SCHEMA_V1 = "hardness_np_hard_authoring_task_v1"
NP_HARD_AUTHORING_PATCH_SCHEMA_V1 = "hardness_np_hard_authoring_patch_v1"
NP_HARD_AUTHORING_TRACE_SCHEMA_V1 = "hardness_np_hard_authoring_trace_v1"
NP_HARD_AUTHORING_PUBLICATION_SCHEMA_V1 = (
    "hardness_np_hard_authoring_publication_v1"
)
NP_HARD_AUTHORING_DIRECTION = "hardness_seed_to_problem"
NP_HARD_AUTHORING_MAX_BODY_CHARS = 32_000

NP_HARD_AUTHORING_TASK_SCHEMA_V2 = "hardness_np_hard_authoring_task_v2"
NP_HARD_AUTHORING_PATCH_SCHEMA_V2 = "hardness_np_hard_authoring_patch_v2"
NP_HARD_AUTHORING_RESULT_SCHEMA_V2 = "hardness_np_hard_authoring_result_v2"
NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2 = "source_to_target"
NP_HARD_SEMANTIC_PLAN_SCHEMA_V1 = "hardness_np_hard_semantic_plan_v1"
NP_HARD_SUCCESSOR_CHAIN_PROBE_SCHEMA_V1 = (
    "hardness_np_hard_successor_chain_probe_v1"
)
NP_HARD_AUTHORING_TASK_CLASSES_V2 = frozenset(
    {
        "semantic_proof",
        "program_composition",
        "program_synthesis",
        "whole_reduction_synthesis",
        "typed_capability_dag",
        "typed_tmkarp_admission_dag",
        "typed_tmkarp_dependent_composition_dag",
        "typed_program_indexed_admission_dag",
        "typed_tmkarp_program_indexed_composition_dag",
        "typed_gadget_indexed_admission_dag",
        "typed_exact_edge_construction_dag",
    }
)


@dataclass(frozen=True)
class NPHardSemanticFormulaStructureV1:
    reference_constructor: str
    block_declaration: str
    introduction_lemma: str
    elimination_lemma: str


@dataclass(frozen=True)
class NPHardSemanticForwardPlanV1:
    target_assignment: str
    literal_value_lemma: str
    main_constraint_lemma: str
    complement_constraint_lemma: str
    block_proof_method: str


@dataclass(frozen=True)
class NPHardSemanticReversePlanV1:
    source_assignment: str
    block_extraction_method: str
    main_constraint_lemma: str
    complement_constraint_lemma: str
    literal_recovery_lemma: str


@dataclass(frozen=True)
class NPHardSemanticLanguageConversionV1:
    method: str
    definitions: tuple[str, ...]


@dataclass(frozen=True)
class NPHardSemanticPlanV1:
    """Strict shared plan consumed by the two reference-semantic nodes."""

    dependency_fingerprint: str
    formula_structure: NPHardSemanticFormulaStructureV1
    forward: NPHardSemanticForwardPlanV1
    reverse: NPHardSemanticReversePlanV1
    language_conversion: NPHardSemanticLanguageConversionV1
    ordered_obligations: tuple[str, ...]
    schema_version: str = NP_HARD_SEMANTIC_PLAN_SCHEMA_V1

    def validate_shape(self) -> None:
        if self.schema_version != NP_HARD_SEMANTIC_PLAN_SCHEMA_V1:
            _v2_fail("invalid_semantic_plan_schema", "unsupported semantic plan schema")
        _v2_require_hash(
            self.dependency_fingerprint, label="semantic plan dependency fingerprint"
        )
        values = (
            self.formula_structure.reference_constructor,
            self.formula_structure.block_declaration,
            self.formula_structure.introduction_lemma,
            self.formula_structure.elimination_lemma,
            self.forward.target_assignment,
            self.forward.literal_value_lemma,
            self.forward.main_constraint_lemma,
            self.forward.complement_constraint_lemma,
            self.forward.block_proof_method,
            self.reverse.source_assignment,
            self.reverse.block_extraction_method,
            self.reverse.main_constraint_lemma,
            self.reverse.complement_constraint_lemma,
            self.reverse.literal_recovery_lemma,
            self.language_conversion.method,
            *self.language_conversion.definitions,
            *self.ordered_obligations,
        )
        if not self.language_conversion.definitions:
            _v2_fail(
                "invalid_semantic_plan_schema",
                "semantic plan language conversion has no definitions",
            )
        if len(self.ordered_obligations) != 10:
            _v2_fail(
                "invalid_semantic_plan_schema",
                "semantic plan must contain five forward then five reverse obligations",
            )
        for value in values:
            if not isinstance(value, str) or not value.strip():
                _v2_fail(
                    "invalid_semantic_plan_schema",
                    "semantic plan contains an empty string field",
                )
            _v2_require_public_text(value, label="semantic plan field")

    def to_dict(self) -> dict[str, Any]:
        self.validate_shape()
        return {
            "schema_version": self.schema_version,
            "dependency_fingerprint": self.dependency_fingerprint,
            "formula_structure": asdict(self.formula_structure),
            "forward": asdict(self.forward),
            "reverse": asdict(self.reverse),
            "language_conversion": {
                "method": self.language_conversion.method,
                "definitions": list(self.language_conversion.definitions),
            },
            "ordered_obligations": list(self.ordered_obligations),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardSemanticPlanV1":
        def exact(mapping: Mapping[str, Any], expected: set[str], label: str) -> None:
            if set(mapping) != expected:
                _v2_fail(
                    "invalid_semantic_plan_schema",
                    f"{label} fields differ from the fixed schema",
                )

        if not isinstance(value, Mapping):
            _v2_fail("invalid_semantic_plan_schema", "semantic plan is not an object")
        exact(
            value,
            {
                "schema_version",
                "dependency_fingerprint",
                "formula_structure",
                "forward",
                "reverse",
                "language_conversion",
                "ordered_obligations",
            },
            "semantic plan",
        )
        nested_specs = {
            "formula_structure": {
                "reference_constructor",
                "block_declaration",
                "introduction_lemma",
                "elimination_lemma",
            },
            "forward": {
                "target_assignment",
                "literal_value_lemma",
                "main_constraint_lemma",
                "complement_constraint_lemma",
                "block_proof_method",
            },
            "reverse": {
                "source_assignment",
                "block_extraction_method",
                "main_constraint_lemma",
                "complement_constraint_lemma",
                "literal_recovery_lemma",
            },
            "language_conversion": {"method", "definitions"},
        }
        nested: dict[str, Mapping[str, Any]] = {}
        for name, fields in nested_specs.items():
            item = value[name]
            if not isinstance(item, Mapping):
                _v2_fail("invalid_semantic_plan_schema", f"{name} is not an object")
            exact(item, fields, name)
            nested[name] = item
        definitions = nested["language_conversion"]["definitions"]
        obligations = value["ordered_obligations"]
        if (
            not isinstance(definitions, list)
            or not all(isinstance(item, str) for item in definitions)
            or not isinstance(obligations, list)
            or not all(isinstance(item, str) for item in obligations)
        ):
            _v2_fail(
                "invalid_semantic_plan_schema",
                "semantic plan list fields are invalid",
            )
        plan = cls(
            schema_version=value["schema_version"],
            dependency_fingerprint=value["dependency_fingerprint"],
            formula_structure=NPHardSemanticFormulaStructureV1(
                **dict(nested["formula_structure"])
            ),
            forward=NPHardSemanticForwardPlanV1(**dict(nested["forward"])),
            reverse=NPHardSemanticReversePlanV1(**dict(nested["reverse"])),
            language_conversion=NPHardSemanticLanguageConversionV1(
                method=nested["language_conversion"]["method"],
                definitions=tuple(definitions),
            ),
            ordered_obligations=tuple(obligations),
        )
        plan.validate_shape()
        return plan


def deletion_command_matches_declaration_v2(
    command: Mapping[str, Any], declaration: str
) -> bool:
    """Match the exact missing Lean declaration named by an error diagnostic."""

    if (
        command.get("timed_out") is not False
        or isinstance(command.get("exit_code"), bool)
        or not isinstance(command.get("exit_code"), int)
        or command.get("exit_code") == 0
    ):
        return False
    stdout = command.get("stdout")
    stderr = command.get("stderr")
    if not isinstance(stdout, str) or not isinstance(stderr, str):
        return False
    if "." not in declaration:
        return False
    identifier = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
    diagnostic_prefix = re.compile(
        r"^(?:[^:\r\n]*\.lean:\d+:\d+:\s*)?"
        r"error(?:\(lean\.unknown(?:identifier|constant)\)|:)\s*",
        re.IGNORECASE,
    )
    unknown_target = re.compile(
        r"\bunknown\s+(?:identifier|constant)\s+(?:"
        rf"`(?P<backtick>{identifier})`|"
        rf'"(?P<double>{identifier})"|'
        rf"'(?P<single>{identifier})'|"
        rf"(?P<bare>{identifier}))",
        re.IGNORECASE,
    )
    for line in (stdout + "\n" + stderr).splitlines():
        prefix = diagnostic_prefix.match(line)
        if prefix is None:
            continue
        for match in unknown_target.finditer(line, prefix.end()):
            missing_name = next(
                value for value in match.groups() if value is not None
            )
            if missing_name == declaration:
                return True
            if not missing_name.startswith(declaration + "."):
                continue
            projection = missing_name[len(declaration) + 1 :]
            if projection and all(
                re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", component)
                is not None
                for component in projection.split(".")
            ):
                return True
    return False

_NP_HARD_TYPED_TASK_CLASSES_V2 = frozenset(
    {
        "whole_reduction_synthesis",
        "typed_capability_dag",
        "typed_tmkarp_admission_dag",
        "typed_tmkarp_dependent_composition_dag",
        "typed_program_indexed_admission_dag",
        "typed_tmkarp_program_indexed_composition_dag",
        "typed_gadget_indexed_admission_dag",
        "typed_exact_edge_construction_dag",
    }
)
_NP_HARD_EXACT_STAGED_TASK_MOTIFS_V2 = {
    "whole_reduction_synthesis": (
        ("reduction-executable", "reduction_executable", ()),
        ("direct-tm", "direct_tm", ("reduction-executable",)),
        (
            "reduction-primitive",
            "reduction_primitive",
            ("reduction-executable", "direct-tm"),
        ),
        ("poly-program", "poly_program", ("reduction-primitive",)),
        (
            "program-run-coherence",
            "program_run_coherence",
            ("poly-program", "reduction-executable"),
        ),
        (
            "semantic-forward",
            "semantic_forward",
            ("poly-program", "program-run-coherence"),
        ),
        (
            "semantic-reverse",
            "semantic_reverse",
            ("poly-program", "program-run-coherence"),
        ),
        (
            "semantic-iff",
            "semantic_iff",
            ("semantic-forward", "semantic-reverse"),
        ),
    ),
    "typed_tmkarp_dependent_composition_dag": (
        ("tmkarp-primitive", "tmkarp_primitive", ()),
        ("tmkarp-program", "tmkarp_program", ("tmkarp-primitive",)),
        ("tmkarp-semantic-iff", "tmkarp_semantic_iff", ("tmkarp-program",)),
        ("composed-program", "dependent_composed_program", ("tmkarp-program",)),
        (
            "composed-semantic-iff",
            "dependent_composed_semantic_iff",
            ("tmkarp-semantic-iff", "composed-program"),
        ),
    ),
    "typed_gadget_indexed_admission_dag": (
        ("gadget-reference-audit", "gadget_reference_audit", ()),
        (
            "gadget-normalization-audit",
            "gadget_normalization_audit",
            ("gadget-reference-audit",),
        ),
        (
            "gadget-executable",
            "gadget_executable",
            ("gadget-reference-audit", "gadget-normalization-audit"),
        ),
        (
            "gadget-parameter-audit",
            "gadget_parameter_audit",
            ("gadget-executable",),
        ),
        (
            "gadget-semantic-forward",
            "gadget_semantic_forward",
            ("gadget-executable", "gadget-parameter-audit"),
        ),
        (
            "gadget-semantic-reverse",
            "gadget_semantic_reverse",
            ("gadget-executable", "gadget-parameter-audit"),
        ),
        (
            "gadget-direct-tm",
            "gadget_direct_tm",
            (
                "gadget-executable",
                "gadget-parameter-audit",
                "gadget-semantic-forward",
                "gadget-semantic-reverse",
            ),
        ),
        (
            "gadget-program",
            "gadget_program",
            ("gadget-executable", "gadget-direct-tm"),
        ),
        (
            "gadget-composed-program",
            "gadget_composed_program",
            ("gadget-program",),
        ),
        (
            "gadget-composed-semantic-iff",
            "gadget_composed_semantic_iff",
            (
                "gadget-semantic-forward",
                "gadget-semantic-reverse",
                "gadget-program",
                "gadget-composed-program",
            ),
        ),
    ),
    "typed_exact_edge_construction_dag": (
        ("parameter-normalization", "parameter_normalization", ()),
        (
            "reduction-primitive",
            "reduction_primitive",
            ("parameter-normalization",),
        ),
        (
            "gadget-definitions",
            "gadget_definitions",
            ("reduction-primitive",),
        ),
        (
            "output-wellformed",
            "output_wellformed",
            ("parameter-normalization", "reduction-primitive", "gadget-definitions"),
        ),
        (
            "polynomial-bound",
            "polynomial_bound",
            ("reduction-primitive",),
        ),
        (
            "poly-program",
            "poly_program",
            ("reduction-primitive", "polynomial-bound"),
        ),
        (
            "program-direct-tm-coherence",
            "program_direct_tm_coherence",
            ("poly-program", "reduction-primitive"),
        ),
        (
            "semantic-forward",
            "semantic_forward",
            ("poly-program",),
        ),
        (
            "semantic-reverse",
            "semantic_reverse",
            ("poly-program",),
        ),
        (
            "semantic-iff",
            "semantic_iff",
            ("semantic-forward", "semantic-reverse"),
        ),
        (
            "certified-reduction",
            "certified_reduction",
            (
                "parameter-normalization",
                "reduction-primitive",
                "gadget-definitions",
                "output-wellformed",
                "polynomial-bound",
                "poly-program",
                "program-direct-tm-coherence",
                "semantic-forward",
                "semantic-reverse",
                "semantic-iff",
            ),
        ),
    ),
}
_NP_HARD_POSITIVE_NAE3_WHOLE_REDUCTION_MOTIF_V2 = (
    ("clause-constraint", "clause_constraint", ()),
    ("complement-constraint", "complement_constraint", ()),
    (
        "clause-gadget",
        "clause_gadget",
        ("clause-constraint", "complement-constraint"),
    ),
    ("reference-executable", "reference_executable", ("clause-gadget",)),
    (
        "reduction-executable",
        "reduction_executable",
        ("reference-executable",),
    ),
    (
        "clause-gadget-direct-tm",
        "clause_gadget_direct_tm",
        ("clause-gadget",),
    ),
    (
        "reference-direct-tm",
        "reference_direct_tm",
        ("reference-executable", "clause-gadget-direct-tm"),
    ),
    (
        "direct-tm",
        "direct_tm",
        ("reduction-executable", "reference-direct-tm"),
    ),
    (
        "reduction-primitive",
        "reduction_primitive",
        ("reduction-executable", "direct-tm"),
    ),
    ("poly-program", "poly_program", ("reduction-primitive",)),
    (
        "program-run-coherence",
        "program_run_coherence",
        ("poly-program", "reduction-executable"),
    ),
    (
        "reference-semantic-forward",
        "reference_semantic_forward",
        ("clause-gadget", "reference-executable"),
    ),
    (
        "reference-semantic-reverse",
        "reference_semantic_reverse",
        ("clause-gadget", "reference-executable"),
    ),
    (
        "semantic-forward",
        "semantic_forward",
        (
            "reduction-executable",
            "program-run-coherence",
            "reference-semantic-forward",
        ),
    ),
    (
        "semantic-reverse",
        "semantic_reverse",
        (
            "reduction-executable",
            "program-run-coherence",
            "reference-semantic-reverse",
        ),
    ),
    (
        "semantic-iff",
        "semantic_iff",
        ("semantic-forward", "semantic-reverse"),
    ),
)
_NP_HARD_EXACT_STAGED_TASK_BOUNDARIES_V2 = {
    "whole_reduction_synthesis": ("semantic-iff", "poly-program"),
    "typed_tmkarp_dependent_composition_dag": (
        "composed-semantic-iff",
        "composed-program",
    ),
    "typed_gadget_indexed_admission_dag": (
        "gadget-composed-semantic-iff",
        "gadget-composed-program",
    ),
    "typed_exact_edge_construction_dag": (
        "certified-reduction",
        "poly-program",
    ),
}
_NP_HARD_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.AuthoringSources"
)
_NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources"
)
_NP_HARD_PROGRAM_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources"
)
_NP_HARD_GADGET_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources"
)
NP_HARD_AUTHORING_OUTCOMES_V2 = frozenset(
    {"accepted", "rejected", "budget_exhausted", "infra_error"}
)

_NP_HARD_V2_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")
_NP_HARD_V2_NODE_RE = re.compile(r"[a-z][a-z0-9-]*\Z")
_NP_HARD_CERTIFIED_REDUCTION_HEAD_V2 = (
    "ComplexityReduction.Certificate.CertifiedReduction"
)
_NP_HARD_GADGET_PACKET_HEAD_V2 = (
    "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources."
    "GadgetIndexedAdmissionPacket"
)
_NP_HARD_TMKARP_REDUCTION_HEAD_V2 = "ComplexityReduction.TMKarpReduction"
_NP_HARD_OBSERVER_CAPABILITY_RECORD_KEYS_V2 = frozenset(
    {
        "capability_kind",
        "id",
        "source",
        "target",
        "source_node",
        "target_node",
        "witness",
        "exact_type",
        "module",
        "authority",
        "registry_fingerprint",
    }
)
_NP_HARD_SUCCESSOR_ONLY_CHAIN_SCHEMA_V2 = (
    "hardness_np_hard_successor_only_observer_chain_v1"
)
_NP_HARD_V2_FORBIDDEN_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)

NP_HARD_AUTHORING_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 term author. Return exactly one JSON object with
only `candidate_declaration` and `replacement_body`, and no markdown. The
orchestrator has frozen the request, source hardness hub, target
problem, direction, declaration, imports, and exact CertifiedReduction type.
You may submit only the Lean term body that fills the declaration after `:=`.
This is a small local construction: keep internal reasoning minimal and emit
the JSON answer immediately. On the first candidate, you MUST try the simplest
kernel-checkable correctness proof, `by intro input; rfl`, whenever the supplied
program run and target acceptance are definitionally equal; do not introduce
`unfold`, `simp`, or a manual iff proof before Lean has rejected that `rfl`
candidate. On a repair turn, never repeat the current rejected body. A target
semantic definition cannot be unfolded inside a source-side hypothesis. Prefer
a fully-qualified public PolyProg already supplied by the input module over
rebuilding that executable.
Do not emit imports, namespaces, declarations, commands, markdown, sorry,
admit, axioms, unsafe code, filesystem operations, or a reduction in the
opposite direction. Use the public input source and Lean diagnostics only.
The Lean compiler, exact resolver, axiom audit, and independent replay decide
whether the candidate is accepted; your response has no proof authority.
"""


class NPHardModelClient(Protocol):
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class NPHardAuthoringTaskV1:
    request_id: str
    registry_fingerprint: str
    input_module: str
    input_problem_declaration: str
    hub_declaration: str
    seed_evidence_declaration: str
    seed_evidence_kind: str
    candidate_module: str
    candidate_declaration: str
    exact_type: str
    input_source_sha256: str
    max_attempts: int
    direction: str = NP_HARD_AUTHORING_DIRECTION
    schema_version: str = NP_HARD_AUTHORING_TASK_SCHEMA_V1

    def validate(self) -> None:
        if self.schema_version != NP_HARD_AUTHORING_TASK_SCHEMA_V1:
            raise ValueError("unsupported NP-hard authoring task schema")
        validate_module_name(self.input_module)
        validate_module_name(self.candidate_module)
        for label, declaration in {
            "input problem": self.input_problem_declaration,
            "hardness hub": self.hub_declaration,
            "seed evidence": self.seed_evidence_declaration,
            "candidate": self.candidate_declaration,
        }.items():
            validate_declaration_name(declaration, label=label)
        if self.direction != NP_HARD_AUTHORING_DIRECTION:
            raise ValueError("NP-hard authoring task changed the frozen direction")
        if not self.request_id.startswith("lean:"):
            raise ValueError("NP-hard authoring task has an invalid request ID")
        if not self.registry_fingerprint.startswith("lean:"):
            raise ValueError("NP-hard authoring task has an invalid registry fingerprint")
        if not self.exact_type.strip():
            raise ValueError("NP-hard authoring task has an empty exact type")
        if not 1 <= self.max_attempts <= 4:
            raise ValueError("NP-hard authoring attempts must be between one and four")

    @property
    def gap_id(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, Any]:
        return {**asdict(self), "gap_id": self.gap_id}


@dataclass(frozen=True)
class NPHardAuthoredCandidateV1:
    task: NPHardAuthoringTaskV1
    source: str
    source_sha256: str
    body_sha256: str
    model_response_sha256: str
    attempt: int
    model_calls: int
    commands: tuple[CommandResult, ...]
    worker_results: tuple[LeanWorkerResult, ...]
    call_records: tuple[dict[str, Any], ...]


@dataclass(frozen=True)
class NPHardAuthoringFailureV1:
    code: str
    explanation: str
    model_calls: int
    commands: tuple[CommandResult, ...]
    worker_results: tuple[LeanWorkerResult, ...]
    call_records: tuple[dict[str, Any], ...]


def _tagged_content_hash(value: str) -> str:
    """Normalize raw SHA-256 values for the strict worker-key contract."""

    if value.startswith("sha256:") and len(value) == 71:
        return value
    if len(value) == 64 and all(character in "0123456789abcdef" for character in value):
        return f"sha256:{value}"
    return sha256_id(value)


def _worker_diagnostic(result: LeanWorkerResult) -> str:
    messages: list[str] = []
    for item in result.diagnostics:
        message = str(item.get("message", "Lean rejected candidate")).strip()
        if message:
            messages.append(message)
    return "\n".join(messages[:12])[:4_000] or "Lean rejected candidate"


def build_np_hard_authoring_task(
    *,
    request_id: str,
    registry_fingerprint: str,
    input_module: str,
    input_problem_declaration: str,
    hub_declaration: str,
    seed_evidence_declaration: str,
    seed_evidence_kind: str,
    input_source_sha256: str,
    job_id: str,
    max_attempts: int,
) -> NPHardAuthoringTaskV1:
    segment = job_id.removeprefix("sha256:")[:16]
    candidate_module = f"Generated.NPHard.C{segment}.AuthoredForward"
    candidate_declaration = f"{candidate_module}.authoredForwardReduction"
    exact_type = (
        "ComplexityReduction.Certificate.CertifiedReduction "
        f"{hub_declaration} {input_problem_declaration}"
    )
    task = NPHardAuthoringTaskV1(
        request_id=request_id,
        registry_fingerprint=registry_fingerprint,
        input_module=input_module,
        input_problem_declaration=input_problem_declaration,
        hub_declaration=hub_declaration,
        seed_evidence_declaration=seed_evidence_declaration,
        seed_evidence_kind=seed_evidence_kind,
        candidate_module=candidate_module,
        candidate_declaration=candidate_declaration,
        exact_type=exact_type,
        input_source_sha256=input_source_sha256,
        max_attempts=max_attempts,
    )
    task.validate()
    return task


def build_np_hard_candidate(
    task: NPHardAuthoringTaskV1, *, body: str = "by\n  contradiction\n"
) -> CandidateSource:
    task.validate()
    candidate = CandidateSource(
        fixed_header=(
            f"import {task.input_module}\n"
            f"import {RUNTIME_MODULE}\n\n"
            f"namespace {task.candidate_module}\n\n"
            "open ComplexityReduction\n"
            "open ComplexityReduction.Certificate\n\n"
            "@[complexity_reduction_ir_typed_edge, "
            "complexity_reduction_ir_component_shared_gadget]\n"
            "noncomputable def authoredForwardReduction :\n"
            f"    {task.exact_type} :=\n"
        ),
        editable_body=body if body.endswith("\n") else body + "\n",
        fixed_footer=(
            f"\nend {task.candidate_module}\n\n"
            f"assert_standard_axioms {task.candidate_declaration}\n"
        ),
        allowed_imports=(task.input_module, RUNTIME_MODULE),
    )
    candidate.validate()
    return candidate


def _response_record(response: ModelResponse, *, attempt: int) -> dict[str, Any]:
    return {
        "attempt": attempt,
        "called": response.called,
        "ok": response.ok,
        "status_code": response.status_code,
        "duration_seconds": response.duration_seconds,
        "usage": response.usage,
        "attempts": response.attempts,
        "finish_reason": response.finish_reason,
        "response_sha256": sha256_id(response.content),
        "response_content": response.content[:20_000],
        "error": response.error,
    }


def _prompt(
    *,
    task: NPHardAuthoringTaskV1,
    input_source: str,
    current_body: str,
    diagnostic: str | None,
) -> str:
    payload: dict[str, Any] = {
        "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V1,
        "request_id": task.request_id,
        "gap_id": task.gap_id,
        "registry_fingerprint": task.registry_fingerprint,
        "objective": "prove_np_hard",
        "direction": task.direction,
        "source_hardness_hub": task.hub_declaration,
        "target_problem": task.input_problem_declaration,
        "seed_evidence": task.seed_evidence_declaration,
        "seed_evidence_kind": task.seed_evidence_kind,
        "candidate_declaration": task.candidate_declaration,
        "declaration_signature": task.exact_type,
        "public_type_summary": (
            "CertifiedReduction is a structure with exactly two fields: "
            "program : PolyProg source.representation target.representation; "
            "correct : forall input, source.accepts input iff "
            "target.accepts (program.run input). Construct it with a structure "
            "literal with program and correct on separate lines; indent every "
            "tactic under `correct := by` farther than the correct field. Do not unfold "
            "the structure type. Private declarations in the input source cannot "
            "be named from the candidate module."
        ),
        "current_editable_body": current_body,
        "validation_strategy": {
            "initial_candidate": (
                "Use the public program and set correct := by; intro input; rfl. "
                "Do not use unfold/simp/manual constructor unless Lean first rejects rfl."
            ),
            "repair_candidate": (
                "The replacement_body must differ from current_editable_body. "
                "Never unfold a target-only semantic definition inside a source-side hypothesis."
            ),
            "compiler_inserted_math_tokens": 0,
        },
        "public_input_source": input_source[:20_000],
        "lean_diagnostic": diagnostic[:4_000] if diagnostic else None,
        "response_template": {
            "candidate_declaration": task.candidate_declaration,
            "replacement_body": "Lean term body only",
        },
    }
    return json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)


def parse_np_hard_authoring_body(
    *, content: str, task: NPHardAuthoringTaskV1
) -> str:
    task.validate()
    payload = extract_json_object(content)
    if not isinstance(payload, dict):
        raise ValueError("model did not return one JSON object")
    expected = {
        "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V1,
        "action": "submit_patch",
        "request_id": task.request_id,
        "gap_id": task.gap_id,
        "direction": task.direction,
        "source_declaration": task.hub_declaration,
        "target_declaration": task.input_problem_declaration,
        "candidate_declaration": task.candidate_declaration,
        "declaration_signature": task.exact_type,
    }
    allowed_keys = {*expected, "replacement_body"}
    if not set(payload).issubset(allowed_keys) or not {
        "candidate_declaration",
        "replacement_body",
    }.issubset(payload):
        raise ValueError("model response changed the closed NP-hard patch schema")
    for key, value in expected.items():
        if key in payload and payload[key] != value:
            raise ValueError(f"model response mutated frozen field: {key}")
    body = payload.get("replacement_body")
    if not isinstance(body, str) or not body.strip():
        raise ValueError("model response has an empty Lean term body")
    if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
        raise ValueError("model response exceeded the Lean body size fence")
    if BANNED_BODY_RE.search(body):
        raise ValueError("model response contains a forbidden Lean command or trust token")
    assert_generated_source_is_safe(body)
    return body if body.endswith("\n") else body + "\n"


def _authoring_error_code(error: ValueError) -> str:
    message = str(error)
    if "direction" in message:
        return "candidate_wrong_direction"
    if any(
        field in message
        for field in (
            "source_declaration",
            "target_declaration",
            "candidate_declaration",
            "declaration_signature",
        )
    ):
        return "candidate_wrong_endpoint"
    if "forbidden Lean command or trust token" in message:
        return "candidate_nonstandard_axiom"
    return "authoring_budget_exhausted"


def author_exact_np_hard_reduction(
    *,
    task: NPHardAuthoringTaskV1,
    input_source: str,
    model: NPHardModelClient | None,
    lean_root: Path,
    candidate_path: Path,
    timeout_seconds: int,
    worker_pool: LeanWorkerPool | None = None,
    worker_session_id: str | None = None,
    worker_owner: str | None = None,
    toolchain: str | None = None,
    lake_manifest_sha256: str | None = None,
) -> NPHardAuthoredCandidateV1 | NPHardAuthoringFailureV1:
    """Run bounded model/Lean repair for one immutable forward reduction."""

    task.validate()
    if model is None:
        return NPHardAuthoringFailureV1(
            code="model_provider_unavailable",
            explanation="prove_np_hard authoring requires a configured model client",
            model_calls=0,
            commands=(),
            worker_results=(),
            call_records=(),
        )
    worker_arguments = (
        worker_session_id,
        worker_owner,
        toolchain,
        lake_manifest_sha256,
    )
    if worker_pool is not None and any(value is None for value in worker_arguments):
        raise ValueError("persistent NP-hard candidate validation is missing worker metadata")
    if worker_pool is None and any(value is not None for value in worker_arguments):
        raise ValueError("NP-hard worker metadata was supplied without a worker pool")
    candidate = build_np_hard_candidate(task)
    diagnostic: str | None = None
    seen_bodies: set[str] = set()
    seen_diagnostics: set[str] = set()
    last_lean_diagnostic: str | None = None
    commands: list[CommandResult] = []
    worker_results: list[LeanWorkerResult] = []
    calls: list[dict[str, Any]] = []
    model_calls = 0
    last_error = "authoring attempts were exhausted"
    last_failure_code = "authoring_budget_exhausted"
    for attempt in range(1, task.max_attempts + 1):
        response = model.complete_json(
            system=NP_HARD_AUTHORING_SYSTEM_PROMPT,
            prompt=_prompt(
                task=task,
                input_source=input_source,
                current_body=candidate.editable_body,
                diagnostic=diagnostic,
            ),
        )
        calls.append(_response_record(response, attempt=attempt))
        model_calls += int(response.called)
        if not response.called:
            return NPHardAuthoringFailureV1(
                code="model_provider_unavailable",
                explanation=response.error or "the configured model was not called",
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        if not response.ok:
            return NPHardAuthoringFailureV1(
                code="model_provider_unavailable",
                explanation=response.error or "model request failed",
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        try:
            body = parse_np_hard_authoring_body(content=response.content, task=task)
            body_hash = sha256_id(body)
            if body_hash in seen_bodies:
                raise ValueError("model repeated an authored Lean body")
            seen_bodies.add(body_hash)
            candidate = candidate.replace_body(body)
        except ValueError as error:
            last_error = str(error)
            last_failure_code = _authoring_error_code(error)
            diagnostic = (
                f"Patch protocol error: {last_error}\n"
                + (
                    f"Last Lean diagnostic (still authoritative):\n{last_lean_diagnostic}"
                    if last_lean_diagnostic
                    else ""
                )
            )
            continue
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        temporary = candidate_path.with_suffix(candidate_path.suffix + ".tmp")
        temporary.write_text(candidate.source, encoding="utf-8")
        temporary.replace(candidate_path)
        if worker_pool is None:
            compile_result = run_command(
                ["lake", "env", "lean", str(candidate_path)],
                cwd=lean_root,
                timeout_seconds=timeout_seconds,
            )
            commands.append(compile_result)
            candidate_verified = compile_result.ok
            candidate_diagnostic = (
                compile_result.stderr or compile_result.stdout or "Lean rejected candidate"
            )[:4_000]
        else:
            assert worker_session_id is not None
            assert worker_owner is not None
            assert toolchain is not None
            assert lake_manifest_sha256 is not None
            dependency_hash = sha256_id(
                {
                    "input_source_sha256": task.input_source_sha256,
                    "registry_fingerprint": task.registry_fingerprint,
                    "exact_type": task.exact_type,
                }
            )
            worker_result = worker_pool.validate(
                session_id=worker_session_id,
                owner=worker_owner,
                key=LeanWorkerKey(
                    toolchain=toolchain,
                    lake_manifest_sha256=_tagged_content_hash(lake_manifest_sha256),
                    base_registry_fingerprint=sha256_id(task.registry_fingerprint),
                    complete_source_sha256=candidate.source_sha256,
                    dependency_sha256=(dependency_hash,),
                    namespace=task.candidate_module,
                    session_id=worker_session_id,
                    editable_allowlist=("replacement_body",),
                ),
                source_path=candidate_path,
                dependency_sha256=(dependency_hash,),
                use_cache=False,
                allow_cold_fallback=False,
            )
            worker_results.append(worker_result)
            candidate_verified = worker_result.verified
            candidate_diagnostic = _worker_diagnostic(worker_result)
        if candidate_verified:
            return NPHardAuthoredCandidateV1(
                task=task,
                source=candidate.source,
                source_sha256=candidate.source_sha256,
                body_sha256=body_hash,
                model_response_sha256=sha256_id(response.content),
                attempt=attempt,
                model_calls=model_calls,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                call_records=tuple(calls),
            )
        diagnostic = candidate_diagnostic
        last_lean_diagnostic = diagnostic
        diagnostic_hash = sha256_id(diagnostic)
        if diagnostic_hash in seen_diagnostics:
            last_error = "Lean diagnostics repeated without authoring progress"
            break
        seen_diagnostics.add(diagnostic_hash)
        last_error = diagnostic
        last_failure_code = "authoring_budget_exhausted"
    return NPHardAuthoringFailureV1(
        code=(
            "semantic_proof_failed"
            if last_failure_code == "authoring_budget_exhausted"
            else last_failure_code
        ),
        explanation=last_error,
        model_calls=model_calls,
        commands=tuple(commands),
        worker_results=tuple(worker_results),
        call_records=tuple(calls),
    )


def publish_np_hard_candidate(
    *, root: Path, candidate: NPHardAuthoredCandidateV1
) -> tuple[Path, dict[str, Any]]:
    """Publish an immutable, content-addressed copy scoped to this job."""

    digest = candidate.source_sha256.removeprefix("sha256:")
    pack_root = root / "published" / digest
    source_path = (
        pack_root
        / "src"
        / Path(*candidate.task.candidate_module.split(".")).with_suffix(".lean")
    )
    manifest_path = pack_root / "manifest.json"
    if pack_root.exists():
        raise ValueError("NP-hard candidate publication already exists")
    source_path.parent.mkdir(parents=True, exist_ok=False)
    source_path.write_text(candidate.source, encoding="utf-8")
    manifest = {
        "schema_version": NP_HARD_AUTHORING_PUBLICATION_SCHEMA_V1,
        "task": candidate.task.to_dict(),
        "source_sha256": candidate.source_sha256,
        "body_sha256": candidate.body_sha256,
        "model_response_sha256": candidate.model_response_sha256,
        "model_calls": candidate.model_calls,
        "attempt": candidate.attempt,
        "provenance_kind": "model_generated",
        "direction": candidate.task.direction,
        "source_declaration": candidate.task.hub_declaration,
        "target_declaration": candidate.task.input_problem_declaration,
        "compiler_inserted_math_token_count": 0,
        "source_relative_path": str(source_path.relative_to(pack_root)),
    }
    manifest_path.write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    source_path.chmod(0o444)
    manifest_path.chmod(0o444)
    return source_path, manifest


class NPHardAuthoringContractError(ValueError):
    """Stable, machine-readable rejection from the v2 NP-hard contract."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _v2_fail(code: str, message: str) -> None:
    raise NPHardAuthoringContractError(code, message)


def _normalized_certified_successor_exact_endpoints_v2(
    *,
    exact_type: str,
    witness: str,
    successor_module: str,
    expected_source: str,
    expected_target: str,
) -> tuple[str, str] | None:
    """Parse one exact fully-qualified ``CertifiedReduction`` application.

    New observations serialize the canonical endpoint handles directly.  For
    byte-compatible H-J.4 task roundtrips, the sole normalization accepted is
    the historical route-owned ``sourceProblem``/``targetProblem`` alias pair,
    derived from the already bound witness/module namespace.  Parsing is token
    exact: reversed endpoints, unrelated aliases, and extra wrappers cannot be
    accepted through substring matches.
    """

    parsed_endpoints = _exact_certified_reduction_endpoints_v2(exact_type)
    if parsed_endpoints is None:
        return None
    parsed_source, parsed_target = parsed_endpoints
    try:
        validate_declaration_name(witness, label="certified successor witness")
        validate_module_name(successor_module)
    except ValueError:
        return None

    witness_namespace = witness.rsplit(".", 1)[0]
    legacy_namespace_owned = _certified_successor_witness_owned_by_module_v2(
        witness=witness, successor_module=successor_module
    )
    legacy_source = (
        f"{witness_namespace}.sourceProblem" if legacy_namespace_owned else None
    )
    legacy_target = (
        f"{witness_namespace}.targetProblem" if legacy_namespace_owned else None
    )
    normalized_source = (
        expected_source
        if parsed_source == expected_source or parsed_source == legacy_source
        else parsed_source
    )
    normalized_target = (
        expected_target
        if parsed_target == expected_target or parsed_target == legacy_target
        else parsed_target
    )
    return normalized_source, normalized_target


def _exact_certified_reduction_endpoints_v2(
    exact_type: str,
) -> tuple[str, str] | None:
    """Parse exactly one fully-qualified two-endpoint CertifiedReduction type."""

    if not isinstance(exact_type, str):
        return None
    tokens = exact_type.split()
    if len(tokens) != 3 or tokens[0] != _NP_HARD_CERTIFIED_REDUCTION_HEAD_V2:
        return None
    endpoints = (tokens[1], tokens[2])
    try:
        for endpoint in endpoints:
            validate_declaration_name(
                endpoint, label="certified reduction endpoint"
            )
    except ValueError:
        return None
    if any("." not in endpoint for endpoint in endpoints):
        return None
    return endpoints


def _certified_successor_witness_owned_by_module_v2(
    *, witness: str, successor_module: str
) -> bool:
    """Check the qualified declaration namespace against its Lean module.

    Route modules conventionally end in ``.Unified`` while their declarations
    live in the immediately enclosing route namespace.  Otherwise the
    declaration namespace must equal the module name itself.  A merely
    fully-qualified unrelated declaration is never accepted.
    """

    try:
        validate_declaration_name(witness, label="certified successor witness")
        validate_module_name(successor_module)
    except ValueError:
        return False
    witness_namespace = witness.rsplit(".", 1)[0]
    allowed_namespaces = {successor_module}
    if successor_module.endswith(".Unified"):
        allowed_namespaces.add(successor_module.removesuffix(".Unified"))
    return witness_namespace in allowed_namespaces


def _exact_gadget_packet_endpoints_v2(
    exact_type: str,
) -> tuple[str, str, str] | None:
    """Parse exactly one fully-qualified three-endpoint gadget packet type."""

    if not isinstance(exact_type, str):
        return None
    tokens = exact_type.split()
    if len(tokens) != 4 or tokens[0] != _NP_HARD_GADGET_PACKET_HEAD_V2:
        return None
    endpoints = (tokens[1], tokens[2], tokens[3])
    try:
        for endpoint in endpoints:
            validate_declaration_name(endpoint, label="gadget packet endpoint")
    except ValueError:
        return None
    if any("." not in endpoint for endpoint in endpoints):
        return None
    return endpoints


def _exact_tmkarp_reduction_endpoints_v2(
    exact_type: str,
) -> tuple[str, str] | None:
    """Parse exactly one fully-qualified two-endpoint TMKarp type."""

    if not isinstance(exact_type, str):
        return None
    tokens = exact_type.split()
    if len(tokens) != 3 or tokens[0] != _NP_HARD_TMKARP_REDUCTION_HEAD_V2:
        return None
    endpoints = (tokens[1], tokens[2])
    try:
        for endpoint in endpoints:
            validate_declaration_name(endpoint, label="TMKarp endpoint")
    except ValueError:
        return None
    if any("." not in endpoint for endpoint in endpoints):
        return None
    return endpoints


def _observer_capability_record_payload_v2(
    value: Mapping[str, str] | tuple[tuple[str, str], ...] | None,
) -> dict[str, str] | None:
    """Normalize one complete Lean observer typed-capability row."""

    if value is None:
        return None
    try:
        payload = dict(value)
    except (TypeError, ValueError):
        return None
    if set(payload) != _NP_HARD_OBSERVER_CAPABILITY_RECORD_KEYS_V2 or not all(
        isinstance(item, str) and item.strip() for item in payload.values()
    ):
        return None
    try:
        validate_declaration_name(payload["source"], label="observer source")
        validate_declaration_name(payload["target"], label="observer target")
        validate_declaration_name(payload["witness"], label="observer witness")
        validate_module_name(payload["module"])
    except ValueError:
        return None
    if (
        not payload["source_node"].startswith("lean-whnf:")
        or not payload["target_node"].startswith("lean-whnf:")
        or not payload["registry_fingerprint"].startswith("lean:")
    ):
        return None
    expected_id = (
        f"{payload['capability_kind']}:{payload['source_node']}:"
        f"{payload['target_node']}"
    )
    if payload["id"] != expected_id:
        return None
    return payload


def _successor_only_observer_chain_payload_v2(
    *,
    admission: Mapping[str, str],
    successor: Mapping[str, str],
    canonical_successor_source: str,
    canonical_successor_target: str,
) -> dict[str, Any]:
    return {
        "schema_version": _NP_HARD_SUCCESSOR_ONLY_CHAIN_SCHEMA_V2,
        "admission": dict(admission),
        "successor": dict(successor),
        "canonical_successor_source": canonical_successor_source,
        "canonical_successor_target": canonical_successor_target,
    }


def _module_public_source_file_v2(module: str) -> str:
    return "Lean/Reference/" + module.replace(".", "/") + ".lean"


def _staged_authoring_surface_is_exact_v2(
    *,
    allowed_imports: tuple[str, ...],
    public_source_files: tuple[str, ...],
    dependency_hashes: tuple[tuple[str, str], ...],
    source_module: str,
    target_module: str,
    intermediate_module: str,
    authority_modules: tuple[str, ...],
) -> bool:
    """Freeze the full model/compiler surface for one staged authoring class."""

    expected_imports = tuple(
        dict.fromkeys(
            (
                target_module,
                source_module,
                RUNTIME_MODULE,
                intermediate_module,
                *authority_modules,
            )
        )
    )
    expected_public_files = tuple(
        sorted(
            {
                _module_public_source_file_v2(module)
                for module in (
                    source_module,
                    target_module,
                    intermediate_module,
                    *authority_modules,
                )
            }
        )
    )
    dependencies = dict(dependency_hashes)
    module_keys = {name for name in dependencies if name.startswith("module:")}
    public_keys = {name for name in dependencies if name.startswith("public:")}
    return (
        len(allowed_imports) == len(expected_imports)
        and set(allowed_imports) == set(expected_imports)
        and len(public_source_files) == len(expected_public_files)
        and set(public_source_files) == set(expected_public_files)
        and module_keys == {f"module:{module}" for module in expected_imports}
        and public_keys
        == {f"public:{relative}" for relative in expected_public_files}
    )


def _v2_require_hash(value: str, *, label: str) -> None:
    if not isinstance(value, str) or not _NP_HARD_V2_HASH_RE.fullmatch(value):
        _v2_fail("candidate_dependency_stale", f"{label} is not a tagged SHA-256")


def _v2_contains_quarantined_text(value: str) -> bool:
    lowered = value.lower()
    return any(marker.lower() in lowered for marker in _NP_HARD_V2_FORBIDDEN_MARKERS)


def _v2_require_public_text(value: str, *, label: str) -> None:
    if _v2_contains_quarantined_text(value):
        _v2_fail("oracle_or_gold_import", f"{label} references quarantined proof material")


def _v2_exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            f"{label} keys drifted; missing={missing!r}, extra={extra!r}",
        )


@dataclass(frozen=True)
class NPHardAuthoringEndpointV2:
    module: str
    term: str

    def validate(self) -> None:
        try:
            validate_module_name(self.module)
            validate_declaration_name(self.term, label="NP-hard v2 endpoint")
        except ValueError as error:
            _v2_fail("candidate_wrong_endpoint", str(error))
        _v2_require_public_text(self.module, label="endpoint module")
        _v2_require_public_text(self.term, label="endpoint declaration")

    def to_dict(self) -> dict[str, str]:
        self.validate()
        return {"module": self.module, "term": self.term}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringEndpointV2":
        if not isinstance(value, Mapping):
            _v2_fail("candidate_wrong_endpoint", "endpoint must be an object")
        _v2_exact_keys(value, {"module", "term"}, label="endpoint")
        if not isinstance(value["module"], str) or not isinstance(value["term"], str):
            _v2_fail("candidate_wrong_endpoint", "endpoint fields must be strings")
        endpoint = cls(module=value["module"], term=value["term"])
        endpoint.validate()
        return endpoint


@dataclass(frozen=True)
class NPHardAuthoringObligationV2:
    node_id: str
    declaration: str
    capability: str
    exact_type: str
    depends_on: tuple[str, ...]

    def validate(self) -> None:
        if not _NP_HARD_V2_NODE_RE.fullmatch(self.node_id):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "invalid gap node ID")
        try:
            validate_declaration_name(self.declaration, label="v2 editable declaration")
        except ValueError as error:
            _v2_fail("candidate_outside_edit_boundary", str(error))
        if self.capability not in {
            "reduction_executable",
            "clause_constraint",
            "complement_constraint",
            "clause_gadget",
            "reference_executable",
            "direct_tm",
            "clause_gadget_direct_tm",
            "reference_direct_tm",
            "representation_adapter",
            "poly_program",
            "program_run_coherence",
            "mapping_invariant",
            "semantic_forward",
            "semantic_reverse",
            "reference_semantic_forward",
            "reference_semantic_reverse",
            "semantic_iff",
            "semantic_proof",
            "tmkarp_primitive",
            "tmkarp_program",
            "tmkarp_semantic_iff",
            "dependent_composed_program",
            "dependent_composed_semantic_iff",
            "program_indexed_executable",
            "program_indexed_primitive",
            "program_indexed_program",
            "program_indexed_coherence_direct_tm",
            "program_indexed_semantic_iff",
            "program_indexed_composed_program",
            "program_indexed_composed_semantic_iff",
            "gadget_reference_audit",
            "gadget_normalization_audit",
            "gadget_executable",
            "gadget_parameter_audit",
            "gadget_semantic_forward",
            "gadget_semantic_reverse",
            "gadget_direct_tm",
            "gadget_program",
            "gadget_composed_program",
            "gadget_composed_semantic_iff",
            "parameter_normalization",
            "reduction_primitive",
            "gadget_definitions",
            "output_wellformed",
            "polynomial_bound",
            "program_direct_tm_coherence",
            "certified_reduction",
        }:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                f"unsupported v2 obligation capability: {self.capability}",
            )
        if not self.exact_type.strip() or len(self.exact_type) > 12_000:
            _v2_fail("candidate_exact_type_mismatch", "v2 obligation exact type is invalid")
        if len(set(self.depends_on)) != len(self.depends_on):
            _v2_fail("candidate_dependency_stale", "v2 obligation repeats a dependency")
        _v2_require_public_text(self.declaration, label="editable declaration")
        _v2_require_public_text(self.exact_type, label="obligation exact type")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {
            "node_id": self.node_id,
            "declaration": self.declaration,
            "capability": self.capability,
            "exact_type": self.exact_type,
            "depends_on": list(self.depends_on),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringObligationV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "gap node must be an object")
        _v2_exact_keys(
            value,
            {"node_id", "declaration", "capability", "exact_type", "depends_on"},
            label="gap node",
        )
        dependencies = value["depends_on"]
        if not isinstance(dependencies, list) or not all(
            isinstance(dependency, str) for dependency in dependencies
        ):
            _v2_fail("candidate_dependency_stale", "gap dependencies must be strings")
        for key in ("node_id", "declaration", "capability", "exact_type"):
            if not isinstance(value[key], str):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"gap field {key} is invalid")
        obligation = cls(
            node_id=value["node_id"],
            declaration=value["declaration"],
            capability=value["capability"],
            exact_type=value["exact_type"],
            depends_on=tuple(dependencies),
        )
        obligation.validate()
        return obligation


@dataclass(frozen=True)
class NPHardAuthoringTaskV2:
    request_id: str
    task_class: str
    source_problem: NPHardAuthoringEndpointV2
    target_problem: NPHardAuthoringEndpointV2
    candidate_module: str
    final_candidate_declaration: str
    final_exact_type: str
    gap_nodes: tuple[NPHardAuthoringObligationV2, ...]
    editable_declarations: tuple[str, ...]
    allowed_imports: tuple[str, ...]
    allowed_primitives: tuple[str, ...]
    allowed_primitive_layers: tuple[tuple[str, tuple[str, ...]], ...]
    allowed_primitive_exact_types: tuple[tuple[str, str], ...]
    forbidden_axioms: tuple[str, ...]
    dependency_hashes: tuple[tuple[str, str], ...]
    public_source_files: tuple[str, ...]
    observed_capability_terms: tuple[tuple[str, str], ...]
    observed_capability_exact_types: tuple[tuple[str, str], ...]
    terminal_node_id: str
    final_program_node_id: str | None
    composition_intermediate: NPHardAuthoringEndpointV2 | None
    composition_successor_module: str | None
    attempt_budget: int
    timeout_seconds: int
    max_output_tokens: int
    composition_successor_source: str | None = None
    composition_successor_target: str | None = None
    composition_admission_observation: tuple[tuple[str, str], ...] | None = None
    composition_successor_observation: tuple[tuple[str, str], ...] | None = None
    required_direction: str = NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2
    schema_version: str = NP_HARD_AUTHORING_TASK_SCHEMA_V2

    @property
    def dependency_fingerprint(self) -> str:
        return sha256_id(dict(self.dependency_hashes))

    def _content_payload(self) -> dict[str, Any]:
        payload = {
            "schema_version": self.schema_version,
            "task_class": self.task_class,
            "source_problem": {"module": self.source_problem.module, "term": self.source_problem.term},
            "target_problem": {"module": self.target_problem.module, "term": self.target_problem.term},
            "required_direction": self.required_direction,
            "candidate_module": self.candidate_module,
            "final_candidate_declaration": self.final_candidate_declaration,
            "final_exact_type": self.final_exact_type,
            "gap_nodes": [node.to_dict() for node in self.gap_nodes],
            "editable_declarations": list(self.editable_declarations),
            "allowed_imports": list(self.allowed_imports),
            "allowed_primitives": list(self.allowed_primitives),
            "allowed_primitive_layers": {
                layer: list(primitives)
                for layer, primitives in self.allowed_primitive_layers
            },
            "allowed_primitive_exact_types": dict(
                self.allowed_primitive_exact_types
            ),
            "forbidden_axioms": list(self.forbidden_axioms),
            "dependency_hashes": dict(self.dependency_hashes),
            "public_source_files": list(self.public_source_files),
            "attempt_budget": self.attempt_budget,
            "timeout_seconds": self.timeout_seconds,
            "max_output_tokens": self.max_output_tokens,
        }
        if self.task_class in _NP_HARD_TYPED_TASK_CLASSES_V2:
            payload.update(
                {
                    "observed_capability_terms": dict(
                        self.observed_capability_terms
                    ),
                    "terminal_node_id": self.terminal_node_id,
                    "final_program_node_id": self.final_program_node_id,
                }
            )
        if self.task_class in {
            "typed_tmkarp_admission_dag",
            "typed_tmkarp_dependent_composition_dag",
            "typed_program_indexed_admission_dag",
            "typed_tmkarp_program_indexed_composition_dag",
            "typed_gadget_indexed_admission_dag",
        }:
            payload["observed_capability_exact_types"] = dict(
                self.observed_capability_exact_types
            )
        if self.task_class in {
            "typed_tmkarp_dependent_composition_dag",
            "typed_tmkarp_program_indexed_composition_dag",
            "typed_gadget_indexed_admission_dag",
        }:
            payload["composition_intermediate"] = (
                self.composition_intermediate.to_dict()
                if self.composition_intermediate is not None
                else None
            )
            if self.task_class != "typed_gadget_indexed_admission_dag":
                payload["composition_successor_module"] = (
                    self.composition_successor_module
                )
                if self.composition_successor_source is not None:
                    payload["composition_successor_source"] = (
                        self.composition_successor_source
                    )
                    payload["composition_successor_target"] = (
                        self.composition_successor_target
                    )
                    payload["composition_admission_observation"] = dict(
                        self.composition_admission_observation or ()
                    )
                    payload["composition_successor_observation"] = dict(
                        self.composition_successor_observation or ()
                    )
        return payload

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content_payload())

    def validate(self) -> None:
        if self.schema_version != NP_HARD_AUTHORING_TASK_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task schema")
        _v2_require_hash(self.request_id, label="request_id")
        if self.task_class not in NP_HARD_AUTHORING_TASK_CLASSES_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task class")
        self.source_problem.validate()
        self.target_problem.validate()
        if self.source_problem.term == self.target_problem.term:
            _v2_fail("candidate_wrong_endpoint", "v2 source and target endpoints are identical")
        if (self.composition_successor_source is None) != (
            self.composition_successor_target is None
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "canonical successor source/target must be supplied together",
            )
        if (self.composition_admission_observation is None) != (
            self.composition_successor_observation is None
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "admission/successor observer records must be supplied together",
            )
        if self.composition_successor_source is not None:
            try:
                validate_declaration_name(
                    self.composition_successor_source,
                    label="canonical composition successor source",
                )
                validate_declaration_name(
                    self.composition_successor_target or "",
                    label="canonical composition successor target",
                )
            except ValueError as error:
                _v2_fail("candidate_wrong_endpoint", str(error))
        if self.task_class in {
            "typed_tmkarp_dependent_composition_dag",
            "typed_tmkarp_program_indexed_composition_dag",
            "typed_gadget_indexed_admission_dag",
        }:
            if self.composition_intermediate is None:
                _v2_fail(
                    "candidate_wrong_endpoint",
                    "typed three-endpoint task lacks its exact intermediate endpoint",
                )
            self.composition_intermediate.validate()
            if len(
                {
                    self.source_problem.term,
                    self.composition_intermediate.term,
                    self.target_problem.term,
                }
            ) != 3:
                _v2_fail(
                    "candidate_wrong_endpoint",
                    "dependent TMKarp composition collapsed an endpoint",
                )
            if (
                self.task_class != "typed_gadget_indexed_admission_dag"
                and self.composition_successor_module is None
            ):
                _v2_fail(
                    "authoring_catalog_dependency_stale",
                    "dependent TMKarp composition lacks its successor module",
                )
            if self.composition_successor_module is not None:
                try:
                    validate_module_name(self.composition_successor_module)
                except ValueError as error:
                    _v2_fail("authoring_catalog_dependency_stale", str(error))
            if (
                self.task_class == "typed_gadget_indexed_admission_dag"
                and self.composition_successor_module is not None
            ):
                _v2_fail(
                    "invalid_np_hard_authoring_v2_schema",
                    "gadget-indexed task carries an unrelated successor module",
                )
            if (
                self.task_class != "typed_tmkarp_dependent_composition_dag"
                and self.composition_successor_source is not None
            ):
                _v2_fail(
                    "invalid_np_hard_authoring_v2_schema",
                    "only successor-only dependent composition carries canonical successor endpoints",
                )
            if (
                self.task_class != "typed_tmkarp_dependent_composition_dag"
                and self.composition_admission_observation is not None
            ):
                _v2_fail(
                    "invalid_np_hard_authoring_v2_schema",
                    "only successor-only dependent composition carries observer chain records",
                )
        elif (
            self.composition_intermediate is not None
            or self.composition_successor_module is not None
            or self.composition_successor_source is not None
            or self.composition_successor_target is not None
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "non-composition task carries an intermediate endpoint",
            )
        if self.required_direction != NP_HARD_AUTHORING_REQUIRED_DIRECTION_V2:
            _v2_fail("candidate_wrong_direction", "v2 task changed source-to-target direction")
        try:
            validate_module_name(self.candidate_module)
            validate_declaration_name(
                self.final_candidate_declaration, label="v2 final candidate declaration"
            )
        except ValueError as error:
            _v2_fail("candidate_outside_edit_boundary", str(error))
        if not self.final_candidate_declaration.startswith(self.candidate_module + "."):
            _v2_fail(
                "candidate_outside_edit_boundary",
                "final declaration escaped the generated candidate module",
            )
        expected_final_type = (
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{self.source_problem.term} {self.target_problem.term}"
        )
        if self.final_exact_type != expected_final_type:
            _v2_fail("candidate_exact_type_mismatch", "v2 final CertifiedReduction type drifted")
        if not self.gap_nodes:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task has no gap nodes")
        node_ids: set[str] = set()
        node_declarations: list[str] = []
        for node in self.gap_nodes:
            node.validate()
            if node.node_id in node_ids:
                _v2_fail("candidate_dependency_stale", "v2 task repeats a gap node")
            if any(dependency not in node_ids for dependency in node.depends_on):
                _v2_fail("candidate_dependency_stale", "v2 gap DAG is not topologically ordered")
            if not node.declaration.startswith(self.candidate_module + "."):
                _v2_fail(
                    "candidate_outside_edit_boundary",
                    "editable declaration escaped the generated candidate module",
                )
            node_ids.add(node.node_id)
            node_declarations.append(node.declaration)
        expected_staged_motif = _NP_HARD_EXACT_STAGED_TASK_MOTIFS_V2.get(
            self.task_class
        )
        if expected_staged_motif is not None:
            observed_staged_motif = tuple(
                (node.node_id, node.capability, node.depends_on)
                for node in self.gap_nodes
            )
            allowed_staged_motifs = (
                (
                    expected_staged_motif,
                    _NP_HARD_POSITIVE_NAE3_WHOLE_REDUCTION_MOTIF_V2,
                )
                if self.task_class == "whole_reduction_synthesis"
                else (expected_staged_motif,)
            )
            if observed_staged_motif not in allowed_staged_motifs:
                _v2_fail(
                    "candidate_dependency_stale",
                    "staged task node order/capability/dependency motif drifted",
                )
            expected_terminal, expected_program = (
                _NP_HARD_EXACT_STAGED_TASK_BOUNDARIES_V2[self.task_class]
            )
            if (
                self.terminal_node_id != expected_terminal
                or self.final_program_node_id != expected_program
            ):
                _v2_fail(
                    "candidate_dependency_stale",
                    "staged task terminal/final-program boundary drifted",
                )
        if self.terminal_node_id not in node_ids:
            _v2_fail(
                "candidate_dependency_stale",
                "v2 terminal node is absent from the exact gap DAG",
            )
        depended_on = {
            dependency for node in self.gap_nodes for dependency in node.depends_on
        }
        sink_nodes = node_ids - depended_on
        if sink_nodes != {self.terminal_node_id}:
            _v2_fail(
                "candidate_dependency_stale",
                "v2 gap DAG must have one explicit terminal node",
            )
        terminal = next(
            node for node in self.gap_nodes if node.node_id == self.terminal_node_id
        )
        if terminal.capability not in {
            "semantic_proof",
            "semantic_iff",
            "tmkarp_semantic_iff",
            "dependent_composed_semantic_iff",
            "program_indexed_semantic_iff",
            "program_indexed_composed_semantic_iff",
            "gadget_composed_semantic_iff",
            "certified_reduction",
        }:
            _v2_fail(
                "candidate_dependency_stale",
                "v2 terminal node is not a semantic certificate",
            )
        if self.final_program_node_id is not None:
            if self.final_program_node_id not in node_ids:
                _v2_fail(
                    "candidate_dependency_stale",
                    "v2 final program node is absent from the exact gap DAG",
                )
            program_node = next(
                node
                for node in self.gap_nodes
                if node.node_id == self.final_program_node_id
            )
            if program_node.capability not in {
                "poly_program",
                "representation_adapter",
                "tmkarp_program",
                "dependent_composed_program",
                "program_indexed_program",
                "program_indexed_composed_program",
                "gadget_program",
                "gadget_composed_program",
            }:
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "v2 final program node does not produce a typed program",
                )
        expected_program_node = {
            "semantic_proof": None,
            "program_composition": "composed-program",
            "program_synthesis": "poly-program",
            "whole_reduction_synthesis": "poly-program",
            "typed_capability_dag": "representation-adapter",
            "typed_tmkarp_admission_dag": "tmkarp-program",
            "typed_tmkarp_dependent_composition_dag": "composed-program",
            "typed_program_indexed_admission_dag": "program",
            "typed_tmkarp_program_indexed_composition_dag": "composed-program",
            "typed_gadget_indexed_admission_dag": "gadget-composed-program",
            "typed_exact_edge_construction_dag": "poly-program",
        }[self.task_class]
        if self.final_program_node_id != expected_program_node:
            _v2_fail(
                "candidate_dependency_stale",
                "v2 final program node differs from its task-class contract",
            )
        if self.task_class == "typed_capability_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "typed capability DAG lacks its explicit program or semantic terminal",
            )
        if self.task_class == "typed_tmkarp_admission_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "tmkarp_semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "typed TMKarp admission DAG lacks its program or semantic terminal",
            )
        if self.task_class == "typed_tmkarp_dependent_composition_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "dependent_composed_semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "dependent TMKarp composition DAG lacks its composed program or semantic terminal",
            )
        if self.task_class == "typed_program_indexed_admission_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "program_indexed_semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "program-indexed admission DAG lacks its explicit program or semantic terminal",
            )
        if self.task_class == "typed_tmkarp_program_indexed_composition_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "program_indexed_composed_semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "TMKarp/program-indexed composition DAG lacks its final program or semantic terminal",
            )
        if self.task_class == "typed_gadget_indexed_admission_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "gadget_composed_semantic_iff"
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "gadget-indexed admission DAG lacks its final program or semantic terminal",
            )
        if self.task_class == "typed_exact_edge_construction_dag" and (
            self.final_program_node_id is None
            or terminal.capability != "certified_reduction"
            or self.observed_capability_terms
            or self.observed_capability_exact_types
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "exact-edge construction DAG lacks its exact certified-reduction terminal, "
                "its poly-program, or carries observer material from a different task family",
            )
        if self.task_class == "whole_reduction_synthesis" and (
            self.final_program_node_id is None
            or terminal.capability != "semantic_iff"
            or self.observed_capability_terms
            or self.observed_capability_exact_types
        ):
            _v2_fail(
                "candidate_dependency_stale",
                "whole-reduction synthesis lacks its semantic terminal/program or "
                "carries a preinstalled capability witness",
            )
        if tuple(node_declarations) != self.editable_declarations:
            _v2_fail(
                "candidate_outside_edit_boundary",
                "editable declaration allowlist differs from the exact gap declarations",
            )
        if len(set(self.allowed_imports)) != len(self.allowed_imports):
            _v2_fail("import_not_allowlisted", "v2 task repeats an allowed import")
        if self.target_problem.module not in self.allowed_imports:
            _v2_fail("import_not_allowlisted", "target input module is not allowlisted")
        for imported in self.allowed_imports:
            try:
                validate_module_name(imported)
            except ValueError as error:
                _v2_fail("import_not_allowlisted", str(error))
            _v2_require_public_text(imported, label="allowed import")
        if len(set(self.allowed_primitives)) != len(self.allowed_primitives):
            _v2_fail("fabricated_declaration_handle", "v2 primitive allowlist has duplicates")
        for primitive in self.allowed_primitives:
            try:
                validate_declaration_name(primitive, label="allowed primitive")
            except ValueError as error:
                _v2_fail("fabricated_declaration_handle", str(error))
            _v2_require_public_text(primitive, label="allowed primitive")
        primitive_layers = dict(self.allowed_primitive_layers)
        expected_layer_names = {"core", "construction", "direct_tm", "semantic"}
        if set(primitive_layers) != expected_layer_names:
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 primitive layers must be exactly core/construction/direct_tm/semantic",
            )
        flattened_layers = tuple(
            primitive
            for layer in ("core", "construction", "direct_tm", "semantic")
            for primitive in primitive_layers[layer]
        )
        if len(set(flattened_layers)) != len(flattened_layers):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 primitive layers overlap",
            )
        if set(flattened_layers) != set(self.allowed_primitives):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 primitive layers do not partition the immutable allowlist",
            )
        for layer, primitives in self.allowed_primitive_layers:
            _v2_require_public_text(layer, label="primitive layer")
            for primitive in primitives:
                _v2_require_public_text(
                    primitive, label=f"allowed primitive in {layer}"
                )
        primitive_exact_types = dict(self.allowed_primitive_exact_types)
        if len(primitive_exact_types) != len(self.allowed_primitive_exact_types):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 allowed primitive exact-type map has duplicates",
            )
        if primitive_exact_types and set(primitive_exact_types) != set(
            self.allowed_primitives
        ):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 allowed primitive exact types do not cover the immutable allowlist",
            )
        for primitive, exact_type in self.allowed_primitive_exact_types:
            _v2_require_public_text(primitive, label="typed allowed primitive")
            _v2_require_public_text(
                exact_type, label=f"allowed primitive exact type {primitive}"
            )
        if not self.forbidden_axioms or not {"sorryAx", "axiom", "unsafe"}.issubset(
            set(self.forbidden_axioms)
        ):
            _v2_fail("candidate_nonstandard_axiom", "v2 forbidden-axiom policy is incomplete")
        if len(set(self.forbidden_axioms)) != len(self.forbidden_axioms):
            _v2_fail("candidate_nonstandard_axiom", "v2 forbidden-axiom list has duplicates")
        if not self.dependency_hashes or len(dict(self.dependency_hashes)) != len(
            self.dependency_hashes
        ):
            _v2_fail("candidate_dependency_stale", "v2 dependency map is empty or duplicated")
        for name, digest in self.dependency_hashes:
            if not name:
                _v2_fail("candidate_dependency_stale", "v2 dependency name is empty")
            _v2_require_public_text(name, label="dependency name")
            _v2_require_hash(digest, label=f"dependency {name}")
        if not self.public_source_files or len(set(self.public_source_files)) != len(
            self.public_source_files
        ):
            _v2_fail("candidate_dependency_stale", "v2 public source list is empty or duplicated")
        for source in self.public_source_files:
            path = Path(source)
            if path.is_absolute() or ".." in path.parts:
                _v2_fail("candidate_dependency_stale", "v2 public source path is unsafe")
            _v2_require_public_text(source, label="public source path")
        observed_terms = dict(self.observed_capability_terms)
        if len(observed_terms) != len(self.observed_capability_terms):
            _v2_fail(
                "fabricated_declaration_handle",
                "v2 observed capability term map has duplicate nodes",
            )
        if set(observed_terms) - node_ids:
            _v2_fail(
                "fabricated_declaration_handle",
                "v2 observed capability term references an unknown gap node",
            )
        for node_id, term in self.observed_capability_terms:
            if not _NP_HARD_V2_NODE_RE.fullmatch(node_id):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "v2 observed capability term has an invalid node ID",
                )
            if not term.strip() or len(term) > 12_000:
                _v2_fail(
                    "fabricated_declaration_handle",
                    "v2 observed capability term is invalid",
                )
            _v2_require_public_text(term, label="observed capability term")
            binding = f"content:observed-capability-term:{node_id}"
            if dict(self.dependency_hashes).get(binding) != sha256_id(term):
                _v2_fail(
                    "candidate_dependency_stale",
                    "v2 observed capability term hash is absent or stale",
                )
        observed_exact_types = dict(self.observed_capability_exact_types)
        if len(observed_exact_types) != len(self.observed_capability_exact_types):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 observed capability exact-type map has duplicate nodes",
            )
        if set(observed_exact_types) - node_ids:
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 observed capability exact type references an unknown gap node",
            )
        for node_id, exact_type in self.observed_capability_exact_types:
            if not _NP_HARD_V2_NODE_RE.fullmatch(node_id):
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "v2 observed capability exact type has an invalid node ID",
                )
            if not exact_type.strip() or len(exact_type) > 12_000:
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "v2 observed capability exact type is invalid",
                )
            _v2_require_public_text(
                exact_type, label="observed capability exact type"
            )
            binding = f"content:observed-capability-exact-type:{node_id}"
            if dict(self.dependency_hashes).get(binding) != sha256_id(exact_type):
                _v2_fail(
                    "candidate_dependency_stale",
                    "v2 observed capability exact-type hash is absent or stale",
                )
        if self.task_class == "typed_capability_dag" and set(observed_terms) != {
            self.final_program_node_id
        }:
            _v2_fail(
                "fabricated_declaration_handle",
                "typed capability DAG must bind exactly its final program witness",
            )
        if self.task_class == "typed_capability_dag":
            assert self.final_program_node_id is not None
            witness = observed_terms[self.final_program_node_id]
            if (
                any(
                    token not in witness
                    for token in ("PolyProg.const", "PolyProg.id", "false")
                )
                or not any(token in witness for token in ("PolyProg.pair", ").pair", ".pair ("))
                or "PolyProg.snd" in witness
            ):
                _v2_fail(
                    "candidate_wrong_direction",
                    "typed capability witness is not the forward product adapter",
                )
        if self.task_class in {
            "typed_tmkarp_admission_dag",
            "typed_tmkarp_dependent_composition_dag",
            "typed_tmkarp_program_indexed_composition_dag",
        }:
            if self.task_class == "typed_tmkarp_admission_dag":
                expected_observed_nodes = {"tmkarp-primitive"}
            elif self.task_class == "typed_tmkarp_dependent_composition_dag":
                expected_observed_nodes = {"tmkarp-primitive", "composed-program"}
            else:
                expected_observed_nodes = {"tmkarp-primitive", "program-executable"}
            if (
                set(observed_terms) != expected_observed_nodes
                or set(observed_exact_types) != expected_observed_nodes
            ):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "typed TMKarp DAG does not bind its exact public witness/type nodes",
                )
            witness = observed_terms["tmkarp-primitive"]
            exact_type = observed_exact_types["tmkarp-primitive"]
            try:
                validate_declaration_name(witness, label="typed TMKarp witness")
            except ValueError as error:
                _v2_fail("fabricated_declaration_handle", str(error))
            if witness.startswith(_NP_HARD_TMKARP_ADMISSION_MODULE + "."):
                admission_module = _NP_HARD_TMKARP_ADMISSION_MODULE
            elif (
                self.task_class == "typed_tmkarp_dependent_composition_dag"
                and witness.startswith(
                    _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE + "."
                )
            ):
                admission_module = (
                    _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
                )
            else:
                _v2_fail(
                    "fabricated_declaration_handle",
                    "typed TMKarp witness escaped its closed public admission authority",
                )
            if admission_module not in self.allowed_imports:
                _v2_fail(
                    "import_not_allowlisted",
                    "typed TMKarp admission module is not allowlisted",
                )
            if self.task_class == "typed_tmkarp_dependent_composition_dag":
                assert self.composition_intermediate is not None
                assert self.composition_successor_module is not None
                if not _staged_authoring_surface_is_exact_v2(
                    allowed_imports=self.allowed_imports,
                    public_source_files=self.public_source_files,
                    dependency_hashes=self.dependency_hashes,
                    source_module=self.source_problem.module,
                    target_module=self.target_problem.module,
                    intermediate_module=self.composition_intermediate.module,
                    authority_modules=(
                        self.composition_successor_module,
                        admission_module,
                    ),
                ):
                    _v2_fail(
                        "candidate_outside_edit_boundary",
                        "dependent TMKarp task surface differs from its exact endpoint/authority closure",
                    )
            if (
                f"module:{admission_module}"
                not in dict(self.dependency_hashes)
            ):
                _v2_fail(
                    "candidate_dependency_stale",
                    "typed TMKarp admission module hash is absent",
                )
            source_backend = (
                self.source_problem.term + ".toEncodedDecisionProblem"
            )
            admission_target = (
                self.target_problem
                if self.task_class == "typed_tmkarp_admission_dag"
                else self.composition_intermediate
            )
            assert admission_target is not None
            target_backend = (
                admission_target.term + ".toEncodedDecisionProblem"
            )
            if _exact_tmkarp_reduction_endpoints_v2(exact_type) != (
                source_backend,
                target_backend,
            ):
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "typed TMKarp witness exact type substitutes or reverses its task endpoints",
                )
            if self.task_class == "typed_tmkarp_dependent_composition_dag":
                successor = observed_terms["composed-program"]
                successor_exact_type = observed_exact_types["composed-program"]
                try:
                    validate_declaration_name(
                        successor, label="typed certified successor witness"
                    )
                except ValueError as error:
                    _v2_fail("fabricated_declaration_handle", str(error))
                assert self.composition_successor_module is not None
                if not _certified_successor_witness_owned_by_module_v2(
                    witness=successor,
                    successor_module=self.composition_successor_module,
                ):
                    _v2_fail(
                        "fabricated_declaration_handle",
                        "certified successor witness is not owned by its observer-bound Lean module",
                    )
                dependencies = dict(self.dependency_hashes)
                for binding in (
                    "content:lean-certified-successor",
                    "content:lean-typed-capability-chain",
                    f"module:{admission_target.module}",
                    f"module:{self.composition_successor_module}",
                    "content:observed-capability-module:composed-program",
                ):
                    if binding not in dependencies:
                        _v2_fail(
                            "candidate_dependency_stale",
                            "dependent TMKarp composition lacks a content-addressed successor binding",
                        )
                if dependencies[
                    "content:observed-capability-module:composed-program"
                ] != sha256_id(self.composition_successor_module):
                    _v2_fail(
                        "candidate_dependency_stale",
                        "dependent TMKarp successor module binding is stale",
                    )
                if admission_target.module not in self.allowed_imports:
                    _v2_fail(
                        "import_not_allowlisted",
                        "dependent TMKarp intermediate module is not allowlisted",
                    )
                if self.composition_successor_module not in self.allowed_imports:
                    _v2_fail(
                        "import_not_allowlisted",
                        "dependent TMKarp successor module is not allowlisted",
                    )
                if (
                    admission_module
                    == _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
                ):
                    admission_observation = (
                        _observer_capability_record_payload_v2(
                            self.composition_admission_observation
                        )
                    )
                    successor_observation = (
                        _observer_capability_record_payload_v2(
                            self.composition_successor_observation
                        )
                    )
                    if admission_observation is None or successor_observation is None:
                        _v2_fail(
                            "candidate_dependency_stale",
                            "successor-only chain lacks complete Lean observer records",
                        )
                    if (
                        self.composition_successor_source,
                        self.composition_successor_target,
                    ) != (admission_target.term, self.target_problem.term):
                        _v2_fail(
                            "candidate_wrong_endpoint",
                            "successor-only chain canonical successor endpoints differ from its task endpoints",
                        )
                    if _exact_certified_reduction_endpoints_v2(
                        successor_exact_type
                    ) != (
                        self.composition_successor_source,
                        self.composition_successor_target,
                    ):
                        _v2_fail(
                            "candidate_exact_type_mismatch",
                            "successor-only chain does not bind one canonical ordered successor type",
                        )
                    expected_admission_record = {
                        "capability_kind": "forward_successor_only_tmkarp_admission",
                        "source": self.source_problem.term,
                        "target": admission_target.term,
                        "witness": witness,
                        "exact_type": exact_type,
                        "module": admission_module,
                        "authority": "lean_exact_successor_only_tmkarp_shared_source",
                    }
                    expected_successor_record = {
                        "capability_kind": "forward_certified_successor",
                        "source": self.composition_successor_source,
                        "target": self.composition_successor_target,
                        "witness": successor,
                        "exact_type": successor_exact_type,
                        "module": self.composition_successor_module,
                        "authority": "lean_registry_exact_certified_successor",
                    }
                    if any(
                        admission_observation[key] != value
                        for key, value in expected_admission_record.items()
                    ) or any(
                        successor_observation[key] != value
                        for key, value in expected_successor_record.items()
                    ):
                        _v2_fail(
                            "candidate_dependency_stale",
                            "successor-only task facts differ from their Lean observer rows",
                        )
                    if (
                        admission_observation["target_node"]
                        != successor_observation["source_node"]
                        or admission_observation["registry_fingerprint"]
                        != successor_observation["registry_fingerprint"]
                    ):
                        _v2_fail(
                            "candidate_wrong_endpoint",
                            "successor-only observer rows do not form one exact endpoint chain",
                        )
                    if dependencies.get(
                        "content:lean-registry-fingerprint"
                    ) != sha256_id(admission_observation["registry_fingerprint"]):
                        _v2_fail(
                            "candidate_dependency_stale",
                            "successor-only observer fingerprint binding is stale",
                        )
                    expected_chain = _successor_only_observer_chain_payload_v2(
                        admission=admission_observation,
                        successor=successor_observation,
                        canonical_successor_source=(
                            self.composition_successor_source
                        ),
                        canonical_successor_target=(
                            self.composition_successor_target
                        ),
                    )
                    for binding, payload in (
                        (
                            "content:lean-successor-only-tmkarp-admission",
                            admission_observation,
                        ),
                        (
                            "content:lean-certified-successor",
                            successor_observation,
                        ),
                        (
                            "content:lean-typed-capability-chain",
                            expected_chain,
                        ),
                    ):
                        if dependencies.get(binding) != sha256_id(payload):
                            _v2_fail(
                                "candidate_dependency_stale",
                                "successor-only observer content binding is stale",
                            )
                    for binding, endpoint in (
                        (
                            "content:observed-composition-successor-source",
                            self.composition_successor_source,
                        ),
                        (
                            "content:observed-composition-successor-target",
                            self.composition_successor_target,
                        ),
                    ):
                        if dependencies.get(binding) != sha256_id(endpoint):
                            _v2_fail(
                                "candidate_dependency_stale",
                                "successor-only canonical endpoint binding is stale",
                            )
                else:
                    if (
                        self.composition_successor_source is not None
                        or self.composition_successor_target is not None
                        or self.composition_admission_observation is not None
                        or self.composition_successor_observation is not None
                    ):
                        _v2_fail(
                            "invalid_np_hard_authoring_v2_schema",
                            "legacy dependent task unexpectedly carries successor-only endpoint bindings",
                        )
                    normalized_successor_endpoints = (
                        _normalized_certified_successor_exact_endpoints_v2(
                            exact_type=successor_exact_type,
                            witness=successor,
                            successor_module=self.composition_successor_module,
                            expected_source=admission_target.term,
                            expected_target=self.target_problem.term,
                        )
                    )
                    if normalized_successor_endpoints != (
                        admission_target.term,
                        self.target_problem.term,
                    ):
                        _v2_fail(
                            "candidate_exact_type_mismatch",
                            "certified successor exact type is not the ordered intermediate-to-target reduction",
                        )
        if self.task_class in {
            "typed_program_indexed_admission_dag",
            "typed_tmkarp_program_indexed_composition_dag",
        }:
            expected_observed_nodes = {"program-executable"}
            if self.task_class == "typed_program_indexed_admission_dag" and (
                set(observed_terms) != expected_observed_nodes
                or set(observed_exact_types) != expected_observed_nodes
            ):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "program-indexed DAG does not bind its one exact public packet/type node",
                )
            witness = observed_terms["program-executable"]
            exact_type = observed_exact_types["program-executable"]
            try:
                validate_declaration_name(
                    witness, label="typed program-indexed packet witness"
                )
            except ValueError as error:
                _v2_fail("fabricated_declaration_handle", str(error))
            if not witness.startswith(
                _NP_HARD_PROGRAM_INDEXED_ADMISSION_MODULE + "."
            ):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "program-indexed witness escaped the closed public packet module",
                )
            if (
                _NP_HARD_PROGRAM_INDEXED_ADMISSION_MODULE
                not in self.allowed_imports
            ):
                _v2_fail(
                    "import_not_allowlisted",
                    "program-indexed packet module is not allowlisted",
                )
            dependencies = dict(self.dependency_hashes)
            if (
                f"module:{_NP_HARD_PROGRAM_INDEXED_ADMISSION_MODULE}"
                not in dependencies
            ):
                _v2_fail(
                    "candidate_dependency_stale",
                    "program-indexed packet module hash is absent",
                )
            packet_source = (
                self.source_problem
                if self.task_class == "typed_program_indexed_admission_dag"
                else self.composition_intermediate
            )
            assert packet_source is not None
            source_index = exact_type.find(packet_source.term)
            target_index = exact_type.rfind(self.target_problem.term)
            if (
                "ProgramIndexedAdmissionPacket" not in exact_type
                or source_index < 0
                or target_index < 0
                or source_index >= target_index
            ):
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "program-indexed packet exact type substitutes or reverses its task endpoints",
                )
            if self.task_class == "typed_tmkarp_program_indexed_composition_dag":
                for binding in (
                    "content:lean-program-indexed-packet",
                    "content:lean-tmkarp-program-indexed-chain",
                    f"module:{packet_source.module}",
                    f"module:{self.composition_successor_module}",
                ):
                    if binding not in dependencies:
                        _v2_fail(
                            "candidate_dependency_stale",
                            "TMKarp/program-indexed composition lacks a content-addressed packet binding",
                        )
                if packet_source.module not in self.allowed_imports:
                    _v2_fail(
                        "import_not_allowlisted",
                        "TMKarp/program-indexed intermediate module is not allowlisted",
                    )
        if self.task_class == "typed_gadget_indexed_admission_dag":
            dependencies = dict(self.dependency_hashes)
            assert self.composition_intermediate is not None
            if not _staged_authoring_surface_is_exact_v2(
                allowed_imports=self.allowed_imports,
                public_source_files=self.public_source_files,
                dependency_hashes=self.dependency_hashes,
                source_module=self.source_problem.module,
                target_module=self.target_problem.module,
                intermediate_module=self.composition_intermediate.module,
                authority_modules=(
                    _NP_HARD_GADGET_INDEXED_ADMISSION_MODULE,
                ),
            ):
                _v2_fail(
                    "candidate_outside_edit_boundary",
                    "gadget-indexed task surface differs from its exact endpoint/packet closure",
                )
            if (
                _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
                in self.allowed_imports
                or f"module:{_NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE}"
                in dependencies
                or any(
                    "SuccessorOnly" in value
                    or "SuccessorAuthoringSources" in value
                    for value in (
                        *self.allowed_imports,
                        *dependencies,
                        *self.public_source_files,
                    )
                )
            ):
                _v2_fail(
                    "candidate_outside_edit_boundary",
                    "gadget-indexed task exposes a successor-only shortcut authority",
                )
            expected_observed_nodes = {"gadget-reference-audit"}
            if (
                set(observed_terms) != expected_observed_nodes
                or set(observed_exact_types) != expected_observed_nodes
            ):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "gadget-indexed DAG does not bind its one exact public packet/type node",
                )
            witness = observed_terms["gadget-reference-audit"]
            exact_type = observed_exact_types["gadget-reference-audit"]
            try:
                validate_declaration_name(
                    witness, label="typed gadget-indexed packet witness"
                )
            except ValueError as error:
                _v2_fail("fabricated_declaration_handle", str(error))
            if not witness.startswith(
                _NP_HARD_GADGET_INDEXED_ADMISSION_MODULE + "."
            ):
                _v2_fail(
                    "fabricated_declaration_handle",
                    "gadget-indexed witness escaped the closed public packet module",
                )
            if (
                _NP_HARD_GADGET_INDEXED_ADMISSION_MODULE
                not in self.allowed_imports
            ):
                _v2_fail(
                    "import_not_allowlisted",
                    "gadget-indexed packet module is not allowlisted",
                )
            for binding in (
                f"module:{_NP_HARD_GADGET_INDEXED_ADMISSION_MODULE}",
                "content:lean-gadget-indexed-packet",
            ):
                if binding not in dependencies:
                    _v2_fail(
                        "candidate_dependency_stale",
                        "gadget-indexed packet lacks a content-addressed binding",
                    )
            if _exact_gadget_packet_endpoints_v2(exact_type) != (
                self.source_problem.term,
                self.composition_intermediate.term,
                self.target_problem.term,
            ):
                _v2_fail(
                    "candidate_exact_type_mismatch",
                    "gadget-indexed packet substitutes or reorders its three exact endpoints",
                )
        if not 1 <= self.attempt_budget <= 4:
            _v2_fail("authoring_gap_budget_exhausted", "v2 attempt budget is outside 1..4")
        if not 1 <= self.timeout_seconds <= 600:
            _v2_fail("authoring_gap_budget_exhausted", "v2 timeout is outside 1..600 seconds")
        if not 1 <= self.max_output_tokens <= FORMAL_MAX_TOKENS:
            _v2_fail("authoring_gap_budget_exhausted", "v2 output token budget is invalid")
        _v2_require_public_text(self.final_exact_type, label="final exact type")
        if self.request_id != self.computed_request_id:
            _v2_fail("candidate_dependency_stale", "v2 request ID does not bind its payload")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {"request_id": self.request_id, **self._content_payload()}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "NPHardAuthoringTaskV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task must be an object")
        legacy_expected = {
            "schema_version",
            "request_id",
            "task_class",
            "source_problem",
            "target_problem",
            "required_direction",
            "candidate_module",
            "final_candidate_declaration",
            "final_exact_type",
            "gap_nodes",
            "editable_declarations",
            "allowed_imports",
            "allowed_primitives",
            "allowed_primitive_layers",
            "allowed_primitive_exact_types",
            "forbidden_axioms",
            "dependency_hashes",
            "public_source_files",
            "attempt_budget",
            "timeout_seconds",
            "max_output_tokens",
        }
        typed_expected = legacy_expected | {
            "observed_capability_terms",
            "terminal_node_id",
            "final_program_node_id",
        }
        tmkarp_expected = typed_expected | {
            "observed_capability_exact_types",
        }
        dependent_composition_expected = tmkarp_expected | {
            "composition_intermediate",
            "composition_successor_module",
        }
        successor_bound_composition_expected = dependent_composition_expected | {
            "composition_successor_source",
            "composition_successor_target",
            "composition_admission_observation",
            "composition_successor_observation",
        }
        gadget_expected = tmkarp_expected | {"composition_intermediate"}
        task_class = value.get("task_class")
        if task_class == "typed_tmkarp_dependent_composition_dag":
            has_successor_source = "composition_successor_source" in value
            has_successor_target = "composition_successor_target" in value
            has_admission_observation = "composition_admission_observation" in value
            has_successor_observation = "composition_successor_observation" in value
            if (
                has_successor_source != has_successor_target
                or has_admission_observation != has_successor_observation
                or has_successor_source != has_admission_observation
            ):
                _v2_fail(
                    "invalid_np_hard_authoring_v2_schema",
                    "canonical successor fields and observer records must occur together",
                )
            expected = (
                successor_bound_composition_expected
                if has_successor_source
                else dependent_composition_expected
            )
        elif task_class == "typed_tmkarp_program_indexed_composition_dag":
            expected = dependent_composition_expected
        elif task_class == "typed_gadget_indexed_admission_dag":
            expected = gadget_expected
        elif task_class in {
            "typed_tmkarp_admission_dag",
            "typed_program_indexed_admission_dag",
        }:
            expected = tmkarp_expected
        elif task_class in {
            "whole_reduction_synthesis",
            "typed_capability_dag",
        }:
            expected = typed_expected
        else:
            expected = legacy_expected
        _v2_exact_keys(value, expected, label="v2 task")
        if value["schema_version"] != NP_HARD_AUTHORING_TASK_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task schema")
        gap_values = value["gap_nodes"]
        dependency_values = value["dependency_hashes"]
        primitive_exact_type_values = value["allowed_primitive_exact_types"]
        primitive_layer_values = value["allowed_primitive_layers"]
        sequence_fields = {
            "editable_declarations": value["editable_declarations"],
            "allowed_imports": value["allowed_imports"],
            "allowed_primitives": value["allowed_primitives"],
            "forbidden_axioms": value["forbidden_axioms"],
            "public_source_files": value["public_source_files"],
        }
        observed_term_values = value.get("observed_capability_terms", {})
        observed_exact_type_values = value.get(
            "observed_capability_exact_types", {}
        )
        if (
            not isinstance(gap_values, list)
            or not isinstance(dependency_values, Mapping)
            or not isinstance(primitive_exact_type_values, Mapping)
            or not isinstance(primitive_layer_values, Mapping)
            or not isinstance(observed_term_values, Mapping)
            or not isinstance(observed_exact_type_values, Mapping)
        ):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task collection fields are invalid")
        for label, items in sequence_fields.items():
            if not isinstance(items, list) or not all(isinstance(item, str) for item in items):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 field {label} is invalid")
        if not all(
            isinstance(layer, str)
            and isinstance(primitives, list)
            and all(isinstance(primitive, str) for primitive in primitives)
            for layer, primitives in primitive_layer_values.items()
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "v2 primitive layer map is invalid",
            )
        string_fields = (
            "request_id",
            "task_class",
            "required_direction",
            "candidate_module",
            "final_candidate_declaration",
            "final_exact_type",
        )
        if not all(isinstance(value[field], str) for field in string_fields):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task string field is invalid")
        if task_class in _NP_HARD_TYPED_TASK_CLASSES_V2 and not isinstance(
            value.get("terminal_node_id"), str
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "v2 terminal node field is invalid",
            )
        if value.get("final_program_node_id") is not None and not isinstance(
            value.get("final_program_node_id"), str
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "v2 final program node field is invalid",
            )
        composition_intermediate = (
            NPHardAuthoringEndpointV2.from_dict(value["composition_intermediate"])
            if task_class
            in {
                "typed_tmkarp_dependent_composition_dag",
                "typed_tmkarp_program_indexed_composition_dag",
                "typed_gadget_indexed_admission_dag",
            }
            else None
        )
        composition_successor_module = (
            value["composition_successor_module"]
            if task_class
            in {
                "typed_tmkarp_dependent_composition_dag",
                "typed_tmkarp_program_indexed_composition_dag",
            }
            and isinstance(value["composition_successor_module"], str)
            else None
        )
        composition_successor_source = (
            value["composition_successor_source"]
            if isinstance(value.get("composition_successor_source"), str)
            else None
        )
        composition_successor_target = (
            value["composition_successor_target"]
            if isinstance(value.get("composition_successor_target"), str)
            else None
        )
        admission_observation_value = value.get(
            "composition_admission_observation"
        )
        successor_observation_value = value.get(
            "composition_successor_observation"
        )
        if admission_observation_value is not None and not isinstance(
            admission_observation_value, Mapping
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "composition admission observation is not an object",
            )
        if successor_observation_value is not None and not isinstance(
            successor_observation_value, Mapping
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "composition successor observation is not an object",
            )
        composition_admission_observation = (
            tuple(sorted(admission_observation_value.items()))
            if isinstance(admission_observation_value, Mapping)
            and all(
                isinstance(key, str) and isinstance(item, str)
                for key, item in admission_observation_value.items()
            )
            else None
        )
        composition_successor_observation = (
            tuple(sorted(successor_observation_value.items()))
            if isinstance(successor_observation_value, Mapping)
            and all(
                isinstance(key, str) and isinstance(item, str)
                for key, item in successor_observation_value.items()
            )
            else None
        )
        if task_class in {
            "typed_tmkarp_dependent_composition_dag",
            "typed_tmkarp_program_indexed_composition_dag",
        } and (
            composition_successor_module is None
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "v2 successor module field is invalid",
            )
        if not all(isinstance(value[field], int) for field in (
            "attempt_budget", "timeout_seconds", "max_output_tokens"
        )):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 task budget field is invalid")
        if not all(isinstance(name, str) and isinstance(digest, str)
                   for name, digest in dependency_values.items()):
            _v2_fail("candidate_dependency_stale", "v2 dependency map is invalid")
        if not all(
            isinstance(name, str) and isinstance(exact_type, str)
            for name, exact_type in primitive_exact_type_values.items()
        ):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 allowed primitive exact-type map is invalid",
            )
        if not all(
            isinstance(node_id, str) and isinstance(term, str)
            for node_id, term in observed_term_values.items()
        ):
            _v2_fail(
                "fabricated_declaration_handle",
                "v2 observed capability term map is invalid",
            )
        if not all(
            isinstance(node_id, str) and isinstance(exact_type, str)
            for node_id, exact_type in observed_exact_type_values.items()
        ):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "v2 observed capability exact-type map is invalid",
            )
        gap_nodes = tuple(
            NPHardAuthoringObligationV2.from_dict(item) for item in gap_values
        )
        if task_class in _NP_HARD_TYPED_TASK_CLASSES_V2:
            terminal_node_id = value["terminal_node_id"]
            final_program_node_id = value["final_program_node_id"]
        else:
            legacy_node_ids = {node.node_id for node in gap_nodes}
            legacy_dependencies = {
                dependency for node in gap_nodes for dependency in node.depends_on
            }
            legacy_sinks = legacy_node_ids - legacy_dependencies
            terminal_node_id = (
                next(iter(legacy_sinks)) if len(legacy_sinks) == 1 else ""
            )
            final_program_node_id = {
                "semantic_proof": None,
                "program_composition": "composed-program",
                "program_synthesis": "poly-program",
                "whole_reduction_synthesis": "poly-program",
            }.get(str(task_class))
        task = cls(
            request_id=value["request_id"],
            task_class=value["task_class"],
            source_problem=NPHardAuthoringEndpointV2.from_dict(value["source_problem"]),
            target_problem=NPHardAuthoringEndpointV2.from_dict(value["target_problem"]),
            candidate_module=value["candidate_module"],
            final_candidate_declaration=value["final_candidate_declaration"],
            final_exact_type=value["final_exact_type"],
            gap_nodes=gap_nodes,
            editable_declarations=tuple(sequence_fields["editable_declarations"]),
            allowed_imports=tuple(sequence_fields["allowed_imports"]),
            allowed_primitives=tuple(sequence_fields["allowed_primitives"]),
            allowed_primitive_layers=tuple(
                (layer, tuple(primitives))
                for layer, primitives in sorted(primitive_layer_values.items())
            ),
            allowed_primitive_exact_types=tuple(
                sorted(primitive_exact_type_values.items())
            ),
            forbidden_axioms=tuple(sequence_fields["forbidden_axioms"]),
            dependency_hashes=tuple(sorted(dependency_values.items())),
            public_source_files=tuple(sequence_fields["public_source_files"]),
            observed_capability_terms=tuple(sorted(observed_term_values.items())),
            observed_capability_exact_types=tuple(
                sorted(observed_exact_type_values.items())
            ),
            terminal_node_id=terminal_node_id,
            final_program_node_id=final_program_node_id,
            composition_intermediate=composition_intermediate,
            composition_successor_module=composition_successor_module,
            attempt_budget=value["attempt_budget"],
            timeout_seconds=value["timeout_seconds"],
            max_output_tokens=value["max_output_tokens"],
            composition_successor_source=composition_successor_source,
            composition_successor_target=composition_successor_target,
            composition_admission_observation=composition_admission_observation,
            composition_successor_observation=composition_successor_observation,
            required_direction=value["required_direction"],
            schema_version=value["schema_version"],
        )
        task.validate()
        return task


def _successor_only_chain_probe_source_v2(
    task: NPHardAuthoringTaskV2,
) -> str:
    """Render the exact isolated Lean witness probe used by runtime/scorers."""

    observed_terms = dict(task.observed_capability_terms)
    admission_witness = observed_terms.get("tmkarp-primitive")
    successor_witness = observed_terms.get("composed-program")
    intermediate = task.composition_intermediate
    if (
        task.task_class != "typed_tmkarp_dependent_composition_dag"
        or intermediate is None
        or not isinstance(admission_witness, str)
        or not admission_witness.startswith(
            _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE + "."
        )
        or not isinstance(successor_witness, str)
    ):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only Lean probe requested for an incompatible task",
        )
    imports = "\n".join(f"import {module}" for module in task.allowed_imports)
    return f"""{imports}

open ComplexityReduction

#check (
  {admission_witness} :
    ComplexityReduction.TMKarpReduction
      {task.source_problem.term}.toEncodedDecisionProblem
      {intermediate.term}.toEncodedDecisionProblem)

#check (
  {successor_witness} :
    ComplexityReduction.Certificate.CertifiedReduction
      {intermediate.term}
      {task.target_problem.term})
"""


def validate_successor_only_authoritative_evidence_v2(
    *,
    task: NPHardAuthoringTaskV2,
    runtime: Mapping[str, Any],
    case_output: Path,
    require_files: bool,
) -> tuple[tuple[str, str], ...]:
    """Verify the pre-model Lean chain probe and its checkpoint bindings."""

    task.validate()
    observed_terms = dict(task.observed_capability_terms)
    admission_witness = observed_terms.get("tmkarp-primitive")
    if not (
        task.task_class == "typed_tmkarp_dependent_composition_dag"
        and isinstance(admission_witness, str)
        and admission_witness.startswith(
            _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE + "."
        )
    ):
        return ()
    evidence_rows = runtime.get("authoritative_evidence")
    if not isinstance(evidence_rows, list) or len(evidence_rows) != 1:
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only runtime lacks one authoritative Lean probe",
        )
    evidence = evidence_rows[0]
    if not isinstance(evidence, Mapping):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative evidence is not an object",
        )
    expected_keys = {
        "schema_version",
        "task_request_id",
        "source_file",
        "source_sha256",
        "source_file_sha256",
        "admission",
        "successor",
        "command",
        "command_certificate_sha256",
        "passed",
        "evidence_sha256",
        "evidence_file",
        "evidence_file_sha256",
    }
    if set(evidence) != expected_keys:
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative evidence shape drifted",
        )
    if (
        evidence.get("schema_version")
        != NP_HARD_SUCCESSOR_CHAIN_PROBE_SCHEMA_V1
        or evidence.get("task_request_id") != task.request_id
        or evidence.get("passed") is not True
    ):
        _v2_fail(
            "candidate_exact_type_mismatch",
            "successor-only authoritative probe did not pass for this task",
        )
    command = evidence.get("command")
    if not isinstance(command, Mapping):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative command is invalid",
        )
    command_keys = {
        "command",
        "exit_code",
        "stdout",
        "stderr",
        "duration_seconds",
        "timed_out",
    }
    if set(command) != command_keys:
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative command shape drifted",
        )
    command_line = command.get("command")
    source_file = evidence.get("source_file")
    if (
        not isinstance(source_file, str)
        or not isinstance(command_line, (list, tuple))
        or list(command_line) != ["lake", "env", "lean", source_file]
        or command.get("exit_code") != 0
        or command.get("timed_out") is not False
        or not isinstance(command.get("stdout"), str)
        or not isinstance(command.get("stderr"), str)
    ):
        _v2_fail(
            "candidate_exact_type_mismatch",
            "successor-only authoritative Lean command did not succeed exactly",
        )
    command_certificate = {
        "command": list(command_line),
        "exit_code": command["exit_code"],
        "stdout": command["stdout"],
        "stderr": command["stderr"],
        "timed_out": command["timed_out"],
    }
    if evidence.get("command_certificate_sha256") != sha256_id(
        command_certificate
    ):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative command certificate drifted",
        )
    stable_evidence = {
        key: evidence[key]
        for key in expected_keys
        - {
            "command",
            "evidence_sha256",
            "evidence_file",
            "evidence_file_sha256",
        }
    }
    if evidence.get("evidence_sha256") != sha256_id(stable_evidence):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative evidence hash drifted",
        )
    expected_source = _successor_only_chain_probe_source_v2(task)
    if evidence.get("source_sha256") != sha256_id(expected_source):
        _v2_fail(
            "candidate_exact_type_mismatch",
            "successor-only authoritative probe source changed its exact checks",
        )
    observed_exact_types = dict(task.observed_capability_exact_types)
    expected_admission = {
        "node_id": "tmkarp-primitive",
        "witness": admission_witness,
        "exact_type": observed_exact_types["tmkarp-primitive"].strip(),
        "module": _NP_HARD_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE,
    }
    assert task.composition_intermediate is not None
    expected_successor = {
        "node_id": "composed-program",
        "witness": observed_terms["composed-program"],
        "exact_type": observed_exact_types["composed-program"].strip(),
        "module": task.composition_successor_module,
        "intermediate_module": task.composition_intermediate.module,
        "intermediate_term": task.composition_intermediate.term,
    }
    if evidence.get("admission") != expected_admission or evidence.get(
        "successor"
    ) != expected_successor:
        _v2_fail(
            "candidate_wrong_endpoint",
            "successor-only authoritative evidence differs from the task DAG",
        )
    bindings = tuple(
        sorted(
            {
                "authoritative:successor-only-chain-probe-source": evidence[
                    "source_sha256"
                ],
                "authoritative:successor-only-chain-probe-command": evidence[
                    "command_certificate_sha256"
                ],
                "authoritative:successor-only-chain-probe-evidence": evidence[
                    "evidence_sha256"
                ],
            }.items()
        )
    )
    runtime_bindings = runtime.get("authoritative_dependency_bindings")
    if not isinstance(runtime_bindings, Mapping) or dict(bindings) != dict(
        runtime_bindings
    ):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative dependency bindings are missing",
        )
    commands = runtime.get("commands")
    if not isinstance(commands, list) or not any(
        isinstance(item, Mapping) and dict(item) == dict(command)
        for item in commands
    ):
        _v2_fail(
            "candidate_dependency_stale",
            "successor-only authoritative command is absent from runtime evidence",
        )
    if require_files:
        case_output = case_output.resolve()
        try:
            source_path = Path(source_file).resolve()
            evidence_path = Path(str(evidence.get("evidence_file"))).resolve()
            source_path.relative_to(case_output)
            evidence_path.relative_to(case_output)
        except (OSError, ValueError):
            _v2_fail(
                "cross_job_candidate",
                "successor-only authoritative evidence escaped its case output",
            )
        if (
            not source_path.is_file()
            or evidence.get("source_file_sha256")
            != _tagged_content_hash(sha256_file(source_path))
            or source_path.read_text(encoding="utf-8") != expected_source
            or not evidence_path.is_file()
            or evidence.get("evidence_file_sha256")
            != _tagged_content_hash(sha256_file(evidence_path))
        ):
            _v2_fail(
                "result_forgery",
                "successor-only authoritative source/evidence file drifted",
            )
        evidence_file_value = json.loads(
            evidence_path.read_text(encoding="utf-8")
        )
        expected_file_value = {
            key: evidence[key]
            for key in expected_keys
            - {"evidence_file", "evidence_file_sha256"}
        }
        if evidence_file_value != expected_file_value:
            _v2_fail(
                "result_forgery",
                "successor-only authoritative evidence file disagrees with runtime",
            )
        checkpoint_path_value = runtime.get("checkpoint_path")
        if not isinstance(checkpoint_path_value, str):
            _v2_fail(
                "checkpoint_tampered",
                "successor-only verified runtime lacks a checkpoint",
            )
        try:
            checkpoint_path = Path(checkpoint_path_value).resolve()
            checkpoint_path.relative_to(case_output)
        except (OSError, ValueError):
            _v2_fail(
                "cross_job_candidate",
                "successor-only checkpoint escaped its case output",
            )
        if (
            not checkpoint_path.is_file()
            or runtime.get("checkpoint_file_sha256")
            != _tagged_content_hash(sha256_file(checkpoint_path))
        ):
            _v2_fail(
                "checkpoint_tampered",
                "successor-only checkpoint file/hash drifted",
            )
        checkpoint = json.loads(checkpoint_path.read_text(encoding="utf-8"))
        snapshot = checkpoint.get("dependency_snapshot")
        if not isinstance(snapshot, Mapping) or any(
            snapshot.get(name) != digest for name, digest in bindings
        ):
            _v2_fail(
                "checkpoint_tampered",
                "successor-only checkpoint lacks authoritative probe bindings",
            )
    return bindings


def _v2_obligations(
    *,
    task_class: str,
    candidate_module: str,
    source_term: str,
    target_term: str,
    program_reference: str | None,
    program_packet_reference: str | None,
    mapping_invariant: str | None,
    representation_adapter_exact_type: str | None,
    composition_intermediate: NPHardAuthoringEndpointV2 | None,
    manifest_nodes: tuple[Mapping[str, Any], ...],
) -> tuple[NPHardAuthoringObligationV2, ...]:
    node_dependencies = {
        str(node["id"]): tuple(str(item) for item in node["depends_on"])
        for node in manifest_nodes
    }
    if task_class == "semantic_proof":
        if program_reference is None:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "proof-only task lacks a public program")
        obligations: list[NPHardAuthoringObligationV2] = []
        if mapping_invariant is not None:
            obligations.append(
                NPHardAuthoringObligationV2(
                    node_id="mapping-invariant",
                    declaration=f"{candidate_module}.mappingInvariantProof",
                    capability="mapping_invariant",
                    exact_type=(
                        f"∀ input : {source_term}.Instance, {mapping_invariant} input "
                        f"({program_reference}.run input)"
                    ),
                    depends_on=node_dependencies.get("mapping-invariant", ()),
                )
            )
            semantic_id = "semantic-iff"
        else:
            semantic_id = "semantic-proof"
        obligations.append(
            NPHardAuthoringObligationV2(
                node_id=semantic_id,
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program_reference}.run input)"
                ),
                depends_on=node_dependencies.get(semantic_id, ()),
            )
        )
    elif task_class == "program_composition":
        program = f"{candidate_module}.composedProgram"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="composed-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("composed-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-proof",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-proof", ()),
            ),
        ]
    elif task_class == "program_synthesis":
        executable = f"{candidate_module}.synthesizedExecutable"
        program = f"{candidate_module}.synthesizedProgram"
        if mapping_invariant is None:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "synthesis task lacks its invariant")
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="reduction-executable",
                declaration=executable,
                capability="reduction_executable",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("reduction-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="poly-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("poly-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence",
                declaration=f"{candidate_module}.programRunCoherence",
                capability="program_run_coherence",
                exact_type=f"∀ input : {source_term}.Instance, {program}.run input = {executable} input",
                depends_on=node_dependencies.get("program-run-coherence", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="mapping-invariant",
                declaration=f"{candidate_module}.mappingInvariantProof",
                capability="mapping_invariant",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {mapping_invariant} input "
                    f"({program}.run input)"
                ),
                depends_on=node_dependencies.get("mapping-invariant", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_proof",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
        ]
    elif task_class == "whole_reduction_synthesis" and tuple(
        str(node["id"]) for node in manifest_nodes
    ) == (
        "clause-constraint",
        "complement-constraint",
        "clause-gadget",
        "reference-executable",
        "reduction-executable",
        "clause-gadget-direct-tm",
        "reference-direct-tm",
        "direct-tm",
        "reduction-primitive",
        "poly-program",
        "program-run-coherence",
        "reference-semantic-forward",
        "reference-semantic-reverse",
        "semantic-forward",
        "semantic-reverse",
        "semantic-iff",
    ):
        target_namespace = target_term.rsplit(".", 1)[0]
        target_gamma = f"{target_namespace}.gamma"
        clause_constraint = f"{candidate_module}.clauseConstraint"
        complement_constraint = f"{candidate_module}.complementConstraint"
        clause_gadget = f"{candidate_module}.clauseGadget"
        reference_executable = f"{candidate_module}.referenceExecutable"
        executable = f"{candidate_module}.synthesizedExecutable"
        clause_gadget_tm = f"{candidate_module}.clauseGadgetDirectTM"
        reference_tm = f"{candidate_module}.referenceDirectTM"
        direct_tm = f"{candidate_module}.synthesizedDirectTM"
        primitive = f"{candidate_module}.synthesizedPrimitive"
        program = f"{candidate_module}.synthesizedProgram"
        reference_forward = f"{candidate_module}.referenceSemanticForward"
        reference_reverse = f"{candidate_module}.referenceSemanticReverse"
        forward = f"{candidate_module}.semanticForward"
        reverse = f"{candidate_module}.semanticReverse"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="clause-constraint",
                declaration=clause_constraint,
                capability="clause_constraint",
                exact_type=(
                    "ComplexityReduction.NAEThreeSAT.Clause → "
                    f"ComplexityReduction.CSP.Constraint {target_gamma}"
                ),
                depends_on=node_dependencies.get("clause-constraint", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="complement-constraint",
                declaration=complement_constraint,
                capability="complement_constraint",
                exact_type=(
                    "ComplexityReduction.SAT.Literal → "
                    f"ComplexityReduction.CSP.Constraint {target_gamma}"
                ),
                depends_on=node_dependencies.get("complement-constraint", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="clause-gadget",
                declaration=clause_gadget,
                capability="clause_gadget",
                exact_type=(
                    "ComplexityReduction.NAEThreeSAT.Clause → "
                    f"{target_term}.Instance"
                ),
                depends_on=node_dependencies.get("clause-gadget", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reference-executable",
                declaration=reference_executable,
                capability="reference_executable",
                exact_type=(
                    "ComplexityReduction.NAEThreeSAT.Formula → "
                    f"{target_term}.Instance"
                ),
                depends_on=node_dependencies.get("reference-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reduction-executable",
                declaration=executable,
                capability="reduction_executable",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("reduction-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="clause-gadget-direct-tm",
                declaration=clause_gadget_tm,
                capability="clause_gadget_direct_tm",
                exact_type=(
                    "ComplexityReduction.TMPolyTimeMap "
                    "ComplexityReduction.Presentation.NAEThreeSAT.clauseEncodedType "
                    f"{target_term}.representation.encodedType {clause_gadget}"
                ),
                depends_on=node_dependencies.get("clause-gadget-direct-tm", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reference-direct-tm",
                declaration=reference_tm,
                capability="reference_direct_tm",
                exact_type=(
                    "ComplexityReduction.TMPolyTimeMap "
                    "ComplexityReduction.Presentation.NAEThreeSAT.formulaEncodedType "
                    f"{target_term}.representation.encodedType {reference_executable}"
                ),
                depends_on=node_dependencies.get("reference-direct-tm", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="direct-tm",
                declaration=direct_tm,
                capability="direct_tm",
                exact_type=(
                    "ComplexityReduction.TMPolyTimeMap "
                    f"{source_term}.representation.encodedType "
                    f"{target_term}.representation.encodedType {executable}"
                ),
                depends_on=node_dependencies.get("direct-tm", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reduction-primitive",
                declaration=primitive,
                capability="reduction_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("reduction-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="poly-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("poly-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence",
                declaration=f"{candidate_module}.programRunCoherence",
                capability="program_run_coherence",
                exact_type=(
                    f"∀ input : {source_term}.Instance, "
                    f"{program}.run input = {executable} input"
                ),
                depends_on=node_dependencies.get("program-run-coherence", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reference-semantic-forward",
                declaration=reference_forward,
                capability="reference_semantic_forward",
                exact_type=(
                    "∀ formula : ComplexityReduction.NAEThreeSAT.Formula, "
                    "ComplexityReduction.NAEThreeSAT.Formula.Satisfiable formula → "
                    f"{target_term}.accepts ({reference_executable} formula)"
                ),
                depends_on=node_dependencies.get("reference-semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reference-semantic-reverse",
                declaration=reference_reverse,
                capability="reference_semantic_reverse",
                exact_type=(
                    "∀ formula : ComplexityReduction.NAEThreeSAT.Formula, "
                    f"{target_term}.accepts ({reference_executable} formula) → "
                    "ComplexityReduction.NAEThreeSAT.Formula.Satisfiable formula"
                ),
                depends_on=node_dependencies.get("reference-semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-forward",
                declaration=forward,
                capability="semantic_forward",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input → "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-reverse",
                declaration=reverse,
                capability="semantic_reverse",
                exact_type=(
                    f"∀ input : {source_term}.Instance, "
                    f"{target_term}.accepts ({program}.run input) → "
                    f"{source_term}.accepts input"
                ),
                depends_on=node_dependencies.get("semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
        ]
    elif task_class == "whole_reduction_synthesis":
        executable = f"{candidate_module}.synthesizedExecutable"
        direct_tm = f"{candidate_module}.synthesizedDirectTM"
        primitive = f"{candidate_module}.synthesizedPrimitive"
        program = f"{candidate_module}.synthesizedProgram"
        forward = f"{candidate_module}.semanticForward"
        reverse = f"{candidate_module}.semanticReverse"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="reduction-executable",
                declaration=executable,
                capability="reduction_executable",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("reduction-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="direct-tm",
                declaration=direct_tm,
                capability="direct_tm",
                exact_type=(
                    "ComplexityReduction.TMPolyTimeMap "
                    f"{source_term}.representation.encodedType "
                    f"{target_term}.representation.encodedType {executable}"
                ),
                depends_on=node_dependencies.get("direct-tm", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reduction-primitive",
                declaration=primitive,
                capability="reduction_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("reduction-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="poly-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("poly-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence",
                declaration=f"{candidate_module}.programRunCoherence",
                capability="program_run_coherence",
                exact_type=(
                    f"∀ input : {source_term}.Instance, "
                    f"{program}.run input = {executable} input"
                ),
                depends_on=node_dependencies.get("program-run-coherence", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-forward",
                declaration=forward,
                capability="semantic_forward",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input → "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-reverse",
                declaration=reverse,
                capability="semantic_reverse",
                exact_type=(
                    f"∀ input : {source_term}.Instance, "
                    f"{target_term}.accepts ({program}.run input) → "
                    f"{source_term}.accepts input"
                ),
                depends_on=node_dependencies.get("semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
        ]
    elif task_class == "typed_capability_dag":
        if program_reference is None or representation_adapter_exact_type is None:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "typed capability DAG lacks its Lean-observed adapter",
            )
        program = f"{candidate_module}.representationAdapter"
        forward = f"{candidate_module}.semanticForward"
        reverse = f"{candidate_module}.semanticReverse"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="representation-adapter",
                declaration=program,
                capability="representation_adapter",
                exact_type=representation_adapter_exact_type,
                depends_on=node_dependencies.get("representation-adapter", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-forward",
                declaration=forward,
                capability="semantic_forward",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input → "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-reverse",
                declaration=reverse,
                capability="semantic_reverse",
                exact_type=(
                    f"∀ input : {source_term}.Instance, "
                    f"{target_term}.accepts ({program}.run input) → "
                    f"{source_term}.accepts input"
                ),
                depends_on=node_dependencies.get("semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=f"{candidate_module}.semanticCorrect",
                capability="semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
        ]
    elif task_class == "typed_exact_edge_construction_dag":
        normalization = f"{candidate_module}.parameterNormalization"
        primitive = f"{candidate_module}.reductionPrimitive"
        gadget = f"{candidate_module}.gadgetDefinitions"
        wellformed = f"{candidate_module}.outputWellformed"
        poly_bound = f"{candidate_module}.polynomialBound"
        program = f"{candidate_module}.polyProgram"
        coherence = f"{candidate_module}.programDirectTMCoherence"
        forward = f"{candidate_module}.semanticForward"
        reverse = f"{candidate_module}.semanticReverse"
        semantic = f"{candidate_module}.semanticCorrect"
        certificate = f"{candidate_module}.certifiedReduction"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="parameter-normalization",
                declaration=normalization,
                capability="parameter_normalization",
                exact_type=f"{source_term}.Instance → {source_term}.Instance",
                depends_on=node_dependencies.get("parameter-normalization", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="reduction-primitive",
                declaration=primitive,
                capability="reduction_primitive",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("reduction-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-definitions",
                declaration=gadget,
                capability="gadget_definitions",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("gadget-definitions", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="output-wellformed",
                declaration=wellformed,
                capability="output_wellformed",
                exact_type=(
                    f"(input : {source_term}.Instance) → "
                    f"{target_term}.accepts ({gadget} input) → "
                    f"{target_term}.accepts ({primitive} input)"
                ),
                depends_on=node_dependencies.get("output-wellformed", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="polynomial-bound",
                declaration=poly_bound,
                capability="polynomial_bound",
                exact_type=(
                    "ComplexityReduction.TMPolyTimeMap "
                    f"{source_term}.representation.encodedType "
                    f"{target_term}.representation.encodedType ({primitive})"
                ),
                depends_on=node_dependencies.get("polynomial-bound", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="poly-program",
                declaration=program,
                capability="poly_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("poly-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-direct-tm-coherence",
                declaration=coherence,
                capability="program_direct_tm_coherence",
                exact_type=(
                    f"(input : {source_term}.Instance) → "
                    f"{program}.run input = {primitive} input"
                ),
                depends_on=node_dependencies.get("program-direct-tm-coherence", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-forward",
                declaration=forward,
                capability="semantic_forward",
                exact_type=(
                    f"(input : {source_term}.Instance) → {source_term}.accepts input → "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-reverse",
                declaration=reverse,
                capability="semantic_reverse",
                exact_type=(
                    f"(input : {source_term}.Instance) → "
                    f"{target_term}.accepts ({program}.run input) → {source_term}.accepts input"
                ),
                depends_on=node_dependencies.get("semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="semantic-iff",
                declaration=semantic,
                capability="semantic_iff",
                exact_type=(
                    f"(input : {source_term}.Instance) → {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("semantic-iff", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="certified-reduction",
                declaration=certificate,
                capability="certified_reduction",
                exact_type=f"{candidate_module}.CertifiedReductionPackage",
                depends_on=node_dependencies.get("certified-reduction", ()),
            ),
        ]
    elif task_class == "typed_program_indexed_admission_dag":
        if program_reference is None:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "typed program-indexed admission DAG lacks its public packet",
            )
        executable = f"{candidate_module}.programIndexedExecutable"
        primitive = f"{candidate_module}.programIndexedPrimitive"
        program = f"{candidate_module}.programIndexedProgram"
        admission = f"{candidate_module}.programIndexedAdmission"
        packet_namespace = (
            "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources."
            "ProgramIndexedAdmissionPacket"
        )
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="program-executable",
                declaration=executable,
                capability="program_indexed_executable",
                exact_type=f"{source_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("program-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-primitive",
                declaration=primitive,
                capability="program_indexed_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("program-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program",
                declaration=program,
                capability="program_indexed_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence-direct-tm",
                declaration=admission,
                capability="program_indexed_coherence_direct_tm",
                exact_type=(
                    f"{packet_namespace}.ProgramRunCoherenceDirectTM "
                    f"{program_reference} {program}"
                ),
                depends_on=node_dependencies.get(
                    "program-run-coherence-direct-tm", ()
                ),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-semantic-iff",
                declaration=f"{candidate_module}.programIndexedSemanticCorrect",
                capability="program_indexed_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("program-semantic-iff", ()),
            ),
        ]
    elif task_class == "typed_tmkarp_program_indexed_composition_dag":
        if (
            program_reference is None
            or program_packet_reference is None
            or composition_intermediate is None
        ):
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "TMKarp/program-indexed composition lacks an admission, packet, or intermediate",
            )
        intermediate_term = composition_intermediate.term
        tmkarp_primitive = f"{candidate_module}.tmKarpPrimitive"
        tmkarp_program = f"{candidate_module}.tmKarpProgram"
        packet_executable = f"{candidate_module}.programIndexedExecutable"
        packet_primitive = f"{candidate_module}.programIndexedPrimitive"
        packet_program = f"{candidate_module}.programIndexedProgram"
        packet_admission = f"{candidate_module}.programIndexedAdmission"
        packet_semantic = f"{candidate_module}.programIndexedSemanticCorrect"
        composed_program = f"{candidate_module}.composedProgram"
        packet_namespace = (
            "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources."
            "ProgramIndexedAdmissionPacket"
        )
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="tmkarp-primitive",
                declaration=tmkarp_primitive,
                capability="tmkarp_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {intermediate_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-program",
                declaration=tmkarp_program,
                capability="tmkarp_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {intermediate_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-semantic-iff",
                declaration=f"{candidate_module}.tmKarpSemanticCorrect",
                capability="tmkarp_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{intermediate_term}.accepts ({tmkarp_program}.run input)"
                ),
                depends_on=node_dependencies.get("tmkarp-semantic-iff", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-executable",
                declaration=packet_executable,
                capability="program_indexed_executable",
                exact_type=f"{intermediate_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("program-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-primitive",
                declaration=packet_primitive,
                capability="program_indexed_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{intermediate_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("program-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program",
                declaration=packet_program,
                capability="program_indexed_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{intermediate_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-run-coherence-direct-tm",
                declaration=packet_admission,
                capability="program_indexed_coherence_direct_tm",
                exact_type=(
                    f"{packet_namespace}.ProgramRunCoherenceDirectTM "
                    f"{program_packet_reference} {packet_program}"
                ),
                depends_on=node_dependencies.get(
                    "program-run-coherence-direct-tm", ()
                ),
            ),
            NPHardAuthoringObligationV2(
                node_id="program-semantic-iff",
                declaration=packet_semantic,
                capability="program_indexed_semantic_iff",
                exact_type=(
                    f"∀ input : {intermediate_term}.Instance, "
                    f"{intermediate_term}.accepts input ↔ "
                    f"{target_term}.accepts ({packet_program}.run input)"
                ),
                depends_on=node_dependencies.get("program-semantic-iff", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="composed-program",
                declaration=composed_program,
                capability="program_indexed_composed_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("composed-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="composed-semantic-iff",
                declaration=f"{candidate_module}.composedSemanticCorrect",
                capability="program_indexed_composed_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({composed_program}.run input)"
                ),
                depends_on=node_dependencies.get("composed-semantic-iff", ()),
            ),
        ]
    elif task_class == "typed_gadget_indexed_admission_dag":
        if program_reference is None or composition_intermediate is None:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "gadget-indexed admission lacks its packet or reference endpoint",
            )
        reference_term = composition_intermediate.term
        executable = f"{candidate_module}.gadgetExecutable"
        forward = f"{candidate_module}.gadgetSemanticForward"
        reverse = f"{candidate_module}.gadgetSemanticReverse"
        gadget_program = f"{candidate_module}.gadgetProgram"
        composed_program = f"{candidate_module}.gadgetComposedProgram"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="gadget-reference-audit",
                declaration=f"{candidate_module}.gadgetReferenceAudit",
                capability="gadget_reference_audit",
                exact_type=f"{program_reference}.referenceAudit",
                depends_on=node_dependencies.get("gadget-reference-audit", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-normalization-audit",
                declaration=f"{candidate_module}.gadgetNormalizationAudit",
                capability="gadget_normalization_audit",
                exact_type=f"{program_reference}.normalizationAudit",
                depends_on=node_dependencies.get("gadget-normalization-audit", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-executable",
                declaration=executable,
                capability="gadget_executable",
                exact_type=f"{reference_term}.Instance → {target_term}.Instance",
                depends_on=node_dependencies.get("gadget-executable", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-parameter-audit",
                declaration=f"{candidate_module}.gadgetParameterAudit",
                capability="gadget_parameter_audit",
                exact_type=f"{program_reference}.parameterAudit",
                depends_on=node_dependencies.get("gadget-parameter-audit", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-semantic-forward",
                declaration=forward,
                capability="gadget_semantic_forward",
                exact_type=(
                    f"∀ input : {reference_term}.Instance, "
                    f"{reference_term}.accepts input → "
                    f"{target_term}.accepts ({executable} input)"
                ),
                depends_on=node_dependencies.get("gadget-semantic-forward", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-semantic-reverse",
                declaration=reverse,
                capability="gadget_semantic_reverse",
                exact_type=(
                    f"∀ input : {reference_term}.Instance, "
                    f"{target_term}.accepts ({executable} input) → "
                    f"{reference_term}.accepts input"
                ),
                depends_on=node_dependencies.get("gadget-semantic-reverse", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-direct-tm",
                declaration=f"{candidate_module}.gadgetDirectTM",
                capability="gadget_direct_tm",
                exact_type=(
                    "ComplexityReduction.Agent.Hardness.Authoring."
                    "ExecutableDirectTMEvidence "
                    f"{reference_term} {target_term} {executable}"
                ),
                depends_on=node_dependencies.get("gadget-direct-tm", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-program",
                declaration=gadget_program,
                capability="gadget_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{reference_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("gadget-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-composed-program",
                declaration=composed_program,
                capability="gadget_composed_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("gadget-composed-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="gadget-composed-semantic-iff",
                declaration=f"{candidate_module}.gadgetComposedSemanticCorrect",
                capability="gadget_composed_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({composed_program}.run input)"
                ),
                depends_on=node_dependencies.get(
                    "gadget-composed-semantic-iff", ()
                ),
            ),
        ]
    elif task_class == "typed_tmkarp_admission_dag":
        if program_reference is None:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "typed TMKarp admission DAG lacks its Lean-observed witness",
            )
        primitive = f"{candidate_module}.tmKarpPrimitive"
        program = f"{candidate_module}.tmKarpProgram"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="tmkarp-primitive",
                declaration=primitive,
                capability="tmkarp_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-program",
                declaration=program,
                capability="tmkarp_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-semantic-iff",
                declaration=f"{candidate_module}.tmKarpSemanticCorrect",
                capability="tmkarp_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({program}.run input)"
                ),
                depends_on=node_dependencies.get("tmkarp-semantic-iff", ()),
            ),
        ]
    elif task_class == "typed_tmkarp_dependent_composition_dag":
        if program_reference is None or composition_intermediate is None:
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "dependent TMKarp composition lacks its admission or intermediate endpoint",
            )
        intermediate_term = composition_intermediate.term
        primitive = f"{candidate_module}.tmKarpPrimitive"
        tmkarp_program = f"{candidate_module}.tmKarpProgram"
        composed_program = f"{candidate_module}.composedProgram"
        obligations = [
            NPHardAuthoringObligationV2(
                node_id="tmkarp-primitive",
                declaration=primitive,
                capability="tmkarp_primitive",
                exact_type=(
                    "ComplexityReduction.Program.Primitive "
                    f"{source_term}.representation {intermediate_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-primitive", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-program",
                declaration=tmkarp_program,
                capability="tmkarp_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {intermediate_term}.representation"
                ),
                depends_on=node_dependencies.get("tmkarp-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="tmkarp-semantic-iff",
                declaration=f"{candidate_module}.tmKarpSemanticCorrect",
                capability="tmkarp_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{intermediate_term}.accepts ({tmkarp_program}.run input)"
                ),
                depends_on=node_dependencies.get("tmkarp-semantic-iff", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="composed-program",
                declaration=composed_program,
                capability="dependent_composed_program",
                exact_type=(
                    "ComplexityReduction.Program.PolyProg "
                    f"{source_term}.representation {target_term}.representation"
                ),
                depends_on=node_dependencies.get("composed-program", ()),
            ),
            NPHardAuthoringObligationV2(
                node_id="composed-semantic-iff",
                declaration=f"{candidate_module}.composedSemanticCorrect",
                capability="dependent_composed_semantic_iff",
                exact_type=(
                    f"∀ input : {source_term}.Instance, {source_term}.accepts input ↔ "
                    f"{target_term}.accepts ({composed_program}.run input)"
                ),
                depends_on=node_dependencies.get("composed-semantic-iff", ()),
            ),
        ]
    else:
        _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 task class")
    expected_ids = tuple(str(node["id"]) for node in manifest_nodes)
    actual_ids = tuple(node.node_id for node in obligations)
    if actual_ids != expected_ids:
        _v2_fail(
            "candidate_dependency_stale",
            f"manifest gap nodes do not match v2 obligations: {expected_ids!r} != {actual_ids!r}",
        )
    return tuple(obligations)


def build_np_hard_authoring_task_v2(
    *,
    root: Path,
    input_module: str,
    input_problem_declaration: str,
    hub_module: str,
    hub_declaration: str,
    task_class: str,
    gap_nodes: tuple[Mapping[str, Any], ...],
    public_source_files: tuple[str, ...],
    allowed_primitives: tuple[str, ...],
    allowed_primitive_layers: Mapping[str, tuple[str, ...]] | None = None,
    allowed_primitive_exact_types: Mapping[str, str] | None = None,
    program_reference: str | None,
    mapping_invariant: str | None,
    program_packet_reference: str | None = None,
    observed_capability_terms: Mapping[str, str] | None = None,
    observed_capability_exact_types: Mapping[str, str] | None = None,
    representation_adapter_exact_type: str | None = None,
    composition_intermediate_module: str | None = None,
    composition_intermediate_declaration: str | None = None,
    composition_successor_module: str | None = None,
    composition_successor_source: str | None = None,
    composition_successor_target: str | None = None,
    composition_admission_observation: Mapping[str, str] | None = None,
    composition_successor_observation: Mapping[str, str] | None = None,
    additional_allowed_imports: tuple[str, ...] = (),
    additional_dependency_hashes: Mapping[str, str] | None = None,
    attempt_budget: int = 4,
    timeout_seconds: int = 60,
    max_output_tokens: int = 3_000,
    runtime_module: str = RUNTIME_MODULE,
) -> NPHardAuthoringTaskV2:
    root = root.resolve()
    source = NPHardAuthoringEndpointV2(module=hub_module, term=hub_declaration)
    target = NPHardAuthoringEndpointV2(
        module=input_module, term=input_problem_declaration
    )
    source.validate()
    target.validate()
    if (composition_intermediate_module is None) != (
        composition_intermediate_declaration is None
    ):
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            "composition intermediate module/declaration must be supplied together",
        )
    composition_intermediate = (
        NPHardAuthoringEndpointV2(
            module=composition_intermediate_module,
            term=composition_intermediate_declaration,
        )
        if composition_intermediate_module is not None
        and composition_intermediate_declaration is not None
        else None
    )
    if composition_intermediate is not None:
        composition_intermediate.validate()
    if composition_successor_module is not None:
        try:
            validate_module_name(composition_successor_module)
        except ValueError as error:
            _v2_fail("authoring_catalog_dependency_stale", str(error))
    if (composition_successor_source is None) != (
        composition_successor_target is None
    ):
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            "canonical successor source/target must be supplied together",
        )
    if (composition_admission_observation is None) != (
        composition_successor_observation is None
    ):
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            "admission/successor observer records must be supplied together",
        )
    if (composition_successor_source is None) != (
        composition_admission_observation is None
    ):
        _v2_fail(
            "invalid_np_hard_authoring_v2_schema",
            "canonical successor fields require their complete observer chain",
        )
    if composition_successor_source is not None:
        if task_class != "typed_tmkarp_dependent_composition_dag":
            _v2_fail(
                "invalid_np_hard_authoring_v2_schema",
                "canonical successor endpoints require a dependent TMKarp task",
            )
        try:
            validate_declaration_name(
                composition_successor_source,
                label="canonical composition successor source",
            )
            validate_declaration_name(
                composition_successor_target or "",
                label="canonical composition successor target",
            )
        except ValueError as error:
            _v2_fail("candidate_wrong_endpoint", str(error))
    dependency_hashes: dict[str, str] = {}
    for relative_name in public_source_files:
        path = (root / relative_name).resolve()
        try:
            path.relative_to(root)
        except ValueError:
            _v2_fail("candidate_dependency_stale", "public source escaped the workspace")
        if not path.is_file():
            _v2_fail("candidate_dependency_stale", f"public source is missing: {relative_name}")
        _v2_require_public_text(relative_name, label="public source")
        source_text = path.read_text(encoding="utf-8")
        _v2_require_public_text(source_text, label=f"public source {relative_name}")
        dependency_hashes[f"public:{relative_name}"] = _tagged_content_hash(sha256_file(path))
    try:
        validated_runtime_module = validate_module_name(runtime_module)
    except ValueError as error:
        _v2_fail("import_not_allowlisted", str(error))
    allowed_imports = tuple(
        dict.fromkeys(
            (
                input_module,
                hub_module,
                validated_runtime_module,
                *((composition_intermediate.module,) if composition_intermediate else ()),
                *((composition_successor_module,) if composition_successor_module else ()),
                *(validate_module_name(module) for module in additional_allowed_imports),
            )
        )
    )
    for imported in allowed_imports:
        path = module_file(root / "Lean", imported)
        dependency_hashes[f"module:{imported}"] = _tagged_content_hash(sha256_file(path))
    for dependency_name, dependency_hash in sorted(
        (additional_dependency_hashes or {}).items()
    ):
        if dependency_name in dependency_hashes:
            _v2_fail(
                "candidate_dependency_stale",
                f"additional dependency shadows an existing binding: {dependency_name}",
            )
        _v2_require_public_text(dependency_name, label="additional dependency name")
        _v2_require_hash(dependency_hash, label=f"additional dependency {dependency_name}")
        dependency_hashes[dependency_name] = dependency_hash
    for node_id, term in sorted((observed_capability_terms or {}).items()):
        if not isinstance(node_id, str) or not isinstance(term, str):
            _v2_fail(
                "fabricated_declaration_handle",
                "observed capability term binding is invalid",
            )
        dependency_hashes[f"content:observed-capability-term:{node_id}"] = sha256_id(
            term
        )
    for node_id, exact_type in sorted(
        (observed_capability_exact_types or {}).items()
    ):
        if not isinstance(node_id, str) or not isinstance(exact_type, str):
            _v2_fail(
                "candidate_exact_type_mismatch",
                "observed capability exact-type binding is invalid",
            )
        dependency_hashes[
            f"content:observed-capability-exact-type:{node_id}"
        ] = sha256_id(exact_type)
    if composition_successor_module is not None:
        dependency_hashes[
            "content:observed-capability-module:composed-program"
        ] = sha256_id(composition_successor_module)
    if composition_successor_source is not None:
        dependency_hashes[
            "content:observed-composition-successor-source"
        ] = sha256_id(composition_successor_source)
        dependency_hashes[
            "content:observed-composition-successor-target"
        ] = sha256_id(composition_successor_target)
    stable_seed_payload = {
        "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V2,
        "source": source.to_dict(),
        "target": target.to_dict(),
        "task_class": task_class,
        "gap_nodes": list(gap_nodes),
        "dependency_hashes": dependency_hashes,
    }
    if task_class == "typed_capability_dag":
        stable_seed_payload.update(
            {
                "observed_capability_terms": dict(
                    sorted((observed_capability_terms or {}).items())
                ),
                "representation_adapter_exact_type": (
                    representation_adapter_exact_type
                ),
            }
        )
    elif task_class == "typed_exact_edge_construction_dag":
        stable_seed_payload.update(
            {
                "observed_capability_terms": {},
                "observed_capability_exact_types": {},
            }
        )
    elif task_class in {
        "typed_tmkarp_admission_dag",
        "typed_tmkarp_dependent_composition_dag",
        "typed_program_indexed_admission_dag",
        "typed_tmkarp_program_indexed_composition_dag",
        "typed_gadget_indexed_admission_dag",
    }:
        stable_seed_payload.update(
            {
                "observed_capability_terms": dict(
                    sorted((observed_capability_terms or {}).items())
                ),
                "observed_capability_exact_types": dict(
                    sorted((observed_capability_exact_types or {}).items())
                ),
            }
        )
        if task_class in {
            "typed_tmkarp_dependent_composition_dag",
            "typed_tmkarp_program_indexed_composition_dag",
            "typed_gadget_indexed_admission_dag",
        }:
            stable_seed_payload["composition_intermediate"] = (
                composition_intermediate.to_dict()
                if composition_intermediate is not None
                else None
            )
            if task_class != "typed_gadget_indexed_admission_dag":
                stable_seed_payload["composition_successor_module"] = (
                    composition_successor_module
                )
                if composition_successor_source is not None:
                    stable_seed_payload["composition_successor_source"] = (
                        composition_successor_source
                    )
                    stable_seed_payload["composition_successor_target"] = (
                        composition_successor_target
                    )
                    stable_seed_payload["composition_admission_observation"] = dict(
                        composition_admission_observation or {}
                    )
                    stable_seed_payload["composition_successor_observation"] = dict(
                        composition_successor_observation or {}
                    )
    stable_seed = sha256_id(stable_seed_payload).removeprefix("sha256:")[:16]
    candidate_module = f"Generated.NPHardV2.C{stable_seed}.Authoring"
    obligations = _v2_obligations(
        task_class=task_class,
        candidate_module=candidate_module,
        source_term=hub_declaration,
        target_term=input_problem_declaration,
        program_reference=program_reference,
        program_packet_reference=program_packet_reference,
        mapping_invariant=mapping_invariant,
        representation_adapter_exact_type=representation_adapter_exact_type,
        composition_intermediate=composition_intermediate,
        manifest_nodes=gap_nodes,
    )
    obligation_ids = {node.node_id for node in obligations}
    obligation_dependencies = {
        dependency for node in obligations for dependency in node.depends_on
    }
    terminal_candidates = obligation_ids - obligation_dependencies
    if len(terminal_candidates) != 1:
        _v2_fail(
            "candidate_dependency_stale",
            "authoring obligation DAG lacks one unique terminal node",
        )
    terminal_node_id = next(iter(terminal_candidates))
    final_program_node_id = {
        "semantic_proof": None,
        "program_composition": "composed-program",
        "program_synthesis": "poly-program",
        "whole_reduction_synthesis": "poly-program",
        "typed_capability_dag": "representation-adapter",
        "typed_tmkarp_admission_dag": "tmkarp-program",
        "typed_tmkarp_dependent_composition_dag": "composed-program",
        "typed_program_indexed_admission_dag": "program",
        "typed_tmkarp_program_indexed_composition_dag": "composed-program",
        "typed_gadget_indexed_admission_dag": "gadget-composed-program",
        "typed_exact_edge_construction_dag": "poly-program",
    }[task_class]
    final_declaration = f"{candidate_module}.authoredForwardReduction"
    task_arguments = {
        "task_class": task_class,
        "source_problem": source,
        "target_problem": target,
        "candidate_module": candidate_module,
        "final_candidate_declaration": final_declaration,
        "final_exact_type": (
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{hub_declaration} {input_problem_declaration}"
        ),
        "gap_nodes": obligations,
        "editable_declarations": tuple(node.declaration for node in obligations),
        "allowed_imports": allowed_imports,
        "allowed_primitives": tuple(allowed_primitives),
        "allowed_primitive_layers": tuple(
            sorted(
                (
                    allowed_primitive_layers
                    or {
                        "core": tuple(allowed_primitives),
                        "construction": (),
                        "direct_tm": (),
                        "semantic": (),
                    }
                ).items()
            )
        ),
        "allowed_primitive_exact_types": tuple(
            sorted((allowed_primitive_exact_types or {}).items())
        ),
        "forbidden_axioms": ("sorryAx", "admit", "axiom", "unsafe"),
        "dependency_hashes": tuple(sorted(dependency_hashes.items())),
        "public_source_files": public_source_files,
        "observed_capability_terms": tuple(
            sorted((observed_capability_terms or {}).items())
        ),
        "observed_capability_exact_types": tuple(
            sorted((observed_capability_exact_types or {}).items())
        ),
        "terminal_node_id": terminal_node_id,
        "final_program_node_id": final_program_node_id,
        "composition_intermediate": composition_intermediate,
        "composition_successor_module": composition_successor_module,
        "attempt_budget": attempt_budget,
        "timeout_seconds": timeout_seconds,
        "max_output_tokens": max_output_tokens,
        "composition_successor_source": composition_successor_source,
        "composition_successor_target": composition_successor_target,
        "composition_admission_observation": (
            tuple(sorted((composition_admission_observation or {}).items()))
            if composition_admission_observation is not None
            else None
        ),
        "composition_successor_observation": (
            tuple(sorted((composition_successor_observation or {}).items()))
            if composition_successor_observation is not None
            else None
        ),
    }
    provisional = NPHardAuthoringTaskV2(
        request_id="sha256:" + "0" * 64, **task_arguments
    )
    task = NPHardAuthoringTaskV2(
        request_id=provisional.computed_request_id, **task_arguments
    )
    task.validate()
    return task


def build_np_hard_authoring_tasks_v2(
    *, root: Path, suite_path: Path
) -> tuple[NPHardAuthoringTaskV2, ...]:
    from .np_hard_generalization import load_np_hard_generalization_suite

    suite = load_np_hard_generalization_suite(suite_path, root=root)
    tasks: list[NPHardAuthoringTaskV2] = []
    for case in suite.cases:
        if case.kind != "model_authoring" or case.authoring is None:
            continue
        authoring = case.authoring
        tasks.append(
            build_np_hard_authoring_task_v2(
                root=root,
                input_module=case.module,
                input_problem_declaration=case.problem,
                hub_module=str(authoring["hub_module"]),
                hub_declaration=str(authoring["hub"]),
                task_class=str(authoring["task_class"]),
                gap_nodes=tuple(authoring["gap_nodes"]),
                public_source_files=case.public_source_files,
                allowed_primitives=tuple(authoring["allowed_primitives"]),
                program_reference=authoring.get("program_reference"),
                mapping_invariant=authoring.get("mapping_invariant"),
            )
        )
    return tuple(tasks)


def build_np_hard_authoring_prompt_v2(
    *, task: NPHardAuthoringTaskV2, root: Path
) -> str:
    task.validate()
    public_sources: dict[str, str] = {}
    for relative_name in task.public_source_files:
        source = (root / relative_name).read_text(encoding="utf-8")
        _v2_require_public_text(source, label=f"prompt source {relative_name}")
        public_sources[relative_name] = source[:20_000]
    payload = {
        "schema_version": NP_HARD_AUTHORING_TASK_SCHEMA_V2,
        "objective": "prove_np_hard",
        "task": task.to_dict(),
        "public_sources": public_sources,
        "policy": {
            "only_edit_exact_declarations": True,
            "compiler_inserted_math_tokens": 0,
            "lean_kernel_is_authority": True,
            "model_may_not_choose_endpoints_or_direction": True,
        },
        "response_template": {
            "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V2,
            "action": "submit_patch",
            "request_id": task.request_id,
            "task_class": task.task_class,
            "required_direction": task.required_direction,
            "source_problem": task.source_problem.to_dict(),
            "target_problem": task.target_problem.to_dict(),
            "dependency_fingerprint": task.dependency_fingerprint,
            "replacement_bodies": {
                declaration: "Lean term body only"
                for declaration in task.editable_declarations
            },
        },
    }
    serialized = json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)
    _v2_require_public_text(serialized, label="v2 prompt")
    for forbidden_key in ('"case_id"', '"expected"', '"gold"', '"hidden_gold"'):
        if forbidden_key in serialized.lower():
            _v2_fail("oracle_or_gold_import", "v2 prompt contains benchmark-only metadata")
    return serialized


@dataclass(frozen=True)
class NPHardAuthoringPatchV2:
    request_id: str
    task_class: str
    required_direction: str
    source_problem: NPHardAuthoringEndpointV2
    target_problem: NPHardAuthoringEndpointV2
    dependency_fingerprint: str
    replacement_bodies: tuple[tuple[str, str], ...]
    action: str = "submit_patch"
    schema_version: str = NP_HARD_AUTHORING_PATCH_SCHEMA_V2

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "action": self.action,
            "request_id": self.request_id,
            "task_class": self.task_class,
            "required_direction": self.required_direction,
            "source_problem": self.source_problem.to_dict(),
            "target_problem": self.target_problem.to_dict(),
            "dependency_fingerprint": self.dependency_fingerprint,
            "replacement_bodies": dict(self.replacement_bodies),
        }


def parse_np_hard_authoring_patch_v2(
    *, content: str, task: NPHardAuthoringTaskV2
) -> NPHardAuthoringPatchV2:
    task.validate()
    try:
        value = extract_json_object(content)
    except ValueError as error:
        _v2_fail("invalid_np_hard_authoring_v2_schema", str(error))
    if not isinstance(value, Mapping):
        _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 patch must be an object")
    expected_keys = {
        "schema_version",
        "action",
        "request_id",
        "task_class",
        "required_direction",
        "source_problem",
        "target_problem",
        "dependency_fingerprint",
        "replacement_bodies",
    }
    _v2_exact_keys(value, expected_keys, label="v2 patch")
    if value["schema_version"] != NP_HARD_AUTHORING_PATCH_SCHEMA_V2 or value["action"] != "submit_patch":
        _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 patch envelope")
    if value["request_id"] != task.request_id or value["task_class"] != task.task_class:
        _v2_fail("candidate_dependency_stale", "v2 patch belongs to another task")
    if value["required_direction"] != task.required_direction:
        _v2_fail("candidate_wrong_direction", "v2 patch mutated the frozen direction")
    source = NPHardAuthoringEndpointV2.from_dict(value["source_problem"])
    target = NPHardAuthoringEndpointV2.from_dict(value["target_problem"])
    if source != task.source_problem or target != task.target_problem:
        _v2_fail("candidate_wrong_endpoint", "v2 patch mutated an exact endpoint")
    if value["dependency_fingerprint"] != task.dependency_fingerprint:
        _v2_fail("candidate_dependency_stale", "v2 patch uses stale dependencies")
    raw_bodies = value["replacement_bodies"]
    if not isinstance(raw_bodies, Mapping):
        _v2_fail("candidate_outside_edit_boundary", "v2 replacement bodies must be an object")
    if set(raw_bodies) != set(task.editable_declarations):
        _v2_fail(
            "candidate_outside_edit_boundary",
            "v2 patch omitted or added an editable declaration",
        )
    bodies: list[tuple[str, str]] = []
    for declaration in task.editable_declarations:
        body = raw_bodies[declaration]
        if not isinstance(body, str) or not body.strip():
            _v2_fail("candidate_outside_edit_boundary", "v2 replacement body is empty")
        if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
            _v2_fail("candidate_outside_edit_boundary", "v2 replacement body is too large")
        match = BANNED_BODY_RE.search(body)
        if match:
            token = match.group(0).lower()
            if token in {"sorry", "admit", "axiom", "unsafe"}:
                code = "candidate_nonstandard_axiom"
            elif token == "import":
                code = "import_not_allowlisted"
            else:
                code = "candidate_outside_edit_boundary"
            _v2_fail(code, f"v2 body contains forbidden token: {token}")
        _v2_require_public_text(body, label="v2 replacement body")
        try:
            assert_generated_source_is_safe(body)
        except ValueError as error:
            code = (
                "oracle_or_gold_import"
                if "quarantined" in str(error)
                else "candidate_nonstandard_axiom"
            )
            _v2_fail(code, str(error))
        bodies.append((declaration, body if body.endswith("\n") else body + "\n"))
    return NPHardAuthoringPatchV2(
        request_id=task.request_id,
        task_class=task.task_class,
        required_direction=task.required_direction,
        source_problem=source,
        target_problem=target,
        dependency_fingerprint=task.dependency_fingerprint,
        replacement_bodies=tuple(bodies),
    )


@dataclass(frozen=True)
class NPHardAuthoringResultV2:
    request_id: str
    outcome: str
    accepted_nodes: tuple[str, ...]
    remaining_nodes: tuple[str, ...]
    candidate_hashes: tuple[tuple[str, str], ...]
    lean_diagnostics: tuple[str, ...]
    policy_diagnostics: tuple[str, ...]
    model_calls: tuple[Mapping[str, Any], ...]
    final_certificate: str | None
    replay_certificate: str | None
    schema_version: str = NP_HARD_AUTHORING_RESULT_SCHEMA_V2

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_AUTHORING_RESULT_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result schema")
        if self.request_id != task.request_id:
            _v2_fail("candidate_dependency_stale", "v2 result belongs to another request")
        if self.outcome not in NP_HARD_AUTHORING_OUTCOMES_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result outcome")
        all_nodes = tuple(node.node_id for node in task.gap_nodes)
        if len(set(self.accepted_nodes)) != len(self.accepted_nodes) or len(
            set(self.remaining_nodes)
        ) != len(self.remaining_nodes):
            _v2_fail("candidate_dependency_stale", "v2 result repeats a node")
        if set(self.accepted_nodes) & set(self.remaining_nodes) or set(
            self.accepted_nodes + self.remaining_nodes
        ) != set(all_nodes):
            _v2_fail("candidate_dependency_stale", "v2 result does not partition gap nodes")
        if self.accepted_nodes != all_nodes[: len(self.accepted_nodes)]:
            _v2_fail("candidate_dependency_stale", "v2 accepted nodes are not a DAG prefix")
        candidate_hashes = dict(self.candidate_hashes)
        if len(candidate_hashes) != len(self.candidate_hashes) or set(candidate_hashes) != set(
            self.accepted_nodes
        ):
            _v2_fail("candidate_dependency_stale", "v2 result candidate hashes do not match accepted nodes")
        for node_id, digest in self.candidate_hashes:
            _v2_require_hash(digest, label=f"candidate hash {node_id}")
        if self.outcome == "accepted":
            if self.accepted_nodes != all_nodes or self.remaining_nodes:
                _v2_fail("candidate_dependency_stale", "accepted v2 result has remaining nodes")
            if self.final_certificate is None or self.replay_certificate is None:
                _v2_fail("independent_replay_failed", "accepted v2 result lacks final certificates")
            _v2_require_hash(self.final_certificate, label="final certificate")
            _v2_require_hash(self.replay_certificate, label="replay certificate")
        elif self.final_certificate is not None or self.replay_certificate is not None:
            _v2_fail("independent_replay_failed", "non-accepted v2 result claims final authority")
        if not all(isinstance(item, str) for item in self.lean_diagnostics + self.policy_diagnostics):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result diagnostics are invalid")
        if not all(isinstance(item, Mapping) for item in self.model_calls):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result model calls are invalid")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {
            "schema_version": self.schema_version,
            "request_id": self.request_id,
            "outcome": self.outcome,
            "accepted_nodes": list(self.accepted_nodes),
            "remaining_nodes": list(self.remaining_nodes),
            "candidate_hashes": dict(self.candidate_hashes),
            "lean_diagnostics": list(self.lean_diagnostics),
            "policy_diagnostics": list(self.policy_diagnostics),
            "model_calls": [dict(item) for item in self.model_calls],
            "final_certificate": self.final_certificate,
            "replay_certificate": self.replay_certificate,
        }

    @classmethod
    def from_dict(
        cls, value: Mapping[str, Any], *, task: NPHardAuthoringTaskV2
    ) -> "NPHardAuthoringResultV2":
        if not isinstance(value, Mapping):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result must be an object")
        expected = {
            "schema_version",
            "request_id",
            "outcome",
            "accepted_nodes",
            "remaining_nodes",
            "candidate_hashes",
            "lean_diagnostics",
            "policy_diagnostics",
            "model_calls",
            "final_certificate",
            "replay_certificate",
        }
        _v2_exact_keys(value, expected, label="v2 result")
        if value["schema_version"] != NP_HARD_AUTHORING_RESULT_SCHEMA_V2:
            _v2_fail("invalid_np_hard_authoring_v2_schema", "unsupported v2 result schema")
        for key in ("accepted_nodes", "remaining_nodes", "lean_diagnostics", "policy_diagnostics"):
            if not isinstance(value[key], list) or not all(isinstance(item, str) for item in value[key]):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 result field {key} is invalid")
        if not isinstance(value["candidate_hashes"], Mapping) or not all(
            isinstance(name, str) and isinstance(digest, str)
            for name, digest in value["candidate_hashes"].items()
        ):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result candidate hashes are invalid")
        if not isinstance(value["model_calls"], list) or not all(
            isinstance(item, Mapping) for item in value["model_calls"]
        ):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result model calls are invalid")
        if not isinstance(value["request_id"], str) or not isinstance(value["outcome"], str):
            _v2_fail("invalid_np_hard_authoring_v2_schema", "v2 result identity is invalid")
        for key in ("final_certificate", "replay_certificate"):
            if value[key] is not None and not isinstance(value[key], str):
                _v2_fail("invalid_np_hard_authoring_v2_schema", f"v2 result field {key} is invalid")
        result = cls(
            request_id=value["request_id"],
            outcome=value["outcome"],
            accepted_nodes=tuple(value["accepted_nodes"]),
            remaining_nodes=tuple(value["remaining_nodes"]),
            candidate_hashes=tuple(sorted(value["candidate_hashes"].items())),
            lean_diagnostics=tuple(value["lean_diagnostics"]),
            policy_diagnostics=tuple(value["policy_diagnostics"]),
            model_calls=tuple(dict(item) for item in value["model_calls"]),
            final_certificate=value["final_certificate"],
            replay_certificate=value["replay_certificate"],
            schema_version=value["schema_version"],
        )
        result.validate(task)
        return result


def accepted_np_hard_authoring_result_v2(
    *,
    task: NPHardAuthoringTaskV2,
    candidate_hashes: Mapping[str, str],
    final_certificate: str,
    replay_certificate: str,
    lean_diagnostics: tuple[str, ...] = (),
    policy_diagnostics: tuple[str, ...] = (),
    model_calls: tuple[Mapping[str, Any], ...] = (),
) -> NPHardAuthoringResultV2:
    result = NPHardAuthoringResultV2(
        request_id=task.request_id,
        outcome="accepted",
        accepted_nodes=tuple(node.node_id for node in task.gap_nodes),
        remaining_nodes=(),
        candidate_hashes=tuple(sorted(candidate_hashes.items())),
        lean_diagnostics=lean_diagnostics,
        policy_diagnostics=policy_diagnostics,
        model_calls=model_calls,
        final_certificate=final_certificate,
        replay_certificate=replay_certificate,
    )
    result.validate(task)
    return result
