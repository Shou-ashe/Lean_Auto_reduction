"""G-C sequential capability runtime for exact NP-hard authoring.

The runtime consumes one immutable :class:`NPHardAuthoringTaskV2` and exposes
exactly one DAG node to the model at a time.  A node is accepted only after a
single persistent Lean worker validates the cumulative candidate, the source
is published by content hash, and a separate fresh Lean process rediscovers
the new declaration.  Checkpoints contain hashes and evidence only; candidate
bodies are recovered from their content-addressed publications on resume.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol

from .authoring_contract import BANNED_BODY_RE, HardnessContractError
from .lean_runner import (
    RUNTIME_MODULE,
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from .lean_worker_pool import LeanWorkerKey, LeanWorkerPool
from .model_client import ModelResponse, extract_json_object
from .models import CommandResult, sha256_id
from .np_hard_authoring import (
    NP_HARD_AUTHORING_MAX_BODY_CHARS,
    NP_HARD_SUCCESSOR_CHAIN_PROBE_SCHEMA_V1,
    NPHardAuthoringObligationV2,
    NPHardAuthoringResultV2,
    NPHardAuthoringTaskV2,
    _certified_successor_witness_owned_by_module_v2,
    _exact_certified_reduction_endpoints_v2,
    _exact_gadget_packet_endpoints_v2,
    _exact_tmkarp_reduction_endpoints_v2,
    _normalized_certified_successor_exact_endpoints_v2,
    _observer_capability_record_payload_v2,
    _staged_authoring_surface_is_exact_v2,
    _successor_only_chain_probe_source_v2,
    _successor_only_observer_chain_payload_v2,
    accepted_np_hard_authoring_result_v2,
    deletion_command_matches_declaration_v2,
)
from .np_hard_production import required_model_call_budget


NP_HARD_NODE_REQUEST_SCHEMA_V1 = "hardness_np_hard_node_request_v1"
NP_HARD_NODE_PATCH_SCHEMA_V1 = "hardness_np_hard_node_patch_v1"
NP_HARD_GAP_CHECKPOINT_SCHEMA_V1 = "hardness_np_hard_gap_checkpoint_v1"
NP_HARD_GAP_PUBLICATION_SCHEMA_V1 = "hardness_np_hard_gap_publication_v1"
NP_HARD_GAP_RUNTIME_REPORT_SCHEMA_V1 = "hardness_np_hard_gap_runtime_result_v1"
NP_HARD_MAX_INSTANCE_CALL_BUDGET = 64
NP_HARD_NODE_PROMPT_MAX_SOURCE_FILES = 8
NP_HARD_NODE_PROMPT_SOURCE_CHAR_BUDGET = 40_000
NP_HARD_NODE_PROMPT_SOURCE_EXCERPT_CHARS = 16_000
NP_HARD_NODE_PROMPT_DEPENDENCY_BODY_CHAR_BUDGET = 16_000
NP_HARD_NODE_PROMPT_DIAGNOSTIC_CHARS = 4_000

_PROMPT_SOURCE_IMPORT_RE = re.compile(
    r"(?m)^\s*import\s+([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)*)\s*$"
)
_PROMPT_SOURCE_STOP_WORDS = frozenset(
    {
        "accepted",
        "authoring",
        "benchmark",
        "capability",
        "complexity",
        "declaration",
        "encoded",
        "encoding",
        "exact",
        "generated",
        "hardness",
        "input",
        "instance",
        "lean",
        "node",
        "problem",
        "program",
        "reduction",
        "reference",
        "representation",
        "source",
        "structured",
        "synthesized",
        "target",
        "type",
    }
)

_TMKARP_PRIMITIVE_CAPABILITIES = frozenset({"tmkarp_primitive"})
_TMKARP_PROGRAM_CAPABILITIES = frozenset({"tmkarp_program"})
_TMKARP_SEMANTIC_IFF_CAPABILITIES = frozenset({"tmkarp_semantic_iff"})
_DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES = frozenset(
    {"dependent_composed_program"}
)
_DEPENDENT_COMPOSED_SEMANTIC_IFF_CAPABILITIES = frozenset(
    {"dependent_composed_semantic_iff"}
)
_TMKARP_ADMISSION_TASK_CLASSES = frozenset(
    {
        "typed_tmkarp_admission_dag",
        "typed_tmkarp_dependent_composition_dag",
        "typed_tmkarp_program_indexed_composition_dag",
    }
)
_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.AuthoringSources"
)
_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources"
)
_PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES = frozenset(
    {"program_indexed_executable"}
)
_PROGRAM_INDEXED_PRIMITIVE_CAPABILITIES = frozenset(
    {"program_indexed_primitive"}
)
_PROGRAM_INDEXED_PROGRAM_CAPABILITIES = frozenset(
    {"program_indexed_program"}
)
_PROGRAM_INDEXED_ADMISSION_CAPABILITIES = frozenset(
    {"program_indexed_coherence_direct_tm"}
)
_PROGRAM_INDEXED_SEMANTIC_CAPABILITIES = frozenset(
    {"program_indexed_semantic_iff"}
)
_PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES = frozenset(
    {"program_indexed_composed_program"}
)
_PROGRAM_INDEXED_COMPOSED_SEMANTIC_CAPABILITIES = frozenset(
    {"program_indexed_composed_semantic_iff"}
)
_PROGRAM_INDEXED_TASK_CLASS = "typed_program_indexed_admission_dag"
_PROGRAM_INDEXED_TASK_CLASSES = frozenset(
    {
        _PROGRAM_INDEXED_TASK_CLASS,
        "typed_tmkarp_program_indexed_composition_dag",
    }
)
_PROGRAM_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.ProgramAuthoringSources"
)
_PROGRAM_INDEXED_PACKET_NAMESPACE = (
    _PROGRAM_INDEXED_ADMISSION_MODULE + ".ProgramIndexedAdmissionPacket"
)
_GADGET_INDEXED_TASK_CLASS = "typed_gadget_indexed_admission_dag"
_GADGET_INDEXED_ADMISSION_MODULE = (
    "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources"
)
_GADGET_INDEXED_PACKET_NAMESPACE = (
    _GADGET_INDEXED_ADMISSION_MODULE + ".GadgetIndexedAdmissionPacket"
)
_GADGET_INDEXED_CAPABILITIES = frozenset(
    {
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
    }
)
_SEMANTIC_IFF_CAPABILITIES = frozenset(
    {
        "semantic_proof",
        "semantic_iff",
        *_TMKARP_SEMANTIC_IFF_CAPABILITIES,
        *_DEPENDENT_COMPOSED_SEMANTIC_IFF_CAPABILITIES,
        *_PROGRAM_INDEXED_SEMANTIC_CAPABILITIES,
        *_PROGRAM_INDEXED_COMPOSED_SEMANTIC_CAPABILITIES,
        "gadget_composed_semantic_iff",
    }
)
_SEMANTIC_FORWARD_CAPABILITIES = frozenset(
    {"semantic_forward", "semantic_forward_implication"}
)
_SEMANTIC_REVERSE_CAPABILITIES = frozenset(
    {"semantic_reverse", "semantic_reverse_implication"}
)
_SEMANTIC_CAPABILITIES = frozenset(
    {
        *_SEMANTIC_IFF_CAPABILITIES,
        *_SEMANTIC_FORWARD_CAPABILITIES,
        *_SEMANTIC_REVERSE_CAPABILITIES,
        "mapping_invariant",
    }
)

NP_HARD_NODE_SYSTEM_PROMPT = """\
You are an untrusted Lean 4 author. Return exactly one JSON object and no
markdown. The request freezes one source-to-target capability node, its exact
type, dependencies, endpoints, declaration, imports, and primitive allowlist.
Submit only the replacement term body for that declaration. Do not emit an
import, namespace, declaration, command, sorry, admit, axiom, unsafe code,
hidden benchmark material, or a reverse reduction. Lean compilation, fresh
Core reconstruction, the axiom gate, and independent replay are the only
authorities. For proof obligations, try the smallest definitional proof
(`by intro input; rfl`) before adding rewrites. If a semantic goal is hidden
behind `PresentedProblem.accepts`, use `change` to expose the pointwise
proposition; do not pass `.accepts` functions themselves as simp theorems.
Then use `constructor`, preserve the forward hypothesis, and project the
backward conjunction when that is what the exposed definition requires.
For a `reduction_executable` node, return an ordinary function matching the
exact arrow type (usually `fun input => ...`), never a `PolyProg`. For a
`poly_program` or `representation_adapter` node, return a `PolyProg` term.
For a Boolean-tag representation adapter from a base problem to a product
target, use the public source representation with `PolyProg.pair`, a constant
false tag, and identity payload. For `semantic_forward` and
`semantic_reverse`, prove only the requested implication and preserve its
source-to-target direction. A `semantic_iff` node should combine the already
accepted forward and reverse declarations; it must not silently replace them.
For a typed TM-Karp admission DAG, the observed `TMKarpReduction` is a
read-only source witness, not an already-authored V2 route. Build only the
active layer: `tmkarp_primitive` must use `Primitive.ofTMPolyTime witness.f
witness.polytime`; `tmkarp_program` must wrap the accepted primitive with
`PolyProg.atom`; and `tmkarp_semantic_iff` must reindex `witness.correct` to
the accepted program. Do not reuse an existing `CertifiedReduction`, final
route, registry path, or hardness theorem in place of these authored layers.
For a dependent composition DAG, the second observer-bound witness is only
the public successor `CertifiedReduction` from the frozen intermediate to the
requested target. `dependent_composed_program` must compose
`successor.program` after the accepted TM-Karp admission program.
`dependent_composed_semantic_iff` must chain the accepted admission semantic
iff with `successor.correct` at the admitted intermediate output. It must not
use the successor alone as a source-to-final route or substitute another final
route/hardness theorem.
For program composition, use
only the public primitives in the request and remember that Lean's composition
constructor is `PolyProg.comp after before`, so the output type of `before`
must be the input type of `after`. For program synthesis, inspect the exact
source/target representations and use the explicit constructor signatures in
the request; in particular, `PolyProg.const` takes both the source and target
encodings before its value. Prefer these public `PolyProg` constructors over
opaque code.
For `whole_reduction_synthesis`, no source-to-target capability is preinstalled:
author the executable and its exact `TMPolyTimeMap` evidence from the public
problem definitions. The runner will then bind them into one `Primitive`, one
`PolyProg.atom`, and separate forward/reverse semantic proofs. Do not search for
or reuse a hidden route; the point of this task is to construct the missing edge.
If the request contains a non-null `recommended_first_body`, copy that body
unchanged into the response template on the first attempt. It was derived only
from the public exact type, public source semantics, and allowlisted primitive
signatures. Invent a different body only after Lean rejects that exact body.
Every repair must respond to the supplied Lean diagnostic and must not repeat
the rejected body.
"""

_POLY_PROG_API_REFERENCE = {
    "primitive_of_tm_polytime": (
        "Program.Primitive.ofTMPolyTime (run : source.Carrier -> target.Carrier) "
        "(proof : TMPolyTimeMap source.encodedType target.encodedType run) : "
        "Program.Primitive source target"
    ),
    "atom": (
        "PolyProg.atom (primitive : Program.Primitive source target) : "
        "PolyProg source target"
    ),
    "comp": (
        "PolyProg.comp (after : PolyProg middle target) "
        "(before : PolyProg source middle) : PolyProg source target"
    ),
    "id": (
        "PolyProg.id (presentation : LawfulEncodedType) : "
        "PolyProg presentation presentation"
    ),
    "const": (
        "PolyProg.const (source target : LawfulEncodedType) "
        "(value : target.Carrier) : PolyProg source target"
    ),
    "pair": (
        "PolyProg.pair (first : PolyProg source left) "
        "(second : PolyProg source right) : "
        "PolyProg source (StandardInstances.prod left right)"
    ),
    "run_comp": "(PolyProg.comp after before).run input = after.run (before.run input)",
    "run_const": "(PolyProg.const source target value).run input = value",
    "run_id": "(PolyProg.id presentation).run input = input",
    "run_pair": "(PolyProg.pair first second).run input = (first.run input, second.run input)",
}

_CAPABILITY_GUIDANCE = {
    "reduction_executable": (
        "Return an ordinary lambda matching the exact A -> B type. Inspect the "
        "public source and target instance definitions and implement the actual "
        "source-to-target transformation; do not return or run a PolyProg."
    ),
    "direct_tm": (
        "Prove TMPolyTimeMap for exactly the accepted reduction_executable. Build "
        "the proof from public TMPolyTimeMap constructors and library lemmas; the "
        "function argument and both encoded endpoint types are frozen by the goal."
    ),
    "reduction_primitive": (
        "Bind exactly the accepted executable and direct_tm dependencies with "
        "Program.Primitive.ofTMPolyTime. Do not substitute a different function "
        "or an existing route primitive."
    ),
    "poly_program": (
        "Return only a PolyProg term. For a product target, use PolyProg.pair; "
        "a standard Boolean-tagging shape is `PolyProg.pair "
        "(PolyProg.const sourceEncoding StandardInstances.bool false) "
        "(PolyProg.id sourceEncoding)`. Never place `.run` applications inside "
        "the value argument of PolyProg.const."
    ),
    "representation_adapter": (
        "Return only the typed PolyProg adapter required by the exact node type. "
        "For the public base-to-Boolean-tag representation shape, preserve the "
        "payload with PolyProg.id and add the false tag with PolyProg.const, "
        "combined by PolyProg.pair. Do not reverse the adapter with PolyProg.snd."
    ),
    "program_run_coherence": (
        "Prove the accepted program and executable agree pointwise. First try "
        "`by intro input; rfl`; otherwise rewrite only with accepted dependencies "
        "and the public PolyProg run equations."
    ),
    "mapping_invariant": (
        "Rewrite with the accepted run-coherence declaration, unfold/change the "
        "public invariant, and prove the resulting conjunction/equalities."
    ),
    "semantic_proof": (
        "Keep the exact source-to-target iff direction. Never project fields from "
        "the source input merely because the target output is a product. Normalize "
        "the program run first, then use `change` on the full iff."
    ),
    "semantic_iff": (
        "Build the exact source-to-target iff from the accepted forward and reverse "
        "implication declarations. Apply each dependency at the same input; do not "
        "re-prove, swap, or weaken either direction."
    ),
    "semantic_forward": (
        "Prove only source acceptance implies target acceptance for the exact "
        "accepted program run. Keep the input fixed and preserve the hypothesis; "
        "for a definitionally transparent adapter, `exact accepted` may close it."
    ),
    "semantic_reverse": (
        "Prove only target acceptance of the exact accepted program run implies "
        "source acceptance. Keep the input fixed and preserve the hypothesis; "
        "for a definitionally transparent adapter, `exact accepted` may close it."
    ),
    "tmkarp_primitive": (
        "Admit exactly the public observer-bound TMKarpReduction executable as a "
        "new V2 Primitive. Use `Primitive.ofTMPolyTime witness.f witness.polytime`; "
        "do not reuse a pre-existing Primitive, CertifiedReduction, or final route."
    ),
    "tmkarp_program": (
        "Wrap exactly the accepted tmkarp_primitive dependency with `PolyProg.atom`. "
        "Do not inline an unrelated primitive or reuse an existing route program."
    ),
    "tmkarp_semantic_iff": (
        "Reindex exactly the observer-bound `witness.correct` theorem to the "
        "accepted tmkarp_program run. Do not replace it with correctness from an "
        "existing CertifiedReduction or registry route."
    ),
    "dependent_composed_program": (
        "Compose exactly the observer-bound successor certificate program after "
        "the accepted tmkarp_program dependency with `PolyProg.comp after before`. "
        "The successor alone is not a source-to-final program."
    ),
    "dependent_composed_semantic_iff": (
        "Chain exactly the accepted tmkarp_semantic_iff with the observer-bound "
        "successor certificate's `correct` theorem at the admitted program output. "
        "Do not re-prove the first segment or reuse another final route."
    ),
    "program_indexed_executable": (
        "Re-export only the executable projection of the observer-bound public "
        "packet; do not read a template marker or reuse a route."
    ),
    "program_indexed_primitive": (
        "Build the primitive from the accepted executable and the packet's "
        "dependent direct-TM projection through the allowlisted packet helper."
    ),
    "program_indexed_program": (
        "Embed exactly the accepted primitive as the one-atom final PolyProg."
    ),
    "program_indexed_coherence_direct_tm": (
        "Close the typed packet admission gate for the accepted program; it must "
        "carry both compiled direct-TM evidence and run coherence."
    ),
    "program_indexed_semantic_iff": (
        "Reindex only the packet semantic theorem through the accepted program "
        "admission gate; do not borrow a CertifiedReduction or hardness route."
    ),
    "gadget_reference_audit": (
        "Re-export exactly the packet-owned source/reference invariant. This is "
        "the first mathematical checkpoint and must not be replaced by True."
    ),
    "gadget_normalization_audit": (
        "Admit exactly the packet-owned normalization invariant after the accepted "
        "reference audit; keep the dependency explicit."
    ),
    "gadget_executable": (
        "Re-export the packet gadget executable only through both accepted audit "
        "checkpoints; do not reuse a raw source-to-target reduction."
    ),
    "gadget_parameter_audit": (
        "Reindex the packet parameter/size invariant to the accepted executable."
    ),
    "gadget_semantic_forward": (
        "Reindex only the packet's forward gadget implication to the accepted "
        "executable and parameter audit."
    ),
    "gadget_semantic_reverse": (
        "Reindex only the packet's reverse gadget implication to the accepted "
        "executable and parameter audit."
    ),
    "gadget_direct_tm": (
        "Reindex the packet direct-TM evidence after the accepted parameter and "
        "two semantic checkpoints."
    ),
    "gadget_program": (
        "Assemble the exact one-atom gadget program from the accepted executable "
        "and direct-TM evidence."
    ),
    "gadget_composed_program": (
        "Compose the packet-owned source normalization with exactly the accepted "
        "gadget program."
    ),
    "gadget_composed_semantic_iff": (
        "Close the source-to-target iff only from the accepted directional gadget "
        "proofs and the exact authored gadget/composed programs."
    ),
}

# Planner reports use the longer names for derived, non-editable projections;
# accepting both names keeps prompt construction explicit when such a node is
# promoted to an editable obligation by a future task schema.
_CAPABILITY_GUIDANCE["semantic_forward_implication"] = _CAPABILITY_GUIDANCE[
    "semantic_forward"
]
_CAPABILITY_GUIDANCE["semantic_reverse_implication"] = _CAPABILITY_GUIDANCE[
    "semantic_reverse"
]

_PROOF_RECIPES = {
    "definitionally_equal": "`by\n  intro input\n  rfl`",
    "false_tag": (
        "For the detected public false-tag wrapper, prefer this shape exactly: "
        "`by\n  intro input\n  change hub.accepts input ↔ "
        "(if false = Bool.true then False else hub.accepts input)\n  rfl`."
    ),
    "conjunction_identity": (
        "For the detected public conjunction wrapper, prefer this shape exactly: "
        "`by\n  intro input\n  change hub.accepts input ↔ false = false ∧ "
        "hub.accepts input\n  exact ⟨fun accepted => ⟨rfl, accepted⟩, "
        "fun accepted => accepted.2⟩`."
    ),
    "mapping_product_identity": (
        "For the detected public mapping invariant, prefer: `by\n  intro input\n  "
        "change false = false ∧ input = input\n  exact ⟨rfl, rfl⟩`."
    ),
    "run_coherence_rfl": "`by\n  intro input\n  rfl`",
    "representation_adapter_false_tag": (
        "For a base-to-Boolean-tag target, use `PolyProg.pair "
        "(PolyProg.const source.representation StandardInstances.bool false) "
        "(PolyProg.id source.representation)`. This preserves the payload and "
        "does not reverse the required reduction."
    ),
    "semantic_forward_identity": (
        "For a definitionally transparent adapter, prefer "
        "`by\n  intro input accepted\n  exact accepted`."
    ),
    "semantic_reverse_identity": (
        "For a definitionally transparent adapter, prefer "
        "`by\n  intro input accepted\n  exact accepted`."
    ),
    "semantic_iff_from_implications": (
        "Apply the accepted forward and reverse declarations to the same input, "
        "then return them with `Iff.intro`/`\u27e8_, _\u27e9`."
    ),
    "tmkarp_primitive_admission": (
        "Use exactly `Primitive.ofTMPolyTime witness.f witness.polytime`, where "
        "the witness is the public exact-endpoint TMKarpReduction in the request."
    ),
    "tmkarp_program_atom": (
        "Use exactly `PolyProg.atom acceptedPrimitive`; the accepted primitive "
        "declaration is the sole executable authority for this node."
    ),
    "tmkarp_semantic_correct": (
        "After unfolding or changing only the accepted generated layers, close "
        "the exact iff with `witness.correct input`."
    ),
    "dependent_program_comp": (
        "Use exactly `PolyProg.comp successor.program admittedProgram`; composition "
        "order is after-then-before in the constructor arguments."
    ),
    "dependent_semantic_trans": (
        "Use the accepted admission iff at `input`, then `.trans` the successor "
        "certificate correctness at `admittedProgram.run input`."
    ),
    "composition_order": (
        "Never swap execution: `(PolyProg.comp after before).run input` is "
        "`after.run (before.run input)`."
    ),
    "namespace_rule": (
        "Public short names are available from the opened target module; otherwise "
        "use their fully-qualified declarations. Do not invent a public "
        "`composedProgram` that is absent from the supplied source."
    ),
}


def _selected_proof_recipes(
    *, capability: str, public_sources: Mapping[str, str]
) -> dict[str, str]:
    """Select a small public-semantics recipe set without consulting gold data."""

    public_text = "\n".join(public_sources.values())
    common = {
        "composition_order": _PROOF_RECIPES["composition_order"],
        "namespace_rule": _PROOF_RECIPES["namespace_rule"],
    }
    if capability in _DEPENDENT_COMPOSED_SEMANTIC_IFF_CAPABILITIES:
        return {
            "dependent_semantic_trans": _PROOF_RECIPES[
                "dependent_semantic_trans"
            ],
            **common,
        }
    if capability in _TMKARP_SEMANTIC_IFF_CAPABILITIES:
        return {
            "tmkarp_semantic_correct": _PROOF_RECIPES[
                "tmkarp_semantic_correct"
            ],
            **common,
        }
    if capability in _SEMANTIC_IFF_CAPABILITIES:
        if "then False else hub.accepts" in public_text:
            selected = "false_tag"
        elif "input.1 = false ∧" in public_text:
            selected = "conjunction_identity"
        else:
            selected = "definitionally_equal"
        recipes = {selected: _PROOF_RECIPES[selected]}
        if capability == "semantic_iff":
            recipes["semantic_iff_from_implications"] = _PROOF_RECIPES[
                "semantic_iff_from_implications"
            ]
        return {**recipes, **common}
    if capability in _SEMANTIC_FORWARD_CAPABILITIES:
        return {
            "semantic_forward_identity": _PROOF_RECIPES[
                "semantic_forward_identity"
            ],
            **common,
        }
    if capability in _SEMANTIC_REVERSE_CAPABILITIES:
        return {
            "semantic_reverse_identity": _PROOF_RECIPES[
                "semantic_reverse_identity"
            ],
            **common,
        }
    if capability == "representation_adapter":
        return {
            "representation_adapter_false_tag": _PROOF_RECIPES[
                "representation_adapter_false_tag"
            ],
            **common,
        }
    if capability == "mapping_invariant":
        return {
            "mapping_product_identity": _PROOF_RECIPES["mapping_product_identity"],
            **common,
        }
    if capability == "program_run_coherence":
        return {
            "run_coherence_rfl": _PROOF_RECIPES["run_coherence_rfl"],
            **common,
        }
    if capability in _TMKARP_PRIMITIVE_CAPABILITIES:
        return {
            "tmkarp_primitive_admission": _PROOF_RECIPES[
                "tmkarp_primitive_admission"
            ],
            **common,
        }
    if capability in _TMKARP_PROGRAM_CAPABILITIES:
        return {
            "tmkarp_program_atom": _PROOF_RECIPES["tmkarp_program_atom"],
            **common,
        }
    if capability in _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES:
        return {
            "dependent_program_comp": _PROOF_RECIPES["dependent_program_comp"],
            **common,
        }
    return common


def _observed_capability_terms(task: NPHardAuthoringTaskV2) -> dict[str, Any]:
    observed = getattr(task, "observed_capability_terms", ())
    if isinstance(observed, Mapping):
        return dict(observed)
    try:
        return dict(observed)
    except (TypeError, ValueError):
        return {}


def _observed_capability_exact_types(
    task: NPHardAuthoringTaskV2,
) -> dict[str, Any]:
    observed = getattr(task, "observed_capability_exact_types", ())
    if isinstance(observed, Mapping):
        return dict(observed)
    try:
        return dict(observed)
    except (TypeError, ValueError):
        return {}


def _observed_capability_term(
    *, task: NPHardAuthoringTaskV2, node: NPHardAuthoringObligationV2
) -> str | None:
    """Read a public observer witness from old or new task serializations."""

    observed = _observed_capability_terms(task)
    candidate: Any = observed.get(node.node_id)
    if not isinstance(candidate, str) or not candidate.strip():
        return None
    _assert_public(candidate, label="observed capability term")
    return candidate.strip()


def _tmkarp_admission_source(task: NPHardAuthoringTaskV2) -> dict[str, str]:
    """Resolve one immutable public TMKarp witness without target-name routing."""

    task_class = getattr(task, "task_class", None)
    if task_class not in _TMKARP_ADMISSION_TASK_CLASSES:
        _fail(
            "candidate_dependency_stale",
            "TMKarp admission source requested for a different task class",
        )
    primitive_nodes = tuple(
        node
        for node in task.gap_nodes
        if node.capability in _TMKARP_PRIMITIVE_CAPABILITIES
    )
    if len(primitive_nodes) != 1:
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp admission DAG must expose one primitive node",
        )
    primitive = primitive_nodes[0]
    witness = _observed_capability_term(task=task, node=primitive)
    observed_terms = _observed_capability_terms(task)
    exact_types = _observed_capability_exact_types(task)
    exact_type = exact_types.get(primitive.node_id)
    if witness is None or not isinstance(exact_type, str) or not exact_type.strip():
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp admission lacks its Lean-observed witness or exact type",
        )
    expected_observed_nodes = {primitive.node_id}
    if task_class == "typed_tmkarp_dependent_composition_dag":
        successor_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES
        )
        if len(successor_nodes) != 1:
            _fail(
                "candidate_dependency_stale",
                "dependent composition DAG must expose one composed program node",
            )
        expected_observed_nodes.add(successor_nodes[0].node_id)
    elif task_class == "typed_tmkarp_program_indexed_composition_dag":
        packet_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES
        )
        if len(packet_nodes) != 1:
            _fail(
                "candidate_dependency_stale",
                "TMKarp/program-indexed DAG must expose one packet executable node",
            )
        expected_observed_nodes.add(packet_nodes[0].node_id)
    if set(observed_terms) != expected_observed_nodes or set(
        exact_types
    ) != expected_observed_nodes:
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp observer bindings do not match the exact editable source nodes",
        )
    _assert_public(exact_type, label="observed capability exact type")
    admission_target = (
        task.target_problem.term
        if task_class == "typed_tmkarp_admission_dag"
        else _composition_intermediate_payload(task)["term"]
    )
    expected_tmkarp_endpoints = (
        task.source_problem.term + ".toEncodedDecisionProblem",
        admission_target + ".toEncodedDecisionProblem",
    )
    if _exact_tmkarp_reduction_endpoints_v2(exact_type) != (
        expected_tmkarp_endpoints
    ):
        _fail(
            "candidate_exact_type_mismatch",
            "typed TMKarp observer exact type is not the exact ordered admission reduction",
        )
    if witness.startswith(_TMKARP_ADMISSION_MODULE + "."):
        admission_module = _TMKARP_ADMISSION_MODULE
    elif (
        task_class == "typed_tmkarp_dependent_composition_dag"
        and witness.startswith(_SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE + ".")
    ):
        admission_module = _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
    else:
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp witness escaped its closed admission authority",
        )
    dependencies = dict(task.dependency_hashes)
    if (
        admission_module not in task.allowed_imports
        or f"module:{admission_module}" not in dependencies
    ):
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp admission module is not fully content addressed",
        )
    if task_class == "typed_tmkarp_dependent_composition_dag":
        intermediate = _composition_intermediate_payload(task)
        successor_module = getattr(task, "composition_successor_module", None)
        if not isinstance(successor_module, str) or not (
            _staged_authoring_surface_is_exact_v2(
                allowed_imports=task.allowed_imports,
                public_source_files=task.public_source_files,
                dependency_hashes=task.dependency_hashes,
                source_module=task.source_problem.module,
                target_module=task.target_problem.module,
                intermediate_module=intermediate["module"],
                authority_modules=(successor_module, admission_module),
            )
        ):
            _fail(
                "candidate_outside_edit_boundary",
                "dependent TMKarp runtime surface differs from its exact authority closure",
            )
    if (
        admission_module == _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE
        and "content:lean-successor-only-tmkarp-admission" not in dependencies
    ):
        _fail(
            "candidate_dependency_stale",
            "successor-only TMKarp admission lacks its dedicated content binding",
        )
    return {
        "node_id": primitive.node_id,
        "witness": witness,
        "exact_type": exact_type.strip(),
        "module": admission_module,
    }


def _composition_intermediate_payload(
    task: NPHardAuthoringTaskV2,
) -> dict[str, str]:
    intermediate = getattr(task, "composition_intermediate", None)
    if intermediate is None:
        _fail(
            "candidate_dependency_stale",
            "dependent composition task lacks its exact intermediate endpoint",
        )
    if isinstance(intermediate, Mapping):
        payload = dict(intermediate)
    elif hasattr(intermediate, "to_dict"):
        payload = dict(intermediate.to_dict())
    else:
        payload = {
            "module": getattr(intermediate, "module", None),
            "term": getattr(intermediate, "term", None),
        }
    if set(payload) != {"module", "term"} or not all(
        isinstance(payload[key], str) and payload[key].strip()
        for key in ("module", "term")
    ):
        _fail(
            "candidate_dependency_stale",
            "dependent composition intermediate endpoint is invalid",
        )
    for value in payload.values():
        _assert_public(value, label="composition intermediate endpoint")
    return {key: payload[key].strip() for key in ("module", "term")}


def _dependent_composition_successor(
    task: NPHardAuthoringTaskV2,
) -> dict[str, str]:
    """Resolve the one public middle-to-target CertifiedReduction witness."""

    if getattr(task, "task_class", None) != "typed_tmkarp_dependent_composition_dag":
        _fail(
            "candidate_dependency_stale",
            "dependent successor requested for a different task class",
        )
    composed_nodes = tuple(
        node
        for node in task.gap_nodes
        if node.capability in _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES
    )
    if len(composed_nodes) != 1:
        _fail(
            "candidate_dependency_stale",
            "dependent composition DAG must expose one composed program node",
        )
    node = composed_nodes[0]
    witness = _observed_capability_term(task=task, node=node)
    exact_type = _observed_capability_exact_types(task).get(node.node_id)
    if witness is None or not isinstance(exact_type, str) or not exact_type.strip():
        _fail(
            "candidate_dependency_stale",
            "dependent composition lacks its observer-bound successor witness",
        )
    _assert_public(exact_type, label="dependent successor exact type")
    successor_module = getattr(task, "composition_successor_module", None)
    if not isinstance(successor_module, str) or not successor_module.strip():
        _fail(
            "candidate_dependency_stale",
            "dependent composition lacks its observer-bound successor module",
        )
    successor_module = successor_module.strip()
    _assert_public(successor_module, label="dependent successor module")
    if not _certified_successor_witness_owned_by_module_v2(
        witness=witness, successor_module=successor_module
    ):
        _fail(
            "fabricated_declaration_handle",
            "dependent successor witness is not owned by its observer-bound Lean module",
        )
    intermediate = _composition_intermediate_payload(task)
    admission = _tmkarp_admission_source(task)
    dependencies = dict(task.dependency_hashes)
    if (
        successor_module not in task.allowed_imports
        or dependencies.get("content:observed-capability-module:composed-program")
        != sha256_id(successor_module)
        or f"module:{successor_module}" not in dependencies
    ):
        _fail(
            "candidate_dependency_stale",
            "dependent successor module is not fully content addressed",
        )
    if admission["module"] == _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE:
        successor_source = getattr(task, "composition_successor_source", None)
        successor_target = getattr(task, "composition_successor_target", None)
        admission_observation = _observer_capability_record_payload_v2(
            getattr(task, "composition_admission_observation", None)
        )
        successor_observation = _observer_capability_record_payload_v2(
            getattr(task, "composition_successor_observation", None)
        )
        if admission_observation is None or successor_observation is None:
            _fail(
                "candidate_dependency_stale",
                "successor-only runtime lacks complete Lean observer records",
            )
        if (successor_source, successor_target) != (
            intermediate["term"],
            task.target_problem.term,
        ):
            _fail(
                "candidate_wrong_endpoint",
                "successor-only canonical successor endpoints differ from the task chain",
            )
        if _exact_certified_reduction_endpoints_v2(exact_type) != (
            successor_source,
            successor_target,
        ):
            _fail(
                "candidate_exact_type_mismatch",
                "successor-only chain lacks one canonical ordered successor type",
            )
        expected_admission_record = {
            "capability_kind": "forward_successor_only_tmkarp_admission",
            "source": task.source_problem.term,
            "target": intermediate["term"],
            "witness": admission["witness"],
            "exact_type": admission["exact_type"],
            "module": admission["module"],
            "authority": "lean_exact_successor_only_tmkarp_shared_source",
        }
        expected_successor_record = {
            "capability_kind": "forward_certified_successor",
            "source": successor_source,
            "target": successor_target,
            "witness": witness,
            "exact_type": exact_type,
            "module": successor_module,
            "authority": "lean_registry_exact_certified_successor",
        }
        if any(
            admission_observation[key] != value
            for key, value in expected_admission_record.items()
        ) or any(
            successor_observation[key] != value
            for key, value in expected_successor_record.items()
        ):
            _fail(
                "candidate_dependency_stale",
                "successor-only runtime facts differ from their Lean observer rows",
            )
        if (
            admission_observation["target_node"]
            != successor_observation["source_node"]
            or admission_observation["registry_fingerprint"]
            != successor_observation["registry_fingerprint"]
        ):
            _fail(
                "candidate_wrong_endpoint",
                "successor-only observer rows do not form one exact runtime chain",
            )
        if dependencies.get(
            "content:lean-registry-fingerprint"
        ) != sha256_id(admission_observation["registry_fingerprint"]):
            _fail(
                "candidate_dependency_stale",
                "successor-only runtime observer fingerprint binding is stale",
            )
        expected_chain = _successor_only_observer_chain_payload_v2(
            admission=admission_observation,
            successor=successor_observation,
            canonical_successor_source=successor_source,
            canonical_successor_target=successor_target,
        )
        for binding, payload in (
            (
                "content:lean-successor-only-tmkarp-admission",
                admission_observation,
            ),
            ("content:lean-certified-successor", successor_observation),
            ("content:lean-typed-capability-chain", expected_chain),
        ):
            if dependencies.get(binding) != sha256_id(payload):
                _fail(
                    "candidate_dependency_stale",
                    "successor-only runtime observer content binding is stale",
                )
        for binding, endpoint in (
            (
                "content:observed-composition-successor-source",
                successor_source,
            ),
            (
                "content:observed-composition-successor-target",
                successor_target,
            ),
        ):
            if dependencies.get(binding) != sha256_id(endpoint):
                _fail(
                    "candidate_dependency_stale",
                    "successor-only canonical endpoint binding is stale",
                )
    else:
        if (
            getattr(task, "composition_successor_source", None) is not None
            or getattr(task, "composition_successor_target", None) is not None
            or getattr(task, "composition_admission_observation", None) is not None
            or getattr(task, "composition_successor_observation", None) is not None
        ):
            _fail(
                "candidate_dependency_stale",
                "legacy dependent task carries unrelated successor-only bindings",
            )
        normalized_successor_endpoints = (
            _normalized_certified_successor_exact_endpoints_v2(
                exact_type=exact_type,
                witness=witness,
                successor_module=successor_module,
                expected_source=intermediate["term"],
                expected_target=task.target_problem.term,
            )
        )
        if normalized_successor_endpoints != (
            intermediate["term"],
            task.target_problem.term,
        ):
            _fail(
                "candidate_exact_type_mismatch",
                "dependent successor exact type is not the ordered intermediate-to-target CertifiedReduction",
            )
    if witness == admission["witness"]:
        _fail(
            "candidate_wrong_endpoint",
            "dependent successor collapsed into the raw admission witness",
        )
    return {
        "node_id": node.node_id,
        "witness": witness,
        "exact_type": exact_type.strip(),
        "module": successor_module,
        "intermediate_module": intermediate["module"],
        "intermediate_term": intermediate["term"],
    }


def _program_indexed_admission_source(
    task: NPHardAuthoringTaskV2,
) -> dict[str, str]:
    """Resolve one immutable public packet without target-name routing."""

    task_class = getattr(task, "task_class", None)
    if task_class not in {
        _PROGRAM_INDEXED_TASK_CLASS,
        "typed_tmkarp_program_indexed_composition_dag",
    }:
        _fail(
            "candidate_dependency_stale",
            "program-indexed packet requested for a different task class",
        )
    executable_nodes = tuple(
        node
        for node in task.gap_nodes
        if node.capability in _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES
    )
    if len(executable_nodes) != 1:
        _fail(
            "candidate_dependency_stale",
            "program-indexed DAG must expose one executable node",
        )
    node = executable_nodes[0]
    witness = _observed_capability_term(task=task, node=node)
    exact_type = _observed_capability_exact_types(task).get(node.node_id)
    if witness is None or not isinstance(exact_type, str) or not exact_type.strip():
        _fail(
            "candidate_dependency_stale",
            "program-indexed DAG lacks its observer-bound packet or exact type",
        )
    observed_terms = _observed_capability_terms(task)
    exact_types = _observed_capability_exact_types(task)
    expected_nodes = (
        {node.node_id}
        if task_class == _PROGRAM_INDEXED_TASK_CLASS
        else {"tmkarp-primitive", node.node_id}
    )
    if set(observed_terms) != expected_nodes or set(exact_types) != expected_nodes:
        _fail(
            "candidate_dependency_stale",
            "program-indexed observer bindings differ from the executable source node",
        )
    if not witness.startswith(_PROGRAM_INDEXED_ADMISSION_MODULE + "."):
        _fail(
            "candidate_dependency_stale",
            "program-indexed packet escaped its closed public source module",
        )
    _assert_public(exact_type, label="program-indexed packet exact type")
    if "ProgramIndexedAdmissionPacket" not in exact_type:
        _fail(
            "candidate_exact_type_mismatch",
            "program-indexed witness exact type is not an admission packet",
        )
    dependencies = dict(task.dependency_hashes)
    if (
        _PROGRAM_INDEXED_ADMISSION_MODULE not in task.allowed_imports
        or f"module:{_PROGRAM_INDEXED_ADMISSION_MODULE}" not in dependencies
    ):
        _fail(
            "candidate_dependency_stale",
            "program-indexed packet module is not fully content addressed",
        )
    return {
        "node_id": node.node_id,
        "witness": witness,
        "exact_type": exact_type.strip(),
        "module": _PROGRAM_INDEXED_ADMISSION_MODULE,
    }


def _gadget_indexed_admission_source(
    task: NPHardAuthoringTaskV2,
) -> dict[str, str]:
    """Resolve one immutable three-endpoint gadget packet by kind and type."""

    if getattr(task, "task_class", None) != _GADGET_INDEXED_TASK_CLASS:
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed packet requested for a different task class",
        )
    reference_nodes = tuple(
        node
        for node in task.gap_nodes
        if node.capability == "gadget_reference_audit"
    )
    if len(reference_nodes) != 1:
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed DAG must expose one reference-audit binding node",
        )
    node = reference_nodes[0]
    witness = _observed_capability_term(task=task, node=node)
    exact_type = _observed_capability_exact_types(task).get(node.node_id)
    if witness is None or not isinstance(exact_type, str) or not exact_type.strip():
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed DAG lacks its observer-bound packet or exact type",
        )
    if set(_observed_capability_terms(task)) != {node.node_id} or set(
        _observed_capability_exact_types(task)
    ) != {node.node_id}:
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed observer bindings differ from the reference-audit node",
        )
    if not witness.startswith(_GADGET_INDEXED_ADMISSION_MODULE + "."):
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed packet escaped its closed public source module",
        )
    _assert_public(exact_type, label="gadget-indexed packet exact type")
    intermediate = _composition_intermediate_payload(task)
    if not _staged_authoring_surface_is_exact_v2(
        allowed_imports=task.allowed_imports,
        public_source_files=task.public_source_files,
        dependency_hashes=task.dependency_hashes,
        source_module=task.source_problem.module,
        target_module=task.target_problem.module,
        intermediate_module=intermediate["module"],
        authority_modules=(_GADGET_INDEXED_ADMISSION_MODULE,),
    ):
        _fail(
            "candidate_outside_edit_boundary",
            "gadget-indexed runtime surface differs from its exact packet closure",
        )
    if _exact_gadget_packet_endpoints_v2(exact_type) != (
        task.source_problem.term,
        intermediate["term"],
        task.target_problem.term,
    ):
        _fail(
            "candidate_exact_type_mismatch",
            "gadget-indexed packet does not bind the task's ordered endpoints",
        )
    dependencies = dict(task.dependency_hashes)
    if (
        _GADGET_INDEXED_ADMISSION_MODULE not in task.allowed_imports
        or f"module:{_GADGET_INDEXED_ADMISSION_MODULE}" not in dependencies
        or "content:lean-gadget-indexed-packet" not in dependencies
    ):
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed packet module is not fully content addressed",
        )
    return {
        "node_id": node.node_id,
        "witness": witness,
        "exact_type": exact_type.strip(),
        "module": _GADGET_INDEXED_ADMISSION_MODULE,
        "reference_module": intermediate["module"],
        "reference_term": intermediate["term"],
    }


def _canonical_lean_body(body: str) -> str:
    return " ".join(body.strip().split())


def _validate_tmkarp_patch_binding(
    *, task: NPHardAuthoringTaskV2, request: NPHardNodeRequestV1, body: str
) -> None:
    """Keep each admission edit on its observer/dependency-derived constructor."""

    task_class = getattr(task, "task_class", None)
    if task_class not in _TMKARP_ADMISSION_TASK_CLASSES:
        return
    allowed_capabilities = (
        _TMKARP_PRIMITIVE_CAPABILITIES
        | _TMKARP_PROGRAM_CAPABILITIES
        | _TMKARP_SEMANTIC_IFF_CAPABILITIES
    )
    if (
        task_class == "typed_tmkarp_program_indexed_composition_dag"
        and request.node.capability not in allowed_capabilities
    ):
        return
    if task_class == "typed_tmkarp_dependent_composition_dag":
        allowed_capabilities |= (
            _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES
            | _DEPENDENT_COMPOSED_SEMANTIC_IFF_CAPABILITIES
        )
    if request.node.capability not in allowed_capabilities:
        _fail(
            "candidate_outside_edit_boundary",
            "typed TMKarp admission exposed an unsupported editable capability",
        )
    forbidden_route_reuse = (
        "CertifiedReduction",
        "NativeTMNPHard",
        "TypedNPHardResult",
        "by_np_hard_resolver",
        "authoredExactNPHardness",
        "finalRoute",
        "authoredTargetResult",
        "ComplexityReduction.Legacy",
        "ComplexityReduction.Karp21.",
    )
    if any(marker in body for marker in forbidden_route_reuse):
        _fail(
            "candidate_outside_edit_boundary",
            "typed TMKarp admission body attempted to reuse a final route or hardness proof",
        )
    expected = _recommended_first_body(
        task=task, request=request, public_sources={}
    )
    if expected is None or _canonical_lean_body(body) != _canonical_lean_body(
        expected
    ):
        _fail(
            "candidate_dependency_stale",
            "typed TMKarp admission body drifted from its exact observer/dependency binding",
        )


def _validate_program_indexed_patch_binding(
    *, task: NPHardAuthoringTaskV2, request: NPHardNodeRequestV1, body: str
) -> None:
    """Bind every packet edit to one observer/dependency-derived constructor."""

    if getattr(task, "task_class", None) not in {
        _PROGRAM_INDEXED_TASK_CLASS,
        "typed_tmkarp_program_indexed_composition_dag",
    }:
        return
    allowed_capabilities = (
        _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES
        | _PROGRAM_INDEXED_PRIMITIVE_CAPABILITIES
        | _PROGRAM_INDEXED_PROGRAM_CAPABILITIES
        | _PROGRAM_INDEXED_ADMISSION_CAPABILITIES
        | _PROGRAM_INDEXED_SEMANTIC_CAPABILITIES
        | _PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES
        | _PROGRAM_INDEXED_COMPOSED_SEMANTIC_CAPABILITIES
    )
    if (
        getattr(task, "task_class", None)
        == "typed_tmkarp_program_indexed_composition_dag"
        and request.node.capability not in allowed_capabilities
    ):
        return
    if request.node.capability not in allowed_capabilities:
        _fail(
            "candidate_outside_edit_boundary",
            "program-indexed DAG exposed an unsupported editable capability",
        )
    forbidden_reuse = (
        "CertifiedReduction",
        "NativeTMNPHard",
        "TypedNPHardResult",
        "by_np_hard_resolver",
        "authoredExactNPHardness",
        "finalRoute",
        "authoredTargetResult",
        "ProgramIndexedReductionTemplate",
        ".template",
        "ComplexityReduction.Legacy",
        "ComplexityReduction.Karp21.",
    )
    if any(marker in body for marker in forbidden_reuse):
        _fail(
            "candidate_outside_edit_boundary",
            "program-indexed body attempted to reuse a template, route, or hardness proof",
        )
    expected = _recommended_first_body(task=task, request=request, public_sources={})
    if expected is None or _canonical_lean_body(body) != _canonical_lean_body(
        expected
    ):
        _fail(
            "candidate_dependency_stale",
            "program-indexed body drifted from its exact packet/dependency binding",
        )


def _validate_gadget_indexed_patch_binding(
    *, task: NPHardAuthoringTaskV2, request: NPHardNodeRequestV1, body: str
) -> None:
    """Keep every gadget edit on its exact packet/dependency constructor."""

    if getattr(task, "task_class", None) != _GADGET_INDEXED_TASK_CLASS:
        return
    if request.node.capability not in _GADGET_INDEXED_CAPABILITIES:
        _fail(
            "candidate_outside_edit_boundary",
            "gadget-indexed DAG exposed an unsupported editable capability",
        )
    forbidden_reuse = (
        "CertifiedReduction",
        "TMKarpReduction",
        "NativeTMNPHard",
        "TypedNPHardResult",
        "by_np_hard_resolver",
        "authoredExactNPHardness",
        "finalRoute",
        "authoredTargetResult",
        "SuccessorAuthoringSources",
        "ComplexityReduction.Legacy",
        "ComplexityReduction.Karp21.",
    )
    if any(marker in body for marker in forbidden_reuse):
        _fail(
            "candidate_outside_edit_boundary",
            "gadget-indexed body attempted to reuse a shortcut, route, or hardness proof",
        )
    expected = _recommended_first_body(task=task, request=request, public_sources={})
    if expected is None or _canonical_lean_body(body) != _canonical_lean_body(
        expected
    ):
        _fail(
            "candidate_dependency_stale",
            "gadget-indexed body drifted from its exact packet/dependency binding",
        )


def _recommended_first_body(
    *,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    public_sources: Mapping[str, str],
) -> str | None:
    """Build a public-shape candidate; the model must still submit the bound patch."""

    capability = request.node.capability
    dependency_nodes = tuple(
        node for node in task.gap_nodes if node.node_id in request.node.depends_on
    )
    if capability in _GADGET_INDEXED_CAPABILITIES:
        packet = _gadget_indexed_admission_source(task)["witness"]
        nodes = {node.capability: node for node in task.gap_nodes}
        if set(_GADGET_INDEXED_CAPABILITIES) - set(nodes):
            _fail(
                "candidate_dependency_stale",
                "gadget-indexed DAG is missing a required exact capability node",
            )
        reference = nodes["gadget_reference_audit"]
        normalization = nodes["gadget_normalization_audit"]
        executable = nodes["gadget_executable"]
        parameter = nodes["gadget_parameter_audit"]
        forward = nodes["gadget_semantic_forward"]
        reverse = nodes["gadget_semantic_reverse"]
        direct_tm = nodes["gadget_direct_tm"]
        gadget_program = nodes["gadget_program"]
        composed_program = nodes["gadget_composed_program"]
        namespace = _GADGET_INDEXED_PACKET_NAMESPACE
        if capability == "gadget_reference_audit":
            if dependency_nodes:
                _fail(
                    "candidate_dependency_stale",
                    "gadget reference audit unexpectedly has an authored dependency",
                )
            return f"by\n  exact {namespace}.toReferenceAudit {packet}"
        if capability == "gadget_normalization_audit":
            if dependency_nodes != (reference,):
                _fail(
                    "candidate_dependency_stale",
                    "gadget normalization audit is not bound to the reference audit",
                )
            return (
                f"by\n  exact {namespace}.toNormalizationAudit {packet} "
                f"{reference.declaration}"
            )
        if capability == "gadget_executable":
            if dependency_nodes != (reference, normalization):
                _fail(
                    "candidate_dependency_stale",
                    "gadget executable is not bound to both normalization audits",
                )
            return (
                f"by\n  exact {namespace}.toGadgetExecutable {packet} "
                f"{reference.declaration} {normalization.declaration}"
            )
        if capability == "gadget_parameter_audit":
            if dependency_nodes != (executable,):
                _fail(
                    "candidate_dependency_stale",
                    "gadget parameter audit is not bound to the executable",
                )
            return (
                f"by\n  exact {namespace}.toParameterAudit {packet} "
                f"{executable.declaration} rfl"
            )
        if capability == "gadget_semantic_forward":
            if dependency_nodes != (executable, parameter):
                _fail(
                    "candidate_dependency_stale",
                    "gadget forward semantic is not bound to executable/parameter audits",
                )
            return (
                f"by\n  exact {namespace}.toSemanticForward {packet} "
                f"{executable.declaration} rfl {parameter.declaration}"
            )
        if capability == "gadget_semantic_reverse":
            if dependency_nodes != (executable, parameter):
                _fail(
                    "candidate_dependency_stale",
                    "gadget reverse semantic is not bound to executable/parameter audits",
                )
            return (
                f"by\n  exact {namespace}.toSemanticReverse {packet} "
                f"{executable.declaration} rfl {parameter.declaration}"
            )
        if capability == "gadget_direct_tm":
            if dependency_nodes != (executable, parameter, forward, reverse):
                _fail(
                    "candidate_dependency_stale",
                    "gadget direct-TM node is not bound to all exact gadget audits",
                )
            return (
                f"by\n  exact {namespace}.toGadgetDirectTM {packet} "
                f"{executable.declaration} rfl {parameter.declaration} "
                f"{forward.declaration} {reverse.declaration}"
            )
        if capability == "gadget_program":
            if dependency_nodes != (executable, direct_tm):
                _fail(
                    "candidate_dependency_stale",
                    "gadget program is not bound to executable/direct-TM nodes",
                )
            return (
                f"by\n  exact {namespace}.toGadgetProgram {packet} "
                f"{executable.declaration} {direct_tm.declaration}"
            )
        if capability == "gadget_composed_program":
            if dependency_nodes != (gadget_program,):
                _fail(
                    "candidate_dependency_stale",
                    "gadget composed program is not bound to the gadget program",
                )
            return (
                f"by\n  exact {namespace}.toComposedProgram {packet} "
                f"{gadget_program.declaration}"
            )
        if capability == "gadget_composed_semantic_iff":
            if dependency_nodes != (
                forward,
                reverse,
                gadget_program,
                composed_program,
            ):
                _fail(
                    "candidate_dependency_stale",
                    "gadget final semantic does not bind the complete authored chain",
                )
            return (
                f"by\n  exact {namespace}.toComposedSemanticProof {packet} "
                f"{executable.declaration} {forward.declaration} "
                f"{reverse.declaration} {gadget_program.declaration} rfl "
                f"{composed_program.declaration} rfl"
            )
    if capability in (
        _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES
        | _PROGRAM_INDEXED_PRIMITIVE_CAPABILITIES
        | _PROGRAM_INDEXED_PROGRAM_CAPABILITIES
        | _PROGRAM_INDEXED_ADMISSION_CAPABILITIES
        | _PROGRAM_INDEXED_SEMANTIC_CAPABILITIES
    ):
        packet = _program_indexed_admission_source(task)["witness"]
        executable_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES
        )
        primitive_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_PRIMITIVE_CAPABILITIES
        )
        program_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_PROGRAM_CAPABILITIES
        )
        admission_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_ADMISSION_CAPABILITIES
        )
        if not (
            len(executable_nodes)
            == len(primitive_nodes)
            == len(program_nodes)
            == len(admission_nodes)
            == 1
        ):
            _fail(
                "candidate_dependency_stale",
                "program-indexed DAG does not identify one executable/primitive/program/admission chain",
            )
        executable = executable_nodes[0]
        primitive = primitive_nodes[0]
        program = program_nodes[0]
        admission = admission_nodes[0]
        if capability in _PROGRAM_INDEXED_EXECUTABLE_CAPABILITIES:
            if dependency_nodes:
                _fail(
                    "candidate_dependency_stale",
                    "program-indexed executable unexpectedly depends on an authored node",
                )
            return (
                "by\n  exact "
                f"{_PROGRAM_INDEXED_PACKET_NAMESPACE}.toExecutable {packet}"
            )
        if capability in _PROGRAM_INDEXED_PRIMITIVE_CAPABILITIES:
            if dependency_nodes != (executable,):
                _fail(
                    "candidate_dependency_stale",
                    "program-indexed primitive is not bound to its executable dependency",
                )
            return (
                "by\n  exact "
                f"{_PROGRAM_INDEXED_PACKET_NAMESPACE}.toPrimitive {packet} "
                f"{executable.declaration} rfl"
            )
        if capability in _PROGRAM_INDEXED_PROGRAM_CAPABILITIES:
            if dependency_nodes != (primitive,):
                _fail(
                    "candidate_dependency_stale",
                    "program-indexed program is not bound to its primitive dependency",
                )
            return (
                "by\n  exact "
                f"{_PROGRAM_INDEXED_PACKET_NAMESPACE}.toProgram "
                f"{primitive.declaration}"
            )
        if capability in _PROGRAM_INDEXED_ADMISSION_CAPABILITIES:
            if dependency_nodes != (program,):
                _fail(
                    "candidate_dependency_stale",
                    "program-indexed admission is not bound to its program dependency",
                )
            return (
                "by\n  exact "
                f"{_PROGRAM_INDEXED_PACKET_NAMESPACE}."
                "ProgramRunCoherenceDirectTM.ofProgram "
                f"{packet} {program.declaration} rfl"
            )
        if capability in _PROGRAM_INDEXED_SEMANTIC_CAPABILITIES:
            if dependency_nodes != (admission,):
                _fail(
                    "candidate_dependency_stale",
                    "program-indexed semantic is not bound to its admission dependency",
                )
            return (
                "by\n  exact "
                f"{_PROGRAM_INDEXED_PACKET_NAMESPACE}.toSemanticProof {packet} "
                f"{program.declaration} {admission.declaration}"
            )

    if capability in (
        _PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES
        | _PROGRAM_INDEXED_COMPOSED_SEMANTIC_CAPABILITIES
    ):
        program_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_PROGRAM_CAPABILITIES
        )
        tmkarp_programs = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_PROGRAM_CAPABILITIES
        )
        tmkarp_semantics = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_SEMANTIC_IFF_CAPABILITIES
        )
        packet_semantics = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_SEMANTIC_CAPABILITIES
        )
        composed_programs = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES
        )
        if not (
            len(program_nodes)
            == len(tmkarp_programs)
            == len(tmkarp_semantics)
            == len(packet_semantics)
            == len(composed_programs)
            == 1
        ):
            _fail(
                "candidate_dependency_stale",
                "TMKarp/program-indexed composition lacks one exact authored chain",
            )
        program = program_nodes[0]
        tmkarp_program = tmkarp_programs[0]
        tmkarp_semantic = tmkarp_semantics[0]
        packet_semantic = packet_semantics[0]
        composed_program = composed_programs[0]
        if capability in _PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES:
            if dependency_nodes != (tmkarp_program, program):
                _fail(
                    "candidate_dependency_stale",
                    "composed program is not bound to both exact authored programs",
                )
            return (
                "by\n  exact PolyProg.comp "
                f"{program.declaration} {tmkarp_program.declaration}"
            )
        if dependency_nodes != (
            tmkarp_semantic,
            packet_semantic,
            composed_program,
        ):
            _fail(
                "candidate_dependency_stale",
                "composed semantic does not bind both segment semantics and final program",
            )
        source = task.source_problem.term
        target = task.target_problem.term
        return (
            "by\n  intro input\n"
            f"  change {source}.accepts input ↔\n"
            f"    {target}.accepts ({program.declaration}.run "
            f"({tmkarp_program.declaration}.run input))\n"
            f"  exact ({tmkarp_semantic.declaration} input).trans\n"
            f"    ({packet_semantic.declaration} "
            f"({tmkarp_program.declaration}.run input))"
        )
    if capability in (
        _TMKARP_PRIMITIVE_CAPABILITIES
        | _TMKARP_PROGRAM_CAPABILITIES
        | _TMKARP_SEMANTIC_IFF_CAPABILITIES
    ):
        admission = _tmkarp_admission_source(task)
        witness = admission["witness"]
        primitive_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_PRIMITIVE_CAPABILITIES
        )
        program_nodes = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_PROGRAM_CAPABILITIES
        )
        if len(primitive_nodes) != 1 or len(program_nodes) != 1:
            _fail(
                "candidate_dependency_stale",
                "typed TMKarp admission DAG does not identify one primitive and program",
            )
        primitive = primitive_nodes[0]
        program = program_nodes[0]
        if capability in _TMKARP_PRIMITIVE_CAPABILITIES:
            return (
                "by\n  exact Primitive.ofTMPolyTime "
                f"{witness}.f {witness}.polytime"
            )
        if capability in _TMKARP_PROGRAM_CAPABILITIES:
            if dependency_nodes != (primitive,):
                _fail(
                    "candidate_dependency_stale",
                    "typed TMKarp program is not bound to its one primitive dependency",
                )
            return f"by\n  exact PolyProg.atom {primitive.declaration}"
        if dependency_nodes != (program,):
            _fail(
                "candidate_dependency_stale",
                "typed TMKarp semantic is not bound to its one program dependency",
            )
        return (
            "by\n  intro input\n  simpa only ["
            f"{program.declaration}, {primitive.declaration}, "
            "PolyProg.run_atom, Primitive.run_ofTMPolyTime] using\n"
            f"    {witness}.correct input"
        )
    if capability in (
        _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES
        | _DEPENDENT_COMPOSED_SEMANTIC_IFF_CAPABILITIES
    ):
        successor = _dependent_composition_successor(task)
        admission_programs = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_PROGRAM_CAPABILITIES
        )
        admission_semantics = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _TMKARP_SEMANTIC_IFF_CAPABILITIES
        )
        composed_programs = tuple(
            node
            for node in task.gap_nodes
            if node.capability in _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES
        )
        if not (
            len(admission_programs)
            == len(admission_semantics)
            == len(composed_programs)
            == 1
        ):
            _fail(
                "candidate_dependency_stale",
                "dependent composition DAG does not identify its unique authored layers",
            )
        admission_program = admission_programs[0]
        admission_semantic = admission_semantics[0]
        composed_program = composed_programs[0]
        if capability in _DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES:
            if request.node != composed_program or dependency_nodes != (
                admission_program,
            ):
                _fail(
                    "candidate_dependency_stale",
                    "dependent composed program is not bound to the admission program",
                )
            return (
                "by\n  exact PolyProg.comp "
                f"{successor['witness']}.program {admission_program.declaration}"
            )
        if dependency_nodes != (admission_semantic, composed_program):
            _fail(
                "candidate_dependency_stale",
                "dependent composed semantic does not bind both authored dependencies",
            )
        source = task.source_problem.term
        target = task.target_problem.term
        return (
            "by\n  intro input\n"
            f"  change {source}.accepts input ↔\n"
            f"    {target}.accepts ({successor['witness']}.program.run "
            f"({admission_program.declaration}.run input))\n"
            f"  exact ({admission_semantic.declaration} input).trans\n"
            f"    ({successor['witness']}.correct "
            f"({admission_program.declaration}.run input))"
        )
    if capability == "semantic_iff":
        forward = [
            node
            for node in dependency_nodes
            if node.capability in _SEMANTIC_FORWARD_CAPABILITIES
        ]
        reverse = [
            node
            for node in dependency_nodes
            if node.capability in _SEMANTIC_REVERSE_CAPABILITIES
        ]
        if len(forward) == len(reverse) == 1:
            return (
                "by\n  intro input\n  exact \u27e8"
                f"{forward[0].declaration} input, "
                f"{reverse[0].declaration} input\u27e9"
            )
    if capability in _SEMANTIC_IFF_CAPABILITIES:
        recipes = _selected_proof_recipes(
            capability=capability, public_sources=public_sources
        )
        if "false_tag" in recipes:
            return (
                "by\n  intro input\n  change hub.accepts input ↔ "
                "(if false = Bool.true then False else hub.accepts input)\n  rfl"
            )
        if "conjunction_identity" in recipes:
            invariant_dependencies = [
                node
                for node in dependency_nodes
                if node.capability == "mapping_invariant"
            ]
            invariant_binding = (
                f"  have invariant := {invariant_dependencies[0].declaration} input\n"
                if len(invariant_dependencies) == 1
                else ""
            )
            forward_witness = (
                "invariant.1" if len(invariant_dependencies) == 1 else "rfl"
            )
            return (
                "by\n  intro input\n"
                f"{invariant_binding}"
                "  change hub.accepts input ↔ false = false ∧ "
                f"hub.accepts input\n  exact ⟨fun accepted => ⟨{forward_witness}, accepted⟩, "
                "fun accepted => accepted.2⟩"
            )
        public_reuse = _public_semantic_reuse_body(
            task=task, public_sources=public_sources
        )
        if public_reuse is not None:
            return public_reuse
        return "by\n  intro input\n  rfl"
    if (
        task.task_class == "whole_reduction_synthesis"
        and capability
        in _SEMANTIC_FORWARD_CAPABILITIES | _SEMANTIC_REVERSE_CAPABILITIES
    ):
        return None
    if capability in _SEMANTIC_FORWARD_CAPABILITIES:
        semantic_dependencies = [
            node
            for node in dependency_nodes
            if node.capability in _SEMANTIC_IFF_CAPABILITIES
        ]
        if len(semantic_dependencies) == 1:
            return (
                "by\n  intro input accepted\n  exact "
                f"({semantic_dependencies[0].declaration} input).mp accepted"
            )
        return "by\n  intro input accepted\n  exact accepted"
    if capability in _SEMANTIC_REVERSE_CAPABILITIES:
        semantic_dependencies = [
            node
            for node in dependency_nodes
            if node.capability in _SEMANTIC_IFF_CAPABILITIES
        ]
        if len(semantic_dependencies) == 1:
            return (
                "by\n  intro input accepted\n  exact "
                f"({semantic_dependencies[0].declaration} input).mpr accepted"
            )
        return "by\n  intro input accepted\n  exact accepted"
    if capability == "mapping_invariant":
        return (
            "by\n  intro input\n  change false = false ∧ input = input\n"
            "  exact ⟨rfl, rfl⟩"
        )
    if capability == "program_run_coherence":
        return "by\n  intro input\n  rfl"
    if capability == "reduction_executable":
        if task.task_class == "whole_reduction_synthesis":
            return None
        return "fun input => (false, input)"
    if (
        capability == "reduction_primitive"
        and task.task_class == "whole_reduction_synthesis"
    ):
        executable = next(
            (
                node
                for node in dependency_nodes
                if node.capability == "reduction_executable"
            ),
            None,
        )
        direct_tm = next(
            (node for node in dependency_nodes if node.capability == "direct_tm"),
            None,
        )
        if executable is None or direct_tm is None:
            _fail(
                "candidate_dependency_stale",
                "whole-reduction primitive is not bound to executable/direct-TM dependencies",
            )
        return (
            "ComplexityReduction.Program.Primitive.ofTMPolyTime "
            f"{executable.declaration} {direct_tm.declaration}"
        )
    if capability == "representation_adapter":
        observed_term = _observed_capability_term(task=task, node=request.node)
        if observed_term is not None:
            return f"by\n  exact {observed_term}"
        if getattr(task, "task_class", None) == "typed_capability_dag":
            _fail(
                "candidate_dependency_stale",
                "typed representation adapter lacks its Lean-observed witness",
            )
        source = task.source_problem.term
        return (
            f"PolyProg.pair (PolyProg.const {source}.representation "
            "StandardInstances.bool false) "
            f"(PolyProg.id {source}.representation)"
        )
    if capability == "poly_program":
        if task.task_class == "whole_reduction_synthesis":
            primitives = [
                node
                for node in dependency_nodes
                if node.capability == "reduction_primitive"
            ]
            if len(primitives) != 1:
                _fail(
                    "candidate_dependency_stale",
                    "whole-reduction program is not bound to one accepted primitive",
                )
            return (
                "ComplexityReduction.Program.PolyProg.atom "
                f"{primitives[0].declaration}"
            )
        if task.task_class == "program_composition":
            first, second = task.allowed_primitives
            return f"PolyProg.comp {second} {first}"
        if task.task_class == "program_synthesis":
            source = task.source_problem.term
            return (
                f"PolyProg.pair (PolyProg.const {source}.representation "
                "StandardInstances.bool false) "
                f"(PolyProg.id {source}.representation)"
            )
    return None


def _public_theorem_names(public_sources: Mapping[str, str]) -> tuple[str, ...]:
    declarations: list[str] = []
    for source in public_sources.values():
        scopes: list[str | None] = []
        for raw_line in source.splitlines():
            line = raw_line.strip()
            namespace_match = re.fullmatch(r"namespace\s+([A-Za-z0-9_.']+)", line)
            if namespace_match:
                scopes.append(namespace_match.group(1))
                continue
            if re.fullmatch(r"section(?:\s+[A-Za-z0-9_.']+)?", line):
                scopes.append(None)
                continue
            if re.fullmatch(r"end(?:\s+[A-Za-z0-9_.']+)?", line):
                if scopes:
                    scopes.pop()
                continue
            declaration_match = re.match(
                r"(?:theorem|lemma)\s+([A-Za-z0-9_.']+)", line
            )
            if declaration_match:
                name = declaration_match.group(1)
                declarations.append(
                    ".".join((*tuple(scope for scope in scopes if scope), name))
                )
    return tuple(dict.fromkeys(declarations))


def _public_semantic_reuse_body(
    *, task: NPHardAuthoringTaskV2, public_sources: Mapping[str, str]
) -> str | None:
    """Build a generic public-theorem reuse recipe when every role is unique."""

    theorem_names = _public_theorem_names(public_sources)
    source_base = task.source_problem.term.rsplit(".", 1)[-1]
    target_base = task.target_problem.term.rsplit(".", 1)[-1]
    program_bases = tuple(
        primitive.rsplit(".", 1)[-1] for primitive in task.allowed_primitives
    )

    def unique_short(short_name: str) -> str | None:
        matched = [name for name in theorem_names if name.rsplit(".", 1)[-1] == short_name]
        return matched[0] if len(matched) == 1 else None

    source_accepts = unique_short(f"{source_base}_accepts")
    target_accepts = unique_short(f"{target_base}_accepts")
    program_runs = [
        name
        for base in program_bases
        if (name := unique_short(f"{base}_run")) is not None
    ]
    correctness = [
        name
        for name in theorem_names
        if name.rsplit(".", 1)[-1].endswith("_correct")
    ]
    if (
        source_accepts is None
        or target_accepts is None
        or len(program_runs) != 1
        or len(correctness) != 1
    ):
        return None
    return (
        "by\n"
        "  intro input\n"
        f"  simpa only [{source_accepts}, {target_accepts}, {program_runs[0]}] using\n"
        f"    {correctness[0]} input"
    )

_QUARANTINED_MARKERS = (
    ".Oracles.",
    ".Gold.",
    ".GoldProofs.",
    ".HiddenTargets.",
    "GoldProof",
    "HiddenTargets",
)


class NPHardGapRuntimeError(ValueError):
    """Typed fail-closed error from the G-C runtime."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardGapRuntimeError(code, message)


def _tagged_file_hash(path: Path) -> str:
    return f"sha256:{sha256_file(path)}"


def _deletion_failure_mentions_declaration(
    command: CommandResult, declaration: str
) -> bool:
    """Accept only a real Lean unknown-declaration failure for N-1 audits."""

    return deletion_command_matches_declaration_v2(
        command.to_dict(), declaration
    )


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    if set(value) != expected:
        _fail(
            "invalid_np_hard_gap_runtime_schema",
            f"{label} keys drifted; missing={sorted(expected - set(value))!r}, "
            f"extra={sorted(set(value) - expected)!r}",
        )


def _assert_public(value: str, *, label: str) -> None:
    lowered = value.lower()
    if any(marker.lower() in lowered for marker in _QUARANTINED_MARKERS):
        _fail("oracle_or_gold_import", f"{label} references quarantined material")


def _assert_program_indexed_prompt_surface(
    public_sources: Mapping[str, str],
) -> None:
    """Reject implementation/template leakage from typed packet prompts."""

    forbidden = (
        "ProgramIndexedReductionTemplate",
        "def template",
        ".template",
        "CertifiedReduction",
        "NativeTMNPHard",
        "finalRoute",
    )
    for name, source in public_sources.items():
        marker = next((item for item in forbidden if item in source), None)
        if marker is not None:
            _fail(
                "candidate_outside_edit_boundary",
                f"program-indexed public source {name} exposes forbidden marker {marker}",
            )


def _assert_gadget_indexed_prompt_surface(
    public_sources: Mapping[str, str],
    *,
    allowed_imports: tuple[str, ...] = (),
    dependency_names: tuple[str, ...] = (),
) -> None:
    """Keep the structured gadget prompt isolated from successor-only reuse."""

    if any(
        "SuccessorAuthoringSources" in value or "SuccessorOnly" in value
        for value in (*allowed_imports, *dependency_names)
    ):
        _fail(
            "candidate_outside_edit_boundary",
            "gadget-indexed task imports a successor-only shortcut authority",
        )
    for name, source in public_sources.items():
        if "SuccessorAuthoringSources" in name or "SuccessorOnly" in source:
            _fail(
                "candidate_outside_edit_boundary",
                "gadget-indexed public surface exposes a successor-only shortcut",
            )


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _run_successor_only_chain_probe(
    *,
    root: Path,
    task: NPHardAuthoringTaskV2,
    output_root: Path,
    timeout_seconds: int,
) -> tuple[Mapping[str, Any], CommandResult, tuple[tuple[str, str], ...]] | None:
    """Kernel-check the two observer witnesses before any model invocation."""

    if getattr(task, "task_class", None) != "typed_tmkarp_dependent_composition_dag":
        return None
    admission = _tmkarp_admission_source(task)
    if admission["module"] != _SUCCESSOR_ONLY_TMKARP_ADMISSION_MODULE:
        return None
    successor = _dependent_composition_successor(task)
    source = _successor_only_chain_probe_source_v2(task)
    probe_root = output_root / "authoritative-evidence" / "successor-only-chain"
    source_path = probe_root / "Probe.lean"
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(source, encoding="utf-8")
    command = run_command(
        ["lake", "env", "lean", str(source_path)],
        cwd=root / "Lean",
        timeout_seconds=timeout_seconds,
    )
    source_sha256 = sha256_id(source)
    source_file_sha256 = _tagged_file_hash(source_path)
    command_certificate = {
        "command": list(command.command),
        "exit_code": command.exit_code,
        "stdout": command.stdout,
        "stderr": command.stderr,
        "timed_out": command.timed_out,
    }
    stable_evidence_core = {
        "schema_version": NP_HARD_SUCCESSOR_CHAIN_PROBE_SCHEMA_V1,
        "task_request_id": task.request_id,
        "source_file": str(source_path),
        "source_sha256": source_sha256,
        "source_file_sha256": source_file_sha256,
        "admission": admission,
        "successor": successor,
        "command_certificate_sha256": sha256_id(command_certificate),
        "passed": command.ok,
    }
    evidence = {
        **stable_evidence_core,
        "command": command.to_dict(),
        "evidence_sha256": sha256_id(stable_evidence_core),
    }
    evidence_path = probe_root / "evidence.json"
    _write_json(evidence_path, evidence)
    result_evidence = {
        **evidence,
        "evidence_file": str(evidence_path),
        "evidence_file_sha256": _tagged_file_hash(evidence_path),
    }
    bindings = tuple(
        sorted(
            {
                "authoritative:successor-only-chain-probe-source": source_sha256,
                "authoritative:successor-only-chain-probe-command": sha256_id(
                    command_certificate
                ),
                "authoritative:successor-only-chain-probe-evidence": evidence[
                    "evidence_sha256"
                ],
            }.items()
        )
    )
    if not command.ok:
        _fail(
            "candidate_exact_type_mismatch",
            "isolated Lean rejected the observer-bound successor-only chain",
        )
    return result_evidence, command, bindings


class NPHardNodeModelClient(Protocol):
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class NPHardNodeRequestV1:
    request_id: str
    task_request_id: str
    node_ordinal: int
    node: NPHardAuthoringObligationV2
    source_problem: Mapping[str, str]
    target_problem: Mapping[str, str]
    required_direction: str
    dependency_snapshot: tuple[tuple[str, str], ...]
    accepted_nodes: tuple[tuple[str, str], ...]
    allowed_imports: tuple[str, ...]
    allowed_primitives: tuple[str, ...]
    node_attempt_budget: int
    instance_call_budget_remaining: int
    schema_version: str = NP_HARD_NODE_REQUEST_SCHEMA_V1

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "task_request_id": self.task_request_id,
            "node_ordinal": self.node_ordinal,
            "node": self.node.to_dict(),
            "source_problem": dict(self.source_problem),
            "target_problem": dict(self.target_problem),
            "required_direction": self.required_direction,
            "dependency_snapshot": dict(self.dependency_snapshot),
            "accepted_nodes": dict(self.accepted_nodes),
            "allowed_imports": list(self.allowed_imports),
            "allowed_primitives": list(self.allowed_primitives),
            "node_attempt_budget": self.node_attempt_budget,
            "instance_call_budget_remaining": self.instance_call_budget_remaining,
        }

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content())

    @property
    def dependency_fingerprint(self) -> str:
        return sha256_id(dict(self.dependency_snapshot))

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_NODE_REQUEST_SCHEMA_V1:
            _fail("invalid_np_hard_gap_runtime_schema", "unsupported node request schema")
        if self.task_request_id != task.request_id or self.request_id != self.computed_request_id:
            _fail("candidate_dependency_stale", "node request does not bind the immutable task")
        if not 1 <= self.node_ordinal <= len(task.gap_nodes):
            _fail("candidate_dependency_stale", "node ordinal is outside the task DAG")
        if self.node != task.gap_nodes[self.node_ordinal - 1]:
            _fail("candidate_dependency_stale", "node request selected a different DAG node")
        if dict(self.source_problem) != task.source_problem.to_dict() or dict(
            self.target_problem
        ) != task.target_problem.to_dict():
            _fail("candidate_wrong_endpoint", "node request changed an exact endpoint")
        if self.required_direction != task.required_direction:
            _fail("candidate_wrong_direction", "node request changed the reduction direction")
        expected_accepted = tuple(
            node.node_id for node in task.gap_nodes[: self.node_ordinal - 1]
        )
        if tuple(name for name, _ in self.accepted_nodes) != expected_accepted:
            _fail("candidate_dependency_stale", "node request skipped a dependency")
        if not 1 <= self.node_attempt_budget <= 4:
            _fail("authoring_gap_budget_exhausted", "node attempt budget is outside 1..4")
        if not 0 <= self.instance_call_budget_remaining <= NP_HARD_MAX_INSTANCE_CALL_BUDGET:
            _fail("authoring_gap_budget_exhausted", "instance call budget is exhausted")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {"request_id": self.request_id, **self._content()}


@dataclass(frozen=True)
class NPHardNodePatchV1:
    request_id: str
    node_id: str
    declaration: str
    dependency_fingerprint: str
    replacement_body: str
    action: str = "submit_node_patch"
    schema_version: str = NP_HARD_NODE_PATCH_SCHEMA_V1


def parse_np_hard_node_patch_v1(
    *, content: str, request: NPHardNodeRequestV1, task: NPHardAuthoringTaskV2
) -> NPHardNodePatchV1:
    request.validate(task)
    value = extract_json_object(content)
    if not isinstance(value, Mapping):
        _fail("invalid_np_hard_gap_runtime_schema", "model did not return one JSON object")
    expected = {
        "schema_version",
        "action",
        "request_id",
        "node_id",
        "declaration",
        "dependency_fingerprint",
        "replacement_body",
    }
    _exact_keys(value, expected, label="node patch")
    if (
        value["schema_version"] != NP_HARD_NODE_PATCH_SCHEMA_V1
        or value["action"] != "submit_node_patch"
    ):
        _fail("invalid_np_hard_gap_runtime_schema", "unsupported node patch envelope")
    if value["request_id"] != request.request_id:
        _fail("candidate_dependency_stale", "node patch belongs to another request")
    if value["node_id"] != request.node.node_id:
        _fail("candidate_dependency_stale", "node patch changed the active DAG node")
    if value["declaration"] != request.node.declaration:
        _fail("candidate_outside_edit_boundary", "node patch changed the editable declaration")
    if value["dependency_fingerprint"] != request.dependency_fingerprint:
        _fail("candidate_dependency_stale", "node patch uses stale dependencies")
    body = value["replacement_body"]
    if not isinstance(body, str) or not body.strip():
        _fail("candidate_outside_edit_boundary", "node replacement body is empty")
    if len(body) > NP_HARD_AUTHORING_MAX_BODY_CHARS:
        _fail("candidate_outside_edit_boundary", "node replacement body is too large")
    match = BANNED_BODY_RE.search(body)
    if match:
        token = match.group(0).lower()
        if token in {"sorry", "admit", "axiom", "unsafe"}:
            code = "candidate_nonstandard_axiom"
        elif token == "import":
            code = "import_not_allowlisted"
        else:
            code = "candidate_outside_edit_boundary"
        _fail(code, f"node replacement contains forbidden token: {token}")
    _assert_public(body, label="node replacement body")
    try:
        assert_generated_source_is_safe(body)
    except ValueError as error:
        _fail("candidate_nonstandard_axiom", str(error))
    _validate_tmkarp_patch_binding(task=task, request=request, body=body)
    _validate_program_indexed_patch_binding(
        task=task, request=request, body=body
    )
    _validate_gadget_indexed_patch_binding(
        task=task, request=request, body=body
    )
    return NPHardNodePatchV1(
        request_id=request.request_id,
        node_id=request.node.node_id,
        declaration=request.node.declaration,
        dependency_fingerprint=request.dependency_fingerprint,
        replacement_body=body if body.endswith("\n") else body + "\n",
    )


@dataclass(frozen=True)
class AcceptedCapabilityNodeV1:
    node_id: str
    declaration: str
    body_sha256: str
    cumulative_source_sha256: str
    publication_manifest_sha256: str
    worker_evidence_sha256: str
    fresh_core_evidence_sha256: str


@dataclass(frozen=True)
class NPHardGapCheckpointV1:
    task_request_id: str
    dependency_snapshot: tuple[tuple[str, str], ...]
    accepted_nodes: tuple[AcceptedCapabilityNodeV1, ...]
    remaining_gap_graph: tuple[Mapping[str, Any], ...]
    total_model_calls: int
    per_node_model_calls: tuple[tuple[str, int], ...]
    model_call_ledger: tuple[Mapping[str, Any], ...]
    checkpoint_hash: str
    schema_version: str = NP_HARD_GAP_CHECKPOINT_SCHEMA_V1

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "task_request_id": self.task_request_id,
            "dependency_snapshot": dict(self.dependency_snapshot),
            "accepted_nodes": [asdict(node) for node in self.accepted_nodes],
            "remaining_gap_graph": [dict(node) for node in self.remaining_gap_graph],
            "total_model_calls": self.total_model_calls,
            "per_node_model_calls": dict(self.per_node_model_calls),
            "model_call_ledger": [dict(item) for item in self.model_call_ledger],
        }

    @property
    def computed_checkpoint_hash(self) -> str:
        return sha256_id(self._content())

    def validate(self, task: NPHardAuthoringTaskV2) -> None:
        task.validate()
        if self.schema_version != NP_HARD_GAP_CHECKPOINT_SCHEMA_V1:
            _fail("checkpoint_tampered", "unsupported checkpoint schema")
        if self.task_request_id != task.request_id:
            _fail("checkpoint_tampered", "checkpoint belongs to another task")
        if self.checkpoint_hash != self.computed_checkpoint_hash:
            _fail("checkpoint_tampered", "checkpoint content hash mismatch")
        accepted_ids = tuple(node.node_id for node in self.accepted_nodes)
        task_ids = tuple(node.node_id for node in task.gap_nodes)
        if accepted_ids != task_ids[: len(accepted_ids)]:
            _fail("checkpoint_tampered", "accepted checkpoint nodes are not a DAG prefix")
        expected_remaining = tuple(
            node.to_dict() for node in task.gap_nodes[len(accepted_ids) :]
        )
        if tuple(dict(node) for node in self.remaining_gap_graph) != expected_remaining:
            _fail("checkpoint_tampered", "checkpoint remaining graph drifted")
        maximum = required_model_call_budget(
            gap_node_count=len(task.gap_nodes), attempt_budget=task.attempt_budget
        )
        if not 0 <= self.total_model_calls <= maximum:
            _fail("checkpoint_tampered", "checkpoint model-call total is invalid")
        if sum(dict(self.per_node_model_calls).values()) != self.total_model_calls:
            _fail("checkpoint_tampered", "checkpoint call counters disagree")
        if len(self.model_call_ledger) != self.total_model_calls:
            _fail("checkpoint_tampered", "checkpoint ledger length disagrees")

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        self.validate(task)
        return {"checkpoint_hash": self.checkpoint_hash, **self._content()}

    @classmethod
    def from_dict(
        cls, value: Mapping[str, Any], *, task: NPHardAuthoringTaskV2
    ) -> "NPHardGapCheckpointV1":
        if not isinstance(value, Mapping):
            _fail("checkpoint_tampered", "checkpoint must be an object")
        expected = {
            "schema_version",
            "task_request_id",
            "dependency_snapshot",
            "accepted_nodes",
            "remaining_gap_graph",
            "total_model_calls",
            "per_node_model_calls",
            "model_call_ledger",
            "checkpoint_hash",
        }
        _exact_keys(value, expected, label="checkpoint")
        if not isinstance(value["dependency_snapshot"], Mapping) or not isinstance(
            value["per_node_model_calls"], Mapping
        ):
            _fail("checkpoint_tampered", "checkpoint maps are invalid")
        if not isinstance(value["accepted_nodes"], list) or not isinstance(
            value["remaining_gap_graph"], list
        ) or not isinstance(value["model_call_ledger"], list):
            _fail("checkpoint_tampered", "checkpoint sequences are invalid")
        node_fields = {field.name for field in AcceptedCapabilityNodeV1.__dataclass_fields__.values()}
        accepted: list[AcceptedCapabilityNodeV1] = []
        for item in value["accepted_nodes"]:
            if not isinstance(item, Mapping):
                _fail("checkpoint_tampered", "accepted node record is invalid")
            _exact_keys(item, node_fields, label="accepted node")
            accepted.append(AcceptedCapabilityNodeV1(**dict(item)))
        checkpoint = cls(
            task_request_id=value["task_request_id"],
            dependency_snapshot=tuple(sorted(value["dependency_snapshot"].items())),
            accepted_nodes=tuple(accepted),
            remaining_gap_graph=tuple(dict(item) for item in value["remaining_gap_graph"]),
            total_model_calls=value["total_model_calls"],
            per_node_model_calls=tuple(sorted(value["per_node_model_calls"].items())),
            model_call_ledger=tuple(dict(item) for item in value["model_call_ledger"]),
            checkpoint_hash=value["checkpoint_hash"],
            schema_version=value["schema_version"],
        )
        checkpoint.validate(task)
        return checkpoint


@dataclass(frozen=True)
class NPHardGapRuntimeResultV1:
    status: str
    task_request_id: str
    accepted_nodes: tuple[str, ...]
    fresh_core_rediscoveries: int
    model_calls: int
    checkpoint_path: str | None
    checkpoint_file_sha256: str | None
    result: NPHardAuthoringResultV2 | None
    failure_code: str | None
    failure_message: str | None
    commands: tuple[CommandResult, ...]
    worker_results: tuple[Mapping[str, Any], ...]
    resumed: bool
    model_call_ledger: tuple[Mapping[str, Any], ...] = ()
    deletion_audits: tuple[Mapping[str, Any], ...] = ()
    authoritative_evidence: tuple[Mapping[str, Any], ...] = ()
    authoritative_dependency_bindings: tuple[tuple[str, str], ...] = ()
    schema_version: str = NP_HARD_GAP_RUNTIME_REPORT_SCHEMA_V1

    def to_dict(self, task: NPHardAuthoringTaskV2) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "status": self.status,
            "task_request_id": self.task_request_id,
            "accepted_nodes": list(self.accepted_nodes),
            "fresh_core_rediscoveries": self.fresh_core_rediscoveries,
            "model_calls": self.model_calls,
            "checkpoint_path": self.checkpoint_path,
            "checkpoint_file_sha256": self.checkpoint_file_sha256,
            "result": self.result.to_dict(task) if self.result is not None else None,
            "failure_code": self.failure_code,
            "failure_message": self.failure_message,
            "commands": [command.to_dict() for command in self.commands],
            "worker_results": [dict(item) for item in self.worker_results],
            "resumed": self.resumed,
            "model_call_ledger": [dict(item) for item in self.model_call_ledger],
            "deletion_audits": [dict(item) for item in self.deletion_audits],
            "authoritative_evidence": [
                dict(item) for item in self.authoritative_evidence
            ],
            "authoritative_dependency_bindings": dict(
                self.authoritative_dependency_bindings
            ),
        }


def _current_dependency_snapshot(
    *,
    root: Path,
    task: NPHardAuthoringTaskV2,
    accepted: tuple[AcceptedCapabilityNodeV1, ...],
    authoritative_evidence: tuple[tuple[str, str], ...] = (),
) -> tuple[tuple[str, str], ...]:
    current: dict[str, str] = {}
    for name, expected in task.dependency_hashes:
        if name.startswith("public:"):
            path = root / name.removeprefix("public:")
        elif name.startswith("module:"):
            path = module_file(root / "Lean", name.removeprefix("module:"))
        elif name.startswith("content:"):
            current[name] = expected
            continue
        else:
            _fail("candidate_dependency_stale", f"unsupported dependency key: {name}")
        if not path.is_file() or _tagged_file_hash(path) != expected:
            _fail("candidate_dependency_stale", f"dependency changed: {name}")
        current[name] = expected
    for node_id, term in sorted(_observed_capability_terms(task).items()):
        if not isinstance(node_id, str) or not isinstance(term, str):
            _fail(
                "candidate_dependency_stale",
                "observed capability term map is invalid",
            )
        _assert_public(term, label="observed capability dependency")
        current[f"observed:{node_id}:term"] = sha256_id(term)
    for node_id, exact_type in sorted(
        _observed_capability_exact_types(task).items()
    ):
        if not isinstance(node_id, str) or not isinstance(exact_type, str):
            _fail(
                "candidate_dependency_stale",
                "observed capability exact-type map is invalid",
            )
        _assert_public(exact_type, label="observed capability exact-type dependency")
        current[f"observed:{node_id}:exact-type"] = sha256_id(exact_type)
    if getattr(task, "task_class", None) == "typed_tmkarp_dependent_composition_dag":
        current["observed:composition-intermediate"] = sha256_id(
            _composition_intermediate_payload(task)
        )
        current["observed:composition-successor-module"] = sha256_id(
            _dependent_composition_successor(task)["module"]
        )
    if getattr(task, "task_class", None) in {
        _PROGRAM_INDEXED_TASK_CLASS,
        "typed_tmkarp_program_indexed_composition_dag",
    }:
        current["observed:program-indexed-packet-module"] = sha256_id(
            _program_indexed_admission_source(task)["module"]
        )
    if getattr(task, "task_class", None) == _GADGET_INDEXED_TASK_CLASS:
        gadget_source = _gadget_indexed_admission_source(task)
        current["observed:gadget-indexed-packet-module"] = sha256_id(
            gadget_source["module"]
        )
        current["observed:gadget-reference-endpoint"] = sha256_id(
            {
                "module": gadget_source["reference_module"],
                "term": gadget_source["reference_term"],
            }
        )
    for node in accepted:
        current[f"accepted:{node.node_id}:body"] = node.body_sha256
        current[f"accepted:{node.node_id}:source"] = node.cumulative_source_sha256
    for name, digest in authoritative_evidence:
        if not name.startswith("authoritative:"):
            _fail(
                "candidate_dependency_stale",
                "runtime authoritative evidence key is invalid",
            )
        current[name] = digest
    return tuple(sorted(current.items()))


def _node_request(
    *,
    task: NPHardAuthoringTaskV2,
    node_ordinal: int,
    dependency_snapshot: tuple[tuple[str, str], ...],
    accepted: tuple[AcceptedCapabilityNodeV1, ...],
    total_model_calls: int,
    instance_call_budget: int | None = None,
) -> NPHardNodeRequestV1:
    effective_call_budget = (
        required_model_call_budget(
            gap_node_count=len(task.gap_nodes), attempt_budget=task.attempt_budget
        )
        if instance_call_budget is None
        else instance_call_budget
    )
    arguments = {
        "task_request_id": task.request_id,
        "node_ordinal": node_ordinal,
        "node": task.gap_nodes[node_ordinal - 1],
        "source_problem": task.source_problem.to_dict(),
        "target_problem": task.target_problem.to_dict(),
        "required_direction": task.required_direction,
        "dependency_snapshot": dependency_snapshot,
        "accepted_nodes": tuple((node.node_id, node.body_sha256) for node in accepted),
        "allowed_imports": task.allowed_imports,
        "allowed_primitives": task.allowed_primitives,
        "node_attempt_budget": min(task.attempt_budget, 4),
        "instance_call_budget_remaining": effective_call_budget - total_model_calls,
    }
    provisional = NPHardNodeRequestV1(request_id="sha256:" + "0" * 64, **arguments)
    request = NPHardNodeRequestV1(request_id=provisional.computed_request_id, **arguments)
    request.validate(task)
    return request


def _prompt_identifier_tokens(value: str) -> frozenset[str]:
    expanded = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return frozenset(
        token
        for token in re.findall(r"[A-Za-z][A-Za-z0-9]*", expanded.lower())
        if len(token) >= 3 and token not in _PROMPT_SOURCE_STOP_WORDS
    )


def _public_source_module(relative_name: str) -> str | None:
    parts = Path(relative_name).parts
    try:
        reference_index = parts.index("Reference")
    except ValueError:
        return None
    module_parts = list(parts[reference_index + 1 :])
    if not module_parts or not module_parts[-1].endswith(".lean"):
        return None
    module_parts[-1] = module_parts[-1].removesuffix(".lean")
    return ".".join(module_parts)


def _source_excerpt(
    source: str, *, query_tokens: frozenset[str], limit: int
) -> str:
    """Return bounded, line-preserving source context around relevant declarations."""

    if len(source) <= limit:
        return source
    lines = source.splitlines(keepends=True)
    selected = set(range(min(28, len(lines))))
    ranked_lines: list[tuple[int, int]] = []
    declaration_re = re.compile(
        r"^\s*(?:def|abbrev|theorem|lemma|structure|class|instance|inductive)\b"
    )
    for index, line in enumerate(lines):
        overlap = len(_prompt_identifier_tokens(line) & query_tokens)
        if overlap:
            score = overlap * 10 + int(bool(declaration_re.match(line))) * 5
            ranked_lines.append((score, index))
    estimated = sum(len(lines[index]) for index in selected)
    for _, center in sorted(ranked_lines, key=lambda item: (-item[0], item[1])):
        window = range(max(0, center - 5), min(len(lines), center + 7))
        additions = [index for index in window if index not in selected]
        addition_size = sum(len(lines[index]) for index in additions)
        if estimated + addition_size > limit - 80:
            continue
        selected.update(additions)
        estimated += addition_size
    groups: list[str] = []
    previous: int | None = None
    for index in sorted(selected):
        if previous is not None and index != previous + 1:
            groups.append("-- ... unrelated public source omitted ...\n")
        groups.append(lines[index])
        previous = index
    excerpt = "".join(groups)
    if len(excerpt) <= limit:
        return excerpt
    marker = "\n-- ... public source excerpt truncated ...\n"
    return excerpt[: limit - len(marker)] + marker


def _node_prompt_public_sources(
    *,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    full_sources: Mapping[str, str],
    accepted_bodies: Mapping[str, str],
    diagnostic: str | None,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Retrieve a bounded source view for one active capability node."""

    module_to_name = {
        module: name
        for name in full_sources
        if (module := _public_source_module(name)) is not None
    }
    source_modules = (task.source_problem.module, task.target_problem.module)
    endpoint_names = tuple(
        dict.fromkeys(
            module_to_name[module]
            for module in source_modules
            if module in module_to_name
        )
    )
    query_text = "\n".join(
        (
            request.node.node_id,
            request.node.capability,
            request.node.declaration,
            request.node.exact_type,
            task.source_problem.module,
            task.source_problem.term,
            task.target_problem.module,
            task.target_problem.term,
            *accepted_bodies.values(),
            diagnostic or "",
        )
    )
    query_tokens = set(_prompt_identifier_tokens(query_text))
    for name in endpoint_names:
        endpoint_source = full_sources[name]
        query_tokens.update(
            _prompt_identifier_tokens(
                "\n".join(_PROMPT_SOURCE_IMPORT_RE.findall(endpoint_source))
            )
        )
        if len(endpoint_source) <= 4_000:
            query_tokens.update(_prompt_identifier_tokens(endpoint_source))
    frozen_query_tokens = frozenset(query_tokens)

    import_graph: dict[str, tuple[str, ...]] = {}
    for name, source in full_sources.items():
        import_graph[name] = tuple(
            module_to_name[module]
            for module in _PROMPT_SOURCE_IMPORT_RE.findall(source)
            if module in module_to_name
        )
    distances: dict[str, int] = {name: 0 for name in endpoint_names}
    frontier = list(endpoint_names)
    cursor = 0
    while cursor < len(frontier):
        current = frontier[cursor]
        cursor += 1
        for imported_name in import_graph.get(current, ()):
            if imported_name in distances:
                continue
            distances[imported_name] = distances[current] + 1
            frontier.append(imported_name)

    ranked: list[tuple[int, str]] = []
    for name, source in full_sources.items():
        path_overlap = len(_prompt_identifier_tokens(name) & frozen_query_tokens)
        signature_text = "\n".join(
            line
            for line in source.splitlines()
            if line.lstrip().startswith(
                (
                    "import ",
                    "def ",
                    "abbrev ",
                    "theorem ",
                    "lemma ",
                    "structure ",
                    "class ",
                    "instance ",
                )
            )
        )
        signature_overlap = len(
            _prompt_identifier_tokens(signature_text) & frozen_query_tokens
        )
        distance = distances.get(name)
        score = path_overlap * 1_200 + min(signature_overlap, 30) * 80
        if name in endpoint_names:
            score += 100_000
        elif distance is not None:
            score += max(200, 1_400 - distance * 250)
        if "Benchmark/Hardness/Inputs" in name:
            score += 1_500
        ranked.append((score, name))

    selected: dict[str, str] = {}
    source_chars = 0
    for _, name in sorted(ranked, key=lambda item: (-item[0], item[1])):
        if len(selected) >= NP_HARD_NODE_PROMPT_MAX_SOURCE_FILES:
            break
        remaining = NP_HARD_NODE_PROMPT_SOURCE_CHAR_BUDGET - source_chars
        if remaining < 256:
            break
        excerpt = _source_excerpt(
            full_sources[name],
            query_tokens=frozen_query_tokens,
            limit=min(NP_HARD_NODE_PROMPT_SOURCE_EXCERPT_CHARS, remaining),
        )
        if not excerpt.strip():
            continue
        selected[name] = excerpt
        source_chars += len(excerpt)

    context = {
        "mode": "node_retrieved_source_excerpts_v1",
        "source_character_budget": NP_HARD_NODE_PROMPT_SOURCE_CHAR_BUDGET,
        "source_file_limit": NP_HARD_NODE_PROMPT_MAX_SOURCE_FILES,
        "included_files": list(selected),
        "included_file_count": len(selected),
        "omitted_file_count": len(full_sources) - len(selected),
        "included_source_characters": source_chars,
        "complete_dependency_hashes_remain_in_node_request": True,
    }
    return selected, context


def _node_prompt_dependency_bodies(
    *,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    accepted_bodies: Mapping[str, str],
) -> dict[str, str]:
    by_id = {node.node_id: node for node in task.gap_nodes}
    required_ids: set[str] = set()
    frontier = list(request.node.depends_on)
    while frontier:
        node_id = frontier.pop()
        if node_id in required_ids:
            continue
        required_ids.add(node_id)
        dependency = by_id.get(node_id)
        if dependency is not None:
            frontier.extend(dependency.depends_on)
    remaining = NP_HARD_NODE_PROMPT_DEPENDENCY_BODY_CHAR_BUDGET
    selected: dict[str, str] = {}
    for node in task.gap_nodes:
        if node.node_id not in required_ids or node.declaration not in accepted_bodies:
            continue
        body = accepted_bodies[node.declaration]
        if remaining <= 0:
            break
        clipped = body[:remaining]
        selected[node.declaration] = clipped
        remaining -= len(clipped)
    return selected


def build_np_hard_node_prompt_v1(
    *,
    root: Path,
    task: NPHardAuthoringTaskV2,
    request: NPHardNodeRequestV1,
    accepted_bodies: Mapping[str, str],
    diagnostic: str | None,
) -> str:
    request.validate(task)
    full_public_sources = {
        name: (root / name).read_text(encoding="utf-8")
        for name in task.public_source_files
    }
    if task.task_class in _PROGRAM_INDEXED_TASK_CLASSES:
        _assert_program_indexed_prompt_surface(full_public_sources)
    if task.task_class == _GADGET_INDEXED_TASK_CLASS:
        _assert_gadget_indexed_prompt_surface(
            full_public_sources,
            allowed_imports=task.allowed_imports,
            dependency_names=tuple(name for name, _ in task.dependency_hashes),
        )
    prompt_dependency_bodies = _node_prompt_dependency_bodies(
        task=task,
        request=request,
        accepted_bodies=accepted_bodies,
    )
    public_sources, public_source_context = _node_prompt_public_sources(
        task=task,
        request=request,
        full_sources=full_public_sources,
        accepted_bodies=prompt_dependency_bodies,
        diagnostic=diagnostic,
    )
    observed_term = _observed_capability_term(task=task, node=request.node)
    recommended_body = _recommended_first_body(
        task=task, request=request, public_sources=full_public_sources
    )
    payload = {
        "schema_version": NP_HARD_NODE_REQUEST_SCHEMA_V1,
        "objective": "prove_np_hard",
        "task_class": task.task_class,
        "node_request": request.to_dict(task),
        "accepted_dependency_bodies": prompt_dependency_bodies,
        "public_sources": public_sources,
        "public_source_context": public_source_context,
        "observed_capability_term": observed_term,
        "lean_api_reference": _POLY_PROG_API_REFERENCE,
        "active_capability_guidance": _CAPABILITY_GUIDANCE.get(
            request.node.capability,
            "Follow the exact active node type and its accepted dependencies.",
        ),
        "proof_recipes": _selected_proof_recipes(
            capability=request.node.capability,
            public_sources=full_public_sources,
        ),
        "recommended_first_body": recommended_body,
        "lean_diagnostic": (
            diagnostic[:NP_HARD_NODE_PROMPT_DIAGNOSTIC_CHARS]
            if diagnostic
            else None
        ),
        "policy": {
            "only_active_declaration_is_editable": True,
            "compiler_inserted_math_tokens": 0,
            "fresh_core_required_after_acceptance": True,
        },
        "response_template": {
            "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
            "action": "submit_node_patch",
            "request_id": request.request_id,
            "node_id": request.node.node_id,
            "declaration": request.node.declaration,
            "dependency_fingerprint": request.dependency_fingerprint,
            "replacement_body": recommended_body or "Lean term body only",
        },
    }
    if getattr(task, "task_class", None) in _TMKARP_ADMISSION_TASK_CLASSES:
        payload["tmkarp_admission_source"] = _tmkarp_admission_source(task)
    if getattr(task, "task_class", None) == "typed_tmkarp_dependent_composition_dag":
        payload["dependent_composition_successor"] = (
            _dependent_composition_successor(task)
        )
    if getattr(task, "task_class", None) in {
        _PROGRAM_INDEXED_TASK_CLASS,
        "typed_tmkarp_program_indexed_composition_dag",
    }:
        payload["program_indexed_admission_source"] = (
            _program_indexed_admission_source(task)
        )
    if getattr(task, "task_class", None) == _GADGET_INDEXED_TASK_CLASS:
        payload["gadget_indexed_admission_source"] = (
            _gadget_indexed_admission_source(task)
        )
    serialized = json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)
    _assert_public(serialized, label="node prompt")
    return serialized


def _task_node_by_id(
    task: NPHardAuthoringTaskV2, *, node_id: str, role: str
) -> NPHardAuthoringObligationV2:
    matched = [node for node in task.gap_nodes if node.node_id == node_id]
    if len(matched) != 1:
        _fail(
            "candidate_dependency_stale",
            f"{role} node ID does not resolve exactly once: {node_id}",
        )
    return matched[0]


def _terminal_semantic_node(
    task: NPHardAuthoringTaskV2,
) -> NPHardAuthoringObligationV2:
    """Resolve the runner-owned certificate semantic without list-position assumptions."""

    explicit_node_id = getattr(task, "terminal_node_id", None)
    if isinstance(explicit_node_id, str) and explicit_node_id:
        node = _task_node_by_id(
            task, node_id=explicit_node_id, role="terminal semantic"
        )
        if node.capability not in _SEMANTIC_IFF_CAPABILITIES:
            _fail(
                "candidate_exact_type_mismatch",
                "terminal semantic node does not provide an iff capability",
            )
        return node

    # Backward compatibility for frozen V2 tasks predating terminal_node_id:
    # choose by the explicit semantic capability, never by list-tail position.
    semantic_nodes = [
        node
        for node in task.gap_nodes
        if node.capability in _SEMANTIC_IFF_CAPABILITIES
    ]
    if len(semantic_nodes) != 1:
        _fail(
            "candidate_exact_type_mismatch",
            "capability DAG must expose exactly one terminal semantic iff node",
        )
    return semantic_nodes[0]


def _resolved_final_program_declaration(
    *, task: NPHardAuthoringTaskV2, public_fallback: str
) -> str:
    """Resolve an authored final program by node ID, or retain a public program."""

    explicit_node_id = getattr(task, "final_program_node_id", None)
    if isinstance(explicit_node_id, str) and explicit_node_id:
        node = _task_node_by_id(task, node_id=explicit_node_id, role="final program")
        if "PolyProg" not in node.exact_type:
            _fail(
                "candidate_exact_type_mismatch",
                "final program node exact type is not a PolyProg",
            )
        return node.declaration
    if public_fallback.strip():
        return public_fallback

    # This fallback is only for transitional callers that have already moved
    # authored-program identity into the capability DAG but not yet populated
    # final_program_node_id.  Ambiguity remains fail closed.
    candidates = [
        node
        for node in task.gap_nodes
        if node.capability
        in {
            "poly_program",
            "representation_adapter",
            *_TMKARP_PROGRAM_CAPABILITIES,
            *_DEPENDENT_COMPOSED_PROGRAM_CAPABILITIES,
            *_PROGRAM_INDEXED_PROGRAM_CAPABILITIES,
            *_PROGRAM_INDEXED_COMPOSED_PROGRAM_CAPABILITIES,
            "gadget_program",
            "gadget_composed_program",
        }
        and "PolyProg" in node.exact_type
    ]
    if len(candidates) != 1:
        _fail(
            "candidate_exact_type_mismatch",
            "capability DAG does not identify one final PolyProg node",
        )
    return candidates[0].declaration


def _candidate_source(
    *,
    task: NPHardAuthoringTaskV2,
    bodies: Mapping[str, str],
    include_final: bool,
    final_program_declaration: str,
    deletion_audit_deleted_declaration: str | None = None,
) -> str:
    if deletion_audit_deleted_declaration is not None and all(
        node.declaration != deletion_audit_deleted_declaration
        for node in task.gap_nodes
    ):
        _fail(
            "candidate_dependency_stale",
            "deletion audit selected a declaration outside the exact gap DAG",
        )
    imports = "\n".join(f"import {name}" for name in task.allowed_imports)
    declarations: list[str] = []
    asserted: list[str] = []
    for node in task.gap_nodes:
        if node.declaration == deletion_audit_deleted_declaration:
            continue
        if node.declaration not in bodies:
            break
        short_name = node.declaration.removeprefix(task.candidate_module + ".")
        declarations.append(
            f"noncomputable def {short_name} :\n    {node.exact_type} :=\n"
            + "\n".join(f"  {line}" for line in bodies[node.declaration].rstrip().splitlines())
            + "\n"
        )
        asserted.append(node.declaration)
    if include_final:
        semantic = _terminal_semantic_node(task).declaration
        resolved_program = _resolved_final_program_declaration(
            task=task, public_fallback=final_program_declaration
        )
        final_short = task.final_candidate_declaration.removeprefix(
            task.candidate_module + "."
        )
        declarations.append(
            f"noncomputable def {final_short} :\n    {task.final_exact_type} where\n"
            f"  program := {resolved_program}\n"
            f"  correct := {semantic}\n"
        )
        declarations.append(
            "def authoredHubRequest : ComplexityReduction.Protocol.TypedNPHardRequestV1 :=\n"
            f"  {{ problem := {task.source_problem.term} }}\n\n"
            "noncomputable def authoredHubResult :\n"
            "    ComplexityReduction.Protocol.TypedNPHardResultV1 authoredHubRequest :=\n"
            "  by_np_hard_resolver\n\n"
            "def authoredTargetRequest : ComplexityReduction.Protocol.TypedNPHardRequestV1 :=\n"
            f"  {{ problem := {task.target_problem.term} }}\n\n"
            "noncomputable def authoredTargetResult :\n"
            "    ComplexityReduction.Protocol.TypedNPHardResultV1 authoredTargetRequest :=\n"
            "  ComplexityReduction.Protocol.TypedNPHardResultV1.fromPath\n"
            "    authoredTargetRequest authoredHubResult.extractNativeHardness\n"
            f"    (.step {task.final_candidate_declaration})\n\n"
            "noncomputable def authoredExactNPHardness :\n"
            "    ComplexityReduction.Certificate.NativeTMNPHard "
            f"{task.target_problem.term} :=\n"
            "  authoredTargetResult.extractNativeHardness\n"
        )
        asserted.extend(
            [task.final_candidate_declaration, f"{task.candidate_module}.authoredExactNPHardness"]
        )
    axiom_audit = ",\n  ".join(asserted)
    return f"""{imports}

namespace {task.candidate_module}

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open {task.source_problem.module}
open {task.target_problem.module}

{chr(10).join(declarations)}
end {task.candidate_module}

assert_standard_axioms
  {axiom_audit}
"""


class NPHardGapRuntimeV1:
    """Run or resume one immutable multi-node NP-hard authoring task."""

    def __init__(
        self,
        *,
        root: Path,
        task: NPHardAuthoringTaskV2,
        output_root: Path,
        model: NPHardNodeModelClient,
        final_program_declaration: str,
        timeout_seconds: int | None = None,
        instance_call_budget: int | None = None,
    ):
        self.root = root.resolve()
        self.task = task
        self.output_root = output_root.resolve()
        self.model = model
        self.final_program_declaration = final_program_declaration
        self.timeout_seconds = timeout_seconds or task.timeout_seconds
        self.authoritative_dependency_evidence: tuple[tuple[str, str], ...] = ()
        task.validate()
        explicit_program_node = getattr(task, "final_program_node_id", None)
        if isinstance(explicit_program_node, str) and explicit_program_node:
            expected_program = _task_node_by_id(
                task, node_id=explicit_program_node, role="final program"
            ).declaration
            if final_program_declaration and final_program_declaration != expected_program:
                _fail(
                    "candidate_dependency_stale",
                    "orchestrator final program disagrees with the explicit DAG node",
                )
        minimum_call_budget = required_model_call_budget(
            gap_node_count=len(task.gap_nodes), attempt_budget=task.attempt_budget
        )
        self.instance_call_budget = (
            minimum_call_budget
            if instance_call_budget is None
            else instance_call_budget
        )
        if not minimum_call_budget <= self.instance_call_budget <= NP_HARD_MAX_INSTANCE_CALL_BUDGET:
            _fail(
                "authoring_gap_budget_exhausted",
                "runtime call budget is outside the full-DAG production policy",
            )

    def _publication_root(self, source_hash: str) -> Path:
        return self.output_root / "published" / source_hash.removeprefix("sha256:")

    def _load_publication_body(self, node: AcceptedCapabilityNodeV1) -> str:
        publication = self._publication_root(node.cumulative_source_sha256)
        source_path = publication / "Candidate.lean"
        body_path = publication / "body.lean"
        manifest_path = publication / "manifest.json"
        if not source_path.is_file() or not body_path.is_file() or not manifest_path.is_file():
            _fail("checkpoint_tampered", f"publication is missing for {node.node_id}")
        source = source_path.read_text(encoding="utf-8")
        body = body_path.read_text(encoding="utf-8")
        if sha256_id(source) != node.cumulative_source_sha256:
            _fail("candidate_tampered", f"published source changed for {node.node_id}")
        if sha256_id(body) != node.body_sha256:
            _fail("candidate_tampered", f"published body changed for {node.node_id}")
        if _tagged_file_hash(manifest_path) != node.publication_manifest_sha256:
            _fail("checkpoint_tampered", f"publication manifest changed for {node.node_id}")
        return body

    def _checkpoint(
        self,
        *,
        accepted: tuple[AcceptedCapabilityNodeV1, ...],
        total_model_calls: int,
        per_node_calls: Mapping[str, int],
        ledger: tuple[Mapping[str, Any], ...],
    ) -> NPHardGapCheckpointV1:
        arguments = {
            "task_request_id": self.task.request_id,
            "dependency_snapshot": _current_dependency_snapshot(
                root=self.root,
                task=self.task,
                accepted=accepted,
                authoritative_evidence=self.authoritative_dependency_evidence,
            ),
            "accepted_nodes": accepted,
            "remaining_gap_graph": tuple(
                node.to_dict() for node in self.task.gap_nodes[len(accepted) :]
            ),
            "total_model_calls": total_model_calls,
            "per_node_model_calls": tuple(sorted(per_node_calls.items())),
            "model_call_ledger": ledger,
        }
        provisional = NPHardGapCheckpointV1(
            checkpoint_hash="sha256:" + "0" * 64, **arguments
        )
        checkpoint = NPHardGapCheckpointV1(
            checkpoint_hash=provisional.computed_checkpoint_hash, **arguments
        )
        checkpoint.validate(self.task)
        return checkpoint

    def _write_checkpoint(self, checkpoint: NPHardGapCheckpointV1) -> tuple[Path, str]:
        path = self.output_root / "checkpoint.json"
        _write_json(path, checkpoint.to_dict(self.task))
        return path, _tagged_file_hash(path)

    def _load_checkpoint(
        self, *, checkpoint_path: Path, expected_file_sha256: str
    ) -> tuple[NPHardGapCheckpointV1, dict[str, str]]:
        checkpoint_path = checkpoint_path.resolve()
        if not checkpoint_path.is_file() or _tagged_file_hash(checkpoint_path) != expected_file_sha256:
            _fail("checkpoint_tampered", "checkpoint file bytes changed")
        try:
            value = json.loads(checkpoint_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            _fail("checkpoint_tampered", str(error))
        checkpoint = NPHardGapCheckpointV1.from_dict(value, task=self.task)
        current = _current_dependency_snapshot(
            root=self.root,
            task=self.task,
            accepted=checkpoint.accepted_nodes,
            authoritative_evidence=self.authoritative_dependency_evidence,
        )
        if current != checkpoint.dependency_snapshot:
            _fail("candidate_dependency_stale", "checkpoint dependency snapshot changed")
        bodies: dict[str, str] = {}
        for accepted in checkpoint.accepted_nodes:
            bodies[accepted.declaration] = self._load_publication_body(accepted)
        return checkpoint, bodies

    @staticmethod
    def _call_record(
        response: ModelResponse,
        *,
        request: NPHardNodeRequestV1,
        prompt: str,
        attempt: int,
        prompt_file: Path,
        response_file: Path,
    ) -> dict[str, Any]:
        return {
            "request_id": request.request_id,
            "node_id": request.node.node_id,
            "attempt": attempt,
            "prompt_sha256": sha256_id(prompt),
            "prompt_file": str(prompt_file),
            "called": response.called,
            "ok": response.ok,
            "status_code": response.status_code,
            "duration_seconds": response.duration_seconds,
            "usage": response.usage,
            "provider_attempts": response.attempts,
            "finish_reason": response.finish_reason,
            "response_sha256": sha256_id(response.content),
            "response_file": str(response_file),
            "error": response.error,
        }

    def run(
        self,
        *,
        resume_checkpoint_path: Path | None = None,
        expected_checkpoint_file_sha256: str | None = None,
        max_new_nodes: int | None = None,
    ) -> NPHardGapRuntimeResultV1:
        if self.output_root.exists() and resume_checkpoint_path is None and any(
            self.output_root.iterdir()
        ):
            _fail("checkpoint_tampered", "new G-C output directory must be fresh")
        self.output_root.mkdir(parents=True, exist_ok=True)
        commands: list[CommandResult] = []
        authoritative_evidence: list[Mapping[str, Any]] = []
        probe = _run_successor_only_chain_probe(
            root=self.root,
            task=self.task,
            output_root=self.output_root,
            timeout_seconds=self.timeout_seconds,
        )
        if probe is not None:
            evidence, command, bindings = probe
            authoritative_evidence.append(evidence)
            commands.append(command)
            self.authoritative_dependency_evidence = bindings
        resumed = resume_checkpoint_path is not None
        if resumed:
            if expected_checkpoint_file_sha256 is None:
                _fail("checkpoint_tampered", "resume requires the expected checkpoint file hash")
            checkpoint, bodies = self._load_checkpoint(
                checkpoint_path=resume_checkpoint_path,
                expected_file_sha256=expected_checkpoint_file_sha256,
            )
            accepted = list(checkpoint.accepted_nodes)
            total_model_calls = checkpoint.total_model_calls
            per_node_calls = dict(checkpoint.per_node_model_calls)
            ledger = list(checkpoint.model_call_ledger)
        else:
            bodies = {}
            accepted = []
            total_model_calls = 0
            per_node_calls = {}
            ledger = []

        worker_results: list[Mapping[str, Any]] = []
        fresh_rediscoveries = 0

        # A resume is not trusted until a fresh process reconstructs every
        # previously accepted cumulative publication.
        if resumed:
            for node in accepted:
                source_path = self._publication_root(node.cumulative_source_sha256) / "Candidate.lean"
                command = run_command(
                    ["lake", "env", "lean", str(source_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                commands.append(command)
                if not command.ok:
                    _fail("fresh_core_resolve_failed", f"resume could not rediscover {node.node_id}")
                fresh_rediscoveries += 1

        service_parent = self.output_root / "worker-services"
        service_parent.mkdir(parents=True, exist_ok=True)
        service_index = 1
        while (service_parent / f"run-{service_index:03d}").exists():
            service_index += 1
        service_root = service_parent / f"run-{service_index:03d}"
        pool = LeanWorkerPool(
            lean_root=self.root / "Lean",
            workspace_root=self.output_root,
            service_root=service_root,
            maximum_workers=1,
            timeout_seconds=self.timeout_seconds,
        )
        session_id = pool.start_session(
            owner=self.task.request_id, namespace=self.task.candidate_module
        )
        candidate_path = self.output_root / "work" / "Candidate.lean"
        candidate_path.parent.mkdir(parents=True, exist_ok=True)
        new_nodes = 0
        checkpoint_path: Path | None = resume_checkpoint_path
        checkpoint_file_hash: str | None = expected_checkpoint_file_sha256
        failure_code: str | None = None
        failure_message: str | None = None
        final_result: NPHardAuthoringResultV2 | None = None
        deletion_audits: list[Mapping[str, Any]] = []
        try:
            for ordinal in range(len(accepted) + 1, len(self.task.gap_nodes) + 1):
                if max_new_nodes is not None and new_nodes >= max_new_nodes:
                    break
                node = self.task.gap_nodes[ordinal - 1]
                dependency_snapshot = _current_dependency_snapshot(
                    root=self.root,
                    task=self.task,
                    accepted=tuple(accepted),
                    authoritative_evidence=self.authoritative_dependency_evidence,
                )
                request = _node_request(
                    task=self.task,
                    node_ordinal=ordinal,
                    dependency_snapshot=dependency_snapshot,
                    accepted=tuple(accepted),
                    total_model_calls=total_model_calls,
                    instance_call_budget=self.instance_call_budget,
                )
                diagnostic: str | None = None
                seen_bodies: set[str] = set()
                accepted_this_node = False
                for attempt in range(1, request.node_attempt_budget + 1):
                    if total_model_calls >= self.instance_call_budget:
                        failure_code = "authoring_gap_budget_exhausted"
                        failure_message = "instance model-call budget exhausted"
                        break
                    accepted_bodies = {
                        declaration: body for declaration, body in bodies.items()
                    }
                    prompt = build_np_hard_node_prompt_v1(
                        root=self.root,
                        task=self.task,
                        request=request,
                        accepted_bodies=accepted_bodies,
                        diagnostic=diagnostic,
                    )
                    response = self.model.complete_json(
                        system=NP_HARD_NODE_SYSTEM_PROMPT, prompt=prompt
                    )
                    model_root = self.output_root / "model-calls"
                    prompt_path = model_root / f"{node.node_id}-attempt-{attempt:02d}-prompt.json"
                    response_path = model_root / f"{node.node_id}-attempt-{attempt:02d}-response.json"
                    prompt_path.parent.mkdir(parents=True, exist_ok=True)
                    prompt_path.write_text(prompt, encoding="utf-8")
                    _write_json(
                        response_path,
                        {
                            "called": response.called,
                            "ok": response.ok,
                            "status_code": response.status_code,
                            "duration_seconds": response.duration_seconds,
                            "usage": response.usage,
                            "attempts": response.attempts,
                            "finish_reason": response.finish_reason,
                            "content": response.content,
                            "error": response.error,
                        },
                    )
                    if not response.called:
                        failure_code = "model_provider_unavailable"
                        failure_message = response.error or "model provider did not execute"
                        break
                    total_model_calls += 1
                    per_node_calls[node.node_id] = per_node_calls.get(node.node_id, 0) + 1
                    ledger.append(
                        self._call_record(
                            response,
                            request=request,
                            prompt=prompt,
                            attempt=attempt,
                            prompt_file=prompt_path,
                            response_file=response_path,
                        )
                    )
                    if not response.ok:
                        failure_code = "model_provider_unavailable"
                        failure_message = response.error or "model request failed"
                        break
                    try:
                        patch = parse_np_hard_node_patch_v1(
                            content=response.content, request=request, task=self.task
                        )
                    except NPHardGapRuntimeError as error:
                        failure_code = error.code
                        failure_message = error.message
                        if error.code == "invalid_np_hard_gap_runtime_schema":
                            diagnostic = (
                                "Response envelope was invalid. Return the exact response_template "
                                f"with every frozen field unchanged: {error.message}"
                            )
                            continue
                        break
                    body_hash = sha256_id(patch.replacement_body)
                    if body_hash in seen_bodies:
                        failure_code = "authoring_gap_budget_exhausted"
                        failure_message = "model repeated the same rejected candidate"
                        diagnostic = (
                            "The replacement body exactly repeated a rejected candidate. "
                            "Return a materially different body that addresses the last Lean diagnostic."
                        )
                        continue
                    seen_bodies.add(body_hash)
                    current_bodies = {**bodies, node.declaration: patch.replacement_body}
                    source = _candidate_source(
                        task=self.task,
                        bodies=current_bodies,
                        include_final=False,
                        final_program_declaration=self.final_program_declaration,
                    )
                    candidate_path.write_text(source, encoding="utf-8")
                    dependencies = tuple(
                        dict.fromkeys(
                            [
                                *(digest for _, digest in dependency_snapshot),
                                body_hash,
                            ]
                        )
                    )
                    key = LeanWorkerKey(
                        toolchain=(self.root / "Lean" / "lean-toolchain").read_text(
                            encoding="utf-8"
                        ).strip(),
                        lake_manifest_sha256=_tagged_file_hash(
                            self.root / "Lean" / "lake-manifest.json"
                        ),
                        base_registry_fingerprint=self.task.dependency_fingerprint,
                        complete_source_sha256=sha256_id(source),
                        dependency_sha256=dependencies,
                        namespace=self.task.candidate_module,
                        session_id=session_id,
                        editable_allowlist=(node.declaration,),
                    )
                    try:
                        worker = pool.validate(
                            session_id=session_id,
                            owner=self.task.request_id,
                            key=key,
                            source_path=candidate_path,
                            dependency_sha256=dependencies,
                            use_cache=False,
                            allow_cold_fallback=False,
                        )
                    except HardnessContractError as error:
                        failure_code = "lean_infrastructure_error"
                        failure_message = f"{error.code}: {error.message}"
                        break
                    worker_results.append(worker.to_dict())
                    if not worker.verified:
                        diagnostic = "\n".join(
                            str(item.get("message", "Lean rejected candidate"))
                            for item in worker.diagnostics
                        )[:8_000]
                        failure_code = (
                            "semantic_proof_failed"
                            if node.capability in _SEMANTIC_CAPABILITIES
                            else "program_synthesis_failed"
                        )
                        failure_message = diagnostic
                        continue

                    source_hash = sha256_id(source)
                    publication = self._publication_root(source_hash)
                    publication.mkdir(parents=True, exist_ok=False)
                    published_source = publication / "Candidate.lean"
                    body_path = publication / "body.lean"
                    manifest_path = publication / "manifest.json"
                    published_source.write_text(source, encoding="utf-8")
                    body_path.write_text(patch.replacement_body, encoding="utf-8")
                    fresh_path = publication / "FreshCore.lean"
                    fresh_path.write_text(
                        source + f"\n#check {node.declaration}\n", encoding="utf-8"
                    )
                    fresh = run_command(
                        ["lake", "env", "lean", str(fresh_path)],
                        cwd=self.root / "Lean",
                        timeout_seconds=self.timeout_seconds,
                    )
                    commands.append(fresh)
                    if not fresh.ok:
                        failure_code = "fresh_core_resolve_failed"
                        failure_message = f"fresh Core did not rediscover {node.node_id}"
                        break
                    fresh_rediscoveries += 1
                    manifest = {
                        "schema_version": NP_HARD_GAP_PUBLICATION_SCHEMA_V1,
                        "task_request_id": self.task.request_id,
                        "node_request_id": request.request_id,
                        "node_id": node.node_id,
                        "declaration": node.declaration,
                        "body_sha256": body_hash,
                        "cumulative_source_sha256": source_hash,
                        "worker_evidence_sha256": sha256_id(worker.to_dict()),
                        "fresh_core_evidence_sha256": sha256_id(fresh.to_dict()),
                        "dependency_snapshot": dict(dependency_snapshot),
                        "compiler_inserted_math_token_count": 0,
                    }
                    _write_json(manifest_path, manifest)
                    record = AcceptedCapabilityNodeV1(
                        node_id=node.node_id,
                        declaration=node.declaration,
                        body_sha256=body_hash,
                        cumulative_source_sha256=source_hash,
                        publication_manifest_sha256=_tagged_file_hash(manifest_path),
                        worker_evidence_sha256=sha256_id(worker.to_dict()),
                        fresh_core_evidence_sha256=sha256_id(fresh.to_dict()),
                    )
                    accepted.append(record)
                    bodies[node.declaration] = patch.replacement_body
                    checkpoint = self._checkpoint(
                        accepted=tuple(accepted),
                        total_model_calls=total_model_calls,
                        per_node_calls=per_node_calls,
                        ledger=tuple(ledger),
                    )
                    checkpoint_path, checkpoint_file_hash = self._write_checkpoint(checkpoint)
                    accepted_this_node = True
                    failure_code = None
                    failure_message = None
                    new_nodes += 1
                    break
                if not accepted_this_node:
                    break

            all_accepted = len(accepted) == len(self.task.gap_nodes)
            paused = not all_accepted and failure_code is None
            if all_accepted:
                final_source = _candidate_source(
                    task=self.task,
                    bodies=bodies,
                    include_final=True,
                    final_program_declaration=self.final_program_declaration,
                )
                final_path = self.output_root / "Final.lean"
                replay_path = self.output_root / "Replay.lean"
                final_path.write_text(final_source, encoding="utf-8")
                replay_path.write_text(final_source, encoding="utf-8")
                final_command = run_command(
                    ["lake", "env", "lean", str(final_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                replay_command = run_command(
                    ["lake", "env", "lean", str(replay_path)],
                    cwd=self.root / "Lean",
                    timeout_seconds=self.timeout_seconds,
                )
                commands.extend((final_command, replay_command))
                if not final_command.ok:
                    failure_code = "final_lean_failed"
                    failure_message = "exact NativeTMNPHard finalization failed"
                elif not replay_command.ok:
                    failure_code = "independent_replay_failed"
                    failure_message = "independent NativeTMNPHard replay failed"
                else:
                    audit_root = self.output_root / "deletion-audits"
                    audit_root.mkdir(parents=True, exist_ok=True)
                    for deleted in self.task.gap_nodes:
                        audit_bodies = {
                            declaration: body
                            for declaration, body in bodies.items()
                            if declaration != deleted.declaration
                        }
                        audit_source = _candidate_source(
                            task=self.task,
                            bodies=audit_bodies,
                            include_final=True,
                            final_program_declaration=self.final_program_declaration,
                            deletion_audit_deleted_declaration=deleted.declaration,
                        )
                        audit_path = audit_root / f"without-{deleted.node_id}.lean"
                        audit_path.write_text(audit_source, encoding="utf-8")
                        audit_command = run_command(
                            ["lake", "env", "lean", str(audit_path)],
                            cwd=self.root / "Lean",
                            timeout_seconds=self.timeout_seconds,
                        )
                        deletion_audits.append(
                            {
                                "node_id": deleted.node_id,
                                "declaration": deleted.declaration,
                                "body_sha256": dict(
                                    (node.node_id, node.body_sha256) for node in accepted
                                )[deleted.node_id],
                                "audit_file": str(audit_path),
                                "audit_file_sha256": _tagged_file_hash(audit_path),
                                "command": audit_command.to_dict(),
                                "diagnostic_matched": (
                                    _deletion_failure_mentions_declaration(
                                        audit_command, deleted.declaration
                                    )
                                ),
                                "passed": _deletion_failure_mentions_declaration(
                                    audit_command, deleted.declaration
                                ),
                            }
                        )
                    if not all(item["passed"] for item in deletion_audits):
                        failure_code = "deletion_audit_failed"
                        failure_message = (
                            "a final artifact remained valid after deleting a model-generated node"
                        )
                    else:
                        final_result = accepted_np_hard_authoring_result_v2(
                            task=self.task,
                            candidate_hashes={
                                node.node_id: node.body_sha256 for node in accepted
                            },
                            final_certificate=sha256_id(final_command.to_dict()),
                            replay_certificate=sha256_id(replay_command.to_dict()),
                            lean_diagnostics=(
                                "every node accepted by the persistent worker and fresh Core",
                                "exact NativeTMNPHard target finalized and replayed",
                            ),
                            policy_diagnostics=(
                                "source-to-target direction and exact endpoints remained frozen",
                                "every generated capability node is required by deletion audit",
                            ),
                            model_calls=tuple(ledger),
                        )
            status = (
                "VERIFIED"
                if final_result is not None
                else "CHECKPOINTED"
                if paused
                else "FAILED"
            )
            return NPHardGapRuntimeResultV1(
                status=status,
                task_request_id=self.task.request_id,
                accepted_nodes=tuple(node.node_id for node in accepted),
                fresh_core_rediscoveries=fresh_rediscoveries,
                model_calls=total_model_calls,
                checkpoint_path=str(checkpoint_path) if checkpoint_path else None,
                checkpoint_file_sha256=checkpoint_file_hash,
                result=final_result,
                failure_code=failure_code,
                failure_message=failure_message,
                commands=tuple(commands),
                worker_results=tuple(worker_results),
                resumed=resumed,
                model_call_ledger=tuple(ledger),
                deletion_audits=tuple(deletion_audits),
                authoritative_evidence=tuple(authoritative_evidence),
                authoritative_dependency_bindings=(
                    self.authoritative_dependency_evidence
                ),
            )
        finally:
            try:
                pool.close_session(session_id=session_id, owner=self.task.request_id)
            finally:
                pool.close()
