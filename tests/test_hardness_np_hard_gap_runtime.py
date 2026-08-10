import hashlib
import json
import shutil
import tempfile
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.lean_runner import (
    RUNTIME_MODULE,
    module_file,
    sha256_file,
)
from agent.hardness.models import CommandResult, sha256_id
from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_authoring import (
    NPHardAuthoringContractError,
    NPHardAuthoringEndpointV2,
    NPHardAuthoringObligationV2,
    NPHardAuthoringTaskV2,
    _module_public_source_file_v2,
    _successor_only_observer_chain_payload_v2,
    build_np_hard_authoring_tasks_v2,
    validate_successor_only_authoritative_evidence_v2,
)
from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2
from agent.hardness.np_hard_gap_runtime import (
    NP_HARD_NODE_PATCH_SCHEMA_V1,
    NPHardGapCheckpointV1,
    NPHardGapRuntimeError,
    NPHardGapRuntimeV1,
    _assert_gadget_indexed_prompt_surface,
    _candidate_source,
    _deletion_failure_mentions_declaration,
    _dependent_composition_successor,
    _gadget_indexed_admission_source,
    _current_dependency_snapshot,
    _node_request,
    _recommended_first_body,
    _run_successor_only_chain_probe,
    _resolved_final_program_declaration,
    _terminal_semantic_node,
    _tmkarp_admission_source,
    _validate_gadget_indexed_patch_binding,
    _validate_tmkarp_patch_binding,
    build_np_hard_node_prompt_v1,
    parse_np_hard_node_patch_v1,
)
from agent.hardness.np_hard_generalization import load_np_hard_generalization_suite


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Gate" / "Suites" / "np_hard_generalization.json"
H_J_5_CASES = (
    (
        "ComplexityReduction.Presentation.MaxCut",
        "ComplexityReduction.Presentation.MaxCut.structuredProblem",
    ),
    (
        "ComplexityReduction.Presentation.MaxCutBinary",
        "ComplexityReduction.Presentation.MaxCutBinary.binaryStructuredProblem",
    ),
)


def tasks():
    return build_np_hard_authoring_tasks_v2(root=ROOT, suite_path=SUITE)


@pytest.fixture(scope="module")
def h_j_5_tasks(tmp_path_factory) -> tuple[NPHardAuthoringTaskV2, ...]:
    output = tmp_path_factory.mktemp("np-hard-h-j-5-gap-runtime")
    return tuple(
        NPHardAuthoringPlannerV2(
            root=ROOT,
            input_module=module,
            input_problem_declaration=problem,
            output_dir=output / f"case-{index}",
        ).plan().task
        for index, (module, problem) in enumerate(H_J_5_CASES)
    )


def request(task, ordinal: int = 1):
    return _node_request(
        task=task,
        node_ordinal=ordinal,
        dependency_snapshot=_current_dependency_snapshot(
            root=ROOT, task=task, accepted=()
        ),
        accepted=(),
        total_model_calls=0,
    )


def patch_payload(task, node_request, body: str = "by\n  rfl\n"):
    return {
        "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
        "action": "submit_node_patch",
        "request_id": node_request.request_id,
        "node_id": node_request.node.node_id,
        "declaration": node_request.node.declaration,
        "dependency_fingerprint": node_request.dependency_fingerprint,
        "replacement_body": body,
    }


def _reissue_h_j_5_task(
    task: NPHardAuthoringTaskV2, **changes
) -> NPHardAuthoringTaskV2:
    provisional = replace(
        task,
        **changes,
        request_id="sha256:" + "0" * 64,
    )
    return replace(provisional, request_id=provisional.computed_request_id)


def _fully_self_signed_unrelated_successor_task(
    *,
    structured: NPHardAuthoringTaskV2,
    binary: NPHardAuthoringTaskV2,
) -> NPHardAuthoringTaskV2:
    unrelated = structured.composition_intermediate
    old_intermediate = binary.composition_intermediate
    assert unrelated is not None and old_intermediate is not None
    exact_types = dict(binary.observed_capability_exact_types)
    tmkarp_head, tmkarp_source, _ = exact_types["tmkarp-primitive"].split()
    exact_types["tmkarp-primitive"] = (
        f"{tmkarp_head} {tmkarp_source} "
        f"{unrelated.term}.toEncodedDecisionProblem"
    )
    successor_head, _, successor_target = exact_types[
        "composed-program"
    ].split()
    exact_types["composed-program"] = (
        f"{successor_head} {unrelated.term} {successor_target}"
    )

    admission = dict(binary.composition_admission_observation or ())
    successor = dict(binary.composition_successor_observation or ())
    fake_intermediate_node = "lean-whnf:4242424242"
    admission.update(
        target=unrelated.term,
        target_node=fake_intermediate_node,
        exact_type=exact_types["tmkarp-primitive"],
    )
    admission["id"] = (
        f"{admission['capability_kind']}:{admission['source_node']}:"
        f"{admission['target_node']}"
    )
    successor.update(
        source=unrelated.term,
        source_node=fake_intermediate_node,
        exact_type=exact_types["composed-program"],
    )
    successor["id"] = (
        f"{successor['capability_kind']}:{successor['source_node']}:"
        f"{successor['target_node']}"
    )

    allowed_imports = tuple(
        dict.fromkeys(
            (
                binary.target_problem.module,
                binary.source_problem.module,
                RUNTIME_MODULE,
                unrelated.module,
                binary.composition_successor_module,
                admission["module"],
            )
        )
    )
    public_modules = (
        binary.source_problem.module,
        binary.target_problem.module,
        unrelated.module,
        binary.composition_successor_module,
        admission["module"],
    )
    public_files = tuple(
        sorted(
            {
                _module_public_source_file_v2(module)
                for module in public_modules
                if module is not None
            }
        )
    )
    dependencies = {
        name: digest
        for name, digest in binary.dependency_hashes
        if not name.startswith(("module:", "public:"))
    }
    for module in allowed_imports:
        assert module is not None
        dependencies[f"module:{module}"] = (
            "sha256:" + sha256_file(module_file(ROOT / "Lean", module))
        )
    for relative in public_files:
        dependencies[f"public:{relative}"] = (
            "sha256:" + sha256_file(ROOT / relative)
        )
    dependencies[
        "content:observed-capability-exact-type:tmkarp-primitive"
    ] = sha256_id(exact_types["tmkarp-primitive"])
    dependencies[
        "content:observed-capability-exact-type:composed-program"
    ] = sha256_id(exact_types["composed-program"])
    dependencies["content:observed-composition-successor-source"] = (
        sha256_id(unrelated.term)
    )
    dependencies["content:observed-composition-successor-target"] = (
        sha256_id(binary.target_problem.term)
    )
    dependencies["content:lean-successor-only-tmkarp-admission"] = (
        sha256_id(admission)
    )
    dependencies["content:lean-certified-successor"] = sha256_id(successor)
    dependencies["content:lean-typed-capability"] = sha256_id(
        {
            key: value
            for key, value in admission.items()
            if key != "registry_fingerprint"
        }
    )
    dependencies["content:lean-typed-capability-chain"] = sha256_id(
        _successor_only_observer_chain_payload_v2(
            admission=admission,
            successor=successor,
            canonical_successor_source=unrelated.term,
            canonical_successor_target=binary.target_problem.term,
        )
    )
    gap_nodes = tuple(
        replace(
            node,
            exact_type=node.exact_type.replace(
                old_intermediate.term, unrelated.term
            ),
        )
        for node in binary.gap_nodes
    )
    return _reissue_h_j_5_task(
        binary,
        composition_intermediate=unrelated,
        composition_successor_source=unrelated.term,
        composition_successor_target=binary.target_problem.term,
        composition_admission_observation=tuple(sorted(admission.items())),
        composition_successor_observation=tuple(sorted(successor.items())),
        observed_capability_exact_types=tuple(sorted(exact_types.items())),
        allowed_imports=allowed_imports,
        public_source_files=public_files,
        dependency_hashes=tuple(sorted(dependencies.items())),
        gap_nodes=gap_nodes,
    )


class EchoRecommendedBodyModel:
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "recommended_first_body" in prompt
        payload = json.loads(prompt)
        content = json.dumps(payload["response_template"], sort_keys=True)
        return ModelResponse(
            called=True,
            ok=True,
            content=content,
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


class NeverModel:
    def __init__(self) -> None:
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        self.calls += 1
        raise AssertionError("authoritative Lean probe must run before the model")


def test_node_requests_expose_exactly_one_topological_gap() -> None:
    counts = [len(task.gap_nodes) for task in tasks()]
    assert counts == [1, 2, 2, 2, 5]
    for task in tasks():
        node_request = request(task)
        assert node_request.node == task.gap_nodes[0]
        assert node_request.node_attempt_budget == 4
        assert node_request.instance_call_budget_remaining == len(task.gap_nodes) * 4
        assert node_request.request_id == node_request.computed_request_id


def test_node_patch_accepts_only_the_active_declaration() -> None:
    task = tasks()[0]
    node_request = request(task)
    parsed = parse_np_hard_node_patch_v1(
        content=json.dumps(patch_payload(task, node_request)),
        request=node_request,
        task=task,
    )
    assert parsed.declaration == task.gap_nodes[0].declaration
    assert parsed.replacement_body.endswith("\n")


def test_node_patch_allows_instance_type_projection() -> None:
    task = tasks()[0]
    node_request = request(task)
    projected = patch_payload(
        task,
        node_request,
        "fun input : Benchmark.Public.source.Instance => input",
    )
    parsed = parse_np_hard_node_patch_v1(
        content=json.dumps(projected), request=node_request, task=task
    )
    assert ".Instance" in parsed.replacement_body


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        (lambda value: value.update(request_id="sha256:" + "0" * 64), "candidate_dependency_stale"),
        (lambda value: value.update(node_id="other-node"), "candidate_dependency_stale"),
        (lambda value: value.update(declaration="Generated.Other.escape"), "candidate_outside_edit_boundary"),
        (lambda value: value.update(dependency_fingerprint="sha256:" + "1" * 64), "candidate_dependency_stale"),
        (lambda value: value.update(replacement_body="by\n  import Bad.Module"), "import_not_allowlisted"),
        (lambda value: value.update(replacement_body="by\n  exact sorry"), "candidate_nonstandard_axiom"),
        (lambda value: value.update(replacement_body="by\n  exact GoldProof.answer"), "oracle_or_gold_import"),
    ],
)
def test_node_patch_mutations_fail_closed(mutation, code: str) -> None:
    task = tasks()[0]
    node_request = request(task)
    value = patch_payload(task, node_request)
    mutation(value)
    with pytest.raises(NPHardGapRuntimeError) as captured:
        parse_np_hard_node_patch_v1(
            content=json.dumps(value), request=node_request, task=task
        )
    assert captured.value.code == code


def test_node_patch_rejects_extra_envelope_field() -> None:
    task = tasks()[0]
    node_request = request(task)
    value = patch_payload(task, node_request)
    value["extra_declaration"] = "escape"
    with pytest.raises(NPHardGapRuntimeError) as captured:
        parse_np_hard_node_patch_v1(
            content=json.dumps(value), request=node_request, task=task
        )
    assert captured.value.code == "invalid_np_hard_gap_runtime_schema"


def test_node_prompt_contains_no_benchmark_answer_metadata() -> None:
    task = tasks()[0]
    node_request = request(task)
    prompt = build_np_hard_node_prompt_v1(
        root=ROOT,
        task=task,
        request=node_request,
        accepted_bodies={},
        diagnostic=None,
    ).lower()
    for marker in ('"case_id"', '"expected"', ".gold.", ".oracles."):
        assert marker not in prompt
    assert "polyprog.comp (after : polyprog middle target)" in prompt
    assert "polyprog.const (source target : lawfulencodedtype)" in prompt


def test_node_prompt_selects_only_the_public_semantic_shape_recipe() -> None:
    task = tasks()[0]
    payload = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=task,
            request=request(task),
            accepted_bodies={},
            diagnostic=None,
        )
    )
    assert "false_tag" in payload["proof_recipes"]
    assert "conjunction_identity" not in payload["proof_recipes"]
    serialized = json.dumps(payload).lower()
    assert ".gold." not in serialized and ".oracles." not in serialized


def test_h_j_capability_recommendations_are_generic_and_dependency_driven() -> None:
    adapter = NPHardAuthoringObligationV2(
        node_id="representation-adapter",
        declaration="Generated.Typed.representationAdapter",
        capability="representation_adapter",
        exact_type="PolyProg Example.source.representation Example.target.representation",
        depends_on=(),
    )
    forward = NPHardAuthoringObligationV2(
        node_id="semantic-forward",
        declaration="Generated.Typed.semanticForward",
        capability="semantic_forward",
        exact_type="forall input, SourceAccepts input -> TargetAccepts input",
        depends_on=(adapter.node_id,),
    )
    reverse = NPHardAuthoringObligationV2(
        node_id="semantic-reverse",
        declaration="Generated.Typed.semanticReverse",
        capability="semantic_reverse",
        exact_type="forall input, TargetAccepts input -> SourceAccepts input",
        depends_on=(adapter.node_id,),
    )
    semantic = NPHardAuthoringObligationV2(
        node_id="semantic-iff",
        declaration="Generated.Typed.semanticIff",
        capability="semantic_iff",
        exact_type="forall input, SourceAccepts input <-> TargetAccepts input",
        depends_on=(forward.node_id, reverse.node_id),
    )
    task = SimpleNamespace(
        source_problem=SimpleNamespace(term="Example.source"),
        gap_nodes=(adapter, forward, reverse, semantic),
        observed_capability_terms=((adapter.node_id, "Example.observedAdapter"),),
    )

    assert _recommended_first_body(
        task=task,
        request=SimpleNamespace(node=adapter),
        public_sources={},
    ) == "by\n  exact Example.observedAdapter"
    assert _recommended_first_body(
        task=SimpleNamespace(
            source_problem=task.source_problem,
            gap_nodes=task.gap_nodes,
            observed_capability_terms=(),
        ),
        request=SimpleNamespace(node=adapter),
        public_sources={},
    ) == (
        "PolyProg.pair (PolyProg.const Example.source.representation "
        "StandardInstances.bool false) "
        "(PolyProg.id Example.source.representation)"
    )
    for implication in (forward, reverse):
        assert _recommended_first_body(
            task=task,
            request=SimpleNamespace(node=implication),
            public_sources={},
        ) == "by\n  intro input accepted\n  exact accepted"
    assert _recommended_first_body(
        task=task,
        request=SimpleNamespace(node=semantic),
        public_sources={},
    ) == (
        "by\n  intro input\n  exact "
        "\u27e8Generated.Typed.semanticForward input, "
        "Generated.Typed.semanticReverse input\u27e9"
    )


def test_h_j_tmkarp_admission_recommendations_are_exactly_observer_bound() -> None:
    primitive = NPHardAuthoringObligationV2(
        node_id="tmkarp-primitive",
        declaration="Generated.TMKarp.tmkarpPrimitive",
        capability="tmkarp_primitive",
        exact_type="Primitive Example.source.representation Example.target.representation",
        depends_on=(),
    )
    program = NPHardAuthoringObligationV2(
        node_id="tmkarp-program",
        declaration="Generated.TMKarp.tmkarpProgram",
        capability="tmkarp_program",
        exact_type="PolyProg Example.source.representation Example.target.representation",
        depends_on=(primitive.node_id,),
    )
    semantic = NPHardAuthoringObligationV2(
        node_id="tmkarp-semantic-iff",
        declaration="Generated.TMKarp.tmkarpSemanticIff",
        capability="tmkarp_semantic_iff",
        exact_type=(
            "forall input, Example.source.accepts input <-> "
            "Example.target.accepts (Generated.TMKarp.tmkarpProgram.run input)"
        ),
        depends_on=(program.node_id,),
    )
    witness = "Example.AuthoringSources.exactTMKarpReduction"
    task = SimpleNamespace(
        task_class="typed_tmkarp_admission_dag",
        gap_nodes=(primitive, program, semantic),
        observed_capability_terms=((primitive.node_id, witness),),
        observed_capability_exact_types=(
            (
                primitive.node_id,
                "ComplexityReduction.TMKarpReduction "
                "Example.source.toEncodedDecisionProblem "
                "Example.target.toEncodedDecisionProblem",
            ),
        ),
    )

    admission = _tmkarp_admission_source(task)
    assert admission["node_id"] == primitive.node_id
    assert admission["witness"] == witness
    expected = {
        primitive.node_id: (
            "by\n  exact Primitive.ofTMPolyTime "
            f"{witness}.f {witness}.polytime"
        ),
        program.node_id: f"by\n  exact PolyProg.atom {primitive.declaration}",
        semantic.node_id: (
            "by\n  intro input\n  simpa only ["
            f"{program.declaration}, {primitive.declaration}, "
            "PolyProg.run_atom, Primitive.run_ofTMPolyTime] using\n"
            f"    {witness}.correct input"
        ),
    }
    for node in task.gap_nodes:
        node_request = SimpleNamespace(node=node)
        body = _recommended_first_body(
            task=task, request=node_request, public_sources={}
        )
        assert body == expected[node.node_id]
        _validate_tmkarp_patch_binding(
            task=task, request=node_request, body=body
        )


def test_h_j_tmkarp_admission_rejects_transitive_raw_route_substitution() -> None:
    primitive = NPHardAuthoringObligationV2(
        node_id="tmkarp-primitive",
        declaration="Generated.TMKarp.tmkarpPrimitive",
        capability="tmkarp_primitive",
        exact_type="Primitive Example.source.representation Example.target.representation",
        depends_on=(),
    )
    program = NPHardAuthoringObligationV2(
        node_id="tmkarp-program",
        declaration="Generated.TMKarp.tmkarpProgram",
        capability="tmkarp_program",
        exact_type="PolyProg Example.source.representation Example.target.representation",
        depends_on=(primitive.node_id,),
    )
    semantic = NPHardAuthoringObligationV2(
        node_id="tmkarp-semantic-iff",
        declaration="Generated.TMKarp.tmkarpSemanticIff",
        capability="tmkarp_semantic_iff",
        exact_type="forall input, Source input <-> Target input",
        depends_on=(program.node_id,),
    )
    task = SimpleNamespace(
        task_class="typed_tmkarp_admission_dag",
        gap_nodes=(primitive, program, semantic),
        observed_capability_terms=(
            (primitive.node_id, "Example.AuthoringSources.exactTMKarpReduction"),
        ),
        observed_capability_exact_types=(
            (
                primitive.node_id,
                "ComplexityReduction.TMKarpReduction Source Target",
            ),
        ),
    )
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _validate_tmkarp_patch_binding(
            task=task,
            request=SimpleNamespace(node=primitive),
            body=(
                "by\n  exact Primitive.ofTMPolyTime "
                "ComplexityReduction.Karp21.SetPacking."
                "cliqueToSetPackingStructuredTMKarpReduction.f "
                "ComplexityReduction.Karp21.SetPacking."
                "cliqueToSetPackingStructuredTMKarpReduction.polytime"
            ),
        )
    assert captured.value.code == "candidate_outside_edit_boundary"


def test_h_j_5_runtime_rejects_exact_type_and_successor_mutations(
    h_j_5_tasks,
) -> None:
    structured, binary = h_j_5_tasks
    _gadget_indexed_admission_source(structured)
    _tmkarp_admission_source(binary)
    _dependent_composition_successor(binary)

    binary_exact_types = dict(binary.observed_capability_exact_types)
    tmkarp_exact = binary_exact_types["tmkarp-primitive"]
    tmkarp_head, tmkarp_source, tmkarp_target = tmkarp_exact.split()
    invalid_tmkarp = (
        f"{tmkarp_head} {tmkarp_target} {tmkarp_source}",
        (
            f"{tmkarp_head} {tmkarp_target} {tmkarp_source} "
            f"{tmkarp_source} {tmkarp_target}"
        ),
        f"Example.Wrapper ({tmkarp_exact})",
    )
    for exact_type in invalid_tmkarp:
        observed = dict(binary_exact_types)
        observed["tmkarp-primitive"] = exact_type
        with pytest.raises(NPHardGapRuntimeError) as captured:
            _tmkarp_admission_source(
                replace(
                    binary,
                    observed_capability_exact_types=tuple(
                        sorted(observed.items())
                    ),
                )
            )
        assert captured.value.code == "candidate_exact_type_mismatch"

    gadget_exact_types = dict(structured.observed_capability_exact_types)
    gadget_exact = gadget_exact_types["gadget-reference-audit"]
    gadget_head, gadget_source, gadget_reference, gadget_target = (
        gadget_exact.split()
    )
    invalid_gadget = (
        f"{gadget_head} {gadget_target} {gadget_reference} {gadget_source}",
        (
            f"{gadget_head} {gadget_target} {gadget_reference} {gadget_source} "
            f"{gadget_source} {gadget_reference} {gadget_target}"
        ),
        f"Example.Wrapper ({gadget_exact})",
    )
    for exact_type in invalid_gadget:
        observed = dict(gadget_exact_types)
        observed["gadget-reference-audit"] = exact_type
        with pytest.raises(NPHardGapRuntimeError) as captured:
            _gadget_indexed_admission_source(
                replace(
                    structured,
                    observed_capability_exact_types=tuple(
                        sorted(observed.items())
                    ),
                )
            )
        assert captured.value.code == "candidate_exact_type_mismatch"

    successor_exact = binary_exact_types["composed-program"]
    successor_head, successor_source, successor_target = successor_exact.split()
    invalid_successors = (
        f"{successor_head} {successor_target} {successor_source}",
        f"{successor_head} Example.Wrong.source {successor_target}",
        f"{successor_head} {successor_source} Example.Wrong.target",
        f"Example.Wrapper ({successor_exact})",
    )
    for exact_type in invalid_successors:
        observed = dict(binary_exact_types)
        observed["composed-program"] = exact_type
        with pytest.raises(NPHardGapRuntimeError) as captured:
            _dependent_composition_successor(
                replace(
                    binary,
                    observed_capability_exact_types=tuple(
                        sorted(observed.items())
                    ),
                )
            )
        assert captured.value.code == "candidate_exact_type_mismatch"

    terms = dict(binary.observed_capability_terms)
    terms["composed-program"] = "Example.Unrelated.fakeCertifiedReduction"
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _dependent_composition_successor(
            replace(
                binary,
                observed_capability_terms=tuple(sorted(terms.items())),
            )
        )
    assert captured.value.code == "fabricated_declaration_handle"

    for task, module, resolver in (
        (
            structured,
            "ComplexityReduction.Presentation.MaxCutBinary",
            _gadget_indexed_admission_source,
        ),
        (
            binary,
            "ComplexityReduction.Agent.Hardness.GadgetAuthoringSources",
            _tmkarp_admission_source,
        ),
    ):
        dependencies = dict(task.dependency_hashes)
        dependencies[f"module:{module}"] = (
            "sha256:" + sha256_file(module_file(ROOT / "Lean", module))
        )
        extra_surface = replace(
            task,
            allowed_imports=(*task.allowed_imports, module),
            dependency_hashes=tuple(sorted(dependencies.items())),
        )
        with pytest.raises(NPHardGapRuntimeError) as captured:
            resolver(extra_surface)
        assert captured.value.code == "candidate_outside_edit_boundary"

    assert structured.composition_intermediate is not None
    unrelated_intermediate = structured.composition_intermediate
    observed = dict(binary_exact_types)
    observed["tmkarp-primitive"] = (
        f"{tmkarp_head} {tmkarp_source} "
        f"{unrelated_intermediate.term}.toEncodedDecisionProblem"
    )
    dependencies = dict(binary.dependency_hashes)
    dependencies[f"module:{unrelated_intermediate.module}"] = (
        "sha256:" + "0" * 64
    )
    unrelated_chain = replace(
        binary,
        composition_intermediate=unrelated_intermediate,
        observed_capability_exact_types=tuple(sorted(observed.items())),
        dependency_hashes=tuple(sorted(dependencies.items())),
        allowed_imports=tuple(
            dict.fromkeys((*binary.allowed_imports, unrelated_intermediate.module))
        ),
    )
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _dependent_composition_successor(unrelated_chain)
    assert captured.value.code == "candidate_outside_edit_boundary"


def test_h_j_5_gadget_prompt_surface_and_exact_body_binding(
    h_j_5_tasks,
) -> None:
    structured, _ = h_j_5_tasks
    public_sources = {
        relative: (ROOT / relative).read_text(encoding="utf-8")
        for relative in structured.public_source_files
    }
    _assert_gadget_indexed_prompt_surface(public_sources)
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _assert_gadget_indexed_prompt_surface(
            {"SuccessorAuthoringSources.lean": "def shortcut := True"}
        )
    assert captured.value.code == "candidate_outside_edit_boundary"
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _assert_gadget_indexed_prompt_surface(
            public_sources,
            allowed_imports=(
                "ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources",
            ),
        )
    assert captured.value.code == "candidate_outside_edit_boundary"

    for node in structured.gap_nodes:
        node_request = SimpleNamespace(node=node)
        body = _recommended_first_body(
            task=structured,
            request=node_request,
            public_sources={},
        )
        assert body is not None
        _validate_gadget_indexed_patch_binding(
            task=structured,
            request=node_request,
            body=body,
        )

    first_request = SimpleNamespace(node=structured.gap_nodes[0])
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _validate_gadget_indexed_patch_binding(
            task=structured,
            request=first_request,
            body="by\n  exact True.intro",
        )
    assert captured.value.code == "candidate_dependency_stale"
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _validate_gadget_indexed_patch_binding(
            task=structured,
            request=first_request,
            body=(
                "by\n  exact ComplexityReduction.Agent.Hardness."
                "SuccessorAuthoringSources."
                "threeSATToMaxCutSuccessorOnlyTMKarpReduction"
            ),
        )
    assert captured.value.code == "candidate_outside_edit_boundary"


def test_h_j_5_deletion_diagnostic_requires_fully_qualified_name() -> None:
    declaration = "Generated.NPHardV2.Cabc.Authoring.gadgetProgram"

    def command(message: str, *, timed_out: bool = False) -> CommandResult:
        return CommandResult(
            command=("lake", "env", "lean", "Probe.lean"),
            exit_code=1,
            stdout="",
            stderr=message,
            duration_seconds=0.01,
            timed_out=timed_out,
        )

    assert not _deletion_failure_mentions_declaration(
        command("error: unknown identifier `gadgetProgram`"), declaration
    )
    assert not _deletion_failure_mentions_declaration(
        command(
            "error: unknown identifier `gadgetProgram`; "
            f"while checking `{declaration}`"
        ),
        declaration,
    )
    assert _deletion_failure_mentions_declaration(
        command(f"error: unknown identifier `{declaration}`"), declaration
    )
    assert _deletion_failure_mentions_declaration(
        command(f"error: unknown identifier `{declaration}.run`"), declaration
    )
    assert not _deletion_failure_mentions_declaration(
        command("error: unknown identifier `Example.Unrelated.gadgetProgram`"),
        declaration,
    )
    assert not _deletion_failure_mentions_declaration(
        command(f"error: unknown identifier `{declaration}`", timed_out=True),
        declaration,
    )


def test_h_j_5_authoritative_successor_probe_and_shared_validation(
    h_j_5_tasks,
    tmp_path,
) -> None:
    _, binary = h_j_5_tasks
    result = _run_successor_only_chain_probe(
        root=ROOT,
        task=binary,
        output_root=tmp_path / "valid-successor-probe",
        timeout_seconds=600,
    )
    assert result is not None
    evidence, command, bindings = result
    runtime = {
        "authoritative_evidence": [evidence],
        "authoritative_dependency_bindings": dict(bindings),
        "commands": [command.to_dict()],
    }
    assert validate_successor_only_authoritative_evidence_v2(
        task=binary,
        runtime=runtime,
        case_output=tmp_path,
        require_files=False,
    ) == bindings

    tampered = dict(runtime)
    tampered["authoritative_dependency_bindings"] = {}
    with pytest.raises(NPHardAuthoringContractError) as captured:
        validate_successor_only_authoritative_evidence_v2(
            task=binary,
            runtime=tampered,
            case_output=tmp_path,
            require_files=False,
        )
    assert captured.value.code == "candidate_dependency_stale"


def test_h_j_5_fully_self_signed_chain_fails_before_model(
    h_j_5_tasks,
    tmp_path,
) -> None:
    structured, binary = h_j_5_tasks
    forged = _fully_self_signed_unrelated_successor_task(
        structured=structured,
        binary=binary,
    )
    forged.validate()
    _tmkarp_admission_source(forged)
    _dependent_composition_successor(forged)
    model = NeverModel()
    final_program = next(
        node.declaration
        for node in forged.gap_nodes
        if node.node_id == forged.final_program_node_id
    )
    runtime = NPHardGapRuntimeV1(
        root=ROOT,
        task=forged,
        output_root=tmp_path / "forged-successor-chain",
        model=model,
        final_program_declaration=final_program,
        timeout_seconds=600,
    )
    with pytest.raises(NPHardGapRuntimeError) as captured:
        runtime.run()
    assert captured.value.code == "candidate_exact_type_mismatch"
    assert model.calls == 0
    evidence_path = (
        tmp_path
        / "forged-successor-chain"
        / "authoritative-evidence"
        / "successor-only-chain"
        / "evidence.json"
    )
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    assert evidence["passed"] is False
    assert evidence["command"]["exit_code"] != 0
    assert evidence["command"]["timed_out"] is False


def _dependent_composition_task():
    source = NPHardAuthoringEndpointV2(module="Example.Source", term="Example.source")
    middle = NPHardAuthoringEndpointV2(module="Example.Middle", term="Example.middle")
    target = NPHardAuthoringEndpointV2(module="Example.Target", term="Example.target")
    primitive = NPHardAuthoringObligationV2(
        node_id="tmkarp-primitive",
        declaration="Generated.Dependent.tmKarpPrimitive",
        capability="tmkarp_primitive",
        exact_type="Primitive Example.source.representation Example.middle.representation",
        depends_on=(),
    )
    admission_program = NPHardAuthoringObligationV2(
        node_id="tmkarp-program",
        declaration="Generated.Dependent.tmKarpProgram",
        capability="tmkarp_program",
        exact_type="PolyProg Example.source.representation Example.middle.representation",
        depends_on=(primitive.node_id,),
    )
    admission_semantic = NPHardAuthoringObligationV2(
        node_id="tmkarp-semantic-iff",
        declaration="Generated.Dependent.tmKarpSemanticCorrect",
        capability="tmkarp_semantic_iff",
        exact_type=(
            "forall input, Example.source.accepts input <-> "
            "Example.middle.accepts (Generated.Dependent.tmKarpProgram.run input)"
        ),
        depends_on=(admission_program.node_id,),
    )
    composed_program = NPHardAuthoringObligationV2(
        node_id="composed-program",
        declaration="Generated.Dependent.composedProgram",
        capability="dependent_composed_program",
        exact_type="PolyProg Example.source.representation Example.target.representation",
        depends_on=(admission_program.node_id,),
    )
    composed_semantic = NPHardAuthoringObligationV2(
        node_id="composed-semantic-iff",
        declaration="Generated.Dependent.composedSemanticCorrect",
        capability="dependent_composed_semantic_iff",
        exact_type=(
            "forall input, Example.source.accepts input <-> "
            "Example.target.accepts (Generated.Dependent.composedProgram.run input)"
        ),
        depends_on=(admission_semantic.node_id, composed_program.node_id),
    )
    admission_module = (
        "ComplexityReduction.Agent.Hardness.AuthoringSources"
    )
    admission = f"{admission_module}.sourceToMiddleTMKarpReduction"
    successor = "Example.Routes.MiddleToTarget.certifiedReduction"
    successor_module = "Example.Routes.MiddleToTarget.Unified"
    allowed_imports = (
        target.module,
        source.module,
        RUNTIME_MODULE,
        middle.module,
        successor_module,
        admission_module,
    )
    public_source_files = tuple(
        sorted(
            {
                _module_public_source_file_v2(module)
                for module in (
                    source.module,
                    target.module,
                    middle.module,
                    successor_module,
                    admission_module,
                )
            }
        )
    )
    dependency_hashes = {
        f"module:{module}": "sha256:" + "0" * 64
        for module in allowed_imports
    }
    dependency_hashes.update(
        {
            f"public:{relative}": "sha256:" + "0" * 64
            for relative in public_source_files
        }
    )
    dependency_hashes[
        "content:observed-capability-module:composed-program"
    ] = sha256_id(successor_module)
    task = SimpleNamespace(
        task_class="typed_tmkarp_dependent_composition_dag",
        source_problem=source,
        target_problem=target,
        composition_intermediate=middle,
        composition_successor_module=successor_module,
        allowed_imports=allowed_imports,
        public_source_files=public_source_files,
        dependency_hashes=tuple(sorted(dependency_hashes.items())),
        gap_nodes=(
            primitive,
            admission_program,
            admission_semantic,
            composed_program,
            composed_semantic,
        ),
        observed_capability_terms=(
            (primitive.node_id, admission),
            (composed_program.node_id, successor),
        ),
        observed_capability_exact_types=(
            (
                primitive.node_id,
                "ComplexityReduction.TMKarpReduction "
                "Example.source.toEncodedDecisionProblem "
                "Example.middle.toEncodedDecisionProblem",
            ),
            (
                composed_program.node_id,
                "ComplexityReduction.Certificate.CertifiedReduction "
                "Example.middle Example.target",
            ),
        ),
    )
    return task, admission, successor


def test_h_j_dependent_composition_recommendations_bind_both_segments() -> None:
    task, admission, successor = _dependent_composition_task()
    primitive, admission_program, admission_semantic, composed_program, composed_semantic = (
        task.gap_nodes
    )
    resolved = _dependent_composition_successor(task)
    assert resolved["witness"] == successor
    assert resolved["intermediate_term"] == task.composition_intermediate.term
    expected = {
        primitive.node_id: (
            "by\n  exact Primitive.ofTMPolyTime "
            f"{admission}.f {admission}.polytime"
        ),
        admission_program.node_id: (
            f"by\n  exact PolyProg.atom {primitive.declaration}"
        ),
        admission_semantic.node_id: (
            "by\n  intro input\n  simpa only ["
            f"{admission_program.declaration}, {primitive.declaration}, "
            "PolyProg.run_atom, Primitive.run_ofTMPolyTime] using\n"
            f"    {admission}.correct input"
        ),
        composed_program.node_id: (
            f"by\n  exact PolyProg.comp {successor}.program "
            f"{admission_program.declaration}"
        ),
        composed_semantic.node_id: (
            "by\n  intro input\n"
            f"  change {task.source_problem.term}.accepts input ↔\n"
            f"    {task.target_problem.term}.accepts ({successor}.program.run "
            f"({admission_program.declaration}.run input))\n"
            f"  exact ({admission_semantic.declaration} input).trans\n"
            f"    ({successor}.correct ({admission_program.declaration}.run input))"
        ),
    }
    for node in task.gap_nodes:
        node_request = SimpleNamespace(node=node)
        body = _recommended_first_body(
            task=task, request=node_request, public_sources={}
        )
        assert body == expected[node.node_id]
        _validate_tmkarp_patch_binding(
            task=task, request=node_request, body=body
        )


def test_h_j_dependent_composition_rejects_successor_only_dead_let() -> None:
    task, _, successor = _dependent_composition_task()
    admission_program = task.gap_nodes[1]
    composed_program = task.gap_nodes[3]
    with pytest.raises(NPHardGapRuntimeError) as captured:
        _validate_tmkarp_patch_binding(
            task=task,
            request=SimpleNamespace(node=composed_program),
            body=(
                "by\n  let _ := "
                f"{admission_program.declaration}\n  exact {successor}.program"
            ),
        )
    assert captured.value.code == "candidate_dependency_stale"


def test_terminal_semantic_and_final_program_resolve_by_explicit_node_id() -> None:
    semantic = NPHardAuthoringObligationV2(
        node_id="semantic-iff",
        declaration="Generated.Typed.semanticIff",
        capability="semantic_iff",
        exact_type="forall input, SourceAccepts input <-> TargetAccepts input",
        depends_on=(),
    )
    adapter = NPHardAuthoringObligationV2(
        node_id="representation-adapter",
        declaration="Generated.Typed.representationAdapter",
        capability="representation_adapter",
        exact_type="PolyProg Example.source.representation Example.target.representation",
        depends_on=(),
    )
    task = SimpleNamespace(
        # Deliberately put the semantic node first: runtime selection must not
        # depend on a list tail convention.
        gap_nodes=(semantic, adapter),
        terminal_node_id=semantic.node_id,
        final_program_node_id=adapter.node_id,
    )
    assert _terminal_semantic_node(task) == semantic
    assert _resolved_final_program_declaration(
        task=task, public_fallback="Public.wrongFallback"
    ) == adapter.declaration


def test_runtime_rejects_orchestrator_program_that_disagrees_with_dag(
    tmp_path,
) -> None:
    task = next(task for task in tasks() if task.final_program_node_id is not None)
    with pytest.raises(NPHardGapRuntimeError) as captured:
        NPHardGapRuntimeV1(
            root=ROOT,
            task=task,
            output_root=tmp_path / "program-mismatch",
            model=EchoRecommendedBodyModel(),
            final_program_declaration="Generated.Unrelated.program",
        )
    assert captured.value.code == "candidate_dependency_stale"


def test_deletion_audit_keeps_later_nodes_but_incremental_build_stays_prefix() -> None:
    task = next(task for task in tasks() if len(task.gap_nodes) >= 5)
    deleted = task.gap_nodes[0]
    bodies = {
        node.declaration: "by\n  rfl\n"
        for node in task.gap_nodes
        if node.declaration != deleted.declaration
    }

    incremental = _candidate_source(
        task=task,
        bodies=bodies,
        include_final=False,
        final_program_declaration="",
    )
    assert all(
        "noncomputable def "
        + node.declaration.removeprefix(task.candidate_module + ".")
        + " :"
        not in incremental
        for node in task.gap_nodes[1:]
    )

    audit = _candidate_source(
        task=task,
        bodies=bodies,
        include_final=True,
        final_program_declaration="",
        deletion_audit_deleted_declaration=deleted.declaration,
    )
    deleted_marker = (
        "noncomputable def "
        + deleted.declaration.removeprefix(task.candidate_module + ".")
        + " :"
    )
    assert deleted_marker not in audit
    assert all(
        "noncomputable def "
        + node.declaration.removeprefix(task.candidate_module + ".")
        + " :"
        in audit
        for node in task.gap_nodes[1:]
    )
    final_marker = (
        "noncomputable def "
        + task.final_candidate_declaration.removeprefix(task.candidate_module + ".")
        + " :"
    )
    assert final_marker in audit


def test_public_shape_recommendations_compile_end_to_end() -> None:
    suite = load_np_hard_generalization_suite(SUITE, root=ROOT)
    cases = [case for case in suite.cases if case.kind == "model_authoring"]
    run_root = Path(
        tempfile.mkdtemp(prefix="pytest-public-shape-", dir=ROOT / "tmp")
    )
    try:
        for case, task in zip(cases, tasks(), strict=True):
            authoring = case.authoring
            assert authoring is not None
            if task.task_class == "semantic_proof":
                final_program = authoring["program_reference"]
            else:
                suffix = (
                    "composedProgram"
                    if task.task_class == "program_composition"
                    else "synthesizedProgram"
                )
                final_program = f"{task.candidate_module}.{suffix}"
            result = NPHardGapRuntimeV1(
                root=ROOT,
                task=task,
                output_root=run_root / case.id,
                model=EchoRecommendedBodyModel(),
                final_program_declaration=final_program,
                timeout_seconds=600,
            ).run()
            assert result.status == "VERIFIED", (
                case.id,
                result.failure_code,
                result.failure_message,
            )
            assert result.model_calls == len(task.gap_nodes)
            assert len(result.accepted_nodes) == len(task.gap_nodes)
            assert all(not row["fallback_used"] for row in result.worker_results)
    finally:
        shutil.rmtree(run_root)


def test_checkpoint_content_hash_detects_mutation() -> None:
    task = tasks()[0]
    arguments = {
        "task_request_id": task.request_id,
        "dependency_snapshot": _current_dependency_snapshot(
            root=ROOT, task=task, accepted=()
        ),
        "accepted_nodes": (),
        "remaining_gap_graph": tuple(node.to_dict() for node in task.gap_nodes),
        "total_model_calls": 0,
        "per_node_model_calls": (),
        "model_call_ledger": (),
    }
    provisional = NPHardGapCheckpointV1(
        checkpoint_hash="sha256:" + "0" * 64, **arguments
    )
    checkpoint = replace(
        provisional, checkpoint_hash=provisional.computed_checkpoint_hash
    )
    checkpoint.validate(task)
    value = checkpoint.to_dict(task)
    value["total_model_calls"] = 1
    with pytest.raises(NPHardGapRuntimeError) as captured:
        NPHardGapCheckpointV1.from_dict(value, task=task)
    assert captured.value.code == "checkpoint_tampered"


def test_formal_g_c_report_satisfies_exit_conditions() -> None:
    path = ROOT / "Reports" / "NP_HARD_GAP_RUNTIME_REPORT.json"
    if not path.is_file():
        pytest.skip("formal G-C runtime report has not been generated")
    report = json.loads(path.read_text(encoding="utf-8"))
    metrics = report["metrics"]
    assert report["passed"] is True
    assert metrics["task_count"] == metrics["verified_task_count"] == 5
    assert metrics["accepted_node_count"] == 12
    assert metrics["multi_gap_verified_count"] >= 1
    assert metrics["program_synthesis_verified_count"] == 1
    assert metrics["nontrivial_semantic_verified_count"] == 2
    assert metrics["fresh_core_rediscovery_count"] >= 12
    assert metrics["checkpoint_resume_verified_count"] == 1
    assert metrics["exact_native_np_hard_final_count"] == 5
    assert metrics["independent_replay_count"] == 5
    assert metrics["persistent_worker_count_per_session"] == 1
    assert metrics["worker_fallback_count"] == 0
    assert metrics["compiler_inserted_math_token_count"] == 0
    assert all(report["tamper_audits"].values())
    # G-C is a completed historical qualification.  Its provenance must stay
    # frozen when the active plan advances to later work packages.
    assert len(report["active_plan_sha256"]) == 64
    int(report["active_plan_sha256"], 16)


def test_full_45_case_report_is_content_addressed_and_complete() -> None:
    summary_path = ROOT / "Reports" / "MAIN_G_C_45_FULL_REPORT.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    raw_path = ROOT / summary["raw_report"]["file"]
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    assert summary["passed"] is True
    assert hashlib.sha256(raw_path.read_bytes()).hexdigest() == summary["raw_report"]["sha256"]
    assert raw["total"] == raw["passed"] == 45
    assert raw["failed"] == 0
    assert summary["counts"]["positive_verified_count"] == 29
    assert summary["counts"]["negative_expected_outcome_count"] == 16
    assert summary["real_model"]["http_ok_count"] == 1
    assert summary["real_model"]["status_code"] == 200
    assert all(summary["gates"].values())
