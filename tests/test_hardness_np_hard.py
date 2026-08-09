from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.np_hard import (
    NP_HARD_DIRECTION,
    NPHardResolutionV1,
    build_np_hard_artifact_source,
    build_np_hard_goal_source,
    build_np_hard_probe_source,
    parse_np_hard_probe_output,
)
from agent.hardness.np_hard_benchmark import load_np_hard_mvp_suite


MARKER = "HARDNESS_NP_HARD"
SCHEMA = "hardness_np_hard_probe_v1"
NONCE = "0123456789abcdef"
PROBLEM = "Example.Clique.problem"
HUB = "Example.ThreeSAT.problem"
COMPLETE = "Example.ThreeSAT.nativeCompleteness"
ATOM = "Example.ThreeSAT.toClique"
FINGERPRINT = "lean:registry"


def row(kind: str, *fields: str) -> str:
    return "\t".join((MARKER, SCHEMA, NONCE, kind, *fields))


def successful_probe(*, direction: str = NP_HARD_DIRECTION) -> str:
    return "\n".join(
        (
            row("registry", FINGERPRINT),
            row("input", PROBLEM, "lean-whnf:input", "clique display", FINGERPRINT),
            row(
                "seed",
                HUB,
                "lean-whnf:hub",
                COMPLETE,
                "native_completeness_projection",
                FINGERPRINT,
            ),
            row(
                "resolved",
                "lean:request",
                "transported_hardness",
                HUB,
                "",
                COMPLETE,
                ATOM,
                "sharedGadget",
                "0",
                "1",
                FINGERPRINT,
                direction,
            ),
            row("reverse_audit", "lean:request", "false", FINGERPRINT),
        )
    )


def test_probe_parser_accepts_lean_selected_forward_hardness() -> None:
    probe = parse_np_hard_probe_output(
        stdout=successful_probe(),
        stderr="",
        nonce=NONCE,
        problem_declaration=PROBLEM,
    )
    assert probe.failure is None
    assert probe.resolution is not None
    assert probe.resolution.direction == "hardness_seed_to_problem"
    assert probe.resolution.hub_declaration == HUB
    assert probe.resolution.atoms == (ATOM,)
    assert probe.resolution.completeness_declaration == COMPLETE
    assert probe.seeds[0].evidence_kind == "native_completeness_projection"
    assert probe.seeds[0].entry_id.startswith("sha256:")


def test_probe_parser_rejects_direction_mutation() -> None:
    with pytest.raises(ValueError, match="frozen direction"):
        parse_np_hard_probe_output(
            stdout=successful_probe(direction="problem_to_hardness_seed"),
            stderr="",
            nonce=NONCE,
            problem_declaration=PROBLEM,
        )


def test_probe_parser_preserves_wrong_direction_only_failure() -> None:
    output = "\n".join(
        (
            row("registry", FINGERPRINT),
            row("input", PROBLEM, "lean-whnf:input", "display", FINGERPRINT),
            row(
                "failure",
                "lean:request",
                "wrong_direction_only",
                COMPLETE,
                "",
                "only input to hub exists",
                FINGERPRINT,
            ),
            row("reverse_audit", "lean:request", "true", FINGERPRINT),
        )
    )
    probe = parse_np_hard_probe_output(
        stdout=output,
        stderr="",
        nonce=NONCE,
        problem_declaration=PROBLEM,
    )
    assert probe.resolution is None
    assert probe.failure is not None
    assert probe.failure.code == "wrong_direction_only"
    assert probe.reverse_only is True


def test_artifact_emits_explicit_hub_path_result_and_final_hardness() -> None:
    resolution = NPHardResolutionV1(
        request_id="lean:request",
        evidence_kind="transported_hardness",
        hub_declaration=HUB,
        hardness_declaration=None,
        completeness_declaration=COMPLETE,
        atoms=(ATOM,),
        roles=("sharedGadget",),
        final_composition_count=0,
        unique_dependency_count=1,
        registry_fingerprint=FINGERPRINT,
    )
    source = build_np_hard_artifact_source(
        input_module="Example.Clique",
        problem_declaration=PROBLEM,
        resolution=resolution,
    )
    assert "def request : ComplexityReduction.Protocol.TypedNPHardRequestV1" in source
    assert "def selectedHubHardness" in source
    assert "def selectedPath" in source
    assert "TypedNPHardResultV1.fromPath" in source
    assert "theorem problemIsNPHard" in source
    assert "NativeTMNPHard Example.Clique.problem" in source
    assert "by_np_hard_resolver" in source
    assert "NativeTMInNP Example.Clique.problem" not in source
    assert "assert_standard_axioms" in source
    with pytest.raises(ValueError, match="frozen"):
        build_np_hard_artifact_source(
            input_module="Example.Clique",
            problem_declaration=PROBLEM,
            resolution=replace(resolution, direction="problem_to_hardness_seed"),
        )


def test_goal_and_probe_sources_freeze_the_v1_request() -> None:
    goal = build_np_hard_goal_source(
        input_module="Example.Clique", problem_declaration=PROBLEM
    )
    assert "TypedNPHardRequestV1" in goal
    assert f"problem := {PROBLEM}" in goal
    assert "target" not in goal
    probe = build_np_hard_probe_source(
        input_module="Example.Clique",
        problem_declaration=PROBLEM,
        nonce=NONCE,
    )
    assert "#hardness_agent_probe_np_hard_v1" in probe
    assert PROBLEM in probe


def test_formal_np_hard_mvp_suite_has_positive_multi_edge_and_typed_negatives() -> None:
    suite = load_np_hard_mvp_suite(
        Path("Benchmark/Hardness/Suites/np_hard_mvp.json")
    )
    assert any(case.expected_status == "VERIFIED" for case in suite)
    assert any("multi-edge" in case.tags for case in suite)
    assert {
        case.expected_failure_code
        for case in suite
        if case.expected_status == "BLOCKED"
    } == {"wrong_direction_only", "no_forward_path_from_hardness_seed"}
