"""Deterministic, case-agnostic Stage P fixtures for offline qualification."""

from __future__ import annotations

import json
from dataclasses import dataclass

from .models import sha256_id
from .stage_p_candidate_validation import (
    StagePCandidateExpectation,
    StagePCandidateObservation,
)
from .stage_p_contract import STAGE_P_PATCH_SCHEMA
from .stage_p_model_authoring import (
    StagePBoundAuthoringTask,
    StagePCandidateSource,
    StagePRepairSession,
)
from .stage_p_runtime import StagePImmutableRequest, StagePRuntimeGap


FIXTURE_IMPORT = "Benchmark.Hardness.Inputs.StageP.ContractProbes"
FIXTURE_SIGNATURE = f"{FIXTURE_IMPORT}.proofProbe"
FIXTURE_HEAD = "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof"


@dataclass(frozen=True)
class StagePOfflineFixture:
    seed: int
    namespace: str
    request: StagePImmutableRequest
    gap: StagePRuntimeGap
    task: StagePBoundAuthoringTask
    candidate: StagePCandidateSource
    expectation: StagePCandidateExpectation
    observation: StagePCandidateObservation

    def repair_session(self) -> StagePRepairSession:
        return StagePRepairSession(task=self.task, candidate=self.candidate)

    def submit_patch_content(
        self,
        *,
        replacement_body: str = "by\n  intro value\n  rfl",
        base_source_sha256: str | None = None,
        editable_file: str | None = None,
        editable_region: str | None = None,
        helper_handles: tuple[str, ...] = (),
        binding_overrides: dict[str, str] | None = None,
    ) -> str:
        protocol = self.task.protocol_task(
            base_source_sha256=base_source_sha256 or self.candidate.source_sha256
        )
        binding = {
            "source_endpoint": protocol.source_endpoint,
            "target_endpoint": protocol.target_endpoint,
            "direction": protocol.direction,
            "objective": protocol.objective,
            "capability_head": protocol.capability_head,
            "declaration_signature": protocol.declaration_signature,
        }
        binding.update(binding_overrides or {})
        return json.dumps(
            {
                "schema_version": STAGE_P_PATCH_SCHEMA,
                "action": "submit_patch",
                "session_id": protocol.session_id,
                "gap_id": protocol.gap_id,
                "task_class": protocol.task_class,
                "base_source_sha256": base_source_sha256
                or protocol.base_source_sha256,
                "editable_file": editable_file or protocol.editable_file,
                "editable_region": editable_region or protocol.editable_region,
                "replacement_body": replacement_body,
                "helper_handles": list(helper_handles),
                "binding_claim": binding,
            },
            sort_keys=True,
        )


def build_stage_p_offline_fixture(seed: int = 1) -> StagePOfflineFixture:
    namespace = f"StageP.Offline.M{seed}"
    request = StagePImmutableRequest(
        source_declaration="StageP.Offline.Source",
        target_declaration="StageP.Offline.Target",
        source_endpoint_id=sha256_id({"seed": seed, "endpoint": "source"}),
        target_endpoint_id=sha256_id({"seed": seed, "endpoint": "target"}),
        objective="reduce_to",
        direction="source_to_target",
        request_policy_sha256=sha256_id({"seed": seed, "policy": "strict"}),
        resolved_parameters_sha256=sha256_id(
            {"seed": seed, "parameters": []}
        ),
        base_registry_fingerprint=sha256_id(
            {"seed": seed, "registry": "base"}
        ),
        max_gap_count=4,
    )
    gap = StagePRuntimeGap(
        request_id=request.request_id,
        ordinal=1,
        task_class="semantic_correctness",
        capability_head=FIXTURE_HEAD,
        declaration_signature=FIXTURE_SIGNATURE,
        source_endpoint_id=request.source_endpoint_id,
        target_endpoint_id=request.target_endpoint_id,
        registry_fingerprint=request.base_registry_fingerprint,
        dependency_hash=sha256_id({"seed": seed, "dependency": 1}),
        parent_checkpoint_hash=request.initial_checkpoint_hash,
    )
    candidate_declaration = f"{namespace}.capability"
    task = StagePBoundAuthoringTask(
        request=request,
        gap=gap,
        candidate_module=namespace,
        candidate_declaration=candidate_declaration,
        declaration_signature=FIXTURE_SIGNATURE,
        expected_type=FIXTURE_SIGNATURE,
        editable_file="Generated/StageP/Capability.lean",
        editable_region="candidate_body",
        allowed_imports=(FIXTURE_IMPORT,),
        helper_handles=(),
        semantic_turn_budget=4,
        token_budget=30_000,
    )
    candidate = StagePCandidateSource(
        fixed_header=(
            f"import {FIXTURE_IMPORT}\n\n"
            f"namespace {namespace}\n\n"
            f"def capability : {FIXTURE_SIGNATURE} :=\n"
        ),
        editable_body="by\n  intro value\n  exact Eq.refl value\n",
        fixed_footer=f"\nend {namespace}\n",
        allowed_imports=(FIXTURE_IMPORT,),
    )
    candidate.validate()
    expectation = StagePCandidateExpectation.from_gap(
        request=request,
        gap=gap,
        candidate_declaration=candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
    )
    observation = StagePCandidateObservation(
        request_id=request.request_id,
        gap_id=gap.gap_id,
        candidate_declaration=candidate_declaration,
        candidate_source_sha256=candidate.source_sha256,
        diagnostics_sha256=sha256_id({"seed": seed, "diagnostics": []}),
        observed_exact_type_sha256=expectation.exact_type_sha256,
        observed_capability_head=expectation.capability_head,
        observed_source_endpoint_id=expectation.source_endpoint_id,
        observed_target_endpoint_id=expectation.target_endpoint_id,
        observed_direction=expectation.direction,
        observed_dependency_fingerprint=expectation.dependency_fingerprint,
        observed_program_index_sha256=None,
        axiom_audit_sha256=sha256_id({"seed": seed, "axiom": "standard"}),
        bundle_sha256=sha256_id({"seed": seed, "bundle": "valid"}),
        static_policy_verified=True,
        lean_verified=True,
        axiom_verified=True,
        bundle_verified=True,
    )
    return StagePOfflineFixture(
        seed=seed,
        namespace=namespace,
        request=request,
        gap=gap,
        task=task,
        candidate=candidate,
        expectation=expectation,
        observation=observation,
    )
