from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.stage_p_contract import StagePContractError
from agent.hardness.stage_p_publication import (
    StagePPromotionWaveBarrier,
    StagePPublicationManifest,
    StagePRunLocalPublishedRegistry,
)
from agent.hardness.stage_p_runtime import StagePGapCheckpoint


PUBLIC_MODULE = "Benchmark.Hardness.Inputs.StageP.ContractProbes"
SOURCE_TEXT = (
    f"import {PUBLIC_MODULE}\n\n"
    "namespace Generated.StageP\n\n"
    "theorem capability : True := by\n"
    "  exact True.intro\n\n"
    "#check capability\n"
    "assert_standard_axioms capability\n\n"
    "end Generated.StageP\n"
)


def digest(value: int) -> str:
    return f"sha256:{value:064x}"


def checkpoint(*, source_text: str = SOURCE_TEXT, gap_ordinal: int = 1) -> StagePGapCheckpoint:
    return StagePGapCheckpoint(
        request_id=digest(1),
        gap_id=digest(2 + gap_ordinal),
        ordinal=gap_ordinal,
        task_class="semantic_correctness",
        registry_fingerprint=digest(10 + gap_ordinal),
        dependency_hash=digest(20 + gap_ordinal),
        parent_checkpoint_hash=digest(30 + gap_ordinal),
        model_response_sha256=digest(40 + gap_ordinal),
        patch_sha256=digest(50 + gap_ordinal),
        candidate_source_sha256=sha256_id(source_text),
        diagnostics_sha256=digest(60 + gap_ordinal),
        bundle_sha256=digest(70 + gap_ordinal),
        axiom_audit_sha256=digest(80 + gap_ordinal),
    )


def registry(tmp_path: Path) -> StagePRunLocalPublishedRegistry:
    return StagePRunLocalPublishedRegistry(
        tmp_path / "published",
        run_id="stage-p-test-run",
        base_registry_fingerprint=digest(90),
    )


def manifest(
    published_registry: StagePRunLocalPublishedRegistry,
    validated: StagePGapCheckpoint,
    *,
    source_text: str = SOURCE_TEXT,
    provenance_kind: str = "model_generated",
    publication_role: str = "case_local",
) -> StagePPublicationManifest:
    return StagePPublicationManifest(
        run_id=published_registry.run_id,
        request_id=validated.request_id,
        gap_id=validated.gap_id,
        gap_ordinal=validated.ordinal,
        parent_checkpoint_hash=validated.parent_checkpoint_hash,
        checkpoint_prepublication_sha256=validated.checkpoint_hash,
        toolchain="leanprover/lean4:test",
        lake_manifest_sha256=digest(100),
        base_registry_fingerprint=validated.registry_fingerprint,
        publication_catalog_before_sha256=published_registry.catalog_fingerprint,
        input_source_sha256=digest(101),
        dependency_fingerprint=validated.dependency_hash,
        dependency_sha256=(digest(102), digest(103)),
        model_response_sha256=validated.model_response_sha256,
        patch_sha256=validated.patch_sha256,
        candidate_source_sha256=sha256_id(source_text),
        diagnostics_sha256=validated.diagnostics_sha256,
        bundle_sha256=validated.bundle_sha256,
        axiom_audit_sha256=validated.axiom_audit_sha256,
        fresh_core_precheck_sha256=digest(104),
        candidate_module="Generated.StageP.Capability",
        declaration="Generated.StageP.capability",
        exact_type_sha256=digest(105),
        capability_head=(
            "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof"
        ),
        source_endpoint_id=digest(106),
        target_endpoint_id=digest(107),
        direction="source_to_target",
        allowed_imports=(PUBLIC_MODULE,),
        provenance_kind=provenance_kind,
        compiler_inserted_math_token_count=0,
        publication_role=publication_role,
    )


def source_file(tmp_path: Path, text: str = SOURCE_TEXT) -> Path:
    path = tmp_path / "candidate" / "Capability.lean"
    path.parent.mkdir(parents=True)
    path.write_text(text, encoding="utf-8")
    return path


def unlock_pack(pack_root: Path) -> None:
    for path in sorted(pack_root.rglob("*"), key=lambda value: len(value.parts), reverse=True):
        path.chmod(0o755 if path.is_dir() else 0o644)
    pack_root.chmod(0o755)


def test_publication_is_content_addressed_read_only_and_consumer_visible(
    tmp_path: Path,
) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    candidate = source_file(tmp_path)
    candidate_hash = validated.candidate_source_sha256
    published_registry.register_job_local_candidate(candidate_hash)
    published_registry.assert_unpublished_isolation(candidate_hash)
    publication = manifest(published_registry, validated)

    published = published_registry.publish(
        manifest=publication,
        checkpoint=validated,
        candidate_source=candidate,
    )

    assert published.capability_hash == publication.capability_hash
    assert published.source_file.read_text(encoding="utf-8") == SOURCE_TEXT
    assert published.source_file.stat().st_mode & 0o222 == 0
    assert published.manifest_file.stat().st_mode & 0o222 == 0
    assert published_registry.require_visible(published.capability_hash) == published
    report = published_registry.to_dict()
    assert report["published_count"] == 1
    assert report["unpublished_candidate_count"] == 0
    assert report["provenance_counts"]["model_generated"] == 1
    assert report["catalog"]["entries"][0]["gap_id"] == validated.gap_id
    unlock_pack(published.pack_root)


def test_manifest_must_match_the_validated_checkpoint(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    mismatched = replace(manifest(published_registry, validated), patch_sha256=digest(999))
    with pytest.raises(StagePContractError) as captured:
        published_registry.publish(
            manifest=mismatched,
            checkpoint=validated,
            candidate_source=source_file(tmp_path),
        )
    assert captured.value.code == "candidate_dependency_stale"


def test_publication_rejects_stale_catalog_snapshot(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    stale = replace(
        manifest(published_registry, validated),
        publication_catalog_before_sha256=digest(998),
    )
    with pytest.raises(StagePContractError) as captured:
        published_registry.publish(
            manifest=stale,
            checkpoint=validated,
            candidate_source=source_file(tmp_path),
        )
    assert captured.value.code == "candidate_dependency_stale"


def test_publication_rejects_source_hash_change_after_validation(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    publication = manifest(published_registry, validated)
    changed = SOURCE_TEXT.replace("True.intro", "by\n  exact True.intro")
    with pytest.raises(StagePContractError) as captured:
        published_registry.publish(
            manifest=publication,
            checkpoint=validated,
            candidate_source=source_file(tmp_path, changed),
        )
    assert captured.value.code == "capability_publication_failed"


@pytest.mark.parametrize(
    ("unsafe_text", "expected_code"),
    [
        (SOURCE_TEXT.replace("exact True.intro", "sorry"), "sorry_axiom_or_unsafe_candidate"),
        (
            SOURCE_TEXT.replace(
                PUBLIC_MODULE,
                "Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility",
            ),
            "oracle_or_gold_import",
        ),
        (SOURCE_TEXT.replace("exact True.intro", "run_tac pure ()"), "sorry_axiom_or_unsafe_candidate"),
    ],
)
def test_publication_rechecks_candidate_security(
    tmp_path: Path, unsafe_text: str, expected_code: str
) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint(source_text=unsafe_text)
    publication = manifest(published_registry, validated, source_text=unsafe_text)
    with pytest.raises(StagePContractError) as captured:
        published_registry.publish(
            manifest=publication,
            checkpoint=validated,
            candidate_source=source_file(tmp_path, unsafe_text),
        )
    assert captured.value.code == expected_code


def test_deleted_published_source_is_not_accepted_from_memory(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    published = published_registry.publish(
        manifest=manifest(published_registry, validated),
        checkpoint=validated,
        candidate_source=source_file(tmp_path),
    )
    published.source_file.parent.chmod(0o755)
    published.source_file.unlink()
    with pytest.raises(StagePContractError) as captured:
        published_registry.require_visible(published.capability_hash)
    assert captured.value.code == "published_capability_not_visible"
    unlock_pack(published.pack_root)


def test_duplicate_gap_publication_is_rejected(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    candidate = source_file(tmp_path)
    first = published_registry.publish(
        manifest=manifest(published_registry, validated),
        checkpoint=validated,
        candidate_source=candidate,
    )
    duplicate = manifest(published_registry, validated)
    with pytest.raises(StagePContractError) as captured:
        published_registry.publish(
            manifest=duplicate,
            checkpoint=validated,
            candidate_source=candidate,
        )
    assert captured.value.code == "capability_publication_failed"
    unlock_pack(first.pack_root)


def test_producer_consumer_barrier_requires_empty_sealed_wave() -> None:
    barrier = StagePPromotionWaveBarrier()
    barrier.start(job_id="producer", wave="producer")
    with pytest.raises(StagePContractError) as active_error:
        barrier.start(job_id="consumer", wave="consumer")
    assert active_error.value.code == "published_capability_not_visible"
    with pytest.raises(StagePContractError) as seal_error:
        barrier.seal_producer_wave()
    assert seal_error.value.code == "capability_publication_failed"
    barrier.finish(job_id="producer")
    barrier.seal_producer_wave()
    with barrier.job(job_id="consumer", wave="consumer"):
        assert barrier.active_jobs == {"consumer": "consumer"}
    assert barrier.active_jobs == {}
    assert barrier.to_dict()["producer_wave_sealed"] is True


def test_consumer_is_strictly_zero_authoring() -> None:
    StagePPromotionWaveBarrier.assert_consumer_zero_authoring(
        model_calls=0, authoring_attempts=0
    )
    with pytest.raises(StagePContractError) as captured:
        StagePPromotionWaveBarrier.assert_consumer_zero_authoring(
            model_calls=1, authoring_attempts=0
        )
    assert captured.value.code == "consumer_authoring_forbidden"


def test_manifest_separates_fixture_and_model_generated_provenance(tmp_path: Path) -> None:
    published_registry = registry(tmp_path)
    validated = checkpoint()
    model_manifest = manifest(published_registry, validated, provenance_kind="model_generated")
    fixture_manifest = replace(model_manifest, provenance_kind="deterministic_fixture")
    assert model_manifest.capability_hash != fixture_manifest.capability_hash
    with pytest.raises(StagePContractError) as captured:
        replace(model_manifest, provenance_kind="template_disguised_as_model").validate()
    assert captured.value.code == "capability_publication_failed"
