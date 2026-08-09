from dataclasses import replace

import pytest

from agent.hardness.connection_catalog import (
    DIRECT_RELATION,
    ConnectionCatalog,
    ConnectionCatalogEntry,
)
from agent.hardness.hardness_target_catalog import (
    NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION,
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
)
from agent.hardness.problem_catalog import ProblemCatalog, ProblemCatalogEntry
from agent.hardness.transported_hardness_catalog import (
    TRANSPORTED_HARDNESS_CONSTRUCTOR,
    build_transported_hardness_catalog,
    build_transported_hardness_validation_source,
)


FINGERPRINT = "lean:transport-fixture"
TOOLCHAIN = "leanprover/lean4:test"
MANIFEST = "a" * 64
HUB_NODE = "lean-whnf:hub"
MIDDLE_NODE = "lean-whnf:middle"
TARGET_NODE = "lean-whnf:target"


def problem(declaration: str, node_id: str) -> ProblemCatalogEntry:
    return ProblemCatalogEntry(
        declaration=declaration,
        declaration_kind="definition",
        display=declaration.rsplit(".", 1)[0],
        problem_node_id=node_id,
        semantic_summary=f"semantic {node_id}",
        representation_summary=f"representation {node_id}",
        encoder_bound_identity_summary=f"codec {node_id}",
        referenced_constants=(),
        registered=True,
        registry_fingerprint=FINGERPRINT,
        accepts_summary="fun _ => True",
        accepts_node_id=f"{node_id}-accepts",
        domain_summary="Fixture.Instance",
        domain_node_id="lean-whnf:fixture-domain",
        representation_node_id="lean-whnf:fixture-representation",
        encoder_bound_identity_node_id="lean-whnf:fixture-codec",
    )


def connection(
    declaration: str,
    source_node_id: str,
    target_node_id: str,
    *,
    role: str,
) -> ConnectionCatalogEntry:
    return ConnectionCatalogEntry(
        certificate_declaration=declaration,
        capability_kind="certified_reduction",
        relation=DIRECT_RELATION,
        direction="forward",
        term_kind="certificate",
        projection_declaration=declaration,
        lean_term=declaration,
        source_fingerprint=f"lean:{source_node_id}",
        target_fingerprint=f"lean:{target_node_id}",
        source_node_id=source_node_id,
        target_node_id=target_node_id,
        source_display=source_node_id,
        target_display=target_node_id,
        component_role=role,
        registry_fingerprint=FINGERPRINT,
    )


def fixture_catalogs() -> tuple[ProblemCatalog, ConnectionCatalog, HardnessTargetCatalog]:
    problems = ProblemCatalog(
        registry_fingerprint=FINGERPRINT,
        entries=(
            problem("Fixture.Hub.problem", HUB_NODE),
            problem("Fixture.Middle.problem", MIDDLE_NODE),
            problem("Fixture.Target.problem", TARGET_NODE),
        ),
        toolchain=TOOLCHAIN,
        lake_manifest_sha256=MANIFEST,
    )
    # Two parallel first edges exercise deterministic canonical selection.  The
    # back edge must not enter a transported simple path.
    connections = ConnectionCatalog(
        registry_fingerprint=FINGERPRINT,
        entries=(
            connection(
                "Fixture.Routes.zHubToMiddle",
                HUB_NODE,
                MIDDLE_NODE,
                role="ingress",
            ),
            connection(
                "Fixture.Routes.aHubToMiddle",
                HUB_NODE,
                MIDDLE_NODE,
                role="ingress",
            ),
            connection(
                "Fixture.Routes.middleToTarget",
                MIDDLE_NODE,
                TARGET_NODE,
                role="sharedGadget",
            ),
            connection(
                "Fixture.Routes.targetBackToHub",
                TARGET_NODE,
                HUB_NODE,
                role="egress",
            ),
        ),
        toolchain=TOOLCHAIN,
        lake_manifest_sha256=MANIFEST,
    )
    completeness = HardnessTargetEvidence(
        target_declaration="Fixture.Hub.problem",
        target_node_id=HUB_NODE,
        evidence_kind="native_completeness",
        evidence_declaration="Fixture.Hub.nativeComplete",
        evidence_lean_term="Fixture.Hub.nativeComplete",
        membership_lean_term=(
            f"{NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION} "
            "Fixture.Hub.nativeComplete"
        ),
        satisfied_policies=("native_np", "native_np_hard", "native_np_complete"),
        validation_source="lean_fixture",
        provenance_declarations=(
            "Fixture.Hub.nativeComplete",
            NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION,
        ),
        registry_fingerprint=FINGERPRINT,
    )
    native_targets = HardnessTargetCatalog(
        registry_fingerprint=FINGERPRINT,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration="Fixture.Hub.problem",
                target_display="hub",
                target_node_id=HUB_NODE,
                target_namespace="Fixture.Hub",
                registry_fingerprint=FINGERPRINT,
                evidences=(completeness,),
            ),
        ),
        toolchain=TOOLCHAIN,
        lake_manifest_sha256=MANIFEST,
    )
    return problems, connections, native_targets


def test_transported_catalog_derives_canonical_simple_shortest_paths() -> None:
    problems, connections, native_targets = fixture_catalogs()
    build = build_transported_hardness_catalog(
        problem_catalog=problems,
        connection_catalog=connections,
        native_target_catalog=native_targets,
        maximum_transport_atoms=2,
    )

    by_target = {path.target_declaration: path for path in build.paths}
    assert set(by_target) == {"Fixture.Middle.problem", "Fixture.Target.problem"}
    assert by_target["Fixture.Middle.problem"].reduction_declarations == (
        "Fixture.Routes.aHubToMiddle",
    )
    assert by_target["Fixture.Target.problem"].reduction_declarations == (
        "Fixture.Routes.aHubToMiddle",
        "Fixture.Routes.middleToTarget",
    )
    assert all(
        "Fixture.Routes.targetBackToHub" not in path.reduction_declarations
        for path in build.paths
    )

    target = next(
        entry
        for entry in build.catalog.entries
        if entry.target_declaration == "Fixture.Target.problem"
    )
    evidence = target.evidences[0]
    assert evidence.evidence_kind == "transported_native_hardness"
    assert evidence.satisfied_policies == ("native_np_hard",)
    assert evidence.membership_lean_term == ""
    assert evidence.evidence_lean_term.startswith(TRANSPORTED_HARDNESS_CONSTRUCTOR)
    assert evidence.evidence_lean_term.index("Fixture.Routes.aHubToMiddle") < (
        evidence.evidence_lean_term.index("Fixture.Routes.middleToTarget")
    )


def test_transported_catalog_validation_batches_every_derived_proof() -> None:
    problems, connections, native_targets = fixture_catalogs()
    build = build_transported_hardness_catalog(
        problem_catalog=problems,
        connection_catalog=connections,
        native_target_catalog=native_targets,
        maximum_transport_atoms=2,
    )

    source = build_transported_hardness_validation_source(build)

    assert source.count("noncomputable def evidence") == len(build.paths)
    assert source.count(TRANSPORTED_HARDNESS_CONSTRUCTOR) == len(build.paths)
    assert source.count("assert_standard_axioms") == 1
    audit = source.split("assert_standard_axioms", 1)[1]
    assert audit.count(".evidence") == len(build.paths)


def test_transported_catalog_rejects_stale_or_mismatched_catalogs() -> None:
    problems, connections, native_targets = fixture_catalogs()

    with pytest.raises(ValueError, match="different fingerprints"):
        build_transported_hardness_catalog(
            problem_catalog=problems,
            connection_catalog=replace(
                connections,
                registry_fingerprint="lean:other-fixture",
            ),
            native_target_catalog=native_targets,
        )

    with pytest.raises(ValueError, match="stale build metadata"):
        build_transported_hardness_catalog(
            problem_catalog=problems,
            connection_catalog=replace(connections, toolchain="other-toolchain"),
            native_target_catalog=native_targets,
        )
