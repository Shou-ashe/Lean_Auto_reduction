from __future__ import annotations

import copy
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.np_hard_publication import (
    FINAL_COMPOSITION_ATTRIBUTE,
    NPHardPublicationError,
    PUBLICATION_CANDIDATE_MANIFEST_SCHEMA,
    PUBLICATION_STATE,
    SUPPORTED_PUBLICATION_CASES,
    TYPED_EDGE_ATTRIBUTE,
    reseal_candidate_manifest,
    validate_candidate_manifest,
)


SOURCE = f"""import Fixture.Dependency
import ComplexityReduction.Annotations.Attributes

namespace ComplexityReduction.Generated.Hardness.Cfixture.Reduction

noncomputable def authoredNode : True := by
  trivial

@[{TYPED_EDGE_ATTRIBUTE}, {FINAL_COMPOSITION_ATTRIBUTE}]
noncomputable def authoredForwardReduction : True := by
  exact authoredNode

end ComplexityReduction.Generated.Hardness.Cfixture.Reduction

assert_standard_axioms
  ComplexityReduction.Generated.Hardness.Cfixture.Reduction.authoredNode,
  ComplexityReduction.Generated.Hardness.Cfixture.Reduction.authoredForwardReduction
"""


def file_hash(path: Path) -> str:
    import hashlib

    return f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}"


def test_roots(tmp_path: Path) -> tuple[Path, Path, Path]:
    repo_root = tmp_path / "repo"
    lean_root = repo_root / "Lean"
    dependency = lean_root / "Reference/Fixture/Dependency.lean"
    dependency.parent.mkdir(parents=True)
    dependency.write_text("def Fixture.Dependency.witness : True := True.intro\n")
    (lean_root / "lean-toolchain").write_text("leanprover/lean4:v4.29.0\n")
    (lean_root / "lake-manifest.json").write_text('{"version":"1.1.0"}\n')
    (lean_root / "lakefile.toml").write_text('name = "fixture"\n')
    pack_root = tmp_path / "pack"
    pack_root.mkdir()
    (pack_root / "Reduction.lean").write_text(SOURCE)
    return repo_root, lean_root, pack_root


def manifest(lean_root: Path, pack_root: Path) -> dict:
    dependency = lean_root / "Reference/Fixture/Dependency.lean"
    project_files = {
        "Lean/Reference/Fixture/Dependency.lean": file_hash(dependency)
    }
    value = {
        "schema_version": PUBLICATION_CANDIDATE_MANIFEST_SCHEMA,
        "state": PUBLICATION_STATE,
        "publication_eligible": False,
        "publication_activation_performed": False,
        "case_id": "cdev-au-01-tagged-three-sat-adapter",
        "label": "Tagged3SAT",
        "canonical_identity_id": f"sha256:{'1' * 64}",
        "canonical_endpoint": "Fixture.target",
        "source_hub": "Fixture.source",
        "direction": "source_to_target",
        "h_j_evidence": {
            "mode": "explicit_shadow_probe",
            "formal_h_j_complete": False,
            "h_j_report_id": None,
        },
        "route": {
            "task_class": "typed_capability_dag",
            "source": "Fixture.source",
            "target": "Fixture.target",
            "direction": "source_to_target",
            "selected_hub": "Fixture.source",
            "terminal_node_id": "node",
            "final_program_node_id": "node",
            "model_nodes": [
                {
                    "node_id": "node",
                    "published_declaration": (
                        "ComplexityReduction.Generated.Hardness.Cfixture."
                        "Reduction.authoredNode"
                    ),
                }
            ],
            "runner_owned_reduction": {
                "published_declaration": (
                    "ComplexityReduction.Generated.Hardness.Cfixture."
                    "Reduction.authoredForwardReduction"
                ),
                "exact_type": "True",
                "attributes": [
                    TYPED_EDGE_ATTRIBUTE,
                    FINAL_COMPOSITION_ATTRIBUTE,
                ],
            },
        },
        "model_evidence": {"call_count": 1},
        "fresh_core_evidence": {"node_count": 1},
        "deletion_evidence": {"node_count": 1},
        "axiom_evidence": {"passed": True},
        "endpoint_evidence": {
            "source": "Fixture.source",
            "target": "Fixture.target",
        },
        "candidate": {
            "module": (
                "ComplexityReduction.Generated.Hardness.Cfixture.Reduction"
            ),
            "namespace": (
                "ComplexityReduction.Generated.Hardness.Cfixture.Reduction"
            ),
            "declaration": (
                "ComplexityReduction.Generated.Hardness.Cfixture.Reduction."
                "authoredForwardReduction"
            ),
            "source_file": "Reduction.lean",
            "source_sha256": file_hash(pack_root / "Reduction.lean"),
            "imports": [
                "Fixture.Dependency",
                "ComplexityReduction.Annotations.Attributes",
            ],
            "attributes": [TYPED_EDGE_ATTRIBUTE, FINAL_COMPOSITION_ATTRIBUTE],
            "native_hardness_tail_present": False,
        },
        "dependencies": {
            "toolchain": {
                "lean_toolchain": "leanprover/lean4:v4.29.0",
                "lean_toolchain_sha256": file_hash(lean_root / "lean-toolchain"),
                "lake_manifest_sha256": file_hash(
                    lean_root / "lake-manifest.json"
                ),
                "lakefile_sha256": file_hash(lean_root / "lakefile.toml"),
            },
            "task_public_source_files": project_files,
            "task_dependency_snapshot_sha256": sha256_id(project_files),
            "closure": {
                "project_source_files": project_files,
                "project_source_file_count": 1,
                "external_import_roots": [
                    "ComplexityReduction.Annotations.Attributes"
                ],
                "graph_sha256": sha256_id({"Fixture.Dependency": []}),
                "closure_sha256": sha256_id(project_files),
                "candidate_cycle_absent": True,
                "runtime_or_hardness_aggregate_import_absent": True,
            },
        },
        "shadow_audits": {
            "clean_shadow_build": {"passed": True},
            "axiom_endpoint_attribute": {"passed": True},
            "import_cycle": {"passed": True},
        },
    }
    return reseal_candidate_manifest(value)


def assert_code(error: pytest.ExceptionInfo[NPHardPublicationError], code: str) -> None:
    assert error.value.code == code


def test_first_publication_interface_is_exactly_four_public_targets() -> None:
    assert set(SUPPORTED_PUBLICATION_CASES) == {
        "cdev-au-01-tagged-three-sat-adapter",
        "chld-au-07-set-covering",
        "chld-au-09-feedback-arc-set",
        "chld-au-10-three-dimensional-matching",
    }
    assert {row["label"] for row in SUPPORTED_PUBLICATION_CASES.values()} == {
        "Tagged3SAT",
        "SetCovering",
        "FeedbackArcSet",
        "ThreeDimensionalMatching",
    }


def test_candidate_manifest_accepts_content_addressed_shadow_only_pack(
    tmp_path: Path,
) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = manifest(lean_root, pack_root)
    validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert value["publication_eligible"] is False
    assert value["publication_activation_performed"] is False


def test_deleted_candidate_fails_closed(tmp_path: Path) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = manifest(lean_root, pack_root)
    (pack_root / "Reduction.lean").unlink()
    with pytest.raises(NPHardPublicationError) as error:
        validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert_code(error, "publication_candidate_missing")


def test_tampered_candidate_fails_closed(tmp_path: Path) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = manifest(lean_root, pack_root)
    (pack_root / "Reduction.lean").write_text(SOURCE.replace("trivial", "simp", 1))
    with pytest.raises(NPHardPublicationError) as error:
        validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert_code(error, "publication_candidate_hash_mismatch")


@pytest.mark.parametrize(
    ("mutated_source", "expected_code"),
    [
        (
            SOURCE.replace(
                "namespace ComplexityReduction",
                "/tmp/old-job/Final.lean\nnamespace ComplexityReduction",
                1,
            ),
            "publication_candidate_path_forbidden",
        ),
        (
            SOURCE.replace(
                "import Fixture.Dependency",
                "import ComplexityReduction.Agent.Hardness.Runtime",
                1,
            ),
            "publication_candidate_import_forbidden",
        ),
        (
            SOURCE.replace(
                f"@[{TYPED_EDGE_ATTRIBUTE}, {FINAL_COMPOSITION_ATTRIBUTE}]\n",
                "",
                1,
            ),
            "publication_candidate_attribute_missing",
        ),
    ],
)
def test_security_mutations_fail_even_after_resealing(
    tmp_path: Path, mutated_source: str, expected_code: str
) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = manifest(lean_root, pack_root)
    source_path = pack_root / "Reduction.lean"
    source_path.write_text(mutated_source)
    value["candidate"]["source_sha256"] = file_hash(source_path)
    import re

    value["candidate"]["imports"] = re.findall(
        r"(?m)^import\s+([A-Za-z0-9_.']+)\s*$", mutated_source
    )
    value = reseal_candidate_manifest(value)
    with pytest.raises(NPHardPublicationError) as error:
        validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert_code(error, expected_code)


def test_dependency_hash_drift_fails_closed(tmp_path: Path) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = manifest(lean_root, pack_root)
    (lean_root / "Reference/Fixture/Dependency.lean").write_text(
        "def Fixture.Dependency.witness : False := by contradiction\n"
    )
    with pytest.raises(NPHardPublicationError) as error:
        validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert_code(error, "publication_dependency_stale")


def test_manifest_tamper_breaks_content_identity(tmp_path: Path) -> None:
    _, lean_root, pack_root = test_roots(tmp_path)
    value = copy.deepcopy(manifest(lean_root, pack_root))
    value["canonical_endpoint"] = "Fixture.otherTarget"
    with pytest.raises(NPHardPublicationError) as error:
        validate_candidate_manifest(value, pack_root=pack_root, lean_root=lean_root)
    assert_code(error, "publication_candidate_content_id_mismatch")
