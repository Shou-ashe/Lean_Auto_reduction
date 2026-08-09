import json

import pytest

from agent.hardness.hardness_target_catalog import (
    HARDNESS_TARGET_CATALOG_SCHEMA,
    MAX_TARGET_RESULTS_PER_ROUND,
    MAX_TARGET_RESULTS_PER_SEARCH,
    NATIVE_NP_COMPLETE_POLICY,
    NATIVE_NP_HARD_POLICY,
    NATIVE_NP_POLICY,
    HardnessTargetCatalogError,
    HardnessTargetSearchError,
    build_hardness_target_summary,
    build_initial_hardness_target_hints,
    hardness_target_catalog_from_dict,
    hardness_target_search_result,
    load_hardness_target_catalog_snapshot,
    parse_hardness_target_catalog,
    parse_hardness_target_searches,
    search_hardness_targets,
)


FINGERPRINT = "lean:registry"
TOOLCHAIN = "leanprover/lean4:v4.19.0"
MANIFEST_SHA256 = "a" * 64
TARGET = "ComplexityReduction.Presentation.ThreeSAT.problem"
TARGET_NAMESPACE = "ComplexityReduction.Presentation.ThreeSAT"
TARGET_NODE = "lean-whnf:three-sat"
MEMBERSHIP = "ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier.inNP"
COMPLETENESS = (
    "ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier.npComplete"
)
MEMBERSHIP_PROJECTION = (
    "ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership"
)


def registry_row(
    *,
    nonce: str = "nonce",
    schema: str = HARDNESS_TARGET_CATALOG_SCHEMA,
    fingerprint: str = FINGERPRINT,
) -> str:
    return "\t".join(
        ["HARDNESS_AGENT", schema, nonce, "registry", fingerprint]
    )


def target_row(
    declaration: str = TARGET,
    *,
    nonce: str = "nonce",
    schema: str = HARDNESS_TARGET_CATALOG_SCHEMA,
    display: str = "ThreeSAT presented target",
    node: str = TARGET_NODE,
    namespace: str | None = None,
    fingerprint: str = FINGERPRINT,
) -> str:
    namespace = namespace or declaration.rpartition(".")[0]
    return "\t".join(
        [
            "HARDNESS_AGENT",
            schema,
            nonce,
            "target",
            declaration,
            display,
            node,
            namespace,
            fingerprint,
        ]
    )


def evidence_row(
    *,
    target: str = TARGET,
    node: str = TARGET_NODE,
    kind: str = "native_membership",
    declaration: str | None = None,
    lean_term: str | None = None,
    membership_term: str | None = None,
    policies: str | None = None,
    validation_source: str = "lean_registry_elaborated_type",
    provenance: str | None = None,
    fingerprint: str = FINGERPRINT,
    nonce: str = "nonce",
    schema: str = HARDNESS_TARGET_CATALOG_SCHEMA,
) -> str:
    completeness = kind in {
        "native_completeness",
        "registered_native_completeness",
    }
    declaration = declaration or (COMPLETENESS if completeness else MEMBERSHIP)
    lean_term = declaration if lean_term is None else lean_term
    if membership_term is None:
        membership_term = (
            f"{MEMBERSHIP_PROJECTION} {declaration}"
            if completeness
            else declaration
        )
    if policies is None:
        policies = (
            "native_np,native_np_hard,native_np_complete"
            if completeness
            else "native_np"
        )
    if provenance is None:
        provenance = (
            f"{declaration},{MEMBERSHIP_PROJECTION}"
            if completeness
            else declaration
        )
    return "\t".join(
        [
            "HARDNESS_AGENT",
            schema,
            nonce,
            "evidence",
            target,
            node,
            kind,
            declaration,
            lean_term,
            membership_term,
            policies,
            validation_source,
            provenance,
            fingerprint,
        ]
    )


def catalog_output() -> str:
    return "\n".join(
        [
            registry_row(),
            target_row(),
            evidence_row(),
            evidence_row(kind="native_completeness"),
        ]
    )


def parse_catalog(output: str | None = None):
    return parse_hardness_target_catalog(
        stdout=output or catalog_output(),
        stderr="",
        nonce="nonce",
        toolchain=TOOLCHAIN,
        lake_manifest_sha256=MANIFEST_SHA256,
    )


def test_parses_membership_and_completeness_grouped_by_target() -> None:
    stdout = "\n".join([registry_row(), target_row(), evidence_row()])
    catalog = parse_hardness_target_catalog(
        stdout=stdout,
        stderr=evidence_row(kind="native_completeness"),
        nonce="nonce",
    )

    assert catalog.registry_fingerprint == FINGERPRINT
    assert len(catalog.entries) == 1
    assert catalog.evidence_count == 2
    entry = catalog.entries[0]
    assert entry.target_declaration == TARGET
    assert entry.target_node_id == TARGET_NODE
    assert entry.target_namespace == TARGET_NAMESPACE
    assert entry.satisfied_policies == (
        NATIVE_NP_POLICY,
        NATIVE_NP_HARD_POLICY,
        NATIVE_NP_COMPLETE_POLICY,
    )
    assert [evidence.evidence_kind for evidence in entry.evidences] == [
        "native_completeness",
        "native_membership",
    ]
    completeness = entry.evidences[0]
    assert completeness.membership_lean_term == (
        f"{MEMBERSHIP_PROJECTION} {COMPLETENESS}"
    )
    assert completeness.provenance_declarations == (
        COMPLETENESS,
        MEMBERSHIP_PROJECTION,
    )


def test_ids_are_stable_and_json_round_trip_is_exact() -> None:
    first = parse_catalog()
    second = parse_catalog()
    assert first.catalog_id == second.catalog_id
    assert first.entries[0].target_entry_id == second.entries[0].target_entry_id
    assert [e.evidence_id for e in first.entries[0].evidences] == [
        e.evidence_id for e in second.entries[0].evidences
    ]
    assert first.catalog_id.startswith("sha256:")
    assert hardness_target_catalog_from_dict(first.to_dict()) == first
    assert json.loads(json.dumps(first.to_dict())) == first.to_dict()


def test_snapshot_rejects_tampering_and_stale_fingerprints(tmp_path) -> None:
    catalog = parse_catalog()
    snapshot = tmp_path / "hardness-targets.json"
    snapshot.write_text(json.dumps(catalog.to_dict()), encoding="utf-8")

    loaded = load_hardness_target_catalog_snapshot(
        snapshot,
        expected_registry_fingerprint=FINGERPRINT,
        expected_toolchain=TOOLCHAIN,
        expected_lake_manifest_sha256=MANIFEST_SHA256,
    )
    assert loaded.catalog_id == catalog.catalog_id

    for keyword, value in (
        ("expected_registry_fingerprint", "lean:other"),
        ("expected_toolchain", "other-toolchain"),
        ("expected_lake_manifest_sha256", "b" * 64),
    ):
        with pytest.raises(
            HardnessTargetCatalogError, match="stale hardness target catalog"
        ):
            load_hardness_target_catalog_snapshot(snapshot, **{keyword: value})

    tampered = catalog.to_dict()
    tampered["entries"][0]["target_display"] = "tampered target"
    snapshot.write_text(json.dumps(tampered), encoding="utf-8")
    with pytest.raises(HardnessTargetCatalogError, match="content ID"):
        load_hardness_target_catalog_snapshot(snapshot)


def test_wrong_nonce_and_schema_rows_are_ignored() -> None:
    noisy = "\n".join(
        [
            registry_row(nonce="other"),
            target_row(nonce="other"),
            evidence_row(nonce="other"),
            registry_row(schema="hardness_target_catalog_v0"),
            target_row(schema="hardness_target_catalog_v0"),
            evidence_row(schema="hardness_target_catalog_v0"),
            catalog_output(),
        ]
    )
    assert parse_catalog(noisy).evidence_count == 2


def test_missing_nonce_bound_registry_fails_closed() -> None:
    output = "\n".join(
        [
            registry_row(nonce="other"),
            target_row(nonce="other"),
            evidence_row(nonce="other"),
            registry_row(schema="hardness_target_catalog_v0"),
        ]
    )
    with pytest.raises(HardnessTargetCatalogError, match="exactly one registry row"):
        parse_catalog(output)


@pytest.mark.parametrize(
    ("rows", "message"),
    [
        (
            [target_row(), target_row(node="lean-whnf:other")],
            "duplicate target row for declaration",
        ),
        (
            [
                target_row(),
                target_row(
                    "ComplexityReduction.Presentation.Clique.problem",
                    node=TARGET_NODE,
                ),
            ],
            "duplicate target row for node",
        ),
    ],
)
def test_duplicate_target_declaration_or_node_is_rejected(
    rows: list[str], message: str
) -> None:
    with pytest.raises(HardnessTargetCatalogError, match=message):
        parse_catalog("\n".join([registry_row(), *rows]))


@pytest.mark.parametrize(
    ("row", "message"),
    [
        (
            evidence_row(
                target="ComplexityReduction.Presentation.Unknown.problem"
            ),
            "target row that was not exported",
        ),
        (
            evidence_row(node="lean-whnf:wrong"),
            "target evidence node does not match",
        ),
        (
            evidence_row(fingerprint="lean:other"),
            "target evidence fingerprint does not match",
        ),
    ],
)
def test_evidence_must_reference_the_exported_target_node_and_fingerprint(
    row: str, message: str
) -> None:
    with pytest.raises(HardnessTargetCatalogError, match=message):
        parse_catalog("\n".join([registry_row(), target_row(), row]))


def test_duplicate_evidence_declaration_is_rejected() -> None:
    output = "\n".join(
        [registry_row(), target_row(), evidence_row(), evidence_row()]
    )
    with pytest.raises(
        HardnessTargetCatalogError, match="duplicate target evidence declaration"
    ):
        parse_catalog(output)


@pytest.mark.parametrize("kind", ["backend_tm_in_np", "unknown_native_evidence"])
def test_backend_or_unknown_evidence_kind_is_rejected(kind: str) -> None:
    output = "\n".join(
        [registry_row(), target_row(), evidence_row(kind=kind)]
    )
    with pytest.raises(
        HardnessTargetCatalogError, match="unsupported or backend target evidence kind"
    ):
        parse_catalog(output)


@pytest.mark.parametrize(
    "row",
    [
        target_row("ComplexityReduction.Expected.ThreeSAT.problem"),
        evidence_row(
            declaration="ComplexityReduction.Oracle.ThreeSAT.inNP",
            lean_term="ComplexityReduction.Oracle.ThreeSAT.inNP",
            membership_term="ComplexityReduction.Oracle.ThreeSAT.inNP",
            provenance="ComplexityReduction.Oracle.ThreeSAT.inNP",
        ),
        evidence_row(
            lean_term=(
                f"{MEMBERSHIP} ComplexityReduction.Legacy.ThreeSAT.support"
            ),
            provenance=(
                f"{MEMBERSHIP},ComplexityReduction.Legacy.ThreeSAT.support"
            ),
        ),
    ],
)
def test_oracle_expected_and_legacy_names_are_rejected(row: str) -> None:
    rows = [registry_row(), row]
    if "\ttarget\t" not in row:
        rows.insert(1, target_row())
    with pytest.raises(
        HardnessTargetCatalogError, match="forbidden public target catalog name"
    ):
        parse_catalog("\n".join(rows))


def test_membership_evidence_cannot_claim_hardness_or_completeness() -> None:
    row = evidence_row(policies="native_np,native_np_hard")
    with pytest.raises(
        HardnessTargetCatalogError, match="membership evidence may satisfy only"
    ):
        parse_catalog("\n".join([registry_row(), target_row(), row]))


@pytest.mark.parametrize(
    ("policies", "membership_term", "provenance", "message"),
    [
        (
            "native_np,native_np_hard",
            f"{MEMBERSHIP_PROJECTION} {COMPLETENESS}",
            f"{COMPLETENESS},{MEMBERSHIP_PROJECTION}",
            "must satisfy all three native policies",
        ),
        (
            "native_np,native_np_hard,native_np_complete",
            "",
            f"{COMPLETENESS},{MEMBERSHIP_PROJECTION}",
            "membership projection is missing or malformed",
        ),
        (
            "native_np,native_np_hard,native_np_complete",
            COMPLETENESS,
            COMPLETENESS,
            "native completeness membership projection",
        ),
    ],
)
def test_completeness_requires_all_policies_and_membership_projection(
    policies: str,
    membership_term: str,
    provenance: str,
    message: str,
) -> None:
    row = evidence_row(
        kind="native_completeness",
        policies=policies,
        membership_term=membership_term,
        provenance=provenance,
    )
    with pytest.raises(HardnessTargetCatalogError, match=message):
        parse_catalog("\n".join([registry_row(), target_row(), row]))


def multi_target_output(*, count_per_group: int = 2) -> str:
    rows = [registry_row()]
    for group in ("Alpha", "Beta"):
        for index in range(count_per_group):
            name = f"{group}Target{index}"
            target = f"ComplexityReduction.Targets.{group}.{name}.problem"
            node = f"lean-whnf:{group.lower()}-{index}"
            evidence = f"ComplexityReduction.Evidence.{group}.{name}.inNP"
            rows.extend(
                [
                    target_row(
                        target,
                        display=f"{group} {name} presented target",
                        node=node,
                    ),
                    evidence_row(
                        target=target,
                        node=node,
                        declaration=evidence,
                        lean_term=evidence,
                        membership_term=evidence,
                        provenance=evidence,
                    ),
                ]
            )
    return "\n".join(rows)


def test_policy_text_and_namespace_searches_are_bounded_and_deterministic() -> None:
    target_b = "ComplexityReduction.Targets.Clique.Clique.problem"
    node_b = "lean-whnf:clique"
    evidence_b = "ComplexityReduction.Evidence.Clique.inNP"
    output = "\n".join(
        [
            *catalog_output().splitlines(),
            target_row(
                target_b,
                display="Clique graph target",
                node=node_b,
            ),
            evidence_row(
                target=target_b,
                node=node_b,
                declaration=evidence_b,
                lean_term=evidence_b,
                membership_term=evidence_b,
                provenance=evidence_b,
            ),
        ]
    )
    catalog = parse_catalog(output)

    hard = search_hardness_targets(
        catalog,
        parse_hardness_target_searches(
            {"searches": [{"required_policies": [NATIVE_NP_HARD_POLICY]}]}
        ),
    )
    assert [entry.target_declaration for entry in hard] == [TARGET]

    clique = search_hardness_targets(
        catalog,
        parse_hardness_target_searches(
            {
                "searches": [
                    {
                        "required_policies": [NATIVE_NP_POLICY],
                        "terms": ["Clique graph"],
                        "namespace_prefixes": [
                            "ComplexityReduction.Targets.Clique"
                        ],
                        "limit": 1,
                    }
                ]
            }
        ),
    )
    assert [entry.target_declaration for entry in clique] == [target_b]

    summary = hardness_target_search_result(
        hard[0],
        required_policies=[NATIVE_NP_POLICY, NATIVE_NP_HARD_POLICY],
    )
    assert [item["evidence_kind"] for item in summary["evidences"]] == [
        "native_completeness"
    ]


def test_search_limit_and_round_cap_are_enforced() -> None:
    catalog = parse_catalog(multi_target_output(count_per_group=8))
    searches = parse_hardness_target_searches(
        {
            "searches": [
                {
                    "namespace_prefixes": ["ComplexityReduction.Targets.Alpha"],
                    "limit": 999,
                },
                {
                    "namespace_prefixes": ["ComplexityReduction.Targets.Beta"],
                    "limit": 999,
                },
            ]
        }
    )
    assert searches[0].limit == MAX_TARGET_RESULTS_PER_SEARCH
    assert searches[1].limit == MAX_TARGET_RESULTS_PER_SEARCH
    results = search_hardness_targets(catalog, searches)
    assert len(results) == MAX_TARGET_RESULTS_PER_ROUND
    assert len({entry.target_entry_id for entry in results}) == len(results)


@pytest.mark.parametrize("field", ["family", "case_id", "gold_target"])
def test_unknown_family_case_and_gold_query_fields_are_rejected(field: str) -> None:
    with pytest.raises(HardnessTargetSearchError, match="unsupported fields"):
        parse_hardness_target_searches(
            {"searches": [{"required_policies": [NATIVE_NP_POLICY], field: "x"}]}
        )


def test_prompt_safe_summary_does_not_reveal_target_or_evidence_declarations() -> None:
    catalog = parse_catalog()
    summary = build_hardness_target_summary(catalog)
    hints = build_initial_hardness_target_hints(catalog)
    assert hints == summary
    assert not summary["contains_declaration_names"]
    assert not summary["full_target_catalog_included"]
    assert summary["target_count"] == 1
    assert summary["evidence_count"] == 2

    serialized = json.dumps(summary, sort_keys=True)
    assert TARGET not in serialized
    assert MEMBERSHIP not in serialized
    assert COMPLETENESS not in serialized
