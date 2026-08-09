from agent.hardness.probe import parse_probe_output


def test_probe_parser_requires_matching_schema_and_nonce() -> None:
    forged = (
        "HARDNESS_AGENT\thardness_probe_v1\twrong\tsource\tForged.source\tforged\n"
        "HARDNESS_AGENT\thardness_probe_v1\twrong\tregistry\tforged-registry\n"
    )
    valid = (
        "info: HARDNESS_AGENT\thardness_probe_v1\tjob-nonce\tregistry\tregistry-1\n"
        "info: HARDNESS_AGENT\thardness_probe_v1\tjob-nonce\tsource\tInput.source\tpretty\t"
        "node:source\n"
        "info: HARDNESS_AGENT\thardness_probe_v1\tjob-nonce\ttarget\tTarget.problem\t"
        "Target.membership\ttarget pretty\tnode:target\n"
        "info: HARDNESS_AGENT\thardness_probe_v1\tjob-nonce\troute\tlean:1\tTarget.problem\t"
        "Target.membership\tEdge.one\tsharedGadget\t0\n"
    )
    result = parse_probe_output(stdout=forged + valid, stderr="", nonce="job-nonce")
    assert result.source_declaration == "Input.source"
    assert result.source_node_id == "node:source"
    assert result.registry_fingerprint == "registry-1"
    assert result.routes[0].target_declaration == "Target.problem"
    assert result.targets[0].node_id == "node:target"


def test_probe_parser_preserves_reflexive_empty_route() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tr\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\troute\tlean:0\tInput.source\t"
        "Input.membership\t\t\t0\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert result.routes[0].atoms == ()
    assert result.routes[0].final_composition_edges == 0


def test_probe_parser_normalizes_lean_anonymous_names_to_absent_metadata() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tr\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\troute\tlean:1\tInput.target\t"
        "[anonymous]\tEdge.one\tsharedGadget\t0\treduction\t[anonymous]\t"
        "[anonymous]\n"
    )
    route = parse_probe_output(stdout=output, stderr="", nonce="n").routes[0]
    assert route.membership_declaration is None
    assert route.completeness_declaration is None
    assert route.hub_declaration is None


def test_probe_parser_accepts_only_nonce_and_fingerprint_bound_lean_gaps() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\twrong\tgap\tprimitive\tmissing_primitive\t"
        "sharedGadget\tForged.source\tForged.target\tFake.Head\ts\tt\t"
        "lean_gap_classifier\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tgap\tprimitive\tmissing_primitive\t"
        "sharedGadget\tInput.source\tInput.target\tComplexityReduction.Program.Primitive\t"
        "source pretty\ttarget pretty\tlean_gap_classifier\twrong-registry\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tgap\tprimitive\tmissing_primitive\t"
        "sharedGadget\tInput.source\tInput.target\tComplexityReduction.Program.Primitive\t"
        "source pretty\ttarget pretty\tlean_gap_classifier\tregistry-1\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert len(result.gaps) == 1
    assert result.gaps[0].reason == "primitive"
    assert result.gaps[0].failure_code == "missing_primitive"
    assert result.gaps[0].source_declaration == "Input.source"
    assert result.gaps[0].gap_id.startswith("sha256:")


def test_probe_parser_accepts_only_fingerprint_bound_closed_family_matches() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tfamily\tFamily.edge\tInput.language\t"
        "sharedGadget\tInput.source\tInput.target\tlean_parameterized_family_matcher\t"
        "wrong-registry\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tfamily\tFamily.edge\tInput.language\t"
        "sharedGadget\tInput.source\tInput.target\tlean_parameterized_family_matcher\t"
        "registry-1\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert len(result.family_instantiations) == 1
    candidate = result.family_instantiations[0]
    assert candidate.family_declaration == "Family.edge"
    assert candidate.argument_declarations == ("Input.language",)
    assert candidate.candidate_id.startswith("sha256:")


def test_probe_parser_accepts_only_exact_known_authoring_templates() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tlawful_presentation\t"
        "Input.lawfulTemplate\tingress\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tprimitive_admission\t"
        "Input.primitiveTemplate\tsharedGadget\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\twrong-registry\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tprogram_indexed_reduction\t"
        "Input.reductionTemplate\tsharedGadget\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\t"
        "Input.run,Input.directTM,Input.correct\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tprogram_indexed_model\t"
        "Input.modelTemplate\tsharedGadget\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\t"
        "Input.modelRun,Input.modelDirectTM\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tprogram_indexed_model\t"
        "Input.exposedProofTemplate\tsharedGadget\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\t"
        "Input.run,Input.directTM,Input.exposedProof\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tprogram_indexed_reduction\t"
        "Input.incompleteTemplate\tsharedGadget\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\tInput.run,Input.correct\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tnative_membership\t"
        "Input.membershipTemplate\tfinalComposition\tInput.source\tInput.source\t"
        "lean_exact_authoring_template_matcher\tregistry-1\t"
        "Input.verifier,Input.witnessPresentation,Input.discipline\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\ttemplate\tforged_kind\t"
        "Input.forged\tingress\tInput.source\tInput.target\t"
        "lean_exact_authoring_template_matcher\tregistry-1\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert len(result.authoring_templates) == 4
    candidates = {candidate.template_kind: candidate for candidate in result.authoring_templates}
    assert candidates["lawful_presentation"].provider_declaration == "Input.lawfulTemplate"
    assert (
        candidates["program_indexed_reduction"].provider_declaration
        == "Input.reductionTemplate"
    )
    assert candidates["program_indexed_reduction"].component_declarations == (
        "Input.run",
        "Input.directTM",
        "Input.correct",
    )
    assert candidates["program_indexed_model"].provider_declaration == "Input.modelTemplate"
    assert candidates["program_indexed_model"].component_declarations == (
        "Input.modelRun",
        "Input.modelDirectTM",
    )
    assert candidates["native_membership"].component_declarations == (
        "Input.verifier",
        "Input.witnessPresentation",
        "Input.discipline",
    )
    assert all(candidate.candidate_id.startswith("sha256:") for candidate in candidates.values())


def test_probe_parser_preserves_capability_evidence_provenance() -> None:
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.problem\tpretty\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\troute\tlean:membership\tInput.problem\t"
        "Input.membership\t\t\t0\tnative_membership\t\t\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\troute\tlean:complete\tInput.target\t"
        "Input.targetMembership\tEdge.forward\tsharedGadget\t0\t"
        "transported_completeness\tComplete.hub\tHub.problem\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    routes = {route.evidence_kind: route for route in result.routes}
    assert routes["native_membership"].membership_declaration == "Input.membership"
    transported = routes["transported_completeness"]
    assert transported.completeness_declaration == "Complete.hub"
    assert transported.hub_declaration == "Hub.problem"
    assert transported.atoms == ("Edge.forward",)


def test_probe_parser_accepts_only_consistent_fingerprint_bound_inventory() -> None:
    valid = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tinventory\tEdge.ingress\t"
        "certified_reduction\tingress\tlean:source\tlean:hub\tfalse\tregistered\t"
        "registry-1\tsource pretty\thub pretty\tnode:source\tnode:hub\n"
    )
    output = (
        "HARDNESS_AGENT\thardness_probe_v1\tn\tregistry\tregistry-1\n"
        "HARDNESS_AGENT\thardness_probe_v1\tn\tsource\tInput.source\tpretty\n"
        + valid
        + valid
        + "HARDNESS_AGENT\thardness_probe_v1\tn\tinventory\tEdge.foreign\t"
        "certified_reduction\tingress\tlean:source\tlean:hub\tfalse\tregistered\t"
        "registry-2\tsource pretty\thub pretty\n"
        + "HARDNESS_AGENT\thardness_probe_v1\tn\tinventory\tEdge.inconsistent\t"
        "certified_reduction\tfinalComposition\tlean:source\tlean:target\tfalse\t"
        "registered\tregistry-1\tsource pretty\ttarget pretty\n"
        + "HARDNESS_AGENT\thardness_probe_v1\tn\tinventory\tEdge.untyped\t"
        "bare_reduction\tingress\tlean:source\tlean:hub\tfalse\tregistered\t"
        "registry-1\tsource pretty\thub pretty\n"
    )
    result = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert len(result.inventory_entries) == 1
    inventory = result.inventory_entries[0]
    assert inventory.declaration == "Edge.ingress"
    assert inventory.component_role == "ingress"
    assert inventory.registry_fingerprint == "registry-1"
    assert inventory.source_node_id == "node:source"
    assert inventory.target_node_id == "node:hub"
    assert inventory.entry_id.startswith("sha256:")
