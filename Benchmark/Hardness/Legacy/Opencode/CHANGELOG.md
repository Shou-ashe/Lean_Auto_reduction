# Benchmark Changelog

## opencode_decision_problem_v0.19.0

- Expanded L14 with alternate graph-tail forked route samples:
  `tagged_xor3_clique_cover_knapsack_dual_tail_forked_route` and
  `right_nested_dual_horn3_clique_cover_knapsack_dual_tail_forked_route`.
  These keep the L14 contract but route the graph branch through
  Chromatic Number and Clique Cover instead of only Clique and Vertex Cover.
- Added L15 public Lean proposition samples for stacked-bridge forked mixed
  gadget-route synthesis:
  `double_tagged_xor3_clique_cover_knapsack_stacked_forked_route` and
  `left_sandwiched_dual_horn3_vertex_knapsack_stacked_forked_route`.
- Each L15 sample requires two public normalization `ProblemEquivM` bridges,
  one source-CSP-to-3SAT gadget edge, two graph-tail Karp21 route witnesses,
  two numeric-tail Karp21 route witnesses, both composed reducibility proofs,
  target memberships, and final source membership.
- L15 combines the L13 stacked-bridge axis with the L14 forked-route axis
  without adding a runner ABI or sample-specific prompt rule.
- Added matching L14/L15 gold proofs. Active levels are now L0-L15 and the
  manifest contains 102 usable samples.

## opencode_decision_problem_v0.18.0

- Added L14 public Lean proposition samples for forked mixed
  gadget-route synthesis:
  `tagged_one_in_three_dual_tail_forked_route`,
  `left_nested_nae3_dual_tail_forked_route`,
  `right_nested_horn3_dual_tail_forked_route`, and
  `sandwiched_three_sat_like_dual_tail_forked_route`.
- Each L14 sample requires a public normalization `ProblemEquivM` bridge, one
  source-CSP-to-3SAT gadget edge, two graph-tail Karp21 route witnesses, two
  numeric-tail Karp21 route witnesses, both composed reducibility proofs,
  target memberships, and final source membership.
- L14 expands benchmark coverage laterally across proof products: candidates
  must assemble two independent route tails from a shared 3SAT pivot in the
  same certificate, without a new runner ABI or sample-specific prompt rule.
- Added matching L14 gold proofs under `Benchmark/GoldProofs/L14/`.
- Active levels are now L0-L14 and the manifest contains 98 usable samples.

## opencode_decision_problem_v0.17.0

- Added L13 public Lean proposition samples for stacked-bridge mixed
  gadget-route synthesis:
  `double_tagged_one_in_three_to_vertex_cover_stacked_bridge`,
  `left_sandwiched_nae3_to_knapsack_stacked_bridge`,
  `right_nested_horn3_to_vertex_cover_stacked_bridge`, and
  `paired_flags_three_sat_like_to_knapsack_stacked_bridge`.
- Each L13 sample requires two explicit public normalization
  `ProblemEquivM` bridges, one source-CSP-to-3SAT gadget edge, two ordinary
  Karp21 route edges, composed reducibility, target membership, and final
  source membership.
- L13 extends L12 by testing stacked bridge composition before the mixed
  CSP-gadget-to-Karp21 route tail, without adding a new runner ABI or
  sample-specific prompt rule.
- Added matching L13 gold proofs under `Benchmark/GoldProofs/L13/`.
- Active levels are now L0-L13 and the manifest contains 94 usable samples.

## opencode_decision_problem_v0.16.0

- Added L12 public Lean proposition samples for mixed CSP-gadget plus Karp21
  route synthesis:
  `tagged_one_in_three_to_vertex_cover_mixed_route`,
  `left_nested_nae3_to_vertex_cover_mixed_route`,
  `right_nested_horn3_to_knapsack_mixed_route`, and
  `sandwiched_three_sat_like_to_knapsack_mixed_route`.
- Each L12 sample requires a public normalization bridge, one fixed
  source-CSP-to-3SAT gadget edge, a fixed final graph or numeric target, one
  intermediate public Karp route target chosen from descriptors, composed
  reducibility, target membership, and final source membership.
- L12 is intended to cover the gap between L11 gadget composition and L10
  ordinary three-hop route synthesis: candidates must splice an existing CSP
  gadget route into a non-CSP Karp21 graph or numeric route tail.
- Added matching L12 gold proofs under `Benchmark/GoldProofs/L12/`.
- Active levels are now L0-L12 and the manifest contains 90 usable samples.

## opencode_decision_problem_v0.15.1

- Expanded L11 from 4 to 8 public Lean proposition samples to cover the full
  4x2 source-CSP/target-CSP composed gadget matrix currently exposed by the
  public local library:
  `sandwiched_one_in_three_roundtrip_composed_gadget`,
  `left_nested_nae3_roundtrip_composed_gadget`,
  `right_nested_three_sat_like_to_nae3_composed_gadget`, and
  `right_left_horn3_to_one_in_three_composed_gadget`.
- The new samples keep the same L11 contract: normalize a wrapped CSP source,
  expose the source-to-3SAT gadget, expose the 3SAT-to-target-CSP gadget, build
  composed reducibility, and transport target NP membership back to the source.
- Added matching L11 gold proofs; all eight L11 gold proofs compile with
  `lake env lean`.
- Active levels remain L0-L11 and the manifest now contains 86 usable samples.

## opencode_decision_problem_v0.15.0

- Added L11 public Lean proposition samples for composed CSP gadget synthesis:
  `tagged_one_in_three_to_nae3_composed_gadget`,
  `right_tagged_nae3_to_one_in_three_composed_gadget`,
  `sandwiched_three_sat_like_to_one_in_three_composed_gadget`, and
  `nested_horn3_to_nae3_composed_gadget`.
- Each L11 sample fixes a CSP source wrapper and a CSP target, then requires a
  public normalization bridge, a source-CSP-to-3SAT Karp reduction, a
  3SAT-to-target-CSP gadget Karp reduction, composed reducibility, target
  membership, and final source membership.
- L11 is intentionally not an open graph-route benchmark: the target type
  fixes the 3SAT pivot and CSP target so candidates must compose existing CSP
  gadget reductions into a new gadget route.
- Added matching L11 gold proofs under `Benchmark/GoldProofs/L11/`; all four
  compile with `lake env lean`.
- Generalized level filtering and obligation classification through `L11`.
  L11 counts as both a multi-hop route and encoding-bridge obligation.
- Active levels are now L0-L11 and the manifest contains 82 usable samples.

## opencode_decision_problem_v0.14.2

- Generalized the non-invasive public route-source audit from an L10-only gate
  to a target-contract-driven gate. Public Lean proposition samples now infer
  the required number of public Karp route theorem mentions from the number of
  public route `KarpReductionM` witnesses in `lean_target_type`; local adapter
  reduction witnesses are not counted as public route edges.
- The audit remains descriptor/retrieval/audit based and does not add
  sample-specific prompt rules or hidden route answers.
- Reduced retrieval noise for explicit public-route targets: direct source
  `InNPEnc` membership cards are no longer rendered when the public target
  already asks for route witnesses, so the route descriptor/path candidates stay
  as the primary agent-facing evidence.
- For explicit multi-hop targets, retrieval now suppresses the separate
  single-edge route descriptor block and uses a multi-hop bridge assembly card;
  the prechecked route-path candidates remain visible as the main construction
  surface.
- First-draft and missing-artifact prompts now surface the public route-source
  audit contract when the target asks for public route witnesses. Missing-file
  retry hints also retain the first prechecked multi-hop route candidate.
- Missing-artifact route hints now choose the two-hop or three-hop bridge
  composition helper according to the public target witness count, and preserve
  the route-path Wrap/Compose instructions from retrieval.

## opencode_decision_problem_v0.14.1

- Added a non-invasive L10 route-source audit after Lean validation. L10
  certificates must mention at least three public Karp route theorem symbols in
  `ProofCertificate.lean`; using identity/refl reductions to fill existential
  route steps no longer counts as a completed L10 certificate.
- The audit does not change the public Lean target, expose hidden targets, or
  add prompt rules. It records `route_source_audit` and
  `route_source_audit_verified` in each sample report.
- Added generic agent-facing two-hop and three-hop route-composition helpers
  and descriptors under `LeanAutoReduction.Reduction.Composition`. These are
  public API affordances for composing existing `KarpReductionM` edges; they do
  not encode benchmark routes or sample-specific theorem choices.
- Re-analysis of `.reduction-agent/runs/sat_csp_20260612T180644Z/report.json`
  showed only `tagged_cnf_three_hop_synthesis` and
  `tagged_set_covering_three_hop_synthesis` used three real public route
  theorem mentions; the other passing candidates used identity-route shortcuts.

## opencode_decision_problem_v0.14.0

- Added L10 public Lean proposition samples for three-hop open route synthesis:
  `tagged_cnf_three_hop_synthesis`, `nested_three_sat_three_hop_synthesis`,
  `sandwiched_clique_three_hop_synthesis`, `deep_vertex_cover_three_hop_synthesis`,
  `tagged_set_covering_three_hop_synthesis`, and
  `wrapped_zero_one_ip_three_hop_synthesis`.
- Each L10 sample asks for a public normalization bridge, three open
  `KarpReductionM` edges, composed reducibility, final target membership, and
  source membership. The route targets remain existential and are not prescribed
  by sample metadata.
- Added matching L10 gold proofs under `Benchmark/GoldProofs/L10/`; all six
  compile with `lake env lean`.
- Generalized benchmark level filtering and obligation classification through
  `L10`; L10 counts as both a multi-hop route and an encoding-bridge obligation.
- Active levels are now L0-L10 and the manifest contains 78 usable samples.
- This change does not modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.12.2

- Pruned the remaining active samples whose formal obligations duplicated a
  same-level representative without adding a new capability axis.
- L3 removed the duplicate graph audit-interface shape
  `max_cut_audit_interface`; `clique_audit_interface` still covers the
  `P ∧ True` adapter pattern, while the remaining L3 samples cover disabled
  branches, duplicate checkers, and classical double-negation adapters.
- L4 now keeps six representative fixed two-hop routes across graph, set,
  numeric, SAT-to-numeric, SAT-to-graph, and feedback-route families. Removed
  horizontal two-hop duplicates:
  `vertex_cover_dual_set_route`, `set_cover_exact_matching_route`,
  `zero_one_numeric_partition_route`, `vertex_cover_hamiltonian_route`, and
  `hard_cnf_three_sat_clique_route`.
- L6 removed the basic `three_sat_chromatic_textbook_adapter` because the
  active benchmark already covers SAT-to-graph textbook routing through harder
  wrapped or multi-hop samples.
- Active levels remain L0-L8 and the manifest contains 68 usable samples.
- This change does not modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.12.1

- Further pruned functionally redundant active benchmark samples after auditing
  the retained L0-L8 surface.
- L5 now keeps one hard representative for each encoding-bridge shape:
  right projection, nested-left projection, nested-right projection, and
  sandwiched projection. Removed the paired horizontal duplicates
  `hard_right_tagged_knapsack_partition_bridge`,
  `hard_nested_left_set_covering_hitting_set_bridge`,
  `hard_nested_right_partition_max_cut_bridge`, and
  `hard_sandwiched_chromatic_clique_cover_bridge`.
- L6 now keeps one hard right-projection textbook adapter representative.
  Removed the duplicate right-projection hard textbook adapters
  `hard_tagged_clique_set_packing_textbook_adapter` and
  `hard_tagged_knapsack_partition_textbook_adapter`.
- Active levels remain L0-L8 and the manifest contains 75 usable samples.
- This change does not modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.12.0

- Pruned functionally redundant active benchmark samples before adding any new
  hard layer.
- Removed the L9 public-proposition smoke layer and its gold proofs. L9
  overlapped L0 direct membership, L7 Schaefer, and L8 local-adapter coverage,
  so keeping it active inflated runtime without exposing a new capability.
- Removed the 8 ordinary L5 `tagged_*_projection_bridge` samples. The remaining
  L5 hard right/nested/sandwiched bridge samples preserve the encoding-bridge
  capability with less repeated projection-pattern enumeration.
- Removed the duplicate L4 `vertex_cover_feedback_arc_route` sample because its
  public Lean target and hidden target were identical to
  `hard_vertex_cover_feedback_arc_route`.
- Removed 5 basic L6 textbook-adapter samples whose source/target route is
  already covered by a harder tagged/nested/sandwiched wrapper:
  `three_sat_clique_textbook_adapter`,
  `clique_set_packing_textbook_adapter`,
  `chromatic_clique_cover_textbook_adapter`,
  `set_cover_exact_cover_textbook_adapter`, and
  `knapsack_partition_textbook_adapter`.
- Active levels are now L0-L8 and the manifest contains 81 usable samples.
- This change does not modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.11.1

- Added L9 gold proof files under `Benchmark/GoldProofs/L9/` for all four
  public Lean proposition baseline samples:
  - `three_sat_public_np_membership`
  - `three_sat_exists_route_to_np_target`
  - `tagged_clique_public_adapter`
  - `schaefer_nae3_public_npcomplete`
- The gold proofs compile directly with `lake env lean` and let
  `--require-gold-proofs` check L9 benchmark closure without exposing proof
  terms to opencode.
- Real opencode L9 baseline run passed 4/4 with zero command-policy,
  timeout, workspace-permission, or Lean-environment failures.
- This confirms L9 is now a useful public-proposition regression layer, but it
  is not yet a capability ceiling: future open-route samples should require
  nontrivial targets, multi-step routes, or helper certificates instead of
  allowing direct/self-route solutions.
- This change does not modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.11.0

- Migrated all four L8 local-adapter samples to the public Lean proposition
  contract. Active benchmark levels L0-L9 now all ask opencode to write only
  `ProofCertificate.lean`.
- Each L8 public target now requires a local semantic adapter proof, a costed
  `KarpReductionM`, the corresponding `PolyReducibleM`, target NP-membership,
  and final source NP-membership.
- Added L8 gold proof files under `Benchmark/GoldProofs/L8/` proving the public
  target propositions from `mathlib + ComplexityReduction`.
- Public Lean proposition validation now honors `--require-gold-proofs`; a
  missing or non-compiling gold proof blocks sample verification when the flag
  is enabled.
- The legacy two-file hidden-target path remains only for archived reports and
  manual compatibility samples. This change does not modify
  `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.10.2

- Tightened L2 public Lean proposition targets. Each L2 sample now requires a
  fixed route target, a `KarpReductionM` certificate to that target, target
  NP-membership, and final source NP-membership.
- Tightened L4 public Lean proposition targets. Each L4 sample now requires two
  fixed route targets, both edge `KarpReductionM` certificates, a composed
  `PolyReducibleM`, final-target NP-membership, and source NP-membership.
- Tightened L5 public Lean proposition targets. Each L5 sample now requires a
  fixed normalized problem, a `ProblemEquivM` encoding bridge, a route from the
  normalized problem to a fixed target, a lifted reducibility certificate, and
  source membership.
- Tightened L6 public Lean proposition targets. Each L6 sample now requires a
  fixed textbook target, a direct adapter `KarpReductionM`, the corresponding
  `PolyReducibleM`, target membership, and source membership.
- Tightened L7 public Lean proposition targets. Each L7 Schaefer hard-side
  sample now requires an explicit `HardRelationCertificate` in addition to the
  NP-completeness proposition.
- Updated L2/L4/L5/L6/L7 hidden target `sampleClaim` declarations to mirror
  the strengthened public propositions for local benchmark sanity checks.
- Public proposition report metrics now classify route, multihop, encoding
  bridge, textbook adapter, and Schaefer hard-side obligations from the public
  Lean target type instead of hard-coding those obligations to false.
- This is a benchmark contract and runner reporting change only. It does not
  modify `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.10.1

- Tightened L1 public Lean proposition targets. L1 no longer asks only for
  `InNPEnc CostedPolyTimeModel problem`, which could be closed for arbitrary
  encoded problems through the generic decidability wrapper. Each L1 sample now
  requires both:
  - `SAT.TMInNPWithCheckedSuffixDecoder problem`
  - `TMInNP problem`
- Tightened L3 public Lean proposition targets. L3 interface samples now expose
  a public `referenceProblem` and require an existential `ProblemEquivM`
  adapter, the reduction induced by that adapter, reference NP membership, and
  final membership for the interface problem.
- Updated L1 hidden targets to mirror the checked-suffix/TM-membership claim.
- Updated L3 hidden targets to mirror the public adapter-existence claim.
- Changed public opencode workspace setup to copy trusted `ComplexityReduction`
  Lean artifacts instead of symlinking the real `.lake` cache. The copied
  snapshot includes both the `ComplexityReduction/` submodule artifact tree and
  the top-level `ComplexityReduction.olean/.ilean` root module artifacts. This
  prevents an opencode-side `lake build` from deleting or mutating the
  validator's real build artifacts through a symlink while keeping
  `import ComplexityReduction` usable inside the public workspace.
- The copied trusted artifact snapshot is now made read-only inside the public
  workspace. This prevents parallel opencode jobs sharing the same public
  workspace from deleting or rewriting each other's copied `.olean/.ilean`
  dependencies during scratch `lake` checks.
- This is a benchmark contract change only. It does not modify
  `Reference/ComplexityReduction`.

## opencode_decision_problem_v0.10.0

- Migrated all L0-L7 usable samples to the public Lean proposition contract:
  `certificate_contract: lean_proposition`.
- L0-L7 samples now expose a public `lean_preamble`, `lean_target_name`, and
  `lean_target_type`. Opencode writes only `ProofCertificate.lean`; the runner
  validates by concatenating the public preamble with that proof and checking
  the final target theorem type in Lean.
- The migration uses old HiddenTargets only as a source for public statement
  generation. It does not keep old route/adapter companion field requirements
  such as `routeTarget`, `normalizedProblem`, `textbookTarget`, or
  `hardCertificate` for L0-L7.
- Public Lean preambles keep only problem-definition helpers needed to state the
  input problem, such as `sourceProblem` or `cspLanguage`; route targets and
  reduction-claim helpers are not migrated into the public contract.
- Removed old route-prescribing proof sentences from L0-L7 public natural
  language descriptions.
- The `lean_proposition` prompt no longer displays public sample metadata whose
  historical names may encode old route/adapter categories; it shows the
  natural-language description, declaration catalog, public Lean preamble, and
  target theorem type.
- L8 remains on the legacy two-file hidden-target local-adapter contract.
- The manifest still contains 99 usable samples; 95 now use
  `lean_proposition` and 4 L8 samples remain legacy.

## opencode_decision_problem_v0.9.0

- Added the public Lean proposition benchmark channel through
  `certificate_contract: lean_proposition`.
- In this channel, a sample exposes a public Lean preamble plus a target theorem
  type. Opencode writes one file, `ProofCertificate.lean`, and the runner
  accepts the sample only when the generated public validator compiles the
  declared target theorem.
- This channel deliberately does not require fixed route-field declarations such
  as `textbookTarget`, `localAdapterProof`, or `hardCertificate`; opencode may
  choose helper declarations, route targets, imports, reductions, and
  intermediate lemmas freely.
- Added `L9` public Lean proposition samples:
  - `three_sat_public_np_membership`
  - `three_sat_exists_route_to_np_target`
  - `tagged_clique_public_adapter`
  - `schaefer_nae3_public_npcomplete`
- Generalized `--levels` filtering through `L9`.
- The manifest now contains 99 usable samples.

## opencode_decision_problem_v0.8.0

- Added `L7` Schaefer hard-side proposition samples:
  - `three_sat_like_schaefer_hard_certificate`
  - `one_in_three_schaefer_hard_certificate`
  - `nae3_schaefer_hard_certificate`
- Added `L8` local-adapter authoring samples:
  - `right_tagged_clique_local_adapter`
  - `nested_vertex_cover_local_adapter`
  - `sandwiched_knapsack_local_adapter`
  - `nested_nae3_csp_local_adapter`
- Generalized benchmark level discovery and `--levels` filtering through `L8`.
- Added generic hidden-validator obligation support for:
  - Schaefer hard-side certificates: `cspLanguage`, `hardCertificate`,
    `schaeferCompletenessCertificate`, and the final proposition certificate.
  - local adapter authoring: `localAdapterProof`, `localAdapterReduction`,
    `localAdapterRoute`, `localAdapterTargetInNP`, and the final membership
    certificate.
- Added report metrics for Schaefer hard-side and local-adapter obligations.
- The manifest now contains 95 usable samples.

## opencode_decision_problem_v0.7.1

- Added 6 harder `L6` textbook-adapter samples without changing runner ABI.
- The new samples combine interface normalization with textbook route
  obligations: opencode must bind an ignored-flag or nested-wrapper input
  interface, then provide one costed Karp reduction from that interface to the
  requested textbook target.
- Covered families:
  - tagged 3-SAT to Clique;
  - tagged Clique to Set Packing;
  - nested Vertex Cover to Set Covering;
  - nested Set Covering to Exact Cover;
  - sandwiched Chromatic Number to Clique Cover;
  - tagged Knapsack to Partition.
- The visible YAML still contains only natural-language problem statements and
  difficulty metadata. It does not expose theorem names, local problem symbols,
  hidden target paths, route answers, or proof terms.
- The manifest now contains 88 usable samples.

## 2026-06-07 P0-P2 benchmark substrate

- Added default opencode oracle isolation for usable-sample runs:
  - opencode runs from a run-local public workspace under
    `.reduction-agent/opencode_public_workspaces/<run-id>/`;
  - `Benchmark/HiddenTargets`, `Benchmark/GoldProofs`, `.reduction-agent`,
    `.lake`, and opencode cache/data directories are excluded from that public
    copy;
  - Lake dependency paths and manifest package directories are rewritten for the
    public workspace;
  - only the trusted `ComplexityReduction` build artifacts are copied into the
    public `.lake/build/lib/lean` tree when available.
- Added `--disable-opencode-oracle-isolation` as a debugging escape hatch.
- `--opencode-public-root` now selects the public workspace base directory.
- Added optional hidden gold proofs under `Benchmark/GoldProofs/Lx/<sample>.lean`.
- Added `--gold-proof-root` and `--require-gold-proofs`.
- Added proposition-level certificate contract support through sample metadata
  `certificate_contract: proposition`.
- In proposition mode the membership-stage file may define
  `propositionCertificate : BenchmarkHiddenSample.sampleClaim`; legacy
  `npMembershipCertificate` remains accepted as a fallback.
- Added report metadata/metrics for oracle isolation, trusted public olean
  links, gold proof presence/compilation, and proposition certificate
  validation.
- Added `Benchmark/GoldProofs/L0/clique.lean` as the first hidden gold proof
  smoke target.

## opencode_decision_problem_v0.7.0

- Added 24 higher-pressure samples:
  - 8 `L4` multi-hop route-composition samples.
  - 8 `L5` encoding/interface-normalization bridge samples.
  - 8 `L6` textbook-construction adapter samples.
- `L4` samples require `routeTarget1`, `routeTarget2`, `reductionStep1`,
  `reductionStep2`, `composedReduction`, `routeTarget2InNP`, and the final
  `npMembershipCertificate`.
- `L5` samples require `normalizedProblem`, `encodingBridgeCertificate`,
  `normalizedRouteTarget`, `normalizedReductionCertificate`,
  `liftedReductionCertificate`, `normalizedRouteTargetInNP`, and the final
  `npMembershipCertificate`.
- `L6` samples require `textbookTarget`, `textbookReductionCertificate`,
  `textbookRouteCertificate`, `textbookTargetInNP`, and the final
  `npMembershipCertificate`.
- The visible sample YAML still gives only natural-language decision problems
  and difficulty metadata. It does not expose NP/P labels, Lean symbols,
  theorem names, route targets, hidden target names, or membership terms.
- Runner hidden-target detection, generated `CombinedValidator.lean`, dry-run
  report defaults, per-sample result summaries, and aggregate metrics now
  support L4/L5/L6 obligations.
- Added report metrics:
  `usable_multihop_route_obligation_count`,
  `usable_multihop_route_certificate_verified_count`,
  `usable_complete_multihop_route_to_np_verified_count`,
  `usable_encoding_bridge_obligation_count`,
  `usable_encoding_bridge_certificate_verified_count`,
  `usable_complete_encoding_bridge_to_np_verified_count`,
  `usable_textbook_adapter_obligation_count`,
  `usable_textbook_adapter_certificate_verified_count`, and
  `usable_complete_textbook_adapter_to_np_verified_count`.
- The manifest now contains 70 usable samples.

## opencode_decision_problem_v0.6.0

- Added 6 L3 interface-adapter samples:
  - `clique_audit_interface`
  - `vertex_cover_disabled_exception_interface`
  - `set_covering_duplicate_checker_interface`
  - `knapsack_double_negation_interface`
  - `max_cut_audit_interface`
  - `hitting_set_disabled_fallback_interface`
- L3 samples are designed to avoid the previous "find a theorem and fill the
  fields" ceiling. The visible sample still gives only the problem statement,
  but the formal hidden `sampleProblem` is an interface variant of a local
  library target.
- L3 membership certificates must provide:
  - `referenceProblem`
  - `interfaceEquivalenceCertificate : ProblemEquivM ... problem referenceProblem`
  - `interfaceReductionCertificate : KarpReductionM ... problem referenceProblem`
  - `referenceMembershipCertificate : InNPEnc ... referenceProblem`
- The hidden validator checks those adapter claims after opencode returns. This
  requires local Lean interface proof authoring, reference-definition unfolding
  or repair, costed adapter packaging, and library theorem invocation.
- Added L3 report metrics:
  `usable_interface_adapter_obligation_count`,
  `usable_interface_adapter_certificate_verified_count`, and
  `usable_complete_interface_adapter_to_np_verified_count`.
- The manifest now contains 46 usable samples.

## opencode_decision_problem_v0.5.0

- Split usable samples and hidden targets into level directories:
  - `Benchmark/Samples/L0` and `Benchmark/HiddenTargets/L0`
  - `Benchmark/Samples/L1` and `Benchmark/HiddenTargets/L1`
  - `Benchmark/Samples/L2` and `Benchmark/HiddenTargets/L2`
- Added 5 L2 route-composition samples:
  - `numeric_subset_tradeoff_route`
  - `exact_cover_route`
  - `graph_coloring_route`
  - `set_cover_budget_route`
  - `generated_mixed_csp_route`
- L2 sample ids, names, and file paths use neutral names so they do not reveal
  the hidden route target.
- L2 samples still expose only natural-language decision problems, but their
  hidden targets additionally validate `routeTarget`, `reductionCertificate`,
  and `routeTargetInNP` before accepting the final NP-membership certificate.
- Runner hidden-target lookup now supports level directories while retaining a
  flat-path fallback for older local reports.
- Added route-composition report metrics:
  `usable_route_obligation_count`, `usable_route_certificate_verified_count`,
  and `usable_complete_route_to_np_verified_count`.

## opencode_decision_problem_v0.4.2

- The generated final `CombinedValidator.lean` now provides a generic
  `ProblemCertificate.problem` alias for the already inlined top-level
  `problem`.
- This supports membership certificates that qualify the companion certificate
  declaration through the local certificate file name, while still validating
  the exact hidden sample claim.

## opencode_decision_problem_v0.4.1

- Final membership validation now uses the run-local
  `ProblemCertificate.lean` snapshot that passed the problem-binding validator.
- Later mutations to the artifact copy of `ProblemCertificate.lean` are reported
  as diagnostics (`problem_certificate_modified_after_binding`) instead of
  adding a proof-blocking obligation.

## opencode_decision_problem_v0.4.0

- Added 10 higher-pressure usable samples for structured and binary-structured
  encodings:
  - structured graph/set-system variants
  - binary-numeric integer-programming, knapsack, and max-cut variants
- The new samples still expose only natural-language decision-problem
  statements to opencode. The matching Lean problem symbols remain only in
  `Benchmark/HiddenTargets/*.lean` for runner-side validation.
- The benchmark now contains 35 usable samples.
- Corrected the visible `max_cut` sample statement to match its hidden unit-edge
  Max Cut target. The weighted/binary-numeric variant remains a separate
  structured sample.
- Added one generic opencode repair round by default after Lean validation
  failure. Repair receives compact compiler/validator feedback, not hidden
  target source or benchmark answer data.

## opencode_decision_problem_v0.3.0

- Split the benchmark samples out of `Benchmark/MANIFEST.yaml` into one file
  per sample under `Benchmark/Samples/`.
- `Benchmark/MANIFEST.yaml` now uses `usable_sample_files` to list the sample
  files in benchmark order.
- Moved hidden Lean sample targets out of the runner and into
  `Benchmark/HiddenTargets/*.lean`.
- Added `--hidden-target-root` so strict benchmark runs can keep hidden targets
  outside the opencode-readable workspace.
- Added runner support for `--jobs` / `--usable-sample-jobs` to process usable
  samples concurrently. The default remains `1`.

## opencode_decision_problem_v0.2.0

- Removed the obsolete fixture directories.
- Removed manifest split/directories entries and fixture-derived diagnostic
  metrics from `Benchmark/MANIFEST.yaml`.
- Replaced direct-answer usable samples with problem-only decision-problem
  samples.
- Removed positive membership labels from sample ids and names. Samples no
  longer expose theorem names, route answers, problem symbols, or membership
  terms.
- The runner now treats opencode as the system under test for usable samples.
  Without `--opencode-usable-samples`, samples are reported as not evaluated
  instead of being deterministically passed by a local registry.
- The benchmark pass condition now uses a hidden target validator. After
  opencode returns, the runner generates `CombinedValidator.lean`, appends the
  hidden `sampleProblem/sampleClaim`, appends the two opencode certificate
  files, and accepts the sample only if Lean checks that the certificate proves
  the hidden sample claim.
## 2026-06-07

- Added 12 hard usable samples without changing runner ABI:
  - 4 L4 fixed two-hop route samples.
  - 8 L5 non-identity encoding bridge samples.
- Manifest usable sample count increased from 70 to 82.
- Added hard single-sample manifests under `.reduction-agent/tmp/`.
- Added `--levels` / `--benchmark-levels` to run an arbitrary subset of
  manifest levels from L0 through L6.
