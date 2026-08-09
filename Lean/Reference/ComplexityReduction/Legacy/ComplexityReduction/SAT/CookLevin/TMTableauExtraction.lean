/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauBlocks

/-!
Decoded evidence from the aggregate verifier-tableau CNF.

`TMTableauBlocks` packages the fixed-pair CNF and proves component extraction.
This file starts the next semantic layer: a satisfied aggregate tableau yields
decoded finite-control rows plus the initial, stack-domain, transition-row, and
endpoint evidence that operational tableau correctness will consume.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Decoded finite-control rows -/

/-- A decoded control row chooses the unique control values witnessed by the row CNF. -/
structure TMVerifierDecodedControlRow {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (a : Assignment) : Type where
  label : Option (tmVerifierTM V).Λ
  state : (tmVerifierTM V).σ
  label_true : (tmVerifierLabelAtom V t label).eval a = true
  state_true : (tmVerifierStateAtom V t state).eval a = true

theorem tmVerifierExactlyOneLabelCNFAt_satisfies_has_label
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierExactlyOneLabelCNFAt V t) a) :
    ∃ label : Option (tmVerifierTM V).Λ,
      (tmVerifierLabelAtom V t label).eval a = true := by
  let atoms := tmVerifierLabelAtomsAt V t
  have hsplit :
      CNF.Satisfies (CookLevin.atLeastOneCNF atoms) a ∧
        CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    simpa [tmVerifierExactlyOneLabelCNFAt, CookLevin.exactlyOneCNF, atoms]
      using (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
        (CookLevin.atMostOneCNF atoms) a).1 h
  rcases (CookLevin.atLeastOneCNF_satisfies atoms a).1 hsplit.1 with
    ⟨lit, hlit, htrue⟩
  rcases List.mem_map.mp hlit with ⟨label, _hlabel, rfl⟩
  exact ⟨label, htrue⟩

theorem tmVerifierExactlyOneStateCNFAt_satisfies_has_state
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierExactlyOneStateCNFAt V t) a) :
    ∃ state : (tmVerifierTM V).σ, (tmVerifierStateAtom V t state).eval a = true := by
  let atoms := tmVerifierStateAtomsAt V t
  have hsplit :
      CNF.Satisfies (CookLevin.atLeastOneCNF atoms) a ∧
        CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    simpa [tmVerifierExactlyOneStateCNFAt, CookLevin.exactlyOneCNF, atoms]
      using (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
        (CookLevin.atMostOneCNF atoms) a).1 h
  rcases (CookLevin.atLeastOneCNF_satisfies atoms a).1 hsplit.1 with
    ⟨lit, hlit, htrue⟩
  rcases List.mem_map.mp hlit with ⟨state, _hstate, rfl⟩
  exact ⟨state, htrue⟩

noncomputable def tmVerifierControlDomainCNFAt_decoded
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a) :
    TMVerifierDecodedControlRow V t a := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierExactlyOneLabelCNFAt V t)
    (tmVerifierExactlyOneStateCNFAt V t) a).1
      (by simpa [tmVerifierControlDomainCNFAt] using h)
  let hlabelExists := tmVerifierExactlyOneLabelCNFAt_satisfies_has_label V t a hsplit.1
  let hstateExists := tmVerifierExactlyOneStateCNFAt_satisfies_has_state V t a hsplit.2
  let label := Classical.choose hlabelExists
  let state := Classical.choose hstateExists
  have hlabel : (tmVerifierLabelAtom V t label).eval a = true :=
    Classical.choose_spec hlabelExists
  have hstate : (tmVerifierStateAtom V t state).eval a = true :=
    Classical.choose_spec hstateExists
  exact
    { label := label
      state := state
      label_true := hlabel
      state_true := hstate }

/-! ### Initial and endpoint boundary literals -/

theorem tmVerifierInitialControlCNF_satisfies_initialLabel
    {L : EncodedDecisionProblem} (V : TMVerifier L) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialControlCNF V) a) :
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)).eval a = true := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierUnitCNF (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)))
    (tmVerifierUnitCNF (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)) a).1
      (by simpa [tmVerifierInitialControlCNF] using h)
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)) a).1 hsplit.1

theorem tmVerifierInitialControlCNF_satisfies_initialState
    {L : EncodedDecisionProblem} (V : TMVerifier L) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialControlCNF V) a) :
    (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState).eval a = true := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierUnitCNF (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)))
    (tmVerifierUnitCNF (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)) a).1
      (by simpa [tmVerifierInitialControlCNF] using h)
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState) a).1 hsplit.2

theorem tmVerifierHaltingControlCNFAt_satisfies_halted
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierHaltingControlCNFAt V t) a) :
    (tmVerifierLabelAtom V t none).eval a = true := by
  exact (tmVerifierUnitCNF_satisfies (tmVerifierLabelAtom V t none) a).1
    (by simpa [tmVerifierHaltingControlCNFAt] using h)

/-! ### Aggregate fixed-pair evidence -/

/-- Boundary evidence extracted from a satisfied fixed-pair aggregate tableau CNF. -/
structure TMVerifierFixedPairTableauEvidence {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment) : Type where
  controlDomainRow :
    ∀ t, t ∈ tmVerifierTableauTimeRange V p →
      CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a
  controlRow :
    ∀ t, t ∈ tmVerifierTableauTimeRange V p → TMVerifierDecodedControlRow V t a
  initial_label :
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)).eval a = true
  initial_state :
    (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState).eval a = true
  initial_stack : CNF.Satisfies (tmVerifierInitialStackCNF V p) a
  stackWellFormedRow :
    ∀ t, t ∈ tmVerifierTableauTimeRange V p →
      CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t) a
  transitionMicroDomainRow :
    ∀ t, t ∈ tmVerifierTransitionTimeRange V p →
      CNF.Satisfies (tmVerifierTransitionMicroDomainCNFAt V p t) a
  transitionRow :
    ∀ t, t ∈ tmVerifierTransitionTimeRange V p →
      CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a
  endpoint_halted :
    (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none).eval a = true
  endpoint_state :
    (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState).eval
      a = true
  endpoint_output_true :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a
  instance_prefix :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V p.1) a

noncomputable def tmVerifierFixedPairTableauCNF_evidence
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFixedPairTableauCNF V B p) a) :
    TMVerifierFixedPairTableauEvidence V B p a := by
  let hControlRows := tmVerifierFixedPairTableauCNF_satisfies_controlDomainRows V B p a h
  let hInitialControl := tmVerifierFixedPairTableauCNF_satisfies_initialControl V B p a h
  let hEndpoint := tmVerifierFixedPairTableauCNF_satisfies_endpoint V B p a h
  exact
    { controlDomainRow := fun t ht =>
        tmVerifierControlDomainRowsCNF_satisfies_at V p t a hControlRows ht
      controlRow := fun t ht =>
        tmVerifierControlDomainCNFAt_decoded V t a
          (tmVerifierControlDomainRowsCNF_satisfies_at V p t a hControlRows ht)
      initial_label :=
        tmVerifierInitialControlCNF_satisfies_initialLabel V a hInitialControl
      initial_state :=
        tmVerifierInitialControlCNF_satisfies_initialState V a hInitialControl
      initial_stack :=
        tmVerifierFixedPairTableauCNF_satisfies_initialStack V B p a h
      stackWellFormedRow := fun t ht =>
        tmVerifierStackWellFormedRowsCNF_satisfies_at V p t a
          (tmVerifierFixedPairTableauCNF_satisfies_stackWellFormedRows V B p a h) ht
      transitionMicroDomainRow := fun t ht =>
        tmVerifierFixedPairTableauCNF_satisfies_transitionMicroDomainRow V B p t a h ht
      transitionRow := fun t ht =>
        tmVerifierFixedPairTableauCNF_satisfies_transitionRow V B p t a h ht
      endpoint_halted :=
        tmVerifierHaltingControlCNFAt_satisfies_halted V (tmVerifierTimeBound V p) a
          (tmVerifierEndpointCNF_satisfies_halting V p a hEndpoint)
      endpoint_state :=
        tmVerifierEndpointCNF_satisfies_initialState V p a hEndpoint
      endpoint_output_true :=
        tmVerifierEndpointCNF_satisfies_outputTrue V p a hEndpoint
      instance_prefix :=
        tmVerifierFixedPairTableauCNF_satisfies_instancePrefix V B p.1 p.2 a h }

namespace TMVerifierXOnlyTableauSeed

/-- Extract fixed-pair tableau evidence from an x-only tableau seed. -/
noncomputable def fixedPairEvidence {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    TMVerifierFixedPairTableauEvidence V B (x, w.cert) a :=
  tmVerifierFixedPairTableauCNF_evidence V B (x, w.cert) a w.fixed_tableau

theorem initialLabel_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)).eval a = true :=
  w.fixedPairEvidence.initial_label

theorem endpointHalted_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (tmVerifierLabelAtom V (tmVerifierTimeBound V (x, w.cert)) none).eval a = true :=
  w.fixedPairEvidence.endpoint_halted

theorem endpointState_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (tmVerifierStateAtom V (tmVerifierTimeBound V (x, w.cert))
      (tmVerifierTM V).initialState).eval a = true :=
  w.fixedPairEvidence.endpoint_state

theorem endpointOutputTrue_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V (x, w.cert)
      (tmVerifierTimeBound V (x, w.cert))) a :=
  w.fixedPairEvidence.endpoint_output_true

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
