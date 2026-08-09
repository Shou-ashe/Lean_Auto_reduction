/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalMicro
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauControlUniqueness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauIOStacks

/-!
Decoded evidence from the global fixed-pair verifier tableau CNF.

The older extraction layer targets `tmVerifierFixedPairTableauCNF`, whose
transition rows use row-local micro-time names.  This file mirrors the boundary
extraction for `tmVerifierGlobalTableauCNF`, where transition micro rows are
named by `tmVerifierFixedMicroTime V p t micro`.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierGlobalTableauCNF_satisfies_controlDomainRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_initialControl
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierInitialControlCNF V) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_initialStack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_stackWellFormedRows
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierStackWellFormedRowsCNF V p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_endpoint
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    CNF.Satisfies (tmVerifierEndpointCNF V p) a :=
  tmVerifierGlobalTableauCNF_satisfies_block V B p a h (by
    simp [tmVerifierGlobalTableauBlocks])

theorem tmVerifierGlobalTableauCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B (x, c)) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  tmVerifierInitialStackCNF_satisfies_instancePrefix V x c a
    (tmVerifierGlobalTableauCNF_satisfies_initialStack V B (x, c) a h)

/--
Boundary evidence extracted from a satisfied global fixed-pair tableau CNF.

This is the global-micro analogue of `TMVerifierFixedPairTableauEvidence`; later
soundness slices should consume this structure instead of rebuilding extraction
from row-local micro-time clauses.
-/
structure TMVerifierGlobalTableauEvidence {L : EncodedDecisionProblem}
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
  transitionFixedMicroDomainRow :
    ∀ t, t ∈ tmVerifierTransitionTimeRange V p →
      CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t) a
  transitionFixedRow :
    ∀ t, t ∈ tmVerifierTransitionTimeRange V p →
      CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V B p t) a
  endpoint_halted :
    (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none).eval a = true
  endpoint_state :
    (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState).eval
      a = true
  endpoint_output_true :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p)) a
  instance_prefix :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V p.1) a

noncomputable def tmVerifierGlobalTableauCNF_evidence
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierGlobalTableauCNF V B p) a) :
    TMVerifierGlobalTableauEvidence V B p a := by
  let hControlRows := tmVerifierGlobalTableauCNF_satisfies_controlDomainRows V B p a h
  let hInitialControl := tmVerifierGlobalTableauCNF_satisfies_initialControl V B p a h
  let hEndpoint := tmVerifierGlobalTableauCNF_satisfies_endpoint V B p a h
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
        tmVerifierGlobalTableauCNF_satisfies_initialStack V B p a h
      stackWellFormedRow := fun t ht =>
        tmVerifierStackWellFormedRowsCNF_satisfies_at V p t a
          (tmVerifierGlobalTableauCNF_satisfies_stackWellFormedRows V B p a h) ht
      transitionFixedMicroDomainRow := fun t ht =>
        tmVerifierGlobalTableauCNF_satisfies_transitionFixedMicroDomainRow V B p t a h ht
      transitionFixedRow := fun t ht =>
        tmVerifierGlobalTableauCNF_satisfies_transitionFixedRow V B p t a h ht
      endpoint_halted :=
        tmVerifierHaltingControlCNFAt_satisfies_halted V (tmVerifierTimeBound V p) a
          (tmVerifierEndpointCNF_satisfies_halting V p a hEndpoint)
      endpoint_state :=
        tmVerifierEndpointCNF_satisfies_initialState V p a hEndpoint
      endpoint_output_true :=
        tmVerifierEndpointCNF_satisfies_outputTrue V p a hEndpoint
      instance_prefix :=
        tmVerifierGlobalTableauCNF_satisfies_instancePrefix V B p.1 p.2 a h }

namespace TMVerifierGlobalTableauEvidence

theorem controlRow_label_proof_irrel
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht ht' : t ∈ tmVerifierTableauTimeRange V p) :
    (E.controlRow t ht).label = (E.controlRow t ht').label := by
  have hproof : ht = ht' := Subsingleton.elim ht ht'
  cases hproof
  rfl

theorem stackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V p)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a :=
  tmVerifierAllStackWellFormedCNFAt_satisfies_stackDomains V p t k a
    (E.stackWellFormedRow t ht)

theorem transitionStackCellDomainsAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a :=
  E.stackCellDomainsAt t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht) k

/-- The decoded TM2 configuration represented by one macro row of a global tableau. -/
noncomputable def decodedCfg
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V p) : (tmVerifierTM V).Cfg where
  l := (E.controlRow t ht).label
  var := (E.controlRow t ht).state
  stk := fun k => tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht k)

theorem decodedCfg_proof_irrel
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht ht' : t ∈ tmVerifierTableauTimeRange V p) :
    E.decodedCfg t ht = E.decodedCfg t ht' := by
  have hproof : ht = ht' := Subsingleton.elim ht ht'
  cases hproof
  rfl

theorem decodedCfg_eq_of_time_eq
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t u : Nat} (ht : t ∈ tmVerifierTableauTimeRange V p)
    (hu : u ∈ tmVerifierTableauTimeRange V p) (htu : t = u) :
    E.decodedCfg t ht = E.decodedCfg u hu := by
  subst u
  exact E.decodedCfg_proof_irrel _ _

theorem initialControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    (E.controlRow 0 (tmVerifierTableauTimeRange_zero_mem V p)).label =
      some (tmVerifierTM V).main := by
  let ht0 := tmVerifierTableauTimeRange_zero_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).label_true E.initial_label

theorem initialControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    (E.controlRow 0 (tmVerifierTableauTimeRange_zero_mem V p)).state =
      (tmVerifierTM V).initialState := by
  let ht0 := tmVerifierTableauTimeRange_zero_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).state_true E.initial_state

theorem endpointControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    (E.controlRow (tmVerifierTimeBound V p)
      (tmVerifierTableauTimeRange_timeBound_mem V p)).label = none := by
  let htEnd := tmVerifierTableauTimeRange_timeBound_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V (tmVerifierTimeBound V p) a
    (E.controlDomainRow (tmVerifierTimeBound V p) htEnd)
    (E.controlRow (tmVerifierTimeBound V p) htEnd).label_true E.endpoint_halted

theorem endpointControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    (E.controlRow (tmVerifierTimeBound V p)
      (tmVerifierTableauTimeRange_timeBound_mem V p)).state =
      (tmVerifierTM V).initialState := by
  let htEnd := tmVerifierTableauTimeRange_timeBound_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V (tmVerifierTimeBound V p) a
    (E.controlDomainRow (tmVerifierTimeBound V p) htEnd)
    (E.controlRow (tmVerifierTimeBound V p) htEnd).state_true E.endpoint_state

theorem decodedCfg_initial
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p) =
      tmVerifierInitialCfg V p := by
  let ht0 := tmVerifierTableauTimeRange_zero_mem V p
  have hStacks :
      (fun k => tmVerifierDecodedStackList V p 0 k a (E.stackCellDomainsAt 0 ht0 k)) =
        (tmVerifierInitialCfg V p).stk := by
    funext k
    by_cases hk : k = (tmVerifierTM V).k₀
    · subst k
      simpa [tmVerifierInitialCfg_input_stack] using
        tmVerifierDecodedStackList_initial_input_eq V p a E.initial_stack
          (E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀)
    · simpa [tmVerifierInitialCfg_noninput_stack_empty V p k hk] using
        tmVerifierDecodedStackList_initial_noninput_eq V p a E.initial_stack k hk
          (E.stackCellDomainsAt 0 ht0 k)
  change
    { l := (E.controlRow 0 ht0).label
      var := (E.controlRow 0 ht0).state
      stk := fun k => tmVerifierDecodedStackList V p 0 k a (E.stackCellDomainsAt 0 ht0 k) } =
      tmVerifierInitialCfg V p
  rw [E.initialControlRow_label, E.initialControlRow_state]
  exact Turing.TM2.Cfg.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, hStacks⟩

theorem decodedCfg_endpoint_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    E.decodedCfg (tmVerifierTimeBound V p) (tmVerifierTableauTimeRange_timeBound_mem V p) =
      tmVerifierOutputCfg V true := by
  let htEnd := tmVerifierTableauTimeRange_timeBound_mem V p
  let tEnd := tmVerifierTimeBound V p
  have hStacks :
      (fun k => tmVerifierDecodedStackList V p tEnd k a (E.stackCellDomainsAt tEnd htEnd k)) =
        (tmVerifierOutputCfg V true).stk := by
    funext k
    by_cases hk : k = (tmVerifierTM V).k₁
    · subst k
      simpa [tmVerifierOutputCfg_output_stack] using
        tmVerifierDecodedStackList_output_true_eq V p tEnd a E.endpoint_output_true
          (E.stackCellDomainsAt tEnd htEnd (tmVerifierTM V).k₁)
    · simpa [tmVerifierOutputCfg_nonoutput_stack_empty V true k hk] using
        tmVerifierDecodedStackList_output_true_nonoutput_eq V p tEnd a E.endpoint_output_true k
          hk (E.stackCellDomainsAt tEnd htEnd k)
  change
    { l := (E.controlRow tEnd htEnd).label
      var := (E.controlRow tEnd htEnd).state
      stk := fun k => tmVerifierDecodedStackList V p tEnd k a
        (E.stackCellDomainsAt tEnd htEnd k) } =
      tmVerifierOutputCfg V true
  rw [E.endpointControlRow_label, E.endpointControlRow_state]
  exact Turing.TM2.Cfg.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, hStacks⟩

theorem transitionDecodedCfg_halted
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        none) :
    E.decodedCfg (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) =
      E.decodedCfg t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht) := by
  let ht0 := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht
  let ht1 := tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht
  let s0 := (E.controlRow t ht0).state
  have hs0 : s0 ∈ tmVerifierStateList V := by
    classical
    simp [tmVerifierStateList]
  have hHaltedRows : CNF.Satisfies (tmVerifierHaltedRowsCNFAt V p t) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierTransitionFixedControlCNFAt V p t)
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
        tmVerifierHaltedRowsCNFAt V p t) a).1
        (by simpa [tmVerifierTransitionFixedRowCNFAt] using E.transitionFixedRow t ht)
    exact (CNF.satisfies_append
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t)
      (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.2
  have hHaltedRow :
      CNF.Satisfies (tmVerifierHaltedRowCNFAt V p t s0) a :=
    tmVerifierHaltedRowsCNFAt_satisfies_state V p t s0 a hHaltedRows hs0
  have hAntecedents :
      ∀ g ∈ tmVerifierHaltedRowAntecedents V t s0, g.eval a = true := by
    intro g hg
    have hg' :
        g = tmVerifierLabelAtom V t none ∨
          g = tmVerifierStateAtom V t s0 := by
      simpa [tmVerifierHaltedRowAntecedents] using hg
    rcases hg' with rfl | rfl
    · simpa [← hLabel] using (E.controlRow t ht0).label_true
    · exact (E.controlRow t ht0).state_true
  have hNextControl :=
    tmVerifierHaltedRowCNFAt_satisfies_next_control V p t s0 a hHaltedRow hAntecedents
  have hNextLabel :
      (E.controlRow (t + 1) ht1).label = none := by
    exact tmVerifierControlDomainCNFAt_satisfies_label_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).label_true hNextControl.1
  have hNextState :
      (E.controlRow (t + 1) ht1).state = s0 := by
    exact tmVerifierControlDomainCNFAt_satisfies_state_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).state_true hNextControl.2
  have hStacks :
      (fun k => tmVerifierDecodedStackList V p (t + 1) k a
        (E.stackCellDomainsAt (t + 1) ht1 k)) =
        (fun k => tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht0 k)) := by
    funext k
    exact TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
      (tmVerifierHaltedRowCNFAt_satisfies_frame V p t s0 a hHaltedRow hAntecedents k
        (E.stackCellDomainsAt t ht0 k) (E.stackCellDomainsAt (t + 1) ht1 k))
  simp [decodedCfg, s0, hLabel, hNextLabel, hNextState, hStacks]

end TMVerifierGlobalTableauEvidence

namespace TMVerifierXOnlyGlobalTableauSeed

/-- Extract global fixed-pair tableau evidence from an x-only global tableau seed. -/
noncomputable def globalEvidence {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    TMVerifierGlobalTableauEvidence V B (x, w.cert) a :=
  tmVerifierGlobalTableauCNF_evidence V B (x, w.cert) a w.global_tableau

theorem initialLabel_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)).eval a = true :=
  w.globalEvidence.initial_label

theorem endpointHalted_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (tmVerifierLabelAtom V (tmVerifierTimeBound V (x, w.cert)) none).eval a = true :=
  w.globalEvidence.endpoint_halted

theorem prefixCNF_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  w.globalEvidence.instance_prefix

theorem initialControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (w.globalEvidence.controlRow 0
      (tmVerifierTableauTimeRange_zero_mem V (x, w.cert))).label =
      some (tmVerifierTM V).main :=
  w.globalEvidence.initialControlRow_label

theorem initialControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (w.globalEvidence.controlRow 0
      (tmVerifierTableauTimeRange_zero_mem V (x, w.cert))).state =
      (tmVerifierTM V).initialState :=
  w.globalEvidence.initialControlRow_state

theorem endpointControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (w.globalEvidence.controlRow (tmVerifierTimeBound V (x, w.cert))
      (tmVerifierTableauTimeRange_timeBound_mem V (x, w.cert))).label = none :=
  w.globalEvidence.endpointControlRow_label

theorem endpointControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    (w.globalEvidence.controlRow (tmVerifierTimeBound V (x, w.cert))
      (tmVerifierTableauTimeRange_timeBound_mem V (x, w.cert))).state =
      (tmVerifierTM V).initialState :=
  w.globalEvidence.endpointControlRow_state

/-- The decoded TM2 configuration represented by one macro row of the seed. -/
noncomputable def decodedCfg
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V (x, w.cert)) :
    (tmVerifierTM V).Cfg :=
  w.globalEvidence.decodedCfg t ht

theorem decodedCfg_initial
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    w.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V (x, w.cert)) =
      tmVerifierInitialCfg V (x, w.cert) :=
  w.globalEvidence.decodedCfg_initial

theorem decodedCfg_endpoint_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    w.decodedCfg (tmVerifierTimeBound V (x, w.cert))
        (tmVerifierTableauTimeRange_timeBound_mem V (x, w.cert)) =
      tmVerifierOutputCfg V true :=
  w.globalEvidence.decodedCfg_endpoint_true

theorem transitionDecodedCfg_halted
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, w.cert))
    (hLabel :
      (w.globalEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, w.cert) ht)).label =
        none) :
    w.decodedCfg (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, w.cert) ht) =
      w.decodedCfg t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, w.cert) ht) :=
  w.globalEvidence.transitionDecodedCfg_halted ht hLabel

end TMVerifierXOnlyGlobalTableauSeed

end SAT
end ComplexityReduction
