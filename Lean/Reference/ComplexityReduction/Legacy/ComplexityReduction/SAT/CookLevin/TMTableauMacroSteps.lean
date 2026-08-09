/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauWindowSelection

/-!
Adjacent macro-configuration semantics for decoded tableau rows.

This file packages the selected-window macro-row theorem as an actual
`FinTM2.step` equality between decoded macro configurations.  It is still a
single-step surface; chaining all bounded rows into a run is a later slice.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierFixedPairTableauEvidence

/-- The decoded TM2 configuration represented by one macro tableau row. -/
noncomputable def decodedCfg
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V p) : (tmVerifierTM V).Cfg where
  l := (E.controlRow t ht).label
  var := (E.controlRow t ht).state
  stk := fun k => tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht k)

theorem transitionDecodedCfg_step
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ}
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)) =
      some
        (E.decodedCfg (t + 1)
          (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht)) := by
  let ht0 := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht
  let ht1 := tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht
  let row := E.controlRow t ht0
  let l0 : (tmVerifierTM V).Λ := l
  let s0 : (tmVerifierTM V).σ := row.state
  have hs0 : s0 ∈ tmVerifierStateList V := by
    classical
    simp [tmVerifierStateList]
  have hl0 : l0 ∈ tmVerifierLabelList V := by
    classical
    simp [tmVerifierLabelList]
  have hState : row.state = s0 := rfl
  rcases E.exists_transitionWindowFiniteStepAuxMacroRow ht hl0 hs0 hLabel hState with
    ⟨w, hw, hStep⟩
  let cfg : (tmVerifierTM V).Cfg :=
    Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
      (fun k => tmVerifierDecodedStackList V p t k a
        (E.transitionStackCellDomainsAt ht k))
  have hNextLabel :
      (E.controlRow (t + 1) ht1).label = cfg.l := by
    exact tmVerifierControlDomainCNFAt_satisfies_label_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).label_true (by simpa [cfg] using hStep.1)
  have hNextState :
      (E.controlRow (t + 1) ht1).state = cfg.var := by
    exact tmVerifierControlDomainCNFAt_satisfies_state_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).state_true (by simpa [cfg] using hStep.2.1)
  have hStacks :
      (fun k => tmVerifierDecodedStackList V p (t + 1) k a
        (E.stackCellDomainsAt (t + 1) ht1 k)) = cfg.stk := by
    simpa [cfg] using hStep.2.2
  have hCfg : cfg = E.decodedCfg (t + 1) ht1 := by
    rcases cfg with ⟨cl, cv, cs⟩
    simp [decodedCfg] at hNextLabel hNextState hStacks ⊢
    rw [← hNextLabel, ← hNextState, ← hStacks]
  have hInputStacks :
      (fun k => tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht0 k)) =
        (fun k => tmVerifierDecodedStackList V p t k a
          (E.transitionStackCellDomainsAt ht k)) := by
    funext k
    exact tmVerifierDecodedStackList_eq_of_domain_proofs V p t k a
      (E.stackCellDomainsAt t ht0 k) (E.transitionStackCellDomainsAt ht k)
  have hStepAuxInput :
      Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
          (fun k => tmVerifierDecodedStackList V p t k a
            (E.stackCellDomainsAt t ht0 k)) =
        cfg := by
    exact congrArg (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0) hInputStacks
  have hLeft :
      (tmVerifierTM V).step (E.decodedCfg t ht0) = some cfg := by
    have hExpand :
        (tmVerifierTM V).step (E.decodedCfg t ht0) =
          some (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
            (fun k => tmVerifierDecodedStackList V p t k a
              (E.stackCellDomainsAt t ht0 k))) := by
      simp [decodedCfg, Turing.FinTM2.step, Turing.TM2.step, row, l0, s0, hLabel, hState]
    exact hExpand.trans (congrArg some hStepAuxInput)
  exact hLeft.trans (congrArg some hCfg)

theorem transitionDecodedCfg_halted
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
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
      (tmVerifierTransitionControlCNFAt V t)
      (tmVerifierTransitionWindowStackCNFAt V B p t ++
        tmVerifierHaltedRowsCNFAt V p t) a).1
        (by simpa [tmVerifierTransitionRowCNFAt] using E.transitionRow t ht)
    exact (CNF.satisfies_append
      (tmVerifierTransitionWindowStackCNFAt V B p t)
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

theorem transitionDecodedCfg_stepOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)) =
      Option.bind
        (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label
        (fun _ =>
          some
            (E.decodedCfg (t + 1)
              (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht))) := by
  let ht0 := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht
  cases hLabel :
      (E.controlRow t ht0).label with
  | none =>
      have hStepNone :
          (tmVerifierTM V).step (E.decodedCfg t ht0) = none := by
        change Turing.TM2.step (tmVerifierTM V).m
          { l := (E.controlRow t ht0).label
            var := (E.controlRow t ht0).state
            stk := fun k =>
              tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht0 k) } = none
        rw [hLabel]
        rfl
      rw [hStepNone]
      rfl
  | some l =>
      simpa [hLabel] using E.transitionDecodedCfg_step ht hLabel

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

/-- The decoded TM2 configuration represented by one macro tableau row. -/
noncomputable def decodedCfg
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    (t : Nat) (ht : t ∈ tmVerifierTableauTimeRange V (x, wSeed.cert)) :
    (tmVerifierTM V).Cfg :=
  wSeed.fixedPairEvidence.decodedCfg t ht

theorem transitionDecodedCfg_step
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ}
    (hLabel :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label =
        some l) :
    (tmVerifierTM V).step
        (wSeed.decodedCfg t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)) =
      some
        (wSeed.decodedCfg (t + 1)
          (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht)) :=
  wSeed.fixedPairEvidence.transitionDecodedCfg_step ht hLabel

theorem transitionDecodedCfg_halted
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    (hLabel :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label =
        none) :
    wSeed.decodedCfg (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht) =
      wSeed.decodedCfg t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht) :=
  wSeed.fixedPairEvidence.transitionDecodedCfg_halted ht hLabel

theorem transitionDecodedCfg_stepOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert)) :
    (tmVerifierTM V).step
        (wSeed.decodedCfg t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)) =
      Option.bind
        (wSeed.fixedPairEvidence.controlRow t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label
        (fun _ =>
          some
            (wSeed.decodedCfg (t + 1)
              (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht))) :=
  wSeed.fixedPairEvidence.transitionDecodedCfg_stepOption ht

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
