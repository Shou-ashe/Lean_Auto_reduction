/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalWindowSelection

/-!
Decoded step soundness for x-only global fixed-micro tableaux.

This file packages selected-window x-only macro-row soundness as actual adjacent
`Turing.FinTM2.step` facts for decoded x-only macro configurations.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem transitionDecodedCfg_halted
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        none) :
    E.decodedCfg (t + 1)
        (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht) =
      E.decodedCfg t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht) := by
  let ht0 := tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht
  let ht1 := tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht
  let s0 := (E.controlRow t ht0).state
  have hs0 : s0 ∈ tmVerifierStateList V := by
    classical
    simp [tmVerifierStateList]
  have hHaltedRows : CNF.Satisfies (tmVerifierXOnlyHaltedRowsCNFAt V x t) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t ++
        tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1
        (by simpa [tmVerifierXOnlyTransitionFixedRowCNFAt] using E.transitionFixedRow t ht)
    exact (CNF.satisfies_append
      (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t)
      (tmVerifierXOnlyHaltedRowsCNFAt V x t) a).1 hsplit.2 |>.2
  have hHaltedRow :
      CNF.Satisfies (tmVerifierXOnlyHaltedRowCNFAt V x t s0) a := by
    intro c hc
    exact hHaltedRows c (by
      rw [tmVerifierXOnlyHaltedRowsCNFAt]
      exact List.mem_flatMap.mpr ⟨s0, hs0, hc⟩)
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
  let antecedents := tmVerifierHaltedRowAntecedents V t s0
  have hsplit := (CNF.satisfies_append
    ([ tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none)
     , tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s0) ])
    (tmVerifierXOnlyFrameAllStacksCNFBetween V x t (t + 1) antecedents) a).1
      (by simpa [tmVerifierXOnlyHaltedRowCNFAt, antecedents] using hHaltedRow)
  have hNextControl :
      (tmVerifierLabelAtom V (t + 1) none).eval a = true ∧
        (tmVerifierStateAtom V (t + 1) s0).eval a = true := by
    constructor
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierLabelAtom V (t + 1) none) a
        (by
          intro c hc
          have hc' :
              c = tmVerifierImplicationClause antecedents
                (tmVerifierLabelAtom V (t + 1) none) := by
            simpa using hc
          subst c
          exact hsplit.1 _ (by simp))
        (by simpa [antecedents] using hAntecedents)
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierStateAtom V (t + 1) s0) a
        (by
          intro c hc
          have hc' :
              c = tmVerifierImplicationClause antecedents
                (tmVerifierStateAtom V (t + 1) s0) := by
            simpa using hc
          subst c
          exact hsplit.1 _ (by simp))
        (by simpa [antecedents] using hAntecedents)
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
      (fun k => tmVerifierXOnlyDecodedStackList V x (t + 1) k a
        (E.stackCellDomainsAt (t + 1) ht1 k)) =
        (fun k => tmVerifierXOnlyDecodedStackList V x t k a
          (E.stackCellDomainsAt t ht0 k)) := by
    funext k
    exact TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq
      (tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x t
        (t + 1) k antecedents a
        (by simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using hsplit.2)
        (E.stackCellDomainsAt t ht0 k) (E.stackCellDomainsAt (t + 1) ht1 k)
        (by
          classical
          simp [tmVerifierStackList])
        (by simpa [antecedents] using hAntecedents))
  simp [decodedCfg, s0, hLabel, hNextLabel, hNextState, hStacks]

theorem transitionDecodedCfg_step
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x)
    {l : (tmVerifierTM V).Λ}
    (hLabel :
      (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label =
        some l) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)) =
      some
        (E.decodedCfg (t + 1)
          (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht)) := by
  let ht0 := tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht
  let ht1 := tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht
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
      (fun k => tmVerifierXOnlyDecodedStackList V x t k a
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
      (fun k => tmVerifierXOnlyDecodedStackList V x (t + 1) k a
        (E.stackCellDomainsAt (t + 1) ht1 k)) = cfg.stk := by
    simpa [cfg] using hStep.2.2
  have hCfg : cfg = E.decodedCfg (t + 1) ht1 := by
    rcases cfg with ⟨cl, cv, cs⟩
    simp [TMVerifierXOnlyGlobalTableauEvidence.decodedCfg] at hNextLabel hNextState hStacks ⊢
    rw [← hNextLabel, ← hNextState, ← hStacks]
  have hInputStacks :
      (fun k => tmVerifierXOnlyDecodedStackList V x t k a (E.stackCellDomainsAt t ht0 k)) =
        (fun k => tmVerifierXOnlyDecodedStackList V x t k a
          (E.transitionStackCellDomainsAt ht k)) := by
    funext k
    exact tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs V x t k a
      (E.stackCellDomainsAt t ht0 k) (E.transitionStackCellDomainsAt ht k)
  have hStepAuxInput :
      Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
          (fun k => tmVerifierXOnlyDecodedStackList V x t k a
            (E.stackCellDomainsAt t ht0 k)) =
        cfg := by
    exact congrArg (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0) hInputStacks
  have hLeft :
      (tmVerifierTM V).step (E.decodedCfg t ht0) = some cfg := by
    have hExpand :
        (tmVerifierTM V).step (E.decodedCfg t ht0) =
          some (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
            (fun k => tmVerifierXOnlyDecodedStackList V x t k a
              (E.stackCellDomainsAt t ht0 k))) := by
      simp [TMVerifierXOnlyGlobalTableauEvidence.decodedCfg, Turing.FinTM2.step,
        Turing.TM2.step, row, l0, s0, hLabel, hState]
    exact hExpand.trans (congrArg some hStepAuxInput)
  exact hLeft.trans (congrArg some hCfg)

theorem transitionDecodedCfg_stepOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)) =
      Option.bind
        (E.controlRow t (tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht)).label
        (fun _ =>
          some
            (E.decodedCfg (t + 1)
              (tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x ht))) := by
  let ht0 := tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x ht
  cases hLabel : (E.controlRow t ht0).label with
  | none =>
      have hStepNone :
          (tmVerifierTM V).step (E.decodedCfg t ht0) = none := by
        change Turing.TM2.step (tmVerifierTM V).m
          { l := (E.controlRow t ht0).label
            var := (E.controlRow t ht0).state
            stk := fun k =>
              tmVerifierXOnlyDecodedStackList V x t k a (E.stackCellDomainsAt t ht0 k) } = none
        rw [hLabel]
        rfl
      rw [hStepNone]
      rfl
  | some l =>
      simpa [hLabel] using E.transitionDecodedCfg_step ht hLabel

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
