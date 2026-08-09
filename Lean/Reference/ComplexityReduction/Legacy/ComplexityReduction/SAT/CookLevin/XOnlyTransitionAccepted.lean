/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTableauAccepted

/-!
Accepted-run satisfaction for x-only global transition rows.

This file contains the transition-row part of the x-only accepted-run
completeness proof.  It is split from `XOnlyTableauAccepted` so both files stay
below the local 1000-line limit.
-/

namespace ComplexityReduction
namespace SAT

/-! ### False-antecedent helpers for x-only transition rows -/

theorem tmVerifierXOnlyWindowFixedAntecedents_fixedGuard_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) {g : Literal}
    (hg : g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w) :
    g ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w := by
  rw [tmVerifierXOnlyWindowFixedAntecedents]
  exact List.mem_append.mpr (Or.inr hg)

theorem tmVerifierXOnlyWindowFixedControlCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w) a := by
  intro c hc
  have hc' :
      c =
          tmVerifierImplicationClause (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) ∨
        c =
          tmVerifierImplicationClause (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
    simpa [tmVerifierXOnlyWindowFixedControlCNFAt] using hc
  rcases hc' with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
      (tmVerifierLabelAtom V (t + 1) w.nextLabel) ant a hmem hAnt
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
      (tmVerifierStateAtom V (t + 1) w.nextState) ant a hmem hAnt

theorem tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (tin tout : Nat) (k : tmVerifierStackIndex V)
    (antecedents : List Literal) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents) a := by
  intro c hc
  rw [tmVerifierXOnlyFrameStackCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierFrameCellCNFBetween_satisfies_of_false_antecedent V tin tout k cell
    antecedents a hmem hAnt c hc

theorem tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (tin tout : Nat) (antecedents : List Literal)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyFrameAllStacksCNFBetween V x tin tout antecedents) a := by
  intro c hc
  rw [tmVerifierXOnlyFrameAllStacksCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_false_antecedent V x tin tout k
    antecedents a hmem hAnt c hc

theorem tmVerifierXOnlyPushActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal} (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a := by
  rw [tmVerifierXOnlyPushActionCNFBetween, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact tmVerifierPushTopCNF_satisfies_of_false_antecedent V B tout raw
        antecedents a hmem hAnt
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
      exact tmVerifierPushShiftCellCNF_satisfies_of_false_antecedent V tin tout
        raw.stack cell antecedents a hmem hAnt c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
    exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_false_antecedent V x tin tout k
      antecedents a hmem hAnt c hc

theorem tmVerifierXOnlyPopActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (k : tmVerifierStackIndex V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal} (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents) a := by
  rw [tmVerifierXOnlyPopActionCNFBetween, CNF.satisfies_append]
  constructor
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
    exact tmVerifierPopShiftCellCNF_satisfies_of_false_antecedent V tin tout k cell
      antecedents a hmem hAnt c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨j, _hj, hc⟩
    exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_false_antecedent V x tin tout j
      antecedents a hmem hAnt c hc

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (tin tout : Nat) (antecedents : List Literal)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
      antecedents) a := by
  simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using
    tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent V x tin tout
      antecedents a hmem hAnt

theorem tmVerifierXOnlyStackActionEffectCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) (a : Assignment)
    {ant : Literal} (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyStackActionEffectCNFBetween V B x tin tout antecedents act)
      a := by
  cases act with
  | push raw =>
      exact tmVerifierXOnlyPushActionCNFBetween_satisfies_of_false_antecedent V B x tin tout
        raw antecedents a hmem hAnt
  | pop k choice =>
      exact tmVerifierXOnlyPopActionCNFBetween_satisfies_of_false_antecedent V x tin tout k
        antecedents a hmem hAnt
  | peek k choice =>
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V x
        tin tout antecedents a hmem hAnt
  | load =>
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V x
        tin tout antecedents a hmem hAnt
  | branch tag =>
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V x
        tin tout antecedents a hmem hAnt

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) (a : Assignment)
    {ant : Literal} (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyStackActionCNFBetween V B x tin tout antecedents act) a := by
  rw [tmVerifierXOnlyStackActionCNFBetween, CNF.satisfies_append]
  exact ⟨tmVerifierXOnlyStackActionEffectCNFBetween_satisfies_of_false_antecedent V B x tin
      tout antecedents act a hmem hAnt,
    tmVerifierStackActionReadCNFAt_satisfies_of_false_antecedent tin antecedents act a
      hmem hAnt⟩

theorem tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal} (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w antecedents) a := by
  intro c hc
  rw [tmVerifierXOnlyWindowFixedStackActionCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨entry, _hentry, hc⟩
  exact tmVerifierXOnlyStackActionCNFBetween_satisfies_of_false_antecedent V B x
    (tmVerifierXOnlyFixedMicroTime V x t entry.2)
    (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1))
    antecedents entry.1 a hmem hAnt c hc

theorem tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w) a := by
  rw [tmVerifierXOnlyWindowFixedStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent V x t
      (tmVerifierXOnlyFixedMicroTime V x t 0)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hmem hAnt
  · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent V x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hmem hAnt

theorem tmVerifierXOnlyWindowFixedStackCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierXOnlyWindowFixedAntecedents V x t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies
      (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w ++
        tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s w)) a := by
  rw [CNF.satisfies_append]
  exact ⟨tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_of_false_antecedent V x t
      l s w a hmem hAnt,
    tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_of_false_antecedent V B x t w
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hmem hAnt⟩

/-! ### Selected x-only window satisfaction for accepted runs -/

theorem tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (tin tout : Nat) (antecedents : List Literal)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hEval :
      ∀ k ∈ tmVerifierStackList V,
        ∀ cell ∈ tmVerifierXOnlyCellRange V x,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt) =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyFrameAllStacksCNFBetween V x tin tout antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierXOnlyFrameAllStacksCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, hk, hc⟩
  rw [tmVerifierXOnlyFrameStackCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
  exact tmVerifierFrameCellCNFBetween_satisfies_of_eval_eq V tin tout k cell
    antecedents (tmVerifierStackFamilyAssignment V p stkAt)
    (fun choice hchoice => hEval k hk cell hcell choice hchoice) c hc

theorem tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (tin tout : Nat) (k : tmVerifierStackIndex V)
    (antecedents : List Literal)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hEval :
      ∀ cell ∈ tmVerifierXOnlyCellRange V x,
        ∀ choice ∈ tmVerifierStackReadChoices V k,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval
              (tmVerifierStackFamilyAssignment V p stkAt) =
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
              (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierXOnlyFrameStackCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
  exact tmVerifierFrameCellCNFBetween_satisfies_of_eval_eq V tin tout k cell
    antecedents (tmVerifierStackFamilyAssignment V p stkAt)
    (fun choice hchoice => hEval cell hcell choice hchoice) c hc

theorem tmVerifierXOnlyPushActionCNFBetween_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hTop :
      (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval
          (tmVerifierStackFamilyAssignment V p stkAt) = true)
    (hShift :
      ∀ cell ∈ tmVerifierXOnlyCellRange V x,
        ∀ choice ∈ tmVerifierStackReadChoices V raw.stack,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tin cell choice).eval
              (tmVerifierStackFamilyAssignment V p stkAt) = true →
            (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tout (cell + 1)
              choice).eval (tmVerifierStackFamilyAssignment V p stkAt) = true)
    (hOther :
      ∀ k ∈ tmVerifierOtherStacks V raw.stack,
        ∀ cell ∈ tmVerifierXOnlyCellRange V x,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt) =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierXOnlyPushActionCNFBetween, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact tmVerifierPushTopCNF_satisfies_of_true V B tout raw antecedents
        (tmVerifierStackFamilyAssignment V p stkAt) hTop
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
      exact tmVerifierPushShiftCellCNF_satisfies_of_transfer V tin tout raw.stack cell
        antecedents (tmVerifierStackFamilyAssignment V p stkAt)
        (fun choice hchoice => hShift cell hcell choice hchoice) c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨k, hk, hc⟩
    exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_eval_eq V p x tin tout k
      antecedents stkAt (fun cell hcell choice hchoice => hOther k hk cell hcell choice hchoice)
      c hc

theorem tmVerifierXOnlyPopActionCNFBetween_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hShift :
      ∀ cell ∈ tmVerifierXOnlyCellRange V x,
        ∀ choice ∈ tmVerifierStackReadChoices V k,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval
              (tmVerifierStackFamilyAssignment V p stkAt) = true →
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
              (tmVerifierStackFamilyAssignment V p stkAt) = true)
    (hOther :
      ∀ j ∈ tmVerifierOtherStacks V k,
        ∀ cell ∈ tmVerifierXOnlyCellRange V x,
          ∀ choice ∈ tmVerifierStackReadChoices V j,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt) =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierXOnlyPopActionCNFBetween, CNF.satisfies_append]
  constructor
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
    exact tmVerifierPopShiftCellCNF_satisfies_of_transfer V tin tout k cell antecedents
      (tmVerifierStackFamilyAssignment V p stkAt)
      (fun choice hchoice => hShift cell hcell choice hchoice) c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨j, hj, hc⟩
    exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_of_eval_eq V p x tin tout j
      antecedents stkAt (fun cell hcell choice hchoice => hOther j hj cell hcell choice hchoice)
      c hc

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (tin tout : Nat) (antecedents : List Literal)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hEval :
      ∀ k ∈ tmVerifierStackList V,
        ∀ cell ∈ tmVerifierXOnlyCellRange V x,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt) =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
                (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using
    tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_eval_eq V p x tin tout antecedents
      stkAt hEval

theorem tmVerifierXOnlyStackActionEffectCNFBetween_satisfies_active_applyStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V) :
    stkAt tout = tmVerifierStackActionApplyStacks act (stkAt tin) →
    CNF.Satisfies
      (tmVerifierXOnlyStackActionEffectCNFBetween V (tmVerifierActivePushPayloadBoundary V)
        x tin tout antecedents act)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro hApply
  cases act with
  | push raw =>
      have hStack :
          stkAt tout raw.stack = raw.symbol :: stkAt tin raw.stack := by
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          congrFun hApply raw.stack
      apply tmVerifierXOnlyPushActionCNFBetween_satisfies_of_transfer
      · have hcell : 0 < (stkAt tout raw.stack).length := by
          simp [hStack]
        have htop : ((stkAt tout raw.stack)[0]'hcell) = raw.symbol := by
          simp [hStack]
        simpa [tmVerifierActivePushPayloadBoundary] using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            tout raw.stack hcell (by simp [htop])
      · intro cell _hcell choice _hchoice hTrue
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_push_shift V p
          stkAt tin tout raw cell choice hStack hTrue
      · intro k hk cell _hcell choice _hchoice
        have hne : k ≠ raw.stack := by
          classical
          simpa [tmVerifierOtherStacks] using hk
        have hStackOther : stkAt tout k = stkAt tin k := by
          simpa [tmVerifierStackActionApplyStacks, Function.update, hne] using
            congrFun hApply k
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt tin tout k cell choice hStackOther
  | pop k choice =>
      have hStack : stkAt tout k = (stkAt tin k).tail := by
        simpa [tmVerifierStackActionApplyStacks, Function.update] using congrFun hApply k
      apply tmVerifierXOnlyPopActionCNFBetween_satisfies_of_transfer
      · intro cell _hcell choice _hchoice hTrue
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_pop_shift V p
          stkAt tin tout k cell choice hStack hTrue
      · intro j hj cell _hcell choice _hchoice
        have hne : j ≠ k := by
          classical
          simpa [tmVerifierOtherStacks] using hj
        have hStackOther : stkAt tout j = stkAt tin j := by
          simpa [tmVerifierStackActionApplyStacks, Function.update, hne] using
            congrFun hApply j
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt tin tout j cell choice hStackOther
  | peek k choice =>
      apply tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack
  | load =>
      apply tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack
  | branch tag =>
      apply tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_active_applyStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (hApply : stkAt tout = tmVerifierStackActionApplyStacks act (stkAt tin))
    (hRead :
      TMVerifierStackActionReadAtomTrue tin
        (tmVerifierStackFamilyAssignment V p stkAt) act) :
    CNF.Satisfies
      (tmVerifierXOnlyStackActionCNFBetween V (tmVerifierActivePushPayloadBoundary V)
        x tin tout antecedents act)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierXOnlyStackActionCNFBetween, CNF.satisfies_append]
  exact ⟨tmVerifierXOnlyStackActionEffectCNFBetween_satisfies_active_applyStacks V p x
      stkAt tin tout antecedents act hApply,
    tmVerifierStackActionReadCNFAt_satisfies_of_read tin antecedents act
      (tmVerifierStackFamilyAssignment V p stkAt) hRead⟩

theorem tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        stkAt (tmVerifierXOnlyFixedMicroTime V x t 0) k = stkAt t k)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        stkAt (t + 1) k =
          stkAt (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k) :
    CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierXOnlyWindowFixedStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_eval_eq V p x t
      (tmVerifierXOnlyFixedMicroTime V x t 0)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) stkAt (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt t (tmVerifierXOnlyFixedMicroTime V x t 0) k cell choice
          (hStart k))
  · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_eval_eq V p x
      (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1)
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) stkAt (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) (t + 1) k
          cell choice (hFinal k))

theorem TMVerifierStackActionReadAtomTrue.of_xOnlyFixedReadGuardAt_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {t actionIdx : Nat}
    {act : TMVerifierStackAction V} {a : Assignment}
    (hGuards : ∀ g ∈ act.xOnlyFixedReadGuardAt x t actionIdx, g.eval a = true) :
    TMVerifierStackActionReadAtomTrue (tmVerifierXOnlyFixedMicroTime V x t actionIdx) a act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionReadAtomTrue]
  | peek k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.xOnlyFixedReadGuardAt])
  | pop k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.xOnlyFixedReadGuardAt])
  | load =>
      simp [TMVerifierStackActionReadAtomTrue]
  | branch tag =>
      simp [TMVerifierStackActionReadAtomTrue]

theorem tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (x : L.Instance.Carrier) (t : Nat) (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (antecedents : List Literal)
    (hStack :
      ∀ micro : Nat,
        stkAt (tmVerifierXOnlyFixedMicroTime V x t micro) =
          tmVerifierWindowMicroStacks V p t w micro)
    (hGuards :
      ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w,
        g.eval (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    CNF.Satisfies
      (tmVerifierXOnlyWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        x t w antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierXOnlyWindowFixedStackActionCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨entry, hentry, hc⟩
  have hApplyBase :=
    tmVerifierWindowMicroStacks_apply_succ_of_zipIdx_mem V p t w entry hentry
  have hApply :
      stkAt (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) =
        tmVerifierStackActionApplyStacks entry.1
          (stkAt (tmVerifierXOnlyFixedMicroTime V x t entry.2)) := by
    rw [hStack (entry.2 + 1), hStack entry.2]
    exact hApplyBase
  have hAction :=
    tmVerifierXOnlyStackActionCNFBetween_satisfies_active_applyStacks V p x stkAt
      (tmVerifierXOnlyFixedMicroTime V x t entry.2)
      (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1))
      antecedents entry.1 hApply
      (TMVerifierStackActionReadAtomTrue.of_xOnlyFixedReadGuardAt_true (by
        intro g hg
        exact hGuards g (by
          rw [tmVerifierXOnlyWindowFixedActionReadGuards,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom]
          exact List.mem_flatMap.mpr ⟨entry, hentry, hg⟩)))
  exact hAction c hc

theorem tmVerifierRunSelectedWindow_xOnlyFixedGuards_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    {t : Nat} (_ht : t < tmVerifierTimeBound V (x, c))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s) :
    ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t
        (tmVerifierRunSelectedWindow V (x, c) t),
      g.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = true := by
  classical
  have hspec :=
    Classical.choose_spec
      (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V (x, c) t l
        (tmVerifierRunCfgAt V (x, c) t).var)
  have hguardsMicro := hspec.2.1
  intro g hg
  rw [tmVerifierXOnlyWindowFixedActionReadGuards,
    tmVerifierXOnlyWindowFixedActionReadGuardsFrom] at hg
  rcases List.mem_flatMap.mp hg with ⟨entry, hentry, hg⟩
  rcases entry with ⟨act, idx⟩
  cases act with
  | push raw =>
      simp [TMVerifierStackAction.xOnlyFixedReadGuardAt] at hg
  | peek k choice =>
      have hg' :
          g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice := by
        simpa [TMVerifierStackAction.xOnlyFixedReadGuardAt] using hg
      subst g
      let w := tmVerifierRunSelectedWindow V (x, c) t
      let localStacks := fun u => tmVerifierWindowMicroStacks V (x, c) t w ((Nat.unpair u).2)
      have hLocalGuard :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice).eval
            (tmVerifierStackFamilyAssignment V (x, c) localStacks) = true := by
        have hmem :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t w := by
          rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
          exact List.mem_flatMap.mpr ⟨(TMVerifierStackAction.peek k choice, idx),
            hentry, by simp [TMVerifierStackAction.readGuardAt]⟩
        have hmemChoose :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t
                (Classical.choose
                  (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V (x, c) t l
                    (tmVerifierRunCfgAt V (x, c) t).var)) := by
          simpa [w, tmVerifierRunSelectedWindow, hl] using hmem
        simpa [tmVerifierRunSelectedWindow, hl, hs, w, localStacks,
          tmVerifierWindowMicroStackFamilyAssignment] using hguardsMicro _ hmemChoose
      have hStack :
          localStacks (tmVerifierMicroTime t idx) k =
            tmVerifierXOnlyAcceptedRunGlobalStacks V x c
              (tmVerifierXOnlyFixedMicroTime V x t idx) k := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
        simp [localStacks, w]
      have hEvalEq :=
        TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
          V (x, c) localStacks (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (tmVerifierMicroTime t idx) (tmVerifierXOnlyFixedMicroTime V x t idx) k 0 choice
          hStack
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using hEvalEq.symm.trans hLocalGuard
  | pop k choice =>
      have hg' :
          g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice := by
        simpa [TMVerifierStackAction.xOnlyFixedReadGuardAt] using hg
      subst g
      let w := tmVerifierRunSelectedWindow V (x, c) t
      let localStacks := fun u => tmVerifierWindowMicroStacks V (x, c) t w ((Nat.unpair u).2)
      have hLocalGuard :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice).eval
            (tmVerifierStackFamilyAssignment V (x, c) localStacks) = true := by
        have hmem :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t w := by
          rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
          exact List.mem_flatMap.mpr ⟨(TMVerifierStackAction.pop k choice, idx),
            hentry, by simp [TMVerifierStackAction.readGuardAt]⟩
        have hmemChoose :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t
                (Classical.choose
                  (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V (x, c) t l
                    (tmVerifierRunCfgAt V (x, c) t).var)) := by
          simpa [w, tmVerifierRunSelectedWindow, hl] using hmem
        simpa [tmVerifierRunSelectedWindow, hl, hs, w, localStacks,
          tmVerifierWindowMicroStackFamilyAssignment] using hguardsMicro _ hmemChoose
      have hStack :
          localStacks (tmVerifierMicroTime t idx) k =
            tmVerifierXOnlyAcceptedRunGlobalStacks V x c
              (tmVerifierXOnlyFixedMicroTime V x t idx) k := by
        rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro]
        simp [localStacks, w]
      have hEvalEq :=
        TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
          V (x, c) localStacks (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (tmVerifierMicroTime t idx) (tmVerifierXOnlyFixedMicroTime V x t idx) k 0 choice
          hStack
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using hEvalEq.symm.trans hLocalGuard
  | load =>
      simp [TMVerifierStackAction.xOnlyFixedReadGuardAt] at hg
  | branch tag =>
      simp [TMVerifierStackAction.xOnlyFixedReadGuardAt] at hg

end SAT
end ComplexityReduction
