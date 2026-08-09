/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionBlocks

/-!
Completeness helpers for primitive stack-action CNF blocks.

`TMStackActionSemantics` proves that satisfied action clauses imply decoded stack
effects.  This file supplies the opposite low-level direction used by the
accepting-run assignment construction: if the relevant stack atoms already
propagate as a concrete action says they should, then the guarded CNF clauses
are satisfied.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Guarded implication clauses -/

theorem tmVerifierImplicationClause_satisfies_of_conclusion
    (antecedents : List Literal) (conclusion : Literal) (a : Assignment)
    (hConclusion : conclusion.eval a = true) :
    Clause.Satisfies (tmVerifierImplicationClause antecedents conclusion) a := by
  exact ⟨conclusion, by simp [tmVerifierImplicationClause], hConclusion⟩

theorem tmVerifierImplicationClause_satisfies_of_false_antecedent
    (antecedents : List Literal) (conclusion ant : Literal) (a : Assignment)
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    Clause.Satisfies (tmVerifierImplicationClause antecedents conclusion) a := by
  exact ⟨Clause.negate ant, by
    rw [tmVerifierImplicationClause]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨ant, hmem, rfl⟩)),
    (Clause.negate_eval_true_iff ant a).2 hAnt⟩

theorem tmVerifierImplicationClause_satisfies_of_last_antecedent
    (antecedents : List Literal) (trigger conclusion : Literal) (a : Assignment)
    (hTrigger : trigger.eval a = true → conclusion.eval a = true) :
    Clause.Satisfies (tmVerifierImplicationClause (antecedents ++ [trigger]) conclusion) a := by
  by_cases h : trigger.eval a = true
  · exact tmVerifierImplicationClause_satisfies_of_conclusion (antecedents ++ [trigger])
      conclusion a (hTrigger h)
  · have hFalse : trigger.eval a = false := by
      cases hEval : trigger.eval a <;> simp [hEval] at h ⊢
    exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (antecedents ++ [trigger]) conclusion trigger a (by simp) hFalse

/-! ### Frame clauses -/

theorem tmVerifierFrameChoiceCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (hEval :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierFrameChoiceCNFBetween V tin tout k cell choice antecedents) a := by
  intro c hc
  have hc' :
      c = tmVerifierFrameForwardClause V tin tout k cell choice antecedents ∨
        c = tmVerifierFrameBackwardClause V tin tout k cell choice antecedents := by
    simpa [tmVerifierFrameChoiceCNFBetween] using hc
  rcases hc' with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_last_antecedent antecedents
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice)
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) a (by
        intro hTin
        simpa [hEval] using hTin)
  · exact tmVerifierImplicationClause_satisfies_of_last_antecedent antecedents
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice)
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice) a (by
        intro hTout
        simpa [hEval] using hTout)

theorem tmVerifierFrameCellCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hEval :
      ∀ choice ∈ tmVerifierStackReadChoices V k,
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierFrameCellCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨choice, hchoice, hc⟩
  exact tmVerifierFrameChoiceCNFBetween_satisfies_of_eval_eq V tin tout k cell choice
    antecedents a (hEval choice hchoice) c hc

theorem tmVerifierFrameStackCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment)
    (hEval :
      ∀ cell ∈ tmVerifierCellRange V p,
        ∀ choice ∈ tmVerifierStackReadChoices V k,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a := by
  intro c hc
  rw [tmVerifierFrameStackCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
  exact tmVerifierFrameCellCNFBetween_satisfies_of_eval_eq V tin tout k cell antecedents a
    (fun choice hchoice => hEval cell hcell choice hchoice) c hc

theorem tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (a : Assignment)
    (hEval :
      ∀ k ∈ tmVerifierStackList V,
        ∀ cell ∈ tmVerifierCellRange V p,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierFrameAllStacksCNFBetween V p tin tout antecedents) a := by
  intro c hc
  rw [tmVerifierFrameAllStacksCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, hk, hc⟩
  exact tmVerifierFrameStackCNFBetween_satisfies_of_eval_eq V p tin tout k antecedents a
    (fun cell hcell choice hchoice => hEval k hk cell hcell choice hchoice) c hc

/-! ### Push, pop, preserve, and read clauses -/

theorem tmVerifierPushTopCNF_satisfies_of_true
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (tout : Nat) (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (hTop : (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval a = true) :
    CNF.Satisfies (tmVerifierPushTopCNF V B tout raw antecedents) a := by
  intro c hc
  have hc' : c = tmVerifierImplicationClause antecedents
      (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)) := by
    simpa [tmVerifierPushTopCNF] using hc
  subst c
  exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)) a hTop

theorem tmVerifierPushShiftCellCNF_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hShift :
      ∀ choice ∈ tmVerifierStackReadChoices V k,
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true →
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice).eval
            a = true) :
    CNF.Satisfies (tmVerifierPushShiftCellCNF V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierPushShiftCellCNF] at hc
  rcases List.mem_map.mp hc with ⟨choice, hchoice, rfl⟩
  exact tmVerifierImplicationClause_satisfies_of_last_antecedent antecedents
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice)
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice) a
    (hShift choice hchoice)

theorem tmVerifierPopShiftCellCNF_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hShift :
      ∀ choice ∈ tmVerifierStackReadChoices V k,
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval
            a = true →
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a =
            true) :
    CNF.Satisfies (tmVerifierPopShiftCellCNF V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierPopShiftCellCNF] at hc
  rcases List.mem_map.mp hc with ⟨choice, hchoice, rfl⟩
  exact tmVerifierImplicationClause_satisfies_of_last_antecedent antecedents
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice)
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) a
    (hShift choice hchoice)

theorem tmVerifierPushActionCNFBetween_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal) (a : Assignment)
    (hTop : (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval a = true)
    (hShift :
      ∀ cell ∈ tmVerifierCellRange V p,
        ∀ choice ∈ tmVerifierStackReadChoices V raw.stack,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tin cell choice).eval
              a = true →
            (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tout (cell + 1)
              choice).eval a = true)
    (hOther :
      ∀ k ∈ tmVerifierOtherStacks V raw.stack,
        ∀ cell ∈ tmVerifierCellRange V p,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a := by
  rw [tmVerifierPushActionCNFBetween, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact tmVerifierPushTopCNF_satisfies_of_true V B tout raw antecedents a hTop
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
      exact tmVerifierPushShiftCellCNF_satisfies_of_transfer V tin tout raw.stack cell
        antecedents a (fun choice hchoice => hShift cell hcell choice hchoice) c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨k, hk, hc⟩
    exact tmVerifierFrameStackCNFBetween_satisfies_of_eval_eq V p tin tout k antecedents a
      (fun cell hcell choice hchoice => hOther k hk cell hcell choice hchoice) c hc

theorem tmVerifierPopActionCNFBetween_satisfies_of_transfer
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (k : tmVerifierStackIndex V) (antecedents : List Literal) (a : Assignment)
    (hShift :
      ∀ cell ∈ tmVerifierCellRange V p,
        ∀ choice ∈ tmVerifierStackReadChoices V k,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval
              a = true →
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a =
              true)
    (hOther :
      ∀ j ∈ tmVerifierOtherStacks V k,
        ∀ cell ∈ tmVerifierCellRange V p,
          ∀ choice ∈ tmVerifierStackReadChoices V j,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval a =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a := by
  rw [tmVerifierPopActionCNFBetween, CNF.satisfies_append]
  constructor
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨cell, hcell, hc⟩
    exact tmVerifierPopShiftCellCNF_satisfies_of_transfer V tin tout k cell antecedents a
      (fun choice hchoice => hShift cell hcell choice hchoice) c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨j, hj, hc⟩
    exact tmVerifierFrameStackCNFBetween_satisfies_of_eval_eq V p tin tout j antecedents a
      (fun cell hcell choice hchoice => hOther j hj cell hcell choice hchoice) c hc

theorem tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (a : Assignment)
    (hEval :
      ∀ k ∈ tmVerifierStackList V,
        ∀ cell ∈ tmVerifierCellRange V p,
          ∀ choice ∈ tmVerifierStackReadChoices V k,
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a =
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a) :
    CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a := by
  simpa [tmVerifierPreserveAllStacksActionCNFBetween] using
    tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p tin tout antecedents a hEval

theorem tmVerifierStackActionReadCNFAt_satisfies_of_read
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (tin : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (hRead : TMVerifierStackActionReadAtomTrue tin a act) :
    CNF.Satisfies (tmVerifierStackActionReadCNFAt tin antecedents act) a := by
  cases act with
  | push raw =>
      simp [tmVerifierStackActionReadCNFAt]
  | peek k choice =>
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) := by
        simpa [tmVerifierStackActionReadCNFAt] using hc
      subst c
      exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) a
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | pop k choice =>
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) := by
        simpa [tmVerifierStackActionReadCNFAt] using hc
      subst c
      exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) a
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | load =>
      simp [tmVerifierStackActionReadCNFAt]
  | branch tag =>
      simp [tmVerifierStackActionReadCNFAt]

theorem tmVerifierStackActionCNFBetween_satisfies_of_parts
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) (a : Assignment)
    (hEffect :
      CNF.Satisfies (tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act) a)
    (hRead : TMVerifierStackActionReadAtomTrue tin a act) :
    CNF.Satisfies (tmVerifierStackActionCNFBetween V B p tin tout antecedents act) a := by
  rw [tmVerifierStackActionCNFBetween, CNF.satisfies_append]
  exact ⟨hEffect, tmVerifierStackActionReadCNFAt_satisfies_of_read tin antecedents act a hRead⟩

theorem tmVerifierWindowStackActionCNFAt_satisfies_of_actions
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) (a : Assignment)
    (hActions :
      ∀ entry ∈ w.actions.zipIdx,
        CNF.Satisfies
          (tmVerifierStackActionCNFBetween V B p
            (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
            antecedents entry.1) a) :
    CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a := by
  intro c hc
  rw [tmVerifierWindowStackActionCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨entry, hentry, hc⟩
  exact hActions entry hentry c hc

end SAT
end ComplexityReduction
