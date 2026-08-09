/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitions
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionSemantics

/-!
CNF-level semantics for primitive x-only stack-action blocks.

The clauses are the same frame/push/pop primitives as the fixed-pair tableau,
but quantified over the certificate-independent x-only cell range.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only frame propagation -/

theorem tmVerifierXOnlyFrameStackCNFBetween_satisfies_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hCell : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierXOnlyFrameStackCNFBetween]
        exact ⟨cell, hcell, hc⟩)
  exact tmVerifierFrameCellCNFBetween_satisfies_forward V tin tout k cell choice antecedents
    a hCell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyFrameStackCNFBetween_satisfies_backward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  have hCell : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierXOnlyFrameStackCNFBetween]
        exact ⟨cell, hcell, hc⟩)
  exact tmVerifierFrameCellCNFBetween_satisfies_backward V tin tout k cell choice antecedents
    a hCell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyFrameAllStacksCNFBetween V x tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hStack :
      CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyFrameAllStacksCNFBetween]
      exact ⟨k, hk, hc⟩)
  exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_forward V x tin tout k cell choice
    antecedents a hStack hcell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_backward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyFrameAllStacksCNFBetween V x tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  have hStack :
      CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout k antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyFrameAllStacksCNFBetween]
      exact ⟨k, hk, hc⟩)
  exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_backward V x tin tout k cell choice
    antecedents a hStack hcell hchoice hAntecedents hChoice

/-! ### X-only push/pop propagation -/

theorem tmVerifierXOnlyPushActionCNFBetween_satisfies_top
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval a = true := by
  have hTop : CNF.Satisfies (tmVerifierPushTopCNF V B tout raw antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyPushActionCNFBetween]
      exact Or.inl hc)
  exact tmVerifierPushTopCNF_satisfies V B tout raw antecedents a hTop hAntecedents

theorem tmVerifierXOnlyPushActionCNFBetween_satisfies_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V raw.stack) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V raw.stack)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tin cell choice).eval a =
        true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tout (cell + 1) choice).eval a =
      true := by
  have hShiftCell :
      CNF.Satisfies (tmVerifierPushShiftCellCNF V tin tout raw.stack cell antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyPushActionCNFBetween]
      exact Or.inr (Or.inl ⟨cell, hcell, hc⟩))
  exact tmVerifierPushShiftCellCNF_satisfies_choice V tin tout raw.stack cell choice
    antecedents a hShiftCell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyPushActionCNFBetween_satisfies_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V j) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V j)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval a = true := by
  have hFrameStack :
      CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout j antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyPushActionCNFBetween]
      exact Or.inr (Or.inr ⟨j, hj, hc⟩))
  exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_forward V x tin tout j cell choice
    antecedents a hFrameStack hcell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyPopActionCNFBetween_satisfies_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval a =
        true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hShiftCell :
      CNF.Satisfies (tmVerifierPopShiftCellCNF V tin tout k cell antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyPopActionCNFBetween]
      exact Or.inl ⟨cell, hcell, hc⟩)
  exact tmVerifierPopShiftCellCNF_satisfies_choice V tin tout k cell choice antecedents a
    hShiftCell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyPopActionCNFBetween_satisfies_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V j) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V j)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval a = true := by
  have hFrameStack :
      CNF.Satisfies (tmVerifierXOnlyFrameStackCNFBetween V x tin tout j antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyPopActionCNFBetween]
      exact Or.inr ⟨j, hj, hc⟩)
  exact tmVerifierXOnlyFrameStackCNFBetween_satisfies_forward V x tin tout j cell choice
    antecedents a hFrameStack hcell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
        antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true :=
  tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_forward V x tin tout k cell choice
    antecedents a (by simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using h)
    hk hcell hchoice hAntecedents hChoice

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_backward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
        antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true :=
  tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_backward V x tin tout k cell choice
    antecedents a (by simpa [tmVerifierXOnlyPreserveAllStacksActionCNFBetween] using h)
    hk hcell hchoice hAntecedents hChoice

/-! ### Primitive x-only action block projections -/

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackActionCNFBetween V B x tin tout antecedents act)
      a) :
    CNF.Satisfies (tmVerifierXOnlyStackActionEffectCNFBetween V B x tin tout antecedents act)
      a :=
  (CNF.satisfies_append
    (tmVerifierXOnlyStackActionEffectCNFBetween V B x tin tout antecedents act)
    (tmVerifierStackActionReadCNFAt tin antecedents act) a).1 h |>.1

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_read
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackActionCNFBetween V B x tin tout antecedents act)
      a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionReadAtomTrue tin a act := by
  have hRead : CNF.Satisfies (tmVerifierStackActionReadCNFAt tin antecedents act) a :=
    (CNF.satisfies_append
      (tmVerifierXOnlyStackActionEffectCNFBetween V B x tin tout antecedents act)
      (tmVerifierStackActionReadCNFAt tin antecedents act) a).1 h |>.2
  exact tmVerifierStackActionReadCNFAt_satisfies tin antecedents act a hRead hAntecedents

end SAT
end ComplexityReduction
