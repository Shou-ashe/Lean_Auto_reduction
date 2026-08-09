/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackDomainBlocks

/-!
CNF-level semantics for primitive stack-action blocks.

The previous slices introduced the stack-action clauses and the per-cell
domain/empty-tail surface.  This file proves the first semantic layer above the
raw CNF blocks: under true window antecedents, satisfied frame/push/pop clauses
propagate the corresponding stack-cell atoms to the next micro-row.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Single-clause propagation lemmas -/

theorem tmVerifierFrameBackwardClause_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment) :
    CNF.Satisfies [tmVerifierFrameBackwardClause V tin tout k cell choice antecedents] a →
      (∀ l ∈ antecedents, l.eval a = true) →
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true →
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  intro h hAntecedents hChoice
  exact tmVerifierImplicationClause_satisfies_of_antecedents
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice) a h (by
      intro l hl
      rcases List.mem_append.mp hl with hlAnt | hlChoice
      · exact hAntecedents l hlAnt
      · have hEq :
            l = TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice := by
          simpa using hlChoice
        simpa [hEq] using hChoice)

theorem tmVerifierPushShiftClause_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment) :
    CNF.Satisfies [tmVerifierPushShiftClause V tin tout k cell choice antecedents] a →
      (∀ l ∈ antecedents, l.eval a = true) →
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true →
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice).eval a =
          true := by
  intro h hAntecedents hChoice
  exact tmVerifierImplicationClause_satisfies_of_antecedents
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice) a h (by
      intro l hl
      rcases List.mem_append.mp hl with hlAnt | hlChoice
      · exact hAntecedents l hlAnt
      · have hEq :
            l = TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice := by
          simpa using hlChoice
        simpa [hEq] using hChoice)

theorem tmVerifierPopShiftClause_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment) :
    CNF.Satisfies [tmVerifierPopShiftClause V tin tout k cell choice antecedents] a →
      (∀ l ∈ antecedents, l.eval a = true) →
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval a =
        true →
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  intro h hAntecedents hChoice
  exact tmVerifierImplicationClause_satisfies_of_antecedents
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) a h (by
      intro l hl
      rcases List.mem_append.mp hl with hlAnt | hlChoice
      · exact hAntecedents l hlAnt
      · have hEq :
            l = TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice := by
          simpa using hlChoice
        simpa [hEq] using hChoice)

theorem tmVerifierPushTopCNF_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (tout : Nat) (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment) :
    CNF.Satisfies (tmVerifierPushTopCNF V B tout raw antecedents) a →
      (∀ l ∈ antecedents, l.eval a = true) →
        (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval a = true := by
  intro h hAntecedents
  exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)) a
    (by simpa [tmVerifierPushTopCNF] using h) hAntecedents

/-! ### Cell and stack block propagation lemmas -/

theorem tmVerifierPushShiftCellCNF_satisfies_choice {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushShiftCellCNF V tin tout k cell antecedents) a)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice).eval a =
      true := by
  have hClause : CNF.Satisfies [tmVerifierPushShiftClause V tin tout k cell choice antecedents] a :=
    by
      intro c hc
      have hc' : c = tmVerifierPushShiftClause V tin tout k cell choice antecedents := by
        simpa using hc
      subst c
      exact h _ (by
        simp [tmVerifierPushShiftCellCNF]
        exact ⟨choice, hchoice, rfl⟩)
  exact tmVerifierPushShiftClause_satisfies V tin tout k cell choice antecedents a hClause
    hAntecedents hChoice

theorem tmVerifierPopShiftCellCNF_satisfies_choice {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPopShiftCellCNF V tin tout k cell antecedents) a)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval a =
        true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hClause : CNF.Satisfies [tmVerifierPopShiftClause V tin tout k cell choice antecedents] a :=
    by
      intro c hc
      have hc' : c = tmVerifierPopShiftClause V tin tout k cell choice antecedents := by
        simpa using hc
      subst c
      exact h _ (by
        simp [tmVerifierPopShiftCellCNF]
        exact ⟨choice, hchoice, rfl⟩)
  exact tmVerifierPopShiftClause_satisfies V tin tout k cell choice antecedents a hClause
    hAntecedents hChoice

theorem tmVerifierFrameCellCNFBetween_satisfies_forward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hClause : CNF.Satisfies [tmVerifierFrameForwardClause V tin tout k cell choice antecedents] a :=
    by
      intro c hc
      have hc' : c = tmVerifierFrameForwardClause V tin tout k cell choice antecedents := by
        simpa using hc
      subst c
      exact h _ (by
        simp [tmVerifierFrameCellCNFBetween, tmVerifierFrameChoiceCNFBetween]
        exact ⟨choice, hchoice, Or.inl rfl⟩)
  exact tmVerifierFrameForwardClause_satisfies V tin tout k cell choice antecedents a hClause
    hAntecedents hChoice

theorem tmVerifierFrameCellCNFBetween_satisfies_backward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  have hClause :
      CNF.Satisfies [tmVerifierFrameBackwardClause V tin tout k cell choice antecedents] a := by
    intro c hc
    have hc' : c = tmVerifierFrameBackwardClause V tin tout k cell choice antecedents := by
      simpa using hc
    subst c
    exact h _ (by
      simp [tmVerifierFrameCellCNFBetween, tmVerifierFrameChoiceCNFBetween]
      exact ⟨choice, hchoice, Or.inr rfl⟩)
  exact tmVerifierFrameBackwardClause_satisfies V tin tout k cell choice antecedents a hClause
    hAntecedents hChoice

theorem tmVerifierFrameStackCNFBetween_satisfies_forward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hCell : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierFrameStackCNFBetween]
        exact ⟨cell, hcell, hc⟩)
  exact tmVerifierFrameCellCNFBetween_satisfies_forward V tin tout k cell choice antecedents a
    hCell hchoice hAntecedents hChoice

theorem tmVerifierFrameStackCNFBetween_satisfies_backward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  have hCell : CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierFrameStackCNFBetween]
        exact ⟨cell, hcell, hc⟩)
  exact tmVerifierFrameCellCNFBetween_satisfies_backward V tin tout k cell choice antecedents a
    hCell hchoice hAntecedents hChoice

theorem tmVerifierFrameAllStacksCNFBetween_satisfies_forward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameAllStacksCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hStack : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierFrameAllStacksCNFBetween]
        exact ⟨k, hk, hc⟩)
  exact tmVerifierFrameStackCNFBetween_satisfies_forward V p tin tout k cell choice antecedents a
    hStack hcell hchoice hAntecedents hChoice

theorem tmVerifierFrameAllStacksCNFBetween_satisfies_backward {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierFrameAllStacksCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  have hStack : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierFrameAllStacksCNFBetween]
        exact ⟨k, hk, hc⟩)
  exact tmVerifierFrameStackCNFBetween_satisfies_backward V p tin tout k cell choice antecedents a
    hStack hcell hchoice hAntecedents hChoice

/-! ### Primitive action block propagation lemmas -/

theorem tmVerifierPushActionCNFBetween_satisfies_top {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)).eval a = true := by
  have hTop : CNF.Satisfies (tmVerifierPushTopCNF V B tout raw antecedents) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierPushActionCNFBetween]
      exact Or.inl hc)
  exact tmVerifierPushTopCNF_satisfies V B tout raw antecedents a hTop hAntecedents

theorem tmVerifierPushActionCNFBetween_satisfies_shift {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V raw.stack) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
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
      simp [tmVerifierPushActionCNFBetween]
      exact Or.inr (Or.inl ⟨cell, hcell, hc⟩))
  exact tmVerifierPushShiftCellCNF_satisfies_choice V tin tout raw.stack cell choice antecedents a
    hShiftCell hchoice hAntecedents hChoice

theorem tmVerifierPushActionCNFBetween_satisfies_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V j) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V j)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval a = true := by
  have hFrameStack : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout j antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierPushActionCNFBetween]
        exact Or.inr (Or.inr ⟨j, hj, hc⟩))
  exact tmVerifierFrameStackCNFBetween_satisfies_forward V p tin tout j cell choice antecedents a
    hFrameStack hcell hchoice hAntecedents hChoice

theorem tmVerifierPopActionCNFBetween_satisfies_shift {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval a =
        true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  have hShiftCell : CNF.Satisfies (tmVerifierPopShiftCellCNF V tin tout k cell antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierPopActionCNFBetween]
        exact Or.inl ⟨cell, hcell, hc⟩)
  exact tmVerifierPopShiftCellCNF_satisfies_choice V tin tout k cell choice antecedents a
    hShiftCell hchoice hAntecedents hChoice

theorem tmVerifierPopActionCNFBetween_satisfies_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V j) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V j)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := j) tout cell choice).eval a = true := by
  have hFrameStack : CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout j antecedents) a :=
    by
      intro c hc
      exact h c (by
        simp [tmVerifierPopActionCNFBetween]
        exact Or.inr ⟨j, hj, hc⟩)
  exact tmVerifierFrameStackCNFBetween_satisfies_forward V p tin tout j cell choice antecedents a
    hFrameStack hcell hchoice hAntecedents hChoice

theorem tmVerifierPreserveAllStacksActionCNFBetween_satisfies_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  exact tmVerifierFrameAllStacksCNFBetween_satisfies_forward V p tin tout k cell choice
    antecedents a (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using h)
    hk hcell hchoice hAntecedents hChoice

theorem tmVerifierPreserveAllStacksActionCNFBetween_satisfies_backward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hchoice : choice ∈ tmVerifierStackReadChoices V k)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hChoice :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true := by
  exact tmVerifierFrameAllStacksCNFBetween_satisfies_backward V p tin tout k cell choice
    antecedents a (by simpa [tmVerifierPreserveAllStacksActionCNFBetween] using h)
    hk hcell hchoice hAntecedents hChoice

end SAT
end ComplexityReduction
