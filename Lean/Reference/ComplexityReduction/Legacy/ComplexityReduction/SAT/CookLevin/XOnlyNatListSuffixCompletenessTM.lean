/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyNatListCheckedSuffixDecoderTM

/-!
Completeness lemmas for the unary natural-list suffix-pattern CNF.

The checked decoder file proves that the CNF forces a nat-list decoder image.
This file proves the converse local facts needed to show that a genuine
`EncodedType.list EncodedType.nat` certificate suffix satisfies the pattern.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem natListMainCellCNFAt_satisfies_of_empty_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hEmpty :
      (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListMainCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · rw [tmVerifierNatListInvalidSymbolChoiceClausesAt, tmVerifierUnitClauses_satisfies]
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨choice, hInvalid, rfl⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice).eval a = true
      · have hInvalidSpec :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
              choice ≠ TMVerifierStackReadChoice.empty ∧
                choice ∉ tmVerifierCertificateRightReadChoices V trueSymbol ∧
                  choice ∉ tmVerifierCertificateRightReadChoices V falseSymbol ∧
                    choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          simpa [tmVerifierNatListInvalidSymbolChoices] using hInvalid
        have hEq :
            choice =
              (TMVerifierStackReadChoice.empty :
                TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell choice TMVerifierStackReadChoice.empty hInvalidSpec.1
            (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
            (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
        exact False.elim (hInvalidSpec.2.1 hEq)
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice).eval a <;> simp [hEval] at hAtom ⊢
    · rw [tmVerifierNatListTrueContinuationClausesAt]
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨choice, hChoice, rfl⟩
      refine ⟨Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice), by simp, ?_⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice).eval a = true
      · have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V trueSymbol hChoice).1
        have hEq :
            choice =
              (TMVerifierStackReadChoice.empty :
                TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell choice TMVerifierStackReadChoice.empty hChoiceMem
            (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
            (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
        exact False.elim (tmVerifierCertificateRightReadChoices_ne_empty hChoice hEq)
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice).eval a <;> simp [hEval] at hAtom ⊢
  · rw [tmVerifierNatListFalseDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨choice, hChoice, rfl⟩
    refine ⟨Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice), by simp, ?_⟩
    apply (Clause.negate_eval_true_iff _ a).2
    by_cases hAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a = true
    · have hChoiceMem :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        (tmVerifierCertificateRightReadChoices_spec V falseSymbol hChoice).1
      have hEq :
          choice =
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell choice TMVerifierStackReadChoice.empty hChoiceMem
          (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
          (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
      exact False.elim (tmVerifierCertificateRightReadChoices_ne_empty hChoice hEq)
    · cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a <;> simp [hEval] at hAtom ⊢

theorem natListDelimiterPreviousClausesAt_satisfies_of_empty_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hEmpty :
      (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListDelimiterPreviousClausesAt]
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨choice, hChoice, rfl⟩
  refine ⟨Clause.negate
    (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell choice), by simp, ?_⟩
  apply (Clause.negate_eval_true_iff _ a).2
  by_cases hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true
  · have hChoiceMem :
        choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
      (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hChoice).1
    have hEq :
        choice =
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ cell a
        (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
          (tmVerifierTM V).k₀)
        hCell choice TMVerifierStackReadChoice.empty hChoiceMem
        (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
        (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
    exact False.elim (tmVerifierCertificateRightReadChoices_ne_empty hChoice hEq)
  · cases hEval :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a <;> simp [hEval] at hAtom ⊢

theorem natListStartDelimiterClausesAt_satisfies_of_not_delimiter_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoiceMem : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hNotDelimiter : choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    CNF.Satisfies (tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListStartDelimiterClausesAt, tmVerifierUnitClauses_satisfies]
  intro lit hlit
  rcases List.mem_map.mp hlit with ⟨delimiterChoice, hDelimiterChoice, rfl⟩
  apply (Clause.negate_eval_true_iff _ a).2
  by_cases hDelimiterAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a = true
  · have hDelimiterMem :
        delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
      (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
    have hEq : delimiterChoice = choice := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ cell a
        (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
          (tmVerifierTM V).k₀)
        hCell delimiterChoice choice hDelimiterMem hChoiceMem hDelimiterAtom hAtom
    exact False.elim (hNotDelimiter (by simpa [hEq] using hDelimiterChoice))
  · cases hEval :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a <;> simp [hEval] at hDelimiterAtom ⊢

theorem natListDelimiterPreviousClausesAt_satisfies_of_not_delimiter_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoiceMem : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hNotDelimiter : choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListDelimiterPreviousClausesAt]
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨delimiterChoice, hDelimiterChoice, rfl⟩
  refine ⟨Clause.negate
    (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell delimiterChoice), by simp, ?_⟩
  apply (Clause.negate_eval_true_iff _ a).2
  by_cases hDelimiterAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a = true
  · have hDelimiterMem :
        delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
      (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
    have hEq : delimiterChoice = choice := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ cell a
        (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
          (tmVerifierTM V).k₀)
        hCell delimiterChoice choice hDelimiterMem hChoiceMem hDelimiterAtom hAtom
    exact False.elim (hNotDelimiter (by simpa [hEq] using hDelimiterChoice))
  · cases hEval :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a <;> simp [hEval] at hDelimiterAtom ⊢

theorem natListDelimiterPreviousClausesAt_satisfies_of_previous_false_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (_E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    {falseChoice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hFalseChoice : falseChoice ∈ tmVerifierCertificateRightReadChoices V falseSymbol)
    (hFalseAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell - 1) falseChoice).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListDelimiterPreviousClausesAt]
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨delimiterChoice, _hDelimiterChoice, rfl⟩
  by_cases hDelimiterAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a = true
  · refine ⟨
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell - 1) falseChoice, ?_, hFalseAtom⟩
    exact List.mem_append_right _
      (List.mem_map.mpr ⟨falseChoice, hFalseChoice, rfl⟩)
  · refine ⟨Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice), by simp, ?_⟩
    apply (Clause.negate_eval_true_iff _ a).2
    cases hEval :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell delimiterChoice).eval a <;> simp [hEval] at hDelimiterAtom ⊢

theorem natListMainCellCNFAt_satisfies_of_true_next_atoms
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {choice nextChoice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true)
    (hNextChoice :
      nextChoice ∈
        tmVerifierCertificateRightReadChoices V trueSymbol ++
          tmVerifierCertificateRightReadChoices V falseSymbol)
    (hNextAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) nextChoice).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListMainCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · rw [tmVerifierNatListInvalidSymbolChoiceClausesAt, tmVerifierUnitClauses_satisfies]
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨badChoice, hInvalid, rfl⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hBadAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a = true
      · have hInvalidSpec :
            badChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
              badChoice ≠ TMVerifierStackReadChoice.empty ∧
                badChoice ∉ tmVerifierCertificateRightReadChoices V trueSymbol ∧
                  badChoice ∉ tmVerifierCertificateRightReadChoices V falseSymbol ∧
                    badChoice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          simpa [tmVerifierNatListInvalidSymbolChoices] using hInvalid
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V trueSymbol hChoice).1
        have hEq : badChoice = choice := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell badChoice choice hInvalidSpec.1 hChoiceMem hBadAtom hAtom
        exact False.elim (hInvalidSpec.2.2.1 (by simpa [hEq] using hChoice))
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a <;> simp [hEval] at hBadAtom ⊢
    · rw [tmVerifierNatListTrueContinuationClausesAt]
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨headChoice, hHeadChoice, rfl⟩
      by_cases hHeadAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell headChoice).eval a = true
      · refine ⟨
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 (cell + 1) nextChoice, ?_, hNextAtom⟩
        exact List.mem_append_right _
          (List.mem_map.mpr ⟨nextChoice, hNextChoice, rfl⟩)
      · refine ⟨Clause.negate
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell headChoice), by simp, ?_⟩
        apply (Clause.negate_eval_true_iff _ a).2
        cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell headChoice).eval a <;> simp [hEval] at hHeadAtom ⊢
  · rw [tmVerifierNatListFalseDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨falseChoice, hFalseChoice, rfl⟩
    by_cases hFalseAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell falseChoice).eval a = true
    · have hFalseMem :
          falseChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        (tmVerifierCertificateRightReadChoices_spec V falseSymbol hFalseChoice).1
      have hChoiceMem :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        (tmVerifierCertificateRightReadChoices_spec V trueSymbol hChoice).1
      have hEq : falseChoice = choice := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell falseChoice choice hFalseMem hChoiceMem hFalseAtom hAtom
      have hSymEq :=
        tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hFalseChoice
          (by simpa [hEq] using hChoice)
      exact False.elim (hTrueFalse hSymEq.symm)
    · refine ⟨Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell falseChoice), by simp, ?_⟩
      apply (Clause.negate_eval_true_iff _ a).2
      cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell falseChoice).eval a <;> simp [hEval] at hFalseAtom ⊢

theorem natListMainCellCNFAt_satisfies_of_false_delimiter_atoms
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {choice delimiterChoice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true)
    (hDelimiterChoice :
      delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hDelimiterAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListMainCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · rw [tmVerifierNatListInvalidSymbolChoiceClausesAt, tmVerifierUnitClauses_satisfies]
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨badChoice, hInvalid, rfl⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hBadAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a = true
      · have hInvalidSpec :
            badChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
              badChoice ≠ TMVerifierStackReadChoice.empty ∧
                badChoice ∉ tmVerifierCertificateRightReadChoices V trueSymbol ∧
                  badChoice ∉ tmVerifierCertificateRightReadChoices V falseSymbol ∧
                    badChoice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          simpa [tmVerifierNatListInvalidSymbolChoices] using hInvalid
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V falseSymbol hChoice).1
        have hEq : badChoice = choice := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell badChoice choice hInvalidSpec.1 hChoiceMem hBadAtom hAtom
        exact False.elim (hInvalidSpec.2.2.2.1 (by simpa [hEq] using hChoice))
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a <;> simp [hEval] at hBadAtom ⊢
    · rw [tmVerifierNatListTrueContinuationClausesAt]
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨trueChoice, hTrueChoice, rfl⟩
      by_cases hTrueAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell trueChoice).eval a = true
      · have hTrueMem :
            trueChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V trueSymbol hTrueChoice).1
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V falseSymbol hChoice).1
        have hEq : trueChoice = choice := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell trueChoice choice hTrueMem hChoiceMem hTrueAtom hAtom
        have hSymEq :=
          tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hTrueChoice
            (by simpa [hEq] using hChoice)
        exact False.elim (hTrueFalse hSymEq)
      · refine ⟨Clause.negate
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell trueChoice), by simp, ?_⟩
        apply (Clause.negate_eval_true_iff _ a).2
        cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell trueChoice).eval a <;> simp [hEval] at hTrueAtom ⊢
  · rw [tmVerifierNatListFalseDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨headChoice, hHeadChoice, rfl⟩
    by_cases hHeadAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell headChoice).eval a = true
    · refine ⟨
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 (cell + 1) delimiterChoice, ?_, hDelimiterAtom⟩
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨delimiterChoice, hDelimiterChoice, rfl⟩)
    · refine ⟨Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell headChoice), by simp, ?_⟩
      apply (Clause.negate_eval_true_iff _ a).2
      cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell headChoice).eval a <;> simp [hEval] at hHeadAtom ⊢

theorem natListMainCellCNFAt_satisfies_of_delimiter_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierNatListMainCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · rw [tmVerifierNatListInvalidSymbolChoiceClausesAt, tmVerifierUnitClauses_satisfies]
      intro lit hlit
      rcases List.mem_map.mp hlit with ⟨badChoice, hInvalid, rfl⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hBadAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a = true
      · have hInvalidSpec :
            badChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
              badChoice ≠ TMVerifierStackReadChoice.empty ∧
                badChoice ∉ tmVerifierCertificateRightReadChoices V trueSymbol ∧
                  badChoice ∉ tmVerifierCertificateRightReadChoices V falseSymbol ∧
                    badChoice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          simpa [tmVerifierNatListInvalidSymbolChoices] using hInvalid
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hChoice).1
        have hEq : badChoice = choice := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell badChoice choice hInvalidSpec.1 hChoiceMem hBadAtom hAtom
        exact False.elim (hInvalidSpec.2.2.2.2 (by simpa [hEq] using hChoice))
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell badChoice).eval a <;> simp [hEval] at hBadAtom ⊢
    · rw [tmVerifierNatListTrueContinuationClausesAt]
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨trueChoice, hTrueChoice, rfl⟩
      refine ⟨Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell trueChoice), by simp, ?_⟩
      apply (Clause.negate_eval_true_iff _ a).2
      by_cases hTrueAtom :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell trueChoice).eval a = true
      · have hTrueMem :
            trueChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V trueSymbol hTrueChoice).1
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hChoice).1
        have hEq : trueChoice = choice := by
          exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
            (tmVerifierTM V).k₀ cell a
            (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
              (tmVerifierTM V).k₀)
            hCell trueChoice choice hTrueMem hChoiceMem hTrueAtom hAtom
        have hSymEq :=
          tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hTrueChoice
            (by simpa [hEq] using hChoice)
        exact False.elim (hTrueDelimiter hSymEq)
      · cases hEval :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell trueChoice).eval a <;> simp [hEval] at hTrueAtom ⊢
  · rw [tmVerifierNatListFalseDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨falseChoice, hFalseChoice, rfl⟩
    refine ⟨Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell falseChoice), by simp, ?_⟩
    apply (Clause.negate_eval_true_iff _ a).2
    by_cases hFalseAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell falseChoice).eval a = true
    · have hFalseMem :
          falseChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        (tmVerifierCertificateRightReadChoices_spec V falseSymbol hFalseChoice).1
      have hChoiceMem :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hChoice).1
      have hEq : falseChoice = choice := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell falseChoice choice hFalseMem hChoiceMem hFalseAtom hAtom
      have hSymEq :=
        tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hFalseChoice
          (by simpa [hEq] using hChoice)
      exact False.elim (hFalseDelimiter hSymEq)
    · cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell falseChoice).eval a <;> simp [hEval] at hFalseAtom ⊢

theorem natListCertificateSymbols_mem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {xs : List Nat} {s : V.Cert.Symbol}
    (hs :
      s ∈ tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs) :
    s = trueSymbol ∨ s = falseSymbol ∨ s = delimiterSymbol := by
  classical
  induction xs with
  | nil =>
      simp at hs
  | cons n xs ih =>
      rw [tmVerifierNatListCertificateSymbols_cons] at hs
      rw [List.mem_append, List.mem_append] at hs
      rcases hs with (hRep | hPair) | hTail
      · left
        simpa using (List.eq_of_mem_replicate hRep)
      · simp at hPair
        rcases hPair with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact ih hTail

theorem natListCertificateSymbols_start_ne_delimiter
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (xs : List Nat) :
    (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
      delimiterSymbol xs)[0]? ≠ some delimiterSymbol := by
  classical
  cases xs with
  | nil =>
      simp
  | cons n xs =>
      cases n with
      | zero =>
          simpa [tmVerifierNatListCertificateSymbols_cons] using hFalseDelimiter
      | succ n =>
          simpa [tmVerifierNatListCertificateSymbols_cons, List.replicate_succ] using
            hTrueDelimiter

theorem natListCertificateSymbols_true_next
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    {xs : List Nat} {i : Nat}
    (h :
      (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i]? = some trueSymbol) :
    (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i + 1]? = some trueSymbol ∨
      (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i + 1]? = some falseSymbol := by
  classical
  induction xs generalizing i with
  | nil =>
      simp at h
  | cons n xs ih =>
      by_cases hi : i < n
      · by_cases hnext : i + 1 < n
        · left
          simp [tmVerifierNatListCertificateSymbols_cons, List.getElem?_append, hnext]
        · right
          have hEq : i + 1 = n := by omega
          simp [tmVerifierNatListCertificateSymbols_cons, hEq]
      · by_cases hFalseIdx : i = n
        · subst i
          simp [tmVerifierNatListCertificateSymbols_cons] at h
          exact False.elim (hTrueFalse h.symm)
        · by_cases hDelimiterIdx : i = n + 1
          · subst i
            simp [tmVerifierNatListCertificateSymbols_cons] at h
            exact False.elim (hTrueDelimiter h.symm)
          · have hTailIndex : n + 2 ≤ i := by omega
            let j := i - (n + 2)
            have hEq : i = n + 2 + j := by
              dsimp [j]
              omega
            have hTail :
                (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
                  delimiterSymbol xs)[j]? = some trueSymbol := by
              have h' := h
              rw [tmVerifierNatListCertificateSymbols_cons] at h'
              have hPrefixLe :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLe] at h'
              have hSub :
                  i - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j := by
                simp [j]
              simpa [hSub] using h'
            have hNext := ih hTail
            rcases hNext with hNext | hNext
            · left
              rw [tmVerifierNatListCertificateSymbols_cons]
              have hPrefixLeNext :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i + 1 := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLeNext]
              have hSubNext :
                  i + 1 - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j + 1 := by
                simp [j]
                omega
              have hSubNext' : i - (n + 1) = j + 1 := by
                dsimp [j]
                omega
              simpa [hSubNext'] using hNext
            · right
              rw [tmVerifierNatListCertificateSymbols_cons]
              have hPrefixLeNext :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i + 1 := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLeNext]
              have hSubNext :
                  i + 1 - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j + 1 := by
                simp [j]
                omega
              have hSubNext' : i - (n + 1) = j + 1 := by
                dsimp [j]
                omega
              simpa [hSubNext'] using hNext

theorem natListCertificateSymbols_false_next
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {xs : List Nat} {i : Nat}
    (h :
      (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i]? = some falseSymbol) :
    (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
      delimiterSymbol xs)[i + 1]? = some delimiterSymbol := by
  classical
  induction xs generalizing i with
  | nil =>
      simp at h
  | cons n xs ih =>
      by_cases hi : i < n
      · have hCurrent :
            (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (n :: xs))[i]? = some trueSymbol := by
          simp [tmVerifierNatListCertificateSymbols_cons, List.getElem?_append, hi]
        rw [hCurrent] at h
        exact False.elim (hTrueFalse (Option.some.inj h))
      · by_cases hFalseIdx : i = n
        · subst i
          simp [tmVerifierNatListCertificateSymbols_cons]
        · by_cases hDelimiterIdx : i = n + 1
          · subst i
            simp [tmVerifierNatListCertificateSymbols_cons] at h
            exact False.elim (hFalseDelimiter h.symm)
          · have hTailIndex : n + 2 ≤ i := by omega
            let j := i - (n + 2)
            have hEq : i = n + 2 + j := by
              dsimp [j]
              omega
            have hTail :
                (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
                  delimiterSymbol xs)[j]? = some falseSymbol := by
              have h' := h
              rw [tmVerifierNatListCertificateSymbols_cons] at h'
              have hPrefixLe :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLe] at h'
              have hSub :
                  i - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j := by
                simp [j]
              simpa [hSub] using h'
            have hNext := ih hTail
            rw [tmVerifierNatListCertificateSymbols_cons]
            have hPrefixLeNext :
                (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                  i + 1 := by
              simp
              omega
            rw [List.getElem?_append_right hPrefixLeNext]
            have hSubNext :
                i + 1 - (List.replicate n trueSymbol ++
                  [falseSymbol, delimiterSymbol]).length = j + 1 := by
              simp [j]
              omega
            have hSubNext' : i - (n + 1) = j + 1 := by
              dsimp [j]
              omega
            simpa [hSubNext'] using hNext

theorem natListCertificateSymbols_delimiter_previous
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {xs : List Nat} {i : Nat}
    (h :
      (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i]? = some delimiterSymbol) :
    0 < i ∧
      (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
        delimiterSymbol xs)[i - 1]? = some falseSymbol := by
  classical
  induction xs generalizing i with
  | nil =>
      simp at h
  | cons n xs ih =>
      by_cases hi : i < n
      · have hCurrent :
            (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (n :: xs))[i]? = some trueSymbol := by
          simp [tmVerifierNatListCertificateSymbols_cons, List.getElem?_append, hi]
        rw [hCurrent] at h
        exact False.elim (hTrueDelimiter (Option.some.inj h))
      · by_cases hFalseIdx : i = n
        · subst i
          simp [tmVerifierNatListCertificateSymbols_cons] at h
          exact False.elim (hFalseDelimiter h)
        · by_cases hDelimiterIdx : i = n + 1
          · subst i
            constructor
            · omega
            · simp [tmVerifierNatListCertificateSymbols_cons]
          · have hTailIndex : n + 2 ≤ i := by omega
            let j := i - (n + 2)
            have hEq : i = n + 2 + j := by
              dsimp [j]
              omega
            have hTail :
                (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
                  delimiterSymbol xs)[j]? = some delimiterSymbol := by
              have h' := h
              rw [tmVerifierNatListCertificateSymbols_cons] at h'
              have hPrefixLe :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLe] at h'
              have hSub :
                  i - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j := by
                simp [j]
              simpa [hSub] using h'
            rcases ih hTail with ⟨hjPos, hPrev⟩
            constructor
            · omega
            · have hPrevEq : i - 1 = n + 2 + (j - 1) := by
                dsimp [j] at hEq ⊢
                omega
              rw [tmVerifierNatListCertificateSymbols_cons]
              have hPrefixLePrev :
                  (List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]).length ≤
                    i - 1 := by
                simp
                omega
              rw [List.getElem?_append_right hPrefixLePrev]
              have hSubPrev :
                  i - 1 - (List.replicate n trueSymbol ++
                    [falseSymbol, delimiterSymbol]).length = j - 1 := by
                simp [j]
                omega
              have hSubPrev' : i - 1 - (n + 2) = j - 1 := by
                dsimp [j]
                omega
              simpa [hSubPrev'] using hPrev

theorem natListSuffixPatternCNF_satisfies_of_mapped_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (xs : List Nat)
    (hSymbols :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness V).inputAlphabet =
        (tmVerifierNatListCertificateSymbols trueSymbol falseSymbol delimiterSymbol xs).map
          (tmVerifierInputRightSymbol (V := V))) :
    CNF.Satisfies
      (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a := by
  classical
  let symbols := tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
    delimiterSymbol xs
  have hSymbols' :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness V).inputAlphabet =
        symbols.map (tmVerifierInputRightSymbol (V := V)) := by
    simpa [symbols] using hSymbols
  have hSuffixLen : E.decodedInitialCertificateSuffixWord.length = symbols.length := by
    calc
      E.decodedInitialCertificateSuffixWord.length =
          (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet).length := by
            simp
      _ = (symbols.map (tmVerifierInputRightSymbol (V := V))).length := by
            rw [hSymbols']
      _ = symbols.length := by
            simp
  have hSuffixLeChoice :
      E.decodedInitialCertificateSuffixWord.length ≤
        E.decodedInitialCertificateChoicePrefix.length := by
    have hWord :
        tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
          E.decodedInitialCertificateSuffixWord := by
      simpa [tmVerifierXOnlyInputChoicePrefixWord] using
        E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
    rw [← hWord]
    exact tmVerifierReadChoicePrefixToStack_length_le
      E.decodedInitialCertificateChoicePrefix
  let bound := tmVerifierCertificateSizeBound V x
  let start := L.Instance.inputSize x + 1
  have hPrefixLen :
      (tmVerifierInstanceInputPrefixWord V x).length = start := by
    simp [start, tmVerifierInstanceInputPrefixWord_length]
  have hChoiceLen : E.decodedInitialCertificateChoicePrefix.length = bound := by
    simpa [bound] using E.decodedInitialCertificateChoicePrefix_length
  have hCellRangeOfOffset :
      ∀ {offset : Nat}, offset ≤ bound →
        start + offset ∈ tmVerifierXOnlyCellRange V x := by
    intro offset hoff
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hCellLeInput : start + offset ≤ tmVerifierXOnlyInputLengthBound V x := by
      dsimp [start, bound]
      simpa [tmVerifierXOnlyInputLengthBound, Nat.add_assoc] using
        Nat.add_le_add_left hoff (L.Instance.inputSize x + 1)
    exact Nat.le_trans hCellLeInput hInputLe
  have hEmptyAtomAtOffset :
      ∀ {offset : Nat}, offset ≤ bound →
        E.decodedInitialCertificateSuffixWord.length ≤ offset →
          (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ (start + offset)).eval a = true := by
    intro offset hoff hSuffixLeOffset
    by_cases hoffEq : offset = bound
    · have hCellBound :
          start + offset =
            (tmVerifierInstanceInputPrefixWord V x).length +
              E.decodedInitialCertificateChoicePrefix.length := by
        rw [hoffEq, hChoiceLen, hPrefixLen]
      simpa [hCellBound] using E.decodedInitialCertificateChoicePrefix_empty_after
    · have hoffLt : offset < bound := lt_of_le_of_ne hoff hoffEq
      have hOffsetPrefix : offset < E.decodedInitialCertificateChoicePrefix.length := by
        simpa [hChoiceLen] using hoffLt
      have hEmptyChoice :
          E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix =
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
        E.decodedInitialCertificateChoicePrefix_empty_of_decoded_suffix_length_le
          hSuffixLeOffset hOffsetPrefix
      have hAtom :=
        E.decodedInitialCertificateChoicePrefix_atom_true (i := offset) hOffsetPrefix
      have hCellEq :
          (tmVerifierInstanceInputPrefixWord V x).length + offset = start + offset := by
        rw [hPrefixLen]
      simpa [tmVerifierStackEmptyAtom, TMVerifierStackReadChoice.atomAt, hEmptyChoice,
        hCellEq] using hAtom
  intro clause hclause
  rw [tmVerifierNatListSuffixPatternCNF, tmVerifierNatListSuffixPatternCNFForBound]
    at hclause
  rw [List.mem_append, List.mem_append] at hclause
  rcases hclause with (hMain | hStart) | hPrevious
  · rcases List.mem_flatMap.mp hMain with ⟨idx, hidxMem, hclauseCell⟩
    have hidx : idx < bound := by
      simpa [bound] using List.mem_range.mp hidxMem
    have hMin : Nat.min idx bound = idx := Nat.min_eq_left (Nat.le_of_lt hidx)
    let cell := start + idx
    have hCellRange : cell ∈ tmVerifierXOnlyCellRange V x :=
      hCellRangeOfOffset (offset := idx) (Nat.le_of_lt hidx)
    have hCellSat :
        CNF.Satisfies
          (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a := by
      by_cases hidxSymbols : idx < symbols.length
      · have hidxPrefix : idx < E.decodedInitialCertificateChoicePrefix.length := by
          simpa [hChoiceLen] using hidx
        let choice := E.decodedInitialCertificateChoicePrefix[idx]'hidxPrefix
        have hChoiceSym :
            choice ∈ tmVerifierCertificateRightReadChoices V symbols[idx] := by
          exact E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
            hSymbols' hidxSymbols hidxPrefix
        have hAtom :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 cell choice).eval a = true := by
          have hAtom' :=
            E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidxPrefix
          have hCellEq :
              (tmVerifierInstanceInputPrefixWord V x).length + idx = cell := by
            dsimp [cell]
            rw [hPrefixLen]
          simpa [choice, hCellEq] using hAtom'
        have hMem :=
          natListCertificateSymbols_mem trueSymbol falseSymbol delimiterSymbol
            (xs := xs) (s := symbols[idx]) (List.getElem_mem hidxSymbols)
        rcases hMem with hTrue | hFalse | hDelimiter
        · have hGet : symbols[idx]? = some trueSymbol := by
            simpa [hTrue] using (List.getElem?_eq_getElem hidxSymbols)
          rcases natListCertificateSymbols_true_next trueSymbol falseSymbol delimiterSymbol
              hTrueFalse hTrueDelimiter hGet with hNextTrue | hNextFalse
          · rcases List.getElem?_eq_some_iff.mp hNextTrue with
              ⟨hNextLen, hNextEq⟩
            have hNextLenSymbols : idx + 1 < symbols.length := by
              simpa [symbols] using hNextLen
            have hNextEqSymbols : symbols[idx + 1] = trueSymbol := by
              simpa [symbols] using hNextEq
            have hnextPrefix : idx + 1 < E.decodedInitialCertificateChoicePrefix.length := by
              have hSymbolsLeChoice : symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
                rw [← hSuffixLen]
                exact hSuffixLeChoice
              exact Nat.lt_of_lt_of_le hNextLenSymbols hSymbolsLeChoice
            let nextChoice := E.decodedInitialCertificateChoicePrefix[idx + 1]'hnextPrefix
            have hNextChoice :
                nextChoice ∈
                  tmVerifierCertificateRightReadChoices V trueSymbol ++
                    tmVerifierCertificateRightReadChoices V falseSymbol := by
              have hRC :
                  nextChoice ∈ tmVerifierCertificateRightReadChoices V symbols[idx + 1] :=
                E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
                  hSymbols' hNextLenSymbols hnextPrefix
              exact List.mem_append_left _
                (by simpa [hNextEqSymbols] using hRC)
            have hNextAtom :
                (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                  0 (cell + 1) nextChoice).eval a = true := by
              have hAtom' :=
                E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnextPrefix
              have hCellEq :
                  (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) =
                    cell + 1 := by
                dsimp [cell]
                rw [hPrefixLen]
                omega
              simpa [nextChoice, ← hCellEq] using hAtom'
            exact E.natListMainCellCNFAt_satisfies_of_true_next_atoms trueSymbol
              falseSymbol delimiterSymbol hTrueFalse hCellRange
              (by simpa [hTrue] using hChoiceSym) hAtom hNextChoice hNextAtom
          · rcases List.getElem?_eq_some_iff.mp hNextFalse with
              ⟨hNextLen, hNextEq⟩
            have hNextLenSymbols : idx + 1 < symbols.length := by
              simpa [symbols] using hNextLen
            have hNextEqSymbols : symbols[idx + 1] = falseSymbol := by
              simpa [symbols] using hNextEq
            have hnextPrefix : idx + 1 < E.decodedInitialCertificateChoicePrefix.length := by
              have hSymbolsLeChoice : symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
                rw [← hSuffixLen]
                exact hSuffixLeChoice
              exact Nat.lt_of_lt_of_le hNextLenSymbols hSymbolsLeChoice
            let nextChoice := E.decodedInitialCertificateChoicePrefix[idx + 1]'hnextPrefix
            have hNextChoice :
                nextChoice ∈
                  tmVerifierCertificateRightReadChoices V trueSymbol ++
                    tmVerifierCertificateRightReadChoices V falseSymbol := by
              have hRC :
                  nextChoice ∈ tmVerifierCertificateRightReadChoices V symbols[idx + 1] :=
                E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
                  hSymbols' hNextLenSymbols hnextPrefix
              exact List.mem_append_right _
                (by simpa [hNextEqSymbols] using hRC)
            have hNextAtom :
                (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                  0 (cell + 1) nextChoice).eval a = true := by
              have hAtom' :=
                E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnextPrefix
              have hCellEq :
                  (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) =
                    cell + 1 := by
                dsimp [cell]
                rw [hPrefixLen]
                omega
              simpa [nextChoice, ← hCellEq] using hAtom'
            exact E.natListMainCellCNFAt_satisfies_of_true_next_atoms trueSymbol
              falseSymbol delimiterSymbol hTrueFalse hCellRange
              (by simpa [hTrue] using hChoiceSym) hAtom hNextChoice hNextAtom
        · have hGet : symbols[idx]? = some falseSymbol := by
            simpa [hFalse] using (List.getElem?_eq_getElem hidxSymbols)
          have hNext := natListCertificateSymbols_false_next trueSymbol falseSymbol
            delimiterSymbol hTrueFalse hFalseDelimiter hGet
          rcases List.getElem?_eq_some_iff.mp hNext with ⟨hNextLen, hNextEq⟩
          have hNextLenSymbols : idx + 1 < symbols.length := by
            simpa [symbols] using hNextLen
          have hNextEqSymbols : symbols[idx + 1] = delimiterSymbol := by
            simpa [symbols] using hNextEq
          have hnextPrefix : idx + 1 < E.decodedInitialCertificateChoicePrefix.length := by
            have hSymbolsLeChoice : symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
              rw [← hSuffixLen]
              exact hSuffixLeChoice
            exact Nat.lt_of_lt_of_le hNextLenSymbols hSymbolsLeChoice
          let delimiterChoice := E.decodedInitialCertificateChoicePrefix[idx + 1]'hnextPrefix
          have hDelimiterChoice :
              delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
            have hRC :
                delimiterChoice ∈ tmVerifierCertificateRightReadChoices V symbols[idx + 1] :=
              E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
                hSymbols' hNextLenSymbols hnextPrefix
            simpa [hNextEqSymbols] using hRC
          have hDelimiterAtom :
              (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 (cell + 1) delimiterChoice).eval a = true := by
            have hAtom' :=
              E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnextPrefix
            have hCellEq :
                (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) =
                  cell + 1 := by
              dsimp [cell]
              rw [hPrefixLen]
              omega
            simpa [delimiterChoice, ← hCellEq] using hAtom'
          exact E.natListMainCellCNFAt_satisfies_of_false_delimiter_atoms trueSymbol
            falseSymbol delimiterSymbol hTrueFalse hCellRange
            (by simpa [hFalse] using hChoiceSym) hAtom hDelimiterChoice hDelimiterAtom
        · exact E.natListMainCellCNFAt_satisfies_of_delimiter_atom trueSymbol
            falseSymbol delimiterSymbol hTrueDelimiter hFalseDelimiter hCellRange
            (by simpa [hDelimiter] using hChoiceSym) hAtom
      · have hSuffixLeIdx : E.decodedInitialCertificateSuffixWord.length ≤ idx := by
          rw [hSuffixLen]
          exact Nat.le_of_not_gt hidxSymbols
        have hEmpty := hEmptyAtomAtOffset (offset := idx) (Nat.le_of_lt hidx) hSuffixLeIdx
        exact E.natListMainCellCNFAt_satisfies_of_empty_atom trueSymbol falseSymbol
          delimiterSymbol hCellRange hEmpty
    exact hCellSat clause (by
      have hCellEq :
          L.Instance.inputSize x + 1 + Nat.min idx (tmVerifierCertificateSizeBound V x) =
            cell := by
        dsimp [cell, start, bound]
        rw [hMin]
      simpa [hCellEq] using hclauseCell)
  · have hStartSat :
        CNF.Satisfies (tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol start) a := by
      by_cases hEmptySymbols : symbols.length = 0
      · have hSuffixLeZero :
            E.decodedInitialCertificateSuffixWord.length ≤ 0 := by
          rw [hSuffixLen, hEmptySymbols]
        have hEmpty := hEmptyAtomAtOffset (offset := 0) (Nat.zero_le bound) hSuffixLeZero
        have hAtom :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 start
              (TMVerifierStackReadChoice.empty :
                TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
          simpa [tmVerifierStackEmptyAtom, TMVerifierStackReadChoice.atomAt] using hEmpty
        exact E.natListStartDelimiterClausesAt_satisfies_of_not_delimiter_atom
          delimiterSymbol (hCellRangeOfOffset (offset := 0) (Nat.zero_le bound))
          (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀)
          (by
            intro hDelim
            exact tmVerifierCertificateRightReadChoices_ne_empty hDelim rfl)
          hAtom
      · have hZeroSymbols : 0 < symbols.length := Nat.pos_of_ne_zero hEmptySymbols
        have hZeroPrefix : 0 < E.decodedInitialCertificateChoicePrefix.length := by
          have hSymbolsLeChoice : symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
            rw [← hSuffixLen]
            exact hSuffixLeChoice
          omega
        let choice := E.decodedInitialCertificateChoicePrefix[0]'hZeroPrefix
        have hChoiceSym :
            choice ∈ tmVerifierCertificateRightReadChoices V symbols[0] :=
          E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
            hSymbols' hZeroSymbols hZeroPrefix
        have hNotDelimiter :
            choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          intro hDelim
          have hSymEq :=
            tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hChoiceSym hDelim
          have hGetDelim : symbols[0]? = some delimiterSymbol := by
            simpa [hSymEq] using (List.getElem?_eq_getElem hZeroSymbols)
          exact natListCertificateSymbols_start_ne_delimiter trueSymbol falseSymbol
            delimiterSymbol hTrueDelimiter hFalseDelimiter xs hGetDelim
        have hAtom :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 start choice).eval a = true := by
          have hAtom' := E.decodedInitialCertificateChoicePrefix_atom_true
            (i := 0) hZeroPrefix
          have hCellEq : (tmVerifierInstanceInputPrefixWord V x).length + 0 = start := by
            rw [hPrefixLen]
          simpa [choice, hCellEq] using hAtom'
        have hChoiceMem :
            choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
          E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hZeroPrefix)
        exact E.natListStartDelimiterClausesAt_satisfies_of_not_delimiter_atom
          delimiterSymbol (hCellRangeOfOffset (offset := 0) (Nat.zero_le bound))
          hChoiceMem hNotDelimiter hAtom
    exact hStartSat clause (by simpa [start] using hStart)
  · rcases List.mem_flatMap.mp hPrevious with ⟨idx, hidxMem, hclauseCell⟩
    have hidx : idx < bound := by
      simpa [bound] using List.mem_range.mp hidxMem
    let offset := Nat.min (idx + 1) bound
    let cell := start + offset
    have hOffsetLe : offset ≤ bound := Nat.min_le_right (idx + 1) bound
    have hCellRange : cell ∈ tmVerifierXOnlyCellRange V x :=
      hCellRangeOfOffset (offset := offset) hOffsetLe
    have hPrevSat :
        CNF.Satisfies
          (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell)
          a := by
      by_cases hOffsetAtBound : offset = bound
      · have hSuffixLeBound :
            E.decodedInitialCertificateSuffixWord.length ≤ bound := by
          rw [hChoiceLen] at hSuffixLeChoice
          exact hSuffixLeChoice
        have hEmpty := hEmptyAtomAtOffset (offset := offset) hOffsetLe
          (by simpa [hOffsetAtBound] using hSuffixLeBound)
        exact E.natListDelimiterPreviousClausesAt_satisfies_of_empty_atom falseSymbol
          delimiterSymbol hCellRange hEmpty
      · have hOffsetLt : offset < bound := lt_of_le_of_ne hOffsetLe hOffsetAtBound
        have hOffsetPrefix : offset < E.decodedInitialCertificateChoicePrefix.length := by
          simpa [hChoiceLen] using hOffsetLt
        by_cases hOffsetSymbols : offset < symbols.length
        · let choice := E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix
          have hChoiceSym :
              choice ∈ tmVerifierCertificateRightReadChoices V symbols[offset] :=
            E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
              hSymbols' hOffsetSymbols hOffsetPrefix
          have hAtom :
              (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 cell choice).eval a = true := by
            have hAtom' :=
              E.decodedInitialCertificateChoicePrefix_atom_true (i := offset) hOffsetPrefix
            have hCellEq :
                (tmVerifierInstanceInputPrefixWord V x).length + offset = cell := by
              dsimp [cell]
              rw [hPrefixLen]
            simpa [choice, hCellEq] using hAtom'
          have hMem :=
            natListCertificateSymbols_mem trueSymbol falseSymbol delimiterSymbol
              (xs := xs) (s := symbols[offset]) (List.getElem_mem hOffsetSymbols)
          rcases hMem with hTrue | hFalse | hDelimiter
          · have hChoiceTrue :
                choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol := by
              simpa [hTrue] using hChoiceSym
            have hNotDelimiter :
                choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
              intro hDelim
              have hSymEq :=
                tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hChoiceTrue hDelim
              exact hTrueDelimiter hSymEq
            exact E.natListDelimiterPreviousClausesAt_satisfies_of_not_delimiter_atom
              falseSymbol delimiterSymbol hCellRange
              (E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hOffsetPrefix))
              hNotDelimiter hAtom
          · have hChoiceFalse :
                choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol := by
              simpa [hFalse] using hChoiceSym
            have hNotDelimiter :
                choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
              intro hDelim
              have hSymEq :=
                tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hChoiceFalse hDelim
              exact hFalseDelimiter hSymEq
            exact E.natListDelimiterPreviousClausesAt_satisfies_of_not_delimiter_atom
              falseSymbol delimiterSymbol hCellRange
              (E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hOffsetPrefix))
              hNotDelimiter hAtom
          · have hGet : symbols[offset]? = some delimiterSymbol := by
              simpa [hDelimiter] using (List.getElem?_eq_getElem hOffsetSymbols)
            rcases natListCertificateSymbols_delimiter_previous trueSymbol falseSymbol
                delimiterSymbol hTrueDelimiter hFalseDelimiter hGet with
              ⟨hOffsetPos, hPrevGet⟩
            rcases List.getElem?_eq_some_iff.mp hPrevGet with ⟨hPrevLen, hPrevEq⟩
            have hPrevLenSymbols : offset - 1 < symbols.length := by
              simpa [symbols] using hPrevLen
            have hPrevEqSymbols : symbols[offset - 1] = falseSymbol := by
              simpa [symbols] using hPrevEq
            have hPrevPrefix : offset - 1 < E.decodedInitialCertificateChoicePrefix.length := by
              have hSymbolsLeChoice : symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
                rw [← hSuffixLen]
                exact hSuffixLeChoice
              omega
            let falseChoice :=
              E.decodedInitialCertificateChoicePrefix[offset - 1]'hPrevPrefix
            have hFalseChoice :
                falseChoice ∈ tmVerifierCertificateRightReadChoices V falseSymbol := by
              have hRC :
                  falseChoice ∈ tmVerifierCertificateRightReadChoices V symbols[offset - 1] :=
                E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
                  hSymbols' hPrevLenSymbols hPrevPrefix
              simpa [hPrevEqSymbols] using hRC
            have hFalseAtom :
                (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                  0 (cell - 1) falseChoice).eval a = true := by
              have hAtom' := E.decodedInitialCertificateChoicePrefix_atom_true
                (i := offset - 1) hPrevPrefix
              have hCellEq :
                  (tmVerifierInstanceInputPrefixWord V x).length + (offset - 1) =
                    cell - 1 := by
                dsimp [cell]
                rw [hPrefixLen]
                omega
              simpa [falseChoice, ← hCellEq] using hAtom'
            exact E.natListDelimiterPreviousClausesAt_satisfies_of_previous_false_atom
              falseSymbol delimiterSymbol hFalseChoice hFalseAtom
        · have hSuffixLeOffset :
              E.decodedInitialCertificateSuffixWord.length ≤ offset := by
            rw [hSuffixLen]
            exact Nat.le_of_not_gt hOffsetSymbols
          have hEmpty := hEmptyAtomAtOffset (offset := offset) hOffsetLe hSuffixLeOffset
          exact E.natListDelimiterPreviousClausesAt_satisfies_of_empty_atom falseSymbol
            delimiterSymbol hCellRange hEmpty
    exact hPrevSat clause (by
      have hCellEq :
          L.Instance.inputSize x + 1 +
              Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x) =
            cell := by
        dsimp [cell, start, offset, bound]
      simpa [hCellEq] using hclauseCell)

end TMVerifierXOnlyGlobalTableauEvidence

/--
Build the unary nat-list checked suffix decoder with both directions proved from
the certificate-symbol stream equations.
-/
noncomputable def tmVerifierNatListCheckedSuffixDecoderComplete
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat → V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier → List Nat)
    (certOfNats_suffix_eq :
      ∀ xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (cert_suffix_eq :
      ∀ c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V))) :
    TMVerifierXOnlyCheckedSuffixDecoder V :=
  tmVerifierNatListCheckedSuffixDecoder V trueSymbol falseSymbol delimiterSymbol
    hFalseDelimiter D certOfNats natsOfCert certOfNats_suffix_eq cert_suffix_eq
    (by
      intro B x a w
      let E := w.evidence
      let c : V.Cert.Carrier := w.valid_suffix.cert
      have hMapped :
          E.decodedInitialCertificateSuffixWord.map
              (tmVerifierComputableWitness V).inputAlphabet =
            tmVerifierCertificateInputSuffixEncoded V c := by
        change
          ((tmVerifierXOnlyGlobalTableauCNF_evidence V B x a
              w.global_tableau).decodedInitialCertificateSuffixWord).map
              (tmVerifierComputableWitness V).inputAlphabet =
            tmVerifierCertificateInputSuffixEncoded V c
        rw [w.valid_suffix.suffix_eq]
        simp [tmVerifierCertificateInputSuffixWord, c]
      have hSymbols :
          E.decodedInitialCertificateSuffixWord.map
              (tmVerifierComputableWitness V).inputAlphabet =
            (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
                delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V)) := by
        rw [hMapped, cert_suffix_eq c]
      exact
        E.natListSuffixPatternCNF_satisfies_of_mapped_suffix trueSymbol falseSymbol
          delimiterSymbol hTrueFalse hTrueDelimiter hFalseDelimiter (natsOfCert c) hSymbols)

end SAT
end ComplexityReduction
