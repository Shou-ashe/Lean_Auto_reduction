/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyNatListSuffixDecoderTM

/-!
Reusable checked-decoder package for unary natural-list certificate suffixes.

This file connects the local `EncodedType.list EncodedType.nat` suffix-pattern
CNF to the choice-level nat-list decoder.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierNatListSuffixPatternCNFForBound_mainCell_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {start bound idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNFForBound V trueSymbol falseSymbol
          delimiterSymbol start bound) a)
    (hidx : idx ∈ List.range bound) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
        (start + Nat.min idx bound)) a := by
  intro clause hclause
  exact h clause (by
    rw [tmVerifierNatListSuffixPatternCNFForBound]
    exact List.mem_append_left _
      (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨idx, hidx, hclause⟩)))

theorem tmVerifierNatListSuffixPatternCNFForBound_startDelimiter_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {start bound : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNFForBound V trueSymbol falseSymbol
          delimiterSymbol start bound) a) :
    CNF.Satisfies (tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol start) a := by
  intro clause hclause
  exact h clause (by
    rw [tmVerifierNatListSuffixPatternCNFForBound]
    exact List.mem_append_left _
      (List.mem_append_right _ hclause))

theorem tmVerifierNatListSuffixPatternCNFForBound_delimiterPrevious_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {start bound idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNFForBound V trueSymbol falseSymbol
          delimiterSymbol start bound) a)
    (hidx : idx ∈ List.range bound) :
    CNF.Satisfies
      (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
        (start + Nat.min (idx + 1) bound)) a := by
  intro clause hclause
  exact h clause (by
    rw [tmVerifierNatListSuffixPatternCNFForBound]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨idx, hidx, hclause⟩))

theorem tmVerifierNatListSuffixPatternCNF_mainCell_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {x : L.Instance.Carrier} {idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    (hidx : idx < tmVerifierCertificateSizeBound V x) :
    CNF.Satisfies
      (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
        (L.Instance.inputSize x + 1 + Nat.min idx (tmVerifierCertificateSizeBound V x))) a := by
  exact tmVerifierNatListSuffixPatternCNFForBound_mainCell_satisfies V trueSymbol
    falseSymbol delimiterSymbol (by simpa [tmVerifierNatListSuffixPatternCNF] using h)
    (by simpa using hidx)

theorem tmVerifierNatListSuffixPatternCNF_startDelimiter_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {x : L.Instance.Carrier} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a) :
    CNF.Satisfies
      (tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol
        (L.Instance.inputSize x + 1)) a := by
  exact tmVerifierNatListSuffixPatternCNFForBound_startDelimiter_satisfies V trueSymbol
    falseSymbol delimiterSymbol (by simpa [tmVerifierNatListSuffixPatternCNF] using h)

theorem tmVerifierNatListSuffixPatternCNF_delimiterPrevious_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {x : L.Instance.Carrier} {idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    (hidx : idx < tmVerifierCertificateSizeBound V x) :
    CNF.Satisfies
      (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
        (L.Instance.inputSize x + 1 +
          Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x))) a := by
  exact tmVerifierNatListSuffixPatternCNFForBound_delimiterPrevious_satisfies V trueSymbol
    falseSymbol delimiterSymbol (by simpa [tmVerifierNatListSuffixPatternCNF] using h)
    (by simpa using hidx)

theorem tmVerifierNatListMainCellCNFAt_next_of_true_atom
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ nextChoice ∈
        tmVerifierCertificateRightReadChoices V trueSymbol ++
          tmVerifierCertificateRightReadChoices V falseSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) nextChoice).eval a = true := by
  have hTrueCNF :
      CNF.Satisfies
        (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell) a := by
    have hSplit := (CNF.satisfies_append
      (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
        delimiterSymbol cell)
      (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell ++
        tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a).1
      (by simpa [tmVerifierNatListMainCellCNFAt, List.append_assoc] using h)
    exact (CNF.satisfies_append
      (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell)
      (tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a).1
        hSplit.2 |>.1
  exact tmVerifierNatListTrueContinuationClausesAt_next_of_atom_true V trueSymbol
    falseSymbol hTrueCNF hChoice hAtom

theorem tmVerifierNatListMainCellCNFAt_delimiter_of_false_atom
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true := by
  have hFalseCNF :
      CNF.Satisfies
        (tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a := by
    have hSplit := (CNF.satisfies_append
      (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
        delimiterSymbol cell)
      (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell ++
        tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a).1
      (by simpa [tmVerifierNatListMainCellCNFAt, List.append_assoc] using h)
    exact (CNF.satisfies_append
      (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell)
      (tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a).1
        hSplit.2 |>.2
  exact tmVerifierNatListFalseDelimiterClausesAt_delimiter_of_atom_true V falseSymbol
    delimiterSymbol hFalseCNF hChoice hAtom

theorem tmVerifierNatListDelimiterPreviousClausesAt_previous_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ falseChoice ∈ tmVerifierCertificateRightReadChoices V falseSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell - 1) falseChoice).eval a = true := by
  let headAtom :=
    TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell choice
  let falseLits :=
    (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell - 1) falseChoice
  have hClause : Clause.Satisfies ([Clause.negate headAtom] ++ falseLits) a := by
    exact h _ (by
      rw [tmVerifierNatListDelimiterPreviousClausesAt]
      exact List.mem_map.mpr ⟨choice, hChoice, rfl⟩)
  rcases hClause with ⟨lit, hlit, heval⟩
  rw [List.mem_append] at hlit
  rcases hlit with hNeg | hPrev
  · simp [headAtom] at hNeg
    subst lit
    have hFalse := (Clause.negate_eval_true_iff headAtom a).1 heval
    simp [headAtom, hAtom] at hFalse
  · rcases List.mem_map.mp hPrev with ⟨falseChoice, hFalseChoice, rfl⟩
    exact ⟨falseChoice, hFalseChoice, heval⟩

theorem tmVerifierCertificateRightReadChoices_symbol_eq_of_mem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {s t : V.Cert.Symbol}
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hs : choice ∈ tmVerifierCertificateRightReadChoices V s)
    (ht : choice ∈ tmVerifierCertificateRightReadChoices V t) :
    s = t := by
  have hsSpec := (tmVerifierCertificateRightReadChoices_spec V s hs).2
  have htSpec := (tmVerifierCertificateRightReadChoices_spec V t ht).2
  rw [hsSpec] at htSpec
  exact Sum.inr.inj (Option.some.inj (Option.some.inj htSpec))

namespace TMVerifierXOnlyGlobalTableauEvidence

/--
At a unary-nat-list certificate offset, the checked pattern permits only empty
or one of the three concrete nat-list certificate symbols.
-/
theorem decodedInitialCertificateChoicePrefix_natList_allowed_at
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length) :
    let choice := E.decodedInitialCertificateChoicePrefix[idx]'hidx
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol ∨
      choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol ∨
      choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  classical
  intro choice
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min idx (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_mainCell_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min idx (tmVerifierCertificateSizeBound V x) = idx := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hChoiceMem :
      choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hidx)
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x)) choice).eval a =
        true := by
    simpa [choice, hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  exact tmVerifierNatListMainCellCNFAt_allowed_of_atom_true V trueSymbol falseSymbol
    delimiterSymbol hCellCNF hChoiceMem hAtom

/-- The first certificate-window choice is not a list delimiter. -/
theorem decodedInitialCertificateChoicePrefix_natList_start_not_delimiter
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    (h0 : 0 < E.decodedInitialCertificateChoicePrefix.length) :
    E.decodedInitialCertificateChoicePrefix[0]'h0 ∉
      tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  intro hDelimiter
  have hStart :
      CNF.Satisfies
        (tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol
          (L.Instance.inputSize x + 1)) a :=
    tmVerifierNatListSuffixPatternCNF_startDelimiter_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1)
        (E.decodedInitialCertificateChoicePrefix[0]'h0)).eval a = true := by
    have hCellEq :
        L.Instance.inputSize x + 1 =
          (tmVerifierInstanceInputPrefixWord V x).length + 0 := by
      rw [tmVerifierInstanceInputPrefixWord_length]
    rw [hCellEq]
    exact E.decodedInitialCertificateChoicePrefix_atom_true (i := 0) h0
  have hUnits :=
    (tmVerifierUnitClauses_satisfies
      ((tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun choice =>
        Clause.negate
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 (L.Instance.inputSize x + 1) choice)) a).1
      (by simpa [tmVerifierNatListStartDelimiterClausesAt] using hStart)
  let lit :=
    Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (L.Instance.inputSize x + 1)
        (E.decodedInitialCertificateChoicePrefix[0]'h0))
  have hLit : lit.eval a = true :=
    hUnits lit (List.mem_map.mpr
      ⟨E.decodedInitialCertificateChoicePrefix[0]'h0, hDelimiter, rfl⟩)
  have hFalse :=
    (Clause.negate_eval_true_iff
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (L.Instance.inputSize x + 1)
        (E.decodedInitialCertificateChoicePrefix[0]'h0)) a).1 hLit
  simp [hAtom] at hFalse

/-- A selected unary `true` forces the next decoded choice to be `true` or `false`. -/
theorem decodedInitialCertificateChoicePrefix_natList_true_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hnext : idx + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hTrue :
      E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
        tmVerifierCertificateRightReadChoices V trueSymbol) :
    E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext ∈
      tmVerifierCertificateRightReadChoices V trueSymbol ++
        tmVerifierCertificateRightReadChoices V falseSymbol := by
  classical
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min idx (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_mainCell_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min idx (tmVerifierCertificateSizeBound V x) = idx := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  rcases tmVerifierNatListMainCellCNFAt_next_of_true_atom V trueSymbol falseSymbol
      delimiterSymbol hCellCNF hTrue hAtom with
    ⟨nextChoice, hNextChoice, hNextAtom⟩
  let decodedNext := E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext
  have hDecodedNextMem :
      decodedNext ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hnext)
  have hNextMem :
      nextChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
    rcases List.mem_append.mp hNextChoice with hNextTrue | hNextFalse
    · exact (tmVerifierCertificateRightReadChoices_spec V trueSymbol hNextTrue).1
    · exact (tmVerifierCertificateRightReadChoices_spec V falseSymbol hNextFalse).1
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hSelected :=
    E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnext
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hNextAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx + 1))
        nextChoice).eval a = true := by
    simpa [hCellSucc] using hNextAtom
  have hEq : decodedNext = nextChoice := by
    simpa [decodedNext] using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx + 1)) a hDomain
        hCell decodedNext nextChoice hDecodedNextMem hNextMem hSelected hNextAtom')
  simpa [decodedNext, hEq] using hNextChoice

/-- A selected unary `false` forces the next decoded choice to be the delimiter. -/
theorem decodedInitialCertificateChoicePrefix_natList_false_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hnext : idx + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hFalse :
      E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
        tmVerifierCertificateRightReadChoices V falseSymbol) :
    E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext ∈
      tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  classical
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min idx (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_mainCell_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min idx (tmVerifierCertificateSizeBound V x) = idx := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  rcases tmVerifierNatListMainCellCNFAt_delimiter_of_false_atom V trueSymbol falseSymbol
      delimiterSymbol hCellCNF hFalse hAtom with
    ⟨delimiterChoice, hDelimiterChoice, hDelimiterAtom⟩
  let decodedNext := E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext
  have hDecodedNextMem :
      decodedNext ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hnext)
  have hDelimiterMem :
      delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hSelected :=
    E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnext
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hDelimiterAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx + 1))
        delimiterChoice).eval a = true := by
    simpa [hCellSucc] using hDelimiterAtom
  have hEq : decodedNext = delimiterChoice := by
    simpa [decodedNext] using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx + 1)) a hDomain
        hCell decodedNext delimiterChoice hDecodedNextMem hDelimiterMem hSelected
        hDelimiterAtom')
  simpa [decodedNext, hEq] using hDelimiterChoice

/-- A selected delimiter at `idx + 1` forces the previous decoded choice to be `false`. -/
theorem decodedInitialCertificateChoicePrefix_natList_delimiter_previous
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hnext : idx + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hDelimiter :
      E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext ∈
        tmVerifierCertificateRightReadChoices V delimiterSymbol) :
    E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
      tmVerifierCertificateRightReadChoices V falseSymbol := by
  classical
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hPrevCNF :
      CNF.Satisfies
        (tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_delimiterPrevious_satisfies V trueSymbol
      falseSymbol delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x) = idx + 1 := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + (idx + 1) := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx + 1) hnext
  rcases tmVerifierNatListDelimiterPreviousClausesAt_previous_of_atom_true V falseSymbol
      delimiterSymbol hPrevCNF hDelimiter hAtom with
    ⟨falseChoice, hFalseChoice, hFalseAtom⟩
  let decodedPrev := E.decodedInitialCertificateChoicePrefix[idx]'hidx
  have hDecodedPrevMem :
      decodedPrev ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hidx)
  have hFalseMem :
      falseChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    (tmVerifierCertificateRightReadChoices_spec V falseSymbol hFalseChoice).1
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length + idx ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hSelected :=
    E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  have hCellPred :
      (L.Instance.inputSize x + 1 +
          Nat.min (idx + 1) (tmVerifierCertificateSizeBound V x)) - 1 =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hFalseAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + idx) falseChoice).eval a =
        true := by
    simpa [hCellPred] using hFalseAtom
  have hEq : decodedPrev = falseChoice := by
    simpa [decodedPrev] using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length + idx) a hDomain hCell
        decodedPrev falseChoice hDecodedPrevMem hFalseMem hSelected hFalseAtom')
  simpa [decodedPrev, hEq] using hFalseChoice

/-- A delimiter cannot be immediately followed by another delimiter. -/
theorem decodedInitialCertificateChoicePrefix_natList_not_delimiter_after_delimiter
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hnext : idx + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hDelimiter :
      E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
        tmVerifierCertificateRightReadChoices V delimiterSymbol) :
    E.decodedInitialCertificateChoicePrefix[idx + 1]'hnext ∉
      tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  intro hNextDelimiter
  have hPrevFalse :=
    E.decodedInitialCertificateChoicePrefix_natList_delimiter_previous
      trueSymbol falseSymbol delimiterSymbol hSuffix hidx hnext hNextDelimiter
  have hEq :=
    tmVerifierCertificateRightReadChoices_symbol_eq_of_mem hPrevFalse hDelimiter
  exact hFalseDelimiter hEq

/-- A selected unary `true` cannot be the final certificate-window cell. -/
theorem decodedInitialCertificateChoicePrefix_natList_true_has_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hTrue :
      E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
        tmVerifierCertificateRightReadChoices V trueSymbol) :
    idx + 1 < E.decodedInitialCertificateChoicePrefix.length := by
  classical
  by_contra hnot
  have hBoundary : idx + 1 = E.decodedInitialCertificateChoicePrefix.length := by
    omega
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min idx (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_mainCell_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min idx (tmVerifierCertificateSizeBound V x) = idx := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  rcases tmVerifierNatListMainCellCNFAt_next_of_true_atom V trueSymbol falseSymbol
      delimiterSymbol hCellCNF hTrue hAtom with
    ⟨nextChoice, hNextChoice, hNextAtom⟩
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hNextMem :
      nextChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
    rcases List.mem_append.mp hNextChoice with hNextTrue | hNextFalse
    · exact (tmVerifierCertificateRightReadChoices_spec V trueSymbol hNextTrue).1
    · exact (tmVerifierCertificateRightReadChoices_spec V falseSymbol hNextFalse).1
  have hNextNonempty :
      nextChoice ≠
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    rcases List.mem_append.mp hNextChoice with hNextTrue | hNextFalse
    · exact tmVerifierCertificateRightReadChoices_ne_empty hNextTrue
    · exact tmVerifierCertificateRightReadChoices_ne_empty hNextFalse
  have hEmptyMem :
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) ∈
          tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hNextAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        nextChoice).eval a = true := by
    simpa [hCellSucc] using hNextAtom
  have hEmptyAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
    simpa [tmVerifierStackEmptyAtom, TMVerifierStackReadChoice.atomAt] using
      E.decodedInitialCertificateChoicePrefix_empty_after
  have hEq :
      nextChoice =
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    simpa using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length) a hDomain hCell
        nextChoice TMVerifierStackReadChoice.empty hNextMem hEmptyMem
        hNextAtom' hEmptyAtom)
  exact hNextNonempty hEq

/-- A selected unary `false` cannot be the final certificate-window cell. -/
theorem decodedInitialCertificateChoicePrefix_natList_false_has_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx < E.decodedInitialCertificateChoicePrefix.length)
    (hFalse :
      E.decodedInitialCertificateChoicePrefix[idx]'hidx ∈
        tmVerifierCertificateRightReadChoices V falseSymbol) :
    idx + 1 < E.decodedInitialCertificateChoicePrefix.length := by
  classical
  by_contra hnot
  have hBoundary : idx + 1 = E.decodedInitialCertificateChoicePrefix.length := by
    omega
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min idx (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierNatListSuffixPatternCNF_mainCell_satisfies V trueSymbol falseSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min idx (tmVerifierCertificateSizeBound V x) = idx := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx) hidx
  rcases tmVerifierNatListMainCellCNFAt_delimiter_of_false_atom V trueSymbol falseSymbol
      delimiterSymbol hCellCNF hFalse hAtom with
    ⟨delimiterChoice, hDelimiterChoice, hDelimiterAtom⟩
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hDelimiterMem :
      delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
  have hDelimiterNonempty :
      delimiterChoice ≠
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
    tmVerifierCertificateRightReadChoices_ne_empty hDelimiterChoice
  have hEmptyMem :
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) ∈
          tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min idx (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hDelimiterAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        delimiterChoice).eval a = true := by
    simpa [hCellSucc] using hDelimiterAtom
  have hEmptyAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
    simpa [tmVerifierStackEmptyAtom, TMVerifierStackReadChoice.atomAt] using
      E.decodedInitialCertificateChoicePrefix_empty_after
  have hEq :
      delimiterChoice =
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    simpa using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length) a hDomain hCell
        delimiterChoice TMVerifierStackReadChoice.empty hDelimiterMem hEmptyMem
        hDelimiterAtom' hEmptyAtom)
  exact hDelimiterNonempty hEq

mutual

/--
Every suffix of the decoded certificate choice window that starts at a list
boundary is accepted by the nat-list choice decoder.
-/
theorem decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode_drop
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {offset : Nat}
    (hoffset : offset ≤ E.decodedInitialCertificateChoicePrefix.length)
    (hBoundary :
      offset = 0 ∨
        ∃ prev : Nat,
          offset = prev + 1 ∧
            ∃ hprev : prev < E.decodedInitialCertificateChoicePrefix.length,
              E.decodedInitialCertificateChoicePrefix[prev]'hprev ∈
                tmVerifierCertificateRightReadChoices V delimiterSymbol) :
    ∃ xs : List Nat,
      tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol
        (E.decodedInitialCertificateChoicePrefix.drop offset) = some xs := by
  classical
  by_cases hEnd : offset = E.decodedInitialCertificateChoicePrefix.length
  · subst offset
    refine ⟨[], ?_⟩
    simp [tmVerifierNatListChoicePrefixDecode.eq_def]
  · have hidx : offset < E.decodedInitialCertificateChoicePrefix.length :=
      lt_of_le_of_ne hoffset hEnd
    let choice := E.decodedInitialCertificateChoicePrefix[offset]'hidx
    have hAllowed :
        choice = TMVerifierStackReadChoice.empty ∨
          choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol ∨
          choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol ∨
          choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
      have hAllowed0 :=
        E.decodedInitialCertificateChoicePrefix_natList_allowed_at
          trueSymbol falseSymbol delimiterSymbol hSuffix hidx
      simpa [choice] using hAllowed0
    have hNotDelimiter :
        choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
      rcases hBoundary with hZero | hPrev
      · subst offset
        simpa [choice] using
          E.decodedInitialCertificateChoicePrefix_natList_start_not_delimiter
            trueSymbol falseSymbol delimiterSymbol hSuffix hidx
      · rcases hPrev with ⟨prev, hoff, hprev, hPrevDelimiter⟩
        subst offset
        simpa [choice] using
          E.decodedInitialCertificateChoicePrefix_natList_not_delimiter_after_delimiter
            trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix hprev hidx
            hPrevDelimiter
    by_cases hEmpty :
        choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
    · refine ⟨[], ?_⟩
      rw [List.drop_eq_getElem_cons hidx]
      rw [tmVerifierNatListChoicePrefixDecode.eq_def]
      simp [choice, hEmpty]
    · by_cases hTrue :
        choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol
      · have hnext :
            offset + 1 < E.decodedInitialCertificateChoicePrefix.length := by
          simpa [choice] using
            E.decodedInitialCertificateChoicePrefix_natList_true_has_successor
              trueSymbol falseSymbol delimiterSymbol hSuffix hidx hTrue
        rcases E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecodeNat_drop
            trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
            (offset := offset + 1) (seen := 1) (by omega)
            ⟨offset, rfl, hidx, by simpa [choice] using hTrue⟩ with
          ⟨xs, hDecodeTail⟩
        refine ⟨xs, ?_⟩
        rw [List.drop_eq_getElem_cons hidx]
        rw [tmVerifierNatListChoicePrefixDecode.eq_def]
        simp [choice, hEmpty, hTrue, hDecodeTail]
      · by_cases hFalse :
          choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol
        · have hnext :
              offset + 1 < E.decodedInitialCertificateChoicePrefix.length := by
            simpa [choice] using
              E.decodedInitialCertificateChoicePrefix_natList_false_has_successor
                trueSymbol falseSymbol delimiterSymbol hSuffix hidx hFalse
          have hDelimiter :
              E.decodedInitialCertificateChoicePrefix[offset + 1]'hnext ∈
                tmVerifierCertificateRightReadChoices V delimiterSymbol := by
            simpa [choice] using
              E.decodedInitialCertificateChoicePrefix_natList_false_successor
                trueSymbol falseSymbol delimiterSymbol hSuffix hidx hnext hFalse
          rcases E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode_drop
              trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
              (offset := offset + 2) (by omega)
              (Or.inr ⟨offset + 1, by omega, hnext, hDelimiter⟩) with
            ⟨xs, hDecodeTail⟩
          refine ⟨0 :: xs, ?_⟩
          rw [List.drop_eq_getElem_cons hidx]
          rw [List.drop_eq_getElem_cons hnext]
          rw [tmVerifierNatListChoicePrefixDecode.eq_def]
          simp [choice, hEmpty, hTrue, hFalse, hDelimiter, hDecodeTail]
        · rcases hAllowed with hAllowedEmpty | hAllowedSymbol
          · exact False.elim (hEmpty hAllowedEmpty)
          · rcases hAllowedSymbol with hAllowedTrue | hAllowedRest
            · exact False.elim (hTrue hAllowedTrue)
            · rcases hAllowedRest with hAllowedFalse | hAllowedDelimiter
              · exact False.elim (hFalse hAllowedFalse)
              · exact False.elim (hNotDelimiter hAllowedDelimiter)
termination_by E.decodedInitialCertificateChoicePrefix.length - offset
decreasing_by all_goals omega

/--
Every suffix of the decoded certificate choice window that starts immediately
after a unary `true` is accepted by the nat-run decoder.
-/
theorem decodedInitialCertificateChoicePrefix_natListChoicePrefixDecodeNat_drop
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a)
    {offset seen : Nat}
    (hoffset : offset ≤ E.decodedInitialCertificateChoicePrefix.length)
    (hPrevTrue :
      ∃ prev : Nat,
        offset = prev + 1 ∧
          ∃ hprev : prev < E.decodedInitialCertificateChoicePrefix.length,
            E.decodedInitialCertificateChoicePrefix[prev]'hprev ∈
              tmVerifierCertificateRightReadChoices V trueSymbol) :
    ∃ xs : List Nat,
      tmVerifierNatListChoicePrefixDecodeNat V trueSymbol falseSymbol delimiterSymbol seen
        (E.decodedInitialCertificateChoicePrefix.drop offset) = some xs := by
  classical
  rcases hPrevTrue with ⟨prev, hoff, hprev, hPrevTrue⟩
  subst offset
  have hidx : prev + 1 < E.decodedInitialCertificateChoicePrefix.length := by
    simpa using
      E.decodedInitialCertificateChoicePrefix_natList_true_has_successor
        trueSymbol falseSymbol delimiterSymbol hSuffix hprev hPrevTrue
  let choice := E.decodedInitialCertificateChoicePrefix[prev + 1]'hidx
  have hCurrent :
      choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol ++
        tmVerifierCertificateRightReadChoices V falseSymbol := by
    have hCurrent0 :=
      E.decodedInitialCertificateChoicePrefix_natList_true_successor
        trueSymbol falseSymbol delimiterSymbol hSuffix hprev hidx hPrevTrue
    simpa [choice] using hCurrent0
  by_cases hTrue :
      choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol
  · have hNotEmpty :
        choice ≠
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
      tmVerifierCertificateRightReadChoices_ne_empty hTrue
    rcases E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecodeNat_drop
        trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
        (offset := prev + 2) (seen := seen + 1) (by omega)
        ⟨prev + 1, by omega, hidx, by simpa [choice] using hTrue⟩ with
      ⟨xs, hDecodeTail⟩
    refine ⟨xs, ?_⟩
    rw [List.drop_eq_getElem_cons hidx]
    rw [tmVerifierNatListChoicePrefixDecodeNat.eq_def]
    simp [choice, hNotEmpty, hTrue, hDecodeTail]
  · have hFalse :
        choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol := by
      rcases List.mem_append.mp hCurrent with hCurrentTrue | hCurrentFalse
      · exact False.elim (hTrue hCurrentTrue)
      · exact hCurrentFalse
    have hNotEmpty :
        choice ≠
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
      tmVerifierCertificateRightReadChoices_ne_empty hFalse
    have hnext :
        prev + 2 < E.decodedInitialCertificateChoicePrefix.length := by
      simpa [choice] using
        E.decodedInitialCertificateChoicePrefix_natList_false_has_successor
          trueSymbol falseSymbol delimiterSymbol hSuffix hidx hFalse
    have hDelimiter :
        E.decodedInitialCertificateChoicePrefix[prev + 2]'hnext ∈
          tmVerifierCertificateRightReadChoices V delimiterSymbol := by
      simpa [choice] using
        E.decodedInitialCertificateChoicePrefix_natList_false_successor
          trueSymbol falseSymbol delimiterSymbol hSuffix hidx hnext hFalse
    rcases E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode_drop
        trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
        (offset := prev + 3) (by omega)
        (Or.inr ⟨prev + 2, by omega, hnext, hDelimiter⟩) with
      ⟨xs, hDecodeTail⟩
    refine ⟨seen :: xs, ?_⟩
    rw [List.drop_eq_getElem_cons hidx]
    rw [List.drop_eq_getElem_cons hnext]
    rw [tmVerifierNatListChoicePrefixDecodeNat.eq_def]
    simp [choice, hNotEmpty, hTrue, hFalse, hDelimiter, hDecodeTail]
termination_by E.decodedInitialCertificateChoicePrefix.length - offset
decreasing_by all_goals omega

end

/-- The whole decoded certificate choice window is accepted by the nat-list decoder. -/
theorem decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a) :
    ∃ xs : List Nat,
      tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol
        E.decodedInitialCertificateChoicePrefix = some xs := by
  simpa using
    E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode_drop
      trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
      (offset := 0) (by omega) (Or.inl rfl)

/--
The assignment-level decoded suffix word has the certificate-symbol stream
returned by the nat-list choice decoder.
-/
theorem decodedInitialCertificateSuffixWord_natListDecode_symbols
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) a) :
    ∃ xs : List Nat,
      tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol
          E.decodedInitialCertificateChoicePrefix = some xs ∧
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierNatListCertificateSymbols trueSymbol falseSymbol delimiterSymbol xs).map
            (tmVerifierInputRightSymbol (V := V)) := by
  rcases E.decodedInitialCertificateChoicePrefix_natListChoicePrefixDecode
      trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix with
    ⟨xs, hDecode⟩
  refine ⟨xs, hDecode, ?_⟩
  have hSymbols :=
    tmVerifierNatListChoicePrefixDecode_sound_symbols V trueSymbol falseSymbol
      delimiterSymbol hDecode
  have hWord :
      tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
        E.decodedInitialCertificateSuffixWord := by
    simpa [tmVerifierXOnlyInputChoicePrefixWord] using
      E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  rw [← hWord]
  exact hSymbols

end TMVerifierXOnlyGlobalTableauEvidence

/--
Build a checked suffix-decoder package from the unary nat-list suffix-pattern
CNF and an encoded suffix decoder for the verifier certificate encoding.

The `validSuffixSeed_satisfies` premise is the local completeness direction for
the concrete certificate encoding; the decoded-suffix soundness direction is
proved here from the checked CNF.
-/
noncomputable def tmVerifierNatListCheckedSuffixDecoder
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat → V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier → List Nat)
    (certOfNats_suffix_eq :
      ∀ xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (_cert_suffix_eq :
      ∀ c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V)))
    (validSuffixSeed_satisfies :
      {B : TMVerifierPushPayloadBoundary V} →
        {x : L.Instance.Carrier} →
          {a : Assignment} →
            TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a →
              CNF.Satisfies
                (tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol
                  delimiterSymbol x) a) :
    TMVerifierXOnlyCheckedSuffixDecoder V where
  decoder := D
  suffixValidityCNF := tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol
    delimiterSymbol
  suffixValidityCNF_tm_polytime :=
    tmVerifierNatListSuffixPatternCNF_tm_polytime V trueSymbol falseSymbol delimiterSymbol
  validSuffixSeed_satisfies := by
    intro B x a w
    exact validSuffixSeed_satisfies w
  decodedSuffix_decode_of_satisfies := by
    intro B x a E hSuffix
    let hDecoded :=
      E.decodedInitialCertificateSuffixWord_natListDecode_symbols
        trueSymbol falseSymbol delimiterSymbol hFalseDelimiter hSuffix
    let xs : List Nat := Classical.choose hDecoded
    have hDecodedSpec := Classical.choose_spec hDecoded
    have hSymbols := hDecodedSpec.2
    have hEncodedSuffix :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) := by
      rw [hSymbols, certOfNats_suffix_eq xs]
    have hLen :
        V.Cert.inputSize (certOfNats xs) =
          E.decodedInitialCertificateSuffixWord.length := by
      have hLen' := congrArg List.length hEncodedSuffix
      calc
        V.Cert.inputSize (certOfNats xs) =
            (tmVerifierCertificateInputSuffixEncoded V (certOfNats xs)).length := by
              rw [tmVerifierCertificateInputSuffixEncoded_length]
        _ = (E.decodedInitialCertificateSuffixWord.map
              (tmVerifierComputableWitness V).inputAlphabet).length := by
              exact hLen'.symm
        _ = E.decodedInitialCertificateSuffixWord.length := by
              simp
    have hSize :
        V.Cert.inputSize (certOfNats xs) ≤ tmVerifierCertificateSizeBound V x := by
      rw [hLen]
      exact E.decodedInitialCertificateSuffixWord_length_le_certificateSizeBound
    refine ⟨certOfNats xs, ?_⟩
    rw [hEncodedSuffix]
    exact D.decode_complete hSize

end SAT
end ComplexityReduction
