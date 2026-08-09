/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackDecoder
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauIOStacks

/-!
Initial and endpoint stack decoding for x-only Cook-Levin tableaux.

These lemmas intentionally stop short of decoding the arbitrary certificate
suffix on the input stack as a typed `TMVerifier.Cert`.  They expose the checked
facts already enforced by the x-only CNF: the instance prefix, bounded empty
tail, empty non-input stacks, and the true output endpoint.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Initial input-stack decoding -/

theorem tmVerifierInstanceInputPrefixWord_length_le_xOnlyCellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    (tmVerifierInstanceInputPrefixWord V x).length ≤ tmVerifierXOnlyCellBound V x := by
  simp [tmVerifierXOnlyCellBound, tmVerifierXOnlyInputLengthBound]
  omega

theorem tmVerifierXOnlyInputLengthBound_le_cellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    tmVerifierXOnlyInputLengthBound V x ≤ tmVerifierXOnlyCellBound V x := by
  simp [tmVerifierXOnlyCellBound]
  omega

theorem tmVerifierBoolOutputWord_length_le_xOnlyCellBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    (tmVerifierBoolOutputWord V true).length ≤ tmVerifierXOnlyCellBound V x := by
  simp [tmVerifierXOnlyCellBound]
  omega

theorem tmVerifierXOnlyDecodedInputStackChoicePrefix_prefix_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (hInitial : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    (hDomain :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x 0 (tmVerifierTM V).k₀) a)
    {i : Nat} (hi : i < (tmVerifierInstanceInputPrefixWord V x).length) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)[i]? =
      some
        (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            (tmVerifierInstanceInputPrefixWord V x)[i])
          (tmVerifierInstanceInputPrefixWord V x)[i]) := by
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ i a hDomain
      (by
        simp [tmVerifierXOnlyCellRange]
        have hPrefix := tmVerifierInstanceInputPrefixWord_length_le_xOnlyCellBound V x
        omega)
  have hChoice :
      d.choice =
        TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            (tmVerifierInstanceInputPrefixWord V x)[i])
          (tmVerifierInstanceInputPrefixWord V x)[i] := by
    exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
      (tmVerifierTM V).k₀ i a hDomain
      (by
        simp [tmVerifierXOnlyCellRange]
        have hPrefix := tmVerifierInstanceInputPrefixWord_length_le_xOnlyCellBound V x
        omega)
      d.choice
      (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
        (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
          (tmVerifierInstanceInputPrefixWord V x)[i])
        (tmVerifierInstanceInputPrefixWord V x)[i])
      d.choice_mem
      (tmVerifierInputStackSymbol_choice_mem V (tmVerifierInstanceInputPrefixWord V x)[i])
      d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt, tmVerifierInputStackSymbolAtom] using
          tmVerifierXOnlyInitialStackCNF_satisfies_input_prefix_symbol V x a hInitial hi)
  rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀ a
    hDomain i
    (by
      simp [tmVerifierXOnlyCellRange]
      have hPrefix := tmVerifierInstanceInputPrefixWord_length_le_xOnlyCellBound V x
      omega)]
  simp [d, hChoice]

theorem tmVerifierXOnlyDecodedInputStackChoicePrefix_empty_at_inputBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (hInitial : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    (hDomain :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x 0 (tmVerifierTM V).k₀) a) :
    ((tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)[
        tmVerifierXOnlyInputLengthBound V x]?) =
      some (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  let cell := tmVerifierXOnlyInputLengthBound V x
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ cell a hDomain
      (by
        simp [tmVerifierXOnlyCellRange, cell]
        exact tmVerifierXOnlyInputLengthBound_le_cellBound V x)
  have hChoice :
      d.choice =
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
      (tmVerifierTM V).k₀ cell a hDomain
      (by
        simp [tmVerifierXOnlyCellRange, cell]
        exact tmVerifierXOnlyInputLengthBound_le_cellBound V x)
      d.choice TMVerifierStackReadChoice.empty d.choice_mem
      (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt, cell] using
          tmVerifierXOnlyInitialStackCNF_satisfies_input_empty_tail V x a hInitial
            (hcell := by
              simp [tmVerifierXOnlyCellRange]
              exact tmVerifierXOnlyInputLengthBound_le_cellBound V x)
            (hTail := le_rfl))
  rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀ a
    hDomain cell
    (by
      simp [tmVerifierXOnlyCellRange, cell]
      exact tmVerifierXOnlyInputLengthBound_le_cellBound V x)]
  simp [d, hChoice, cell]

theorem tmVerifierXOnlyDecodedStackList_initial_noninput_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (hInitial : CNF.Satisfies (tmVerifierXOnlyInitialStackCNF V x) a)
    (k : tmVerifierStackIndex V) (hk : k ≠ (tmVerifierTM V).k₀)
    (hDomain : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x 0 k) a) :
    tmVerifierXOnlyDecodedStackList V x 0 k a hDomain = [] := by
  unfold tmVerifierXOnlyDecodedStackList
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x 0 k 0 a hDomain
      (tmVerifierXOnlyCellRange_zero_mem V x)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0 k 0 a hDomain
      (tmVerifierXOnlyCellRange_zero_mem V x) d.choice TMVerifierStackReadChoice.empty
      d.choice_mem (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierXOnlyInitialStackCNF_satisfies_noninput_empty V x a hInitial hk
            (tmVerifierXOnlyCellRange_zero_mem V x))
  simp [tmVerifierXOnlyDecodedStackChoicePrefix, d, hChoice]

/-! ### Endpoint output-true stack decoding -/

theorem tmVerifierXOnlyOutputTrueCNFAt_satisfies_output_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a)
    {i : Nat} (hi : i < (tmVerifierBoolOutputWord V true).length) :
    (tmVerifierOutputStackSymbolAtom V t i (tmVerifierBoolOutputWord V true)[i]).eval
      a = true := by
  have hUnit := (tmVerifierXOnlyOutputTrueCNFAt_satisfies V x t a).1 h |>.1
  exact hUnit _ (by
    rw [tmVerifierOutputTrueSymbolLiteralsAt]
    apply List.mem_append_left
    apply List.mem_map.mpr
    let hzip : i < (tmVerifierBoolOutputWord V true).zipIdx.length := by simp [hi]
    refine ⟨(tmVerifierBoolOutputWord V true).zipIdx[i], ?_, ?_⟩
    · exact List.getElem_mem (l := (tmVerifierBoolOutputWord V true).zipIdx) (n := i)
        hzip
    · rw [List.getElem_zipIdx]
      simp)

theorem tmVerifierXOnlyOutputTrueCNFAt_satisfies_output_empty_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a) :
    (tmVerifierStackEmptyAtom V t (tmVerifierTM V).k₁
        (tmVerifierBoolOutputWord V true).length).eval a = true := by
  have hUnit := (tmVerifierXOnlyOutputTrueCNFAt_satisfies V x t a).1 h |>.1
  exact hUnit _ (by
    apply List.mem_append_right
    rw [tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt]
    apply List.mem_map.mpr
    refine ⟨(tmVerifierBoolOutputWord V true).length, ?_, rfl⟩
    simp [tmVerifierXOnlyCellRange, tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x])

theorem tmVerifierXOnlyOutputTrueCNFAt_satisfies_nonoutput_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a)
    {k : tmVerifierStackIndex V} (hk : k ≠ (tmVerifierTM V).k₁)
    {cell : Nat} (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    (tmVerifierStackEmptyAtom V t k cell).eval a = true := by
  have hUnit := (tmVerifierXOnlyOutputTrueCNFAt_satisfies V x t a).1 h |>.2
  exact hUnit _ (by
    rw [tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt]
    rw [List.mem_flatMap]
    refine ⟨k, ?_, ?_⟩
    · simp [tmVerifierNonOutputStacks, hk]
    · apply List.mem_map.mpr
      exact ⟨cell, hcell, rfl⟩)

theorem tmVerifierXOnlyDecodedStackList_output_true_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (hOutput : CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a)
    (hDomain :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t (tmVerifierTM V).k₁) a) :
    tmVerifierXOnlyDecodedStackList V x t (tmVerifierTM V).k₁ a hDomain =
      tmVerifierBoolOutputWord V true := by
  unfold tmVerifierXOnlyDecodedStackList
  apply tmVerifierReadChoicePrefixToStack_eq_of_symbols_empty
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)
  · intro i hi
    let d :=
      tmVerifierXOnlyDecodedStackCellOf V x t (tmVerifierTM V).k₁ i a hDomain
        (by
          simp [tmVerifierXOnlyCellRange]
          have hOutputLen := tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x
          omega)
    have hChoice :
        d.choice =
          TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₁)
            (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁
              (tmVerifierBoolOutputWord V true)[i])
            (tmVerifierBoolOutputWord V true)[i] := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t
        (tmVerifierTM V).k₁ i a hDomain
        (by
          simp [tmVerifierXOnlyCellRange]
          have hOutputLen := tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x
          omega)
        d.choice
        (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₁)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁
            (tmVerifierBoolOutputWord V true)[i])
          (tmVerifierBoolOutputWord V true)[i])
        d.choice_mem
        (tmVerifierOutputStackSymbol_choice_mem V (tmVerifierBoolOutputWord V true)[i])
        d.atom_true
        (by
          simpa [TMVerifierStackReadChoice.atomAt, tmVerifierOutputStackSymbolAtom] using
            tmVerifierXOnlyOutputTrueCNFAt_satisfies_output_symbol V x t a hOutput hi)
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x t (tmVerifierTM V).k₁ a
      hDomain i
      (by
        simp [tmVerifierXOnlyCellRange]
        have hOutputLen := tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x
        omega)]
    simp [d, hChoice]
  · let d :=
      tmVerifierXOnlyDecodedStackCellOf V x t (tmVerifierTM V).k₁
        (tmVerifierBoolOutputWord V true).length a hDomain
        (by
          simp [tmVerifierXOnlyCellRange]
          exact tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x)
    have hChoice :
        d.choice =
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₁) := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t
        (tmVerifierTM V).k₁ (tmVerifierBoolOutputWord V true).length a hDomain
        (by
          simp [tmVerifierXOnlyCellRange]
          exact tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x)
        d.choice TMVerifierStackReadChoice.empty d.choice_mem
        (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₁) d.atom_true
        (by
          simpa [TMVerifierStackReadChoice.atomAt] using
            tmVerifierXOnlyOutputTrueCNFAt_satisfies_output_empty_tail V x t a hOutput)
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x t (tmVerifierTM V).k₁ a
      hDomain (tmVerifierBoolOutputWord V true).length
      (by
        simp [tmVerifierXOnlyCellRange]
        exact tmVerifierBoolOutputWord_length_le_xOnlyCellBound V x)]
    simp [d, hChoice]

theorem tmVerifierXOnlyDecodedStackList_output_true_nonoutput_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (a : Assignment)
    (hOutput : CNF.Satisfies (tmVerifierXOnlyOutputTrueCNFAt V x t) a)
    (k : tmVerifierStackIndex V) (hk : k ≠ (tmVerifierTM V).k₁)
    (hDomain : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    tmVerifierXOnlyDecodedStackList V x t k a hDomain = [] := by
  unfold tmVerifierXOnlyDecodedStackList
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x t k 0 a hDomain
      (tmVerifierXOnlyCellRange_zero_mem V x)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t k 0 a hDomain
      (tmVerifierXOnlyCellRange_zero_mem V x) d.choice TMVerifierStackReadChoice.empty
      d.choice_mem (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierXOnlyOutputTrueCNFAt_satisfies_nonoutput_empty V x t a hOutput hk
            (tmVerifierXOnlyCellRange_zero_mem V x))
  simp [tmVerifierXOnlyDecodedStackChoicePrefix, d, hChoice]

end SAT
end ComplexityReduction
