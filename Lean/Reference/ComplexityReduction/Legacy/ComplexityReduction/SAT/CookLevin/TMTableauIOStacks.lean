/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauMacroSteps

/-!
Initial and endpoint stack decoding for aggregate Cook-Levin tableaux.

The stack I/O CNF blocks force concrete input and output words by unit clauses.
This file connects those clauses to the decoded stack-list projection used by
macro tableau configurations.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Local list/choice helpers -/

theorem tmVerifierReadChoicePrefixToStack_eq_of_symbols_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L} {k : tmVerifierStackIndex V}
    (payload : (tmVerifierTM V).Γ k → Nat)
    (word : List ((tmVerifierTM V).Γ k))
    (choices : List (TMVerifierStackReadChoice V k))
    (hSymbols :
      ∀ i, (hi : i < word.length) →
        choices[i]? = some
          (TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload word[i]) word[i]))
    (hEmpty :
      choices[word.length]? = some
        (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack choices = word := by
  induction word generalizing choices with
  | nil =>
      cases choices with
      | nil => simp at hEmpty
      | cons choice rest =>
          cases choice <;> simp [tmVerifierReadChoicePrefixToStack] at hEmpty ⊢
  | cons head tail ih =>
      cases choices with
      | nil =>
          have h0 := hSymbols 0 (by simp)
          simp at h0
      | cons choice rest =>
          have h0 := hSymbols 0 (by simp)
          cases choice with
          | empty => simp at h0
          | symbol pl s =>
              simp at h0
              rcases h0 with ⟨_hPayload, hSymbol⟩
              subst s
              simp [tmVerifierReadChoicePrefixToStack]
              apply ih
              · intro i hi
                have hSym := hSymbols (i + 1) (by simp [hi])
                simpa using hSym
              · simpa using hEmpty

theorem tmVerifierDecodedStackChoicePrefix_getElem?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (cell : Nat) (hcell : cell ∈ tmVerifierCellRange V p) :
    (tmVerifierDecodedStackChoicePrefix V p t k a h)[cell]? =
      some ((tmVerifierDecodedStackCellOf V p t k cell a h hcell).choice) := by
  cases cell with
  | zero =>
      simp [tmVerifierDecodedStackChoicePrefix]
  | succ i =>
      have hi : i < tmVerifierCellBound V p := by
        simp [tmVerifierCellRange, List.mem_range] at hcell
        omega
      rw [tmVerifierDecodedStackChoicePrefix]
      rw [List.getElem?_cons_succ]
      rw [List.getElem?_map]
      have hLen : i < (tmVerifierCellSuccessorRange V p).attach.length := by
        simp [tmVerifierCellSuccessorRange, hi]
      rw [List.getElem?_eq_getElem hLen]
      rw [List.getElem_attach]
      simp [tmVerifierCellSuccessorRange]

theorem tmVerifierInputStackSymbol_choice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) :
    TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
        (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s) s ∈
      tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
  tmVerifierActiveStackSymbolPayload_mem V (tmVerifierTM V).k₀ s
    (tmVerifierStackSymbolActive_input V s)

theorem tmVerifierOutputStackSymbol_choice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) :
    TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₁)
        (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s) s ∈
      tmVerifierStackReadChoices V (tmVerifierTM V).k₁ :=
  tmVerifierActiveStackSymbolPayload_mem V (tmVerifierTM V).k₁ s
    (tmVerifierStackSymbolActive_output V s)

/-! ### Initial stack decoding -/

theorem tmVerifierInitialStackCNF_satisfies_input_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialStackCNF V p) a)
    {i : Nat} (hi : i < (tmVerifierInputWord V p).length) :
    (tmVerifierInputStackSymbolAtom V 0 i (tmVerifierInputWord V p)[i]).eval a = true := by
  have hUnit := (tmVerifierInitialStackCNF_satisfies V p a).1 h |>.1
  exact hUnit _ (by
    rw [tmVerifierInputStackSymbolLiterals]
    apply List.mem_append_left
    apply List.mem_map.mpr
    let hzip : i < (tmVerifierInputWord V p).zipIdx.length := by simp [hi]
    refine ⟨(tmVerifierInputWord V p).zipIdx[i], ?_, ?_⟩
    · exact List.getElem_mem (l := (tmVerifierInputWord V p).zipIdx) (n := i) hzip
    · rw [List.getElem_zipIdx]
      simp)

theorem tmVerifierInitialStackCNF_satisfies_input_empty_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialStackCNF V p) a) :
    (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀
        (tmVerifierInputWord V p).length).eval a = true := by
  have hUnit := (tmVerifierInitialStackCNF_satisfies V p a).1 h |>.1
  exact hUnit _ (by
    apply List.mem_append_right
    rw [tmVerifierInputStackEmptyTailLiterals]
    apply List.mem_map.mpr
    refine ⟨(tmVerifierInputWord V p).length, ?_, rfl⟩
    simp [tmVerifierTailCells, tmVerifierCellRange, tmVerifierCellBound]
    omega)

theorem tmVerifierInitialStackCNF_satisfies_noninput_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialStackCNF V p) a)
    {k : tmVerifierStackIndex V} (hk : k ≠ (tmVerifierTM V).k₀)
    {cell : Nat} (hcell : cell ∈ tmVerifierCellRange V p) :
    (tmVerifierStackEmptyAtom V 0 k cell).eval a = true := by
  have hUnit := (tmVerifierInitialStackCNF_satisfies V p a).1 h |>.2
  exact hUnit _ (by
    rw [tmVerifierInitialNonInputEmptyLiterals]
    rw [List.mem_flatMap]
    refine ⟨k, ?_, ?_⟩
    · simp [tmVerifierNonInputStacks, hk]
    · apply List.mem_map.mpr
      exact ⟨cell, hcell, rfl⟩)

theorem tmVerifierDecodedStackList_initial_input_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (hInitial : CNF.Satisfies (tmVerifierInitialStackCNF V p) a)
    (hDomain :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p 0 (tmVerifierTM V).k₀) a) :
    tmVerifierDecodedStackList V p 0 (tmVerifierTM V).k₀ a hDomain =
      tmVerifierInputWord V p := by
  unfold tmVerifierDecodedStackList
  apply tmVerifierReadChoicePrefixToStack_eq_of_symbols_empty
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)
  · intro i hi
    let d :=
      tmVerifierDecodedStackCellOf V p 0 (tmVerifierTM V).k₀ i a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
    have hChoice :
        d.choice =
          TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
            (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
              (tmVerifierInputWord V p)[i])
            (tmVerifierInputWord V p)[i] := by
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p 0 (tmVerifierTM V).k₀ i
        a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
        d.choice
        (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            (tmVerifierInputWord V p)[i])
          (tmVerifierInputWord V p)[i])
        d.choice_mem
        (tmVerifierInputStackSymbol_choice_mem V (tmVerifierInputWord V p)[i])
        d.atom_true
        (by
          simpa [TMVerifierStackReadChoice.atomAt, tmVerifierInputStackSymbolAtom] using
            tmVerifierInitialStackCNF_satisfies_input_symbol V p a hInitial hi)
    rw [tmVerifierDecodedStackChoicePrefix_getElem? V p 0 (tmVerifierTM V).k₀ a hDomain i
      (by
        simp [tmVerifierCellRange, tmVerifierCellBound]
        omega)]
    simp [d, hChoice]
  · let d :=
      tmVerifierDecodedStackCellOf V p 0 (tmVerifierTM V).k₀
        (tmVerifierInputWord V p).length a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
    have hChoice :
        d.choice =
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p 0 (tmVerifierTM V).k₀
        (tmVerifierInputWord V p).length a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
        d.choice TMVerifierStackReadChoice.empty d.choice_mem
        (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) d.atom_true
        (by
          simpa [TMVerifierStackReadChoice.atomAt] using
            tmVerifierInitialStackCNF_satisfies_input_empty_tail V p a hInitial)
    rw [tmVerifierDecodedStackChoicePrefix_getElem? V p 0 (tmVerifierTM V).k₀ a hDomain
      (tmVerifierInputWord V p).length
      (by
        simp [tmVerifierCellRange, tmVerifierCellBound]
        omega)]
    simp [d, hChoice]

theorem tmVerifierDecodedStackList_initial_noninput_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment)
    (hInitial : CNF.Satisfies (tmVerifierInitialStackCNF V p) a)
    (k : tmVerifierStackIndex V) (hk : k ≠ (tmVerifierTM V).k₀)
    (hDomain : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p 0 k) a) :
    tmVerifierDecodedStackList V p 0 k a hDomain = [] := by
  unfold tmVerifierDecodedStackList
  let d := tmVerifierDecodedStackCellOf V p 0 k 0 a hDomain (tmVerifierCellRange_zero_mem V p)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p 0 k 0 a hDomain
      (tmVerifierCellRange_zero_mem V p) d.choice TMVerifierStackReadChoice.empty d.choice_mem
      (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierInitialStackCNF_satisfies_noninput_empty V p a hInitial hk
            (tmVerifierCellRange_zero_mem V p))
  simp [tmVerifierDecodedStackChoicePrefix, d, hChoice]

theorem TMVerifierFixedPairTableauEvidence.decodedCfg_initial
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
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

/-! ### Endpoint output-true stack decoding -/

theorem tmVerifierOutputTrueCNFAt_satisfies_output_symbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a)
    {i : Nat} (hi : i < (tmVerifierBoolOutputWord V true).length) :
    (tmVerifierOutputStackSymbolAtom V t i (tmVerifierBoolOutputWord V true)[i]).eval
      a = true := by
  have hUnit := (tmVerifierOutputTrueCNFAt_satisfies V p t a).1 h |>.1
  exact hUnit _ (by
    rw [tmVerifierOutputTrueSymbolLiteralsAt]
    apply List.mem_append_left
    apply List.mem_map.mpr
    let hzip : i < (tmVerifierBoolOutputWord V true).zipIdx.length := by simp [hi]
    refine ⟨(tmVerifierBoolOutputWord V true).zipIdx[i], ?_, ?_⟩
    · exact List.getElem_mem (l := (tmVerifierBoolOutputWord V true).zipIdx) (n := i) hzip
    · rw [List.getElem_zipIdx]
      simp)

theorem tmVerifierOutputTrueCNFAt_satisfies_output_empty_tail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a) :
    (tmVerifierStackEmptyAtom V t (tmVerifierTM V).k₁
        (tmVerifierBoolOutputWord V true).length).eval a = true := by
  have hUnit := (tmVerifierOutputTrueCNFAt_satisfies V p t a).1 h |>.1
  exact hUnit _ (by
    apply List.mem_append_right
    rw [tmVerifierOutputTrueEmptyTailLiteralsAt]
    apply List.mem_map.mpr
    refine ⟨(tmVerifierBoolOutputWord V true).length, ?_, rfl⟩
    simp [tmVerifierTailCells, tmVerifierCellRange, tmVerifierCellBound]
    omega)

theorem tmVerifierOutputTrueCNFAt_satisfies_nonoutput_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a)
    {k : tmVerifierStackIndex V} (hk : k ≠ (tmVerifierTM V).k₁)
    {cell : Nat} (hcell : cell ∈ tmVerifierCellRange V p) :
    (tmVerifierStackEmptyAtom V t k cell).eval a = true := by
  have hUnit := (tmVerifierOutputTrueCNFAt_satisfies V p t a).1 h |>.2
  exact hUnit _ (by
    rw [tmVerifierOutputTrueNonOutputEmptyLiteralsAt]
    rw [List.mem_flatMap]
    refine ⟨k, ?_, ?_⟩
    · simp [tmVerifierNonOutputStacks, hk]
    · apply List.mem_map.mpr
      exact ⟨cell, hcell, rfl⟩)

theorem tmVerifierDecodedStackList_output_true_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (hOutput : CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a)
    (hDomain :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t (tmVerifierTM V).k₁) a) :
    tmVerifierDecodedStackList V p t (tmVerifierTM V).k₁ a hDomain =
      tmVerifierBoolOutputWord V true := by
  unfold tmVerifierDecodedStackList
  apply tmVerifierReadChoicePrefixToStack_eq_of_symbols_empty
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)
  · intro i hi
    let d :=
      tmVerifierDecodedStackCellOf V p t (tmVerifierTM V).k₁ i a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
    have hChoice :
        d.choice =
          TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₁)
            (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁
              (tmVerifierBoolOutputWord V true)[i])
            (tmVerifierBoolOutputWord V true)[i] := by
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t (tmVerifierTM V).k₁ i
        a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
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
            tmVerifierOutputTrueCNFAt_satisfies_output_symbol V p t a hOutput hi)
    rw [tmVerifierDecodedStackChoicePrefix_getElem? V p t (tmVerifierTM V).k₁ a hDomain i
      (by
        simp [tmVerifierCellRange, tmVerifierCellBound]
        omega)]
    simp [d, hChoice]
  · let d :=
      tmVerifierDecodedStackCellOf V p t (tmVerifierTM V).k₁
        (tmVerifierBoolOutputWord V true).length a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
    have hChoice :
        d.choice =
          (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₁) := by
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t (tmVerifierTM V).k₁
        (tmVerifierBoolOutputWord V true).length a hDomain
        (by
          simp [tmVerifierCellRange, tmVerifierCellBound]
          omega)
        d.choice TMVerifierStackReadChoice.empty d.choice_mem
        (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₁) d.atom_true
        (by
          simpa [TMVerifierStackReadChoice.atomAt] using
            tmVerifierOutputTrueCNFAt_satisfies_output_empty_tail V p t a hOutput)
    rw [tmVerifierDecodedStackChoicePrefix_getElem? V p t (tmVerifierTM V).k₁ a hDomain
      (tmVerifierBoolOutputWord V true).length
      (by
        simp [tmVerifierCellRange, tmVerifierCellBound]
        omega)]
    simp [d, hChoice]

theorem tmVerifierDecodedStackList_output_true_nonoutput_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) (a : Assignment)
    (hOutput : CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a)
    (k : tmVerifierStackIndex V) (hk : k ≠ (tmVerifierTM V).k₁)
    (hDomain : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    tmVerifierDecodedStackList V p t k a hDomain = [] := by
  unfold tmVerifierDecodedStackList
  let d := tmVerifierDecodedStackCellOf V p t k 0 a hDomain (tmVerifierCellRange_zero_mem V p)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p t k 0 a hDomain
      (tmVerifierCellRange_zero_mem V p) d.choice TMVerifierStackReadChoice.empty d.choice_mem
      (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierOutputTrueCNFAt_satisfies_nonoutput_empty V p t a hOutput hk
            (tmVerifierCellRange_zero_mem V p))
  simp [tmVerifierDecodedStackChoicePrefix, d, hChoice]

theorem TMVerifierFixedPairTableauEvidence.decodedCfg_endpoint_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
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

namespace TMVerifierXOnlyTableauSeed

theorem decodedCfg_initial
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    wSeed.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V (x, wSeed.cert)) =
      tmVerifierInitialCfg V (x, wSeed.cert) :=
  wSeed.fixedPairEvidence.decodedCfg_initial

theorem decodedCfg_endpoint_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    wSeed.decodedCfg (tmVerifierTimeBound V (x, wSeed.cert))
        (tmVerifierTableauTimeRange_timeBound_mem V (x, wSeed.cert)) =
      tmVerifierOutputCfg V true :=
  wSeed.fixedPairEvidence.decodedCfg_endpoint_true

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
