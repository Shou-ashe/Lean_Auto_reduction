/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackActionSemantics
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackDecoder

/-!
Decoded x-only stack-list effects of primitive stack actions.

This file lifts x-only primitive action CNF consequences from atom propagation
to canonical decoded prefixes and concrete stack lists.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Well-formed x-only stack prefixes -/

theorem tmVerifierXOnlyStackWellFormedCNFAt_satisfies_emptyTail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a) :
    CNF.Satisfies (tmVerifierXOnlyStackEmptyTailCNFAt V x t k) a := by
  have hPair :
      CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x t k ++
            tmVerifierXOnlyStackEmptyTailCNFAt V x t k) a ∧
        CNF.Satisfies (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) a := by
    exact (CNF.satisfies_append
      (tmVerifierXOnlyStackCellDomainsCNFAt V x t k ++
        tmVerifierXOnlyStackEmptyTailCNFAt V x t k)
      (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) a).1
        (by simpa [tmVerifierXOnlyStackWellFormedCNFAt] using h)
  exact (CNF.satisfies_append
    (tmVerifierXOnlyStackCellDomainsCNFAt V x t k)
    (tmVerifierXOnlyStackEmptyTailCNFAt V x t k) a).1 hPair.1 |>.2

theorem tmVerifierXOnlyStackWellFormedCNFAt_satisfies_empty_successor
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x)
    (hEmpty : (tmVerifierStackEmptyAtom V t k cell).eval a = true) :
    (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  exact tmVerifierXOnlyStackEmptyTailCNFAt_satisfies_successor V x t k cell a
    (tmVerifierXOnlyStackWellFormedCNFAt_satisfies_emptyTail V x t k a h) hcell hEmpty

private theorem xOnlyRangeAttachMap_succ_head?_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 2 → α) :
    (((List.range (n + 1)).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n + 1 := by simpa using cell.2
          omega))).head? =
      some (f 1 (by omega)) := by
  rw [List.head?_eq_getElem?]
  rw [List.getElem?_eq_some_iff]
  refine ⟨by simp, ?_⟩
  simp

theorem tmVerifierXOnlyDecodedStackCellOf_choice_eq_of_cellRange_proofs
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (h₁ h₂ : cell ∈ tmVerifierXOnlyCellRange V x) :
    (tmVerifierXOnlyDecodedStackCellOf V x t k cell a h h₁).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x t k cell a h h₂).choice := by
  congr

theorem tmVerifierXOnlyDecodedStackChoicePrefix_tail_toStack
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hDomains : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hWF : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a) :
    tmVerifierReadChoicePrefixToStack
        (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a hDomains).tail =
      (tmVerifierReadChoicePrefixToStack
        (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a hDomains)).tail := by
  apply tmVerifierReadChoicePrefixToStack_tail_eq_tail_of_empty_successor
  intro second rest hPrefix
  cases hBound : tmVerifierXOnlyCellBound V x with
  | zero =>
      simp [tmVerifierXOnlyDecodedStackChoicePrefix, tmVerifierXOnlyCellSuccessorRange,
        hBound] at hPrefix
      have hImpossible : False := by
        have hLen := congrArg List.length hPrefix.2
        simp [hBound] at hLen
      exact False.elim hImpossible
  | succ n =>
      have hzero : 0 ∈ tmVerifierXOnlyCellSuccessorRange V x := by
        simp [tmVerifierXOnlyCellSuccessorRange, hBound]
      let d0 :=
        tmVerifierXOnlyDecodedStackCellOf V x t k 0 a hDomains
          (tmVerifierXOnlyCellRange_zero_mem V x)
      let d1 :=
        tmVerifierXOnlyDecodedStackCellOf V x t k 1 a hDomains
          (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x 0 hzero)
      have hEmptyNext :
          d0.choice = TMVerifierStackReadChoice.empty →
            d1.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
        intro hEmptyChoice
        have hEmpty0 : (tmVerifierStackEmptyAtom V t k 0).eval a = true :=
          d0.empty_atom_true hEmptyChoice
        have hEmpty1 :
            (tmVerifierStackEmptyAtom V t k (0 + 1)).eval a = true :=
          tmVerifierXOnlyStackWellFormedCNFAt_satisfies_empty_successor V x t k 0 a hWF
            hzero hEmpty0
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t k 1 a
          hDomains (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x 0 hzero)
          d1.choice TMVerifierStackReadChoice.empty d1.choice_mem
          (tmVerifierStackReadChoices_empty_mem V k) d1.atom_true
          (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty1)
      have hRest :
          second :: rest =
            ((tmVerifierXOnlyCellSuccessorRange V x).attach.map fun cell =>
              (tmVerifierXOnlyDecodedStackCellOf V x t k (cell.1 + 1) a hDomains
                (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1
                  cell.2)).choice) := by
        have hCons := hPrefix
        simp only [tmVerifierXOnlyDecodedStackChoicePrefix] at hCons
        exact (List.cons.inj hCons).2.symm
      have hTailHead :
          (((tmVerifierXOnlyCellSuccessorRange V x).attach.map fun cell =>
            (tmVerifierXOnlyDecodedStackCellOf V x t k (cell.1 + 1) a hDomains
              (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1
                cell.2)).choice)).head? =
            some d1.choice := by
        simpa [tmVerifierXOnlyCellSuccessorRange, hBound, d1, tmVerifierXOnlyCellRange]
          using xOnlyRangeAttachMap_succ_head?_subtype_aux n
            (fun cell _hcell =>
              (tmVerifierXOnlyDecodedStackCellOf V x t k cell a hDomains
                (by
                  rw [tmVerifierXOnlyCellRange, List.mem_range]
                  rw [hBound]
                  omega)).choice)
      have hSecond : second = d1.choice := by
        rw [← Option.some.injEq]
        calc
          some second = (second :: rest).head? := by simp
          _ = (((tmVerifierXOnlyCellSuccessorRange V x).attach.map fun cell =>
                (tmVerifierXOnlyDecodedStackCellOf V x t k (cell.1 + 1) a hDomains
                  (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1
                    cell.2)).choice)).head? := by
            rw [hRest]
          _ = some d1.choice := hTailHead
      rw [hSecond]
      exact hEmptyNext (by
        have hHead := List.cons.inj hPrefix |>.1
        simpa [d0] using hHead)

/-! ### Canonical decoded-prefix effect predicates -/

noncomputable def TMVerifierXOnlyDecodedPushPrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (a : Assignment)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin raw.stack) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a) :
    Prop :=
  (tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack 0 a hOut
      (tmVerifierXOnlyCellRange_zero_mem V x)).choice =
    TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol ∧
  ∀ cell, ∀ hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x,
    (tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack (cell + 1) a hOut
        (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell)).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin raw.stack cell a hIn
        (tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell)).choice

noncomputable def TMVerifierXOnlyDecodedPopPrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a) : Prop :=
  ∀ cell, ∀ hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x,
    (tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut
        (tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell)).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin k (cell + 1) a hIn
        (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell)).choice

noncomputable def TMVerifierXOnlyDecodedFramePrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a) : Prop :=
  ∀ cell, ∀ hcell : cell ∈ tmVerifierXOnlyCellRange V x,
    (tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut hcell).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin k cell a hIn hcell).choice

/-! ### Primitive action effects on canonical decoded prefixes -/

def tmVerifierXOnlyPushActionCNFBetween_decoded_top
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents)
      a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierDecodedStackCell V tout raw.stack 0 a :=
  { choice := TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack)
      (B.payload raw) raw.symbol
    choice_mem := tmVerifierPushPayloadBoundary_readChoice_mem V B raw hraw
    atom_true := by
      simpa [TMVerifierStackReadChoice.atomAt] using
        tmVerifierXOnlyPushActionCNFBetween_satisfies_top V B x tin tout raw antecedents a h
          hAntecedents }

def tmVerifierXOnlyPushActionCNFBetween_decoded_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat) (antecedents : List Literal)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents)
      a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin raw.stack cell a) :
    TMVerifierDecodedStackCell V tout raw.stack (cell + 1) a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierXOnlyPushActionCNFBetween_satisfies_shift V B x tin tout raw cell d.choice
        antecedents a h hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierXOnlyPushActionCNFBetween_decoded_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents)
      a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin j cell a) :
    TMVerifierDecodedStackCell V tout j cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierXOnlyPushActionCNFBetween_satisfies_other_stack_forward V B x tin tout raw j
        cell d.choice antecedents a h hj hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierXOnlyPopActionCNFBetween_decoded_shift
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin k (cell + 1) a) :
    TMVerifierDecodedStackCell V tout k cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierXOnlyPopActionCNFBetween_satisfies_shift V x tin tout k cell d.choice
        antecedents a h hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierXOnlyPopActionCNFBetween_decoded_other_stack_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin j cell a) :
    TMVerifierDecodedStackCell V tout j cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierXOnlyPopActionCNFBetween_satisfies_other_stack_forward V x tin tout k j cell
        d.choice antecedents a h hj hcell d.choice_mem hAntecedents d.atom_true }

def tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_forward
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
      antecedents) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (d : TMVerifierDecodedStackCell V tin k cell a) :
    TMVerifierDecodedStackCell V tout k cell a :=
  { choice := d.choice
    choice_mem := d.choice_mem
    atom_true :=
      tmVerifierXOnlyPreserveAllStacksActionCNFBetween_satisfies_forward V x tin tout k cell
        d.choice antecedents a h hk hcell d.choice_mem hAntecedents d.atom_true }

/-! ### Canonical decoded-prefix effects from primitive action blocks -/

theorem tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_top_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hOut :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack 0 a hOut
        (tmVerifierXOnlyCellRange_zero_mem V x)).choice =
      TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol := by
  let dCanonical :=
    tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack 0 a hOut
      (tmVerifierXOnlyCellRange_zero_mem V x)
  let dAction :=
    tmVerifierXOnlyPushActionCNFBetween_decoded_top V B x tin tout raw antecedents a hAction
      hraw hAntecedents
  have hEq : dCanonical.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout raw.stack 0 a hOut
      (tmVerifierXOnlyCellRange_zero_mem V x) dCanonical dAction
  simpa [dCanonical, dAction, tmVerifierXOnlyPushActionCNFBetween_decoded_top] using hEq

theorem tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_shift_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hIn :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin raw.stack) a)
    (hOut :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a)
    (hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack (cell + 1) a hOut
        (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell)).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin raw.stack cell a hIn
        (tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell)).choice := by
  let hcellIn := tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell
  let hcellOut := tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell
  let dIn := tmVerifierXOnlyDecodedStackCellOf V x tin raw.stack cell a hIn hcellIn
  let dOut := tmVerifierXOnlyDecodedStackCellOf V x tout raw.stack (cell + 1) a hOut hcellOut
  let dAction :=
    tmVerifierXOnlyPushActionCNFBetween_decoded_shift V B x tin tout raw cell antecedents a
      hAction hcellIn hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout raw.stack (cell + 1) a
      hOut hcellOut dOut dAction
  simpa [dIn, dOut, dAction, tmVerifierXOnlyPushActionCNFBetween_decoded_shift] using hEq

theorem tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hIn :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin raw.stack) a)
    (hOut :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierXOnlyDecodedPushPrefixEffect V B x tin tout raw a hIn hOut := by
  constructor
  · exact tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_top_choice_eq V B x tin tout
      raw antecedents a hAction hOut hraw hAntecedents
  · intro cell hcell
    exact tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_shift_choice_eq V B x tin tout
      raw cell antecedents a hAction hIn hOut hcell hAntecedents

theorem tmVerifierXOnlyPushActionCNFBetween_decoded_other_stack_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPushActionCNFBetween V B x tin tout raw antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin j) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout j) a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout j cell a hOut hcell).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin j cell a hIn hcell).choice := by
  let dIn := tmVerifierXOnlyDecodedStackCellOf V x tin j cell a hIn hcell
  let dOut := tmVerifierXOnlyDecodedStackCellOf V x tout j cell a hOut hcell
  let dAction :=
    tmVerifierXOnlyPushActionCNFBetween_decoded_other_stack_forward V B x tin tout raw j
      cell antecedents a hAction hj hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout j cell a hOut hcell dOut
      dAction
  simpa [dIn, dOut, dAction,
    tmVerifierXOnlyPushActionCNFBetween_decoded_other_stack_forward] using hEq

theorem tmVerifierXOnlyPopActionCNFBetween_decoded_prefix_shift_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents)
      a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut
        (tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell)).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin k (cell + 1) a hIn
        (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell)).choice := by
  let hcellOut := tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell hcell
  let hcellIn := tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell hcell
  let dIn := tmVerifierXOnlyDecodedStackCellOf V x tin k (cell + 1) a hIn hcellIn
  let dOut := tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut hcellOut
  let dAction :=
    tmVerifierXOnlyPopActionCNFBetween_decoded_shift V x tin tout k cell antecedents a
      hAction hcellOut hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout k cell a hOut hcellOut dOut
      dAction
  simpa [dIn, dOut, dAction, tmVerifierXOnlyPopActionCNFBetween_decoded_shift] using hEq

theorem tmVerifierXOnlyPopActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents)
      a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierXOnlyDecodedPopPrefixEffect V x tin tout k a hIn hOut := by
  intro cell hcell
  exact tmVerifierXOnlyPopActionCNFBetween_decoded_prefix_shift_choice_eq V x tin tout k
    cell antecedents a hAction hIn hOut hcell hAntecedents

theorem tmVerifierXOnlyPopActionCNFBetween_decoded_other_stack_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierXOnlyPopActionCNFBetween V x tin tout k antecedents)
      a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin j) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout j) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout j cell a hOut hcell).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin j cell a hIn hcell).choice := by
  let dIn := tmVerifierXOnlyDecodedStackCellOf V x tin j cell a hIn hcell
  let dOut := tmVerifierXOnlyDecodedStackCellOf V x tout j cell a hOut hcell
  let dAction :=
    tmVerifierXOnlyPopActionCNFBetween_decoded_other_stack_forward V x tin tout k j cell
      antecedents a hAction hj hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout j cell a hOut hcell dOut
      dAction
  simpa [dIn, dOut, dAction,
    tmVerifierXOnlyPopActionCNFBetween_decoded_other_stack_forward] using hEq

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
        antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut hcell).choice =
      (tmVerifierXOnlyDecodedStackCellOf V x tin k cell a hIn hcell).choice := by
  let dIn := tmVerifierXOnlyDecodedStackCellOf V x tin k cell a hIn hcell
  let dOut := tmVerifierXOnlyDecodedStackCellOf V x tout k cell a hOut hcell
  let dAction :=
    tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_forward V x tin tout k cell
      antecedents a hAction hk hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain V x tout k cell a hOut hcell dOut
      dAction
  simpa [dIn, dOut, dAction,
    tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_forward] using hEq

theorem tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierXOnlyPreserveAllStacksActionCNFBetween V x tin tout
        antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a)
    (hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a)
    (hk : k ∈ tmVerifierStackList V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierXOnlyDecodedFramePrefixEffect V x tin tout k a hIn hOut := by
  intro cell hcell
  exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_choice_eq V x tin tout k
    cell antecedents a hAction hIn hOut hk hcell hAntecedents

/-! ### Concrete stack-list consequences -/

theorem TMVerifierXOnlyDecodedPushPrefixEffect.choicePrefix_eq_cons_dropLast
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier} {tin tout : Nat}
    {raw : TMVerifierStackSymbol V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin raw.stack) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a}
    (hEff : TMVerifierXOnlyDecodedPushPrefixEffect V B x tin tout raw a hIn hOut) :
    tmVerifierXOnlyDecodedStackChoicePrefix V x tout raw.stack a hOut =
      TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol ::
        (tmVerifierXOnlyDecodedStackChoicePrefix V x tin raw.stack a hIn).dropLast := by
  rcases hEff with ⟨hTop, hShift⟩
  rw [tmVerifierXOnlyDecodedStackChoicePrefix_dropLast]
  simp only [tmVerifierXOnlyDecodedStackChoicePrefix]
  exact List.cons_eq_cons.mpr ⟨hTop, by
    apply List.map_congr_left
    intro cell hcell
    exact hShift cell.1 cell.2⟩

theorem TMVerifierXOnlyDecodedFramePrefixEffect.choicePrefix_eq
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a}
    (hEff : TMVerifierXOnlyDecodedFramePrefixEffect V x tin tout k a hIn hOut) :
    tmVerifierXOnlyDecodedStackChoicePrefix V x tout k a hOut =
      tmVerifierXOnlyDecodedStackChoicePrefix V x tin k a hIn := by
  simp only [tmVerifierXOnlyDecodedStackChoicePrefix]
  exact List.cons_eq_cons.mpr ⟨hEff 0 (tmVerifierXOnlyCellRange_zero_mem V x), by
    apply List.map_congr_left
    intro cell hcell
    exact hEff (cell.1 + 1)
      (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1 cell.2)⟩

theorem TMVerifierXOnlyDecodedPopPrefixEffect.choicePrefix_dropLast_eq_tail
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a}
    (hEff : TMVerifierXOnlyDecodedPopPrefixEffect V x tin tout k a hIn hOut) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x tout k a hOut).dropLast =
      (tmVerifierXOnlyDecodedStackChoicePrefix V x tin k a hIn).tail := by
  rw [tmVerifierXOnlyDecodedStackChoicePrefix_dropLast]
  simp only [tmVerifierXOnlyDecodedStackChoicePrefix]
  apply List.map_congr_left
  intro cell hcell
  exact hEff cell.1 cell.2

theorem TMVerifierXOnlyDecodedPushPrefixEffect.decodedStackList_eq_cons
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier} {tin tout : Nat}
    {raw : TMVerifierStackSymbol V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin raw.stack) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout raw.stack) a}
    (hEff : TMVerifierXOnlyDecodedPushPrefixEffect V B x tin tout raw a hIn hOut)
    (hInWF : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x tin raw.stack) a) :
    tmVerifierXOnlyDecodedStackList V x tout raw.stack a hOut =
      raw.symbol :: tmVerifierXOnlyDecodedStackList V x tin raw.stack a hIn := by
  let inPrefix := tmVerifierXOnlyDecodedStackChoicePrefix V x tin raw.stack a hIn
  have hLast : inPrefix.getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V raw.stack) :=
    tmVerifierXOnlyDecodedStackChoicePrefix_final_empty V x tin raw.stack a hIn hInWF
  calc
    tmVerifierXOnlyDecodedStackList V x tout raw.stack a hOut =
        tmVerifierReadChoicePrefixToStack
          (TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack)
            (B.payload raw) raw.symbol :: inPrefix.dropLast) := by
      simp [tmVerifierXOnlyDecodedStackList, inPrefix,
        TMVerifierXOnlyDecodedPushPrefixEffect.choicePrefix_eq_cons_dropLast hEff]
    _ = raw.symbol :: tmVerifierReadChoicePrefixToStack inPrefix.dropLast := rfl
    _ = raw.symbol :: tmVerifierReadChoicePrefixToStack inPrefix := by
      rw [tmVerifierReadChoicePrefixToStack_dropLast_of_getLast?_empty inPrefix hLast]
    _ = raw.symbol :: tmVerifierXOnlyDecodedStackList V x tin raw.stack a hIn := rfl

theorem TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a}
    (hEff : TMVerifierXOnlyDecodedFramePrefixEffect V x tin tout k a hIn hOut) :
    tmVerifierXOnlyDecodedStackList V x tout k a hOut =
      tmVerifierXOnlyDecodedStackList V x tin k a hIn := by
  simp [tmVerifierXOnlyDecodedStackList,
    TMVerifierXOnlyDecodedFramePrefixEffect.choicePrefix_eq hEff]

theorem TMVerifierXOnlyDecodedPopPrefixEffect.decodedStackList_eq_tail
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier} {tin tout : Nat}
    {k : tmVerifierStackIndex V} {a : Assignment}
    {hIn : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tin k) a}
    {hOut : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x tout k) a}
    (hEff : TMVerifierXOnlyDecodedPopPrefixEffect V x tin tout k a hIn hOut)
    (hInWF : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x tin k) a)
    (hOutWF : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x tout k) a) :
    tmVerifierXOnlyDecodedStackList V x tout k a hOut =
      (tmVerifierXOnlyDecodedStackList V x tin k a hIn).tail := by
  let outPrefix := tmVerifierXOnlyDecodedStackChoicePrefix V x tout k a hOut
  let inPrefix := tmVerifierXOnlyDecodedStackChoicePrefix V x tin k a hIn
  have hOutLast : outPrefix.getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) :=
    tmVerifierXOnlyDecodedStackChoicePrefix_final_empty V x tout k a hOut hOutWF
  calc
    tmVerifierXOnlyDecodedStackList V x tout k a hOut =
        tmVerifierReadChoicePrefixToStack outPrefix := rfl
    _ = tmVerifierReadChoicePrefixToStack outPrefix.dropLast := by
      exact (tmVerifierReadChoicePrefixToStack_dropLast_of_getLast?_empty outPrefix
        hOutLast).symm
    _ = tmVerifierReadChoicePrefixToStack inPrefix.tail := by
      rw [TMVerifierXOnlyDecodedPopPrefixEffect.choicePrefix_dropLast_eq_tail hEff]
    _ = (tmVerifierReadChoicePrefixToStack inPrefix).tail := by
      exact tmVerifierXOnlyDecodedStackChoicePrefix_tail_toStack V x tin k a hIn hInWF
    _ = (tmVerifierXOnlyDecodedStackList V x tin k a hIn).tail := rfl

end SAT
end ComplexityReduction
