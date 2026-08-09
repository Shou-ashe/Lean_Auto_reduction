/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackChoiceUniqueness

/-!
Bounded decoded-prefix effects of primitive stack actions.

`TMStackActionDecoded` constructs decoded cells from satisfied action blocks.
This file uses per-cell domain uniqueness to compare those action-produced
cells with the canonical decoded cells chosen by `tmVerifierDecodedStackCellOf`.
The result is still bounded-prefix semantics: push/pop/frame effects are stated
as pointwise equations over the bounded cell range, not as a full `TM2.stepAux`
theorem.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Cell-range bookkeeping -/

theorem tmVerifierCellRange_zero_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    0 ∈ tmVerifierCellRange V p := by
  simp [tmVerifierCellRange]

theorem tmVerifierCellSuccessorRange_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (cell : Nat) :
    cell ∈ tmVerifierCellSuccessorRange V p →
      cell ∈ tmVerifierCellRange V p := by
  intro hcell
  rw [tmVerifierCellSuccessorRange, List.mem_range] at hcell
  rw [tmVerifierCellRange, List.mem_range]
  exact Nat.lt_trans hcell (Nat.lt_succ_self _)

theorem tmVerifierCellSuccessorRange_succ_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (cell : Nat) :
    cell ∈ tmVerifierCellSuccessorRange V p →
      cell + 1 ∈ tmVerifierCellRange V p := by
  intro hcell
  rw [tmVerifierCellSuccessorRange, List.mem_range] at hcell
  rw [tmVerifierCellRange, List.mem_range]
  simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ hcell

/-! ### Canonical decoded-prefix effect predicates -/

noncomputable def TMVerifierDecodedPushPrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (a : Assignment)
    (hIn :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin raw.stack) a)
    (hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a) : Prop :=
  (tmVerifierDecodedStackCellOf V p tout raw.stack 0 a hOut
      (tmVerifierCellRange_zero_mem V p)).choice =
    TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol ∧
  ∀ cell, ∀ hcell : cell ∈ tmVerifierCellSuccessorRange V p,
    (tmVerifierDecodedStackCellOf V p tout raw.stack (cell + 1) a hOut
        (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell)).choice =
      (tmVerifierDecodedStackCellOf V p tin raw.stack cell a hIn
        (tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell)).choice

noncomputable def TMVerifierDecodedPopPrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a) : Prop :=
  ∀ cell, ∀ hcell : cell ∈ tmVerifierCellSuccessorRange V p,
    (tmVerifierDecodedStackCellOf V p tout k cell a hOut
        (tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell)).choice =
      (tmVerifierDecodedStackCellOf V p tin k (cell + 1) a hIn
        (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell)).choice

noncomputable def TMVerifierDecodedFramePrefixEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a) : Prop :=
  ∀ cell, ∀ hcell : cell ∈ tmVerifierCellRange V p,
    (tmVerifierDecodedStackCellOf V p tout k cell a hOut hcell).choice =
      (tmVerifierDecodedStackCellOf V p tin k cell a hIn hcell).choice

/-! ### Push effects on canonical decoded prefixes -/

theorem tmVerifierPushActionCNFBetween_decoded_prefix_top_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout raw.stack 0 a hOut
        (tmVerifierCellRange_zero_mem V p)).choice =
      TMVerifierStackReadChoice.symbol (V := V) (k := raw.stack) (B.payload raw) raw.symbol := by
  let dCanonical :=
    tmVerifierDecodedStackCellOf V p tout raw.stack 0 a hOut
      (tmVerifierCellRange_zero_mem V p)
  let dAction :=
    tmVerifierPushActionCNFBetween_decoded_top V B p tin tout raw antecedents a hAction hraw
      hAntecedents
  have hEq :
      dCanonical.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout raw.stack 0 a hOut
      (tmVerifierCellRange_zero_mem V p) dCanonical dAction
  simpa [dCanonical, dAction, tmVerifierPushActionCNFBetween_decoded_top] using hEq

theorem tmVerifierPushActionCNFBetween_decoded_prefix_shift_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (cell : Nat) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hIn :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin raw.stack) a)
    (hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a)
    (hcell : cell ∈ tmVerifierCellSuccessorRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout raw.stack (cell + 1) a hOut
        (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell)).choice =
      (tmVerifierDecodedStackCellOf V p tin raw.stack cell a hIn
        (tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell)).choice := by
  let hcellIn := tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell
  let hcellOut := tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell
  let dIn := tmVerifierDecodedStackCellOf V p tin raw.stack cell a hIn hcellIn
  let dOut := tmVerifierDecodedStackCellOf V p tout raw.stack (cell + 1) a hOut hcellOut
  let dAction :=
    tmVerifierPushActionCNFBetween_decoded_shift V B p tin tout raw cell antecedents a hAction
      hcellIn hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout raw.stack (cell + 1) a hOut
      hcellOut dOut dAction
  simpa [dIn, dOut, dAction, tmVerifierPushActionCNFBetween_decoded_shift] using hEq

theorem tmVerifierPushActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hIn :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin raw.stack) a)
    (hOut :
      CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout raw.stack) a)
    (hraw : raw ∈ tmVerifierControlPushSymbols V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierDecodedPushPrefixEffect V B p tin tout raw a hIn hOut := by
  constructor
  · exact tmVerifierPushActionCNFBetween_decoded_prefix_top_choice_eq V B p tin tout raw
      antecedents a hAction hOut hraw hAntecedents
  · intro cell hcell
    exact tmVerifierPushActionCNFBetween_decoded_prefix_shift_choice_eq V B p tin tout raw cell
      antecedents a hAction hIn hOut hcell hAntecedents

theorem tmVerifierPushActionCNFBetween_decoded_other_stack_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin j) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout j) a)
    (hj : j ∈ tmVerifierOtherStacks V raw.stack)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout j cell a hOut hcell).choice =
      (tmVerifierDecodedStackCellOf V p tin j cell a hIn hcell).choice := by
  let dIn := tmVerifierDecodedStackCellOf V p tin j cell a hIn hcell
  let dOut := tmVerifierDecodedStackCellOf V p tout j cell a hOut hcell
  let dAction :=
    tmVerifierPushActionCNFBetween_decoded_other_stack_forward V B p tin tout raw j cell
      antecedents a hAction hj hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout j cell a hOut hcell dOut dAction
  simpa [dIn, dOut, dAction, tmVerifierPushActionCNFBetween_decoded_other_stack_forward]
    using hEq

/-! ### Pop and frame effects on canonical decoded prefixes -/

theorem tmVerifierPopActionCNFBetween_decoded_prefix_shift_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a)
    (hcell : cell ∈ tmVerifierCellSuccessorRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout k cell a hOut
        (tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell)).choice =
      (tmVerifierDecodedStackCellOf V p tin k (cell + 1) a hIn
        (tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell)).choice := by
  let hcellOut := tmVerifierCellSuccessorRange_mem_cellRange V p cell hcell
  let hcellIn := tmVerifierCellSuccessorRange_succ_mem_cellRange V p cell hcell
  let dIn := tmVerifierDecodedStackCellOf V p tin k (cell + 1) a hIn hcellIn
  let dOut := tmVerifierDecodedStackCellOf V p tout k cell a hOut hcellOut
  let dAction :=
    tmVerifierPopActionCNFBetween_decoded_shift V p tin tout k cell antecedents a hAction
      hcellOut hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout k cell a hOut hcellOut dOut
      dAction
  simpa [dIn, dOut, dAction, tmVerifierPopActionCNFBetween_decoded_shift] using hEq

theorem tmVerifierPopActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierDecodedPopPrefixEffect V p tin tout k a hIn hOut := by
  intro cell hcell
  exact tmVerifierPopActionCNFBetween_decoded_prefix_shift_choice_eq V p tin tout k cell
    antecedents a hAction hIn hOut hcell hAntecedents

theorem tmVerifierPopActionCNFBetween_decoded_other_stack_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k j : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction : CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin j) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout j) a)
    (hj : j ∈ tmVerifierOtherStacks V k)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout j cell a hOut hcell).choice =
      (tmVerifierDecodedStackCellOf V p tin j cell a hIn hcell).choice := by
  let dIn := tmVerifierDecodedStackCellOf V p tin j cell a hIn hcell
  let dOut := tmVerifierDecodedStackCellOf V p tout j cell a hOut hcell
  let dAction :=
    tmVerifierPopActionCNFBetween_decoded_other_stack_forward V p tin tout k j cell antecedents
      a hAction hj hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout j cell a hOut hcell dOut dAction
  simpa [dIn, dOut, dAction, tmVerifierPopActionCNFBetween_decoded_other_stack_forward]
    using hEq

theorem tmVerifierPreserveAllStacksActionCNFBetween_decoded_choice_eq
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    (tmVerifierDecodedStackCellOf V p tout k cell a hOut hcell).choice =
      (tmVerifierDecodedStackCellOf V p tin k cell a hIn hcell).choice := by
  let dIn := tmVerifierDecodedStackCellOf V p tin k cell a hIn hcell
  let dOut := tmVerifierDecodedStackCellOf V p tout k cell a hOut hcell
  let dAction :=
    tmVerifierPreserveAllStacksActionCNFBetween_decoded_forward V p tin tout k cell
      antecedents a hAction hk hcell hAntecedents dIn
  have hEq : dOut.choice = dAction.choice :=
    tmVerifierDecodedStackCell_choice_eq_of_domain V p tout k cell a hOut hcell dOut dAction
  simpa [dIn, dOut, dAction, tmVerifierPreserveAllStacksActionCNFBetween_decoded_forward]
    using hEq

theorem tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment)
    (hAction :
      CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents) a)
    (hIn : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tin k) a)
    (hOut : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p tout k) a)
    (hk : k ∈ tmVerifierStackList V)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierDecodedFramePrefixEffect V p tin tout k a hIn hOut := by
  intro cell hcell
  exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_choice_eq V p tin tout k cell
    antecedents a hAction hIn hOut hk hcell hAntecedents

end SAT
end ComplexityReduction
