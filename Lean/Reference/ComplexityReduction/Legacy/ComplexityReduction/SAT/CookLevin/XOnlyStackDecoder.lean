/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyExtraction
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists.Decoded

/-!
Concrete stack-list decoding for the x-only Cook-Levin tableau surface.

The x-only tableau fixes only the instance prefix and leaves the certificate
suffix existential.  This file therefore decodes bounded stack rows as raw
TM2 stack lists over the x-only cell range, without interpreting the arbitrary
input-stack suffix as a typed verifier certificate.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only cell-range bookkeeping -/

theorem tmVerifierXOnlyCellRange_zero_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    0 ∈ tmVerifierXOnlyCellRange V x := by
  simp [tmVerifierXOnlyCellRange]

theorem tmVerifierXOnlyCellBound_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    tmVerifierXOnlyCellBound V x ∈ tmVerifierXOnlyCellRange V x := by
  simp [tmVerifierXOnlyCellRange]

theorem tmVerifierXOnlyCellSuccessorRange_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (cell : Nat) :
    cell ∈ tmVerifierXOnlyCellSuccessorRange V x →
      cell ∈ tmVerifierXOnlyCellRange V x := by
  intro hcell
  rw [tmVerifierXOnlyCellSuccessorRange, List.mem_range] at hcell
  rw [tmVerifierXOnlyCellRange, List.mem_range]
  exact Nat.lt_trans hcell (Nat.lt_succ_self _)

theorem tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (cell : Nat) :
    cell ∈ tmVerifierXOnlyCellSuccessorRange V x →
      cell + 1 ∈ tmVerifierXOnlyCellRange V x := by
  intro hcell
  rw [tmVerifierXOnlyCellSuccessorRange, List.mem_range] at hcell
  rw [tmVerifierXOnlyCellRange, List.mem_range]
  simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ hcell

/-! ### X-only decoded cells -/

theorem tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_cell_choice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    ∃ choice ∈ tmVerifierStackReadChoices V k,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a =
        true := by
  rcases tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_cell V x t k cell a h hcell with
    ⟨l, hl, heval⟩
  rw [tmVerifierStackCellChoiceLiteralsAt] at hl
  rcases List.mem_map.mp hl with ⟨choice, hchoice, rfl⟩
  exact ⟨choice, hchoice, heval⟩

theorem tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (choice₁ choice₂ : TMVerifierStackReadChoice V k)
    (hmem₁ : choice₁ ∈ tmVerifierStackReadChoices V k)
    (hmem₂ : choice₂ ∈ tmVerifierStackReadChoices V k)
    (htrue₁ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₁).eval a =
        true)
    (htrue₂ :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice₂).eval a =
        true) :
    choice₁ = choice₂ := by
  have hDomain : CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyStackCellDomainsCNFAt]
      exact ⟨cell, hcell, hc⟩)
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_choice_eq V t k cell a hDomain
    choice₁ choice₂ hmem₁ hmem₂ htrue₁ htrue₂

/-- Choose a decoded cell from a satisfied x-only stack-domain row. -/
noncomputable def tmVerifierXOnlyDecodedStackCellOf
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    TMVerifierDecodedStackCell V t k cell a :=
  by
    classical
    let witness :=
      tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_cell_choice V x t k cell a h hcell
    exact
      { choice := Classical.choose witness
        choice_mem := (Classical.choose_spec witness).1
        atom_true := (Classical.choose_spec witness).2 }

theorem tmVerifierXOnlyDecodedStackCell_choice_eq_of_domain
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x)
    (d₁ d₂ : TMVerifierDecodedStackCell V t k cell a) :
    d₁.choice = d₂.choice :=
  tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t k cell a h hcell
    d₁.choice d₂.choice d₁.choice_mem d₂.choice_mem d₁.atom_true d₂.atom_true

/-! ### X-only decoded prefixes as concrete stack lists -/

private theorem xOnlyRangeAttachPrefix_getLast?_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α) :
    (f 0 (by omega) :: ((List.range n).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega))).getLast? =
      some (f n (by omega)) := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_cons, List.length_map, List.length_attach, List.length_range,
    Nat.add_one_sub_one]
  cases n with
  | zero => simp
  | succ n =>
      rw [List.getElem?_cons_succ]
      rw [List.getElem?_map]
      simp

private theorem xOnlyRangeAttachPrefix_dropLast_subtype_aux {α : Type} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α) :
    (f 0 (by omega) :: ((List.range n).attach.map fun cell =>
        f (cell.1 + 1) (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega))).dropLast =
      ((List.range n).attach.map fun cell =>
        f cell.1 (by
          have hcell : cell.1 < n := by simpa using cell.2
          omega)) := by
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    change
      ((f 0 (by omega) :: ((List.range n).attach.map fun cell =>
          f (cell.1 + 1) (by
            have hcell : cell.1 < n := by simpa using cell.2
            omega))).dropLast)[i] =
        (((List.range n).attach.map fun cell =>
          f cell.1 (by
            have hcell : cell.1 < n := by simpa using cell.2
            omega)))[i]
    rw [List.getElem_dropLast]
    cases i with
    | zero =>
        simp
    | succ i =>
        rw [List.getElem_cons_succ]
        rw [List.getElem_map]
        rw [List.getElem_map]
        simp

/-- Decode one satisfied x-only stack-domain row into a finite read-choice prefix. -/
noncomputable def tmVerifierXOnlyDecodedStackChoicePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    List (TMVerifierStackReadChoice V k) :=
  (tmVerifierXOnlyDecodedStackCellOf V x t k 0 a h
      (tmVerifierXOnlyCellRange_zero_mem V x)).choice ::
    ((tmVerifierXOnlyCellSuccessorRange V x).attach.map fun cell =>
      (tmVerifierXOnlyDecodedStackCellOf V x t k (cell.1 + 1) a h
        (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1 cell.2)).choice)

/-- Decode one satisfied x-only stack-domain row into the concrete stack list it represents. -/
noncomputable def tmVerifierXOnlyDecodedStackList
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    List ((tmVerifierTM V).Γ k) :=
  tmVerifierReadChoicePrefixToStack (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h)

theorem tmVerifierXOnlyDecodedStackList_head?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    (tmVerifierXOnlyDecodedStackList V x t k a h).head? =
      (tmVerifierXOnlyDecodedStackCellOf V x t k 0 a h
        (tmVerifierXOnlyCellRange_zero_mem V x)).choice.toOption := by
  simp [tmVerifierXOnlyDecodedStackList, tmVerifierXOnlyDecodedStackChoicePrefix,
    tmVerifierReadChoicePrefixToStack_cons_head?]

theorem tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h₁ h₂ : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    tmVerifierXOnlyDecodedStackList V x t k a h₁ =
      tmVerifierXOnlyDecodedStackList V x t k a h₂ := by
  simp [tmVerifierXOnlyDecodedStackList, tmVerifierXOnlyDecodedStackChoicePrefix]

theorem tmVerifierXOnlyDecodedStackList_eq_of_time_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    {t₁ t₂ : Nat} (ht : t₁ = t₂) (k : tmVerifierStackIndex V) (a : Assignment)
    (h₁ : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t₁ k) a)
    (h₂ : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t₂ k) a) :
    tmVerifierXOnlyDecodedStackList V x t₁ k a h₁ =
      tmVerifierXOnlyDecodedStackList V x t₂ k a h₂ := by
  cases ht
  exact tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs V x t₁ k a h₁ h₂

theorem tmVerifierXOnlyDecodedStackChoicePrefix_getElem?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (cell : Nat) (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h)[cell]? =
      some ((tmVerifierXOnlyDecodedStackCellOf V x t k cell a h hcell).choice) := by
  cases cell with
  | zero =>
      simp [tmVerifierXOnlyDecodedStackChoicePrefix]
  | succ i =>
      have hi : i < tmVerifierXOnlyCellBound V x := by
        simp [tmVerifierXOnlyCellRange, List.mem_range] at hcell
        omega
      rw [tmVerifierXOnlyDecodedStackChoicePrefix]
      rw [List.getElem?_cons_succ]
      rw [List.getElem?_map]
      have hLen : i < (tmVerifierXOnlyCellSuccessorRange V x).attach.length := by
        simp [tmVerifierXOnlyCellSuccessorRange, hi]
      rw [List.getElem?_eq_getElem hLen]
      rw [List.getElem_attach]
      simp [tmVerifierXOnlyCellSuccessorRange]

theorem tmVerifierXOnlyDecodedStackChoicePrefix_getLast?
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h).getLast? =
      some ((tmVerifierXOnlyDecodedStackCellOf V x t k (tmVerifierXOnlyCellBound V x)
        a h (tmVerifierXOnlyCellBound_mem_cellRange V x)).choice) := by
  simpa [tmVerifierXOnlyDecodedStackChoicePrefix, tmVerifierXOnlyCellSuccessorRange,
    tmVerifierXOnlyCellRange] using
    xOnlyRangeAttachPrefix_getLast?_subtype_aux (tmVerifierXOnlyCellBound V x)
      (fun cell _hcell =>
        (tmVerifierXOnlyDecodedStackCellOf V x t k cell a h
          (by simpa [tmVerifierXOnlyCellRange, List.mem_range] using _hcell)).choice)

theorem tmVerifierXOnlyDecodedStackChoicePrefix_final_empty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (hDomains : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hWF : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a hDomains).getLast? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
  rw [tmVerifierXOnlyDecodedStackChoicePrefix_getLast?]
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x t k (tmVerifierXOnlyCellBound V x)
      a hDomains (tmVerifierXOnlyCellBound_mem_cellRange V x)
  have hChoice :
      d.choice = (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
    exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x t k
      (tmVerifierXOnlyCellBound V x) a hDomains
      (tmVerifierXOnlyCellBound_mem_cellRange V x)
      d.choice TMVerifierStackReadChoice.empty d.choice_mem
      (tmVerifierStackReadChoices_empty_mem V k) d.atom_true
      (by
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierXOnlyStackWellFormedCNFAt_satisfies_finalEmpty V x t k a hWF)
  simp [d, hChoice]

theorem tmVerifierXOnlyDecodedStackChoicePrefix_dropLast
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h).dropLast =
      ((tmVerifierXOnlyCellSuccessorRange V x).attach.map fun cell =>
        (tmVerifierXOnlyDecodedStackCellOf V x t k cell.1 a h
          (tmVerifierXOnlyCellSuccessorRange_mem_cellRange V x cell.1 cell.2)).choice) := by
  simpa [tmVerifierXOnlyDecodedStackChoicePrefix, tmVerifierXOnlyCellSuccessorRange,
    tmVerifierXOnlyCellRange] using
    xOnlyRangeAttachPrefix_dropLast_subtype_aux (tmVerifierXOnlyCellBound V x)
      (fun cell _hcell =>
        (tmVerifierXOnlyDecodedStackCellOf V x t k cell a h
          (by simpa [tmVerifierXOnlyCellRange, List.mem_range] using _hcell)).choice)

end SAT
end ComplexityReduction
