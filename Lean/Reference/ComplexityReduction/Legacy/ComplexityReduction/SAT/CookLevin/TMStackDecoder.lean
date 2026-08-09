/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionSemantics

/-!
Decoded stack-cell surface for the future standard-TM Cook-Levin tableau.

This file does not yet prove full stack equality or `TM2.stepAux` correctness.
It packages the domain clauses as a reusable decoder: every bounded stack cell
in a satisfied well-formed row has a true audited empty-or-symbol read choice,
and the empty-tail clauses propagate emptiness to successor cells.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Decoded cells -/

/-- A decoded bounded stack cell is an audited read choice whose atom is true. -/
structure TMVerifierDecodedStackCell {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (a : Assignment) where
  choice : TMVerifierStackReadChoice V k
  choice_mem : choice ∈ tmVerifierStackReadChoices V k
  atom_true : (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a = true

namespace TMVerifierDecodedStackCell

/-- Semantic `Option` value represented by a decoded cell. -/
def toOption {L : EncodedDecisionProblem} {V : TMVerifier L}
    {t : Nat} {k : tmVerifierStackIndex V} {cell : Nat} {a : Assignment}
    (d : TMVerifierDecodedStackCell V t k cell a) : Option ((tmVerifierTM V).Γ k) :=
  d.choice.toOption

theorem empty_atom_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {t : Nat} {k : tmVerifierStackIndex V} {cell : Nat} {a : Assignment}
    (d : TMVerifierDecodedStackCell V t k cell a)
    (h : d.choice = TMVerifierStackReadChoice.empty) :
    (tmVerifierStackEmptyAtom V t k cell).eval a = true := by
  simpa [TMVerifierStackReadChoice.atomAt, h] using d.atom_true

theorem symbol_atom_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {t : Nat} {k : tmVerifierStackIndex V} {cell payload : Nat}
    {symbol : (tmVerifierTM V).Γ k} {a : Assignment}
    (d : TMVerifierDecodedStackCell V t k cell a)
    (h : d.choice = TMVerifierStackReadChoice.symbol (V := V) (k := k) payload symbol) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval a = true := by
  simpa [TMVerifierStackReadChoice.atomAt, h] using d.atom_true

end TMVerifierDecodedStackCell

theorem tmVerifierStackCellDomainCNFAt_satisfies_has_choice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment) :
    CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a →
      ∃ choice ∈ tmVerifierStackReadChoices V k,
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a = true := by
  intro h
  rcases tmVerifierStackCellDomainCNFAt_satisfies_has_atom V t k cell a h with
    ⟨l, hl, heval⟩
  rw [tmVerifierStackCellChoiceLiteralsAt] at hl
  rcases List.mem_map.mp hl with
    ⟨choice, hchoice, rfl⟩
  exact ⟨choice, hchoice, heval⟩

theorem tmVerifierStackCellDomainsCNFAt_satisfies_cell_choice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellRange V p) :
    ∃ choice ∈ tmVerifierStackReadChoices V k,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a = true := by
  have hDomain : CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierStackCellDomainsCNFAt]
      exact ⟨cell, hcell, hc⟩)
  exact tmVerifierStackCellDomainCNFAt_satisfies_has_choice V t k cell a hDomain

theorem tmVerifierStackWellFormedCNFAt_satisfies_cell_choice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a)
  (hcell : cell ∈ tmVerifierCellRange V p) :
    ∃ choice ∈ tmVerifierStackReadChoices V k,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a = true := by
  have hDomains : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a :=
    tmVerifierStackWellFormedCNFAt_satisfies_domains V p t k a h
  exact tmVerifierStackCellDomainsCNFAt_satisfies_cell_choice V p t k cell a hDomains hcell

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_stack_cell_choice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellRange V p) :
    ∃ choice ∈ tmVerifierStackReadChoices V k,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t cell choice).eval a = true := by
  have hStack : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierAllStackWellFormedCNFAt]
      exact ⟨k, hk, hc⟩)
  exact tmVerifierStackWellFormedCNFAt_satisfies_cell_choice V p t k cell a hStack hcell

/-- Choose a decoded cell from a satisfied stack-domain block. -/
noncomputable def tmVerifierDecodedStackCellOf
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellRange V p) :
    TMVerifierDecodedStackCell V t k cell a :=
  by
    classical
    let witness := tmVerifierStackCellDomainsCNFAt_satisfies_cell_choice V p t k cell a h hcell
    exact
      { choice := Classical.choose witness
        choice_mem := (Classical.choose_spec witness).1
        atom_true := (Classical.choose_spec witness).2 }

/-- Decode all bounded cells of one stack into audited read choices. -/
noncomputable def tmVerifierDecodedStackPrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    List (TMVerifierStackReadChoice V k) :=
  (tmVerifierCellRange V p).attach.map fun cell =>
    (tmVerifierDecodedStackCellOf V p t k cell.1 a h cell.2).choice

@[simp]
theorem tmVerifierDecodedStackPrefix_length
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a) :
    (tmVerifierDecodedStackPrefix V p t k a h).length =
      (tmVerifierCellRange V p).length := by
  simp [tmVerifierDecodedStackPrefix]

theorem tmVerifierDecodedStackPrefix_choice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (choice : TMVerifierStackReadChoice V k)
    (hchoice : choice ∈ tmVerifierDecodedStackPrefix V p t k a h) :
    choice ∈ tmVerifierStackReadChoices V k := by
  rcases List.mem_map.mp hchoice with ⟨cell, _hcell, hEq⟩
  rw [← hEq]
  exact (tmVerifierDecodedStackCellOf V p t k cell.1 a h cell.2).choice_mem

/-! ### Empty-tail propagation through well-formed rows -/

theorem tmVerifierStackWellFormedCNFAt_satisfies_empty_successor
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a)
  (hcell : cell ∈ tmVerifierCellSuccessorRange V p)
  (hEmpty : (tmVerifierStackEmptyAtom V t k cell).eval a = true) :
    (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  have hTail : CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k) a :=
    tmVerifierStackWellFormedCNFAt_satisfies_emptyTail V p t k a h
  exact tmVerifierStackEmptyTailCNFAt_satisfies_successor V p t k cell a hTail hcell hEmpty

theorem tmVerifierAllStackWellFormedCNFAt_satisfies_empty_successor
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V p t) a)
    (hk : k ∈ tmVerifierStackList V)
    (hcell : cell ∈ tmVerifierCellSuccessorRange V p)
    (hEmpty : (tmVerifierStackEmptyAtom V t k cell).eval a = true) :
    (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  have hStack : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierAllStackWellFormedCNFAt]
      exact ⟨k, hk, hc⟩)
  exact tmVerifierStackWellFormedCNFAt_satisfies_empty_successor V p t k cell a hStack hcell
    hEmpty

end SAT
end ComplexityReduction
