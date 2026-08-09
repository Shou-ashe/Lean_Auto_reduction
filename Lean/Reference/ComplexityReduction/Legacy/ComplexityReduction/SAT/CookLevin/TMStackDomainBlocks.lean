/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMPushPayloadBoundary

/-!
Stack-domain and empty-tail blocks for the future standard-TM Cook-Levin tableau.

The transition-window layer can only reason about stack actions once each
bounded stack cell has a well-formed finite choice: either the cell is empty or
it contains one of the audited active stack symbols for that stack.  This file
packages that exactly-one domain surface and the monotone empty-tail constraint
needed by later push/pop semantics.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Per-cell domains -/

/-- The audited empty-or-active-symbol literals for one stack cell. -/
noncomputable def tmVerifierStackCellChoiceLiteralsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : List Literal :=
  tmVerifierStackReadChoiceLiteralsAt V t k cell

/-- Exactly one audited stack-cell choice is selected. -/
noncomputable def tmVerifierStackCellDomainCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : CNF :=
  tmVerifierStackReadChoiceDomainCNFAt V t k cell

/-- The top-cell domain is the read-choice domain used by transition windows. -/
noncomputable def tmVerifierStackTopDomainCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  tmVerifierStackCellDomainCNFAt V t k 0

theorem tmVerifierStackCellDomainCNFAt_satisfies_has_atom
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment) :
    CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a →
      ∃ l ∈ tmVerifierStackCellChoiceLiteralsAt V t k cell, l.eval a = true := by
  intro h
  exact tmVerifierStackReadChoiceDomainCNFAt_satisfies_has_atom V t k cell a h

theorem tmVerifierStackTopDomainCNFAt_satisfies_has_atom
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment) :
    CNF.Satisfies (tmVerifierStackTopDomainCNFAt V t k) a →
      ∃ l ∈ tmVerifierStackCellChoiceLiteralsAt V t k 0, l.eval a = true := by
  intro h
  exact tmVerifierStackCellDomainCNFAt_satisfies_has_atom V t k 0 a h

/-! ### Bounded stack-domain blocks -/

/-- Cell coordinates whose successor is still inside `tmVerifierCellRange`. -/
noncomputable def tmVerifierCellSuccessorRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : List Nat :=
  List.range (tmVerifierCellBound V p)

/-- Cell-domain clauses for all bounded cells of one stack at one time row. -/
noncomputable def tmVerifierStackCellDomainsCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierCellRange V p).flatMap fun cell =>
    tmVerifierStackCellDomainCNFAt V t k cell

theorem tmVerifierStackCellDomainsCNFAt_satisfies_cell
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellRange V p) :
    ∃ l ∈ tmVerifierStackCellChoiceLiteralsAt V t k cell, l.eval a = true := by
  have hDomain : CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierStackCellDomainsCNFAt]
      exact ⟨cell, hcell, hc⟩)
  exact tmVerifierStackCellDomainCNFAt_satisfies_has_atom V t k cell a hDomain

/-! ### Empty-tail prefix constraints -/

/-- If a bounded stack cell is empty, then its successor cell is empty as well. -/
noncomputable def tmVerifierStackEmptyTailClause
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : Clause :=
  tmVerifierImplicationClause
    [tmVerifierStackEmptyAtom V t k cell]
    (tmVerifierStackEmptyAtom V t k (cell + 1))

theorem tmVerifierStackEmptyTailClause_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment) :
    CNF.Satisfies [tmVerifierStackEmptyTailClause V t k cell] a →
      (tmVerifierStackEmptyAtom V t k cell).eval a = true →
        (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  intro h hEmpty
  exact tmVerifierImplicationClause_satisfies_of_antecedents
    [tmVerifierStackEmptyAtom V t k cell]
    (tmVerifierStackEmptyAtom V t k (cell + 1)) a h (by
      intro l hl
      have hl' : l = tmVerifierStackEmptyAtom V t k cell := by
        simpa using hl
      simpa [hl'] using hEmpty)

/-- Empty-tail monotonicity clauses for one stack over the bounded successor range. -/
noncomputable def tmVerifierStackEmptyTailCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierCellSuccessorRange V p).map fun cell =>
    tmVerifierStackEmptyTailClause V t k cell

theorem tmVerifierStackEmptyTailCNFAt_satisfies_successor
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k) a)
    (hcell : cell ∈ tmVerifierCellSuccessorRange V p)
    (hEmpty : (tmVerifierStackEmptyAtom V t k cell).eval a = true) :
    (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  have hClause : CNF.Satisfies [tmVerifierStackEmptyTailClause V t k cell] a := by
    intro c hc
    have hc' : c = tmVerifierStackEmptyTailClause V t k cell := by
      simpa using hc
    subst c
    exact h _ (by
      simp [tmVerifierStackEmptyTailCNFAt]
      exact ⟨cell, hcell, rfl⟩)
  exact tmVerifierStackEmptyTailClause_satisfies V t k cell a hClause hEmpty

/-! ### Combined well-formedness blocks -/

/-- A sentinel clause forcing the final bounded cell to be empty. -/
noncomputable def tmVerifierStackFinalEmptyCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  [[tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)]]

theorem tmVerifierStackFinalEmptyCNFAt_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k) a) :
    (tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)).eval a = true := by
  have hClause :
      Clause.Satisfies [tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)] a := by
    exact h _ (by simp [tmVerifierStackFinalEmptyCNFAt])
  rcases hClause with ⟨l, hl, heval⟩
  have hlit : l = tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p) := by
    simpa using hl
  simpa [hlit] using heval

/-- Domain, empty-tail, and final-empty clauses for one stack at one time row. -/
noncomputable def tmVerifierStackWellFormedCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierStackCellDomainsCNFAt V p t k ++
    tmVerifierStackEmptyTailCNFAt V p t k) ++
      tmVerifierStackFinalEmptyCNFAt V p t k

theorem tmVerifierStackWellFormedCNFAt_satisfies_domains
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p t k) a := by
  have hPair :
      CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p t k ++
            tmVerifierStackEmptyTailCNFAt V p t k) a ∧
        CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k) a := by
    exact (CNF.satisfies_append
      (tmVerifierStackCellDomainsCNFAt V p t k ++
        tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierStackFinalEmptyCNFAt V p t k) a).1
        (by simpa [tmVerifierStackWellFormedCNFAt] using h)
  exact (CNF.satisfies_append
    (tmVerifierStackCellDomainsCNFAt V p t k)
    (tmVerifierStackEmptyTailCNFAt V p t k) a).1 hPair.1 |>.1

theorem tmVerifierStackWellFormedCNFAt_satisfies_emptyTail
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    CNF.Satisfies (tmVerifierStackEmptyTailCNFAt V p t k) a := by
  have hPair :
      CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p t k ++
            tmVerifierStackEmptyTailCNFAt V p t k) a ∧
        CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k) a := by
    exact (CNF.satisfies_append
      (tmVerifierStackCellDomainsCNFAt V p t k ++
        tmVerifierStackEmptyTailCNFAt V p t k)
      (tmVerifierStackFinalEmptyCNFAt V p t k) a).1
        (by simpa [tmVerifierStackWellFormedCNFAt] using h)
  exact (CNF.satisfies_append
    (tmVerifierStackCellDomainsCNFAt V p t k)
    (tmVerifierStackEmptyTailCNFAt V p t k) a).1 hPair.1 |>.2

theorem tmVerifierStackWellFormedCNFAt_satisfies_finalEmptyCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    CNF.Satisfies (tmVerifierStackFinalEmptyCNFAt V p t k) a := by
  exact (CNF.satisfies_append
    (tmVerifierStackCellDomainsCNFAt V p t k ++
      tmVerifierStackEmptyTailCNFAt V p t k)
    (tmVerifierStackFinalEmptyCNFAt V p t k) a).1
      (by simpa [tmVerifierStackWellFormedCNFAt] using h) |>.2

theorem tmVerifierStackWellFormedCNFAt_satisfies_finalEmpty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p t k) a) :
    (tmVerifierStackEmptyAtom V t k (tmVerifierCellBound V p)).eval a = true :=
  tmVerifierStackFinalEmptyCNFAt_satisfies V p t k a
    (tmVerifierStackWellFormedCNFAt_satisfies_finalEmptyCNF V p t k a h)

/-- Domain, empty-tail, and final-empty clauses for every stack at one time row. -/
noncomputable def tmVerifierAllStackWellFormedCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  (tmVerifierStackList V).flatMap fun k =>
    tmVerifierStackWellFormedCNFAt V p t k

end SAT
end ComplexityReduction
