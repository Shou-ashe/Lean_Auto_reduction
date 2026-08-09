/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBounds

/-!
Certificate-independent CNF block families for the x-only global tableau.

These blocks are the parts of the global tableau whose finite ranges can already
be expressed from the x-only bounds.  Transition-window clauses are migrated in a
later file because they also mention the global micro-row coordinate inside
window antecedents and action effects.
-/

namespace ComplexityReduction
namespace SAT

/-! ### x-only bounded cell blocks -/

/-- Cell-domain clauses for all x-only bounded cells of one stack at one time row. -/
noncomputable def tmVerifierXOnlyStackCellDomainsCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierXOnlyCellRange V x).flatMap fun cell =>
    tmVerifierStackCellDomainCNFAt V t k cell

theorem tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_cell
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellRange V x) :
    ∃ l ∈ tmVerifierStackCellChoiceLiteralsAt V t k cell, l.eval a = true := by
  have hDomain : CNF.Satisfies (tmVerifierStackCellDomainCNFAt V t k cell) a := by
    intro c hc
    exact h c (by
      simp [tmVerifierXOnlyStackCellDomainsCNFAt]
      exact ⟨cell, hcell, hc⟩)
  exact tmVerifierStackCellDomainCNFAt_satisfies_has_atom V t k cell a hDomain

/-- Empty-tail monotonicity clauses over the x-only bounded successor range. -/
noncomputable def tmVerifierXOnlyStackEmptyTailCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierXOnlyCellSuccessorRange V x).map fun cell =>
    tmVerifierStackEmptyTailClause V t k cell

theorem tmVerifierXOnlyStackEmptyTailCNFAt_satisfies_successor
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (cell : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackEmptyTailCNFAt V x t k) a)
    (hcell : cell ∈ tmVerifierXOnlyCellSuccessorRange V x)
    (hEmpty : (tmVerifierStackEmptyAtom V t k cell).eval a = true) :
    (tmVerifierStackEmptyAtom V t k (cell + 1)).eval a = true := by
  have hClause : CNF.Satisfies [tmVerifierStackEmptyTailClause V t k cell] a := by
    intro c hc
    have hc' : c = tmVerifierStackEmptyTailClause V t k cell := by
      simpa using hc
    subst c
    exact h _ (by
      simp [tmVerifierXOnlyStackEmptyTailCNFAt]
      exact ⟨cell, hcell, rfl⟩)
  exact tmVerifierStackEmptyTailClause_satisfies V t k cell a hClause hEmpty

/-- Sentinel clause forcing the final x-only bounded cell to be empty. -/
noncomputable def tmVerifierXOnlyStackFinalEmptyCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  [[tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)]]

theorem tmVerifierXOnlyStackFinalEmptyCNFAt_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) a) :
    (tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)).eval a = true := by
  have hClause :
      Clause.Satisfies [tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)] a :=
    h _ (by simp [tmVerifierXOnlyStackFinalEmptyCNFAt])
  rcases hClause with ⟨l, hl, heval⟩
  have hlit : l = tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x) := by
    simpa using hl
  simpa [hlit] using heval

/-- Domain, empty-tail, and final-empty clauses for one x-only stack row. -/
noncomputable def tmVerifierXOnlyStackWellFormedCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V) : CNF :=
  (tmVerifierXOnlyStackCellDomainsCNFAt V x t k ++
    tmVerifierXOnlyStackEmptyTailCNFAt V x t k) ++
      tmVerifierXOnlyStackFinalEmptyCNFAt V x t k

theorem tmVerifierXOnlyStackWellFormedCNFAt_satisfies_domains
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a) :
    CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a := by
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
    (tmVerifierXOnlyStackEmptyTailCNFAt V x t k) a).1 hPair.1 |>.1

theorem tmVerifierXOnlyStackWellFormedCNFAt_satisfies_finalEmpty
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) (k : tmVerifierStackIndex V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackWellFormedCNFAt V x t k) a) :
    (tmVerifierStackEmptyAtom V t k (tmVerifierXOnlyCellBound V x)).eval a = true := by
  have hFinal :
      CNF.Satisfies (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) a :=
    (CNF.satisfies_append
      (tmVerifierXOnlyStackCellDomainsCNFAt V x t k ++
        tmVerifierXOnlyStackEmptyTailCNFAt V x t k)
      (tmVerifierXOnlyStackFinalEmptyCNFAt V x t k) a).1
        (by simpa [tmVerifierXOnlyStackWellFormedCNFAt] using h) |>.2
  exact tmVerifierXOnlyStackFinalEmptyCNFAt_satisfies V x t k a hFinal

/-- X-only well-formed rows for every stack at one time row. -/
noncomputable def tmVerifierXOnlyAllStackWellFormedCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  (tmVerifierStackList V).flatMap fun k =>
    tmVerifierXOnlyStackWellFormedCNFAt V x t k

/-- X-only stack well-formedness rows at every bounded macro time row. -/
noncomputable def tmVerifierXOnlyStackWellFormedRowsCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
    tmVerifierXOnlyAllStackWellFormedCNFAt V x t

/-! ### x-only initial stack and output endpoint blocks -/

/-- Empty-tail literals for cells beyond the x-only input length bound. -/
noncomputable def tmVerifierXOnlyInputStackEmptyTailLiterals
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : List Literal :=
  (tmVerifierXOnlyCellRange V x).filter (fun cell =>
      tmVerifierXOnlyInputLengthBound V x ≤ cell) |>.map fun cell =>
    tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell

/-- Initial input-stack clauses fixing only the instance prefix and the x-only tail. -/
noncomputable def tmVerifierXOnlyInputStackInitialCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierUnitClauses
    (tmVerifierInstanceInputPrefixLiterals V x ++
      tmVerifierXOnlyInputStackEmptyTailLiterals V x)

/-- Initial empty-stack literals for all non-input stacks over the x-only cell range. -/
noncomputable def tmVerifierXOnlyInitialNonInputEmptyLiterals
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : List Literal :=
  (tmVerifierNonInputStacks V).flatMap fun k =>
    (tmVerifierXOnlyCellRange V x).map fun cell => tmVerifierStackEmptyAtom V 0 k cell

/-- Initial non-input stack clauses over the x-only cell range. -/
noncomputable def tmVerifierXOnlyInitialNonInputEmptyStackCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierUnitClauses (tmVerifierXOnlyInitialNonInputEmptyLiterals V x)

/-- Complete x-only initial stack block. -/
noncomputable def tmVerifierXOnlyInitialStackCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierXOnlyInputStackInitialCNF V x ++
    tmVerifierXOnlyInitialNonInputEmptyStackCNF V x

/-- Output-stack empty-tail literals over the x-only cell range. -/
noncomputable def tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : List Literal :=
  (tmVerifierXOnlyCellRange V x).filter (fun cell =>
      (tmVerifierBoolOutputWord V true).length ≤ cell) |>.map fun cell =>
    tmVerifierStackEmptyAtom V t (tmVerifierTM V).k₁ cell

/-- Output-stack clauses at one row over the x-only cell range. -/
noncomputable def tmVerifierXOnlyOutputTrueStackCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  tmVerifierUnitClauses
    (tmVerifierOutputTrueSymbolLiteralsAt V t ++
      tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt V x t)

/-- Non-output stack empty literals at one output row over the x-only cell range. -/
noncomputable def tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : List Literal :=
  (tmVerifierNonOutputStacks V).flatMap fun k =>
    (tmVerifierXOnlyCellRange V x).map fun cell => tmVerifierStackEmptyAtom V t k cell

/-- Non-output stack empty clauses at one output row over the x-only cell range. -/
noncomputable def tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  tmVerifierUnitClauses (tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt V x t)

/-- Complete x-only output-true block at one row. -/
noncomputable def tmVerifierXOnlyOutputTrueCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (t : Nat) : CNF :=
  tmVerifierXOnlyOutputTrueStackCNFAt V x t ++
    tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt V x t

/-- Final halting/output-true endpoint block at the x-only time bound. -/
noncomputable def tmVerifierXOnlyEndpointCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x) ++
    tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
      (tmVerifierTM V).initialState) ++
    tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)

/-! ### x-only fixed micro-domain rows -/

/-- Stack well-formed rows for x-only global micro rows touched by one window. -/
noncomputable def tmVerifierXOnlyWindowFixedMicroDomainCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) : CNF :=
  (tmVerifierWindowMicroTimeRange V w).flatMap fun micro =>
    (tmVerifierStackList V).flatMap fun k =>
      tmVerifierXOnlyStackWellFormedCNFAt V x
        (tmVerifierXOnlyFixedMicroTime V x t micro) k

/-- X-only fixed micro-domain rows for every statement window of one transition row. -/
noncomputable def tmVerifierXOnlyTransitionFixedMicroDomainCNFAt
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (t : Nat) : CNF :=
  (tmVerifierLabelList V).flatMap fun l =>
    (tmVerifierStateList V).flatMap fun s =>
      (tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s).flatMap fun w =>
        tmVerifierXOnlyWindowFixedMicroDomainCNFAt V x t w

/-- X-only fixed micro-domain rows for every transition row with a successor. -/
noncomputable def tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyTransitionTimeRange V x).flatMap fun t =>
    tmVerifierXOnlyTransitionFixedMicroDomainCNFAt V x t

/-! ### x-only aggregate blocks before transition-window migration -/

/-- Named x-only blocks that do not require migrated transition-window clauses. -/
noncomputable def tmVerifierXOnlyGlobalTableauBaseBlocks
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List CNF :=
  [ (tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
      tmVerifierControlDomainCNFAt V t
  , tmVerifierInitialControlCNF V
  , tmVerifierXOnlyInitialStackCNF V x
  , tmVerifierXOnlyStackWellFormedRowsCNF V x
  , tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x
  , tmVerifierXOnlyEndpointCNF V x
  ]

/-- Aggregate x-only base CNF, excluding transition-window clauses for now. -/
noncomputable def tmVerifierXOnlyGlobalTableauBaseCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyGlobalTableauBaseBlocks V x).flatMap id

theorem tmVerifierXOnlyGlobalTableauBaseCNF_satisfies_block
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauBaseCNF V x) a)
    {block : CNF} (hblock : block ∈ tmVerifierXOnlyGlobalTableauBaseBlocks V x) :
    CNF.Satisfies block a := by
  intro c hc
  exact h c (by
    rw [tmVerifierXOnlyGlobalTableauBaseCNF]
    exact List.mem_flatMap.mpr ⟨block, hblock, hc⟩)

end SAT
end ComplexityReduction
