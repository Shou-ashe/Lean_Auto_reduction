/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMActiveSymbols

/-!
Input/output stack CNF blocks for the future standard-TM Cook-Levin tableau.

This slice only talks about the stacks whose alphabets are available from the
`TM2ComputableInPolyTime` verifier witness: the input stack and the output stack.
Internal-stack transition clauses still need a finite active-symbol boundary
before they can be generated soundly.
-/

namespace ComplexityReduction
namespace SAT

/-- Positive atom saying that the input stack has symbol `s` at a cell. -/
noncomputable def tmVerifierInputStackSymbolAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t cell : Nat)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) : Literal :=
  tmVerifierStackSymbolAtom V t (tmVerifierTM V).k₀ cell
    (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)

/-- Positive atom saying that the output stack has symbol `s` at a cell. -/
noncomputable def tmVerifierOutputStackSymbolAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t cell : Nat)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) : Literal :=
  tmVerifierStackSymbolAtom V t (tmVerifierTM V).k₁ cell
    (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)

/-! ### Initial input-stack clauses -/

/-- Symbol literals for the initial input stack at time zero. -/
noncomputable def tmVerifierInputStackSymbolLiterals {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : List Literal :=
  (tmVerifierInputWord V p).zipIdx.map fun entry =>
    tmVerifierInputStackSymbolAtom V 0 entry.2 entry.1

/-- Empty-tail literals for cells beyond the initial input word. -/
noncomputable def tmVerifierInputStackEmptyTailLiterals {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : List Literal :=
  (tmVerifierTailCells V p (tmVerifierInputWord V p).length).map fun cell =>
    tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell

/-- Initial input-stack clauses: concrete input symbols plus empty cells after the word. -/
noncomputable def tmVerifierInputStackInitialCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  tmVerifierUnitClauses
    (tmVerifierInputStackSymbolLiterals V p ++ tmVerifierInputStackEmptyTailLiterals V p)

/-- All stack indices except the verifier input stack. -/
noncomputable def tmVerifierNonInputStacks {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (tmVerifierStackIndex V) :=
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  letI : DecidableEq (tmVerifierTM V).K := (tmVerifierTM V).kDecidableEq
  ((Finset.univ : Finset (tmVerifierStackIndex V)).filter
    (fun k => k ≠ (tmVerifierTM V).k₀)).toList

/-- Initial empty-stack literals for all non-input stacks over the bounded cell range. -/
noncomputable def tmVerifierInitialNonInputEmptyLiterals {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : List Literal :=
  (tmVerifierNonInputStacks V).flatMap fun k =>
    (tmVerifierCellRange V p).map fun cell => tmVerifierStackEmptyAtom V 0 k cell

/-- Initial non-input stack clauses: every bounded cell is empty. -/
noncomputable def tmVerifierInitialNonInputEmptyStackCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  tmVerifierUnitClauses (tmVerifierInitialNonInputEmptyLiterals V p)

/-- Complete initial stack I/O block for a fixed instance/certificate pair. -/
noncomputable def tmVerifierInitialStackCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : CNF :=
  tmVerifierInputStackInitialCNF V p ++ tmVerifierInitialNonInputEmptyStackCNF V p

/-! ### Output-true clauses -/

/-- Symbol literals forcing the output stack to contain the Boolean `true` word at time `t`. -/
noncomputable def tmVerifierOutputTrueSymbolLiteralsAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : List Literal :=
  (tmVerifierBoolOutputWord V true).zipIdx.map fun entry =>
    tmVerifierOutputStackSymbolAtom V t entry.2 entry.1

/-- Empty-tail literals beyond the Boolean `true` output word at time `t`. -/
noncomputable def tmVerifierOutputTrueEmptyTailLiteralsAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    List Literal :=
  (tmVerifierTailCells V p (tmVerifierBoolOutputWord V true).length).map fun cell =>
    tmVerifierStackEmptyAtom V t (tmVerifierTM V).k₁ cell

/-- Output-stack clauses forcing exactly the known `true` word and an empty tail. -/
noncomputable def tmVerifierOutputTrueStackCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  tmVerifierUnitClauses
    (tmVerifierOutputTrueSymbolLiteralsAt V t ++
      tmVerifierOutputTrueEmptyTailLiteralsAt V p t)

/-- All stack indices except the verifier output stack. -/
noncomputable def tmVerifierNonOutputStacks {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (tmVerifierStackIndex V) :=
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  letI : DecidableEq (tmVerifierTM V).K := (tmVerifierTM V).kDecidableEq
  ((Finset.univ : Finset (tmVerifierStackIndex V)).filter
    (fun k => k ≠ (tmVerifierTM V).k₁)).toList

/-- Empty-stack literals for all non-output stacks at a proposed accepting row. -/
noncomputable def tmVerifierOutputTrueNonOutputEmptyLiteralsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : List Literal :=
  (tmVerifierNonOutputStacks V).flatMap fun k =>
    (tmVerifierCellRange V p).map fun cell => tmVerifierStackEmptyAtom V t k cell

/-- Clauses forcing all non-output stacks to be empty at a proposed accepting row. -/
noncomputable def tmVerifierOutputTrueNonOutputEmptyStackCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  tmVerifierUnitClauses (tmVerifierOutputTrueNonOutputEmptyLiteralsAt V p t)

/-- Complete output-true stack block at a proposed accepting row. -/
noncomputable def tmVerifierOutputTrueCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) : CNF :=
  tmVerifierOutputTrueStackCNFAt V p t ++
    tmVerifierOutputTrueNonOutputEmptyStackCNFAt V p t

/-! ### Configuration semantics for the generated input/output clauses -/

@[simp]
theorem tmVerifierInitialCfg_input_stack {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) :
    (tmVerifierInitialCfg V p).stk (tmVerifierTM V).k₀ = tmVerifierInputWord V p := by
  simp [tmVerifierInitialCfg, Turing.initList]

theorem tmVerifierInitialCfg_noninput_stack_empty {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (k : tmVerifierStackIndex V) (h : k ≠ (tmVerifierTM V).k₀) :
    (tmVerifierInitialCfg V p).stk k = [] := by
  simp [tmVerifierInitialCfg, Turing.initList, h]

@[simp]
theorem tmVerifierOutputCfg_output_stack {L : EncodedDecisionProblem}
    (V : TMVerifier L) (b : Bool) :
    (tmVerifierOutputCfg V b).stk (tmVerifierTM V).k₁ = tmVerifierBoolOutputWord V b := by
  simp [tmVerifierOutputCfg, Turing.haltList]

theorem tmVerifierOutputCfg_nonoutput_stack_empty {L : EncodedDecisionProblem}
    (V : TMVerifier L) (b : Bool) (k : tmVerifierStackIndex V)
    (h : k ≠ (tmVerifierTM V).k₁) :
    (tmVerifierOutputCfg V b).stk k = [] := by
  simp [tmVerifierOutputCfg, Turing.haltList, h]

theorem tmVerifierInitialCfg_input_stack_get? {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (cell : Nat) :
    ((tmVerifierInitialCfg V p).stk (tmVerifierTM V).k₀)[cell]? =
      (tmVerifierInputWord V p)[cell]? := by
  simp

theorem tmVerifierOutputCfg_output_stack_get? {L : EncodedDecisionProblem}
    (V : TMVerifier L) (b : Bool) (cell : Nat) :
    ((tmVerifierOutputCfg V b).stk (tmVerifierTM V).k₁)[cell]? =
      (tmVerifierBoolOutputWord V b)[cell]? := by
  simp

theorem tmVerifierInputStackInitialCNF_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment) :
    CNF.Satisfies (tmVerifierInputStackInitialCNF V p) a ↔
      ∀ l ∈
        tmVerifierInputStackSymbolLiterals V p ++ tmVerifierInputStackEmptyTailLiterals V p,
          l.eval a = true := by
  simp [tmVerifierInputStackInitialCNF, tmVerifierUnitClauses_satisfies]

theorem tmVerifierInitialStackCNF_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (a : Assignment) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p) a ↔
      (∀ l ∈
        tmVerifierInputStackSymbolLiterals V p ++ tmVerifierInputStackEmptyTailLiterals V p,
          l.eval a = true) ∧
      (∀ l ∈ tmVerifierInitialNonInputEmptyLiterals V p, l.eval a = true) := by
  simp [tmVerifierInitialStackCNF, CNF.satisfies_append,
    tmVerifierInputStackInitialCNF_satisfies, tmVerifierInitialNonInputEmptyStackCNF,
    tmVerifierUnitClauses_satisfies]

theorem tmVerifierOutputTrueCNFAt_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (a : Assignment) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p t) a ↔
      (∀ l ∈
        tmVerifierOutputTrueSymbolLiteralsAt V t ++
          tmVerifierOutputTrueEmptyTailLiteralsAt V p t,
          l.eval a = true) ∧
      (∀ l ∈ tmVerifierOutputTrueNonOutputEmptyLiteralsAt V p t, l.eval a = true) := by
  simp [tmVerifierOutputTrueCNFAt, CNF.satisfies_append, tmVerifierOutputTrueStackCNFAt,
    tmVerifierOutputTrueNonOutputEmptyStackCNFAt, tmVerifierUnitClauses_satisfies]

end SAT
end ComplexityReduction
