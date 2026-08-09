/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMControlBlocks

/-!
Low-level stack atom and I/O symbol codes for the standard-TM Cook-Levin tableau.

This file deliberately sits below `TMActiveSymbols`: it provides the raw atom
surface and role-tagged I/O payload codes without choosing which active payload
will be used for a concrete stack symbol in an assignment.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Stack and input/output symbol atoms -/

/-- Stable code for one stack index of the extracted verifier machine. -/
noncomputable def tmVerifierStackCode {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) : Nat :=
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  ((Fintype.equivFin (tmVerifierTM V).K) k).val

/-- Stable code for an input-stack symbol, transported through the verifier input alphabet. -/
noncomputable def tmVerifierInputSymbolCode {L : EncodedDecisionProblem}
    (V : TMVerifier L) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) : Nat :=
  letI : Fintype (tmVerifierInputEncodedType V).Symbol :=
    (tmVerifierInputEncodedType V).finite_symbol
  ((Fintype.equivFin (tmVerifierInputEncodedType V).Symbol)
    ((tmVerifierComputableWitness V).inputAlphabet s)).val

/-- Stable code for an output-stack symbol, transported through the verifier output alphabet. -/
noncomputable def tmVerifierOutputSymbolCode {L : EncodedDecisionProblem}
    (V : TMVerifier L) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) : Nat :=
  letI : Fintype EncodedType.bool.Symbol := EncodedType.bool.finite_symbol
  ((Fintype.equivFin EncodedType.bool.Symbol)
    ((tmVerifierComputableWitness V).outputAlphabet s)).val

/--
Role-tagged input/output symbols that can already be named without assuming a
finite alphabet for every internal stack.
-/
inductive TMVerifierIOSymbol {L : EncodedDecisionProblem} (V : TMVerifier L) : Type where
  | input : (tmVerifierTM V).Γ (tmVerifierTM V).k₀ → TMVerifierIOSymbol V
  | output : (tmVerifierTM V).Γ (tmVerifierTM V).k₁ → TMVerifierIOSymbol V

namespace TMVerifierIOSymbol

/-- Stable payload code for an already-audited input/output stack symbol. -/
noncomputable def code {L : EncodedDecisionProblem} {V : TMVerifier L} :
    TMVerifierIOSymbol V → Nat
  | input s => Nat.pair 0 (tmVerifierInputSymbolCode V s)
  | output s => Nat.pair 1 (tmVerifierOutputSymbolCode V s)

end TMVerifierIOSymbol

/-- Positive atom saying that stack `k` has the audited payload `payload` at a cell. -/
noncomputable def tmVerifierStackSymbolAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell payload : Nat) :
    Literal :=
  tmVerifierTableauAtom TMVerifierTableauVarKind.stackSymbol t (tmVerifierStackCode V k)
    cell payload

/-- Positive atom saying that stack `k` is empty at a cell coordinate. -/
noncomputable def tmVerifierStackEmptyAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : Literal :=
  tmVerifierTableauAtom TMVerifierTableauVarKind.stackEmpty t (tmVerifierStackCode V k)
    cell 0

/-- Negative atom saying that stack `k` is not empty at a cell coordinate. -/
noncomputable def negTMVerifierStackEmptyAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (k : tmVerifierStackIndex V) (cell : Nat) : Literal :=
  negTMVerifierTableauAtom TMVerifierTableauVarKind.stackEmpty t (tmVerifierStackCode V k)
    cell 0

/-! ### Unit-clause helpers and bounded cell ranges -/

/-- Convert literals into positive unit clauses. -/
def tmVerifierUnitClauses (ls : List Literal) : CNF :=
  ls.map fun l => [l]

theorem tmVerifierUnitClauses_satisfies (ls : List Literal) (a : Assignment) :
    CNF.Satisfies (tmVerifierUnitClauses ls) a ↔
      ∀ l ∈ ls, l.eval a = true := by
  simp [tmVerifierUnitClauses, CNF.Satisfies, Clause.Satisfies]

/-- Bounded cell coordinates for a verifier tableau associated to a fixed pair. -/
noncomputable def tmVerifierCellRange {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : List Nat :=
  List.range (tmVerifierCellBound V p + 1)

/-- Cells in the bounded tableau range at or beyond a concrete stack word length. -/
noncomputable def tmVerifierTailCells {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (len : Nat) : List Nat :=
  (tmVerifierCellRange V p).filter fun i => len ≤ i

end SAT
end ComplexityReduction
