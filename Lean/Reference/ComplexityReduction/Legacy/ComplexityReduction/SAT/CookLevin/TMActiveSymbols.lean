/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackAtoms

/-!
Finite active-symbol boundary for the future standard-TM Cook-Levin transition
clauses.

`FinTM2` provides finite control, finite states, and a finite input alphabet,
but not a uniform `Fintype (tm.Γ k)` for every stack.  This file therefore
records an auditable finite list of stack symbols that transition/window clauses
are allowed to name: all input/output stack symbols available through the
verifier witness, plus the finite images of every `push` instruction over the
finite internal-state set.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Active stack-symbol payloads -/

/-- A raw stack symbol paired with its stack index. -/
structure TMVerifierStackSymbol {L : EncodedDecisionProblem} (V : TMVerifier L) where
  stack : tmVerifierStackIndex V
  symbol : (tmVerifierTM V).Γ stack

/-- A stack symbol together with the SAT payload code used for its atom. -/
structure TMVerifierNamedStackSymbol {L : EncodedDecisionProblem} (V : TMVerifier L) where
  stack : tmVerifierStackIndex V
  payload : Nat
  symbol : (tmVerifierTM V).Γ stack

/-- Positive atom for one named active stack symbol. -/
noncomputable def tmVerifierNamedStackSymbolAtom {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t cell : Nat) (s : TMVerifierNamedStackSymbol V) : Literal :=
  tmVerifierStackSymbolAtom V t s.stack cell s.payload

/-- All input-stack symbols, named through the role-tagged input-symbol payload codes. -/
noncomputable def tmVerifierInputNamedStackSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierNamedStackSymbol V) :=
  letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := (tmVerifierTM V).Γk₀Fin
  letI : DecidableEq ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := Classical.decEq _
  ((Finset.univ : Finset ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)).toList).map
    fun s =>
      { stack := (tmVerifierTM V).k₀
        payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.input (V := V) s)
        symbol := s }

/-- All output-stack symbols, named through the role-tagged output-symbol payload codes. -/
noncomputable def tmVerifierOutputNamedStackSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierNamedStackSymbol V) :=
  letI : Fintype EncodedType.bool.Symbol := EncodedType.bool.finite_symbol
  letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₁) :=
    Fintype.ofEquiv EncodedType.bool.Symbol
      (tmVerifierComputableWitness V).outputAlphabet.symm
  letI : DecidableEq ((tmVerifierTM V).Γ (tmVerifierTM V).k₁) := Classical.decEq _
  ((Finset.univ : Finset ((tmVerifierTM V).Γ (tmVerifierTM V).k₁)).toList).map
    fun s =>
      { stack := (tmVerifierTM V).k₁
        payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.output (V := V) s)
        symbol := s }

/-- The finite input/output stack-symbol boundary available before inspecting transitions. -/
noncomputable def tmVerifierIONamedStackSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierNamedStackSymbol V) :=
  tmVerifierInputNamedStackSymbols V ++ tmVerifierOutputNamedStackSymbols V

/-! ### Push-symbol collection from the finite control graph -/

/-- The finite image of one `push` payload function over all internal states. -/
noncomputable def tmVerifierPushSymbolsFor {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V)
    (f : (tmVerifierTM V).σ → (tmVerifierTM V).Γ k) :
    List (TMVerifierStackSymbol V) :=
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  letI : DecidableEq (tmVerifierTM V).σ := Classical.decEq _
  ((Finset.univ : Finset (tmVerifierTM V).σ).toList).map
    fun s => { stack := k, symbol := f s }

/-- Raw stack symbols that may be pushed by a statement. -/
noncomputable def tmVerifierStmtPushSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : (tmVerifierTM V).Stmt → List (TMVerifierStackSymbol V)
  | Turing.TM2.Stmt.push k f q =>
      tmVerifierPushSymbolsFor V k f ++ tmVerifierStmtPushSymbols V q
  | Turing.TM2.Stmt.peek _ _ q => tmVerifierStmtPushSymbols V q
  | Turing.TM2.Stmt.pop _ _ q => tmVerifierStmtPushSymbols V q
  | Turing.TM2.Stmt.load _ q => tmVerifierStmtPushSymbols V q
  | Turing.TM2.Stmt.branch _ q₁ q₂ =>
      tmVerifierStmtPushSymbols V q₁ ++ tmVerifierStmtPushSymbols V q₂
  | Turing.TM2.Stmt.goto _ => []
  | Turing.TM2.Stmt.halt => []

/-- Raw stack symbols that may be pushed anywhere in the verifier control graph. -/
noncomputable def tmVerifierControlPushSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierStackSymbol V) :=
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI : DecidableEq (tmVerifierTM V).Λ := Classical.decEq _
  ((Finset.univ : Finset (tmVerifierTM V).Λ).toList).flatMap
    fun l => tmVerifierStmtPushSymbols V ((tmVerifierTM V).m l)

/-- Assign fresh payload codes to the finitely collected push symbols. -/
noncomputable def tmVerifierNamedPushedStackSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierNamedStackSymbol V) :=
  (tmVerifierControlPushSymbols V).zipIdx.map fun entry =>
    { stack := entry.1.stack
      payload := Nat.pair 2 entry.2
      symbol := entry.1.symbol }

/-- The full finite active-symbol boundary available to transition/window clauses. -/
noncomputable def tmVerifierActiveStackSymbols {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (TMVerifierNamedStackSymbol V) :=
  tmVerifierIONamedStackSymbols V ++ tmVerifierNamedPushedStackSymbols V

def tmVerifierStackSymbolActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (s : (tmVerifierTM V).Γ k) : Prop :=
  ∃ named ∈ tmVerifierActiveStackSymbols V, named.stack = k ∧ HEq named.symbol s

noncomputable def tmVerifierActiveStackSymbolPayload
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (s : (tmVerifierTM V).Γ k) : Nat := by
  classical
  exact if h : tmVerifierStackSymbolActive V k s then (Classical.choose h).payload else 0

/-! ### Boundary checks -/

theorem tmVerifierStackSymbolActive_input
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₀) :
    tmVerifierStackSymbolActive V (tmVerifierTM V).k₀ s := by
  refine
    ⟨{ stack := (tmVerifierTM V).k₀
       payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.input (V := V) s)
       symbol := s }, ?_, rfl, HEq.rfl⟩
  simp [tmVerifierActiveStackSymbols, tmVerifierIONamedStackSymbols,
    tmVerifierInputNamedStackSymbols]

theorem tmVerifierStackSymbolActive_output
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) :
    tmVerifierStackSymbolActive V (tmVerifierTM V).k₁ s := by
  refine
    ⟨{ stack := (tmVerifierTM V).k₁
       payload := TMVerifierIOSymbol.code (TMVerifierIOSymbol.output (V := V) s)
       symbol := s }, ?_, rfl, HEq.rfl⟩
  simp [tmVerifierActiveStackSymbols, tmVerifierIONamedStackSymbols,
    tmVerifierOutputNamedStackSymbols]

theorem tmVerifierPushSymbolsFor_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V)
    (f : (tmVerifierTM V).σ → (tmVerifierTM V).Γ k) (s : (tmVerifierTM V).σ) :
    ({ stack := k, symbol := f s } : TMVerifierStackSymbol V) ∈
      tmVerifierPushSymbolsFor V k f := by
  simp [tmVerifierPushSymbolsFor]

theorem tmVerifierStmtPushSymbols_push_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V)
    (f : (tmVerifierTM V).σ → (tmVerifierTM V).Γ k)
    (q : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) :
    ({ stack := k, symbol := f s } : TMVerifierStackSymbol V) ∈
      tmVerifierStmtPushSymbols V (Turing.TM2.Stmt.push k f q) := by
  simp [tmVerifierStmtPushSymbols, tmVerifierPushSymbolsFor_mem]

theorem tmVerifierControlPushSymbols_label_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (l : (tmVerifierTM V).Λ) (sym : TMVerifierStackSymbol V)
    (h : sym ∈ tmVerifierStmtPushSymbols V ((tmVerifierTM V).m l)) :
    sym ∈ tmVerifierControlPushSymbols V := by
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI : DecidableEq (tmVerifierTM V).Λ := Classical.decEq _
  simp [tmVerifierControlPushSymbols]
  exact ⟨l, h⟩

end SAT
end ComplexityReduction
