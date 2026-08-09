/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.SatLike
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SAT

/-!
The local 3SAT target as both a `SatLikeProblem` and an encoded decision
problem.
-/

namespace ComplexityReduction
namespace SAT

open ComplexityReduction

/-- Finite alphabet used by the local 3CNF encoding. -/
abbrev ThreeSATSymbol : Type :=
  Option (Bool ⊕ Bool)

namespace ThreeSATEncoding

/-- Field delimiter. -/
def delimiter : ThreeSATSymbol :=
  none

/-- Tag token: `false` for a literal polarity field, `true` for a variable field. -/
def tagToken (b : Bool) : ThreeSATSymbol :=
  some (Sum.inl b)

/-- Unary natural-number bit token. -/
def bitToken (b : Bool) : ThreeSATSymbol :=
  some (Sum.inr b)

/-- Encode a natural number using the shared unary encoding. -/
def encodeNat (n : Nat) : List ThreeSATSymbol :=
  (EncodedType.nat.encode n).map bitToken

/-- Encode one literal as polarity and variable fields. -/
def encodeLiteral (l : Literal) : List ThreeSATSymbol :=
  [delimiter, tagToken false, bitToken l.neg, delimiter, tagToken true] ++ encodeNat l.var

/-- Encode one clause. -/
def encodeClause (c : Clause) : List ThreeSATSymbol :=
  [delimiter] ++ c.flatMap encodeLiteral

/-- Encode a bundled 3CNF by encoding its underlying clauses. -/
def encodeThreeCNF (φ : ThreeCNF) : List ThreeSATSymbol :=
  φ.clauses.flatMap encodeClause

end ThreeSATEncoding

/-- Concrete finite-alphabet encoding for bundled 3CNF formulas. -/
def threeCNFEncodedType : EncodedType where
  Carrier := ThreeCNF
  Symbol := ThreeSATSymbol
  finite_symbol := inferInstance
  encode := ThreeSATEncoding.encodeThreeCNF

/-- The local 3SAT problem viewed through the satisfiability-style interface. -/
def threeSATSatLike : SatLikeProblem where
  Inst := threeCNFEncodedType
  Assignment := fun _ => Assignment
  Satisfies := fun φ a => φ.Satisfies a

/-- The encoded decision problem induced by local 3SAT satisfiability. -/
def threeSATDecisionProblem : EncodedDecisionProblem :=
  threeSATSatLike.toDecisionProblem

@[simp]
theorem threeSATDecisionProblem_isYes_iff (φ : ThreeCNF) :
    threeSATDecisionProblem.isYes φ ↔ φ.Satisfiable :=
  Iff.rfl

end SAT
end ComplexityReduction
