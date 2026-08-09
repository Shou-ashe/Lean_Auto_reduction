/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.BoolRel

/-!
Standard Boolean relations for concrete CSP decision problems.

These constructors keep common relations in one reusable place.  The example
files package them as fixed finite languages and inherit the generic
Boolean-CSP-to-3SAT reductions.
-/

namespace ComplexityReduction
namespace CSP

namespace BoolRel

/-- Build a Boolean relation from a decidable predicate on tuples. -/
noncomputable def ofPredicate (k : Nat) (p : BoolTuple k → Prop) [DecidablePred p] : BoolRel where
  arity := k
  accepts := Finset.univ.filter p

@[simp]
theorem ofPredicate_arity (k : Nat) (p : BoolTuple k → Prop) [DecidablePred p] :
    (ofPredicate k p).arity = k :=
  rfl

@[simp]
theorem holds_ofPredicate_iff (k : Nat) (p : BoolTuple k → Prop) [DecidablePred p]
    (t : BoolTuple k) :
    (ofPredicate k p).Holds t ↔ p t := by
  classical
  change t ∈ (Finset.univ.filter p : Finset (BoolTuple k)) ↔ p t
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩

end BoolRel

namespace StandardRelations

/-- Interpret a relation-level negation flag as a literal value. -/
def literalValue (neg : Bool) (b : Bool) : Bool :=
  if neg then !b else b

/-- Number of true entries in a Boolean tuple. -/
def trueCount (k : Nat) (t : BoolTuple k) : Nat :=
  ((Finset.univ : Finset (Fin k)).filter fun i => t i = true).card

/-- The relation accepting tuples with exactly `n` true entries. -/
noncomputable def exactlyRel (k n : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => trueCount k t = n

/-- The ternary one-in-three relation. -/
noncomputable def exactlyOne3Rel : BoolRel :=
  exactlyRel 3 1

/-- The relation accepting tuples whose entries are not all equal. -/
noncomputable def notAllEqualRel (k : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => ∃ i j : Fin k, t i ≠ t j

/-- The ternary not-all-equal relation used by NAE-3SAT. -/
noncomputable def notAllEqual3Rel : BoolRel :=
  notAllEqualRel 3

/-- A `k`-literal clause relation with one negation flag per coordinate. -/
noncomputable def clauseRel (k : Nat) (neg : Fin k → Bool) : BoolRel :=
  BoolRel.ofPredicate k fun t => ∃ i : Fin k, literalValue (neg i) (t i) = true

/-- A binary clause relation, parameterized by the two literal polarities. -/
noncomputable def binaryClauseRel (leftNeg rightNeg : Bool) : BoolRel :=
  clauseRel 2 fun
    | ⟨0, _⟩ => leftNeg
    | ⟨1, _⟩ => rightNeg

/-- A ternary clause relation, parameterized by the three literal polarities. -/
noncomputable def ternaryClauseRel (firstNeg secondNeg thirdNeg : Bool) : BoolRel :=
  clauseRel 3 fun
    | ⟨0, _⟩ => firstNeg
    | ⟨1, _⟩ => secondNeg
    | ⟨2, _⟩ => thirdNeg

/-- The binary implication relation `x -> y`. -/
noncomputable def implicationRel : BoolRel :=
  BoolRel.ofPredicate 2 fun t =>
    literalValue true (t ⟨0, by decide⟩) = true ∨
      literalValue false (t ⟨1, by decide⟩) = true

/-- The binary disequality/XOR relation. -/
noncomputable def xorRel : BoolRel :=
  BoolRel.ofPredicate 2 fun t => t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩

/-- The relation accepting tuples whose number of true entries has a fixed parity. -/
noncomputable def parityRel (k parity : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => trueCount k t % 2 = parity % 2

/-- The ternary odd-parity relation `x xor y xor z = true`. -/
noncomputable def oddParity3Rel : BoolRel :=
  parityRel 3 1

/-- The ternary even-parity relation `x xor y xor z = false`. -/
noncomputable def evenParity3Rel : BoolRel :=
  parityRel 3 0

/-- Unary pinning to true. -/
noncomputable def pinTrueRel : BoolRel :=
  BoolRel.ofPredicate 1 fun t => t ⟨0, by decide⟩ = true

/-- Unary pinning to false. -/
noncomputable def pinFalseRel : BoolRel :=
  BoolRel.ofPredicate 1 fun t => t ⟨0, by decide⟩ = false

@[simp]
theorem exactlyRel_arity (k n : Nat) :
    (exactlyRel k n).arity = k :=
  rfl

@[simp]
theorem exactlyOne3Rel_arity :
    exactlyOne3Rel.arity = 3 :=
  rfl

@[simp]
theorem notAllEqualRel_arity (k : Nat) :
    (notAllEqualRel k).arity = k :=
  rfl

@[simp]
theorem notAllEqual3Rel_arity :
    notAllEqual3Rel.arity = 3 :=
  rfl

@[simp]
theorem clauseRel_arity (k : Nat) (neg : Fin k → Bool) :
    (clauseRel k neg).arity = k :=
  rfl

@[simp]
theorem binaryClauseRel_arity (leftNeg rightNeg : Bool) :
    (binaryClauseRel leftNeg rightNeg).arity = 2 :=
  rfl

@[simp]
theorem ternaryClauseRel_arity (firstNeg secondNeg thirdNeg : Bool) :
    (ternaryClauseRel firstNeg secondNeg thirdNeg).arity = 3 :=
  rfl

@[simp]
theorem implicationRel_arity :
    implicationRel.arity = 2 :=
  rfl

@[simp]
theorem xorRel_arity :
    xorRel.arity = 2 :=
  rfl

@[simp]
theorem parityRel_arity (k parity : Nat) :
    (parityRel k parity).arity = k :=
  rfl

@[simp]
theorem oddParity3Rel_arity :
    oddParity3Rel.arity = 3 :=
  rfl

@[simp]
theorem evenParity3Rel_arity :
    evenParity3Rel.arity = 3 :=
  rfl

@[simp]
theorem pinTrueRel_arity :
    pinTrueRel.arity = 1 :=
  rfl

@[simp]
theorem pinFalseRel_arity :
    pinFalseRel.arity = 1 :=
  rfl

end StandardRelations

end CSP
end ComplexityReduction
