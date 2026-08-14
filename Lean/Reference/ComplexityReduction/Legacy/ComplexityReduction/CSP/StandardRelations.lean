/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.BoolRel
import Mathlib.Tactic.FinCases

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
def ofPredicate (k : Nat) (p : BoolTuple k → Prop) [DecidablePred p] : BoolRel where
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
def exactlyRel (k n : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => trueCount k t = n

/-- The ternary one-in-three relation. -/
noncomputable def exactlyOne3Rel : BoolRel :=
  exactlyRel 3 1

/-- The relation accepting tuples whose entries are not all equal. -/
def notAllEqualRel (k : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => ∃ i j : Fin k, t i ≠ t j

/-- The ternary not-all-equal relation used by NAE-3SAT. -/
def notAllEqual3Rel : BoolRel :=
  notAllEqualRel 3

/-- A `k`-literal clause relation with one negation flag per coordinate. -/
def clauseRel (k : Nat) (neg : Fin k → Bool) : BoolRel :=
  BoolRel.ofPredicate k fun t => ∃ i : Fin k, literalValue (neg i) (t i) = true

/-- A binary clause relation, parameterized by the two literal polarities. -/
def binaryClauseRel (leftNeg rightNeg : Bool) : BoolRel :=
  clauseRel 2 fun
    | ⟨0, _⟩ => leftNeg
    | ⟨1, _⟩ => rightNeg

/-- A ternary clause relation, parameterized by the three literal polarities. -/
def ternaryClauseRel (firstNeg secondNeg thirdNeg : Bool) : BoolRel :=
  clauseRel 3 fun
    | ⟨0, _⟩ => firstNeg
    | ⟨1, _⟩ => secondNeg
    | ⟨2, _⟩ => thirdNeg

/-- The binary implication relation `x -> y`. -/
def implicationRel : BoolRel :=
  BoolRel.ofPredicate 2 fun t =>
    literalValue true (t ⟨0, by decide⟩) = true ∨
      literalValue false (t ⟨1, by decide⟩) = true

/-- The binary disequality/XOR relation. -/
def xorRel : BoolRel :=
  BoolRel.ofPredicate 2 fun t => t ⟨0, by decide⟩ ≠ t ⟨1, by decide⟩

/-- The relation accepting tuples whose number of true entries has a fixed parity. -/
def parityRel (k parity : Nat) : BoolRel :=
  BoolRel.ofPredicate k fun t => trueCount k t % 2 = parity % 2

/-- The ternary odd-parity relation `x xor y xor z = true`. -/
def oddParity3Rel : BoolRel :=
  parityRel 3 1

/-- The ternary even-parity relation `x xor y xor z = false`. -/
def evenParity3Rel : BoolRel :=
  parityRel 3 0

/-- Unary pinning to true. -/
def pinTrueRel : BoolRel :=
  BoolRel.ofPredicate 1 fun t => t ⟨0, by decide⟩ = true

/-- Unary pinning to false. -/
def pinFalseRel : BoolRel :=
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

/-! ### Ordered tuples and truth-table meaning of the not-all-equal relations -/

/-- An explicit ordered ternary Boolean tuple, independent of any reduction. -/
def tripleTuple (first second third : Bool) : BoolTuple 3 := fun
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨2, _⟩ => third

/-- An explicit ordered four-ary Boolean tuple, independent of any reduction. -/
def quadTuple (first second third fourth : Bool) : BoolTuple 4 := fun
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨2, _⟩ => third
  | ⟨3, _⟩ => fourth

/-- An explicit ordered five-ary Boolean tuple, independent of any reduction. -/
def quintTuple (first second third fourth fifth : Bool) : BoolTuple 5 := fun
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨2, _⟩ => third
  | ⟨3, _⟩ => fourth
  | ⟨4, _⟩ => fifth

/-- The truth-table meaning of the standard ternary not-all-equal relation. -/
theorem notAllEqual3Rel_holds_triple_iff (first second third : Bool) :
    notAllEqual3Rel.Holds (tripleTuple first second third) ↔
      ¬ (first = second ∧ second = third) := by
  classical
  unfold notAllEqual3Rel notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨left, right, different⟩ equalValues
    fin_cases left <;> fin_cases right <;>
      simp_all [tripleTuple]
  · intro notAllEqual
    by_cases firstSecond : first = second
    · have secondThird : second ≠ third := by
        intro secondThird
        exact notAllEqual ⟨firstSecond, secondThird⟩
      exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by
        simpa [tripleTuple] using secondThird⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by
        simpa [tripleTuple] using firstSecond⟩

/-- The truth-table meaning of the standard four-ary not-all-equal relation. -/
theorem notAllEqual4Rel_holds_quad_iff (first second third fourth : Bool) :
    (notAllEqualRel 4).Holds (quadTuple first second third fourth) ↔
      ¬ (first = second ∧ second = third ∧ third = fourth) := by
  classical
  unfold notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨left, right, different⟩ equalValues
    fin_cases left <;> fin_cases right <;>
      simp_all [quadTuple]
  · intro notAllEqual
    by_cases firstSecond : first = second
    · by_cases secondThird : second = third
      · have thirdFourth : third ≠ fourth := by
          intro thirdFourth
          exact notAllEqual ⟨firstSecond, secondThird, thirdFourth⟩
        exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by
          simpa [quadTuple] using thirdFourth⟩
      · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by
          simpa [quadTuple] using secondThird⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by
        simpa [quadTuple] using firstSecond⟩

/-- The truth-table meaning of the standard five-ary not-all-equal relation. -/
theorem notAllEqual5Rel_holds_quint_iff (first second third fourth fifth : Bool) :
    (notAllEqualRel 5).Holds (quintTuple first second third fourth fifth) ↔
      ¬ (first = second ∧ second = third ∧ third = fourth ∧ fourth = fifth) := by
  classical
  unfold notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨left, right, different⟩ equalValues
    fin_cases left <;> fin_cases right <;>
      simp_all [quintTuple]
  · intro notAllEqual
    by_cases firstSecond : first = second
    · by_cases secondThird : second = third
      · by_cases thirdFourth : third = fourth
        · have fourthFifth : fourth ≠ fifth := by
            intro fourthFifth
            exact notAllEqual ⟨firstSecond, secondThird, thirdFourth, fourthFifth⟩
          exact ⟨⟨3, by decide⟩, ⟨4, by decide⟩, by
            simpa [quintTuple] using fourthFifth⟩
        · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, by
            simpa [quintTuple] using thirdFourth⟩
      · exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by
          simpa [quintTuple] using secondThird⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by
        simpa [quintTuple] using firstSecond⟩

end StandardRelations

end CSP
end ComplexityReduction
