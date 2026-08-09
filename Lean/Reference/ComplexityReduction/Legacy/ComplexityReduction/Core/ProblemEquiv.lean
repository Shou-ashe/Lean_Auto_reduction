/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.Reduction

namespace ComplexityReduction

/--
A polynomial-time semantic equivalence between encoded decision problems.

This is the transport layer for representation changes. It deliberately asks only for
many-one correctness in both directions, not definitional equality of encodings or syntax.
-/
structure ProblemEquivM (M : PolyTimeModel) (A B : EncodedDecisionProblem) where
  toMap : PolyTimeMap M A.Instance B.Instance
  invMap : PolyTimeMap M B.Instance A.Instance
  to_correct : ∀ x, A.isYes x ↔ B.isYes (toMap.toFun x)
  inv_correct : ∀ y, B.isYes y ↔ A.isYes (invMap.toFun y)

namespace ProblemEquivM

/-- Reflexive problem equivalence. -/
def refl (M : PolyTimeModel) (A : EncodedDecisionProblem) : ProblemEquivM M A A where
  toMap := PolyTimeMap.id M A.Instance
  invMap := PolyTimeMap.id M A.Instance
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

/-- Symmetry of problem equivalence. -/
def symm {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : ProblemEquivM M A B) : ProblemEquivM M B A where
  toMap := e.invMap
  invMap := e.toMap
  to_correct := e.inv_correct
  inv_correct := e.to_correct

/-- Transitivity of problem equivalence. -/
def trans {M : PolyTimeModel} {A B C : EncodedDecisionProblem}
    (eAB : ProblemEquivM M A B) (eBC : ProblemEquivM M B C) :
    ProblemEquivM M A C where
  toMap := PolyTimeMap.comp eBC.toMap eAB.toMap
  invMap := PolyTimeMap.comp eAB.invMap eBC.invMap
  to_correct := fun x => Iff.trans (eAB.to_correct x) (eBC.to_correct (eAB.toMap.toFun x))
  inv_correct := fun z =>
    Iff.trans (eBC.inv_correct z) (eAB.inv_correct (eBC.invMap.toFun z))

/-- Use the forward direction as a Karp reduction. -/
def toKarpReductionM {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : ProblemEquivM M A B) : KarpReductionM M A B where
  f := e.toMap
  correct := e.to_correct

/-- Use the inverse direction as a Karp reduction. -/
def invKarpReductionM {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : ProblemEquivM M A B) : KarpReductionM M B A where
  f := e.invMap
  correct := e.inv_correct

/-- Problem equivalence gives reducibility in the forward direction. -/
theorem toReducible {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : ProblemEquivM M A B) : PolyReducibleM M A B :=
  ⟨e.toKarpReductionM⟩

/-- Problem equivalence gives reducibility in the inverse direction. -/
theorem invReducible {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : ProblemEquivM M A B) : PolyReducibleM M B A :=
  ⟨e.invKarpReductionM⟩

/--
Transport a reduction across equivalent source and target representations.

If `A` is equivalent to `A'`, `B` is equivalent to `B'`, and the reduction has already
been proved in the normalized representation `A' <= B'`, then this produces the
concrete reduction `A <= B`.
-/
theorem transport {M : PolyTimeModel} {A A' B B' : EncodedDecisionProblem}
    (eA : ProblemEquivM M A A') (eB : ProblemEquivM M B B')
    (h : PolyReducibleM M A' B') :
    PolyReducibleM M A B := by
  rcases h with ⟨r⟩
  exact ⟨{
    f := PolyTimeMap.comp eB.invMap (PolyTimeMap.comp r.f eA.toMap)
    correct := fun x =>
      Iff.trans (eA.to_correct x)
        (Iff.trans (r.correct (eA.toMap.toFun x))
          (eB.inv_correct (r.f.toFun (eA.toMap.toFun x)))) }⟩

/-- Transport only the source representation of a reduction. -/
theorem transportSource {M : PolyTimeModel} {A A' B : EncodedDecisionProblem}
    (eA : ProblemEquivM M A A') (h : PolyReducibleM M A' B) :
    PolyReducibleM M A B :=
  transport eA (refl M B) h

/-- Transport only the target representation of a reduction. -/
theorem transportTarget {M : PolyTimeModel} {A B B' : EncodedDecisionProblem}
    (eB : ProblemEquivM M B B') (h : PolyReducibleM M A B') :
    PolyReducibleM M A B :=
  transport (refl M A) eB h

/-- Build a problem equivalence from two predicates over the same encoding. -/
def ofPredicateIff (M : PolyTimeModel) (X : EncodedType) (A B : X.Carrier → Prop)
    (h : ∀ x, A x ↔ B x) :
    ProblemEquivM M
      ({ Instance := X, isYes := A } : EncodedDecisionProblem)
      ({ Instance := X, isYes := B } : EncodedDecisionProblem) where
  toMap := PolyTimeMap.id M X
  invMap := PolyTimeMap.id M X
  to_correct := h
  inv_correct := fun x => (h x).symm

/--
Lift a polynomial-time equivalence of encodings to a problem equivalence, when the
predicate is preserved by the forward map.
-/
def ofPolyTimeEquiv {M : PolyTimeModel} {A B : EncodedDecisionProblem}
    (e : PolyTimeEquiv M A.Instance B.Instance)
    (hPredicate : ∀ x, A.isYes x ↔ B.isYes (e.toMap.toFun x)) :
    ProblemEquivM M A B where
  toMap := e.toMap
  invMap := e.invMap
  to_correct := hPredicate
  inv_correct := by
    intro y
    have hRight :
        B.isYes y ↔ B.isYes (e.toMap.toFun (e.invMap.toFun y)) := by
      rw [e.right_inv y]
    exact hRight.trans (hPredicate (e.invMap.toFun y)).symm

end ProblemEquivM

end ComplexityReduction
