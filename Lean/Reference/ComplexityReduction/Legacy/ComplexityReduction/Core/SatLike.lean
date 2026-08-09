/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.ProblemEquiv

namespace ComplexityReduction

/--
A minimal satisfiability-style semantic interface.

The concrete syntax of instances is intentionally hidden. A problem exposes only encoded
instances, a witness/assignment type for each instance, and a satisfaction predicate.
-/
structure SatLikeProblem : Type 1 where
  Inst : EncodedType
  Assignment : Inst.Carrier → Type
  Satisfies : ∀ x, Assignment x → Prop

namespace SatLikeProblem

/-- The encoded decision problem induced by existential satisfaction. -/
def toDecisionProblem (P : SatLikeProblem) : EncodedDecisionProblem where
  Instance := P.Inst
  isYes := fun x => ∃ a, P.Satisfies x a

end SatLikeProblem

/--
A semantic map between satisfiability-style problems.

The assignment-level fields are optional data for review and later certificate extraction:
they make explicit the natural-language proof obligations "lift a satisfying assignment"
and "project a satisfying assignment back".
-/
structure SatLikeReduction (A B : SatLikeProblem) where
  map : A.Inst.Carrier → B.Inst.Carrier
  lift :
    ∀ x, A.Assignment x → B.Assignment (map x)
  project :
    ∀ x, B.Assignment (map x) → A.Assignment x
  lift_correct :
    ∀ x a, A.Satisfies x a → B.Satisfies (map x) (lift x a)
  project_correct :
    ∀ x b, B.Satisfies (map x) b → A.Satisfies x (project x b)

namespace SatLikeReduction

/-- A satisfiability-style reduction induces a plain semantic reduction. -/
def toSemanticReduction {A B : SatLikeProblem} (r : SatLikeReduction A B) :
    SemanticReduction A.toDecisionProblem B.toDecisionProblem where
  f := r.map
  correct := by
    intro x
    constructor
    · intro h
      rcases h with ⟨a, ha⟩
      exact ⟨r.lift x a, r.lift_correct x a ha⟩
    · intro h
      rcases h with ⟨b, hb⟩
      exact ⟨r.project x b, r.project_correct x b hb⟩

/-- Add a model-level polynomial-time certificate to a satisfiability-style reduction. -/
def toKarpReductionM {M : PolyTimeModel} {A B : SatLikeProblem}
    (r : SatLikeReduction A B) (h : M.IsPolyTimeMap r.map) :
    KarpReductionM M A.toDecisionProblem B.toDecisionProblem :=
  r.toSemanticReduction.toKarpReductionM h

end SatLikeReduction

/--
A polynomial-time equivalence between a concrete encoded problem and a `SatLikeProblem`.

This is an adapter: it records that a domain-specific problem can be viewed through the
generic satisfiability-style interface without changing yes-instances up to a polynomial
time representation conversion.
-/
abbrev SatLikeAdapterM (M : PolyTimeModel) (L : EncodedDecisionProblem)
    (P : SatLikeProblem) : Type :=
  ProblemEquivM M L P.toDecisionProblem

end ComplexityReduction
