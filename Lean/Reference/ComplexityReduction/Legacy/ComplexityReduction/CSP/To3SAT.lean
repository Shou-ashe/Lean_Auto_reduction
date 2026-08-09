/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.SatLike
import ComplexityReduction.Legacy.ComplexityReduction.CSP.ToCNF
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT

/-!
The local Boolean-CSP to 3SAT semantic reduction.
-/

namespace ComplexityReduction
namespace CSP

open SAT

/-- Translate a CSP formula into a bundled local 3CNF. -/
noncomputable def Formula.toThreeCNF {Γ : BoolLanguage} (hΓ : Γ.IsThreeBounded) (φ : Formula Γ) :
    ThreeCNF :=
  CNF.toThreeCNF (Formula.toCNF φ) (Formula.toCNF_clauseBound hΓ φ)

@[simp]
theorem Formula.toThreeCNF_satisfies {Γ : BoolLanguage} (hΓ : Γ.IsThreeBounded)
    (φ : Formula Γ) (a : SAT.Assignment) :
    (Formula.toThreeCNF hΓ φ).Satisfies a ↔ Formula.Satisfies φ a := by
  simp [Formula.toThreeCNF, Formula.toCNF_correct]

/-- Translate a CSP formula into local 3CNF with no arity restriction. -/
noncomputable def Formula.toThreeCNFGeneral {Γ : BoolLanguage} (φ : Formula Γ) :
    ThreeCNF :=
  CNF.splitToThreeCNF (Formula.toCNF φ)

theorem Formula.toThreeCNFGeneral_satisfiable_iff {Γ : BoolLanguage} (φ : Formula Γ) :
    (Formula.toThreeCNFGeneral φ).Satisfiable ↔ Formula.Satisfiable φ := by
  unfold Formula.toThreeCNFGeneral
  exact (SAT.CNF.splitToThreeCNF_satisfiable_iff (Formula.toCNF φ)).trans
    (Formula.toCNF_satisfiable_iff φ)

/-- The Boolean CSP `SatLikeProblem` reduces to local 3SAT when the language is 3-bounded. -/
noncomputable def boolCSPToThreeSATSatLikeReduction {Γ : BoolLanguage} (hΓ : Γ.IsThreeBounded) :
    SatLikeReduction (boolCSPSatLike Γ) threeSATSatLike where
  map := fun φ => Formula.toThreeCNF hΓ φ
  lift := fun _ a => a
  project := fun _ a => a
  lift_correct := by
    intro φ a hSat
    simpa [Formula.toThreeCNF] using (Formula.toThreeCNF_satisfies hΓ φ a).2 hSat
  project_correct := by
    intro φ a hSat
    simpa [Formula.toThreeCNF] using (Formula.toThreeCNF_satisfies hΓ φ a).1 hSat

/-- The encoded many-one reduction induced by the satisfiability-style bridge. -/
noncomputable def boolCSPToThreeSATReduction {Γ : BoolLanguage} (hΓ : Γ.IsThreeBounded) :
    SemanticReduction (boolCSPDecisionProblem Γ) threeSATDecisionProblem :=
  (boolCSPToThreeSATSatLikeReduction hΓ).toSemanticReduction

/-- Unrestricted-arity Boolean CSP reduces semantically to local 3SAT. -/
noncomputable def boolCSPToThreeSATGeneralReduction (Γ : BoolLanguage) :
    SemanticReduction (boolCSPDecisionProblem Γ) threeSATDecisionProblem where
  f := fun φ => Formula.toThreeCNFGeneral φ
  correct := by
    intro φ
    exact (Formula.toThreeCNFGeneral_satisfiable_iff φ).symm

end CSP
end ComplexityReduction
