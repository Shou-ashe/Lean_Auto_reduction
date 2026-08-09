/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.SatLike
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Encoding

/-!
`SatLikeProblem` adapters for Boolean CSP formulas.
-/

namespace ComplexityReduction
namespace CSP

open ComplexityReduction

/-- Boolean CSP formulas viewed as a satisfiability-style problem. -/
def boolCSPSatLike (Γ : BoolLanguage) : SatLikeProblem where
  Inst := formulaEncodedType Γ
  Assignment := fun _ => SAT.Assignment
  Satisfies := fun φ a => Formula.Satisfies φ a

/-- The encoded decision problem induced by Boolean CSP satisfiability. -/
def boolCSPDecisionProblem (Γ : BoolLanguage) : EncodedDecisionProblem :=
  (boolCSPSatLike Γ).toDecisionProblem

@[simp]
theorem boolCSPDecisionProblem_isYes_iff (Γ : BoolLanguage) (φ : Formula Γ) :
    (boolCSPDecisionProblem Γ).isYes φ ↔ Formula.Satisfiable φ :=
  Iff.rfl

end CSP
end ComplexityReduction
