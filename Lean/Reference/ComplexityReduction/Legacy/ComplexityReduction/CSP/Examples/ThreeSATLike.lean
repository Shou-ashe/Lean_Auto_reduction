/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.To3SATCosted
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations

/-!
A fixed finite Boolean CSP language for ordinary 3SAT clauses.

The eight symbols represent the eight possible polarity patterns of a ternary
clause.  This gives the CSP library a direct regression case for a familiar
NP-complete Boolean CSP without relying on the target-side `ThreeCNF` syntax.
-/

namespace ComplexityReduction
namespace CSP
namespace Examples

open SAT

/-- Relation symbols for ternary clauses. -/
inductive ThreeSATLikeSymbol where
  | posPosPos
  | negPosPos
  | posNegPos
  | posPosNeg
  | negNegPos
  | negPosNeg
  | posNegNeg
  | negNegNeg
  deriving DecidableEq, Repr

instance : Fintype ThreeSATLikeSymbol where
  elems :=
    { val :=
        [ ThreeSATLikeSymbol.posPosPos
        , ThreeSATLikeSymbol.negPosPos
        , ThreeSATLikeSymbol.posNegPos
        , ThreeSATLikeSymbol.posPosNeg
        , ThreeSATLikeSymbol.negNegPos
        , ThreeSATLikeSymbol.negPosNeg
        , ThreeSATLikeSymbol.posNegNeg
        , ThreeSATLikeSymbol.negNegNeg
        ]
      nodup := by simp }
  complete := by
    intro s
    cases s <;> simp

/-- The Boolean relation attached to a 3SAT polarity symbol. -/
noncomputable def threeSATLikeRelationOf : ThreeSATLikeSymbol → BoolRel
  | ThreeSATLikeSymbol.posPosPos => StandardRelations.ternaryClauseRel false false false
  | ThreeSATLikeSymbol.negPosPos => StandardRelations.ternaryClauseRel true false false
  | ThreeSATLikeSymbol.posNegPos => StandardRelations.ternaryClauseRel false true false
  | ThreeSATLikeSymbol.posPosNeg => StandardRelations.ternaryClauseRel false false true
  | ThreeSATLikeSymbol.negNegPos => StandardRelations.ternaryClauseRel true true false
  | ThreeSATLikeSymbol.negPosNeg => StandardRelations.ternaryClauseRel true false true
  | ThreeSATLikeSymbol.posNegNeg => StandardRelations.ternaryClauseRel false true true
  | ThreeSATLikeSymbol.negNegNeg => StandardRelations.ternaryClauseRel true true true

@[simp]
theorem threeSATLikeRelationOf_arity (s : ThreeSATLikeSymbol) :
    (threeSATLikeRelationOf s).arity = 3 := by
  cases s <;> simp [threeSATLikeRelationOf]

/-- The fixed ternary-clause CSP language. -/
noncomputable def threeSATLikeLanguage : BoolLanguage where
  Symbol := ThreeSATLikeSymbol
  finiteSymbol := inferInstance
  relationOf := threeSATLikeRelationOf

@[simp]
theorem threeSATLikeLanguage_relation_arity (s : threeSATLikeLanguage.Symbol) :
    (threeSATLikeLanguage.relationOf s).arity = 3 := by
  cases s <;> simp [threeSATLikeLanguage, threeSATLikeRelationOf]

/-- The 3SAT-like CSP language is 3-bounded. -/
theorem threeSATLikeLanguage_isThreeBounded :
    threeSATLikeLanguage.IsThreeBounded := by
  intro s
  rw [threeSATLikeLanguage_relation_arity s]

/-- The encoded decision problem for the fixed ternary-clause CSP language. -/
noncomputable def threeSATLikeDecisionProblem : EncodedDecisionProblem :=
  boolCSPDecisionProblem threeSATLikeLanguage

/-- The generic Boolean-CSP-to-3SAT semantic reduction specialized to ternary clauses. -/
noncomputable def threeSATLikeToThreeSATReduction :
    SemanticReduction threeSATLikeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATReduction threeSATLikeLanguage_isThreeBounded

/-- The same specialization with the project-local costed certificate. -/
noncomputable def threeSATLikeToThreeSATCostedReduction :
    CostedReduction threeSATLikeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATCostedReduction threeSATLikeLanguage_isThreeBounded

/-- The corresponding Karp reduction in the costed polynomial-time model. -/
noncomputable def threeSATLikeToThreeSATKarpReduction :
    KarpReductionM CostedPolyTimeModel threeSATLikeDecisionProblem threeSATDecisionProblem :=
  boolCSPToThreeSATKarpReduction threeSATLikeLanguage_isThreeBounded

/-- A positive ternary clause over variables `0`, `1`, and `2`. -/
noncomputable def positiveTernaryClauseConstraint : Constraint threeSATLikeLanguage where
  symbol := ThreeSATLikeSymbol.posPosPos
  vars := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2

/-- A mixed-polarity ternary clause sharing variable `2`. -/
noncomputable def mixedTernaryClauseConstraint : Constraint threeSATLikeLanguage where
  symbol := ThreeSATLikeSymbol.negPosNeg
  vars := fun
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 3
    | ⟨2, _⟩ => 2

/-- A small 3SAT-like formula over the fixed ternary-clause language. -/
noncomputable def threeSATLikeSampleFormula : Formula threeSATLikeLanguage :=
  [positiveTernaryClauseConstraint, mixedTernaryClauseConstraint]

/-- The real CSP encoding assigns a nonzero length to the ternary-clause sample formula. -/
theorem threeSATLikeSampleFormula_inputSize_pos :
    0 < (boolCSPDecisionProblem threeSATLikeLanguage).Instance.inputSize
      threeSATLikeSampleFormula := by
  change 0 < (Encoding.encodeFormula (Γ := threeSATLikeLanguage)
    threeSATLikeSampleFormula).length
  simp [Encoding.encodeFormula, Encoding.encodeConstraint, threeSATLikeSampleFormula,
    positiveTernaryClauseConstraint, mixedTernaryClauseConstraint]

end Examples
end CSP
end ComplexityReduction
