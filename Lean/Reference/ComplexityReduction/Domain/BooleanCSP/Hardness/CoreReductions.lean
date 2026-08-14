/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.Cores
import ComplexityReduction.Domain.BooleanCSP.Hardness.InterpretCompiler
import ComplexityReduction.Domain.BooleanCSP.Hardness.GraphColoringToOneInThree
import ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources
import ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Presentation.ThreeSATLike
import ComplexityReduction.Problems.Karp21.Satisfiability

/-!
NP-hardness certificates for Schaefer's hard Boolean CSP cores.

The natural-language proof of the hardness direction of Schaefer's dichotomy
reduces every non-tractable finite Boolean constraint language to one of a
finite list of canonical NP-hard cores.  This module stores the library's
certified NP-hardness evidence for those cores:

* `threeSATLikeCore` at its canonical `Presentation.ThreeSATLike` endpoint,
  via the established structured-3SAT shared gadget.
* `nae3Core`, via the established 3SAT-to-positive-NAE3-CSP bridge.
* `oneInThreeCore` and `exactlyTwo3Core`, which are primitive-positively
  interdefinable: exactly-one with polarity complements is exactly-two, and
  each core realizes the complement gadget by two constraints.  The two
  `Gadget` values below make the interdefinability explicit, and hardness
  transports between the two cores through `LanguageInterpretation`.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness

open ComplexityReduction.CSP
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program

/-! ### The 3SAT-like core -/

/--
The canonical 3SAT-like core endpoint is NP-hard via the established
structured-3SAT shared gadget.
-/
theorem threeSATLikeCoreNPHard :
    NativeTMNPHard Presentation.ThreeSATLike.presentedProblem :=
  NativeTMNPHard.ofCompleteAlongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step ThreeSATToThreeSATLikeStandardTM.sharedGadget)

/-! ### The positive NAE-3 core -/

/--
The exact structured-3SAT-to-positive-NAE3-CSP reduction, repackaged as the
certificate for the positive NAE-3 core.
-/
noncomputable def nae3CoreReduction :
    CertifiedReduction Problems.Karp21.Satisfiability.threeSATStructuredProblem
      (cspOf nae3Core) := by
  let program : PolyProg
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.representation
      (cspOf nae3Core).representation :=
    .atom (Primitive.ofTMPolyTime
      Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.executable (by
        simpa [nae3Core, Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.gamma,
          Problems.Karp21.Satisfiability.threeSATStructuredProblem,
          Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
          cspOf, Presentation.FiniteDomainCSPTable.presentedProblem,
          Presentation.FiniteDomainCSPTable.lawfulRepresentation] using
            Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_tmPolyTime))
  refine ⟨program, ?_⟩
  intro formula
  have hrun : program.run formula =
      Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.executable formula := rfl
  simpa [cspOf_accepts, hrun] using
    Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.executable_correct formula

/-- The positive NAE-3 core is NP-hard. -/
theorem nae3CoreNPHard : NativeTMNPHard (cspOf nae3Core) :=
  NativeTMNPHard.ofCompleteAlongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step nae3CoreReduction)

/-! ### Exactly-one and exactly-two are pp-interdefinable -/

/-- The positive exactly-one core is NP-hard by the direct fixed-three-colouring compiler. -/
theorem oneInThreeCoreNPHard : NativeTMNPHard (cspOf oneInThreeCore) :=
  GraphColoringToOneInThree.oneInThreeCoreNPHard

/--
The exactly-one relation is pp-definable over the exactly-two core by the
seven-constraint complement gadget.
-/
noncomputable def oneInThreeGadgetOfExactlyTwo3 :
    Gadget exactlyTwo3Core StandardRelations.exactlyOne3Rel where
  formula := [ exactlyTwo3Constraint 0 3 6,
    exactlyTwo3Constraint 7 6 6,
    exactlyTwo3Constraint 1 4 8,
    exactlyTwo3Constraint 9 8 8,
    exactlyTwo3Constraint 2 5 10,
    exactlyTwo3Constraint 11 10 10,
    exactlyTwo3Constraint 3 4 5 ]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
  outputs_injective := by
    intro i j equality
    have hi : (fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2) i = i.val := by
      fin_cases i <;> rfl
    have hj : (fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2) j = j.val := by
      fin_cases j <;> rfl
    apply Fin.ext
    rw [← hi, ← hj, equality]
  correct := by
    intro tuple
    constructor
    · intro tupleHolds
      refine ⟨oneInThreeTupleWitness tuple, ?_⟩
      constructor
      · intro constraint constraintMember
        have hgadget := exactlyTwo3_gadget_witness tupleHolds
        rcases hgadget with ⟨h1, h2, h3, h4, h5, h6, h7⟩
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · exact h1
        rcases List.mem_cons.mp h' with rfl | h''
        · exact h2
        rcases List.mem_cons.mp h'' with rfl | h'''
        · exact h3
        rcases List.mem_cons.mp h''' with rfl | h''''
        · exact h4
        rcases List.mem_cons.mp h'''' with rfl | h'''''
        · exact h5
        rcases List.mem_cons.mp h''''' with rfl | h''''''
        · exact h6
        · rcases List.mem_cons.mp h'''''' with rfl | hEmpty
          · exact h7
          · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hgadget : Constraint.Satisfies (exactlyTwo3Constraint 0 3 6) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 7 6 6) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 1 4 8) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 9 8 8) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 2 5 10) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 11 10 10) assignment ∧
          Constraint.Satisfies (exactlyTwo3Constraint 3 4 5) assignment := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact satisfies (exactlyTwo3Constraint 0 3 6) (by simp)
        · exact satisfies (exactlyTwo3Constraint 7 6 6) (by simp)
        · exact satisfies (exactlyTwo3Constraint 1 4 8) (by simp)
        · exact satisfies (exactlyTwo3Constraint 9 8 8) (by simp)
        · exact satisfies (exactlyTwo3Constraint 2 5 10) (by simp)
        · exact satisfies (exactlyTwo3Constraint 11 10 10) (by simp)
        · exact satisfies (exactlyTwo3Constraint 3 4 5) (by simp)
      have htupleHolds : StandardRelations.exactlyOne3Rel.Holds
          (StandardRelations.tripleTuple (assignment 0) (assignment 1)
            (assignment 2)) :=
        exactlyOne3_of_exactlyTwo3_gadget 0 1 2 3 4 5 6 7 8 9 10 11
          assignment hgadget
      have h0 : assignment 0 = tuple ⟨0, by decide⟩ := outputs ⟨0, by decide⟩
      have h1 : assignment 1 = tuple ⟨1, by decide⟩ := outputs ⟨1, by decide⟩
      have h2 : assignment 2 = tuple ⟨2, by decide⟩ := outputs ⟨2, by decide⟩
      rw [h0, h1, h2] at htupleHolds
      have htuple : StandardRelations.tripleTuple (tuple ⟨0, by decide⟩)
          (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩) = tuple := by
        funext i
        fin_cases i <;> rfl
      rw [htuple] at htupleHolds
      exact htupleHolds

/--
The exactly-two relation is pp-definable over the exactly-one core by the
dual seven-constraint complement gadget.
-/
noncomputable def exactlyTwo3GadgetOfOneInThree :
    Gadget oneInThreeCore (StandardRelations.exactlyRel 3 2) where
  formula := [ oneInThreeConstraint 0 3 6,
    oneInThreeConstraint 7 6 6,
    oneInThreeConstraint 1 4 8,
    oneInThreeConstraint 9 8 8,
    oneInThreeConstraint 2 5 10,
    oneInThreeConstraint 11 10 10,
    oneInThreeConstraint 3 4 5 ]
  outputs := fun
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
  outputs_injective := by
    intro i j equality
    have hi : (fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2) i = i.val := by
      fin_cases i <;> rfl
    have hj : (fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 2) j = j.val := by
      fin_cases j <;> rfl
    apply Fin.ext
    rw [← hi, ← hj, equality]
  correct := by
    intro tuple
    constructor
    · intro tupleHolds
      refine ⟨exactlyTwo3TupleWitness tuple, ?_⟩
      constructor
      · intro constraint constraintMember
        have hgadget := oneInThree_gadget_witness tupleHolds
        rcases hgadget with ⟨h1, h2, h3, h4, h5, h6, h7⟩
        rcases List.mem_cons.mp constraintMember with rfl | h'
        · exact h1
        rcases List.mem_cons.mp h' with rfl | h''
        · exact h2
        rcases List.mem_cons.mp h'' with rfl | h'''
        · exact h3
        rcases List.mem_cons.mp h''' with rfl | h''''
        · exact h4
        rcases List.mem_cons.mp h'''' with rfl | h'''''
        · exact h5
        rcases List.mem_cons.mp h''''' with rfl | h''''''
        · exact h6
        · rcases List.mem_cons.mp h'''''' with rfl | hEmpty
          · exact h7
          · cases hEmpty
      · intro i
        fin_cases i <;> rfl
    · rintro ⟨assignment, ⟨satisfies, outputs⟩⟩
      have hgadget : Constraint.Satisfies (oneInThreeConstraint 0 3 6) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 7 6 6) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 1 4 8) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 9 8 8) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 2 5 10) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 11 10 10) assignment ∧
          Constraint.Satisfies (oneInThreeConstraint 3 4 5) assignment := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact satisfies (oneInThreeConstraint 0 3 6) (by simp)
        · exact satisfies (oneInThreeConstraint 7 6 6) (by simp)
        · exact satisfies (oneInThreeConstraint 1 4 8) (by simp)
        · exact satisfies (oneInThreeConstraint 9 8 8) (by simp)
        · exact satisfies (oneInThreeConstraint 2 5 10) (by simp)
        · exact satisfies (oneInThreeConstraint 11 10 10) (by simp)
        · exact satisfies (oneInThreeConstraint 3 4 5) (by simp)
      have htupleHolds : (StandardRelations.exactlyRel 3 2).Holds
          (StandardRelations.tripleTuple (assignment 0) (assignment 1)
            (assignment 2)) :=
        exactlyTwo3_of_oneInThree_gadget 0 1 2 3 4 5 6 7 8 9 10 11
          assignment hgadget
      have h0 : assignment 0 = tuple ⟨0, by decide⟩ := outputs ⟨0, by decide⟩
      have h1 : assignment 1 = tuple ⟨1, by decide⟩ := outputs ⟨1, by decide⟩
      have h2 : assignment 2 = tuple ⟨2, by decide⟩ := outputs ⟨2, by decide⟩
      rw [h0, h1, h2] at htupleHolds
      have htuple : StandardRelations.tripleTuple (tuple ⟨0, by decide⟩)
          (tuple ⟨1, by decide⟩) (tuple ⟨2, by decide⟩) = tuple := by
        funext i
        fin_cases i <;> rfl
      rw [htuple] at htupleHolds
      exact htupleHolds

/-- The exactly-two core interprets the exactly-one core. -/
noncomputable def exactlyTwo3InterpretsOneInThree :
    LanguageInterpretation oneInThreeCore exactlyTwo3Core where
  gadgetOf := fun _ => oneInThreeGadgetOfExactlyTwo3

/-- The exactly-one core interprets the exactly-two core. -/
noncomputable def oneInThreeInterpretsExactlyTwo3 :
    LanguageInterpretation exactlyTwo3Core oneInThreeCore where
  gadgetOf := fun _ => exactlyTwo3GadgetOfOneInThree

/-- Satisfiability transports from the exactly-one core to the exactly-two core. -/
theorem oneInThree_satisfiable_iff_exactlyTwo3 (formula : CSP.Formula oneInThreeCore) :
    CSP.Formula.Satisfiable
        (interpret exactlyTwo3InterpretsOneInThree formula) ↔
      CSP.Formula.Satisfiable formula :=
  interpret_satisfiable_iff exactlyTwo3InterpretsOneInThree formula

/-- Satisfiability transports from the exactly-two core to the exactly-one core. -/
theorem exactlyTwo3_satisfiable_iff_oneInThree (formula : CSP.Formula exactlyTwo3Core) :
    CSP.Formula.Satisfiable
        (interpret oneInThreeInterpretsExactlyTwo3 formula) ↔
      CSP.Formula.Satisfiable formula :=
  interpret_satisfiable_iff oneInThreeInterpretsExactlyTwo3 formula

/-! ### Certified hardness transport for the exactly-one / exactly-two pair -/

/--
Once the positive exactly-one core is closed by its direct source reduction,
the exactly-two core needs no additional machine proof: the generic
interpretation compiler turns the fixed seven-constraint gadget above into
the required direct-TM certified reduction automatically.
-/
theorem exactlyTwo3CoreNPHard_of_oneInThree
    (oneInThreeNPHard : NativeTMNPHard (cspOf oneInThreeCore)) :
    NativeTMNPHard (cspOf exactlyTwo3Core) :=
  nPHard_of_interpretation_auto exactlyTwo3InterpretsOneInThree
    oneInThreeNPHard

/-- The positive exactly-two core is NP-hard, with no external hardness premise. -/
theorem exactlyTwo3CoreNPHard : NativeTMNPHard (cspOf exactlyTwo3Core) :=
  exactlyTwo3CoreNPHard_of_oneInThree oneInThreeCoreNPHard

assert_standard_axioms
  threeSATLikeCoreNPHard,
  nae3CoreReduction,
  nae3CoreNPHard,
  oneInThreeCoreNPHard,
  oneInThreeGadgetOfExactlyTwo3,
  exactlyTwo3GadgetOfOneInThree,
  exactlyTwo3InterpretsOneInThree,
  oneInThreeInterpretsExactlyTwo3,
  oneInThree_satisfiable_iff_exactlyTwo3,
  exactlyTwo3_satisfiable_iff_oneInThree,
  exactlyTwo3CoreNPHard_of_oneInThree,
  exactlyTwo3CoreNPHard

end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
