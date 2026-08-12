/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold
import ComplexityReduction.Domain.BooleanCSP
import ComplexityReduction.Domain.ThreeSATToNAEThreeSAT
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations
import ComplexityReduction.Program.List

/-!
Public reference-stage evidence for Boolean-CSP authoring.

Positive NAE-3 CSP targets should reuse the established endpoint-exact
3SAT-to-NAE-3SAT ingress and author only the remaining representation bridge.
This leaf deliberately exposes no Boolean-CSP target, final route, hardness
facade, or benchmark-specific declaration.
-/

namespace ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources

open ComplexityReduction

/-- A reusable source-to-reference stage, without a final target route. -/
structure ReferenceIngressSeed
    (source reference : Encoding.PresentedProblem) where
  executable : source.Instance → reference.Instance
  executableDirectTM :
    Authoring.ExecutableDirectTMEvidence source reference executable
  executableCorrect :
    Authoring.ExecutableSemanticProof source reference executable

/--
Exact structured-3SAT ingress to the public NAE-3SAT reference presentation.
The remaining authoring task is therefore a reference-to-target adapter, not
a fresh reconstruction of the 3SAT normalization.
-/
noncomputable def threeSATToNAEThreeSATIngress :
    ReferenceIngressSeed
      Domain.ThreeSATToNAEThreeSAT.sourceProblem
      Domain.ThreeSATToNAEThreeSAT.targetProblem where
  executable := Domain.ThreeSATToNAEThreeSAT.executable
  executableDirectTM := by
    simpa [Authoring.ExecutableDirectTMEvidence,
      Domain.ThreeSATToNAEThreeSAT.sourceProblem,
      Domain.ThreeSATToNAEThreeSAT.targetProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
      Presentation.NAEThreeSAT.structuredProblem,
      Presentation.NAEThreeSAT.structuredPresentation] using
        Domain.ThreeSATToNAEThreeSAT.executable_tmPolyTime
  executableCorrect := by
    intro formula
    change SAT.ThreeCNF.Satisfiable formula ↔
      NAEThreeSAT.Formula.Satisfiable
        (Domain.ThreeSATToNAEThreeSAT.executable formula)
    exact Domain.ThreeSATToNAEThreeSAT.executable_correct formula

namespace PositiveNAE3CSP

open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP

/-- The generic one-symbol positive NAE-3 language used by public CSP targets. -/
noncomputable def gamma : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => StandardRelations.notAllEqual3Rel

/-- An explicit ordered ternary Boolean tuple. -/
def tripleTuple (first second third : Bool) : BoolTuple 3 := fun
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨2, _⟩ => third

theorem notAllEqual3Rel_holds_triple_iff (first second third : Bool) :
    StandardRelations.notAllEqual3Rel.Holds
        (tripleTuple first second third) ↔
      Domain.ThreeSATToNAEThreeSAT.nae3Values first second third := by
  classical
  unfold StandardRelations.notAllEqual3Rel StandardRelations.notAllEqualRel
  rw [BoolRel.holds_ofPredicate_iff]
  constructor
  · rintro ⟨left, right, different⟩
    fin_cases left <;> fin_cases right <;>
      cases first <;> cases second <;> cases third <;>
        simp_all [tripleTuple, Domain.ThreeSATToNAEThreeSAT.nae3Values]
  · intro notAllEqual
    by_cases firstSecond : first = second
    · have secondThird : second ≠ third := by
        intro secondThird
        exact notAllEqual ⟨firstSecond, secondThird⟩
      exact ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by
        simpa [tripleTuple] using secondThird⟩
    · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by
        simpa [tripleTuple] using firstSecond⟩

/-- Turn one signed NAE literal into its collision-free CSP variable key. -/
abbrev literalKey : SAT.Literal → Nat :=
  Domain.ThreeSATToNAEThreeSAT.literalKey

/-- Flip only the polarity of one SAT literal. -/
def complementLiteral (literal : SAT.Literal) : SAT.Literal :=
  SAT.Clause.negate literal

/-- The positive NAE constraint corresponding to one signed NAE clause. -/
noncomputable def clauseConstraint (clause : NAEThreeSAT.Clause) :
    Constraint gamma where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => literalKey clause.first
    | ⟨1, _⟩ => literalKey clause.second
    | ⟨2, _⟩ => literalKey clause.third

/--
Force the CSP variables for a literal and its polarity complement to disagree.
`NAE(x, y, y)` is equivalent to `x ≠ y`.
-/
noncomputable def complementConstraint (literal : SAT.Literal) :
    Constraint gamma where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => literalKey literal
    | ⟨1, _⟩ => literalKey (complementLiteral literal)
    | ⟨2, _⟩ => literalKey (complementLiteral literal)

/-- One clause plus the three local polarity-consistency constraints it uses. -/
noncomputable def clauseBlock (clause : NAEThreeSAT.Clause) : Formula gamma :=
  [ clauseConstraint clause,
    complementConstraint clause.first,
    complementConstraint clause.second,
    complementConstraint clause.third ]

/-- Type-correct reference-to-positive-NAE3-CSP representation bridge. -/
noncomputable def referenceExecutable (formula : NAEThreeSAT.Formula) :
    Formula gamma :=
  formula.flatMap clauseBlock

/--
Complete type-correct executable from structured 3SAT to the generic positive
NAE-3 CSP carrier. Semantic and direct-TM obligations remain explicit staged
authoring nodes.
-/
noncomputable def executable (formula : SAT.ThreeCNF) : Formula gamma :=
  referenceExecutable (threeSATToNAEThreeSATIngress.executable formula)

/-! ### Direct-TM bridge -/

private abbrev literalEncoding : EncodedType :=
  BooleanCSPReductionScaffold.literalEncoding

private abbrev clauseEncoding : EncodedType :=
  BooleanCSPReductionScaffold.clauseEncoding

private noncomputable abbrev targetEncoding : EncodedType :=
  Presentation.FiniteDomainCSPTable.encodedType gamma

/-- The unique relation symbol of the positive NAE-3 language has code zero. -/
theorem relationCode_eq_zero (symbol : gamma.Symbol) :
    Presentation.FiniteDomainCSPTable.relationCode gamma symbol = 0 := by
  have bounded :=
    Presentation.FiniteDomainCSPTable.relationCode_lt_card gamma symbol
  have lessThanOne :
      Presentation.FiniteDomainCSPTable.relationCode gamma symbol < 1 := by
    simpa [gamma] using bounded
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ lessThanOne)

private theorem firstLiteral_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.first := by
  simpa [clauseEncoding, literalEncoding] using
    BooleanCSPReductionScaffold.clauseFirst_tmPolyTime

private theorem secondLiteral_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.second := by
  simpa [clauseEncoding, literalEncoding] using
    BooleanCSPReductionScaffold.clauseSecond_tmPolyTime

private theorem thirdLiteral_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.third := by
  simpa [clauseEncoding, literalEncoding] using
    BooleanCSPReductionScaffold.clauseThird_tmPolyTime

/-- The standard raw encoder payload for one positive ternary NAE constraint. -/
def constraintPayload (first second third : Nat) : Nat × List Nat :=
  (0, [first, second, third])

private theorem constraintPayload_tmPolyTime {X : EncodedType}
    {first second third : X.Carrier → Nat}
    (hFirst : TMPolyTimeMap X EncodedType.nat first)
    (hSecond : TMPolyTimeMap X EncodedType.nat second)
    (hThird : TMPolyTimeMap X EncodedType.nat third) :
    TMPolyTimeMap X
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      (fun input => constraintPayload (first input) (second input) (third input)) := by
  simpa [constraintPayload, BooleanCSPReductionScaffold.constraintPayload] using
    BooleanCSPReductionScaffold.constraintPayload_tmPolyTime
      hFirst hSecond hThird

private theorem literalKeyAfter_tmPolyTime
    {literal : NAEThreeSAT.Clause → SAT.Literal}
    (hLiteral : TMPolyTimeMap clauseEncoding literalEncoding literal) :
    TMPolyTimeMap clauseEncoding EncodedType.nat
      (fun clause => literalKey (literal clause)) := by
  change TMPolyTimeMap BooleanCSPReductionScaffold.clauseEncoding
    BooleanCSPReductionScaffold.literalEncoding literal at hLiteral
  simpa [clauseEncoding, literalEncoding, literalKey] using
    BooleanCSPReductionScaffold.literalKeyAfter_tmPolyTime
      (X := BooleanCSPReductionScaffold.clauseEncoding) hLiteral

private theorem complementLiteralAfter_tmPolyTime
    {literal : NAEThreeSAT.Clause → SAT.Literal}
    (hLiteral : TMPolyTimeMap clauseEncoding literalEncoding literal) :
    TMPolyTimeMap clauseEncoding literalEncoding
      (fun clause => complementLiteral (literal clause)) := by
  change TMPolyTimeMap BooleanCSPReductionScaffold.clauseEncoding
    BooleanCSPReductionScaffold.literalEncoding literal at hLiteral
  simpa [clauseEncoding, literalEncoding, complementLiteral,
      BooleanCSPReductionScaffold.complementLiteral] using
    BooleanCSPReductionScaffold.complementLiteralAfter_tmPolyTime
      (X := BooleanCSPReductionScaffold.clauseEncoding) hLiteral

private theorem complementKeyAfter_tmPolyTime
    {literal : NAEThreeSAT.Clause → SAT.Literal}
    (hLiteral : TMPolyTimeMap clauseEncoding literalEncoding literal) :
    TMPolyTimeMap clauseEncoding EncodedType.nat
      (fun clause => literalKey (complementLiteral (literal clause))) := by
  change TMPolyTimeMap BooleanCSPReductionScaffold.clauseEncoding
    BooleanCSPReductionScaffold.literalEncoding literal at hLiteral
  simpa [clauseEncoding, literalEncoding, literalKey, complementLiteral,
      BooleanCSPReductionScaffold.complementLiteral] using
    BooleanCSPReductionScaffold.complementKeyAfter_tmPolyTime
      (X := BooleanCSPReductionScaffold.clauseEncoding) hLiteral

/-- Raw canonical encoder payload of one clause constraint. -/
def clauseConstraintCode (clause : NAEThreeSAT.Clause) : Nat × List Nat :=
  constraintPayload (literalKey clause.first) (literalKey clause.second)
    (literalKey clause.third)

private theorem clauseConstraintCode_tmPolyTime :
    TMPolyTimeMap clauseEncoding
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      clauseConstraintCode := by
  simpa [clauseConstraintCode] using constraintPayload_tmPolyTime
    (X := clauseEncoding)
    (literalKeyAfter_tmPolyTime firstLiteral_tmPolyTime)
    (literalKeyAfter_tmPolyTime secondLiteral_tmPolyTime)
    (literalKeyAfter_tmPolyTime thirdLiteral_tmPolyTime)

/-- Raw canonical encoder payload of one polarity-complement constraint. -/
def complementConstraintCode (literal : SAT.Literal) : Nat × List Nat :=
  constraintPayload (literalKey literal)
    (literalKey (complementLiteral literal))
    (literalKey (complementLiteral literal))

private theorem complementConstraintCodeAfter_tmPolyTime
    {literal : NAEThreeSAT.Clause → SAT.Literal}
    (hLiteral : TMPolyTimeMap clauseEncoding literalEncoding literal) :
    TMPolyTimeMap clauseEncoding
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      (fun clause => complementConstraintCode (literal clause)) := by
  simpa [complementConstraintCode] using constraintPayload_tmPolyTime
    (X := clauseEncoding)
    (literalKeyAfter_tmPolyTime hLiteral)
    (complementKeyAfter_tmPolyTime hLiteral)
    (complementKeyAfter_tmPolyTime hLiteral)

/-- Raw canonical encoder payload of the complete four-constraint clause block. -/
def clauseBlockCode (clause : NAEThreeSAT.Clause) :
    List (Nat × List Nat) :=
  [ clauseConstraintCode clause,
    complementConstraintCode clause.first,
    complementConstraintCode clause.second,
    complementConstraintCode clause.third ]

private theorem clauseBlockCode_tmPolyTime :
    TMPolyTimeMap clauseEncoding
      Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
      clauseBlockCode := by
  let ConstraintCode :=
    Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
  let FormulaCode := Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
  have hFirstComplement := complementConstraintCodeAfter_tmPolyTime
    firstLiteral_tmPolyTime
  have hSecondComplement := complementConstraintCodeAfter_tmPolyTime
    secondLiteral_tmPolyTime
  have hThirdComplement := complementConstraintCodeAfter_tmPolyTime
    thirdLiteral_tmPolyTime
  have output := TMPolyTimeMap.list_cons_of clauseConstraintCode_tmPolyTime
    (TMPolyTimeMap.list_cons_of hFirstComplement
      (TMPolyTimeMap.list_cons_of hSecondComplement
        (TMPolyTimeMap.list_singleton_of hThirdComplement)))
  simpa [clauseBlockCode, ConstraintCode, FormulaCode] using output

private theorem constraintCode_clauseConstraint (clause : NAEThreeSAT.Clause) :
    Presentation.FiniteDomainCSPTable.constraintCode (clauseConstraint clause) =
      clauseConstraintCode clause := by
  apply Prod.ext
  · simpa [Presentation.FiniteDomainCSPTable.constraintCode,
      clauseConstraintCode, constraintPayload] using relationCode_eq_zero ()
  · simp [Presentation.FiniteDomainCSPTable.constraintCode,
      clauseConstraintCode, constraintPayload, clauseConstraint,
      Constraint.varsList, gamma, StandardRelations.notAllEqual3Rel,
      StandardRelations.notAllEqualRel, BoolRel.ofPredicate,
      List.ofFn, Fin.foldr, Fin.foldr.loop]

private theorem constraintCode_complementConstraint (literal : SAT.Literal) :
    Presentation.FiniteDomainCSPTable.constraintCode
        (complementConstraint literal) =
      complementConstraintCode literal := by
  apply Prod.ext
  · simpa [Presentation.FiniteDomainCSPTable.constraintCode,
      complementConstraintCode, constraintPayload] using relationCode_eq_zero ()
  · simp [Presentation.FiniteDomainCSPTable.constraintCode,
      complementConstraintCode, constraintPayload, complementConstraint,
      Constraint.varsList, gamma, StandardRelations.notAllEqual3Rel,
      StandardRelations.notAllEqualRel, BoolRel.ofPredicate,
      List.ofFn, Fin.foldr, Fin.foldr.loop]

private theorem clauseBlockCode_eq_formulaCode (clause : NAEThreeSAT.Clause) :
    clauseBlockCode clause =
      Presentation.FiniteDomainCSPTable.formulaCode gamma (clauseBlock clause) := by
  simp [clauseBlockCode, clauseBlock,
    Presentation.FiniteDomainCSPTable.formulaCode,
    constraintCode_clauseConstraint, constraintCode_complementConstraint]

/-- The authored four-constraint clause gadget is direct-TM polynomial time. -/
theorem clauseBlock_tmPolyTime :
    TMPolyTimeMap clauseEncoding targetEncoding clauseBlock := by
  exact Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code
    clauseBlockCode_tmPolyTime clauseBlockCode_eq_formulaCode

/-- Raw canonical encoder payload of the complete reference bridge. -/
noncomputable def referenceExecutableCode (formula : NAEThreeSAT.Formula) :
    List (Nat × List Nat) :=
  formula.flatMap clauseBlockCode

private theorem referenceExecutableCode_eq_formulaCode
    (formula : NAEThreeSAT.Formula) :
    referenceExecutableCode formula =
      Presentation.FiniteDomainCSPTable.formulaCode gamma
        (referenceExecutable formula) := by
  unfold referenceExecutableCode referenceExecutable
    Presentation.FiniteDomainCSPTable.formulaCode
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro clause _
  exact clauseBlockCode_eq_formulaCode clause

private theorem referenceExecutableCode_tmPolyTime :
    TMPolyTimeMap Presentation.NAEThreeSAT.formulaEncodedType
      Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
      referenceExecutableCode := by
  have mapped := TMPolyTimeMap.list_map clauseBlockCode_tmPolyTime
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType)
    mapped
  convert flattened using 1

/-- The exact NAE-3SAT-to-positive-NAE3-CSP representation bridge is direct-TM. -/
theorem referenceExecutable_tmPolyTime :
    TMPolyTimeMap Presentation.NAEThreeSAT.formulaEncodedType
      targetEncoding referenceExecutable := by
  exact Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code
    referenceExecutableCode_tmPolyTime referenceExecutableCode_eq_formulaCode

/-- The complete structured-3SAT-to-positive-NAE3-CSP executable is direct-TM. -/
theorem executable_tmPolyTime :
    TMPolyTimeMap Domain.ThreeSATToNAEThreeSAT.sourceEncoding
      targetEncoding executable := by
  have output := TMPolyTimeMap.comp referenceExecutable_tmPolyTime
    Domain.ThreeSATToNAEThreeSAT.executable_tmPolyTime
  simpa [executable, threeSATToNAEThreeSATIngress, Function.comp] using output

/-! ### Semantic bridge -/

/-- Decode a signed-literal key back into the Boolean value of that literal. -/
def forwardAssignment (assignment : SAT.Assignment) : SAT.Assignment :=
  fun key =>
    let decoded := Nat.unpair key
    if decoded.2 = 0 then assignment decoded.1 else !(assignment decoded.1)

@[simp] theorem forwardAssignment_literalKey
    (assignment : SAT.Assignment) (literal : SAT.Literal) :
    forwardAssignment assignment (literalKey literal) = literal.eval assignment := by
  cases literal with
  | mk index negated =>
      cases negated <;>
        simp [forwardAssignment, literalKey,
          Domain.ThreeSATToNAEThreeSAT.literalKey,
          ComplexityReduction.boolToNat, Nat.unpair_pair, SAT.Literal.eval]

/-- Read a source assignment from the positive key of each CSP variable pair. -/
def reverseAssignment (assignment : SAT.Assignment) : SAT.Assignment :=
  fun index => assignment (literalKey (SAT.Literal.positive index))

theorem clauseConstraint_satisfies_iff (clause : NAEThreeSAT.Clause)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (clauseConstraint clause) assignment ↔
      Domain.ThreeSATToNAEThreeSAT.nae3Values
        (assignment (literalKey clause.first))
        (assignment (literalKey clause.second))
        (assignment (literalKey clause.third)) := by
  let tuple := Constraint.assignmentTuple (clauseConstraint clause) assignment
  have tupleEquality : tuple = tripleTuple
      (assignment (literalKey clause.first))
      (assignment (literalKey clause.second))
      (assignment (literalKey clause.third)) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple ↔ _
  rw [tupleEquality]
  exact notAllEqual3Rel_holds_triple_iff _ _ _

theorem complementConstraint_satisfies_iff (literal : SAT.Literal)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (complementConstraint literal) assignment ↔
      assignment (literalKey literal) ≠
        assignment (literalKey (complementLiteral literal)) := by
  let tuple := Constraint.assignmentTuple
    (complementConstraint literal) assignment
  have tupleEquality : tuple = tripleTuple
        (assignment (literalKey literal))
        (assignment (literalKey (complementLiteral literal)))
        (assignment (literalKey (complementLiteral literal))) := by
    funext index
    fin_cases index <;> rfl
  change StandardRelations.notAllEqual3Rel.Holds tuple ↔ _
  rw [tupleEquality, notAllEqual3Rel_holds_triple_iff]
  cases assignment (literalKey literal) <;>
    cases assignment (literalKey (complementLiteral literal)) <;>
      simp [Domain.ThreeSATToNAEThreeSAT.nae3Values]

theorem complementConstraint_forward
    (literal : SAT.Literal) (assignment : SAT.Assignment) :
    Constraint.Satisfies (complementConstraint literal)
      (forwardAssignment assignment) := by
  rw [complementConstraint_satisfies_iff]
  cases literal with
  | mk index negated =>
      cases negated <;> cases value : assignment index <;>
        simp [complementLiteral, SAT.Clause.negate,
          forwardAssignment_literalKey, SAT.Literal.eval, value]

theorem literal_eval_reverse_of_complement
    (literal : SAT.Literal) (assignment : SAT.Assignment)
    (consistent :
      Constraint.Satisfies (complementConstraint literal) assignment) :
    literal.eval (reverseAssignment assignment) =
      assignment (literalKey literal) := by
  rw [complementConstraint_satisfies_iff] at consistent
  cases literal with
  | mk index negated =>
      cases negated
      · simp [reverseAssignment, literalKey,
          Domain.ThreeSATToNAEThreeSAT.literalKey,
          ComplexityReduction.boolToNat, SAT.Literal.eval,
          SAT.Literal.positive]
      · simp [reverseAssignment, complementLiteral, SAT.Clause.negate,
          literalKey, Domain.ThreeSATToNAEThreeSAT.literalKey,
          ComplexityReduction.boolToNat, SAT.Literal.eval,
          SAT.Literal.positive] at consistent ⊢
        cases positiveValue : assignment (Nat.pair index 0) <;>
          cases negativeValue : assignment (Nat.pair index 1) <;>
            simp_all

theorem clauseConstraint_forward_iff
    (clause : NAEThreeSAT.Clause) (assignment : SAT.Assignment) :
    Constraint.Satisfies (clauseConstraint clause)
        (forwardAssignment assignment) ↔
      clause.Satisfies assignment := by
  rw [clauseConstraint_satisfies_iff]
  simp [NAEThreeSAT.Clause.Satisfies,
    Domain.ThreeSATToNAEThreeSAT.nae3Values]

theorem referenceExecutable_satisfies_forward
    (formula : NAEThreeSAT.Formula) (assignment : SAT.Assignment)
    (satisfies : NAEThreeSAT.Formula.Satisfies formula assignment) :
    CSP.Formula.Satisfies (referenceExecutable formula)
      (forwardAssignment assignment) := by
  intro constraint constraintMember
  rcases List.mem_flatMap.mp constraintMember with
    ⟨clause, clauseMember, blockMember⟩
  simp [clauseBlock] at blockMember
  rcases blockMember with rfl | rfl | rfl | rfl
  · exact (clauseConstraint_forward_iff clause assignment).2
      (satisfies clause clauseMember)
  · exact complementConstraint_forward clause.first assignment
  · exact complementConstraint_forward clause.second assignment
  · exact complementConstraint_forward clause.third assignment

theorem referenceExecutable_satisfies_reverse
    (formula : NAEThreeSAT.Formula) (assignment : SAT.Assignment)
    (satisfies :
      CSP.Formula.Satisfies (referenceExecutable formula) assignment) :
    NAEThreeSAT.Formula.Satisfies formula (reverseAssignment assignment) := by
  intro clause clauseMember
  have clauseSatisfies : Constraint.Satisfies (clauseConstraint clause) assignment :=
    satisfies _ (List.mem_flatMap.mpr
      ⟨clause, clauseMember, by simp [clauseBlock]⟩)
  have firstConsistent :
      Constraint.Satisfies (complementConstraint clause.first) assignment :=
    satisfies _ (List.mem_flatMap.mpr
      ⟨clause, clauseMember, by simp [clauseBlock]⟩)
  have secondConsistent :
      Constraint.Satisfies (complementConstraint clause.second) assignment :=
    satisfies _ (List.mem_flatMap.mpr
      ⟨clause, clauseMember, by simp [clauseBlock]⟩)
  have thirdConsistent :
      Constraint.Satisfies (complementConstraint clause.third) assignment :=
    satisfies _ (List.mem_flatMap.mpr
      ⟨clause, clauseMember, by simp [clauseBlock]⟩)
  rw [clauseConstraint_satisfies_iff] at clauseSatisfies
  rw [NAEThreeSAT.Clause.Satisfies]
  change Domain.ThreeSATToNAEThreeSAT.nae3Values
    (clause.first.eval (reverseAssignment assignment))
    (clause.second.eval (reverseAssignment assignment))
    (clause.third.eval (reverseAssignment assignment))
  rw [literal_eval_reverse_of_complement clause.first assignment firstConsistent,
    literal_eval_reverse_of_complement clause.second assignment secondConsistent,
    literal_eval_reverse_of_complement clause.third assignment thirdConsistent]
  exact clauseSatisfies

theorem referenceExecutable_correct (formula : NAEThreeSAT.Formula) :
    NAEThreeSAT.Formula.Satisfiable formula ↔
      CSP.Formula.Satisfiable (referenceExecutable formula) := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨forwardAssignment assignment,
      referenceExecutable_satisfies_forward formula assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨reverseAssignment assignment,
      referenceExecutable_satisfies_reverse formula assignment satisfies⟩

/-- Semantic correctness of the complete structured-3SAT-to-positive-NAE3 bridge. -/
theorem executable_correct (formula : SAT.ThreeCNF) :
    SAT.ThreeCNF.Satisfiable formula ↔
      CSP.Formula.Satisfiable (executable formula) := by
  rw [Domain.ThreeSATToNAEThreeSAT.executable_correct]
  exact referenceExecutable_correct _

end PositiveNAE3CSP

/--
Complete reusable structured-3SAT ingress to the generic positive NAE-3 CSP
endpoint.  The executable, direct-TM machine, and semantic proof are indexed
to the same exact source and target representations.
-/
noncomputable def threeSATToPositiveNAE3CSPIngress :
    ReferenceIngressSeed
      Domain.ThreeSATToNAEThreeSAT.sourceProblem
      (Domain.BooleanCSP.cspOf PositiveNAE3CSP.gamma) where
  executable := PositiveNAE3CSP.executable
  executableDirectTM := by
    simpa [Authoring.ExecutableDirectTMEvidence,
      Domain.ThreeSATToNAEThreeSAT.sourceProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredProblem,
      Problems.Karp21.Satisfiability.threeSATStructuredPresentation,
      Domain.BooleanCSP.cspOf,
      Presentation.FiniteDomainCSPTable.presentedProblem,
      Presentation.FiniteDomainCSPTable.lawfulRepresentation] using
        PositiveNAE3CSP.executable_tmPolyTime
  executableCorrect := by
    intro formula
    change SAT.ThreeCNF.Satisfiable formula ↔
      CSP.Formula.Satisfiable (PositiveNAE3CSP.executable formula)
    exact PositiveNAE3CSP.executable_correct formula

assert_standard_axioms
  threeSATToNAEThreeSATIngress,
  threeSATToPositiveNAE3CSPIngress,
  PositiveNAE3CSP.executable,
  PositiveNAE3CSP.clauseBlock_tmPolyTime,
  PositiveNAE3CSP.referenceExecutable_tmPolyTime,
  PositiveNAE3CSP.executable_tmPolyTime,
  PositiveNAE3CSP.referenceExecutable_correct,
  PositiveNAE3CSP.executable_correct

end ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources
