/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Domain.BooleanCSP
import ComplexityReduction.Domain.ThreeSATToNAEThreeSAT
import ComplexityReduction.Legacy.ComplexityReduction.CSP.StandardRelations
import ComplexityReduction.Presentation.NAEThreeSATTM
import ComplexityReduction.Presentation.SatisfiabilityTM
import ComplexityReduction.Program.List

/-!
Public construction scaffold for authoring a new positive-NAE4 Boolean-CSP
reduction.

This module intentionally contains no NAE4-to-CSP clause gadget, no final
source-to-target executable, no target-specific direct-TM theorem, and no
target-specific semantic correctness theorem.  It exposes the established
3SAT-to-NAE3 predecessor and the four-ary positive NAE constraint machinery
needed to author the missing bridge in independently checked DAG nodes.
-/

namespace ComplexityReduction.Agent.Hardness.BooleanCSPNAE4ReductionScaffold

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP

/-- A reusable predecessor stage, without any Boolean-CSP target bridge. -/
structure ReferenceIngressSeed
    (source reference : Encoding.PresentedProblem) where
  executable : source.Instance → reference.Instance
  executableDirectTM :
    Authoring.ExecutableDirectTMEvidence source reference executable
  executableCorrect :
    Authoring.ExecutableSemanticProof source reference executable

/-- Exact structured-3SAT ingress to the public NAE-3SAT presentation. -/
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

/-- The one-symbol positive NAE-4 language, definitionally matching Q-B02. -/
noncomputable def gamma : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => StandardRelations.notAllEqualRel 4

/-- Collision-free key for one signed literal. -/
abbrev literalKey : SAT.Literal → Nat :=
  Domain.ThreeSATToNAEThreeSAT.literalKey

/-- Canonical faithful encoded type of one signed literal. -/
abbrev literalEncoding : EncodedType :=
  Presentation.Satisfiability.literalEncodedType

/-- Canonical faithful encoded type of one exact NAE clause. -/
abbrev clauseEncoding : EncodedType :=
  Presentation.NAEThreeSAT.clauseEncodedType

/-- Flip only one literal's polarity. -/
def complementLiteral (literal : SAT.Literal) : SAT.Literal :=
  SAT.Clause.negate literal

/-- Complementing a literal flips its Boolean value under every assignment. -/
@[simp] theorem complementLiteral_eval (literal : SAT.Literal)
    (assignment : SAT.Assignment) :
    (complementLiteral literal).eval assignment = !literal.eval assignment := by
  cases literal with
  | mk var neg =>
      cases neg <;> simp [complementLiteral, SAT.Clause.negate, SAT.Literal.eval]

/-- Decode the public signed-literal key into that literal's Boolean value. -/
def literalAssignment (assignment : SAT.Assignment) : SAT.Assignment :=
  fun key =>
    let decoded := Nat.unpair key
    if decoded.2 = 0 then assignment decoded.1 else !(assignment decoded.1)

@[simp] theorem literalAssignment_literalKey
    (assignment : SAT.Assignment) (literal : SAT.Literal) :
    literalAssignment assignment (literalKey literal) = literal.eval assignment := by
  cases literal with
  | mk var neg =>
      cases neg <;>
        simp [literalAssignment, literalKey,
          Domain.ThreeSATToNAEThreeSAT.literalKey,
          ComplexityReduction.boolToNat, Nat.unpair_pair, SAT.Literal.eval]

/-- Read a source assignment from the positive key of each variable. -/
def positiveKeyAssignment (assignment : SAT.Assignment) : SAT.Assignment :=
  fun var => assignment (literalKey (SAT.Literal.positive var))

/-- A positive/negative key complement law recovers every signed literal value. -/
theorem literal_eval_positiveKeyAssignment
    (assignment : SAT.Assignment)
    (negativeValue : ∀ var,
      assignment (literalKey (SAT.Literal.negative var)) =
        !assignment (literalKey (SAT.Literal.positive var)))
    (literal : SAT.Literal) :
    literal.eval (positiveKeyAssignment assignment) =
      assignment (literalKey literal) := by
  cases literal with
  | mk var neg =>
      cases neg
      · rfl
      · simpa [positiveKeyAssignment, SAT.Literal.eval,
          SAT.Literal.positive, SAT.Literal.negative] using
            (negativeValue var).symm

/-- Recover one signed literal from only its own local complement constraint. -/
theorem literal_eval_positiveKeyAssignment_of_complement
    (assignment : SAT.Assignment)
    (literal : SAT.Literal)
    (consistent :
      assignment (literalKey (complementLiteral literal)) =
        !assignment (literalKey literal)) :
    literal.eval (positiveKeyAssignment assignment) =
      assignment (literalKey literal) := by
  cases literal with
  | mk var neg =>
      cases neg
      · rfl
      · simpa [positiveKeyAssignment, complementLiteral,
          SAT.Clause.negate, SAT.Literal.eval, SAT.Literal.positive,
          SAT.Literal.negative] using congrArg Bool.not consistent

/-! ### Public clause/literal direct-TM building blocks -/

/-- Public direct-TM view from one clause to its exact nested encoder payload. -/
theorem clausePayload_tmPolyTime :
    TMPolyTimeMap clauseEncoding
      Presentation.NAEThreeSAT.clausePayloadEncodedType
      Presentation.NAEThreeSAT.clausePayload := by
  simpa [clauseEncoding] using
    Presentation.NAEThreeSAT.clausePayload_tmPolyTime

/-- Public direct-TM projection of the first literal of one exact NAE clause. -/
theorem clauseFirst_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.first := by
  simpa [clauseEncoding, literalEncoding] using
    Presentation.NAEThreeSAT.clauseFirst_tmPolyTime

/-- Public direct-TM projection of the second literal of one exact NAE clause. -/
theorem clauseSecond_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.second := by
  simpa [clauseEncoding, literalEncoding] using
    Presentation.NAEThreeSAT.clauseSecond_tmPolyTime

/-- Public direct-TM projection of the third literal of one exact NAE clause. -/
theorem clauseThird_tmPolyTime :
    TMPolyTimeMap clauseEncoding literalEncoding NAEThreeSAT.Clause.third := by
  simpa [clauseEncoding, literalEncoding] using
    Presentation.NAEThreeSAT.clauseThird_tmPolyTime

/-- Public direct-TM polarity flip for one canonically encoded literal. -/
theorem complementLiteral_tmPolyTime :
    TMPolyTimeMap literalEncoding literalEncoding complementLiteral := by
  simpa [literalEncoding, complementLiteral] using
    Presentation.Satisfiability.literalNegate_tmPolyTime

/-- Public direct-TM map from one signed literal to its collision-free key. -/
theorem literalKey_tmPolyTime :
    TMPolyTimeMap literalEncoding EncodedType.nat literalKey := by
  simpa [literalEncoding, literalKey] using
    Domain.ThreeSATToNAEThreeSAT.literalKey_tmPolyTime

/-- Compose an arbitrary direct-TM literal producer with the public key map. -/
theorem literalKeyAfter_tmPolyTime {X : EncodedType}
    {literal : X.Carrier → SAT.Literal}
    (hLiteral : TMPolyTimeMap X literalEncoding literal) :
    TMPolyTimeMap X EncodedType.nat (fun input => literalKey (literal input)) := by
  have output := TMPolyTimeMap.comp literalKey_tmPolyTime hLiteral
  simpa [Function.comp] using output

/-- Compose an arbitrary direct-TM literal producer with polarity complement. -/
theorem complementLiteralAfter_tmPolyTime {X : EncodedType}
    {literal : X.Carrier → SAT.Literal}
    (hLiteral : TMPolyTimeMap X literalEncoding literal) :
    TMPolyTimeMap X literalEncoding
      (fun input => complementLiteral (literal input)) := by
  have output := TMPolyTimeMap.comp complementLiteral_tmPolyTime hLiteral
  simpa [Function.comp] using output

/-- Produce the collision-free key of the complemented output literal. -/
theorem complementKeyAfter_tmPolyTime {X : EncodedType}
    {literal : X.Carrier → SAT.Literal}
    (hLiteral : TMPolyTimeMap X literalEncoding literal) :
    TMPolyTimeMap X EncodedType.nat
      (fun input => literalKey (complementLiteral (literal input))) := by
  exact literalKeyAfter_tmPolyTime
    (complementLiteralAfter_tmPolyTime hLiteral)

/-- Generic positive four-ary constraint constructor over the scaffold language. -/
noncomputable def quaternaryConstraint (first second third fourth : Nat) :
    Constraint gamma where
  symbol := ()
  vars := fun
    | ⟨0, _⟩ => first
    | ⟨1, _⟩ => second
    | ⟨2, _⟩ => third
    | ⟨3, _⟩ => fourth

/-- Satisfaction of the generic four-ary constructor in pointwise form. -/
theorem quaternaryConstraint_satisfies_iff (first second third fourth : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (quaternaryConstraint first second third fourth) assignment ↔
      ¬ (assignment first = assignment second ∧
        assignment second = assignment third ∧
        assignment third = assignment fourth) := by
  let tuple := Constraint.assignmentTuple
    (quaternaryConstraint first second third fourth) assignment
  have tupleEquality : tuple =
      StandardRelations.quadTuple (assignment first) (assignment second)
        (assignment third) (assignment fourth) := by
    funext index
    fin_cases index <;> rfl
  change (StandardRelations.notAllEqualRel 4).Holds tuple ↔ _
  rw [tupleEquality]
  exact StandardRelations.notAllEqual4Rel_holds_quad_iff _ _ _ _

/-- A clause constraint: one NAE-3 clause padded into one NAE-4 constraint. -/
noncomputable def clauseConstraint (first second third : Nat) :
    Constraint gamma :=
  quaternaryConstraint first second third third

/-- One padded clause constraint rejects exactly the constant clause tuple. -/
theorem clauseConstraint_satisfies_iff (first second third : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (clauseConstraint first second third) assignment ↔
      ¬ (assignment first = assignment second ∧
        assignment second = assignment third) := by
  rw [clauseConstraint, quaternaryConstraint_satisfies_iff]
  constructor
  · intro notAll ⟨firstSecond, secondThird⟩
    exact notAll ⟨firstSecond, secondThird, rfl⟩
  · intro notAll
    rintro ⟨firstSecond, secondThird, _⟩
    exact notAll ⟨firstSecond, secondThird⟩

/-- Two Boolean values differ exactly when the second is the negation of the first. -/
theorem bool_ne_iff_eq_not (first second : Bool) :
    first ≠ second ↔ second = !first := by
  cases first <;> cases second <;> simp

/-- Repeating one endpoint in an NAE-4 constraint enforces Boolean complement. -/
theorem quaternaryConstraint_repeat_satisfies_iff (first second : Nat)
    (assignment : SAT.Assignment) :
    Constraint.Satisfies (quaternaryConstraint first second first first) assignment ↔
      assignment second = !assignment first := by
  rw [quaternaryConstraint_satisfies_iff]
  constructor
  · intro different
    apply (bool_ne_iff_eq_not _ _).1
    intro equal
    exact different ⟨equal, equal.symm, rfl⟩
  · intro complement equalities
    have different : assignment first ≠ assignment second :=
      (bool_ne_iff_eq_not _ _).2 complement
    exact different equalities.1

/-- Canonical raw encoder payload for one positive four-ary constraint. -/
def constraintPayload (first second third fourth : Nat) : Nat × List Nat :=
  (0, [first, second, third, fourth])

/-- The unique relation symbol of the scaffold language has code zero. -/
theorem relationCode_eq_zero (symbol : gamma.Symbol) :
    Presentation.FiniteDomainCSPTable.relationCode gamma symbol = 0 := by
  have bounded :=
    Presentation.FiniteDomainCSPTable.relationCode_lt_card gamma symbol
  have lessThanOne :
      Presentation.FiniteDomainCSPTable.relationCode gamma symbol < 1 := by
    simpa [gamma] using bounded
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ lessThanOne)

/-- The generic four-ary constructor uses the canonical finite-table payload. -/
theorem constraintCode_quaternaryConstraint (first second third fourth : Nat) :
    Presentation.FiniteDomainCSPTable.constraintCode
        (quaternaryConstraint first second third fourth) =
      constraintPayload first second third fourth := by
  apply Prod.ext
  · simpa [Presentation.FiniteDomainCSPTable.constraintCode,
      constraintPayload] using relationCode_eq_zero ()
  · simp [Presentation.FiniteDomainCSPTable.constraintCode,
      constraintPayload, quaternaryConstraint, Constraint.varsList,
      gamma, StandardRelations.notAllEqualRel,
      BoolRel.ofPredicate, List.ofFn, Fin.foldr, Fin.foldr.loop]

/-- Direct-TM assembly of one canonical four-ary-constraint payload. -/
theorem constraintPayload_tmPolyTime {X : EncodedType}
    {first second third fourth : X.Carrier → Nat}
    (hFirst : TMPolyTimeMap X EncodedType.nat first)
    (hSecond : TMPolyTimeMap X EncodedType.nat second)
    (hThird : TMPolyTimeMap X EncodedType.nat third)
    (hFourth : TMPolyTimeMap X EncodedType.nat fourth) :
    TMPolyTimeMap X
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      (fun input => constraintPayload (first input) (second input)
        (third input) (fourth input)) := by
  have hVariables := TMPolyTimeMap.list_cons_of hFirst
    (TMPolyTimeMap.list_cons_of hSecond
      (TMPolyTimeMap.list_cons_of hThird
        (TMPolyTimeMap.list_singleton_of hFourth)))
  have hRelation : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (show Nat from 0)) :=
    TMPolyTimeMap.const X EncodedType.nat (show Nat from 0)
  have output := TMPolyTimeMap.prod_mk hRelation hVariables
  simpa [constraintPayload,
    Presentation.FiniteDomainCSPTable.constraintCodeEncodedType,
    Function.comp] using output

/--
Direct-TM assembly of the encoded canonical four-ary constraint.
The four computed variable keys are inferred from their polynomial-time proofs;
the caller still chooses the keys and how the resulting constraints are assembled.
-/
theorem quaternaryConstraintCode_tmPolyTime {X : EncodedType}
    {first second third fourth : X.Carrier → Nat}
    (hFirst : TMPolyTimeMap X EncodedType.nat first)
    (hSecond : TMPolyTimeMap X EncodedType.nat second)
    (hThird : TMPolyTimeMap X EncodedType.nat third)
    (hFourth : TMPolyTimeMap X EncodedType.nat fourth) :
    TMPolyTimeMap X
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType
      (fun input => Presentation.FiniteDomainCSPTable.constraintCode
        (quaternaryConstraint (first input) (second input) (third input)
          (fourth input))) := by
  simpa only [constraintCode_quaternaryConstraint] using
    constraintPayload_tmPolyTime hFirst hSecond hThird hFourth

/-- Lift an authored clause gadget pointwise to an exact NAE formula bridge. -/
noncomputable def referenceExecutableFromClauseGadget
    (clauseGadget : NAEThreeSAT.Clause → CSP.Formula gamma)
    (formula : NAEThreeSAT.Formula) : CSP.Formula gamma :=
  formula.flatMap clauseGadget

/--
Generic direct-TM lifting from an authored clause gadget to formula `flatMap`.
The target formula encoder is exactly a list of finite-table constraint codes.
-/
theorem referenceExecutableFromClauseGadget_tmPolyTime
    {clauseGadget : NAEThreeSAT.Clause → CSP.Formula gamma}
    (hGadget :
      TMPolyTimeMap Presentation.NAEThreeSAT.clauseEncodedType
        (Presentation.FiniteDomainCSPTable.encodedType gamma) clauseGadget) :
    TMPolyTimeMap Presentation.NAEThreeSAT.formulaEncodedType
      (Presentation.FiniteDomainCSPTable.encodedType gamma)
      (referenceExecutableFromClauseGadget clauseGadget) := by
  have hGadgetCode :
      TMPolyTimeMap Presentation.NAEThreeSAT.clauseEncodedType
        Presentation.FiniteDomainCSPTable.formulaCodeEncodedType
        (fun clause =>
          Presentation.FiniteDomainCSPTable.formulaCode gamma
            (clauseGadget clause)) := by
    rcases hGadget with ⟨gadgetTM⟩
    refine ⟨
      { tm := gadgetTM.tm
        inputAlphabet := gadgetTM.inputAlphabet
        outputAlphabet := gadgetTM.outputAlphabet
        time := gadgetTM.time
        outputsFun := by
          intro clause
          simpa [Presentation.FiniteDomainCSPTable.encodedType] using
            gadgetTM.outputsFun clause }⟩
  have mapped := TMPolyTimeMap.list_map hGadgetCode
  have flattened := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime
      Presentation.FiniteDomainCSPTable.constraintCodeEncodedType)
    mapped
  exact Presentation.FiniteDomainCSPTable.formula_tmPolyTime_of_code flattened
    (by
      intro formula
      change
        (List.map (fun clause =>
          Presentation.FiniteDomainCSPTable.formulaCode gamma
            (clauseGadget clause)) formula).flatten =
        List.map Presentation.FiniteDomainCSPTable.constraintCode
          (formula.flatMap clauseGadget)
      rw [List.map_flatMap]
      rfl)

/-- Compose an authored reference bridge after the established 3SAT ingress. -/
noncomputable def executableFromReference
    (referenceExecutable : NAEThreeSAT.Formula → CSP.Formula gamma)
    (formula : SAT.ThreeCNF) : CSP.Formula gamma :=
  referenceExecutable (threeSATToNAEThreeSATIngress.executable formula)

/-- Generic direct-TM composition with the established 3SAT-to-NAE3 ingress. -/
theorem executableFromReference_tmPolyTime
    {referenceExecutable : NAEThreeSAT.Formula → CSP.Formula gamma}
    (hReference :
      TMPolyTimeMap Presentation.NAEThreeSAT.formulaEncodedType
        (Presentation.FiniteDomainCSPTable.encodedType gamma)
        referenceExecutable) :
    TMPolyTimeMap Domain.ThreeSATToNAEThreeSAT.sourceEncoding
      (Presentation.FiniteDomainCSPTable.encodedType gamma)
      (executableFromReference referenceExecutable) := by
  have output := TMPolyTimeMap.comp hReference
    Domain.ThreeSATToNAEThreeSAT.executable_tmPolyTime
  simpa [executableFromReference, threeSATToNAEThreeSATIngress,
    Function.comp] using output

assert_standard_axioms
  threeSATToNAEThreeSATIngress,
  complementLiteral_eval,
  literalAssignment_literalKey,
  literal_eval_positiveKeyAssignment,
  literal_eval_positiveKeyAssignment_of_complement,
  quaternaryConstraint_satisfies_iff,
  clauseConstraint_satisfies_iff,
  bool_ne_iff_eq_not,
  quaternaryConstraint_repeat_satisfies_iff,
  clausePayload_tmPolyTime,
  clauseFirst_tmPolyTime,
  clauseSecond_tmPolyTime,
  clauseThird_tmPolyTime,
  complementLiteral_tmPolyTime,
  literalKey_tmPolyTime,
  literalKeyAfter_tmPolyTime,
  complementLiteralAfter_tmPolyTime,
  complementKeyAfter_tmPolyTime,
  quaternaryConstraint,
  clauseConstraint,
  constraintCode_quaternaryConstraint,
  constraintPayload_tmPolyTime,
  quaternaryConstraintCode_tmPolyTime,
  referenceExecutableFromClauseGadget,
  referenceExecutableFromClauseGadget_tmPolyTime,
  executableFromReference,
  executableFromReference_tmPolyTime

end ComplexityReduction.Agent.Hardness.BooleanCSPNAE4ReductionScaffold
