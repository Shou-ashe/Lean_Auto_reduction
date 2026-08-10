/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Satisfiability

/-!
An exact public presentation of not-all-equal 3-SAT.

The carrier stores exactly three ordinary SAT literals per clause.  A clause
is accepted when its three literal values are not all equal, and a formula is
accepted when one total Boolean assignment accepts every clause.  The selected
codec is a list of nested triples over the canonical structured SAT-literal
codec.  This module owns only the problem/presentation boundary; it contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace NAEThreeSAT

/-- One ordered not-all-equal clause with exactly three literal positions. -/
structure Clause where
  first : SAT.Literal
  second : SAT.Literal
  third : SAT.Literal
  deriving DecidableEq, Repr

namespace Clause

/-- A NAE clause holds precisely when its three Boolean values are not all equal. -/
def Satisfies (clause : Clause) (assignment : SAT.Assignment) : Prop :=
  ¬ (clause.first.eval assignment = clause.second.eval assignment ∧
      clause.second.eval assignment = clause.third.eval assignment)

/-- Executable Boolean spelling of the exact NAE predicate. -/
def satisfiesBool (clause : Clause) (assignment : SAT.Assignment) : Bool :=
  !((clause.first.eval assignment == clause.second.eval assignment) &&
      (clause.second.eval assignment == clause.third.eval assignment))

@[simp] theorem satisfiesBool_eq_true_iff (clause : Clause) (assignment : SAT.Assignment) :
    satisfiesBool clause assignment = true ↔ Satisfies clause assignment := by
  cases firstValue : clause.first.eval assignment <;>
    cases secondValue : clause.second.eval assignment <;>
      cases thirdValue : clause.third.eval assignment <;>
        simp [satisfiesBool, Satisfies, firstValue, secondValue, thirdValue]

/-- Complement every literal polarity in one NAE clause. -/
def negate (clause : Clause) : Clause where
  first := SAT.Clause.negate clause.first
  second := SAT.Clause.negate clause.second
  third := SAT.Clause.negate clause.third

end Clause

/-- A NAE-3SAT formula is an ordered list of exact three-literal clauses. -/
abbrev Formula : Type := List Clause

namespace Formula

/-- Pointwise satisfaction of every exact NAE clause. -/
def Satisfies (formula : Formula) (assignment : SAT.Assignment) : Prop :=
  ∀ clause ∈ formula, clause.Satisfies assignment

/-- Existential satisfiability of an exact NAE-3SAT formula. -/
def Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : SAT.Assignment, Satisfies formula assignment

@[simp] theorem satisfies_nil (assignment : SAT.Assignment) :
    Satisfies ([] : Formula) assignment := by
  simp [Satisfies]

@[simp] theorem satisfies_append (left right : Formula) (assignment : SAT.Assignment) :
    Satisfies (left ++ right) assignment ↔
      Satisfies left assignment ∧ Satisfies right assignment := by
  simp only [Satisfies, List.mem_append]
  aesop

end Formula

end NAEThreeSAT

namespace Presentation
namespace NAEThreeSAT

open ComplexityReduction.NAEThreeSAT

/-- The exact nested-product payload used to encode one NAE clause. -/
abbrev clausePayloadEncodedType : EncodedType :=
  EncodedType.prod Presentation.Satisfiability.literalPresentation.encodedType
    (EncodedType.prod Presentation.Satisfiability.literalPresentation.encodedType
      Presentation.Satisfiability.literalPresentation.encodedType)

/-- Read one NAE clause as its exact nested-product payload. -/
def clausePayload (clause : Clause) :
    clausePayloadEncodedType.Carrier :=
  (clause.first, (clause.second, clause.third))

/-- Faithful finite-alphabet encoding for exact NAE clauses. -/
def clauseEncodedType : EncodedType where
  Carrier := Clause
  Symbol := clausePayloadEncodedType.Symbol
  finite_symbol := clausePayloadEncodedType.finite_symbol
  encode := fun clause => clausePayloadEncodedType.encode (clausePayload clause)

private theorem clausePayload_injective : Function.Injective clausePayload := by
  intro left right equality
  cases left with
  | mk leftFirst leftSecond leftThird =>
      cases right with
      | mk rightFirst rightSecond rightThird =>
          simp only [clausePayload] at equality
          cases equality
          rfl

/-- The selected exact NAE-clause encoding is faithful. -/
theorem clauseEncodedType_encode_injective :
    Function.Injective clauseEncodedType.encode := by
  intro left right equality
  apply clausePayload_injective
  exact
    (EncodedType.prod_encode_injective
      ComplexityReduction.Karp21.literalStructuredEncodedType_encode_injective
      (EncodedType.prod_encode_injective
        ComplexityReduction.Karp21.literalStructuredEncodedType_encode_injective
        ComplexityReduction.Karp21.literalStructuredEncodedType_encode_injective)) equality

/-- Exact list encoding for ordered NAE formulas. -/
abbrev formulaEncodedType : EncodedType :=
  EncodedType.list clauseEncodedType

/-- Faithfulness of the complete ordered NAE formula encoding. -/
theorem formulaEncodedType_encode_injective :
    Function.Injective formulaEncodedType.encode :=
  EncodedType.list_encode_injective clauseEncodedType_encode_injective

/-- Full representation identity of one exact NAE clause. -/
def clauseShape : CodecShape :=
  .prod Presentation.Satisfiability.literalShape
    (.prod Presentation.Satisfiability.literalShape
      Presentation.Satisfiability.literalShape)

/-- Full representation identity of an ordered exact NAE formula. -/
def structuredShape : CodecShape :=
  .list clauseShape

/-- Canonical lawful exact NAE-3SAT representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := formulaEncodedType
  representation := structuredShape.identity
  faithful := ⟨formulaEncodedType_encode_injective⟩

@[simp] theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = formulaEncodedType :=
  rfl

@[simp] theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The represented carrier is exactly the public NAE formula carrier. -/
theorem structuredPresentation_carrier_eq_formula :
    structuredPresentation.Carrier = ComplexityReduction.NAEThreeSAT.Formula :=
  rfl

/-- The exact NAE-3SAT semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ComplexityReduction.NAEThreeSAT.Formula.Satisfiable

/-- Canonical exact public NAE-3SAT endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp] theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp] theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

@[simp] theorem structuredProblem_accepts (formula : structuredProblem.Instance) :
    structuredProblem.accepts formula ↔
      ComplexityReduction.NAEThreeSAT.Formula.Satisfiable formula :=
  Iff.rfl

assert_standard_axioms
  clauseEncodedType_encode_injective,
  formulaEncodedType_encode_injective,
  structuredProblem_accepts

end NAEThreeSAT
end Presentation
end ComplexityReduction
