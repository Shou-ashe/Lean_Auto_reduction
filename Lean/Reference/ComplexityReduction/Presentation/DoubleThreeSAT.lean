/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Satisfiability

/-!
An exact public presentation of the Double-3SAT decision problem.

The carrier stores exactly three ordinary SAT literals per clause, matching
the canonical structured 3SAT literal codec.  A clause is satisfied when all
three literal values are true, and a formula is satisfied when one total
Boolean assignment satisfies every clause.  Double-3SAT asks for the
assignment-counting semantics over the declared variable set: the formula is
accepted when at least two distinct total assignments satisfy it.  Because
assignments are total functions `Nat → Bool`, distinctness is functional
inequality; no undeclared variable or partial assignment can create a
spurious second witness.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace DoubleThreeSAT

/-- One ordered clause with exactly three literal positions. -/
structure Clause where
  first : SAT.Literal
  second : SAT.Literal
  third : SAT.Literal
  deriving DecidableEq, Repr

namespace Clause

/-- A clause holds precisely when all three literals evaluate to true. -/
def Satisfies (clause : Clause) (assignment : SAT.Assignment) : Prop :=
  clause.first.eval assignment = true ∧
    clause.second.eval assignment = true ∧
    clause.third.eval assignment = true

end Clause

/-- A Double-3SAT formula is an ordered list of exact three-literal clauses. -/
abbrev Formula : Type := List Clause

namespace Formula

/-- Pointwise satisfaction of every clause by one total assignment. -/
def Satisfies (formula : Formula) (assignment : SAT.Assignment) : Prop :=
  ∀ clause ∈ formula, clause.Satisfies assignment

/-- At least two distinct total assignments satisfy the formula. -/
def DoubleSatisfiable (formula : Formula) : Prop :=
  ∃ first second : SAT.Assignment,
    first ≠ second ∧ Satisfies formula first ∧ Satisfies formula second

/-- The empty formula has two distinct satisfying assignments. -/
theorem double_satisfiable_empty :
    DoubleSatisfiable ([] : Formula) := by
  refine ⟨fun _ => false, fun _ => true, ?_, ?_, ?_⟩
  · intro heq
    have := congrFun heq 0
    simp at this
  · intro clause hc
    simp at hc
  · intro clause hc
    simp at hc

end Formula

end DoubleThreeSAT

namespace Presentation
namespace DoubleThreeSAT

open ComplexityReduction.DoubleThreeSAT

/-- The exact nested-product payload used to encode one clause. -/
abbrev clausePayloadEncodedType : EncodedType :=
  EncodedType.prod Presentation.Satisfiability.literalPresentation.encodedType
    (EncodedType.prod Presentation.Satisfiability.literalPresentation.encodedType
      Presentation.Satisfiability.literalPresentation.encodedType)

/-- Read one clause as its exact nested-product payload. -/
def clausePayload (clause : Clause) :
    clausePayloadEncodedType.Carrier :=
  (clause.first, (clause.second, clause.third))

/-- Faithful finite-alphabet encoding for exact clauses. -/
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

/-- The selected exact clause encoding is faithful. -/
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

/-- Exact list encoding for ordered formulas. -/
abbrev formulaEncodedType : EncodedType :=
  EncodedType.list clauseEncodedType

/-- Faithfulness of the complete ordered formula encoding. -/
theorem formulaEncodedType_encode_injective :
    Function.Injective formulaEncodedType.encode :=
  EncodedType.list_encode_injective clauseEncodedType_encode_injective

/-- Full representation identity of one exact clause. -/
def clauseShape : CodecShape :=
  .prod Presentation.Satisfiability.literalShape
    (.prod Presentation.Satisfiability.literalShape
      Presentation.Satisfiability.literalShape)

/-- Full representation identity of an ordered exact formula. -/
def structuredShape : CodecShape :=
  .list clauseShape

/-- Canonical lawful exact Double-3SAT representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := formulaEncodedType
  representation := structuredShape.identity
  faithful := ⟨formulaEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = formulaEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The represented carrier is exactly the public formula carrier. -/
theorem structuredPresentation_carrier_eq_Formula :
    structuredPresentation.Carrier = ComplexityReduction.DoubleThreeSAT.Formula :=
  rfl

/-- The exact Double-3SAT semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := Formula.DoubleSatisfiable

/-- Canonical exact public Double-3SAT endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (formula : structuredProblem.Instance) :
    structuredProblem.accepts formula ↔ Formula.DoubleSatisfiable formula :=
  Iff.rfl

assert_standard_axioms
  clauseEncodedType_encode_injective,
  formulaEncodedType_encode_injective,
  structuredProblem_accepts

end DoubleThreeSAT
end Presentation
end ComplexityReduction
