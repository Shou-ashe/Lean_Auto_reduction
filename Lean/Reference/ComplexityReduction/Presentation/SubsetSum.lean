/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
An exact public presentation of the Subset Sum decision problem.

An instance is a list of unary natural numbers together with a target.  It is
accepted when some sublist of the items (preserving each item's identity)
sums exactly to the target.  Subsequence semantics means the witness never
reuses an item, so duplicate values in the item list remain distinct
elements.  The target is an ordinary unary natural; a target outside the
total sum range is simply a No instance.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace SubsetSum

/-- A subset-sum instance: an item list plus a target value. -/
structure SubsetSumInput where
  items : List Nat
  target : Nat
  deriving Repr

namespace SubsetSumInput

/-- The instance is accepted when some sublist of items sums exactly to the target. -/
def accepted (I : SubsetSumInput) : Prop :=
  ∃ witness : List Nat, witness.Sublist I.items ∧ witness.sum = I.target

/-- A zero target is always reachable by the empty sublist. -/
theorem accepted_zero_target (I : SubsetSumInput) :
    accepted { items := I.items, target := 0 } := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · simp

/-- Every accepted witness is a sublist of the declared item list. -/
theorem accepted_witness_sublist (I : SubsetSumInput) :
    accepted I → ∃ witness : List Nat, witness.Sublist I.items ∧ witness.sum = I.target := by
  rintro ⟨witness, hsub, hsum⟩
  exact ⟨witness, hsub, hsum⟩

end SubsetSumInput

end SubsetSum

namespace Presentation
namespace SubsetSum

open ComplexityReduction.SubsetSum

/-- The complete ordered layout of a subset-sum instance: items plus target. -/
def subsetSumShape : CodecShape :=
  .prod (.list .unaryNat) .unaryNat

/-- Nested-product finite-alphabet payload for one subset-sum instance. -/
def subsetSumTupleEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat

/-- Concrete finite-alphabet encoding of the exact subset-sum carrier. -/
def subsetSumEncodedType : EncodedType where
  Carrier := SubsetSumInput
  Symbol := subsetSumTupleEncodedType.Symbol
  finite_symbol := subsetSumTupleEncodedType.finite_symbol
  encode := fun I => subsetSumTupleEncodedType.encode (I.items, I.target)

/-- The exact subset-sum encoding is faithful. -/
theorem subsetSumEncodedType_encode_injective :
    Function.Injective subsetSumEncodedType.encode := by
  intro I J henc
  have htuple : (I.items, I.target) = (J.items, J.target) :=
    (EncodedType.prod_encode_injective
      (EncodedType.list_encode_injective EncodedType.nat_encode_injective)
      EncodedType.nat_encode_injective) (by
      simpa [subsetSumEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Canonical lawful exact subset-sum representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := subsetSumEncodedType
  representation := subsetSumShape.identity
  faithful := ⟨subsetSumEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = subsetSumEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = subsetSumShape.identity :=
  rfl

/-- The represented carrier is exactly the public subset-sum syntax. -/
theorem structuredPresentation_carrier_eq_SubsetSumInput :
    structuredPresentation.Carrier = SubsetSumInput :=
  rfl

/-- The exact subset-sum semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := SubsetSumInput.accepted

/-- Canonical exact public subset-sum endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = subsetSumShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ SubsetSumInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ SubsetSumInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  subsetSumEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  SubsetSumInput.accepted_zero_target

end SubsetSum
end Presentation
end ComplexityReduction
