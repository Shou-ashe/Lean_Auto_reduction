/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
An exact public presentation of the Set Splitting decision problem.

An instance is a family of finite sets over natural elements.  It is accepted
when there is a two-coloring of the elements that splits every set: each set
contains an element of each color.  The witness is a total function
`Nat → Bool`; sets with fewer than two distinct elements are unsplittable and
therefore make the instance a No instance.  Empty families are accepted by
any coloring.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace SetSplitting

/-- A set-splitting instance: an ordered family of finite sets. -/
structure SetSplittingInput where
  family : List (List Nat)
  deriving Repr

namespace SetSplittingInput

/-- A two-coloring splits the whole family when every set has both colors. -/
def Split (family : List (List Nat)) (left : Nat → Bool) : Prop :=
  ∀ s ∈ family, (∃ x ∈ s, left x = true) ∧ (∃ x ∈ s, left x = false)

/-- The instance is accepted when some two-coloring splits every set. -/
def accepted (I : SetSplittingInput) : Prop :=
  ∃ left : Nat → Bool, Split I.family left

/-- The empty family is split by any coloring. -/
theorem accepted_empty_family :
    accepted { family := [] } := by
  refine ⟨fun _ => true, ?_⟩
  intro s hs
  have hfalse : False := List.not_mem_nil hs
  exact False.elim hfalse

/-- A single-element set can never be split. -/
theorem rejected_singleton (element : Nat) :
    ¬ accepted { family := [[element]] } := by
  rintro ⟨left, hsplit⟩
  have hleft := (hsplit [element] (by simp)).1
  have hright := (hsplit [element] (by simp)).2
  rcases hleft with ⟨x, hx, hxcolor⟩
  rcases hright with ⟨y, hy, hycolor⟩
  have : x = element := by
    simpa using (List.mem_singleton.mp hx)
  have : y = element := by
    simpa using (List.mem_singleton.mp hy)
  subst x
  subst y
  rw [hxcolor] at hycolor
  contradiction

end SetSplittingInput

end SetSplitting

namespace Presentation
namespace SetSplitting

open ComplexityReduction.SetSplitting

/-- The complete ordered layout of a set-splitting instance. -/
def setSplittingShape : CodecShape :=
  .list (.list .unaryNat)

/-- Concrete finite-alphabet encoding of the exact set-splitting carrier. -/
def setSplittingEncodedType : EncodedType where
  Carrier := SetSplittingInput
  Symbol := (EncodedType.list (EncodedType.list EncodedType.nat)).Symbol
  finite_symbol := (EncodedType.list (EncodedType.list EncodedType.nat)).finite_symbol
  encode := fun I => (EncodedType.list (EncodedType.list EncodedType.nat)).encode I.family

/-- The exact set-splitting encoding is faithful. -/
theorem setSplittingEncodedType_encode_injective :
    Function.Injective setSplittingEncodedType.encode := by
  intro I J henc
  have hfamily : I.family = J.family :=
    (EncodedType.list_encode_injective
      (EncodedType.list_encode_injective EncodedType.nat_encode_injective)) (by
      simpa [setSplittingEncodedType] using henc)
  cases I
  cases J
  cases hfamily
  rfl

/-- Canonical lawful exact set-splitting representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := setSplittingEncodedType
  representation := setSplittingShape.identity
  faithful := ⟨setSplittingEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = setSplittingEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = setSplittingShape.identity :=
  rfl

/-- The represented carrier is exactly the public set-splitting syntax. -/
theorem structuredPresentation_carrier_eq_SetSplittingInput :
    structuredPresentation.Carrier = SetSplittingInput :=
  rfl

/-- The exact set-splitting semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := SetSplittingInput.accepted

/-- Canonical exact public set-splitting endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = setSplittingShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ SetSplittingInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ SetSplittingInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  setSplittingEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  SetSplittingInput.accepted_empty_family

end SetSplitting
end Presentation
end ComplexityReduction
