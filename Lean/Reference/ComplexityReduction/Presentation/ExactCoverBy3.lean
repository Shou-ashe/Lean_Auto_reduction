/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
An exact public presentation of the Exact Cover by 3-sets decision problem.

A set is a length-three vector of natural elements; element identity is
functional, so a set may repeat an element but its three positions are always
distinct positions of the carrier.  An instance is an ordered family of such
sets.  It is accepted when some subfamily (a list of family members, no set
reused) covers every element of the universe exactly once: each universe
element appears in exactly one chosen set at exactly one position.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace ExactCoverBy3

/-- One length-three set over natural elements. -/
structure Set3 where
  first : Nat
  second : Nat
  third : Nat

namespace Set3

/-- The three positions of one set hold pairwise distinct elements. -/
def membersNodup (s : Set3) : Prop :=
  s.first ≠ s.second ∧ s.second ≠ s.third ∧ s.first ≠ s.third

/-- Two sets have disjoint element ranges. -/
def Disjoint (left right : Set3) : Prop :=
  left.first ≠ right.first ∧ left.first ≠ right.second ∧ left.first ≠ right.third ∧
    left.second ≠ right.first ∧ left.second ≠ right.second ∧ left.second ≠ right.third ∧
    left.third ≠ right.first ∧ left.third ≠ right.second ∧ left.third ≠ right.third

end Set3

/-- An exact-cover instance: an ordered family of length-three sets. -/
structure ExactCoverBy3Input where
  sets : List Set3

namespace ExactCoverBy3Input

/-- The universe is the set of elements occurring anywhere in the family. -/
def Universe (I : ExactCoverBy3Input) : Set Nat :=
  { x | ∃ s ∈ I.sets, s.first = x ∨ s.second = x ∨ s.third = x }

/-- One element is covered exactly once when exactly one chosen position holds it. -/
def CoversExactlyOnce (I : ExactCoverBy3Input) (sub : List Set3) (x : Nat) : Prop :=
  ∃ s ∈ sub,
    (s.first = x ∨ s.second = x ∨ s.third = x) ∧
      ∀ t ∈ sub, (t.first = x ∨ t.second = x ∨ t.third = x) → t = s

/-- Some subfamily covers every element of a family exactly once. -/
def acceptedFamily (sets : List Set3) : Prop :=
  ∃ sub : List Set3,
    (∀ s ∈ sub, s ∈ sets) ∧
    (∀ s ∈ sub, Set3.membersNodup s) ∧
    (∀ x, x ∈ Universe { sets := sets } → CoversExactlyOnce { sets := sets } sub x)

/-- The instance is accepted when some subfamily covers every element exactly once. -/
def accepted (I : ExactCoverBy3Input) : Prop :=
  acceptedFamily I.sets

/-- The empty family has an empty exact cover. -/
theorem accepted_empty_family : accepted { sets := [] } := by
  refine ⟨[], ?_, ?_, ?_⟩
  · intro s hs
    simp at hs
  · intro s hs
    simp at hs
  · intro x hx
    simp [Universe] at hx

end ExactCoverBy3Input

end ExactCoverBy3

namespace Presentation
namespace ExactCoverBy3

open ComplexityReduction.ExactCoverBy3

/-- The exact nested-product payload of one length-three set. -/
abbrev set3PayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Read one length-three set as its exact nested-product payload. -/
def set3Payload (s : Set3) : set3PayloadEncodedType.Carrier :=
  (s.first, (s.second, s.third))

/-- Faithful finite-alphabet encoding for one length-three set. -/
def set3EncodedType : EncodedType where
  Carrier := Set3
  Symbol := set3PayloadEncodedType.Symbol
  finite_symbol := set3PayloadEncodedType.finite_symbol
  encode := fun s => set3PayloadEncodedType.encode (set3Payload s)

private theorem set3Payload_injective : Function.Injective set3Payload := by
  intro left right equality
  cases left with
  | mk leftFirst leftSecond leftThird =>
      cases right with
      | mk rightFirst rightSecond rightThird =>
          simp only [set3Payload] at equality
          cases equality
          rfl

/-- The exact length-three-set encoding is faithful. -/
theorem set3EncodedType_encode_injective :
    Function.Injective set3EncodedType.encode := by
  intro left right equality
  apply set3Payload_injective
  exact
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        EncodedType.nat_encode_injective)) equality

/-- Exact list encoding for ordered families of length-three sets. -/
abbrev familyEncodedType : EncodedType :=
  EncodedType.list set3EncodedType

/-- Faithfulness of the complete ordered family encoding. -/
theorem familyEncodedType_encode_injective :
    Function.Injective familyEncodedType.encode :=
  EncodedType.list_encode_injective set3EncodedType_encode_injective

/-- Full representation identity of one length-three set. -/
def set3Shape : CodecShape :=
  .prod .unaryNat (.prod .unaryNat .unaryNat)

/-- Full representation identity of an ordered family. -/
def structuredShape : CodecShape :=
  .list set3Shape

/-- Canonical lawful exact exact-cover-by-3 representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := familyEncodedType
  representation := structuredShape.identity
  faithful := ⟨familyEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = familyEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The represented carrier is exactly the public family carrier. -/
theorem structuredPresentation_carrier_eq_Family :
    structuredPresentation.Carrier = List Set3 :=
  rfl

/-- The exact exact-cover-by-3 semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ExactCoverBy3Input.acceptedFamily

/-- Canonical exact public exact-cover-by-3 endpoint. -/
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
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ ExactCoverBy3Input.acceptedFamily input :=
  Iff.rfl

assert_standard_axioms
  set3EncodedType_encode_injective,
  familyEncodedType_encode_injective,
  structuredProblem_accepts

end ExactCoverBy3
end Presentation
end ComplexityReduction
