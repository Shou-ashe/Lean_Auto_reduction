/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
An exact public presentation of the Exact Cover by 4-sets decision problem.

A set is a length-four tuple of natural elements.  An instance is an ordered
family of such sets.  It is accepted when some subfamily (a list of family
members, no set reused) covers every element of the universe exactly once:
each universe element appears in exactly one chosen set at exactly one
position.  This is the size-4 restricted presentation of Exact Cover; the
size promise is part of the carrier type, so no set outside the promised
cardinality can be encoded.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace ExactCoverBy4

/-- One length-four set over natural elements. -/
structure Set4 where
  first : Nat
  second : Nat
  third : Nat
  fourth : Nat

namespace Set4

/-- The four positions of one set hold pairwise distinct elements. -/
def membersNodup (s : Set4) : Prop :=
  s.first ≠ s.second ∧ s.first ≠ s.third ∧ s.first ≠ s.fourth ∧
    s.second ≠ s.third ∧ s.second ≠ s.fourth ∧ s.third ≠ s.fourth

end Set4

/-- An exact-cover instance: an ordered family of length-four sets. -/
structure ExactCoverBy4Input where
  sets : List Set4

namespace ExactCoverBy4Input

/-- The universe is the set of elements occurring anywhere in the family. -/
def Universe (I : ExactCoverBy4Input) : Set Nat :=
  { x | ∃ s ∈ I.sets,
      s.first = x ∨ s.second = x ∨ s.third = x ∨ s.fourth = x }

/-- One element is covered exactly once when exactly one chosen position holds it. -/
def CoversExactlyOnce (I : ExactCoverBy4Input) (sub : List Set4) (x : Nat) : Prop :=
  ∃ s ∈ sub,
    (s.first = x ∨ s.second = x ∨ s.third = x ∨ s.fourth = x) ∧
      ∀ t ∈ sub,
        (t.first = x ∨ t.second = x ∨ t.third = x ∨ t.fourth = x) → t = s

/-- Some subfamily covers every element of a family exactly once. -/
def acceptedFamily (sets : List Set4) : Prop :=
  ∃ sub : List Set4,
    (∀ s ∈ sub, s ∈ sets) ∧
    (∀ s ∈ sub, Set4.membersNodup s) ∧
    (∀ x, x ∈ Universe { sets := sets } → CoversExactlyOnce { sets := sets } sub x)

/-- The instance is accepted when some subfamily covers every element exactly once. -/
def accepted (I : ExactCoverBy4Input) : Prop :=
  acceptedFamily I.sets

/-- The empty family has an empty exact cover. -/
theorem accepted_empty_family : acceptedFamily ([] : List Set4) := by
  refine ⟨[], ?_, ?_, ?_⟩
  · intro s hs
    simp at hs
  · intro s hs
    simp at hs
  · intro x hx
    simp [Universe] at hx

end ExactCoverBy4Input

end ExactCoverBy4

namespace Presentation
namespace ExactCoverBy4

open ComplexityReduction.ExactCoverBy4

/-- The exact nested-product payload of one length-four set. -/
abbrev set4PayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat))

/-- Read one length-four set as its exact nested-product payload. -/
def set4Payload (s : Set4) : set4PayloadEncodedType.Carrier :=
  (s.first, (s.second, (s.third, s.fourth)))

/-- Faithful finite-alphabet encoding for one length-four set. -/
def set4EncodedType : EncodedType where
  Carrier := Set4
  Symbol := set4PayloadEncodedType.Symbol
  finite_symbol := set4PayloadEncodedType.finite_symbol
  encode := fun s => set4PayloadEncodedType.encode (set4Payload s)

private theorem set4Payload_injective : Function.Injective set4Payload := by
  intro left right equality
  cases left with
  | mk leftFirst leftSecond leftThird leftFourth =>
      cases right with
      | mk rightFirst rightSecond rightThird rightFourth =>
          simp only [set4Payload] at equality
          cases equality
          rfl

/-- The exact length-four-set encoding is faithful. -/
theorem set4EncodedType_encode_injective :
    Function.Injective set4EncodedType.encode := by
  intro left right equality
  apply set4Payload_injective
  exact
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        (EncodedType.prod_encode_injective
          EncodedType.nat_encode_injective
          EncodedType.nat_encode_injective))) equality

/-- Exact list encoding for ordered families of length-four sets. -/
abbrev familyEncodedType : EncodedType :=
  EncodedType.list set4EncodedType

/-- Faithfulness of the complete ordered family encoding. -/
theorem familyEncodedType_encode_injective :
    Function.Injective familyEncodedType.encode :=
  EncodedType.list_encode_injective set4EncodedType_encode_injective

/-- Full representation identity of one length-four set. -/
def set4Shape : CodecShape :=
  .prod .unaryNat (.prod .unaryNat (.prod .unaryNat .unaryNat))

/-- Full representation identity of an ordered family. -/
def structuredShape : CodecShape :=
  .list set4Shape

/-- Canonical lawful exact exact-cover-by-4 representation. -/
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
    structuredPresentation.Carrier = List Set4 :=
  rfl

/-- The exact exact-cover-by-4 semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ExactCoverBy4Input.acceptedFamily

/-- Canonical exact public exact-cover-by-4 endpoint. -/
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
    structuredProblem.accepts input ↔ ExactCoverBy4Input.acceptedFamily input :=
  Iff.rfl

assert_standard_axioms
  set4EncodedType_encode_injective,
  familyEncodedType_encode_injective,
  structuredProblem_accepts

end ExactCoverBy4
end Presentation
end ComplexityReduction
