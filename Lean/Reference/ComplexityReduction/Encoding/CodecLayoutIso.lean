/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Logic.Equiv.Defs
import ComplexityReduction.Encoding.CodecShape

/-!
Typed structural layout isomorphisms for canonical codec-shape identities.

`CodecLayoutIso` is intentionally a small syntax of audited layout changes. Its endpoints are
`CodecShape.Identity` values, so an arbitrary carrier equality or `Equiv` cannot be used as a
representation change. This leaf has no carrier function, encoder, decoder, presentation, program,
certificate, registry, or route interface.
-/

namespace ComplexityReduction
namespace Encoding

open CodecShape

/--
Structural changes between two explicitly identified codec layouts.

The constructors are closed under inversion and composition and may lift a structural change below
product, sum, or list structure. Reassociation and swapping are the only primitive changes; this
is not an admission rule for arbitrary Lean equivalences.
-/
inductive CodecLayoutIso : CodecShape.Identity → CodecShape.Identity → Type where
  | identity (shape : CodecShape.Identity) : CodecLayoutIso shape shape
  | inverse {source target : CodecShape.Identity} :
      CodecLayoutIso source target → CodecLayoutIso target source
  | compose {source middle target : CodecShape.Identity} :
      CodecLayoutIso source middle → CodecLayoutIso middle target → CodecLayoutIso source target
  | prodCongr {leftSource leftTarget rightSource rightTarget : CodecShape.Identity} :
      CodecLayoutIso leftSource leftTarget → CodecLayoutIso rightSource rightTarget →
        CodecLayoutIso
          (CodecShape.prod leftSource.toShape rightSource.toShape).identity
          (CodecShape.prod leftTarget.toShape rightTarget.toShape).identity
  | sumCongr {leftSource leftTarget rightSource rightTarget : CodecShape.Identity} :
      CodecLayoutIso leftSource leftTarget → CodecLayoutIso rightSource rightTarget →
        CodecLayoutIso
          (CodecShape.sum leftSource.toShape rightSource.toShape).identity
          (CodecShape.sum leftTarget.toShape rightTarget.toShape).identity
  | listCongr {source target : CodecShape.Identity} :
      CodecLayoutIso source target →
        CodecLayoutIso (CodecShape.list source.toShape).identity
          (CodecShape.list target.toShape).identity
  | prodAssoc (first second third : CodecShape) :
      CodecLayoutIso
        (CodecShape.prod (CodecShape.prod first second) third).identity
        (CodecShape.prod first (CodecShape.prod second third)).identity
  | prodSwap (left right : CodecShape) :
      CodecLayoutIso (CodecShape.prod left right).identity (CodecShape.prod right left).identity
  | sumAssoc (first second third : CodecShape) :
      CodecLayoutIso
        (CodecShape.sum (CodecShape.sum first second) third).identity
        (CodecShape.sum first (CodecShape.sum second third)).identity
  | sumSwap (left right : CodecShape) :
      CodecLayoutIso (CodecShape.sum left right).identity (CodecShape.sum right left).identity

namespace CodecLayoutIso

/--
The complete structural identities at the two ends of a layout witness.

This is an observational endpoint index only: it contains no executable map and no constructor
for `CodecLayoutIso`.  In particular, an equality of carriers or an arbitrary `Equiv` cannot be
turned into this pair *and* a structural layout witness; the latter remains indexed by these exact
identities.
-/
structure EndpointIdentityPair where
  source : CodecShape.Identity
  target : CodecShape.Identity
  deriving DecidableEq, Repr

/-- Recover the exact identity pair already fixed by a structural layout witness. -/
def endpointIdentities {source target : CodecShape.Identity}
    (_layout : CodecLayoutIso source target) : EndpointIdentityPair :=
  ⟨source, target⟩

/-- The source endpoint recovered from a layout is precisely its source identity index. -/
@[simp]
theorem endpointIdentities_source {source target : CodecShape.Identity}
    (layout : CodecLayoutIso source target) :
    layout.endpointIdentities.source = source :=
  rfl

/-- The target endpoint recovered from a layout is precisely its target identity index. -/
@[simp]
theorem endpointIdentities_target {source target : CodecShape.Identity}
    (layout : CodecLayoutIso source target) :
    layout.endpointIdentities.target = target :=
  rfl

/--
Endpoint pairs agree exactly when both complete representation-identity indices agree.

No comparison of the denoted Lean carriers appears in this statement, so equal carriers cannot
silently identify layouts with distinct codec shapes.
-/
theorem endpointIdentities_eq_iff
    {source target source' target' : CodecShape.Identity}
    (layout : CodecLayoutIso source target) (layout' : CodecLayoutIso source' target') :
    layout.endpointIdentities = layout'.endpointIdentities ↔
      source = source' ∧ target = target' := by
  constructor
  · intro equality
    constructor
    · simpa only [endpointIdentities_source] using
        congrArg EndpointIdentityPair.source equality
    · simpa only [endpointIdentities_target] using
        congrArg EndpointIdentityPair.target equality
  · rintro ⟨sourceEquality, targetEquality⟩
    cases sourceEquality
    cases targetEquality
    rfl

/--
Structural composition retains the outer complete identity endpoints, while the matching middle
identity is enforced by the type of `trans`.
-/
@[simp]
theorem endpointIdentities_trans {source middle target : CodecShape.Identity}
    (first : CodecLayoutIso source middle) (second : CodecLayoutIso middle target) :
    (CodecLayoutIso.compose first second).endpointIdentities =
      ⟨first.endpointIdentities.source, second.endpointIdentities.target⟩ :=
  rfl

/--
Every audited layout change preserves the multiplicity of each atomic codec
choice.  The proof follows the closed layout syntax: congruence recurses into
the corresponding sublayouts, while reassociation and swapping only rearrange
addition.  Consequently an arbitrary carrier equivalence cannot be used to
change a unary-natural leaf into a binary-natural leaf.
-/
theorem atomicOccurrences_preserved (atom : CodecShape.AtomicShape)
    {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    CodecShape.atomicOccurrences atom source.toShape =
      CodecShape.atomicOccurrences atom target.toShape := by
  induction layout with
  | identity shape =>
      rfl
  | inverse layout inductionHypothesis =>
      exact inductionHypothesis.symm
  | compose first second firstInvariant secondInvariant =>
      exact firstInvariant.trans secondInvariant
  | prodCongr left right leftInvariant rightInvariant =>
      exact congrArg₂ (· + ·) leftInvariant rightInvariant
  | sumCongr left right leftInvariant rightInvariant =>
      exact congrArg₂ (· + ·) leftInvariant rightInvariant
  | listCongr layout invariant =>
      exact invariant
  | prodAssoc first second third =>
      exact Nat.add_assoc _ _ _
  | prodSwap left right =>
      exact Nat.add_comm _ _
  | sumAssoc first second third =>
      exact Nat.add_assoc _ _ _
  | sumSwap left right =>
      exact Nat.add_comm _ _

/--
Different atomic-layout counts rule out an audited structural layout witness.

This is the admission boundary used by the same-carrier regression below:
the theorem speaks about a `CodecLayoutIso`, rather than the equality or
equivalence of its denoted Lean carriers.
-/
theorem no_layout_of_atomicOccurrences_ne (atom : CodecShape.AtomicShape)
    {source target : CodecShape.Identity}
    (different : CodecShape.atomicOccurrences atom source.toShape ≠
      CodecShape.atomicOccurrences atom target.toShape) :
    ¬ Nonempty (CodecLayoutIso source target) := by
  rintro ⟨layout⟩
  exact different (atomicOccurrences_preserved atom layout)

/--
There is no structural-layout witness from the unary natural codec to the
base-two natural codec, even though the two codecs denote the same `Nat`
carrier.
-/
theorem no_unaryNat_to_binaryNat_layout :
    ¬ Nonempty (CodecLayoutIso CodecShape.unaryNat.identity CodecShape.binaryNat.identity) := by
  apply no_layout_of_atomicOccurrences_ne .binaryNat
  simpa only [CodecShape.Identity.toShape_identity] using Nat.zero_ne_one

/--
A same-carrier codec change cannot be smuggled through an intermediate
structural layout.  The two witnesses would compose to the forbidden direct
unary-to-binary layout, so this is a negative composition regression at the
typed layout boundary rather than a comparison of ordinary `Nat` functions.
-/
theorem no_unaryNat_to_binaryNat_composition (middle : CodecShape.Identity) :
    ¬ (Nonempty (CodecLayoutIso CodecShape.unaryNat.identity middle) ∧
      Nonempty (CodecLayoutIso middle CodecShape.binaryNat.identity)) := by
  rintro ⟨⟨first⟩, ⟨second⟩⟩
  exact no_unaryNat_to_binaryNat_layout ⟨.compose first second⟩

/-- The carrier-level identity equivalence exists for the two `Nat` codecs. -/
def unaryNatBinaryNatCarrierEquiv :
    Equiv CodecShape.unaryNat.identity.Denote CodecShape.binaryNat.identity.Denote :=
  Equiv.refl Nat

/--
The unary and binary `Nat` carriers have the same Lean type but remain different layout endpoints.

This regression records at the layout boundary that carrier equality alone cannot select a codec
identity.
-/
theorem unaryNat_binaryNat_endpointIdentities_ne :
    (CodecLayoutIso.identity CodecShape.unaryNat.identity).endpointIdentities ≠
      (CodecLayoutIso.identity CodecShape.binaryNat.identity).endpointIdentities := by
  intro equality
  exact CodecShape.unaryNat_identity_ne_binaryNat_identity
    ((endpointIdentities_eq_iff _ _).mp equality).1

/-- The identity layout transformation at one explicitly chosen representation identity. -/
def refl (shape : CodecShape.Identity) : CodecLayoutIso shape shape :=
  .identity shape

/-- Reverse a structural layout transformation without changing either endpoint identity. -/
def symm {source target : CodecShape.Identity} :
    CodecLayoutIso source target → CodecLayoutIso target source :=
  .inverse

/-- Compose only endpoint-compatible structural layout transformations. -/
def trans {source middle target : CodecShape.Identity} :
    CodecLayoutIso source middle → CodecLayoutIso middle target → CodecLayoutIso source target :=
  .compose

/--
Reversing a layout swaps its complete representation-identity endpoints.

This tracks identities rather than denoted carriers: an inverse executable
equivalence therefore cannot silently turn a layout at one codec into a
layout at a different same-carrier codec.
-/
@[simp]
theorem endpointIdentities_symm {source target : CodecShape.Identity}
    (layout : CodecLayoutIso source target) :
    layout.symm.endpointIdentities =
      ⟨layout.endpointIdentities.target, layout.endpointIdentities.source⟩ :=
  rfl

/--
An audited layout followed by its audited inverse returns to the exact source
representation identity pair.  In particular, composition cannot reuse a
same-carrier intermediate layout to manufacture a different codec endpoint.
-/
@[simp]
theorem endpointIdentities_trans_symm {source target : CodecShape.Identity}
    (layout : CodecLayoutIso source target) :
    (layout.trans layout.symm).endpointIdentities = (refl source).endpointIdentities :=
  rfl

/-- Lift two structural changes through a product layout. -/
def prod {leftSource leftTarget rightSource rightTarget : CodecShape.Identity}
    (left : CodecLayoutIso leftSource leftTarget) (right : CodecLayoutIso rightSource rightTarget) :
    CodecLayoutIso
      (CodecShape.prod leftSource.toShape rightSource.toShape).identity
      (CodecShape.prod leftTarget.toShape rightTarget.toShape).identity :=
  .prodCongr left right

/-- Lift two structural changes through a sum layout. -/
def sum {leftSource leftTarget rightSource rightTarget : CodecShape.Identity}
    (left : CodecLayoutIso leftSource leftTarget) (right : CodecLayoutIso rightSource rightTarget) :
    CodecLayoutIso
      (CodecShape.sum leftSource.toShape rightSource.toShape).identity
      (CodecShape.sum leftTarget.toShape rightTarget.toShape).identity :=
  .sumCongr left right

/-- Lift a structural change through a list layout. -/
def list {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    CodecLayoutIso (CodecShape.list source.toShape).identity
      (CodecShape.list target.toShape).identity :=
  .listCongr layout

/-- A product reassociation is a structural layout witness, not a carrier equivalence. -/
def prodAssocLayout (first second third : CodecShape) :
    CodecLayoutIso
      (CodecShape.prod (CodecShape.prod first second) third).identity
      (CodecShape.prod first (CodecShape.prod second third)).identity :=
  .prodAssoc first second third

/-- A product swap is a structural layout witness with explicitly chosen endpoint layouts. -/
def prodSwapLayout (left right : CodecShape) :
    CodecLayoutIso (CodecShape.prod left right).identity (CodecShape.prod right left).identity :=
  .prodSwap left right

/-- A sum reassociation is a structural layout witness, not a carrier equivalence. -/
def sumAssocLayout (first second third : CodecShape) :
    CodecLayoutIso
      (CodecShape.sum (CodecShape.sum first second) third).identity
      (CodecShape.sum first (CodecShape.sum second third)).identity :=
  .sumAssoc first second third

/-- A sum swap is a structural layout witness with explicitly chosen endpoint layouts. -/
def sumSwapLayout (left right : CodecShape) :
    CodecLayoutIso (CodecShape.sum left right).identity (CodecShape.sum right left).identity :=
  .sumSwap left right

/--
Interpret an audited structural layout witness as its executable carrier equivalence.

The direction is intentionally one-way: this function exposes the equivalence implemented by a
`CodecLayoutIso`, but no constructor accepts an arbitrary `Equiv` as a layout witness.
-/
def toEquiv {source target : CodecShape.Identity} :
    CodecLayoutIso source target → Equiv source.Denote target.Denote
  | .identity _ => Equiv.refl _
  | .inverse layout => layout.toEquiv.symm
  | .compose first second => first.toEquiv.trans second.toEquiv
  | .prodCongr left right =>
      { toFun := fun value => (left.toEquiv value.1, right.toEquiv value.2)
        invFun := fun value => (left.toEquiv.symm value.1, right.toEquiv.symm value.2)
        left_inv := by
          intro value
          cases value
          simp
        right_inv := by
          intro value
          cases value
          simp }
  | .sumCongr left right =>
      { toFun := fun value =>
          match value with
          | .inl value => .inl (left.toEquiv value)
          | .inr value => .inr (right.toEquiv value)
        invFun := fun value =>
          match value with
          | .inl value => .inl (left.toEquiv.symm value)
          | .inr value => .inr (right.toEquiv.symm value)
        left_inv := by
          intro value
          cases value <;> simp
        right_inv := by
          intro value
          cases value <;> simp }
  | .listCongr layout =>
      { toFun := List.map layout.toEquiv
        invFun := List.map layout.toEquiv.symm
        left_inv := by
          intro values
          induction values with
          | nil => rfl
          | cons value values ih => simp [ih]
        right_inv := by
          intro values
          induction values with
          | nil => rfl
          | cons value values ih => simp [ih] }
  | .prodAssoc _ _ _ =>
      { toFun := fun value => (value.1.1, (value.1.2, value.2))
        invFun := fun value => ((value.1, value.2.1), value.2.2)
        left_inv := by
          intro value
          cases value
          rfl
        right_inv := by
          intro value
          cases value
          rfl }
  | .prodSwap _ _ =>
      { toFun := fun value => (value.2, value.1)
        invFun := fun value => (value.2, value.1)
        left_inv := by
          intro value
          cases value
          rfl
        right_inv := by
          intro value
          cases value
          rfl }
  | .sumAssoc _ _ _ =>
      { toFun := fun value =>
          match value with
          | .inl (.inl first) => .inl first
          | .inl (.inr second) => .inr (.inl second)
          | .inr third => .inr (.inr third)
        invFun := fun value =>
          match value with
          | .inl first => .inl (.inl first)
          | .inr (.inl second) => .inl (.inr second)
          | .inr (.inr third) => .inr third
        left_inv := by
          intro value
          cases value with
          | inl value =>
              cases value <;> rfl
          | inr value =>
              rfl
        right_inv := by
          intro value
          cases value with
          | inl value =>
              rfl
          | inr value =>
              cases value <;> rfl }
  | .sumSwap _ _ =>
      { toFun := fun value =>
          match value with
          | .inl left => .inr left
          | .inr right => .inl right
        invFun := fun value =>
          match value with
          | .inl right => .inr right
          | .inr left => .inl left
        left_inv := by
          intro value
          cases value <;> rfl
        right_inv := by
          intro value
          cases value <;> rfl }

/--
The bare carrier equivalence is not a structural-layout witness.

`toEquiv` exposes executable semantics only after a closed witness has been
constructed; this theorem records the converse failure at a concrete
same-carrier pair, rather than trusting a convention about use of `Equiv`.
-/
theorem unaryNatBinaryNatCarrierEquiv_has_no_structuralLayout :
    ¬ ∃ layout : CodecLayoutIso CodecShape.unaryNat.identity CodecShape.binaryNat.identity,
      layout.toEquiv = unaryNatBinaryNatCarrierEquiv := by
  rintro ⟨layout, _⟩
  exact no_unaryNat_to_binaryNat_layout ⟨layout⟩

/-- Execute an audited structural layout transformation in its forward direction. -/
def apply {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    source.Denote → target.Denote :=
  layout.toEquiv

/-- Execute the inverse of an audited structural layout transformation. -/
def applyInverse {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    target.Denote → source.Denote :=
  layout.toEquiv.symm

/-- Forward execution of a layout is injective because its inverse is audited in the same witness. -/
theorem apply_injective {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    Function.Injective layout.apply :=
  layout.toEquiv.injective

/-- Forward execution of a layout is surjective because its inverse is audited in the same witness. -/
theorem apply_surjective {source target : CodecShape.Identity} (layout : CodecLayoutIso source target) :
    Function.Surjective layout.apply :=
  layout.toEquiv.surjective

/-- Inverse execution cancels a forward structural layout execution. -/
@[simp]
theorem applyInverse_apply {source target : CodecShape.Identity} (layout : CodecLayoutIso source target)
    (value : source.Denote) :
    layout.applyInverse (layout.apply value) = value :=
  layout.toEquiv.symm_apply_apply value

/-- Forward execution cancels inverse structural layout execution. -/
@[simp]
theorem apply_applyInverse {source target : CodecShape.Identity} (layout : CodecLayoutIso source target)
    (value : target.Denote) :
    layout.apply (layout.applyInverse value) = value :=
  layout.toEquiv.apply_symm_apply value

/-- The identity layout implements the identity equivalence. -/
@[simp]
theorem toEquiv_refl (shape : CodecShape.Identity) :
    (refl shape).toEquiv = Equiv.refl shape.Denote :=
  rfl

/-- Inverting a layout inverts only its already-audited structural equivalence. -/
@[simp]
theorem toEquiv_symm {source target : CodecShape.Identity}
    (layout : CodecLayoutIso source target) :
    layout.symm.toEquiv = layout.toEquiv.symm :=
  rfl

/-- Composition projects to composition of exactly the already-audited layout equivalences. -/
@[simp]
theorem toEquiv_trans {source middle target : CodecShape.Identity}
    (first : CodecLayoutIso source middle) (second : CodecLayoutIso middle target) :
    (first.trans second).toEquiv = first.toEquiv.trans second.toEquiv :=
  rfl

/-- The identity layout executes as the identity function. -/
@[simp]
theorem apply_refl (shape : CodecShape.Identity) (value : shape.Denote) :
    (refl shape).apply value = value :=
  rfl

/-- A composed layout executes in the same order as its two audited components. -/
@[simp]
theorem apply_trans {source middle target : CodecShape.Identity}
    (first : CodecLayoutIso source middle) (second : CodecLayoutIso middle target)
    (value : source.Denote) :
    (first.trans second).apply value = second.apply (first.apply value) :=
  rfl

/-- Inverting a layout swaps its forward and inverse executable semantics. -/
@[simp]
theorem apply_symm {source target : CodecShape.Identity} (layout : CodecLayoutIso source target)
    (value : target.Denote) :
    layout.symm.apply value = layout.applyInverse value :=
  rfl

/-- The inverse execution of an inverted layout is its original forward execution. -/
@[simp]
theorem applyInverse_symm {source target : CodecShape.Identity} (layout : CodecLayoutIso source target)
    (value : source.Denote) :
    layout.symm.applyInverse value = layout.apply value :=
  rfl

end CodecLayoutIso
end Encoding
end ComplexityReduction
