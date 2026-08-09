/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Canonical V2 structural codec-shape identities.

This module owns only the finite syntax used to name standard representations and the typed value
that carries such a name.  It intentionally has no carrier, encoder, decoder, presentation,
program, certificate, registry, or route interface.  Consequently, a carrier type alone cannot
select or identify a representation: later layers must carry one of these identities explicitly.
-/

namespace ComplexityReduction
namespace Encoding

/--
The closed structural language for standard representation layouts.

Unary and binary natural-number layouts are distinct constructors.  Product, sum, and list
identities retain their complete recursive layout rather than collapsing to the represented Lean
carrier type.
-/
inductive CodecShape where
  | unit
  | bool
  | unaryNat
  | binaryNat
  | prod (left right : CodecShape)
  | sum (left right : CodecShape)
  | list (element : CodecShape)
  deriving DecidableEq, Repr

namespace CodecShape

/--
The atomic leaves which a standard structural layout may contain.

This separate finite type is deliberately smaller than `CodecShape`: product,
sum, and list are layout constructors, while these four atoms are the
representation choices whose multiplicity must survive every audited layout
change.  In particular, unary and binary natural-number leaves remain
distinct even though they denote the same Lean carrier.
-/
inductive AtomicShape where
  | unit
  | bool
  | unaryNat
  | binaryNat
  deriving DecidableEq, Repr

/-- The Lean carrier denoted by a standard structural codec layout. -/
def Denote : CodecShape → Type
  | unit => Unit
  | bool => Bool
  | unaryNat => Nat
  | binaryNat => Nat
  | prod left right => left.Denote × right.Denote
  | sum left right => left.Denote ⊕ right.Denote
  | list element => List element.Denote

/--
Count occurrences of one atomic representation choice in a structural shape.

Only product, sum, and list recurse.  This finite structural invariant is
independent of the Lean carrier denoted by the shape, so it can distinguish
same-carrier codecs such as unary and binary natural numbers.
-/
def atomicOccurrences (atom : AtomicShape) : CodecShape → Nat
  | unit => if atom = .unit then 1 else 0
  | bool => if atom = .bool then 1 else 0
  | unaryNat => if atom = .unaryNat then 1 else 0
  | binaryNat => if atom = .binaryNat then 1 else 0
  | prod left right => atomicOccurrences atom left + atomicOccurrences atom right
  | sum left right => atomicOccurrences atom left + atomicOccurrences atom right
  | list element => atomicOccurrences atom element

@[simp]
theorem atomicOccurrences_prod (atom : AtomicShape) (left right : CodecShape) :
    atomicOccurrences atom (prod left right) =
      atomicOccurrences atom left + atomicOccurrences atom right :=
  rfl

@[simp]
theorem atomicOccurrences_sum (atom : AtomicShape) (left right : CodecShape) :
    atomicOccurrences atom (sum left right) =
      atomicOccurrences atom left + atomicOccurrences atom right :=
  rfl

@[simp]
theorem atomicOccurrences_list (atom : AtomicShape) (element : CodecShape) :
    atomicOccurrences atom (list element) = atomicOccurrences atom element :=
  rfl

@[simp]
theorem unaryNat_binaryNat_atomicOccurrences :
    atomicOccurrences .binaryNat unaryNat = 0 ∧
      atomicOccurrences .binaryNat binaryNat = 1 := by
  decide

/-- Unary and binary natural layouts deliberately denote the same Lean carrier. -/
theorem unaryNat_denote_eq_binaryNat_denote : unaryNat.Denote = binaryNat.Denote :=
  rfl

/-- A typed, structural representation identity; it has no carrier or string field. -/
structure Identity where
  shape : CodecShape
  deriving DecidableEq, Repr

/-- The unique V2 identity associated with one structural codec shape. -/
def identity (shape : CodecShape) : Identity :=
  ⟨shape⟩

/-- Recover the exact structural shape carried by a representation identity. -/
def Identity.toShape (identity : Identity) : CodecShape :=
  identity.shape

/-- The carrier denoted by the exact structural identity. -/
abbrev Identity.Denote (identity : Identity) : Type :=
  identity.toShape.Denote

@[simp]
theorem Identity.toShape_identity (shape : CodecShape) :
    (shape.identity).toShape = shape :=
  rfl

/-- Structural identities are injective: equal identities have equal complete shapes. -/
theorem identity_injective : Function.Injective identity := by
  intro left right equality
  simpa using congrArg Identity.toShape equality

/-- Equality of canonical representation identities is exactly equality of their shapes. -/
theorem identity_eq_iff (left right : CodecShape) :
    left.identity = right.identity ↔ left = right := by
  constructor
  · intro equality
    exact identity_injective equality
  · intro equality
    cases equality
    rfl

/-- Recovering the shape from an identity is injective, even when the shapes share a carrier. -/
theorem identity_toShape_injective : Function.Injective Identity.toShape := by
  intro ⟨left⟩ ⟨right⟩ equality
  cases equality
  rfl

/-- Two representation identities agree exactly when their complete shapes agree. -/
theorem identity_toShape_eq_iff (left right : Identity) :
    left.toShape = right.toShape ↔ left = right := by
  constructor
  · intro equality
    exact identity_toShape_injective equality
  · intro equality
    cases equality
    rfl

/-- Unequal shapes cannot be made equal by forgetting their carriers. -/
theorem identity_ne_of_shape_ne {left right : CodecShape} (h : left ≠ right) :
    left.identity ≠ right.identity :=
  fun equality => h (identity_injective equality)

/--
Different structural atomic profiles rule out equality of codec shapes.

This is deliberately only a one-way discriminator: layout order is retained
by `CodecShape` itself, while an atomic profile gives a small, computable
negative test that does not inspect a denoted Lean carrier.
-/
theorem shape_ne_of_atomicOccurrences_ne (atom : AtomicShape)
    {left right : CodecShape}
    (different : atomicOccurrences atom left ≠ atomicOccurrences atom right) :
    left ≠ right := by
  intro equality
  exact different (congrArg (atomicOccurrences atom) equality)

/--
Different structural atomic profiles rule out equality of representation
identities, even when their denoted Lean carriers happen to agree.
-/
theorem identity_ne_of_atomicOccurrences_ne (atom : AtomicShape)
    {left right : CodecShape}
    (different : atomicOccurrences atom left ≠ atomicOccurrences atom right) :
    left.identity ≠ right.identity :=
  identity_ne_of_shape_ne (shape_ne_of_atomicOccurrences_ne atom different)

/-- Product identities retain both ordered component shapes. -/
theorem prod_identity_eq_iff (left₁ right₁ left₂ right₂ : CodecShape) :
    (prod left₁ right₁).identity = (prod left₂ right₂).identity ↔
      left₁ = left₂ ∧ right₁ = right₂ := by
  rw [identity_eq_iff]
  constructor
  · exact CodecShape.prod.inj
  · rintro ⟨leftEquality, rightEquality⟩
    cases leftEquality
    cases rightEquality
    rfl

/-- Sum identities retain both ordered component shapes. -/
theorem sum_identity_eq_iff (left₁ right₁ left₂ right₂ : CodecShape) :
    (sum left₁ right₁).identity = (sum left₂ right₂).identity ↔
      left₁ = left₂ ∧ right₁ = right₂ := by
  rw [identity_eq_iff]
  constructor
  · exact CodecShape.sum.inj
  · rintro ⟨leftEquality, rightEquality⟩
    cases leftEquality
    cases rightEquality
    rfl

/-- List identities retain the exact element layout. -/
theorem list_identity_eq_iff (element₁ element₂ : CodecShape) :
    (list element₁).identity = (list element₂).identity ↔ element₁ = element₂ := by
  rw [identity_eq_iff]
  constructor
  · exact CodecShape.list.inj
  · intro equality
    cases equality
    rfl

/-- Unary and binary natural-number representations never share an identity. -/
theorem unaryNat_identity_ne_binaryNat_identity :
    unaryNat.identity ≠ binaryNat.identity := by
  apply identity_ne_of_atomicOccurrences_ne .binaryNat
  decide

/-- Equal carriers never collapse the distinct unary and binary representation identities. -/
theorem unaryNat_binaryNat_same_denote_different_identity :
    unaryNat.Denote = binaryNat.Denote ∧ unaryNat.identity ≠ binaryNat.identity :=
  ⟨unaryNat_denote_eq_binaryNat_denote, unaryNat_identity_ne_binaryNat_identity⟩

/-- A list representation is distinct from its element representation. -/
theorem list_identity_ne_element_identity (shape : CodecShape) :
    (list shape).identity ≠ shape.identity := by
  intro equality
  have shapeEquality : list shape = shape := identity_injective equality
  cases shape <;> cases shapeEquality

/-- Reordering a product layout changes its representation identity when its factors differ. -/
theorem prod_identity_ne_swapped (left right : CodecShape) (h : left ≠ right) :
    (prod left right).identity ≠ (prod right left).identity := by
  intro equality
  have shapes := identity_injective equality
  cases shapes
  exact h rfl

end CodecShape
end Encoding
end ComplexityReduction
