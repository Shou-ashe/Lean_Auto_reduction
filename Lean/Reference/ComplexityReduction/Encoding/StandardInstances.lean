/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedType
import ComplexityReduction.Encoding.CodecShape
import ComplexityReduction.Encoding.LawfulEncodedType

/-!
Standard structural lawful representations.

These definitions reuse the existing `ComplexityReduction.EncodedType`
implementations and their established injectivity theorems.  They introduce no
alternative encoder and do not derive a lawful representation from a bare
equivalence or a bare injectivity proof.
-/

namespace ComplexityReduction
namespace Encoding
namespace StandardInstances

/--
The only canonical raw presentation: `Unit` has a subsingleton carrier, so
the legacy empty-word raw encoder is faithful without admitting raw encodings
for general carriers.
-/
def unit : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.raw Unit
  representation := CodecShape.unit.identity
  faithful := FaithfulEncoding.rawOfSubsingleton Unit

private def sumLeftSymbol {α β : Type} : Bool ⊕ (α ⊕ β) → Option α
  | .inr (.inl value) => some value
  | _ => none

private def sumRightSymbol {α β : Type} : Bool ⊕ (α ⊕ β) → Option β
  | .inr (.inr value) => some value
  | _ => none

private theorem sum_left_filter_encode (left right : ComplexityReduction.EncodedType)
    (value : left.Carrier) :
    List.filterMap sumLeftSymbol
        ((ComplexityReduction.EncodedType.sum left right).encode (.inl value)) = left.encode value := by
  simp [ComplexityReduction.EncodedType.sum, sumLeftSymbol]

private theorem sum_right_filter_encode (left right : ComplexityReduction.EncodedType)
    (value : right.Carrier) :
    List.filterMap sumRightSymbol
        ((ComplexityReduction.EncodedType.sum left right).encode (.inr value)) = right.encode value := by
  simp [ComplexityReduction.EncodedType.sum, sumRightSymbol]

/-- The legacy tagged sum encoder is injective when both component encoders are injective. -/
theorem sum_encode_injective {left right : ComplexityReduction.EncodedType}
    (leftInjective : Function.Injective left.encode) (rightInjective : Function.Injective right.encode) :
    Function.Injective (ComplexityReduction.EncodedType.sum left right).encode := by
  intro first second equality
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          have filtered := congrArg (List.filterMap (@sumLeftSymbol left.Symbol right.Symbol)) equality
          exact congrArg Sum.inl (leftInjective (by
            simpa [sum_left_filter_encode] using filtered))
      | inr second =>
          have heads := congrArg List.head? equality
          simp [ComplexityReduction.EncodedType.sum] at heads
  | inr first =>
      cases second with
      | inl second =>
          have heads := congrArg List.head? equality
          simp [ComplexityReduction.EncodedType.sum] at heads
      | inr second =>
          have filtered := congrArg (List.filterMap (@sumRightSymbol left.Symbol right.Symbol)) equality
          exact congrArg Sum.inr (rightInjective (by
            simpa [sum_right_filter_encode] using filtered))

/-- The standard Boolean encoding with its Boolean structural identity. -/
def bool : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.bool
  representation := CodecShape.bool.identity
  faithful := ⟨ComplexityReduction.EncodedType.bool_encode_injective⟩

/-- The existing unary natural-number encoding with its unary structural identity. -/
def unaryNat : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.nat
  representation := CodecShape.unaryNat.identity
  faithful := ⟨ComplexityReduction.EncodedType.nat_encode_injective⟩

/-- The existing base-two natural-number encoding with its distinct binary identity. -/
def binaryNat : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.binaryNat
  representation := CodecShape.binaryNat.identity
  faithful := ⟨ComplexityReduction.EncodedType.binaryNat_encode_injective⟩

/--
Build a product representation only from two already-lawful component
representations.  The result keeps the complete ordered product layout.
-/
def prod (left right : LawfulEncodedType) : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.prod left.encodedType right.encodedType
  representation :=
    (CodecShape.prod left.representation.toShape right.representation.toShape).identity
  faithful := ⟨ComplexityReduction.EncodedType.prod_encode_injective
    left.faithful.encode_injective right.faithful.encode_injective⟩

/--
Build a sum representation only from two already-lawful component representations.  The tag and
the ordered sum layout are fixed by the reused `EncodedType.sum` encoder.
-/
def sum (left right : LawfulEncodedType) : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.sum left.encodedType right.encodedType
  representation :=
    (CodecShape.sum left.representation.toShape right.representation.toShape).identity
  faithful := ⟨sum_encode_injective left.faithful.encode_injective right.faithful.encode_injective⟩

/--
Build a list representation only from an already-lawful element
representation, retaining the complete list layout identity.
-/
def list (element : LawfulEncodedType) : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.list element.encodedType
  representation := (CodecShape.list element.representation.toShape).identity
  faithful := ⟨ComplexityReduction.EncodedType.list_encode_injective
    element.faithful.encode_injective⟩

/-- The raw-unit presentation has the unique empty-word input size. -/
@[simp]
theorem inputSize_unit (input : unit.Carrier) : unit.inputSize input = 0 := by
  simp [LawfulEncodedType.inputSize, unit, ComplexityReduction.EncodedType.inputSize,
    ComplexityReduction.EncodedType.raw]

/-- The standard Boolean presentation measures every input by its one-symbol encoding. -/
@[simp]
theorem inputSize_bool (input : bool.Carrier) : bool.inputSize input = 1 := by
  exact ComplexityReduction.EncodedType.inputSize_bool input

/-- Unary natural input size is the length inherited from the existing unary encoder. -/
@[simp]
theorem inputSize_unaryNat (input : Nat) :
    unaryNat.inputSize input = input + 1 := by
  exact ComplexityReduction.EncodedType.inputSize_nat input

/-- Binary natural input size is exactly the length of the reused base-two digit word. -/
@[simp]
theorem inputSize_binaryNat (input : binaryNat.Carrier) :
    binaryNat.inputSize input = (Nat.digits 2 input).length := by
  simp [LawfulEncodedType.inputSize, binaryNat, ComplexityReduction.EncodedType.inputSize,
    ComplexityReduction.EncodedType.binaryNat]

/-- Product input size keeps both component encodings and their single delimiter. -/
@[simp]
theorem inputSize_prod (left right : LawfulEncodedType)
    (input : (prod left right).Carrier) :
    (prod left right).inputSize input =
      left.inputSize input.1 + 1 + right.inputSize input.2 := by
  exact ComplexityReduction.EncodedType.inputSize_prod left.encodedType right.encodedType input

/-- A left sum input has its tag followed by precisely the left component word. -/
@[simp]
theorem inputSize_sum_inl (left right : LawfulEncodedType) (input : left.Carrier) :
    (sum left right).inputSize (.inl input) = left.inputSize input + 1 := by
  simp [LawfulEncodedType.inputSize, sum, ComplexityReduction.EncodedType.inputSize,
    ComplexityReduction.EncodedType.sum, Nat.add_comm]

/-- A right sum input has its tag followed by precisely the right component word. -/
@[simp]
theorem inputSize_sum_inr (left right : LawfulEncodedType) (input : right.Carrier) :
    (sum left right).inputSize (.inr input) = right.inputSize input + 1 := by
  simp [LawfulEncodedType.inputSize, sum, ComplexityReduction.EncodedType.inputSize,
    ComplexityReduction.EncodedType.sum, Nat.add_comm]

/-- The empty list representation has no encoded symbols. -/
@[simp]
theorem inputSize_list_nil (element : LawfulEncodedType) :
    (list element).inputSize [] = 0 := by
  exact ComplexityReduction.EncodedType.inputSize_list_nil element.encodedType

/-- List input size keeps each element word and exactly one trailing delimiter per element. -/
@[simp]
theorem inputSize_list_cons (element : LawfulEncodedType) (input : element.Carrier)
    (inputs : List element.Carrier) :
    (list element).inputSize (input :: inputs) =
      element.inputSize input + 1 + (list element).inputSize inputs := by
  exact ComplexityReduction.EncodedType.inputSize_list_cons element.encodedType input inputs

/-- The canonical raw-unit presentation wraps the exact legacy raw encoder. -/
@[simp]
theorem unit_encodedType : unit.encodedType = ComplexityReduction.EncodedType.raw Unit :=
  rfl

/-- The canonical raw-unit presentation retains the unit structural identity. -/
@[simp]
theorem unit_representation : unit.representation = CodecShape.unit.identity :=
  rfl

/-- The Boolean presentation wraps the exact legacy Boolean encoder. -/
@[simp]
theorem bool_encodedType : bool.encodedType = ComplexityReduction.EncodedType.bool :=
  rfl

/-- The Boolean presentation retains its exact canonical representation identity. -/
@[simp]
theorem bool_representation : bool.representation = CodecShape.bool.identity :=
  rfl

/-- The unary-natural presentation wraps the exact legacy unary encoder. -/
@[simp]
theorem unaryNat_encodedType : unaryNat.encodedType = ComplexityReduction.EncodedType.nat :=
  rfl

/-- The unary-natural presentation retains its exact canonical representation identity. -/
@[simp]
theorem unaryNat_representation : unaryNat.representation = CodecShape.unaryNat.identity :=
  rfl

/-- The binary-natural presentation wraps the exact legacy base-two encoder. -/
@[simp]
theorem binaryNat_encodedType : binaryNat.encodedType = ComplexityReduction.EncodedType.binaryNat :=
  rfl

/-- The binary-natural presentation retains its exact canonical representation identity. -/
@[simp]
theorem binaryNat_representation : binaryNat.representation = CodecShape.binaryNat.identity :=
  rfl

/-- Product presentations retain both exact component encoders. -/
@[simp]
theorem prod_encodedType (left right : LawfulEncodedType) :
    (prod left right).encodedType = ComplexityReduction.EncodedType.prod left.encodedType right.encodedType :=
  rfl

/-- Sum presentations retain both exact component encoders. -/
@[simp]
theorem sum_encodedType (left right : LawfulEncodedType) :
    (sum left right).encodedType = ComplexityReduction.EncodedType.sum left.encodedType right.encodedType :=
  rfl

/-- List presentations retain the exact element encoder. -/
@[simp]
theorem list_encodedType (element : LawfulEncodedType) :
    (list element).encodedType = ComplexityReduction.EncodedType.list element.encodedType :=
  rfl

/-- The canonical raw-unit representation is structurally eligible for automatic selection. -/
def unitStructuralCertificate : unit.StructuralCertificate :=
  unit.structuralCertificateOfOrigin .unit

/-- The standard Boolean representation is structurally eligible for automatic selection. -/
def boolStructuralCertificate : bool.StructuralCertificate :=
  bool.structuralCertificateOfOrigin .bool

/-- The standard unary natural-number representation has its closed structural origin. -/
def unaryNatStructuralCertificate : unaryNat.StructuralCertificate :=
  unaryNat.structuralCertificateOfOrigin .unaryNat

/-- The standard base-two natural-number representation has its closed structural origin. -/
def binaryNatStructuralCertificate : binaryNat.StructuralCertificate :=
  binaryNat.structuralCertificateOfOrigin .binaryNat

/-- Product structural certificates are assembled only from exact component certificates. -/
def prodStructuralCertificate (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (prod left right).StructuralCertificate :=
  (prod left right).structuralCertificateOfOrigin (.prod leftCertificate.origin rightCertificate.origin)

/-- Sum structural certificates are assembled only from exact component certificates. -/
def sumStructuralCertificate (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (sum left right).StructuralCertificate :=
  (sum left right).structuralCertificateOfOrigin (.sum leftCertificate.origin rightCertificate.origin)

/-- List structural certificates are assembled only from an exact element certificate. -/
def listStructuralCertificate (element : LawfulEncodedType)
    (elementCertificate : element.StructuralCertificate) :
    (list element).StructuralCertificate :=
  (list element).structuralCertificateOfOrigin (.list elementCertificate.origin)

/-- The raw-unit automatic-admission certificate has exactly the closed unit origin. -/
@[simp]
theorem unitStructuralCertificate_origin : unitStructuralCertificate.origin = .unit :=
  rfl

/--
The Boolean automatic-admission certificate has exactly the closed Boolean
origin.  This is an origin equality, not a consequence of the Boolean
carrier or encoder injectivity alone.
-/
@[simp]
theorem boolStructuralCertificate_origin : boolStructuralCertificate.origin = .bool :=
  rfl

/-- The unary-natural automatic-admission certificate has exactly the closed unary origin. -/
@[simp]
theorem unaryNatStructuralCertificate_origin : unaryNatStructuralCertificate.origin = .unaryNat :=
  rfl

/-- The base-two automatic-admission certificate has exactly the closed binary origin. -/
@[simp]
theorem binaryNatStructuralCertificate_origin : binaryNatStructuralCertificate.origin = .binaryNat :=
  rfl

/--
Product automatic admission is closed under exactly the two component
certificates: its origin is the structural product of their origins.  No
carrier equality, `Equiv`, or independently supplied encoder can establish
this equality.
-/
@[simp]
theorem prodStructuralCertificate_origin (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (prodStructuralCertificate left right leftCertificate rightCertificate).origin =
      .prod leftCertificate.origin rightCertificate.origin :=
  rfl

/-- Sum automatic admission is closed under exactly the two component certificates. -/
@[simp]
theorem sumStructuralCertificate_origin (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (sumStructuralCertificate left right leftCertificate rightCertificate).origin =
      .sum leftCertificate.origin rightCertificate.origin :=
  rfl

/-- List automatic admission is closed under exactly its element certificate. -/
@[simp]
theorem listStructuralCertificate_origin (element : LawfulEncodedType)
    (elementCertificate : element.StructuralCertificate) :
    (listStructuralCertificate element elementCertificate).origin =
      .list elementCertificate.origin :=
  rfl

/-- Product admission reconstructs the exact ordered product representation identity. -/
@[simp]
theorem prodStructuralCertificate_representation (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (prodStructuralCertificate left right leftCertificate rightCertificate).toLawfulEncodedType.representation =
      (CodecShape.prod left.representation.toShape right.representation.toShape).identity :=
  rfl

/-- Sum admission reconstructs the exact tagged ordered sum representation identity. -/
@[simp]
theorem sumStructuralCertificate_representation (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (sumStructuralCertificate left right leftCertificate rightCertificate).toLawfulEncodedType.representation =
      (CodecShape.sum left.representation.toShape right.representation.toShape).identity :=
  rfl

/-- List admission reconstructs the exact element-indexed list representation identity. -/
@[simp]
theorem listStructuralCertificate_representation (element : LawfulEncodedType)
    (elementCertificate : element.StructuralCertificate) :
    (listStructuralCertificate element elementCertificate).toLawfulEncodedType.representation =
      (CodecShape.list element.representation.toShape).identity :=
  rfl

/-- The raw-unit structural certificate reconstructs its exact presentation. -/
theorem unitStructuralCertificate_presentation :
    unitStructuralCertificate.toLawfulEncodedType = unit :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Each standard structural certificate reconstructs its exact Boolean presentation. -/
theorem boolStructuralCertificate_presentation :
    boolStructuralCertificate.toLawfulEncodedType = bool :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Each standard structural certificate reconstructs its exact unary-natural presentation. -/
theorem unaryNatStructuralCertificate_presentation :
    unaryNatStructuralCertificate.toLawfulEncodedType = unaryNat :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Each standard structural certificate reconstructs its exact binary-natural presentation. -/
theorem binaryNatStructuralCertificate_presentation :
    binaryNatStructuralCertificate.toLawfulEncodedType = binaryNat :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Structural composition preserves the exact product presentation it certifies. -/
theorem prodStructuralCertificate_presentation (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (prodStructuralCertificate left right leftCertificate rightCertificate).toLawfulEncodedType =
      prod left right :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Structural composition preserves the exact sum presentation it certifies. -/
theorem sumStructuralCertificate_presentation (left right : LawfulEncodedType)
    (leftCertificate : left.StructuralCertificate) (rightCertificate : right.StructuralCertificate) :
    (sumStructuralCertificate left right leftCertificate rightCertificate).toLawfulEncodedType =
      sum left right :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Structural composition preserves the exact list presentation it certifies. -/
theorem listStructuralCertificate_presentation (element : LawfulEncodedType)
    (elementCertificate : element.StructuralCertificate) :
    (listStructuralCertificate element elementCertificate).toLawfulEncodedType = list element :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- Unary and base-two natural encodings remain different representation choices. -/
theorem unaryNat_representation_ne_binaryNat_representation :
    unaryNat.representation ≠ binaryNat.representation :=
  CodecShape.unaryNat_identity_ne_binaryNat_identity

/-- Unary and base-two naturals share a Lean carrier but never a representation identity. -/
theorem unaryNat_carrier_eq_binaryNat_carrier : unaryNat.Carrier = binaryNat.Carrier :=
  rfl

/-- Ordered product layouts remain distinct even when both products have carrier `Nat × Nat`. -/
theorem unaryBinary_prod_representation_ne_binaryUnary_prod :
    (prod unaryNat binaryNat).representation ≠ (prod binaryNat unaryNat).representation :=
  CodecShape.prod_identity_ne_swapped CodecShape.unaryNat CodecShape.binaryNat (by decide)

/-- Element codecs cannot be forgotten when forming list representations over the same carrier. -/
theorem unaryNatList_representation_ne_binaryNatList_representation :
    (list unaryNat).representation ≠ (list binaryNat).representation := by
  intro equality
  have shapeEquality : CodecShape.unaryNat = CodecShape.binaryNat :=
    CodecShape.list_identity_eq_iff _ _ |>.mp equality
  exact CodecShape.unaryNat_identity_ne_binaryNat_identity
    (CodecShape.identity_eq_iff _ _ |>.mpr shapeEquality)

/-- The product constructor preserves the left component's explicit shape. -/
theorem prod_representation_shape (left right : LawfulEncodedType) :
    (prod left right).representation.toShape =
      CodecShape.prod left.representation.toShape right.representation.toShape :=
  rfl

/-- The sum constructor preserves the two explicitly ordered component shapes. -/
theorem sum_representation_shape (left right : LawfulEncodedType) :
    (sum left right).representation.toShape =
      CodecShape.sum left.representation.toShape right.representation.toShape :=
  rfl

/-- The list constructor preserves its element's explicit shape. -/
theorem list_representation_shape (element : LawfulEncodedType) :
    (list element).representation.toShape = CodecShape.list element.representation.toShape :=
  rfl

end StandardInstances
end Encoding
end ComplexityReduction
