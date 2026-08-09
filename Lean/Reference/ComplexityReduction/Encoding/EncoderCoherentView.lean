/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Logic.Equiv.Defs
import ComplexityReduction.Encoding.LawfulEncodedType

/-!
Encoder-coherent structural views between exact lawful presentations.

An `EncoderCoherentView` is the sole V2 encoding-layer contract for a
record wrapper, nested wrapper, or a reordered record whose *encoded field
order* is unchanged.  It requires the actual carrier map, an equivalence of
the two finite alphabets, and a pointwise proof that the target encoder is
the alphabet-renaming of the source encoder after that map.

The contract deliberately has no constructor from a bare carrier `Equiv`, a
carrier equality, or a `CodecShape` identity.  It also has no `PolyProg`,
certificate, automatic-presentation, registry, or resolver interface: those
layers must consume this evidence explicitly in later phases.
-/

namespace ComplexityReduction
namespace Encoding

/--
A one-way structural view with encoder-level coherence.

The source and target are exact `LawfulEncodedType` indices, so their concrete
encoders remain observable.  In particular, equal carriers or equal
`CodecShape` identities do not fill any field of this structure.
-/
structure EncoderCoherentView (source target : LawfulEncodedType) : Type where
  /-- The wrapper/view's actual carrier map. -/
  carrierMap : source.Carrier → target.Carrier
  /-- The exact finite-alphabet renaming used by the two concrete encoders. -/
  alphabetEquiv : source.encodedType.Symbol ≃ target.encodedType.Symbol
  /-- The target encoding is exactly the pointwise alphabet-renaming of the source encoding. -/
  encode_coherent : ∀ input,
    target.encode (carrierMap input) = (source.encode input).map alphabetEquiv

namespace EncoderCoherentView

/-- Execute the carrier map certified by an encoder-coherent structural view. -/
def apply {source target : LawfulEncodedType}
    (view : EncoderCoherentView source target) : source.Carrier → target.Carrier :=
  view.carrierMap

/-- The public execution API is definitionally the supplied carrier map. -/
@[simp]
theorem apply_eq_carrierMap {source target : LawfulEncodedType}
    (view : EncoderCoherentView source target) (input : source.Carrier) :
    view.apply input = view.carrierMap input :=
  rfl

/-- The exact encoder coherence retained by a view. -/
@[simp]
theorem encode_coherent_apply {source target : LawfulEncodedType}
    (view : EncoderCoherentView source target) (input : source.Carrier) :
    target.encode (view.apply input) = (source.encode input).map view.alphabetEquiv :=
  view.encode_coherent input

/-- Encoder coherence preserves the concrete encoded-input length. -/
theorem inputSize_eq {source target : LawfulEncodedType}
    (view : EncoderCoherentView source target) (input : source.Carrier) :
    target.inputSize (view.apply input) = source.inputSize input := by
  rw [LawfulEncodedType.inputSize_eq_encode_length,
    LawfulEncodedType.inputSize_eq_encode_length, view.encode_coherent_apply]
  simp

/-- The identity view at one exact lawful presentation. -/
def refl (presentation : LawfulEncodedType) : EncoderCoherentView presentation presentation where
  carrierMap := id
  alphabetEquiv := Equiv.refl _
  encode_coherent := by
    intro input
    simp

/-- Compose only views whose exact middle lawful presentation index agrees. -/
def trans {source middle target : LawfulEncodedType}
    (first : EncoderCoherentView source middle)
    (second : EncoderCoherentView middle target) : EncoderCoherentView source target where
  carrierMap := fun input => second.carrierMap (first.carrierMap input)
  alphabetEquiv := first.alphabetEquiv.trans second.alphabetEquiv
  encode_coherent := by
    intro input
    calc
      target.encode (second.carrierMap (first.carrierMap input)) =
          (middle.encode (first.carrierMap input)).map second.alphabetEquiv :=
        second.encode_coherent _
      _ = ((source.encode input).map first.alphabetEquiv).map second.alphabetEquiv := by
        rw [first.encode_coherent]
      _ = (source.encode input).map (first.alphabetEquiv.trans second.alphabetEquiv) := by
        simp only [List.map_map]
        rfl

/-- Composition executes the two explicitly supplied carrier maps in order. -/
@[simp]
theorem apply_trans {source middle target : LawfulEncodedType}
    (first : EncoderCoherentView source middle)
    (second : EncoderCoherentView middle target) (input : source.Carrier) :
    (first.trans second).apply input = second.apply (first.apply input) :=
  rfl

/--
An audited bidirectional wrapper between two exact lawful presentations.

Both directions must independently satisfy encoder coherence, and their
carrier/alphabet maps must be actual inverses.  This is deliberately stronger
than a bare `Equiv`: no constructor accepts an equivalence without the two
per-input encoding proofs.
-/
structure EncoderCoherentWrapper (source target : LawfulEncodedType) : Type where
  forward : EncoderCoherentView source target
  reverse : EncoderCoherentView target source
  leftInverse : ∀ input, reverse.apply (forward.apply input) = input
  rightInverse : ∀ input, forward.apply (reverse.apply input) = input
  alphabetInverse : reverse.alphabetEquiv = forward.alphabetEquiv.symm

namespace EncoderCoherentWrapper

/-- The carrier equivalence is derived from audited maps and their inverse laws. -/
def carrierEquiv {source target : LawfulEncodedType}
    (wrapper : EncoderCoherentWrapper source target) : source.Carrier ≃ target.Carrier where
  toFun := wrapper.forward.apply
  invFun := wrapper.reverse.apply
  left_inv := wrapper.leftInverse
  right_inv := wrapper.rightInverse

/-- The derived equivalence executes the audited forward encoder-coherent map. -/
@[simp]
theorem carrierEquiv_apply {source target : LawfulEncodedType}
    (wrapper : EncoderCoherentWrapper source target) (input : source.Carrier) :
    wrapper.carrierEquiv input = wrapper.forward.apply input :=
  rfl

end EncoderCoherentWrapper

/--
Audited automatic-presentation eligibility for a bidirectional wrapper.

The target must already have a closed structural certificate.  This is an
encoding-layer admission object only; P1-C03 is responsible for connecting it
to semantic-source request selection, so existing exact structural admission
and its public `.certificate` projection remain unchanged.
-/
structure EncoderCoherentAutomaticAdmission (source target : LawfulEncodedType) : Type where
  wrapper : EncoderCoherentWrapper source target
  targetStructuralCertificate : target.StructuralCertificate

end EncoderCoherentView
end Encoding
end ComplexityReduction
