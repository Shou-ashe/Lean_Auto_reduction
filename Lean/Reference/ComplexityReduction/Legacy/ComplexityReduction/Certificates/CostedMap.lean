/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMPolyTime
import ComplexityReduction.Legacy.ComplexityReduction.Core.SizeBound

namespace ComplexityReduction

/-- A cost function is polynomially bounded by input encoding length. -/
def PolynomialTimeBound {α : Type} (inputSize : α → Nat) (cost : α → Nat) : Prop :=
  ∃ degree coeff const : Nat,
    ∀ x, cost x ≤ coeff * (inputSize x) ^ degree + const

namespace PolynomialTimeBound

/-- Build a polynomial time-bound witness from explicit constants. -/
theorem intro_with {α : Type} {inputSize cost : α → Nat}
    (degree coeff const : Nat)
    (h : ∀ x, cost x ≤ coeff * (inputSize x) ^ degree + const) :
    PolynomialTimeBound inputSize cost :=
  ⟨degree, coeff, const, h⟩

/-- Linear time bounds are polynomial time bounds. -/
theorem of_linear {α : Type} {inputSize cost : α → Nat}
    (h : ∃ coeff const : Nat, ∀ x, cost x ≤ coeff * inputSize x + const) :
    PolynomialTimeBound inputSize cost := by
  rcases h with ⟨coeff, const, hBound⟩
  exact ⟨1, coeff, const, by
    intro x
    simpa using hBound x⟩

end PolynomialTimeBound

/-- A typed map together with polynomial cost and output-size certificates. -/
structure CostedMap (X Y : EncodedType) (f : X.Carrier → Y.Carrier) where
  cost : X.Carrier → Nat
  cost_bound : PolynomialTimeBound (fun x => X.inputSize x) cost
  output_bound :
    PolynomialSizeBound (fun x => X.inputSize x) (fun y => Y.inputSize y) f

namespace CostedMap

/-- Build a costed certificate by charging the encoded output length as cost. -/
def of_encodedLinearSizeBound {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : LinearSizeBound (fun x => X.inputSize x) (fun y => Y.inputSize y) f) :
    CostedMap X Y f := by
  refine
    { cost := fun x => Y.inputSize (f x)
      cost_bound := ?_
      output_bound := PolynomialSizeBound.of_linear h }
  exact PolynomialTimeBound.of_linear h

/-- Typeclass-encoding wrapper for linear output-size certificates. -/
def of_hasEncodingLinearSizeBound {α β : Type} [HasEncoding α] [HasEncoding β]
    {f : α → β}
    (h : LinearSizeBound
      (fun x : α => HasEncoding.inputSize x)
      (fun y : β => HasEncoding.inputSize y)
      f) :
    CostedMap (HasEncoding.toEncodedType α) (HasEncoding.toEncodedType β) f := by
  apply of_encodedLinearSizeBound
  simpa [EncodedType.inputSize, HasEncoding.toEncodedType, HasEncoding.inputSize] using h

/-- Build a costed certificate by charging encoded output length as cost. -/
def of_encodedPolynomialSizeBound {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : PolynomialSizeBound (fun x => X.inputSize x) (fun y => Y.inputSize y) f) :
    CostedMap X Y f := by
  refine
    { cost := fun x => Y.inputSize (f x)
      cost_bound := ?_
      output_bound := h }
  exact h

/--
Build a costed certificate for any map whose output encoding is always empty.
This is useful for explicitly documenting current raw-encoded targets; it is
not a faithful natural-language encoding theorem by itself.
-/
def of_emptyOutputEncoding {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : ∀ x, Y.encode (f x) = []) : CostedMap X Y f := by
  refine
    { cost := fun _ => 0
      cost_bound := ?_
      output_bound := PolynomialSizeBound.const 0 ?_ }
  · exact ⟨0, 0, 0, by intro x; simp⟩
  · intro x
    simp [EncodedType.inputSize, h x]

/-- Typeclass-encoding wrapper for polynomial output-size certificates. -/
def of_hasEncodingPolynomialSizeBound {α β : Type} [HasEncoding α] [HasEncoding β]
    {f : α → β}
    (h : PolynomialSizeBound
      (fun x : α => HasEncoding.inputSize x)
      (fun y : β => HasEncoding.inputSize y)
      f) :
    CostedMap (HasEncoding.toEncodedType α) (HasEncoding.toEncodedType β) f := by
  apply of_encodedPolynomialSizeBound
  simpa [EncodedType.inputSize, HasEncoding.toEncodedType, HasEncoding.inputSize] using h

end CostedMap

/-- Closure-generated map predicate with explicit costed maps as primitives. -/
inductive CostedPolyTimeMap : {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  | of_costed {X Y : EncodedType} {f : X.Carrier → Y.Carrier} :
      CostedMap X Y f → CostedPolyTimeMap f
  | id_map {X : EncodedType} :
      CostedPolyTimeMap (X := X) (Y := X) id
  | comp_map {X Y Z : EncodedType} {f : Y.Carrier → Z.Carrier} {g : X.Carrier → Y.Carrier}
      (hf : CostedPolyTimeMap f) (hg : CostedPolyTimeMap g) :
      CostedPolyTimeMap (f ∘ g)
  | const_map {X Y : EncodedType} (y : Y.Carrier) :
      CostedPolyTimeMap (X := X) (Y := Y) (fun _ => y)
  | fst_map {X Y : EncodedType} :
      CostedPolyTimeMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  | snd_map {X Y : EncodedType} :
      CostedPolyTimeMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  | prod_mk_map {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier}
      {g : X.Carrier → Z.Carrier}
      (hf : CostedPolyTimeMap f) (hg : CostedPolyTimeMap g) :
      CostedPolyTimeMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  | inl_map {X Y : EncodedType} :
      CostedPolyTimeMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  | inr_map {X Y : EncodedType} :
      CostedPolyTimeMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  | list_map_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (hf : CostedPolyTimeMap f) :
      CostedPolyTimeMap (X := EncodedType.list X) (Y := EncodedType.list Y)
        (fun xs => xs.map f)
  | list_append_map {X : EncodedType} :
      CostedPolyTimeMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  | list_foldl_map {X Y : EncodedType} {step : Y.Carrier × X.Carrier → Y.Carrier}
      (hstep : CostedPolyTimeMap (X := EncodedType.prod Y X) (Y := Y) step)
      (init : Y.Carrier) :
      CostedPolyTimeMap (X := EncodedType.list X) (Y := Y)
        (fun xs => xs.foldl (fun acc x => step (acc, x)) init)

/-- The project-local costed polynomial-time map model. -/
def CostedPolyTimeModel : PolyTimeModel where
  IsPolyTimeMap := CostedPolyTimeMap
  id_map := CostedPolyTimeMap.id_map
  comp_map := CostedPolyTimeMap.comp_map
  const_map := CostedPolyTimeMap.const_map
  fst_map := CostedPolyTimeMap.fst_map
  snd_map := CostedPolyTimeMap.snd_map
  prod_mk_map := CostedPolyTimeMap.prod_mk_map
  inl_map := CostedPolyTimeMap.inl_map
  inr_map := CostedPolyTimeMap.inr_map
  list_map_map := CostedPolyTimeMap.list_map_map
  list_append_map := CostedPolyTimeMap.list_append_map
  list_foldl_map := CostedPolyTimeMap.list_foldl_map

end ComplexityReduction
