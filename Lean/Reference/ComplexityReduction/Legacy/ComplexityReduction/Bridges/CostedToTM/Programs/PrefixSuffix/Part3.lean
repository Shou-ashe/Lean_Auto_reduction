import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.PrefixSuffix.Part2

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

/--
TM2 polynomial-time computation of the structural product map `x ↦ (f x, z)`
when the left component is a symbolwise encoding map and the right component is
fixed.

This is still only a direct `prod_mk` structural subcase: it does not prove
arbitrary product-pairing closure.
-/

noncomputable def prodSymbolMapConstRightComputableInPolyTime
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (z : Z.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y Z).encode
      (fun x : X.Carrier => (f x, z)) where
  tm :=
    suffixListMapMachine X.Symbol (Option (Y.Symbol ⊕ Z.Symbol))
      ([none] ++ (Z.encode z).map (fun s => some (Sum.inr s)))
      (fun s => some (Sum.inl (mapSym s)))
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (Y.Symbol ⊕ Z.Symbol))
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      suffixListMap_outputs X.Symbol (Option (Y.Symbol ⊕ Z.Symbol))
        ([none] ++ (Z.encode z).map (fun s => some (Sum.inr s)))
        (fun s => some (Sum.inl (mapSym s)))
        (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod Y Z).encode (f x, z))) =
          some
            ((X.encode x).map
              (fun s : X.Symbol => some (Sum.inl (mapSym s) : Y.Symbol ⊕ Z.Symbol)) ++
              ([none] ++
                (Z.encode z).map (fun s : Z.Symbol => some (Sum.inr s : Y.Symbol ⊕ Z.Symbol))))
      simp [EncodedType.prod, hf x, List.map_map, Function.comp_def]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/--
TM2 polynomial-time computation of the structural product map `x ↦ (f x, x)`
when the left component always has empty encoding.
-/
noncomputable def prodEmptyLeftIdComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y X).encode
      (fun x : X.Carrier => (f x, x)) where
  tm :=
    prefixMapMachine X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
      none (fun s => some (Sum.inr s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      prefixMap_outputs X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
        none (fun s => some (Sum.inr s))
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · simp [EncodedType.prod, hf x]
      constructor
      · rfl
      · intro a _
        rfl
    · simp

/--
TM2 polynomial-time computation of the structural product map `x ↦ (x, f x)`
when the right component always has empty encoding.
-/
noncomputable def prodIdEmptyRightComputableInPolyTime
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod X Y).encode
      (fun x : X.Carrier => (x, f x)) where
  tm :=
    suffixMapMachine X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
      none (fun s => some (Sum.inl s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      suffixMap_outputs X.Symbol (Option (X.Symbol ⊕ Y.Symbol))
        none (fun s => some (Sum.inl s))
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    ·
      have hNone :
          (Equiv.cast rfl).symm (none : Option (X.Symbol ⊕ Y.Symbol)) = none := by
        rfl
      have hSome :
          ∀ a : X.Symbol,
            (Equiv.cast rfl).symm (some (Sum.inl a : X.Symbol ⊕ Y.Symbol)) =
              some (Sum.inl a : X.Symbol ⊕ Y.Symbol) := by
        intro a
        rfl
      simp [EncodedType.prod, hf x, Function.comp_def]
      induction X.encode x with
      | nil =>
          simpa only [List.map_nil, List.nil_append] using congrArg (fun z => [z]) hNone
      | cons a xs ih =>
          simp only [List.map_cons]
          congr
    · simp

/-- TM2 polynomial-time computation of the left sum injection. -/
noncomputable def inlComputableInPolyTime (X Y : EncodedType) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.sum X Y).encode
      (@Sum.inl X.Carrier Y.Carrier) where
  tm :=
    prefixMapMachine X.Symbol (Bool ⊕ (X.Symbol ⊕ Y.Symbol))
      (Sum.inl false) (fun s => Sum.inr (Sum.inl s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      prefixMap_outputs X.Symbol (Bool ⊕ (X.Symbol ⊕ Y.Symbol))
        (Sum.inl false) (fun s => Sum.inr (Sum.inl s))
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · simp [EncodedType.sum]
      constructor
      · rfl
      · intro a _
        rfl
    · simp

/-- TM2 polynomial-time computation of the right sum injection. -/
noncomputable def inrComputableInPolyTime (X Y : EncodedType) :
    Turing.TM2ComputableInPolyTime Y.encode (EncodedType.sum X Y).encode
      (@Sum.inr X.Carrier Y.Carrier) where
  tm :=
    prefixMapMachine Y.Symbol (Bool ⊕ (X.Symbol ⊕ Y.Symbol))
      (Sum.inl true) (fun s => Sum.inr (Sum.inr s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun y := by
    convert
      prefixMap_outputs Y.Symbol (Bool ⊕ (X.Symbol ⊕ Y.Symbol))
        (Sum.inl true) (fun s => Sum.inr (Sum.inr s))
        (List.map (Equiv.cast rfl).invFun (Y.encode y)) using 1
    · simp [EncodedType.sum]
      constructor
      · rfl
      · intro a _
        rfl
    · simp

/--
TM2 polynomial-time computation of the structural product map `x ↦ (y, x)` for
an arbitrary fixed left component.

This is still only a direct `prod_mk` structural subcase: it pairs a fixed
constant with the identity map by writing the fixed left encoding and product
delimiter before the retagged input.
-/
noncomputable def prodLeftConstIdComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y X).encode
      (fun x : X.Carrier => (y, x)) where
  tm :=
    prefixListMapMachine X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
      ((Y.encode y).map (fun s => some (Sum.inl s)) ++ [none])
      (fun s => some (Sum.inr s))
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (Y.Symbol ⊕ X.Symbol))
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      prefixListMap_outputs X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
        ((Y.encode y).map (fun s => some (Sum.inl s)) ++ [none])
        (fun s => some (Sum.inr s))
        (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod Y X).encode (y, x))) =
          some
            ((Y.encode y).map (fun s : Y.Symbol => some (Sum.inl s : Y.Symbol ⊕ X.Symbol)) ++
              [none] ++
              (X.encode x).map (fun s : X.Symbol => some (Sum.inr s : Y.Symbol ⊕ X.Symbol)))
      simp [EncodedType.prod]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/--
TM2 polynomial-time computation of the structural product map `x ↦ (y, f x)`
when the left component is fixed and the right component is a symbolwise
encoding map.

This is still only a direct `prod_mk` structural subcase: it does not prove
arbitrary product-pairing closure.
-/
noncomputable def prodLeftConstSymbolMapComputableInPolyTime
    (X Y Z : EncodedType) (y : Y.Carrier) (f : X.Carrier → Z.Carrier)
    (mapSym : X.Symbol → Z.Symbol)
    (hf : ∀ x, Z.encode (f x) = (X.encode x).map mapSym) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y Z).encode
      (fun x : X.Carrier => (y, f x)) where
  tm :=
    prefixListMapMachine X.Symbol (Option (Y.Symbol ⊕ Z.Symbol))
      ((Y.encode y).map (fun s => some (Sum.inl s)) ++ [none])
      (fun s => some (Sum.inr (mapSym s)))
  inputAlphabet := Equiv.refl X.Symbol
  outputAlphabet := Equiv.refl (Option (Y.Symbol ⊕ Z.Symbol))
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      prefixListMap_outputs X.Symbol (Option (Y.Symbol ⊕ Z.Symbol))
        ((Y.encode y).map (fun s => some (Sum.inl s)) ++ [none])
        (fun s => some (Sum.inr (mapSym s)))
        (X.encode x) using 1
    · change List.map id (X.encode x) = X.encode x
      simp
    · change
        some (List.map id ((EncodedType.prod Y Z).encode (y, f x))) =
          some
            ((Y.encode y).map (fun s : Y.Symbol => some (Sum.inl s : Y.Symbol ⊕ Z.Symbol)) ++
              [none] ++
              (X.encode x).map
                (fun s : X.Symbol => some (Sum.inr (mapSym s) : Y.Symbol ⊕ Z.Symbol)))
      simp [EncodedType.prod, hf x, List.map_map, Function.comp_def]
    · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

/--
TM2 polynomial-time computation of the structural product map `x ↦ (y, x)` when
the fixed left component has empty encoding.

This is a useful direct `prod_mk` subcase: the product encoding is just the
product delimiter followed by the right component encoding.
-/
noncomputable def prodEmptyLeftConstIdComputableInPolyTime
    (X Y : EncodedType) (y : Y.Carrier) (hy : Y.encode y = []) :
    Turing.TM2ComputableInPolyTime X.encode (EncodedType.prod Y X).encode
      (fun x : X.Carrier => (y, x)) where
  tm :=
    prefixMapMachine X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
      none (fun s => some (Sum.inr s))
  inputAlphabet := Equiv.cast rfl
  outputAlphabet := Equiv.cast rfl
  time := 4 * Polynomial.X + 3
  outputsFun x := by
    convert
      prefixMap_outputs X.Symbol (Option (Y.Symbol ⊕ X.Symbol))
        none (fun s => some (Sum.inr s))
        (List.map (Equiv.cast rfl).invFun (X.encode x)) using 1
    · simp [EncodedType.prod, hy]
      constructor
      · rfl
      · intro a _
        rfl
    · simp

end TM2Programs
end ComplexityReduction
