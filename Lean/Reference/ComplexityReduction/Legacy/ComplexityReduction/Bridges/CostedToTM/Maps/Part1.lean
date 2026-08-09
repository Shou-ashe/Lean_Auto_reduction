/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs

namespace ComplexityReduction

namespace TMPolyTimeMap

/--
Maps that preserve encodings up to a fixed alphabet equivalence are directly
TM2 polynomial-time.
-/
theorem of_encodingEquiv (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (e : X.Symbol ≃ Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map e) :
    TMPolyTimeMap X Y f :=
  ⟨TM2Programs.encodingEquivComputableInPolyTime X Y f e hf⟩

/-- Boolean negation as a one-symbol encoding equivalence. -/
def boolNotEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- Boolean negation is directly TM2 polynomial-time computable. -/
theorem bool_not : TMPolyTimeMap EncodedType.bool EncodedType.bool Bool.not :=
  of_encodingEquiv EncodedType.bool EncodedType.bool Bool.not boolNotEquiv (by
    intro b
    cases b <;> rfl)

/-- Unary natural-number equality is directly TM2 polynomial-time computable. -/
theorem nat_eq :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      (fun p : Nat × Nat => decide (p.1 = p.2)) :=
  ⟨TM2Programs.natEqComputableInPolyTime⟩

/-- Unary natural-number subtraction is directly TM2 polynomial-time computable. -/
theorem nat_sub :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.1 - p.2) :=
  ⟨TM2Programs.natSubComputableInPolyTime⟩

/-- Constant maps are directly TM2 polynomial-time computable. -/
theorem const (X Y : EncodedType) (y : Y.Carrier) : TMPolyTimeMap X Y (fun _ => y) :=
  ⟨TM2Programs.constComputableInPolyTime X Y y⟩

/--
Direct TM2 polynomial-time maps are closed under composition by the local
sequential-composition machine.

This deliberately avoids mathlib's `Turing.TM2ComputableInPolyTime.comp`, which
is a `proof_wanted` in the current dependency.
-/
theorem comp {X Y Z : EncodedType}
    {f : Y.Carrier → Z.Carrier} {g : X.Carrier → Y.Carrier}
    (hf : TMPolyTimeMap Y Z f) (hg : TMPolyTimeMap X Y g) :
    TMPolyTimeMap X Z (f ∘ g) := by
  rcases hf with ⟨hf⟩
  rcases hg with ⟨hg⟩
  exact ⟨TM2Programs.seqCompComputableInPolyTime hg hf⟩

/-- Constants with empty output encodings are directly TM2 polynomial-time computable. -/
theorem const_of_emptyEncoding (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) : TMPolyTimeMap X Y (fun _ => y) :=
  by
    let _h := hy
    exact const X Y y

/--
Any map whose output encoding is always empty is directly TM2 polynomial-time
for the current encoding.
-/
theorem of_emptyOutputEncoding (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) : TMPolyTimeMap X Y f :=
  ⟨TM2Programs.emptyOutputComputableInPolyTime X Y f hf⟩

/--
Finite-symbol filter-map transductions are directly TM2 polynomial-time.

This packages the checked `filterMapMachine`: the machine scans the input
encoding, keeps the symbols selected by `keep`, and reverses its temporary stack
back into source order.
-/
theorem symbol_filterMap
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (keep : X.Symbol → Option Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).filterMap keep) :
    TMPolyTimeMap X Y f :=
  ⟨{ tm := TM2Programs.filterMapMachine X.Symbol Y.Symbol keep
     inputAlphabet := Equiv.refl X.Symbol
     outputAlphabet := Equiv.refl Y.Symbol
     time := 4 * Polynomial.X + 2
     outputsFun := by
      intro x
      have hOut :=
        TM2Programs.filterMap_outputs X.Symbol Y.Symbol keep (X.encode x)
      change Turing.TM2OutputsInTime
        (TM2Programs.filterMapMachine X.Symbol Y.Symbol keep)
        (List.map _root_.id (X.encode x))
        (some (List.map _root_.id (Y.encode (f x))))
        ((4 * Polynomial.X + 2).eval (X.encode x).length)
      simpa [hf x, List.map_id, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using hOut }⟩

/-- Left sum injections are directly TM2 polynomial-time computable. -/
theorem inl (X Y : EncodedType) :
    TMPolyTimeMap X (EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier) :=
  ⟨TM2Programs.inlComputableInPolyTime X Y⟩

/-- Right sum injections are directly TM2 polynomial-time computable. -/
theorem inr (X Y : EncodedType) :
    TMPolyTimeMap Y (EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier) :=
  ⟨TM2Programs.inrComputableInPolyTime X Y⟩

/-- First product projections are directly TM2 polynomial-time computable. -/
theorem fst (X Y : EncodedType) :
    TMPolyTimeMap (EncodedType.prod X Y) X (@Prod.fst X.Carrier Y.Carrier) :=
  ⟨TM2Programs.fstComputableInPolyTime X Y⟩

/-- Second product projections are directly TM2 polynomial-time computable. -/
theorem snd (X Y : EncodedType) :
    TMPolyTimeMap (EncodedType.prod X Y) Y (@Prod.snd X.Carrier Y.Carrier) :=
  ⟨TM2Programs.sndComputableInPolyTime X Y⟩

/--
The structural product map `x ↦ (y, x)` is directly TM2 polynomial-time for an
arbitrary fixed left component.
-/
theorem prod_left_const_id (X Y : EncodedType) (y : Y.Carrier) :
    TMPolyTimeMap X (EncodedType.prod Y X) (fun x : X.Carrier => (y, x)) :=
  ⟨TM2Programs.prodLeftConstIdComputableInPolyTime X Y y⟩

/--
The structural product map `x ↦ (x, y)` is directly TM2 polynomial-time for an
arbitrary fixed right component.
-/
theorem prod_id_const (X Y : EncodedType) (y : Y.Carrier) :
    TMPolyTimeMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, y)) :=
  ⟨TM2Programs.prodRightConstIdComputableInPolyTime X Y y⟩

/--
The structural product map `x ↦ (f x, z)` is directly TM2 polynomial-time when
the left component is symbolwise on encodings and the right component is fixed.
-/
theorem prod_symbolMap_const_right
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (z : Z.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    TMPolyTimeMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (f x, z)) :=
  ⟨TM2Programs.prodSymbolMapConstRightComputableInPolyTime X Y Z f z mapSym hf⟩

/--
The structural product map `x ↦ (y, f x)` is directly TM2 polynomial-time when
the left component is fixed and the right component is symbolwise on encodings.
-/
theorem prod_left_const_symbolMap
    (X Y Z : EncodedType) (y : Y.Carrier) (f : X.Carrier → Z.Carrier)
    (mapSym : X.Symbol → Z.Symbol)
    (hf : ∀ x, Z.encode (f x) = (X.encode x).map mapSym) :
    TMPolyTimeMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (y, f x)) :=
  ⟨TM2Programs.prodLeftConstSymbolMapComputableInPolyTime X Y Z y f mapSym hf⟩

/--
The structural product map `x ↦ (y, x)` is directly TM2 polynomial-time when
the fixed left component has empty encoding.
-/
theorem prod_emptyLeft_const_id (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMPolyTimeMap X (EncodedType.prod Y X) (fun x : X.Carrier => (y, x)) :=
  ⟨TM2Programs.prodEmptyLeftConstIdComputableInPolyTime X Y y hy⟩

/--
The structural product map `x ↦ (x, y)` is directly TM2 polynomial-time when
the fixed right component has empty encoding.
-/
theorem prod_id_const_emptyRight (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMPolyTimeMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, y)) :=
  ⟨TM2Programs.prodRightConstEmptyIdComputableInPolyTime X Y y hy⟩

/--
The structural product map `x ↦ (f x, x)` is directly TM2 polynomial-time when
the left component always has empty encoding.
-/
theorem prod_emptyLeft_id (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    TMPolyTimeMap X (EncodedType.prod Y X) (fun x : X.Carrier => (f x, x)) :=
  ⟨TM2Programs.prodEmptyLeftIdComputableInPolyTime X Y f hf⟩

/--
The structural product map `x ↦ (x, f x)` is directly TM2 polynomial-time when
the right component always has empty encoding.
-/
theorem prod_id_emptyRight (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    TMPolyTimeMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, f x)) :=
  ⟨TM2Programs.prodIdEmptyRightComputableInPolyTime X Y f hf⟩

/--
Pairing the two projections of an encoded product is directly TM2
polynomial-time.

This is only the `prod_mk_map` structural subcase
`p ↦ (Prod.fst p, Prod.snd p)`, obtained from the identity witness on the
encoded product type.
-/
theorem prod_fst_snd (X Y : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod X Y)
      (EncodedType.prod X Y)
      (fun p : X.Carrier × Y.Carrier => (p.1, p.2)) := by
  simpa [Prod.eta] using TMPolyTimeMap.id (EncodedType.prod X Y)

/--
The structural product diagonal `x ↦ (x, x)` is directly TM2 polynomial-time.

This is only a direct `prod_mk_map` subcase; it does not prove arbitrary product
pairing closure.
-/
theorem prod_diag (X : EncodedType) :
    TMPolyTimeMap X (EncodedType.prod X X) (fun x : X.Carrier => (x, x)) :=
  ⟨TM2Programs.prodDiagComputableInPolyTime X⟩

/--
Product pairing is directly TM2 polynomial-time when both component encodings
are obtained by fixed symbol maps from the same input encoding.

This is only a symbolwise structural subcase of `prod_mk_map`; it does not
prove arbitrary product-pairing closure.
-/
theorem prod_symbolMaps
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (g : X.Carrier → Z.Carrier)
    (mapLeft : X.Symbol → Y.Symbol) (mapRight : X.Symbol → Z.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapLeft)
    (hg : ∀ x, Z.encode (g x) = (X.encode x).map mapRight) :
    TMPolyTimeMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (f x, g x)) :=
  ⟨TM2Programs.prodSymbolMapsComputableInPolyTime X Y Z f g mapLeft mapRight hf hg⟩

/--
Direct TM2 polynomial-time maps are closed under arbitrary product pairing.

This is the full `prod_mk_map` closure constructor: the two supplied machines
share the original input encoding, and `prodMkMachine` copies that input before
running and combining their outputs.
-/
theorem prod_mk
    {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier} {g : X.Carrier → Z.Carrier}
    (hf : TMPolyTimeMap X Y f) (hg : TMPolyTimeMap X Z g) :
    TMPolyTimeMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (f x, g x)) := by
  rcases hf with ⟨hf⟩
  rcases hg with ⟨hg⟩
  exact ⟨TM2Programs.prodMkComputableInPolyTime hf hg⟩

/-- Encoded-list append is directly TM2 polynomial-time computable. -/
theorem list_append (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list X) (EncodedType.list X))
      (EncodedType.list X)
      (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) :=
  ⟨TM2Programs.listAppendComputableInPolyTime X⟩

/-- Singleton-list construction is directly TM2 polynomial-time computable. -/
theorem list_singleton (X : EncodedType) :
    TMPolyTimeMap X (EncodedType.list X) (fun x : X.Carrier => [x]) :=
  ⟨TM2Programs.listSingletonComputableInPolyTime X⟩

/-- List cons is directly TM2 polynomial-time computable from an element/list pair. -/
theorem list_cons (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod X (EncodedType.list X))
      (EncodedType.list X)
      (fun p : X.Carrier × List X.Carrier => p.1 :: p.2) := by
  have hHead :
      TMPolyTimeMap
        (EncodedType.prod X (EncodedType.list X))
        (EncodedType.list X)
        (fun p : X.Carrier × List X.Carrier => [p.1]) :=
    TMPolyTimeMap.comp (list_singleton X) (fst (X := X) (Y := EncodedType.list X))
  have hTail :
      TMPolyTimeMap
        (EncodedType.prod X (EncodedType.list X))
        (EncodedType.list X)
        (fun p : X.Carrier × List X.Carrier => p.2) :=
    snd (X := X) (Y := EncodedType.list X)
  have hPair :
      TMPolyTimeMap
        (EncodedType.prod X (EncodedType.list X))
        (EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (fun p : X.Carrier × List X.Carrier => ([p.1], p.2)) :=
    prod_mk hHead hTail
  have hAppend :
      TMPolyTimeMap
        (EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2) :=
    list_append X
  have hComp := TMPolyTimeMap.comp hAppend hPair
  simpa [Function.comp] using hComp

/--
List-mapping to a fixed value is directly TM2 polynomial-time computable.

This is only a structural `list_map_map` subcase; it does not prove arbitrary
list-map closure.
-/
theorem list_const (X Y : EncodedType) (y : Y.Carrier) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map fun _ => y) :=
  ⟨TM2Programs.listConstComputableInPolyTime X Y y⟩

/--
List-mapping to a fixed value is directly TM2 polynomial-time when that value's
encoding is empty.
-/
theorem list_const_empty (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map fun _ => y) :=
  ⟨TM2Programs.listConstEmptyComputableInPolyTime X Y y hy⟩

/--
List-map is directly TM2 polynomial-time when every mapped element has empty
encoding.
-/
theorem list_emptyOutput (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map f) :=
  ⟨TM2Programs.listEmptyOutputComputableInPolyTime X Y f hf⟩

/--
List-map is directly TM2 polynomial-time when the element map is realized by a
fixed symbol map on encodings.

This is only a symbolwise structural subcase of `list_map_map`; it does not
prove arbitrary list-map closure.
-/
theorem list_symbolMap (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map f) :=
  ⟨TM2Programs.listSymbolMapComputableInPolyTime X Y f mapSym hf⟩

/--
List-map is directly TM2 polynomial-time for the identity element map.

This is only the identity structural subcase of `list_map_map`; it reuses the
TM2 identity witness for the encoded list type.
-/
theorem list_id (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list X)
      (fun xs : List X.Carrier => xs.map fun x => x) := by
  simpa using TMPolyTimeMap.id (EncodedType.list X)

/--
Direct TM2 polynomial-time maps are closed under encoded-list map.

The machine scans the source list block by block, runs the supplied element
witness on each decoded block, writes each mapped output block and delimiter to
a reverse accumulator, resets all supplied-machine work stacks, and finally
drains the accumulator to the public output stack.
-/
theorem list_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hf : TMPolyTimeMap X Y f) :
    TMPolyTimeMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map f) := by
  rcases hf with ⟨hf⟩
  exact ⟨TM2Programs.listMapComputableInPolyTime hf⟩

/--
Bounded raw-stack list fold as a typed TM2 polynomial-time fold wrapper.

The caller supplies the raw accumulator semantics through `hOutput` and the
global prefix accumulator/output and step-time polynomial bounds.  This is not
the arbitrary `list_foldl_map` closure constructor.
-/
theorem list_foldl_boundedRaw (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (tm : Turing.FinTM2)
    (readInput : Option (Y.Symbol ⊕ X.Symbol) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → Y.Symbol) (initialAcc : List Y.Symbol)
    (mapped : List Y.Symbol → X.Carrier → List (tm.Γ tm.k₁))
    (stepTime : List Y.Symbol → X.Carrier → Nat) (bound stepBound : Polynomial Nat)
    (hRun : ∀ acc x,
      StateTransition.EvalsToInTime tm.step
        (Turing.initList tm
          (acc.map (fun b => readInput (some (Sum.inl b))) ++ readInput none ::
            (X.encode x).map (fun a => readInput (some (Sum.inr a)))))
        (some (Turing.haltList tm (mapped acc x))) (stepTime acc x))
    (hInitial : ∀ xs : List X.Carrier,
      initialAcc.length ≤ bound.eval ((EncodedType.list X).inputSize xs))
    (hMapped : ∀ (xs : List X.Carrier) acc x,
      acc.length ≤ bound.eval ((EncodedType.list X).inputSize xs) →
        (mapped acc x).length ≤ bound.eval ((EncodedType.list X).inputSize xs))
    (hStep : ∀ (xs : List X.Carrier) acc x,
      acc.length ≤ bound.eval ((EncodedType.list X).inputSize xs) →
        stepTime acc x ≤ stepBound.eval ((EncodedType.list X).inputSize xs))
    (hOutput : ∀ xs : List X.Carrier,
      Y.encode (xs.foldl (fun acc x => step (acc, x)) init) =
        TM2Programs.listFoldLoopAcc writeOutput mapped initialAcc xs) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) := by
  let hRaw :=
    TM2Programs.listFoldBoundedComputableInPolyTime
      (δ := X.Carrier) (α := X.Symbol) (β := Y.Symbol)
      tm readInput writeOutput initialAcc X.encode mapped stepTime bound stepBound
      hRun
      (by
        intro xs
        simpa using hInitial xs)
      (by
        intro xs acc x hAcc
        exact hMapped xs acc x (by simpa using hAcc))
      (by
        intro xs acc x hAcc
        exact hStep xs acc x (by simpa using hAcc))
  exact
    ⟨{ tm := hRaw.tm
       inputAlphabet := hRaw.inputAlphabet
       outputAlphabet := hRaw.outputAlphabet
       time := hRaw.time
       outputsFun := by
        intro xs
        simpa [EncodedType.list, hOutput xs] using hRaw.outputsFun xs }⟩

/--
Typed reachable-accumulator list fold as a direct TM2 polynomial-time fold.

The caller supplies a direct TM2 witness for the step and a polynomial bound on
the exact reachable loop time.  This avoids the unsound arbitrary raw
`list_foldl_map` closure: the step machine is only run on accumulator encodings
that arise from the typed fold itself.
-/
theorem list_foldl_typed (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (time : Polynomial Nat)
    (hTime : ∀ xs : List X.Carrier,
      2 + TM2Programs.listFoldTypedLoopTime X Y step hStep init xs ≤
        time.eval ((EncodedType.list X).inputSize xs)) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) :=
  ⟨TM2Programs.listFoldTypedComputableInPolyTime X Y step init hStep time hTime⟩

/-- Default time polynomial for a reachable typed list fold with a global accumulator bound. -/
noncomputable def listFoldTypedBoundedTimePolynomial (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (bound : Polynomial Nat) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
    (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))

/--
Typed/reachable list fold with a polynomial global accumulator-size bound.

The bound is stated against the original encoded list size.  The step may inspect
the current element, but the caller must show both that the next accumulator
stays within the same bound and that each element seen by the fold has encoding
length at most the original list encoding length.
-/
theorem list_foldl_typed_bounded (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (bound : Polynomial Nat)
    (hInit : ∀ xs : List X.Carrier,
      Y.inputSize init ≤ bound.eval ((EncodedType.list X).inputSize xs))
    (hStepBound : ∀ (source : List X.Carrier) (acc : Y.Carrier) (x : X.Carrier),
      Y.inputSize acc ≤ bound.eval ((EncodedType.list X).inputSize source) →
        X.inputSize x ≤ (EncodedType.list X).inputSize source →
          Y.inputSize (step (acc, x)) ≤
            bound.eval ((EncodedType.list X).inputSize source)) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) := by
  let time := listFoldTypedBoundedTimePolynomial X Y step hStep bound
  refine list_foldl_typed X Y step init hStep time ?_
  intro source
  let N := (EncodedType.list X).inputSize source
  let B := bound.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (rest : List X.Carrier) (acc : Y.Carrier),
        (EncodedType.list X).inputSize rest ≤ N →
          Y.inputSize acc ≤ B →
            TM2Programs.listFoldTypedLoopTime X Y step hStep acc rest ≤
              C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hRest _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro acc hRest hAcc
        have hxN : X.inputSize x ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hxsN : (EncodedType.list X).inputSize xs ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hNext :
            Y.inputSize (step (acc, x)) ≤ B := by
          simpa [B, N] using hStepBound source acc x (by simpa [B, N] using hAcc) hxN
        have hTail := ih (step (acc, x)) hxsN hNext
        have hStepTime :
            hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (acc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize acc + 1 + X.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode x).length
                (Y.encode acc).length (Y.encode (step (acc, x))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))) ≤
              C * (X.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAcc)
              (by simpa [EncodedType.inputSize] using hNext)
              hStepTime
        calc
          TM2Programs.listFoldTypedLoopTime X Y step hStep acc (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime X Y step hStep (step (acc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode x).length
                (Y.encode acc).length (Y.encode (step (acc, x))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))) := by
                rfl
          _ ≤ C * (EncodedType.list X).inputSize xs + C * (X.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list X).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y step hStep init source ≤ C * N := by
    simpa [N, B] using hLoopAux source init (by simp [N]) (hInit source)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, listFoldTypedBoundedTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [show (EncodedType.list X).inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

/-- Default time polynomial for a typed list fold whose accumulator grows per element. -/
noncomputable def listFoldTypedGrowthTimePolynomial (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (base grow : Polynomial Nat) : Polynomial Nat :=
  let bound := base + Polynomial.X * grow
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
    (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))

/--
Typed/reachable list fold when each processed element can grow the accumulator
by at most `grow(inputSize)`, from an initial `base(inputSize)` bound.
-/
theorem list_foldl_typed_growth_bounded (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (base grow : Polynomial Nat)
    (hInit : ∀ xs : List X.Carrier,
      Y.inputSize init ≤ base.eval ((EncodedType.list X).inputSize xs))
    (hStepGrowth : ∀ (source : List X.Carrier) (acc : Y.Carrier) (x : X.Carrier),
      X.inputSize x ≤ (EncodedType.list X).inputSize source →
        Y.inputSize (step (acc, x)) ≤
          Y.inputSize acc + grow.eval ((EncodedType.list X).inputSize source)) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) := by
  let time := listFoldTypedGrowthTimePolynomial X Y step hStep base grow
  refine list_foldl_typed X Y step init hStep time ?_
  intro source
  let N := (EncodedType.list X).inputSize source
  let B₀ := base.eval N
  let G := grow.eval N
  let B := B₀ + N * G
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (rest : List X.Carrier) (acc : Y.Carrier),
        (EncodedType.list X).inputSize rest ≤ N →
          Y.inputSize acc ≤ B₀ + (N - (EncodedType.list X).inputSize rest) * G →
            TM2Programs.listFoldTypedLoopTime X Y step hStep acc rest ≤
              C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hRest _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro acc hRest hAcc
        have hxN : X.inputSize x ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hxsN : (EncodedType.list X).inputSize xs ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hAccFull : Y.inputSize acc ≤ B := by
          dsimp [B]
          nlinarith [hAcc, Nat.sub_le N ((EncodedType.list X).inputSize (x :: xs))]
        have hNextGrowth :=
          hStepGrowth source acc x hxN
        have hNext :
            Y.inputSize (step (acc, x)) ≤
              B₀ + (N - (EncodedType.list X).inputSize xs) * G := by
          have hGrowth :
              Y.inputSize (step (acc, x)) ≤ Y.inputSize acc + G := by
            simpa [G, N] using hNextGrowth
          have hSub :
              N - (EncodedType.list X).inputSize (x :: xs) + 1 ≤
                N - (EncodedType.list X).inputSize xs := by
            rw [EncodedType.inputSize_list_cons]
            rw [EncodedType.inputSize_list_cons] at hRest
            omega
          have hBudget :
              (N - (EncodedType.list X).inputSize (x :: xs)) * G + G ≤
                (N - (EncodedType.list X).inputSize xs) * G := by
            calc
              (N - (EncodedType.list X).inputSize (x :: xs)) * G + G
                  = (N - (EncodedType.list X).inputSize (x :: xs) + 1) * G := by
                    ring
              _ ≤ (N - (EncodedType.list X).inputSize xs) * G :=
                    Nat.mul_le_mul_right G hSub
          nlinarith [hAcc, hGrowth, hBudget]
        have hNextFull : Y.inputSize (step (acc, x)) ≤ B := by
          dsimp [B]
          nlinarith [hNext, Nat.sub_le N ((EncodedType.list X).inputSize xs)]
        have hTail := ih (step (acc, x)) hxsN hNext
        have hStepTime :
            hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (acc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize acc + 1 + X.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode x).length
                (Y.encode acc).length (Y.encode (step (acc, x))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))) ≤
              C * (X.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccFull)
              (by simpa [EncodedType.inputSize] using hNextFull)
              hStepTime
        calc
          TM2Programs.listFoldTypedLoopTime X Y step hStep acc (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime X Y step hStep (step (acc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode x).length
                (Y.encode acc).length (Y.encode (step (acc, x))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x))) := by
                rfl
          _ ≤ C * (EncodedType.list X).inputSize xs + C * (X.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list X).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hInit' :
      Y.inputSize init ≤ B₀ + (N - (EncodedType.list X).inputSize source) * G := by
    have h := hInit source
    simpa [N, B₀] using h
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y step hStep init source ≤ C * N := by
    simpa [N] using hLoopAux source init (by simp [N]) hInit'
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, listFoldTypedGrowthTimePolynomial, B₀, G, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [show (EncodedType.list X).inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

/--
List-fold is directly TM2 polynomial-time when the folded result's encoding is
empty for every input list.

This is only an empty-output structural subcase of `list_foldl_map`; it does
not use or prove arbitrary fold closure.
-/
theorem list_foldl_emptyOutput (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hf : ∀ xs : List X.Carrier,
      Y.encode (xs.foldl (fun acc x => step (acc, x)) init) = []) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) :=
  TMPolyTimeMap.of_emptyOutputEncoding
    (EncodedType.list X)
    Y
    (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init)
    hf

/--
List-fold is directly TM2 polynomial-time when the step keeps the accumulator.

This is only a structural `list_foldl_map` subcase; it reuses the constant-map
TM2 witness for the folded result `init`.
-/
theorem list_foldl_keepAccumulator (X Y : EncodedType) (init : Y.Carrier) :
    TMPolyTimeMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier =>
        xs.foldl (fun acc x => (acc, x).1) init) := by
  simpa using TMPolyTimeMap.const (EncodedType.list X) Y init

end TMPolyTimeMap

/--
Constructor-by-constructor obligations for interpreting the project-local
`CostedPolyTimeMap` closure language in direct TM2 semantics.

This structure is intentionally stronger and more explicit than
`CostedTMSound`: it exposes exactly which closure facts and primitive facts must
be supplied before arbitrary costed maps can be transported to TM semantics.
-/
structure CostedClosureTMSound : Type 1 where
  of_costed :
    {X Y : EncodedType} → {f : X.Carrier → Y.Carrier} →
      CostedMap X Y f → TMPolyTimeMap X Y f
  id_map :
    {X : EncodedType} → TMPolyTimeMap X X id
  comp_map :
    {X Y Z : EncodedType} →
    {f : Y.Carrier → Z.Carrier} →
    {g : X.Carrier → Y.Carrier} →
      TMPolyTimeMap Y Z f → TMPolyTimeMap X Y g → TMPolyTimeMap X Z (f ∘ g)
  const_map :
    {X Y : EncodedType} →
      (y : Y.Carrier) → TMPolyTimeMap X Y (fun _ => y)
  fst_map :
    {X Y : EncodedType} →
      TMPolyTimeMap (EncodedType.prod X Y) X (@Prod.fst X.Carrier Y.Carrier)
  snd_map :
    {X Y : EncodedType} →
      TMPolyTimeMap (EncodedType.prod X Y) Y (@Prod.snd X.Carrier Y.Carrier)
  prod_mk_map :
    {X Y Z : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
    {g : X.Carrier → Z.Carrier} →
      TMPolyTimeMap X Y f → TMPolyTimeMap X Z g →
        TMPolyTimeMap X (EncodedType.prod Y Z) (fun x => (f x, g x))
  inl_map :
    {X Y : EncodedType} →
      TMPolyTimeMap X (EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  inr_map :
    {X Y : EncodedType} →
      TMPolyTimeMap Y (EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  list_map_map :
    {X Y : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
      TMPolyTimeMap X Y f →
        TMPolyTimeMap (EncodedType.list X) (EncodedType.list Y) (fun xs => xs.map f)
  list_append_map :
    {X : EncodedType} →
      TMPolyTimeMap
        (EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  list_foldl_map :
    {X Y : EncodedType} →
    {step : Y.Carrier × X.Carrier → Y.Carrier} →
      TMPolyTimeMap (EncodedType.prod Y X) Y step →
      (init : Y.Carrier) →
        TMPolyTimeMap (EncodedType.list X) Y
          (fun xs => xs.foldl (fun acc x => step (acc, x)) init)

namespace CostedClosureTMSound

/-- Bundle explicit constructor obligations into the legacy coarse soundness hook. -/
def toCostedTMSound (h : CostedClosureTMSound) : CostedTMSound where
  sound := by
    intro X Y f hf
    induction hf with
    | of_costed hCosted =>
        exact h.of_costed hCosted
    | id_map =>
        exact h.id_map
    | comp_map hf hg ihf ihg =>
        exact h.comp_map ihf ihg
    | const_map y =>
        exact h.const_map y
    | fst_map =>
        exact h.fst_map
    | snd_map =>
        exact h.snd_map
    | prod_mk_map hf hg ihf ihg =>
        exact h.prod_mk_map ihf ihg
    | inl_map =>
        exact h.inl_map
    | inr_map =>
        exact h.inr_map
    | list_map_map hf ih =>
        exact h.list_map_map ih
    | list_append_map =>
        exact h.list_append_map
    | list_foldl_map hstep init ih =>
        exact h.list_foldl_map ih init

end CostedClosureTMSound

/--
A proof-carrying costed primitive: the cost/output-size certificate is kept, but
the TM polynomial-time witness is supplied separately instead of inferred from
output size alone.
-/
structure TMBackedCostedMap (X Y : EncodedType) (f : X.Carrier → Y.Carrier) where
  costed : CostedMap X Y f
  tm_polytime : TMPolyTimeMap X Y f

namespace TMBackedCostedMap

/--
Encoding-preserving maps carry both a linear-size certificate and a direct
identity-machine TM2 witness.
-/
noncomputable def ofEncodingEquiv (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (e : X.Symbol ≃ Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map e) :
    TMBackedCostedMap X Y f where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := Y)
      (LinearSizeBound.of_le (by
        intro x
        rw [EncodedType.inputSize, EncodedType.inputSize, hf x]
        simp))
  tm_polytime := TMPolyTimeMap.of_encodingEquiv X Y f e hf

/-- Identity maps carry both a costed certificate and a direct TM2 witness. -/
def id (X : EncodedType) : TMBackedCostedMap X X id where
  costed := CostedMap.of_encodedLinearSizeBound (X := X) (Y := X) LinearSizeBound.id
  tm_polytime := TMPolyTimeMap.id X

/-- Boolean negation carries both a constant-size certificate and a direct TM2 witness. -/
def boolNot : TMBackedCostedMap EncodedType.bool EncodedType.bool Bool.not where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.bool) (Y := EncodedType.bool)
      (LinearSizeBound.const 1 (by
        intro b
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime := TMPolyTimeMap.bool_not

/-- Unary natural-number equality carries a constant-size output certificate and direct TM2 witness. -/
noncomputable def natEq :
    TMBackedCostedMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      (fun p : Nat × Nat => decide (p.1 = p.2)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.prod EncodedType.nat EncodedType.nat)
      (Y := EncodedType.bool)
      (LinearSizeBound.const 1 (by
        intro p
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime := TMPolyTimeMap.nat_eq


end TMBackedCostedMap
end ComplexityReduction
