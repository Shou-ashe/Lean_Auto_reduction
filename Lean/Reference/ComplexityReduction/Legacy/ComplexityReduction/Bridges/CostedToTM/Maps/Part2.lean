import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1

namespace ComplexityReduction
namespace TMBackedCostedMap

/-- Constant maps carry both a costed certificate and a direct TM2 witness. -/

noncomputable def const (X Y : EncodedType) (y : Y.Carrier) :
    TMBackedCostedMap X Y (fun _ => y) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := Y)
      (LinearSizeBound.const (Y.inputSize y) (by
        intro x
        exact Nat.le_refl _))
  tm_polytime := TMPolyTimeMap.const X Y y

/--
A constant map whose encoded output is empty carries both the size/cost
certificate and the direct TM2 witness.
-/
noncomputable def constOfEmptyEncoding (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) : TMBackedCostedMap X Y (fun _ => y) where
  costed := (const X Y y).costed
  tm_polytime := TMPolyTimeMap.const_of_emptyEncoding X Y y hy

/-- Unary natural-number subtraction carries a direct TM2 witness. -/
noncomputable def natSub :
    TMBackedCostedMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.1 - p.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.prod EncodedType.nat EncodedType.nat)
      (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        cases p with
        | mk n m =>
            simp [EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
            omega))
  tm_polytime := TMPolyTimeMap.nat_sub

/--
Any map whose output encoding is always empty carries a zero-size costed
certificate and a direct TM2 empty-output witness for the current encoding.
-/
noncomputable def ofEmptyOutputEncoding (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (hf : ∀ x, Y.encode (f x) = []) :
    TMBackedCostedMap X Y f where
  costed := CostedMap.of_emptyOutputEncoding hf
  tm_polytime := TMPolyTimeMap.of_emptyOutputEncoding X Y f hf

/--
Proof-carrying finite-symbol filter-map transduction.

The output-size certificate is linear because `List.filterMap` never increases
the encoded length.
-/
noncomputable def symbolFilterMap
    (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (keep : X.Symbol → Option Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).filterMap keep) :
    TMBackedCostedMap X Y f where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := Y)
      (LinearSizeBound.of_le (by
        intro x
        rw [EncodedType.inputSize, EncodedType.inputSize, hf x]
        exact TM2Programs.filterMap_length_le keep (X.encode x)))
  tm_polytime := TMPolyTimeMap.symbol_filterMap X Y f keep hf

/-- Proof-carrying map into a raw-encoded codomain. -/
noncomputable def rawCodomain (X : EncodedType) (α : Type) (f : X.Carrier → α) :
    TMBackedCostedMap X (EncodedType.raw α) f :=
  ofEmptyOutputEncoding X (EncodedType.raw α) f (by intro _; rfl)

/--
Proof-carrying structural product map for `x ↦ (y, x)` with an arbitrary fixed
left component.
-/
noncomputable def prodLeftConstId (X Y : EncodedType) (y : Y.Carrier) :
    TMBackedCostedMap X (EncodedType.prod Y X) (fun x : X.Carrier => (y, x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y X)
      (LinearSizeBound.intro_with 1 (Y.inputSize y + 1) (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod]
        omega))
  tm_polytime := TMPolyTimeMap.prod_left_const_id X Y y

/--
Proof-carrying structural product map for `x ↦ (x, y)` with an arbitrary fixed
right component.
-/
noncomputable def prodIdConst (X Y : EncodedType) (y : Y.Carrier) :
    TMBackedCostedMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, y)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod X Y)
      (LinearSizeBound.intro_with 1 (Y.inputSize y + 1) (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod]))
  tm_polytime := TMPolyTimeMap.prod_id_const X Y y

/--
Proof-carrying structural product map for `x ↦ (f x, z)` when the left
component is symbolwise on encodings and the right component is fixed.
-/
noncomputable def prodSymbolMapConstRight
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (z : Z.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    TMBackedCostedMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (f x, z)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y Z)
      (LinearSizeBound.intro_with 1 (Z.inputSize z + 1) (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hf x]))
  tm_polytime := TMPolyTimeMap.prod_symbolMap_const_right X Y Z f z mapSym hf

/--
Proof-carrying structural product map for `x ↦ (y, f x)` when the left
component is fixed and the right component is symbolwise on encodings.
-/
noncomputable def prodLeftConstSymbolMap
    (X Y Z : EncodedType) (y : Y.Carrier) (f : X.Carrier → Z.Carrier)
    (mapSym : X.Symbol → Z.Symbol)
    (hf : ∀ x, Z.encode (f x) = (X.encode x).map mapSym) :
    TMBackedCostedMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (y, f x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y Z)
      (LinearSizeBound.intro_with 1 (Y.inputSize y + 1) (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hf x]
        omega))
  tm_polytime := TMPolyTimeMap.prod_left_const_symbolMap X Y Z y f mapSym hf

/--
Proof-carrying structural product map for `x ↦ (y, x)` when the fixed left
component has empty encoding.
-/
noncomputable def prodEmptyLeftConstId (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMBackedCostedMap X (EncodedType.prod Y X) (fun x : X.Carrier => (y, x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y X)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hy]))
  tm_polytime := TMPolyTimeMap.prod_emptyLeft_const_id X Y y hy

/--
Proof-carrying structural product map for `x ↦ (x, y)` when the fixed right
component has empty encoding.
-/
noncomputable def prodIdConstEmptyRight (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMBackedCostedMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, y)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod X Y)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hy]))
  tm_polytime := TMPolyTimeMap.prod_id_const_emptyRight X Y y hy

/--
Proof-carrying structural product map for `x ↦ (f x, x)` when the left
component always has empty encoding.
-/
noncomputable def prodEmptyLeftId (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (hf : ∀ x, Y.encode (f x) = []) :
    TMBackedCostedMap X (EncodedType.prod Y X) (fun x : X.Carrier => (f x, x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y X)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hf x]))
  tm_polytime := TMPolyTimeMap.prod_emptyLeft_id X Y f hf

/--
Proof-carrying structural product map for `x ↦ (x, f x)` when the right
component always has empty encoding.
-/
noncomputable def prodIdEmptyRight (X Y : EncodedType)
    (f : X.Carrier → Y.Carrier) (hf : ∀ x, Y.encode (f x) = []) :
    TMBackedCostedMap X (EncodedType.prod X Y) (fun x : X.Carrier => (x, f x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod X Y)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hf x]))
  tm_polytime := TMPolyTimeMap.prod_id_emptyRight X Y f hf

/--
Proof-carrying structural product map for pairing the two projections of an
encoded product.
-/
def prodFstSnd (X Y : EncodedType) :
    TMBackedCostedMap
      (EncodedType.prod X Y)
      (EncodedType.prod X Y)
      (fun p : X.Carrier × Y.Carrier => (p.1, p.2)) where
  costed := by
    simpa [Prod.eta] using (TMBackedCostedMap.id (EncodedType.prod X Y)).costed
  tm_polytime := TMPolyTimeMap.prod_fst_snd X Y

/--
Proof-carrying structural product diagonal map `x ↦ (x, x)`.
-/
noncomputable def prodDiag (X : EncodedType) :
    TMBackedCostedMap X (EncodedType.prod X X) (fun x : X.Carrier => (x, x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod X X)
      (LinearSizeBound.intro_with 2 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod]
        omega))
  tm_polytime := TMPolyTimeMap.prod_diag X

/--
Proof-carrying structural product map when both components are symbolwise on
encodings from the same input.
-/
noncomputable def prodSymbolMaps
    (X Y Z : EncodedType) (f : X.Carrier → Y.Carrier) (g : X.Carrier → Z.Carrier)
    (mapLeft : X.Symbol → Y.Symbol) (mapRight : X.Symbol → Z.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapLeft)
    (hg : ∀ x, Z.encode (g x) = (X.encode x).map mapRight) :
    TMBackedCostedMap X (EncodedType.prod Y Z) (fun x : X.Carrier => (f x, g x)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.prod Y Z)
      (LinearSizeBound.intro_with 2 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.prod, hf x, hg x]
        omega))
  tm_polytime := TMPolyTimeMap.prod_symbolMaps X Y Z f g mapLeft mapRight hf hg

/--
Proof-carrying structural list-map for `xs ↦ xs.map (fun _ => y)` when the
fixed target element is arbitrary.
-/
noncomputable def listConst (X Y : EncodedType) (y : Y.Carrier) :
    TMBackedCostedMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map fun _ => y) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.list X)
      (Y := EncodedType.list Y)
      (LinearSizeBound.intro_with (Y.inputSize y + 1) 0 (by
        intro xs
        rw [EncodedType.inputSize, EncodedType.inputSize]
        have h := TM2Programs.listConstExpand_length_le
          (α := X.Symbol) (β := Y.Symbol) (Y.encode y) ((EncodedType.list X).encode xs)
        rw [TM2Programs.listConst_flatMap_encode X Y y xs] at h
        simpa [EncodedType.inputSize] using h))
  tm_polytime := TMPolyTimeMap.list_const X Y y

/--
Proof-carrying structural list-map for `xs ↦ xs.map (fun _ => y)` when the
fixed target element has empty encoding.
-/
noncomputable def listConstEmpty (X Y : EncodedType) (y : Y.Carrier)
    (hy : Y.encode y = []) :
    TMBackedCostedMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map fun _ => y) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.list X)
      (Y := EncodedType.list Y)
      (LinearSizeBound.of_le (by
        intro xs
        rw [EncodedType.inputSize, EncodedType.inputSize]
        rw [TM2Programs.listConstEmpty_target_encode X Y y hy xs]
        have hlen :
            (List.replicate xs.length (none : Option Y.Symbol)).length = xs.length :=
          List.length_replicate
        exact hlen.symm ▸ TM2Programs.listEncode_length_ge_length X xs))
  tm_polytime := TMPolyTimeMap.list_const_empty X Y y hy

/--
Proof-carrying structural list-map when every mapped element has empty encoding.
-/
noncomputable def listEmptyOutput (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (hf : ∀ x, Y.encode (f x) = []) :
    TMBackedCostedMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map f) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.list X)
      (Y := EncodedType.list Y)
      (LinearSizeBound.of_le (by
        intro xs
        rw [EncodedType.inputSize, EncodedType.inputSize]
        rw [TM2Programs.listEmptyOutput_target_encode X Y f hf xs]
        have hlen :
            (List.replicate xs.length (none : Option Y.Symbol)).length = xs.length :=
          List.length_replicate
        exact hlen.symm ▸ TM2Programs.listEncode_length_ge_length X xs))
  tm_polytime := TMPolyTimeMap.list_emptyOutput X Y f hf

/--
Proof-carrying structural list-map when the element map is symbolwise on
encodings.
-/
noncomputable def listSymbolMap (X Y : EncodedType) (f : X.Carrier → Y.Carrier)
    (mapSym : X.Symbol → Y.Symbol)
    (hf : ∀ x, Y.encode (f x) = (X.encode x).map mapSym) :
    TMBackedCostedMap
      (EncodedType.list X)
      (EncodedType.list Y)
      (fun xs : List X.Carrier => xs.map f) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.list X)
      (Y := EncodedType.list Y)
      (LinearSizeBound.of_le (by
        intro xs
        change ((EncodedType.list Y).encode (xs.map f)).length ≤
          ((EncodedType.list X).encode xs).length
        rw [TM2Programs.listSymbolMap_target_encode X Y f mapSym hf xs]
        have hlen :
            (List.map (Option.map mapSym) ((EncodedType.list X).encode xs)).length =
              ((EncodedType.list X).encode xs).length := by
          induction (EncodedType.list X).encode xs with
          | nil =>
              rfl
          | cons a rest ih =>
              change Nat.succ ((List.map (Option.map mapSym) rest).length) =
                Nat.succ rest.length
              exact congrArg Nat.succ ih
        exact Nat.le_of_eq hlen))
  tm_polytime := TMPolyTimeMap.list_symbolMap X Y f mapSym hf

/--
Proof-carrying structural list-map for the identity element map.
-/
def listId (X : EncodedType) :
    TMBackedCostedMap
      (EncodedType.list X)
      (EncodedType.list X)
      (fun xs : List X.Carrier => xs.map fun x => x) where
  costed := by
    simpa using (TMBackedCostedMap.id (EncodedType.list X)).costed
  tm_polytime := TMPolyTimeMap.list_id X

/-- Proof-carrying singleton-list constructor `x ↦ [x]`. -/
noncomputable def listSingleton (X : EncodedType) :
    TMBackedCostedMap X (EncodedType.list X) (fun x : X.Carrier => [x]) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := X)
      (Y := EncodedType.list X)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.list]))
  tm_polytime := TMPolyTimeMap.list_singleton X

/-- Proof-carrying list cons constructor `(x, xs) ↦ x :: xs`. -/
noncomputable def listCons (X : EncodedType) :
    TMBackedCostedMap
      (EncodedType.prod X (EncodedType.list X))
      (EncodedType.list X)
      (fun p : X.Carrier × List X.Carrier => p.1 :: p.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.prod X (EncodedType.list X))
      (Y := EncodedType.list X)
      (LinearSizeBound.of_le (by
        intro p
        cases p with
        | mk x xs =>
            simp [EncodedType.inputSize, EncodedType.prod, EncodedType.list]))
  tm_polytime := TMPolyTimeMap.list_cons X

/--
Proof-carrying bounded raw-stack list-fold wrapper.

This constructor requires an ordinary polynomial output-size certificate in
addition to the raw-stack TM2 bounds.  It does not use arbitrary
`listFoldlMap`.
-/
noncomputable def listFoldlBoundedRaw (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (tm : Turing.FinTM2)
    (readInput : Option (Y.Symbol ⊕ X.Symbol) → tm.Γ tm.k₀)
    (writeOutput : tm.Γ tm.k₁ → Y.Symbol) (initialAcc : List Y.Symbol)
    (mapped : List Y.Symbol → X.Carrier → List (tm.Γ tm.k₁))
    (stepTime : List Y.Symbol → X.Carrier → Nat) (bound stepBound : Polynomial Nat)
    (hSize :
      PolynomialSizeBound
        (fun xs : List X.Carrier => (EncodedType.list X).inputSize xs)
        (fun y : Y.Carrier => Y.inputSize y)
        (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init))
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
    TMBackedCostedMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) where
  costed := CostedMap.of_encodedPolynomialSizeBound hSize
  tm_polytime :=
    TMPolyTimeMap.list_foldl_boundedRaw X Y step init tm readInput writeOutput initialAcc
      mapped stepTime bound stepBound hRun hInitial hMapped hStep hOutput

/--
Proof-carrying typed/reachable list-fold wrapper.

The step witness is explicit because the exact loop-time expression depends on
the concrete TM2 program for the step.  Callers must also provide an ordinary
polynomial output-size certificate for the folded result.
-/
noncomputable def listFoldlTyped (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (time : Polynomial Nat)
    (hTime : ∀ xs : List X.Carrier,
      2 + TM2Programs.listFoldTypedLoopTime X Y step hStep init xs ≤
        time.eval ((EncodedType.list X).inputSize xs))
    (hSize :
      PolynomialSizeBound
        (fun xs : List X.Carrier => (EncodedType.list X).inputSize xs)
        (fun y : Y.Carrier => Y.inputSize y)
        (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init)) :
    TMBackedCostedMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) where
  costed := CostedMap.of_encodedPolynomialSizeBound hSize
  tm_polytime := TMPolyTimeMap.list_foldl_typed X Y step init hStep time hTime

/--
Proof-carrying structural list-fold when the folded result has empty encoding
for every input list.
-/
noncomputable def listFoldlEmptyOutput (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hf : ∀ xs : List X.Carrier,
      Y.encode (xs.foldl (fun acc x => step (acc, x)) init) = []) :
    TMBackedCostedMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init) :=
  ofEmptyOutputEncoding
    (EncodedType.list X)
    Y
    (fun xs : List X.Carrier => xs.foldl (fun acc x => step (acc, x)) init)
    hf

/--
Proof-carrying structural list-fold whose step keeps the accumulator, so the
folded result is the initial value.
-/
noncomputable def listFoldlKeepAccumulator (X Y : EncodedType) (init : Y.Carrier) :
    TMBackedCostedMap
      (EncodedType.list X)
      Y
      (fun xs : List X.Carrier =>
        xs.foldl (fun acc x => (acc, x).1) init) where
  costed := by
    simpa using (TMBackedCostedMap.const (EncodedType.list X) Y init).costed
  tm_polytime := TMPolyTimeMap.list_foldl_keepAccumulator X Y init

theorem toCostedPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : TMBackedCostedMap X Y f) : CostedPolyTimeMap (X := X) (Y := Y) f :=
  CostedPolyTimeMap.of_costed h.costed

theorem toTMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : TMBackedCostedMap X Y f) : TMPolyTimeMap X Y f :=
  h.tm_polytime

end TMBackedCostedMap

/--
A reduction that simultaneously carries the project-local costed certificate
and the direct TM2 polynomial-time witness.
-/
structure TMBackedCostedReduction (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  costed : CostedPolyTimeMap (X := A.Instance) (Y := B.Instance) f
  tm_polytime : TMPolyTimeMap A.Instance B.Instance f
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)

namespace TMBackedCostedReduction

/-- Build a proof-carrying reduction from a proof-carrying map and correctness. -/
def ofTMBackedCostedMap {A B : EncodedDecisionProblem}
    {f : A.Instance.Carrier → B.Instance.Carrier}
    (hMap : TMBackedCostedMap A.Instance B.Instance f)
    (hCorrect : ∀ x, A.isYes x ↔ B.isYes (f x)) :
    TMBackedCostedReduction A B where
  f := f
  costed := hMap.toCostedPolyTimeMap
  tm_polytime := hMap.toTMPolyTimeMap
  correct := hCorrect

/-- Reflexivity in the proof-carrying costed/TM bridge. -/
def refl (A : EncodedDecisionProblem) : TMBackedCostedReduction A A :=
  ofTMBackedCostedMap (TMBackedCostedMap.id A.Instance) (fun _ => Iff.rfl)

/--
Composition for proof-carrying costed/TM reductions.

This uses the local checked sequential TM2 runner through `TMPolyTimeMap.comp`;
it does not rely on the coarse `CostedTMSound` boundary.
-/
def comp {A B C : EncodedDecisionProblem}
    (rBC : TMBackedCostedReduction B C) (rAB : TMBackedCostedReduction A B) :
    TMBackedCostedReduction A C where
  f := rBC.f ∘ rAB.f
  costed := CostedPolyTimeMap.comp_map rBC.costed rAB.costed
  tm_polytime := TMPolyTimeMap.comp rBC.tm_polytime rAB.tm_polytime
  correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))

/-- Forget to the existing project-local costed Karp reduction. -/
def toCostedKarpReduction {A B : EncodedDecisionProblem}
    (r : TMBackedCostedReduction A B) :
    KarpReductionM CostedPolyTimeModel A B where
  f := { toFun := r.f, polytime := r.costed }
  correct := r.correct

/-- Forget to direct TM2 Karp semantics without using `CostedTMSound`. -/
def toTMKarpReduction {A B : EncodedDecisionProblem}
    (r : TMBackedCostedReduction A B) : TMKarpReduction A B where
  f := r.f
  polytime := r.tm_polytime
  correct := r.correct

/-- Forget to project-local costed reducibility. -/
theorem toCostedPolyReducible {A B : EncodedDecisionProblem}
    (r : TMBackedCostedReduction A B) : PolyReducibleM CostedPolyTimeModel A B :=
  ⟨r.toCostedKarpReduction⟩

/-- Forget to direct TM2 reducibility. -/
theorem toTMPolyReducible {A B : EncodedDecisionProblem}
    (r : TMBackedCostedReduction A B) : TMPolyReducible A B :=
  ⟨r.toTMKarpReduction⟩

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : TMBackedCostedReduction A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

end TMBackedCostedReduction
end ComplexityReduction
