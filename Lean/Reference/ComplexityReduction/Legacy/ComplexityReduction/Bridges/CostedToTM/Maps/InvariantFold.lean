import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1

namespace ComplexityReduction
namespace TMPolyTimeMap

/--
Typed/reachable list fold with a polynomial accumulator-size bound and an
explicit accumulator invariant.  This is the bounded fold proof with the
invariant threaded through the reachable loop states.
-/
theorem list_foldl_typed_invariant_bounded (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (bound : Polynomial Nat) (Inv : Nat → Y.Carrier → Prop)
    (hInit : ∀ xs : List X.Carrier,
      Inv ((EncodedType.list X).inputSize xs) init ∧
        Y.inputSize init ≤ bound.eval ((EncodedType.list X).inputSize xs))
    (hStepBound : ∀ (source : List X.Carrier) (acc : Y.Carrier) (x : X.Carrier),
      Inv ((EncodedType.list X).inputSize source) acc →
        Y.inputSize acc ≤ bound.eval ((EncodedType.list X).inputSize source) →
          X.inputSize x ≤ (EncodedType.list X).inputSize source →
            Inv ((EncodedType.list X).inputSize source) (step (acc, x)) ∧
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
          Inv N acc →
            Y.inputSize acc ≤ B →
              TM2Programs.listFoldTypedLoopTime X Y step hStep acc rest ≤
                C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hRest _hInv _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro acc hRest hInv hAcc
        have hxN : X.inputSize x ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hxsN : (EncodedType.list X).inputSize xs ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hNextPair :
            Inv N (step (acc, x)) ∧ Y.inputSize (step (acc, x)) ≤ B := by
          simpa [B, N] using hStepBound source acc x (by simpa [N] using hInv)
            (by simpa [B, N] using hAcc) hxN
        have hTail := ih (step (acc, x)) hxsN hNextPair.1 hNextPair.2
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
              (by simpa [EncodedType.inputSize] using hNextPair.2)
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
  have hInitPair := hInit source
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y step hStep init source ≤ C * N := by
    simpa [N, B] using hLoopAux source init (by simp [N]) hInitPair.1 hInitPair.2
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, listFoldTypedBoundedTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [show (EncodedType.list X).inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

/--
Typed/reachable list fold with an accumulator invariant and an additive
per-element growth bound.
-/
theorem list_foldl_typed_invariant_growth_bounded (X Y : EncodedType)
    (step : Y.Carrier × X.Carrier → Y.Carrier) (init : Y.Carrier)
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod Y X).encode Y.encode step)
    (base grow : Polynomial Nat) (Inv : Nat → Y.Carrier → Prop)
    (hInit : ∀ xs : List X.Carrier,
      Inv ((EncodedType.list X).inputSize xs) init ∧
        Y.inputSize init ≤ base.eval ((EncodedType.list X).inputSize xs))
    (hStepGrowth : ∀ (source : List X.Carrier) (acc : Y.Carrier) (x : X.Carrier),
      Inv ((EncodedType.list X).inputSize source) acc →
        X.inputSize x ≤ (EncodedType.list X).inputSize source →
          Inv ((EncodedType.list X).inputSize source) (step (acc, x)) ∧
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
          Inv N acc →
            Y.inputSize acc ≤ B₀ + (N - (EncodedType.list X).inputSize rest) * G →
              TM2Programs.listFoldTypedLoopTime X Y step hStep acc rest ≤
                C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hRest _hInv _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro acc hRest hInv hAcc
        have hxN : X.inputSize x ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hxsN : (EncodedType.list X).inputSize xs ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hAccFull : Y.inputSize acc ≤ B := by
          dsimp [B]
          nlinarith [hAcc, Nat.sub_le N ((EncodedType.list X).inputSize (x :: xs))]
        have hNextGrowth := hStepGrowth source acc x (by simpa [N] using hInv) hxN
        have hNext :
            Y.inputSize (step (acc, x)) ≤
              B₀ + (N - (EncodedType.list X).inputSize xs) * G := by
          have hGrowth :
              Y.inputSize (step (acc, x)) ≤ Y.inputSize acc + G := by
            simpa [G, N] using hNextGrowth.2
          have hSub :
              N - (EncodedType.list X).inputSize (x :: xs) + 1 ≤
                N - (EncodedType.list X).inputSize xs := by
            have hCons :
                (EncodedType.list X).inputSize (x :: xs) =
                  X.inputSize x + 1 + (EncodedType.list X).inputSize xs :=
              EncodedType.inputSize_list_cons X x xs
            rw [hCons] at hRest ⊢
            omega
          calc
            Y.inputSize (step (acc, x)) ≤ Y.inputSize acc + G := hGrowth
            _ ≤ B₀ + (N - (EncodedType.list X).inputSize (x :: xs)) * G + G := by
                  omega
            _ = B₀ + (N - (EncodedType.list X).inputSize (x :: xs) + 1) * G := by
                  ring
            _ ≤ B₀ + (N - (EncodedType.list X).inputSize xs) * G :=
                  Nat.add_le_add_left (Nat.mul_le_mul_right G hSub) B₀
        have hTail := ih (step (acc, x)) hxsN hNextGrowth.1 hNext
        have hStepTime :
            hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (acc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize acc + 1 + X.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hNextFull : Y.inputSize (step (acc, x)) ≤ B := by
          dsimp [B]
          nlinarith [hNext, Nat.sub_le N ((EncodedType.list X).inputSize xs)]
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
  have hInitPair := hInit source
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y step hStep init source ≤ C * N := by
    simpa [N, B₀, G] using
      hLoopAux source init (by simp [N]) hInitPair.1 (by simpa [N, B₀] using hInitPair.2)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, listFoldTypedGrowthTimePolynomial, B₀, G, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [show (EncodedType.list X).inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

end TMPolyTimeMap
end ComplexityReduction
