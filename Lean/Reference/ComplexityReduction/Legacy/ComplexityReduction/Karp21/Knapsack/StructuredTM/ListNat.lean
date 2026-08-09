import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ConstraintBound
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Small binary-natural list helpers for the compact Knapsack code-generation
layer.
-/

theorem encodedList_inputSize_append (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  induction xs with
  | nil =>
      simp [EncodedType.inputSize_list_nil]
  | cons x xs ih =>
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, ih]
      omega

theorem encodedList_inputSize_append_singleton (X : EncodedType)
    (xs : List X.Carrier) (x : X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ [x]) =
      (EncodedType.list X).inputSize xs + X.inputSize x + 1 := by
  rw [encodedList_inputSize_append]
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
  omega

theorem binaryNatListAppendSingleton_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list EncodedType.binaryNat) EncodedType.binaryNat)
      (EncodedType.list EncodedType.binaryNat)
      (fun p : List Nat × Nat => p.1 ++ [p.2]) := by
  let X := EncodedType.prod (EncodedType.list EncodedType.binaryNat) EncodedType.binaryNat
  let L := EncodedType.list EncodedType.binaryNat
  have hHead : TMPolyTimeMap X L (fun p : List Nat × Nat => p.1) := by
    simpa [X, L] using TMPolyTimeMap.fst L EncodedType.binaryNat
  have hPayload : TMPolyTimeMap X EncodedType.binaryNat (fun p : List Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd L EncodedType.binaryNat
  have hSingleton : TMPolyTimeMap X L (fun p : List Nat × Nat => [p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.binaryNat) hPayload
    simpa [Function.comp, L] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun p : List Nat × Nat => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hHead hSingleton
  have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.binaryNat) hPair
  simpa [Function.comp, X, L] using hComp

def binaryNatListSumStep (p : Nat × Nat) : Nat :=
  p.1 + p.2

def binaryNatListSum (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => binaryNatListSumStep (acc, x)) 0

theorem binaryNatListSum_foldl_eq (xs : List Nat) (acc : Nat) :
    xs.foldl (fun acc x => binaryNatListSumStep (acc, x)) acc =
      acc + xs.sum := by
  induction xs generalizing acc with
  | nil =>
      simp [binaryNatListSumStep]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [binaryNatListSumStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem binaryNatListSum_eq_sum (xs : List Nat) :
    binaryNatListSum xs = xs.sum := by
  simpa [binaryNatListSum] using (binaryNatListSum_foldl_eq xs 0)

theorem binaryNatListSumStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatListSumStep := by
  simpa [binaryNatListSumStep] using binaryNatAdd_tm_polytime

theorem binaryNatListSumStep_growth
    (source : List Nat) (acc x : Nat)
    (hx :
      EncodedType.binaryNat.inputSize x ≤
        (EncodedType.list EncodedType.binaryNat).inputSize source) :
    EncodedType.binaryNat.inputSize (binaryNatListSumStep (acc, x)) ≤
      EncodedType.binaryNat.inputSize acc +
        ((Polynomial.X + Polynomial.C 1).eval
          ((EncodedType.list EncodedType.binaryNat).inputSize source)) := by
  have hAdd := binaryNatAdd_inputSize_le acc x
  simp [binaryNatListSumStep, Polynomial.eval_add, Polynomial.eval_X] at ⊢
  omega

theorem binaryNatListSum_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatListSum := by
  rcases binaryNatListSumStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        (EncodedType.list EncodedType.binaryNat)
        EncodedType.binaryNat
        (fun xs : List Nat =>
          xs.foldl (fun acc x => binaryNatListSumStep (acc, x)) (0 : Nat)) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        EncodedType.binaryNat EncodedType.binaryNat
        binaryNatListSumStep (0 : Nat) hStep
        (Polynomial.C 1) (Polynomial.X + Polynomial.C 1) ?_ ?_
    · intro xs
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    · intro source acc x hx
      exact binaryNatListSumStep_growth source acc x hx
  simpa [binaryNatListSum] using hFold

theorem binaryNatListSum_tm_polytime_sum :
      TMPolyTimeMap
      (EncodedType.list EncodedType.binaryNat)
      EncodedType.binaryNat
      (fun xs : List Nat => xs.sum) := by
  convert binaryNatListSum_tm_polytime using 1
  funext xs
  exact (binaryNatListSum_eq_sum xs).symm

theorem binaryNatList_sum_inputSize_le (xs : List Nat) :
    EncodedType.binaryNat.inputSize xs.sum ≤
      2 * (EncodedType.list EncodedType.binaryNat).inputSize xs + 1 := by
  induction xs with
  | nil =>
      simp [EncodedType.inputSize, EncodedType.binaryNat]
  | cons x xs ih =>
      have hAdd := binaryNatAdd_inputSize_le x xs.sum
      rw [List.sum_cons]
      have hCons :
          (EncodedType.list EncodedType.binaryNat).inputSize (x :: xs) =
            EncodedType.binaryNat.inputSize x + 1 +
              (EncodedType.list EncodedType.binaryNat).inputSize xs :=
        EncodedType.inputSize_list_cons EncodedType.binaryNat x xs
      calc
        EncodedType.binaryNat.inputSize (x + xs.sum)
            ≤ EncodedType.binaryNat.inputSize x +
                EncodedType.binaryNat.inputSize xs.sum + 1 := hAdd
        _ ≤ EncodedType.binaryNat.inputSize x +
              (2 * (EncodedType.list EncodedType.binaryNat).inputSize xs + 1) + 1 := by
              omega
        _ ≤ 2 *
              (EncodedType.binaryNat.inputSize x + 1 +
                (EncodedType.list EncodedType.binaryNat).inputSize xs) + 1 := by
              omega
        _ = 2 * (EncodedType.list EncodedType.binaryNat).inputSize (x :: xs) + 1 := by
              rw [hCons]

def compactDigitVectorsMassStep (p : Nat × List Nat) : Nat :=
  p.1 + p.2.sum

def compactDigitVectorsMassExecutable (vectors : List (List Nat)) : Nat :=
  vectors.foldl (fun acc digits => compactDigitVectorsMassStep (acc, digits)) 0

theorem compactDigitVectorsMass_foldl_eq
    (vectors : List (List Nat)) (acc : Nat) :
    vectors.foldl (fun acc digits => compactDigitVectorsMassStep (acc, digits)) acc =
      acc + (vectors.map List.sum).sum := by
  induction vectors generalizing acc with
  | nil =>
      simp [compactDigitVectorsMassStep]
  | cons digits vectors ih =>
      rw [List.foldl_cons, ih]
      simp [compactDigitVectorsMassStep, Nat.add_assoc]

theorem compactDigitVectorsMassExecutable_eq
    (vectors : List (List Nat)) :
    compactDigitVectorsMassExecutable vectors = compactDigitVectorsMass vectors := by
  simpa [compactDigitVectorsMassExecutable, compactDigitVectorsMass] using
    compactDigitVectorsMass_foldl_eq vectors 0

theorem compactDigitVectorsMassStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat))
      EncodedType.binaryNat
      compactDigitVectorsMassStep := by
  let X := EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hAcc : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × List Nat => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hDigits :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : Nat × List Nat => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hSum : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × List Nat => p.2.sum) := by
    have hComp := TMPolyTimeMap.comp binaryNatListSum_tm_polytime_sum hDigits
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : Nat × List Nat => (p.1, p.2.sum)) :=
    TMPolyTimeMap.prod_mk hAcc hSum
  have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair
  simpa [Function.comp, compactDigitVectorsMassStep, X] using hComp

theorem compactDigitVectorsMassStep_growth
    (source : List (List Nat)) (acc : Nat) (digits : List Nat)
    (hdigits :
      (EncodedType.list EncodedType.binaryNat).inputSize digits ≤
        (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize source) :
    EncodedType.binaryNat.inputSize (compactDigitVectorsMassStep (acc, digits)) ≤
      EncodedType.binaryNat.inputSize acc +
        ((Polynomial.C 2 * Polynomial.X + Polynomial.C 2).eval
          ((EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize source)) := by
  have hAdd := binaryNatAdd_inputSize_le acc digits.sum
  have hSum := binaryNatList_sum_inputSize_le digits
  simp [compactDigitVectorsMassStep, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X] at ⊢
  omega

theorem compactDigitVectorsMassExecutable_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      EncodedType.binaryNat
      compactDigitVectorsMassExecutable := by
  rcases compactDigitVectorsMassStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        EncodedType.binaryNat
        (fun vectors : List (List Nat) =>
          vectors.foldl (fun acc digits => compactDigitVectorsMassStep (acc, digits))
            (0 : Nat)) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        (EncodedType.list EncodedType.binaryNat) EncodedType.binaryNat
        compactDigitVectorsMassStep (0 : Nat) hStep
        (Polynomial.C 1) (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) ?_ ?_
    · intro vectors
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    · intro source acc digits hdigits
      exact compactDigitVectorsMassStep_growth source acc digits hdigits
  simpa [compactDigitVectorsMassExecutable] using hFold

theorem compactDigitVectorsMass_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      EncodedType.binaryNat
      compactDigitVectorsMass := by
  convert compactDigitVectorsMassExecutable_tm_polytime using 1
  funext vectors
  exact (compactDigitVectorsMassExecutable_eq vectors).symm

end Knapsack
end Karp21
end ComplexityReduction
