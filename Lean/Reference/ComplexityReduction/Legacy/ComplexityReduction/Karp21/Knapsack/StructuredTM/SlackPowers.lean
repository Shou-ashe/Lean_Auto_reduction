import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitsList
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryMul
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ConstraintBound
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct binary witnesses for compact slack powers.

The semantic definition uses `compactBinaryPowers ((Nat.digits 2 bound).length)`.
This module obtains the length fuel from the direct binary payload list for the
bound, then folds over that structural bit list to emit `1, 2, 4, ...`.
-/

def binaryPowersAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)

def binaryPowersStepInputEncodedType : EncodedType :=
  EncodedType.prod binaryPowersAccEncodedType EncodedType.bool

def binaryPowersInit : Nat × List Nat :=
  (1, [])

def binaryPowersStep (p : (Nat × List Nat) × Bool) : Nat × List Nat :=
  (p.1.1 + p.1.1, p.1.2 ++ [p.1.1])

def binaryPowersFold (bits : List Bool) : Nat × List Nat :=
  bits.foldl (fun acc bit => binaryPowersStep (acc, bit)) binaryPowersInit

def binaryPowersFromBits (bits : List Bool) : List Nat :=
  (binaryPowersFold bits).2

def compactSlackPowersExecutable (constraint : List Int × Int) : List Nat :=
  binaryPowersFromBits (binaryNatBitsList (compactConstraintBound constraint))

def shiftedBinaryPowers (power : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => power :: shiftedBinaryPowers (power + power) n

theorem shiftedBinaryPowers_double (power n : Nat) :
    shiftedBinaryPowers (power + power) n =
      (shiftedBinaryPowers power n).map fun q => 2 * q := by
  induction n generalizing power with
  | zero =>
      simp [shiftedBinaryPowers]
  | succ n ih =>
      simp [shiftedBinaryPowers, ih (power + power), two_mul]

theorem shiftedBinaryPowers_one_eq_compactBinaryPowers (n : Nat) :
    shiftedBinaryPowers 1 n = compactBinaryPowers n := by
  induction n with
  | zero =>
      simp [shiftedBinaryPowers, compactBinaryPowers]
  | succ n ih =>
      rw [shiftedBinaryPowers, compactBinaryPowers]
      congr
      rw [← ih]
      simpa using shiftedBinaryPowers_double 1 n

theorem binaryPowersFold_snd_eq
    (bits : List Bool) (power : Nat) (out : List Nat) :
    (bits.foldl (fun acc bit => binaryPowersStep (acc, bit)) (power, out)).2 =
      out ++ shiftedBinaryPowers power bits.length := by
  induction bits generalizing power out with
  | nil =>
      simp [shiftedBinaryPowers, binaryPowersStep]
  | cons bit bits ih =>
      rw [List.foldl_cons]
      simpa [binaryPowersStep, shiftedBinaryPowers, List.append_assoc] using
        ih (power + power) (out ++ [power])

theorem binaryPowersFromBits_eq_compactBinaryPowers (bits : List Bool) :
    binaryPowersFromBits bits = compactBinaryPowers bits.length := by
  rw [binaryPowersFromBits, binaryPowersFold]
  have h := binaryPowersFold_snd_eq bits 1 []
  simpa [binaryPowersInit, shiftedBinaryPowers_one_eq_compactBinaryPowers] using h

theorem binaryNatBitsList_length (n : Nat) :
    (binaryNatBitsList n).length = (Nat.digits 2 n).length := by
  simp [binaryNatBitsList, EncodedType.binaryNat]

theorem compactSlackPowersExecutable_eq
    (constraint : List Int × Int) :
    compactSlackPowersExecutable constraint = compactSlackPowers constraint := by
  rw [compactSlackPowersExecutable, binaryPowersFromBits_eq_compactBinaryPowers,
    compactSlackPowers, compactSlackBitCount, binaryNatBitsList_length]

theorem binaryPowersStep_tm_polytime :
    TMPolyTimeMap
      binaryPowersStepInputEncodedType
      binaryPowersAccEncodedType
      binaryPowersStep := by
  let X := binaryPowersStepInputEncodedType
  let A := binaryPowersAccEncodedType
  let L := EncodedType.list EncodedType.binaryNat
  have hAcc : TMPolyTimeMap X A (fun p : (Nat × List Nat) × Bool => p.1) := by
    simpa [X, A, binaryPowersStepInputEncodedType] using
      TMPolyTimeMap.fst A EncodedType.bool
  have hPower : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List Nat) × Bool => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, binaryPowersAccEncodedType, X, L] using hComp
  have hOut : TMPolyTimeMap X L
      (fun p : (Nat × List Nat) × Bool => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, binaryPowersAccEncodedType, X, L] using hComp
  have hDouble : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List Nat) × Bool => p.1.1 + p.1.1) := by
    have hComp := TMPolyTimeMap.comp binaryNatDouble_tm_polytime hPower
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod L EncodedType.binaryNat)
        (fun p : (Nat × List Nat) × Bool => (p.1.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hOut hPower
  have hAppend : TMPolyTimeMap X L
      (fun p : (Nat × List Nat) × Bool => p.1.2 ++ [p.1.1]) := by
    have hComp := TMPolyTimeMap.comp binaryNatListAppendSingleton_tm_polytime hAppendInput
    simpa [Function.comp, X, L] using hComp
  have hPair := TMPolyTimeMap.prod_mk hDouble hAppend
  simpa [binaryPowersStep, A, binaryPowersAccEncodedType, X] using hPair

def binaryPowersAccBound (N processed : Nat) (acc : Nat × List Nat) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ processed + 1 ∧
    (EncodedType.list EncodedType.binaryNat).inputSize acc.2 ≤ processed * (N + 2)

theorem binaryPowersInitAcc_bound (N : Nat) :
    binaryPowersAccBound N 0 binaryPowersInit := by
  constructor
  · simp [binaryPowersInit, EncodedType.inputSize, EncodedType.binaryNat]
  · change (EncodedType.list EncodedType.binaryNat).inputSize ([] : List Nat) ≤
        0 * (N + 2)
    rw [Nat.zero_mul]
    exact le_of_eq (EncodedType.inputSize_list_nil EncodedType.binaryNat)

theorem binaryPowersStep_bound {N processed : Nat}
    {acc : Nat × List Nat} {bit : Bool}
    (hAcc : binaryPowersAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    binaryPowersAccBound N (processed + 1) (binaryPowersStep (acc, bit)) := by
  rcases acc with ⟨power, out⟩
  rcases hAcc with ⟨hPower, hOut⟩
  have hDouble := binaryNatDouble_inputSize_le power
  have hAppend :
      (EncodedType.list EncodedType.binaryNat).inputSize (out ++ [power]) =
        (EncodedType.list EncodedType.binaryNat).inputSize out +
          EncodedType.binaryNat.inputSize power + 1 :=
    encodedList_inputSize_append_singleton EncodedType.binaryNat out power
  constructor
  · have hPower' :
        EncodedType.binaryNat.inputSize power + 1 ≤ processed + 2 := by
      simpa [Nat.add_assoc] using Nat.add_le_add_right hPower 1
    simpa [binaryPowersStep] using hDouble.trans hPower'
  · calc
      (EncodedType.list EncodedType.binaryNat).inputSize
          (binaryPowersStep ((power, out), bit)).2
          = (EncodedType.list EncodedType.binaryNat).inputSize out +
              EncodedType.binaryNat.inputSize power + 1 := by
            simp [binaryPowersStep, hAppend]
      _ ≤ processed * (N + 2) + (processed + 1) + 1 := by
            nlinarith [hPower, hOut]
      _ ≤ (processed + 1) * (N + 2) := by
            nlinarith [hProcessed, Nat.zero_le processed, Nat.zero_le N]

theorem binaryPowersFold_bound_aux {N processed : Nat}
    (rest : List Bool) (acc : Nat × List Nat)
    (hAcc : binaryPowersAccBound N processed acc)
    (hLen : processed + rest.length ≤ N) :
    binaryPowersAccBound N (processed + rest.length)
      (rest.foldl (fun acc bit => binaryPowersStep (acc, bit)) acc) := by
  induction rest generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons bit rest ih =>
      have hProcessed : processed ≤ N := by omega
      have hStep := binaryPowersStep_bound (N := N) (processed := processed)
        (acc := acc) (bit := bit) hAcc hProcessed
      have hLenTail : processed + 1 + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLen
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (processed := processed + 1) (acc := binaryPowersStep (acc, bit))
          hStep hLenTail

theorem binaryPowersFold_bound_of_inputSize_le {N : Nat}
    (bits : List Bool)
    (hSize : (EncodedType.list EncodedType.bool).inputSize bits ≤ N) :
    binaryPowersAccBound N bits.length
      (bits.foldl (fun acc bit => binaryPowersStep (acc, bit)) binaryPowersInit) := by
  have hLenRaw := binaryMulList_length_le_inputSize EncodedType.bool bits
  have hLen : bits.length ≤ N := by
    exact hLenRaw.trans hSize
  have h := binaryPowersFold_bound_aux (N := N) (processed := 0) bits binaryPowersInit
    (binaryPowersInitAcc_bound N) (by simpa using hLen)
  simpa using h

noncomputable def binaryPowersFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.X * Polynomial.X + Polynomial.C 3 * Polynomial.X + Polynomial.C 3

@[simp] theorem binaryPowersFoldAccBoundPolynomial_eval (N : Nat) :
    binaryPowersFoldAccBoundPolynomial.eval N = N * N + 3 * N + 3 := by
  simp [binaryPowersFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem binaryPowersAccBound_inputSize_le {N processed : Nat}
    {acc : Nat × List Nat}
    (hAcc : binaryPowersAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    binaryPowersAccEncodedType.inputSize acc ≤
      binaryPowersFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨power, out⟩
  rcases hAcc with ⟨hPower, hOut⟩
  simp [binaryPowersAccEncodedType, EncodedType.inputSize_prod] at hPower hOut ⊢
  nlinarith [hPower, hOut, hProcessed, Nat.zero_le N]

noncomputable def binaryPowersFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod binaryPowersAccEncodedType EncodedType.bool).encode
        binaryPowersAccEncodedType.encode
        binaryPowersStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm binaryPowersFoldAccBoundPolynomial
    (hStep.time.comp
      (binaryPowersFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem binaryPowersFold_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.bool)
      binaryPowersAccEncodedType
      binaryPowersFold := by
  rcases binaryPowersStep_tm_polytime with ⟨hStep⟩
  let time := binaryPowersFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      EncodedType.bool binaryPowersAccEncodedType
      binaryPowersStep binaryPowersInit hStep time ?_
  intro source
  let N := (EncodedType.list EncodedType.bool).inputSize source
  let B := binaryPowersFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List Bool),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              EncodedType.bool binaryPowersAccEncodedType
              binaryPowersStep hStep
              (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                binaryPowersInit)
              rest ≤
            C * (EncodedType.list EncodedType.bool).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          exact List.mem_append_right pref (by simp)
        have hxN : EncodedType.bool.inputSize x ≤ N := by
          have hElem := binaryMulList_element_inputSize_le
            (X := EncodedType.bool) (x := x) (xs := source) hxMemSource
          simpa [N] using hElem
        have hPrefixSize : (EncodedType.list EncodedType.bool).inputSize pref ≤ N := by
          have hEqSize :
              (EncodedType.list EncodedType.bool).inputSize source =
                (EncodedType.list EncodedType.bool).inputSize pref +
                  (EncodedType.list EncodedType.bool).inputSize (x :: xs) := by
            rw [hEq]
            exact binaryMulList_inputSize_append EncodedType.bool pref (x :: xs)
          omega
        have hPrefixBound :=
          binaryPowersFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen := binaryMulList_length_le_inputSize EncodedType.bool pref
          exact hLen.trans hPrefixSize
        have hAccSize :
            binaryPowersAccEncodedType.inputSize
                (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                  binaryPowersInit) ≤ B := by
          simpa [B] using binaryPowersAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepBound := binaryPowersStep_bound
          (N := N) (processed := pref.length)
          (acc := pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
            binaryPowersInit)
          (bit := x) hPrefixBound hPrefixLenN
        have hNextSize :
            binaryPowersAccEncodedType.inputSize
                (binaryPowersStep
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit, x)) ≤ B := by
          have hPrefixSucc : pref.length + 1 ≤ N := by
            have hSourceLenN : source.length ≤ N := by
              have hLen := binaryMulList_length_le_inputSize EncodedType.bool source
              omega
            have hLenEq : source.length = pref.length + (x :: xs).length := by
              rw [hEq]
              exact binaryMulList_length_append_cons pref x xs
            simp at hLenEq
            omega
          simpa [B] using binaryPowersAccBound_inputSize_le hStepBound hPrefixSucc
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod binaryPowersAccEncodedType
                    EncodedType.bool).inputSize
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit, x)) ≤ T := by
          have hArg :
              (EncodedType.prod binaryPowersAccEncodedType
                    EncodedType.bool).inputSize
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change binaryPowersAccEncodedType.inputSize
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit) + 1 +
                EncodedType.bool.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (EncodedType.bool.encode x).length
                (binaryPowersAccEncodedType.encode
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit)).length
                (binaryPowersAccEncodedType.encode
                  (binaryPowersStep
                    (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                      binaryPowersInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod binaryPowersAccEncodedType
                    EncodedType.bool).inputSize
                    (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                      binaryPowersInit, x))) ≤
              C * (EncodedType.bool.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hNextSize)
              hStepTime
        have hTail := ih (pref := pref ++ [x]) (by
          rw [hEq]
          simp [List.append_assoc])
        calc
          TM2Programs.listFoldTypedLoopTime
              EncodedType.bool binaryPowersAccEncodedType
              binaryPowersStep hStep
              (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                binaryPowersInit)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
              EncodedType.bool binaryPowersAccEncodedType
              binaryPowersStep hStep
              ((pref ++ [x]).foldl (fun acc bit => binaryPowersStep (acc, bit))
                binaryPowersInit)
              xs +
            TM2Programs.listFoldBlockTime hStep.tm
              (EncodedType.bool.encode x).length
              (binaryPowersAccEncodedType.encode
                (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                  binaryPowersInit)).length
              (binaryPowersAccEncodedType.encode
                (binaryPowersStep
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit, x))).length
              (hStep.time.eval
                ((EncodedType.prod binaryPowersAccEncodedType
                  EncodedType.bool).inputSize
                  (pref.foldl (fun acc bit => binaryPowersStep (acc, bit))
                    binaryPowersInit, x))) := by
                simp [TM2Programs.listFoldTypedLoopTime, List.foldl_append]; rfl
          _ ≤ C * (EncodedType.list EncodedType.bool).inputSize xs +
              C * (EncodedType.bool.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ = C * (EncodedType.list EncodedType.bool).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                ring
  have hLoop := hLoopAux [] source (by simp)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, binaryPowersFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, Polynomial.eval_add,
      TM2Programs.listFoldBlockTimeCoeff]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        EncodedType.bool binaryPowersAccEncodedType
        binaryPowersStep hStep binaryPowersInit source ≤ time.eval N
  rw [hTimeEval]
  have hLoop' :
      TM2Programs.listFoldTypedLoopTime
        EncodedType.bool binaryPowersAccEncodedType
        binaryPowersStep hStep binaryPowersInit source ≤ C * N := by
    simpa [N] using hLoop
  nlinarith [hLoop', Nat.zero_le C, Nat.zero_le N]

theorem binaryPowersFromBits_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.bool)
      (EncodedType.list EncodedType.binaryNat)
      binaryPowersFromBits := by
  have hFold := binaryPowersFold_tm_polytime
  have hSnd :
      TMPolyTimeMap binaryPowersAccEncodedType (EncodedType.list EncodedType.binaryNat)
        (fun acc : Nat × List Nat => acc.2) := by
    simpa [binaryPowersAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, binaryPowersFromBits] using hComp

theorem compactSlackPowersExecutable_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactSlackPowersExecutable := by
  have hBoundBits :
      TMPolyTimeMap
        constraintBinaryStructuredEncodedType
        (EncodedType.list EncodedType.bool)
        (fun constraint : List Int × Int =>
          binaryNatBitsList (compactConstraintBound constraint)) := by
    have hComp := TMPolyTimeMap.comp binaryNatBitsList_tm_polytime
      compactConstraintBound_tm_polytime
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp binaryPowersFromBits_tm_polytime hBoundBits
  simpa [Function.comp, compactSlackPowersExecutable] using hComp

theorem compactSlackPowers_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactSlackPowers := by
  convert compactSlackPowersExecutable_tm_polytime using 1
  funext constraint
  exact (compactSlackPowersExecutable_eq constraint).symm

end Knapsack
end Karp21
end ComplexityReduction
