import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SignedParts
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.TargetDigits

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct binary witnesses for compact shifted constraint bounds and target digits.
-/

def compactConstraintBoundExecutable (constraint : List Int × Int) : Nat :=
  let shift := rowNegativeShift constraint.1
  match binaryIntSignBool constraint.2 with
  | false => binaryIntPayload constraint.2 + shift
  | true =>
      let magnitude := Nat.succ (binaryIntPayload constraint.2)
      if binaryNatSuccLeBool (shift, magnitude) then 0 else shift - magnitude

theorem compactConstraintBoundExecutable_eq
    (constraint : List Int × Int) :
    compactConstraintBoundExecutable constraint = compactConstraintBound constraint := by
  rcases constraint with ⟨row, bound⟩
  cases bound with
  | ofNat n =>
      simp only [compactConstraintBoundExecutable, compactConstraintBound, binaryIntSignBool,
        binaryIntPayload, Int.ofNat_eq_natCast]
      have hCast :
          ((n + rowNegativeShift row : Nat) : Int) =
            (n : Int) + (rowNegativeShift row : Int) := by
        omega
      rw [← hCast, Int.toNat_natCast]
  | negSucc n =>
      by_cases hlt : rowNegativeShift row < n.succ
      · have hSuccLe : (rowNegativeShift row).succ ≤ n.succ := by omega
        have hFlag : binaryNatSuccLeBool (rowNegativeShift row, n.succ) = true := by
          simp [binaryNatSuccLeBool, hSuccLe]
        have hToNat : Int.toNat (Int.negSucc n + (rowNegativeShift row : Int)) = 0 := by
          apply Int.toNat_of_nonpos
          omega
        simp [compactConstraintBoundExecutable, compactConstraintBound, binaryIntSignBool,
          binaryIntPayload, hFlag, hToNat]
      · have hLe : n.succ ≤ rowNegativeShift row := le_of_not_gt hlt
        have hNotSuccLe : ¬ (rowNegativeShift row).succ ≤ n.succ := by omega
        have hFlag : binaryNatSuccLeBool (rowNegativeShift row, n.succ) = false := by
          simp [binaryNatSuccLeBool, hNotSuccLe]
        have hToNat :
            Int.toNat (Int.negSucc n + (rowNegativeShift row : Int)) =
              rowNegativeShift row - n.succ := by
          have hCast :
              Int.negSucc n + (rowNegativeShift row : Int) =
                ((rowNegativeShift row - n.succ : Nat) : Int) := by
            omega
          rw [hCast, Int.toNat_natCast]
        simp [compactConstraintBoundExecutable, compactConstraintBound, binaryIntSignBool,
          binaryIntPayload, hFlag, hToNat]

theorem compactConstraintBoundExecutable_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactConstraintBoundExecutable := by
  let X := constraintBinaryStructuredEncodedType
  let N := EncodedType.binaryNat
  have hRow :
      TMPolyTimeMap X intRowBinaryStructuredEncodedType
        (fun constraint : List Int × Int => constraint.1) := by
    simpa [X, constraintBinaryStructuredEncodedType] using
      TMPolyTimeMap.fst intRowBinaryStructuredEncodedType EncodedType.binaryInt
  have hBound :
      TMPolyTimeMap X EncodedType.binaryInt
        (fun constraint : List Int × Int => constraint.2) := by
    simpa [X, constraintBinaryStructuredEncodedType] using
      TMPolyTimeMap.snd intRowBinaryStructuredEncodedType EncodedType.binaryInt
  have hShift :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int => rowNegativeShift constraint.1) := by
    have hComp := TMPolyTimeMap.comp rowNegativeShift_tm_polytime hRow
    simpa [Function.comp, X, N] using hComp
  have hSign :
      TMPolyTimeMap X EncodedType.bool
        (fun constraint : List Int × Int => binaryIntSignBool constraint.2) := by
    have hComp := TMPolyTimeMap.comp binaryIntSignBool_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int => binaryIntPayload constraint.2) := by
    have hComp := TMPolyTimeMap.comp binaryIntPayload_tm_polytime hBound
    simpa [Function.comp, X, N] using hComp
  have hPositiveInput :
      TMPolyTimeMap X (EncodedType.prod N N)
        (fun constraint : List Int × Int =>
          (binaryIntPayload constraint.2, rowNegativeShift constraint.1)) :=
    TMPolyTimeMap.prod_mk hPayload hShift
  have hPositive :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int =>
          binaryIntPayload constraint.2 + rowNegativeShift constraint.1) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPositiveInput
    simpa [Function.comp, X, N] using hComp
  have hMagnitude :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int => Nat.succ (binaryIntPayload constraint.2)) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hPayload
    simpa [Function.comp, X, N] using hComp
  have hNegativePair :
      TMPolyTimeMap X (EncodedType.prod N N)
        (fun constraint : List Int × Int =>
          (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2))) :=
    TMPolyTimeMap.prod_mk hShift hMagnitude
  have hUnderflow :
      TMPolyTimeMap X EncodedType.bool
        (fun constraint : List Int × Int =>
          binaryNatSuccLeBool
            (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2))) := by
    have hComp := TMPolyTimeMap.comp binaryNatSuccLeBool_tm_polytime hNegativePair
    simpa [Function.comp, X] using hComp
  have hSubtract :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int =>
          rowNegativeShift constraint.1 - Nat.succ (binaryIntPayload constraint.2)) := by
    have hComp := TMPolyTimeMap.comp binaryNatSub_tm_polytime hNegativePair
    simpa [Function.comp, X, N] using hComp
  have hZero : TMPolyTimeMap X N (fun _ : List Int × Int => (0 : Nat)) :=
    TMPolyTimeMap.const X N (0 : Nat)
  have hNegativeBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun constraint : List Int × Int =>
          (binaryNatSuccLeBool
            (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2)),
            constraint)) :=
    TMPolyTimeMap.prod_mk hUnderflow (TMPolyTimeMap.id X)
  have hNegativeDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        N
        (fun p : Bool × (List Int × Int) =>
          match p.1 with
          | true => (0 : Nat)
          | false => rowNegativeShift p.2.1 - Nat.succ (binaryIntPayload p.2.2)) :=
    Clique.boolProduct_dispatch_tm_polytime X N
      (fFalse := fun constraint : List Int × Int =>
        rowNegativeShift constraint.1 - Nat.succ (binaryIntPayload constraint.2))
      (fTrue := fun _ : List Int × Int => (0 : Nat))
      hSubtract hZero
  have hNegative :
      TMPolyTimeMap X N
        (fun constraint : List Int × Int =>
          if binaryNatSuccLeBool
              (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2))
          then (0 : Nat)
          else rowNegativeShift constraint.1 - Nat.succ (binaryIntPayload constraint.2)) := by
    have hComp := TMPolyTimeMap.comp hNegativeDispatch hNegativeBranchInput
    convert hComp using 1
    funext constraint
    cases h :
        binaryNatSuccLeBool
          (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2)) <;>
      simp [Function.comp, h]
  have hOuterInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun constraint : List Int × Int =>
          (binaryIntSignBool constraint.2, constraint)) :=
    TMPolyTimeMap.prod_mk hSign (TMPolyTimeMap.id X)
  have hOuterDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        N
        (fun p : Bool × (List Int × Int) =>
          match p.1 with
          | true =>
              if binaryNatSuccLeBool
                  (rowNegativeShift p.2.1, Nat.succ (binaryIntPayload p.2.2))
              then (0 : Nat)
              else rowNegativeShift p.2.1 - Nat.succ (binaryIntPayload p.2.2)
          | false => binaryIntPayload p.2.2 + rowNegativeShift p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime X N
      (fFalse := fun constraint : List Int × Int =>
        binaryIntPayload constraint.2 + rowNegativeShift constraint.1)
      (fTrue := fun constraint : List Int × Int =>
        if binaryNatSuccLeBool
            (rowNegativeShift constraint.1, Nat.succ (binaryIntPayload constraint.2))
        then (0 : Nat)
        else rowNegativeShift constraint.1 - Nat.succ (binaryIntPayload constraint.2))
      hPositive hNegative
  have hOut := TMPolyTimeMap.comp hOuterDispatch hOuterInput
  convert hOut using 1
  funext constraint
  rcases constraint with ⟨row, bound⟩
  cases hSignValue : binaryIntSignBool bound
  · simp [Function.comp, compactConstraintBoundExecutable, hSignValue]
  · simp [Function.comp, compactConstraintBoundExecutable, hSignValue, Nat.succ_eq_add_one]
    rfl

theorem compactConstraintBound_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactConstraintBound := by
  convert compactConstraintBoundExecutable_tm_polytime using 1
  funext constraint
  exact (compactConstraintBoundExecutable_eq constraint).symm

def compactConstraintBoundDigits (constraints : List (List Int × Int)) : List Nat :=
  constraints.map compactConstraintBound

theorem compactConstraintBoundDigits_tm_polytime :
    TMPolyTimeMap
      constraintListBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactConstraintBoundDigits := by
  have hMap := TMPolyTimeMap.list_map compactConstraintBound_tm_polytime
  simpa [compactConstraintBoundDigits, constraintListBinaryStructuredEncodedType] using hMap

theorem compactConstraintBoundDigits_eq
    (constraints : List (List Int × Int)) :
    compactConstraintBoundDigits constraints = constraints.map compactConstraintBound := rfl

def compactTargetDigitsExecutable (I : IntegerProgrammingInput) : List Nat :=
  compactTargetOnes I ++ compactConstraintBoundDigits I.constraints

theorem compactTargetDigitsExecutable_eq (I : IntegerProgrammingInput) :
    compactTargetDigitsExecutable I = compactTargetDigits I := by
  simp [compactTargetDigitsExecutable, compactTargetDigits, compactTargetOnes_eq_replicate,
    compactConstraintBoundDigits]

theorem compactTargetDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactTargetDigitsExecutable := by
  let X := integerProgrammingBinaryStructuredEncodedType
  let L := EncodedType.list EncodedType.binaryNat
  have hOnes :
      TMPolyTimeMap X L compactTargetOnes := by
    simpa [X, L] using compactTargetOnes_tm_polytime
  have hBounds :
      TMPolyTimeMap X L (fun I : IntegerProgrammingInput =>
        compactConstraintBoundDigits I.constraints) := by
    have hComp := TMPolyTimeMap.comp compactConstraintBoundDigits_tm_polytime
      integerProgrammingBinaryConstraints_tm_polytime
    simpa [Function.comp, X, L] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun I : IntegerProgrammingInput =>
          (compactTargetOnes I, compactConstraintBoundDigits I.constraints)) :=
    TMPolyTimeMap.prod_mk hOnes hBounds
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.binaryNat) hPair
  simpa [Function.comp, compactTargetDigitsExecutable, L, X] using hAppend

theorem compactTargetDigits_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactTargetDigits := by
  convert compactTargetDigitsExecutable_tm_polytime using 1
  funext I
  exact (compactTargetDigitsExecutable_eq I).symm

end Knapsack
end Karp21
end ComplexityReduction
