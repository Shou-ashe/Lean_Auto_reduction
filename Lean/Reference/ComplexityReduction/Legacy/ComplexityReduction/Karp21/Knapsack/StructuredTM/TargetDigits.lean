import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListLength

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Executable pieces for compact target digit generation.
-/

def rowLengthOnesAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)

def rowLengthOnesStepInputEncodedType : EncodedType :=
  EncodedType.prod rowLengthOnesAccEncodedType EncodedType.binaryInt

def rowLengthOnesInit : Nat × List Nat :=
  (0, [])

def rowLengthOnesStep (p : (Nat × List Nat) × Int) : Nat × List Nat :=
  (p.1.1.succ, p.1.2 ++ [1])

def rowLengthOnesFold (row : List Int) : Nat × List Nat :=
  row.foldl (fun acc z => rowLengthOnesStep (acc, z)) rowLengthOnesInit

def rowTargetOnes (row : List Int) : List Nat :=
  (rowLengthOnesFold row).2

theorem rowLengthOnesFold_eq
    (row : List Int) (len : Nat) (ones : List Nat) :
    row.foldl (fun acc z => rowLengthOnesStep (acc, z)) (len, ones) =
      (len + row.length, ones ++ List.replicate row.length 1) := by
  induction row generalizing len ones with
  | nil =>
      simp [rowLengthOnesStep]
  | cons z zs ih =>
      rw [List.foldl_cons, ih]
      simp [rowLengthOnesStep, List.replicate_succ, List.append_assoc,
        Nat.succ_eq_add_one]
      omega

theorem rowLengthOnesFold_eq_length_replicate (row : List Int) :
    rowLengthOnesFold row = (row.length, List.replicate row.length 1) := by
  unfold rowLengthOnesFold rowLengthOnesInit
  simpa using rowLengthOnesFold_eq row 0 []

theorem rowTargetOnes_eq_replicate (row : List Int) :
    rowTargetOnes row = List.replicate row.length 1 := by
  simp [rowTargetOnes, rowLengthOnesFold_eq_length_replicate]

theorem rowLengthOnesStep_tm_polytime :
    TMPolyTimeMap
      rowLengthOnesStepInputEncodedType
      rowLengthOnesAccEncodedType
      rowLengthOnesStep := by
  let X := rowLengthOnesStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X rowLengthOnesAccEncodedType
        (fun p : (Nat × List Nat) × Int => p.1) := by
    simpa [X, rowLengthOnesStepInputEncodedType] using
      TMPolyTimeMap.fst rowLengthOnesAccEncodedType EncodedType.binaryInt
  have hLen :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : (Nat × List Nat) × Int => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, rowLengthOnesAccEncodedType, X] using hComp
  have hOnes :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : (Nat × List Nat) × Int => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, rowLengthOnesAccEncodedType, X] using hComp
  have hLenSucc :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : (Nat × List Nat) × Int => p.1.1.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hLen
    simpa [Function.comp, X] using hComp
  have hOne :
      TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (1 : Nat)
  have hOneList :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun _ : X.Carrier => ([(1 : Nat)] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.binaryNat) hOne
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.binaryNat)
          (EncodedType.list EncodedType.binaryNat))
        (fun p : (Nat × List Nat) × Int => (p.1.2, [(1 : Nat)])) :=
    TMPolyTimeMap.prod_mk hOnes hOneList
  have hAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : (Nat × List Nat) × Int => p.1.2 ++ [1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.binaryNat) hAppendInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hLenSucc hAppend
  simpa [rowLengthOnesStep, rowLengthOnesAccEncodedType, X] using hOut

theorem binaryNatList_inputSize_singleton_one :
    (EncodedType.list EncodedType.binaryNat).inputSize ([1] : List Nat) = 2 := by
  simp [EncodedType.inputSize, EncodedType.list, EncodedType.binaryNat]

theorem rowLengthOnesStep_growth
    (source : List Int) (acc : Nat × List Nat) (z : Int) :
    rowLengthOnesAccEncodedType.inputSize (rowLengthOnesStep (acc, z)) ≤
      rowLengthOnesAccEncodedType.inputSize acc +
        ((Polynomial.C 5).eval (intRowBinaryStructuredEncodedType.inputSize source)) := by
  rcases acc with ⟨len, ones⟩
  have hSucc := binaryNatAdd_inputSize_le len 1
  have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  have hAppend :
      (EncodedType.list EncodedType.binaryNat).inputSize (ones ++ [1]) =
        (EncodedType.list EncodedType.binaryNat).inputSize ones + 2 := by
    have h :=
      Clique.encodedList_inputSize_append EncodedType.binaryNat ones ([(1 : Nat)] : List Nat)
    simpa [binaryNatList_inputSize_singleton_one] using h
  simp [hOne] at hSucc
  simp only [rowLengthOnesStep, rowLengthOnesAccEncodedType, EncodedType.inputSize_prod]
  simp [Nat.succ_eq_add_one]
  omega

theorem rowLengthOnesFold_tm_polytime :
    TMPolyTimeMap
      intRowBinaryStructuredEncodedType
      rowLengthOnesAccEncodedType
      rowLengthOnesFold := by
  rcases rowLengthOnesStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        rowLengthOnesAccEncodedType
        (fun row : List Int =>
          row.foldl (fun acc z => rowLengthOnesStep (acc, z)) rowLengthOnesInit) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        EncodedType.binaryInt rowLengthOnesAccEncodedType
        rowLengthOnesStep rowLengthOnesInit hStep
        (Polynomial.C 1) (Polynomial.C 5) ?_ ?_
    · intro row
      simp [rowLengthOnesInit, rowLengthOnesAccEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.binaryNat, EncodedType.list]
    · intro source acc z _hz
      exact rowLengthOnesStep_growth source acc z
  simpa [rowLengthOnesFold] using hFold

theorem rowTargetOnes_tm_polytime :
    TMPolyTimeMap
      intRowBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      rowTargetOnes := by
  have hSnd :
      TMPolyTimeMap rowLengthOnesAccEncodedType (EncodedType.list EncodedType.binaryNat)
        (fun acc : Nat × List Nat => acc.2) := by
    simpa [rowLengthOnesAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hComp := TMPolyTimeMap.comp hSnd rowLengthOnesFold_tm_polytime
  simpa [Function.comp, rowTargetOnes] using hComp

def compactTargetOnesStepInputEncodedType : EncodedType :=
  EncodedType.prod rowLengthOnesAccEncodedType constraintBinaryStructuredEncodedType

def compactTargetOnesStep (p : (Nat × List Nat) × (List Int × Int)) : Nat × List Nat :=
  let rowOnes := rowLengthOnesFold p.2.1
  match binaryNatSuccLeBool (p.1.1, rowOnes.1) with
  | true => rowOnes
  | false => p.1

def compactTargetOnesFold (constraints : List (List Int × Int)) : Nat × List Nat :=
  constraints.foldl (fun acc constraint => compactTargetOnesStep (acc, constraint))
    rowLengthOnesInit

def compactTargetOnes (I : IntegerProgrammingInput) : List Nat :=
  (compactTargetOnesFold I.constraints).2

theorem compactTargetOnesStep_eq_max_replicate
    (len : Nat) (constraint : List Int × Int) :
    compactTargetOnesStep ((len, List.replicate len 1), constraint) =
      (max len constraint.1.length, List.replicate (max len constraint.1.length) 1) := by
  simp only [compactTargetOnesStep, rowLengthOnesFold_eq_length_replicate]
  by_cases hlt : len.succ ≤ constraint.1.length
  · have hMax : max len constraint.1.length = constraint.1.length := by
      exact max_eq_right (by omega)
    simp [binaryNatSuccLeBool, hlt, hMax]
  · have hMax : max len constraint.1.length = len := by
      exact max_eq_left (by omega)
    simp [binaryNatSuccLeBool, hlt, hMax]

theorem compactTargetOnesFold_eq_max
    (constraints : List (List Int × Int)) (len : Nat) :
    constraints.foldl
        (fun acc constraint => compactTargetOnesStep (acc, constraint))
        (len, List.replicate len 1) =
      (max len (constraintsVarBound constraints),
        List.replicate (max len (constraintsVarBound constraints)) 1) := by
  induction constraints generalizing len with
  | nil =>
      simp [constraintsVarBound]
  | cons constraint constraints ih =>
      rw [List.foldl_cons, compactTargetOnesStep_eq_max_replicate,
        ih (max len constraint.1.length)]
      simp [constraintsVarBound, constraintVarBound, max_assoc]

theorem compactTargetOnesFold_eq (constraints : List (List Int × Int)) :
    compactTargetOnesFold constraints =
      (constraintsVarBound constraints, List.replicate (constraintsVarBound constraints) 1) := by
  unfold compactTargetOnesFold rowLengthOnesInit
  simpa [constraintsVarBound] using compactTargetOnesFold_eq_max constraints 0

theorem compactTargetOnes_eq_replicate (I : IntegerProgrammingInput) :
    compactTargetOnes I = List.replicate (varBound I) 1 := by
  simp [compactTargetOnes, compactTargetOnesFold_eq, varBound]

theorem compactTargetOnesStep_tm_polytime :
    TMPolyTimeMap
      compactTargetOnesStepInputEncodedType
      rowLengthOnesAccEncodedType
      compactTargetOnesStep := by
  let X := compactTargetOnesStepInputEncodedType
  let A := rowLengthOnesAccEncodedType
  let P := EncodedType.prod A A
  have hAcc : TMPolyTimeMap X A
      (fun p : (Nat × List Nat) × (List Int × Int) => p.1) := by
    simpa [X, compactTargetOnesStepInputEncodedType, A] using
      TMPolyTimeMap.fst A constraintBinaryStructuredEncodedType
  have hConstraint : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun p : (Nat × List Nat) × (List Int × Int) => p.2) := by
    simpa [X, compactTargetOnesStepInputEncodedType, A] using
      TMPolyTimeMap.snd A constraintBinaryStructuredEncodedType
  have hRow : TMPolyTimeMap X intRowBinaryStructuredEncodedType
      (fun p : (Nat × List Nat) × (List Int × Int) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst intRowBinaryStructuredEncodedType EncodedType.binaryInt
    have hComp := TMPolyTimeMap.comp hFst hConstraint
    simpa [Function.comp, constraintBinaryStructuredEncodedType, X] using hComp
  have hRowOnes : TMPolyTimeMap X A
      (fun p : (Nat × List Nat) × (List Int × Int) => rowLengthOnesFold p.2.1) := by
    have hComp := TMPolyTimeMap.comp rowLengthOnesFold_tm_polytime hRow
    simpa [Function.comp, A, X] using hComp
  have hAccLen : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List Nat) × (List Int × Int) => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, rowLengthOnesAccEncodedType, A, X] using hComp
  have hRowLen : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List Nat) × (List Int × Int) => (rowLengthOnesFold p.2.1).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hRowOnes
    simpa [Function.comp, rowLengthOnesAccEncodedType, A, X] using hComp
  have hCompareInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : (Nat × List Nat) × (List Int × Int) =>
          (p.1.1, (rowLengthOnesFold p.2.1).1)) :=
    TMPolyTimeMap.prod_mk hAccLen hRowLen
  have hFlag : TMPolyTimeMap X EncodedType.bool
      (fun p : (Nat × List Nat) × (List Int × Int) =>
        binaryNatSuccLeBool (p.1.1, (rowLengthOnesFold p.2.1).1)) := by
    have hComp := TMPolyTimeMap.comp binaryNatSuccLeBool_tm_polytime hCompareInput
    simpa [Function.comp, X] using hComp
  have hPayload : TMPolyTimeMap X P
      (fun p : (Nat × List Nat) × (List Int × Int) =>
        (p.1, rowLengthOnesFold p.2.1)) :=
    TMPolyTimeMap.prod_mk hAcc hRowOnes
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool P)
        (fun p : (Nat × List Nat) × (List Int × Int) =>
          (binaryNatSuccLeBool (p.1.1, (rowLengthOnesFold p.2.1).1),
            (p.1, rowLengthOnesFold p.2.1))) :=
    TMPolyTimeMap.prod_mk hFlag hPayload
  have hFalse : TMPolyTimeMap P A (fun p : A.Carrier × A.Carrier => p.1) := by
    simpa [P, A] using TMPolyTimeMap.fst A A
  have hTrue : TMPolyTimeMap P A (fun p : A.Carrier × A.Carrier => p.2) := by
    simpa [P, A] using TMPolyTimeMap.snd A A
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool P)
        A
        (fun p : Bool × (A.Carrier × A.Carrier) =>
          match p.1 with
          | true => p.2.2
          | false => p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime P A
      (fFalse := fun p : A.Carrier × A.Carrier => p.1)
      (fTrue := fun p : A.Carrier × A.Carrier => p.2)
      hFalse hTrue
  have hOut := TMPolyTimeMap.comp hDispatch hBranchInput
  simpa [Function.comp, compactTargetOnesStep, A, P] using hOut

theorem binaryNatList_inputSize_replicate_one (n : Nat) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (List.replicate n (1 : Nat)) = 2 * n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ, EncodedType.inputSize_list_cons, ih]
      simp [EncodedType.inputSize, EncodedType.binaryNat, Nat.mul_add]
      omega

theorem rowLengthOnesFold_inputSize_le (row : List Int) :
    rowLengthOnesAccEncodedType.inputSize (rowLengthOnesFold row) ≤
      3 * intRowBinaryStructuredEncodedType.inputSize row + 1 := by
  rw [rowLengthOnesFold_eq_length_replicate]
  have hLen :
      EncodedType.binaryNat.inputSize row.length ≤
        intRowBinaryStructuredEncodedType.inputSize row := by
    exact (binaryNat_inputSize_le_self row.length).trans
      (by
        simpa [intRowBinaryStructuredEncodedType] using
          encodedList_length_le_inputSize EncodedType.binaryInt row)
  have hList :
      (EncodedType.list EncodedType.binaryNat).inputSize
          (List.replicate row.length (1 : Nat)) ≤
        2 * intRowBinaryStructuredEncodedType.inputSize row := by
    rw [binaryNatList_inputSize_replicate_one]
    have hRowLength :
        row.length ≤ intRowBinaryStructuredEncodedType.inputSize row := by
      simpa [intRowBinaryStructuredEncodedType] using
        encodedList_length_le_inputSize EncodedType.binaryInt row
    nlinarith
  simp [rowLengthOnesAccEncodedType, EncodedType.inputSize_prod]
  change
    EncodedType.binaryNat.inputSize row.length + 1 +
        (EncodedType.list EncodedType.binaryNat).inputSize
          (List.replicate row.length (1 : Nat)) ≤
      3 * intRowBinaryStructuredEncodedType.inputSize row + 1
  omega

theorem constraint_row_inputSize_le_constraint (constraint : List Int × Int) :
    intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
      constraintBinaryStructuredEncodedType.inputSize constraint := by
  simp [constraintBinaryStructuredEncodedType, EncodedType.inputSize_prod]
  omega

theorem compactTargetOnesStep_growth
    (source : List (List Int × Int)) (acc : Nat × List Nat) (constraint : List Int × Int)
    (hConstraint :
      constraintBinaryStructuredEncodedType.inputSize constraint ≤
        constraintListBinaryStructuredEncodedType.inputSize source) :
    rowLengthOnesAccEncodedType.inputSize (compactTargetOnesStep (acc, constraint)) ≤
      rowLengthOnesAccEncodedType.inputSize acc +
        ((Polynomial.C 3 * Polynomial.X + Polynomial.C 5).eval
          (constraintListBinaryStructuredEncodedType.inputSize source)) := by
  rw [compactTargetOnesStep]
  cases h :
      binaryNatSuccLeBool (acc.1, (rowLengthOnesFold constraint.1).1)
  · simp
  · have hRow := rowLengthOnesFold_inputSize_le constraint.1
    have hRowSource :
        intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
          constraintListBinaryStructuredEncodedType.inputSize source :=
      (constraint_row_inputSize_le_constraint constraint).trans hConstraint
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    nlinarith

theorem compactTargetOnesFold_tm_polytime :
    TMPolyTimeMap
      constraintListBinaryStructuredEncodedType
      rowLengthOnesAccEncodedType
      compactTargetOnesFold := by
  rcases compactTargetOnesStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        constraintListBinaryStructuredEncodedType
        rowLengthOnesAccEncodedType
        (fun constraints : List (List Int × Int) =>
          constraints.foldl
            (fun acc constraint => compactTargetOnesStep (acc, constraint))
            rowLengthOnesInit) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        constraintBinaryStructuredEncodedType rowLengthOnesAccEncodedType
        compactTargetOnesStep rowLengthOnesInit hStep
        (Polynomial.C 1) (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) ?_ ?_
    · intro constraints
      simp [rowLengthOnesInit, rowLengthOnesAccEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.binaryNat, EncodedType.list]
    · intro source acc constraint hConstraint
      exact compactTargetOnesStep_growth source acc constraint hConstraint
  simpa [compactTargetOnesFold] using hFold

theorem compactTargetOnes_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactTargetOnes := by
  have hFold :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        rowLengthOnesAccEncodedType
        (fun I : IntegerProgrammingInput => compactTargetOnesFold I.constraints) := by
    have hComp := TMPolyTimeMap.comp compactTargetOnesFold_tm_polytime
      integerProgrammingBinaryConstraints_tm_polytime
    simpa [Function.comp] using hComp
  have hSnd :
      TMPolyTimeMap rowLengthOnesAccEncodedType (EncodedType.list EncodedType.binaryNat)
        (fun acc : Nat × List Nat => acc.2) := by
    simpa [rowLengthOnesAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactTargetOnes] using hComp

end Knapsack
end Karp21
end ComplexityReduction
