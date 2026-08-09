import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryLogic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Binary-natural length folds for encoded lists.

These folds count input list elements by scanning the list structure, so later
compact Knapsack code-generation steps can build ranges/prefixes whose length is
bounded by source structure rather than by an arbitrary binary numeral.
-/

def binaryListLengthStep (X : EncodedType) (p : Nat × X.Carrier) : Nat :=
  p.1.succ

def binaryListLengthFold (X : EncodedType) (xs : List X.Carrier) : Nat :=
  xs.foldl (fun acc x => binaryListLengthStep X (acc, x)) 0

theorem binaryListLengthFold_eq_add_length
    (X : EncodedType) (xs : List X.Carrier) (acc : Nat) :
    xs.foldl (fun acc x => binaryListLengthStep X (acc, x)) acc =
      acc + xs.length := by
  induction xs generalizing acc with
  | nil =>
      simp [binaryListLengthStep]
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [binaryListLengthStep, Nat.succ_eq_add_one]
      omega

theorem binaryListLengthFold_eq_length (X : EncodedType) (xs : List X.Carrier) :
    binaryListLengthFold X xs = xs.length := by
  unfold binaryListLengthFold
  simpa using binaryListLengthFold_eq_add_length X xs 0

theorem binaryListLengthStep_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat X)
      EncodedType.binaryNat
      (binaryListLengthStep X) := by
  let P := EncodedType.prod EncodedType.binaryNat X
  have hAcc : TMPolyTimeMap P EncodedType.binaryNat (fun p : Nat × X.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst EncodedType.binaryNat X
  have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hAcc
  simpa [Function.comp, binaryListLengthStep, P] using hComp

theorem binaryListLengthStep_growth (X : EncodedType)
    (source : List X.Carrier) (acc : Nat) (x : X.Carrier) :
    EncodedType.binaryNat.inputSize (binaryListLengthStep X (acc, x)) ≤
      EncodedType.binaryNat.inputSize acc +
        ((Polynomial.X + Polynomial.C 2).eval
          ((EncodedType.list X).inputSize source)) := by
  have hAdd := binaryNatAdd_inputSize_le acc 1
  have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  simp [binaryListLengthStep, Nat.succ_eq_add_one, hOne,
    Polynomial.eval_add, Polynomial.eval_X] at hAdd ⊢
  omega

theorem binaryListLengthFold_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.list X)
      EncodedType.binaryNat
      (binaryListLengthFold X) := by
  rcases binaryListLengthStep_tm_polytime X with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      X EncodedType.binaryNat (binaryListLengthStep X) (0 : Nat) hStep
      (Polynomial.C 1) (Polynomial.X + Polynomial.C 2) ?_ ?_
  · intro xs
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  · intro source acc x _hx
    exact binaryListLengthStep_growth X source acc x

theorem binaryListLength_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.list X)
      EncodedType.binaryNat
      (fun xs : List X.Carrier => xs.length) := by
  convert binaryListLengthFold_tm_polytime X using 1
  funext xs
  exact (binaryListLengthFold_eq_length X xs).symm

theorem intRowBinaryLength_tm_polytime :
    TMPolyTimeMap
      intRowBinaryStructuredEncodedType
      EncodedType.binaryNat
      (fun row : List Int => row.length) := by
  simpa [intRowBinaryStructuredEncodedType] using
    binaryListLength_tm_polytime EncodedType.binaryInt

theorem constraintListBinaryLength_tm_polytime :
    TMPolyTimeMap
      constraintListBinaryStructuredEncodedType
      EncodedType.binaryNat
      (fun constraints : List (List Int × Int) => constraints.length) := by
  simpa [constraintListBinaryStructuredEncodedType] using
    binaryListLength_tm_polytime constraintBinaryStructuredEncodedType

theorem binaryNat_inputSize_le_self (n : Nat) :
    EncodedType.binaryNat.inputSize n ≤ n := by
  cases n with
  | zero =>
      simp [EncodedType.inputSize, EncodedType.binaryNat]
  | succ n =>
      exact binaryNat_inputSize_le_of_lt_two_pow ((Nat.succ n).lt_two_pow_self)

def constraintsVarBoundFoldStep (p : Nat × (List Int × Int)) : Nat :=
  binaryNatMax (p.1, p.2.1.length)

def constraintsVarBoundFold (constraints : List (List Int × Int)) : Nat :=
  constraints.foldl (fun acc constraint => constraintsVarBoundFoldStep (acc, constraint)) 0

theorem constraintsVarBoundFold_eq_max
    (constraints : List (List Int × Int)) (acc : Nat) :
    constraints.foldl (fun acc constraint => constraintsVarBoundFoldStep (acc, constraint))
        acc =
      max acc (constraintsVarBound constraints) := by
  induction constraints generalizing acc with
  | nil =>
      simp [constraintsVarBound]
  | cons constraint constraints ih =>
      rw [List.foldl_cons, ih]
      simp [constraintsVarBoundFoldStep, binaryNatMax, constraintsVarBound,
        constraintVarBound, max_assoc]

theorem constraintsVarBoundFold_eq_constraintsVarBound
    (constraints : List (List Int × Int)) :
    constraintsVarBoundFold constraints = constraintsVarBound constraints := by
  unfold constraintsVarBoundFold
  simpa [constraintsVarBound] using constraintsVarBoundFold_eq_max constraints 0

theorem constraintsVarBoundFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)
      EncodedType.binaryNat
      constraintsVarBoundFoldStep := by
  let X := EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType
  have hAcc : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : Nat × (List Int × Int) => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat constraintBinaryStructuredEncodedType
  have hConstraint : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun p : Nat × (List Int × Int) => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat constraintBinaryStructuredEncodedType
  have hRow : TMPolyTimeMap X intRowBinaryStructuredEncodedType
      (fun p : Nat × (List Int × Int) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst intRowBinaryStructuredEncodedType EncodedType.binaryInt
    have hComp := TMPolyTimeMap.comp hFst hConstraint
    simpa [Function.comp, constraintBinaryStructuredEncodedType, X] using hComp
  have hRowLength : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : Nat × (List Int × Int) => p.2.1.length) := by
    have hComp := TMPolyTimeMap.comp intRowBinaryLength_tm_polytime hRow
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : Nat × (List Int × Int) => (p.1, p.2.1.length)) :=
    TMPolyTimeMap.prod_mk hAcc hRowLength
  have hOut := TMPolyTimeMap.comp binaryNatMax_tm_polytime hPair
  simpa [Function.comp, constraintsVarBoundFoldStep, X] using hOut

theorem constraint_row_length_binaryNat_inputSize_le_constraint
    (constraint : List Int × Int) :
    EncodedType.binaryNat.inputSize constraint.1.length ≤
      constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hLen :
      constraint.1.length ≤ intRowBinaryStructuredEncodedType.inputSize constraint.1 := by
    simpa [intRowBinaryStructuredEncodedType] using
      encodedList_length_le_inputSize EncodedType.binaryInt constraint.1
  have hRow :
      intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
        constraintBinaryStructuredEncodedType.inputSize constraint := by
    simp [constraintBinaryStructuredEncodedType, EncodedType.inputSize_prod]
    omega
  exact (binaryNat_inputSize_le_self constraint.1.length).trans (hLen.trans hRow)

theorem constraintsVarBoundFoldStep_growth
    (source : List (List Int × Int)) (acc : Nat) (constraint : List Int × Int)
    (hConstraint :
      constraintBinaryStructuredEncodedType.inputSize constraint ≤
        constraintListBinaryStructuredEncodedType.inputSize source) :
    EncodedType.binaryNat.inputSize (constraintsVarBoundFoldStep (acc, constraint)) ≤
      EncodedType.binaryNat.inputSize acc +
        ((Polynomial.X + Polynomial.C 2).eval
          (constraintListBinaryStructuredEncodedType.inputSize source)) := by
  rw [constraintsVarBoundFoldStep, binaryNatMax_eq_lt_dispatch]
  cases hlt : binaryNatSuccLeBool (acc, constraint.1.length)
  · simp [Polynomial.eval_add, Polynomial.eval_X]
  · have hRow :=
      (constraint_row_length_binaryNat_inputSize_le_constraint constraint).trans hConstraint
    simp [Polynomial.eval_add, Polynomial.eval_X]
    omega

theorem constraintsVarBoundFold_tm_polytime :
    TMPolyTimeMap
      constraintListBinaryStructuredEncodedType
      EncodedType.binaryNat
      constraintsVarBoundFold := by
  rcases constraintsVarBoundFoldStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        constraintListBinaryStructuredEncodedType
        EncodedType.binaryNat
        (fun constraints : List (List Int × Int) =>
          constraints.foldl
            (fun acc constraint => constraintsVarBoundFoldStep (acc, constraint)) (0 : Nat)) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        constraintBinaryStructuredEncodedType EncodedType.binaryNat
        constraintsVarBoundFoldStep (0 : Nat) hStep
        (Polynomial.C 1) (Polynomial.X + Polynomial.C 2) ?_ ?_
    · intro constraints
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    · intro source acc constraint hConstraint
      exact constraintsVarBoundFoldStep_growth source acc constraint hConstraint
  simpa [constraintsVarBoundFold] using hFold

theorem constraintsVarBound_tm_polytime :
    TMPolyTimeMap
      constraintListBinaryStructuredEncodedType
      EncodedType.binaryNat
      constraintsVarBound := by
  convert constraintsVarBoundFold_tm_polytime using 1
  funext constraints
  exact (constraintsVarBoundFold_eq_constraintsVarBound constraints).symm

theorem varBound_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      varBound := by
  have hComp := TMPolyTimeMap.comp constraintsVarBound_tm_polytime
    integerProgrammingBinaryConstraints_tm_polytime
  simpa [Function.comp, varBound] using hComp

end Knapsack
end Karp21
end ComplexityReduction
