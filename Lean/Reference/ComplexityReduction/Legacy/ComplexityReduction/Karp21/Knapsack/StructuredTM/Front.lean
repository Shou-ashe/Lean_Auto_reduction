import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part4
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part1

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Front-layer direct TM witnesses for the binary-numeric compact
0-1-IP-to-Knapsack route.

These are only the encoding-structural pieces: tuple projections/reifiers and
the fixed no-instance.  The compact arithmetic core still needs dedicated
binary arithmetic/list-fold witnesses before the full `compactMap` route can be
projected from a `TMBackedCostedReduction`.
-/

def integerProgrammingBinaryTupleOfInput (I : IntegerProgrammingInput) :
    integerProgrammingTupleBinaryStructuredEncodedType.Carrier :=
  (I.numVariables, I.constraints)

theorem integerProgrammingBinaryTupleOfInput_encode (I : IntegerProgrammingInput) :
    integerProgrammingTupleBinaryStructuredEncodedType.encode
        (integerProgrammingBinaryTupleOfInput I) =
      integerProgrammingBinaryStructuredEncodedType.encode I := by
  rfl

noncomputable def integerProgrammingBinaryTupleOfInputTMBackedMap :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      integerProgrammingTupleBinaryStructuredEncodedType
      integerProgrammingBinaryTupleOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    integerProgrammingBinaryStructuredEncodedType
    integerProgrammingTupleBinaryStructuredEncodedType
    integerProgrammingBinaryTupleOfInput
    (Equiv.refl integerProgrammingTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro I
      change
        integerProgrammingTupleBinaryStructuredEncodedType.encode
            (integerProgrammingBinaryTupleOfInput I) =
          (integerProgrammingBinaryStructuredEncodedType.encode I).map id
      simp [integerProgrammingBinaryTupleOfInput_encode])

def integerProgrammingBinaryTupleToInput
    (p : integerProgrammingTupleBinaryStructuredEncodedType.Carrier) :
    IntegerProgrammingInput where
  numVariables := p.1
  constraints := p.2

theorem integerProgrammingBinaryTupleToInput_encode
    (p : integerProgrammingTupleBinaryStructuredEncodedType.Carrier) :
    integerProgrammingBinaryStructuredEncodedType.encode
        (integerProgrammingBinaryTupleToInput p) =
      integerProgrammingTupleBinaryStructuredEncodedType.encode p := by
  rcases p with ⟨numVariables, constraints⟩
  rfl

noncomputable def integerProgrammingBinaryTupleToInputTMBackedMap :
    TMBackedCostedMap
      integerProgrammingTupleBinaryStructuredEncodedType
      integerProgrammingBinaryStructuredEncodedType
      integerProgrammingBinaryTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    integerProgrammingTupleBinaryStructuredEncodedType
    integerProgrammingBinaryStructuredEncodedType
    integerProgrammingBinaryTupleToInput
    (Equiv.refl integerProgrammingTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro p
      change
        integerProgrammingBinaryStructuredEncodedType.encode
            (integerProgrammingBinaryTupleToInput p) =
          (integerProgrammingTupleBinaryStructuredEncodedType.encode p).map id
      simp [integerProgrammingBinaryTupleToInput_encode])

theorem integerProgrammingBinaryConstraints_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      constraintListBinaryStructuredEncodedType
      (fun I : IntegerProgrammingInput => I.constraints) := by
  have hTuple :=
    integerProgrammingBinaryTupleOfInputTMBackedMap.tm_polytime
  have hConstraints :
      TMPolyTimeMap
        integerProgrammingTupleBinaryStructuredEncodedType
        constraintListBinaryStructuredEncodedType
        (fun p : integerProgrammingTupleBinaryStructuredEncodedType.Carrier => p.2) := by
    simpa [integerProgrammingTupleBinaryStructuredEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat constraintListBinaryStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hConstraints hTuple
  simpa [Function.comp, integerProgrammingBinaryTupleOfInput] using hComp

theorem integerProgrammingBinaryVariableCount_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      (fun I : IntegerProgrammingInput => I.numVariables) := by
  have hTuple :=
    integerProgrammingBinaryTupleOfInputTMBackedMap.tm_polytime
  have hVariables :
      TMPolyTimeMap
        integerProgrammingTupleBinaryStructuredEncodedType
        EncodedType.binaryNat
        (fun p : integerProgrammingTupleBinaryStructuredEncodedType.Carrier => p.1) := by
    simpa [integerProgrammingTupleBinaryStructuredEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat constraintListBinaryStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hVariables hTuple
  simpa [Function.comp, integerProgrammingBinaryTupleOfInput] using hComp

def knapsackBinaryTupleToInput
    (p : knapsackTupleBinaryStructuredEncodedType.Carrier) :
    KnapsackInput where
  items := p.1
  capacity := p.2.1
  targetValue := p.2.2

theorem knapsackBinaryTupleToInput_encode
    (p : knapsackTupleBinaryStructuredEncodedType.Carrier) :
    knapsackBinaryStructuredEncodedType.encode (knapsackBinaryTupleToInput p) =
      knapsackTupleBinaryStructuredEncodedType.encode p := by
  rcases p with ⟨items, capacity, targetValue⟩
  rfl

noncomputable def knapsackBinaryTupleToInputTMBackedMap :
    TMBackedCostedMap
      knapsackTupleBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      knapsackBinaryTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    knapsackTupleBinaryStructuredEncodedType
    knapsackBinaryStructuredEncodedType
    knapsackBinaryTupleToInput
    (Equiv.refl knapsackTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro p
      change
        knapsackBinaryStructuredEncodedType.encode
            (knapsackBinaryTupleToInput p) =
          (knapsackTupleBinaryStructuredEncodedType.encode p).map id
      simp [knapsackBinaryTupleToInput_encode])

def compactCodePairItem (code : Nat) : Nat × Nat :=
  (code, code)

theorem compactCodePairItem_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      knapsackItemBinaryStructuredEncodedType
      compactCodePairItem := by
  simpa [compactCodePairItem, knapsackItemBinaryStructuredEncodedType] using
    TMPolyTimeMap.prod_diag EncodedType.binaryNat

def compactItemsFromCodes (codes : List Nat) : List (Nat × Nat) :=
  codes.map compactCodePairItem

theorem compactItemsFromCodes_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.binaryNat)
      knapsackItemListBinaryStructuredEncodedType
      compactItemsFromCodes := by
  have hMap := TMPolyTimeMap.list_map compactCodePairItem_tm_polytime
  simpa [compactItemsFromCodes, knapsackItemListBinaryStructuredEncodedType] using hMap

theorem compactItemsFromCodes_eq_compactItems (I : IntegerProgrammingInput) :
    compactItemsFromCodes (compactItemCodes I) = compactItems I := by
  rfl

def compactTargetBounds (targetCode : Nat) : Nat × Nat :=
  (targetCode, targetCode)

theorem compactTargetBounds_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      knapsackBoundsBinaryStructuredEncodedType
      compactTargetBounds := by
  simpa [compactTargetBounds, knapsackBoundsBinaryStructuredEncodedType] using
    TMPolyTimeMap.prod_diag EncodedType.binaryNat

def compactCoreAssemblyEncodedType : EncodedType :=
  EncodedType.prod knapsackItemListBinaryStructuredEncodedType EncodedType.binaryNat

def compactCoreAssembly (p : compactCoreAssemblyEncodedType.Carrier) : KnapsackInput where
  items := p.1
  capacity := p.2
  targetValue := p.2

theorem compactCoreAssembly_eq_compactMapCore (I : IntegerProgrammingInput) :
    compactCoreAssembly (compactItems I, compactTargetCode I) = compactMapCore I := by
  rfl

theorem compactCoreAssembly_tm_polytime :
    TMPolyTimeMap
      compactCoreAssemblyEncodedType
      knapsackBinaryStructuredEncodedType
      compactCoreAssembly := by
  let X := compactCoreAssemblyEncodedType
  have hItems :
      TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, compactCoreAssemblyEncodedType] using
      TMPolyTimeMap.fst knapsackItemListBinaryStructuredEncodedType EncodedType.binaryNat
  have hTarget :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactCoreAssemblyEncodedType] using
      TMPolyTimeMap.snd knapsackItemListBinaryStructuredEncodedType EncodedType.binaryNat
  have hBounds :
      TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
        (fun p : X.Carrier => compactTargetBounds p.2) := by
    have hComp := TMPolyTimeMap.comp compactTargetBounds_tm_polytime hTarget
    simpa [Function.comp, compactTargetBounds, X] using hComp
  have hTuple :
      TMPolyTimeMap X knapsackTupleBinaryStructuredEncodedType
        (fun p : X.Carrier => (p.1, compactTargetBounds p.2)) :=
    TMPolyTimeMap.prod_mk hItems hBounds
  have hInput := TMPolyTimeMap.comp knapsackBinaryTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, knapsackBinaryTupleToInput, compactCoreAssembly,
    compactTargetBounds, X] using hInput

noncomputable def compactCoreAssemblyTMBackedMap :
    TMBackedCostedMap
      compactCoreAssemblyEncodedType
      knapsackBinaryStructuredEncodedType
      compactCoreAssembly where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.intro_with 1 3 3 (by
        intro p
        rcases p with ⟨items, targetCode⟩
        simp [compactCoreAssemblyEncodedType, compactCoreAssembly,
          knapsackBinaryStructured_inputSize_eq, EncodedType.inputSize_prod]
        omega))
  tm_polytime := compactCoreAssembly_tm_polytime

theorem compactMapCore_tm_polytime_of_code_witnesses
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMapCore := by
  have hItems :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        knapsackItemListBinaryStructuredEncodedType
        compactItems := by
    have hComp := TMPolyTimeMap.comp compactItemsFromCodes_tm_polytime hCodes
    simpa [Function.comp, compactItemsFromCodes] using hComp
  have hPair :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        compactCoreAssemblyEncodedType
        (fun I : IntegerProgrammingInput => (compactItems I, compactTargetCode I)) :=
    TMPolyTimeMap.prod_mk hItems hTarget
  have hOut := TMPolyTimeMap.comp compactCoreAssembly_tm_polytime hPair
  simpa [Function.comp, compactCoreAssembly, compactMapCore,
    compactCoreAssemblyEncodedType] using hOut

noncomputable def compactConstraintBoundsNonnegativeBool (I : IntegerProgrammingInput) :
    Bool := by
  classical
  exact if compactConstraintBoundsNonnegative I then true else false

theorem compactConstraintBoundsNonnegativeBool_eq_true_iff
    (I : IntegerProgrammingInput) :
    compactConstraintBoundsNonnegativeBool I = true ↔
      compactConstraintBoundsNonnegative I := by
  classical
  unfold compactConstraintBoundsNonnegativeBool
  by_cases hBounds : compactConstraintBoundsNonnegative I <;> simp [hBounds]

noncomputable def compactConstraintBoundNonnegativeBool (constraint : List Int × Int) :
    Bool := by
  classical
  exact if compactConstraintBoundNonnegative constraint then true else false

theorem compactConstraintBoundNonnegativeBool_eq_true_iff
    (constraint : List Int × Int) :
    compactConstraintBoundNonnegativeBool constraint = true ↔
      compactConstraintBoundNonnegative constraint := by
  classical
  unfold compactConstraintBoundNonnegativeBool
  by_cases hBound : compactConstraintBoundNonnegative constraint <;> simp [hBound]

noncomputable def intNatAddNonnegativeBool (p : Int × Nat) : Bool := by
  classical
  exact if 0 ≤ p.1 + (p.2 : Int) then true else false

theorem intNatAddNonnegativeBool_eq_compactConstraintBoundNonnegativeBool
    (constraint : List Int × Int) :
    intNatAddNonnegativeBool (constraint.2, rowNegativeShift constraint.1) =
      compactConstraintBoundNonnegativeBool constraint := by
  classical
  unfold intNatAddNonnegativeBool compactConstraintBoundNonnegativeBool
    compactConstraintBoundNonnegative
  by_cases hBound : 0 ≤ constraint.2 + (rowNegativeShift constraint.1 : Int) <;>
    simp [hBound]

theorem compactConstraintBoundNonnegativeBool_tm_polytime_of_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hIntNatNonnegative :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        EncodedType.bool
        intNatAddNonnegativeBool) :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      EncodedType.bool
      compactConstraintBoundNonnegativeBool := by
  let X := constraintBinaryStructuredEncodedType
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
      TMPolyTimeMap X EncodedType.binaryNat
        (fun constraint : List Int × Int => rowNegativeShift constraint.1) := by
    have hComp := TMPolyTimeMap.comp hRowShift hRow
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        (fun constraint : List Int × Int =>
          (constraint.2, rowNegativeShift constraint.1)) :=
    TMPolyTimeMap.prod_mk hBound hShift
  have hOut := TMPolyTimeMap.comp hIntNatNonnegative hPair
  convert hOut using 1
  funext constraint
  exact (intNatAddNonnegativeBool_eq_compactConstraintBoundNonnegativeBool constraint).symm

def boolListAnd (xs : List Bool) : Bool :=
  xs.foldl (fun acc x => Clique.boolAndPair (acc, x)) true

theorem boolListAnd_foldl_eq_true_iff (xs : List Bool) (acc : Bool) :
    xs.foldl (fun acc x => Clique.boolAndPair (acc, x)) acc = true ↔
      acc = true ∧ ∀ x ∈ xs, x = true := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      change
        xs.foldl (fun acc x => Clique.boolAndPair (acc, x))
            (Clique.boolAndPair (acc, x)) = true ↔
          acc = true ∧ ∀ y ∈ x :: xs, y = true
      rw [ih (Clique.boolAndPair (acc, x))]
      constructor
      · rintro ⟨hHead, hTail⟩
        have hAccX : acc = true ∧ x = true := by
          cases acc <;> cases x <;> simp [Clique.boolAndPair] at hHead ⊢
        refine ⟨hAccX.1, ?_⟩
        intro y hy
        cases hy with
        | head =>
            simpa using hAccX.2
        | tail _ hyTail =>
            exact hTail y hyTail
      · rintro ⟨hAcc, hAll⟩
        constructor
        · have hx : x = true := hAll x (by simp)
          cases acc <;> cases x <;> simp [Clique.boolAndPair] at hAcc hx ⊢
        · intro y hy
          exact hAll y (List.mem_cons_of_mem x hy)

theorem boolListAnd_eq_true_iff (xs : List Bool) :
    boolListAnd xs = true ↔ ∀ x ∈ xs, x = true := by
  simpa [boolListAnd] using boolListAnd_foldl_eq_true_iff xs true

theorem boolListAnd_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.bool)
      EncodedType.bool
      boolListAnd := by
  rcases Clique.boolAndPair_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.bool EncodedType.bool Clique.boolAndPair true hStep
      (Polynomial.C 1) (Polynomial.C 1) ?_ ?_
  · intro xs
    simp
  · intro source acc x _hx
    simp [Clique.boolAndPair]

noncomputable def compactConstraintBoundsNonnegativeFromListBool
    (constraints : List (List Int × Int)) : Bool :=
  boolListAnd (constraints.map compactConstraintBoundNonnegativeBool)

theorem compactConstraintBoundsNonnegativeFromListBool_eq_true_iff
    (constraints : List (List Int × Int)) :
    compactConstraintBoundsNonnegativeFromListBool constraints = true ↔
      ∀ constraint ∈ constraints, compactConstraintBoundNonnegative constraint := by
  rw [compactConstraintBoundsNonnegativeFromListBool, boolListAnd_eq_true_iff]
  constructor
  · intro hAll constraint hConstraint
    have hBool :
        compactConstraintBoundNonnegativeBool constraint = true :=
      hAll (compactConstraintBoundNonnegativeBool constraint)
        (List.mem_map.mpr ⟨constraint, hConstraint, rfl⟩)
    exact (compactConstraintBoundNonnegativeBool_eq_true_iff constraint).1 hBool
  · intro hAll b hb
    rcases List.mem_map.mp hb with ⟨constraint, hConstraint, rfl⟩
    exact (compactConstraintBoundNonnegativeBool_eq_true_iff constraint).2
      (hAll constraint hConstraint)

theorem compactConstraintBoundsNonnegativeFromListBool_eq
    (I : IntegerProgrammingInput) :
    compactConstraintBoundsNonnegativeFromListBool I.constraints =
      compactConstraintBoundsNonnegativeBool I := by
  by_cases hBounds : compactConstraintBoundsNonnegative I
  · have hInput :
        compactConstraintBoundsNonnegativeBool I = true :=
      (compactConstraintBoundsNonnegativeBool_eq_true_iff I).2 hBounds
    have hList :
        compactConstraintBoundsNonnegativeFromListBool I.constraints = true :=
      (compactConstraintBoundsNonnegativeFromListBool_eq_true_iff I.constraints).2
        hBounds
    rw [hList, hInput]
  · have hInput :
        compactConstraintBoundsNonnegativeBool I = false := by
      cases hValue : compactConstraintBoundsNonnegativeBool I
      · rfl
      · exact False.elim
          (hBounds ((compactConstraintBoundsNonnegativeBool_eq_true_iff I).1 hValue))
    have hList :
        compactConstraintBoundsNonnegativeFromListBool I.constraints = false := by
      cases hValue : compactConstraintBoundsNonnegativeFromListBool I.constraints
      · rfl
      · exact False.elim
          (hBounds
            ((compactConstraintBoundsNonnegativeFromListBool_eq_true_iff I.constraints).1
              hValue))
    rw [hList, hInput]

theorem compactConstraintBoundsNonnegativeBool_tm_polytime_of_constraint_witness
    (hConstraint :
      TMPolyTimeMap
        constraintBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundNonnegativeBool) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.bool
      compactConstraintBoundsNonnegativeBool := by
  have hConstraintBools :
      TMPolyTimeMap
        constraintListBinaryStructuredEncodedType
        (EncodedType.list EncodedType.bool)
        (fun constraints : List (List Int × Int) =>
          constraints.map compactConstraintBoundNonnegativeBool) :=
    TMPolyTimeMap.list_map hConstraint
  have hAll :
      TMPolyTimeMap
        constraintListBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundsNonnegativeFromListBool := by
    have hComp := TMPolyTimeMap.comp boolListAnd_tm_polytime hConstraintBools
    simpa [Function.comp, compactConstraintBoundsNonnegativeFromListBool] using hComp
  have hInput := TMPolyTimeMap.comp hAll integerProgrammingBinaryConstraints_tm_polytime
  convert hInput using 1
  funext I
  exact (compactConstraintBoundsNonnegativeFromListBool_eq I).symm

theorem compactConstraintBoundsNonnegativeBool_tm_polytime_of_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hIntNatNonnegative :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        EncodedType.bool
        intNatAddNonnegativeBool) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.bool
      compactConstraintBoundsNonnegativeBool :=
  compactConstraintBoundsNonnegativeBool_tm_polytime_of_constraint_witness
    (compactConstraintBoundNonnegativeBool_tm_polytime_of_arithmetic_witnesses
      hRowShift hIntNatNonnegative)

theorem compactMap_tm_polytime_of_guard_and_core_witnesses
    (hGuard :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundsNonnegativeBool)
    (hCore :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        knapsackBinaryStructuredEncodedType
        compactMapCore) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap := by
  let X := integerProgrammingBinaryStructuredEncodedType
  let Y := knapsackBinaryStructuredEncodedType
  have hNo :
      TMPolyTimeMap X Y (fun _ : IntegerProgrammingInput => compactNoKnapsackInput) := by
    simpa [X, Y] using
      (TMBackedCostedMap.const X Y compactNoKnapsackInput).tm_polytime
  have hInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : IntegerProgrammingInput => (compactConstraintBoundsNonnegativeBool I, I)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        Y
        (fun p : Bool × IntegerProgrammingInput =>
          match p.1 with
          | true => compactMapCore p.2
          | false => compactNoKnapsackInput) :=
    Clique.boolProduct_dispatch_tm_polytime X Y
      (fFalse := fun _ : IntegerProgrammingInput => compactNoKnapsackInput)
      (fTrue := compactMapCore)
      hNo hCore
  have hComp := TMPolyTimeMap.comp hDispatch hInput
  convert hComp using 1
  funext I
  by_cases hBounds : compactConstraintBoundsNonnegative I
  · have hBool : compactConstraintBoundsNonnegativeBool I = true :=
      (compactConstraintBoundsNonnegativeBool_eq_true_iff I).2 hBounds
    simp [Function.comp, compactMap, hBounds, hBool]
  · have hBool : compactConstraintBoundsNonnegativeBool I = false := by
      cases hValue : compactConstraintBoundsNonnegativeBool I
      · rfl
      · exact False.elim
          (hBounds ((compactConstraintBoundsNonnegativeBool_eq_true_iff I).1 hValue))
    simp [Function.comp, compactMap, hBounds, hBool]

theorem compactMap_tm_polytime_of_guard_and_code_witnesses
    (hGuard :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundsNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMap_tm_polytime_of_guard_and_core_witnesses hGuard
    (compactMapCore_tm_polytime_of_code_witnesses hCodes hTarget)

theorem compactMap_tm_polytime_of_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hIntNatNonnegative :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        EncodedType.bool
        intNatAddNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMap_tm_polytime_of_guard_and_code_witnesses
    (compactConstraintBoundsNonnegativeBool_tm_polytime_of_arithmetic_witnesses
      hRowShift hIntNatNonnegative)
    hCodes hTarget

noncomputable def compactMapTMBackedMap_of_guard_and_code_witnesses
    (hGuard :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundsNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      zeroOneIPToKnapsackCompactBinaryStructured_polynomialSizeBound
  tm_polytime :=
    compactMap_tm_polytime_of_guard_and_code_witnesses hGuard hCodes hTarget

noncomputable def zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_witnesses
    (hGuard :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.bool
        compactConstraintBoundsNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedReduction
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (compactMapTMBackedMap_of_guard_and_code_witnesses hGuard hCodes hTarget)
    (by
      intro I
      simpa [zeroOneIntegerProgrammingBinaryStructuredDecisionProblem,
        integerProgrammingBinaryStructuredDecisionProblem,
        knapsackBinaryStructuredDecisionProblem] using compactMap_correct I)

noncomputable def compactMapTMBackedMap_of_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hIntNatNonnegative :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        EncodedType.bool
        intNatAddNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMapTMBackedMap_of_guard_and_code_witnesses
    (compactConstraintBoundsNonnegativeBool_tm_polytime_of_arithmetic_witnesses
      hRowShift hIntNatNonnegative)
    hCodes hTarget

noncomputable def zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hIntNatNonnegative :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
        EncodedType.bool
        intNatAddNonnegativeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedReduction
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_witnesses
    (compactConstraintBoundsNonnegativeBool_tm_polytime_of_arithmetic_witnesses
      hRowShift hIntNatNonnegative)
    hCodes hTarget

theorem compactNoKnapsackInput_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      (fun _ : IntegerProgrammingInput => compactNoKnapsackInput) :=
  (TMBackedCostedMap.const
    integerProgrammingBinaryStructuredEncodedType
    knapsackBinaryStructuredEncodedType
    compactNoKnapsackInput).tm_polytime

noncomputable def compactNoKnapsackInputTMBackedMap :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      (fun _ : IntegerProgrammingInput => compactNoKnapsackInput) :=
  TMBackedCostedMap.const
    integerProgrammingBinaryStructuredEncodedType
    knapsackBinaryStructuredEncodedType
    compactNoKnapsackInput

end Knapsack
end Karp21
end ComplexityReduction
