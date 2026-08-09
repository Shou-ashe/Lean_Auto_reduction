import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.SymbolList
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.Front
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct unary-to-binary natural-number bridge.

The converter scans the unary input into a raw unit list, then folds over that
list with the already verified binary successor machine.  This keeps the
encoding bridge in direct `TMPolyTimeMap` semantics.
-/

def binaryNatFromUnitStep (p : Nat × Unit) : Nat :=
  p.1.succ

def binaryNatFromUnits (xs : List Unit) : Nat :=
  xs.foldl (fun acc x => binaryNatFromUnitStep (acc, x)) 0

theorem binaryNatFromUnits_eq_length_from (xs : List Unit) (acc : Nat) :
    xs.foldl (fun acc x => binaryNatFromUnitStep (acc, x)) acc = acc + xs.length := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      change xs.foldl (fun acc x => binaryNatFromUnitStep (acc, x))
          (binaryNatFromUnitStep (acc, x)) =
        acc + (x :: xs).length
      rw [ih]
      simp [binaryNatFromUnitStep, Nat.succ_eq_add_one, Nat.add_assoc]
      omega

theorem binaryNatFromUnits_eq_length (xs : List Unit) :
    binaryNatFromUnits xs = xs.length := by
  unfold binaryNatFromUnits
  simpa using binaryNatFromUnits_eq_length_from xs 0

theorem binaryNatFromUnits_replicate (n : Nat) :
    binaryNatFromUnits (List.replicate n ()) = n := by
  simp [binaryNatFromUnits_eq_length]

theorem binaryNatFromUnitStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat (EncodedType.raw Unit))
      EncodedType.binaryNat
      binaryNatFromUnitStep := by
  let X := EncodedType.prod EncodedType.binaryNat (EncodedType.raw Unit)
  have hAcc : TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat (EncodedType.raw Unit)
  have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hAcc
  simpa [Function.comp, binaryNatFromUnitStep, X] using hComp

theorem binaryNatFromUnits_tm_polytime :
    TMPolyTimeMap rawUnitListEncodedType EncodedType.binaryNat binaryNatFromUnits := by
  rcases binaryNatFromUnitStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      (EncodedType.raw Unit) EncodedType.binaryNat
      binaryNatFromUnitStep (0 : Nat) hStep
      (Polynomial.C 0) (Polynomial.C 2) ?_ ?_
  · intro xs
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  · intro source acc x _hx
    have hSucc := binaryNatAdd_inputSize_le acc 1
    have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    simpa [binaryNatFromUnitStep, Nat.succ_eq_add_one, hOne] using hSucc

theorem unaryNatToBinaryNat_inputSize_le (n : Nat) :
    EncodedType.binaryNat.inputSize n ≤ EncodedType.nat.inputSize n := by
  have hlt : n < 2 ^ EncodedType.nat.inputSize n := by
    rw [EncodedType.inputSize_nat]
    exact n.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ n))
  exact binaryNat_inputSize_le_of_lt_two_pow hlt

theorem unaryNatToBinaryNat_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.binaryNat id := by
  have hComp :=
    TMPolyTimeMap.comp binaryNatFromUnits_tm_polytime natToRawUnitListTMBackedMap.tm_polytime
  convert hComp using 1
  funext n
  exact (binaryNatFromUnits_replicate n).symm

noncomputable def unaryNatToBinaryNatTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.binaryNat id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (LinearSizeBound.intro_with 1 0 (by
        intro n
        simpa using unaryNatToBinaryNat_inputSize_le n))
  tm_polytime := unaryNatToBinaryNat_tm_polytime

/-! ### Unary signed integers to binary signed integers -/

abbrev UnaryIntScanAcc := (Bool × Bool) × Nat

def unaryIntScanAccEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.prod EncodedType.bool EncodedType.bool) EncodedType.binaryNat

def unaryIntScanInit : UnaryIntScanAcc :=
  ((false, false), 0)

def unaryIntScanStep (p : UnaryIntScanAcc × Bool) : UnaryIntScanAcc :=
  let acc := p.1
  let b := p.2
  if acc.1.1 then
    if b then ((true, acc.1.2), acc.2.succ) else acc
  else
    ((true, b), acc.2)

def unaryIntScanToInt (acc : UnaryIntScanAcc) : Int :=
  if acc.1.2 then Int.negSucc acc.2 else Int.ofNat acc.2

def unaryIntScanAccToBinaryIntKeep :
    unaryIntScanAccEncodedType.Symbol → Option EncodedType.binaryInt.Symbol
  | some (Sum.inl (some (Sum.inr b))) => some (Sum.inl b)
  | some (Sum.inr b) => some (Sum.inr b)
  | _ => none

theorem unaryIntScanToInt_encode_filterMap (acc : unaryIntScanAccEncodedType.Carrier) :
    EncodedType.binaryInt.encode (unaryIntScanToInt acc) =
      (unaryIntScanAccEncodedType.encode acc).filterMap unaryIntScanAccToBinaryIntKeep := by
  rcases acc with ⟨⟨seen, sign⟩, payload⟩
  cases sign <;>
    simp [unaryIntScanToInt, unaryIntScanAccEncodedType, EncodedType.prod,
      EncodedType.bool, EncodedType.binaryInt, unaryIntScanAccToBinaryIntKeep]

theorem unaryIntScanToInt_tm_polytime :
    TMPolyTimeMap unaryIntScanAccEncodedType EncodedType.binaryInt unaryIntScanToInt :=
  (TMBackedCostedMap.symbolFilterMap
    unaryIntScanAccEncodedType
    EncodedType.binaryInt
    unaryIntScanToInt
    unaryIntScanAccToBinaryIntKeep
    unaryIntScanToInt_encode_filterMap).tm_polytime

theorem unaryIntScanStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod unaryIntScanAccEncodedType (finiteSymbolEncodedType Bool))
      unaryIntScanAccEncodedType
      unaryIntScanStep := by
  let B := finiteSymbolEncodedType Bool
  let A := unaryIntScanAccEncodedType
  let X := EncodedType.prod A B
  have hAcc : TMPolyTimeMap X A (fun p : A.Carrier × B.Carrier => p.1) := by
    simpa [X, A, B] using TMPolyTimeMap.fst A B
  have hBitFinite : TMPolyTimeMap X B (fun p : A.Carrier × B.Carrier => p.2) := by
    simpa [X, A, B] using TMPolyTimeMap.snd A B
  have hFiniteBool : TMPolyTimeMap B EncodedType.bool id :=
    finiteSymbol_map_tm_polytime Bool EncodedType.bool id
  have hBit : TMPolyTimeMap X EncodedType.bool (fun p : A.Carrier × B.Carrier => p.2) := by
    have hComp := TMPolyTimeMap.comp hFiniteBool hBitFinite
    simpa [Function.comp] using hComp
  have hLeftPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : A.Carrier × B.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst (EncodedType.prod EncodedType.bool EncodedType.bool)
        EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A] using hComp
  have hSeen : TMPolyTimeMap X EncodedType.bool
      (fun p : A.Carrier × B.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hLeftPair
    simpa [Function.comp] using hComp
  have hSign : TMPolyTimeMap X EncodedType.bool
      (fun p : A.Carrier × B.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hLeftPair
    simpa [Function.comp] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : A.Carrier × B.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd (EncodedType.prod EncodedType.bool EncodedType.bool)
        EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A] using hComp
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFirst :
      TMPolyTimeMap X A
        (fun p : A.Carrier × B.Carrier => ((true, p.2), p.1.2)) := by
    have hFlags :
        TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
          (fun p : A.Carrier × B.Carrier => (true, p.2)) :=
      TMPolyTimeMap.prod_mk hTrueConst hBit
    have hOut := TMPolyTimeMap.prod_mk hFlags hPayload
    simpa [A] using hOut
  have hIncrement :
      TMPolyTimeMap X A
        (fun p : A.Carrier × B.Carrier => ((true, p.1.1.2), p.1.2.succ)) := by
    have hFlags :
        TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
          (fun p : A.Carrier × B.Carrier => (true, p.1.1.2)) :=
      TMPolyTimeMap.prod_mk hTrueConst hSign
    have hSucc : TMPolyTimeMap X EncodedType.binaryNat
        (fun p : A.Carrier × B.Carrier => p.1.2.succ) := by
      have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hPayload
      simpa [Function.comp] using hComp
    have hOut := TMPolyTimeMap.prod_mk hFlags hSucc
    simpa [A] using hOut
  have hSeenStep :
      TMPolyTimeMap X A
        (fun p : A.Carrier × B.Carrier =>
          match p.2 with
          | true => ((true, p.1.1.2), p.1.2.succ)
          | false => p.1) := by
    have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2, p)) :=
      TMPolyTimeMap.prod_mk hBit (TMPolyTimeMap.id X)
    have hDispatch :=
      Clique.boolProduct_dispatch_tm_polytime X A hAcc hIncrement
    have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
    simpa [Function.comp] using hComp
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.1.1.1, p)) :=
    TMPolyTimeMap.prod_mk hSeen (TMPolyTimeMap.id X)
  have hDispatch :=
    Clique.boolProduct_dispatch_tm_polytime X A hFirst hSeenStep
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨⟨⟨seen, sign⟩, payload⟩, b⟩
  cases seen <;> cases b <;> simp [Function.comp, unaryIntScanStep] <;> rfl

theorem unaryIntScanStep_inputSize_growth
    (source : List Bool) (acc : UnaryIntScanAcc) (b : Bool)
    (_hb :
      (finiteSymbolEncodedType Bool).inputSize b ≤
        (EncodedType.list (finiteSymbolEncodedType Bool)).inputSize source) :
    unaryIntScanAccEncodedType.inputSize (unaryIntScanStep (acc, b)) ≤
      unaryIntScanAccEncodedType.inputSize acc + 2 := by
  rcases acc with ⟨⟨seen, sign⟩, payload⟩
  cases seen <;> cases b
  · simp [unaryIntScanStep, unaryIntScanAccEncodedType, EncodedType.inputSize_prod]
  · simp [unaryIntScanStep, unaryIntScanAccEncodedType, EncodedType.inputSize_prod]
  · simp [unaryIntScanStep, unaryIntScanAccEncodedType, EncodedType.inputSize_prod]
  · have hSucc := binaryNatAdd_inputSize_le payload 1
    have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    have hPayload :
        EncodedType.binaryNat.inputSize payload.succ ≤
          EncodedType.binaryNat.inputSize payload + 2 := by
      simpa [Nat.succ_eq_add_one, hOne, Nat.add_assoc] using hSucc
    simp [unaryIntScanStep, unaryIntScanAccEncodedType, EncodedType.inputSize_prod]
    omega

theorem unaryIntScan_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list (finiteSymbolEncodedType Bool))
      unaryIntScanAccEncodedType
      (fun xs : List Bool =>
        xs.foldl (fun acc b => unaryIntScanStep (acc, b)) unaryIntScanInit) := by
  rcases unaryIntScanStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      (finiteSymbolEncodedType Bool) unaryIntScanAccEncodedType
      unaryIntScanStep unaryIntScanInit hStep
      (Polynomial.C 4) (Polynomial.C 2) ?_ ?_
  · intro xs
    simp [unaryIntScanInit, unaryIntScanAccEncodedType, EncodedType.inputSize,
      EncodedType.prod, EncodedType.bool, EncodedType.binaryNat]
  · intro source acc b hb
    simpa [Polynomial.eval_C] using unaryIntScanStep_inputSize_growth source acc b hb

def unaryIntFromSymbols (xs : List Bool) : Int :=
  unaryIntScanToInt (xs.foldl (fun acc b => unaryIntScanStep (acc, b)) unaryIntScanInit)

theorem unaryIntFromTypedSymbols_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list (finiteSymbolEncodedType Bool))
      EncodedType.binaryInt
      unaryIntFromSymbols := by
  have hComp := TMPolyTimeMap.comp unaryIntScanToInt_tm_polytime unaryIntScan_tm_polytime
  simpa [Function.comp, unaryIntFromSymbols] using hComp

theorem unaryIntFromRawSymbols_tm_polytime :
    TMPolyTimeMap
      (symbolListEncodedType Bool)
      EncodedType.binaryInt
      unaryIntFromSymbols := by
  have hComp :=
    TMPolyTimeMap.comp unaryIntFromTypedSymbols_tm_polytime
      (rawSymbols_to_finiteSymbolList_tm_polytime Bool)
  simpa [Function.comp] using hComp

theorem unaryIntScan_true_replicate
    (n payload : Nat) (sign : Bool) :
    (List.replicate n true).foldl
        (fun acc b => unaryIntScanStep (acc, b)) ((true, sign), payload) =
      ((true, sign), payload + n) := by
  induction n generalizing payload with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons]
      simpa [unaryIntScanStep, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih payload.succ

theorem unaryIntScan_encode_ofNat (n : Nat) :
    (EncodedType.int.encode (Int.ofNat n)).foldl
        (fun acc b => unaryIntScanStep (acc, b)) unaryIntScanInit =
      ((true, false), n) := by
  rw [show EncodedType.int.encode (Int.ofNat n) =
      false :: List.replicate n true ++ [false] by rfl]
  change (List.replicate n true ++ [false]).foldl
      (fun acc b => unaryIntScanStep (acc, b)) ((true, false), 0) =
    ((true, false), n)
  rw [List.foldl_append]
  have hRep := unaryIntScan_true_replicate n 0 false
  simpa [unaryIntScanInit, unaryIntScanStep] using congrArg
    (fun acc => [false].foldl (fun acc b => unaryIntScanStep (acc, b)) acc) hRep

theorem unaryIntScan_encode_negSucc (n : Nat) :
    (EncodedType.int.encode (Int.negSucc n)).foldl
        (fun acc b => unaryIntScanStep (acc, b)) unaryIntScanInit =
      ((true, true), n) := by
  rw [show EncodedType.int.encode (Int.negSucc n) =
      true :: List.replicate n true ++ [false] by rfl]
  change (List.replicate n true ++ [false]).foldl
      (fun acc b => unaryIntScanStep (acc, b)) ((true, true), 0) =
    ((true, true), n)
  rw [List.foldl_append]
  have hRep := unaryIntScan_true_replicate n 0 true
  simpa [unaryIntScanInit, unaryIntScanStep] using congrArg
    (fun acc => [false].foldl (fun acc b => unaryIntScanStep (acc, b)) acc) hRep

theorem unaryIntFromSymbols_encode (z : Int) :
    unaryIntFromSymbols (EncodedType.int.encode z) = z := by
  cases z with
  | ofNat n =>
      simp only [unaryIntFromSymbols]
      rw [unaryIntScan_encode_ofNat]
      simp [unaryIntScanToInt]
  | negSucc n =>
      simp only [unaryIntFromSymbols]
      rw [unaryIntScan_encode_negSucc]
      simp [unaryIntScanToInt]

theorem unaryIntToBinaryInt_inputSize_le (z : Int) :
    EncodedType.binaryInt.inputSize z ≤ EncodedType.int.inputSize z := by
  cases z with
  | ofNat n =>
      have hNat := unaryNatToBinaryNat_inputSize_le n
      simpa [EncodedType.inputSize, EncodedType.binaryInt, EncodedType.int] using
        Nat.succ_le_succ hNat
  | negSucc n =>
      have hNat := unaryNatToBinaryNat_inputSize_le n
      simpa [EncodedType.inputSize, EncodedType.binaryInt, EncodedType.int] using
        Nat.succ_le_succ hNat

theorem unaryIntToBinaryInt_tm_polytime :
    TMPolyTimeMap EncodedType.int EncodedType.binaryInt id := by
  have hSymbols := encodedSymbols_map_tm_polytime EncodedType.int Bool id
  have hComp := TMPolyTimeMap.comp unaryIntFromRawSymbols_tm_polytime hSymbols
  convert hComp using 1
  funext z
  change z = unaryIntFromSymbols (List.map id (EncodedType.int.encode z))
  rw [List.map_id]
  exact (unaryIntFromSymbols_encode z).symm

noncomputable def unaryIntToBinaryIntTMBackedMap :
    TMBackedCostedMap EncodedType.int EncodedType.binaryInt id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (LinearSizeBound.intro_with 1 0 (by
        intro z
        simpa using unaryIntToBinaryInt_inputSize_le z))
  tm_polytime := unaryIntToBinaryInt_tm_polytime

/-! ### Unary structured Knapsack instances to binary structured Knapsack instances -/

def knapsackStructuredTupleOfInput (I : KnapsackInput) :
    knapsackTupleStructuredEncodedType.Carrier :=
  (I.items, (I.capacity, I.targetValue))

theorem knapsackStructuredTupleOfInput_encode (I : KnapsackInput) :
    knapsackTupleStructuredEncodedType.encode (knapsackStructuredTupleOfInput I) =
      knapsackStructuredEncodedType.encode I := by
  rfl

noncomputable def knapsackStructuredTupleOfInputTMBackedMap :
    TMBackedCostedMap
      knapsackStructuredEncodedType
      knapsackTupleStructuredEncodedType
      knapsackStructuredTupleOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    knapsackStructuredEncodedType
    knapsackTupleStructuredEncodedType
    knapsackStructuredTupleOfInput
    (Equiv.refl knapsackTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change
        knapsackTupleStructuredEncodedType.encode
            (knapsackStructuredTupleOfInput I) =
          (knapsackStructuredEncodedType.encode I).map id
      simp [knapsackStructuredTupleOfInput_encode])

theorem knapsackItemStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      knapsackItemStructuredEncodedType
      knapsackItemBinaryStructuredEncodedType
      id := by
  let X := knapsackItemStructuredEncodedType
  have hWeight : TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.1) := by
    have hFst : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
      simpa [X, knapsackItemStructuredEncodedType] using
        TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp unaryNatToBinaryNat_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hValue : TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.2) := by
    have hSnd : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
      simpa [X, knapsackItemStructuredEncodedType] using
        TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp unaryNatToBinaryNat_tm_polytime hSnd
    simpa [Function.comp, X] using hComp
  have hPair : TMPolyTimeMap X knapsackItemBinaryStructuredEncodedType
      (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hWeight hValue
  simpa [X, knapsackItemBinaryStructuredEncodedType, Prod.eta] using hPair

theorem knapsackItemListStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      knapsackItemListStructuredEncodedType
      knapsackItemListBinaryStructuredEncodedType
      id := by
  have hMap := TMPolyTimeMap.list_map knapsackItemStructuredToBinary_tm_polytime
  convert hMap using 1
  funext items
  exact (List.map_id items).symm

theorem knapsackBoundsStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      knapsackBoundsStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
      id := by
  let X := knapsackBoundsStructuredEncodedType
  have hCapacity :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.1) := by
    have hFst : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
      simpa [X, knapsackBoundsStructuredEncodedType] using
        TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp unaryNatToBinaryNat_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hTarget :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.2) := by
    have hSnd : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
      simpa [X, knapsackBoundsStructuredEncodedType] using
        TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp unaryNatToBinaryNat_tm_polytime hSnd
    simpa [Function.comp, X] using hComp
  have hPair : TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
      (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hCapacity hTarget
  simpa [X, knapsackBoundsBinaryStructuredEncodedType, Prod.eta] using hPair

theorem knapsackTupleStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      knapsackTupleStructuredEncodedType
      knapsackTupleBinaryStructuredEncodedType
      id := by
  let X := knapsackTupleStructuredEncodedType
  have hItems : TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    have hFst : TMPolyTimeMap X knapsackItemListStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
      simpa [X, knapsackTupleStructuredEncodedType] using
        TMPolyTimeMap.fst knapsackItemListStructuredEncodedType
          knapsackBoundsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp knapsackItemListStructuredToBinary_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hBounds : TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    have hSnd : TMPolyTimeMap X knapsackBoundsStructuredEncodedType
        (fun p : X.Carrier => p.2) := by
      simpa [X, knapsackTupleStructuredEncodedType] using
        TMPolyTimeMap.snd knapsackItemListStructuredEncodedType
          knapsackBoundsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp knapsackBoundsStructuredToBinary_tm_polytime hSnd
    simpa [Function.comp, X] using hComp
  have hPair : TMPolyTimeMap X knapsackTupleBinaryStructuredEncodedType
      (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hItems hBounds
  simpa [X, knapsackTupleBinaryStructuredEncodedType, Prod.eta] using hPair

theorem knapsackStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      id := by
  have hTupleFrom := knapsackStructuredTupleOfInputTMBackedMap.tm_polytime
  have hTuple :
      TMPolyTimeMap
        knapsackStructuredEncodedType
        knapsackTupleBinaryStructuredEncodedType
        knapsackStructuredTupleOfInput := by
    have hComp := TMPolyTimeMap.comp knapsackTupleStructuredToBinary_tm_polytime hTupleFrom
    simpa [Function.comp] using hComp
  have hOut := TMPolyTimeMap.comp knapsackBinaryTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, knapsackStructuredTupleOfInput, knapsackBinaryTupleToInput] using hOut

noncomputable def knapsackStructuredToBinaryStructuredTMKarpReduction :
    TMKarpReduction
      knapsackStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem where
  f := id
  polytime := knapsackStructuredToBinary_tm_polytime
  correct := by
    intro I
    rfl

end Knapsack
end Karp21
end ComplexityReduction
