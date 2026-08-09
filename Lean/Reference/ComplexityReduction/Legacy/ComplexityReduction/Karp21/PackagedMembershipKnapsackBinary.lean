/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryLogic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful binary-structured Knapsack.

The certificate is a finite Boolean selection list.  Missing positions default to
`false`, matching the finite-assignment convention used by the SAT verifier.
The verifier accumulates selected weights and values with `binaryNat` arithmetic.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace Knapsack

abbrev knapsackBinaryCertificateEncodedType : EncodedType :=
  SAT.finiteAssignmentCertEncodedType

abbrev KnapsackBinaryCertificate := List Bool

/-! ### Binary projections and comparison -/

def knapsackBinaryItemsForMembership (I : KnapsackInput) : List (Nat × Nat) :=
  I.items

theorem knapsackBinaryItems_encode_filterMap (I : KnapsackInput) :
    knapsackItemListBinaryStructuredEncodedType.encode
        (knapsackBinaryItemsForMembership I) =
      (knapsackBinaryStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodLeftSymbol
          knapsackItemListBinaryStructuredEncodedType.Symbol
          knapsackBoundsBinaryStructuredEncodedType.Symbol) := by
  simpa [knapsackBinaryItemsForMembership, knapsackBinaryStructuredEncodedType,
    knapsackTupleBinaryStructuredEncodedType] using
    (EncodedType.prod_left_filter_encode
      knapsackItemListBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
      (I.items, (I.capacity, I.targetValue))).symm

noncomputable def knapsackBinaryItemsTMBackedMap :
    TMBackedCostedMap
      knapsackBinaryStructuredEncodedType
      knapsackItemListBinaryStructuredEncodedType
      knapsackBinaryItemsForMembership :=
  TMBackedCostedMap.symbolFilterMap
    knapsackBinaryStructuredEncodedType knapsackItemListBinaryStructuredEncodedType
    knapsackBinaryItemsForMembership
    (@EncodedType.prodLeftSymbol
      knapsackItemListBinaryStructuredEncodedType.Symbol
      knapsackBoundsBinaryStructuredEncodedType.Symbol)
    knapsackBinaryItems_encode_filterMap

def knapsackBinaryBoundsForMembership (I : KnapsackInput) : Nat × Nat :=
  (I.capacity, I.targetValue)

theorem knapsackBinaryBounds_encode_filterMap (I : KnapsackInput) :
    knapsackBoundsBinaryStructuredEncodedType.encode
        (knapsackBinaryBoundsForMembership I) =
      (knapsackBinaryStructuredEncodedType.encode I).filterMap
        (@EncodedType.prodRightSymbol
          knapsackItemListBinaryStructuredEncodedType.Symbol
          knapsackBoundsBinaryStructuredEncodedType.Symbol) := by
  simpa [knapsackBinaryBoundsForMembership, knapsackBinaryStructuredEncodedType,
    knapsackTupleBinaryStructuredEncodedType] using
    (EncodedType.prod_right_filter_encode
      knapsackItemListBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
      (I.items, (I.capacity, I.targetValue))).symm

noncomputable def knapsackBinaryBoundsTMBackedMap :
    TMBackedCostedMap
      knapsackBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
      knapsackBinaryBoundsForMembership :=
  TMBackedCostedMap.symbolFilterMap
    knapsackBinaryStructuredEncodedType knapsackBoundsBinaryStructuredEncodedType
    knapsackBinaryBoundsForMembership
    (@EncodedType.prodRightSymbol
      knapsackItemListBinaryStructuredEncodedType.Symbol
      knapsackBoundsBinaryStructuredEncodedType.Symbol)
    knapsackBinaryBounds_encode_filterMap

def binaryNatLeBool (p : Nat × Nat) : Bool :=
  binaryNatSuccLeBool (p.1, p.2.succ)

theorem binaryNatLeBool_eq_true_iff (p : Nat × Nat) :
    binaryNatLeBool p = true ↔ p.1 ≤ p.2 := by
  rcases p with ⟨a, b⟩
  simp [binaryNatLeBool, binaryNatSuccLeBool]

theorem binaryNatLeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.bool
      binaryNatLeBool := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hLeft : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hRight : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hRightSucc :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.2.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hRight
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : Nat × Nat => (p.1, p.2.succ)) :=
    TMPolyTimeMap.prod_mk hLeft hRightSucc
  have hComp := TMPolyTimeMap.comp binaryNatSuccLeBool_tm_polytime hPair
  simpa [Function.comp, binaryNatLeBool, X] using hComp

/-! ### Semantic finite-certificate sums -/

def selectedWeightFrom : List (Nat × Nat) → KnapsackBinaryCertificate → Nat → Nat
  | [], _, _ => 0
  | item :: items, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then item.1 else 0) +
        selectedWeightFrom items bits (idx + 1)

def selectedValueFrom : List (Nat × Nat) → KnapsackBinaryCertificate → Nat → Nat
  | [], _, _ => 0
  | item :: items, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then item.2 else 0) +
        selectedValueFrom items bits (idx + 1)

def selectionFrom : List (Nat × Nat) → KnapsackBinaryCertificate → Nat → List Bool
  | [], _, _ => []
  | _ :: items, bits, idx =>
      SAT.lookupBoolAt (bits, idx) :: selectionFrom items bits (idx + 1)

@[simp] theorem selectionFrom_length
    (items : List (Nat × Nat)) (bits : KnapsackBinaryCertificate) (idx : Nat) :
    (selectionFrom items bits idx).length = items.length := by
  induction items generalizing idx with
  | nil =>
      simp [selectionFrom]
  | cons item items ih =>
      simp [selectionFrom, ih]

theorem selectedWeightFrom_eq_selectedWeight_selectionFrom
    (items : List (Nat × Nat)) (bits : KnapsackBinaryCertificate) (idx capacity target : Nat) :
    selectedWeightFrom items bits idx =
      selectedWeight { items := items, capacity := capacity, targetValue := target }
        (selectionFrom items bits idx) := by
  induction items generalizing idx with
  | nil =>
      simp [selectedWeightFrom, selectionFrom, selectedWeight]
  | cons item items ih =>
      simp [selectedWeightFrom, selectionFrom, selectedWeight, ih]

theorem selectedValueFrom_eq_selectedValue_selectionFrom
    (items : List (Nat × Nat)) (bits : KnapsackBinaryCertificate) (idx capacity target : Nat) :
    selectedValueFrom items bits idx =
      selectedValue { items := items, capacity := capacity, targetValue := target }
        (selectionFrom items bits idx) := by
  induction items generalizing idx with
  | nil =>
      simp [selectedValueFrom, selectionFrom, selectedValue]
  | cons item items ih =>
      simp [selectedValueFrom, selectionFrom, selectedValue, ih]

@[simp] theorem lookup_cons_zero (b : Bool) (bits : List Bool) :
    SAT.lookupBoolAt (b :: bits, 0) = b := by
  simp [SAT.lookupBoolAt_eq_getD]

@[simp] theorem lookup_cons_succ (b : Bool) (bits : List Bool) (idx : Nat) :
    SAT.lookupBoolAt (b :: bits, idx + 1) = SAT.lookupBoolAt (bits, idx) := by
  simp [SAT.lookupBoolAt_eq_getD]

theorem selectionFrom_cons_succ
    (items : List (Nat × Nat)) (b : Bool) (bits : List Bool) (idx : Nat) :
    selectionFrom items (b :: bits) (idx + 1) = selectionFrom items bits idx := by
  induction items generalizing idx with
  | nil =>
      simp [selectionFrom]
  | cons item items ih =>
      simp [selectionFrom, ih]

theorem selectionFrom_self_of_length
    (items : List (Nat × Nat)) (selected : List Bool)
    (hLen : selected.length = items.length) :
    selectionFrom items selected 0 = selected := by
  induction items generalizing selected with
  | nil =>
      have hNil : selected = [] := by
        cases selected with
        | nil => rfl
        | cons b bs => simp at hLen
      simp [selectionFrom, hNil]
  | cons item items ih =>
      cases selected with
      | nil =>
          simp at hLen
      | cons b bs =>
          have hTail : bs.length = items.length := by simpa using hLen
          have hRec : selectionFrom items (b :: bs) 1 = bs := by
            rw [show (1 : Nat) = 0 + 1 by rfl]
            rw [selectionFrom_cons_succ]
            exact ih bs hTail
          simp [selectionFrom, hRec]

/-! ### Instruction-list runner for direct TM verification -/

def foldInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod knapsackBinaryCertificateEncodedType
      knapsackItemBinaryStructuredEncodedType)

def foldInstructionListEncodedType : EncodedType :=
  EncodedType.list foldInstructionEncodedType

def foldInputEncodedType : EncodedType :=
  EncodedType.prod knapsackItemListBinaryStructuredEncodedType
    knapsackBinaryCertificateEncodedType

def foldAccEncodedType : EncodedType :=
  EncodedType.prod knapsackBinaryCertificateEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat))

abbrev FoldInstruction := Bool × (KnapsackBinaryCertificate × (Nat × Nat))

abbrev FoldAcc := KnapsackBinaryCertificate × (Nat × (Nat × Nat))

def foldInitInstruction (bits : KnapsackBinaryCertificate) : FoldInstruction :=
  (false, (bits, (0, 0)))

def foldItemInstruction (item : Nat × Nat) : FoldInstruction :=
  (true, ([], item))

def foldInstructions
    (p : List (Nat × Nat) × KnapsackBinaryCertificate) :
    List FoldInstruction :=
  foldInitInstruction p.2 :: p.1.map foldItemInstruction

def foldRunnerInit : FoldAcc :=
  ([], (0, (0, 0)))

def foldStep (p : FoldAcc × FoldInstruction) : FoldAcc :=
  if p.2.1 then
    let bits := p.1.1
    let idx := p.1.2.1
    let weight := p.1.2.2.1
    let value := p.1.2.2.2
    let item := p.2.2.2
    if SAT.lookupBoolAt (bits, idx) then
      (bits, (idx + 1, (weight + item.1, value + item.2)))
    else
      (bits, (idx + 1, (weight, value)))
  else
    (p.2.2.1, (0, (0, 0)))

def foldFromInstructions (xs : List FoldInstruction) : Nat × Nat :=
  ((xs.foldl (fun acc x => foldStep (acc, x)) foldRunnerInit).2).2

def certificateSums (p : List (Nat × Nat) × KnapsackBinaryCertificate) : Nat × Nat :=
  foldFromInstructions (foldInstructions p)

theorem foldElementInstructions_fold_eq_sums
    (items : List (Nat × Nat)) (bits : KnapsackBinaryCertificate)
    (idx weight value : Nat) :
    ((items.map foldItemInstruction).foldl
        (fun acc instr => foldStep (acc, instr))
        (bits, (idx, (weight, value)))) =
      (bits,
        (idx + items.length,
          (weight + selectedWeightFrom items bits idx,
            value + selectedValueFrom items bits idx))) := by
  induction items generalizing idx weight value with
  | nil =>
      simp [selectedWeightFrom, selectedValueFrom]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      rw [List.map_cons, List.foldl_cons]
      cases hBit : SAT.lookupBoolAt (bits, idx)
      · simp [foldItemInstruction, foldStep, hBit]
        have h := ih (idx + 1) weight value
        simpa [foldStep, hBit, selectedWeightFrom, selectedValueFrom,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      · simp [foldItemInstruction, foldStep, hBit]
        have h := ih (idx + 1) (weight + w) (value + v)
        simpa [foldStep, hBit, selectedWeightFrom, selectedValueFrom,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem certificateSums_eq_weightValueFrom
    (p : List (Nat × Nat) × KnapsackBinaryCertificate) :
    certificateSums p =
      (selectedWeightFrom p.1 p.2 0, selectedValueFrom p.1 p.2 0) := by
  rcases p with ⟨items, bits⟩
  change
    (((foldInitInstruction bits :: items.map foldItemInstruction).foldl
        (fun acc instr => foldStep (acc, instr)) foldRunnerInit).2).2 =
      (selectedWeightFrom items bits 0, selectedValueFrom items bits 0)
  rw [List.foldl_cons]
  have hFold := foldElementInstructions_fold_eq_sums items bits 0 0 0
  have hSums := congrArg (fun acc : FoldAcc => acc.2.2) hFold
  simpa [foldRunnerInit, foldInitInstruction, foldStep] using hSums

theorem foldInitInstruction_tm_polytime :
    TMPolyTimeMap
      knapsackBinaryCertificateEncodedType
      foldInstructionEncodedType
      foldInitInstruction := by
  have hFalse :
      TMPolyTimeMap knapsackBinaryCertificateEncodedType EncodedType.bool
        (fun _ : KnapsackBinaryCertificate => false) :=
    TMPolyTimeMap.const knapsackBinaryCertificateEncodedType EncodedType.bool false
  have hBits :
      TMPolyTimeMap knapsackBinaryCertificateEncodedType
        knapsackBinaryCertificateEncodedType id :=
    TMPolyTimeMap.id knapsackBinaryCertificateEncodedType
  have hDummy :
      TMPolyTimeMap knapsackBinaryCertificateEncodedType
        knapsackItemBinaryStructuredEncodedType
        (fun _ : KnapsackBinaryCertificate => ((0, 0) : Nat × Nat)) :=
    TMPolyTimeMap.const knapsackBinaryCertificateEncodedType
      knapsackItemBinaryStructuredEncodedType ((0, 0) : Nat × Nat)
  have hPayload :
      TMPolyTimeMap knapsackBinaryCertificateEncodedType
        (EncodedType.prod knapsackBinaryCertificateEncodedType
          knapsackItemBinaryStructuredEncodedType)
        (fun bits : KnapsackBinaryCertificate => (bits, ((0, 0) : Nat × Nat))) :=
    TMPolyTimeMap.prod_mk hBits hDummy
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [foldInitInstruction, foldInstructionEncodedType] using hOut

theorem foldItemInstruction_tm_polytime :
    TMPolyTimeMap
      knapsackItemBinaryStructuredEncodedType
      foldInstructionEncodedType
      foldItemInstruction := by
  have hTrue :
      TMPolyTimeMap knapsackItemBinaryStructuredEncodedType EncodedType.bool
        (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const knapsackItemBinaryStructuredEncodedType EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap knapsackItemBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
        (fun _ : Nat × Nat => ([] : KnapsackBinaryCertificate)) :=
    TMPolyTimeMap.const knapsackItemBinaryStructuredEncodedType
      knapsackBinaryCertificateEncodedType []
  have hItem :
      TMPolyTimeMap knapsackItemBinaryStructuredEncodedType
        knapsackItemBinaryStructuredEncodedType id :=
    TMPolyTimeMap.id knapsackItemBinaryStructuredEncodedType
  have hPayload :
      TMPolyTimeMap knapsackItemBinaryStructuredEncodedType
        (EncodedType.prod knapsackBinaryCertificateEncodedType
          knapsackItemBinaryStructuredEncodedType)
        (fun item : Nat × Nat => (([] : KnapsackBinaryCertificate), item)) :=
    TMPolyTimeMap.prod_mk hEmpty hItem
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [foldItemInstruction, foldInstructionEncodedType] using hOut

theorem foldInstructions_tm_polytime :
    TMPolyTimeMap
      foldInputEncodedType
      foldInstructionListEncodedType
      foldInstructions := by
  let X := foldInputEncodedType
  have hItems :
      TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, foldInputEncodedType] using
      TMPolyTimeMap.fst knapsackItemListBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hBits :
      TMPolyTimeMap X knapsackBinaryCertificateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, foldInputEncodedType] using
      TMPolyTimeMap.snd knapsackItemListBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hInit :
      TMPolyTimeMap X foldInstructionEncodedType
        (fun p : X.Carrier => foldInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp foldInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X foldInstructionListEncodedType
        (fun p : X.Carrier => [foldInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton foldInstructionEncodedType) hInit
    simpa [Function.comp, foldInstructionListEncodedType, X] using hComp
  have hItemInstructions :
      TMPolyTimeMap X foldInstructionListEncodedType
        (fun p : X.Carrier => p.1.map foldItemInstruction) := by
    have hMap := TMPolyTimeMap.list_map foldItemInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hItems
    simpa [Function.comp, foldInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod foldInstructionListEncodedType foldInstructionListEncodedType)
        (fun p : X.Carrier => ([foldInitInstruction p.2],
          p.1.map foldItemInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hItemInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append foldInstructionEncodedType) hAppendInput
  simpa [Function.comp, foldInstructions, foldInstructionListEncodedType, X] using hOut

theorem foldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod foldAccEncodedType foldInstructionEncodedType)
      foldAccEncodedType
      foldStep := by
  let X := EncodedType.prod foldAccEncodedType foldInstructionEncodedType
  let A := foldAccEncodedType
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  let Payload := EncodedType.prod knapsackBinaryCertificateEncodedType
    knapsackItemBinaryStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A foldInstructionEncodedType
  have hInstr : TMPolyTimeMap X foldInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A foldInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, foldInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, foldInstructionEncodedType, Payload, X] using hComp
  have hAccBits : TMPolyTimeMap X knapsackBinaryCertificateEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst knapsackBinaryCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccRest : TMPolyTimeMap X Rest (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd knapsackBinaryCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hAccRest
    simpa [Function.comp, Rest, X] using hComp
  have hAccSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hSnd hAccRest
    simpa [Function.comp, Rest, X] using hComp
  have hAccWeight : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hAccSums
    simpa [Function.comp, X] using hComp
  have hAccValue : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hAccSums
    simpa [Function.comp, X] using hComp
  have hPayloadBits : TMPolyTimeMap X knapsackBinaryCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst knapsackBinaryCertificateEncodedType
      knapsackItemBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadItem : TMPolyTimeMap X knapsackItemBinaryStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd knapsackBinaryCertificateEncodedType
      knapsackItemBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadWeight : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hPayloadItem
    simpa [Function.comp, knapsackItemBinaryStructuredEncodedType, X] using hComp
  have hPayloadValue : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hPayloadItem
    simpa [Function.comp, knapsackItemBinaryStructuredEncodedType, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X SAT.lookupBoolInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hAccBits hAccIdx
  have hLookup :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => SAT.lookupBoolAt (p.1.1, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp SAT.lookupBoolAt_tm_polytime hLookupInput
    simpa [Function.comp, SAT.lookupBoolInputEncodedType] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hNextIdxInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hAccIdx hOne
  have hNextIdx :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (show Nat from p.1.2.1) + 1) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hNextIdxInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hWeightAddInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.1, p.2.2.2.1)) :=
    TMPolyTimeMap.prod_mk hAccWeight hPayloadWeight
  have hWeightAdd :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hWeightAddInput
    simpa [Function.comp, X] using hComp
  have hValueAddInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.2, p.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccValue hPayloadValue
  have hValueAdd :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hValueAddInput
    simpa [Function.comp, X] using hComp
  have hSelectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
            (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hWeightAdd hValueAdd
  have hUnselectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.1, p.1.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccWeight hAccValue
  have hSelectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
              (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hNextIdx hSelectedSums
  have hUnselectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1, (p.1.2.2.1, p.1.2.2.2))) :=
    TMPolyTimeMap.prod_mk hNextIdx hUnselectedSums
  have hSelectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
              (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2))))) :=
    TMPolyTimeMap.prod_mk hAccBits hSelectedRest
  have hUnselectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1, ((show Nat from p.1.2.1) + 1, (p.1.2.2.1, p.1.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccBits hUnselectedRest
  have hInnerInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (SAT.lookupBoolAt (p.1.1, p.1.2.1), p)) :=
    TMPolyTimeMap.prod_mk hLookup (TMPolyTimeMap.id X)
  have hInnerBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                ((show Nat from p.2.1.2.1) + 1,
                  ((show Nat from p.2.1.2.2.1) + (show Nat from p.2.2.2.2.1),
                    (show Nat from p.2.1.2.2.2) + (show Nat from p.2.2.2.2.2))))
          | false =>
              (p.2.1.1,
                ((show Nat from p.2.1.2.1) + 1,
                  (p.2.1.2.2.1, p.2.1.2.2.2)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.1.1, ((show Nat from p.1.2.1) + 1, (p.1.2.2.1, p.1.2.2.2))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
              (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2)))))
      hUnselectedBranch hSelectedBranch
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        if SAT.lookupBoolAt (p.1.1, p.1.2.1) then
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
                (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2))))
        else
          (p.1.1, ((show Nat from p.1.2.1) + 1, (p.1.2.2.1, p.1.2.2.2)))) := by
    have hComp := TMPolyTimeMap.comp hInnerBranch hInnerInput
    convert hComp using 1
    funext p
    cases h : SAT.lookupBoolAt (p.1.1, p.1.2.1) <;> simp [h]
  have hZeroNat : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hZeroBin : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hZeroSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hZeroBin hZeroBin
  have hZeroRest :
      TMPolyTimeMap X Rest
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hZeroNat hZeroSums
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier => (p.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat))))) :=
    TMPolyTimeMap.prod_mk hPayloadBits hZeroRest
  have hOuterInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hOuterBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              if SAT.lookupBoolAt (p.2.1.1, p.2.1.2.1) then
                (p.2.1.1,
                  ((show Nat from p.2.1.2.1) + 1,
                    ((show Nat from p.2.1.2.2.1) + (show Nat from p.2.2.2.2.1),
                      (show Nat from p.2.1.2.2.2) + (show Nat from p.2.2.2.2.2))))
              else
                (p.2.1.1,
                  ((show Nat from p.2.1.2.1) + 1,
                    (p.2.1.2.2.1, p.2.1.2.2.2)))
          | false =>
              (p.2.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat))))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat)))))
      (fTrue := fun p : X.Carrier =>
        if SAT.lookupBoolAt (p.1.1, p.1.2.1) then
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2.1),
                (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2.2))))
        else
          (p.1.1, ((show Nat from p.1.2.1) + 1, (p.1.2.2.1, p.1.2.2.2))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hOuterBranch hOuterInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨bits, idx, weight, value⟩, ⟨tag, payloadBits, item⟩⟩
  rcases item with ⟨w, v⟩
  cases tag
  · rfl
  · cases SAT.lookupBoolAt (bits, idx) <;> rfl

theorem foldStep_growth
    (source : foldInstructionListEncodedType.Carrier)
    (acc : foldAccEncodedType.Carrier)
    (instr : foldInstructionEncodedType.Carrier)
    (hInstr :
      foldInstructionEncodedType.inputSize instr ≤
        foldInstructionListEncodedType.inputSize source) :
    foldAccEncodedType.inputSize (foldStep (acc, instr)) ≤
      foldAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
          (foldInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, idx, weight, value⟩
  rcases instr with ⟨tag, payloadBits, item⟩
  rcases item with ⟨w, v⟩
  change Nat at idx weight value w v
  cases tag
  · have hLocal :
        foldAccEncodedType.inputSize
            (payloadBits, ((0 : Nat), ((0 : Nat), (0 : Nat)))) ≤
          foldInstructionEncodedType.inputSize
            (false, (payloadBits, ((w, v) : Nat × Nat))) + 20 := by
      simp [foldAccEncodedType, foldInstructionEncodedType,
        knapsackItemBinaryStructuredEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool]
      omega
    have hBound := hLocal.trans (Nat.add_le_add_right hInstr 20)
    simpa [foldStep, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      hBound.trans (by omega)
  · have hw :
        EncodedType.binaryNat.inputSize w ≤
          foldInstructionEncodedType.inputSize (true, (payloadBits, (w, v))) := by
      simp [foldInstructionEncodedType, knapsackItemBinaryStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hv :
        EncodedType.binaryNat.inputSize v ≤
          foldInstructionEncodedType.inputSize (true, (payloadBits, (w, v))) := by
      simp [foldInstructionEncodedType, knapsackItemBinaryStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hwSource : EncodedType.binaryNat.inputSize w ≤
        foldInstructionListEncodedType.inputSize source :=
      hw.trans hInstr
    have hvSource : EncodedType.binaryNat.inputSize v ≤
        foldInstructionListEncodedType.inputSize source :=
      hv.trans hInstr
    cases hBit : SAT.lookupBoolAt (bits, idx)
    · have hLocal :
          foldAccEncodedType.inputSize
              (bits, (idx + 1, (weight, value))) ≤
            foldAccEncodedType.inputSize (bits, (idx, (weight, value))) + 5 := by
        simp [foldAccEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat]
        omega
      have hGrow : 5 ≤
          (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
            (foldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      simpa [foldStep, hBit] using hLocal.trans (by omega)
    · have hAddW := binaryNatAdd_inputSize_le weight w
      have hAddV := binaryNatAdd_inputSize_le value v
      have hLocal :
          foldAccEncodedType.inputSize
              (bits, (idx + 1, (weight + w, value + v))) ≤
            foldAccEncodedType.inputSize (bits, (idx, (weight, value))) +
              EncodedType.binaryNat.inputSize w +
              EncodedType.binaryNat.inputSize v + 10 := by
        simp [foldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hAddW hAddV ⊢
        omega
      have hGrow :
          EncodedType.binaryNat.inputSize w +
              EncodedType.binaryNat.inputSize v + 10 ≤
            (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
              (foldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      simpa [foldStep, hBit] using hLocal.trans (by omega)

theorem foldAcc_tm_polytime :
    TMPolyTimeMap foldInstructionListEncodedType foldAccEncodedType
      (fun xs : foldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => foldStep (acc, x)) foldRunnerInit) := by
  rcases foldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      foldInstructionEncodedType foldAccEncodedType
      foldStep foldRunnerInit hStep
      (Polynomial.C 20) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    change foldAccEncodedType.inputSize foldRunnerInit ≤
      (Polynomial.C 20).eval (foldInstructionEncodedType.list.inputSize xs)
    have hInit : foldAccEncodedType.inputSize foldRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        foldInstructionEncodedType.inputSize instr ≤
          foldInstructionListEncodedType.inputSize source := by
      simpa [foldInstructionListEncodedType] using hInstr
    simpa [foldInstructionListEncodedType] using foldStep_growth source acc instr hInstr'

theorem foldFromInstructions_tm_polytime :
    TMPolyTimeMap foldInstructionListEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      foldFromInstructions := by
  have hFold := foldAcc_tm_polytime
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hRest :
      TMPolyTimeMap foldAccEncodedType Rest (fun acc : FoldAcc => acc.2) := by
    simpa [foldAccEncodedType, Rest] using
      TMPolyTimeMap.snd knapsackBinaryCertificateEncodedType Rest
  have hSums :
      TMPolyTimeMap Rest (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun rest : Nat × (Nat × Nat) => rest.2) := by
    simpa [Rest] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hProjection := TMPolyTimeMap.comp hSums hRest
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, foldFromInstructions, foldAccEncodedType, Rest] using hComp

theorem certificateSums_tm_polytime :
    TMPolyTimeMap foldInputEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      certificateSums := by
  have hComp := TMPolyTimeMap.comp foldFromInstructions_tm_polytime
    foldInstructions_tm_polytime
  simpa [Function.comp, certificateSums] using hComp

/-! ### Finite verifier -/

def knapsackBinaryStructuredFiniteVerify
    (I : KnapsackInput) (bits : KnapsackBinaryCertificate) : Bool :=
  let sums := certificateSums (I.items, bits)
  Clique.boolAndPair
    (binaryNatLeBool (sums.1, I.capacity),
      binaryNatLeBool (I.targetValue, sums.2))

theorem knapsackBinaryStructuredFiniteVerify_eq_true_iff
    (I : KnapsackInput) (bits : KnapsackBinaryCertificate) :
    knapsackBinaryStructuredFiniteVerify I bits = true ↔
      selectedWeightFrom I.items bits 0 ≤ I.capacity ∧
        I.targetValue ≤ selectedValueFrom I.items bits 0 := by
  rw [knapsackBinaryStructuredFiniteVerify, certificateSums_eq_weightValueFrom]
  simp [Clique.boolAndPair_eq_and, binaryNatLeBool_eq_true_iff]

theorem knapsackBinaryStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType)
      EncodedType.bool
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        knapsackBinaryStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod knapsackBinaryStructuredEncodedType
    knapsackBinaryCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X knapsackBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hBits :
      TMPolyTimeMap X knapsackBinaryCertificateEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd knapsackBinaryStructuredEncodedType
        knapsackBinaryCertificateEncodedType
  have hItems :
      TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.items) := by
    have hComp := TMPolyTimeMap.comp
      knapsackBinaryItemsTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, knapsackBinaryItemsForMembership, X] using hComp
  have hBounds :
      TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (p.1.capacity, p.1.targetValue)) := by
    have hComp := TMPolyTimeMap.comp
      knapsackBinaryBoundsTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, knapsackBinaryBoundsForMembership, X] using hComp
  have hCapacity :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.capacity) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hTarget :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : KnapsackInput × KnapsackBinaryCertificate => p.1.targetValue) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hSumsInput :
      TMPolyTimeMap X foldInputEncodedType
        (fun p : KnapsackInput × KnapsackBinaryCertificate => (p.1.items, p.2)) :=
    TMPolyTimeMap.prod_mk hItems hBits
  have hSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          certificateSums (p.1.items, p.2)) := by
    have hComp := TMPolyTimeMap.comp certificateSums_tm_polytime hSumsInput
    simpa [Function.comp, foldInputEncodedType, X] using hComp
  have hWeightSum : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        (certificateSums (p.1.items, p.2)).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hSums
    simpa [Function.comp, X] using hComp
  have hValueSum : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : KnapsackInput × KnapsackBinaryCertificate =>
        (certificateSums (p.1.items, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hSums
    simpa [Function.comp, X] using hComp
  have hWeightOKInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          ((certificateSums (p.1.items, p.2)).1, p.1.capacity)) :=
    TMPolyTimeMap.prod_mk hWeightSum hCapacity
  have hWeightOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          binaryNatLeBool ((certificateSums (p.1.items, p.2)).1, p.1.capacity)) := by
    have hComp := TMPolyTimeMap.comp binaryNatLeBool_tm_polytime hWeightOKInput
    simpa [Function.comp, X] using hComp
  have hValueOKInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (p.1.targetValue, (certificateSums (p.1.items, p.2)).2)) :=
    TMPolyTimeMap.prod_mk hTarget hValueSum
  have hValueOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          binaryNatLeBool (p.1.targetValue, (certificateSums (p.1.items, p.2)).2)) := by
    have hComp := TMPolyTimeMap.comp binaryNatLeBool_tm_polytime hValueOKInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : KnapsackInput × KnapsackBinaryCertificate =>
          (binaryNatLeBool ((certificateSums (p.1.items, p.2)).1, p.1.capacity),
            binaryNatLeBool (p.1.targetValue, (certificateSums (p.1.items, p.2)).2))) :=
    TMPolyTimeMap.prod_mk hWeightOK hValueOK
  have hAnd := TMPolyTimeMap.comp Clique.boolAndPair_tm_polytime hAndInput
  simpa [Function.comp, knapsackBinaryStructuredFiniteVerify, X] using hAnd

theorem itemListBinary_inputSize_ge_two_mul_length (items : List (Nat × Nat)) :
    2 * items.length ≤ knapsackItemListBinaryStructuredEncodedType.inputSize items := by
  induction items with
  | nil =>
      simp [knapsackItemListBinaryStructuredEncodedType]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      change
        2 * items.length ≤
          (EncodedType.list knapsackItemBinaryStructuredEncodedType).inputSize items at ih
      have hTail :
          2 * items.length ≤
            (EncodedType.list
              (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)).inputSize items := by
        simpa [knapsackItemBinaryStructuredEncodedType] using ih
      change
        2 * ((w, v) :: items).length ≤
          (EncodedType.list knapsackItemBinaryStructuredEncodedType).inputSize
            ((w, v) :: items)
      rw [EncodedType.inputSize_list_cons]
      simp [knapsackItemBinaryStructuredEncodedType, EncodedType.inputSize_prod]
      omega

theorem knapsackBinaryCertificate_inputSize_le_linear
    (I : KnapsackInput) (selected : List Bool)
    (hLen : selected.length = I.items.length) :
    knapsackBinaryCertificateEncodedType.inputSize selected ≤
      knapsackBinaryStructuredEncodedType.inputSize I := by
  have hItems := itemListBinary_inputSize_ge_two_mul_length I.items
  calc
    knapsackBinaryCertificateEncodedType.inputSize selected = 2 * selected.length := by
      rw [SAT.boolList_inputSize_eq_two_mul_length]
    _ = 2 * I.items.length := by rw [hLen]
    _ ≤ knapsackItemListBinaryStructuredEncodedType.inputSize I.items := hItems
    _ ≤ knapsackBinaryStructuredEncodedType.inputSize I := by
      change
        (knapsackItemListBinaryStructuredEncodedType.encode I.items).length ≤
          (knapsackTupleBinaryStructuredEncodedType.encode
            (I.items, (I.capacity, I.targetValue))).length
      simp [knapsackTupleBinaryStructuredEncodedType, EncodedType.prod]

end Knapsack

/-- Direct finite-certificate TM verifier for faithful binary-structured Knapsack. -/
noncomputable def knapsackBinaryStructuredFiniteTMVerifier :
    TMVerifier knapsackBinaryStructuredDecisionProblem where
  Cert := Knapsack.knapsackBinaryCertificateEncodedType
  verify := Knapsack.knapsackBinaryStructuredFiniteVerify
  verifier_polytime := Knapsack.knapsackBinaryStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hWeight, hValue⟩
    refine ⟨selected, ?_, ?_⟩
    · simpa using
        Knapsack.knapsackBinaryCertificate_inputSize_le_linear I selected hLen
    · have hSelection :
          Knapsack.selectionFrom I.items selected 0 = selected :=
        Knapsack.selectionFrom_self_of_length I.items selected hLen
      have hWeightFrom :=
        Knapsack.selectedWeightFrom_eq_selectedWeight_selectionFrom
          I.items selected 0 I.capacity I.targetValue
      have hValueFrom :=
        Knapsack.selectedValueFrom_eq_selectedValue_selectionFrom
          I.items selected 0 I.capacity I.targetValue
      rw [hSelection] at hWeightFrom hValueFrom
      exact
        (Knapsack.knapsackBinaryStructuredFiniteVerify_eq_true_iff I selected).2
          ⟨by simpa [hWeightFrom] using hWeight,
            by simpa [hValueFrom] using hValue⟩
  sound := by
    intro I bits hVerify
    let selected := Knapsack.selectionFrom I.items bits 0
    have hLen : selected.length = I.items.length := by
      simp [selected]
    have hWeightFrom :=
      Knapsack.selectedWeightFrom_eq_selectedWeight_selectionFrom
        I.items bits 0 I.capacity I.targetValue
    have hValueFrom :=
      Knapsack.selectedValueFrom_eq_selectedValue_selectionFrom
        I.items bits 0 I.capacity I.targetValue
    rcases (Knapsack.knapsackBinaryStructuredFiniteVerify_eq_true_iff I bits).1 hVerify
      with ⟨hWeight, hValue⟩
    refine ⟨selected, hLen, ?_, ?_⟩
    · simpa [selected, hWeightFrom] using hWeight
    · simpa [selected, hValueFrom] using hValue

theorem knapsackBinaryStructured_TMInNP :
    TMInNP knapsackBinaryStructuredDecisionProblem :=
  TMInNP.intro knapsackBinaryStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
