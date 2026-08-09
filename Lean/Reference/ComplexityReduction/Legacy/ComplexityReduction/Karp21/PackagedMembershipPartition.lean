/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Partition.

The certificate is a finite Boolean selection list.  During verification, missing
certificate positions default to `false`, exactly as `SAT.finiteAssignment` does.
Soundness converts any accepting finite certificate into a length-exact selection
list by reading precisely one Boolean for each encoded weight.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace Partition

abbrev partitionCertificateEncodedType : EncodedType :=
  SAT.finiteAssignmentCertEncodedType

abbrev PartitionCertificate := List Bool

/-! ### Structured Partition projection -/

def partitionWeightsForMembership (I : PartitionInput) : List Nat :=
  I.weights

theorem partitionWeightsForMembership_encode (I : PartitionInput) :
    partitionWeightsStructuredEncodedType.encode (partitionWeightsForMembership I) =
      partitionStructuredEncodedType.encode I := by
  rfl

noncomputable def partitionWeightsForMembershipTMBackedMap :
    TMBackedCostedMap
      partitionStructuredEncodedType
      partitionWeightsStructuredEncodedType
      partitionWeightsForMembership :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionStructuredEncodedType partitionWeightsStructuredEncodedType
    partitionWeightsForMembership
    (Equiv.refl partitionWeightsStructuredEncodedType.Symbol)
    (by
      intro I
      change
        partitionWeightsStructuredEncodedType.encode (partitionWeightsForMembership I) =
          (partitionStructuredEncodedType.encode I).map id
      simp [partitionWeightsForMembership_encode])

/-! ### Semantic finite-certificate sums -/

def partitionSelectedWeightFrom : List Nat → PartitionCertificate → Nat → Nat
  | [], _, _ => 0
  | w :: ws, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then w else 0) +
        partitionSelectedWeightFrom ws bits (idx + 1)

def partitionUnselectedWeightFrom : List Nat → PartitionCertificate → Nat → Nat
  | [], _, _ => 0
  | w :: ws, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then 0 else w) +
        partitionUnselectedWeightFrom ws bits (idx + 1)

def partitionSelectionFrom : List Nat → PartitionCertificate → Nat → List Bool
  | [], _, _ => []
  | _ :: ws, bits, idx =>
      SAT.lookupBoolAt (bits, idx) :: partitionSelectionFrom ws bits (idx + 1)

@[simp] theorem partitionSelectionFrom_length
    (weights : List Nat) (bits : PartitionCertificate) (idx : Nat) :
    (partitionSelectionFrom weights bits idx).length = weights.length := by
  induction weights generalizing idx with
  | nil =>
      simp [partitionSelectionFrom]
  | cons w ws ih =>
      simp [partitionSelectionFrom, ih]

theorem partitionSelectedWeightFrom_eq_selectedPartitionWeight_selectionFrom
    (weights : List Nat) (bits : PartitionCertificate) (idx : Nat) :
    partitionSelectedWeightFrom weights bits idx =
      selectedPartitionWeight { weights := weights }
        (partitionSelectionFrom weights bits idx) := by
  induction weights generalizing idx with
  | nil =>
      simp [partitionSelectedWeightFrom, partitionSelectionFrom, selectedPartitionWeight]
  | cons w ws ih =>
      simp [partitionSelectedWeightFrom, partitionSelectionFrom, selectedPartitionWeight,
        ih]

theorem partitionUnselectedWeightFrom_eq_unselectedPartitionWeight_selectionFrom
    (weights : List Nat) (bits : PartitionCertificate) (idx : Nat) :
    partitionUnselectedWeightFrom weights bits idx =
      unselectedPartitionWeight { weights := weights }
        (partitionSelectionFrom weights bits idx) := by
  induction weights generalizing idx with
  | nil =>
      simp [partitionUnselectedWeightFrom, partitionSelectionFrom,
        unselectedPartitionWeight]
  | cons w ws ih =>
      simp [partitionUnselectedWeightFrom, partitionSelectionFrom,
        unselectedPartitionWeight, ih]

@[simp] theorem partitionLookup_cons_zero (b : Bool) (bits : List Bool) :
    SAT.lookupBoolAt (b :: bits, 0) = b := by
  simp [SAT.lookupBoolAt_eq_getD]

@[simp] theorem partitionLookup_cons_succ
    (b : Bool) (bits : List Bool) (idx : Nat) :
    SAT.lookupBoolAt (b :: bits, idx + 1) = SAT.lookupBoolAt (bits, idx) := by
  simp [SAT.lookupBoolAt_eq_getD]

theorem partitionSelectionFrom_cons_succ
    (weights : List Nat) (b : Bool) (bits : List Bool) (idx : Nat) :
    partitionSelectionFrom weights (b :: bits) (idx + 1) =
      partitionSelectionFrom weights bits idx := by
  induction weights generalizing idx with
  | nil =>
      simp [partitionSelectionFrom]
  | cons w ws ih =>
      simp [partitionSelectionFrom, ih]

theorem partitionSelectionFrom_self_of_length
    (weights : List Nat) (selected : List Bool)
    (hLen : selected.length = weights.length) :
    partitionSelectionFrom weights selected 0 = selected := by
  induction weights generalizing selected with
  | nil =>
      have hNil : selected = [] := by
        cases selected with
        | nil => rfl
        | cons b bs => simp at hLen
      simp [partitionSelectionFrom, hNil]
  | cons w ws ih =>
      cases selected with
      | nil =>
          simp at hLen
      | cons b bs =>
          have hTail : bs.length = ws.length := by simpa using hLen
          have hRec : partitionSelectionFrom ws (b :: bs) 1 = bs := by
            rw [show (1 : Nat) = 0 + 1 by rfl]
            rw [partitionSelectionFrom_cons_succ]
            exact ih bs hTail
          simp [partitionSelectionFrom, hRec]

/-! ### Instruction-list runner for direct TM verification -/

def partitionFoldInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod partitionCertificateEncodedType EncodedType.nat)

def partitionFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list partitionFoldInstructionEncodedType

def partitionFoldInputEncodedType : EncodedType :=
  EncodedType.prod partitionWeightsStructuredEncodedType partitionCertificateEncodedType

def partitionFoldAccEncodedType : EncodedType :=
  EncodedType.prod partitionCertificateEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat))

abbrev PartitionFoldInstruction :=
  Bool × (PartitionCertificate × Nat)

abbrev PartitionFoldAcc :=
  PartitionCertificate × (Nat × (Nat × Nat))

def partitionFoldInitInstruction
    (bits : PartitionCertificate) : PartitionFoldInstruction :=
  (false, (bits, 0))

def partitionFoldWeightInstruction (w : Nat) : PartitionFoldInstruction :=
  (true, ([], w))

def partitionFoldInstructions
    (p : List Nat × PartitionCertificate) :
    List PartitionFoldInstruction :=
  partitionFoldInitInstruction p.2 :: p.1.map partitionFoldWeightInstruction

def partitionFoldRunnerInit : PartitionFoldAcc :=
  ([], (0, (0, 0)))

def partitionFoldStep
    (p : PartitionFoldAcc × PartitionFoldInstruction) :
    PartitionFoldAcc :=
  if p.2.1 then
    let bits := p.1.1
    let idx := p.1.2.1
    let selected := p.1.2.2.1
    let unselected := p.1.2.2.2
    let w := p.2.2.2
    if SAT.lookupBoolAt (bits, idx) then
      (bits, (idx + 1, (selected + w, unselected)))
    else
      (bits, (idx + 1, (selected, unselected + w)))
  else
    (p.2.2.1, (0, (0, 0)))

def partitionFoldFromInstructions
    (xs : List PartitionFoldInstruction) : Nat × Nat :=
  ((xs.foldl (fun acc x => partitionFoldStep (acc, x))
    partitionFoldRunnerInit).2).2

def partitionCertificateSums
    (p : List Nat × PartitionCertificate) : Nat × Nat :=
  partitionFoldFromInstructions (partitionFoldInstructions p)

theorem partitionFoldElementInstructions_fold_eq_sums
    (weights : List Nat) (bits : PartitionCertificate)
    (idx selected unselected : Nat) :
    ((weights.map partitionFoldWeightInstruction).foldl
        (fun acc instr => partitionFoldStep (acc, instr))
        (bits, (idx, (selected, unselected)))) =
      (bits,
        (idx + weights.length,
          (selected + partitionSelectedWeightFrom weights bits idx,
            unselected + partitionUnselectedWeightFrom weights bits idx))) := by
  induction weights generalizing idx selected unselected with
  | nil =>
      simp [partitionSelectedWeightFrom, partitionUnselectedWeightFrom]
  | cons w ws ih =>
      rw [List.map_cons, List.foldl_cons]
      cases hBit : SAT.lookupBoolAt (bits, idx)
      · simp [partitionFoldWeightInstruction, partitionFoldStep, hBit]
        have h :=
          ih (idx + 1) selected (unselected + w)
        simpa [partitionFoldStep, hBit, partitionSelectedWeightFrom,
          partitionUnselectedWeightFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using h
      · simp [partitionFoldWeightInstruction, partitionFoldStep, hBit]
        have h :=
          ih (idx + 1) (selected + w) unselected
        simpa [partitionFoldStep, hBit, partitionSelectedWeightFrom,
          partitionUnselectedWeightFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using h

theorem partitionCertificateSums_eq_weightFrom
    (p : List Nat × PartitionCertificate) :
    partitionCertificateSums p =
      (partitionSelectedWeightFrom p.1 p.2 0,
        partitionUnselectedWeightFrom p.1 p.2 0) := by
  rcases p with ⟨weights, bits⟩
  change
    (((partitionFoldInitInstruction bits ::
        weights.map partitionFoldWeightInstruction).foldl
          (fun acc instr => partitionFoldStep (acc, instr))
          partitionFoldRunnerInit).2).2 =
      (partitionSelectedWeightFrom weights bits 0,
        partitionUnselectedWeightFrom weights bits 0)
  rw [List.foldl_cons]
  have hFold :=
    partitionFoldElementInstructions_fold_eq_sums weights bits 0 0 0
  have hSums := congrArg (fun acc : PartitionFoldAcc => acc.2.2) hFold
  simpa [partitionFoldRunnerInit, partitionFoldInitInstruction, partitionFoldStep]
    using hSums

theorem partitionFoldInitInstruction_tm_polytime :
    TMPolyTimeMap
      partitionCertificateEncodedType
      partitionFoldInstructionEncodedType
      partitionFoldInitInstruction := by
  have hFalse :
      TMPolyTimeMap partitionCertificateEncodedType EncodedType.bool
        (fun _ : PartitionCertificate => false) :=
    TMPolyTimeMap.const partitionCertificateEncodedType EncodedType.bool false
  have hBits :
      TMPolyTimeMap partitionCertificateEncodedType partitionCertificateEncodedType id :=
    TMPolyTimeMap.id partitionCertificateEncodedType
  have hZero :
      TMPolyTimeMap partitionCertificateEncodedType EncodedType.nat
        (fun _ : PartitionCertificate => (0 : Nat)) :=
    TMPolyTimeMap.const partitionCertificateEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap partitionCertificateEncodedType
        (EncodedType.prod partitionCertificateEncodedType EncodedType.nat)
        (fun bits : PartitionCertificate => (bits, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hBits hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [partitionFoldInitInstruction, partitionFoldInstructionEncodedType] using hOut

theorem partitionFoldWeightInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      partitionFoldInstructionEncodedType
      partitionFoldWeightInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.nat partitionCertificateEncodedType
        (fun _ : Nat => ([] : PartitionCertificate)) :=
    TMPolyTimeMap.const EncodedType.nat partitionCertificateEncodedType []
  have hWeight : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod partitionCertificateEncodedType EncodedType.nat)
        (fun w : Nat => (([] : PartitionCertificate), w)) :=
    TMPolyTimeMap.prod_mk hEmpty hWeight
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [partitionFoldWeightInstruction, partitionFoldInstructionEncodedType] using hOut

theorem partitionFoldInstructions_tm_polytime :
    TMPolyTimeMap
      partitionFoldInputEncodedType
      partitionFoldInstructionListEncodedType
      partitionFoldInstructions := by
  let X := partitionFoldInputEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, partitionFoldInputEncodedType] using
      TMPolyTimeMap.fst partitionWeightsStructuredEncodedType partitionCertificateEncodedType
  have hBits :
      TMPolyTimeMap X partitionCertificateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, partitionFoldInputEncodedType] using
      TMPolyTimeMap.snd partitionWeightsStructuredEncodedType partitionCertificateEncodedType
  have hInit :
      TMPolyTimeMap X partitionFoldInstructionEncodedType
        (fun p : X.Carrier => partitionFoldInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp partitionFoldInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X partitionFoldInstructionListEncodedType
        (fun p : X.Carrier => [partitionFoldInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton partitionFoldInstructionEncodedType) hInit
    simpa [Function.comp, partitionFoldInstructionListEncodedType, X] using hComp
  have hWeightInstructions :
      TMPolyTimeMap X partitionFoldInstructionListEncodedType
        (fun p : X.Carrier => p.1.map partitionFoldWeightInstruction) := by
    have hMap := TMPolyTimeMap.list_map partitionFoldWeightInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hWeights
    simpa [Function.comp, partitionFoldInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionFoldInstructionListEncodedType
          partitionFoldInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([partitionFoldInitInstruction p.2],
            p.1.map partitionFoldWeightInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hWeightInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append partitionFoldInstructionEncodedType) hAppendInput
  simpa [Function.comp, partitionFoldInstructions, partitionFoldInstructionListEncodedType, X]
    using hOut

theorem partitionFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionFoldAccEncodedType partitionFoldInstructionEncodedType)
      partitionFoldAccEncodedType
      partitionFoldStep := by
  let X := EncodedType.prod partitionFoldAccEncodedType partitionFoldInstructionEncodedType
  let A := partitionFoldAccEncodedType
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)
  let Payload := EncodedType.prod partitionCertificateEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A partitionFoldInstructionEncodedType
  have hInstr : TMPolyTimeMap X partitionFoldInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A partitionFoldInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, partitionFoldInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, partitionFoldInstructionEncodedType, Payload, X] using hComp
  have hAccBits : TMPolyTimeMap X partitionCertificateEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst partitionCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccRest : TMPolyTimeMap X Rest
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd partitionCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAccRest
    simpa [Function.comp, Rest, X] using hComp
  have hAccSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAccRest
    simpa [Function.comp, Rest, X] using hComp
  have hAccSelected : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAccSums
    simpa [Function.comp, X] using hComp
  have hAccUnselected : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hAccSums
    simpa [Function.comp, X] using hComp
  have hPayloadBits : TMPolyTimeMap X partitionCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst partitionCertificateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadWeight : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd partitionCertificateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X SAT.lookupBoolInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hAccBits hAccIdx
  have hLookup :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => SAT.lookupBoolAt (p.1.1, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp SAT.lookupBoolAt_tm_polytime hLookupInput
    simpa [Function.comp, SAT.lookupBoolInputEncodedType] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (1 : Nat)) :=
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
  have hSelectedAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.2.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccSelected hPayloadWeight
  have hSelectedAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.1) + (show Nat from p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hSelectedAddInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hUnselectedAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.2.2, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccUnselected hPayloadWeight
  have hUnselectedAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hUnselectedAddInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hTrueSelectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2)) :=
    TMPolyTimeMap.prod_mk hSelectedAdd hAccUnselected
  have hTrueUnselectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hAccSelected hUnselectedAdd
  have hTrueSelectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2))) :=
    TMPolyTimeMap.prod_mk hNextIdx hTrueSelectedSums
  have hTrueUnselectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1,
            (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hNextIdx hTrueUnselectedSums
  have hTrueSelectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccBits hTrueSelectedRest
  have hTrueUnselectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2))))) :=
    TMPolyTimeMap.prod_mk hAccBits hTrueUnselectedRest
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
                  ((show Nat from p.2.1.2.2.1) + (show Nat from p.2.2.2.2),
                    p.2.1.2.2.2)))
          | false =>
              (p.2.1.1,
                ((show Nat from p.2.1.2.1) + 1,
                  (p.2.1.2.2.1,
                    (show Nat from p.2.1.2.2.2) + (show Nat from p.2.2.2.2))))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2)))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2))))
      hTrueUnselectedBranch hTrueSelectedBranch
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        if SAT.lookupBoolAt (p.1.1, p.1.2.1) then
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2)))
        else
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2))))) := by
    have hComp := TMPolyTimeMap.comp hInnerBranch hInnerInput
    convert hComp using 1
    funext p
    cases h : SAT.lookupBoolAt (p.1.1, p.1.2.1) <;> simp [h]
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hZeroSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hZero hZero
  have hZeroRest :
      TMPolyTimeMap X Rest
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hZero hZeroSums
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat))))) :=
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
                    ((show Nat from p.2.1.2.2.1) + (show Nat from p.2.2.2.2),
                      p.2.1.2.2.2)))
              else
                (p.2.1.1,
                  ((show Nat from p.2.1.2.1) + 1,
                    (p.2.1.2.2.1,
                      (show Nat from p.2.1.2.2.2) + (show Nat from p.2.2.2.2))))
          | false =>
              (p.2.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat))))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.2.2.1, ((0 : Nat), ((0 : Nat), (0 : Nat)))))
      (fTrue := fun p : X.Carrier =>
        if SAT.lookupBoolAt (p.1.1, p.1.2.1) then
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2)))
        else
          (p.1.1,
            ((show Nat from p.1.2.1) + 1,
              (p.1.2.2.1, (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2)))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hOuterBranch hOuterInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨bits, idx, selected, unselected⟩, ⟨tag, payloadBits, w⟩⟩
  cases tag
  · rfl
  · cases SAT.lookupBoolAt (bits, idx) <;> rfl

theorem partitionFoldStep_growth
    (source : partitionFoldInstructionListEncodedType.Carrier)
    (acc : partitionFoldAccEncodedType.Carrier)
    (instr : partitionFoldInstructionEncodedType.Carrier)
    (hInstr :
      partitionFoldInstructionEncodedType.inputSize instr ≤
        partitionFoldInstructionListEncodedType.inputSize source) :
    partitionFoldAccEncodedType.inputSize (partitionFoldStep (acc, instr)) ≤
      partitionFoldAccEncodedType.inputSize acc +
        (Polynomial.X + Polynomial.C 20).eval
          (partitionFoldInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, idx, selected, unselected⟩
  rcases instr with ⟨tag, payloadBits, w⟩
  change Nat at idx selected unselected w
  cases tag
  · have hLocal :
        partitionFoldAccEncodedType.inputSize
            (payloadBits, ((0 : Nat), ((0 : Nat), (0 : Nat)))) ≤
          partitionFoldInstructionEncodedType.inputSize (false, (payloadBits, w)) + 20 := by
      simp [partitionFoldAccEncodedType, partitionFoldInstructionEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat]
      omega
    have hBound := hLocal.trans (Nat.add_le_add_right hInstr 20)
    simpa [partitionFoldStep, Polynomial.eval_add] using
      hBound.trans (by omega)
  · have hw :
        w ≤ partitionFoldInstructionEncodedType.inputSize (true, (payloadBits, w)) := by
      simp [partitionFoldInstructionEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, EncodedType.inputSize_nat]
      omega
    have hwSource :
        w ≤ partitionFoldInstructionListEncodedType.inputSize source :=
      hw.trans hInstr
    cases hBit : SAT.lookupBoolAt (bits, idx)
    · have hLocal :
          partitionFoldAccEncodedType.inputSize
              (bits, (idx + 1, (selected, unselected + w))) ≤
            partitionFoldAccEncodedType.inputSize (bits, (idx, (selected, unselected))) +
              w + 5 := by
        simp [partitionFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      have hGrow : w + 5 ≤
          (Polynomial.X + Polynomial.C 20).eval
            (partitionFoldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add]
        omega
      simpa [partitionFoldStep, hBit] using
        hLocal.trans (by omega)
    · have hLocal :
          partitionFoldAccEncodedType.inputSize
              (bits, (idx + 1, (selected + w, unselected))) ≤
            partitionFoldAccEncodedType.inputSize (bits, (idx, (selected, unselected))) +
              w + 5 := by
        simp [partitionFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      have hGrow : w + 5 ≤
          (Polynomial.X + Polynomial.C 20).eval
            (partitionFoldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add]
        omega
      simpa [partitionFoldStep, hBit] using
        hLocal.trans (by omega)

theorem partitionFoldAcc_tm_polytime :
    TMPolyTimeMap partitionFoldInstructionListEncodedType partitionFoldAccEncodedType
      (fun xs : partitionFoldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => partitionFoldStep (acc, x))
          partitionFoldRunnerInit) := by
  rcases partitionFoldStep_tm_polytime with ⟨hStep⟩
  let base : Polynomial Nat := Polynomial.C 20
  let grow : Polynomial Nat := Polynomial.X + Polynomial.C 20
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      partitionFoldInstructionEncodedType partitionFoldAccEncodedType
      partitionFoldStep partitionFoldRunnerInit hStep base grow ?_ ?_
  · intro xs
    change partitionFoldAccEncodedType.inputSize partitionFoldRunnerInit ≤
      (Polynomial.C 20).eval
        (partitionFoldInstructionEncodedType.list.inputSize xs)
    have hInit : partitionFoldAccEncodedType.inputSize partitionFoldRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        partitionFoldInstructionEncodedType.inputSize instr ≤
          partitionFoldInstructionListEncodedType.inputSize source := by
      simpa [partitionFoldInstructionListEncodedType] using hInstr
    simpa [partitionFoldInstructionListEncodedType, grow] using
      partitionFoldStep_growth source acc instr hInstr'

theorem partitionFoldFromInstructions_tm_polytime :
    TMPolyTimeMap partitionFoldInstructionListEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      partitionFoldFromInstructions := by
  have hFold := partitionFoldAcc_tm_polytime
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hRest :
      TMPolyTimeMap partitionFoldAccEncodedType Rest
        (fun acc : PartitionFoldAcc => acc.2) := by
    simpa [partitionFoldAccEncodedType, Rest] using
      TMPolyTimeMap.snd partitionCertificateEncodedType Rest
  have hSums :
      TMPolyTimeMap Rest (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun rest : Nat × (Nat × Nat) => rest.2) := by
    simpa [Rest] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hProjection := TMPolyTimeMap.comp hSums hRest
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, partitionFoldFromInstructions, partitionFoldAccEncodedType, Rest]
    using hComp

theorem partitionCertificateSums_tm_polytime :
    TMPolyTimeMap partitionFoldInputEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      partitionCertificateSums := by
  have hComp := TMPolyTimeMap.comp partitionFoldFromInstructions_tm_polytime
    partitionFoldInstructions_tm_polytime
  simpa [Function.comp, partitionCertificateSums] using hComp

/-! ### Finite verifier -/

def partitionStructuredFiniteVerify
    (I : PartitionInput) (bits : PartitionCertificate) : Bool :=
  let sums := partitionCertificateSums (I.weights, bits)
  decide (sums.1 = sums.2)

theorem partitionStructuredFiniteVerify_eq_true_iff
    (I : PartitionInput) (bits : PartitionCertificate) :
    partitionStructuredFiniteVerify I bits = true ↔
      partitionSelectedWeightFrom I.weights bits 0 =
        partitionUnselectedWeightFrom I.weights bits 0 := by
  rw [partitionStructuredFiniteVerify, partitionCertificateSums_eq_weightFrom]
  simp

theorem partitionStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionStructuredEncodedType partitionCertificateEncodedType)
      EncodedType.bool
      (fun p : PartitionInput × PartitionCertificate =>
        partitionStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod partitionStructuredEncodedType partitionCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X partitionStructuredEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.1) := by
    simpa [X] using TMPolyTimeMap.fst partitionStructuredEncodedType partitionCertificateEncodedType
  have hBits :
      TMPolyTimeMap X partitionCertificateEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.2) := by
    simpa [X] using TMPolyTimeMap.snd partitionStructuredEncodedType partitionCertificateEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.1.weights) := by
    have hComp := TMPolyTimeMap.comp
      partitionWeightsForMembershipTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, partitionWeightsForMembership, X] using hComp
  have hSumsInput :
      TMPolyTimeMap X partitionFoldInputEncodedType
        (fun p : PartitionInput × PartitionCertificate => (p.1.weights, p.2)) :=
    TMPolyTimeMap.prod_mk hWeights hBits
  have hSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : PartitionInput × PartitionCertificate =>
          partitionCertificateSums (p.1.weights, p.2)) := by
    have hComp := TMPolyTimeMap.comp partitionCertificateSums_tm_polytime hSumsInput
    simpa [Function.comp, partitionFoldInputEncodedType, X] using hComp
  have hEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hSums
  simpa [Function.comp, partitionStructuredFiniteVerify, X] using hEq

theorem partitionCertificate_inputSize_le_linear
    (I : PartitionInput) (selected : List Bool)
    (hLen : selected.length = I.weights.length) :
    partitionCertificateEncodedType.inputSize selected ≤
      partitionStructuredEncodedType.inputSize I := by
  rw [SAT.boolList_inputSize_eq_two_mul_length, hLen, partitionStructured_inputSize_eq]
  omega

end Partition

/-- Direct finite-certificate TM verifier for faithful structured Partition. -/
noncomputable def partitionStructuredFiniteTMVerifier :
    TMVerifier partitionStructuredDecisionProblem where
  Cert := Partition.partitionCertificateEncodedType
  verify := Partition.partitionStructuredFiniteVerify
  verifier_polytime := Partition.partitionStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hEq⟩
    refine ⟨selected, ?_, ?_⟩
    · simpa using Partition.partitionCertificate_inputSize_le_linear I selected hLen
    · have hSelection :
          Partition.partitionSelectionFrom I.weights selected 0 = selected :=
        Partition.partitionSelectionFrom_self_of_length I.weights selected hLen
      have hSelected :=
        Partition.partitionSelectedWeightFrom_eq_selectedPartitionWeight_selectionFrom
          I.weights selected 0
      have hUnselected :=
        Partition.partitionUnselectedWeightFrom_eq_unselectedPartitionWeight_selectionFrom
          I.weights selected 0
      rw [hSelection] at hSelected hUnselected
      exact
        (Partition.partitionStructuredFiniteVerify_eq_true_iff I selected).2
          (by simpa [hSelected, hUnselected] using hEq)
  sound := by
    intro I bits hVerify
    let selected := Partition.partitionSelectionFrom I.weights bits 0
    have hLen : selected.length = I.weights.length := by
      simp [selected]
    have hSelected :=
      Partition.partitionSelectedWeightFrom_eq_selectedPartitionWeight_selectionFrom
        I.weights bits 0
    have hUnselected :=
      Partition.partitionUnselectedWeightFrom_eq_unselectedPartitionWeight_selectionFrom
        I.weights bits 0
    refine ⟨selected, hLen, ?_⟩
    have hEq :=
      (Partition.partitionStructuredFiniteVerify_eq_true_iff I bits).1 hVerify
    simpa [selected, hSelected, hUnselected] using hEq

theorem partitionStructured_TMInNP :
    TMInNP partitionStructuredDecisionProblem :=
  TMInNP.intro partitionStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
