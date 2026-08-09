/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartition

/-!
Direct standard-TM NP membership witness for faithful binary-structured
Partition.

The semantic certificate is the same finite Boolean selection list used by the
structured verifier.  The runner below accumulates the selected and unselected
weights with `binaryNat` arithmetic, avoiding binary-to-unary expansion.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace Partition

/-! ### Binary projection -/

def partitionBinaryWeightsForMembership (I : PartitionInput) : List Nat :=
  I.weights

theorem partitionBinaryWeightsForMembership_encode (I : PartitionInput) :
    partitionWeightsBinaryStructuredEncodedType.encode
        (partitionBinaryWeightsForMembership I) =
      partitionBinaryStructuredEncodedType.encode I := by
  rfl

noncomputable def partitionBinaryWeightsForMembershipTMBackedMap :
    TMBackedCostedMap
      partitionBinaryStructuredEncodedType
      partitionWeightsBinaryStructuredEncodedType
      partitionBinaryWeightsForMembership :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionBinaryStructuredEncodedType
    partitionWeightsBinaryStructuredEncodedType
    partitionBinaryWeightsForMembership
    (Equiv.refl partitionWeightsBinaryStructuredEncodedType.Symbol)
    (by
      intro I
      change
        partitionWeightsBinaryStructuredEncodedType.encode
            (partitionBinaryWeightsForMembership I) =
          (partitionBinaryStructuredEncodedType.encode I).map id
      simp [partitionBinaryWeightsForMembership_encode])

/-! ### Binary instruction-list runner -/

def partitionBinaryFoldInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod partitionCertificateEncodedType EncodedType.binaryNat)

def partitionBinaryFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list partitionBinaryFoldInstructionEncodedType

def partitionBinaryFoldInputEncodedType : EncodedType :=
  EncodedType.prod partitionWeightsBinaryStructuredEncodedType partitionCertificateEncodedType

def partitionBinaryFoldAccEncodedType : EncodedType :=
  EncodedType.prod partitionCertificateEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat))

abbrev PartitionBinaryFoldInstruction :=
  Bool × (PartitionCertificate × Nat)

abbrev PartitionBinaryFoldAcc :=
  PartitionCertificate × (Nat × (Nat × Nat))

def partitionBinaryFoldInitInstruction
    (bits : PartitionCertificate) : PartitionBinaryFoldInstruction :=
  (false, (bits, 0))

def partitionBinaryFoldWeightInstruction (w : Nat) : PartitionBinaryFoldInstruction :=
  (true, ([], w))

def partitionBinaryFoldInstructions
    (p : List Nat × PartitionCertificate) :
    List PartitionBinaryFoldInstruction :=
  partitionBinaryFoldInitInstruction p.2 :: p.1.map partitionBinaryFoldWeightInstruction

def partitionBinaryFoldRunnerInit : PartitionBinaryFoldAcc :=
  ([], (0, (0, 0)))

def partitionBinaryFoldStep
    (p : PartitionBinaryFoldAcc × PartitionBinaryFoldInstruction) :
    PartitionBinaryFoldAcc :=
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

def partitionBinaryFoldFromInstructions
    (xs : List PartitionBinaryFoldInstruction) : Nat × Nat :=
  ((xs.foldl (fun acc x => partitionBinaryFoldStep (acc, x))
    partitionBinaryFoldRunnerInit).2).2

def partitionBinaryCertificateSums
    (p : List Nat × PartitionCertificate) : Nat × Nat :=
  partitionBinaryFoldFromInstructions (partitionBinaryFoldInstructions p)

theorem partitionBinaryFoldElementInstructions_fold_eq_sums
    (weights : List Nat) (bits : PartitionCertificate)
    (idx selected unselected : Nat) :
    ((weights.map partitionBinaryFoldWeightInstruction).foldl
        (fun acc instr => partitionBinaryFoldStep (acc, instr))
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
      · simp [partitionBinaryFoldWeightInstruction, partitionBinaryFoldStep, hBit]
        have h := ih (idx + 1) selected (unselected + w)
        simpa [partitionBinaryFoldStep, hBit, partitionSelectedWeightFrom,
          partitionUnselectedWeightFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using h
      · simp [partitionBinaryFoldWeightInstruction, partitionBinaryFoldStep, hBit]
        have h := ih (idx + 1) (selected + w) unselected
        simpa [partitionBinaryFoldStep, hBit, partitionSelectedWeightFrom,
          partitionUnselectedWeightFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using h

theorem partitionBinaryCertificateSums_eq_weightFrom
    (p : List Nat × PartitionCertificate) :
    partitionBinaryCertificateSums p =
      (partitionSelectedWeightFrom p.1 p.2 0,
        partitionUnselectedWeightFrom p.1 p.2 0) := by
  rcases p with ⟨weights, bits⟩
  change
    (((partitionBinaryFoldInitInstruction bits ::
        weights.map partitionBinaryFoldWeightInstruction).foldl
          (fun acc instr => partitionBinaryFoldStep (acc, instr))
          partitionBinaryFoldRunnerInit).2).2 =
      (partitionSelectedWeightFrom weights bits 0,
        partitionUnselectedWeightFrom weights bits 0)
  rw [List.foldl_cons]
  have hFold :=
    partitionBinaryFoldElementInstructions_fold_eq_sums weights bits 0 0 0
  have hSums := congrArg (fun acc : PartitionBinaryFoldAcc => acc.2.2) hFold
  simpa [partitionBinaryFoldRunnerInit, partitionBinaryFoldInitInstruction,
    partitionBinaryFoldStep] using hSums

theorem partitionBinaryFoldInitInstruction_tm_polytime :
    TMPolyTimeMap
      partitionCertificateEncodedType
      partitionBinaryFoldInstructionEncodedType
      partitionBinaryFoldInitInstruction := by
  have hFalse :
      TMPolyTimeMap partitionCertificateEncodedType EncodedType.bool
        (fun _ : PartitionCertificate => false) :=
    TMPolyTimeMap.const partitionCertificateEncodedType EncodedType.bool false
  have hBits :
      TMPolyTimeMap partitionCertificateEncodedType partitionCertificateEncodedType id :=
    TMPolyTimeMap.id partitionCertificateEncodedType
  have hZero :
      TMPolyTimeMap partitionCertificateEncodedType EncodedType.binaryNat
        (fun _ : PartitionCertificate => (0 : Nat)) :=
    TMPolyTimeMap.const partitionCertificateEncodedType EncodedType.binaryNat (0 : Nat)
  have hPayload :
      TMPolyTimeMap partitionCertificateEncodedType
        (EncodedType.prod partitionCertificateEncodedType EncodedType.binaryNat)
        (fun bits : PartitionCertificate => (bits, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hBits hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [partitionBinaryFoldInitInstruction, partitionBinaryFoldInstructionEncodedType]
    using hOut

theorem partitionBinaryFoldWeightInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      partitionBinaryFoldInstructionEncodedType
      partitionBinaryFoldWeightInstruction := by
  have hTrue :
      TMPolyTimeMap EncodedType.binaryNat EncodedType.bool
        (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.binaryNat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.binaryNat partitionCertificateEncodedType
        (fun _ : Nat => ([] : PartitionCertificate)) :=
    TMPolyTimeMap.const EncodedType.binaryNat partitionCertificateEncodedType []
  have hWeight : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat id :=
    TMPolyTimeMap.id EncodedType.binaryNat
  have hPayload :
      TMPolyTimeMap EncodedType.binaryNat
        (EncodedType.prod partitionCertificateEncodedType EncodedType.binaryNat)
        (fun w : Nat => (([] : PartitionCertificate), w)) :=
    TMPolyTimeMap.prod_mk hEmpty hWeight
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [partitionBinaryFoldWeightInstruction, partitionBinaryFoldInstructionEncodedType]
    using hOut

theorem partitionBinaryFoldInstructions_tm_polytime :
    TMPolyTimeMap
      partitionBinaryFoldInputEncodedType
      partitionBinaryFoldInstructionListEncodedType
      partitionBinaryFoldInstructions := by
  let X := partitionBinaryFoldInputEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsBinaryStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, partitionBinaryFoldInputEncodedType] using
      TMPolyTimeMap.fst partitionWeightsBinaryStructuredEncodedType
        partitionCertificateEncodedType
  have hBits :
      TMPolyTimeMap X partitionCertificateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, partitionBinaryFoldInputEncodedType] using
      TMPolyTimeMap.snd partitionWeightsBinaryStructuredEncodedType
        partitionCertificateEncodedType
  have hInit :
      TMPolyTimeMap X partitionBinaryFoldInstructionEncodedType
        (fun p : X.Carrier => partitionBinaryFoldInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp partitionBinaryFoldInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X partitionBinaryFoldInstructionListEncodedType
        (fun p : X.Carrier => [partitionBinaryFoldInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton partitionBinaryFoldInstructionEncodedType) hInit
    simpa [Function.comp, partitionBinaryFoldInstructionListEncodedType, X] using hComp
  have hWeightInstructions :
      TMPolyTimeMap X partitionBinaryFoldInstructionListEncodedType
        (fun p : X.Carrier => p.1.map partitionBinaryFoldWeightInstruction) := by
    have hMap := TMPolyTimeMap.list_map partitionBinaryFoldWeightInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hWeights
    simpa [Function.comp, partitionBinaryFoldInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionBinaryFoldInstructionListEncodedType
          partitionBinaryFoldInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([partitionBinaryFoldInitInstruction p.2],
            p.1.map partitionBinaryFoldWeightInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hWeightInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append partitionBinaryFoldInstructionEncodedType) hAppendInput
  simpa [Function.comp, partitionBinaryFoldInstructions,
    partitionBinaryFoldInstructionListEncodedType, X] using hOut

theorem partitionBinaryFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionBinaryFoldAccEncodedType
        partitionBinaryFoldInstructionEncodedType)
      partitionBinaryFoldAccEncodedType
      partitionBinaryFoldStep := by
  let X := EncodedType.prod partitionBinaryFoldAccEncodedType
    partitionBinaryFoldInstructionEncodedType
  let A := partitionBinaryFoldAccEncodedType
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  let Payload := EncodedType.prod partitionCertificateEncodedType EncodedType.binaryNat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A partitionBinaryFoldInstructionEncodedType
  have hInstr : TMPolyTimeMap X partitionBinaryFoldInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A partitionBinaryFoldInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, partitionBinaryFoldInstructionEncodedType, Payload, X]
      using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, partitionBinaryFoldInstructionEncodedType, Payload, X]
      using hComp
  have hAccBits : TMPolyTimeMap X partitionCertificateEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst partitionCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccRest : TMPolyTimeMap X Rest (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd partitionCertificateEncodedType Rest
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
  have hAccSelected : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hAccSums
    simpa [Function.comp, X] using hComp
  have hAccUnselected : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hAccSums
    simpa [Function.comp, X] using hComp
  have hPayloadBits : TMPolyTimeMap X partitionCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst partitionCertificateEncodedType EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadWeight : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd partitionCertificateEncodedType EncodedType.binaryNat
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
  have hSelectedAddInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccSelected hPayloadWeight
  have hSelectedAdd :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.1) + (show Nat from p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatAdd_tm_polytime hSelectedAddInput
    simpa [Function.comp, X] using hComp
  have hUnselectedAddInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.2, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccUnselected hPayloadWeight
  have hUnselectedAdd :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : X.Carrier =>
          (show Nat from p.1.2.2.2) + (show Nat from p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatAdd_tm_polytime hUnselectedAddInput
    simpa [Function.comp, X] using hComp
  have hTrueSelectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + (show Nat from p.2.2.2), p.1.2.2.2)) :=
    TMPolyTimeMap.prod_mk hSelectedAdd hAccUnselected
  have hTrueUnselectedSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
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
  have hZeroBin : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hZeroSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hZeroBin hZeroBin
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

theorem partitionBinaryFoldStep_growth
    (source : partitionBinaryFoldInstructionListEncodedType.Carrier)
    (acc : partitionBinaryFoldAccEncodedType.Carrier)
    (instr : partitionBinaryFoldInstructionEncodedType.Carrier)
    (hInstr :
      partitionBinaryFoldInstructionEncodedType.inputSize instr ≤
        partitionBinaryFoldInstructionListEncodedType.inputSize source) :
    partitionBinaryFoldAccEncodedType.inputSize (partitionBinaryFoldStep (acc, instr)) ≤
      partitionBinaryFoldAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
          (partitionBinaryFoldInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, idx, selected, unselected⟩
  rcases instr with ⟨tag, payloadBits, w⟩
  change Nat at idx selected unselected w
  cases tag
  · have hLocal :
        partitionBinaryFoldAccEncodedType.inputSize
            (payloadBits, ((0 : Nat), ((0 : Nat), (0 : Nat)))) ≤
          partitionBinaryFoldInstructionEncodedType.inputSize
            (false, (payloadBits, w)) + 20 := by
      simp [partitionBinaryFoldAccEncodedType, partitionBinaryFoldInstructionEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool]
      omega
    have hBound := hLocal.trans (Nat.add_le_add_right hInstr 20)
    simpa [partitionBinaryFoldStep, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] using hBound.trans (by omega)
  · have hw :
        EncodedType.binaryNat.inputSize w ≤
          partitionBinaryFoldInstructionEncodedType.inputSize (true, (payloadBits, w)) := by
      simp [partitionBinaryFoldInstructionEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool]
      omega
    have hwSource : EncodedType.binaryNat.inputSize w ≤
        partitionBinaryFoldInstructionListEncodedType.inputSize source :=
      hw.trans hInstr
    cases hBit : SAT.lookupBoolAt (bits, idx)
    · have hAdd := Knapsack.binaryNatAdd_inputSize_le unselected w
      have hLocal :
          partitionBinaryFoldAccEncodedType.inputSize
              (bits, (idx + 1, (selected, unselected + w))) ≤
            partitionBinaryFoldAccEncodedType.inputSize (bits, (idx, (selected, unselected))) +
              EncodedType.binaryNat.inputSize w + 10 := by
        simp [partitionBinaryFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hAdd ⊢
        omega
      have hGrow :
          EncodedType.binaryNat.inputSize w + 10 ≤
            (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
              (partitionBinaryFoldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      simpa [partitionBinaryFoldStep, hBit] using hLocal.trans (by omega)
    · have hAdd := Knapsack.binaryNatAdd_inputSize_le selected w
      have hLocal :
          partitionBinaryFoldAccEncodedType.inputSize
              (bits, (idx + 1, (selected + w, unselected))) ≤
            partitionBinaryFoldAccEncodedType.inputSize (bits, (idx, (selected, unselected))) +
              EncodedType.binaryNat.inputSize w + 10 := by
        simp [partitionBinaryFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hAdd ⊢
        omega
      have hGrow :
          EncodedType.binaryNat.inputSize w + 10 ≤
            (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
              (partitionBinaryFoldInstructionListEncodedType.inputSize source) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      simpa [partitionBinaryFoldStep, hBit] using hLocal.trans (by omega)

theorem partitionBinaryFoldAcc_tm_polytime :
    TMPolyTimeMap partitionBinaryFoldInstructionListEncodedType
      partitionBinaryFoldAccEncodedType
      (fun xs : partitionBinaryFoldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => partitionBinaryFoldStep (acc, x))
          partitionBinaryFoldRunnerInit) := by
  rcases partitionBinaryFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      partitionBinaryFoldInstructionEncodedType partitionBinaryFoldAccEncodedType
      partitionBinaryFoldStep partitionBinaryFoldRunnerInit hStep
      (Polynomial.C 20) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    change partitionBinaryFoldAccEncodedType.inputSize partitionBinaryFoldRunnerInit ≤
      (Polynomial.C 20).eval (partitionBinaryFoldInstructionEncodedType.list.inputSize xs)
    have hInit : partitionBinaryFoldAccEncodedType.inputSize
        partitionBinaryFoldRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        partitionBinaryFoldInstructionEncodedType.inputSize instr ≤
          partitionBinaryFoldInstructionListEncodedType.inputSize source := by
      simpa [partitionBinaryFoldInstructionListEncodedType] using hInstr
    simpa [partitionBinaryFoldInstructionListEncodedType] using
      partitionBinaryFoldStep_growth source acc instr hInstr'

theorem partitionBinaryFoldFromInstructions_tm_polytime :
    TMPolyTimeMap partitionBinaryFoldInstructionListEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      partitionBinaryFoldFromInstructions := by
  have hFold := partitionBinaryFoldAcc_tm_polytime
  let Rest := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hRest :
      TMPolyTimeMap partitionBinaryFoldAccEncodedType Rest
        (fun acc : PartitionBinaryFoldAcc => acc.2) := by
    simpa [partitionBinaryFoldAccEncodedType, Rest] using
      TMPolyTimeMap.snd partitionCertificateEncodedType Rest
  have hSums :
      TMPolyTimeMap Rest (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun rest : Nat × (Nat × Nat) => rest.2) := by
    simpa [Rest] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hProjection := TMPolyTimeMap.comp hSums hRest
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, partitionBinaryFoldFromInstructions,
    partitionBinaryFoldAccEncodedType, Rest] using hComp

theorem partitionBinaryCertificateSums_tm_polytime :
    TMPolyTimeMap partitionBinaryFoldInputEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      partitionBinaryCertificateSums := by
  have hComp := TMPolyTimeMap.comp partitionBinaryFoldFromInstructions_tm_polytime
    partitionBinaryFoldInstructions_tm_polytime
  simpa [Function.comp, partitionBinaryCertificateSums] using hComp

/-! ### Finite verifier -/

def partitionBinaryFiniteVerify
    (I : PartitionInput) (bits : PartitionCertificate) : Bool :=
  let sums := partitionBinaryCertificateSums (I.weights, bits)
  Knapsack.binaryNatEqBool sums

theorem partitionBinaryFiniteVerify_eq_true_iff
    (I : PartitionInput) (bits : PartitionCertificate) :
    partitionBinaryFiniteVerify I bits = true ↔
      partitionSelectedWeightFrom I.weights bits 0 =
        partitionUnselectedWeightFrom I.weights bits 0 := by
  rw [partitionBinaryFiniteVerify, partitionBinaryCertificateSums_eq_weightFrom]
  exact Knapsack.binaryNatEqBool_eq_true_iff _

theorem partitionBinaryFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionBinaryStructuredEncodedType partitionCertificateEncodedType)
      EncodedType.bool
      (fun p : PartitionInput × PartitionCertificate =>
        partitionBinaryFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod partitionBinaryStructuredEncodedType partitionCertificateEncodedType
  have hInstance :
      TMPolyTimeMap X partitionBinaryStructuredEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst partitionBinaryStructuredEncodedType partitionCertificateEncodedType
  have hBits :
      TMPolyTimeMap X partitionCertificateEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd partitionBinaryStructuredEncodedType partitionCertificateEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsBinaryStructuredEncodedType
        (fun p : PartitionInput × PartitionCertificate => p.1.weights) := by
    have hComp := TMPolyTimeMap.comp
      partitionBinaryWeightsForMembershipTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, partitionBinaryWeightsForMembership, X] using hComp
  have hSumsInput :
      TMPolyTimeMap X partitionBinaryFoldInputEncodedType
        (fun p : PartitionInput × PartitionCertificate => (p.1.weights, p.2)) :=
    TMPolyTimeMap.prod_mk hWeights hBits
  have hSums :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : PartitionInput × PartitionCertificate =>
          partitionBinaryCertificateSums (p.1.weights, p.2)) := by
    have hComp := TMPolyTimeMap.comp partitionBinaryCertificateSums_tm_polytime hSumsInput
    simpa [Function.comp, partitionBinaryFoldInputEncodedType, X] using hComp
  have hEq := TMPolyTimeMap.comp Knapsack.binaryNatEqBool_tm_polytime hSums
  simpa [Function.comp, partitionBinaryFiniteVerify, X] using hEq

theorem partitionWeightsBinary_length_le_inputSize (weights : List Nat) :
    weights.length ≤ partitionWeightsBinaryStructuredEncodedType.inputSize weights := by
  simpa [partitionWeightsBinaryStructuredEncodedType] using
    Knapsack.encodedList_length_le_inputSize EncodedType.binaryNat weights

theorem partitionBinaryCertificate_inputSize_le_linear
    (I : PartitionInput) (selected : List Bool)
    (hLen : selected.length = I.weights.length) :
    partitionCertificateEncodedType.inputSize selected ≤
      2 * partitionBinaryStructuredEncodedType.inputSize I := by
  rw [SAT.boolList_inputSize_eq_two_mul_length, hLen]
  have hWeights := partitionWeightsBinary_length_le_inputSize I.weights
  change 2 * I.weights.length ≤
    2 * partitionWeightsBinaryStructuredEncodedType.inputSize I.weights
  exact Nat.mul_le_mul_left 2 hWeights

end Partition

/-- Direct finite-certificate TM verifier for faithful binary-structured Partition. -/
noncomputable def partitionBinaryStructuredFiniteTMVerifier :
    TMVerifier partitionBinaryStructuredDecisionProblem where
  Cert := Partition.partitionCertificateEncodedType
  verify := Partition.partitionBinaryFiniteVerify
  verifier_polytime := Partition.partitionBinaryFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 2, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hEq⟩
    refine ⟨selected, ?_, ?_⟩
    · simpa using Partition.partitionBinaryCertificate_inputSize_le_linear I selected hLen
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
        (Partition.partitionBinaryFiniteVerify_eq_true_iff I selected).2
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
      (Partition.partitionBinaryFiniteVerify_eq_true_iff I bits).1 hVerify
    simpa [selected, hSelected, hUnselected] using hEq

theorem partitionBinaryStructured_TMInNP :
    TMInNP partitionBinaryStructuredDecisionProblem :=
  TMInNP.intro partitionBinaryStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
