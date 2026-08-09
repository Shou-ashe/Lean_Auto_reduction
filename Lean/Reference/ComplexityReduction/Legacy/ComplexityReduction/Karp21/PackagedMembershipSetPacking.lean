/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetPackingScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Set Packing.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace SetPackingMembership

def setPackingInputToTuple
    (I : setPackingStructuredEncodedType.Carrier) :
    setPackingTupleStructuredEncodedType.Carrier :=
  (I.system, I.k)

theorem setPackingInputToTuple_encode (I : setPackingStructuredEncodedType.Carrier) :
    setPackingTupleStructuredEncodedType.encode (setPackingInputToTuple I) =
      setPackingStructuredEncodedType.encode I := by
  cases I
  rfl

noncomputable def setPackingInputToTupleTMBackedMap :
    TMBackedCostedMap
      setPackingStructuredEncodedType
      setPackingTupleStructuredEncodedType
      setPackingInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    setPackingStructuredEncodedType
    setPackingTupleStructuredEncodedType
    setPackingInputToTuple
    (Equiv.refl setPackingTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change setPackingTupleStructuredEncodedType.encode (setPackingInputToTuple I) =
        (setPackingStructuredEncodedType.encode I).map id
      simp [setPackingInputToTuple_encode])

def setPackingStructuredFiniteVerify (I : SetPackingInput) (cert : List (List Nat)) :
    Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (I.k, cert.length),
      setPackingScanBool (I.system.sets, cert))

theorem setPackingStructuredFiniteVerify_eq_true_iff
    (I : SetPackingInput) (cert : List (List Nat)) :
    setPackingStructuredFiniteVerify I cert = true ↔
      I.k ≤ cert.length ∧ PackingScanOK I.system.sets [] [] cert := by
  rw [setPackingStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    HittingSet.natLeBool_eq_true_iff, setPackingScanBool_eq_true_iff]

theorem setPackingVerifier_complete
    {I : SetPackingInput} {selected : List (List Nat)}
    (hLen : selected.length ≥ I.k)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    setPackingStructuredFiniteVerify I selected = true := by
  refine (setPackingStructuredFiniteVerify_eq_true_iff I selected).2 ?_
  exact ⟨hLen, PackingScanOK.of_props hFamily hNodup hDisjoint⟩

theorem setPackingVerifier_sound
    {I : SetPackingInput} {cert : List (List Nat)}
    (hVerify : setPackingStructuredFiniteVerify I cert = true) :
    SetPacking I := by
  rcases (setPackingStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hLen, hScan⟩
  refine ⟨cert, hLen, ?_, PackingScanOK.nodup hScan, PackingScanOK.pairwiseDisjoint hScan⟩
  exact PackingScanOK.mem_family hScan

theorem setPacking_family_inputSize_le (I : SetPackingInput) :
    setFamilyStructuredEncodedType.inputSize I.system.sets ≤
      setPackingStructuredEncodedType.inputSize I := by
  rw [SetPacking.setPackingStructured_inputSize_eq, SetPacking.setSystemStructured_inputSize_eq]
  omega

theorem setPacking_sets_length_le_inputSize (I : SetPackingInput) :
    I.system.sets.length ≤ setPackingStructuredEncodedType.inputSize I := by
  have hList :
      I.system.sets.length ≤ setFamilyStructuredEncodedType.inputSize I.system.sets := by
    simpa [setFamilyStructuredEncodedType] using
      Clique.encodedList_length_le_inputSize setStructuredEncodedType I.system.sets
  exact hList.trans (setPacking_family_inputSize_le I)

theorem setPacking_set_inputSize_le
    {I : SetPackingInput} {S : List Nat}
    (hS : S ∈ I.system.sets) :
    setStructuredEncodedType.inputSize S ≤
      setPackingStructuredEncodedType.inputSize I := by
  have hElem := Clique.encodedList_element_inputSize_le
    (X := setStructuredEncodedType) (x := S) (xs := I.system.sets) hS
  have hElem' :
      setStructuredEncodedType.inputSize S ≤
        setFamilyStructuredEncodedType.inputSize I.system.sets := by
    simpa [setFamilyStructuredEncodedType] using hElem
  exact hElem'.trans (setPacking_family_inputSize_le I)

theorem setPackingCertificate_inputSize_le_poly
    (I : SetPackingInput) (selected : List (List Nat))
    (hNodup : selected.Nodup)
    (hMem : ∀ S ∈ selected, S ∈ I.system.sets) :
    setPackingCertificateEncodedType.inputSize selected ≤
      2 * (setPackingStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let Ssize := setPackingStructuredEncodedType.inputSize I
  have hLen : selected.length ≤ I.system.sets.length :=
    FiniteWitness.nodup_length_le_of_mem hNodup hMem
  have hSourceLen : I.system.sets.length ≤ Ssize := by
    simpa [Ssize] using setPacking_sets_length_le_inputSize I
  have hEach : ∀ S ∈ selected, setStructuredEncodedType.inputSize S ≤ Ssize := by
    intro S hS
    simpa [Ssize] using setPacking_set_inputSize_le (I := I) (hMem S hS)
  have hList := Clique.encodedList_inputSize_le_length_mul_bound
    setStructuredEncodedType selected Ssize hEach
  calc
    setPackingCertificateEncodedType.inputSize selected
        ≤ selected.length * (Ssize + 1) := by
          simpa [setPackingCertificateEncodedType, setFamilyStructuredEncodedType] using hList
    _ ≤ Ssize * (Ssize + 1) :=
        Nat.mul_le_mul_right (Ssize + 1) (hLen.trans hSourceLen)
    _ ≤ 2 * Ssize ^ 2 + 2 := by nlinarith

theorem setPackingStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setPackingStructuredEncodedType setPackingCertificateEncodedType)
      EncodedType.bool
      (fun p : SetPackingInput × List (List Nat) =>
        setPackingStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod setPackingStructuredEncodedType setPackingCertificateEncodedType
  have hI : TMPolyTimeMap X setPackingStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst setPackingStructuredEncodedType setPackingCertificateEncodedType
  have hCert : TMPolyTimeMap X setPackingCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd setPackingStructuredEncodedType setPackingCertificateEncodedType
  have hTuple : TMPolyTimeMap X setPackingTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp setPackingInputToTupleTMBackedMap.tm_polytime hI
    simpa [Function.comp, setPackingInputToTuple, X] using hComp
  have hSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType (fun p : X.Carrier => p.1.system) := by
    have hFst := TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, setPackingTupleStructuredEncodedType, X] using hComp
  have hK : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, setPackingTupleStructuredEncodedType, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, HittingSet.setSystemInputToTuple, X] using hComp
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hCertLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime hCert
    simpa [Function.comp, setPackingCertificateEncodedType, setFamilyStructuredEncodedType, X]
      using hComp
  have hLenInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.k, p.2.length)) :=
    TMPolyTimeMap.prod_mk hK hCertLength
  have hLen : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.natLeBool (p.1.k, p.2.length)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLenInput
    simpa [Function.comp, X] using hComp
  have hScanInput : TMPolyTimeMap X setPackingScanInputEncodedType
      (fun p : X.Carrier => (p.1.system.sets, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hCert
  have hScan : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => setPackingScanBool (p.1.system.sets, p.2)) := by
    have hComp := TMPolyTimeMap.comp setPackingScanBool_tm_polytime hScanInput
    simpa [Function.comp, setPackingScanInputEncodedType, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (HittingSet.natLeBool (p.1.k, p.2.length),
          setPackingScanBool (p.1.system.sets, p.2))) :=
    TMPolyTimeMap.prod_mk hLen hScan
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, setPackingStructuredFiniteVerify, X] using hOut

end SetPackingMembership

/-- Direct finite-certificate TM verifier for faithful structured Set Packing. -/
noncomputable def setPackingStructuredFiniteTMVerifier :
    TMVerifier setPackingStructuredDecisionProblem where
  Cert := SetPackingMembership.setPackingCertificateEncodedType
  verify := SetPackingMembership.setPackingStructuredFiniteVerify
  verifier_polytime := SetPackingMembership.setPackingStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
    refine ⟨selected, ?_, ?_⟩
    · exact SetPackingMembership.setPackingCertificate_inputSize_le_poly
        I selected hNodup hFamily
    · exact SetPackingMembership.setPackingVerifier_complete
        hLen hFamily hNodup hDisjoint
  sound := by
    intro I cert hVerify
    exact SetPackingMembership.setPackingVerifier_sound hVerify

theorem setPackingStructured_TMInNP :
    TMInNP setPackingStructuredDecisionProblem :=
  TMInNP.intro setPackingStructuredFiniteTMVerifier

/-! ### Alternative index-list verifier for checked suffix decoding -/

namespace SetPackingMembership

abbrev setPackingIndexCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

abbrev setPackingIndexDecodeAccEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType

abbrev SetPackingIndexDecodeAcc :=
  List (List Nat) × List (List Nat)

abbrev setPackingIndexDecodeInstructionEncodedType : EncodedType :=
  EncodedType.sum setFamilyStructuredEncodedType EncodedType.nat

abbrev setPackingIndexDecodeInstructionListEncodedType : EncodedType :=
  EncodedType.list setPackingIndexDecodeInstructionEncodedType

abbrev setPackingIndexDecodeInputEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType

def setPackingIndexDecodeRunnerInit : SetPackingIndexDecodeAcc :=
  (([] : List (List Nat)), ([] : List (List Nat)))

def setPackingIndexDecodeInitInstruction (source : List (List Nat)) :
    setPackingIndexDecodeInstructionEncodedType.Carrier :=
  Sum.inl source

def setPackingIndexDecodeIndexInstruction (j : Nat) :
    setPackingIndexDecodeInstructionEncodedType.Carrier :=
  Sum.inr j

def setPackingIndexDecodeInstructions (p : List (List Nat) × List Nat) :
    List setPackingIndexDecodeInstructionEncodedType.Carrier :=
  setPackingIndexDecodeInitInstruction p.1 ::
    p.2.map setPackingIndexDecodeIndexInstruction

def setPackingIndexDecodeStep
    (p : SetPackingIndexDecodeAcc × setPackingIndexDecodeInstructionEncodedType.Carrier) :
    SetPackingIndexDecodeAcc :=
  match p.2 with
  | Sum.inl source => (source, [])
  | Sum.inr j => (p.1.1, p.1.2 ++ [SteinerTree.setFamilyGetD (p.1.1, j)])

def setPackingIndexDecodeFromInstructions
    (xs : List setPackingIndexDecodeInstructionEncodedType.Carrier) :
    List (List Nat) :=
  (xs.foldl (fun acc instr => setPackingIndexDecodeStep (acc, instr))
    setPackingIndexDecodeRunnerInit).2

def setPackingIndexDecode (p : List (List Nat) × List Nat) :
    List (List Nat) :=
  setPackingIndexDecodeFromInstructions (setPackingIndexDecodeInstructions p)

theorem setPackingIndexDecodeIndexInstructions_fold_eq
    (idxs : List Nat) (source out : List (List Nat)) :
    (idxs.map setPackingIndexDecodeIndexInstruction).foldl
        (fun acc instr => setPackingIndexDecodeStep (acc, instr)) (source, out) =
      (source, out ++ idxs.map (fun j => source.getD j [])) := by
  induction idxs generalizing out with
  | nil =>
      simp
  | cons j idxs ih =>
      have h := ih (out ++ [source.getD j []])
      simpa [setPackingIndexDecodeIndexInstruction, setPackingIndexDecodeStep,
        SteinerTree.setFamilyGetD, List.append_assoc] using h

theorem setPackingIndexDecode_eq_map_getD
    (source : List (List Nat)) (idxs : List Nat) :
    setPackingIndexDecode (source, idxs) =
      idxs.map fun j => source.getD j [] := by
  change
    (((setPackingIndexDecodeInitInstruction source ::
      idxs.map setPackingIndexDecodeIndexInstruction).foldl
        (fun acc instr => setPackingIndexDecodeStep (acc, instr))
        setPackingIndexDecodeRunnerInit).2) =
      idxs.map fun j => source.getD j []
  rw [List.foldl_cons]
  have hFold := setPackingIndexDecodeIndexInstructions_fold_eq idxs source []
  simpa [setPackingIndexDecodeRunnerInit, setPackingIndexDecodeInitInstruction,
    setPackingIndexDecodeStep] using congrArg Prod.snd hFold

theorem setFamily_getD_inputSize_le
    (source : List (List Nat)) (j : Nat) :
    setStructuredEncodedType.inputSize (source.getD j []) ≤
      setFamilyStructuredEncodedType.inputSize source := by
  by_cases hj : j < source.length
  · rw [List.getD_eq_getElem (l := source) (d := []) hj]
    have hMem : source[j] ∈ source := List.getElem_mem hj
    simpa [setFamilyStructuredEncodedType] using
      Clique.encodedList_element_inputSize_le
        (X := setStructuredEncodedType) (x := source[j]) (xs := source) hMem
  · have hLen : source.length ≤ j := Nat.le_of_not_gt hj
    rw [List.getD_eq_default (l := source) (d := []) (n := j) hLen]
    exact Nat.zero_le _

theorem setPackingIndexDecodeInitInstruction_tm_polytime :
    TMPolyTimeMap
      setFamilyStructuredEncodedType
      setPackingIndexDecodeInstructionEncodedType
      setPackingIndexDecodeInitInstruction := by
  simpa [setPackingIndexDecodeInstructionEncodedType,
    setPackingIndexDecodeInitInstruction] using
    TMPolyTimeMap.inl setFamilyStructuredEncodedType EncodedType.nat

theorem setPackingIndexDecodeIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setPackingIndexDecodeInstructionEncodedType
      setPackingIndexDecodeIndexInstruction := by
  simpa [setPackingIndexDecodeInstructionEncodedType,
    setPackingIndexDecodeIndexInstruction] using
    TMPolyTimeMap.inr setFamilyStructuredEncodedType EncodedType.nat

theorem setPackingIndexDecodeInstructions_tm_polytime :
    TMPolyTimeMap
      setPackingIndexDecodeInputEncodedType
      setPackingIndexDecodeInstructionListEncodedType
      setPackingIndexDecodeInstructions := by
  let X := setPackingIndexDecodeInputEncodedType
  have hSource : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, setPackingIndexDecodeInputEncodedType] using
      TMPolyTimeMap.fst setFamilyStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, setPackingIndexDecodeInputEncodedType] using
      TMPolyTimeMap.snd setFamilyStructuredEncodedType setStructuredEncodedType
  have hInit : TMPolyTimeMap X setPackingIndexDecodeInstructionEncodedType
      (fun p : X.Carrier => setPackingIndexDecodeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp setPackingIndexDecodeInitInstruction_tm_polytime
      hSource
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X setPackingIndexDecodeInstructionListEncodedType
        (fun p : X.Carrier => [setPackingIndexDecodeInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton setPackingIndexDecodeInstructionEncodedType) hInit
    simpa [Function.comp, setPackingIndexDecodeInstructionListEncodedType, X] using hComp
  have hIdxInstructions :
      TMPolyTimeMap X setPackingIndexDecodeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setPackingIndexDecodeIndexInstruction) := by
    have hMap :=
      TMPolyTimeMap.list_map setPackingIndexDecodeIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hIdxs
    simpa [Function.comp, setPackingIndexDecodeInstructionListEncodedType,
      setStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setPackingIndexDecodeInstructionListEncodedType
          setPackingIndexDecodeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([setPackingIndexDecodeInitInstruction p.1],
            p.2.map setPackingIndexDecodeIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hIdxInstructions
  have hAppend :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append setPackingIndexDecodeInstructionEncodedType)
      hAppendInput
  simpa [Function.comp, setPackingIndexDecodeInstructions,
    setPackingIndexDecodeInstructionListEncodedType, X] using hAppend

theorem setPackingIndexDecodeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setPackingIndexDecodeAccEncodedType
        setPackingIndexDecodeInstructionEncodedType)
      setPackingIndexDecodeAccEncodedType
      setPackingIndexDecodeStep := by
  let A := setPackingIndexDecodeAccEncodedType
  have hLeft :
      TMPolyTimeMap setFamilyStructuredEncodedType A
        (fun source : List (List Nat) => (source, ([] : List (List Nat)))) := by
    have hSource : TMPolyTimeMap setFamilyStructuredEncodedType
        setFamilyStructuredEncodedType id :=
      TMPolyTimeMap.id setFamilyStructuredEncodedType
    have hEmpty : TMPolyTimeMap setFamilyStructuredEncodedType
        setFamilyStructuredEncodedType (fun _ => ([] : List (List Nat))) :=
      TMPolyTimeMap.const setFamilyStructuredEncodedType setFamilyStructuredEncodedType []
    have hOut := TMPolyTimeMap.prod_mk hSource hEmpty
    simpa [A, setPackingIndexDecodeAccEncodedType] using hOut
  have hRight :
      TMPolyTimeMap
        (EncodedType.prod A EncodedType.nat)
        A
        (fun p : A.Carrier × Nat =>
          ((show List (List Nat) from p.1.1),
            (show List (List Nat) from p.1.2) ++
              [SteinerTree.setFamilyGetD ((show List (List Nat) from p.1.1), p.2)])) := by
    let X := EncodedType.prod A EncodedType.nat
    have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
      simpa [X] using TMPolyTimeMap.fst A EncodedType.nat
    have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
      simpa [X] using TMPolyTimeMap.snd A EncodedType.nat
    have hSource : TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => p.1.1) := by
      have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType
        setFamilyStructuredEncodedType
      have hComp := TMPolyTimeMap.comp hFst hAcc
      simpa [Function.comp, A, setPackingIndexDecodeAccEncodedType, X] using hComp
    have hOut : TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType
        setFamilyStructuredEncodedType
      have hComp := TMPolyTimeMap.comp hSnd hAcc
      simpa [Function.comp, A, setPackingIndexDecodeAccEncodedType, X] using hComp
    have hLookupInput :
        TMPolyTimeMap X
          (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
          (fun p : X.Carrier => ((show List (List Nat) from p.1.1), p.2)) :=
      TMPolyTimeMap.prod_mk hSource hJ
    have hLookup : TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier =>
          SteinerTree.setFamilyGetD ((show List (List Nat) from p.1.1), p.2)) := by
      have hComp := TMPolyTimeMap.comp SteinerTree.setFamilyGetD_tm_polytime
        hLookupInput
      simpa [Function.comp, X] using hComp
    have hSingleton : TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier =>
          [SteinerTree.setFamilyGetD ((show List (List Nat) from p.1.1), p.2)]) := by
      have hComp := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton setStructuredEncodedType) hLookup
      simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
    have hAppendInput :
        TMPolyTimeMap X
          (EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType)
          (fun p : X.Carrier =>
            ((show List (List Nat) from p.1.2),
              [SteinerTree.setFamilyGetD ((show List (List Nat) from p.1.1), p.2)])) :=
      TMPolyTimeMap.prod_mk hOut hSingleton
    have hNewOut : TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (List Nat) from p.1.2) ++
            [SteinerTree.setFamilyGetD ((show List (List Nat) from p.1.1), p.2)]) := by
      have hComp := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append setStructuredEncodedType) hAppendInput
      simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
    have hPair := TMPolyTimeMap.prod_mk hSource hNewOut
    simpa [A, setPackingIndexDecodeAccEncodedType, X] using hPair
  have hChoice :=
    prodSumChoice_tm_polytime A setFamilyStructuredEncodedType EncodedType.nat
  have hBranches := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem setPackingIndexDecodeFold_tm_polytime :
    TMPolyTimeMap
      setPackingIndexDecodeInstructionListEncodedType
      setPackingIndexDecodeAccEncodedType
      (fun xs : setPackingIndexDecodeInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => setPackingIndexDecodeStep (acc, instr))
          setPackingIndexDecodeRunnerInit) := by
  rcases setPackingIndexDecodeStep_tm_polytime with ⟨hStep⟩
  let Inv : Nat → setPackingIndexDecodeAccEncodedType.Carrier → Prop :=
    fun N acc => setFamilyStructuredEncodedType.inputSize
      (show List (List Nat) from acc.1) ≤ N
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setPackingIndexDecodeInstructionEncodedType setPackingIndexDecodeAccEncodedType
      setPackingIndexDecodeStep setPackingIndexDecodeRunnerInit hStep
      (Polynomial.C 1000) (Polynomial.C 3 * Polynomial.X + Polynomial.C 1000)
      Inv ?_ ?_
  · intro xs
    constructor
    · dsimp [Inv]
      have hNilFamily : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := by
        native_decide
      simp [setPackingIndexDecodeRunnerInit, hNilFamily]
    · change setPackingIndexDecodeAccEncodedType.inputSize
          setPackingIndexDecodeRunnerInit ≤
        (Polynomial.C 1000).eval
          (setPackingIndexDecodeInstructionEncodedType.list.inputSize xs)
      have hInit :
          setPackingIndexDecodeAccEncodedType.inputSize setPackingIndexDecodeRunnerInit ≤
            1000 := by
        native_decide
      simpa using hInit
  · intro source acc instr hInv hInstr
    rcases acc with ⟨sourceFamily, out⟩
    change List (List Nat) at sourceFamily out
    have hSourceSize :
        setFamilyStructuredEncodedType.inputSize sourceFamily ≤
          setPackingIndexDecodeInstructionListEncodedType.inputSize source := by
      simpa [Inv] using hInv
    cases instr with
    | inl initSource =>
        have hInitLe :
            setFamilyStructuredEncodedType.inputSize initSource ≤
              setPackingIndexDecodeInstructionEncodedType.inputSize (Sum.inl initSource) := by
          simp [EncodedType.inputSize, EncodedType.sum]
        have hInitLeSource := hInitLe.trans hInstr
        constructor
        · simpa [Inv, setPackingIndexDecodeStep] using hInitLeSource
        · have hNilFamily :
              setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := by
            native_decide
          simp [setPackingIndexDecodeStep, setPackingIndexDecodeAccEncodedType,
            setPackingIndexDecodeInstructionEncodedType,
            EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, hNilFamily] at hInv hInstr hInitLeSource ⊢
          omega
    | inr j =>
        have hGetD := setFamily_getD_inputSize_le sourceFamily j
        have hAppend :
            setFamilyStructuredEncodedType.inputSize
                (out ++ [SteinerTree.setFamilyGetD (sourceFamily, j)]) =
              setFamilyStructuredEncodedType.inputSize out +
                setStructuredEncodedType.inputSize (sourceFamily.getD j []) + 1 := by
          simpa [setFamilyStructuredEncodedType, SteinerTree.setFamilyGetD,
            EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil] using
            Clique.encodedList_inputSize_append setStructuredEncodedType out
              [sourceFamily.getD j []]
        constructor
        · simpa [Inv, setPackingIndexDecodeStep] using hInv
        · simp [setPackingIndexDecodeStep, setPackingIndexDecodeAccEncodedType,
            setPackingIndexDecodeInstructionEncodedType,
            setPackingIndexDecodeInstructionListEncodedType,
            EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, hAppend] at hInv hSourceSize hGetD ⊢
          omega

theorem setPackingIndexDecodeFromInstructions_tm_polytime :
    TMPolyTimeMap
      setPackingIndexDecodeInstructionListEncodedType
      setFamilyStructuredEncodedType
      setPackingIndexDecodeFromInstructions := by
  have hFold := setPackingIndexDecodeFold_tm_polytime
  have hOut := TMPolyTimeMap.snd setFamilyStructuredEncodedType
    setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setPackingIndexDecodeFromInstructions,
    setPackingIndexDecodeAccEncodedType] using hComp

theorem setPackingIndexDecode_tm_polytime :
    TMPolyTimeMap
      setPackingIndexDecodeInputEncodedType
      setFamilyStructuredEncodedType
      setPackingIndexDecode := by
  have hComp := TMPolyTimeMap.comp setPackingIndexDecodeFromInstructions_tm_polytime
    setPackingIndexDecodeInstructions_tm_polytime
  simpa [Function.comp, setPackingIndexDecode] using hComp

def setPackingIndexStructuredFiniteVerify (I : SetPackingInput) (idxs : List Nat) :
    Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (I.k, idxs.length),
      graphBoolAndPair
        (HittingSet.boundedNatListBool (I.system.sets.length, idxs),
          setPackingScanBool (I.system.sets,
            setPackingIndexDecode (I.system.sets, idxs))))

theorem setPackingIndexStructuredFiniteVerify_eq_true_iff
    (I : SetPackingInput) (idxs : List Nat) :
    setPackingIndexStructuredFiniteVerify I idxs = true ↔
      I.k ≤ idxs.length ∧
        (∀ j ∈ idxs, j < I.system.sets.length) ∧
          PackingScanOK I.system.sets [] []
            (idxs.map fun j => I.system.sets.getD j []) := by
  rw [setPackingIndexStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff, setPackingScanBool_eq_true_iff,
    setPackingIndexDecode_eq_map_getD]

theorem setPackingIndexStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setPackingStructuredEncodedType setPackingIndexCertificateEncodedType)
      EncodedType.bool
      (fun p : SetPackingInput × List Nat =>
        setPackingIndexStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod setPackingStructuredEncodedType setPackingIndexCertificateEncodedType
  have hI : TMPolyTimeMap X setPackingStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, setPackingIndexCertificateEncodedType] using
      TMPolyTimeMap.fst setPackingStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, setPackingIndexCertificateEncodedType] using
      TMPolyTimeMap.snd setPackingStructuredEncodedType setStructuredEncodedType
  have hTuple : TMPolyTimeMap X setPackingTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp setPackingInputToTupleTMBackedMap.tm_polytime hI
    simpa [Function.comp, setPackingInputToTuple, X] using hComp
  have hSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType (fun p : X.Carrier => p.1.system) := by
    have hFst := TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, setPackingTupleStructuredEncodedType, X] using hComp
  have hK : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, setPackingTupleStructuredEncodedType, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, HittingSet.setSystemInputToTuple, X] using hComp
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hSetsLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.system.sets.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime hSets
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hCertLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hIdxs
    simpa [Function.comp, setPackingIndexCertificateEncodedType,
      setStructuredEncodedType, X] using hComp
  have hLenInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.k, p.2.length)) :=
    TMPolyTimeMap.prod_mk hK hCertLength
  have hLen : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.natLeBool (p.1.k, p.2.length)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLenInput
    simpa [Function.comp, X] using hComp
  have hBoundInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.system.sets.length, p.2)) :=
    TMPolyTimeMap.prod_mk hSetsLength hIdxs
  have hBound : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        HittingSet.boundedNatListBool (p.1.system.sets.length, p.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hBoundInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X] using hComp
  have hDecodeInput :
      TMPolyTimeMap X setPackingIndexDecodeInputEncodedType
        (fun p : X.Carrier => (p.1.system.sets, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hIdxs
  have hDecoded : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => setPackingIndexDecode (p.1.system.sets, p.2)) := by
    have hComp := TMPolyTimeMap.comp setPackingIndexDecode_tm_polytime hDecodeInput
    simpa [Function.comp, setPackingIndexDecodeInputEncodedType, X] using hComp
  have hScanInput : TMPolyTimeMap X setPackingScanInputEncodedType
      (fun p : X.Carrier =>
        (p.1.system.sets, setPackingIndexDecode (p.1.system.sets, p.2))) :=
    TMPolyTimeMap.prod_mk hSets hDecoded
  have hScan : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        setPackingScanBool
          (p.1.system.sets, setPackingIndexDecode (p.1.system.sets, p.2))) := by
    have hComp := TMPolyTimeMap.comp setPackingScanBool_tm_polytime hScanInput
    simpa [Function.comp, setPackingScanInputEncodedType, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
            setPackingScanBool
              (p.1.system.sets, setPackingIndexDecode (p.1.system.sets, p.2)))) :=
    TMPolyTimeMap.prod_mk hBound hScan
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
            setPackingScanBool
              (p.1.system.sets, setPackingIndexDecode (p.1.system.sets, p.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (p.1.k, p.2.length),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
                setPackingScanBool
                  (p.1.system.sets, setPackingIndexDecode (p.1.system.sets, p.2))))) :=
    TMPolyTimeMap.prod_mk hLen hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, setPackingIndexStructuredFiniteVerify, X] using hAll

theorem setPackingIndexCertificate_inputSize_le_poly
    (I : SetPackingInput) (idxs : List Nat)
    (hLen : idxs.length ≤ I.system.sets.length)
    (hBounds : ∀ j ∈ idxs, j < I.system.sets.length) :
    setPackingIndexCertificateEncodedType.inputSize idxs ≤
      2 * (setPackingStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := setPackingStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le I.system.sets.length idxs hBounds
  have hSets : I.system.sets.length ≤ S := by
    simpa [S] using setPacking_sets_length_le_inputSize I
  calc
    setPackingIndexCertificateEncodedType.inputSize idxs
        ≤ idxs.length * (I.system.sets.length + 1) := by
          simpa [setPackingIndexCertificateEncodedType] using hCert
    _ ≤ I.system.sets.length * (I.system.sets.length + 1) :=
        Nat.mul_le_mul_right (I.system.sets.length + 1) hLen
    _ ≤ S * (S + 1) := Nat.mul_le_mul hSets (Nat.succ_le_succ hSets)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

theorem setPackingIndexVerifier_complete
    {I : SetPackingInput} {selected : List (List Nat)}
    (hLen : selected.length ≥ I.k)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    setPackingIndexStructuredFiniteVerify I (selected.map I.system.sets.idxOf) = true := by
  classical
  refine (setPackingIndexStructuredFiniteVerify_eq_true_iff I
    (selected.map I.system.sets.idxOf)).2 ?_
  have hBounds : ∀ j ∈ selected.map I.system.sets.idxOf,
      j < I.system.sets.length := by
    intro j hj
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  have hDecoded :
      (selected.map I.system.sets.idxOf).map
          (fun j => I.system.sets.getD j []) =
        selected := by
    simpa [FiniteWitness.valuesFromIndices] using
      (FiniteWitness.valuesFromIdxOf_eq
        (values := I.system.sets) (fallback := ([] : List Nat)) (by
          intro S hS
          exact hFamily S hS))
  have hScan : PackingScanOK I.system.sets [] []
      ((selected.map I.system.sets.idxOf).map fun j => I.system.sets.getD j []) := by
    rw [hDecoded]
    exact PackingScanOK.of_props hFamily hNodup hDisjoint
  refine ⟨?_, hBounds, hScan⟩
  simpa using hLen

theorem setPackingIndexVerifier_sound
    {I : SetPackingInput} {idxs : List Nat}
    (hVerify : setPackingIndexStructuredFiniteVerify I idxs = true) :
    SetPacking I := by
  rcases (setPackingIndexStructuredFiniteVerify_eq_true_iff I idxs).1 hVerify with
    ⟨hLen, _hBounds, hScan⟩
  let selected := idxs.map fun j => I.system.sets.getD j []
  refine ⟨selected, ?_, ?_, PackingScanOK.nodup hScan,
    PackingScanOK.pairwiseDisjoint hScan⟩
  · simpa [selected] using hLen
  · simpa [selected] using PackingScanOK.mem_family hScan

end SetPackingMembership

/--
Alternative direct finite-certificate TM verifier for faithful structured Set
Packing whose certificate is a nat-list of selected source-family indices.
-/
noncomputable def setPackingIndexStructuredFiniteTMVerifier :
    TMVerifier setPackingStructuredDecisionProblem where
  Cert := SetPackingMembership.setPackingIndexCertificateEncodedType
  verify := SetPackingMembership.setPackingIndexStructuredFiniteVerify
  verifier_polytime := SetPackingMembership.setPackingIndexStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
    let idxs := selected.map I.system.sets.idxOf
    have hBounds : ∀ j ∈ idxs, j < I.system.sets.length := by
      intro j hj
      rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
      exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
    have hIdxLen : idxs.length ≤ I.system.sets.length := by
      have hSelectedLen :
          selected.length ≤ I.system.sets.length :=
        FiniteWitness.nodup_length_le_of_mem hNodup hFamily
      simpa [idxs] using hSelectedLen
    refine ⟨idxs, ?_, ?_⟩
    · exact SetPackingMembership.setPackingIndexCertificate_inputSize_le_poly
        I idxs hIdxLen hBounds
    · exact SetPackingMembership.setPackingIndexVerifier_complete
        hLen hFamily hNodup hDisjoint
  sound := by
    intro I idxs hVerify
    exact SetPackingMembership.setPackingIndexVerifier_sound hVerify

theorem setPackingStructured_TMInNP_index :
    TMInNP setPackingStructuredDecisionProblem :=
  TMInNP.intro setPackingIndexStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
