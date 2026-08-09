/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingScan
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM

/-!
Alternative nat-list certificate verifier for faithful structured
3-Dimensional Matching.

The original verifier uses a selected triple list as its certificate.  This
file adds an equivalent verifier whose certificate is a list of indices into
the input triple family.  The certificate encoding is exactly
`EncodedType.list EncodedType.nat`, so it can reuse the checked nat-list suffix
CNF without pretending that a triple-list encoding is a nat-list suffix.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace ThreeDimensionalMatchingMembership

abbrev threeDMIndexCertificateEncodedType : EncodedType :=
  setStructuredEncodedType

abbrev threeDMIndexDecodeAccEncodedType : EncodedType :=
  EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType

abbrev ThreeDMIndexDecodeAcc :=
  List Triple × List Triple

abbrev threeDMIndexDecodeInstructionEncodedType : EncodedType :=
  EncodedType.sum tripleListStructuredEncodedType EncodedType.nat

abbrev threeDMIndexDecodeInstructionListEncodedType : EncodedType :=
  EncodedType.list threeDMIndexDecodeInstructionEncodedType

abbrev threeDMIndexDecodeInputEncodedType : EncodedType :=
  EncodedType.prod tripleListStructuredEncodedType setStructuredEncodedType

def threeDMIndexDecodeRunnerInit : ThreeDMIndexDecodeAcc :=
  (([] : List Triple), ([] : List Triple))

def threeDMIndexDecodeInitInstruction (source : List Triple) :
    threeDMIndexDecodeInstructionEncodedType.Carrier :=
  Sum.inl source

def threeDMIndexDecodeIndexInstruction (j : Nat) :
    threeDMIndexDecodeInstructionEncodedType.Carrier :=
  Sum.inr j

def tripleListGetD (p : List Triple × Nat) : Triple :=
  EncodedListLookup.getD tripleStructuredEncodedType defaultTriple p

def threeDMIndexDecodeInstructions (p : List Triple × List Nat) :
    List threeDMIndexDecodeInstructionEncodedType.Carrier :=
  threeDMIndexDecodeInitInstruction p.1 ::
    p.2.map threeDMIndexDecodeIndexInstruction

def threeDMIndexDecodeStep
    (p : ThreeDMIndexDecodeAcc × threeDMIndexDecodeInstructionEncodedType.Carrier) :
    ThreeDMIndexDecodeAcc :=
  match p.2 with
  | Sum.inl source => (source, [])
  | Sum.inr j => (p.1.1, p.1.2 ++ [tripleListGetD (p.1.1, j)])

def threeDMIndexDecodeFromInstructions
    (xs : List threeDMIndexDecodeInstructionEncodedType.Carrier) :
    List Triple :=
  (xs.foldl (fun acc instr => threeDMIndexDecodeStep (acc, instr))
    threeDMIndexDecodeRunnerInit).2

def threeDMIndexDecode (p : List Triple × List Nat) : List Triple :=
  threeDMIndexDecodeFromInstructions (threeDMIndexDecodeInstructions p)

theorem tripleListGetD_eq_getD (source : List Triple) (j : Nat) :
    tripleListGetD (source, j) = source.getD j defaultTriple := by
  rfl

theorem threeDMIndexDecodeIndexInstructions_fold_eq
    (idxs : List Nat) (source out : List Triple) :
    (idxs.map threeDMIndexDecodeIndexInstruction).foldl
        (fun acc instr => threeDMIndexDecodeStep (acc, instr)) (source, out) =
      (source, out ++ idxs.map (fun j => source.getD j defaultTriple)) := by
  induction idxs generalizing out with
  | nil =>
      simp
  | cons j idxs ih =>
      have h := ih (out ++ [source.getD j defaultTriple])
      simpa [threeDMIndexDecodeIndexInstruction, threeDMIndexDecodeStep,
        tripleListGetD, EncodedListLookup.getD, List.append_assoc] using h

theorem threeDMIndexDecode_eq_map_getD
    (source : List Triple) (idxs : List Nat) :
    threeDMIndexDecode (source, idxs) =
      idxs.map fun j => source.getD j defaultTriple := by
  change
    (((threeDMIndexDecodeInitInstruction source ::
      idxs.map threeDMIndexDecodeIndexInstruction).foldl
        (fun acc instr => threeDMIndexDecodeStep (acc, instr))
        threeDMIndexDecodeRunnerInit).2) =
      idxs.map fun j => source.getD j defaultTriple
  rw [List.foldl_cons]
  have hFold := threeDMIndexDecodeIndexInstructions_fold_eq idxs source []
  simpa [threeDMIndexDecodeRunnerInit, threeDMIndexDecodeInitInstruction,
    threeDMIndexDecodeStep] using congrArg Prod.snd hFold

theorem tripleList_getD_inputSize_le
    (source : List Triple) (j : Nat) :
    tripleStructuredEncodedType.inputSize (source.getD j defaultTriple) ≤
      tripleListStructuredEncodedType.inputSize source +
        tripleStructuredEncodedType.inputSize defaultTriple := by
  simpa [tripleListStructuredEncodedType] using
    EncodedListLookup.getD_inputSize_le tripleStructuredEncodedType defaultTriple source j

theorem threeDMIndexDecodeInitInstruction_tm_polytime :
    TMPolyTimeMap
      tripleListStructuredEncodedType
      threeDMIndexDecodeInstructionEncodedType
      threeDMIndexDecodeInitInstruction := by
  simpa [threeDMIndexDecodeInstructionEncodedType,
    threeDMIndexDecodeInitInstruction] using
    TMPolyTimeMap.inl tripleListStructuredEncodedType EncodedType.nat

theorem threeDMIndexDecodeIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      threeDMIndexDecodeInstructionEncodedType
      threeDMIndexDecodeIndexInstruction := by
  simpa [threeDMIndexDecodeInstructionEncodedType,
    threeDMIndexDecodeIndexInstruction] using
    TMPolyTimeMap.inr tripleListStructuredEncodedType EncodedType.nat

theorem threeDMIndexDecodeInstructions_tm_polytime :
    TMPolyTimeMap
      threeDMIndexDecodeInputEncodedType
      threeDMIndexDecodeInstructionListEncodedType
      threeDMIndexDecodeInstructions := by
  let X := threeDMIndexDecodeInputEncodedType
  have hSource : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, threeDMIndexDecodeInputEncodedType] using
      TMPolyTimeMap.fst tripleListStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, threeDMIndexDecodeInputEncodedType] using
      TMPolyTimeMap.snd tripleListStructuredEncodedType setStructuredEncodedType
  have hInit : TMPolyTimeMap X threeDMIndexDecodeInstructionEncodedType
      (fun p : X.Carrier => threeDMIndexDecodeInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp threeDMIndexDecodeInitInstruction_tm_polytime
      hSource
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X threeDMIndexDecodeInstructionListEncodedType
        (fun p : X.Carrier => [threeDMIndexDecodeInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton threeDMIndexDecodeInstructionEncodedType) hInit
    simpa [Function.comp, threeDMIndexDecodeInstructionListEncodedType, X] using hComp
  have hIdxInstructions :
      TMPolyTimeMap X threeDMIndexDecodeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map threeDMIndexDecodeIndexInstruction) := by
    have hMap :=
      TMPolyTimeMap.list_map threeDMIndexDecodeIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hIdxs
    simpa [Function.comp, threeDMIndexDecodeInstructionListEncodedType,
      setStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod threeDMIndexDecodeInstructionListEncodedType
          threeDMIndexDecodeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([threeDMIndexDecodeInitInstruction p.1],
            p.2.map threeDMIndexDecodeIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hIdxInstructions
  have hAppend :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append threeDMIndexDecodeInstructionEncodedType)
      hAppendInput
  simpa [Function.comp, threeDMIndexDecodeInstructions,
    threeDMIndexDecodeInstructionListEncodedType, X] using hAppend

theorem tripleListGetD_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)
      tripleStructuredEncodedType
      tripleListGetD := by
  simpa [tripleListGetD, tripleListStructuredEncodedType] using
    EncodedListLookup.getD_tm_polytime tripleStructuredEncodedType defaultTriple

theorem threeDMIndexDecodeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod threeDMIndexDecodeAccEncodedType
        threeDMIndexDecodeInstructionEncodedType)
      threeDMIndexDecodeAccEncodedType
      threeDMIndexDecodeStep := by
  let A := threeDMIndexDecodeAccEncodedType
  have hLeft :
      TMPolyTimeMap tripleListStructuredEncodedType A
        (fun source : List Triple => (source, ([] : List Triple))) := by
    have hSource : TMPolyTimeMap tripleListStructuredEncodedType
        tripleListStructuredEncodedType id :=
      TMPolyTimeMap.id tripleListStructuredEncodedType
    have hEmpty : TMPolyTimeMap tripleListStructuredEncodedType
        tripleListStructuredEncodedType (fun _ => ([] : List Triple)) :=
      TMPolyTimeMap.const tripleListStructuredEncodedType tripleListStructuredEncodedType []
    have hOut := TMPolyTimeMap.prod_mk hSource hEmpty
    simpa [A, threeDMIndexDecodeAccEncodedType] using hOut
  have hRight :
      TMPolyTimeMap
        (EncodedType.prod A EncodedType.nat)
        A
        (fun p : A.Carrier × Nat =>
          ((show List Triple from p.1.1),
            (show List Triple from p.1.2) ++
              [tripleListGetD ((show List Triple from p.1.1), p.2)])) := by
    let X := EncodedType.prod A EncodedType.nat
    have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
      simpa [X] using TMPolyTimeMap.fst A EncodedType.nat
    have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
      simpa [X] using TMPolyTimeMap.snd A EncodedType.nat
    have hSource : TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier => p.1.1) := by
      have hFst := TMPolyTimeMap.fst tripleListStructuredEncodedType
        tripleListStructuredEncodedType
      have hComp := TMPolyTimeMap.comp hFst hAcc
      simpa [Function.comp, A, threeDMIndexDecodeAccEncodedType, X] using hComp
    have hOut : TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd tripleListStructuredEncodedType
        tripleListStructuredEncodedType
      have hComp := TMPolyTimeMap.comp hSnd hAcc
      simpa [Function.comp, A, threeDMIndexDecodeAccEncodedType, X] using hComp
    have hLookupInput :
        TMPolyTimeMap X
          (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)
          (fun p : X.Carrier => ((show List Triple from p.1.1), p.2)) :=
      TMPolyTimeMap.prod_mk hSource hJ
    have hLookup : TMPolyTimeMap X tripleStructuredEncodedType
        (fun p : X.Carrier =>
          tripleListGetD ((show List Triple from p.1.1), p.2)) := by
      have hComp := TMPolyTimeMap.comp tripleListGetD_tm_polytime hLookupInput
      simpa [Function.comp, X] using hComp
    have hSingleton : TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          [tripleListGetD ((show List Triple from p.1.1), p.2)]) := by
      have hComp := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton tripleStructuredEncodedType) hLookup
      simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
    have hAppendInput :
        TMPolyTimeMap X
          (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
          (fun p : X.Carrier =>
            ((show List Triple from p.1.2),
              [tripleListGetD ((show List Triple from p.1.1), p.2)])) :=
      TMPolyTimeMap.prod_mk hOut hSingleton
    have hNewOut : TMPolyTimeMap X tripleListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List Triple from p.1.2) ++
            [tripleListGetD ((show List Triple from p.1.1), p.2)]) := by
      have hComp := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append tripleStructuredEncodedType) hAppendInput
      simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
    have hPair := TMPolyTimeMap.prod_mk hSource hNewOut
    simpa [A, threeDMIndexDecodeAccEncodedType, X] using hPair
  have hChoice :=
    prodSumChoice_tm_polytime A tripleListStructuredEncodedType EncodedType.nat
  have hBranches := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem threeDMIndexDecodeFold_tm_polytime :
    TMPolyTimeMap
      threeDMIndexDecodeInstructionListEncodedType
      threeDMIndexDecodeAccEncodedType
      (fun xs : threeDMIndexDecodeInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => threeDMIndexDecodeStep (acc, instr))
          threeDMIndexDecodeRunnerInit) := by
  rcases threeDMIndexDecodeStep_tm_polytime with ⟨hStep⟩
  let Inv : Nat → threeDMIndexDecodeAccEncodedType.Carrier → Prop :=
    fun N acc => tripleListStructuredEncodedType.inputSize
      (show List Triple from acc.1) ≤ N
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      threeDMIndexDecodeInstructionEncodedType threeDMIndexDecodeAccEncodedType
      threeDMIndexDecodeStep threeDMIndexDecodeRunnerInit hStep
      (Polynomial.C 1000) (Polynomial.C 10 * Polynomial.X + Polynomial.C 2000)
      Inv ?_ ?_
  · intro xs
    constructor
    · dsimp [Inv]
      have hNil : tripleListStructuredEncodedType.inputSize ([] : List Triple) = 0 := by
        native_decide
      simp [threeDMIndexDecodeRunnerInit, hNil]
    · change threeDMIndexDecodeAccEncodedType.inputSize
          threeDMIndexDecodeRunnerInit ≤
        (Polynomial.C 1000).eval
          (threeDMIndexDecodeInstructionEncodedType.list.inputSize xs)
      have hInit :
          threeDMIndexDecodeAccEncodedType.inputSize threeDMIndexDecodeRunnerInit ≤
            1000 := by
        native_decide
      simpa using hInit
  · intro source acc instr hInv hInstr
    rcases acc with ⟨sourceTriples, out⟩
    change List Triple at sourceTriples out
    have hSourceSize :
        tripleListStructuredEncodedType.inputSize sourceTriples ≤
          threeDMIndexDecodeInstructionListEncodedType.inputSize source := by
      simpa [Inv] using hInv
    cases instr with
    | inl initSource =>
        have hInitLe :
            tripleListStructuredEncodedType.inputSize initSource ≤
              threeDMIndexDecodeInstructionEncodedType.inputSize (Sum.inl initSource) := by
          simp [EncodedType.inputSize, EncodedType.sum]
        have hInitLeSource := hInitLe.trans hInstr
        constructor
        · simpa [Inv, threeDMIndexDecodeStep] using hInitLeSource
        · have hNil : tripleListStructuredEncodedType.inputSize ([] : List Triple) = 0 := by
            native_decide
          simp [threeDMIndexDecodeStep, threeDMIndexDecodeAccEncodedType,
            threeDMIndexDecodeInstructionEncodedType,
            EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, hNil] at hInv hInstr hInitLeSource ⊢
          omega
    | inr j =>
        have hGetD :
            tripleStructuredEncodedType.inputSize (tripleListGetD (sourceTriples, j)) ≤
              tripleListStructuredEncodedType.inputSize sourceTriples +
                tripleStructuredEncodedType.inputSize defaultTriple := by
          simpa [tripleListGetD, EncodedListLookup.getD] using
            tripleList_getD_inputSize_le sourceTriples j
        have hAppend :
            tripleListStructuredEncodedType.inputSize
                (out ++ [tripleListGetD (sourceTriples, j)]) =
              tripleListStructuredEncodedType.inputSize out +
                tripleStructuredEncodedType.inputSize
                  (tripleListGetD (sourceTriples, j)) + 1 := by
          simpa [tripleListStructuredEncodedType, EncodedType.inputSize_list_cons,
            EncodedType.inputSize_list_nil] using
            Clique.encodedList_inputSize_append tripleStructuredEncodedType out
              [tripleListGetD (sourceTriples, j)]
        have hDefault :
            tripleStructuredEncodedType.inputSize defaultTriple ≤ 1000 := by
          native_decide
        constructor
        · simpa [Inv, threeDMIndexDecodeStep] using hInv
        · simp [threeDMIndexDecodeStep, threeDMIndexDecodeAccEncodedType,
            threeDMIndexDecodeInstructionEncodedType,
            threeDMIndexDecodeInstructionListEncodedType,
            EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, hAppend] at hInv hSourceSize hGetD hDefault ⊢
          omega

theorem threeDMIndexDecodeFromInstructions_tm_polytime :
    TMPolyTimeMap
      threeDMIndexDecodeInstructionListEncodedType
      tripleListStructuredEncodedType
      threeDMIndexDecodeFromInstructions := by
  have hFold := threeDMIndexDecodeFold_tm_polytime
  have hOut := TMPolyTimeMap.snd tripleListStructuredEncodedType
    tripleListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, threeDMIndexDecodeFromInstructions,
    threeDMIndexDecodeAccEncodedType] using hComp

theorem threeDMIndexDecode_tm_polytime :
    TMPolyTimeMap
      threeDMIndexDecodeInputEncodedType
      tripleListStructuredEncodedType
      threeDMIndexDecode := by
  have hComp := TMPolyTimeMap.comp threeDMIndexDecodeFromInstructions_tm_polytime
    threeDMIndexDecodeInstructions_tm_polytime
  simpa [Function.comp, threeDMIndexDecode] using hComp

def threeDMIndexStructuredFiniteVerify
    (I : ThreeDimensionalMatchingInput) (idxs : List Nat) : Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (I.k, idxs.length),
      graphBoolAndPair
        (HittingSet.boundedNatListBool (I.triples.length, idxs),
          matchingScanBool
            ((I.xSize, I.ySize, I.zSize),
              (I.triples, threeDMIndexDecode (I.triples, idxs)))))

theorem threeDMIndexStructuredFiniteVerify_eq_true_iff
    (I : ThreeDimensionalMatchingInput) (idxs : List Nat) :
    threeDMIndexStructuredFiniteVerify I idxs = true ↔
      I.k ≤ idxs.length ∧
        (∀ j ∈ idxs, j < I.triples.length) ∧
          MatchingFreshOK (I.xSize, I.ySize, I.zSize) I.triples [] [] []
            (idxs.map fun j => I.triples.getD j defaultTriple) := by
  rw [threeDMIndexStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff, matchingScanBool_eq_true_iff,
    threeDMIndexDecode_eq_map_getD]

theorem threeDMIndexStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod threeDimensionalMatchingStructuredEncodedType
        threeDMIndexCertificateEncodedType)
      EncodedType.bool
      (fun p : ThreeDimensionalMatchingInput × List Nat =>
        threeDMIndexStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod threeDimensionalMatchingStructuredEncodedType
    threeDMIndexCertificateEncodedType
  let Tuple := threeDimensionalMatchingTupleStructuredEncodedType
  have hI : TMPolyTimeMap X threeDimensionalMatchingStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, threeDMIndexCertificateEncodedType] using
      TMPolyTimeMap.fst threeDimensionalMatchingStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, threeDMIndexCertificateEncodedType] using
      TMPolyTimeMap.snd threeDimensionalMatchingStructuredEncodedType setStructuredEncodedType
  have hTuple : TMPolyTimeMap X Tuple (fun p : X.Carrier => threeDMInputToTuple p.1) := by
    have hComp := TMPolyTimeMap.comp threeDMInputToTupleTMBackedMap.tm_polytime hI
    simpa [Function.comp, Tuple, X] using hComp
  have hXSize : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.xSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)))
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, threeDMInputToTuple, Tuple, X] using hComp
  have hTail1 : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)))
      (fun p : X.Carrier => (threeDMInputToTuple p.1).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)))
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, Tuple, X] using hComp
  have hYSize : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.ySize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hFst hTail1
    simpa [Function.comp, threeDMInputToTuple, X] using hComp
  have hTail2 : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat))
      (fun p : X.Carrier => (threeDMInputToTuple p.1).2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hTail1
    simpa [Function.comp, X] using hComp
  have hZSize : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.zSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hTail2
    simpa [Function.comp, threeDMInputToTuple, X] using hComp
  have hTail3 : TMPolyTimeMap X
      (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)
      (fun p : X.Carrier => (threeDMInputToTuple p.1).2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod tripleListStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hTail2
    simpa [Function.comp, X] using hComp
  have hTriples : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.1.triples) := by
    have hFst := TMPolyTimeMap.fst tripleListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail3
    simpa [Function.comp, threeDMInputToTuple, X] using hComp
  have hK : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hSnd := TMPolyTimeMap.snd tripleListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail3
    simpa [Function.comp, threeDMInputToTuple, X] using hComp
  have hTriplesLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.triples.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap tripleStructuredEncodedType).tm_polytime hTriples
    simpa [Function.comp, tripleListStructuredEncodedType, X] using hComp
  have hIdxLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hIdxs
    simpa [Function.comp, threeDMIndexCertificateEncodedType,
      setStructuredEncodedType, X] using hComp
  have hLenInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.k, p.2.length)) :=
    TMPolyTimeMap.prod_mk hK hIdxLength
  have hLen : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.natLeBool (p.1.k, p.2.length)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLenInput
    simpa [Function.comp, X] using hComp
  have hBoundInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.triples.length, p.2)) :=
    TMPolyTimeMap.prod_mk hTriplesLength hIdxs
  have hBound : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        HittingSet.boundedNatListBool (p.1.triples.length, p.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hBoundInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X]
      using hComp
  have hDecodeInput :
      TMPolyTimeMap X threeDMIndexDecodeInputEncodedType
        (fun p : X.Carrier => (p.1.triples, p.2)) :=
    TMPolyTimeMap.prod_mk hTriples hIdxs
  have hDecoded : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => threeDMIndexDecode (p.1.triples, p.2)) := by
    have hComp := TMPolyTimeMap.comp threeDMIndexDecode_tm_polytime hDecodeInput
    simpa [Function.comp, threeDMIndexDecodeInputEncodedType, X] using hComp
  have hBoundsTail : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.ySize, p.1.zSize)) :=
    TMPolyTimeMap.prod_mk hYSize hZSize
  have hBounds : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => (p.1.xSize, p.1.ySize, p.1.zSize)) := by
    have hOut := TMPolyTimeMap.prod_mk hXSize hBoundsTail
    simpa [tripleStructuredEncodedType] using hOut
  have hScanTail : TMPolyTimeMap X
      (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
      (fun p : X.Carrier => (p.1.triples, threeDMIndexDecode (p.1.triples, p.2))) :=
    TMPolyTimeMap.prod_mk hTriples hDecoded
  have hScanInput : TMPolyTimeMap X matchingScanInputEncodedType
      (fun p : X.Carrier =>
        ((p.1.xSize, p.1.ySize, p.1.zSize),
          (p.1.triples, threeDMIndexDecode (p.1.triples, p.2)))) :=
    TMPolyTimeMap.prod_mk hBounds hScanTail
  have hScan : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        matchingScanBool
          ((p.1.xSize, p.1.ySize, p.1.zSize),
            (p.1.triples, threeDMIndexDecode (p.1.triples, p.2)))) := by
    have hComp := TMPolyTimeMap.comp matchingScanBool_tm_polytime hScanInput
    simpa [Function.comp, matchingScanInputEncodedType, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.triples.length, p.2),
            matchingScanBool
              ((p.1.xSize, p.1.ySize, p.1.zSize),
                (p.1.triples, threeDMIndexDecode (p.1.triples, p.2))))) :=
    TMPolyTimeMap.prod_mk hBound hScan
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (p.1.triples.length, p.2),
            matchingScanBool
              ((p.1.xSize, p.1.ySize, p.1.zSize),
                (p.1.triples, threeDMIndexDecode (p.1.triples, p.2))))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.natLeBool (p.1.k, p.2.length),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.triples.length, p.2),
                matchingScanBool
                  ((p.1.xSize, p.1.ySize, p.1.zSize),
                    (p.1.triples, threeDMIndexDecode (p.1.triples, p.2)))))) :=
    TMPolyTimeMap.prod_mk hLen hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, threeDMIndexStructuredFiniteVerify, X] using hAll

theorem threeDMIndexCertificate_inputSize_le_poly
    (I : ThreeDimensionalMatchingInput) (idxs : List Nat)
    (hLen : idxs.length ≤ I.triples.length)
    (hBounds : ∀ j ∈ idxs, j < I.triples.length) :
    threeDMIndexCertificateEncodedType.inputSize idxs ≤
      2 * (threeDimensionalMatchingStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := threeDimensionalMatchingStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le I.triples.length idxs hBounds
  have hTriples : I.triples.length ≤ S := by
    simpa [S] using threeDimensionalMatching_triples_length_le_inputSize I
  calc
    threeDMIndexCertificateEncodedType.inputSize idxs
        ≤ idxs.length * (I.triples.length + 1) := by
          simpa [threeDMIndexCertificateEncodedType] using hCert
    _ ≤ I.triples.length * (I.triples.length + 1) :=
        Nat.mul_le_mul_right (I.triples.length + 1) hLen
    _ ≤ S * (S + 1) := Nat.mul_le_mul hTriples (Nat.succ_le_succ hTriples)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

theorem threeDMIndexVerifier_complete
    {I : ThreeDimensionalMatchingInput} {selected : List Triple}
    (hLen : selected.length ≥ I.k)
    (hMemBounds : ∀ t ∈ selected, t ∈ I.triples ∧ TripleWithinBounds I t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    threeDMIndexStructuredFiniteVerify I (selected.map I.triples.idxOf) = true := by
  classical
  refine (threeDMIndexStructuredFiniteVerify_eq_true_iff I
    (selected.map I.triples.idxOf)).2 ?_
  have hBounds : ∀ j ∈ selected.map I.triples.idxOf,
      j < I.triples.length := by
    intro j hj
    rcases List.mem_map.mp hj with ⟨t, ht, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hMemBounds t ht).1
  have hDecoded :
      (selected.map I.triples.idxOf).map
          (fun j => I.triples.getD j defaultTriple) =
        selected := by
    simpa [FiniteWitness.valuesFromIndices] using
      (FiniteWitness.valuesFromIdxOf_eq
        (values := I.triples) (fallback := defaultTriple) (by
          intro t ht
          exact (hMemBounds t ht).1))
  have hx := ThreeDimensionalMatching.matching_x_projection_nodup_of_disjoint
    hNodup hDisjoint
  have hy := ThreeDimensionalMatching.matching_y_projection_nodup_of_disjoint
    hNodup hDisjoint
  have hz := ThreeDimensionalMatching.matching_z_projection_nodup_of_disjoint
    hNodup hDisjoint
  have hFresh : MatchingFreshOK (I.xSize, I.ySize, I.zSize) I.triples [] [] []
      ((selected.map I.triples.idxOf).map fun j => I.triples.getD j defaultTriple) := by
    rw [hDecoded]
    apply MatchingFreshOK.of_props
    · intro t ht
      rcases hMemBounds t ht with ⟨hMem, hBoundsT⟩
      exact ⟨hMem, (tripleWithinBoundsForBounds_iff I t).2 hBoundsT⟩
    · exact hx
    · exact hy
    · exact hz
  refine ⟨?_, hBounds, hFresh⟩
  simpa using hLen

theorem threeDMIndexVerifier_sound
    {I : ThreeDimensionalMatchingInput} {idxs : List Nat}
    (hVerify : threeDMIndexStructuredFiniteVerify I idxs = true) :
    ThreeDimensionalMatching I := by
  rcases (threeDMIndexStructuredFiniteVerify_eq_true_iff I idxs).1 hVerify with
    ⟨hLen, _hBounds, hFresh⟩
  let selected := idxs.map fun j => I.triples.getD j defaultTriple
  have hMemBounds := MatchingFreshOK.mem_bounds hFresh
  rcases MatchingFreshOK.projections_nodup hFresh with
    ⟨hx, hy, hz⟩
  have hNodup : selected.Nodup :=
    List.Nodup.of_map (fun t : Triple => t.1) hx
  have hDisjoint : DisjointTriples selected :=
    ThreeDimensionalMatching.disjointTriples_of_coordinate_nodup hx hy hz
  refine ⟨selected, ?_, ?_, hNodup, hDisjoint⟩
  · simpa [selected] using hLen
  · intro t ht
    rcases hMemBounds t (by simpa [selected] using ht) with ⟨hMem, hBoundsT⟩
    exact ⟨hMem, (tripleWithinBoundsForBounds_iff I t).1 hBoundsT⟩

end ThreeDimensionalMatchingMembership

/--
Alternative direct finite-certificate TM verifier for faithful structured 3DM
whose certificate is a nat-list of selected source-triple indices.
-/
noncomputable def threeDimensionalMatchingIndexStructuredFiniteTMVerifier :
    TMVerifier threeDimensionalMatchingStructuredDecisionProblem where
  Cert := ThreeDimensionalMatchingMembership.threeDMIndexCertificateEncodedType
  verify := ThreeDimensionalMatchingMembership.threeDMIndexStructuredFiniteVerify
  verifier_polytime :=
    ThreeDimensionalMatchingMembership.threeDMIndexStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hMemBounds, hNodup, hDisjoint⟩
    let idxs := selected.map I.triples.idxOf
    have hBounds : ∀ j ∈ idxs, j < I.triples.length := by
      intro j hj
      rcases List.mem_map.mp hj with ⟨t, ht, rfl⟩
      exact List.idxOf_lt_length_iff.mpr (hMemBounds t ht).1
    have hIdxLen : idxs.length ≤ I.triples.length := by
      have hSelectedLen :
          selected.length ≤ I.triples.length :=
        FiniteWitness.nodup_length_le_of_mem hNodup (by
          intro t ht
          exact (hMemBounds t ht).1)
      simpa [idxs] using hSelectedLen
    refine ⟨idxs, ?_, ?_⟩
    · exact ThreeDimensionalMatchingMembership.threeDMIndexCertificate_inputSize_le_poly
        I idxs hIdxLen hBounds
    · exact ThreeDimensionalMatchingMembership.threeDMIndexVerifier_complete
        hLen hMemBounds hNodup hDisjoint
  sound := by
    intro I idxs hVerify
    exact ThreeDimensionalMatchingMembership.threeDMIndexVerifier_sound hVerify

theorem threeDimensionalMatchingStructured_TMInNP_index :
    TMInNP threeDimensionalMatchingStructuredDecisionProblem :=
  TMInNP.intro threeDimensionalMatchingIndexStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
