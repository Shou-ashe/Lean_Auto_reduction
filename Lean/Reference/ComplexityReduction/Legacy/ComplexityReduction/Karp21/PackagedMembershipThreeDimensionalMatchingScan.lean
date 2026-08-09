/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingCore

/-!
Direct standard-TM runner proofs and final NP witness for faithful structured
3-Dimensional Matching.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace ThreeDimensionalMatchingMembership

theorem matchingScanStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod matchingScanAccEncodedType matchingScanInstructionEncodedType)
      matchingScanAccEncodedType
      matchingScanStep := by
  let X := EncodedType.prod matchingScanAccEncodedType matchingScanInstructionEncodedType
  let A := matchingScanAccEncodedType
  let SeenTail := EncodedType.prod setStructuredEncodedType setStructuredEncodedType
  let SeenOK := EncodedType.prod matchingScanSeenEncodedType EncodedType.bool
  let AccTail := EncodedType.prod tripleListStructuredEncodedType SeenOK
  let PayloadTail := EncodedType.prod tripleListStructuredEncodedType tripleStructuredEncodedType
  let NatPair := EncodedType.prod EncodedType.nat EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst matchingScanAccEncodedType matchingScanInstructionEncodedType
  have hInstr : TMPolyTimeMap X matchingScanInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd matchingScanAccEncodedType matchingScanInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool matchingScanPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, matchingScanInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X matchingScanPayloadEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool matchingScanPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, matchingScanInstructionEncodedType, X] using hComp
  have hBoundsAcc : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst tripleStructuredEncodedType AccTail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, matchingScanAccEncodedType, AccTail, X] using hComp
  have hAccTail : TMPolyTimeMap X AccTail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd tripleStructuredEncodedType AccTail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, matchingScanAccEncodedType, AccTail, X] using hComp
  have hSourceAcc : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst tripleListStructuredEncodedType SeenOK
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, AccTail, X] using hComp
  have hSeenOK : TMPolyTimeMap X SeenOK (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd tripleListStructuredEncodedType SeenOK
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, AccTail, X] using hComp
  have hSeen : TMPolyTimeMap X matchingScanSeenEncodedType
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst matchingScanSeenEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hSeenOK
    simpa [Function.comp, SeenOK, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd matchingScanSeenEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hSeenOK
    simpa [Function.comp, SeenOK, X] using hComp
  have hSeenX : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.2.2.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType SeenTail
    have hComp := TMPolyTimeMap.comp hFst hSeen
    simpa [Function.comp, matchingScanSeenEncodedType, SeenTail, X] using hComp
  have hSeenTail : TMPolyTimeMap X SeenTail (fun p : X.Carrier => p.1.2.2.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType SeenTail
    have hComp := TMPolyTimeMap.comp hSnd hSeen
    simpa [Function.comp, matchingScanSeenEncodedType, SeenTail, X] using hComp
  have hSeenY : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.2.2.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSeenTail
    simpa [Function.comp, SeenTail, X] using hComp
  have hSeenZ : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.2.2.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSeenTail
    simpa [Function.comp, SeenTail, X] using hComp
  have hPayloadBounds : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst tripleStructuredEncodedType PayloadTail
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, matchingScanPayloadEncodedType, PayloadTail, X] using hComp
  have hPayloadTail : TMPolyTimeMap X PayloadTail (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd tripleStructuredEncodedType PayloadTail
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, matchingScanPayloadEncodedType, PayloadTail, X] using hComp
  have hPayloadSource : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst tripleListStructuredEncodedType tripleStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayloadTail
    simpa [Function.comp, PayloadTail, X] using hComp
  have hTriple : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd tripleListStructuredEncodedType tripleStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayloadTail
    simpa [Function.comp, PayloadTail, X] using hComp
  have hTripleX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat NatPair
    have hComp := TMPolyTimeMap.comp hFst hTriple
    simpa [Function.comp, tripleStructuredEncodedType, NatPair, X] using hComp
  have hTripleTail : TMPolyTimeMap X NatPair (fun p : X.Carrier => p.2.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat NatPair
    have hComp := TMPolyTimeMap.comp hSnd hTriple
    simpa [Function.comp, tripleStructuredEncodedType, NatPair, X] using hComp
  have hTripleY : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTripleTail
    simpa [Function.comp, NatPair, X] using hComp
  have hTripleZ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTripleTail
    simpa [Function.comp, NatPair, X] using hComp
  have hEmptySet : TMPolyTimeMap X setStructuredEncodedType (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X setStructuredEncodedType []
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hEmptySeenTail : TMPolyTimeMap X SeenTail
      (fun _ : X.Carrier => (([] : List Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hEmptySet hEmptySet
  have hEmptySeen : TMPolyTimeMap X matchingScanSeenEncodedType
      (fun _ : X.Carrier => (([] : List Nat), (([] : List Nat), ([] : List Nat)))) := by
    have hOut := TMPolyTimeMap.prod_mk hEmptySet hEmptySeenTail
    simpa [matchingScanSeenEncodedType, SeenTail] using hOut
  have hFalseSeenOK : TMPolyTimeMap X SeenOK
      (fun _ : X.Carrier =>
        ((([] : List Nat), (([] : List Nat), ([] : List Nat))), true)) :=
    TMPolyTimeMap.prod_mk hEmptySeen hTrue
  have hFalseTail : TMPolyTimeMap X AccTail
      (fun p : X.Carrier =>
        (p.2.2.2.1, (((([] : List Nat), (([] : List Nat), ([] : List Nat))), true)))) :=
    TMPolyTimeMap.prod_mk hPayloadSource hFalseSeenOK
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.2.2.1,
          (p.2.2.2.1, (((([] : List Nat), (([] : List Nat), ([] : List Nat))), true))))) := by
    have hOut := TMPolyTimeMap.prod_mk hPayloadBounds hFalseTail
    simpa [A, matchingScanAccEncodedType, AccTail, SeenOK] using hOut
  have hNewSeenXInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
      (fun p : X.Carrier => (p.2.2.2.2.1, p.1.2.2.1.1)) :=
    TMPolyTimeMap.prod_mk hTripleX hSeenX
  have hNewSeenX : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2.2.1 :: p.1.2.2.1.1) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons EncodedType.nat) hNewSeenXInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hNewSeenYInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
      (fun p : X.Carrier => (p.2.2.2.2.2.1, p.1.2.2.1.2.1)) :=
    TMPolyTimeMap.prod_mk hTripleY hSeenY
  have hNewSeenY : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2.2.2.1 :: p.1.2.2.1.2.1) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons EncodedType.nat) hNewSeenYInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hNewSeenZInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
      (fun p : X.Carrier => (p.2.2.2.2.2.2, p.1.2.2.1.2.2)) :=
    TMPolyTimeMap.prod_mk hTripleZ hSeenZ
  have hNewSeenZ : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2.2.2.2 :: p.1.2.2.1.2.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons EncodedType.nat) hNewSeenZInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hContainsXInput : TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
      (fun p : X.Carrier => (p.2.2.2.2.1, p.1.2.2.1.1)) := by
    simpa [HittingSet.setContainsInstructionInputEncodedType] using hNewSeenXInput
  have hContainsX : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2.2.2.1, p.1.2.2.1.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsXInput
    simpa [Function.comp, X] using hComp
  have hNotX : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => Bool.not (HittingSet.setContainsBool (p.2.2.2.2.1, p.1.2.2.1.1))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hContainsX
    simpa [Function.comp, X] using hComp
  have hContainsYInput : TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
      (fun p : X.Carrier => (p.2.2.2.2.2.1, p.1.2.2.1.2.1)) := by
    simpa [HittingSet.setContainsInstructionInputEncodedType] using hNewSeenYInput
  have hContainsY : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2.2.2.2.1, p.1.2.2.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsYInput
    simpa [Function.comp, X] using hComp
  have hNotY : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.1, p.1.2.2.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hContainsY
    simpa [Function.comp, X] using hComp
  have hContainsZInput : TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
      (fun p : X.Carrier => (p.2.2.2.2.2.2, p.1.2.2.1.2.2)) := by
    simpa [HittingSet.setContainsInstructionInputEncodedType] using hNewSeenZInput
  have hContainsZ : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2.2.2.2.2, p.1.2.2.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsZInput
    simpa [Function.comp, X] using hComp
  have hNotZ : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.2, p.1.2.2.1.2.2))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hContainsZ
    simpa [Function.comp, X] using hComp
  have hNotYZInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.1, p.1.2.2.1.2.1)),
          Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.2, p.1.2.2.1.2.2)))) :=
    TMPolyTimeMap.prod_mk hNotY hNotZ
  have hNotYZ : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.1, p.1.2.2.1.2.1)),
            Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.2, p.1.2.2.1.2.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hNotYZInput
    simpa [Function.comp, X] using hComp
  have hFreshInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (Bool.not (HittingSet.setContainsBool (p.2.2.2.2.1, p.1.2.2.1.1)),
          graphBoolAndPair
            (Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.1, p.1.2.2.1.2.1)),
              Bool.not (HittingSet.setContainsBool (p.2.2.2.2.2.2, p.1.2.2.1.2.2))))) :=
    TMPolyTimeMap.prod_mk hNotX hNotYZ
  have hFresh : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => matchingLocalFreshBool p.1.2.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hFreshInput
    simpa [Function.comp, matchingLocalFreshBool, X] using hComp
  have hBoundsInput : TMPolyTimeMap X tripleBoundsInputEncodedType
      (fun p : X.Carrier => (p.1.1, p.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hBoundsAcc hTriple
  have hBoundsOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => tripleWithinBoundsBool (p.1.1, p.2.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp tripleWithinBoundsBool_tm_polytime hBoundsInput
    simpa [Function.comp, tripleBoundsInputEncodedType, X] using hComp
  have hContainsTripleInput : TMPolyTimeMap X tripleContainsInputEncodedType
      (fun p : X.Carrier => (p.2.2.2.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hTriple hSourceAcc
  have hContainsTriple : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => tripleContainsBool (p.2.2.2.2, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp tripleContainsBool_tm_polytime hContainsTripleInput
    simpa [Function.comp, tripleContainsInputEncodedType, X] using hComp
  have hContainsFreshInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (tripleContainsBool (p.2.2.2.2, p.1.2.1),
          matchingLocalFreshBool p.1.2.2.1 p.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hContainsTriple hFresh
  have hContainsFresh : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (tripleContainsBool (p.2.2.2.2, p.1.2.1),
            matchingLocalFreshBool p.1.2.2.1 p.2.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hContainsFreshInput
    simpa [Function.comp, X] using hComp
  have hLocalOKInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (tripleWithinBoundsBool (p.1.1, p.2.2.2.2),
          graphBoolAndPair
            (tripleContainsBool (p.2.2.2.2, p.1.2.1),
              matchingLocalFreshBool p.1.2.2.1 p.2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hBoundsOK hContainsFresh
  have hLocalOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => matchingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hLocalOKInput
    simpa [Function.comp, matchingLocalOKBool, X] using hComp
  have hNewOKInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (p.1.2.2.2, matchingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hOk hLocalOK
  have hNewOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2.2, matchingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hNewOKInput
    simpa [Function.comp, X] using hComp
  have hNewSeenTail : TMPolyTimeMap X SeenTail
      (fun p : X.Carrier =>
        (p.2.2.2.2.2.1 :: p.1.2.2.1.2.1,
          p.2.2.2.2.2.2 :: p.1.2.2.1.2.2)) :=
    TMPolyTimeMap.prod_mk hNewSeenY hNewSeenZ
  have hNewSeen : TMPolyTimeMap X matchingScanSeenEncodedType
      (fun p : X.Carrier =>
        (p.2.2.2.2.1 :: p.1.2.2.1.1,
          (p.2.2.2.2.2.1 :: p.1.2.2.1.2.1,
            p.2.2.2.2.2.2 :: p.1.2.2.1.2.2))) := by
    have hOut := TMPolyTimeMap.prod_mk hNewSeenX hNewSeenTail
    simpa [matchingScanSeenEncodedType, SeenTail] using hOut
  have hNewSeenOK : TMPolyTimeMap X SeenOK
      (fun p : X.Carrier =>
        ((p.2.2.2.2.1 :: p.1.2.2.1.1,
            (p.2.2.2.2.2.1 :: p.1.2.2.1.2.1,
              p.2.2.2.2.2.2 :: p.1.2.2.1.2.2)),
          graphBoolAndPair
            (p.1.2.2.2, matchingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hNewSeen hNewOK
  have hTrueTail : TMPolyTimeMap X AccTail
      (fun p : X.Carrier =>
        (p.1.2.1,
          ((p.2.2.2.2.1 :: p.1.2.2.1.1,
              (p.2.2.2.2.2.1 :: p.1.2.2.1.2.1,
                p.2.2.2.2.2.2 :: p.1.2.2.1.2.2)),
            graphBoolAndPair
              (p.1.2.2.2, matchingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hSourceAcc hNewSeenOK
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier => matchingScanElementStep p.1 p.2.2.2.2) := by
    have hOut := TMPolyTimeMap.prod_mk hBoundsAcc hTrueTail
    simpa [matchingScanElementStep, A, matchingScanAccEncodedType, AccTail, SeenOK] using hOut
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => matchingScanElementStep p.2.1 p.2.2.2.2.2
          | false =>
              (p.2.2.2.1,
                (p.2.2.2.2.1,
                  (((([] : List Nat), (([] : List Nat), ([] : List Nat))), true))))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.2.2.1,
          (p.2.2.2.1, (((([] : List Nat), (([] : List Nat), ([] : List Nat))), true)))))
      (fTrue := fun p : X.Carrier => matchingScanElementStep p.1 p.2.2.2.2)
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  simpa [Function.comp, matchingScanStep] using hOut

theorem matchingScanFold_tm_polytime :
    TMPolyTimeMap
      matchingScanInstructionListEncodedType
      matchingScanAccEncodedType
      (fun xs : matchingScanInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => matchingScanStep (acc, x)) matchingScanRunnerInit) := by
  rcases matchingScanStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      matchingScanInstructionEncodedType matchingScanAccEncodedType
      matchingScanStep matchingScanRunnerInit hStep
      (Polynomial.C 1000) (Polynomial.X + Polynomial.C 1000) ?_ ?_
  · intro xs
    simp [matchingScanRunnerInit, matchingScanAccEncodedType, matchingScanSeenEncodedType,
      defaultTriple, tripleStructuredEncodedType, tripleListStructuredEncodedType,
      setStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
      EncodedType.inputSize_nat, EncodedType.inputSize_list_nil]
  · intro source acc instr hInstr
    rcases acc with ⟨bounds, accTail⟩
    rcases accTail with ⟨sourceAcc, seenOK⟩
    rcases seenOK with ⟨seen, ok⟩
    rcases seen with ⟨seenX, seenTail⟩
    rcases seenTail with ⟨seenY, seenZ⟩
    rcases instr with ⟨tag, payload⟩
    rcases payload with ⟨initBounds, payloadTail⟩
    rcases payloadTail with ⟨initSource, t⟩
    cases tag <;>
      simp [matchingScanStep, matchingScanElementStep, matchingScanAccEncodedType,
        matchingScanSeenEncodedType, matchingScanInstructionEncodedType,
        matchingScanPayloadEncodedType, tripleStructuredEncodedType, setStructuredEncodedType,
        tripleListStructuredEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, EncodedType.inputSize_nat, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_nil, Polynomial.eval_add] at hInstr ⊢ <;>
      omega

theorem matchingScanFromInstructions_tm_polytime :
    TMPolyTimeMap
      matchingScanInstructionListEncodedType
      EncodedType.bool
      matchingScanFromInstructions := by
  have hFold := matchingScanFold_tm_polytime
  have hTail1 := TMPolyTimeMap.snd tripleStructuredEncodedType
    (EncodedType.prod tripleListStructuredEncodedType
      (EncodedType.prod matchingScanSeenEncodedType EncodedType.bool))
  have hComp1 := TMPolyTimeMap.comp hTail1 hFold
  have hTail2 := TMPolyTimeMap.snd tripleListStructuredEncodedType
    (EncodedType.prod matchingScanSeenEncodedType EncodedType.bool)
  have hComp2 := TMPolyTimeMap.comp hTail2 hComp1
  have hSnd := TMPolyTimeMap.snd matchingScanSeenEncodedType EncodedType.bool
  have hComp3 := TMPolyTimeMap.comp hSnd hComp2
  simpa [Function.comp, matchingScanFromInstructions, matchingScanAccEncodedType] using hComp3

theorem matchingScanBool_tm_polytime :
    TMPolyTimeMap
      matchingScanInputEncodedType
      EncodedType.bool
      matchingScanBool := by
  have hComp := TMPolyTimeMap.comp matchingScanFromInstructions_tm_polytime
    matchingScanInstructions_tm_polytime
  simpa [Function.comp, matchingScanBool] using hComp

/-! ### Full finite verifier -/

def threeDMInputToTuple (I : ThreeDimensionalMatchingInput) :
    threeDimensionalMatchingTupleStructuredEncodedType.Carrier :=
  (I.xSize, (I.ySize, (I.zSize, (I.triples, I.k))))

theorem threeDMInputToTuple_encode (I : ThreeDimensionalMatchingInput) :
    threeDimensionalMatchingTupleStructuredEncodedType.encode (threeDMInputToTuple I) =
      threeDimensionalMatchingStructuredEncodedType.encode I := by
  rfl

noncomputable def threeDMInputToTupleTMBackedMap :
    TMBackedCostedMap
      threeDimensionalMatchingStructuredEncodedType
      threeDimensionalMatchingTupleStructuredEncodedType
      threeDMInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    threeDimensionalMatchingStructuredEncodedType
    threeDimensionalMatchingTupleStructuredEncodedType
    threeDMInputToTuple
    (Equiv.refl threeDimensionalMatchingTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change threeDimensionalMatchingTupleStructuredEncodedType.encode (threeDMInputToTuple I) =
        (threeDimensionalMatchingStructuredEncodedType.encode I).map id
      simp [threeDMInputToTuple_encode])

def threeDimensionalMatchingStructuredFiniteVerify
    (I : ThreeDimensionalMatchingInput) (cert : List Triple) : Bool :=
  graphBoolAndPair
    (HittingSet.natLeBool (I.k, cert.length),
      matchingScanBool ((I.xSize, I.ySize, I.zSize), (I.triples, cert)))

theorem threeDimensionalMatchingStructuredFiniteVerify_eq_true_iff
    (I : ThreeDimensionalMatchingInput) (cert : List Triple) :
    threeDimensionalMatchingStructuredFiniteVerify I cert = true ↔
      I.k ≤ cert.length ∧
        MatchingFreshOK (I.xSize, I.ySize, I.zSize) I.triples [] [] [] cert := by
  rw [threeDimensionalMatchingStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    HittingSet.natLeBool_eq_true_iff, matchingScanBool_eq_true_iff]

theorem threeDimensionalMatchingVerifier_complete
    {I : ThreeDimensionalMatchingInput} {selected : List Triple}
    (hLen : selected.length ≥ I.k)
    (hMemBounds : ∀ t ∈ selected, t ∈ I.triples ∧ TripleWithinBounds I t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    threeDimensionalMatchingStructuredFiniteVerify I selected = true := by
  refine (threeDimensionalMatchingStructuredFiniteVerify_eq_true_iff I selected).2 ?_
  have hx := ThreeDimensionalMatching.matching_x_projection_nodup_of_disjoint hNodup hDisjoint
  have hy := ThreeDimensionalMatching.matching_y_projection_nodup_of_disjoint hNodup hDisjoint
  have hz := ThreeDimensionalMatching.matching_z_projection_nodup_of_disjoint hNodup hDisjoint
  refine ⟨hLen, ?_⟩
  apply MatchingFreshOK.of_props
  · intro t ht
    rcases hMemBounds t ht with ⟨hMem, hBounds⟩
    exact ⟨hMem, (tripleWithinBoundsForBounds_iff I t).2 hBounds⟩
  · exact hx
  · exact hy
  · exact hz

theorem threeDimensionalMatchingVerifier_sound
    {I : ThreeDimensionalMatchingInput} {cert : List Triple}
    (hVerify : threeDimensionalMatchingStructuredFiniteVerify I cert = true) :
    ThreeDimensionalMatching I := by
  rcases (threeDimensionalMatchingStructuredFiniteVerify_eq_true_iff I cert).1 hVerify with
    ⟨hLen, hFresh⟩
  have hMemBounds := MatchingFreshOK.mem_bounds hFresh
  rcases MatchingFreshOK.projections_nodup hFresh with
    ⟨hx, hy, hz⟩
  have hNodup : cert.Nodup :=
    List.Nodup.of_map (fun t : Triple => t.1) hx
  have hDisjoint : DisjointTriples cert :=
    ThreeDimensionalMatching.disjointTriples_of_coordinate_nodup hx hy hz
  refine ⟨cert, hLen, ?_, hNodup, hDisjoint⟩
  intro t ht
  rcases hMemBounds t ht with ⟨hMem, hBounds⟩
  exact ⟨hMem, (tripleWithinBoundsForBounds_iff I t).1 hBounds⟩

theorem threeDimensionalMatchingStructured_inputSize_eq
    (I : ThreeDimensionalMatchingInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize I =
      I.xSize + (I.ySize + (I.zSize + (tripleListStructuredEncodedType.inputSize I.triples +
        I.k + 8))) := by
  rw [ThreeDimensionalMatching.threeDimensionalMatchingStructured_inputSize_eq]
  simp [EncodedType.inputSize_nat]
  omega

theorem threeDimensionalMatching_triples_length_le_inputSize
    (I : ThreeDimensionalMatchingInput) :
    I.triples.length ≤ threeDimensionalMatchingStructuredEncodedType.inputSize I := by
  have hList :
      I.triples.length ≤ tripleListStructuredEncodedType.inputSize I.triples := by
    simpa [tripleListStructuredEncodedType] using
      Clique.encodedList_length_le_inputSize tripleStructuredEncodedType I.triples
  rw [threeDimensionalMatchingStructured_inputSize_eq]
  omega

theorem threeDimensionalMatching_triple_inputSize_le
    {I : ThreeDimensionalMatchingInput} {t : Triple}
    (ht : t ∈ I.triples) :
    tripleStructuredEncodedType.inputSize t ≤
      threeDimensionalMatchingStructuredEncodedType.inputSize I := by
  have hElem := Clique.encodedList_element_inputSize_le
    (X := tripleStructuredEncodedType) (x := t) (xs := I.triples) ht
  have hElem' :
      tripleStructuredEncodedType.inputSize t ≤
        tripleListStructuredEncodedType.inputSize I.triples := by
    simpa [tripleListStructuredEncodedType] using hElem
  have hList :
      tripleListStructuredEncodedType.inputSize I.triples ≤
        threeDimensionalMatchingStructuredEncodedType.inputSize I := by
    rw [threeDimensionalMatchingStructured_inputSize_eq]
    omega
  exact hElem'.trans hList

theorem threeDimensionalMatchingCertificate_inputSize_le_poly
    (I : ThreeDimensionalMatchingInput) (selected : List Triple)
    (hNodup : selected.Nodup)
    (hMem : ∀ t ∈ selected, t ∈ I.triples) :
    threeDMCertificateEncodedType.inputSize selected ≤
      2 * (threeDimensionalMatchingStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := threeDimensionalMatchingStructuredEncodedType.inputSize I
  have hLen : selected.length ≤ I.triples.length :=
    FiniteWitness.nodup_length_le_of_mem hNodup hMem
  have hTriplesLen : I.triples.length ≤ S := by
    simpa [S] using threeDimensionalMatching_triples_length_le_inputSize I
  have hEach : ∀ t ∈ selected, tripleStructuredEncodedType.inputSize t ≤ S := by
    intro t ht
    simpa [S] using threeDimensionalMatching_triple_inputSize_le (I := I) (hMem t ht)
  have hList := Clique.encodedList_inputSize_le_length_mul_bound
    tripleStructuredEncodedType selected S hEach
  calc
    threeDMCertificateEncodedType.inputSize selected
        ≤ selected.length * (S + 1) := by
          simpa [threeDMCertificateEncodedType, tripleListStructuredEncodedType] using hList
    _ ≤ S * (S + 1) := Nat.mul_le_mul_right (S + 1) (hLen.trans hTriplesLen)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

theorem threeDimensionalMatchingStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod threeDimensionalMatchingStructuredEncodedType threeDMCertificateEncodedType)
      EncodedType.bool
      (fun p : ThreeDimensionalMatchingInput × List Triple =>
        threeDimensionalMatchingStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod threeDimensionalMatchingStructuredEncodedType threeDMCertificateEncodedType
  let Tuple := threeDimensionalMatchingTupleStructuredEncodedType
  have hI : TMPolyTimeMap X threeDimensionalMatchingStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst threeDimensionalMatchingStructuredEncodedType threeDMCertificateEncodedType
  have hCert : TMPolyTimeMap X threeDMCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd threeDimensionalMatchingStructuredEncodedType threeDMCertificateEncodedType
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
  have hCertLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap tripleStructuredEncodedType).tm_polytime hCert
    simpa [Function.comp, threeDMCertificateEncodedType, tripleListStructuredEncodedType, X]
      using hComp
  have hLenInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.k, p.2.length)) :=
    TMPolyTimeMap.prod_mk hK hCertLength
  have hLen : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.natLeBool (p.1.k, p.2.length)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLenInput
    simpa [Function.comp, X] using hComp
  have hBoundsTail : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.ySize, p.1.zSize)) :=
    TMPolyTimeMap.prod_mk hYSize hZSize
  have hBounds : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => (p.1.xSize, p.1.ySize, p.1.zSize)) := by
    have hOut := TMPolyTimeMap.prod_mk hXSize hBoundsTail
    simpa [tripleStructuredEncodedType] using hOut
  have hScanTail : TMPolyTimeMap X
      (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
      (fun p : X.Carrier => (p.1.triples, p.2)) :=
    TMPolyTimeMap.prod_mk hTriples hCert
  have hScanInput : TMPolyTimeMap X matchingScanInputEncodedType
      (fun p : X.Carrier => ((p.1.xSize, p.1.ySize, p.1.zSize), (p.1.triples, p.2))) :=
    TMPolyTimeMap.prod_mk hBounds hScanTail
  have hScan : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        matchingScanBool ((p.1.xSize, p.1.ySize, p.1.zSize), (p.1.triples, p.2))) := by
    have hComp := TMPolyTimeMap.comp matchingScanBool_tm_polytime hScanInput
    simpa [Function.comp, matchingScanInputEncodedType, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (HittingSet.natLeBool (p.1.k, p.2.length),
          matchingScanBool ((p.1.xSize, p.1.ySize, p.1.zSize), (p.1.triples, p.2)))) :=
    TMPolyTimeMap.prod_mk hLen hScan
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, threeDimensionalMatchingStructuredFiniteVerify, X] using hOut

end ThreeDimensionalMatchingMembership

/-- Direct finite-certificate TM verifier for faithful structured 3DM. -/
noncomputable def threeDimensionalMatchingStructuredFiniteTMVerifier :
    TMVerifier threeDimensionalMatchingStructuredDecisionProblem where
  Cert := ThreeDimensionalMatchingMembership.threeDMCertificateEncodedType
  verify := ThreeDimensionalMatchingMembership.threeDimensionalMatchingStructuredFiniteVerify
  verifier_polytime :=
    ThreeDimensionalMatchingMembership.threeDimensionalMatchingStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hLen, hMemBounds, hNodup, hDisjoint⟩
    refine ⟨selected, ?_, ?_⟩
    · exact
        ThreeDimensionalMatchingMembership.threeDimensionalMatchingCertificate_inputSize_le_poly
          I selected hNodup (by
            intro t ht
            exact (hMemBounds t ht).1)
    · exact ThreeDimensionalMatchingMembership.threeDimensionalMatchingVerifier_complete
        hLen hMemBounds hNodup hDisjoint
  sound := by
    intro I cert hVerify
    exact ThreeDimensionalMatchingMembership.threeDimensionalMatchingVerifier_sound hVerify

theorem threeDimensionalMatchingStructured_TMInNP :
    TMInNP threeDimensionalMatchingStructuredDecisionProblem :=
  TMInNP.intro threeDimensionalMatchingStructuredFiniteTMVerifier


end Karp21
end ComplexityReduction
