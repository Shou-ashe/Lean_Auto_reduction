/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.FamilyRunner

/-!
Direct TM-backed structured assembly for the faithful Set Covering to Hitting
Set route.
-/

namespace ComplexityReduction
namespace Karp21
namespace HittingSet

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Generic list length as a direct TM-backed projection -/

def listLengthDelimiterKeep (X : EncodedType) :
    (EncodedType.list X).Symbol → Option Bool
  | none => some true
  | some _ => none

theorem listLengthDelimiter_filterMap_eq (X : EncodedType) (xs : List X.Carrier) :
    ((EncodedType.list X).encode xs).filterMap (listLengthDelimiterKeep X) =
      unaryPayloadEncodedType.encode xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      dsimp [EncodedType.list]
      have hPayloadTail :
          ∀ tail : List (Option X.Symbol),
            List.filterMap
                (listLengthDelimiterKeep X)
                ((List.map some (X.encode x) ++ [none]) ++ tail) =
              [true] ++ List.filterMap (listLengthDelimiterKeep X) tail := by
        induction X.encode x with
        | nil =>
            intro tail
            change
              List.filterMap (listLengthDelimiterKeep X) (none :: tail) =
                true :: List.filterMap (listLengthDelimiterKeep X) tail
            rfl
        | cons a rest ihRest =>
            intro tail
            change
              List.filterMap
                  (listLengthDelimiterKeep X)
                  (some a :: ((List.map some rest ++ [none]) ++ tail)) =
                [true] ++ List.filterMap (listLengthDelimiterKeep X) tail
            simp only [List.filterMap_cons, listLengthDelimiterKeep]
            exact ihRest tail
      have hTail :
          (List.flatMap (fun y => List.map some (X.encode y) ++ [none])
              xs).filterMap (listLengthDelimiterKeep X) =
            List.replicate xs.length true := by
        simpa [EncodedType.list, unaryPayloadEncodedType] using ih
      calc
        List.filterMap
            (listLengthDelimiterKeep X)
            ((List.map some (X.encode x) ++ [none]) ++
              List.flatMap
                (fun y => List.map some (X.encode y) ++ [none])
                xs)
            = [] ++ [true] ++ List.replicate xs.length true := by
              let tail :=
                List.flatMap
                  (fun y => List.map some (X.encode y) ++ [none])
                  xs
              have hStep := hPayloadTail tail
              calc
                List.filterMap
                    (listLengthDelimiterKeep X)
                    ((List.map some (X.encode x) ++ [none]) ++ tail)
                    =
                  [true] ++ List.filterMap (listLengthDelimiterKeep X) tail := hStep
                _ = [true] ++ List.replicate xs.length true := by
                  exact congrArg (fun ys => [true] ++ ys) hTail
                _ = [] ++ [true] ++ List.replicate xs.length true := rfl
        _ = List.replicate (x :: xs).length true := by
              simpa [unaryPayloadEncodedType, Nat.succ_eq_add_one] using
                (show true :: List.replicate xs.length true =
                  List.replicate (Nat.succ xs.length) true from rfl)

theorem encodedListLength_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  simpa [EncodedType.inputSize] using
    (TM2Programs.listEncode_length_ge_length X xs)

noncomputable def listLengthTMBackedMap (X : EncodedType) :
    TMBackedCostedMap (EncodedType.list X) EncodedType.nat List.length where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.list X) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro xs
        have h := encodedListLength_le_inputSize X xs
        simpa [EncodedType.inputSize, EncodedType.nat] using Nat.succ_le_succ h))
  tm_polytime := by
    have hPayload :
        TMPolyTimeMap (EncodedType.list X) unaryPayloadEncodedType
          (fun xs : List X.Carrier => xs.length) :=
      (TMBackedCostedMap.symbolFilterMap
        (EncodedType.list X) unaryPayloadEncodedType
        (fun xs : List X.Carrier => xs.length)
        (listLengthDelimiterKeep X)
        (by
          intro xs
          simpa using (listLengthDelimiter_filterMap_eq X xs).symm)).tm_polytime
    have hNat := unaryPayloadToNatTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hNat hPayload
    simpa [Function.comp] using hComp

/-! ### Tuple reifiers for source and target structured inputs -/

def setSystemInputToTuple
    (S : setSystemStructuredEncodedType.Carrier) :
    setSystemTupleStructuredEncodedType.Carrier :=
  (S.universeSize, S.sets)

theorem setSystemInputToTuple_encode
    (S : setSystemStructuredEncodedType.Carrier) :
    setSystemTupleStructuredEncodedType.encode (setSystemInputToTuple S) =
      setSystemStructuredEncodedType.encode S := by
  cases S
  rfl

noncomputable def setSystemInputToTupleTMBackedMap :
    TMBackedCostedMap
      setSystemStructuredEncodedType
      setSystemTupleStructuredEncodedType
      setSystemInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    setSystemStructuredEncodedType
    setSystemTupleStructuredEncodedType
    setSystemInputToTuple
    (Equiv.refl setSystemTupleStructuredEncodedType.Symbol)
    (by
      intro S
      change setSystemTupleStructuredEncodedType.encode (setSystemInputToTuple S) =
        (setSystemStructuredEncodedType.encode S).map id
      simp [setSystemInputToTuple_encode])

def setCoveringInputToTuple
    (I : setCoveringStructuredEncodedType.Carrier) :
    setCoveringTupleStructuredEncodedType.Carrier :=
  (I.system, I.k)

theorem setCoveringInputToTuple_encode
    (I : setCoveringStructuredEncodedType.Carrier) :
    setCoveringTupleStructuredEncodedType.encode (setCoveringInputToTuple I) =
      setCoveringStructuredEncodedType.encode I := by
  cases I
  rfl

noncomputable def setCoveringInputToTupleTMBackedMap :
    TMBackedCostedMap
      setCoveringStructuredEncodedType
      setCoveringTupleStructuredEncodedType
      setCoveringInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    setCoveringStructuredEncodedType
    setCoveringTupleStructuredEncodedType
    setCoveringInputToTuple
    (Equiv.refl setCoveringTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change setCoveringTupleStructuredEncodedType.encode (setCoveringInputToTuple I) =
        (setCoveringStructuredEncodedType.encode I).map id
      simp [setCoveringInputToTuple_encode])

def hittingSetTupleToHittingSetInput
    (p : hittingSetTupleStructuredEncodedType.Carrier) : HittingSetInput where
  system := p.1
  k := p.2

theorem hittingSetTupleToHittingSetInput_encode
    (p : hittingSetTupleStructuredEncodedType.Carrier) :
    hittingSetStructuredEncodedType.encode (hittingSetTupleToHittingSetInput p) =
      hittingSetTupleStructuredEncodedType.encode p := by
  rcases p with ⟨system, k⟩
  rfl

noncomputable def hittingSetTupleToHittingSetInputTMBackedMap :
    TMBackedCostedMap
      hittingSetTupleStructuredEncodedType
      hittingSetStructuredEncodedType
      hittingSetTupleToHittingSetInput :=
  TMBackedCostedMap.ofEncodingEquiv
    hittingSetTupleStructuredEncodedType
    hittingSetStructuredEncodedType
    hittingSetTupleToHittingSetInput
    (Equiv.refl hittingSetTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change hittingSetStructuredEncodedType.encode (hittingSetTupleToHittingSetInput p) =
        (hittingSetTupleStructuredEncodedType.encode p).map id
      simp [hittingSetTupleToHittingSetInput_encode])

/-! ### Structured Set Covering to Hitting Set TM-backed assembly -/

theorem setCoveringToHittingSetStructured_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      hittingSetStructuredEncodedType
      map := by
  let X := setCoveringStructuredEncodedType
  have hSourceTuple :
      TMPolyTimeMap X setCoveringTupleStructuredEncodedType
        (fun I : SetCoveringInput => (I.system, I.k)) := by
    simpa [X, setCoveringInputToTuple] using
      setCoveringInputToTupleTMBackedMap.tm_polytime
  have hSourceSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType
        (fun I : SetCoveringInput => I.system) := by
    have hFst := TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hSourceTuple
    simpa [Function.comp, setCoveringTupleStructuredEncodedType, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : SetCoveringInput => I.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hSourceTuple
    simpa [Function.comp, setCoveringTupleStructuredEncodedType, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : SetCoveringInput => (I.system.universeSize, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp setSystemInputToTupleTMBackedMap.tm_polytime
      hSourceSystem
    simpa [Function.comp, setSystemInputToTuple, X] using hComp
  have hUniverseSize :
      TMPolyTimeMap X EncodedType.nat
        (fun I : SetCoveringInput => I.system.universeSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun I : SetCoveringInput => I.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hDualUniverse :
      TMPolyTimeMap X EncodedType.nat
        (fun I : SetCoveringInput => I.system.sets.length) := by
    have hComp := TMPolyTimeMap.comp
      (listLengthTMBackedMap setStructuredEncodedType).tm_polytime hSets
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hFamilyInput :
      TMPolyTimeMap X dualFamilyInstructionInputEncodedType
        (fun I : SetCoveringInput => (I.system.sets, I.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hSets hUniverseSize
  have hDualFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun I : SetCoveringInput =>
          dualFamilyFromSetFamily (I.system.sets, I.system.universeSize)) := by
    have hComp := TMPolyTimeMap.comp dualFamilyFromSetFamily_tm_polytime hFamilyInput
    simpa [Function.comp, X] using hComp
  have hTargetSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : SetCoveringInput =>
          (I.system.sets.length,
            dualFamilyFromSetFamily (I.system.sets, I.system.universeSize))) :=
    TMPolyTimeMap.prod_mk hDualUniverse hDualFamily
  have hTargetSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType
        (fun I : SetCoveringInput =>
          { universeSize := I.system.sets.length
            sets := dualFamilyFromSetFamily (I.system.sets, I.system.universeSize) }) := by
    have hComp := TMPolyTimeMap.comp SetCovering.setSystemTupleToSetSystemInputTMBackedMap.tm_polytime
      hTargetSystemTuple
    simpa [Function.comp, SetCovering.setSystemTupleToSetSystemInput, X] using hComp
  have hTargetTuple :
      TMPolyTimeMap X hittingSetTupleStructuredEncodedType
        (fun I : SetCoveringInput =>
          ({ universeSize := I.system.sets.length
             sets := dualFamilyFromSetFamily (I.system.sets, I.system.universeSize) }, I.k)) :=
    TMPolyTimeMap.prod_mk hTargetSystem hBudget
  have hOut :
      TMPolyTimeMap X hittingSetStructuredEncodedType
        (fun I : SetCoveringInput =>
          { system :=
              { universeSize := I.system.sets.length
                sets := dualFamilyFromSetFamily (I.system.sets, I.system.universeSize) }
            k := I.k }) := by
    have hComp := TMPolyTimeMap.comp hittingSetTupleToHittingSetInputTMBackedMap.tm_polytime
      hTargetTuple
    simpa [Function.comp, hittingSetTupleToHittingSetInput, X] using hComp
  convert hOut using 1
  funext I
  simp [map, dualSystem, dualFamilyFromSetFamily_eq_dualSystem_sets]

noncomputable def setCoveringToHittingSetStructuredTMBackedMap :
    TMBackedCostedMap
      setCoveringStructuredEncodedType
      hittingSetStructuredEncodedType
      map where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      setCoveringToHittingSetStructured_polynomialSizeBound
  tm_polytime := setCoveringToHittingSetStructured_tm_polytime

noncomputable def setCoveringToHittingSetStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      setCoveringStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    setCoveringToHittingSetStructuredTMBackedMap
    (by
      intro I
      simpa [setCoveringStructuredDecisionProblem, hittingSetStructuredDecisionProblem,
        setCoveringDecisionProblem] using map_correct I)

noncomputable def setCoveringToHittingSetStructuredTMKarpReduction :
    TMKarpReduction
      setCoveringStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  setCoveringToHittingSetStructuredTMBackedKarpReduction.toTMKarpReduction

noncomputable def setCoveringToHittingSetStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      setCoveringStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  setCoveringToHittingSetStructuredTMBackedKarpReduction.toCostedKarpReduction

end HittingSet
end Karp21
end ComplexityReduction
