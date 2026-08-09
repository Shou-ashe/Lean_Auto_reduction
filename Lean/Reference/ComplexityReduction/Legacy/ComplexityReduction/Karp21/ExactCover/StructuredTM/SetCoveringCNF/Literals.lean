import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part2
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatPairTM

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed literal layer for the compact Set-Covering-to-CNF route.

The CNF map in `ExactCover.Part1` uses variables `Nat.pair slot choice`.
This file isolates that arithmetic/literal writer and the source choice-count
projection before the larger slot-clause and coverage-clause runners are built.
-/

def setCoveringChoiceLitFromPair (p : Nat × Nat) : SAT.Literal :=
  SAT.Literal.positive (Nat.pair p.1 p.2)

def setCoveringChoiceNegLitFromPair (p : Nat × Nat) : SAT.Literal :=
  SAT.Literal.negative (Nat.pair p.1 p.2)

theorem setCoveringChoiceLitFromPair_eq
    (I : SetCoveringInput) (slot choice : Nat) :
    setCoveringChoiceLitFromPair (slot, choice) =
      setCoveringChoiceLit I slot choice := by
  rfl

theorem setCoveringChoiceNegLitFromPair_eq
    (I : SetCoveringInput) (slot choice : Nat) :
    setCoveringChoiceNegLitFromPair (slot, choice) =
      setCoveringChoiceNegLit I slot choice := by
  rfl

theorem setCoveringChoiceVar_tm_polytime :
    TMPolyTimeMap
      vertexPairEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
  simpa [vertexPairEncodedType] using natPair_tm_polytime

theorem setCoveringChoiceLitFromPair_tm_polytime :
    TMPolyTimeMap
      vertexPairEncodedType
      literalStructuredEncodedType
      setCoveringChoiceLitFromPair := by
  have hVar := setCoveringChoiceVar_tm_polytime
  have hLit := TMPolyTimeMap.comp posAuxTMBackedMap.tm_polytime hVar
  simpa [Function.comp, setCoveringChoiceLitFromPair, SAT.Literal.positive,
    SAT.Clause.posAux] using hLit

theorem setCoveringChoiceNegLitFromPair_tm_polytime :
    TMPolyTimeMap
      vertexPairEncodedType
      literalStructuredEncodedType
      setCoveringChoiceNegLitFromPair := by
  have hVar := setCoveringChoiceVar_tm_polytime
  have hLit := TMPolyTimeMap.comp negAuxTMBackedMap.tm_polytime hVar
  simpa [Function.comp, setCoveringChoiceNegLitFromPair, SAT.Literal.negative,
    SAT.Clause.negAux] using hLit

theorem setCoveringSystem_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setSystemStructuredEncodedType
      (fun I : SetCoveringInput => I.system) := by
  let X := setCoveringStructuredEncodedType
  have hTuple :
      TMPolyTimeMap X setCoveringTupleStructuredEncodedType
        HittingSet.setCoveringInputToTuple := by
    simpa [X] using HittingSet.setCoveringInputToTupleTMBackedMap.tm_polytime
  have hFst :=
    TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
  have hComp := TMPolyTimeMap.comp hFst hTuple
  simpa [Function.comp, HittingSet.setCoveringInputToTuple,
    setCoveringTupleStructuredEncodedType, X] using hComp

theorem setCoveringSets_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setFamilyStructuredEncodedType
      (fun I : SetCoveringInput => I.system.sets) := by
  let X := setCoveringStructuredEncodedType
  have hSystem := setCoveringSystem_tm_polytime
  have hTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : SetCoveringInput => HittingSet.setSystemInputToTuple I.system) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, X] using hComp
  have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hTuple
  simpa [Function.comp, HittingSet.setSystemInputToTuple,
    setSystemTupleStructuredEncodedType, X] using hComp

theorem setCoveringChoiceCount_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      EncodedType.nat
      setCoveringChoiceCount := by
  have hSets := setCoveringSets_tm_polytime
  have hLength :
      TMPolyTimeMap
        setCoveringStructuredEncodedType
        EncodedType.nat
        (fun I : SetCoveringInput => I.system.sets.length) := by
    have hComp :=
      TMPolyTimeMap.comp
        (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime
        hSets
    simpa [Function.comp, setFamilyStructuredEncodedType] using hComp
  have hSucc := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hLength
  simpa [Function.comp, setCoveringChoiceCount, Nat.succ_eq_add_one] using hSucc

end ExactCover
end Karp21
end ComplexityReduction
