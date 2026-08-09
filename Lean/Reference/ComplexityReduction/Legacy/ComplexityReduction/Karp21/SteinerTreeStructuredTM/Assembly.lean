/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Terminals

/-!
Direct TM-backed structured assembly for the compact
Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Executable compact edge and terminal surfaces -/

def compactEdgesExecutable (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  compactRootSelfEdge ::
    compactFamilyEdgesExecutable
      (I.system.universeSize, I.system.sets.length, I.system.sets)

theorem compactEdgesExecutable_eq_compactEdges (I : ExactCoverInput) :
    compactEdgesExecutable I = compactEdges I := by
  simp [compactEdgesExecutable, compactEdges,
    compactFamilyEdgesExecutable_eq_compactEdges_tail]

theorem compactEdgesExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      weightedEdgeListStructuredEncodedType
      compactEdgesExecutable := by
  let X := exactCoverStructuredEncodedType
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun I : X.Carrier => I.system.sets) := by
    simpa [X] using exactCoverSets_tm_polytime
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun I : X.Carrier => (I.system.sets.length, I.system.sets)) :=
    TMPolyTimeMap.prod_mk hSetCount hSets
  have hContext :
      TMPolyTimeMap X compactFamilyEdgeContextEncodedType
        (fun I : X.Carrier =>
          (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    simpa [compactFamilyEdgeContextEncodedType] using TMPolyTimeMap.prod_mk hUniverse hTail
  have hFamily :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun I : X.Carrier =>
          compactFamilyEdgesExecutable
            (I.system.universeSize, I.system.sets.length, I.system.sets)) := by
    have hComp := TMPolyTimeMap.comp compactFamilyEdgesExecutable_tm_polytime hContext
    simpa [Function.comp, X] using hComp
  have hRoot :
      TMPolyTimeMap X weightedEdgeStructuredEncodedType
        (fun _ : X.Carrier => compactRootSelfEdge) :=
    TMPolyTimeMap.const X weightedEdgeStructuredEncodedType compactRootSelfEdge
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod weightedEdgeStructuredEncodedType weightedEdgeListStructuredEncodedType)
        (fun I : X.Carrier =>
          (compactRootSelfEdge,
            compactFamilyEdgesExecutable
              (I.system.universeSize, I.system.sets.length, I.system.sets))) :=
    TMPolyTimeMap.prod_mk hRoot hFamily
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons weightedEdgeStructuredEncodedType) hConsInput
  simpa [Function.comp, compactEdgesExecutable, weightedEdgeListStructuredEncodedType, X]
    using hCons

def compactTerminalsExecutableFromInput (I : ExactCoverInput) : List Nat :=
  compactTerminalsExecutable (I.system.sets.length, I.system.universeSize)

theorem compactTerminalsExecutableFromInput_eq_compactTerminals (I : ExactCoverInput) :
    compactTerminalsExecutableFromInput I = compactTerminals I := by
  simp [compactTerminalsExecutableFromInput, compactTerminalsExecutable_eq_compactTerminals]

theorem compactTerminalsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      (EncodedType.list EncodedType.nat)
      compactTerminalsExecutableFromInput := by
  let X := exactCoverStructuredEncodedType
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hInput :
      TMPolyTimeMap X compactTerminalListInputEncodedType
        (fun I : X.Carrier => (I.system.sets.length, I.system.universeSize)) := by
    simpa [compactTerminalListInputEncodedType] using TMPolyTimeMap.prod_mk hSetCount hUniverse
  have hComp := TMPolyTimeMap.comp compactTerminalsExecutable_tm_polytime hInput
  simpa [Function.comp, compactTerminalsExecutableFromInput, X] using hComp

/-! ### Weighted graph and Steiner instance assembly -/

def compactVertexCountExecutable (I : ExactCoverInput) : Nat :=
  I.system.sets.length + I.system.universeSize + 1

theorem compactVertexCountExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      compactVertexCountExecutable := by
  let X := exactCoverStructuredEncodedType
  have hSetCount :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.sets.length) := by
    simpa [X] using exactCoverSetsLength_tm_polytime
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun I : X.Carrier => (I.system.sets.length, I.system.universeSize)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk hSetCount hUniverse
  have hAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => I.system.sets.length + I.system.universeSize) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
    simpa [Function.comp, natAddInputEncodedType, X] using hComp
  have hSucc := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAdd
  simpa [Function.comp, compactVertexCountExecutable, Nat.succ_eq_add_one, X] using hSucc

def compactGraphExecutable (I : ExactCoverInput) : WeightedGraphInput where
  vertices := compactVertexCountExecutable I
  edges := compactEdgesExecutable I
  directed := true

theorem compactGraphExecutable_eq_compactMapCore_graph (I : ExactCoverInput) :
    compactGraphExecutable I = (compactMapCore I).graph := by
  simp [compactGraphExecutable, compactVertexCountExecutable,
    compactEdgesExecutable_eq_compactEdges, compactMapCore]

theorem compactGraphExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      weightedGraphStructuredEncodedType
      compactGraphExecutable := by
  let X := exactCoverStructuredEncodedType
  have hVertices :
      TMPolyTimeMap X EncodedType.nat compactVertexCountExecutable := by
    simpa [X] using compactVertexCountExecutable_tm_polytime
  have hEdges :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType compactEdgesExecutable := by
    simpa [X] using compactEdgesExecutable_tm_polytime
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPayload :
      TMPolyTimeMap X weightedGraphPayloadStructuredEncodedType
        (fun I : X.Carrier => (compactEdgesExecutable I, true)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap X weightedGraphTupleStructuredEncodedType
        (fun I : X.Carrier => (compactVertexCountExecutable I, (compactEdgesExecutable I, true))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph :=
    TMPolyTimeMap.comp weightedGraphTupleToWeightedGraphInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, weightedGraphTupleToWeightedGraphInput, compactGraphExecutable, X]
    using hGraph

def compactMapCoreExecutable (I : ExactCoverInput) : SteinerTreeInput where
  graph := compactGraphExecutable I
  terminals := compactTerminalsExecutableFromInput I
  weightBound := I.system.universeSize

theorem compactMapCoreExecutable_eq_compactMapCore (I : ExactCoverInput) :
    compactMapCoreExecutable I = compactMapCore I := by
  simp [compactMapCoreExecutable, compactMapCore,
    compactGraphExecutable_eq_compactMapCore_graph,
    compactTerminalsExecutableFromInput_eq_compactTerminals]

theorem compactMapCoreExecutable_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      steinerTreeStructuredEncodedType
      compactMapCoreExecutable := by
  let X := exactCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X weightedGraphStructuredEncodedType compactGraphExecutable := by
    simpa [X] using compactGraphExecutable_tm_polytime
  have hTerminals :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) compactTerminalsExecutableFromInput := by
    simpa [X] using compactTerminalsExecutableFromInput_tm_polytime
  have hWeight :
      TMPolyTimeMap X EncodedType.nat (fun I : X.Carrier => I.system.universeSize) := by
    simpa [X] using exactCoverUniverseSize_tm_polytime
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)
        (fun I : X.Carrier =>
          (compactTerminalsExecutableFromInput I, I.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hTerminals hWeight
  have hTuple :
      TMPolyTimeMap X steinerTreeTupleStructuredEncodedType
        (fun I : X.Carrier =>
          (compactGraphExecutable I,
            (compactTerminalsExecutableFromInput I, I.system.universeSize))) :=
    TMPolyTimeMap.prod_mk hGraph hPayload
  have hOut :=
    TMPolyTimeMap.comp steinerTreeTupleToSteinerTreeInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, steinerTreeTupleToSteinerTreeInput, compactMapCoreExecutable, X]
    using hOut

/-! ### Guarded public map and reductions -/

def exactCoverToSteinerTreeCompactStructuredTMMap (I : ExactCoverInput) : SteinerTreeInput :=
  match exactCoverWellFormedBool I with
  | true => compactMapCoreExecutable I
  | false => noInput

theorem exactCoverToSteinerTreeCompactStructuredTMMap_eq_compactMap
    (I : ExactCoverInput) :
    exactCoverToSteinerTreeCompactStructuredTMMap I = compactMap I := by
  by_cases hWellFormed : SetSystemWellFormed I.system
  · have hBool : exactCoverWellFormedBool I = true :=
      (exactCoverWellFormedBool_eq_true_iff I).2 hWellFormed
    simp [exactCoverToSteinerTreeCompactStructuredTMMap, hBool, compactMap,
      hWellFormed, compactMapCoreExecutable_eq_compactMapCore]
  · have hBool : exactCoverWellFormedBool I = false := by
      cases h : exactCoverWellFormedBool I with
      | false => rfl
      | true =>
          have hWF := (exactCoverWellFormedBool_eq_true_iff I).1 h
          exact False.elim (hWellFormed hWF)
    simp [exactCoverToSteinerTreeCompactStructuredTMMap, hBool, compactMap, hWellFormed]

theorem exactCoverToSteinerTreeCompactStructured_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      steinerTreeStructuredEncodedType
      exactCoverToSteinerTreeCompactStructuredTMMap := by
  let X := exactCoverStructuredEncodedType
  have hGuard :
      TMPolyTimeMap X EncodedType.bool exactCoverWellFormedBool := by
    simpa [X] using exactCoverWellFormedBool_tm_polytime
  have hCore :
      TMPolyTimeMap X steinerTreeStructuredEncodedType compactMapCoreExecutable := by
    simpa [X] using compactMapCoreExecutable_tm_polytime
  have hNo :
      TMPolyTimeMap X steinerTreeStructuredEncodedType (fun _ : X.Carrier => noInput) :=
    TMPolyTimeMap.const X steinerTreeStructuredEncodedType noInput
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : X.Carrier => (exactCoverWellFormedBool I, I)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hDispatch :=
    graphBoolProduct_dispatch_tm_polytime X steinerTreeStructuredEncodedType
      (fFalse := fun _ : X.Carrier => noInput)
      (fTrue := compactMapCoreExecutable)
      hNo hCore
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  simpa [Function.comp, exactCoverToSteinerTreeCompactStructuredTMMap] using hComp

theorem exactCoverToSteinerTreeCompactStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : ExactCoverInput => exactCoverStructuredEncodedType.inputSize I)
      (fun J : SteinerTreeInput => steinerTreeStructuredEncodedType.inputSize J)
      exactCoverToSteinerTreeCompactStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro I
  rw [exactCoverToSteinerTreeCompactStructuredTMMap_eq_compactMap]
  exact compactMap_structured_inputSize_le_source_poly I

noncomputable def exactCoverToSteinerTreeCompactStructuredTMBackedMap :
    TMBackedCostedMap
      exactCoverStructuredEncodedType
      steinerTreeStructuredEncodedType
      exactCoverToSteinerTreeCompactStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      exactCoverToSteinerTreeCompactStructuredTMMap_polynomialSizeBound
  tm_polytime := exactCoverToSteinerTreeCompactStructured_tm_polytime

theorem exactCoverToSteinerTreeCompactStructuredTMMap_correct (I : ExactCoverInput) :
    exactCoverStructuredDecisionProblem.isYes I ↔
      steinerTreeStructuredDecisionProblem.isYes
        (exactCoverToSteinerTreeCompactStructuredTMMap I) := by
  rw [exactCoverToSteinerTreeCompactStructuredTMMap_eq_compactMap]
  simpa [exactCoverStructuredDecisionProblem, steinerTreeStructuredDecisionProblem]
    using compactMap_correct I

noncomputable def exactCoverToSteinerTreeCompactStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      exactCoverStructuredDecisionProblem
      steinerTreeStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    exactCoverToSteinerTreeCompactStructuredTMBackedMap
    (by
      intro I
      exact exactCoverToSteinerTreeCompactStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Exact-Cover-to-Steiner-Tree reduction,
projected from the direct TM-backed compact graph assembly.
-/
noncomputable def exactCoverToSteinerTreeCompactStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      exactCoverStructuredDecisionProblem
      steinerTreeStructuredDecisionProblem :=
  exactCoverToSteinerTreeCompactStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Exact-Cover-to-Steiner-Tree reduction. -/
noncomputable def exactCoverToSteinerTreeCompactStructuredTMKarpReduction :
    TMKarpReduction
      exactCoverStructuredDecisionProblem
      steinerTreeStructuredDecisionProblem :=
  exactCoverToSteinerTreeCompactStructuredTMBackedKarpReduction.toTMKarpReduction

end SteinerTree
end Karp21
end ComplexityReduction
