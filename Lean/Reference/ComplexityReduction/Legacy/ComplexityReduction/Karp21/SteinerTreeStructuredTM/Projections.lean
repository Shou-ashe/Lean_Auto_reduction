/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTree
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.Base
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM

/-!
Reusable structured projections and tuple reifiers for the compact
Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Source projections -/

theorem exactCoverSystem_encode (I : ExactCoverInput) :
    setSystemStructuredEncodedType.encode I.system =
      exactCoverStructuredEncodedType.encode I := by
  rfl

noncomputable def exactCoverSystemTMBackedMap :
    TMBackedCostedMap
      exactCoverStructuredEncodedType
      setSystemStructuredEncodedType
      (fun I : ExactCoverInput => I.system) :=
  TMBackedCostedMap.ofEncodingEquiv
    exactCoverStructuredEncodedType
    setSystemStructuredEncodedType
    (fun I : ExactCoverInput => I.system)
    (Equiv.refl exactCoverStructuredEncodedType.Symbol)
    (by
      intro I
      change setSystemStructuredEncodedType.encode I.system =
        (exactCoverStructuredEncodedType.encode I).map id
      simp [exactCoverSystem_encode])

/-! ### Weighted-graph and Steiner Tree reifiers -/

def weightedGraphTupleToWeightedGraphInput
    (p : weightedGraphTupleStructuredEncodedType.Carrier) : WeightedGraphInput where
  vertices := p.1
  edges := p.2.1
  directed := p.2.2

theorem weightedGraphTupleToWeightedGraphInput_encode
    (p : weightedGraphTupleStructuredEncodedType.Carrier) :
    weightedGraphStructuredEncodedType.encode (weightedGraphTupleToWeightedGraphInput p) =
      weightedGraphTupleStructuredEncodedType.encode p := by
  rcases p with ⟨vertices, edges, directed⟩
  rfl

noncomputable def weightedGraphTupleToWeightedGraphInputTMBackedMap :
    TMBackedCostedMap
      weightedGraphTupleStructuredEncodedType
      weightedGraphStructuredEncodedType
      weightedGraphTupleToWeightedGraphInput :=
  TMBackedCostedMap.ofEncodingEquiv
    weightedGraphTupleStructuredEncodedType
    weightedGraphStructuredEncodedType
    weightedGraphTupleToWeightedGraphInput
    (Equiv.refl weightedGraphTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change weightedGraphStructuredEncodedType.encode
          (weightedGraphTupleToWeightedGraphInput p) =
        (weightedGraphTupleStructuredEncodedType.encode p).map id
      simp [weightedGraphTupleToWeightedGraphInput_encode])

def steinerTreeTupleToSteinerTreeInput
    (p : steinerTreeTupleStructuredEncodedType.Carrier) : SteinerTreeInput where
  graph := p.1
  terminals := p.2.1
  weightBound := p.2.2

theorem steinerTreeTupleToSteinerTreeInput_encode
    (p : steinerTreeTupleStructuredEncodedType.Carrier) :
    steinerTreeStructuredEncodedType.encode (steinerTreeTupleToSteinerTreeInput p) =
      steinerTreeTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, terminals, weightBound⟩
  rfl

noncomputable def steinerTreeTupleToSteinerTreeInputTMBackedMap :
    TMBackedCostedMap
      steinerTreeTupleStructuredEncodedType
      steinerTreeStructuredEncodedType
      steinerTreeTupleToSteinerTreeInput :=
  TMBackedCostedMap.ofEncodingEquiv
    steinerTreeTupleStructuredEncodedType
    steinerTreeStructuredEncodedType
    steinerTreeTupleToSteinerTreeInput
    (Equiv.refl steinerTreeTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change steinerTreeStructuredEncodedType.encode
          (steinerTreeTupleToSteinerTreeInput p) =
        (steinerTreeTupleStructuredEncodedType.encode p).map id
      simp [steinerTreeTupleToSteinerTreeInput_encode])

/-! ### Shared source field projections -/

theorem exactCoverSystemTuple_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      setSystemTupleStructuredEncodedType
      (fun I : ExactCoverInput => (I.system.universeSize, I.system.sets)) := by
  have hSystem := exactCoverSystemTMBackedMap.tm_polytime
  have hTuple := HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hTuple hSystem
  simpa [Function.comp, HittingSet.setSystemInputToTuple] using hComp

theorem exactCoverUniverseSize_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      (fun I : ExactCoverInput => I.system.universeSize) := by
  have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hFst exactCoverSystemTuple_tm_polytime
  simpa [Function.comp, setSystemTupleStructuredEncodedType] using hComp

theorem exactCoverSets_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      setFamilyStructuredEncodedType
      (fun I : ExactCoverInput => I.system.sets) := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd exactCoverSystemTuple_tm_polytime
  simpa [Function.comp, setSystemTupleStructuredEncodedType] using hComp

theorem exactCoverSetsLength_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.nat
      (fun I : ExactCoverInput => I.system.sets.length) := by
  have hComp := TMPolyTimeMap.comp
    (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime
    exactCoverSets_tm_polytime
  simpa [Function.comp, setFamilyStructuredEncodedType] using hComp

end SteinerTree
end Karp21
end ComplexityReduction
