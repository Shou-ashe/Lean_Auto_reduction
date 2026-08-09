/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.FinalAssemblyTM

/-!
Guarded executable output assembly for the DHC selector/path gadget.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Direct graph and DHC-input reifiers -/

def dhcExecutableGraphFromInput (I : VertexCoverInput) : GraphInput where
  vertices := dhcVertexCountFromInput I
  edges := dhcEdgeListExecutableFromInput I
  directed := true

theorem dhcVertexCountFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      EncodedType.nat
      dhcVertexCountFromInput := by
  have hComp := TMPolyTimeMap.comp
    dhcVertexCountFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcVertexCountFromInput,
    dhcIndexedSourceIncidenceBudgetFromInput] using hComp

theorem dhcExecutableGraphFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      graphStructuredEncodedType
      dhcExecutableGraphFromInput := by
  let X := vertexCoverStructuredEncodedType
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : VertexCoverInput => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : VertexCoverInput => (dhcEdgeListExecutableFromInput I, true)) :=
    TMPolyTimeMap.prod_mk dhcEdgeListExecutableFromInput_tm_polytime hDirected
  have hTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : VertexCoverInput =>
          (dhcVertexCountFromInput I, (dhcEdgeListExecutableFromInput I, true))) :=
    TMPolyTimeMap.prod_mk dhcVertexCountFromInput_tm_polytime hPayload
  have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, dhcExecutableGraphFromInput, X] using hComp

theorem dhcExecutableGraphFromInput_eq_textbookGraph
    (I : VertexCoverInput) :
    dhcExecutableGraphFromInput I = (textbookMap I).graph := by
  simp [dhcExecutableGraphFromInput, textbookMap,
    dhcVertexCountFromInput_eq_textbookVertexCount,
    dhcEdgeListExecutableFromInput_eq_textbookEdgeList]

def dhcExecutableInputFromVertexCover
    (I : VertexCoverInput) : DirectedHamiltonianCircuitInput :=
  directedHamiltonianCircuitGraphToInput (dhcExecutableGraphFromInput I)

theorem dhcExecutableInputFromVertexCover_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      directedHamiltonianCircuitStructuredEncodedType
      dhcExecutableInputFromVertexCover := by
  have hComp := TMPolyTimeMap.comp
    directedHamiltonianCircuitGraphToInputTMBackedMap.tm_polytime
    dhcExecutableGraphFromInput_tm_polytime
  simpa [Function.comp, directedHamiltonianCircuitGraphToInput,
    dhcExecutableInputFromVertexCover] using hComp

theorem dhcExecutableInputFromVertexCover_eq_textbookMap
    (I : VertexCoverInput) :
    dhcExecutableInputFromVertexCover I = textbookMap I := by
  simp [dhcExecutableInputFromVertexCover, directedHamiltonianCircuitGraphToInput,
    dhcExecutableGraphFromInput_eq_textbookGraph]

/-! ### Guarded public map -/

def vertexCoverToDirectedHamiltonianCircuitStructuredTMMap
    (I : VertexCoverInput) : DirectedHamiltonianCircuitInput :=
  if FeedbackNodeSet.hasUncoverableEdgeTM I then
    noInput
  else
    dhcExecutableInputFromVertexCover I

abbrev dhcGuardedExecutableMap :
    VertexCoverInput → DirectedHamiltonianCircuitInput :=
  vertexCoverToDirectedHamiltonianCircuitStructuredTMMap

theorem vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap
    (I : VertexCoverInput) :
    vertexCoverToDirectedHamiltonianCircuitStructuredTMMap I = guardedTextbookMap I := by
  classical
  by_cases hBadBool : FeedbackNodeSet.hasUncoverableEdgeTM I = true
  · have hBad : FeedbackNodeSet.HasUncoverableEdge I.graph :=
      (FeedbackNodeSet.hasUncoverableEdgeTM_eq_true_iff I).1 hBadBool
    simp [vertexCoverToDirectedHamiltonianCircuitStructuredTMMap, hBadBool,
      guardedTextbookMap, hBad]
  · have hBadFalse : FeedbackNodeSet.hasUncoverableEdgeTM I = false := by
      cases h : FeedbackNodeSet.hasUncoverableEdgeTM I
      · rfl
      · exact False.elim (hBadBool h)
    have hNoBad : ¬ FeedbackNodeSet.HasUncoverableEdge I.graph := by
      intro hBad
      exact hBadBool ((FeedbackNodeSet.hasUncoverableEdgeTM_eq_true_iff I).2 hBad)
    simp [vertexCoverToDirectedHamiltonianCircuitStructuredTMMap, hBadFalse,
      guardedTextbookMap, hNoBad, dhcExecutableInputFromVertexCover_eq_textbookMap]

theorem dhcGuardedExecutableMap_eq_guardedTextbookMap
    (I : VertexCoverInput) :
    dhcGuardedExecutableMap I = guardedTextbookMap I :=
  vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap I

theorem vertexCoverToDirectedHamiltonianCircuitStructured_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      directedHamiltonianCircuitStructuredEncodedType
      vertexCoverToDirectedHamiltonianCircuitStructuredTMMap := by
  let X := vertexCoverStructuredEncodedType
  have hNo :
      TMPolyTimeMap X directedHamiltonianCircuitStructuredEncodedType
        (fun _ : VertexCoverInput => noInput) :=
    TMPolyTimeMap.const X directedHamiltonianCircuitStructuredEncodedType noInput
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : VertexCoverInput => (FeedbackNodeSet.hasUncoverableEdgeTM I, I)) :=
    TMPolyTimeMap.prod_mk FeedbackNodeSet.hasUncoverableEdgeTM_tm_polytime
      (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        directedHamiltonianCircuitStructuredEncodedType
        (fun p : Bool × VertexCoverInput =>
          match p.1 with
          | true => noInput
          | false => dhcExecutableInputFromVertexCover p.2) :=
    graphBoolProduct_dispatch_tm_polytime X directedHamiltonianCircuitStructuredEncodedType
      (fFalse := fun I : VertexCoverInput => dhcExecutableInputFromVertexCover I)
      (fTrue := fun _ : VertexCoverInput => noInput)
      dhcExecutableInputFromVertexCover_tm_polytime hNo
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext I
  cases h : FeedbackNodeSet.hasUncoverableEdgeTM I <;>
    simp [Function.comp, vertexCoverToDirectedHamiltonianCircuitStructuredTMMap, h]

/-! ### Public P16c surface -/

theorem vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_inputSize_le_vertexCover_poly
    (I : VertexCoverInput) :
    directedHamiltonianCircuitStructuredEncodedType.inputSize
        (vertexCoverToDirectedHamiltonianCircuitStructuredTMMap I) ≤
      1000 * (vertexCoverStructuredEncodedType.inputSize I) ^ 8 + 1000 := by
  rw [vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap]
  exact directedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_vertexCover_poly I

theorem vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize I)
      (fun J : DirectedHamiltonianCircuitInput =>
        directedHamiltonianCircuitStructuredEncodedType.inputSize J)
      vertexCoverToDirectedHamiltonianCircuitStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 8 1000 1000 ?_
  intro I
  exact vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_inputSize_le_vertexCover_poly I

noncomputable def vertexCoverToDirectedHamiltonianCircuitStructuredTMBackedMap :
    TMBackedCostedMap
      vertexCoverStructuredEncodedType
      directedHamiltonianCircuitStructuredEncodedType
      vertexCoverToDirectedHamiltonianCircuitStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_polynomialSizeBound
  tm_polytime := vertexCoverToDirectedHamiltonianCircuitStructured_tm_polytime

theorem vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_correct
    (I : VertexCoverInput) :
    vertexCoverStructuredDecisionProblem.isYes I ↔
      directedHamiltonianCircuitStructuredDecisionProblem.isYes
        (vertexCoverToDirectedHamiltonianCircuitStructuredTMMap I) := by
  rw [vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_eq_guardedTextbookMap]
  simpa [vertexCoverStructuredDecisionProblem,
    directedHamiltonianCircuitStructuredDecisionProblem, vertexCoverDecisionProblem]
    using guardedTextbookMap_correct I

noncomputable def vertexCoverToDirectedHamiltonianCircuitStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      vertexCoverStructuredDecisionProblem
      directedHamiltonianCircuitStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    vertexCoverToDirectedHamiltonianCircuitStructuredTMBackedMap
    (by
      intro I
      exact vertexCoverToDirectedHamiltonianCircuitStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Vertex-Cover-to-Directed-Hamiltonian-
Circuit reduction, projected from the direct TM-backed witness.
-/
noncomputable def vertexCoverToDirectedHamiltonianCircuitStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem
      directedHamiltonianCircuitStructuredDecisionProblem :=
  vertexCoverToDirectedHamiltonianCircuitStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def vertexCoverToDirectedHamiltonianCircuitStructuredTMKarpReduction :
    TMKarpReduction
      vertexCoverStructuredDecisionProblem
      directedHamiltonianCircuitStructuredDecisionProblem :=
  vertexCoverToDirectedHamiltonianCircuitStructuredTMBackedKarpReduction.toTMKarpReduction

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
