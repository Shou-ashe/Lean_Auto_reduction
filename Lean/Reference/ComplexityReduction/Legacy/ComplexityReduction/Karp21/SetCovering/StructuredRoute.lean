/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.FamilyRunner

/-!
TM-backed structured assembly for the Vertex Cover to Set Covering route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetCovering

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Edge-list length as a direct TM-backed projection -/

def edgeListLengthDelimiterKeep :
    edgeListStructuredEncodedType.Symbol → Option Bool
  | none => some true
  | some _ => none

theorem edgeListLengthDelimiter_filterMap_eq (edges : List (Nat × Nat)) :
    (edgeListStructuredEncodedType.encode edges).filterMap edgeListLengthDelimiterKeep =
      unaryPayloadEncodedType.encode edges.length := by
  induction edges with
  | nil =>
      rfl
  | cons e edges ih =>
      dsimp [edgeListStructuredEncodedType, EncodedType.list]
      have hPayloadTail :
          ∀ tail : List (Option edgeStructuredEncodedType.Symbol),
            List.filterMap
                (edgeListLengthDelimiterKeep :
                  Option edgeStructuredEncodedType.Symbol → Option Bool)
                ((List.map some (edgeStructuredEncodedType.encode e) ++ [none]) ++ tail) =
              [true] ++ List.filterMap
                (edgeListLengthDelimiterKeep :
                  Option edgeStructuredEncodedType.Symbol → Option Bool)
                tail := by
        induction edgeStructuredEncodedType.encode e with
        | nil =>
            intro tail
            change
              List.filterMap
                  (edgeListLengthDelimiterKeep :
                    Option edgeStructuredEncodedType.Symbol → Option Bool)
                  (none :: tail) =
                true :: List.filterMap
                  (edgeListLengthDelimiterKeep :
                    Option edgeStructuredEncodedType.Symbol → Option Bool)
                  tail
            rfl
        | cons a rest ihRest =>
            intro tail
            change
                  List.filterMap
                      (edgeListLengthDelimiterKeep :
                    Option edgeStructuredEncodedType.Symbol → Option Bool)
                  (some a :: ((List.map some rest ++ [none]) ++ tail)) =
                [true] ++ List.filterMap
                  (edgeListLengthDelimiterKeep :
                    Option edgeStructuredEncodedType.Symbol → Option Bool)
                  tail
            simp only [List.filterMap_cons, edgeListLengthDelimiterKeep]
            exact ihRest tail
      have hTail :
          (List.flatMap (fun x => List.map some (edgeStructuredEncodedType.encode x) ++ [none])
              edges).filterMap
              (edgeListLengthDelimiterKeep :
                Option edgeStructuredEncodedType.Symbol → Option Bool) =
            List.replicate edges.length true := by
        simpa [edgeListStructuredEncodedType, EncodedType.list, unaryPayloadEncodedType] using ih
      calc
        List.filterMap
            (edgeListLengthDelimiterKeep :
              Option edgeStructuredEncodedType.Symbol → Option Bool)
            ((List.map some (edgeStructuredEncodedType.encode e) ++ [none]) ++
              List.flatMap
                (fun x => List.map some (edgeStructuredEncodedType.encode x) ++ [none])
                edges)
            = [] ++ [true] ++ List.replicate edges.length true := by
              let tail :=
                List.flatMap
                  (fun x => List.map some (edgeStructuredEncodedType.encode x) ++ [none])
                  edges
              have hStep := hPayloadTail tail
              calc
                List.filterMap
                    (edgeListLengthDelimiterKeep :
                      Option edgeStructuredEncodedType.Symbol → Option Bool)
                    ((List.map some (edgeStructuredEncodedType.encode e) ++ [none]) ++ tail)
                    =
                  [true] ++
                    List.filterMap
                      (edgeListLengthDelimiterKeep :
                        Option edgeStructuredEncodedType.Symbol → Option Bool)
                      tail := hStep
                _ = [true] ++ List.replicate edges.length true := by
                  exact congrArg
                    (fun xs => [true] ++ xs)
                    hTail
                _ = [] ++ [true] ++ List.replicate edges.length true := rfl
        _ = List.replicate (e :: edges).length true := by
              simpa [unaryPayloadEncodedType, Nat.succ_eq_add_one] using
                (show true :: List.replicate edges.length true =
                  List.replicate (Nat.succ edges.length) true from rfl)

theorem edgeListLength_le_inputSize (edges : List (Nat × Nat)) :
    edges.length ≤ edgeListStructuredEncodedType.inputSize edges := by
  simpa [edgeListStructuredEncodedType, EncodedType.inputSize] using
    (TM2Programs.listEncode_length_ge_length edgeStructuredEncodedType edges)

noncomputable def edgeListLengthTMBackedMap :
    TMBackedCostedMap edgeListStructuredEncodedType EncodedType.nat List.length where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := edgeListStructuredEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro edges
        have h := edgeListLength_le_inputSize edges
        simpa [EncodedType.inputSize, EncodedType.nat] using Nat.succ_le_succ h))
  tm_polytime := by
    have hPayload :
        TMPolyTimeMap edgeListStructuredEncodedType unaryPayloadEncodedType
          (fun edges : List (Nat × Nat) => edges.length) :=
      (TMBackedCostedMap.symbolFilterMap
        edgeListStructuredEncodedType unaryPayloadEncodedType
        (fun edges : List (Nat × Nat) => edges.length)
        edgeListLengthDelimiterKeep
        (by
          intro edges
          simpa using (edgeListLengthDelimiter_filterMap_eq edges).symm)).tm_polytime
    have hNat := unaryPayloadToNatTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hNat hPayload
    simpa [Function.comp] using hComp

/-! ### Structured Vertex Cover to Set Covering TM-backed assembly -/

theorem vertexCoverToSetCoveringStructured_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      setCoveringStructuredEncodedType
      map := by
  let X := vertexCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : VertexCoverInput => I.graph) := by
    simpa [X] using vertexCoverGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : VertexCoverInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.graph.edges.length) := by
    have hComp := TMPolyTimeMap.comp edgeListLengthTMBackedMap.tm_polytime hEdges
    simpa [Function.comp, X] using hComp
  have hFamilyInput :
      TMPolyTimeMap X incidenceFamilyInstructionInputEncodedType
        (fun I : VertexCoverInput => (I.graph.edges, I.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hEdges hVertices
  have hFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun I : VertexCoverInput =>
          incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices)) := by
    have hComp := TMPolyTimeMap.comp incidenceFamilyFromEdges_tm_polytime hFamilyInput
    simpa [Function.comp, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : VertexCoverInput =>
          (I.graph.edges.length,
            incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices))) :=
    TMPolyTimeMap.prod_mk hUniverse hFamily
  have hSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType
        (fun I : VertexCoverInput =>
          { universeSize := I.graph.edges.length
            sets := incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices) }) := by
    have hComp := TMPolyTimeMap.comp setSystemTupleToSetSystemInputTMBackedMap.tm_polytime
      hSystemTuple
    simpa [Function.comp, setSystemTupleToSetSystemInput, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.k) := by
    simpa [X] using vertexCoverBudgetTMBackedMap.tm_polytime
  have hTargetTuple :
      TMPolyTimeMap X setCoveringTupleStructuredEncodedType
        (fun I : VertexCoverInput =>
          ({ universeSize := I.graph.edges.length
             sets := incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices) }, I.k)) :=
    TMPolyTimeMap.prod_mk hSystem hBudget
  have hOut :
      TMPolyTimeMap X setCoveringStructuredEncodedType
        (fun I : VertexCoverInput =>
          { system :=
              { universeSize := I.graph.edges.length
                sets := incidenceFamilyFromEdges (I.graph.edges, I.graph.vertices) }
            k := I.k }) := by
    have hComp := TMPolyTimeMap.comp setCoveringTupleToSetCoveringInputTMBackedMap.tm_polytime
      hTargetTuple
    simpa [Function.comp, setCoveringTupleToSetCoveringInput, X] using hComp
  convert hOut using 1
  funext I
  simp [map, edgeSetSystem, incidenceFamilyFromEdges_eq_edgeSetSystem_sets]

noncomputable def vertexCoverToSetCoveringStructuredTMBackedMap :
    TMBackedCostedMap
      vertexCoverStructuredEncodedType
      setCoveringStructuredEncodedType
      map where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      vertexCoverToSetCoveringStructured_polynomialSizeBound
  tm_polytime := vertexCoverToSetCoveringStructured_tm_polytime

noncomputable def vertexCoverToSetCoveringStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      vertexCoverStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    vertexCoverToSetCoveringStructuredTMBackedMap
    (by
      intro I
      simpa [vertexCoverStructuredDecisionProblem, setCoveringStructuredDecisionProblem,
        vertexCoverDecisionProblem] using map_correct I)

noncomputable def vertexCoverToSetCoveringStructuredTMKarpReduction :
    TMKarpReduction
      vertexCoverStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  vertexCoverToSetCoveringStructuredTMBackedKarpReduction.toTMKarpReduction

noncomputable def vertexCoverToSetCoveringStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  vertexCoverToSetCoveringStructuredTMBackedKarpReduction.toCostedKarpReduction

end SetCovering
end Karp21
end ComplexityReduction
