/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering.Base
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.FamilyRunner

/-!
Direct TM-backed structured assembly for the faithful Clique-to-Set-Packing
compact conflict-code route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Tuple reifier for the structured Set Packing target -/

def setPackingTupleToSetPackingInput
    (p : setPackingTupleStructuredEncodedType.Carrier) : SetPackingInput where
  system := p.1
  k := p.2

theorem setPackingTupleToSetPackingInput_encode
    (p : setPackingTupleStructuredEncodedType.Carrier) :
    setPackingStructuredEncodedType.encode (setPackingTupleToSetPackingInput p) =
      setPackingTupleStructuredEncodedType.encode p := by
  rcases p with ⟨system, k⟩
  rfl

noncomputable def setPackingTupleToSetPackingInputTMBackedMap :
    TMBackedCostedMap
      setPackingTupleStructuredEncodedType
      setPackingStructuredEncodedType
      setPackingTupleToSetPackingInput :=
  TMBackedCostedMap.ofEncodingEquiv
    setPackingTupleStructuredEncodedType
    setPackingStructuredEncodedType
    setPackingTupleToSetPackingInput
    (Equiv.refl setPackingTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change setPackingStructuredEncodedType.encode (setPackingTupleToSetPackingInput p) =
        (setPackingTupleStructuredEncodedType.encode p).map id
      simp [setPackingTupleToSetPackingInput_encode])

/-! ### Structured Clique to Set Packing TM-backed assembly -/

theorem cliqueToSetPackingStructured_tm_polytime :
    TMPolyTimeMap
      cliqueStructuredEncodedType
      setPackingStructuredEncodedType
      compactMap := by
  let X := cliqueStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : CliqueInput => I.graph) := by
    simpa [X] using cliqueGraphTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : CliqueInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSourceEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : CliqueInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hCandidates :
      TMPolyTimeMap X vertexPairListEncodedType
        (fun I : CliqueInput => strictNatPairCandidates I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp strictNatPairCandidatesTMBackedMap.tm_polytime hVertices
    simpa [Function.comp, X] using hComp
  have hComplementInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType vertexPairListEncodedType)
        (fun I : CliqueInput =>
          (I.graph.edges, strictNatPairCandidates I.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hSourceEdges hCandidates
  have hComplementEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : CliqueInput => structuredComplementEdges I.graph) := by
    have hComp := TMPolyTimeMap.comp complementEdgesFromCandidates_tm_polytime hComplementInput
    simpa [Function.comp, structuredComplementEdges, X] using hComp
  have hCodeInput :
      TMPolyTimeMap X codeComplementEdgeInstructionInputEncodedType
        (fun I : CliqueInput =>
          (I.graph.vertices, structuredComplementEdges I.graph)) :=
    TMPolyTimeMap.prod_mk hVertices hComplementEdges
  have hCodeAcc :
      TMPolyTimeMap X codeComplementEdgesAccEncodedType
        (fun I : CliqueInput =>
          codeComplementEdgesFromInput
            (I.graph.vertices, structuredComplementEdges I.graph)) := by
    have hComp := TMPolyTimeMap.comp codeComplementEdgesFromInput_tm_polytime hCodeInput
    simpa [Function.comp, codeComplementEdgeInstructionInputEncodedType, X] using hComp
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueInput =>
          (codeComplementEdgesFromInput
            (I.graph.vertices, structuredComplementEdges I.graph)).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCodeAcc
    simpa [Function.comp, codeComplementEdgesAccEncodedType, X] using hComp
  have hCodedEdges :
      TMPolyTimeMap X codedComplementEdgeListEncodedType
        (fun I : CliqueInput =>
          (codeComplementEdgesFromInput
            (I.graph.vertices, structuredComplementEdges I.graph)).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCodeAcc
    simpa [Function.comp, codeComplementEdgesAccEncodedType, X] using hComp
  have hFamilyInput :
      TMPolyTimeMap X compactFamilyInstructionInputEncodedType
        (fun I : CliqueInput =>
          (I.graph.vertices,
            (codeComplementEdgesFromInput
              (I.graph.vertices, structuredComplementEdges I.graph)).2)) :=
    TMPolyTimeMap.prod_mk hVertices hCodedEdges
  have hFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun I : CliqueInput =>
          compactFamilyFromInput
            (I.graph.vertices,
              (codeComplementEdgesFromInput
                (I.graph.vertices, structuredComplementEdges I.graph)).2)) := by
    have hComp := TMPolyTimeMap.comp compactFamilyFromInput_tm_polytime hFamilyInput
    simpa [Function.comp, compactFamilyInstructionInputEncodedType, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : CliqueInput =>
          ((codeComplementEdgesFromInput
              (I.graph.vertices, structuredComplementEdges I.graph)).1,
            compactFamilyFromInput
              (I.graph.vertices,
                (codeComplementEdgesFromInput
                  (I.graph.vertices, structuredComplementEdges I.graph)).2))) :=
    TMPolyTimeMap.prod_mk hUniverse hFamily
  have hSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType
        (fun I : CliqueInput =>
          { universeSize :=
              (codeComplementEdgesFromInput
                (I.graph.vertices, structuredComplementEdges I.graph)).1
            sets :=
              compactFamilyFromInput
                (I.graph.vertices,
                  (codeComplementEdgesFromInput
                    (I.graph.vertices, structuredComplementEdges I.graph)).2) }) := by
    have hComp :=
      TMPolyTimeMap.comp SetCovering.setSystemTupleToSetSystemInputTMBackedMap.tm_polytime
        hSystemTuple
    simpa [Function.comp, SetCovering.setSystemTupleToSetSystemInput, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueInput => I.k) := by
    simpa [X] using cliqueBudgetTMBackedMap.tm_polytime
  have hTargetTuple :
      TMPolyTimeMap X setPackingTupleStructuredEncodedType
        (fun I : CliqueInput =>
          ({ universeSize :=
              (codeComplementEdgesFromInput
                (I.graph.vertices, structuredComplementEdges I.graph)).1
             sets :=
              compactFamilyFromInput
                (I.graph.vertices,
                  (codeComplementEdgesFromInput
                    (I.graph.vertices, structuredComplementEdges I.graph)).2) }, I.k)) :=
    TMPolyTimeMap.prod_mk hSystem hBudget
  have hOut :
      TMPolyTimeMap X setPackingStructuredEncodedType
        (fun I : CliqueInput =>
          { system :=
              { universeSize :=
                  (codeComplementEdgesFromInput
                    (I.graph.vertices, structuredComplementEdges I.graph)).1
                sets :=
                  compactFamilyFromInput
                    (I.graph.vertices,
                      (codeComplementEdgesFromInput
                        (I.graph.vertices, structuredComplementEdges I.graph)).2) }
            k := I.k }) := by
    have hComp := TMPolyTimeMap.comp setPackingTupleToSetPackingInputTMBackedMap.tm_polytime
      hTargetTuple
    simpa [Function.comp, setPackingTupleToSetPackingInput, X] using hComp
  convert hOut using 1
  funext I
  simp [compactMap, compactSetSystemFromAcc]
  rw [codeComplementEdgesFromInput_eq, compactFamilyFromInput_eq]
  constructor <;> rfl

noncomputable def cliqueToSetPackingStructuredTMBackedMap :
    TMBackedCostedMap
      cliqueStructuredEncodedType
      setPackingStructuredEncodedType
      compactMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueToSetPackingStructured_compactPolynomialSizeBound
  tm_polytime := cliqueToSetPackingStructured_tm_polytime

noncomputable def cliqueToSetPackingStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      cliqueStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    cliqueToSetPackingStructuredTMBackedMap
    (by
      intro I
      simpa [cliqueStructuredDecisionProblem, setPackingStructuredDecisionProblem,
        cliqueDecisionProblem] using compactMap_correct I)

noncomputable def cliqueToSetPackingStructuredTMKarpReduction :
    TMKarpReduction
      cliqueStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  cliqueToSetPackingStructuredTMBackedKarpReduction.toTMKarpReduction

noncomputable def cliqueToSetPackingStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      cliqueStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  cliqueToSetPackingStructuredTMBackedKarpReduction.toCostedKarpReduction

end SetPacking
end Karp21
end ComplexityReduction
