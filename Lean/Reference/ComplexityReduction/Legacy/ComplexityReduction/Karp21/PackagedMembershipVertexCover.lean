/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetCovering
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Vertex Cover.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace VertexCover

/--
Finite-certificate verifier for faithful structured Vertex Cover, reusing the
verified direct-TM Vertex-Cover-to-Set-Covering map and Set Covering verifier.
-/
def vertexCoverStructuredFiniteVerify (I : VertexCoverInput) (cover : List Nat) :
    Bool :=
  setCoveringStructuredFiniteVerify (SetCovering.map I) cover

theorem edgeSetSystem_getElemOpt_eq_incident
    (I : VertexCoverInput) {v : Nat} (hv : v < I.graph.vertices) :
    ((SetCovering.map I).system.sets[v]?.getD []) =
      SetCovering.incidentEdgeIndices I v := by
  simp [SetCovering.map, SetCovering.edgeSetSystem, hv]

theorem edgeSetSystem_getD_eq_incident
    (I : VertexCoverInput) {v : Nat} (hv : v < I.graph.vertices) :
    (SetCovering.map I).system.sets.getD v [] =
      SetCovering.incidentEdgeIndices I v := by
  simp [SetCovering.map, SetCovering.edgeSetSystem, hv]

theorem vertexCoverStructuredFiniteVerify_eq_true_iff
    (I : VertexCoverInput) (cover : List Nat) :
    vertexCoverStructuredFiniteVerify I cover = true ↔
      cover.length ≤ I.k ∧
        VerticesWithinBounds I.graph cover ∧
        CoversEdges I.graph cover := by
  rw [vertexCoverStructuredFiniteVerify,
    setCoveringStructuredFiniteVerify_eq_true_iff]
  constructor
  · rintro ⟨hLen, hWithin, hCoversUniverse⟩
    refine ⟨by simpa [SetCovering.map] using hLen, ?_, ?_⟩
    · intro v hv
      simpa [SetCovering.map, SetCovering.edgeSetSystem] using hWithin v hv
    · intro e he
      rcases List.mem_iff_get.mp he with ⟨j, hjEq⟩
      have hCovered := hCoversUniverse j.val (by
        simp [SetCovering.map, SetCovering.edgeSetSystem, j.isLt])
      rcases hCovered with ⟨v, hvCover, hjIncidentMapped⟩
      have hvLt : v < I.graph.vertices := by
        simpa [SetCovering.map, SetCovering.edgeSetSystem] using hWithin v hvCover
      have hjIncident :
          j.val ∈ SetCovering.incidentEdgeIndices I v := by
        simpa [edgeSetSystem_getElemOpt_eq_incident I hvLt] using hjIncidentMapped
      have hEndpoint :=
        (SetCovering.mem_incidentEdgeIndices_iff I v j.val).1 hjIncident |>.2
      have hGetD : I.graph.edges.getD j.val (0, 0) = e := by
        rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) j.isLt]
        exact hjEq
      rw [hGetD] at hEndpoint
      rcases hEndpoint with hLeft | hRight
      · exact Or.inl (by simpa [hLeft] using hvCover)
      · exact Or.inr (by simpa [hRight] using hvCover)
  · rintro ⟨hLen, hWithin, hCoversEdges⟩
    refine ⟨by simpa [SetCovering.map] using hLen, ?_, ?_⟩
    · intro v hv
      simpa [SetCovering.map, SetCovering.edgeSetSystem] using hWithin v hv
    · intro j hj
      let e := I.graph.edges.getD j (0, 0)
      have heMem : e ∈ I.graph.edges := by
        dsimp [e]
        rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) hj]
        exact List.getElem_mem _
      rcases hCoversEdges e heMem with hLeft | hRight
      · refine ⟨e.1, hLeft, ?_⟩
        have hvLt : e.1 < I.graph.vertices := hWithin e.1 hLeft
        have hjIncident :
            j ∈ SetCovering.incidentEdgeIndices I e.1 := by
          rw [SetCovering.mem_incidentEdgeIndices_iff]
          exact ⟨hj, Or.inl rfl⟩
        rw [edgeSetSystem_getD_eq_incident I hvLt]
        exact hjIncident
      · refine ⟨e.2, hRight, ?_⟩
        have hvLt : e.2 < I.graph.vertices := hWithin e.2 hRight
        have hjIncident :
            j ∈ SetCovering.incidentEdgeIndices I e.2 := by
          rw [SetCovering.mem_incidentEdgeIndices_iff]
          exact ⟨hj, Or.inr rfl⟩
        rw [edgeSetSystem_getD_eq_incident I hvLt]
        exact hjIncident

theorem vertexCoverStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : VertexCoverInput × List Nat =>
        vertexCoverStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType
  have hInstance :
      TMPolyTimeMap X vertexCoverStructuredEncodedType
        (fun p : VertexCoverInput × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst vertexCoverStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : VertexCoverInput × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd vertexCoverStructuredEncodedType setStructuredEncodedType
  have hMapped :
      TMPolyTimeMap X setCoveringStructuredEncodedType
        (fun p : VertexCoverInput × List Nat => SetCovering.map p.1) := by
    have hComp := TMPolyTimeMap.comp SetCovering.vertexCoverToSetCoveringStructured_tm_polytime
      hInstance
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringStructuredEncodedType setStructuredEncodedType)
        (fun p : VertexCoverInput × List Nat => (SetCovering.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp setCoveringStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, vertexCoverStructuredFiniteVerify, X] using hComp

theorem vertexCoverCertificate_inputSize_le_square
    (I : VertexCoverInput) (cover : List Nat)
    (hLen : cover.length ≤ I.k)
    (hWithin : VerticesWithinBounds I.graph cover) :
    setStructuredEncodedType.inputSize cover ≤
      (vertexCoverStructuredEncodedType.inputSize I) ^ 2 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le
    I.graph.vertices cover hWithin
  have hK : I.k ≤ S := by
    simpa [S] using SetCovering.vertexCoverStructured_inputSize_ge_budget I
  have hVertices : I.graph.vertices + 1 ≤ S := by
    change I.graph.vertices + 1 ≤ vertexCoverStructuredEncodedType.inputSize I
    rw [vertexCoverStructured_inputSize_eq, graphStructured_inputSize_eq]
    omega
  calc
    setStructuredEncodedType.inputSize cover
        ≤ cover.length * (I.graph.vertices + 1) := hCert
    _ ≤ I.k * (I.graph.vertices + 1) :=
        Nat.mul_le_mul_right (I.graph.vertices + 1) hLen
    _ ≤ S * S := Nat.mul_le_mul hK hVertices
    _ = S ^ 2 := by ring

end VertexCover

/-- Direct finite-certificate TM verifier for faithful structured Vertex Cover. -/
noncomputable def vertexCoverStructuredFiniteTMVerifier :
    TMVerifier vertexCoverStructuredDecisionProblem where
  Cert := setStructuredEncodedType
  verify := VertexCover.vertexCoverStructuredFiniteVerify
  verifier_polytime := VertexCover.vertexCoverStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨cover, hLen, _hNodup, hWithin, hCovers⟩
    refine ⟨cover, ?_, ?_⟩
    · simpa using
        VertexCover.vertexCoverCertificate_inputSize_le_square I cover hLen hWithin
    · exact (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff I cover).2
        ⟨hLen, hWithin, hCovers⟩
  sound := by
    intro I cover hVerify
    change List Nat at cover
    rcases (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff I cover).1 hVerify with
      ⟨hLen, hWithin, hCovers⟩
    refine ⟨cover.dedup, ?_, List.nodup_dedup cover, ?_, ?_⟩
    · exact (List.Sublist.length_le (List.dedup_sublist cover)).trans hLen
    · intro v hv
      exact hWithin v (List.mem_dedup.mp hv)
    · intro e he
      rcases hCovers e he with hLeft | hRight
      · exact Or.inl (List.mem_dedup.mpr hLeft)
      · exact Or.inr (List.mem_dedup.mpr hRight)

theorem vertexCoverStructured_TMInNP :
    TMInNP vertexCoverStructuredDecisionProblem :=
  TMInNP.intro vertexCoverStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
