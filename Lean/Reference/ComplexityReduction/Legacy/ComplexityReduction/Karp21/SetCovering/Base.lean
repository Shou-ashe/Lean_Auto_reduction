/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import Mathlib.Data.List.Dedup

/-!
Third P15b target: Vertex Cover to Set Covering.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetCovering

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/--
For a vertex `v`, list the source-edge indices incident to `v`.  The target
set-cover universe is the edge-index set.
-/
def incidentEdgeIndices (I : VertexCoverInput) (v : Nat) : List Nat :=
  I.graph.edges.findIdxs fun e => decide (e.1 = v ∨ e.2 = v)

theorem mem_incidentEdgeIndices_iff (I : VertexCoverInput) (v j : Nat) :
    j ∈ incidentEdgeIndices I v ↔
      j < I.graph.edges.length ∧
        let e := I.graph.edges.getD j (0, 0)
        e.1 = v ∨ e.2 = v := by
  constructor
  · intro hj
    rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.graph.edges)
        (p := fun e : Nat × Nat => decide (e.1 = v ∨ e.2 = v))).1 hj with
      ⟨hjLt, hPred⟩
    refine ⟨hjLt, ?_⟩
    rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) hjLt]
    exact of_decide_eq_true hPred
  · rintro ⟨hjLt, hEndpoint⟩
    rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) hjLt] at hEndpoint
    exact
      (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.graph.edges)
        (p := fun e : Nat × Nat => decide (e.1 = v ∨ e.2 = v))).2
        ⟨hjLt, by exact decide_eq_true hEndpoint⟩

/-- Incidence set-system for the standard Vertex Cover to Set Covering reduction. -/
def edgeSetSystem (I : VertexCoverInput) : SetSystemInput where
  universeSize := I.graph.edges.length
  sets := (List.range I.graph.vertices).map (incidentEdgeIndices I)

theorem mem_edgeSetSystem_sets_iff (I : VertexCoverInput) (S : List Nat) :
    S ∈ (edgeSetSystem I).sets ↔
      ∃ v, v < I.graph.vertices ∧ S = incidentEdgeIndices I v := by
  constructor
  · intro hS
    rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
    exact ⟨v, by simpa using hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩

/-- A canonical vertex naming a set in the incidence family. -/
noncomputable def vertexOfSet (I : VertexCoverInput) (S : List Nat) : Nat := by
  classical
  exact if h : S ∈ (edgeSetSystem I).sets then
    Classical.choose ((mem_edgeSetSystem_sets_iff I S).1 h)
  else 0

theorem vertexOfSet_lt_of_mem (I : VertexCoverInput) {S : List Nat}
    (hS : S ∈ (edgeSetSystem I).sets) :
    vertexOfSet I S < I.graph.vertices := by
  classical
  simp [vertexOfSet, hS,
    (Classical.choose_spec ((mem_edgeSetSystem_sets_iff I S).1 hS)).1]

theorem incidentEdgeIndices_vertexOfSet_of_mem (I : VertexCoverInput) {S : List Nat}
    (hS : S ∈ (edgeSetSystem I).sets) :
    S = incidentEdgeIndices I (vertexOfSet I S) := by
  classical
  unfold vertexOfSet
  rw [dif_pos hS]
  exact (Classical.choose_spec ((mem_edgeSetSystem_sets_iff I S).1 hS)).2

/-- P15b syntax map from Vertex Cover to Set Covering. -/
def map (I : VertexCoverInput) : SetCoveringInput where
  system := edgeSetSystem I
  k := I.k

theorem map_correct (I : VertexCoverInput) :
    vertexCoverDecisionProblem.isYes I ↔ SetCovering (map I) := by
  constructor
  · rintro ⟨cover, hLen, hNodup, hBounds, hCovers⟩
    let selected := cover.map (incidentEdgeIndices I)
    refine ⟨selected, by simpa [selected] using hLen, ?_, ?_⟩
    · intro S hS
      rcases List.mem_map.mp hS with ⟨v, hv, rfl⟩
      exact (mem_edgeSetSystem_sets_iff I (incidentEdgeIndices I v)).2
        ⟨v, hBounds v hv, rfl⟩
    · intro j hj
      let e := I.graph.edges.getD j (0, 0)
      have hjEdges : j < I.graph.edges.length := by
        simpa [map, edgeSetSystem] using hj
      have heMem : e ∈ I.graph.edges := by
        dsimp [e]
        rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) hjEdges]
        exact List.getElem_mem _
      rcases hCovers e heMem with hv | hv
      · refine ⟨incidentEdgeIndices I e.1, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨e.1, hv, rfl⟩
        · rw [mem_incidentEdgeIndices_iff]
          exact ⟨hjEdges, Or.inl rfl⟩
      · refine ⟨incidentEdgeIndices I e.2, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨e.2, hv, rfl⟩
        · rw [mem_incidentEdgeIndices_iff]
          exact ⟨hjEdges, Or.inr rfl⟩
  · rintro ⟨selected, hLen, hFamily, hCovers⟩
    let coverWithDup := selected.map (vertexOfSet I)
    let cover := coverWithDup.dedup
    refine ⟨cover, ?_, List.nodup_dedup coverWithDup, ?_, ?_⟩
    · exact (List.Sublist.length_le (List.dedup_sublist coverWithDup)).trans
        (by simpa [coverWithDup] using hLen)
    · intro v hv
      have hv' : v ∈ coverWithDup := List.mem_dedup.mp hv
      rcases List.mem_map.mp hv' with ⟨S, hSSelected, rfl⟩
      exact vertexOfSet_lt_of_mem I (hFamily S hSSelected)
    · intro e he
      rcases List.mem_iff_get.mp he with ⟨j, hjEq⟩
      have hCovered := hCovers j.val j.isLt
      rcases hCovered with ⟨S, hSSelected, hjS⟩
      have hSFamily := hFamily S hSSelected
      have hIncident := incidentEdgeIndices_vertexOfSet_of_mem I hSFamily
      have hjIncident :
          j.val ∈ incidentEdgeIndices I (vertexOfSet I S) := by
        rw [hIncident] at hjS
        exact hjS
      have hEndpoint :=
        (mem_incidentEdgeIndices_iff I (vertexOfSet I S) j.val).1 hjIncident |>.2
      have hGetD : I.graph.edges.getD j.val (0, 0) = e := by
        rw [List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) j.isLt]
        exact hjEq
      have hvCover : vertexOfSet I S ∈ cover := by
        exact List.mem_dedup.mpr (List.mem_map.mpr ⟨S, hSSelected, rfl⟩)
      rw [hGetD] at hEndpoint
      rcases hEndpoint with hLeft | hRight
      · exact Or.inl (by simpa [hLeft] using hvCover)
      · exact Or.inr (by simpa [hRight] using hvCover)

/-- Each incidence list is no longer than the source edge list. -/
theorem incidentEdgeIndices_length_le (I : VertexCoverInput) (v : Nat) :
    (incidentEdgeIndices I v).length ≤ I.graph.edges.length := by
  simpa [incidentEdgeIndices] using
    (List.countP_le_length (l := I.graph.edges)
      (p := fun e : Nat × Nat => decide (e.1 = v ∨ e.2 = v)))

/-- Structured size of one incidence set is quadratic in the source edge count. -/
theorem incidentEdgeIndices_structured_inputSize_le (I : VertexCoverInput) (v : Nat) :
    setStructuredEncodedType.inputSize (incidentEdgeIndices I v) ≤
      I.graph.edges.length * (I.graph.edges.length + 2) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat (incidentEdgeIndices I v) (I.graph.edges.length + 1)
      (by
        intro j hj
        have hjLt := (mem_incidentEdgeIndices_iff I v j).1 hj |>.1
        simp [EncodedType.inputSize, EncodedType.nat]
        omega)
  have hLen := incidentEdgeIndices_length_le I v
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (I.graph.edges.length + 2) hLen
    simpa [setStructuredEncodedType, Nat.add_assoc] using hMul)

/-- Structured size of the incidence family is polynomial in source vertices and edges. -/
theorem edgeSetSystem_family_structured_inputSize_le (I : VertexCoverInput) :
    setFamilyStructuredEncodedType.inputSize (edgeSetSystem I).sets ≤
      I.graph.vertices * (I.graph.edges.length * (I.graph.edges.length + 2) + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (edgeSetSystem I).sets
      (I.graph.edges.length * (I.graph.edges.length + 2))
      (by
        intro S hS
        rcases (mem_edgeSetSystem_sets_iff I S).1 hS with ⟨v, _hv, rfl⟩
        exact incidentEdgeIndices_structured_inputSize_le I v)
  have hLen : (edgeSetSystem I).sets.length = I.graph.vertices := by
    simp [edgeSetSystem]
  exact hList.trans (by
    exact Nat.mul_le_mul_right
      (I.graph.edges.length * (I.graph.edges.length + 2) + 1)
      (le_of_eq hLen))

/-- Exact structured set-system input size under the project-local field encoding. -/
theorem setSystemStructured_inputSize_eq (S : SetSystemInput) :
    setSystemStructuredEncodedType.inputSize S =
      S.universeSize + setFamilyStructuredEncodedType.inputSize S.sets + 2 := by
  change setSystemTupleStructuredEncodedType.inputSize (S.universeSize, S.sets) =
    S.universeSize + setFamilyStructuredEncodedType.inputSize S.sets + 2
  simp [setSystemTupleStructuredEncodedType]
  omega

/-- Reify the tuple-shaped Set System payload as the project target structure. -/
def setSystemTupleToSetSystemInput
    (p : setSystemTupleStructuredEncodedType.Carrier) : SetSystemInput where
  universeSize := p.1
  sets := p.2

theorem setSystemTupleToSetSystemInput_encode
    (p : setSystemTupleStructuredEncodedType.Carrier) :
    setSystemStructuredEncodedType.encode (setSystemTupleToSetSystemInput p) =
      setSystemTupleStructuredEncodedType.encode p := by
  rcases p with ⟨universeSize, sets⟩
  rfl

noncomputable def setSystemTupleToSetSystemInputTMBackedMap :
    TMBackedCostedMap
      setSystemTupleStructuredEncodedType
      setSystemStructuredEncodedType
      setSystemTupleToSetSystemInput :=
  TMBackedCostedMap.ofEncodingEquiv
    setSystemTupleStructuredEncodedType
    setSystemStructuredEncodedType
    setSystemTupleToSetSystemInput
    (Equiv.refl setSystemTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change setSystemStructuredEncodedType.encode (setSystemTupleToSetSystemInput p) =
        (setSystemTupleStructuredEncodedType.encode p).map id
      simp [setSystemTupleToSetSystemInput_encode])

/-- Structured size of the incidence set-system is polynomial in source vertices and edges. -/
theorem edgeSetSystem_structured_inputSize_le (I : VertexCoverInput) :
    setSystemStructuredEncodedType.inputSize (edgeSetSystem I) ≤
      I.graph.edges.length +
        I.graph.vertices * (I.graph.edges.length * (I.graph.edges.length + 2) + 1) + 2 := by
  have hFamily := edgeSetSystem_family_structured_inputSize_le I
  rw [setSystemStructured_inputSize_eq]
  change
    I.graph.edges.length + setFamilyStructuredEncodedType.inputSize (edgeSetSystem I).sets + 2 ≤
      I.graph.edges.length +
        I.graph.vertices * (I.graph.edges.length * (I.graph.edges.length + 2) + 1) + 2
  omega

/-- Exact structured Set Covering input size under the project-local field encoding. -/
theorem setCoveringStructured_inputSize_eq (I : SetCoveringInput) :
    setCoveringStructuredEncodedType.inputSize I =
      setSystemStructuredEncodedType.inputSize I.system + I.k + 2 := by
  change setCoveringTupleStructuredEncodedType.inputSize (I.system, I.k) =
    setSystemStructuredEncodedType.inputSize I.system + I.k + 2
  simp [setCoveringTupleStructuredEncodedType]
  omega

/-- Reify the tuple-shaped Set Covering payload as the project target structure. -/
def setCoveringTupleToSetCoveringInput
    (p : setCoveringTupleStructuredEncodedType.Carrier) : SetCoveringInput where
  system := p.1
  k := p.2

theorem setCoveringTupleToSetCoveringInput_encode
    (p : setCoveringTupleStructuredEncodedType.Carrier) :
    setCoveringStructuredEncodedType.encode (setCoveringTupleToSetCoveringInput p) =
      setCoveringTupleStructuredEncodedType.encode p := by
  rcases p with ⟨system, k⟩
  rfl

noncomputable def setCoveringTupleToSetCoveringInputTMBackedMap :
    TMBackedCostedMap
      setCoveringTupleStructuredEncodedType
      setCoveringStructuredEncodedType
      setCoveringTupleToSetCoveringInput :=
  TMBackedCostedMap.ofEncodingEquiv
    setCoveringTupleStructuredEncodedType
    setCoveringStructuredEncodedType
    setCoveringTupleToSetCoveringInput
    (Equiv.refl setCoveringTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change setCoveringStructuredEncodedType.encode (setCoveringTupleToSetCoveringInput p) =
        (setCoveringTupleStructuredEncodedType.encode p).map id
      simp [setCoveringTupleToSetCoveringInput_encode])

theorem vertexCoverStructured_inputSize_ge_vertices (I : VertexCoverInput) :
    I.graph.vertices ≤ vertexCoverStructuredEncodedType.inputSize I := by
  rw [ComplexityReduction.Karp21.VertexCover.vertexCoverStructured_inputSize_eq,
    ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
  omega

theorem vertexCoverStructured_inputSize_ge_edges_length (I : VertexCoverInput) :
    I.graph.edges.length ≤ vertexCoverStructuredEncodedType.inputSize I := by
  have hEdges :
      I.graph.edges.length ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeListStructuredEncodedType, EncodedType.inputSize] using
      (TM2Programs.listEncode_length_ge_length edgeStructuredEncodedType I.graph.edges)
  rw [ComplexityReduction.Karp21.VertexCover.vertexCoverStructured_inputSize_eq,
    ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
  omega

theorem vertexCoverStructured_inputSize_ge_budget (I : VertexCoverInput) :
    I.k ≤ vertexCoverStructuredEncodedType.inputSize I := by
  rw [ComplexityReduction.Karp21.VertexCover.vertexCoverStructured_inputSize_eq]
  omega

/-- Structured output size of the Vertex-Cover-to-Set-Covering map is polynomial in
the structured source size. -/
theorem setCoveringStructured_inputSize_map_le_vertexCover_poly (I : VertexCoverInput) :
    setCoveringStructuredEncodedType.inputSize (map I) ≤
      10 * (vertexCoverStructuredEncodedType.inputSize I + 1) ^ 3 + 20 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hSystem := edgeSetSystem_structured_inputSize_le I
  have hV : I.graph.vertices ≤ S := vertexCoverStructured_inputSize_ge_vertices I
  have hE : I.graph.edges.length ≤ S := vertexCoverStructured_inputSize_ge_edges_length I
  have hK : I.k ≤ S := vertexCoverStructured_inputSize_ge_budget I
  have hE2 : I.graph.edges.length + 2 ≤ S + 2 := Nat.add_le_add_right hE 2
  have hEE : I.graph.edges.length * (I.graph.edges.length + 2) ≤ S * (S + 2) :=
    Nat.mul_le_mul hE hE2
  have hVEE :
      I.graph.vertices * (I.graph.edges.length * (I.graph.edges.length + 2)) ≤
        S * (S * (S + 2)) := by
    exact Nat.mul_le_mul hV hEE
  have hFamilyTerm :
      I.graph.vertices *
          (I.graph.edges.length * (I.graph.edges.length + 2) + 1) ≤
        S * (S * (S + 2)) + S := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add hVEE hV
  calc
    setCoveringStructuredEncodedType.inputSize (map I)
        = setSystemStructuredEncodedType.inputSize (edgeSetSystem I) + I.k + 2 := by
            simp [map, setCoveringStructured_inputSize_eq]
    _ ≤ (I.graph.edges.length +
          I.graph.vertices * (I.graph.edges.length * (I.graph.edges.length + 2) + 1) + 2) +
          I.k + 2 := by
            omega
    _ ≤ S + (S * (S * (S + 2)) + S) + 2 + S + 2 := by
            omega
    _ ≤ 10 * (S + 1) ^ 3 + 20 := by
            nlinarith

/-- Polynomial output-size bound for the structured Vertex-Cover-to-Set-Covering map. -/
theorem vertexCoverToSetCoveringStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize I)
      (fun J : SetCoveringInput => setCoveringStructuredEncodedType.inputSize J)
      map := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro I
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hBase := setCoveringStructured_inputSize_map_le_vertexCover_poly I
  have hPoly : 10 * (S + 1) ^ 3 + 20 ≤ 1000 * S ^ 3 + 1000 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        ring_nf
        omega
  exact hBase.trans hPoly

/-- Direct TM-backed raw-codomain Karp reduction from Vertex Cover to Set Covering. -/
noncomputable def vertexCoverToSetCoveringTMBackedKarpReduction :
    TMBackedCostedReduction vertexCoverDecisionProblem setCoveringDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.rawCodomain vertexCoverDecisionProblem.Instance SetCoveringInput map)
    (by
      intro I
      simpa [setCoveringDecisionProblem] using map_correct I)

/-- Costed Karp reduction from Vertex Cover to Set Covering. -/
noncomputable def vertexCoverToSetCoveringKarpReduction :
    KarpReductionM CostedPolyTimeModel vertexCoverDecisionProblem setCoveringDecisionProblem :=
  vertexCoverToSetCoveringTMBackedKarpReduction.toCostedKarpReduction

/--
Proof-carrying composed raw-codomain reduction from Clique to Set Covering via
Vertex Cover.
-/
noncomputable def cliqueToSetCoveringViaVertexCoverTMBackedKarpReduction :
    TMBackedCostedReduction cliqueDecisionProblem setCoveringDecisionProblem :=
  TMBackedCostedReduction.comp
    vertexCoverToSetCoveringTMBackedKarpReduction
    VertexCover.cliqueToVertexCoverTMBackedKarpReduction

/--
Costed Karp reduction from the faithful finite-alphabet Vertex Cover encoding to
the faithful finite-alphabet Set Covering encoding.

This is the pre-P16c costed-only compatibility theorem.  The public structured
transport name is supplied by `SetCovering.FamilyRunner` from a direct TM-backed
witness.
-/
def vertexCoverToSetCoveringStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem setCoveringStructuredDecisionProblem where
  f :=
    { toFun := map
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            vertexCoverToSetCoveringStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [vertexCoverStructuredDecisionProblem, setCoveringStructuredDecisionProblem,
      vertexCoverDecisionProblem] using map_correct I

/-- First witness in the raw-encoding collision for Set Covering. -/
def rawEncodingCollisionA : SetCoveringInput where
  system := { universeSize := 0, sets := [] }
  k := 0

/-- Second witness in the raw-encoding collision for Set Covering. -/
def rawEncodingCollisionB : SetCoveringInput where
  system := { universeSize := 1, sets := [] }
  k := 0

theorem rawEncodingCollisionA_ne_rawEncodingCollisionB :
    rawEncodingCollisionA ≠ rawEncodingCollisionB := by
  intro h
  have hu :
      rawEncodingCollisionA.system.universeSize =
        rawEncodingCollisionB.system.universeSize :=
    congrArg (fun I : SetCoveringInput => I.system.universeSize) h
  norm_num [rawEncodingCollisionA, rawEncodingCollisionB] at hu

/--
The current raw encoding for Set Covering is not faithful: two different formal
instances encode as the same empty string.
-/
theorem setCoveringRawEncoding_not_faithful :
    ¬ setCoveringDecisionProblem.FaithfulEncoding := by
  refine EncodedDecisionProblem.EncodingCollision.not_faithful ?_
  exact
    ⟨rawEncodingCollisionA, rawEncodingCollisionB,
      rawEncodingCollisionA_ne_rawEncodingCollisionB, rfl⟩

/-- The structured finite-alphabet Set Covering encoding is faithful. -/
theorem setCoveringStructuredEncoding_faithful :
    setCoveringStructuredDecisionProblem.FaithfulEncoding where
  injective := setCoveringStructuredEncodedType_encode_injective

theorem setCoveringStructuredEncoding_predicateRespects :
    setCoveringStructuredDecisionProblem.PredicateRespectsEncoding :=
  setCoveringStructuredEncoding_faithful.predicateRespects

theorem setCoveringStructuredEncoding_accepts_encode_iff (I : SetCoveringInput) :
    setCoveringStructuredDecisionProblem.toEncodedLanguage.accepts
        (setCoveringStructuredEncodedType.encode I) ↔
      SetCovering I :=
  setCoveringStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Set Covering is locally in NP for the project-local costed model. -/
theorem setCoveringInNP :
    InNPEnc CostedPolyTimeModel setCoveringDecisionProblem :=
  decidableInNP setCoveringDecisionProblem

/-- Local NP-completeness of Set Covering via Vertex Cover. -/
theorem setCoveringNPComplete :
    NPCompleteEnc CostedPolyTimeModel setCoveringDecisionProblem :=
  NPCompleteEnc.transfer
    VertexCover.vertexCoverNPComplete
    ⟨vertexCoverToSetCoveringKarpReduction⟩
    setCoveringInNP

end SetCovering
end Karp21
end ComplexityReduction
