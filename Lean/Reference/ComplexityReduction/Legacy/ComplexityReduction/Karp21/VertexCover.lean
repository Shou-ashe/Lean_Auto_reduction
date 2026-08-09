/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.ProdSigma

/-!
Second P15b target: Clique to Vertex Cover.
-/

namespace ComplexityReduction
namespace Karp21
namespace VertexCover

open ComplexityReduction.Combinatorics.Graph

/-- A fixed no-instance of Vertex Cover. -/
def noInstance : VertexCoverInput where
  graph := { vertices := 2, edges := [(0, 1)], directed := false }
  k := 0

theorem noInstance_isNo :
    ¬ VertexCover noInstance := by
  rintro ⟨cover, hLen, _hNodup, _hBounds, hCovers⟩
  cases cover with
  | nil =>
      have hEdge := hCovers (0, 1) (by simp [noInstance])
      simp at hEdge
  | cons v vs =>
      simp [noInstance] at hLen

/-- All unordered non-edges of a graph, represented in increasing orientation. -/
def complementEdges (g : GraphInput) : List (Nat × Nat) :=
  structuredComplementEdges g

theorem mem_complementEdges_iff (g : GraphInput) (e : Nat × Nat) :
    e ∈ complementEdges g ↔
      e.1 < g.vertices ∧ e.2 < g.vertices ∧
        e.1 < e.2 ∧ ¬ HasUndirectedEdge g e.1 e.2 := by
  cases e with
  | mk u v =>
      simp [complementEdges, mem_structuredComplementEdges_iff]

/-- Undirected complement graph used by the standard Clique to Vertex Cover reduction. -/
noncomputable def complementGraph (g : GraphInput) : GraphInput where
  vertices := g.vertices
  edges := complementEdges g
  directed := false

theorem hasUndirectedEdge_comm (g : GraphInput) (u v : Nat) :
    HasUndirectedEdge g u v ↔ HasUndirectedEdge g v u := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem hasUndirectedEdge_complementGraph_iff (g : GraphInput) (u v : Nat) :
    HasUndirectedEdge (complementGraph g) u v ↔
      u < g.vertices ∧ v < g.vertices ∧ u ≠ v ∧ ¬ HasUndirectedEdge g u v := by
  constructor
  · intro h
    rcases h with h | h
    · rcases (mem_complementEdges_iff g (u, v)).1 h with ⟨hu, hv, huv, hNonedge⟩
      exact ⟨hu, hv, Nat.ne_of_lt huv, hNonedge⟩
    · rcases (mem_complementEdges_iff g (v, u)).1 h with ⟨hv, hu, hvu, hNonedge⟩
      refine ⟨hu, hv, Nat.ne_of_gt hvu, ?_⟩
      intro hEdge
      exact hNonedge ((hasUndirectedEdge_comm g u v).1 hEdge)
  · rintro ⟨hu, hv, huvNe, hNonedge⟩
    have hCases : u < v ∨ v < u := by omega
    rcases hCases with huv | hvu
    · exact Or.inl (by
        simp [complementGraph, mem_complementEdges_iff, hu, hv, huv, hNonedge])
    · exact Or.inr (by
        have hSymNonedge : ¬ HasUndirectedEdge g v u := by
          intro hEdge
          exact hNonedge ((hasUndirectedEdge_comm g u v).2 hEdge)
        simp [complementGraph, mem_complementEdges_iff, hv, hu, hvu, hSymNonedge])

theorem complementGraph_wellFormed (g : GraphInput) :
    WellFormed (complementGraph g) := by
  intro e he
  have hmem := (mem_complementEdges_iff g e).1 (by simpa [complementGraph] using he)
  exact ⟨hmem.1, hmem.2.1⟩

theorem nodup_length_le_of_verticesWithinBounds {g : GraphInput} {vs : List Nat}
    (hNodup : vs.Nodup) (hBounds : VerticesWithinBounds g vs) :
    vs.length ≤ g.vertices := by
  let s : Finset Nat := vs.toFinset
  have hs : s ⊆ Finset.range g.vertices := by
    intro v hv
    exact Finset.mem_range.mpr (hBounds v (by simpa [s] using hv))
  have hCard := Finset.card_le_card hs
  simpa [s, List.toFinset_card_of_nodup hNodup] using hCard

theorem noClique_of_vertices_lt_k (I : CliqueInput) (h : I.graph.vertices < I.k) :
    ¬ Clique I := by
  rintro ⟨vs, hLen, hNodup, hBounds, _hAdj⟩
  have hLe := nodup_length_le_of_verticesWithinBounds hNodup hBounds
  omega

/-- P15b syntax map from Clique to Vertex Cover via the graph complement. -/
noncomputable def map (I : CliqueInput) : VertexCoverInput :=
  if I.k ≤ I.graph.vertices then
    { graph := complementGraph I.graph
      k := I.graph.vertices - I.k }
  else noInstance

theorem map_correct (I : CliqueInput) :
    cliqueDecisionProblem.isYes I ↔ VertexCover (map I) := by
  classical
  by_cases hk : I.k ≤ I.graph.vertices
  · constructor
    · rintro ⟨vs, hLen, hNodup, hBounds, hAdj⟩
      let cliqueSet : Finset Nat := vs.toFinset
      have hCliqueSubset : cliqueSet ⊆ Finset.range I.graph.vertices := by
        intro v hv
        exact Finset.mem_range.mpr (hBounds v (by simpa [cliqueSet] using hv))
      let coverSet : Finset Nat := Finset.range I.graph.vertices \ cliqueSet
      refine ⟨coverSet.toList, ?_, Finset.nodup_toList coverSet, ?_, ?_⟩
      · have hCoverLen : coverSet.toList.length = I.graph.vertices - I.k := by
          rw [Finset.length_toList, Finset.card_sdiff_of_subset hCliqueSubset,
            Finset.card_range]
          simp [cliqueSet, hLen, List.toFinset_card_of_nodup hNodup]
        simpa [map, hk] using le_of_eq hCoverLen
      · intro v hv
        have hvSet : v ∈ coverSet := Finset.mem_toList.mp hv
        have hvLt := Finset.mem_range.mp (Finset.mem_sdiff.mp hvSet).1
        simpa [map, hk, complementGraph] using hvLt
      · intro e he
        have he' := (mem_complementEdges_iff I.graph e).1 (by simpa [map, hk,
          complementGraph] using he)
        rcases he' with ⟨huBound, hvBound, huvLt, hNonedge⟩
        by_cases huCover : e.1 ∈ coverSet.toList
        · exact Or.inl huCover
        · right
          by_contra hvCover
          have huClique : e.1 ∈ cliqueSet := by
            have huRange : e.1 ∈ Finset.range I.graph.vertices := Finset.mem_range.mpr huBound
            have huNotCoverSet : e.1 ∉ coverSet := by
              intro h
              exact huCover (Finset.mem_toList.mpr h)
            by_contra huNotClique
            exact huNotCoverSet (Finset.mem_sdiff.mpr ⟨huRange, huNotClique⟩)
          have hvClique : e.2 ∈ cliqueSet := by
            have hvRange : e.2 ∈ Finset.range I.graph.vertices := Finset.mem_range.mpr hvBound
            have hvNotCoverSet : e.2 ∉ coverSet := by
              intro h
              exact hvCover (Finset.mem_toList.mpr h)
            by_contra hvNotClique
            exact hvNotCoverSet (Finset.mem_sdiff.mpr ⟨hvRange, hvNotClique⟩)
          have hEdge := hAdj e.1 (by simpa [cliqueSet] using huClique)
            e.2 (by simpa [cliqueSet] using hvClique) (Nat.ne_of_lt huvLt)
          exact hNonedge hEdge
    · intro hVC
      rcases hVC with ⟨cover, hLen, hNodup, hBounds, hCovers⟩
      let coverSet : Finset Nat := cover.toFinset
      have hCoverSubset : coverSet ⊆ Finset.range I.graph.vertices := by
        intro v hv
        exact Finset.mem_range.mpr (by
          have hvList : v ∈ cover := by simpa [coverSet] using hv
          simpa [map, hk, complementGraph] using hBounds v hvList)
      let available : Finset Nat := Finset.range I.graph.vertices \ coverSet
      have hAvailableCard : I.k ≤ available.card := by
        rw [Finset.card_sdiff_of_subset hCoverSubset, Finset.card_range]
        have hCoverCard : coverSet.card ≤ I.graph.vertices - I.k := by
          simpa [coverSet, List.toFinset_card_of_nodup hNodup, map, hk,
            complementGraph] using hLen
        omega
      rcases Finset.exists_subset_card_eq hAvailableCard with ⟨cliqueSet, hSub, hCard⟩
      refine ⟨cliqueSet.toList, by simp [Finset.length_toList, hCard],
        Finset.nodup_toList cliqueSet, ?_, ?_⟩
      · intro v hv
        have hvSet : v ∈ cliqueSet := Finset.mem_toList.mp hv
        have hvAvail := hSub hvSet
        exact Finset.mem_range.mp (Finset.mem_sdiff.mp hvAvail).1
      · intro u hu v hv huv
        have huSet : u ∈ cliqueSet := Finset.mem_toList.mp hu
        have hvSet : v ∈ cliqueSet := Finset.mem_toList.mp hv
        have huAvail := hSub huSet
        have hvAvail := hSub hvSet
        have huBound := Finset.mem_range.mp (Finset.mem_sdiff.mp huAvail).1
        have hvBound := Finset.mem_range.mp (Finset.mem_sdiff.mp hvAvail).1
        have huNotCoverSet := (Finset.mem_sdiff.mp huAvail).2
        have hvNotCoverSet := (Finset.mem_sdiff.mp hvAvail).2
        by_contra hNonedge
        have hCases : u < v ∨ v < u := by omega
        rcases hCases with huvLt | hvuLt
        · have hCompEdge : (u, v) ∈ (map I).graph.edges := by
            simp [map, hk, complementGraph, mem_complementEdges_iff, huBound, hvBound,
              huvLt, hNonedge]
          have hCovered := hCovers (u, v) hCompEdge
          rcases hCovered with huCover | hvCover
          · exact huNotCoverSet (by simpa [coverSet] using huCover)
          · exact hvNotCoverSet (by simpa [coverSet] using hvCover)
        · have hSymNonedge : ¬ HasUndirectedEdge I.graph v u := by
            intro hEdge
            exact hNonedge (hEdge.elim (fun h => Or.inr h) (fun h => Or.inl h))
          have hCompEdge : (v, u) ∈ (map I).graph.edges := by
            simp [map, hk, complementGraph, mem_complementEdges_iff, hvBound, huBound,
              hvuLt, hSymNonedge]
          have hCovered := hCovers (v, u) hCompEdge
          rcases hCovered with hvCover | huCover
          · exact hvNotCoverSet (by simpa [coverSet] using hvCover)
          · exact huNotCoverSet (by simpa [coverSet] using huCover)
  · constructor
    · intro hClique
      exact (noClique_of_vertices_lt_k I (Nat.lt_of_not_ge hk) hClique).elim
    · intro hVC
      exact (noInstance_isNo (by simpa [map, hk] using hVC)).elim

/-- Filtering never increases list length. -/
theorem filter_length_le {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases h : p x
      · simp [h, filter_length_le p xs]
      · exact Nat.le_trans (by simpa [h] using filter_length_le p xs) (Nat.le_succ xs.length)

/-- If every element encoding has size at most `B`, the delimiter-list encoding is linear in
the number of elements. -/
theorem encodedList_inputSize_le_length_mul_bound (X : EncodedType)
    (xs : List X.Carrier) (B : Nat)
    (hB : ∀ x ∈ xs, X.inputSize x ≤ B) :
    (EncodedType.list X).inputSize xs ≤ xs.length * (B + 1) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : X.inputSize x ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, X.inputSize y ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        (EncodedType.list X).inputSize (x :: xs)
            = X.inputSize x + 1 + (EncodedType.list X).inputSize xs := by
              simp
        _ ≤ B + 1 + xs.length * (B + 1) := by
              omega
        _ = (x :: xs).length * (B + 1) := by
              simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

/-- One edge whose endpoints are within an `n`-vertex graph has linear structured size. -/
theorem edgeStructured_inputSize_le_of_bounds {g : GraphInput} {e : Nat × Nat}
    (h : EdgeWithinBounds g e) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * g.vertices + 1 := by
  cases e with
  | mk u v =>
      simp [edgeStructuredEncodedType, EdgeWithinBounds] at h ⊢
      omega

theorem edgeStructured_inputSize_le_of_mem_complementEdges {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ complementEdges g) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * g.vertices + 1 := by
  have hmem := (mem_complementEdges_iff g e).1 he
  exact edgeStructured_inputSize_le_of_bounds ⟨hmem.1, hmem.2.1⟩

/-- The complement edge list has at most `n^2` candidate pairs. -/
theorem complementEdges_length_le (g : GraphInput) :
    (complementEdges g).length ≤ g.vertices * g.vertices := by
  have hOut :=
    complementEdgesFromCandidates_length_le
      (g.edges, strictNatPairCandidates g.vertices)
  have hCandidates :
      (strictNatPairCandidates g.vertices).length ≤ g.vertices * g.vertices := by
    rw [strictNatPairCandidates_replicate]
    exact strictNatPairCandidatesCore_length_le_square g.vertices
  simpa [complementEdges, structuredComplementEdges] using hOut.trans hCandidates

/-- Structured size of the complement edge list is polynomial in the vertex count. -/
theorem complementEdges_structured_inputSize_le (g : GraphInput) :
    edgeListStructuredEncodedType.inputSize (complementEdges g) ≤
      (g.vertices * g.vertices) * (2 * g.vertices + 2) := by
  have hList :=
    encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (complementEdges g) (2 * g.vertices + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_complementEdges he)
  have hLen := complementEdges_length_le g
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (2 * g.vertices + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

/-- Exact structured graph input size under the project-local field encoding. -/
theorem graphStructured_inputSize_eq (g : GraphInput) :
    graphStructuredEncodedType.inputSize g =
      g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4 := by
  change graphTupleStructuredEncodedType.inputSize (g.vertices, (g.edges, g.directed)) =
    g.vertices + edgeListStructuredEncodedType.inputSize g.edges + 4
  simp [graphTupleStructuredEncodedType, graphPayloadStructuredEncodedType]
  omega

/-- Structured size of the complement graph is polynomial in the source vertex count. -/
theorem complementGraph_structured_inputSize_le (g : GraphInput) :
    graphStructuredEncodedType.inputSize (complementGraph g) ≤
      g.vertices + (g.vertices * g.vertices) * (2 * g.vertices + 2) + 4 := by
  have hEdges := complementEdges_structured_inputSize_le g
  rw [graphStructured_inputSize_eq]
  simp [complementGraph]
  omega

/-- The structured source encoding includes the source vertex count in unary. -/
theorem cliqueStructured_inputSize_ge_vertices_succ (I : CliqueInput) :
    I.graph.vertices + 1 ≤ cliqueStructuredEncodedType.inputSize I := by
  have hGraph :
      I.graph.vertices + 1 ≤ graphStructuredEncodedType.inputSize I.graph := by
    rw [graphStructured_inputSize_eq]
    omega
  calc
    I.graph.vertices + 1 ≤ graphStructuredEncodedType.inputSize I.graph := hGraph
    _ ≤ cliqueStructuredEncodedType.inputSize I := by
      change graphStructuredEncodedType.inputSize I.graph ≤
        cliqueTupleStructuredEncodedType.inputSize (I.graph, I.k)
      simp [cliqueTupleStructuredEncodedType]
      omega

/-- Exact structured Vertex Cover input size under the project-local field encoding. -/
theorem vertexCoverStructured_inputSize_eq (I : VertexCoverInput) :
    vertexCoverStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.k + 2 := by
  change vertexCoverTupleStructuredEncodedType.inputSize (I.graph, I.k) =
    graphStructuredEncodedType.inputSize I.graph + I.k + 2
  simp [vertexCoverTupleStructuredEncodedType]
  omega

/-- Reify the tuple-shaped Vertex Cover payload as the project target structure. -/
def vertexCoverTupleToVertexCoverInput
    (p : vertexCoverTupleStructuredEncodedType.Carrier) : VertexCoverInput where
  graph := p.1
  k := p.2

theorem vertexCoverTupleToVertexCoverInput_encode
    (p : vertexCoverTupleStructuredEncodedType.Carrier) :
    vertexCoverStructuredEncodedType.encode (vertexCoverTupleToVertexCoverInput p) =
      vertexCoverTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, k⟩
  rfl

noncomputable def vertexCoverTupleToVertexCoverInputTMBackedMap :
    TMBackedCostedMap
      vertexCoverTupleStructuredEncodedType
      vertexCoverStructuredEncodedType
      vertexCoverTupleToVertexCoverInput :=
  TMBackedCostedMap.ofEncodingEquiv
    vertexCoverTupleStructuredEncodedType
    vertexCoverStructuredEncodedType
    vertexCoverTupleToVertexCoverInput
    (Equiv.refl vertexCoverTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change vertexCoverStructuredEncodedType.encode (vertexCoverTupleToVertexCoverInput p) =
        (vertexCoverTupleStructuredEncodedType.encode p).map id
      simp [vertexCoverTupleToVertexCoverInput_encode])

theorem cliqueToVertexCoverStructured_tm_polytime :
    TMPolyTimeMap cliqueStructuredEncodedType vertexCoverStructuredEncodedType map := by
  let X := cliqueStructuredEncodedType
  have hGraph : TMPolyTimeMap X graphStructuredEncodedType (fun I : CliqueInput => I.graph) := by
    simpa [X] using cliqueGraphTMBackedMap.tm_polytime
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun I : CliqueInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : CliqueInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hSourceEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun I : CliqueInput => I.graph.edges) := by
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
        (fun I : CliqueInput => complementEdges I.graph) := by
    have hComp := TMPolyTimeMap.comp complementEdgesFromCandidates_tm_polytime hComplementInput
    simpa [Function.comp, complementEdges, structuredComplementEdges, X] using hComp
  have hDirected :
      TMPolyTimeMap X EncodedType.bool (fun _ : CliqueInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hGraphPayloadOut :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : CliqueInput => (complementEdges I.graph, false)) :=
    TMPolyTimeMap.prod_mk hComplementEdges hDirected
  have hGraphTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : CliqueInput => (I.graph.vertices, (complementEdges I.graph, false))) :=
    TMPolyTimeMap.prod_mk hVertices hGraphPayloadOut
  have hComplementGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : CliqueInput => complementGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hGraphTuple
    simpa [Function.comp, Clique.graphTupleToGraph, complementGraph, X] using hComp
  have hBudgetSource : TMPolyTimeMap X EncodedType.nat (fun I : CliqueInput => I.k) := by
    simpa [X] using cliqueBudgetTMBackedMap.tm_polytime
  have hBudgetInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : CliqueInput => (I.graph.vertices, I.k)) :=
    TMPolyTimeMap.prod_mk hVertices hBudgetSource
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueInput => I.graph.vertices - I.k) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hBudgetInput
    simpa [Function.comp, X] using hComp
  have hTargetTuple :
      TMPolyTimeMap X vertexCoverTupleStructuredEncodedType
        (fun I : CliqueInput => (complementGraph I.graph, I.graph.vertices - I.k)) :=
    TMPolyTimeMap.prod_mk hComplementGraph hBudget
  have hTrueBranch :
      TMPolyTimeMap X vertexCoverStructuredEncodedType
        (fun I : CliqueInput =>
          { graph := complementGraph I.graph
            k := I.graph.vertices - I.k }) := by
    have hComp := TMPolyTimeMap.comp vertexCoverTupleToVertexCoverInputTMBackedMap.tm_polytime
      hTargetTuple
    simpa [Function.comp, vertexCoverTupleToVertexCoverInput, X] using hComp
  have hGuardSubInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : CliqueInput => (I.k, I.graph.vertices)) :=
    TMPolyTimeMap.prod_mk hBudgetSource hVertices
  have hGuardSub :
      TMPolyTimeMap X EncodedType.nat
        (fun I : CliqueInput => I.k - I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hGuardSubInput
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : CliqueInput => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hGuardEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : CliqueInput => (I.k - I.graph.vertices, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hGuardSub hZero
  have hGuardEq :
      TMPolyTimeMap X EncodedType.bool
        (fun I : CliqueInput => decide (I.k - I.graph.vertices = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hGuardEqInput
    simpa [Function.comp, X] using hComp
  have hGuard :
      TMPolyTimeMap X EncodedType.bool
        (fun I : CliqueInput => decide (I.k ≤ I.graph.vertices)) := by
    convert hGuardEq using 1
    funext I
    by_cases hk : I.k ≤ I.graph.vertices
    · have hSub : I.k - I.graph.vertices = 0 := Nat.sub_eq_zero_of_le hk
      simp [hk, hSub]
    · have hSub : I.k - I.graph.vertices ≠ 0 := by
        intro hZeroSub
        exact hk ((Nat.sub_eq_zero_iff_le).1 hZeroSub)
      simp [hk, hSub]
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun I : CliqueInput => (decide (I.k ≤ I.graph.vertices), I)) :=
    TMPolyTimeMap.prod_mk hGuard (TMPolyTimeMap.id X)
  have hFalseBranch :
      TMPolyTimeMap X vertexCoverStructuredEncodedType (fun _ : CliqueInput => noInstance) :=
    TMPolyTimeMap.const X vertexCoverStructuredEncodedType noInstance
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        vertexCoverStructuredEncodedType
        (fun p : Bool × CliqueInput =>
          match p.1 with
          | true =>
              { graph := complementGraph p.2.graph
                k := p.2.graph.vertices - p.2.k }
          | false => noInstance) :=
    graphBoolProduct_dispatch_tm_polytime X vertexCoverStructuredEncodedType
      (fFalse := fun _ : CliqueInput => noInstance)
      (fTrue := fun I : CliqueInput =>
        { graph := complementGraph I.graph
          k := I.graph.vertices - I.k })
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext I
  by_cases hk : I.k ≤ I.graph.vertices
  · simp [Function.comp, map, hk]
  · simp [Function.comp, map, hk]

/-- Structured output size of the Clique-to-Vertex-Cover map is cubic in the source vertex count. -/
theorem vertexCoverStructured_inputSize_map_le_vertices_poly (I : CliqueInput) :
    vertexCoverStructuredEncodedType.inputSize (map I) ≤
      10 * (I.graph.vertices + 1) ^ 3 + 20 := by
  classical
  by_cases hk : I.k ≤ I.graph.vertices
  · have hGraph := complementGraph_structured_inputSize_le I.graph
    have hBudget : I.graph.vertices - I.k ≤ I.graph.vertices := Nat.sub_le _ _
    calc
      vertexCoverStructuredEncodedType.inputSize (map I)
          = graphStructuredEncodedType.inputSize (complementGraph I.graph) + 1 +
              ((I.graph.vertices - I.k) + 1) := by
                simp [map, hk, vertexCoverStructured_inputSize_eq]
                omega
      _ ≤ (I.graph.vertices + (I.graph.vertices * I.graph.vertices) *
            (2 * I.graph.vertices + 2) + 4) + 1 + (I.graph.vertices + 1) := by
                omega
      _ ≤ 10 * (I.graph.vertices + 1) ^ 3 + 20 := by
                nlinarith
  · have hNo : vertexCoverStructuredEncodedType.inputSize noInstance ≤ 20 := by
      rw [vertexCoverStructured_inputSize_eq, graphStructured_inputSize_eq]
      change
        2 + (EncodedType.list edgeStructuredEncodedType).inputSize
          ([((0 : Nat), (1 : Nat))] : List (Nat × Nat)) + 4 + 2 ≤ 20
      have hEdge :
          edgeStructuredEncodedType.inputSize ((0 : Nat), (1 : Nat)) ≤ 4 := by
        change
          (EncodedType.prod EncodedType.nat EncodedType.nat).inputSize
            ((0 : Nat), (1 : Nat)) ≤ 4
        norm_num
      have hList :
          (EncodedType.list edgeStructuredEncodedType).inputSize
              ([((0 : Nat), (1 : Nat))] : List (Nat × Nat)) ≤ 1 * (4 + 1) :=
        encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
          ([((0 : Nat), (1 : Nat))] : List (Nat × Nat)) 4 (by
            intro e he
            have heq : e = ((0 : Nat), (1 : Nat)) := by
              exact List.mem_singleton.mp he
            simpa [heq] using hEdge)
      omega
    calc
      vertexCoverStructuredEncodedType.inputSize (map I)
          = vertexCoverStructuredEncodedType.inputSize noInstance := by
              simp [map, hk]
      _ ≤ 20 := hNo
      _ ≤ 10 * (I.graph.vertices + 1) ^ 3 + 20 := Nat.le_add_left 20 _

/-- Polynomial output-size bound for the structured Clique-to-Vertex-Cover map. -/
theorem cliqueToVertexCoverStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : CliqueInput => cliqueStructuredEncodedType.inputSize I)
      (fun J : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize J)
      map := by
  refine PolynomialSizeBound.intro_with 3 10 20 ?_
  intro I
  have hVertex := vertexCoverStructured_inputSize_map_le_vertices_poly I
  have hInput := cliqueStructured_inputSize_ge_vertices_succ I
  have hPow :
      (I.graph.vertices + 1) ^ 3 ≤ (cliqueStructuredEncodedType.inputSize I) ^ 3 :=
    Nat.pow_le_pow_left hInput 3
  exact hVertex.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hPow) 20)

noncomputable def cliqueToVertexCoverStructuredTMBackedMap :
    TMBackedCostedMap cliqueStructuredEncodedType vertexCoverStructuredEncodedType map where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueToVertexCoverStructured_polynomialSizeBound
  tm_polytime := cliqueToVertexCoverStructured_tm_polytime

/--
Proof-carrying TM2/costed reduction for the current raw-encoded Vertex Cover
target.  This is not a natural-language encoding conformance theorem.
-/
noncomputable def cliqueToVertexCoverTMBackedKarpReduction :
    TMBackedCostedReduction cliqueDecisionProblem vertexCoverDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.rawCodomain cliqueDecisionProblem.Instance VertexCoverInput map)
    map_correct

/-- Costed Karp reduction from Clique to Vertex Cover. -/
noncomputable def cliqueToVertexCoverKarpReduction :
    KarpReductionM CostedPolyTimeModel cliqueDecisionProblem vertexCoverDecisionProblem :=
  cliqueToVertexCoverTMBackedKarpReduction.toCostedKarpReduction

noncomputable def cliqueToVertexCoverStructuredTMBackedKarpReduction :
    TMBackedCostedReduction cliqueStructuredDecisionProblem vertexCoverStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    cliqueToVertexCoverStructuredTMBackedMap
    (by
      intro I
      simpa [cliqueStructuredDecisionProblem, vertexCoverStructuredDecisionProblem,
        cliqueDecisionProblem] using map_correct I)

noncomputable def cliqueToVertexCoverStructuredTMKarpReduction :
    TMKarpReduction cliqueStructuredDecisionProblem vertexCoverStructuredDecisionProblem :=
  cliqueToVertexCoverStructuredTMBackedKarpReduction.toTMKarpReduction

/-- Costed Karp reduction from faithful structured Clique to faithful structured Vertex Cover. -/
noncomputable def cliqueToVertexCoverStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      cliqueStructuredDecisionProblem vertexCoverStructuredDecisionProblem :=
  cliqueToVertexCoverStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- First witness in the raw-encoding collision for Vertex Cover. -/
def rawEncodingCollisionA : VertexCoverInput where
  graph := { vertices := 0, edges := [], directed := false }
  k := 0

/-- Second witness in the raw-encoding collision for Vertex Cover. -/
def rawEncodingCollisionB : VertexCoverInput where
  graph := { vertices := 1, edges := [], directed := false }
  k := 0

theorem rawEncodingCollisionA_ne_rawEncodingCollisionB :
    rawEncodingCollisionA ≠ rawEncodingCollisionB := by
  intro h
  have hv :
      rawEncodingCollisionA.graph.vertices = rawEncodingCollisionB.graph.vertices :=
    congrArg (fun I : VertexCoverInput => I.graph.vertices) h
  norm_num [rawEncodingCollisionA, rawEncodingCollisionB] at hv

/--
The current raw encoding for Vertex Cover is not faithful: two different
formal instances encode as the same empty string.
-/
theorem vertexCoverRawEncoding_not_faithful :
    ¬ vertexCoverDecisionProblem.FaithfulEncoding := by
  refine EncodedDecisionProblem.EncodingCollision.not_faithful ?_
  exact
    ⟨rawEncodingCollisionA, rawEncodingCollisionB,
      rawEncodingCollisionA_ne_rawEncodingCollisionB, rfl⟩

/--
The structured finite-alphabet Vertex Cover encoding is faithful.  This is the
first positive conformance theorem separating textbook instance semantics from
the current raw encoding.
-/
theorem vertexCoverStructuredEncoding_faithful :
    vertexCoverStructuredDecisionProblem.FaithfulEncoding where
  injective := vertexCoverStructuredEncodedType_encode_injective

theorem vertexCoverStructuredEncoding_predicateRespects :
    vertexCoverStructuredDecisionProblem.PredicateRespectsEncoding :=
  vertexCoverStructuredEncoding_faithful.predicateRespects

theorem vertexCoverStructuredEncoding_accepts_encode_iff (I : VertexCoverInput) :
    vertexCoverStructuredDecisionProblem.toEncodedLanguage.accepts
        (vertexCoverStructuredEncodedType.encode I) ↔
      VertexCover I :=
  vertexCoverStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Vertex Cover is locally in NP for the project-local costed model. -/
theorem vertexCoverInNP :
    InNPEnc CostedPolyTimeModel vertexCoverDecisionProblem :=
  decidableInNP vertexCoverDecisionProblem

/-- Local NP-completeness of Vertex Cover via Clique. -/
theorem vertexCoverNPComplete :
    NPCompleteEnc CostedPolyTimeModel vertexCoverDecisionProblem :=
  NPCompleteEnc.transfer
    Clique.cliqueNPComplete
    ⟨cliqueToVertexCoverKarpReduction⟩
    vertexCoverInNP

end VertexCover
end Karp21
end ComplexityReduction
