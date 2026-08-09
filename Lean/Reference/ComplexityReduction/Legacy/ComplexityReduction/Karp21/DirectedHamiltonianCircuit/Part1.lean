/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSet
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
P15d graph target: Vertex Cover to Directed Hamiltonian Circuit.

For the current raw directed-Hamiltonian schema, the edge condition depends on
the set of listed vertices rather than cyclic order.  The reduction therefore
uses the same bounded vertex-subset witness list as the feedback-node-set route
and maps nonempty source witness sets to a one-vertex loop instance.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-- All bounded vertex lists of length `n`, represented by functions `Fin n -> Fin n`. -/
noncomputable def vertexListCandidates (n : Nat) : List (List Nat) := by
  classical
  exact (Finset.univ : Finset (Fin n → Fin n)).toList.map fun f =>
    List.ofFn fun i : Fin n => (f i).val

theorem mem_vertexListCandidates_of_length_bounds {n : Nat} {cycle : List Nat}
    (hLen : cycle.length = n) (hBounds : ∀ v ∈ cycle, v < n) :
    cycle ∈ vertexListCandidates n := by
  classical
  subst n
  let f : Fin cycle.length → Fin cycle.length := fun i =>
    ⟨cycle.get i, hBounds (cycle.get i) (List.get_mem cycle i)⟩
  have hList : (List.ofFn fun i : Fin cycle.length => (f i).val) = cycle := by
    simp [f]
  exact List.mem_map.mpr ⟨f, by simp, hList⟩

theorem mem_vertexListCandidates_length {n : Nat} {cycle : List Nat}
    (h : cycle ∈ vertexListCandidates n) :
    cycle.length = n := by
  classical
  rcases List.mem_map.mp h with ⟨f, _hf, rfl⟩
  simp

theorem mem_vertexListCandidates_bounds {n : Nat} {cycle : List Nat}
    (h : cycle ∈ vertexListCandidates n) :
    ∀ v ∈ cycle, v < n := by
  classical
  rcases List.mem_map.mp h with ⟨f, _hf, rfl⟩
  intro v hv
  simp at hv
  rcases hv with ⟨i, rfl⟩
  exact (f i).isLt

theorem orderedDirectedHamiltonianCycle_selected_of_cycle {g : GraphInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle g cycle) :
    DirectedHamiltonianCycle g cycle :=
  hCycle.toSetLike

theorem orderedDirectedCycleSteps_of_isChain_closing {g : GraphInput} {cycle : List Nat}
    (hChain : cycle.IsChain fun a b => HasDirectedEdge g a b)
    (hClosing : ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasDirectedEdge g x y) :
    OrderedDirectedCycleSteps g cycle := by
  intro i
  by_cases hSucc : i.val + 1 < cycle.length
  · have hRel := hChain.getElem i.val hSucc
    simpa [cyclicSuccIndex, Nat.mod_eq_of_lt hSucc] using hRel
  · have hLenPos : 0 < cycle.length := by omega
    have hLastLt : cycle.length - 1 < cycle.length := by omega
    have hiVal : i.val = cycle.length - 1 := by omega
    have hiEq : i = ⟨cycle.length - 1, hLastLt⟩ := by
      ext
      exact hiVal
    subst i
    have hne : cycle ≠ [] := List.ne_nil_of_length_pos hLenPos
    have hx :
        cycle.get ⟨cycle.length - 1, hLastLt⟩ ∈ cycle.getLast? := by
      rw [List.get_length_sub_one hLastLt, List.getLast?_eq_getLast_of_ne_nil hne]
      simp
    have hSuccIndex :
        cyclicSuccIndex (cycle := cycle) ⟨cycle.length - 1, hLastLt⟩ = ⟨0, hLenPos⟩ := by
      ext
      simp [cyclicSuccIndex]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLenPos)]
      exact Nat.mod_self cycle.length
    have hy :
        cycle.get (cyclicSuccIndex (cycle := cycle) ⟨cycle.length - 1, hLastLt⟩) ∈
          cycle.head? := by
      rw [hSuccIndex, List.head?_eq_some_head hne]
      simp [List.head_eq_getElem_zero hne]
    exact hClosing _ hx _ hy

/-- Canonical bounded ordered directed-Hamiltonian witnesses for an input. -/
noncomputable def orderedDirectedHamiltonianCircuitWitnesses
    (I : DirectedHamiltonianCircuitInput) : List (List Nat) := by
  classical
  exact (vertexListCandidates I.graph.vertices).filter fun cycle =>
    decide (I.graph.directed = true ∧ OrderedDirectedHamiltonianCycle I.graph cycle)

theorem mem_orderedDirectedHamiltonianCircuitWitnesses_iff
    (I : DirectedHamiltonianCircuitInput) (cycle : List Nat) :
    cycle ∈ orderedDirectedHamiltonianCircuitWitnesses I ↔
      cycle ∈ vertexListCandidates I.graph.vertices ∧
        I.graph.directed = true ∧ OrderedDirectedHamiltonianCycle I.graph cycle := by
  classical
  simp [orderedDirectedHamiltonianCircuitWitnesses]

theorem orderedDirectedHamiltonianCircuit_iff_witnesses_pos
    (I : DirectedHamiltonianCircuitInput) :
    OrderedDirectedHamiltonianCircuit I ↔
      0 < (orderedDirectedHamiltonianCircuitWitnesses I).length := by
  constructor
  · rintro ⟨hDirected, cycle, hCycle⟩
    rcases hCycle with ⟨hLen, hNodup, hBounds, hSteps⟩
    have hMemCandidates : cycle ∈ vertexListCandidates I.graph.vertices :=
      mem_vertexListCandidates_of_length_bounds hLen hBounds
    have hMem : cycle ∈ orderedDirectedHamiltonianCircuitWitnesses I :=
      (mem_orderedDirectedHamiltonianCircuitWitnesses_iff I cycle).2
        ⟨hMemCandidates, hDirected, hLen, hNodup, hBounds, hSteps⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : orderedDirectedHamiltonianCircuitWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons cycle rest =>
        have hMem : cycle ∈ orderedDirectedHamiltonianCircuitWitnesses I := by
          simp [hList]
        rcases (mem_orderedDirectedHamiltonianCircuitWitnesses_iff I cycle).1 hMem with
          ⟨_hCandidate, hDirected, hCycle⟩
        exact ⟨hDirected, cycle, hCycle⟩

theorem directedHamiltonianCycle_selected_of_cycle {g : GraphInput} {cycle : List Nat}
    (hCycle : DirectedHamiltonianCycle g cycle) :
    DirectedHamiltonianCycle g
      (FeedbackNodeSet.selectedVertices g.vertices
        (FeedbackNodeSet.selectOfList g.vertices cycle)) := by
  rcases hCycle with ⟨hLen, hNodup, hBounds, hStep⟩
  have hSelectedLen :
      (FeedbackNodeSet.selectedVertices g.vertices
        (FeedbackNodeSet.selectOfList g.vertices cycle)).length = g.vertices := by
    have hEq :=
      FeedbackNodeSet.selectedVertices_selectOfList_length_eq hNodup hBounds
    omega
  refine ⟨hSelectedLen, ?_, ?_, ?_⟩
  · exact FeedbackNodeSet.selectedVertices_nodup g.vertices
      (FeedbackNodeSet.selectOfList g.vertices cycle)
  · exact FeedbackNodeSet.selectedVertices_withinBounds g
      (FeedbackNodeSet.selectOfList g.vertices cycle)
  · intro u hu
    have huCycle :=
      (FeedbackNodeSet.mem_selectedVertices_selectOfList_iff hBounds u).1 hu
    rcases hStep u huCycle with ⟨v, hvCycle, hEdge⟩
    exact
      ⟨v, (FeedbackNodeSet.mem_selectedVertices_selectOfList_iff hBounds v).2 hvCycle,
        hEdge⟩

/-- Canonical bounded directed-Hamiltonian witnesses for an input. -/
noncomputable def directedHamiltonianCircuitWitnesses
    (I : DirectedHamiltonianCircuitInput) : List (List Nat) := by
  exact orderedDirectedHamiltonianCircuitWitnesses I

theorem mem_directedHamiltonianCircuitWitnesses_iff
    (I : DirectedHamiltonianCircuitInput) (cycle : List Nat) :
    cycle ∈ directedHamiltonianCircuitWitnesses I ↔
      cycle ∈ vertexListCandidates I.graph.vertices ∧
        I.graph.directed = true ∧ OrderedDirectedHamiltonianCycle I.graph cycle := by
  simpa [directedHamiltonianCircuitWitnesses] using
    mem_orderedDirectedHamiltonianCircuitWitnesses_iff I cycle

theorem directedHamiltonianCircuit_iff_witnesses_pos
    (I : DirectedHamiltonianCircuitInput) :
    DirectedHamiltonianCircuit I ↔
      0 < (directedHamiltonianCircuitWitnesses I).length := by
  simpa [DirectedHamiltonianCircuit, OrderedDirectedHamiltonianCircuit,
    directedHamiltonianCircuitWitnesses] using
    orderedDirectedHamiltonianCircuit_iff_witnesses_pos I

/-- A bounded source vertex is incident with source edge index `i`. -/
def SourceIncidentAt (I : VertexCoverInput) (u i : Nat) : Prop :=
  i < I.graph.edges.length ∧
    u < I.graph.vertices ∧
    ((I.graph.edges.getD i (0, 0)).1 = u ∨
      (I.graph.edges.getD i (0, 0)).2 = u)

/--
Karp's DHC construction is indexed by source edge incidences.  We keep only
bounded source vertices, matching the local `VertexCover` witness semantics.
-/
noncomputable def sourceIncidences (I : VertexCoverInput) : List (Nat × Nat) := by
  classical
  exact ((List.range I.graph.vertices).product (List.range I.graph.edges.length)).filter
    fun ui => decide (SourceIncidentAt I ui.1 ui.2)

theorem mem_sourceIncidences_iff (I : VertexCoverInput) (ui : Nat × Nat) :
    ui ∈ sourceIncidences I ↔ SourceIncidentAt I ui.1 ui.2 := by
  cases ui with
  | mk u i =>
      simp [sourceIncidences, SourceIncidentAt, and_assoc, and_left_comm]

theorem sourceIncidences_nodup (I : VertexCoverInput) :
    (sourceIncidences I).Nodup := by
  classical
  simpa [sourceIncidences] using
    ((List.nodup_range (n := I.graph.vertices)).product
      (List.nodup_range (n := I.graph.edges.length))).filter
        (fun ui => decide (SourceIncidentAt I ui.1 ui.2))

theorem sourceIncidence_left_of_edge_index
    {I : VertexCoverInput} {i : Nat} (hi : i < I.graph.edges.length)
    (hLeft : I.graph.edges[i].1 < I.graph.vertices) :
    (I.graph.edges[i].1, i) ∈ sourceIncidences I := by
  exact (mem_sourceIncidences_iff I (I.graph.edges[i].1, i)).2 (by
    simp [SourceIncidentAt, hi, hLeft])

theorem sourceIncidence_right_of_edge_index
    {I : VertexCoverInput} {i : Nat} (hi : i < I.graph.edges.length)
    (hRight : I.graph.edges[i].2 < I.graph.vertices) :
    (I.graph.edges[i].2, i) ∈ sourceIncidences I := by
  exact (mem_sourceIncidences_iff I (I.graph.edges[i].2, i)).2 (by
    simp [SourceIncidentAt, hi, hRight])

theorem sourceIncidence_endpoint_eq_left_or_right
    {I : VertexCoverInput} {u i : Nat} (hi : i < I.graph.edges.length)
    (hInc : (u, i) ∈ sourceIncidences I) :
    u = I.graph.edges[i].1 ∨ u = I.graph.edges[i].2 := by
  have hSource : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hInc
  rcases hSource.2.2 with hLeft | hRight
  · left
    simpa [List.getD_getElem?, hi] using hLeft.symm
  · right
    simpa [List.getD_getElem?, hi] using hRight.symm

/-- Selector vertex `a_slot` in the textbook DHC gadget. -/
def textbookSelectorVertex (slot : Nat) : Nat :=
  slot

/-- Incidence vertex `<u,i,bit>` in the textbook DHC gadget. -/
noncomputable def textbookIncidenceVertex
    (I : VertexCoverInput) (u i bit : Nat) : Nat :=
  I.k + 2 * (sourceIncidences I).idxOf (u, i) + bit

/-- Total vertex count for the selector/incidence vocabulary. -/
noncomputable def textbookVertexCount (I : VertexCoverInput) : Nat :=
  I.k + 2 * (sourceIncidences I).length

theorem textbookSelectorVertex_lt {I : VertexCoverInput} {slot : Nat} (hslot : slot < I.k) :
    textbookSelectorVertex slot < textbookVertexCount I := by
  simp [textbookSelectorVertex, textbookVertexCount]
  omega

theorem textbookIncidenceVertex_lt {I : VertexCoverInput} {u i bit : Nat}
    (hInc : (u, i) ∈ sourceIncidences I) (hbit : bit < 2) :
    textbookIncidenceVertex I u i bit < textbookVertexCount I := by
  have hIdx : (sourceIncidences I).idxOf (u, i) < (sourceIncidences I).length :=
    List.idxOf_lt_length_iff.mpr hInc
  simp [textbookIncidenceVertex, textbookVertexCount]
  omega

theorem textbookIncidenceVertex_inj
    {I : VertexCoverInput} {u v i j bit bit' : Nat}
    (hui : (u, i) ∈ sourceIncidences I) (_hvj : (v, j) ∈ sourceIncidences I)
    (hbit : bit < 2) (hbit' : bit' < 2)
    (hEq : textbookIncidenceVertex I u i bit = textbookIncidenceVertex I v j bit') :
    (u, i) = (v, j) ∧ bit = bit' := by
  have hIdx :
      (sourceIncidences I).idxOf (u, i) = (sourceIncidences I).idxOf (v, j) := by
    simp [textbookIncidenceVertex] at hEq
    omega
  have hBit : bit = bit' := by
    simp [textbookIncidenceVertex] at hEq
    omega
  exact ⟨(List.idxOf_inj hui).1 hIdx, hBit⟩

theorem textbookIncidenceVertex_ne_of_incidence_ne
    {I : VertexCoverInput} {u v i j bit bit' : Nat}
    (hui : (u, i) ∈ sourceIncidences I) (hvj : (v, j) ∈ sourceIncidences I)
    (hbit : bit < 2) (hbit' : bit' < 2)
    (hIncNe : (u, i) ≠ (v, j)) :
    textbookIncidenceVertex I u i bit ≠ textbookIncidenceVertex I v j bit' := by
  intro hEq
  exact hIncNe (textbookIncidenceVertex_inj hui hvj hbit hbit' hEq).1

theorem textbookIncidenceVertex_ne_of_bit_ne
    {I : VertexCoverInput} {u v i j bit bit' : Nat}
    (hui : (u, i) ∈ sourceIncidences I) (hvj : (v, j) ∈ sourceIncidences I)
    (hbit : bit < 2) (hbit' : bit' < 2) (hBitNe : bit ≠ bit') :
    textbookIncidenceVertex I u i bit ≠ textbookIncidenceVertex I v j bit' := by
  intro hEq
  exact hBitNe (textbookIncidenceVertex_inj hui hvj hbit hbit' hEq).2

theorem textbookSelectorVertex_ne_textbookIncidenceVertex
    {I : VertexCoverInput} {slot u i bit : Nat} (hslot : slot < I.k) :
    textbookSelectorVertex slot ≠ textbookIncidenceVertex I u i bit := by
  simp [textbookSelectorVertex, textbookIncidenceVertex]
  omega

/-- The selector following `slot`, with wrap-around when `I.k > 0`. -/
def textbookNextSelector (I : VertexCoverInput) (slot : Nat) : Nat :=
  if I.k = 0 then 0 else (slot + 1) % I.k

theorem textbookNextSelector_lt {I : VertexCoverInput} {slot : Nat} (hslot : slot < I.k) :
    textbookNextSelector I slot < I.k := by
  unfold textbookNextSelector
  by_cases hk : I.k = 0
  · simp [hk] at hslot
  · simp [hk, Nat.mod_lt _ (Nat.pos_of_ne_zero hk)]

theorem textbookNextSelector_last_of_pos {I : VertexCoverInput} (hk : 0 < I.k) :
    textbookNextSelector I (I.k - 1) = 0 := by
  unfold textbookNextSelector
  have hkNe : I.k ≠ 0 := Nat.ne_of_gt hk
  simp [hkNe]
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hk)]
  exact Nat.mod_self I.k

/-- Source incidences for the same source vertex with no incident source edge between them. -/
def ConsecutiveIncident (I : VertexCoverInput) (u i j : Nat) : Prop :=
  SourceIncidentAt I u i ∧
    SourceIncidentAt I u j ∧
    i < j ∧
    ∀ h, i < h → h < j → ¬ SourceIncidentAt I u h

/-- The first incident edge index of a bounded source vertex. -/
def FirstIncident (I : VertexCoverInput) (u i : Nat) : Prop :=
  SourceIncidentAt I u i ∧ ∀ h, h < i → ¬ SourceIncidentAt I u h

/-- The last incident edge index of a bounded source vertex. -/
def LastIncident (I : VertexCoverInput) (u i : Nat) : Prop :=
  SourceIncidentAt I u i ∧
    ∀ h, i < h → h < I.graph.edges.length → ¬ SourceIncidentAt I u h

theorem sourceIncidence_mem_of_first {I : VertexCoverInput} {u i : Nat}
    (h : FirstIncident I u i) :
    (u, i) ∈ sourceIncidences I :=
  (mem_sourceIncidences_iff I (u, i)).2 h.1

theorem sourceIncidence_mem_of_last {I : VertexCoverInput} {u i : Nat}
    (h : LastIncident I u i) :
    (u, i) ∈ sourceIncidences I :=
  (mem_sourceIncidences_iff I (u, i)).2 h.1

theorem sourceIncidence_mem_left_of_consecutive {I : VertexCoverInput} {u i j : Nat}
    (h : ConsecutiveIncident I u i j) :
    (u, i) ∈ sourceIncidences I :=
  (mem_sourceIncidences_iff I (u, i)).2 h.1

theorem sourceIncidence_mem_right_of_consecutive {I : VertexCoverInput} {u i j : Nat}
    (h : ConsecutiveIncident I u i j) :
    (u, j) ∈ sourceIncidences I :=
  (mem_sourceIncidences_iff I (u, j)).2 h.2.1

theorem firstIncident_unique {I : VertexCoverInput} {u i j : Nat}
    (hi : FirstIncident I u i) (hj : FirstIncident I u j) :
    i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hji
  · exact (hj.2 i hij hi.1).elim
  · exact hij
  · exact (hi.2 j hji hj.1).elim

theorem lastIncident_unique {I : VertexCoverInput} {u i j : Nat}
    (hi : LastIncident I u i) (hj : LastIncident I u j) :
    i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hji
  · exact (hi.2 j hij hj.1.1 hj.1).elim
  · exact hij
  · exact (hj.2 i hji hi.1.1 hi.1).elim

theorem consecutiveIncident_unique_right {I : VertexCoverInput} {u i j j' : Nat}
    (hj : ConsecutiveIncident I u i j) (hj' : ConsecutiveIncident I u i j') :
    j = j' := by
  rcases Nat.lt_trichotomy j j' with hjlt | heq | hj'lt
  · exact (hj'.2.2.2 j hj.2.2.1 hjlt hj.2.1).elim
  · exact heq
  · exact (hj.2.2.2 j' hj'.2.2.1 hj'lt hj'.2.1).elim

theorem consecutiveIncident_unique_left {I : VertexCoverInput} {u i i' j : Nat}
    (hi : ConsecutiveIncident I u i j) (hi' : ConsecutiveIncident I u i' j) :
    i = i' := by
  rcases Nat.lt_trichotomy i i' with hilt | heq | hi'lt
  · exact (hi.2.2.2 i' hilt hi'.2.2.1 hi'.1).elim
  · exact heq
  · exact (hi'.2.2.2 i hi'lt hi.2.2.1 hi.1).elim

/-- All source incidences belonging to a fixed bounded source vertex. -/
noncomputable def incidencesOfVertex (I : VertexCoverInput) (u : Nat) : List (Nat × Nat) := by
  classical
  exact ((List.range I.graph.edges.length).filter fun i =>
    decide (SourceIncidentAt I u i)).map fun i => (u, i)

theorem mem_incidencesOfVertex_iff (I : VertexCoverInput) (u : Nat) (ui : Nat × Nat) :
    ui ∈ incidencesOfVertex I u ↔ ui ∈ sourceIncidences I ∧ ui.1 = u := by
  classical
  cases ui with
  | mk v i =>
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨j, hj, hEq⟩
        have hjSource : SourceIncidentAt I u j := by
          exact of_decide_eq_true ((List.mem_filter.mp hj).2)
        simp at hEq
        rcases hEq with ⟨rfl, rfl⟩
        exact ⟨(mem_sourceIncidences_iff I (u, j)).2 hjSource, rfl⟩
      · intro h
        rcases h with ⟨hSource, hvu⟩
        have hSource' : SourceIncidentAt I v i := (mem_sourceIncidences_iff I (v, i)).1 hSource
        have hvu' : v = u := by simpa using hvu
        subst v
        exact List.mem_map.mpr
          ⟨i,
            List.mem_filter.mpr ⟨List.mem_range.mpr hSource'.1,
              by simpa using hSource'⟩,
            rfl⟩

theorem sourceIncidence_mem_incidencesOfVertex
    {I : VertexCoverInput} {u i : Nat} (hInc : (u, i) ∈ sourceIncidences I) :
    (u, i) ∈ incidencesOfVertex I u :=
  (mem_incidencesOfVertex_iff I u (u, i)).2 ⟨hInc, rfl⟩

theorem incidencesOfVertex_nodup (I : VertexCoverInput) (u : Nat) :
    (incidencesOfVertex I u).Nodup := by
  classical
  rw [incidencesOfVertex]
  exact ((List.nodup_range (n := I.graph.edges.length)).filter
    (fun i => decide (SourceIncidentAt I u i))).map
      (by
        intro i j hEq
        simpa using congrArg Prod.snd hEq)

theorem incidencesOfVertex_pairwise_edge_lt (I : VertexCoverInput) (u : Nat) :
    (incidencesOfVertex I u).Pairwise fun ui uj => ui.2 < uj.2 := by
  classical
  rw [incidencesOfVertex]
  have hPair :
      (((List.range I.graph.edges.length).filter fun i =>
        decide (SourceIncidentAt I u i))).Pairwise (fun i j => i < j) := by
    exact (List.pairwise_lt_range (n := I.graph.edges.length)).filter _
  simpa [List.pairwise_map] using hPair

/-- The two local gadget vertices attached to one source incidence. -/
noncomputable def incidencePairVertices
    (I : VertexCoverInput) (ui : Nat × Nat) : List Nat :=
  [textbookIncidenceVertex I ui.1 ui.2 0,
    textbookIncidenceVertex I ui.1 ui.2 1]

/-- The straight incidence track of a source vertex, before same-edge detours are inserted. -/
noncomputable def plainVertexTrack (I : VertexCoverInput) (u : Nat) : List Nat :=
  ((incidencesOfVertex I u).map fun ui => incidencePairVertices I ui).flatten

/-- Cover-side owner candidate for source edge `i`, chosen from the cover list if present. -/
noncomputable def edgeOwner? (I : VertexCoverInput) (cover : List Nat) (i : Nat) : Option Nat := by
  classical
  exact cover.find? fun u => decide (SourceIncidentAt I u i)

theorem edgeOwner?_eq_some_mem {I : VertexCoverInput} {cover : List Nat}
    {i owner : Nat} (h : edgeOwner? I cover i = some owner) :
    owner ∈ cover := by
  classical
  simpa [edgeOwner?] using
    (List.mem_of_find?_eq_some (p := fun u => decide (SourceIncidentAt I u i)) h)

theorem edgeOwner?_eq_some_incident {I : VertexCoverInput} {cover : List Nat}
    {i owner : Nat} (h : edgeOwner? I cover i = some owner) :
    SourceIncidentAt I owner i := by
  classical
  simpa [edgeOwner?] using
    (List.find?_some (p := fun u => decide (SourceIncidentAt I u i)) h)

theorem edgeOwner?_isSome_iff (I : VertexCoverInput) (cover : List Nat) (i : Nat) :
    (edgeOwner? I cover i).isSome ↔ ∃ u, u ∈ cover ∧ SourceIncidentAt I u i := by
  classical
  simp [edgeOwner?, List.find?_isSome]

theorem edgeOwner?_isSome_of_coversEdgeIndex {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) (hCovers : CoversEdges I.graph cover)
    {i : Nat} (hi : i < I.graph.edges.length) :
    (edgeOwner? I cover i).isSome := by
  classical
  have hCovered := hCovers I.graph.edges[i] (List.get_mem I.graph.edges ⟨i, hi⟩)
  refine (edgeOwner?_isSome_iff I cover i).2 ?_
  rcases hCovered with hLeft | hRight
  · refine ⟨I.graph.edges[i].1, hLeft, ?_⟩
    simp [SourceIncidentAt, hi, hBounds _ hLeft]
  · refine ⟨I.graph.edges[i].2, hRight, ?_⟩
    simp [SourceIncidentAt, hi, hBounds _ hRight]

theorem exists_selected_other_incident_of_unselected_incidence
    {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) (hCovers : CoversEdges I.graph cover)
    {u i : Nat} (hInc : SourceIncidentAt I u i) (huNot : u ∉ cover) :
    ∃ v : Nat, v ∈ cover ∧ SourceIncidentAt I v i ∧ v ≠ u := by
  classical
  rcases hInc with ⟨hi, _huBound, hEndpoint⟩
  have hCovered := hCovers I.graph.edges[i] (List.get_mem I.graph.edges ⟨i, hi⟩)
  rcases hEndpoint with hLeft | hRight
  · have hLeft' : I.graph.edges[i].1 = u := by
      simpa [List.getD_getElem?, hi] using hLeft
    rcases hCovered with hCoverLeft | hCoverRight
    · exact (huNot (hLeft' ▸ hCoverLeft)).elim
    · refine ⟨I.graph.edges[i].2, hCoverRight, ?_, ?_⟩
      · simp [SourceIncidentAt, hi, hBounds _ hCoverRight]
      · intro hEq
        exact huNot (hEq ▸ hCoverRight)
  · have hRight' : I.graph.edges[i].2 = u := by
      simpa [List.getD_getElem?, hi] using hRight
    rcases hCovered with hCoverLeft | hCoverRight
    · refine ⟨I.graph.edges[i].1, hCoverLeft, ?_, ?_⟩
      · simp [SourceIncidentAt, hi, hBounds _ hCoverLeft]
      · intro hEq
        exact huNot (hEq ▸ hCoverLeft)
    · exact (huNot (hRight' ▸ hCoverRight)).elim

theorem sourceIncidentAt_other_endpoint_unique
    {I : VertexCoverInput} {u v w i : Nat}
    (hu : SourceIncidentAt I u i) (hv : SourceIncidentAt I v i)
    (hw : SourceIncidentAt I w i) (huv : u ≠ v) (hwv : w ≠ v) :
    w = u := by
  rcases hu with ⟨_hiu, _hub, huEndpoint⟩
  rcases hv with ⟨_hiv, _hvb, hvEndpoint⟩
  rcases hw with ⟨_hiw, _hwb, hwEndpoint⟩
  rcases huEndpoint with huLeft | huRight <;>
    rcases hvEndpoint with hvLeft | hvRight <;>
    rcases hwEndpoint with hwLeft | hwRight <;>
    omega

theorem selected_other_sourceIncidence_of_unselected_incidence
    {I : VertexCoverInput} {i v : Nat} (hv : SourceIncidentAt I v i) :
    (v, i) ∈ sourceIncidences I :=
  (mem_sourceIncidences_iff I (v, i)).2 hv

/-- A cover witness padded to exactly `k` selector slots. -/
def coverSlots (I : VertexCoverInput) (cover : List Nat) : List (Option Nat) :=
  cover.map some ++ List.replicate (I.k - cover.length) none

theorem coverSlots_length {I : VertexCoverInput} {cover : List Nat}
    (hLen : cover.length ≤ I.k) :
    (coverSlots I cover).length = I.k := by
  simp [coverSlots]
  omega

theorem coverSlots_some_mem_cover {I : VertexCoverInput} {cover : List Nat} {u : Nat}
    (h : some u ∈ coverSlots I cover) :
    u ∈ cover := by
  simpa [coverSlots] using h

/-- Selector-slot choice, defaulting to `none` outside the padded cover list. -/
def coverSlotChoice (I : VertexCoverInput) (cover : List Nat) (slot : Nat) : Option Nat :=
  (coverSlots I cover).getD slot none

theorem coverSlotChoice_eq_some_mem
    {I : VertexCoverInput} {cover : List Nat} {slot u : Nat}
    (h : coverSlotChoice I cover slot = some u) :
    u ∈ cover := by
  classical
  unfold coverSlotChoice at h
  by_cases hslot : slot < (coverSlots I cover).length
  · have hGet :
        (coverSlots I cover).getD slot none = (coverSlots I cover)[slot] := by
      exact List.getD_eq_getElem (l := coverSlots I cover) (d := none) (n := slot) hslot
    have hMem : (coverSlots I cover).getD slot none ∈ coverSlots I cover := by
      rw [hGet]
      exact List.get_mem (coverSlots I cover) ⟨slot, hslot⟩
    have hSomeMem : some u ∈ coverSlots I cover := by
      rw [h] at hMem
      exact hMem
    exact coverSlots_some_mem_cover hSomeMem
  · have hDefault : (coverSlots I cover).getD slot none = none := by
      exact List.getD_eq_default (l := coverSlots I cover) (d := none) (n := slot)
        (Nat.not_lt.mp hslot)
    rw [hDefault] at h
    simp at h

theorem coverSlotChoice_eq_some_of_mem
    {I : VertexCoverInput} {cover : List Nat} {u : Nat}
    (_hLen : cover.length ≤ I.k) (hu : u ∈ cover) :
    coverSlotChoice I cover (cover.idxOf u) = some u := by
  classical
  have hIdx : cover.idxOf u < cover.length := List.idxOf_lt_length_iff.mpr hu
  unfold coverSlotChoice coverSlots
  rw [List.getD_append]
  · have hIdxMap : cover.idxOf u < (cover.map some).length := by
      simpa using hIdx
    rw [List.getD_eq_getElem (l := cover.map some) (d := none)
      (n := cover.idxOf u) hIdxMap]
    simp
  · simpa using hIdx

theorem coverSlotChoice_eq_some_get
    {I : VertexCoverInput} {cover : List Nat} {slot u : Nat}
    (h : coverSlotChoice I cover slot = some u) :
    ∃ hslot : slot < cover.length, cover[slot] = u := by
  classical
  unfold coverSlotChoice coverSlots at h
  by_cases hslot : slot < cover.length
  · have hMapSlot : slot < (cover.map some).length := by
      simpa using hslot
    rw [List.getD_append (l := cover.map some)
      (l' := List.replicate (I.k - cover.length) none) (d := none) (n := slot)
      hMapSlot] at h
    rw [List.getD_eq_getElem (l := cover.map some) (d := none) (n := slot) hMapSlot] at h
    simp at h
    exact ⟨hslot, h⟩
  · have hMapLe : (cover.map some).length ≤ slot := by
      simpa using Nat.le_of_not_gt hslot
    rw [List.getD_append_right (l := cover.map some)
      (l' := List.replicate (I.k - cover.length) none) (d := none) (n := slot)
      hMapLe] at h
    simp at h

theorem coverSlotChoice_eq_some_inj_of_nodup
    {I : VertexCoverInput} {cover : List Nat} {slot₁ slot₂ u v : Nat}
    (hNodup : cover.Nodup)
    (h₁ : coverSlotChoice I cover slot₁ = some u)
    (h₂ : coverSlotChoice I cover slot₂ = some v)
    (huv : u = v) :
    slot₁ = slot₂ := by
  rcases coverSlotChoice_eq_some_get h₁ with ⟨hslot₁, hget₁⟩
  rcases coverSlotChoice_eq_some_get h₂ with ⟨hslot₂, hget₂⟩
  have hGetEq :
      cover.get ⟨slot₁, hslot₁⟩ = cover.get ⟨slot₂, hslot₂⟩ := by
    simp [hget₁, hget₂, huv]
  have hFin :
      (⟨slot₁, hslot₁⟩ : Fin cover.length) = ⟨slot₂, hslot₂⟩ :=
    (hNodup.get_inj_iff).1 hGetEq
  exact congrArg Fin.val hFin

theorem exists_coverSlotChoice_eq_some_of_mem
    {I : VertexCoverInput} {cover : List Nat} {u : Nat}
    (hLen : cover.length ≤ I.k) (hu : u ∈ cover) :
    ∃ slot, slot < I.k ∧ coverSlotChoice I cover slot = some u := by
  classical
  have hIdx : cover.idxOf u < cover.length := List.idxOf_lt_length_iff.mpr hu
  exact ⟨cover.idxOf u, lt_of_lt_of_le hIdx hLen,
    coverSlotChoice_eq_some_of_mem hLen hu⟩

/-- Straight selector-slot skeleton before edge-detours are inserted. -/
noncomputable def straightSlotSkeleton
    (I : VertexCoverInput) (slot : Nat) (choice : Option Nat) : List Nat :=
  [textbookSelectorVertex slot] ++
    match choice with
    | none => []
    | some u => plainVertexTrack I u

/-- Straight cover traversal skeleton, used as the base for the forward witness. -/
noncomputable def straightCoverSkeleton (I : VertexCoverInput) (cover : List Nat) : List Nat :=
  (((List.range I.k).zip (coverSlots I cover)).map fun pair =>
    straightSlotSkeleton I pair.1 pair.2).flatten

/-- Forced local arcs `<u,i,0> -> <u,i,1>` for every source incidence. -/
noncomputable def textbookIncidenceArcs (I : VertexCoverInput) : List (Nat × Nat) :=
  (sourceIncidences I).map fun ui =>
    (textbookIncidenceVertex I ui.1 ui.2 0,
      textbookIncidenceVertex I ui.1 ui.2 1)

theorem mem_textbookIncidenceArcs {I : VertexCoverInput} {u i : Nat}
    (hInc : (u, i) ∈ sourceIncidences I) :
    (textbookIncidenceVertex I u i 0, textbookIncidenceVertex I u i 1) ∈
      textbookIncidenceArcs I := by
  exact List.mem_map.mpr ⟨(u, i), hInc, rfl⟩

/-- Same-edge cross arcs between the two endpoint-incidence tracks. -/
noncomputable def textbookCrossArcs (I : VertexCoverInput) : List (Nat × Nat) := by
  classical
  exact ((((sourceIncidences I).product (sourceIncidences I)).filter fun pair =>
    decide (pair.1.2 = pair.2.2 ∧ pair.1.1 ≠ pair.2.1)).map fun pair =>
      [ (textbookIncidenceVertex I pair.1.1 pair.1.2 0,
          textbookIncidenceVertex I pair.2.1 pair.2.2 0)
      , (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
          textbookIncidenceVertex I pair.2.1 pair.2.2 1)
      ]).flatten

theorem mem_textbookCrossArcs_bit0 {I : VertexCoverInput} {u v i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) (hv : (v, i) ∈ sourceIncidences I)
    (huv : u ≠ v) :
    (textbookIncidenceVertex I u i 0, textbookIncidenceVertex I v i 0) ∈
      textbookCrossArcs I := by
  classical
  simp [textbookCrossArcs]
  refine ⟨u, i, v, ?_, ?_⟩
  · exact ⟨⟨hu, hv⟩, huv⟩
  · left
    exact ⟨rfl, rfl⟩

theorem mem_textbookCrossArcs_bit1 {I : VertexCoverInput} {u v i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) (hv : (v, i) ∈ sourceIncidences I)
    (huv : u ≠ v) :
    (textbookIncidenceVertex I u i 1, textbookIncidenceVertex I v i 1) ∈
      textbookCrossArcs I := by
  classical
  simp [textbookCrossArcs]
  refine ⟨u, i, v, ?_, ?_⟩
  · exact ⟨⟨hu, hv⟩, huv⟩
  · right
    exact ⟨rfl, rfl⟩

/-- Chain arcs joining consecutive incidences of the same source vertex. -/
noncomputable def textbookChainArcs (I : VertexCoverInput) : List (Nat × Nat) := by
  classical
  exact (((sourceIncidences I).product (sourceIncidences I)).filter fun pair =>
    decide (pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map
    fun pair =>
      (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
        textbookIncidenceVertex I pair.2.1 pair.2.2 0)

theorem mem_textbookChainArcs {I : VertexCoverInput} {u i j : Nat}
    (hConsec : ConsecutiveIncident I u i j) :
    (textbookIncidenceVertex I u i 1, textbookIncidenceVertex I u j 0) ∈
      textbookChainArcs I := by
  classical
  have hi : (u, i) ∈ sourceIncidences I := sourceIncidence_mem_left_of_consecutive hConsec
  have hj : (u, j) ∈ sourceIncidences I := sourceIncidence_mem_right_of_consecutive hConsec
  simp [textbookChainArcs]
  refine ⟨u, i, j, ?_, ?_⟩
  · exact ⟨⟨hi, hj⟩, hConsec⟩
  · exact ⟨rfl, rfl⟩

/-- The first element of a consecutive-pair list member belongs to the source list. -/
theorem left_mem_of_mem_consecutivePairs {α : Type*} :
    ∀ {l : List α} {a b : α}, (a, b) ∈ l.consecutivePairs → a ∈ l
  | [], _, _, h => by
      simp [List.consecutivePairs] at h
  | [_x], _, _, h => by
      simp [List.consecutivePairs] at h
  | x :: y :: rest, a, b, h => by
      simp [List.consecutivePairs] at h ⊢
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr (by simpa using left_mem_of_mem_consecutivePairs h)

/-- The second element of a consecutive-pair list member belongs to the source list. -/
theorem right_mem_of_mem_consecutivePairs {α : Type*} :
    ∀ {l : List α} {a b : α}, (a, b) ∈ l.consecutivePairs → b ∈ l
  | [], _, _, h => by
      simp [List.consecutivePairs] at h
  | [_x], _, _, h => by
      simp [List.consecutivePairs] at h
  | x :: y :: rest, a, b, h => by
      simp [List.consecutivePairs] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h.2)
      · exact Or.inr (by simpa using right_mem_of_mem_consecutivePairs h)

theorem rel_of_mem_consecutivePairs_of_pairwise {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} {p q : α}, l.Pairwise R → (p, q) ∈ l.consecutivePairs → R p q
  | [], _, _, _hPair, h => by
      simp [List.consecutivePairs] at h
  | [_x], _, _, _hPair, h => by
      simp [List.consecutivePairs] at h
  | x :: y :: rest, p, q, hPair, h => by
      cases hPair with
      | cons hHead hTail =>
          simp [List.consecutivePairs] at h
          rcases h with h | h
          · rcases h with ⟨rfl, rfl⟩
            exact hHead q (by simp)
          · exact rel_of_mem_consecutivePairs_of_pairwise hTail h

theorem edgeIndex_lt_of_mem_incidencesOfVertex_consecutivePairs
    {I : VertexCoverInput} {u : Nat} {ui uj : Nat × Nat}
    (hpair : (ui, uj) ∈ (incidencesOfVertex I u).consecutivePairs) :
    ui.2 < uj.2 :=
  rel_of_mem_consecutivePairs_of_pairwise
    (R := fun ui uj : Nat × Nat => ui.2 < uj.2)
    (incidencesOfVertex_pairwise_edge_lt I u) hpair

/-- Every adjacent pair of a list occurs in its `consecutivePairs` list. -/
theorem isChain_mem_consecutivePairs {α : Type*} (l : List α) :
    l.IsChain fun a b => (a, b) ∈ l.consecutivePairs := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp
      | cons y ys =>
          rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · simp [List.consecutivePairs]
          · exact ih.imp fun a b h => by
              right
              simpa [List.consecutivePairs] using h

/-- Chain arcs following the actual incidence-list adjacency for one source vertex. -/
noncomputable def textbookTrackChainArcsForVertex
    (I : VertexCoverInput) (u : Nat) : List (Nat × Nat) :=
  (incidencesOfVertex I u).consecutivePairs.map fun pair =>
    (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
      textbookIncidenceVertex I pair.2.1 pair.2.2 0)

/-- Chain arcs following actual incidence-list adjacency, for all bounded source vertices. -/
noncomputable def textbookTrackChainArcs (I : VertexCoverInput) : List (Nat × Nat) :=
  ((List.range I.graph.vertices).map fun u => textbookTrackChainArcsForVertex I u).flatten

theorem mem_textbookTrackChainArcsForVertex
    {I : VertexCoverInput} {u : Nat} {ui uj : Nat × Nat}
    (hpair : (ui, uj) ∈ (incidencesOfVertex I u).consecutivePairs) :
    (textbookIncidenceVertex I ui.1 ui.2 1,
      textbookIncidenceVertex I uj.1 uj.2 0) ∈ textbookTrackChainArcsForVertex I u := by
  exact List.mem_map.mpr ⟨(ui, uj), hpair, rfl⟩

theorem mem_textbookTrackChainArcs
    {I : VertexCoverInput} {u : Nat} (hu : u < I.graph.vertices) {ui uj : Nat × Nat}
    (hpair : (ui, uj) ∈ (incidencesOfVertex I u).consecutivePairs) :
    (textbookIncidenceVertex I ui.1 ui.2 1,
      textbookIncidenceVertex I uj.1 uj.2 0) ∈ textbookTrackChainArcs I := by
  exact List.mem_flatten.mpr
    ⟨textbookTrackChainArcsForVertex I u,
      List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩,
      mem_textbookTrackChainArcsForVertex hpair⟩

/-- Entry arcs to the first actual incidence-list vertex for each bounded source vertex. -/
noncomputable def textbookTrackEntryArcs (I : VertexCoverInput) : List (Nat × Nat) :=
  ((List.range I.k).product (List.range I.graph.vertices)).flatMap fun pair =>
    match (incidencesOfVertex I pair.2).head? with
    | none => []
    | some ui =>
        [(textbookSelectorVertex pair.1,
          textbookIncidenceVertex I ui.1 ui.2 0)]

/-- Exit arcs from the last actual incidence-list vertex for each bounded source vertex. -/
noncomputable def textbookTrackExitArcs (I : VertexCoverInput) : List (Nat × Nat) :=
  ((List.range I.k).product (List.range I.graph.vertices)).flatMap fun pair =>
    match (incidencesOfVertex I pair.2).getLast? with
    | none => []
    | some ui =>
        [(textbookIncidenceVertex I ui.1 ui.2 1,
          textbookSelectorVertex (textbookNextSelector I pair.1))]

theorem mem_of_head?_eq_some {α : Type*} {l : List α} {x : α}
    (h : l.head? = some x) :
    x ∈ l := by
  cases l with
  | nil =>
      simp at h
  | cons y ys =>
      simp at h
      subst x
      simp

theorem mem_of_getLast?_eq_some {α : Type*} {l : List α} {x : α}
    (h : l.getLast? = some x) :
    x ∈ l := by
  cases l with
  | nil =>
      simp at h
  | cons y ys =>
      have hx : x ∈ (y :: ys).getLast? := by simp [h]
      rcases List.mem_getLast?_eq_getLast hx with ⟨hne, rfl⟩
      exact List.getLast_mem hne

theorem mem_textbookTrackEntryArcs
    {I : VertexCoverInput} {slot u : Nat} {ui : Nat × Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices)
    (hHead : (incidencesOfVertex I u).head? = some ui) :
    (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0) ∈
      textbookTrackEntryArcs I := by
  classical
  rw [textbookTrackEntryArcs]
  refine List.mem_flatMap.mpr ⟨(slot, u), ?_, ?_⟩
  · exact List.mem_product.mpr ⟨List.mem_range.mpr hslot, List.mem_range.mpr hu⟩
  · simp [hHead]

theorem mem_textbookTrackExitArcs
    {I : VertexCoverInput} {slot u : Nat} {ui : Nat × Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices)
    (hLast : (incidencesOfVertex I u).getLast? = some ui) :
    (textbookIncidenceVertex I ui.1 ui.2 1,
      textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookTrackExitArcs I := by
  classical
  rw [textbookTrackExitArcs]
  refine List.mem_flatMap.mpr ⟨(slot, u), ?_, ?_⟩
  · exact List.mem_product.mpr ⟨List.mem_range.mpr hslot, List.mem_range.mpr hu⟩
  · simp [hLast]

theorem List.head?_eq_some_of_mem_forall_eq {α : Type*} {l : List α} {x : α}
    (hx : x ∈ l) (hAll : ∀ y ∈ l, y = x) :
    l.head? = some x := by
  cases l with
  | nil =>
      simp at hx
  | cons y ys =>
      have hy : y = x := hAll y (by simp)
      simp [hy]

/-- Selector skip arcs, used by unused cover positions. -/
def textbookSelectorSkipArcs (I : VertexCoverInput) : List (Nat × Nat) :=
  (List.range I.k).map fun slot =>
    (textbookSelectorVertex slot, textbookSelectorVertex (textbookNextSelector I slot))

theorem mem_textbookSelectorSkipArcs {I : VertexCoverInput} {slot : Nat}
    (hslot : slot < I.k) :
    (textbookSelectorVertex slot, textbookSelectorVertex (textbookNextSelector I slot)) ∈
      textbookSelectorSkipArcs I := by
  exact List.mem_map.mpr ⟨slot, List.mem_range.mpr hslot, rfl⟩

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
