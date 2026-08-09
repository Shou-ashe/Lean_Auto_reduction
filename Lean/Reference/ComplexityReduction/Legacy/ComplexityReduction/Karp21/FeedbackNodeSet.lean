/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Digraph
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
P15d graph target: Vertex Cover to Feedback Node Set.

The current graph schemas are raw finite objects.  This module follows the P15c
finite-witness pattern: enumerate bounded vertex-subset witnesses for the source
problem and map nonempty witness sets to a tiny yes-instance of the current
feedback-node-set semantics.
-/

namespace ComplexityReduction
namespace Karp21
namespace FeedbackNodeSet

open ComplexityReduction.Combinatorics.Graph

/-- Vertices selected by a Boolean characteristic function over `Fin n`. -/
def selectedVertices (n : Nat) (select : Fin n → Bool) : List Nat :=
  (List.range n).filter fun v => if h : v < n then select ⟨v, h⟩ else false

/-- Characteristic function of a raw vertex list. -/
def selectOfList (n : Nat) (vs : List Nat) : Fin n → Bool :=
  fun i => decide (i.val ∈ vs)

theorem selectedVertices_nodup (n : Nat) (select : Fin n → Bool) :
    (selectedVertices n select).Nodup := by
  simpa [selectedVertices] using
    (List.nodup_range (n := n)).filter
      (fun v => if h : v < n then select ⟨v, h⟩ else false)

theorem selectedVertices_withinBounds (g : GraphInput) (select : Fin g.vertices → Bool) :
    VerticesWithinBounds g (selectedVertices g.vertices select) := by
  intro v hv
  simp [selectedVertices] at hv
  exact hv.1

theorem mem_selectedVertices_selectOfList_iff {n : Nat} {vs : List Nat}
    (hBounds : ∀ v ∈ vs, v < n) (v : Nat) :
    v ∈ selectedVertices n (selectOfList n vs) ↔ v ∈ vs := by
  constructor
  · intro hv
    simp [selectedVertices, selectOfList] at hv
    exact hv.2
  · intro hv
    have hvn : v < n := hBounds v hv
    simp [selectedVertices, selectOfList, hvn, hv]

theorem selectedVertices_selectOfList_toFinset_eq {n : Nat} {vs : List Nat}
    (hBounds : ∀ v ∈ vs, v < n) :
    (selectedVertices n (selectOfList n vs)).toFinset = vs.toFinset := by
  apply Finset.ext
  intro v
  simp [mem_selectedVertices_selectOfList_iff hBounds v]

theorem selectedVertices_selectOfList_length_eq {n : Nat} {vs : List Nat}
    (hNodup : vs.Nodup) (hBounds : ∀ v ∈ vs, v < n) :
    (selectedVertices n (selectOfList n vs)).length = vs.length := by
  have hSelNodup := selectedVertices_nodup n (selectOfList n vs)
  rw [← List.toFinset_card_of_nodup hSelNodup,
    selectedVertices_selectOfList_toFinset_eq hBounds,
    List.toFinset_card_of_nodup hNodup]

/-- All vertex subsets represented as canonical bounded lists. -/
noncomputable def vertexSubsetCandidates (n : Nat) : List (List Nat) := by
  classical
  exact (Finset.univ : Finset (Fin n → Bool)).toList.map (selectedVertices n)

theorem selectedVertices_mem_vertexSubsetCandidates (n : Nat) (select : Fin n → Bool) :
    selectedVertices n select ∈ vertexSubsetCandidates n := by
  classical
  simp [vertexSubsetCandidates]

theorem coversEdges_selected_of_covers {g : GraphInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds g cover) (hCovers : CoversEdges g cover) :
    CoversEdges g (selectedVertices g.vertices (selectOfList g.vertices cover)) := by
  intro e he
  rcases hCovers e he with hLeft | hRight
  · left
    exact (mem_selectedVertices_selectOfList_iff hBounds e.1).2 hLeft
  · right
    exact (mem_selectedVertices_selectOfList_iff hBounds e.2).2 hRight

/-- Canonical bounded vertex-cover witnesses for an input. -/
noncomputable def vertexCoverWitnesses (I : VertexCoverInput) : List (List Nat) := by
  classical
  exact (vertexSubsetCandidates I.graph.vertices).filter fun cover =>
    decide
      (cover.length ≤ I.k ∧ cover.Nodup ∧ VerticesWithinBounds I.graph cover ∧
        CoversEdges I.graph cover)

theorem mem_vertexCoverWitnesses_iff (I : VertexCoverInput) (cover : List Nat) :
    cover ∈ vertexCoverWitnesses I ↔
      cover ∈ vertexSubsetCandidates I.graph.vertices ∧
        cover.length ≤ I.k ∧ cover.Nodup ∧ VerticesWithinBounds I.graph cover ∧
          CoversEdges I.graph cover := by
  classical
  simp [vertexCoverWitnesses]

theorem vertexCover_iff_witnesses_pos (I : VertexCoverInput) :
    VertexCover I ↔ 0 < (vertexCoverWitnesses I).length := by
  constructor
  · rintro ⟨cover, hLen, hNodup, hBounds, hCovers⟩
    let selected := selectedVertices I.graph.vertices (selectOfList I.graph.vertices cover)
    have hSelectedMem :
        selected ∈ vertexSubsetCandidates I.graph.vertices := by
      exact selectedVertices_mem_vertexSubsetCandidates I.graph.vertices
        (selectOfList I.graph.vertices cover)
    have hSelectedLen : selected.length ≤ I.k := by
      have hEq :=
        selectedVertices_selectOfList_length_eq hNodup hBounds
      have hEq' : selected.length = cover.length := by
        simpa [selected] using hEq
      omega
    have hPred :
        selected.length ≤ I.k ∧ selected.Nodup ∧ VerticesWithinBounds I.graph selected ∧
          CoversEdges I.graph selected := by
      refine ⟨hSelectedLen, ?_, ?_, ?_⟩
      · exact selectedVertices_nodup I.graph.vertices (selectOfList I.graph.vertices cover)
      · exact selectedVertices_withinBounds I.graph (selectOfList I.graph.vertices cover)
      · exact coversEdges_selected_of_covers hBounds hCovers
    have hMem : selected ∈ vertexCoverWitnesses I :=
      (mem_vertexCoverWitnesses_iff I selected).2 ⟨hSelectedMem, hPred⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : vertexCoverWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons cover rest =>
        have hMem : cover ∈ vertexCoverWitnesses I := by
          simp [hList]
        rcases (mem_vertexCoverWitnesses_iff I cover).1 hMem with
          ⟨_hCandidate, hLen, hNodup, hBounds, hCovers⟩
        exact ⟨cover, hLen, hNodup, hBounds, hCovers⟩

theorem feedbackNodeSetWitness_selected_of_witness {g : GraphInput} {removed : List Nat}
    (hWitness : FeedbackNodeSetWitness g removed) :
    FeedbackNodeSetWitness g
      (selectedVertices g.vertices (selectOfList g.vertices removed)) := by
  rcases hWitness with ⟨hNodup, hBounds, hHits⟩
  refine ⟨?_, ?_, ?_⟩
  · exact selectedVertices_nodup g.vertices (selectOfList g.vertices removed)
  · exact selectedVertices_withinBounds g (selectOfList g.vertices removed)
  · intro cycle hCycle
    rcases hHits cycle hCycle with ⟨v, hvCycle, hvRemoved⟩
    exact ⟨v, hvCycle, (mem_selectedVertices_selectOfList_iff hBounds v).2 hvRemoved⟩

/-- Canonical bounded feedback-node-set witnesses for an input. -/
noncomputable def feedbackNodeSetWitnesses (I : FeedbackNodeSetInput) : List (List Nat) := by
  classical
  exact (vertexSubsetCandidates I.graph.vertices).filter fun removed =>
    decide (removed.length ≤ I.k ∧ FeedbackNodeSetWitness I.graph removed)

theorem mem_feedbackNodeSetWitnesses_iff (I : FeedbackNodeSetInput) (removed : List Nat) :
    removed ∈ feedbackNodeSetWitnesses I ↔
      removed ∈ vertexSubsetCandidates I.graph.vertices ∧
        removed.length ≤ I.k ∧ FeedbackNodeSetWitness I.graph removed := by
  classical
  simp [feedbackNodeSetWitnesses]

theorem feedbackNodeSet_iff_witnesses_pos (I : FeedbackNodeSetInput) :
    FeedbackNodeSet I ↔ 0 < (feedbackNodeSetWitnesses I).length := by
  constructor
  · rintro ⟨removed, hLen, hWitness⟩
    rcases hWitness with ⟨hNodup, hBounds, hHits⟩
    let selected := selectedVertices I.graph.vertices (selectOfList I.graph.vertices removed)
    have hSelectedMem :
        selected ∈ vertexSubsetCandidates I.graph.vertices := by
      exact selectedVertices_mem_vertexSubsetCandidates I.graph.vertices
        (selectOfList I.graph.vertices removed)
    have hSelectedLen : selected.length ≤ I.k := by
      have hEq :=
        selectedVertices_selectOfList_length_eq hNodup hBounds
      have hEq' : selected.length = removed.length := by
        simpa [selected] using hEq
      omega
    have hSelectedWitness :
        FeedbackNodeSetWitness I.graph selected :=
      feedbackNodeSetWitness_selected_of_witness ⟨hNodup, hBounds, hHits⟩
    have hMem : selected ∈ feedbackNodeSetWitnesses I :=
      (mem_feedbackNodeSetWitnesses_iff I selected).2
        ⟨hSelectedMem, hSelectedLen, hSelectedWitness⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : feedbackNodeSetWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons removed rest =>
        have hMem : removed ∈ feedbackNodeSetWitnesses I := by
          simp [hList]
        rcases (mem_feedbackNodeSetWitnesses_iff I removed).1 hMem with
          ⟨_hCandidate, hLen, hWitness⟩
        exact ⟨removed, hLen, hWitness⟩

/-- One-vertex graph with a self loop. -/
def oneVertexLoopDigraph : GraphInput where
  vertices := 1
  edges := [(0, 0)]
  directed := true

/-- One-vertex graph with no directed edge. -/
def oneVertexEmptyDigraph : GraphInput where
  vertices := 1
  edges := []
  directed := true

theorem loopDigraph_singleton_cycle :
    DirectedCycle oneVertexLoopDigraph [0] := by
  simp [DirectedCycle, VerticesWithinBounds, HasDirectedEdge,
    oneVertexLoopDigraph]

theorem emptyDigraph_no_directedCycle :
    ¬ ∃ cycle : List Nat, DirectedCycle oneVertexEmptyDigraph cycle := by
  rintro ⟨cycle, hCycle⟩
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  cases cycle with
  | nil =>
      simp at hPos
  | cons u rest =>
      cases rest with
      | nil =>
          have hu0 : u = 0 := by
            have huBound : u < 1 := hBounds u (by simp)
            omega
          rcases hStep u (by simp) with ⟨v, _hvCycle, hEdge⟩
          simp [oneVertexEmptyDigraph, HasDirectedEdge] at hEdge
      | cons v rest' =>
          have hu0 : u = 0 := by
            have huBound : u < 1 := hBounds u (by simp)
            omega
          have hv0 : v = 0 := by
            have hvBound : v < 1 := hBounds v (by simp)
            omega
          subst u
          subst v
          simp at hNodup

/-- A yes-instance for the current feedback-node-set semantics. -/
def yesInput : FeedbackNodeSetInput where
  graph := oneVertexEmptyDigraph
  k := 0

/-- A no-instance for the current feedback-node-set semantics. -/
def noInput : FeedbackNodeSetInput where
  graph := oneVertexLoopDigraph
  k := 0

theorem yesInput_isYes :
    FeedbackNodeSet yesInput := by
  refine ⟨[], by simp [yesInput], ?_⟩
  refine ⟨by simp, by simp [VerticesWithinBounds], ?_⟩
  intro cycle hCycle
  exact False.elim (emptyDigraph_no_directedCycle ⟨cycle, hCycle⟩)

theorem noInput_isNo :
    ¬ FeedbackNodeSet noInput := by
  rintro ⟨removed, hLen, _hNodup, _hBounds, hHits⟩
  have hRemovedNil : removed = [] := by
    cases removed with
    | nil => rfl
    | cons v rest =>
        simp [noInput] at hLen
  have hHit := hHits [0] loopDigraph_singleton_cycle
  simp [hRemovedNil] at hHit

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : FeedbackNodeSetInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    FeedbackNodeSet (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15d syntax map from Vertex Cover to Feedback Node Set. -/
noncomputable def map (I : VertexCoverInput) : FeedbackNodeSetInput :=
  indicatorInput (vertexCoverWitnesses I).length

theorem map_correct (I : VertexCoverInput) :
    vertexCoverDecisionProblem.isYes I ↔ FeedbackNodeSet (map I) := by
  change VertexCover I ↔ FeedbackNodeSet (map I)
  rw [vertexCover_iff_witnesses_pos]
  exact (indicatorInput_correct (vertexCoverWitnesses I).length).symm

/-! ### Textbook directed-cycle route -/

def HasUncoverableEdge (g : GraphInput) : Prop :=
  ∃ e ∈ g.edges, ¬ e.1 < g.vertices ∧ ¬ e.2 < g.vertices

def edgeToArcs (g : GraphInput) (e : Nat × Nat) : List (Nat × Nat) :=
  if e.1 < g.vertices then
    if e.2 < g.vertices then [(e.1, e.2), (e.2, e.1)] else [(e.1, e.1)]
  else
    if e.2 < g.vertices then [(e.2, e.2)] else []

def textbookEdges (g : GraphInput) : List (Nat × Nat) :=
  g.edges.flatMap (edgeToArcs g)

def textbookGraph (g : GraphInput) : GraphInput where
  vertices := g.vertices
  edges := textbookEdges g
  directed := true

theorem mem_textbookEdges_of_mem_edgeToArcs {g : GraphInput} {e arc : Nat × Nat}
    (he : e ∈ g.edges) (hArc : arc ∈ edgeToArcs g e) :
    arc ∈ textbookEdges g :=
  List.mem_flatMap.mpr ⟨e, he, hArc⟩

noncomputable def textbookMap (I : VertexCoverInput) : FeedbackNodeSetInput := by
  classical
  exact
    if HasUncoverableEdge I.graph then
      noInput
    else
      { graph := textbookGraph I.graph
        k := I.k }

theorem not_vertexCover_of_hasUncoverableEdge {I : VertexCoverInput}
    (hBad : HasUncoverableEdge I.graph) :
    ¬ VertexCover I := by
  rcases hBad with ⟨e, he, hLeftBad, hRightBad⟩
  rintro ⟨cover, _hLen, _hNodup, hBounds, hCovers⟩
  rcases hCovers e he with hLeft | hRight
  · exact hLeftBad (hBounds e.1 hLeft)
  · exact hRightBad (hBounds e.2 hRight)

theorem cover_hits_arc_of_mem_edgeToArcs {g : GraphInput} {cover : List Nat}
    {e arc : Nat × Nat} (hBounds : VerticesWithinBounds g cover)
    (hCover : e.1 ∈ cover ∨ e.2 ∈ cover) (hArc : arc ∈ edgeToArcs g e) :
    arc.1 ∈ cover ∨ arc.2 ∈ cover := by
  cases arc with
  | mk u v =>
      by_cases hLeft : e.1 < g.vertices
      · by_cases hRight : e.2 < g.vertices
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with hArc | hArc
          · rcases hArc with ⟨rfl, rfl⟩
            exact hCover
          · rcases hArc with ⟨rfl, rfl⟩
            exact hCover.symm
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with ⟨rfl, rfl⟩
          rcases hCover with hCover | hCover
          · exact Or.inl hCover
          · exact False.elim (hRight (hBounds e.2 hCover))
      · by_cases hRight : e.2 < g.vertices
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with ⟨rfl, rfl⟩
          rcases hCover with hCover | hCover
          · exact False.elim (hLeft (hBounds e.1 hCover))
          · exact Or.inl hCover
        · simp [edgeToArcs, hLeft, hRight] at hArc

theorem singleton_directedCycle_of_loop {g : GraphInput} {u : Nat}
    (hu : u < g.vertices) (hLoop : (u, u) ∈ g.edges) :
    DirectedCycle g [u] := by
  simp [DirectedCycle, VerticesWithinBounds, HasDirectedEdge, hu, hLoop]

theorem pair_directedCycle_of_two_arcs {g : GraphInput} {u v : Nat}
    (hu : u < g.vertices) (hv : v < g.vertices) (huvNe : u ≠ v)
    (hForward : (u, v) ∈ g.edges) (hBackward : (v, u) ∈ g.edges) :
    DirectedCycle g [u, v] := by
  simp [DirectedCycle, VerticesWithinBounds, HasDirectedEdge, hu, hv, huvNe,
    hForward, hBackward]

theorem textbookMap_correct (I : VertexCoverInput) :
    vertexCoverDecisionProblem.isYes I ↔ FeedbackNodeSet (textbookMap I) := by
  classical
  change VertexCover I ↔ FeedbackNodeSet (textbookMap I)
  by_cases hBad : HasUncoverableEdge I.graph
  · constructor
    · intro hVC
      exact False.elim (not_vertexCover_of_hasUncoverableEdge hBad hVC)
    · intro hFNS
      exact False.elim (noInput_isNo (by simpa [textbookMap, hBad] using hFNS))
  · constructor
    · rintro ⟨cover, hLen, hNodup, hBounds, hCovers⟩
      refine ⟨cover, by simpa [textbookMap, hBad] using hLen, ?_⟩
      refine ⟨hNodup, ?_, ?_⟩
      · intro v hv
        simpa [textbookMap, hBad, textbookGraph] using hBounds v hv
      · intro cycle hCycle
        rcases hCycle with ⟨hPos, _hCycleNodup, _hCycleBounds, hStep⟩
        cases cycle with
        | nil => simp at hPos
        | cons u rest =>
            have huCycle : u ∈ u :: rest := by simp
            rcases hStep u huCycle with ⟨v, hvCycle, hEdge⟩
            have hEdgeTextbook : (u, v) ∈ textbookEdges I.graph := by
              simpa [textbookMap, hBad, textbookGraph, HasDirectedEdge] using hEdge
            rcases List.mem_flatMap.mp hEdgeTextbook with ⟨e, he, hArc⟩
            have hHit := cover_hits_arc_of_mem_edgeToArcs hBounds (hCovers e he) hArc
            rcases hHit with huCover | hvCover
            · exact ⟨u, huCycle, huCover⟩
            · exact ⟨v, hvCycle, hvCover⟩
    · rintro ⟨removed, hLen, hWitness⟩
      rcases hWitness with ⟨hNodup, hBounds, hHits⟩
      refine ⟨removed, by simpa [textbookMap, hBad] using hLen, hNodup, ?_, ?_⟩
      · intro v hv
        simpa [textbookMap, hBad, textbookGraph] using hBounds v hv
      · intro e he
        rcases e with ⟨u, v⟩
        by_contra hNotCovered
        have hLeftNot : u ∉ removed := by
          intro h
          exact hNotCovered (Or.inl h)
        have hRightNot : v ∉ removed := by
          intro h
          exact hNotCovered (Or.inr h)
        by_cases hLeft : u < I.graph.vertices
        · by_cases hRight : v < I.graph.vertices
          · by_cases hEq : u = v
            · subst v
              have hLoop : (u, u) ∈ (textbookGraph I.graph).edges := by
                exact mem_textbookEdges_of_mem_edgeToArcs he (by simp [edgeToArcs, hLeft])
              have hCycle : DirectedCycle (textbookGraph I.graph) [u] :=
                singleton_directedCycle_of_loop hLeft hLoop
              have hHit := hHits [u] (by simpa [textbookMap, hBad] using hCycle)
              rcases hHit with ⟨v, hv, hvRemoved⟩
              simp at hv
              subst v
              exact hLeftNot hvRemoved
            · have hForward : (u, v) ∈ (textbookGraph I.graph).edges := by
                exact mem_textbookEdges_of_mem_edgeToArcs he
                  (by simp [edgeToArcs, hLeft, hRight])
              have hBackward : (v, u) ∈ (textbookGraph I.graph).edges := by
                exact mem_textbookEdges_of_mem_edgeToArcs he
                  (by simp [edgeToArcs, hLeft, hRight])
              have hCycle : DirectedCycle (textbookGraph I.graph) [u, v] :=
                pair_directedCycle_of_two_arcs hLeft hRight hEq hForward hBackward
              have hHit := hHits [u, v] (by simpa [textbookMap, hBad] using hCycle)
              rcases hHit with ⟨v, hv, hvRemoved⟩
              simp at hv
              rcases hv with rfl | rfl
              · exact hLeftNot hvRemoved
              · exact hRightNot hvRemoved
          · have hLoop : (u, u) ∈ (textbookGraph I.graph).edges := by
              exact mem_textbookEdges_of_mem_edgeToArcs he
                (by simp [edgeToArcs, hLeft, hRight])
            have hCycle : DirectedCycle (textbookGraph I.graph) [u] :=
              singleton_directedCycle_of_loop hLeft hLoop
            have hHit := hHits [u] (by simpa [textbookMap, hBad] using hCycle)
            rcases hHit with ⟨v, hv, hvRemoved⟩
            simp at hv
            subst v
            exact hLeftNot hvRemoved
        · by_cases hRight : v < I.graph.vertices
          · have hLoop : (v, v) ∈ (textbookGraph I.graph).edges := by
              exact mem_textbookEdges_of_mem_edgeToArcs he
                (by simp [edgeToArcs, hLeft, hRight])
            have hCycle : DirectedCycle (textbookGraph I.graph) [v] :=
              singleton_directedCycle_of_loop hRight hLoop
            have hHit := hHits [v] (by simpa [textbookMap, hBad] using hCycle)
            rcases hHit with ⟨v, hv, hvRemoved⟩
            simp at hv
            subst v
            exact hRightNot hvRemoved
          · exact False.elim (hBad ⟨(u, v), he, hLeft, hRight⟩)

/-! ### Structured finite-alphabet size bound for the textbook route -/

theorem edgeToArcs_length_le_two (g : GraphInput) (e : Nat × Nat) :
    (edgeToArcs g e).length ≤ 2 := by
  by_cases hLeft : e.1 < g.vertices
  · by_cases hRight : e.2 < g.vertices <;> simp [edgeToArcs, hLeft, hRight]
  · by_cases hRight : e.2 < g.vertices <;> simp [edgeToArcs, hLeft, hRight]

theorem edgeToArcs_flatMap_length_le (g : GraphInput) (edges : List (Nat × Nat)) :
    (edges.flatMap (edgeToArcs g)).length ≤ 2 * edges.length := by
  induction edges with
  | nil =>
      simp
  | cons e edges ih =>
      have hHead := edgeToArcs_length_le_two g e
      calc
        (List.flatMap (edgeToArcs g) (e :: edges)).length =
            (edgeToArcs g e).length + (List.flatMap (edgeToArcs g) edges).length := by
              simp
        _ ≤ 2 + 2 * edges.length := by
              exact Nat.add_le_add hHead ih
        _ = 2 * (e :: edges).length := by
              simp
              omega

theorem textbookEdges_length_le (g : GraphInput) :
    (textbookEdges g).length ≤ 2 * g.edges.length := by
  simpa [textbookEdges] using edgeToArcs_flatMap_length_le g g.edges

theorem edgeToArcs_within_bounds {g : GraphInput} {e arc : Nat × Nat}
    (hArc : arc ∈ edgeToArcs g e) :
    arc.1 < g.vertices ∧ arc.2 < g.vertices := by
  cases arc with
  | mk u v =>
      by_cases hLeft : e.1 < g.vertices
      · by_cases hRight : e.2 < g.vertices
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with hArc | hArc
          · rcases hArc with ⟨rfl, rfl⟩
            exact ⟨hLeft, hRight⟩
          · rcases hArc with ⟨rfl, rfl⟩
            exact ⟨hRight, hLeft⟩
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with ⟨rfl, rfl⟩
          exact ⟨hLeft, hLeft⟩
      · by_cases hRight : e.2 < g.vertices
        · simp [edgeToArcs, hLeft, hRight] at hArc
          rcases hArc with ⟨rfl, rfl⟩
          exact ⟨hRight, hRight⟩
        · simp [edgeToArcs, hLeft, hRight] at hArc

theorem edgeStructured_inputSize_le_of_mem_textbookEdges {g : GraphInput} {arc : Nat × Nat}
    (hArc : arc ∈ textbookEdges g) :
    edgeStructuredEncodedType.inputSize arc ≤ 2 * g.vertices + 1 := by
  rcases List.mem_flatMap.mp hArc with ⟨e, _he, hMem⟩
  rcases edgeToArcs_within_bounds hMem with ⟨hFirst, hSecond⟩
  cases arc with
  | mk u v =>
      simp [edgeStructuredEncodedType] at hFirst hSecond ⊢
      omega

theorem textbookEdges_structured_inputSize_le (g : GraphInput) :
    edgeListStructuredEncodedType.inputSize (textbookEdges g) ≤
      (2 * g.edges.length) * (2 * g.vertices + 2) := by
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdges g) (2 * g.vertices + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_textbookEdges he)
  have hLen := textbookEdges_length_le g
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (2 * g.vertices + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem feedbackNodeSetStructured_inputSize_eq (I : FeedbackNodeSetInput) :
    feedbackNodeSetStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.k + 2 := by
  change feedbackNodeSetTupleStructuredEncodedType.inputSize (I.graph, I.k) =
    graphStructuredEncodedType.inputSize I.graph + I.k + 2
  simp [feedbackNodeSetTupleStructuredEncodedType]
  omega

theorem vertexCoverStructured_inputSize_ge_edges_length (I : VertexCoverInput) :
    I.graph.edges.length ≤ vertexCoverStructuredEncodedType.inputSize I := by
  have hEdges :
      I.graph.edges.length ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeListStructuredEncodedType, EncodedType.inputSize] using
      (TM2Programs.listEncode_length_ge_length edgeStructuredEncodedType I.graph.edges)
  rw [VertexCover.vertexCoverStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
  omega

theorem vertexCoverStructured_inputSize_ge_vertices (I : VertexCoverInput) :
    I.graph.vertices ≤ vertexCoverStructuredEncodedType.inputSize I := by
  rw [VertexCover.vertexCoverStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
  omega

theorem vertexCoverStructured_inputSize_ge_budget (I : VertexCoverInput) :
    I.k ≤ vertexCoverStructuredEncodedType.inputSize I := by
  rw [VertexCover.vertexCoverStructured_inputSize_eq]
  omega

theorem noInput_structured_inputSize_le :
    feedbackNodeSetStructuredEncodedType.inputSize noInput ≤ 100 := by
  rw [feedbackNodeSetStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
  change
    1 + edgeListStructuredEncodedType.inputSize ([(0, 0)] : List (Nat × Nat)) + 4 + 0 + 2 ≤
      100
  have hEdge :
      edgeStructuredEncodedType.inputSize ((0 : Nat), (0 : Nat)) ≤ 3 := by
    change (EncodedType.prod EncodedType.nat EncodedType.nat).inputSize
      ((0 : Nat), (0 : Nat)) ≤ 3
    norm_num
  have hList :
      edgeListStructuredEncodedType.inputSize ([(0, 0)] : List (Nat × Nat)) ≤ 1 * (3 + 1) :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      ([(0, 0)] : List (Nat × Nat)) 3 (by
        intro e he
        have heq : e = ((0 : Nat), (0 : Nat)) := List.mem_singleton.mp he
        simpa [heq] using hEdge)
  omega

theorem feedbackNodeSetStructured_inputSize_textbookMap_le_vertexCover_poly
    (I : VertexCoverInput) :
    feedbackNodeSetStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (vertexCoverStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  classical
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using vertexCoverStructured_inputSize_ge_vertices I
  have hEdgesLen : I.graph.edges.length ≤ S := by
    simpa [S] using vertexCoverStructured_inputSize_ge_edges_length I
  have hBudget : I.k ≤ S := by
    simpa [S] using vertexCoverStructured_inputSize_ge_budget I
  by_cases hBad : HasUncoverableEdge I.graph
  · calc
      feedbackNodeSetStructuredEncodedType.inputSize (textbookMap I) =
          feedbackNodeSetStructuredEncodedType.inputSize noInput := by
            simp [textbookMap, hBad]
      _ ≤ 100 := noInput_structured_inputSize_le
      _ ≤ 1000 * S ^ 2 + 1000 := by
            omega
  · have hEdges := textbookEdges_structured_inputSize_le I.graph
    have hEdgePoly :
        (2 * I.graph.edges.length) * (2 * I.graph.vertices + 2) ≤
          (2 * S) * (2 * S + 2) := by
      have hLeft : 2 * I.graph.edges.length ≤ 2 * S := by omega
      have hRight : 2 * I.graph.vertices + 2 ≤ 2 * S + 2 := by omega
      exact Nat.mul_le_mul hLeft hRight
    have hOutput :
        feedbackNodeSetStructuredEncodedType.inputSize (textbookMap I) ≤
          I.graph.vertices +
            (2 * I.graph.edges.length) * (2 * I.graph.vertices + 2) +
            4 + I.k + 2 := by
      rw [feedbackNodeSetStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
      simp [textbookMap, hBad, textbookGraph]
      omega
    have hCoarse :
        feedbackNodeSetStructuredEncodedType.inputSize (textbookMap I) ≤
          S + (2 * S) * (2 * S + 2) + 4 + S + 2 := by
      omega
    calc
      feedbackNodeSetStructuredEncodedType.inputSize (textbookMap I) ≤
          S + (2 * S) * (2 * S + 2) + 4 + S + 2 := hCoarse
      _ ≤ 1000 * S ^ 2 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem vertexCoverToFeedbackNodeSetStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize I)
      (fun J : FeedbackNodeSetInput => feedbackNodeSetStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact feedbackNodeSetStructured_inputSize_textbookMap_le_vertexCover_poly I

/-- Costed Karp reduction from Vertex Cover to Feedback Node Set. -/
noncomputable def vertexCoverToFeedbackNodeSetTMBackedKarpReduction :
    TMBackedCostedReduction vertexCoverDecisionProblem feedbackNodeSetDecisionProblem := by
  simpa [feedbackNodeSetDecisionProblem, feedbackNodeSetEncodedType] using
    rawCodomainTMBackedReduction
      vertexCoverDecisionProblem
      Combinatorics.Graph.FeedbackNodeSet
      map
      map_correct

/-- Costed Karp reduction from Vertex Cover to Feedback Node Set. -/
noncomputable def vertexCoverToFeedbackNodeSetKarpReduction :
    KarpReductionM CostedPolyTimeModel vertexCoverDecisionProblem
      feedbackNodeSetDecisionProblem :=
  vertexCoverToFeedbackNodeSetTMBackedKarpReduction.toCostedKarpReduction

/-- Costed Karp reduction from Vertex Cover to Feedback Node Set by bidirected edges. -/
noncomputable def vertexCoverToFeedbackNodeSet_textbookTMBackedKarpReduction :
    TMBackedCostedReduction vertexCoverDecisionProblem feedbackNodeSetDecisionProblem := by
  simpa [feedbackNodeSetDecisionProblem, feedbackNodeSetEncodedType] using
    rawCodomainTMBackedReduction
      vertexCoverDecisionProblem
      Combinatorics.Graph.FeedbackNodeSet
      textbookMap
      textbookMap_correct

/-- Costed Karp reduction from Vertex Cover to Feedback Node Set by bidirected edges. -/
noncomputable def vertexCoverToFeedbackNodeSet_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel vertexCoverDecisionProblem
      feedbackNodeSetDecisionProblem :=
  vertexCoverToFeedbackNodeSet_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- The structured finite-alphabet Feedback Node Set encoding is faithful. -/
theorem feedbackNodeSetStructuredEncoding_faithful :
    feedbackNodeSetStructuredDecisionProblem.FaithfulEncoding where
  injective := feedbackNodeSetStructuredEncodedType_encode_injective

theorem feedbackNodeSetStructuredEncoding_predicateRespects :
    feedbackNodeSetStructuredDecisionProblem.PredicateRespectsEncoding :=
  feedbackNodeSetStructuredEncoding_faithful.predicateRespects

theorem feedbackNodeSetStructuredEncoding_accepts_encode_iff (I : FeedbackNodeSetInput) :
    feedbackNodeSetStructuredDecisionProblem.toEncodedLanguage.accepts
        (feedbackNodeSetStructuredEncodedType.encode I) ↔
      FeedbackNodeSet I :=
  feedbackNodeSetStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Feedback Node Set is locally in NP for the project-local costed model. -/
theorem feedbackNodeSetInNP :
    InNPEnc CostedPolyTimeModel feedbackNodeSetDecisionProblem :=
  decidableInNP feedbackNodeSetDecisionProblem

/-- Local NP-completeness of Feedback Node Set via Vertex Cover. -/
theorem feedbackNodeSetNPComplete :
    NPCompleteEnc CostedPolyTimeModel feedbackNodeSetDecisionProblem :=
  NPCompleteEnc.transfer
    VertexCover.vertexCoverNPComplete
    ⟨vertexCoverToFeedbackNodeSetKarpReduction⟩
    feedbackNodeSetInNP

/-- Local NP-completeness of Feedback Node Set via the P15t textbook cycle route. -/
theorem feedbackNodeSet_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel feedbackNodeSetDecisionProblem :=
  NPCompleteEnc.transfer
    VertexCover.vertexCoverNPComplete
    ⟨vertexCoverToFeedbackNodeSet_textbookKarpReduction⟩
    feedbackNodeSetInNP

end FeedbackNodeSet
end Karp21
end ComplexityReduction
