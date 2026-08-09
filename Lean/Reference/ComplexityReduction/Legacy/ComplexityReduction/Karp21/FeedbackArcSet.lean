/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSet
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

/-!
P15d graph target: Feedback Node Set to Feedback Arc Set.

This is a current-schema finite-witness route.  A source feedback-node-set
witness list controls a tiny yes/no feedback-arc-set instance under the raw
semantics from `Graph.Digraph`.
-/

namespace ComplexityReduction
namespace Karp21
namespace FeedbackArcSet

open ComplexityReduction.Combinatorics.Graph

/-- A yes-instance for the current feedback-arc-set semantics. -/
def yesInput : FeedbackArcSetInput where
  graph := FeedbackNodeSet.oneVertexEmptyDigraph
  k := 0

/-- A no-instance for the current feedback-arc-set semantics. -/
def noInput : FeedbackArcSetInput where
  graph := FeedbackNodeSet.oneVertexLoopDigraph
  k := 0

theorem yesInput_isYes :
    FeedbackArcSet yesInput := by
  refine ⟨[], by simp [yesInput], ?_⟩
  refine ⟨by simp [yesInput, FeedbackNodeSet.oneVertexEmptyDigraph], ?_⟩
  intro cycle hCycle
  exact False.elim
    (FeedbackNodeSet.emptyDigraph_no_directedCycle
      ⟨cycle, by simpa [yesInput, deleteArcs, FeedbackNodeSet.oneVertexEmptyDigraph] using hCycle⟩)

theorem noInput_isNo :
    ¬ FeedbackArcSet noInput := by
  rintro ⟨removed, hLen, _hWithinEdges, hNoCycle⟩
  have hRemovedNil : removed = [] := by
    cases removed with
    | nil => rfl
    | cons e rest =>
        simp [noInput] at hLen
  have hCycle :
      DirectedCycle (deleteArcs noInput.graph removed) [0] := by
    simpa [noInput, hRemovedNil, deleteArcs] using
      FeedbackNodeSet.loopDigraph_singleton_cycle
  exact hNoCycle [0] hCycle

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : FeedbackArcSetInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    FeedbackArcSet (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15d syntax map from Feedback Node Set to Feedback Arc Set. -/
noncomputable def map (I : FeedbackNodeSetInput) : FeedbackArcSetInput :=
  indicatorInput (FeedbackNodeSet.feedbackNodeSetWitnesses I).length

theorem map_correct (I : FeedbackNodeSetInput) :
    feedbackNodeSetDecisionProblem.isYes I ↔ FeedbackArcSet (map I) := by
  change FeedbackNodeSet I ↔ FeedbackArcSet (map I)
  rw [FeedbackNodeSet.feedbackNodeSet_iff_witnesses_pos]
  exact (indicatorInput_correct (FeedbackNodeSet.feedbackNodeSetWitnesses I).length).symm

/-! ### Textbook node-splitting route -/

def inVertex (u : Nat) : Nat :=
  2 * u

def outVertex (u : Nat) : Nat :=
  2 * u + 1

def splitArc (u : Nat) : Nat × Nat :=
  (inVertex u, outVertex u)

def crossArc (e : Nat × Nat) : Nat × Nat :=
  (outVertex e.1, inVertex e.2)

def boundedSourceEdges (g : GraphInput) : List (Nat × Nat) :=
  g.edges.filter fun e => decide (e.1 < g.vertices ∧ e.2 < g.vertices)

def splitArcs (g : GraphInput) : List (Nat × Nat) :=
  (List.range g.vertices).map splitArc

def crossArcs (g : GraphInput) : List (Nat × Nat) :=
  (boundedSourceEdges g).map crossArc

def splitGraph (g : GraphInput) : GraphInput where
  vertices := 2 * g.vertices
  edges := splitArcs g ++ crossArcs g
  directed := true

def removedSplitArcs (removed : List Nat) : List (Nat × Nat) :=
  removed.map splitArc

def normalizedVerticesOfArcs (removed : List (Nat × Nat)) : List Nat :=
  (removed.map fun e => e.1 / 2).dedup

def expandedCycle (cycle : List Nat) : List Nat :=
  cycle.map inVertex ++ cycle.map outVertex

def projectedCycle (g : GraphInput) (cycle : List Nat) : List Nat :=
  (List.range g.vertices).filter fun u => decide (inVertex u ∈ cycle)

noncomputable def textbookMap (I : FeedbackNodeSetInput) : FeedbackArcSetInput :=
  { graph := splitGraph I.graph
    k := I.k }

theorem inVertex_injective :
    Function.Injective inVertex := by
  intro u v h
  simp [inVertex] at h
  omega

theorem outVertex_injective :
    Function.Injective outVertex := by
  intro u v h
  simp [outVertex] at h
  omega

theorem inVertex_ne_outVertex (u v : Nat) :
    inVertex u ≠ outVertex v := by
  simp [inVertex, outVertex]
  omega

theorem outVertex_ne_inVertex (u v : Nat) :
    outVertex u ≠ inVertex v := by
  exact (inVertex_ne_outVertex v u).symm

theorem inVertex_lt_split {g : GraphInput} {u : Nat} (hu : u < g.vertices) :
    inVertex u < (splitGraph g).vertices := by
  simp [splitGraph, inVertex]
  omega

theorem outVertex_lt_split {g : GraphInput} {u : Nat} (hu : u < g.vertices) :
    outVertex u < (splitGraph g).vertices := by
  simp [splitGraph, outVertex]
  omega

theorem mem_boundedSourceEdges_iff (g : GraphInput) (e : Nat × Nat) :
    e ∈ boundedSourceEdges g ↔
      e ∈ g.edges ∧ e.1 < g.vertices ∧ e.2 < g.vertices := by
  cases e with
  | mk u v =>
      simp [boundedSourceEdges]

theorem mem_splitArcs_iff {g : GraphInput} {e : Nat × Nat} :
    e ∈ splitArcs g ↔ ∃ u, u < g.vertices ∧ e = splitArc u := by
  constructor
  · intro he
    rcases List.mem_map.mp he with ⟨u, hu, rfl⟩
    exact ⟨u, List.mem_range.mp hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩

theorem mem_crossArcs_iff {g : GraphInput} {e : Nat × Nat} :
    e ∈ crossArcs g ↔
      ∃ a, a ∈ g.edges ∧ a.1 < g.vertices ∧ a.2 < g.vertices ∧ e = crossArc a := by
  constructor
  · intro he
    rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
    rcases (mem_boundedSourceEdges_iff g a).1 ha with ⟨haEdge, haLeft, haRight⟩
    exact ⟨a, haEdge, haLeft, haRight, rfl⟩
  · rintro ⟨a, haEdge, haLeft, haRight, rfl⟩
    exact List.mem_map.mpr
      ⟨a, (mem_boundedSourceEdges_iff g a).2 ⟨haEdge, haLeft, haRight⟩, rfl⟩

theorem mem_splitGraph_edges_iff {g : GraphInput} {e : Nat × Nat} :
    e ∈ (splitGraph g).edges ↔
      (∃ u, u < g.vertices ∧ e = splitArc u) ∨
        ∃ a, a ∈ g.edges ∧ a.1 < g.vertices ∧ a.2 < g.vertices ∧ e = crossArc a := by
  simp [splitGraph, mem_splitArcs_iff, mem_crossArcs_iff]

theorem splitArc_mem_splitGraph {g : GraphInput} {u : Nat} (hu : u < g.vertices) :
    splitArc u ∈ (splitGraph g).edges := by
  exact (mem_splitGraph_edges_iff (g := g) (e := splitArc u)).2
    (Or.inl ⟨u, hu, rfl⟩)

theorem crossArc_mem_splitGraph {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ g.edges) (hLeft : e.1 < g.vertices) (hRight : e.2 < g.vertices) :
    crossArc e ∈ (splitGraph g).edges := by
  exact (mem_splitGraph_edges_iff (g := g) (e := crossArc e)).2
    (Or.inr ⟨e, he, hLeft, hRight, rfl⟩)

theorem mem_projectedCycle_iff {g : GraphInput} {cycle : List Nat} {u : Nat} :
    u ∈ projectedCycle g cycle ↔ u < g.vertices ∧ inVertex u ∈ cycle := by
  simp [projectedCycle]

theorem mem_expandedCycle_iff {cycle : List Nat} {x : Nat} :
    x ∈ expandedCycle cycle ↔
      (∃ u ∈ cycle, x = inVertex u) ∨ ∃ u ∈ cycle, x = outVertex u := by
  constructor
  · intro hx
    simp [expandedCycle] at hx
    rcases hx with ⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩
    · exact Or.inl ⟨u, hu, hxu.symm⟩
    · exact Or.inr ⟨u, hu, hxu.symm⟩
  · intro hx
    simp [expandedCycle]
    rcases hx with ⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩
    · exact Or.inl ⟨u, hu, hxu.symm⟩
    · exact Or.inr ⟨u, hu, hxu.symm⟩

theorem inVertex_mem_expandedCycle {cycle : List Nat} {u : Nat} (hu : u ∈ cycle) :
    inVertex u ∈ expandedCycle cycle := by
  exact mem_expandedCycle_iff.2 (Or.inl ⟨u, hu, rfl⟩)

theorem outVertex_mem_expandedCycle {cycle : List Nat} {u : Nat} (hu : u ∈ cycle) :
    outVertex u ∈ expandedCycle cycle := by
  exact mem_expandedCycle_iff.2 (Or.inr ⟨u, hu, rfl⟩)

theorem inVertex_div_two (u : Nat) :
    inVertex u / 2 = u := by
  simp [inVertex]

theorem outVertex_div_two (u : Nat) :
    outVertex u / 2 = u := by
  simp [outVertex, Nat.add_comm, Nat.add_mul_div_left]

theorem expandedCycle_nodup {cycle : List Nat} (hNodup : cycle.Nodup) :
    (expandedCycle cycle).Nodup := by
  unfold expandedCycle
  refine (hNodup.map inVertex_injective).append (hNodup.map outVertex_injective) ?_
  intro x hx hy
  rcases List.mem_map.mp hx with ⟨u, _hu, rfl⟩
  rcases List.mem_map.mp hy with ⟨v, _hv, hEq⟩
  exact outVertex_ne_inVertex v u hEq

theorem expandedCycle_withinBounds {g : GraphInput} {cycle : List Nat}
    (hBounds : VerticesWithinBounds g cycle) :
    VerticesWithinBounds (splitGraph g) (expandedCycle cycle) := by
  intro x hx
  rcases mem_expandedCycle_iff.1 hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
  · exact inVertex_lt_split (g := g) (hBounds u hu)
  · exact outVertex_lt_split (g := g) (hBounds u hu)

theorem splitGraph_edge_cases {g : GraphInput} {u v : Nat}
    (hEdge : HasDirectedEdge (splitGraph g) u v) :
    (∃ a, a < g.vertices ∧ u = inVertex a ∧ v = outVertex a) ∨
      ∃ a b,
        (a, b) ∈ g.edges ∧ a < g.vertices ∧ b < g.vertices ∧
          u = outVertex a ∧ v = inVertex b := by
  rcases (mem_splitGraph_edges_iff (g := g) (e := (u, v))).1 hEdge with hSplit | hCross
  · rcases hSplit with ⟨a, ha, hEq⟩
    rcases hEq with ⟨rfl, rfl⟩
    exact Or.inl ⟨a, ha, rfl, rfl⟩
  · rcases hCross with ⟨a, haEdge, haLeft, haRight, hEq⟩
    rcases a with ⟨s, t⟩
    rcases hEq with ⟨rfl, rfl⟩
    exact Or.inr ⟨s, t, haEdge, haLeft, haRight, rfl, rfl⟩

theorem expandedCycle_directedCycle {g : GraphInput} {cycle : List Nat}
    (hCycle : DirectedCycle g cycle) :
    DirectedCycle (splitGraph g) (expandedCycle cycle) := by
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  refine ⟨?_, expandedCycle_nodup hNodup, expandedCycle_withinBounds hBounds, ?_⟩
  · cases cycle with
    | nil =>
        simp at hPos
    | cons u rest =>
        have hu : u ∈ u :: rest := by simp
        exact List.length_pos_of_mem (inVertex_mem_expandedCycle (cycle := u :: rest) hu)
  · intro x hx
    rcases mem_expandedCycle_iff.1 hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨outVertex u, outVertex_mem_expandedCycle hu, ?_⟩
      simpa [HasDirectedEdge, splitArc] using splitArc_mem_splitGraph (g := g) (hBounds u hu)
    · rcases hStep u hu with ⟨v, hv, hEdge⟩
      refine ⟨inVertex v, inVertex_mem_expandedCycle hv, ?_⟩
      simpa [HasDirectedEdge, crossArc] using
        crossArc_mem_splitGraph (g := g) (e := (u, v)) hEdge (hBounds u hu) (hBounds v hv)

theorem exists_projectedCycle_mem_of_splitCycle {g : GraphInput} {cycle : List Nat}
    (hCycle : DirectedCycle (splitGraph g) cycle) :
    ∃ u, u ∈ projectedCycle g cycle := by
  rcases hCycle with ⟨hPos, _hNodup, _hBounds, hStep⟩
  cases cycle with
  | nil =>
      simp at hPos
  | cons x rest =>
      have hx : x ∈ x :: rest := by simp
      rcases hStep x hx with ⟨y, hy, hEdge⟩
      rcases splitGraph_edge_cases hEdge with hSplit | hCross
      · rcases hSplit with ⟨u, hu, hxEq, _hyEq⟩
        exact ⟨u, mem_projectedCycle_iff.2 ⟨hu, by simp [hxEq]⟩⟩
      · rcases hCross with ⟨u, v, _hEdge, _hu, hv, _hxEq, hyEq⟩
        exact ⟨v, mem_projectedCycle_iff.2 ⟨hv, by simpa [hyEq] using hy⟩⟩

theorem outVertex_mem_of_inVertex_mem_splitCycle {g : GraphInput} {cycle : List Nat}
    (hCycle : DirectedCycle (splitGraph g) cycle) {u : Nat} (huIn : inVertex u ∈ cycle) :
    outVertex u ∈ cycle := by
  rcases hCycle with ⟨_hPos, _hNodup, _hBounds, hStep⟩
  rcases hStep (inVertex u) huIn with ⟨y, hy, hEdge⟩
  rcases splitGraph_edge_cases hEdge with hSplit | hCross
  · rcases hSplit with ⟨a, _ha, hTail, hHead⟩
    have hau : a = u := by
      apply inVertex_injective
      exact hTail.symm
    subst a
    simpa [hHead] using hy
  · rcases hCross with ⟨a, _b, _hEdge, _ha, _hb, hTail, _hHead⟩
    exact False.elim (inVertex_ne_outVertex u a hTail)

theorem projectedCycle_directedCycle_of_split {g : GraphInput} {cycle : List Nat}
    (hCycle : DirectedCycle (splitGraph g) cycle) :
    DirectedCycle g (projectedCycle g cycle) := by
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  have hCycle' : DirectedCycle (splitGraph g) cycle := ⟨hPos, hNodup, hBounds, hStep⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases exists_projectedCycle_mem_of_splitCycle hCycle' with ⟨u, hu⟩
    exact List.length_pos_of_mem hu
  · exact (List.nodup_range (n := g.vertices)).filter _
  · intro u hu
    exact (mem_projectedCycle_iff.1 hu).1
  · intro u huProj
    rcases mem_projectedCycle_iff.1 huProj with ⟨huBound, huIn⟩
    rcases hStep (inVertex u) huIn with ⟨y, hy, hEdgeIn⟩
    rcases splitGraph_edge_cases hEdgeIn with hSplitIn | hCrossIn
    · rcases hSplitIn with ⟨a, _ha, hTailIn, hHeadIn⟩
      have hau : a = u := by
        apply inVertex_injective
        exact hTailIn.symm
      subst a
      have huOut : outVertex u ∈ cycle := by
        simpa [hHeadIn] using hy
      rcases hStep (outVertex u) huOut with ⟨z, hz, hEdgeOut⟩
      rcases splitGraph_edge_cases hEdgeOut with hSplitOut | hCrossOut
      · rcases hSplitOut with ⟨a, _ha, hTailOut, _hHeadOut⟩
        exact False.elim (outVertex_ne_inVertex u a hTailOut)
      · rcases hCrossOut with ⟨a, b, hSourceEdge, _ha, hb, hTailOut, hHeadOut⟩
        have hau : a = u := by
          apply outVertex_injective
          exact hTailOut.symm
        subst a
        refine ⟨b, ?_, ?_⟩
        · exact mem_projectedCycle_iff.2 ⟨hb, by simpa [hHeadOut] using hz⟩
        · exact hSourceEdge
    · rcases hCrossIn with ⟨a, _b, _hSourceEdge, _ha, _hb, hTailIn, _hHeadIn⟩
      exact False.elim (inVertex_ne_outVertex u a hTailIn)

theorem normalizedVertices_length_le (removed : List (Nat × Nat)) :
    (normalizedVerticesOfArcs removed).length ≤ removed.length := by
  have hSub := List.dedup_sublist (removed.map fun e => e.1 / 2)
  simpa [normalizedVerticesOfArcs] using hSub.length_le

theorem normalizedVertices_nodup (removed : List (Nat × Nat)) :
    (normalizedVerticesOfArcs removed).Nodup := by
  simpa [normalizedVerticesOfArcs] using
    (List.nodup_dedup (removed.map fun e => e.1 / 2))

theorem tailSource_lt_of_mem_splitGraph_edges {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ (splitGraph g).edges) :
    e.1 / 2 < g.vertices := by
  rcases (mem_splitGraph_edges_iff (g := g) (e := e)).1 he with hSplit | hCross
  · rcases hSplit with ⟨u, hu, rfl⟩
    simpa [splitArc, inVertex_div_two] using hu
  · rcases hCross with ⟨a, _haEdge, haLeft, _haRight, rfl⟩
    simpa [crossArc, outVertex_div_two] using haLeft

theorem splitArc_not_removed_of_inVertex_mem_deleteSplitCycle
    {g : GraphInput} {removed : List Nat} {cycle : List Nat} {u : Nat}
    (hCycle : DirectedCycle (deleteArcs (splitGraph g) (removedSplitArcs removed)) cycle)
    (huIn : inVertex u ∈ cycle) :
    splitArc u ∉ removedSplitArcs removed := by
  rcases hCycle with ⟨_hPos, _hNodup, _hBounds, hStep⟩
  rcases hStep (inVertex u) huIn with ⟨y, _hy, hEdge⟩
  rcases (hasDirectedEdge_deleteArcs_iff.mp hEdge) with ⟨hEdgeOrig, hNotRemoved⟩
  rcases splitGraph_edge_cases hEdgeOrig with hSplit | hCross
  · rcases hSplit with ⟨a, _ha, hTail, hHead⟩
    have hua : u = a := inVertex_injective hTail
    subst a
    simpa [splitArc, hHead] using hNotRemoved
  · rcases hCross with ⟨a, _b, _hSourceEdge, _ha, _hb, hTail, _hHead⟩
    exact False.elim (inVertex_ne_outVertex u a hTail)

theorem splitArc_not_mem_of_not_normalized
    {removed : List (Nat × Nat)} {u : Nat}
    (hu : u ∉ normalizedVerticesOfArcs removed) :
    splitArc u ∉ removed := by
  intro hmem
  apply hu
  change u ∈ (removed.map fun e => e.1 / 2).dedup
  apply List.mem_dedup.mpr
  exact List.mem_map.mpr ⟨splitArc u, hmem, by simp [splitArc, inVertex_div_two]⟩

theorem crossArc_not_mem_of_not_normalized
    {removed : List (Nat × Nat)} {e : Nat × Nat}
    (hu : e.1 ∉ normalizedVerticesOfArcs removed) :
    crossArc e ∉ removed := by
  intro hmem
  apply hu
  change e.1 ∈ (removed.map fun f => f.1 / 2).dedup
  apply List.mem_dedup.mpr
  exact List.mem_map.mpr ⟨crossArc e, hmem, by simp [crossArc, outVertex_div_two]⟩

theorem expandedCycle_directedCycle_deleteArcs
    {g : GraphInput} {cycle : List Nat} {removed : List (Nat × Nat)}
    (hCycle : DirectedCycle g cycle)
    (hNoRemovedVertex : ∀ u ∈ cycle, u ∉ normalizedVerticesOfArcs removed) :
    DirectedCycle (deleteArcs (splitGraph g) removed) (expandedCycle cycle) := by
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  refine ⟨?_, expandedCycle_nodup hNodup, ?_, ?_⟩
  · simpa [expandedCycle] using hPos
  · intro x hx
    simpa [deleteArcs] using expandedCycle_withinBounds (g := g) hBounds x hx
  · intro x hx
    rcases mem_expandedCycle_iff.1 hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨outVertex u, outVertex_mem_expandedCycle hu, ?_⟩
      have hOrig : HasDirectedEdge (splitGraph g) (inVertex u) (outVertex u) := by
        simpa [HasDirectedEdge, splitArc] using
          splitArc_mem_splitGraph (g := g) (hBounds u hu)
      have hNot : (inVertex u, outVertex u) ∉ removed := by
        simpa [splitArc] using
          splitArc_not_mem_of_not_normalized (removed := removed) (u := u)
            (hNoRemovedVertex u hu)
      exact (hasDirectedEdge_deleteArcs_iff).2 ⟨hOrig, hNot⟩
    · rcases hStep u hu with ⟨v, hv, hEdge⟩
      refine ⟨inVertex v, inVertex_mem_expandedCycle hv, ?_⟩
      have hOrig : HasDirectedEdge (splitGraph g) (outVertex u) (inVertex v) := by
        simpa [HasDirectedEdge, crossArc] using
          crossArc_mem_splitGraph (g := g) (e := (u, v))
            hEdge (hBounds u hu) (hBounds v hv)
      have hNot : (outVertex u, inVertex v) ∉ removed := by
        simpa [crossArc] using
          crossArc_not_mem_of_not_normalized (removed := removed) (e := (u, v))
            (hNoRemovedVertex u hu)
      exact (hasDirectedEdge_deleteArcs_iff).2 ⟨hOrig, hNot⟩

theorem textbookMap_correct (I : FeedbackNodeSetInput) :
    feedbackNodeSetDecisionProblem.isYes I ↔ FeedbackArcSet (textbookMap I) := by
  change FeedbackNodeSet I ↔ FeedbackArcSet (textbookMap I)
  constructor
  · rintro ⟨removed, hLen, hWitness⟩
    rcases hWitness with ⟨_hNodup, hBounds, hHits⟩
    refine ⟨removedSplitArcs removed, by simpa [textbookMap, removedSplitArcs] using hLen, ?_⟩
    refine ⟨?_, ?_⟩
    · intro e he
      rcases List.mem_map.mp he with ⟨u, huRemoved, rfl⟩
      simpa [textbookMap] using
        splitArc_mem_splitGraph (g := I.graph) (hBounds u huRemoved)
    · intro cycle hCycle
      have hCycleSplit : DirectedCycle (splitGraph I.graph) cycle :=
        directedCycle_of_deleteArcs hCycle
      have hProjected : DirectedCycle I.graph (projectedCycle I.graph cycle) :=
        projectedCycle_directedCycle_of_split hCycleSplit
      rcases hHits (projectedCycle I.graph cycle) hProjected with
        ⟨u, huProjected, huRemoved⟩
      rcases mem_projectedCycle_iff.1 huProjected with ⟨_huBound, huIn⟩
      have hNotRemoved :=
        splitArc_not_removed_of_inVertex_mem_deleteSplitCycle
          (g := I.graph) (removed := removed) hCycle huIn
      exact hNotRemoved (List.mem_map.mpr ⟨u, huRemoved, rfl⟩)
  · rintro ⟨removedArcs, hLen, hWitness⟩
    rcases hWitness with ⟨hEdges, hNoCycle⟩
    let removedVertices := normalizedVerticesOfArcs removedArcs
    refine ⟨removedVertices, ?_, ?_⟩
    · exact (normalizedVertices_length_le removedArcs).trans
        (by simpa [textbookMap] using hLen)
    · refine ⟨normalizedVertices_nodup removedArcs, ?_, ?_⟩
      · intro u hu
        have huDedup : u ∈ (removedArcs.map fun e => e.1 / 2).dedup := by
          simpa [removedVertices, normalizedVerticesOfArcs] using hu
        have huMap : u ∈ removedArcs.map (fun e => e.1 / 2) :=
          List.mem_dedup.mp huDedup
        rcases List.mem_map.mp huMap with ⟨e, heRemoved, huEq⟩
        have hTailBound : e.1 / 2 < I.graph.vertices :=
          tailSource_lt_of_mem_splitGraph_edges (g := I.graph)
            (by simpa [textbookMap] using hEdges e heRemoved)
        simpa [huEq] using hTailBound
      · intro cycle hCycle
        by_contra hNoHit
        have hNoRemovedVertex : ∀ u ∈ cycle, u ∉ removedVertices := by
          intro u hu hur
          exact hNoHit ⟨u, hu, hur⟩
        have hExpanded :
            DirectedCycle (deleteArcs (splitGraph I.graph) removedArcs)
              (expandedCycle cycle) :=
          expandedCycle_directedCycle_deleteArcs hCycle (by
            intro u hu
            simpa [removedVertices] using hNoRemovedVertex u hu)
        have hExpanded' :
            DirectedCycle (deleteArcs (textbookMap I).graph removedArcs)
              (expandedCycle cycle) := by
          simpa [textbookMap] using hExpanded
        exact hNoCycle (expandedCycle cycle) hExpanded'

theorem splitArcs_length_eq (g : GraphInput) :
    (splitArcs g).length = g.vertices := by
  simp [splitArcs]

theorem boundedSourceEdges_length_le (g : GraphInput) :
    (boundedSourceEdges g).length ≤ g.edges.length := by
  simpa [boundedSourceEdges] using
    (VertexCover.filter_length_le
      (fun e : Nat × Nat => decide (e.1 < g.vertices ∧ e.2 < g.vertices)) g.edges)

theorem crossArcs_length_le (g : GraphInput) :
    (crossArcs g).length ≤ g.edges.length := by
  simpa [crossArcs] using boundedSourceEdges_length_le g

theorem splitGraph_edges_length_le (g : GraphInput) :
    (splitGraph g).edges.length ≤ g.vertices + g.edges.length := by
  simp [splitGraph, splitArcs_length_eq]
  exact crossArcs_length_le g

theorem edgeWithinBounds_of_mem_splitGraph_edges {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ (splitGraph g).edges) :
    EdgeWithinBounds (splitGraph g) e := by
  rcases (mem_splitGraph_edges_iff (g := g) (e := e)).1 he with hSplit | hCross
  · rcases hSplit with ⟨u, hu, rfl⟩
    exact ⟨inVertex_lt_split (g := g) hu, outVertex_lt_split (g := g) hu⟩
  · rcases hCross with ⟨a, _haEdge, haLeft, haRight, rfl⟩
    exact ⟨outVertex_lt_split (g := g) haLeft, inVertex_lt_split (g := g) haRight⟩

theorem edgeStructured_inputSize_le_of_mem_splitGraph_edges {g : GraphInput} {e : Nat × Nat}
    (he : e ∈ (splitGraph g).edges) :
    edgeStructuredEncodedType.inputSize e ≤ 4 * g.vertices + 1 := by
  have hBase :=
    VertexCover.edgeStructured_inputSize_le_of_bounds
      (g := splitGraph g) (e := e) (edgeWithinBounds_of_mem_splitGraph_edges he)
  exact hBase.trans (by simp [splitGraph]; omega)

theorem splitGraph_edges_structured_inputSize_le (g : GraphInput) :
    edgeListStructuredEncodedType.inputSize (splitGraph g).edges ≤
      (g.vertices + g.edges.length) * (4 * g.vertices + 2) := by
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (splitGraph g).edges (4 * g.vertices + 1) (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_splitGraph_edges he)
  have hLen := splitGraph_edges_length_le g
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (4 * g.vertices + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem feedbackArcSetStructured_inputSize_eq (I : FeedbackArcSetInput) :
    feedbackArcSetStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.k + 2 := by
  change feedbackArcSetTupleStructuredEncodedType.inputSize (I.graph, I.k) =
    graphStructuredEncodedType.inputSize I.graph + I.k + 2
  simp [feedbackArcSetTupleStructuredEncodedType]
  omega

theorem feedbackNodeSetStructured_inputSize_ge_vertices (I : FeedbackNodeSetInput) :
    I.graph.vertices ≤ feedbackNodeSetStructuredEncodedType.inputSize I := by
  rw [FeedbackNodeSet.feedbackNodeSetStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem feedbackNodeSetStructured_inputSize_ge_edges_length (I : FeedbackNodeSetInput) :
    I.graph.edges.length ≤ feedbackNodeSetStructuredEncodedType.inputSize I := by
  have hEdges :
      I.graph.edges.length ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeListStructuredEncodedType, EncodedType.inputSize] using
      (TM2Programs.listEncode_length_ge_length edgeStructuredEncodedType I.graph.edges)
  rw [FeedbackNodeSet.feedbackNodeSetStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem feedbackNodeSetStructured_inputSize_ge_budget (I : FeedbackNodeSetInput) :
    I.k ≤ feedbackNodeSetStructuredEncodedType.inputSize I := by
  rw [FeedbackNodeSet.feedbackNodeSetStructured_inputSize_eq]
  omega

theorem feedbackArcSetStructured_inputSize_textbookMap_le_feedbackNodeSet_poly
    (I : FeedbackNodeSetInput) :
    feedbackArcSetStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (feedbackNodeSetStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  let S := feedbackNodeSetStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using feedbackNodeSetStructured_inputSize_ge_vertices I
  have hEdgesLen : I.graph.edges.length ≤ S := by
    simpa [S] using feedbackNodeSetStructured_inputSize_ge_edges_length I
  have hBudget : I.k ≤ S := by
    simpa [S] using feedbackNodeSetStructured_inputSize_ge_budget I
  have hEdges := splitGraph_edges_structured_inputSize_le I.graph
  have hEdges' :
      edgeListStructuredEncodedType.inputSize (splitArcs I.graph ++ crossArcs I.graph) ≤
        (I.graph.vertices + I.graph.edges.length) * (4 * I.graph.vertices + 2) := by
    simpa [splitGraph] using hEdges
  have hEdgePoly :
      (I.graph.vertices + I.graph.edges.length) * (4 * I.graph.vertices + 2) ≤
        (2 * S) * (4 * S + 2) := by
    have hLeft : I.graph.vertices + I.graph.edges.length ≤ 2 * S := by omega
    have hRight : 4 * I.graph.vertices + 2 ≤ 4 * S + 2 := by omega
    exact Nat.mul_le_mul hLeft hRight
  have hCoarse :
      feedbackArcSetStructuredEncodedType.inputSize (textbookMap I) ≤
        2 * S + (2 * S) * (4 * S + 2) + 4 + S + 2 := by
    rw [feedbackArcSetStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
    simp [textbookMap, splitGraph]
    omega
  calc
    feedbackArcSetStructuredEncodedType.inputSize (textbookMap I) ≤
        2 * S + (2 * S) * (4 * S + 2) + 4 + S + 2 := hCoarse
    _ ≤ 1000 * S ^ 2 + 1000 := by
        cases S with
        | zero =>
            norm_num
        | succ S =>
            ring_nf
            omega

theorem feedbackNodeSetToFeedbackArcSetStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : FeedbackNodeSetInput => feedbackNodeSetStructuredEncodedType.inputSize I)
      (fun J : FeedbackArcSetInput => feedbackArcSetStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact feedbackArcSetStructured_inputSize_textbookMap_le_feedbackNodeSet_poly I

/-- Costed Karp reduction from Feedback Node Set to Feedback Arc Set. -/
noncomputable def feedbackNodeSetToFeedbackArcSetTMBackedKarpReduction :
    TMBackedCostedReduction feedbackNodeSetDecisionProblem feedbackArcSetDecisionProblem := by
  simpa [feedbackArcSetDecisionProblem, feedbackArcSetEncodedType] using
    rawCodomainTMBackedReduction
      feedbackNodeSetDecisionProblem
      Combinatorics.Graph.FeedbackArcSet
      map
      map_correct

/-- Costed Karp reduction from Feedback Node Set to Feedback Arc Set. -/
noncomputable def feedbackNodeSetToFeedbackArcSetKarpReduction :
    KarpReductionM CostedPolyTimeModel feedbackNodeSetDecisionProblem
      feedbackArcSetDecisionProblem :=
  feedbackNodeSetToFeedbackArcSetTMBackedKarpReduction.toCostedKarpReduction

/-- Costed Karp reduction from Feedback Node Set to Feedback Arc Set by node splitting. -/
noncomputable def feedbackNodeSetToFeedbackArcSet_textbookTMBackedKarpReduction :
    TMBackedCostedReduction feedbackNodeSetDecisionProblem feedbackArcSetDecisionProblem := by
  simpa [feedbackArcSetDecisionProblem, feedbackArcSetEncodedType] using
    rawCodomainTMBackedReduction
      feedbackNodeSetDecisionProblem
      Combinatorics.Graph.FeedbackArcSet
      textbookMap
      textbookMap_correct

/-- Costed Karp reduction from Feedback Node Set to Feedback Arc Set by node splitting. -/
noncomputable def feedbackNodeSetToFeedbackArcSet_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel feedbackNodeSetDecisionProblem
      feedbackArcSetDecisionProblem :=
  feedbackNodeSetToFeedbackArcSet_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- The structured finite-alphabet Feedback Arc Set encoding is faithful. -/
theorem feedbackArcSetStructuredEncoding_faithful :
    feedbackArcSetStructuredDecisionProblem.FaithfulEncoding where
  injective := feedbackArcSetStructuredEncodedType_encode_injective

theorem feedbackArcSetStructuredEncoding_predicateRespects :
    feedbackArcSetStructuredDecisionProblem.PredicateRespectsEncoding :=
  feedbackArcSetStructuredEncoding_faithful.predicateRespects

theorem feedbackArcSetStructuredEncoding_accepts_encode_iff (I : FeedbackArcSetInput) :
    feedbackArcSetStructuredDecisionProblem.toEncodedLanguage.accepts
        (feedbackArcSetStructuredEncodedType.encode I) ↔
      FeedbackArcSet I :=
  feedbackArcSetStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Feedback Arc Set is locally in NP for the project-local costed model. -/
theorem feedbackArcSetInNP :
    InNPEnc CostedPolyTimeModel feedbackArcSetDecisionProblem :=
  decidableInNP feedbackArcSetDecisionProblem

/-- Local NP-completeness of Feedback Arc Set via Feedback Node Set. -/
theorem feedbackArcSetNPComplete :
    NPCompleteEnc CostedPolyTimeModel feedbackArcSetDecisionProblem :=
  NPCompleteEnc.transfer
    FeedbackNodeSet.feedbackNodeSetNPComplete
    ⟨feedbackNodeSetToFeedbackArcSetKarpReduction⟩
    feedbackArcSetInNP

/-- Local NP-completeness of Feedback Arc Set via the P15u textbook node-splitting route. -/
theorem feedbackArcSet_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel feedbackArcSetDecisionProblem :=
  NPCompleteEnc.transfer
    FeedbackNodeSet.feedbackNodeSet_textbookNPComplete
    ⟨feedbackNodeSetToFeedbackArcSet_textbookKarpReduction⟩
    feedbackArcSetInNP

end FeedbackArcSet
end Karp21
end ComplexityReduction
