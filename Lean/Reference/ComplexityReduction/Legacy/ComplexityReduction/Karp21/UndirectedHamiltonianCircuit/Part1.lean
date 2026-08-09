/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

/-!
P15d/P15w graph target: Directed Hamiltonian Circuit to Undirected Hamiltonian Circuit.

The compatibility route preserves the P15d finite-witness discipline: bounded
directed Hamiltonian witnesses are enumerated and nonemptiness is represented by
a one-vertex undirected loop instance.  P15w uses the ordered undirected
Hamiltonian semantics installed here as the target for the standard replacement
gadget.
-/

namespace ComplexityReduction
namespace Karp21
namespace UndirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

theorem orderedUndirectedCycleSteps_of_isChain_closing {g : GraphInput} {cycle : List Nat}
    (hChain : cycle.IsChain fun a b => HasUndirectedEdge g a b)
    (hClosing : ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasUndirectedEdge g x y) :
    OrderedUndirectedCycleSteps g cycle := by
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

/-- `m` parallel self-loops on the single undirected vertex. -/
def loopEdges (m : Nat) : List (Nat × Nat) :=
  List.replicate m (0, 0)

/-- One-vertex undirected-Hamiltonian instance, satisfiable exactly when `m > 0`. -/
def loopInput (m : Nat) : UndirectedHamiltonianCircuitInput where
  graph :=
    { vertices := 1
      edges := loopEdges m
      directed := false }

theorem loopInput_correct (m : Nat) :
    UndirectedHamiltonianCircuit (loopInput m) ↔ 0 < m := by
  constructor
  · rintro ⟨_hUndirected, cycle, hCycle⟩
    rcases hCycle with ⟨hLen, _hNodup, _hBounds, hSteps⟩
    cases cycle with
    | nil =>
        simp [loopInput] at hLen
    | cons u rest =>
        cases rest with
        | nil =>
            have hEdge := hSteps ⟨0, by simp⟩
            rcases hEdge with hEdge | hEdge
            · have hEdge' : (u, u) ∈ loopEdges m := by
                simpa [loopInput] using hEdge
              have hLenPos : 0 < (loopEdges m).length := List.length_pos_of_mem hEdge'
              simpa [loopEdges] using hLenPos
            · have hEdge' : (u, u) ∈ loopEdges m := by
                simpa [loopInput] using hEdge
              have hLenPos : 0 < (loopEdges m).length := List.length_pos_of_mem hEdge'
              simpa [loopEdges] using hLenPos
        | cons v rest' =>
            simp [loopInput] at hLen
  · intro hm
    cases m with
    | zero =>
        omega
    | succ m =>
        refine ⟨rfl, [0], ?_⟩
        simp [OrderedUndirectedHamiltonianCycle, OrderedUndirectedCycleSteps,
          VerticesWithinBounds, HasUndirectedEdge, loopInput, loopEdges, cyclicSuccIndex]

/-- Canonical bounded ordered undirected-Hamiltonian witnesses for an input. -/
noncomputable def orderedUndirectedHamiltonianCircuitWitnesses
    (I : UndirectedHamiltonianCircuitInput) : List (List Nat) := by
  classical
  exact (DirectedHamiltonianCircuit.vertexListCandidates I.graph.vertices).filter fun cycle =>
    decide (I.graph.directed = false ∧ OrderedUndirectedHamiltonianCycle I.graph cycle)

theorem mem_orderedUndirectedHamiltonianCircuitWitnesses_iff
    (I : UndirectedHamiltonianCircuitInput) (cycle : List Nat) :
    cycle ∈ orderedUndirectedHamiltonianCircuitWitnesses I ↔
      cycle ∈ DirectedHamiltonianCircuit.vertexListCandidates I.graph.vertices ∧
        I.graph.directed = false ∧ OrderedUndirectedHamiltonianCycle I.graph cycle := by
  classical
  simp [orderedUndirectedHamiltonianCircuitWitnesses]

theorem orderedUndirectedHamiltonianCircuit_iff_witnesses_pos
    (I : UndirectedHamiltonianCircuitInput) :
    OrderedUndirectedHamiltonianCircuit I ↔
      0 < (orderedUndirectedHamiltonianCircuitWitnesses I).length := by
  constructor
  · rintro ⟨hUndirected, cycle, hCycle⟩
    rcases hCycle with ⟨hLen, hNodup, hBounds, hSteps⟩
    have hMemCandidates : cycle ∈
        DirectedHamiltonianCircuit.vertexListCandidates I.graph.vertices :=
      DirectedHamiltonianCircuit.mem_vertexListCandidates_of_length_bounds hLen hBounds
    have hMem : cycle ∈ orderedUndirectedHamiltonianCircuitWitnesses I :=
      (mem_orderedUndirectedHamiltonianCircuitWitnesses_iff I cycle).2
        ⟨hMemCandidates, hUndirected, hLen, hNodup, hBounds, hSteps⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : orderedUndirectedHamiltonianCircuitWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons cycle rest =>
        have hMem : cycle ∈ orderedUndirectedHamiltonianCircuitWitnesses I := by
          simp [hList]
        rcases (mem_orderedUndirectedHamiltonianCircuitWitnesses_iff I cycle).1 hMem with
          ⟨_hCandidate, hUndirected, hCycle⟩
        exact ⟨hUndirected, cycle, hCycle⟩

/-- Canonical bounded undirected-Hamiltonian witnesses for the public target predicate. -/
noncomputable def undirectedHamiltonianCircuitWitnesses
    (I : UndirectedHamiltonianCircuitInput) : List (List Nat) :=
  orderedUndirectedHamiltonianCircuitWitnesses I

theorem undirectedHamiltonianCircuit_iff_witnesses_pos
    (I : UndirectedHamiltonianCircuitInput) :
    UndirectedHamiltonianCircuit I ↔
      0 < (undirectedHamiltonianCircuitWitnesses I).length := by
  simpa [UndirectedHamiltonianCircuit, OrderedUndirectedHamiltonianCircuit,
    undirectedHamiltonianCircuitWitnesses] using
    orderedUndirectedHamiltonianCircuit_iff_witnesses_pos I

/-- In-vertex of the standard directed-to-undirected Hamiltonian replacement. -/
def inVertex (v : Nat) : Nat :=
  3 * v

/-- Middle vertex of the standard directed-to-undirected Hamiltonian replacement. -/
def midVertex (v : Nat) : Nat :=
  3 * v + 1

/-- Out-vertex of the standard directed-to-undirected Hamiltonian replacement. -/
def outVertex (v : Nat) : Nat :=
  3 * v + 2

/-- The three-vertex path replacing one directed source vertex. -/
def replacementBlock (v : Nat) : List Nat :=
  [inVertex v, midVertex v, outVertex v]

/-- Vertex count of the standard replacement graph. -/
def textbookVertexCount (I : DirectedHamiltonianCircuitInput) : Nat :=
  3 * I.graph.vertices

/-- Internal path edges for one replacement block. -/
def internalEdgesForVertex (v : Nat) : List (Nat × Nat) :=
  [(inVertex v, midVertex v), (midVertex v, outVertex v)]

/-- All internal path edges in the standard replacement graph. -/
def textbookInternalEdges (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  (List.range I.graph.vertices).flatMap internalEdgesForVertex

/-- Cross edge corresponding to one source directed edge. -/
def crossEdgeOfDirectedEdge (e : Nat × Nat) : Nat × Nat :=
  (outVertex e.1, inVertex e.2)

/-- All source-edge cross edges in the standard replacement graph. -/
def textbookCrossEdges (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  I.graph.edges.map crossEdgeOfDirectedEdge

/-- Edge list for the standard directed-to-undirected Hamiltonian replacement. -/
def textbookEdgeList (I : DirectedHamiltonianCircuitInput) : List (Nat × Nat) :=
  textbookInternalEdges I ++ textbookCrossEdges I

/-- P15w standard replacement map from directed to undirected Hamiltonian circuit. -/
def textbookMap (I : DirectedHamiltonianCircuitInput) : UndirectedHamiltonianCircuitInput where
  graph :=
    { vertices := textbookVertexCount I
      edges := textbookEdgeList I
      directed := false }

/-- Lift a directed Hamiltonian vertex cycle through the replacement blocks. -/
def liftedCycle (cycle : List Nat) : List Nat :=
  cycle.flatMap replacementBlock

theorem replacementBlock_length (v : Nat) :
    (replacementBlock v).length = 3 := by
  rfl

theorem liftedCycle_length (cycle : List Nat) :
    (liftedCycle cycle).length = 3 * cycle.length := by
  simp [liftedCycle, replacementBlock, Nat.mul_comm]

theorem replacementBlock_nodup (v : Nat) :
    (replacementBlock v).Nodup := by
  simp [replacementBlock, inVertex, midVertex, outVertex]

theorem replacementBlock_disjoint_of_ne {u v : Nat} (huv : u ≠ v) :
    List.Disjoint (replacementBlock u) (replacementBlock v) := by
  intro x hx hy
  simp [replacementBlock, inVertex, midVertex, outVertex] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with hy | hy | hy <;> omega

theorem replacementBlock_withinBounds {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hv : v < I.graph.vertices) (hx : x ∈ replacementBlock v) :
    x < textbookVertexCount I := by
  simp [replacementBlock, inVertex, midVertex, outVertex, textbookVertexCount] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> omega

theorem liftedCycle_nodup {cycle : List Nat} (hNodup : cycle.Nodup) :
    (liftedCycle cycle).Nodup := by
  classical
  unfold liftedCycle
  have hLocal : ∀ v ∈ cycle, (replacementBlock v).Nodup := by
    intro v _hv
    exact replacementBlock_nodup v
  have hPair :
      cycle.Pairwise fun u v => List.Disjoint (replacementBlock u) (replacementBlock v) := by
    exact hNodup.pairwise_of_forall_ne fun u _hu v _hv huv =>
      replacementBlock_disjoint_of_ne huv
  have hFlat := (List.nodup_flatMap (l₁ := cycle) (f := replacementBlock)).2
    ⟨hLocal, hPair⟩
  simpa [List.flatMap] using hFlat

theorem liftedCycle_withinBounds {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hBounds : VerticesWithinBounds I.graph cycle) :
    VerticesWithinBounds (textbookMap I).graph (liftedCycle cycle) := by
  intro x hx
  rcases List.mem_flatMap.mp hx with ⟨v, hvCycle, hxBlock⟩
  exact replacementBlock_withinBounds (I := I) (hBounds v hvCycle) hxBlock

theorem mem_textbookEdgeList_internal_in_mid {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    (inVertex v, midVertex v) ∈ textbookEdgeList I := by
  unfold textbookEdgeList textbookInternalEdges internalEdgesForVertex
  exact List.mem_append.mpr
    (Or.inl (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, by simp⟩))

theorem mem_textbookEdgeList_internal_mid_out {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    (midVertex v, outVertex v) ∈ textbookEdgeList I := by
  unfold textbookEdgeList textbookInternalEdges internalEdgesForVertex
  exact List.mem_append.mpr
    (Or.inl (List.mem_flatMap.mpr ⟨v, List.mem_range.mpr hv, by simp⟩))

theorem mem_textbookEdgeList_cross {I : DirectedHamiltonianCircuitInput} {u v : Nat}
    (hEdge : HasDirectedEdge I.graph u v) :
    (outVertex u, inVertex v) ∈ textbookEdgeList I := by
  unfold textbookEdgeList textbookCrossEdges crossEdgeOfDirectedEdge
  exact List.mem_append.mpr
    (Or.inr (List.mem_map.mpr ⟨(u, v), by simpa [HasDirectedEdge] using hEdge, rfl⟩))

theorem has_textbook_internal_in_mid {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    HasUndirectedEdge (textbookMap I).graph (inVertex v) (midVertex v) :=
  Or.inl (mem_textbookEdgeList_internal_in_mid (I := I) hv)

theorem has_textbook_internal_mid_out {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    HasUndirectedEdge (textbookMap I).graph (midVertex v) (outVertex v) :=
  Or.inl (mem_textbookEdgeList_internal_mid_out (I := I) hv)

theorem has_textbook_cross {I : DirectedHamiltonianCircuitInput} {u v : Nat}
    (hEdge : HasDirectedEdge I.graph u v) :
    HasUndirectedEdge (textbookMap I).graph (outVertex u) (inVertex v) :=
  Or.inl (mem_textbookEdgeList_cross (I := I) hEdge)

theorem replacementBlock_edgeChain {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    (replacementBlock v).IsChain fun a b => HasUndirectedEdge (textbookMap I).graph a b := by
  rw [List.isChain_iff_getElem]
  intro n hn
  have hnCases : n = 0 ∨ n = 1 := by
    simp [replacementBlock] at hn
    omega
  rcases hnCases with rfl | rfl
  · simpa [replacementBlock] using has_textbook_internal_in_mid (I := I) hv
  · simpa [replacementBlock] using has_textbook_internal_mid_out (I := I) hv

theorem directedCycle_edgeChain {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    cycle.IsChain fun u v => HasDirectedEdge I.graph u v := by
  rw [List.isChain_iff_getElem]
  intro n hn
  have hnLt : n < cycle.length := by omega
  let i : Fin cycle.length := ⟨n, hnLt⟩
  have hSuccIndex : cyclicSuccIndex i = ⟨n + 1, hn⟩ := by
    ext
    simp [i, cyclicSuccIndex, Nat.mod_eq_of_lt hn]
  simpa [i, hSuccIndex] using hCycle.2.2.2 i

theorem liftedCycle_edgeChain {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    (liftedCycle cycle).IsChain fun a b => HasUndirectedEdge (textbookMap I).graph a b := by
  classical
  unfold liftedCycle
  let blocks : List (List Nat) := cycle.map replacementBlock
  have hNoNil : [] ∉ blocks := by
    intro hNil
    rcases List.mem_map.mp hNil with ⟨v, _hv, hEq⟩
    simp [replacementBlock] at hEq
  have hFlatten :
      blocks.flatten.IsChain fun a b => HasUndirectedEdge (textbookMap I).graph a b := by
    rw [List.isChain_flatten hNoNil]
    constructor
    · intro block hBlock
      rcases List.mem_map.mp hBlock with ⟨v, hvCycle, rfl⟩
      exact replacementBlock_edgeChain (I := I) (hCycle.2.2.1 v hvCycle)
    · rw [List.isChain_map]
      exact (directedCycle_edgeChain hCycle).imp fun u v hEdge => by
        intro x hx y hy
        simp [replacementBlock] at hx hy
        subst x
        subst y
        exact has_textbook_cross (I := I) hEdge
  simpa [blocks] using hFlatten

theorem liftedCycle_core {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    (liftedCycle cycle).length = (textbookMap I).graph.vertices ∧
      (liftedCycle cycle).Nodup ∧
      VerticesWithinBounds (textbookMap I).graph (liftedCycle cycle) := by
  rcases hCycle with ⟨hLen, hNodup, hBounds, _hSteps⟩
  refine ⟨?_, liftedCycle_nodup hNodup, liftedCycle_withinBounds hBounds⟩
  simp [textbookMap, textbookVertexCount, liftedCycle_length, hLen]

theorem liftedCycle_head?_cons (v : Nat) (rest : List Nat) :
    (liftedCycle (v :: rest)).head? = some (inVertex v) := by
  simp [liftedCycle, replacementBlock]

theorem liftedCycle_getLast?_of_getLast? :
    ∀ {cycle : List Nat} {v : Nat}, cycle.getLast? = some v →
      (liftedCycle cycle).getLast? = some (outVertex v)
  | [], _v, hLast => by
      simp at hLast
  | [u], v, hLast => by
      simp [liftedCycle, replacementBlock] at hLast ⊢
      subst v
      rfl
  | u :: w :: rest, v, hLast => by
      have hTail : (w :: rest).getLast? = some v := by
        simpa using hLast
      have hLift := liftedCycle_getLast?_of_getLast? hTail
      have hTailNe : liftedCycle (w :: rest) ≠ [] := by
        simp [liftedCycle, replacementBlock]
      rw [liftedCycle]
      change (replacementBlock u ++ liftedCycle (w :: rest)).getLast? = some (outVertex v)
      rw [List.getLast?_append_of_ne_nil (replacementBlock u) hTailNe]
      exact hLift

theorem directedCycle_cyclicClosingEdge {I : DirectedHamiltonianCircuitInput}
    {cycle : List Nat} (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    ∀ x ∈ cycle.getLast?, ∀ y ∈ cycle.head?, HasDirectedEdge I.graph x y := by
  intro x hx y hy
  have hLenPos : 0 < cycle.length := by
    cases cycle with
    | nil =>
        simp at hx
    | cons _ _ =>
        simp
  have hLastLt : cycle.length - 1 < cycle.length := by omega
  have hne : cycle ≠ [] := List.ne_nil_of_length_pos hLenPos
  have hxEq : cycle.get ⟨cycle.length - 1, hLastLt⟩ = x := by
    rw [List.get_length_sub_one hLastLt]
    simpa [List.getLast?_eq_getLast_of_ne_nil hne] using hx
  have hyEq : cycle.get ⟨0, hLenPos⟩ = y := by
    simpa [List.head?_eq_some_head hne, List.head_eq_getElem_zero hne] using hy
  have hSuccIndex :
      cyclicSuccIndex (cycle := cycle) ⟨cycle.length - 1, hLastLt⟩ = ⟨0, hLenPos⟩ := by
      ext
      simp [cyclicSuccIndex]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLenPos)]
      exact Nat.mod_self cycle.length
  have hEdge := hCycle.2.2.2 ⟨cycle.length - 1, hLastLt⟩
  rw [hSuccIndex] at hEdge
  rw [hxEq, hyEq] at hEdge
  exact hEdge

theorem liftedCycle_cyclicClosingEdge {I : DirectedHamiltonianCircuitInput}
    {cycle : List Nat} (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    ∀ x ∈ (liftedCycle cycle).getLast?, ∀ y ∈ (liftedCycle cycle).head?,
      HasUndirectedEdge (textbookMap I).graph x y := by
  intro x hx y hy
  cases cycle with
  | nil =>
      simp [liftedCycle] at hx
  | cons first rest =>
      have hSourceNe : first :: rest ≠ [] := by simp
      let last := (first :: rest).getLast hSourceNe
      have hLastSource : (first :: rest).getLast? = some last := by
        simp [last, List.getLast?_eq_getLast_of_ne_nil hSourceNe]
      have hLastLift := liftedCycle_getLast?_of_getLast? hLastSource
      have hxEq : outVertex last = x := by
        simpa [hLastLift] using hx
      have hHeadLift := liftedCycle_head?_cons first rest
      have hyEq : inVertex first = y := by
        simpa [hHeadLift] using hy
      have hHeadSource : first ∈ (first :: rest).head? := by
        simp
      have hSourceEdge : HasDirectedEdge I.graph last first :=
        directedCycle_cyclicClosingEdge hCycle last (by simp [hLastSource]) first hHeadSource
      simpa [hxEq, hyEq] using has_textbook_cross (I := I) hSourceEdge

theorem liftedCycle_orderedHamiltonianCycle {I : DirectedHamiltonianCircuitInput}
    {cycle : List Nat} (hCycle : OrderedDirectedHamiltonianCycle I.graph cycle) :
    OrderedUndirectedHamiltonianCycle (textbookMap I).graph (liftedCycle cycle) := by
  rcases liftedCycle_core hCycle with ⟨hLen, hNodup, hBounds⟩
  exact ⟨hLen, hNodup, hBounds,
    orderedUndirectedCycleSteps_of_isChain_closing
      (liftedCycle_edgeChain hCycle)
      (liftedCycle_cyclicClosingEdge hCycle)⟩

theorem textbookMap_uhc_of_directedHamiltonianCircuit {I : DirectedHamiltonianCircuitInput}
    (hDHC : DirectedHamiltonianCircuit I) :
    UndirectedHamiltonianCircuit (textbookMap I) := by
  rcases hDHC with ⟨_hDirected, cycle, hCycle⟩
  exact ⟨rfl, liftedCycle cycle, liftedCycle_orderedHamiltonianCycle hCycle⟩

theorem mem_textbookEdgeList_mid_left {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (midVertex v, x) ∈ textbookEdgeList I) :
    x = outVertex v := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hFirst : midVertex v = inVertex u := hPair.1
      unfold inVertex midVertex at hFirst
      omega
    · have hFirst : midVertex v = midVertex u := hPair.1
      have hSecond : x = outVertex u := hPair.2
      have huv : u = v := by
        unfold midVertex at hFirst
        omega
      subst u
      exact hSecond
  · rcases List.mem_map.mp hCross with ⟨e, _he, hPair⟩
    cases e with
    | mk u w =>
        have hFirst : outVertex u = midVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.fst hPair
        unfold midVertex outVertex at hFirst
        omega

theorem mem_textbookEdgeList_mid_right {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (x, midVertex v) ∈ textbookEdgeList I) :
    x = inVertex v := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hFirst : x = inVertex u := hPair.1
      have hSecond : midVertex v = midVertex u := hPair.2
      have huv : u = v := by
        unfold midVertex at hSecond
        omega
      subst u
      exact hFirst
    · have hSecond : midVertex v = outVertex u := hPair.2
      unfold midVertex outVertex at hSecond
      omega
  · rcases List.mem_map.mp hCross with ⟨e, _he, hPair⟩
    cases e with
    | mk u w =>
        have hSecond : inVertex w = midVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.snd hPair
        unfold inVertex midVertex at hSecond
        omega

theorem textbook_mid_neighbor_choice {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : HasUndirectedEdge (textbookMap I).graph (midVertex v) x) :
    x = inVertex v ∨ x = outVertex v := by
  rcases hEdge with hEdge | hEdge
  · exact Or.inr (mem_textbookEdgeList_mid_left hEdge)
  · exact Or.inl (mem_textbookEdgeList_mid_right hEdge)

theorem hasUndirectedEdge_symm {g : GraphInput} {u v : Nat}
    (hEdge : HasUndirectedEdge g u v) :
    HasUndirectedEdge g v u := by
  rcases hEdge with hEdge | hEdge
  · exact Or.inr hEdge
  · exact Or.inl hEdge

theorem orderedUndirectedCycle_edge_to_cycleSuccessor
    {g : GraphInput} {cycle : List Nat} {v : Nat}
    (hSteps : OrderedUndirectedCycleSteps g cycle) (hv : v ∈ cycle) :
    HasUndirectedEdge g v (DirectedHamiltonianCircuit.cycleSuccessor cycle v) := by
  classical
  have hIdx : cycle.idxOf v < cycle.length := List.idxOf_lt_length_iff.mpr hv
  have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le _) hIdx
  let i : Fin cycle.length := ⟨cycle.idxOf v, hIdx⟩
  have hGet : cycle.get i = v := by
    simp [i, List.getElem_idxOf hIdx]
  have hSucc :
      cyclicSuccIndex (cycle := cycle) i =
        ⟨(cycle.idxOf v + 1) % cycle.length, Nat.mod_lt _ hLen⟩ := by
    rfl
  have hEdge := hSteps i
  rw [hGet, hSucc] at hEdge
  simpa [DirectedHamiltonianCircuit.cycleSuccessor, hLen] using hEdge

theorem orderedUndirectedCycle_exists_predecessor_successor
    {g : GraphInput} {cycle : List Nat} {v : Nat}
    (hNodup : cycle.Nodup) (hSteps : OrderedUndirectedCycleSteps g cycle) (hv : v ∈ cycle) :
    ∃ u, u ∈ cycle ∧ DirectedHamiltonianCircuit.cycleSuccessor cycle u = v ∧
      HasUndirectedEdge g u v := by
  rcases List.mem_iff_get.mp hv with ⟨i, rfl⟩
  by_cases hiZero : i.val = 0
  · have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    let last : Fin cycle.length := ⟨cycle.length - 1, by omega⟩
    refine ⟨cycle.get last, List.get_mem _ _, ?_, ?_⟩
    · have hIdxOf : cycle.idxOf (cycle.get last) = last.val := by
        exact hNodup.idxOf_getElem last.val last.isLt
      have hSucc : cyclicSuccIndex (cycle := cycle) last = i := by
        ext
        simp [cyclicSuccIndex, last, hiZero]
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLen)]
        exact Nat.mod_self cycle.length
      have hGetSucc :
          cycle.get
              ⟨(cycle.idxOf (cycle.get last) + 1) % cycle.length,
                Nat.mod_lt _ hLen⟩ =
            cycle.get i := by
        rw [hIdxOf]
        exact congrArg (fun j : Fin cycle.length => cycle.get j) hSucc
      simpa [DirectedHamiltonianCircuit.cycleSuccessor, hLen] using hGetSucc
    · have hSucc : cyclicSuccIndex (cycle := cycle) last = i := by
        ext
        simp [cyclicSuccIndex, last, hiZero]
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLen)]
        exact Nat.mod_self cycle.length
      simpa [hSucc] using hSteps last
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hiZero
    let pred : Fin cycle.length := ⟨i.val - 1, by omega⟩
    refine ⟨cycle.get pred, List.get_mem _ _, ?_, ?_⟩
    · have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have hIdxOf : cycle.idxOf (cycle.get pred) = pred.val := by
        exact hNodup.idxOf_getElem pred.val pred.isLt
      have hSucc : cyclicSuccIndex (cycle := cycle) pred = i := by
        ext
        simp [cyclicSuccIndex, pred]
        have hPredSucc : i.val - 1 + 1 = i.val :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hiPos)
        rw [hPredSucc]
        exact Nat.mod_eq_of_lt i.isLt
      have hGetSucc :
          cycle.get
              ⟨(cycle.idxOf (cycle.get pred) + 1) % cycle.length,
                Nat.mod_lt _ hLen⟩ =
            cycle.get i := by
        rw [hIdxOf]
        exact congrArg (fun j : Fin cycle.length => cycle.get j) hSucc
      simpa [DirectedHamiltonianCircuit.cycleSuccessor, hLen] using hGetSucc
    · have hSucc : cyclicSuccIndex (cycle := cycle) pred = i := by
        ext
        simp [cyclicSuccIndex, pred]
        have hPredSucc : i.val - 1 + 1 = i.val :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hiPos)
        rw [hPredSucc]
        exact Nat.mod_eq_of_lt i.isLt
      simpa [hSucc] using hSteps pred

theorem orderedUndirectedHamiltonianCycle_mem_of_lt
    {g : GraphInput} {cycle : List Nat}
    (h : OrderedUndirectedHamiltonianCycle g cycle) {v : Nat} (hv : v < g.vertices) :
    v ∈ cycle :=
  mem_of_verticesWithinBounds_length_nodup h.1 h.2.1 h.2.2.1 hv

theorem mem_textbookEdgeList_in_left {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (inVertex v, x) ∈ textbookEdgeList I) :
    x = midVertex v := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hFirst : inVertex v = inVertex u := hPair.1
      have hSecond : x = midVertex u := hPair.2
      have huv : u = v := by
        unfold inVertex at hFirst
        omega
      subst u
      exact hSecond
    · have hFirst : inVertex v = midVertex u := hPair.1
      unfold inVertex midVertex at hFirst
      omega
  · rcases List.mem_map.mp hCross with ⟨e, _he, hPair⟩
    cases e with
    | mk u w =>
        have hFirst : outVertex u = inVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.fst hPair
        unfold inVertex outVertex at hFirst
        omega

theorem mem_textbookEdgeList_in_right {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (x, inVertex v) ∈ textbookEdgeList I) :
    (x = midVertex v) ∨ ∃ u, HasDirectedEdge I.graph u v ∧ x = outVertex u := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hSecond : inVertex v = midVertex u := hPair.2
      unfold inVertex midVertex at hSecond
      omega
    · have hSecond : inVertex v = outVertex u := hPair.2
      unfold inVertex outVertex at hSecond
      omega
  · rcases List.mem_map.mp hCross with ⟨e, he, hPair⟩
    cases e with
    | mk u w =>
        have hFirst : x = outVertex u := by
          simpa [crossEdgeOfDirectedEdge] using (congrArg Prod.fst hPair).symm
        have hSecond : inVertex w = inVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.snd hPair
        have hwv : w = v := by
          unfold inVertex at hSecond
          omega
        subst w
        exact Or.inr ⟨u, by simpa [HasDirectedEdge] using he, hFirst⟩

theorem textbook_in_neighbor_choice {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : HasUndirectedEdge (textbookMap I).graph (inVertex v) x) :
    x = midVertex v ∨ ∃ u, HasDirectedEdge I.graph u v ∧ x = outVertex u := by
  rcases hEdge with hEdge | hEdge
  · exact Or.inl (mem_textbookEdgeList_in_left hEdge)
  · exact mem_textbookEdgeList_in_right hEdge

theorem mem_textbookEdgeList_out_left {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (outVertex v, x) ∈ textbookEdgeList I) :
    (x = midVertex v) ∨ ∃ w, HasDirectedEdge I.graph v w ∧ x = inVertex w := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hFirst : outVertex v = inVertex u := hPair.1
      unfold inVertex outVertex at hFirst
      omega
    · have hFirst : outVertex v = midVertex u := hPair.1
      unfold midVertex outVertex at hFirst
      omega
  · rcases List.mem_map.mp hCross with ⟨e, he, hPair⟩
    cases e with
    | mk u w =>
        have hFirst : outVertex u = outVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.fst hPair
        have huv : u = v := by
          unfold outVertex at hFirst
          omega
        have hSecond : x = inVertex w := by
          simpa [crossEdgeOfDirectedEdge] using (congrArg Prod.snd hPair).symm
        subst u
        exact Or.inr ⟨w, by simpa [HasDirectedEdge] using he, hSecond⟩

theorem mem_textbookEdgeList_out_right {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : (x, outVertex v) ∈ textbookEdgeList I) :
    x = midVertex v := by
  unfold textbookEdgeList textbookInternalEdges textbookCrossEdges at hEdge
  rcases List.mem_append.mp hEdge with hInternal | hCross
  · rcases List.mem_flatMap.mp hInternal with ⟨u, _hu, hPair⟩
    simp [internalEdgesForVertex] at hPair
    rcases hPair with hPair | hPair
    · have hSecond : outVertex v = midVertex u := hPair.2
      unfold midVertex outVertex at hSecond
      omega
    · have hFirst : x = midVertex u := hPair.1
      have hSecond : outVertex v = outVertex u := hPair.2
      have huv : u = v := by
        unfold outVertex at hSecond
        omega
      subst u
      exact hFirst
  · rcases List.mem_map.mp hCross with ⟨e, _he, hPair⟩
    cases e with
    | mk u w =>
        have hSecond : inVertex w = outVertex v := by
          simpa [crossEdgeOfDirectedEdge] using congrArg Prod.snd hPair
        unfold inVertex outVertex at hSecond
        omega

theorem textbook_out_neighbor_choice {I : DirectedHamiltonianCircuitInput} {v x : Nat}
    (hEdge : HasUndirectedEdge (textbookMap I).graph (outVertex v) x) :
    x = midVertex v ∨ ∃ w, HasDirectedEdge I.graph v w ∧ x = inVertex w := by
  rcases hEdge with hEdge | hEdge
  · exact mem_textbookEdgeList_out_left hEdge
  · exact Or.inl (mem_textbookEdgeList_out_right hEdge)

theorem inVertex_lt_textbookVertexCount {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    inVertex v < textbookVertexCount I := by
  unfold inVertex textbookVertexCount
  omega

theorem midVertex_lt_textbookVertexCount {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    midVertex v < textbookVertexCount I := by
  unfold midVertex textbookVertexCount
  omega

theorem outVertex_lt_textbookVertexCount {I : DirectedHamiltonianCircuitInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    outVertex v < textbookVertexCount I := by
  unfold outVertex textbookVertexCount
  omega

theorem inVertex_mem_of_orderedUHC
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    inVertex v ∈ cycle := by
  exact orderedUndirectedHamiltonianCycle_mem_of_lt hCycle
    (by simpa [textbookMap] using inVertex_lt_textbookVertexCount (I := I) hv)

theorem midVertex_mem_of_orderedUHC
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    midVertex v ∈ cycle := by
  exact orderedUndirectedHamiltonianCycle_mem_of_lt hCycle
    (by simpa [textbookMap] using midVertex_lt_textbookVertexCount (I := I) hv)

theorem outVertex_mem_of_orderedUHC
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    outVertex v ∈ cycle := by
  exact orderedUndirectedHamiltonianCycle_mem_of_lt hCycle
    (by simpa [textbookMap] using outVertex_lt_textbookVertexCount (I := I) hv)

theorem cycleSuccessor_mid_choice
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = inVertex v ∨
      DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = outVertex v := by
  have hMem := midVertex_mem_of_orderedUHC hCycle hv
  have hEdge :=
    orderedUndirectedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hMem
  exact textbook_mid_neighbor_choice hEdge

theorem cyclePredecessor_mid_choice
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    ∃ p, p ∈ cycle ∧ DirectedHamiltonianCircuit.cycleSuccessor cycle p = midVertex v ∧
      (p = inVertex v ∨ p = outVertex v) := by
  have hMem := midVertex_mem_of_orderedUHC hCycle hv
  rcases orderedUndirectedCycle_exists_predecessor_successor
      hCycle.2.1 hCycle.2.2.2 hMem with
    ⟨p, hpMem, hpSucc, hpEdge⟩
  refine ⟨p, hpMem, hpSucc, ?_⟩
  exact textbook_mid_neighbor_choice (hasUndirectedEdge_symm hpEdge)

theorem cycleSuccessor_mid_out_forces_in_predecessor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices)
    (hSucc : DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = outVertex v) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = midVertex v := by
  rcases cyclePredecessor_mid_choice hCycle hv with ⟨p, hpMem, hpSucc, hpClass⟩
  rcases hpClass with hpIn | hpOut
  · simpa [hpIn] using hpSucc
  · subst p
    have hInMem := inVertex_mem_of_orderedUHC hCycle hv
    have hMidMem := midVertex_mem_of_orderedUHC hCycle hv
    have hOutMem := outVertex_mem_of_orderedUHC hCycle hv
    have hOutNeMid : outVertex v ≠ midVertex v := by
      unfold outVertex midVertex
      omega
    have hInNeOut : inVertex v ≠ outVertex v := by
      unfold inVertex outVertex
      omega
    have hInNeMid : inVertex v ≠ midVertex v := by
      unfold inVertex midVertex
      omega
    exact False.elim
      (DirectedHamiltonianCircuit.cycleSuccessor_two_cycle_no_extra
        hCycle.2.1 hOutMem hMidMem hInMem hOutNeMid hInNeOut hInNeMid hpSucc hSucc)

theorem cycleSuccessor_mid_in_forces_out_predecessor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices)
    (hSucc : DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = inVertex v) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex v) = midVertex v := by
  rcases cyclePredecessor_mid_choice hCycle hv with ⟨p, hpMem, hpSucc, hpClass⟩
  rcases hpClass with hpIn | hpOut
  · subst p
    have hInMem := inVertex_mem_of_orderedUHC hCycle hv
    have hMidMem := midVertex_mem_of_orderedUHC hCycle hv
    have hOutMem := outVertex_mem_of_orderedUHC hCycle hv
    have hInNeMid : inVertex v ≠ midVertex v := by
      unfold inVertex midVertex
      omega
    have hOutNeIn : outVertex v ≠ inVertex v := by
      unfold inVertex outVertex
      omega
    have hOutNeMid : outVertex v ≠ midVertex v := by
      unfold midVertex outVertex
      omega
    exact False.elim
      (DirectedHamiltonianCircuit.cycleSuccessor_two_cycle_no_extra
        hCycle.2.1 hInMem hMidMem hOutMem hInNeMid hOutNeIn hOutNeMid hpSucc hSucc)
  · simpa [hpOut] using hpSucc

theorem replacementBlock_forced_orientation
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    (DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = midVertex v ∧
        DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = outVertex v) ∨
      (DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex v) = midVertex v ∧
        DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = inVertex v) := by
  rcases cycleSuccessor_mid_choice hCycle hv with hSuccIn | hSuccOut
  · exact Or.inr ⟨cycleSuccessor_mid_in_forces_out_predecessor hCycle hv hSuccIn, hSuccIn⟩
  · exact Or.inl ⟨cycleSuccessor_mid_out_forces_in_predecessor hCycle hv hSuccOut, hSuccOut⟩

def BlockForward (cycle : List Nat) (v : Nat) : Prop :=
  DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = midVertex v ∧
    DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = outVertex v

def BlockReverse (cycle : List Nat) (v : Nat) : Prop :=
  DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex v) = midVertex v ∧
    DirectedHamiltonianCircuit.cycleSuccessor cycle (midVertex v) = inVertex v

theorem replacementBlock_forced_orientation'
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) :
    BlockForward cycle v ∨ BlockReverse cycle v := by
  simpa [BlockForward, BlockReverse] using replacementBlock_forced_orientation hCycle hv

end UndirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
