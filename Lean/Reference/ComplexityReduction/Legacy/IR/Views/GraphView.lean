/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.IR.Core.WellFormed

/-!
Graph-shaped views over the universal relational carrier.
-/

namespace ComplexityReduction

/-- A graph view over an IR carrier. Edge orientation policy is fixed by users of the view. -/
structure GraphView (U : UniversalRelIR) where
  vertexSort : SortId
  edgeRel : RelId
  vertex_wf : U.SortWF vertexSort
  edge_sig : U.relSig? edgeRel = some { arity := [vertexSort, vertexSort] }

namespace GraphView

def Vertices {U : UniversalRelIR} (V : GraphView U) : List ObjId :=
  U.objectsOfSort V.vertexSort

def Adjacent {U : UniversalRelIR} (V : GraphView U) (u v : ObjId) : Prop :=
  U.RelHolds V.edgeRel [u, v]

def AdjacentBool {U : UniversalRelIR} (V : GraphView U) (u v : ObjId) : Bool :=
  U.RelHoldsBool V.edgeRel [u, v]

def UndirectedAdjacent {U : UniversalRelIR} (V : GraphView U) (u v : ObjId) : Prop :=
  V.Adjacent u v ∨ V.Adjacent v u

def UndirectedAdjacentBool {U : UniversalRelIR} (V : GraphView U) (u v : ObjId) : Bool :=
  V.AdjacentBool u v || V.AdjacentBool v u

@[simp] theorem mem_vertices_iff {U : UniversalRelIR} (V : GraphView U)
    {v : ObjId} :
    v ∈ V.Vertices ↔ U.ObjWF V.vertexSort v := by
  simp [Vertices]

@[simp] theorem adjacentBool_eq_true_iff {U : UniversalRelIR} (V : GraphView U)
    {u v : ObjId} :
    V.AdjacentBool u v = true ↔ V.Adjacent u v := by
  simp [AdjacentBool, Adjacent]

@[simp] theorem undirectedAdjacentBool_eq_true_iff {U : UniversalRelIR}
    (V : GraphView U) {u v : ObjId} :
    V.UndirectedAdjacentBool u v = true ↔ V.UndirectedAdjacent u v := by
  simp [UndirectedAdjacentBool, UndirectedAdjacent]

theorem undirectedAdjacent_comm {U : UniversalRelIR} (V : GraphView U) (u v : ObjId) :
    V.UndirectedAdjacent u v ↔ V.UndirectedAdjacent v u := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem edge_tuple_wf {U : UniversalRelIR} (V : GraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    U.TupleWF { arity := [V.vertexSort, V.vertexSort] } [u, v] :=
  U.RelHolds_tuple_wf hU h V.edge_sig

theorem left_mem_of_adjacent {U : UniversalRelIR} (V : GraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    u ∈ V.Vertices := by
  have hTuple := V.edge_tuple_wf hU h
  have hLeft : U.ObjWF V.vertexSort u :=
    U.ObjWF_of_tuple_get? hTuple (k := 0) (s := V.vertexSort) (x := u)
      (by simp) (by simp)
  simpa [Vertices] using hLeft

theorem right_mem_of_adjacent {U : UniversalRelIR} (V : GraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    v ∈ V.Vertices := by
  have hTuple := V.edge_tuple_wf hU h
  have hRight : U.ObjWF V.vertexSort v :=
    U.ObjWF_of_tuple_get? hTuple (k := 1) (s := V.vertexSort) (x := v)
      (by simp) (by simp)
  simpa [Vertices] using hRight

theorem left_mem_of_undirectedAdjacent {U : UniversalRelIR} (V : GraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.UndirectedAdjacent u v) :
    u ∈ V.Vertices := by
  rcases h with h | h
  · exact V.left_mem_of_adjacent hU h
  · exact V.right_mem_of_adjacent hU h

theorem right_mem_of_undirectedAdjacent {U : UniversalRelIR} (V : GraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.UndirectedAdjacent u v) :
    v ∈ V.Vertices := by
  rcases h with h | h
  · exact V.right_mem_of_adjacent hU h
  · exact V.left_mem_of_adjacent hU h

end GraphView

end ComplexityReduction
