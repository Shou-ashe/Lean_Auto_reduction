/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.IR.Core.WellFormed

/-!
Bipartite incidence views over the universal relational carrier.
-/

namespace ComplexityReduction

/-- A two-sort incidence relation view over one `UniversalRelIR`. -/
structure IncidenceView (U : UniversalRelIR) where
  leftSort : SortId
  rightSort : SortId
  memRel : RelId
  left_wf : U.SortWF leftSort
  right_wf : U.SortWF rightSort
  mem_sig : U.relSig? memRel = some { arity := [leftSort, rightSort] }

namespace IncidenceView

def Mem {U : UniversalRelIR} (V : IncidenceView U) (l r : ObjId) : Prop :=
  U.RelHolds V.memRel [l, r]

def LeftObjects {U : UniversalRelIR} (V : IncidenceView U) : List ObjId :=
  U.objectsOfSort V.leftSort

def RightObjects {U : UniversalRelIR} (V : IncidenceView U) : List ObjId :=
  U.objectsOfSort V.rightSort

/--
Selected right objects form an exact cover of the left objects: each left object
is incident to exactly one selected right object.
-/
def ExactCoverPredicate {U : UniversalRelIR} (V : IncidenceView U)
    (selected : List ObjId) : Prop :=
  selected.Nodup ∧
    (∀ r ∈ selected, r ∈ V.RightObjects) ∧
    ∀ l ∈ V.LeftObjects,
      ∃ r ∈ selected,
        V.Mem l r ∧ ∀ r' ∈ selected, V.Mem l r' → r' = r

def ExistsExactCover {U : UniversalRelIR} (V : IncidenceView U) : Prop :=
  ∃ selected, V.ExactCoverPredicate selected

@[simp] theorem mem_leftObjects_iff {U : UniversalRelIR} (V : IncidenceView U)
    {l : ObjId} :
    l ∈ V.LeftObjects ↔ U.ObjWF V.leftSort l := by
  simp [LeftObjects]

@[simp] theorem mem_rightObjects_iff {U : UniversalRelIR} (V : IncidenceView U)
    {r : ObjId} :
    r ∈ V.RightObjects ↔ U.ObjWF V.rightSort r := by
  simp [RightObjects]

theorem mem_tuple_wf {U : UniversalRelIR} (V : IncidenceView U)
    (hU : U.WellFormed) {l r : ObjId} (h : V.Mem l r) :
    U.TupleWF { arity := [V.leftSort, V.rightSort] } [l, r] :=
  U.RelHolds_tuple_wf hU h V.mem_sig

end IncidenceView

end ComplexityReduction
