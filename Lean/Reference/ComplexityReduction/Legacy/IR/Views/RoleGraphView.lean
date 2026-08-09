/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.IR.Views.GraphView

/-!
Role-preserving graph views for gadget schemas.
-/

namespace ComplexityReduction

/-- Graph view with a separate vertex-role relation. -/
structure RoleGraphView (U : UniversalRelIR) where
  vertexSort : SortId
  roleSort : SortId
  edgeRel : RelId
  roleRel : RelId
  vertex_wf : U.SortWF vertexSort
  role_wf : U.SortWF roleSort
  edge_sig : U.relSig? edgeRel = some { arity := [vertexSort, vertexSort] }
  role_sig : U.relSig? roleRel = some { arity := [vertexSort, roleSort] }

namespace RoleGraphView

def toGraphView {U : UniversalRelIR} (V : RoleGraphView U) : GraphView U where
  vertexSort := V.vertexSort
  edgeRel := V.edgeRel
  vertex_wf := V.vertex_wf
  edge_sig := V.edge_sig

def Vertices {U : UniversalRelIR} (V : RoleGraphView U) : List ObjId :=
  U.objectsOfSort V.vertexSort

def Roles {U : UniversalRelIR} (V : RoleGraphView U) : List RoleId :=
  U.objectsOfSort V.roleSort

def Adjacent {U : UniversalRelIR} (V : RoleGraphView U) (u v : ObjId) : Prop :=
  U.RelHolds V.edgeRel [u, v]

def AdjacentBool {U : UniversalRelIR} (V : RoleGraphView U) (u v : ObjId) : Bool :=
  U.RelHoldsBool V.edgeRel [u, v]

@[simp] theorem toGraphView_vertices {U : UniversalRelIR} (V : RoleGraphView U) :
    V.toGraphView.Vertices = V.Vertices := by
  rfl

@[simp] theorem toGraphView_vertices_length {U : UniversalRelIR} (V : RoleGraphView U) :
    V.toGraphView.Vertices.length = V.Vertices.length := by
  rfl

@[simp] theorem toGraphView_adjacent {U : UniversalRelIR} (V : RoleGraphView U)
    (u v : ObjId) :
    V.toGraphView.Adjacent u v ↔ V.Adjacent u v := by
  rfl

@[simp] theorem toGraphView_adjacentBool {U : UniversalRelIR} (V : RoleGraphView U)
    (u v : ObjId) :
    V.toGraphView.AdjacentBool u v = V.AdjacentBool u v := by
  rfl

@[simp] theorem toGraphView_undirectedAdjacent {U : UniversalRelIR}
    (V : RoleGraphView U) (u v : ObjId) :
    V.toGraphView.UndirectedAdjacent u v ↔ V.Adjacent u v ∨ V.Adjacent v u := by
  rfl

@[simp] theorem toGraphView_undirectedAdjacentBool {U : UniversalRelIR}
    (V : RoleGraphView U) (u v : ObjId) :
    V.toGraphView.UndirectedAdjacentBool u v =
      (V.AdjacentBool u v || V.AdjacentBool v u) := by
  rfl

theorem toGraphView_edge_tuple_wf {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    U.TupleWF { arity := [V.vertexSort, V.vertexSort] } [u, v] :=
  GraphView.edge_tuple_wf V.toGraphView hU h

def HasRole {U : UniversalRelIR} (V : RoleGraphView U) (role : RoleId) (v : ObjId) :
    Prop :=
  U.RelHolds V.roleRel [v, role]

def HasRoleBool {U : UniversalRelIR} (V : RoleGraphView U) (role : RoleId) (v : ObjId) :
    Bool :=
  U.RelHoldsBool V.roleRel [v, role]

/-- Distinguished roles used by target bridges and selection gadgets. -/
structure RolePredicatePolicy {U : UniversalRelIR} (V : RoleGraphView U) where
  requiredRole : RoleId
  selectableRole : RoleId
  auxiliaryRole : RoleId
  requiredRole_wf : U.ObjWF V.roleSort requiredRole
  selectableRole_wf : U.ObjWF V.roleSort selectableRole
  auxiliaryRole_wf : U.ObjWF V.roleSort auxiliaryRole

namespace RolePredicatePolicy

def Required {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Prop :=
  V.HasRole policy.requiredRole v

def RequiredBool {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Bool :=
  V.HasRoleBool policy.requiredRole v

def Selectable {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Prop :=
  V.HasRole policy.selectableRole v

def SelectableBool {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Bool :=
  V.HasRoleBool policy.selectableRole v

def Auxiliary {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Prop :=
  V.HasRole policy.auxiliaryRole v

def AuxiliaryBool {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) (v : ObjId) : Bool :=
  V.HasRoleBool policy.auxiliaryRole v

end RolePredicatePolicy

def VerticesWithRole {U : UniversalRelIR} (V : RoleGraphView U) (role : RoleId) :
    List ObjId :=
  V.Vertices.filter fun v => U.RelHoldsBool V.roleRel [v, role]

def IsRoleNeighbor {U : UniversalRelIR} (V : RoleGraphView U)
    (v : ObjId) (role : RoleId) (u : ObjId) : Prop :=
  u ∈ V.Vertices ∧ V.HasRole role u ∧ (V.Adjacent v u ∨ V.Adjacent u v)

def IsRoleNeighborBool {U : UniversalRelIR} (V : RoleGraphView U)
    (v : ObjId) (role : RoleId) (u : ObjId) : Bool :=
  decide (u ∈ V.Vertices) && V.HasRoleBool role u &&
    (V.AdjacentBool v u || V.AdjacentBool u v)

def ExactlyOneNeighborPredicate {U : UniversalRelIR} (V : RoleGraphView U)
    (requiredRole selectableRole : RoleId) : Prop :=
  ∀ v ∈ V.Vertices,
    V.HasRole requiredRole v →
      ∃ u, V.IsRoleNeighbor v selectableRole u ∧
        ∀ u', V.IsRoleNeighbor v selectableRole u' → u' = u

@[simp] theorem mem_vertices_iff {U : UniversalRelIR} (V : RoleGraphView U)
    {v : ObjId} :
    v ∈ V.Vertices ↔ U.ObjWF V.vertexSort v := by
  simp [Vertices]

@[simp] theorem mem_roles_iff {U : UniversalRelIR} (V : RoleGraphView U)
    {role : RoleId} :
    role ∈ V.Roles ↔ U.ObjWF V.roleSort role := by
  simp [Roles]

theorem vertices_nodup {U : UniversalRelIR} (V : RoleGraphView U) :
    V.Vertices.Nodup :=
  U.objectsOfSort_nodup V.vertexSort

@[simp] theorem mem_verticesWithRole_iff {U : UniversalRelIR}
    (V : RoleGraphView U) {role : RoleId} {v : ObjId} :
    v ∈ V.VerticesWithRole role ↔ v ∈ V.Vertices ∧ V.HasRole role v := by
  simp [VerticesWithRole, HasRole]

theorem verticesWithRole_nodup {U : UniversalRelIR}
    (V : RoleGraphView U) (role : RoleId) :
    (V.VerticesWithRole role).Nodup := by
  simpa [VerticesWithRole] using
    (V.vertices_nodup.filter fun v => U.RelHoldsBool V.roleRel [v, role])

@[simp] theorem adjacentBool_eq_true_iff {U : UniversalRelIR} (V : RoleGraphView U)
    {u v : ObjId} :
    V.AdjacentBool u v = true ↔ V.Adjacent u v := by
  simp [AdjacentBool, Adjacent]

@[simp] theorem hasRoleBool_eq_true_iff {U : UniversalRelIR} (V : RoleGraphView U)
    {role : RoleId} {v : ObjId} :
    V.HasRoleBool role v = true ↔ V.HasRole role v := by
  simp [HasRoleBool, HasRole]

namespace RolePredicatePolicy

def RequiredVertices {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) : List ObjId :=
  V.VerticesWithRole policy.requiredRole

def SelectableVertices {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) : List ObjId :=
  V.VerticesWithRole policy.selectableRole

def AuxiliaryVertices {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) : List ObjId :=
  V.VerticesWithRole policy.auxiliaryRole

theorem requiredRole_mem_roles {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.requiredRole ∈ V.Roles :=
  (RoleGraphView.mem_roles_iff V).mpr policy.requiredRole_wf

theorem selectableRole_mem_roles {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.selectableRole ∈ V.Roles :=
  (RoleGraphView.mem_roles_iff V).mpr policy.selectableRole_wf

theorem auxiliaryRole_mem_roles {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.auxiliaryRole ∈ V.Roles :=
  (RoleGraphView.mem_roles_iff V).mpr policy.auxiliaryRole_wf

@[simp] theorem requiredBool_eq_true_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    policy.RequiredBool v = true ↔ policy.Required v := by
  simp [RequiredBool, Required]

@[simp] theorem selectableBool_eq_true_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    policy.SelectableBool v = true ↔ policy.Selectable v := by
  simp [SelectableBool, Selectable]

@[simp] theorem auxiliaryBool_eq_true_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    policy.AuxiliaryBool v = true ↔ policy.Auxiliary v := by
  simp [AuxiliaryBool, Auxiliary]

theorem mem_requiredVertices_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    v ∈ policy.RequiredVertices ↔ v ∈ V.Vertices ∧ policy.Required v := by
  simp [RequiredVertices, Required]

theorem mem_selectableVertices_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    v ∈ policy.SelectableVertices ↔ v ∈ V.Vertices ∧ policy.Selectable v := by
  simp [SelectableVertices, Selectable]

theorem mem_auxiliaryVertices_iff {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) {v : ObjId} :
    v ∈ policy.AuxiliaryVertices ↔ v ∈ V.Vertices ∧ policy.Auxiliary v := by
  simp [AuxiliaryVertices, Auxiliary]

theorem requiredVertices_nodup {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.RequiredVertices.Nodup := by
  simpa [RequiredVertices] using V.verticesWithRole_nodup policy.requiredRole

theorem selectableVertices_nodup {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.SelectableVertices.Nodup := by
  simpa [SelectableVertices] using V.verticesWithRole_nodup policy.selectableRole

theorem auxiliaryVertices_nodup {U : UniversalRelIR} {V : RoleGraphView U}
    (policy : RolePredicatePolicy V) :
    policy.AuxiliaryVertices.Nodup := by
  simpa [AuxiliaryVertices] using V.verticesWithRole_nodup policy.auxiliaryRole

end RolePredicatePolicy

@[simp] theorem isRoleNeighborBool_eq_true_iff {U : UniversalRelIR}
    (V : RoleGraphView U) {v : ObjId} {role : RoleId} {u : ObjId} :
    V.IsRoleNeighborBool v role u = true ↔ V.IsRoleNeighbor v role u := by
  rw [IsRoleNeighborBool, IsRoleNeighbor]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    hasRoleBool_eq_true_iff, adjacentBool_eq_true_iff]
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem edge_tuple_wf {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    U.TupleWF { arity := [V.vertexSort, V.vertexSort] } [u, v] :=
  U.RelHolds_tuple_wf hU h V.edge_sig

theorem left_mem_of_adjacent {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    u ∈ V.Vertices := by
  have hTuple := V.edge_tuple_wf hU h
  have hLeft : U.ObjWF V.vertexSort u :=
    U.ObjWF_of_tuple_get? hTuple (k := 0) (s := V.vertexSort) (x := u)
      (by simp) (by simp)
  simpa [Vertices] using hLeft

theorem right_mem_of_adjacent {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {u v : ObjId} (h : V.Adjacent u v) :
    v ∈ V.Vertices := by
  have hTuple := V.edge_tuple_wf hU h
  have hRight : U.ObjWF V.vertexSort v :=
    U.ObjWF_of_tuple_get? hTuple (k := 1) (s := V.vertexSort) (x := v)
      (by simp) (by simp)
  simpa [Vertices] using hRight

theorem role_tuple_wf {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {role : RoleId} {v : ObjId} (h : V.HasRole role v) :
    U.TupleWF { arity := [V.vertexSort, V.roleSort] } [v, role] :=
  U.RelHolds_tuple_wf hU h V.role_sig

theorem vertex_mem_of_hasRole {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {role : RoleId} {v : ObjId} (h : V.HasRole role v) :
    v ∈ V.Vertices := by
  have hTuple := V.role_tuple_wf hU h
  have hVertex : U.ObjWF V.vertexSort v :=
    U.ObjWF_of_tuple_get? hTuple (k := 0) (s := V.vertexSort) (x := v)
      (by simp) (by simp)
  simpa [Vertices] using hVertex

theorem role_mem_of_hasRole {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {role : RoleId} {v : ObjId} (h : V.HasRole role v) :
    role ∈ V.Roles := by
  have hTuple := V.role_tuple_wf hU h
  have hRole : U.ObjWF V.roleSort role :=
    U.ObjWF_of_tuple_get? hTuple (k := 1) (s := V.roleSort) (x := role)
      (by simp) (by simp)
  simpa [Roles] using hRole

theorem neighbor_mem_of_isRoleNeighbor {U : UniversalRelIR} (V : RoleGraphView U)
    {v : ObjId} {role : RoleId} {u : ObjId} (h : V.IsRoleNeighbor v role u) :
    u ∈ V.Vertices :=
  h.1

theorem hasRole_of_isRoleNeighbor {U : UniversalRelIR} (V : RoleGraphView U)
    {v : ObjId} {role : RoleId} {u : ObjId} (h : V.IsRoleNeighbor v role u) :
    V.HasRole role u :=
  h.2.1

theorem adjacent_or_reverse_of_isRoleNeighbor {U : UniversalRelIR} (V : RoleGraphView U)
    {v : ObjId} {role : RoleId} {u : ObjId} (h : V.IsRoleNeighbor v role u) :
    V.Adjacent v u ∨ V.Adjacent u v :=
  h.2.2

theorem source_mem_of_isRoleNeighbor {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {v : ObjId} {role : RoleId} {u : ObjId}
    (h : V.IsRoleNeighbor v role u) :
    v ∈ V.Vertices := by
  rcases V.adjacent_or_reverse_of_isRoleNeighbor h with hAdj | hAdj
  · exact V.left_mem_of_adjacent hU hAdj
  · exact V.right_mem_of_adjacent hU hAdj

theorem isRoleNeighborBool_members_of_true {U : UniversalRelIR} (V : RoleGraphView U)
    (hU : U.WellFormed) {v : ObjId} {role : RoleId} {u : ObjId}
    (h : V.IsRoleNeighborBool v role u = true) :
    v ∈ V.Vertices ∧ role ∈ V.Roles ∧ u ∈ V.Vertices := by
  have hNeighbor : V.IsRoleNeighbor v role u :=
    (V.isRoleNeighborBool_eq_true_iff).mp h
  exact
    ⟨ V.source_mem_of_isRoleNeighbor hU hNeighbor
    , V.role_mem_of_hasRole hU (V.hasRole_of_isRoleNeighbor hNeighbor)
    , V.neighbor_mem_of_isRoleNeighbor hNeighbor ⟩

theorem uniqueRoleNeighbor_of_exactlyOneNeighborPredicate {U : UniversalRelIR}
    (V : RoleGraphView U) {requiredRole selectableRole : RoleId} {v : ObjId}
    (h : V.ExactlyOneNeighborPredicate requiredRole selectableRole)
    (hv : v ∈ V.Vertices) (hrole : V.HasRole requiredRole v) :
    ∃ u, V.IsRoleNeighbor v selectableRole u ∧
      ∀ u', V.IsRoleNeighbor v selectableRole u' → u' = u :=
  h v hv hrole

theorem existsRoleNeighbor_of_exactlyOneNeighborPredicate {U : UniversalRelIR}
    (V : RoleGraphView U) {requiredRole selectableRole : RoleId} {v : ObjId}
    (h : V.ExactlyOneNeighborPredicate requiredRole selectableRole)
    (hv : v ∈ V.Vertices) (hrole : V.HasRole requiredRole v) :
    ∃ u, V.IsRoleNeighbor v selectableRole u := by
  rcases V.uniqueRoleNeighbor_of_exactlyOneNeighborPredicate h hv hrole with
    ⟨u, hu, _hunique⟩
  exact ⟨u, hu⟩

theorem existsRoleNeighborMem_of_exactlyOneNeighborPredicate {U : UniversalRelIR}
    (V : RoleGraphView U) {requiredRole selectableRole : RoleId} {v : ObjId}
    (h : V.ExactlyOneNeighborPredicate requiredRole selectableRole)
    (hv : v ∈ V.Vertices) (hrole : V.HasRole requiredRole v) :
    ∃ u ∈ V.Vertices, V.IsRoleNeighbor v selectableRole u := by
  rcases V.uniqueRoleNeighbor_of_exactlyOneNeighborPredicate h hv hrole with
    ⟨u, hu, _hunique⟩
  exact ⟨u, V.neighbor_mem_of_isRoleNeighbor hu, hu⟩

theorem roleNeighbor_eq_of_exactlyOneNeighborPredicate {U : UniversalRelIR}
    (V : RoleGraphView U) {requiredRole selectableRole : RoleId} {v u u' : ObjId}
    (h : V.ExactlyOneNeighborPredicate requiredRole selectableRole)
    (hv : v ∈ V.Vertices) (hrole : V.HasRole requiredRole v)
    (hu : V.IsRoleNeighbor v selectableRole u)
    (hu' : V.IsRoleNeighbor v selectableRole u') :
    u' = u := by
  rcases V.uniqueRoleNeighbor_of_exactlyOneNeighborPredicate h hv hrole with
    ⟨w, _hw, hunique⟩
  exact (hunique u' hu').trans (hunique u hu).symm

end RoleGraphView

end ComplexityReduction
