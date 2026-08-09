/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.GraphIR

/-!
Canonical typed role-graph hub for graph role-assignment gadgets.

The hub stores an exact graph together with its role-sort cardinality.  Its
canonical view reserves role `0` for graph vertices and role `1` for an
auxiliary role; graph-role membership is intentionally implicit in this
minimal view.  A later domain gadget can extend the view through an explicit
adapter without rebuilding the graph hub or its representation.
-/

namespace ComplexityReduction
namespace Domain

open Encoding

/-- The canonical role-graph carrier: role-sort cardinality and one graph hub value. -/
abbrev RoleGraphIR : Type := Nat × GraphIR

namespace RoleGraphIR

/-- Assemble a role-graph hub value from its role cardinality and graph payload. -/
def mk (roleCount : Nat) (graph : GraphIR) : RoleGraphIR :=
  (roleCount, graph)

/-- The declared cardinality of the role sort. -/
def roleCount (input : RoleGraphIR) : Nat :=
  input.1

/-- The exact canonical graph payload. -/
def graph (input : RoleGraphIR) : GraphIR :=
  input.2

/-- The role-graph vertex count is owned by its embedded canonical graph. -/
def vertexCount (input : RoleGraphIR) : Nat :=
  input.graph.vertexCount

/-- The ordered role-graph edge list is owned by its embedded canonical graph. -/
def edges (input : RoleGraphIR) : List (Nat × Nat) :=
  input.graph.edges

/-- The role-graph orientation policy is owned by its embedded canonical graph. -/
def directed (input : RoleGraphIR) : Bool :=
  input.graph.directed

@[simp] theorem mk_roleCount (roleCount : Nat) (graph : GraphIR) :
    (mk roleCount graph).roleCount = roleCount :=
  rfl

@[simp] theorem mk_graph (roleCount : Nat) (graph : GraphIR) :
    (mk roleCount graph).graph = graph :=
  rfl

/-- A canonical graph vertex in this exact role-graph view. -/
abbrev Vertex (input : RoleGraphIR) : Type :=
  Fin input.vertexCount

/-- A canonical role in this exact role-graph view. -/
abbrev Role (input : RoleGraphIR) : Type :=
  Fin input.roleCount

/-- The fixed graph-vertex role used by the shared role-assignment gadget. -/
def graphVertexRole : Nat :=
  0

/-- The fixed auxiliary role reserved by the shared role-assignment gadget. -/
def auxiliaryRole : Nat :=
  1

/-- Graph adjacency in the role-graph hub is exactly the embedded graph adjacency. -/
def Adjacent (input : RoleGraphIR) (left right : Nat) : Prop :=
  input.graph.Adjacent left right

/-- Every in-range vertex is assigned to the canonical graph-vertex role. -/
def HasRole (input : RoleGraphIR) (role vertex : Nat) : Prop :=
  vertex < input.vertexCount ∧ role = graphVertexRole

/-- A minimal fixed-role view over one canonical role-graph hub input. -/
structure View (input : RoleGraphIR) where
  graphVertexRole_eq : graphVertexRole < input.roleCount
  auxiliaryRole_eq : auxiliaryRole < input.roleCount

/-- The role-graph carrier is well formed when it has the two required roles and a well-formed graph. -/
def WellFormed (input : RoleGraphIR) : Prop :=
  input.graph.WellFormed ∧ input.roleCount = 2

/-- The target semantic contract for a graph whose vertices receive the canonical graph role. -/
def IsRoleAssignedGraph (input : RoleGraphIR) : Prop :=
  input.WellFormed ∧
    ∃ _view : input.View,
      ∀ vertex, vertex < input.vertexCount → input.HasRole graphVertexRole vertex

/-- The exact role-assignment executable used by the shared graph-hub gadget. -/
def roleAssignment (input : GraphIR) : RoleGraphIR :=
  mk 2 input

/-- The role-assignment output has the fixed canonical role view. -/
def roleAssignmentView (input : GraphIR) : (roleAssignment input).View where
  graphVertexRole_eq := by
    simp [roleAssignment, mk, graphVertexRole, roleCount]
  auxiliaryRole_eq := by
    simp [roleAssignment, mk, auxiliaryRole, roleCount]

/-- Role assignment preserves graph well-formedness while installing two roles. -/
theorem roleAssignment_wellFormed {input : GraphIR} (wellFormed : input.WellFormed) :
    (roleAssignment input).WellFormed :=
  ⟨wellFormed, rfl⟩

/-- Every bounded source vertex receives the canonical graph-vertex role. -/
theorem roleAssignment_hasGraphRole (input : GraphIR) {vertex : Nat}
    (vertexBound : vertex < input.vertexCount) :
    (roleAssignment input).HasRole graphVertexRole vertex := by
  exact ⟨by simpa [roleAssignment, mk, vertexCount, graph] using vertexBound, rfl⟩

/-- The role-assignment output satisfies the exact target semantic contract. -/
theorem roleAssignment_isRoleAssignedGraph {input : GraphIR} (wellFormed : input.WellFormed) :
    (roleAssignment input).IsRoleAssignedGraph := by
  refine ⟨roleAssignment_wellFormed wellFormed, roleAssignmentView input, ?_⟩
  intro vertex vertexBound
  exact roleAssignment_hasGraphRole input vertexBound

/-- The role-assignment target contract can only hold when the embedded graph is well formed. -/
theorem graph_wellFormed_of_isRoleAssignedGraph {input : RoleGraphIR}
    (assigned : input.IsRoleAssignedGraph) :
    input.graph.WellFormed :=
  assigned.1.1

/-- The representation of the role graph is the role cardinality paired with the graph hub representation. -/
abbrev lawfulRepresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.unaryNat GraphIR.lawfulRepresentation

/-- Automatic structural admission for the full role-graph representation. -/
abbrev lawfulRepresentationStructuralCertificate : lawfulRepresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate StandardInstances.unaryNat GraphIR.lawfulRepresentation
    StandardInstances.unaryNatStructuralCertificate GraphIR.lawfulRepresentationStructuralCertificate

@[simp] theorem lawfulRepresentation_carrier : lawfulRepresentation.Carrier = RoleGraphIR :=
  rfl

/-- The complete role-graph presentation is reconstructed only from structural evidence. -/
theorem lawfulRepresentationStructuralCertificate_presentation :
    lawfulRepresentationStructuralCertificate.toLawfulEncodedType = lawfulRepresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The exact role-assigned graph endpoint. -/
def roleAssignedGraphProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation ⟨IsRoleAssignedGraph⟩

/-- The target endpoint exposes exactly the role-assignment semantic contract. -/
@[simp] theorem roleAssignedGraphProblem_accepts (input : RoleGraphIR) :
    roleAssignedGraphProblem.accepts input ↔ input.IsRoleAssignedGraph :=
  Iff.rfl

/-- The target endpoint retains its complete encoder-bound identity. -/
@[simp] theorem roleAssignedGraphProblem_encoderBoundIdentity :
    roleAssignedGraphProblem.encoderBoundRepresentationIdentity =
      lawfulRepresentation.encoderBoundIdentity :=
  rfl

/-- Automatic selection of this target presentation is justified by structural evidence. -/
def roleAssignedGraphAutomaticAdmission :
    PresentedProblem.AutomaticPresentationAdmission roleAssignedGraphProblem :=
  PresentedProblem.automaticAdmissionOfStructural lawfulRepresentationStructuralCertificate

end RoleGraphIR
end Domain
end ComplexityReduction
