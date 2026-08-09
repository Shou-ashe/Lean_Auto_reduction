/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.Core

/-!
Canonical typed graph hub.

`GraphIR` owns a structural graph carrier independently of CR's
`GraphInput` wrapper.  The carrier has the same ordered data fields--vertex
count, edge list, and directedness--but the wrapper-to-hub conversion belongs
to an ingress adapter, not this hub.  This leaf contains no programs,
certificates, routes, registry declarations, or erased-interchange imports.
-/

namespace ComplexityReduction
namespace Domain

open Encoding

/-- The canonical graph hub: vertex count, ordered edge list, and directedness. -/
abbrev GraphIR : Type := Nat × (List (Nat × Nat) × Bool)

namespace GraphIR

/-- Assemble one canonical graph value from its explicit fields. -/
def mk (vertexCount : Nat) (edges : List (Nat × Nat)) (directed : Bool) : GraphIR :=
  (vertexCount, (edges, directed))

/-- The declared number of graph vertices. -/
def vertexCount (input : GraphIR) : Nat :=
  input.1

/-- The ordered edge list.  Multiplicity and orientation are retained. -/
def edges (input : GraphIR) : List (Nat × Nat) :=
  input.2.1

/-- The graph orientation policy. -/
def directed (input : GraphIR) : Bool :=
  input.2.2

@[simp] theorem mk_vertexCount (vertexCount : Nat) (edges : List (Nat × Nat)) (directed : Bool) :
    (mk vertexCount edges directed).vertexCount = vertexCount :=
  rfl

@[simp] theorem mk_edges (vertexCount : Nat) (edges : List (Nat × Nat)) (directed : Bool) :
    (mk vertexCount edges directed).edges = edges :=
  rfl

@[simp] theorem mk_directed (vertexCount : Nat) (edges : List (Nat × Nat)) (directed : Bool) :
    (mk vertexCount edges directed).directed = directed :=
  rfl

/-- A bounded vertex in this exact graph hub. -/
abbrev Vertex (input : GraphIR) : Type :=
  Fin input.vertexCount

/-- The semantic adjacency relation stored by the ordered edge list. -/
def Adjacent (input : GraphIR) (left right : Nat) : Prop :=
  (left, right) ∈ input.edges

/-- One edge is in range exactly when both endpoints are bounded vertices. -/
def EdgeWithinBounds (input : GraphIR) (edge : Nat × Nat) : Prop :=
  edge.1 < input.vertexCount ∧ edge.2 < input.vertexCount

/-- The graph hub's well-formedness contract. -/
def WellFormed (input : GraphIR) : Prop :=
  ∀ edge ∈ input.edges, input.EdgeWithinBounds edge

/-- Every stored edge of a well-formed graph has a bounded left endpoint. -/
theorem left_lt_vertexCount {input : GraphIR} (wellFormed : input.WellFormed)
    {edge : Nat × Nat} (member : edge ∈ input.edges) :
    edge.1 < input.vertexCount :=
  (wellFormed edge member).1

/-- Every stored edge of a well-formed graph has a bounded right endpoint. -/
theorem right_lt_vertexCount {input : GraphIR} (wellFormed : input.WellFormed)
    {edge : Nat × Nat} (member : edge ∈ input.edges) :
    edge.2 < input.vertexCount :=
  (wellFormed edge member).2

/-- The structural presentation of one graph edge. -/
abbrev edgePresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.unaryNat StandardInstances.unaryNat

/-- Structural admission for one graph edge. -/
abbrev edgeStructuralCertificate : edgePresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate StandardInstances.unaryNat StandardInstances.unaryNat
    StandardInstances.unaryNatStructuralCertificate StandardInstances.unaryNatStructuralCertificate

/-- The structural presentation of the ordered edge list. -/
abbrev edgeListPresentation : LawfulEncodedType :=
  StandardInstances.list edgePresentation

/-- Structural admission for the exact edge-list representation. -/
abbrev edgeListStructuralCertificate : edgeListPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate edgePresentation edgeStructuralCertificate

/-- The edge-list/directedness suffix of the graph hub representation. -/
abbrev payloadPresentation : LawfulEncodedType :=
  StandardInstances.prod edgeListPresentation StandardInstances.bool

/-- Structural admission for the graph payload suffix. -/
abbrev payloadStructuralCertificate : payloadPresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate edgeListPresentation StandardInstances.bool
    edgeListStructuralCertificate StandardInstances.boolStructuralCertificate

/-- The exact encoder-bound lawful representation of the canonical graph hub. -/
abbrev lawfulRepresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.unaryNat payloadPresentation

/-- Automatic structural admission for the exact graph-hub representation. -/
abbrev lawfulRepresentationStructuralCertificate : lawfulRepresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate StandardInstances.unaryNat payloadPresentation
    StandardInstances.unaryNatStructuralCertificate payloadStructuralCertificate

@[simp] theorem lawfulRepresentation_carrier : lawfulRepresentation.Carrier = GraphIR :=
  rfl

/-- The hub's complete presentation is reconstructed only from structural evidence. -/
theorem lawfulRepresentationStructuralCertificate_presentation :
    lawfulRepresentationStructuralCertificate.toLawfulEncodedType = lawfulRepresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The exact graph-hub endpoint indexed by the structural graph representation. -/
def wellFormedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation ⟨WellFormed⟩

/-- The graph-hub endpoint is precisely its canonical well-formedness contract. -/
@[simp] theorem wellFormedProblem_accepts (input : GraphIR) :
    wellFormedProblem.accepts input ↔ input.WellFormed :=
  Iff.rfl

/-- The graph-hub endpoint exposes its complete encoder-bound identity. -/
@[simp] theorem wellFormedProblem_encoderBoundIdentity :
    wellFormedProblem.encoderBoundRepresentationIdentity =
      lawfulRepresentation.encoderBoundIdentity :=
  rfl

/-- Automatic selection of this graph presentation is justified by structural evidence. -/
def wellFormedAutomaticAdmission :
    PresentedProblem.AutomaticPresentationAdmission wellFormedProblem :=
  PresentedProblem.automaticAdmissionOfStructural lawfulRepresentationStructuralCertificate

end GraphIR
end Domain
end ComplexityReduction
