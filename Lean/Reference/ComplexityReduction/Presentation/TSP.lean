/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
An exact public presentation of the Travelling Salesperson decision problem.

An instance is a weighted graph (vertex count, directed flag, weighted edge
list) plus a cost budget.  A tour is a duplicate-free vertex list of the full
vertex count; its cost is the sum, over every consecutive pair including the
closing pair, of the cheapest available edge cost in the declared direction
(0 when the edge is absent, so an absent edge makes a low-cost "tour" possible
only when the budget is large enough to accept the missing-edge convention is
NOT used: absent edges cost 0 is a No-instance trap for witnesses, so a tour
whose closing or consecutive edge is absent is still recorded by its cost and
may or may not fit the budget).  The instance is accepted when some tour has
total cost at most the budget.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding

namespace TSP

/-- One directed weighted edge. -/
structure WeightedEdge where
  source : Nat
  dest : Nat
  weight : Nat

/-- A weighted graph instance with a directedness flag. -/
structure WeightedGraphInput where
  vertices : Nat
  directed : Bool
  edges : List WeightedEdge

namespace WeightedGraphInput

/-- The edge weight of one directed pair, or zero when no edge is declared. -/
def cost (g : WeightedGraphInput) (u v : Nat) : Nat :=
  (g.edges.filter fun e => e.source = u ∧ e.dest = v).foldl
    (fun acc e => if acc = 0 then e.weight else min acc e.weight) 0

/-- The cost of a tour: every consecutive pair plus the closing pair. -/
def tourCost (g : WeightedGraphInput) (tour : List Nat) : Nat :=
  (tour.zip (tour.tail ++ tour.take 1)).foldl
    (fun acc (u, v) => acc + g.cost u v) 0

end WeightedGraphInput

/-- A TSP instance: a weighted graph plus a cost budget. -/
structure TSPInput where
  graph : WeightedGraphInput
  budget : Nat

namespace TSPInput

/-- The instance is accepted when some full tour fits the cost budget. -/
def accepted (I : TSPInput) : Prop :=
  ∃ tour : List Nat,
    tour.length = I.graph.vertices ∧ tour.Nodup ∧
      WeightedGraphInput.tourCost I.graph tour ≤ I.budget

/-- The empty graph has the empty zero-cost tour. -/
theorem accepted_empty_graph (budget : Nat) :
    accepted { graph := { vertices := 0, directed := false, edges := [] }, budget := budget } := by
  refine ⟨[], ?_, ?_, ?_⟩
  · rfl
  · simp
  · simp [WeightedGraphInput.tourCost]

end TSPInput

end TSP

namespace Presentation
namespace TSP

open ComplexityReduction.TSP

/-- The complete ordered layout of one weighted edge. -/
def weightedEdgeShape : CodecShape :=
  .prod .unaryNat (.prod .unaryNat .unaryNat)

/-- The complete ordered layout of a weighted graph input. -/
def weightedGraphShape : CodecShape :=
  .prod .unaryNat (.prod .bool (.list weightedEdgeShape))

/-- The complete ordered layout of a TSP instance. -/
def tspShape : CodecShape :=
  .prod weightedGraphShape .unaryNat

/-- The exact nested-product payload of one weighted edge. -/
abbrev edgePayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Read one weighted edge as its exact nested-product payload. -/
def edgePayload (e : WeightedEdge) : edgePayloadEncodedType.Carrier :=
  (e.source, (e.dest, e.weight))

/-- Faithful finite-alphabet encoding for one weighted edge. -/
def edgeEncodedType : EncodedType where
  Carrier := WeightedEdge
  Symbol := edgePayloadEncodedType.Symbol
  finite_symbol := edgePayloadEncodedType.finite_symbol
  encode := fun e => edgePayloadEncodedType.encode (edgePayload e)

private theorem edgePayload_injective : Function.Injective edgePayload := by
  intro left right equality
  cases left with
  | mk leftSource leftDest leftWeight =>
      cases right with
      | mk rightSource rightDest rightWeight =>
          simp only [edgePayload] at equality
          cases equality
          rfl

/-- The exact weighted-edge encoding is faithful. -/
theorem edgeEncodedType_encode_injective :
    Function.Injective edgeEncodedType.encode := by
  intro left right equality
  apply edgePayload_injective
  exact
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        EncodedType.nat_encode_injective)) equality

/-- The exact nested-product payload of a weighted graph input. -/
abbrev graphPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.bool (EncodedType.list edgeEncodedType))

/-- Read one weighted graph input as its exact nested-product payload. -/
def graphPayload (g : WeightedGraphInput) : graphPayloadEncodedType.Carrier :=
  (g.vertices, (g.directed, g.edges))

/-- Faithful finite-alphabet encoding for one weighted graph input. -/
def graphEncodedType : EncodedType where
  Carrier := WeightedGraphInput
  Symbol := graphPayloadEncodedType.Symbol
  finite_symbol := graphPayloadEncodedType.finite_symbol
  encode := fun g => graphPayloadEncodedType.encode (graphPayload g)

private theorem graphPayload_injective : Function.Injective graphPayload := by
  intro left right equality
  cases left with
  | mk leftVertices leftDirected leftEdges =>
      cases right with
      | mk rightVertices rightDirected rightEdges =>
          simp only [graphPayload] at equality
          cases equality
          rfl

/-- The exact weighted-graph encoding is faithful. -/
theorem graphEncodedType_encode_injective :
    Function.Injective graphEncodedType.encode := by
  intro left right equality
  apply graphPayload_injective
  exact
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.bool_encode_injective
        (EncodedType.list_encode_injective edgeEncodedType_encode_injective))) equality

/-- The exact nested-product payload of a TSP instance. -/
abbrev tspPayloadEncodedType : EncodedType :=
  EncodedType.prod graphEncodedType EncodedType.nat

/-- Read one TSP instance as its exact nested-product payload. -/
def tspPayload (I : TSPInput) : tspPayloadEncodedType.Carrier :=
  (I.graph, I.budget)

/-- Faithful finite-alphabet encoding for one TSP instance. -/
def tspEncodedType : EncodedType where
  Carrier := TSPInput
  Symbol := tspPayloadEncodedType.Symbol
  finite_symbol := tspPayloadEncodedType.finite_symbol
  encode := fun I => tspPayloadEncodedType.encode (tspPayload I)

private theorem tspPayload_injective : Function.Injective tspPayload := by
  intro left right equality
  cases left with
  | mk leftGraph leftBudget =>
      cases right with
      | mk rightGraph rightBudget =>
          simp only [tspPayload] at equality
          cases equality
          rfl

/-- The exact TSP encoding is faithful. -/
theorem tspEncodedType_encode_injective :
    Function.Injective tspEncodedType.encode := by
  intro left right equality
  apply tspPayload_injective
  exact
    (EncodedType.prod_encode_injective
      graphEncodedType_encode_injective
      EncodedType.nat_encode_injective) equality

/-- Canonical lawful exact TSP representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := tspEncodedType
  representation := tspShape.identity
  faithful := ⟨tspEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = tspEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = tspShape.identity :=
  rfl

/-- The represented carrier is exactly the public TSP syntax. -/
theorem structuredPresentation_carrier_eq_TSPInput :
    structuredPresentation.Carrier = TSPInput :=
  rfl

/-- The exact TSP semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := TSPInput.accepted

/-- Canonical exact public TSP endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = tspShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ TSPInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ TSPInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  edgeEncodedType_encode_injective,
  graphEncodedType_encode_injective,
  tspEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes

end TSP
end Presentation
end ComplexityReduction
