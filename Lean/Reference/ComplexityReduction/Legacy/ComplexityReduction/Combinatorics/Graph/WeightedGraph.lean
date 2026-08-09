/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Basic

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- Weighted graph instance schema with natural-number weights. -/
structure WeightedGraphInput where
  vertices : Nat
  edges : List (Nat × Nat × Nat)
  directed : Bool
  deriving Repr

def weightedGraphEncodedType : EncodedType :=
  EncodedType.raw WeightedGraphInput

/-- Structured finite-alphabet encoding for one weighted edge `(u, v, w)`. -/
def weightedEdgeStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Structured finite-alphabet encoding for weighted edge lists. -/
def weightedEdgeListStructuredEncodedType : EncodedType :=
  EncodedType.list weightedEdgeStructuredEncodedType

/-- Structured payload encoding for weighted edge data and directedness. -/
def weightedGraphPayloadStructuredEncodedType : EncodedType :=
  EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool

/-- Tuple-shaped finite-alphabet encoding for weighted graph fields. -/
def weightedGraphTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat weightedGraphPayloadStructuredEncodedType

/-- Concrete finite-alphabet weighted-graph encoding. -/
def weightedGraphStructuredEncodedType : EncodedType where
  Carrier := WeightedGraphInput
  Symbol := weightedGraphTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun g => weightedGraphTupleStructuredEncodedType.encode
    (g.vertices, (g.edges, g.directed))

theorem weightedEdgeStructuredEncodedType_encode_injective :
    Function.Injective weightedEdgeStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      EncodedType.nat_encode_injective)

theorem weightedEdgeListStructuredEncodedType_encode_injective :
    Function.Injective weightedEdgeListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective weightedEdgeStructuredEncodedType_encode_injective

theorem weightedGraphPayloadStructuredEncodedType_encode_injective :
    Function.Injective weightedGraphPayloadStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    weightedEdgeListStructuredEncodedType_encode_injective
    EncodedType.bool_encode_injective

theorem weightedGraphTupleStructuredEncodedType_encode_injective :
    Function.Injective weightedGraphTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    weightedGraphPayloadStructuredEncodedType_encode_injective

theorem weightedGraphStructuredEncodedType_encode_injective :
    Function.Injective weightedGraphStructuredEncodedType.encode := by
  intro g h henc
  have htuple :
      (g.vertices, (g.edges, g.directed)) =
        (h.vertices, (h.edges, h.directed)) :=
    weightedGraphTupleStructuredEncodedType_encode_injective (by
      simpa [weightedGraphStructuredEncodedType] using henc)
  cases g
  cases h
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

def weightedDecisionProblem (P : WeightedGraphInput → Prop) : EncodedDecisionProblem where
  Instance := weightedGraphEncodedType
  isYes := P

/-- Karp-style Steiner-tree instance over a natural-weight graph. -/
structure SteinerTreeInput where
  graph : WeightedGraphInput
  terminals : List Nat
  weightBound : Nat
  deriving Repr

def steinerTreeEncodedType : EncodedType :=
  EncodedType.raw SteinerTreeInput

/-- Structured finite-alphabet encoding for Steiner Tree fields. -/
def steinerTreeTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod weightedGraphStructuredEncodedType
    (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.nat)

/-- Concrete finite-alphabet Steiner Tree encoding. -/
def steinerTreeStructuredEncodedType : EncodedType where
  Carrier := SteinerTreeInput
  Symbol := steinerTreeTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => steinerTreeTupleStructuredEncodedType.encode
    (I.graph, (I.terminals, I.weightBound))

theorem steinerTreeTupleStructuredEncodedType_encode_injective :
    Function.Injective steinerTreeTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    weightedGraphStructuredEncodedType_encode_injective
    (EncodedType.prod_encode_injective
      (EncodedType.list_encode_injective EncodedType.nat_encode_injective)
      EncodedType.nat_encode_injective)

theorem steinerTreeStructuredEncodedType_encode_injective :
    Function.Injective steinerTreeStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, (I.terminals, I.weightBound)) =
      (J.graph, (J.terminals, J.weightBound)) :=
    steinerTreeTupleStructuredEncodedType_encode_injective (by
      simpa [steinerTreeStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

/-- A listed weighted edge is selected in a candidate tree. -/
def WeightedEdgeInGraph (g : WeightedGraphInput) (e : Nat × Nat × Nat) : Prop :=
  e ∈ g.edges

/-- Total weight of a candidate edge list. -/
def WeightedEdgeListWeight (edges : List (Nat × Nat × Nat)) : Nat :=
  (edges.map (fun e => e.2.2)).sum

/-- A vertex is an endpoint of a selected weighted edge. -/
def WeightedEdgeHasEndpoint (e : Nat × Nat × Nat) (v : Nat) : Prop :=
  e.1 = v ∨ e.2.1 = v

/-- A selected weighted edge can be traversed from `u` to `v`. -/
def WeightedEdgeTraverses (directed : Bool) (e : Nat × Nat × Nat) (u v : Nat) : Prop :=
  (e.1 = u ∧ e.2.1 = v) ∨ (directed = false ∧ e.1 = v ∧ e.2.1 = u)

/-- One graph step inside a selected weighted edge list. -/
def WeightedAdjacent (selected : List (Nat × Nat × Nat)) (directed : Bool)
    (u v : Nat) : Prop :=
  ∃ e ∈ selected, WeightedEdgeTraverses directed e u v

/-- Reachability inside the selected weighted subgraph. -/
inductive WeightedReachable (selected : List (Nat × Nat × Nat)) (directed : Bool) :
    Nat → Nat → Prop
  | refl (u : Nat) : WeightedReachable selected directed u u
  | step {u v w : Nat} :
      WeightedAdjacent selected directed u v →
      WeightedReachable selected directed v w →
      WeightedReachable selected directed u w

/--
Proof-friendly connected-subgraph predicate used by the Steiner-tree skeleton:
all terminals are present in the endpoint set of the selected edge list and are
reachable from the first listed terminal.
-/
def ContainsTerminals (selected : List (Nat × Nat × Nat)) (terminals : List Nat)
    (directed : Bool := false) : Prop :=
  ∀ t ∈ terminals,
    (∃ e ∈ selected, WeightedEdgeHasEndpoint e t) ∧
      match terminals with
      | [] => True
      | root :: _ => WeightedReachable selected directed root t

def SteinerTree (I : SteinerTreeInput) : Prop :=
  ∃ selected : List (Nat × Nat × Nat),
    (∀ e ∈ selected, WeightedEdgeInGraph I.graph e) ∧
      ContainsTerminals selected I.terminals I.graph.directed ∧
      WeightedEdgeListWeight selected ≤ I.weightBound

def steinerTreeDecisionProblem : EncodedDecisionProblem where
  Instance := steinerTreeEncodedType
  isYes := SteinerTree

/-- Steiner Tree over the structured finite-alphabet encoding. -/
def steinerTreeStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := steinerTreeStructuredEncodedType
  isYes := SteinerTree

end Graph
end Combinatorics
end ComplexityReduction
