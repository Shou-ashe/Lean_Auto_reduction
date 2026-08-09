/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Basic
import Mathlib.Data.Finset.Card

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- Directed graph instance schema. -/
abbrev DigraphInput : Type :=
  GraphInput

/-- Directed graph well-formedness uses the generic edge-bound predicate. -/
def DigraphWellFormed (g : DigraphInput) : Prop :=
  g.directed = true ∧ WellFormed g

/-- A nonempty directed-cycle witness in the raw graph schema.

The local graph layer records a cycle extensionally as a finite set-like vertex
list: each listed vertex has a directed edge to another listed vertex.  This is
the predicate used by feedback-node/arc-set targets; Hamiltonian circuits keep
their separate all-vertices predicate below.
-/
def DirectedCycle (g : DigraphInput) (cycle : List Nat) : Prop :=
  0 < cycle.length ∧
    cycle.Nodup ∧
    VerticesWithinBounds g cycle ∧
    ∀ u ∈ cycle, ∃ v ∈ cycle, HasDirectedEdge g u v

/-- Karp-style directed Hamiltonian-circuit instance. -/
structure DirectedHamiltonianCircuitInput where
  graph : DigraphInput
  deriving Repr

def directedHamiltonianCircuitEncodedType : EncodedType :=
  EncodedType.raw DirectedHamiltonianCircuitInput

/-- Concrete finite-alphabet Directed Hamiltonian Circuit encoding. -/
def directedHamiltonianCircuitStructuredEncodedType : EncodedType where
  Carrier := DirectedHamiltonianCircuitInput
  Symbol := graphStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => graphStructuredEncodedType.encode I.graph

theorem directedHamiltonianCircuitStructuredEncodedType_encode_injective :
    Function.Injective directedHamiltonianCircuitStructuredEncodedType.encode := by
  intro I J henc
  have hgraph : I.graph = J.graph :=
    graphStructuredEncodedType_encode_injective (by
      simpa [directedHamiltonianCircuitStructuredEncodedType] using henc)
  cases I
  cases J
  cases hgraph
  rfl

/-- Successor index in a nonempty cyclic list, represented by an existing index proof. -/
def cyclicSuccIndex {cycle : List Nat} (i : Fin cycle.length) : Fin cycle.length :=
  ⟨(i.val + 1) % cycle.length,
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- Ordered directed successor condition for a listed cyclic walk. -/
def OrderedDirectedCycleSteps (g : DigraphInput) (cycle : List Nat) : Prop :=
  ∀ i : Fin cycle.length,
    HasDirectedEdge g (cycle.get i) (cycle.get (cyclicSuccIndex i))

/-- Ordered undirected successor condition for a listed cyclic walk. -/
def OrderedUndirectedCycleSteps (g : GraphInput) (cycle : List Nat) : Prop :=
  ∀ i : Fin cycle.length,
    HasUndirectedEdge g (cycle.get i) (cycle.get (cyclicSuccIndex i))

/-- The list is an ordered directed Hamiltonian cycle over all vertices. -/
def OrderedDirectedHamiltonianCycle (g : DigraphInput) (cycle : List Nat) : Prop :=
  cycle.length = g.vertices ∧
    cycle.Nodup ∧
    VerticesWithinBounds g cycle ∧
    OrderedDirectedCycleSteps g cycle

/-- A bounded nodup list with graph-cardinality length contains every graph vertex. -/
theorem mem_of_verticesWithinBounds_length_nodup {g : GraphInput} {vs : List Nat}
    (hLen : vs.length = g.vertices) (hNodup : vs.Nodup)
    (hBounds : VerticesWithinBounds g vs) {v : Nat} (hv : v < g.vertices) :
    v ∈ vs := by
  classical
  by_contra hvNotMem
  let s : Finset Nat := vs.toFinset
  have hsSubset : s ⊆ Finset.range g.vertices := by
    intro u hu
    exact Finset.mem_range.mpr (hBounds u (by simpa [s] using hu))
  have hsStrict : s ⊂ Finset.range g.vertices := by
    refine ⟨hsSubset, ?_⟩
    intro hRangeSubset
    have hvSet : v ∈ s := hRangeSubset (Finset.mem_range.mpr hv)
    exact hvNotMem (by simpa [s] using hvSet)
  have hCardLt := Finset.card_lt_card hsStrict
  have hCardEq : s.card = (Finset.range g.vertices).card := by
    simp [s, List.toFinset_card_of_nodup hNodup, hLen]
  omega

/-- A bounded nodup list containing every graph vertex has graph-cardinality length. -/
theorem length_eq_vertices_of_nodup_verticesWithinBounds_all
    {g : GraphInput} {vs : List Nat} (hNodup : vs.Nodup)
    (hBounds : VerticesWithinBounds g vs)
    (hAll : ∀ v, v < g.vertices → v ∈ vs) :
    vs.length = g.vertices := by
  classical
  let s : Finset Nat := vs.toFinset
  have hSet : s = Finset.range g.vertices := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_range.mpr (hBounds v (by simpa [s] using hv))
    · intro hv
      exact (by simpa [s] using hAll v (Finset.mem_range.mp hv))
  have hCard := congrArg Finset.card hSet
  simpa [s, List.toFinset_card_of_nodup hNodup] using hCard

/-- Every bounded graph vertex occurs in an ordered Hamiltonian-cycle witness. -/
theorem OrderedDirectedHamiltonianCycle.mem_of_lt {g : DigraphInput} {cycle : List Nat}
    (h : OrderedDirectedHamiltonianCycle g cycle) {v : Nat} (hv : v < g.vertices) :
    v ∈ cycle :=
  mem_of_verticesWithinBounds_length_nodup h.1 h.2.1 h.2.2.1 hv

/-- The list is a directed Hamiltonian cycle over all vertices. -/
def DirectedHamiltonianCycle (g : DigraphInput) (cycle : List Nat) : Prop :=
  cycle.length = g.vertices ∧
    cycle.Nodup ∧
    VerticesWithinBounds g cycle ∧
    ∀ u ∈ cycle, ∃ v ∈ cycle, HasDirectedEdge g u v

theorem OrderedDirectedHamiltonianCycle.toSetLike {g : DigraphInput} {cycle : List Nat}
    (h : OrderedDirectedHamiltonianCycle g cycle) :
    DirectedHamiltonianCycle g cycle := by
  rcases h with ⟨hLen, hNodup, hBounds, hSteps⟩
  refine ⟨hLen, hNodup, hBounds, ?_⟩
  intro u hu
  rcases List.mem_iff_get.mp hu with ⟨i, rfl⟩
  exact ⟨cycle.get (cyclicSuccIndex i), List.get_mem _ _, hSteps i⟩

/-- Semantic directed-Hamiltonian-circuit predicate with ordered successor semantics. -/
def DirectedHamiltonianCircuit (I : DirectedHamiltonianCircuitInput) : Prop :=
  I.graph.directed = true ∧ ∃ cycle : List Nat, OrderedDirectedHamiltonianCycle I.graph cycle

/-- Semantic ordered directed-Hamiltonian-circuit predicate. -/
def OrderedDirectedHamiltonianCircuit (I : DirectedHamiltonianCircuitInput) : Prop :=
  I.graph.directed = true ∧ ∃ cycle : List Nat, OrderedDirectedHamiltonianCycle I.graph cycle

def directedHamiltonianCircuitDecisionProblem : EncodedDecisionProblem where
  Instance := directedHamiltonianCircuitEncodedType
  isYes := DirectedHamiltonianCircuit

/-- Directed Hamiltonian Circuit over the structured finite-alphabet encoding. -/
def directedHamiltonianCircuitStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := directedHamiltonianCircuitStructuredEncodedType
  isYes := DirectedHamiltonianCircuit

/-- Karp-style undirected Hamiltonian-circuit instance. -/
structure UndirectedHamiltonianCircuitInput where
  graph : GraphInput
  deriving Repr

def undirectedHamiltonianCircuitEncodedType : EncodedType :=
  EncodedType.raw UndirectedHamiltonianCircuitInput

/-- Concrete finite-alphabet Undirected Hamiltonian Circuit encoding. -/
def undirectedHamiltonianCircuitStructuredEncodedType : EncodedType where
  Carrier := UndirectedHamiltonianCircuitInput
  Symbol := graphStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => graphStructuredEncodedType.encode I.graph

theorem undirectedHamiltonianCircuitStructuredEncodedType_encode_injective :
    Function.Injective undirectedHamiltonianCircuitStructuredEncodedType.encode := by
  intro I J henc
  have hgraph : I.graph = J.graph :=
    graphStructuredEncodedType_encode_injective (by
      simpa [undirectedHamiltonianCircuitStructuredEncodedType] using henc)
  cases I
  cases J
  cases hgraph
  rfl

/-- The list is an ordered undirected Hamiltonian cycle over all vertices. -/
def OrderedUndirectedHamiltonianCycle (g : GraphInput) (cycle : List Nat) : Prop :=
  cycle.length = g.vertices ∧
    cycle.Nodup ∧
    VerticesWithinBounds g cycle ∧
    OrderedUndirectedCycleSteps g cycle

/-- The list is an undirected Hamiltonian cycle over all vertices. -/
def UndirectedHamiltonianCycle (g : GraphInput) (cycle : List Nat) : Prop :=
  cycle.length = g.vertices ∧
    cycle.Nodup ∧
    VerticesWithinBounds g cycle ∧
    ∀ u ∈ cycle, ∃ v ∈ cycle, HasUndirectedEdge g u v

theorem OrderedUndirectedHamiltonianCycle.toSetLike {g : GraphInput} {cycle : List Nat}
    (h : OrderedUndirectedHamiltonianCycle g cycle) :
    UndirectedHamiltonianCycle g cycle := by
  rcases h with ⟨hLen, hNodup, hBounds, hSteps⟩
  refine ⟨hLen, hNodup, hBounds, ?_⟩
  intro u hu
  rcases List.mem_iff_get.mp hu with ⟨i, rfl⟩
  exact ⟨cycle.get (cyclicSuccIndex i), List.get_mem _ _, hSteps i⟩

/-- Semantic undirected-Hamiltonian-circuit predicate with ordered successor semantics. -/
def UndirectedHamiltonianCircuit (I : UndirectedHamiltonianCircuitInput) : Prop :=
  I.graph.directed = false ∧ ∃ cycle : List Nat, OrderedUndirectedHamiltonianCycle I.graph cycle

/-- Semantic ordered undirected-Hamiltonian-circuit predicate. -/
def OrderedUndirectedHamiltonianCircuit (I : UndirectedHamiltonianCircuitInput) : Prop :=
  I.graph.directed = false ∧ ∃ cycle : List Nat, OrderedUndirectedHamiltonianCycle I.graph cycle

def undirectedHamiltonianCircuitDecisionProblem : EncodedDecisionProblem where
  Instance := undirectedHamiltonianCircuitEncodedType
  isYes := UndirectedHamiltonianCircuit

/-- Undirected Hamiltonian Circuit over the structured finite-alphabet encoding. -/
def undirectedHamiltonianCircuitStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := undirectedHamiltonianCircuitStructuredEncodedType
  isYes := UndirectedHamiltonianCircuit

/-- Karp-style feedback-node-set instance. -/
structure FeedbackNodeSetInput where
  graph : GraphInput
  k : Nat
  deriving Repr

def feedbackNodeSetEncodedType : EncodedType :=
  EncodedType.raw FeedbackNodeSetInput

/-- Tuple-shaped finite-alphabet encoding for Feedback Node Set fields. -/
def feedbackNodeSetTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Feedback Node Set encoding with graph and budget fields. -/
def feedbackNodeSetStructuredEncodedType : EncodedType where
  Carrier := FeedbackNodeSetInput
  Symbol := feedbackNodeSetTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => feedbackNodeSetTupleStructuredEncodedType.encode (I.graph, I.k)

theorem feedbackNodeSetTupleStructuredEncodedType_encode_injective :
    Function.Injective feedbackNodeSetTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem feedbackNodeSetStructuredEncodedType_encode_injective :
    Function.Injective feedbackNodeSetStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    feedbackNodeSetTupleStructuredEncodedType_encode_injective (by
      simpa [feedbackNodeSetStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/--
Placeholder-free semantic hook for feedback node sets: deleting `removed`
leaves no directed cycle witness in the retained vertices.
-/
def FeedbackNodeSetWitness (g : GraphInput) (removed : List Nat) : Prop :=
  removed.Nodup ∧ VerticesWithinBounds g removed ∧
    ∀ cycle : List Nat,
      DirectedCycle g cycle → ∃ v ∈ cycle, v ∈ removed

def FeedbackNodeSet (I : FeedbackNodeSetInput) : Prop :=
  ∃ removed : List Nat, removed.length ≤ I.k ∧ FeedbackNodeSetWitness I.graph removed

def feedbackNodeSetDecisionProblem : EncodedDecisionProblem where
  Instance := feedbackNodeSetEncodedType
  isYes := FeedbackNodeSet

/-- Feedback Node Set over the structured finite-alphabet encoding. -/
def feedbackNodeSetStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := feedbackNodeSetStructuredEncodedType
  isYes := FeedbackNodeSet

/-- Karp-style feedback-arc-set instance. -/
structure FeedbackArcSetInput where
  graph : GraphInput
  k : Nat
  deriving Repr

def feedbackArcSetEncodedType : EncodedType :=
  EncodedType.raw FeedbackArcSetInput

/-- Tuple-shaped finite-alphabet encoding for Feedback Arc Set fields. -/
def feedbackArcSetTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Feedback Arc Set encoding with graph and budget fields. -/
def feedbackArcSetStructuredEncodedType : EncodedType where
  Carrier := FeedbackArcSetInput
  Symbol := feedbackArcSetTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => feedbackArcSetTupleStructuredEncodedType.encode (I.graph, I.k)

theorem feedbackArcSetTupleStructuredEncodedType_encode_injective :
    Function.Injective feedbackArcSetTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem feedbackArcSetStructuredEncodedType_encode_injective :
    Function.Injective feedbackArcSetStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    feedbackArcSetTupleStructuredEncodedType_encode_injective (by
      simpa [feedbackArcSetStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- A directed arc lies on the set-like directed-cycle witness. -/
def ArcOnDirectedCycle (g : GraphInput) (cycle : List Nat) (e : Nat × Nat) : Prop :=
  e ∈ g.edges ∧ e.1 ∈ cycle ∧ e.2 ∈ cycle

/-- Delete the listed directed arcs from a graph, preserving the vertex bound and directed flag. -/
def deleteArcs (g : GraphInput) (removed : List (Nat × Nat)) : GraphInput where
  vertices := g.vertices
  edges := g.edges.filter fun e => decide (e ∉ removed)
  directed := g.directed

theorem mem_deleteArcs_edges_iff
    {g : GraphInput} {removed : List (Nat × Nat)} {e : Nat × Nat} :
    e ∈ (deleteArcs g removed).edges ↔ e ∈ g.edges ∧ e ∉ removed := by
  simp [deleteArcs]

theorem hasDirectedEdge_deleteArcs_iff
    {g : GraphInput} {removed : List (Nat × Nat)} {u v : Nat} :
    HasDirectedEdge (deleteArcs g removed) u v ↔
      HasDirectedEdge g u v ∧ (u, v) ∉ removed := by
  simpa [HasDirectedEdge] using
    (mem_deleteArcs_edges_iff (g := g) (removed := removed) (e := (u, v)))

theorem directedCycle_of_deleteArcs
    {g : GraphInput} {removed : List (Nat × Nat)} {cycle : List Nat}
    (hCycle : DirectedCycle (deleteArcs g removed) cycle) :
    DirectedCycle g cycle := by
  rcases hCycle with ⟨hPos, hNodup, hBounds, hStep⟩
  refine ⟨hPos, hNodup, ?_, ?_⟩
  · intro v hv
    simpa [deleteArcs] using hBounds v hv
  · intro u hu
    rcases hStep u hu with ⟨v, hv, hEdge⟩
    exact ⟨v, hv, (hasDirectedEdge_deleteArcs_iff.mp hEdge).1⟩

def FeedbackArcSetWitness (g : GraphInput) (removed : List (Nat × Nat)) : Prop :=
  (∀ e ∈ removed, e ∈ g.edges) ∧
    ∀ cycle : List Nat, DirectedCycle (deleteArcs g removed) cycle → False

def FeedbackArcSet (I : FeedbackArcSetInput) : Prop :=
  ∃ removed : List (Nat × Nat), removed.length ≤ I.k ∧ FeedbackArcSetWitness I.graph removed

def feedbackArcSetDecisionProblem : EncodedDecisionProblem where
  Instance := feedbackArcSetEncodedType
  isYes := FeedbackArcSet

/-- Feedback Arc Set over the structured finite-alphabet encoding. -/
def feedbackArcSetStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := feedbackArcSetStructuredEncodedType
  isYes := FeedbackArcSet

end Graph
end Combinatorics
end ComplexityReduction
