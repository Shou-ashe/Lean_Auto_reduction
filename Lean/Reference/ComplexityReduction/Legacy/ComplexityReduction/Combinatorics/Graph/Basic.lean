/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic
import ComplexityReduction.Legacy.ComplexityReduction.Core

/-!
Basic graph-domain schemas for future Karp-style reductions.
-/

namespace ComplexityReduction
namespace Combinatorics
namespace Graph

/-- Finite directed or undirected graph instance represented by vertex count and edge list. -/
structure GraphInput where
  vertices : Nat
  edges : List (Nat × Nat)
  directed : Bool
  deriving Repr

/-- Raw stable encoding placeholder for graph instances. -/
def graphEncodedType : EncodedType :=
  EncodedType.raw GraphInput

/-- Structured finite-alphabet encoding for one graph edge. -/
def edgeStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- Structured finite-alphabet encoding for graph edge lists. -/
def edgeListStructuredEncodedType : EncodedType :=
  EncodedType.list edgeStructuredEncodedType

/-- Structured payload encoding for graph edge data and directedness. -/
def graphPayloadStructuredEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType EncodedType.bool

/-- Tuple-shaped finite-alphabet encoding for graph fields. -/
def graphTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat graphPayloadStructuredEncodedType

/--
Concrete finite-alphabet graph encoding with explicit vertex-count, edge-list,
and directedness fields.  This is the reusable non-raw encoding surface used for
textbook semantic conformance checks.
-/
def graphStructuredEncodedType : EncodedType where
  Carrier := GraphInput
  Symbol := graphTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun g => graphTupleStructuredEncodedType.encode (g.vertices, (g.edges, g.directed))

theorem edgeStructuredEncodedType_encode_injective :
    Function.Injective edgeStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    EncodedType.nat_encode_injective

theorem edgeListStructuredEncodedType_encode_injective :
    Function.Injective edgeListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective edgeStructuredEncodedType_encode_injective

theorem graphPayloadStructuredEncodedType_encode_injective :
    Function.Injective graphPayloadStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    edgeListStructuredEncodedType_encode_injective
    EncodedType.bool_encode_injective

theorem graphTupleStructuredEncodedType_encode_injective :
    Function.Injective graphTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    graphPayloadStructuredEncodedType_encode_injective

theorem graphStructuredEncodedType_encode_injective :
    Function.Injective graphStructuredEncodedType.encode := by
  intro g h henc
  have htuple :
      (g.vertices, (g.edges, g.directed)) =
        (h.vertices, (h.edges, h.directed)) :=
    graphTupleStructuredEncodedType_encode_injective (by
      simpa [graphStructuredEncodedType] using henc)
  cases g
  cases h
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

/-- Well-formed edge predicate for the vertex bound. -/
def EdgeWithinBounds (g : GraphInput) (e : Nat × Nat) : Prop :=
  e.1 < g.vertices ∧ e.2 < g.vertices

/-- Well-formed graph instances have every edge inside the vertex range. -/
def WellFormed (g : GraphInput) : Prop :=
  ∀ e ∈ g.edges, EdgeWithinBounds g e

/-- Generic graph decision-problem constructor. -/
def decisionProblem (P : GraphInput → Prop) : EncodedDecisionProblem where
  Instance := graphEncodedType
  isYes := P

/-- Input-size hook for graph-domain certificates. -/
def inputSize (g : GraphInput) : Nat :=
  graphEncodedType.inputSize g

/-- Directed edge membership in the raw edge list. -/
def HasDirectedEdge (g : GraphInput) (u v : Nat) : Prop :=
  (u, v) ∈ g.edges

/-- Undirected edge membership, accepting either orientation in the raw edge list. -/
def HasUndirectedEdge (g : GraphInput) (u v : Nat) : Prop :=
  (u, v) ∈ g.edges ∨ (v, u) ∈ g.edges

/-- A list of vertices lies inside the graph vertex range. -/
def VerticesWithinBounds (g : GraphInput) (vs : List Nat) : Prop :=
  ∀ v ∈ vs, v < g.vertices

/-- A vertex list is pairwise adjacent in the undirected graph sense. -/
def PairwiseAdjacent (g : GraphInput) (vs : List Nat) : Prop :=
  ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → HasUndirectedEdge g u v

/-- Karp-style clique instance: graph plus requested clique size. -/
structure CliqueInput where
  graph : GraphInput
  k : Nat
  deriving Repr

def cliqueEncodedType : EncodedType :=
  EncodedType.raw CliqueInput

/-- Tuple-shaped finite-alphabet encoding for Clique fields. -/
def cliqueTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Clique encoding with graph and requested size fields. -/
def cliqueStructuredEncodedType : EncodedType where
  Carrier := CliqueInput
  Symbol := cliqueTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => cliqueTupleStructuredEncodedType.encode (I.graph, I.k)

theorem cliqueTupleStructuredEncodedType_encode_injective :
    Function.Injective cliqueTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem cliqueStructuredEncodedType_encode_injective :
    Function.Injective cliqueStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    cliqueTupleStructuredEncodedType_encode_injective (by
      simpa [cliqueStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Semantic clique predicate for a graph instance. -/
def Clique (I : CliqueInput) : Prop :=
  ∃ vs : List Nat,
    vs.length = I.k ∧ vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
      PairwiseAdjacent I.graph vs

/-- Encoded decision problem for clique. -/
def cliqueDecisionProblem : EncodedDecisionProblem where
  Instance := cliqueEncodedType
  isYes := Clique

/-- Clique over the structured finite-alphabet encoding. -/
def cliqueStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := cliqueStructuredEncodedType
  isYes := Clique

/-- Karp-style vertex-cover instance. -/
structure VertexCoverInput where
  graph : GraphInput
  k : Nat
  deriving Repr

def vertexCoverEncodedType : EncodedType :=
  EncodedType.raw VertexCoverInput

/-- Tuple-shaped finite-alphabet encoding for Vertex Cover fields. -/
def vertexCoverTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Vertex Cover encoding with graph and budget fields. -/
def vertexCoverStructuredEncodedType : EncodedType where
  Carrier := VertexCoverInput
  Symbol := vertexCoverTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => vertexCoverTupleStructuredEncodedType.encode (I.graph, I.k)

theorem vertexCoverTupleStructuredEncodedType_encode_injective :
    Function.Injective vertexCoverTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem vertexCoverStructuredEncodedType_encode_injective :
    Function.Injective vertexCoverStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    vertexCoverTupleStructuredEncodedType_encode_injective (by
      simpa [vertexCoverStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- A vertex list covers every edge of the graph. -/
def CoversEdges (g : GraphInput) (cover : List Nat) : Prop :=
  ∀ e ∈ g.edges, e.1 ∈ cover ∨ e.2 ∈ cover

/-- Semantic vertex-cover predicate. -/
def VertexCover (I : VertexCoverInput) : Prop :=
  ∃ cover : List Nat,
    cover.length ≤ I.k ∧ cover.Nodup ∧ VerticesWithinBounds I.graph cover ∧
      CoversEdges I.graph cover

/-- Encoded decision problem for vertex cover. -/
def vertexCoverDecisionProblem : EncodedDecisionProblem where
  Instance := vertexCoverEncodedType
  isYes := VertexCover

/-- Vertex Cover over the structured finite-alphabet encoding. -/
def vertexCoverStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := vertexCoverStructuredEncodedType
  isYes := VertexCover

/-- Karp-style chromatic-number instance. -/
structure ChromaticNumberInput where
  graph : GraphInput
  colors : Nat
  deriving Repr

def chromaticNumberEncodedType : EncodedType :=
  EncodedType.raw ChromaticNumberInput

/-- Tuple-shaped finite-alphabet encoding for Chromatic Number fields. -/
def chromaticNumberTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Chromatic Number encoding with graph and color bound fields. -/
def chromaticNumberStructuredEncodedType : EncodedType where
  Carrier := ChromaticNumberInput
  Symbol := chromaticNumberTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => chromaticNumberTupleStructuredEncodedType.encode (I.graph, I.colors)

theorem chromaticNumberTupleStructuredEncodedType_encode_injective :
    Function.Injective chromaticNumberTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem chromaticNumberStructuredEncodedType_encode_injective :
    Function.Injective chromaticNumberStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.colors) = (J.graph, J.colors) :=
    chromaticNumberTupleStructuredEncodedType_encode_injective (by
      simpa [chromaticNumberStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- A finite coloring is represented as a total map into natural-number color ids. -/
def ProperColoring (g : GraphInput) (colors : Nat) (colorOf : Nat → Nat) : Prop :=
  (∀ v, v < g.vertices → colorOf v < colors) ∧
    ∀ e ∈ g.edges, colorOf e.1 ≠ colorOf e.2

/-- Semantic chromatic-number predicate: colorable with at most `colors` colors. -/
def ChromaticNumber (I : ChromaticNumberInput) : Prop :=
  ∃ colorOf : Nat → Nat, ProperColoring I.graph I.colors colorOf

def chromaticNumberDecisionProblem : EncodedDecisionProblem where
  Instance := chromaticNumberEncodedType
  isYes := ChromaticNumber

/-- Chromatic Number over the structured finite-alphabet encoding. -/
def chromaticNumberStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := chromaticNumberStructuredEncodedType
  isYes := ChromaticNumber

/-- Karp-style clique-cover instance. -/
structure CliqueCoverInput where
  graph : GraphInput
  k : Nat
  deriving Repr

def cliqueCoverEncodedType : EncodedType :=
  EncodedType.raw CliqueCoverInput

/-- Tuple-shaped finite-alphabet encoding for Clique Cover fields. -/
def cliqueCoverTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Clique Cover encoding with graph and block bound fields. -/
def cliqueCoverStructuredEncodedType : EncodedType where
  Carrier := CliqueCoverInput
  Symbol := cliqueCoverTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => cliqueCoverTupleStructuredEncodedType.encode (I.graph, I.k)

theorem cliqueCoverTupleStructuredEncodedType_encode_injective :
    Function.Injective cliqueCoverTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem cliqueCoverStructuredEncodedType_encode_injective :
    Function.Injective cliqueCoverStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    cliqueCoverTupleStructuredEncodedType_encode_injective (by
      simpa [cliqueCoverStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- A family of vertex lists covers all vertices and each block is a clique. -/
def CliqueCoverFamily (g : GraphInput) (blocks : List (List Nat)) : Prop :=
  (∀ v, v < g.vertices → ∃ block ∈ blocks, v ∈ block) ∧
    ∀ block ∈ blocks, block.Nodup ∧ VerticesWithinBounds g block ∧ PairwiseAdjacent g block

/-- Semantic clique-cover predicate. -/
def CliqueCover (I : CliqueCoverInput) : Prop :=
  ∃ blocks : List (List Nat), blocks.length ≤ I.k ∧ CliqueCoverFamily I.graph blocks

def cliqueCoverDecisionProblem : EncodedDecisionProblem where
  Instance := cliqueCoverEncodedType
  isYes := CliqueCover

/-- Clique Cover over the structured finite-alphabet encoding. -/
def cliqueCoverStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := cliqueCoverStructuredEncodedType
  isYes := CliqueCover

/-- Karp-style max-cut instance with unit edge weights. -/
structure MaxCutInput where
  graph : GraphInput
  threshold : Nat
  deriving Repr

def maxCutEncodedType : EncodedType :=
  EncodedType.raw MaxCutInput

/-- Tuple-shaped finite-alphabet encoding for Max Cut fields. -/
def maxCutTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Max Cut encoding with graph and threshold fields. -/
def maxCutStructuredEncodedType : EncodedType where
  Carrier := MaxCutInput
  Symbol := maxCutTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => maxCutTupleStructuredEncodedType.encode (I.graph, I.threshold)

/-- Tuple-shaped binary-numeric finite-alphabet encoding for Max Cut fields. -/
def maxCutTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod graphStructuredEncodedType EncodedType.binaryNat

/-- Concrete binary-numeric finite-alphabet Max Cut encoding with graph and threshold fields. -/
def maxCutBinaryStructuredEncodedType : EncodedType where
  Carrier := MaxCutInput
  Symbol := maxCutTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => maxCutTupleBinaryStructuredEncodedType.encode (I.graph, I.threshold)

theorem maxCutTupleStructuredEncodedType_encode_injective :
    Function.Injective maxCutTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem maxCutStructuredEncodedType_encode_injective :
    Function.Injective maxCutStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.threshold) = (J.graph, J.threshold) :=
    maxCutTupleStructuredEncodedType_encode_injective (by
      simpa [maxCutStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

theorem maxCutTupleBinaryStructuredEncodedType_encode_injective :
    Function.Injective maxCutTupleBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    graphStructuredEncodedType_encode_injective
    EncodedType.binaryNat_encode_injective

theorem maxCutBinaryStructuredEncodedType_encode_injective :
    Function.Injective maxCutBinaryStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.threshold) = (J.graph, J.threshold) :=
    maxCutTupleBinaryStructuredEncodedType_encode_injective (by
      simpa [maxCutBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Number of listed edges cut by a Boolean side assignment. -/
def CutSize (g : GraphInput) (side : Nat → Bool) : Nat :=
  (g.edges.filter (fun e => decide (side e.1 ≠ side e.2))).length

/-- Semantic max-cut predicate for the unit-weight graph schema. -/
def MaxCut (I : MaxCutInput) : Prop :=
  ∃ side : Nat → Bool, I.threshold ≤ CutSize I.graph side

def maxCutDecisionProblem : EncodedDecisionProblem where
  Instance := maxCutEncodedType
  isYes := MaxCut

/-- Max Cut over the structured finite-alphabet encoding. -/
def maxCutStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := maxCutStructuredEncodedType
  isYes := MaxCut

/-- Max Cut over the binary-numeric finite-alphabet encoding. -/
def maxCutBinaryStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := maxCutBinaryStructuredEncodedType
  isYes := MaxCut

end Graph
end Combinatorics
end ComplexityReduction
