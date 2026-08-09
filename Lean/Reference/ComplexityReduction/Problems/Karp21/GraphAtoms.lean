/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Projections
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Program.CompileTM
import ComplexityReduction.Protocol.MissingCapability

/-!
Direct-TM-backed graph-family primitive atoms for canonical V2 programs.

The graph, Clique, and Vertex-Cover wrappers below retain the exact faithful
structured encoders from `ComplexityReduction`.  Field projections, strict
pair generation, candidate complement scanning, and the complete
Clique-to-Vertex-Cover construction are admitted only from the corresponding
legacy `TMPolyTimeMap` witnesses.  In particular, the legacy
`TMBackedCostedMap` values are used solely through their existing direct-TM
fields; no V2 primitive is constructed from their cost fields.

The current CR library has no exact direct-TM computations for the
Incidence/RoleGraph role-assignment and neighbour-check requests.  Those are
returned as typed missing capabilities rather than being replaced by arbitrary
functions, route-local machines, packets, providers, slots, or descriptors.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace GraphAtoms

open Encoding
open Program
open ComplexityReduction.Combinatorics.Graph

/-- The exact structural representation of one graph edge. -/
abbrev edgePresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.unaryNat StandardInstances.unaryNat

/-- The exact structural representation of an ordered graph edge list. -/
abbrev edgeListPresentation : LawfulEncodedType :=
  StandardInstances.list edgePresentation

/-- The exact structural representation of an edge-list/directedness payload. -/
abbrev graphPayloadPresentation : LawfulEncodedType :=
  StandardInstances.prod edgeListPresentation StandardInstances.bool

/-- The complete explicit identity of CR's faithful structured graph wrapper. -/
def graphStructuredShape : CodecShape :=
  .prod .unaryNat (.prod (.list (.prod .unaryNat .unaryNat)) .bool)

/--
The exact V2 presentation of CR's structured graph wrapper.

This is user-locked rather than structurally admitted: the legacy encoder's
carrier is the `GraphInput` structure, not the nested product carrier of the
standard structural constructors.
-/
def graphStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
  representation := graphStructuredShape.identity
  faithful := ⟨ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective⟩

/-- The graph presentation retains the exact legacy structured graph encoder. -/
@[simp]
theorem graphStructuredPresentation_encodedType :
    graphStructuredPresentation.encodedType =
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType :=
  rfl

/-- The graph presentation retains its full explicit representation identity. -/
@[simp]
theorem graphStructuredPresentation_representation :
    graphStructuredPresentation.representation = graphStructuredShape.identity :=
  rfl

/-- The graph presentation has exactly the legacy `GraphInput` carrier. -/
theorem graphStructuredPresentation_carrier_eq_GraphInput :
    graphStructuredPresentation.Carrier = GraphInput :=
  rfl

/-- A discoverable V2 endpoint for structured graph well-formedness. -/
@[complexity_reduction_ir_typed_problem]
def graphWellFormedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt graphStructuredPresentation ⟨WellFormed⟩

/-- The graph endpoint has exactly the semantic well-formedness predicate. -/
@[simp]
theorem graphWellFormedProblem_accepts (graph : graphWellFormedProblem.Instance) :
    graphWellFormedProblem.accepts graph ↔ WellFormed graph :=
  Iff.rfl

/-- The complete explicit identity of CR's structured Clique wrapper. -/
def cliqueStructuredShape : CodecShape :=
  .prod graphStructuredShape .unaryNat

/-- The exact V2 presentation of CR's structured Clique wrapper. -/
def cliqueStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Combinatorics.Graph.cliqueStructuredEncodedType
  representation := cliqueStructuredShape.identity
  faithful := ⟨ComplexityReduction.Combinatorics.Graph.cliqueStructuredEncodedType_encode_injective⟩

/-- The Clique presentation retains the full graph-plus-budget codec identity. -/
@[simp]
theorem cliqueStructuredPresentation_representation :
    cliqueStructuredPresentation.representation = cliqueStructuredShape.identity :=
  rfl

/-- The Clique presentation retains the exact legacy structured encoder. -/
@[simp]
theorem cliqueStructuredPresentation_encodedType :
    cliqueStructuredPresentation.encodedType =
      ComplexityReduction.Combinatorics.Graph.cliqueStructuredEncodedType :=
  rfl

/-- The exact V2 presentation of CR's structured Vertex-Cover wrapper. -/
def vertexCoverStructuredPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType
  representation := cliqueStructuredShape.identity
  faithful := ⟨ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType_encode_injective⟩

/-- Clique and Vertex Cover use distinct carriers but the same graph-plus-budget codec shape. -/
@[simp]
theorem vertexCoverStructuredPresentation_representation :
    vertexCoverStructuredPresentation.representation = cliqueStructuredShape.identity :=
  rfl

/-- A discoverable V2 endpoint for the existing structured Clique problem. -/
@[complexity_reduction_ir_typed_problem]
def cliqueStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt cliqueStructuredPresentation ⟨Clique⟩

/-- A discoverable V2 endpoint for the existing structured Vertex-Cover problem. -/
@[complexity_reduction_ir_typed_problem]
def vertexCoverStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt vertexCoverStructuredPresentation ⟨VertexCover⟩

/-- The Clique endpoint retains exactly the CR Clique semantics. -/
@[simp]
theorem cliqueStructuredProblem_accepts (input : cliqueStructuredProblem.Instance) :
    cliqueStructuredProblem.accepts input ↔ Clique input :=
  Iff.rfl

/-- The Vertex-Cover endpoint retains exactly the CR Vertex-Cover semantics. -/
@[simp]
theorem vertexCoverStructuredProblem_accepts (input : vertexCoverStructuredProblem.Instance) :
    vertexCoverStructuredProblem.accepts input ↔ VertexCover input :=
  Iff.rfl

/-- The direct-TM graph computations admitted by this family-local V2 leaf. -/
inductive PrimitiveRequest where
  | graphVertices
  | graphPayload
  | cliqueGraph
  | cliqueBudget
  | vertexCoverGraph
  | vertexCoverBudget
  | strictPairCandidates
  | complementEdgesFromCandidates
  | cliqueToVertexCover
  deriving DecidableEq, Repr

/-- The exact V2 source presentation required by each graph primitive request. -/
def sourcePresentation : PrimitiveRequest → LawfulEncodedType
  | .graphVertices => graphStructuredPresentation
  | .graphPayload => graphStructuredPresentation
  | .cliqueGraph => cliqueStructuredPresentation
  | .cliqueBudget => cliqueStructuredPresentation
  | .vertexCoverGraph => vertexCoverStructuredPresentation
  | .vertexCoverBudget => vertexCoverStructuredPresentation
  | .strictPairCandidates => StandardInstances.unaryNat
  | .complementEdgesFromCandidates =>
      StandardInstances.prod edgeListPresentation edgeListPresentation
  | .cliqueToVertexCover => cliqueStructuredPresentation

/-- The exact V2 target presentation required by each graph primitive request. -/
def targetPresentation : PrimitiveRequest → LawfulEncodedType
  | .graphVertices => StandardInstances.unaryNat
  | .graphPayload => graphPayloadPresentation
  | .cliqueGraph => graphStructuredPresentation
  | .cliqueBudget => StandardInstances.unaryNat
  | .vertexCoverGraph => graphStructuredPresentation
  | .vertexCoverBudget => StandardInstances.unaryNat
  | .strictPairCandidates => edgeListPresentation
  | .complementEdgesFromCandidates => edgeListPresentation
  | .cliqueToVertexCover => vertexCoverStructuredPresentation

/-- The direct-TM primitive required to answer one exact graph request. -/
abbrev RequiredPrimitive (request : PrimitiveRequest) : Type :=
  Primitive (sourcePresentation request) (targetPresentation request)

/-- Direct-TM graph-vertex projection for the exact custom graph presentation. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def graphVerticesPrimitive :
    Primitive (sourcePresentation .graphVertices) (targetPresentation .graphVertices) :=
  Primitive.ofTMPolyTime GraphInput.vertices (by
    simpa [sourcePresentation, targetPresentation, graphStructuredPresentation] using
      ComplexityReduction.Karp21.graphVerticesTMBackedMap.tm_polytime)

/-- The graph-vertex primitive executes precisely the legacy field projection. -/
@[simp]
theorem graphVerticesPrimitive_run (graph : (sourcePresentation .graphVertices).Carrier) :
    graphVerticesPrimitive.run graph = graph.vertices :=
  rfl

/-- The stored graph-vertex evidence certifies exactly its field-projection executable. -/
theorem graphVerticesPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .graphVertices).encodedType
      (targetPresentation .graphVertices).encodedType GraphInput.vertices := by
  simpa only [graphVerticesPrimitive_run] using graphVerticesPrimitive.tmPolyTime

/-- Direct-TM graph payload projection for the exact custom graph presentation. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def graphPayloadPrimitive :
    Primitive (sourcePresentation .graphPayload) (targetPresentation .graphPayload) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.graphPayloadOfGraph (by
    simpa [sourcePresentation, targetPresentation, graphStructuredPresentation,
      graphPayloadPresentation, edgeListPresentation, edgePresentation] using
      ComplexityReduction.Karp21.graphPayloadTMBackedMap.tm_polytime)

/-- The graph-payload primitive executes exactly the legacy payload projection. -/
@[simp]
theorem graphPayloadPrimitive_run (graph : (sourcePresentation .graphPayload).Carrier) :
    graphPayloadPrimitive.run graph = ComplexityReduction.Karp21.graphPayloadOfGraph graph :=
  rfl

/-- The stored graph-payload evidence certifies exactly its legacy projection executable. -/
theorem graphPayloadPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .graphPayload).encodedType
      (targetPresentation .graphPayload).encodedType
      ComplexityReduction.Karp21.graphPayloadOfGraph := by
  simpa only [graphPayloadPrimitive_run] using graphPayloadPrimitive.tmPolyTime

/-- Direct-TM projection of the graph field from a structured Clique input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueGraphPrimitive :
    Primitive (sourcePresentation .cliqueGraph) (targetPresentation .cliqueGraph) :=
  Primitive.ofTMPolyTime (fun input : CliqueInput => input.graph) (by
    simpa [sourcePresentation, targetPresentation, cliqueStructuredPresentation,
      graphStructuredPresentation] using
      ComplexityReduction.Karp21.cliqueGraphTMBackedMap.tm_polytime)

/-- The Clique graph primitive executes precisely the legacy graph-field projection. -/
@[simp]
theorem cliqueGraphPrimitive_run (input : (sourcePresentation .cliqueGraph).Carrier) :
    cliqueGraphPrimitive.run input = input.graph :=
  rfl

/-- The stored Clique graph evidence certifies exactly its field-projection executable. -/
theorem cliqueGraphPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .cliqueGraph).encodedType
      (targetPresentation .cliqueGraph).encodedType (fun input : CliqueInput => input.graph) := by
  simpa only [cliqueGraphPrimitive_run] using cliqueGraphPrimitive.tmPolyTime

/-- Direct-TM projection of the clique-size field from a structured Clique input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueBudgetPrimitive :
    Primitive (sourcePresentation .cliqueBudget) (targetPresentation .cliqueBudget) :=
  Primitive.ofTMPolyTime (fun input : CliqueInput => input.k) (by
    simpa [sourcePresentation, targetPresentation, cliqueStructuredPresentation] using
      ComplexityReduction.Karp21.cliqueBudgetTMBackedMap.tm_polytime)

/-- The Clique budget primitive executes precisely the legacy budget-field projection. -/
@[simp]
theorem cliqueBudgetPrimitive_run (input : (sourcePresentation .cliqueBudget).Carrier) :
    cliqueBudgetPrimitive.run input = input.k :=
  rfl

/-- The stored Clique budget evidence certifies exactly its field-projection executable. -/
theorem cliqueBudgetPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .cliqueBudget).encodedType
      (targetPresentation .cliqueBudget).encodedType (fun input : CliqueInput => input.k) := by
  simpa only [cliqueBudgetPrimitive_run] using cliqueBudgetPrimitive.tmPolyTime

/-- Direct-TM projection of the graph field from a structured Vertex-Cover input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def vertexCoverGraphPrimitive :
    Primitive (sourcePresentation .vertexCoverGraph) (targetPresentation .vertexCoverGraph) :=
  Primitive.ofTMPolyTime (fun input : VertexCoverInput => input.graph) (by
    simpa [sourcePresentation, targetPresentation, vertexCoverStructuredPresentation,
      graphStructuredPresentation] using
      ComplexityReduction.Karp21.vertexCoverGraphTMBackedMap.tm_polytime)

/-- The Vertex-Cover graph primitive executes precisely the legacy graph-field projection. -/
@[simp]
theorem vertexCoverGraphPrimitive_run (input : (sourcePresentation .vertexCoverGraph).Carrier) :
    vertexCoverGraphPrimitive.run input = input.graph :=
  rfl

/-- The stored Vertex-Cover graph evidence certifies exactly its field-projection executable. -/
theorem vertexCoverGraphPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .vertexCoverGraph).encodedType
      (targetPresentation .vertexCoverGraph).encodedType
      (fun input : VertexCoverInput => input.graph) := by
  simpa only [vertexCoverGraphPrimitive_run] using vertexCoverGraphPrimitive.tmPolyTime

/-- Direct-TM projection of the budget field from a structured Vertex-Cover input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def vertexCoverBudgetPrimitive :
    Primitive (sourcePresentation .vertexCoverBudget) (targetPresentation .vertexCoverBudget) :=
  Primitive.ofTMPolyTime (fun input : VertexCoverInput => input.k) (by
    simpa [sourcePresentation, targetPresentation, vertexCoverStructuredPresentation] using
      ComplexityReduction.Karp21.vertexCoverBudgetTMBackedMap.tm_polytime)

/-- The Vertex-Cover budget primitive executes precisely the legacy budget-field projection. -/
@[simp]
theorem vertexCoverBudgetPrimitive_run (input : (sourcePresentation .vertexCoverBudget).Carrier) :
    vertexCoverBudgetPrimitive.run input = input.k :=
  rfl

/-- The stored Vertex-Cover budget evidence certifies exactly its field-projection executable. -/
theorem vertexCoverBudgetPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .vertexCoverBudget).encodedType
      (targetPresentation .vertexCoverBudget).encodedType
      (fun input : VertexCoverInput => input.k) := by
  simpa only [vertexCoverBudgetPrimitive_run] using vertexCoverBudgetPrimitive.tmPolyTime

/--
The reusable direct-TM strict-pair generator used by graph-complement
constructions.  Its output is exactly the ordered list of bounded strict
vertex pairs, not an arbitrary candidate-list implementation.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def strictPairCandidatesPrimitive :
    Primitive (sourcePresentation .strictPairCandidates) (targetPresentation .strictPairCandidates) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.strictNatPairCandidates (by
    simpa [sourcePresentation, targetPresentation, edgeListPresentation, edgePresentation] using
      ComplexityReduction.Karp21.strictNatPairCandidates_tm_polytime)

/-- The strict-pair atom executes exactly CR's direct-TM candidate generator. -/
@[simp]
theorem strictPairCandidatesPrimitive_run
    (vertices : (sourcePresentation .strictPairCandidates).Carrier) :
    strictPairCandidatesPrimitive.run vertices =
      ComplexityReduction.Karp21.strictNatPairCandidates vertices :=
  rfl

/--
The reusable direct-TM complement scanner over an already supplied source-edge
and candidate-edge pair.  This is the exact component of the existing graph
complement construction, not a new route-local machine.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def complementEdgesFromCandidatesPrimitive :
    Primitive (sourcePresentation .complementEdgesFromCandidates)
      (targetPresentation .complementEdgesFromCandidates) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.complementEdgesFromCandidates (by
    simpa [sourcePresentation, targetPresentation, edgeListPresentation, edgePresentation] using
      ComplexityReduction.Karp21.complementEdgesFromCandidates_tm_polytime)

/-- The complement scanner executes exactly the legacy candidate-filter executable. -/
@[simp]
theorem complementEdgesFromCandidatesPrimitive_run
    (input : (sourcePresentation .complementEdgesFromCandidates).Carrier) :
    complementEdgesFromCandidatesPrimitive.run input =
      ComplexityReduction.Karp21.complementEdgesFromCandidates input :=
  rfl

/--
The complete existing structured Clique-to-Vertex-Cover executable, admitted
directly from its CR `TMPolyTimeMap`.  This declaration is only an atom; a
certified route must separately supply the existing semantic correctness proof.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueToVertexCoverPrimitive :
    Primitive (sourcePresentation .cliqueToVertexCover) (targetPresentation .cliqueToVertexCover) :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.VertexCover.map (by
    simpa [sourcePresentation, targetPresentation, cliqueStructuredPresentation,
      vertexCoverStructuredPresentation] using
      ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime)

/-- The full graph-family atom executes exactly the legacy Clique-to-Vertex-Cover map. -/
@[simp]
theorem cliqueToVertexCoverPrimitive_run
    (input : (sourcePresentation .cliqueToVertexCover).Carrier) :
    cliqueToVertexCoverPrimitive.run input = ComplexityReduction.Karp21.VertexCover.map input :=
  rfl

/-
The two equalities below are the endpoint audit for the existing standard
direct-TM map.  They deliberately identify its type indices with the concrete
tagged `PresentedProblem` declarations above; they do not introduce a second
route record, descriptor, or metadata endpoint.
-/

/-- The standard direct-TM Clique-to-Vertex-Cover map starts at the concrete Clique endpoint. -/
@[simp]
theorem cliqueToVertexCoverPrimitive_sourceEndpoint :
    sourcePresentation .cliqueToVertexCover = cliqueStructuredProblem.representation :=
  rfl

/-- The standard direct-TM Clique-to-Vertex-Cover map ends at the concrete Vertex-Cover endpoint. -/
@[simp]
theorem cliqueToVertexCoverPrimitive_targetEndpoint :
    targetPresentation .cliqueToVertexCover = vertexCoverStructuredProblem.representation :=
  rfl

/--
The concrete V2 registration surface for the existing Clique-to-Vertex-Cover
direct-TM primitive.

This declaration stores no new executable, cost map, or machine: it is the
family-local primitive above, re-indexed visibly by the two concrete V2
`PresentedProblem` declarations.  Consequently a registry capability for the
route endpoints can arise only by validating this V2 `Primitive` declaration's
elaborated type, never from a legacy theorem name or metadata record.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueToVertexCoverEndpointPrimitive :
    Primitive cliqueStructuredProblem.representation vertexCoverStructuredProblem.representation :=
  cliqueToVertexCoverPrimitive

/-- The endpoint-indexed registration primitive has exactly the one admitted executable. -/
@[simp]
theorem cliqueToVertexCoverEndpointPrimitive_run
    (input : cliqueStructuredProblem.Instance) :
    cliqueToVertexCoverEndpointPrimitive.run input =
      ComplexityReduction.Karp21.VertexCover.map input :=
  rfl

/--
The endpoint-indexed registration primitive retains the same direct-TM witness
as the family-local primitive; no cost-only evidence can enter this boundary.
-/
theorem cliqueToVertexCoverEndpointPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      cliqueStructuredProblem.representation.encodedType
      vertexCoverStructuredProblem.representation.encodedType
      ComplexityReduction.Karp21.VertexCover.map := by
  simpa only [cliqueToVertexCoverEndpointPrimitive_run] using
    cliqueToVertexCoverEndpointPrimitive.tmPolyTime

/-- The canonical V2 program atom for graph-vertex projection. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def graphVertices :
    PolyProg (sourcePresentation .graphVertices) (targetPresentation .graphVertices) :=
  .atom graphVerticesPrimitive

/-- The canonical V2 program atom for graph-payload projection. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def graphPayload :
    PolyProg (sourcePresentation .graphPayload) (targetPresentation .graphPayload) :=
  .atom graphPayloadPrimitive

/-- The canonical V2 program atom for the graph field of a structured Clique input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueGraph :
    PolyProg (sourcePresentation .cliqueGraph) (targetPresentation .cliqueGraph) :=
  .atom cliqueGraphPrimitive

/-- The canonical V2 program atom for the budget field of a structured Clique input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueBudget :
    PolyProg (sourcePresentation .cliqueBudget) (targetPresentation .cliqueBudget) :=
  .atom cliqueBudgetPrimitive

/-- The canonical V2 program atom for the graph field of a structured Vertex-Cover input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def vertexCoverGraph :
    PolyProg (sourcePresentation .vertexCoverGraph) (targetPresentation .vertexCoverGraph) :=
  .atom vertexCoverGraphPrimitive

/-- The canonical V2 program atom for the budget field of a structured Vertex-Cover input. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def vertexCoverBudget :
    PolyProg (sourcePresentation .vertexCoverBudget) (targetPresentation .vertexCoverBudget) :=
  .atom vertexCoverBudgetPrimitive

/-- The canonical V2 program atom for strict graph-pair generation. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def strictPairCandidates :
    PolyProg (sourcePresentation .strictPairCandidates) (targetPresentation .strictPairCandidates) :=
  .atom strictPairCandidatesPrimitive

/-- The canonical V2 program atom for candidate complement scanning. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def complementEdgesFromCandidates :
    PolyProg (sourcePresentation .complementEdgesFromCandidates)
      (targetPresentation .complementEdgesFromCandidates) :=
  .atom complementEdgesFromCandidatesPrimitive

/-- The canonical V2 program atom for the full existing Clique-to-Vertex-Cover construction. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def cliqueToVertexCover :
    PolyProg (sourcePresentation .cliqueToVertexCover) (targetPresentation .cliqueToVertexCover) :=
  .atom cliqueToVertexCoverPrimitive

/-- The canonical graph-vertex program executes exactly its admitted projection primitive. -/
@[simp]
theorem graphVertices_run (graph : (sourcePresentation .graphVertices).Carrier) :
    graphVertices.run graph = graph.vertices :=
  rfl

/-- The canonical graph-payload program executes exactly its admitted projection primitive. -/
@[simp]
theorem graphPayload_run (graph : (sourcePresentation .graphPayload).Carrier) :
    graphPayload.run graph = ComplexityReduction.Karp21.graphPayloadOfGraph graph :=
  rfl

/-- The canonical Clique graph program executes exactly its admitted projection primitive. -/
@[simp]
theorem cliqueGraph_run (input : (sourcePresentation .cliqueGraph).Carrier) :
    cliqueGraph.run input = input.graph :=
  rfl

/-- The canonical Clique budget program executes exactly its admitted projection primitive. -/
@[simp]
theorem cliqueBudget_run (input : (sourcePresentation .cliqueBudget).Carrier) :
    cliqueBudget.run input = input.k :=
  rfl

/-- The canonical Vertex-Cover graph program executes exactly its admitted projection primitive. -/
@[simp]
theorem vertexCoverGraph_run (input : (sourcePresentation .vertexCoverGraph).Carrier) :
    vertexCoverGraph.run input = input.graph :=
  rfl

/-- The canonical Vertex-Cover budget program executes exactly its admitted projection primitive. -/
@[simp]
theorem vertexCoverBudget_run (input : (sourcePresentation .vertexCoverBudget).Carrier) :
    vertexCoverBudget.run input = input.k :=
  rfl

/-- The canonical strict-pair program executes exactly its admitted candidate generator. -/
@[simp]
theorem strictPairCandidates_run
    (vertices : (sourcePresentation .strictPairCandidates).Carrier) :
    strictPairCandidates.run vertices =
      ComplexityReduction.Karp21.strictNatPairCandidates vertices :=
  rfl

/-- The canonical complement-scanner program executes exactly its admitted scanner. -/
@[simp]
theorem complementEdgesFromCandidates_run
    (input : (sourcePresentation .complementEdgesFromCandidates).Carrier) :
    complementEdgesFromCandidates.run input =
      ComplexityReduction.Karp21.complementEdgesFromCandidates input :=
  rfl

/-- The canonical Clique-to-Vertex-Cover program executes exactly its admitted construction. -/
@[simp]
theorem cliqueToVertexCover_run
    (input : (sourcePresentation .cliqueToVertexCover).Carrier) :
    cliqueToVertexCover.run input = ComplexityReduction.Karp21.VertexCover.map input :=
  rfl

/-- Compiling the exact V2 graph-vertex atom preserves its field-projection direct-TM witness. -/
theorem graphVertices_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .graphVertices).encodedType
      (targetPresentation .graphVertices).encodedType GraphInput.vertices := by
  simpa only [graphVertices_run] using graphVertices.compileTM

/-- Compiling the graph-payload program preserves its field-projection direct-TM witness. -/
theorem graphPayload_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .graphPayload).encodedType
      (targetPresentation .graphPayload).encodedType
      ComplexityReduction.Karp21.graphPayloadOfGraph := by
  simpa only [graphPayload_run] using graphPayload.compileTM

/-- Compiling the Clique graph program preserves its field-projection direct-TM witness. -/
theorem cliqueGraph_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .cliqueGraph).encodedType
      (targetPresentation .cliqueGraph).encodedType (fun input : CliqueInput => input.graph) := by
  simpa only [cliqueGraph_run] using cliqueGraph.compileTM

/-- Compiling the Clique budget program preserves its field-projection direct-TM witness. -/
theorem cliqueBudget_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .cliqueBudget).encodedType
      (targetPresentation .cliqueBudget).encodedType (fun input : CliqueInput => input.k) := by
  simpa only [cliqueBudget_run] using cliqueBudget.compileTM

/-- Compiling the Vertex-Cover graph program preserves its field-projection direct-TM witness. -/
theorem vertexCoverGraph_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .vertexCoverGraph).encodedType
      (targetPresentation .vertexCoverGraph).encodedType
      (fun input : VertexCoverInput => input.graph) := by
  simpa only [vertexCoverGraph_run] using vertexCoverGraph.compileTM

/-- Compiling the Vertex-Cover budget program preserves its field-projection direct-TM witness. -/
theorem vertexCoverBudget_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .vertexCoverBudget).encodedType
      (targetPresentation .vertexCoverBudget).encodedType
      (fun input : VertexCoverInput => input.k) := by
  simpa only [vertexCoverBudget_run] using vertexCoverBudget.compileTM

/-- Compiling the exact V2 strict-pair atom preserves its direct-TM witness. -/
theorem strictPairCandidates_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .strictPairCandidates).encodedType
      (targetPresentation .strictPairCandidates).encodedType
      ComplexityReduction.Karp21.strictNatPairCandidates := by
  simpa only [strictPairCandidates_run] using strictPairCandidates.compileTM

/-- Compiling the exact V2 complement scanner preserves its direct-TM witness. -/
theorem complementEdgesFromCandidates_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .complementEdgesFromCandidates).encodedType
      (targetPresentation .complementEdgesFromCandidates).encodedType
      ComplexityReduction.Karp21.complementEdgesFromCandidates := by
  simpa only [complementEdgesFromCandidates_run] using
    complementEdgesFromCandidates.compileTM

/-- Compiling the full V2 Clique-to-Vertex-Cover atom preserves its direct-TM witness. -/
theorem cliqueToVertexCover_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (sourcePresentation .cliqueToVertexCover).encodedType
      (targetPresentation .cliqueToVertexCover).encodedType
      ComplexityReduction.Karp21.VertexCover.map := by
  simpa only [cliqueToVertexCover_run] using cliqueToVertexCover.compileTM

/-- Resolve an available graph request only by its exact direct-TM-backed V2 primitive. -/
noncomputable def resolvePrimitive (request : PrimitiveRequest) :
    Except (Protocol.MissingCapability PrimitiveRequest) (RequiredPrimitive request) :=
  match request with
  | .graphVertices => .ok graphVerticesPrimitive
  | .graphPayload => .ok graphPayloadPrimitive
  | .cliqueGraph => .ok cliqueGraphPrimitive
  | .cliqueBudget => .ok cliqueBudgetPrimitive
  | .vertexCoverGraph => .ok vertexCoverGraphPrimitive
  | .vertexCoverBudget => .ok vertexCoverBudgetPrimitive
  | .strictPairCandidates => .ok strictPairCandidatesPrimitive
  | .complementEdgesFromCandidates => .ok complementEdgesFromCandidatesPrimitive
  | .cliqueToVertexCover => .ok cliqueToVertexCoverPrimitive

/-- The full structured Clique-to-Vertex-Cover request resolves to its exact direct-TM atom. -/
@[simp]
theorem resolvePrimitive_cliqueToVertexCover :
    resolvePrimitive .cliqueToVertexCover = .ok cliqueToVertexCoverPrimitive :=
  rfl

/-- Graph-family computations not currently backed by exact CR direct-TM evidence. -/
inductive MissingPrimitiveRequest where
  | incidenceConstruction
  | roleAssignment
  | neighborLookup (vertex : Nat)
  | requiredRoleCheck
  | selectableRoleCheck
  deriving DecidableEq, Repr

/--
The only blocker admitted for an unavailable graph operation.  It preserves
the exact closed request and says only that its canonical shared primitive is
absent; it carries no executable, cost evidence, or TM evidence.
-/
def missingPrimitive (request : MissingPrimitiveRequest) :
    Protocol.MissingCapability MissingPrimitiveRequest :=
  .primitive request

/--
No exact V2/CR direct-TM primitive currently computes the requested
Incidence-to-RoleGraph construction.  This result carries no executable or
cost/TM evidence.
-/
def missingIncidenceConstruction : Protocol.MissingCapability MissingPrimitiveRequest :=
  missingPrimitive .incidenceConstruction

/-- Missing role assignment is represented by a typed blocker, never a local function. -/
def missingRoleAssignment : Protocol.MissingCapability MissingPrimitiveRequest :=
  missingPrimitive .roleAssignment

/-- Missing neighbour lookup remains indexed by the exact queried vertex. -/
def missingNeighborLookup (vertex : Nat) : Protocol.MissingCapability MissingPrimitiveRequest :=
  missingPrimitive (.neighborLookup vertex)

/-- Missing required-role checking is a typed primitive blocker. -/
def missingRequiredRoleCheck : Protocol.MissingCapability MissingPrimitiveRequest :=
  missingPrimitive .requiredRoleCheck

/-- Missing selectable-role checking is a typed primitive blocker. -/
def missingSelectableRoleCheck : Protocol.MissingCapability MissingPrimitiveRequest :=
  missingPrimitive .selectableRoleCheck

/-- Every unavailable graph operation retains its exact missing request. -/
@[simp]
theorem missingPrimitive_endpoint (request : MissingPrimitiveRequest) :
    (missingPrimitive request).endpoint = request :=
  rfl

/-- Every unavailable graph operation is blocked specifically by the absent primitive. -/
@[simp]
theorem missingPrimitive_reason (request : MissingPrimitiveRequest) :
    (missingPrimitive request).reason = .primitive :=
  rfl

/-- The incidence blocker records the exact missing request and no fabricated capability. -/
@[simp]
theorem missingIncidenceConstruction_endpoint :
    missingIncidenceConstruction.endpoint = .incidenceConstruction :=
  rfl

/-- Role assignment retains its exact missing request. -/
@[simp]
theorem missingRoleAssignment_endpoint :
    missingRoleAssignment.endpoint = .roleAssignment :=
  rfl

/-- The neighbour-lookup blocker retains the exact queried vertex. -/
@[simp]
theorem missingNeighborLookup_endpoint (vertex : Nat) :
    (missingNeighborLookup vertex).endpoint = .neighborLookup vertex :=
  rfl

/-- Required-role checking retains its exact missing request. -/
@[simp]
theorem missingRequiredRoleCheck_endpoint :
    missingRequiredRoleCheck.endpoint = .requiredRoleCheck :=
  rfl

/-- Selectable-role checking retains its exact missing request. -/
@[simp]
theorem missingSelectableRoleCheck_endpoint :
    missingSelectableRoleCheck.endpoint = .selectableRoleCheck :=
  rfl

/-- The incidence construction is blocked specifically by the absent primitive. -/
@[simp]
theorem missingIncidenceConstruction_reason : missingIncidenceConstruction.reason = .primitive :=
  rfl

/-- Role assignment is blocked specifically by the absent primitive. -/
@[simp]
theorem missingRoleAssignment_reason : missingRoleAssignment.reason = .primitive :=
  rfl

/-- Neighbour lookup is blocked specifically by the absent primitive. -/
@[simp]
theorem missingNeighborLookup_reason (vertex : Nat) :
    (missingNeighborLookup vertex).reason = .primitive :=
  rfl

/-- Required-role checking is blocked specifically by the absent primitive. -/
@[simp]
theorem missingRequiredRoleCheck_reason : missingRequiredRoleCheck.reason = .primitive :=
  rfl

/-- Selectable-role checking is blocked specifically by the absent primitive. -/
@[simp]
theorem missingSelectableRoleCheck_reason : missingSelectableRoleCheck.reason = .primitive :=
  rfl

/--
Resolve every unavailable graph request only to its exact typed blocker.
The empty success branch makes it impossible to introduce a route-local
function, bare cost map, legacy metadata, or local TM as a substitute.
-/
def resolveMissingPrimitive (request : MissingPrimitiveRequest) :
    Except (Protocol.MissingCapability MissingPrimitiveRequest) Empty :=
  .error (missingPrimitive request)

/--
The common result type of a closed graph-family primitive admission request.

The success branch is intentionally `Empty`: this is the family-local
fail-closed boundary for operations such as the raw legacy
`IncidenceView -> RoleGraphView` construction or the legacy Graph-to-RoleGraph
role-assignment support.  In particular, a legacy packet, a raw Lean function,
or a cost projection cannot be placed in this result in lieu of an exact
`Primitive`.
-/
abbrev MissingPrimitiveResolution (_request : MissingPrimitiveRequest) : Type :=
  Except (Protocol.MissingCapability MissingPrimitiveRequest) Empty

/--
The exact closed admission result for the missing shared
Incidence-to-RoleGraph construction primitive.

This declaration deliberately does not import the old incidence packet or
its raw/cost construction evidence.  Those artifacts have no V2 primitive
admission path at this endpoint.
-/
def resolveIncidenceConstruction :
    MissingPrimitiveResolution .incidenceConstruction :=
  resolveMissingPrimitive .incidenceConstruction

/--
The exact closed admission result for the missing Graph-to-RoleGraph
role-assignment primitive.

In particular, the legacy route-local identity/cost evidence is not a
substitute for a primitive from the structured graph presentation to the
canonical RoleGraph presentation.
-/
def resolveRoleAssignment :
    MissingPrimitiveResolution .roleAssignment :=
  resolveMissingPrimitive .roleAssignment

/-- The incidence-construction request resolves to its exact closed blocker. -/
@[simp]
theorem resolveMissingPrimitive_incidenceConstruction :
    resolveMissingPrimitive .incidenceConstruction = .error missingIncidenceConstruction :=
  rfl

/-- The closed incidence-construction admission preserves its exact blocker. -/
@[simp]
theorem resolveIncidenceConstruction_exact :
    resolveIncidenceConstruction = .error missingIncidenceConstruction :=
  rfl

/-- The role-assignment request resolves to its exact closed blocker. -/
@[simp]
theorem resolveMissingPrimitive_roleAssignment :
    resolveMissingPrimitive .roleAssignment = .error missingRoleAssignment :=
  rfl

/-- The closed role-assignment admission preserves its exact blocker. -/
@[simp]
theorem resolveRoleAssignment_exact :
    resolveRoleAssignment = .error missingRoleAssignment :=
  rfl

/-- A neighbour lookup resolves to the blocker indexed by that same vertex. -/
@[simp]
theorem resolveMissingPrimitive_neighborLookup (vertex : Nat) :
    resolveMissingPrimitive (.neighborLookup vertex) = .error (missingNeighborLookup vertex) :=
  rfl

/-- Required-role checking resolves to its exact closed blocker. -/
@[simp]
theorem resolveMissingPrimitive_requiredRoleCheck :
    resolveMissingPrimitive .requiredRoleCheck = .error missingRequiredRoleCheck :=
  rfl

/-- Selectable-role checking resolves to its exact closed blocker. -/
@[simp]
theorem resolveMissingPrimitive_selectableRoleCheck :
    resolveMissingPrimitive .selectableRoleCheck = .error missingSelectableRoleCheck :=
  rfl

/-- No missing graph request has a success branch from which a capability could arise. -/
theorem resolveMissingPrimitive_no_success (request : MissingPrimitiveRequest) :
    ¬ ∃ result, resolveMissingPrimitive request = .ok result := by
  rintro ⟨result, _⟩
  exact Empty.elim result

/-- No raw legacy incidence construction can enter the exact primitive admission result. -/
theorem resolveIncidenceConstruction_no_success :
    ¬ ∃ result, resolveIncidenceConstruction = .ok result :=
  resolveMissingPrimitive_no_success .incidenceConstruction

/-- No raw legacy role-assignment construction can enter the exact primitive admission result. -/
theorem resolveRoleAssignment_no_success :
    ¬ ∃ result, resolveRoleAssignment = .ok result :=
  resolveMissingPrimitive_no_success .roleAssignment

end GraphAtoms
end Karp21
end Problems
end ComplexityReduction
