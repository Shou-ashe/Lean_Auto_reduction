/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Basic
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of CR's structured `GraphInput` carrier.

`ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType` already
contains the concrete finite-alphabet encoder and a proof of its injectivity.
This leaf binds that exact encoder to its full layout identity and exposes
semantic graph endpoints at that representation.

Although its encoded payload has a product/list shape, `GraphInput` is a
custom wrapper around that payload.  There is consequently no closed
`StructuralRepresentationOrigin` whose indexed encoded type is this wrapper
encoder.  The presentation below is intentionally user-locked: it exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace Graph

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete ordered layout of a structured graph: vertices, edge list, and directed flag. -/
def structuredShape : CodecShape :=
  .prod .unaryNat (.prod (.list (.prod .unaryNat .unaryNat)) .bool)

/--
The exact lawful V2 presentation of CR's `GraphInput` structured encoder.

This is deliberately a user-selected presentation rather than an automatic
one: faithful encoding alone, including this reused CR injectivity theorem,
does not provide structural admission for a custom wrapper carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := graphStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨graphStructuredEncodedType_encode_injective⟩

/-- The presentation wraps exactly CR's structured graph encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = graphStructuredEncodedType :=
  rfl

/-- The representation identity retains the vertex/edge/directed field layout. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The represented carrier is exactly CR's graph syntax, not an erased interchange value. -/
theorem structuredPresentation_carrier_eq_graphInput :
    structuredPresentation.Carrier = GraphInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's existing structured graph encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = graphStructuredEncodedType.encode input :=
  rfl

/-- The graph semantic problem before it is paired with the selected structured presentation. -/
def semanticProblem (predicate : GraphInput → Prop) : ComplexityReduction.DecisionProblem where
  Instance := GraphInput
  isYes := predicate

/-- The generic semantic graph endpoint keeps precisely its supplied graph predicate. -/
@[simp]
theorem semanticProblem_isYes (predicate : GraphInput → Prop) (input : GraphInput) :
    (semanticProblem predicate).isYes input ↔ predicate input :=
  Iff.rfl

/-- A graph predicate interpreted at exactly the selected structured graph presentation. -/
def problemAt (predicate : GraphInput → Prop) : ProblemAt structuredPresentation where
  isYes := predicate

/--
The V2 presented graph problem for an arbitrary graph predicate.

The construction uses the exact graph presentation above rather than CR's
raw `Graph.decisionProblem` compatibility encoder.
-/
def presentedProblem (predicate : GraphInput → Prop) : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation (problemAt predicate)

/-- Every generic graph endpoint retains the exact selected structured presentation. -/
@[simp]
theorem presentedProblem_representation (predicate : GraphInput → Prop) :
    (presentedProblem predicate).representation = structuredPresentation :=
  rfl

/-- Every generic graph endpoint projects to precisely the structured graph encoder. -/
@[simp]
theorem presentedProblem_backendEndpoint_instance (predicate : GraphInput → Prop) :
    (presentedProblem predicate).backendEndpoint.Instance = graphStructuredEncodedType :=
  rfl

/-- Every generic graph endpoint retains the complete graph representation identity. -/
@[simp]
theorem presentedProblem_representationIdentity (predicate : GraphInput → Prop) :
    (presentedProblem predicate).representationIdentity = structuredShape.identity :=
  rfl

/-- The typed graph predicate remains definitionally the predicate supplied to the facade. -/
@[simp]
theorem problemAt_isYes (predicate : GraphInput → Prop) (input : structuredPresentation.Carrier) :
    (problemAt predicate).isYes input ↔ predicate input :=
  Iff.rfl

/-- The endpoint acceptance predicate remains aligned with its supplied graph semantics. -/
@[simp]
theorem presentedProblem_accepts (predicate : GraphInput → Prop)
    (input : (presentedProblem predicate).Instance) :
    (presentedProblem predicate).accepts input ↔ predicate input :=
  Iff.rfl

/-- The graph-bound predicate at the selected structured presentation. -/
def wellFormedProblemAt : ProblemAt structuredPresentation :=
  problemAt WellFormed

/-
The custom graph wrapper has no closed structural certificate, so
`structuredPresentation` is intentionally not tagged as automatically
selectable presentation evidence.  The concrete well-formed endpoint below
is nevertheless a valid registry candidate because its elaborated type is
exactly `PresentedProblem`.
-/
/-- The canonical V2 endpoint for well-formed structured graph instances. -/
@[complexity_reduction_ir_typed_problem]
def wellFormedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation wellFormedProblemAt

/-- The well-formed graph endpoint retains exactly the selected graph presentation. -/
@[simp]
theorem wellFormedProblem_representation :
    wellFormedProblem.representation = structuredPresentation :=
  rfl

/-- The well-formed graph endpoint projects to CR's structured graph encoder. -/
@[simp]
theorem wellFormedProblem_backendEndpoint_instance :
    wellFormedProblem.backendEndpoint.Instance = graphStructuredEncodedType :=
  rfl

/-- The well-formed graph endpoint retains the complete graph codec identity. -/
@[simp]
theorem wellFormedProblem_representationIdentity :
    wellFormedProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The fixed-presentation predicate is exactly CR's graph well-formedness predicate. -/
@[simp]
theorem wellFormedProblemAt_isYes (input : structuredPresentation.Carrier) :
    wellFormedProblemAt.isYes input ↔ WellFormed input :=
  Iff.rfl

/-- The V2 endpoint has exactly the established graph-bound semantics. -/
@[simp]
theorem wellFormedProblem_accepts (input : wellFormedProblem.Instance) :
    wellFormedProblem.accepts input ↔ WellFormed input :=
  Iff.rfl

end Graph
end Presentation
end ComplexityReduction
