/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Max Cut endpoint.

`partitionToMaxCutStructuredTMKarpReduction` consumes
`maxCutStructuredDecisionProblem`.  This leaf therefore binds exactly that
endpoint's finite-alphabet encoder and predicate to a distinct V2
representation identity.  `MaxCutInput` is a custom wrapper around a graph
and unary threshold, so it is intentionally user-locked: its payload shape
does not supply a structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace MaxCut

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph-and-unary-cut-threshold layout of a Max Cut input. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/--
The exact lawful V2 presentation of CR's structured Max Cut encoder.

The carrier is a custom `MaxCutInput` wrapper, rather than the product carrier
denoted by `structuredShape`; thus the reused injectivity theorem establishes
lawfulness but does not establish structural admission.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := maxCutStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨maxCutStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Max Cut encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = maxCutStructuredEncodedType :=
  rfl

/-- The representation identity records all graph fields and the unary cut threshold. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's Max Cut wrapper syntax. -/
theorem structuredPresentation_carrier_eq_MaxCutInput :
    structuredPresentation.Carrier = MaxCutInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = maxCutStructuredEncodedType.encode input :=
  rfl

/-- The existing Max Cut predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := MaxCut

/-- The canonical V2 endpoint for CR's structured Karp21 Max Cut problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Max Cut presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete graph-and-threshold representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's structured Max Cut decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = maxCutStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Max Cut semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ MaxCut input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Max Cut instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ MaxCut input :=
  Iff.rfl

end MaxCut
end Presentation
end ComplexityReduction
