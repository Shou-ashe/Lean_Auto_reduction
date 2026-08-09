/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of the unary structured Karp21 Knapsack endpoint.

This leaf selects `knapsackStructuredEncodedType`, not the raw compatibility
encoder `knapsackEncodedType`.  It is exactly the source endpoint of
`Karp21.JobSequencing.knapsackToJobSequencingStructuredTMKarpReduction`.
Its `KnapsackInput` carrier is a custom three-field wrapper around the
standard payload layout, so the presentation is explicitly user-selected and
intentionally exports no structural certificate or automatic-presentation
admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace Knapsack

open Encoding
open ComplexityReduction.Combinatorics

/-- The complete unary layout of Knapsack items, capacity, and target value. -/
def structuredShape : CodecShape :=
  .prod (.list (.prod .unaryNat .unaryNat)) (.prod .unaryNat .unaryNat)

/--
The exact lawful V2 presentation of CR's unary structured Knapsack encoder.

The carrier remains CR's custom `KnapsackInput` syntax rather than the nested
product denoted by `structuredShape`; therefore faithful encoding alone does
not admit this presentation as structural.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := knapsackStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨knapsackStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's unary structured Knapsack encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = knapsackStructuredEncodedType :=
  rfl

/-- The representation identity records every item, capacity, and target-value field. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's established Knapsack syntax. -/
theorem structuredPresentation_carrier_eq_KnapsackInput :
    structuredPresentation.Carrier = KnapsackInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established unary structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = knapsackStructuredEncodedType.encode input :=
  rfl

/-- The existing Knapsack predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := Knapsack

/-- The canonical V2 endpoint for CR's unary structured Karp21 Knapsack problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Knapsack presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete unary Knapsack representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's unary structured Knapsack problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = knapsackStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Knapsack semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ Knapsack input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Knapsack instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ Knapsack input :=
  Iff.rfl

end Knapsack
end Presentation
end ComplexityReduction
