/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Presentation.Knapsack

/-!
Canonical V2 presentation of CR's binary-numeric structured Knapsack endpoint.

`Knapsack.knapsackStructuredToBinaryStructuredTMKarpReduction` targets
`knapsackBinaryStructuredDecisionProblem`.  Its carrier remains the custom
`KnapsackInput` wrapper used by the unary presentation, but every item weight,
item value, capacity, and target value uses the binary-natural codec.  The
full shape records that distinction, so sharing the carrier cannot collapse
the unary and binary representations.  This endpoint is explicitly
user-locked: it exports no structural certificate or automatic admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace KnapsackBinary

open Encoding
open ComplexityReduction.Combinatorics

/-- The complete binary-natural layout of Knapsack items, capacity, and target value. -/
def structuredShape : CodecShape :=
  .prod (.list (.prod .binaryNat .binaryNat)) (.prod .binaryNat .binaryNat)

/--
The exact lawful V2 presentation of CR's binary-numeric structured Knapsack
encoder. `KnapsackInput` is a custom three-field wrapper rather than the
nested product denoted by `structuredShape`, so faithful encoding alone does
not make this presentation structurally automatic.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := knapsackBinaryStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨knapsackBinaryStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's binary structured Knapsack encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = knapsackBinaryStructuredEncodedType :=
  rfl

/-- The representation identity records binary codecs for all four numeric field positions. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The binary structured presentation has CR's established Knapsack wrapper carrier. -/
theorem structuredPresentation_carrier_eq_KnapsackInput :
    structuredPresentation.Carrier = KnapsackInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's binary structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = knapsackBinaryStructuredEncodedType.encode input :=
  rfl

/-- Binary and unary Knapsack presentations retain distinct complete representation identities. -/
theorem structuredPresentation_representation_ne_unary :
    structuredPresentation.representation ≠ Knapsack.structuredPresentation.representation := by
  rw [structuredPresentation_representation, Knapsack.structuredPresentation_representation]
  exact CodecShape.identity_ne_of_shape_ne (by decide)

/-- The existing Knapsack predicate at CR's exact binary structured presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := Knapsack

/-- The canonical V2 endpoint for CR's binary-numeric structured Knapsack problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected binary Knapsack presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete binary-natural Knapsack representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's binary structured Knapsack problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = knapsackBinaryStructuredDecisionProblem :=
  rfl

/-- The presented fixed-representation predicate is definitionally CR's Knapsack semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ Knapsack input :=
  Iff.rfl

/-- The typed binary endpoint accepts exactly the existing Knapsack instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ Knapsack input :=
  Iff.rfl

end KnapsackBinary
end Presentation
end ComplexityReduction
