/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Basic

/-!
Canonical IR-side target for the Exactly-One-Neighbor graph problem.

This module gives benchmark and route-planning code a stable library target.
The checked membership packet lives in `ComplexityReduction.Verification.GraphWitness`;
this module records the stable theorem names in the target descriptor.
-/

namespace ComplexityReduction

/-- Exactly-One-Neighbor instance: a graph and the vertices that must be covered. -/
structure ExactlyOneNeighborInput where
  graph : ComplexityReduction.Combinatorics.Graph.GraphInput
  R : List Nat
  deriving Repr

/-- Raw stable encoding for the canonical Exactly-One-Neighbor target. -/
def exactlyOneNeighborEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.raw ExactlyOneNeighborInput

/-- Structured finite-alphabet encoding for the required-vertex list. -/
def exactlyOneNeighborRequiredVerticesStructuredEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat

/-- Tuple-shaped finite-alphabet encoding for Exactly-One-Neighbor fields. -/
def exactlyOneNeighborTupleStructuredEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    exactlyOneNeighborRequiredVerticesStructuredEncodedType

/--
Concrete finite-alphabet encoding for canonical Exactly-One-Neighbor targets.

The existing Phase-1 lower-bound and membership wrappers still use the raw
target problem below.  This structured encoding is the target-encoding surface
needed before a future native-IR route can replace those raw wrappers.
-/
def exactlyOneNeighborStructuredEncodedType : ComplexityReduction.EncodedType where
  Carrier := ExactlyOneNeighborInput
  Symbol := exactlyOneNeighborTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => exactlyOneNeighborTupleStructuredEncodedType.encode (I.graph, I.R)

theorem exactlyOneNeighborRequiredVerticesStructuredEncodedType_encode_injective :
    Function.Injective exactlyOneNeighborRequiredVerticesStructuredEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective
    ComplexityReduction.EncodedType.nat_encode_injective

theorem exactlyOneNeighborTupleStructuredEncodedType_encode_injective :
    Function.Injective exactlyOneNeighborTupleStructuredEncodedType.encode :=
  ComplexityReduction.EncodedType.prod_encode_injective
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective
    exactlyOneNeighborRequiredVerticesStructuredEncodedType_encode_injective

theorem exactlyOneNeighborStructuredEncodedType_encode_injective :
    Function.Injective exactlyOneNeighborStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.R) = (J.graph, J.R) :=
    exactlyOneNeighborTupleStructuredEncodedType_encode_injective (by
      simpa [exactlyOneNeighborStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- The structured Exactly-One-Neighbor encoding is exactly the graph field plus `R`. -/
theorem exactlyOneNeighborStructured_inputSize_eq (I : ExactlyOneNeighborInput) :
    exactlyOneNeighborStructuredEncodedType.inputSize I =
      (ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.inputSize
        I.graph) + 1 +
        exactlyOneNeighborRequiredVerticesStructuredEncodedType.inputSize I.R := by
  change exactlyOneNeighborTupleStructuredEncodedType.inputSize (I.graph, I.R) = _
  simp [exactlyOneNeighborTupleStructuredEncodedType]

/-- Vertex `v` has exactly one graph neighbor in the selected list `S`. -/
def HasExactlyOneNeighborIn
    (g : ComplexityReduction.Combinatorics.Graph.GraphInput) (S : List Nat) (v : Nat) :
    Prop :=
  ∃ u, u ∈ S ∧ ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge g u v ∧
    ∀ u', u' ∈ S →
      ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge g u' v → u' = u

/-- Every vertex in `R` has exactly one graph neighbor in `S`. -/
def AllVerticesHaveExactlyOneNeighborIn
    (g : ComplexityReduction.Combinatorics.Graph.GraphInput) (R S : List Nat) : Prop :=
  ∀ v ∈ R, HasExactlyOneNeighborIn g S v

/-- A candidate witness for the canonical Exactly-One-Neighbor target. -/
def ExactlyOneNeighborWitness (I : ExactlyOneNeighborInput) (S : List Nat) : Prop :=
  S.Nodup ∧
    ComplexityReduction.Combinatorics.Graph.VerticesWithinBounds I.graph S ∧
    ComplexityReduction.Combinatorics.Graph.VerticesWithinBounds I.graph I.R ∧
    AllVerticesHaveExactlyOneNeighborIn I.graph I.R S

/-- Yes predicate for the canonical Exactly-One-Neighbor target. -/
def ExactlyOneNeighborYes (I : ExactlyOneNeighborInput) : Prop :=
  ∃ S : List Nat, ExactlyOneNeighborWitness I S

/-- Encoded decision problem for the canonical Exactly-One-Neighbor target. -/
def exactlyOneNeighborDecisionProblem : ComplexityReduction.EncodedDecisionProblem where
  Instance := exactlyOneNeighborEncodedType
  isYes := ExactlyOneNeighborYes

/-- Structured finite-alphabet decision problem for canonical Exactly-One-Neighbor. -/
def exactlyOneNeighborStructuredDecisionProblem : ComplexityReduction.EncodedDecisionProblem where
  Instance := exactlyOneNeighborStructuredEncodedType
  isYes := ExactlyOneNeighborYes

@[simp] theorem exactlyOneNeighborDecisionProblem_isYes (I : ExactlyOneNeighborInput) :
    exactlyOneNeighborDecisionProblem.isYes I = ExactlyOneNeighborYes I :=
  rfl

@[simp] theorem exactlyOneNeighborStructuredDecisionProblem_isYes (I : ExactlyOneNeighborInput) :
    exactlyOneNeighborStructuredDecisionProblem.isYes I = ExactlyOneNeighborYes I :=
  rfl

/--
Capability-card metadata for canonical graph targets.

The three theorem tracks are separate by design: a lower-bound edge does not
imply membership, and NP-completeness is blocked until both are present.
-/
structure CanonicalTargetCapabilityCard where
  name : String
  problemSymbol : String
  structuredProblemSymbol : Option String := none
  inputSymbol : String
  structuredInputEncodingSymbol : Option String := none
  witnessPredicateSymbol : String
  yesPredicateSymbol : String
  encodingStatus : String := "raw_only"
  lowerBoundTheorem : Option String := none
  membershipTheorem : Option String := none
  structuredMembershipTheorem : Option String := none
  structuredMembershipPacket : Option String := none
  completenessTheorem : Option String := none
  lowerBoundStatus : String
  membershipStatus : String
  completenessStatus : String
  nativeMigrationStatus : String := "metadata_only_pending_ir"
  nativeMigrationMissingObligations : List String := []
  missingObligations : List String := []
  roles : List String := ["canonical_target"]
  deriving Repr

/-- Target descriptor for the canonical Exactly-One-Neighbor decision problem. -/
def exactlyOneNeighborTargetDescriptor : CanonicalTargetCapabilityCard :=
  { name := "exactly_one_neighbor"
    problemSymbol := "ComplexityReduction.exactlyOneNeighborDecisionProblem"
    structuredProblemSymbol :=
      some "ComplexityReduction.exactlyOneNeighborStructuredDecisionProblem"
    inputSymbol := "ComplexityReduction.ExactlyOneNeighborInput"
    structuredInputEncodingSymbol :=
      some "ComplexityReduction.exactlyOneNeighborStructuredEncodedType"
    witnessPredicateSymbol := "ComplexityReduction.ExactlyOneNeighborWitness"
    yesPredicateSymbol := "ComplexityReduction.ExactlyOneNeighborYes"
    encodingStatus := "structured_encoding_surface_available_raw_routes_pending"
    lowerBoundTheorem := some "ComplexityReduction.exactlyOneNeighbor_NPHard"
    membershipTheorem := some "ComplexityReduction.exactlyOneNeighbor_inNP"
    structuredMembershipTheorem :=
      some "ComplexityReduction.exactlyOneNeighborStructured_inNP"
    structuredMembershipPacket :=
      some "ComplexityReduction.exactlyOneNeighborStructuredFiniteWitnessMembershipPacket"
    completenessTheorem := some "ComplexityReduction.exactlyOneNeighbor_NPComplete"
    lowerBoundStatus := "proved_phase1_lower_bound"
    membershipStatus := "proved_phase1_membership_structured_packet_available"
    completenessStatus := "proved_phase1_np_complete"
    nativeMigrationStatus := "metadata_only_pending_ir"
    nativeMigrationMissingObligations :=
      [ "missing_exact_cover_to_exactly_one_neighbor_structured_cost_certificate",
        "missing_exact_cover_to_exactly_one_neighbor_tm_backed_certificate",
        "missing_exactly_one_neighbor_structured_checker_tm_backed_certificate",
        "missing_raw_empty_output_replacement" ]
    missingObligations := []
    roles :=
      [ "canonical_target", "graph_target", "exactly_one_neighbor",
        "structured_encoding_surface",
        "structured_membership_available",
        "lower_bound_available", "membership_available", "np_complete_available" ] }

/-- Public canonical graph target descriptors currently exposed by the IR layer. -/
def canonicalGraphTargetDescriptors : List CanonicalTargetCapabilityCard :=
  [exactlyOneNeighborTargetDescriptor]

theorem canonicalGraphTargetDescriptors_length :
    canonicalGraphTargetDescriptors.length = 1 :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_membership_theorem :
    exactlyOneNeighborTargetDescriptor.membershipTheorem =
      some "ComplexityReduction.exactlyOneNeighbor_inNP" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_completeness_theorem :
    exactlyOneNeighborTargetDescriptor.completenessTheorem =
      some "ComplexityReduction.exactlyOneNeighbor_NPComplete" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_lower_bound_theorem :
    exactlyOneNeighborTargetDescriptor.lowerBoundTheorem =
      some "ComplexityReduction.exactlyOneNeighbor_NPHard" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_structured_problem :
    exactlyOneNeighborTargetDescriptor.structuredProblemSymbol =
      some "ComplexityReduction.exactlyOneNeighborStructuredDecisionProblem" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_structured_encoding :
    exactlyOneNeighborTargetDescriptor.structuredInputEncodingSymbol =
      some "ComplexityReduction.exactlyOneNeighborStructuredEncodedType" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_structured_membership_theorem :
    exactlyOneNeighborTargetDescriptor.structuredMembershipTheorem =
      some "ComplexityReduction.exactlyOneNeighborStructured_inNP" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_structured_membership_packet :
    exactlyOneNeighborTargetDescriptor.structuredMembershipPacket =
      some "ComplexityReduction.exactlyOneNeighborStructuredFiniteWitnessMembershipPacket" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_native_migration_status :
    exactlyOneNeighborTargetDescriptor.nativeMigrationStatus =
      "metadata_only_pending_ir" :=
  rfl

theorem exactlyOneNeighborTargetDescriptor_no_missing_obligations :
    exactlyOneNeighborTargetDescriptor.missingObligations = [] :=
  rfl

end ComplexityReduction
