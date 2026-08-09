/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Encoding.Core

/-!
Canonical typed graph-colouring hub.

The carrier deliberately separates the graph payload from its colour bound.
It is not the concrete `ChromaticNumberInput` wrapper, so a source-specific
adapter owns that wrapper normalization while any future shared gadget is
indexed only by this hub and its target hub.
-/

namespace ComplexityReduction
namespace Domain

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- A graph-colouring instance retaining both its graph and colour bound. -/
abbrev GraphColoringIR : Type := GraphInput × Nat

namespace GraphColoringIR

/-- The graph component of a canonical graph-colouring instance. -/
def graph (input : GraphColoringIR) : GraphInput :=
  input.1

/-- The retained colour bound of a canonical graph-colouring instance. -/
def colors (input : GraphColoringIR) : Nat :=
  input.2

/-- Exact graph-colouring semantics at the canonical graph-and-bound carrier. -/
def IsColorable (input : GraphColoringIR) : Prop :=
  ∃ colorOf : Nat → Nat, ProperColoring input.graph input.colors colorOf

/-- The hub reuses the one canonical lawful graph presentation and unary bound codec. -/
abbrev lawfulRepresentation : LawfulEncodedType :=
  StandardInstances.prod Presentation.Graph.structuredPresentation StandardInstances.unaryNat

@[simp] theorem lawfulRepresentation_carrier : lawfulRepresentation.Carrier = GraphColoringIR :=
  rfl

@[simp] theorem lawfulRepresentation_encodedType :
    lawfulRepresentation.encodedType =
      chromaticNumberTupleStructuredEncodedType :=
  rfl

/-- The exact canonical typed graph-colouring endpoint. -/
def chromaticNumberProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation ⟨IsColorable⟩

@[simp] theorem chromaticNumberProblem_accepts (input : GraphColoringIR) :
    chromaticNumberProblem.accepts input ↔ input.IsColorable :=
  Iff.rfl

@[simp] theorem chromaticNumberProblem_encoderBoundIdentity :
    chromaticNumberProblem.encoderBoundRepresentationIdentity =
      lawfulRepresentation.encoderBoundIdentity :=
  rfl

end GraphColoringIR
end Domain
end ComplexityReduction
