/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Domain.Core.GraphIR
import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Protocol.ComponentResolver

/-!
The structured-`GraphInput` ingress adapter for the canonical graph hub.

This is the only component that reads CR's concrete `GraphInput` wrapper.
The source and target encoders expose the same ordered data word, but that
fact is used only to construct a direct-TM-backed adapter at their distinct
typed endpoints; it does not identify the two presentations or grant an
identity route.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphToGraphIRAdapter

open Certificate Encoding ComplexityReduction.Combinatorics.Graph

abbrev sourceProblem : PresentedProblem :=
  Presentation.Graph.wellFormedProblem

abbrev hubProblem : PresentedProblem :=
  GraphIR.wellFormedProblem

abbrev IngressRequest (source hub : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .ingress source hub

/-- The one exact structured-graph to canonical-GraphIR ingress request. -/
def request : IngressRequest sourceProblem hubProblem :=
  .exact

/-- Rebuild the canonical graph hub from the concrete structured wrapper fields. -/
def ingressExecutable (input : sourceProblem.Instance) : hubProblem.Instance :=
  GraphIR.mk input.vertices input.edges input.directed

private theorem ingressExecutable_encode (input : sourceProblem.Instance) :
    hubProblem.representation.encodedType.encode (ingressExecutable input) =
      sourceProblem.representation.encodedType.encode input :=
  rfl

private noncomputable def ingressTMBacked :
    ComplexityReduction.TMBackedCostedMap
      sourceProblem.representation.encodedType
      hubProblem.representation.encodedType
      ingressExecutable :=
  ComplexityReduction.TMBackedCostedMap.ofEncodingEquiv
    sourceProblem.representation.encodedType
    hubProblem.representation.encodedType
    ingressExecutable
    (Equiv.refl sourceProblem.representation.encodedType.Symbol)
    (by
      intro input
      change hubProblem.representation.encodedType.encode (ingressExecutable input) =
        (sourceProblem.representation.encodedType.encode input).map id
      simpa using ingressExecutable_encode input)

/-- Direct-TM evidence for the exact wrapper-to-hub executable. -/
theorem ingressExecutable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceProblem.representation.encodedType
      hubProblem.representation.encodedType ingressExecutable :=
  ingressTMBacked.tm_polytime

/-- The one direct-TM-backed atom required by the structured graph ingress. -/
noncomputable def ingressPrimitive :
    Program.Primitive sourceProblem.representation hubProblem.representation :=
  Program.Primitive.ofTMPolyTime ingressExecutable ingressExecutable_tmPolyTime

/-- The authoritative program for the concrete GraphInput ingress component. -/
noncomputable def ingressProgram :
    Program.PolyProg sourceProblem.representation hubProblem.representation :=
  .atom ingressPrimitive

@[simp] theorem ingressProgram_run (input : sourceProblem.Instance) :
    ingressProgram.run input = ingressExecutable input :=
  rfl

/-- The wrapper and graph hub have the same graph well-formedness semantics at this adapter. -/
theorem ingressProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ hubProblem.accepts (ingressProgram.run input) := by
  change (∀ edge ∈ input.edges, edge.1 < input.vertices ∧ edge.2 < input.vertices) ↔
    ∀ edge ∈ input.edges, edge.1 < input.vertices ∧ edge.2 < input.vertices
  rfl

/-- The canonical structured GraphInput ingress certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def sourceAdapter : CertifiedReduction sourceProblem hubProblem where
  program := ingressProgram
  correct := ingressProgram_correct

abbrev Resolution : Type 2 :=
  Protocol.ComponentResolution .ingress sourceProblem hubProblem

/-- The exact structured graph ingress accepts only its program-indexed certificate. -/
noncomputable def resolve : Resolution :=
  Protocol.ComponentResolver.accept request sourceAdapter

@[simp] theorem resolve_exact : resolve = .accepted sourceAdapter :=
  rfl

end GraphToGraphIRAdapter
end Domain
end ComplexityReduction
