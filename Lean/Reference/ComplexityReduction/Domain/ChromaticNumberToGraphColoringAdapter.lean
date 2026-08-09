/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Domain.Core.GraphColoringIR
import ComplexityReduction.Presentation.ChromaticNumber
import ComplexityReduction.Protocol.ComponentResolver

/-!
Concrete structured-Chromatic-Number ingress to the wrapper-independent
canonical graph-colouring hub.  This is the only layer in this component path
that mentions `ChromaticNumberInput`.
-/

namespace ComplexityReduction
namespace Domain
namespace ChromaticNumberToGraphColoringAdapter

open Certificate Encoding ComplexityReduction.Combinatorics.Graph

abbrev sourceProblem : PresentedProblem :=
  Presentation.ChromaticNumber.structuredProblem

abbrev hubProblem : PresentedProblem :=
  GraphColoringIR.chromaticNumberProblem

abbrev IngressRequest (source hub : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .ingress source hub

def request : IngressRequest sourceProblem hubProblem := .exact

/-- Forget only the concrete source wrapper, retaining all graph-colouring data. -/
def ingressExecutable (input : ChromaticNumberInput) : GraphColoringIR :=
  (input.graph, input.colors)

private theorem ingressExecutable_encode (input : ChromaticNumberInput) :
    hubProblem.representation.encodedType.encode (ingressExecutable input) =
      sourceProblem.representation.encodedType.encode input := by
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

/-- Direct-TM evidence for the exact wrapper-normalization executable. -/
theorem ingressExecutable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceProblem.representation.encodedType
      hubProblem.representation.encodedType ingressExecutable :=
  ingressTMBacked.tm_polytime

noncomputable def ingressPrimitive :
    Program.Primitive sourceProblem.representation hubProblem.representation :=
  Program.Primitive.ofTMPolyTime ingressExecutable ingressExecutable_tmPolyTime

noncomputable def ingressProgram :
    Program.PolyProg sourceProblem.representation hubProblem.representation :=
  .atom ingressPrimitive

@[simp] theorem ingressProgram_run (input : sourceProblem.Instance) :
    ingressProgram.run input = ingressExecutable input :=
  rfl

theorem ingressProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ hubProblem.accepts (ingressProgram.run input) := by
  change ChromaticNumber input ↔ GraphColoringIR.IsColorable (input.graph, input.colors)
  rfl

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def sourceAdapter : CertifiedReduction sourceProblem hubProblem where
  program := ingressProgram
  correct := ingressProgram_correct

abbrev Resolution : Type 2 :=
  Protocol.ComponentResolution .ingress sourceProblem hubProblem

noncomputable def resolve : Resolution :=
  Protocol.ComponentResolver.accept request sourceAdapter

@[simp] theorem resolve_exact : resolve = .accepted sourceAdapter :=
  rfl

theorem resolve_accepted_endpoint :
    match resolve with
    | .accepted certificate => certificate.program = ingressProgram
    | .blocked _ => False :=
  rfl

end ChromaticNumberToGraphColoringAdapter
end Domain
end ComplexityReduction
