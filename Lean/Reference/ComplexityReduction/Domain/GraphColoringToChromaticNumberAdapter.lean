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
Concrete structured-Chromatic-Number egress from the wrapper-independent
canonical graph-colouring hub. This is the only layer in this component path
that constructs `ChromaticNumberInput`.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToChromaticNumberAdapter

open Certificate Encoding ComplexityReduction.Combinatorics.Graph

abbrev hubProblem : PresentedProblem :=
  GraphColoringIR.chromaticNumberProblem

abbrev targetProblem : PresentedProblem :=
  Presentation.ChromaticNumber.structuredProblem

abbrev EgressRequest (hub target : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .egress hub target

def request : EgressRequest hubProblem targetProblem := .exact

/-- Reconstruct the concrete target wrapper without changing graph-colouring data. -/
def egressExecutable (input : GraphColoringIR) : ChromaticNumberInput where
  graph := input.graph
  colors := input.colors

private theorem egressExecutable_encode (input : GraphColoringIR) :
    targetProblem.representation.encodedType.encode (egressExecutable input) =
      hubProblem.representation.encodedType.encode input := by
  rfl

private noncomputable def egressTMBacked :
    ComplexityReduction.TMBackedCostedMap
      hubProblem.representation.encodedType
      targetProblem.representation.encodedType
      egressExecutable :=
  ComplexityReduction.TMBackedCostedMap.ofEncodingEquiv
    hubProblem.representation.encodedType
    targetProblem.representation.encodedType
    egressExecutable
    (Equiv.refl hubProblem.representation.encodedType.Symbol)
    (by
      intro input
      change targetProblem.representation.encodedType.encode (egressExecutable input) =
        (hubProblem.representation.encodedType.encode input).map id
      simpa using egressExecutable_encode input)

/-- Direct-TM evidence for the exact canonical-hub-to-wrapper executable. -/
theorem egressExecutable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap hubProblem.representation.encodedType
      targetProblem.representation.encodedType egressExecutable :=
  egressTMBacked.tm_polytime

noncomputable def egressPrimitive :
    Program.Primitive hubProblem.representation targetProblem.representation :=
  Program.Primitive.ofTMPolyTime egressExecutable egressExecutable_tmPolyTime

noncomputable def egressProgram :
    Program.PolyProg hubProblem.representation targetProblem.representation :=
  .atom egressPrimitive

@[simp] theorem egressProgram_run (input : hubProblem.Instance) :
    egressProgram.run input = egressExecutable input :=
  rfl

theorem egressProgram_correct (input : hubProblem.Instance) :
    hubProblem.accepts input ↔ targetProblem.accepts (egressProgram.run input) := by
  change GraphColoringIR.IsColorable input ↔ ChromaticNumber (egressExecutable input)
  rfl

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_egress]
noncomputable def targetAdapter : CertifiedReduction hubProblem targetProblem where
  program := egressProgram
  correct := egressProgram_correct

abbrev Resolution : Type 2 :=
  Protocol.ComponentResolution .egress hubProblem targetProblem

noncomputable def resolve : Resolution :=
  Protocol.ComponentResolver.accept request targetAdapter

@[simp] theorem resolve_exact : resolve = .accepted targetAdapter :=
  rfl

theorem resolve_accepted_endpoint :
    match resolve with
    | .accepted certificate => certificate.program = egressProgram
    | .blocked _ => False :=
  rfl

end GraphColoringToChromaticNumberAdapter
end Domain
end ComplexityReduction
