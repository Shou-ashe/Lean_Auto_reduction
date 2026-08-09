import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Encoding.StandardInstances

/-!
A forward hardness path exists from canonical 3SAT, but the exact tagged target
has no registered native verifier membership.  Completeness must therefore stop
before transport.
-/

namespace Benchmark.Hardness.Inputs.Completeness.MissingTargetMembership

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Certificate

abbrev hub : PresentedProblem := NativeCookLevin.canonicalThreeSAT

private def semantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hub.Instance
  isYes := fun input => hub.accepts input.2

@[complexity_reduction_ir_typed_problem]
def source : PresentedProblem where
  semantic := semantic
  representation := StandardInstances.prod StandardInstances.bool hub.representation
  carrier_eq := rfl

def forwardProgram : PolyProg hub.representation source.representation :=
  .pair (.const hub.representation StandardInstances.bool false) (.id hub.representation)

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
def forward : CertifiedReduction hub source where
  program := forwardProgram
  correct := by
    intro input
    rfl

end Benchmark.Hardness.Inputs.Completeness.MissingTargetMembership
