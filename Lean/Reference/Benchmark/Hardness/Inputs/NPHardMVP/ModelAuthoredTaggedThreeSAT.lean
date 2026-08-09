import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Encoding.StandardInstances

/-!
Public R-C input with no registered forward edge or final hardness theorem.

The target preserves canonical 3SAT acceptance while adding a Boolean tag.
Only the executable construction is supplied.  A production author must still
write and kernel-check the exact `CertifiedReduction canonicalThreeSAT target`
term, including its semantic proof, before the NP-hard resolver can close it.
-/

namespace Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program

abbrev hub : PresentedProblem := NativeCookLevin.canonicalThreeSAT

def taggedSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hub.Instance
  isYes := fun input => if input.1 then False else hub.accepts input.2

@[complexity_reduction_ir_typed_problem]
def source : PresentedProblem where
  semantic := taggedSemantic
  representation := StandardInstances.prod StandardInstances.bool hub.representation
  carrier_eq := rfl

/-- Public executable available to an author; this declaration grants no route capability. -/
def forwardProgram : PolyProg hub.representation source.representation :=
  .pair (.const hub.representation StandardInstances.bool false) (.id hub.representation)

end Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT
