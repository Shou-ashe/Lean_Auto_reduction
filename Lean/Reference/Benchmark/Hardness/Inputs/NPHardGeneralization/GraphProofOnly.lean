import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Problems.Karp21.GraphAtoms

/-!
Graph-family NP-hard authoring input.

The exact target and reduction program are public.  The semantic certificate is
deliberately absent from this module, so importing the input does not register a
forward hardness edge.  The isolated benchmark gold supplies the missing proof.
-/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program

abbrev hub : PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

def guardedCliqueSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hub.Instance
  isYes := fun input => input.1 = false ∧ hub.accepts input.2

@[complexity_reduction_ir_typed_problem]
def source : PresentedProblem where
  semantic := guardedCliqueSemantic
  representation := StandardInstances.prod StandardInstances.bool hub.representation
  carrier_eq := rfl

def forwardProgram : PolyProg hub.representation source.representation :=
  .pair (.const hub.representation StandardInstances.bool false) (.id hub.representation)

def mappingInvariant (input : hub.Instance) (output : source.Instance) : Prop :=
  output.1 = false ∧ output.2 = input

@[complexity_reduction_ir_typed_gap]
def semanticGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .egress hub source :=
  .exact

end Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly
