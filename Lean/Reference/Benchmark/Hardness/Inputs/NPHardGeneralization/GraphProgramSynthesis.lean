import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Problems.Karp21.GraphAtoms

/-!
Graph-family program-synthesis and multi-gap NP-hard input.

Only the exact encoding and semantic specification are public.  A valid run has
to construct an executable/program, establish its mapping invariant, and build
the exact semantic certificate before a reduction edge can be admitted.
-/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding

abbrev hub : PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

def synthesizedSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hub.Instance
  isYes := fun input => input.1 = false ∧ hub.accepts input.2

@[complexity_reduction_ir_typed_problem]
def source : PresentedProblem where
  semantic := synthesizedSemantic
  representation := StandardInstances.prod StandardInstances.bool hub.representation
  carrier_eq := rfl

def mappingInvariant (input : hub.Instance) (output : source.Instance) : Prop :=
  output.1 = false ∧ output.2 = input

@[complexity_reduction_ir_typed_gap]
def primitiveGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .primitive .egress hub source :=
  .exact

@[complexity_reduction_ir_typed_gap]
def programGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .executableRelationContract .egress hub source :=
  .exact

@[complexity_reduction_ir_typed_gap]
def semanticGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .egress hub source :=
  .exact

end Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis
