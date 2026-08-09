import Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis

/-! Isolated benchmark self-check.  Never imported by the public input tree. -/

namespace Benchmark.Hardness.Gold.NPHardGeneralization.GraphProgramSynthesis

open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis

def synthesizedExecutable (input : hub.Instance) : source.Instance :=
  (false, input)

def synthesizedProgram : PolyProg hub.representation source.representation :=
  .pair (.const hub.representation StandardInstances.bool false) (.id hub.representation)

theorem synthesizedProgramRun (input : hub.Instance) :
    synthesizedProgram.run input = synthesizedExecutable input := by
  rfl

theorem synthesizedInvariant (input : hub.Instance) :
    mappingInvariant input (synthesizedProgram.run input) := by
  rw [synthesizedProgramRun]
  change false = false ∧ input = input
  exact ⟨rfl, rfl⟩

theorem synthesizedSemanticIff (input : hub.Instance) :
    hub.accepts input ↔ source.accepts (synthesizedProgram.run input) := by
  change hub.accepts input ↔ false = false ∧ hub.accepts input
  constructor
  · intro accepted
    have invariant := synthesizedInvariant input
    exact ⟨invariant.1, accepted⟩
  · intro accepted
    exact accepted.2

def certifiedReduction : CertifiedReduction hub source where
  program := synthesizedProgram
  correct := synthesizedSemanticIff

end Benchmark.Hardness.Gold.NPHardGeneralization.GraphProgramSynthesis
