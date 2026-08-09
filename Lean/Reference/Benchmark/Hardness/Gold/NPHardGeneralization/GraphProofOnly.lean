import Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly

/-! Isolated benchmark self-check.  Never imported by the public input tree. -/

namespace Benchmark.Hardness.Gold.NPHardGeneralization.GraphProofOnly

open ComplexityReduction.Certificate
open Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly

theorem forwardInvariant (input : hub.Instance) :
    mappingInvariant input (forwardProgram.run input) := by
  change false = false ∧ input = input
  exact ⟨rfl, rfl⟩

theorem semanticIff (input : hub.Instance) :
    hub.accepts input ↔ source.accepts (forwardProgram.run input) := by
  change hub.accepts input ↔ false = false ∧ hub.accepts input
  constructor
  · intro accepted
    exact ⟨rfl, accepted⟩
  · intro accepted
    exact accepted.2

def certifiedReduction : CertifiedReduction hub source where
  program := forwardProgram
  correct := semanticIff

end Benchmark.Hardness.Gold.NPHardGeneralization.GraphProofOnly
