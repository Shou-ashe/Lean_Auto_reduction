import Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProof
import ComplexityReduction.AxiomGate

/-!
Gold sanity proof for the public Phase-7 case.  This module is deliberately
outside `Benchmark.Hardness.Inputs`, is absent from the active manifest and
model context, and cannot be imported by generated sources.
-/

namespace Benchmark.Hardness.Oracles.Gold.ModelSemanticProof

open Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProofCore

def executableCorrect :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof
      source target executable := by
  intro input
  change input = input ↔ True
  simp

assert_standard_axioms executableCorrect

end Benchmark.Hardness.Oracles.Gold.ModelSemanticProof
