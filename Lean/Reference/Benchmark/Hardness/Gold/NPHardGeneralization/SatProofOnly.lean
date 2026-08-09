import Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT

/-! Isolated benchmark self-check.  Never imported by the public input tree. -/

namespace Benchmark.Hardness.Gold.NPHardGeneralization.SatProofOnly

open ComplexityReduction.Certificate
open Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT

theorem semanticIff (input : hub.Instance) :
    hub.accepts input ↔ source.accepts (forwardProgram.run input) := by
  rfl

def certifiedReduction : CertifiedReduction hub source where
  program := forwardProgram
  correct := semanticIff

end Benchmark.Hardness.Gold.NPHardGeneralization.SatProofOnly
