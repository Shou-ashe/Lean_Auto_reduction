import Benchmark.HiddenTargets.L0.clique
import ComplexityReduction.Karp21

namespace BenchmarkGoldProof

noncomputable section

def goldCertificate : BenchmarkHiddenSample.sampleClaim := by
  exact ComplexityReduction.Karp21.Clique.cliqueInNP

end

end BenchmarkGoldProof
