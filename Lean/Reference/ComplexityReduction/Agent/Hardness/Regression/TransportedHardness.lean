import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Certificate.CompletenessTransport
import ComplexityReduction.Routes.ThreeSATToClique.Unified

/-!
Regression for exact native-hardness transport.  The target proof is composed
only from the registered canonical completeness root and one existing forward
`CertifiedReduction` atom.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.TransportedHardness

open Certificate

noncomputable def cliquePath : CertifiedPath
    Certificate.NativeCookLevin.canonicalThreeSAT
    Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  .step Routes.ThreeSATToClique.sharedGadget

noncomputable def cliqueNativeHardness : NativeTMNPHard
    Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  NativeTMNPHard.ofCompleteAlongPath
    Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness
    cliquePath

assert_standard_axioms cliquePath, cliqueNativeHardness

end ComplexityReduction.Agent.Hardness.Regression.TransportedHardness
