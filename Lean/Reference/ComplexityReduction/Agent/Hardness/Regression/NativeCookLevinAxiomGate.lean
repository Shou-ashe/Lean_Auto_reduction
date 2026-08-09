import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier

/-!
Negative regression for the job-local Cook--Levin root axiom gate.

The deliberately poisoned declaration is confined to this non-production regression module.
Public benchmark inputs remain axiom-free.  The test proves that even a term with the exact
native-membership type cannot enter a verified artifact when its local root transitively depends
on a non-standard axiom.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.NativeCookLevinAxiomGate

abbrev source : Encoding.PresentedProblem :=
  Presentation.Knapsack.structuredProblem

axiom poisonedMembership : Certificate.NativeTMInNP source

noncomputable def poisonedRoot : Certificate.CertifiedReduction
    source Certificate.NativeCookLevin.canonicalThreeSAT :=
  Certificate.NativeCookLevin.reduce poisonedMembership

/--
error: axiom gate rejected ComplexityReduction.Agent.Hardness.Regression.NativeCookLevinAxiomGate.poisonedRoot: forbidden axiom ComplexityReduction.Agent.Hardness.Regression.NativeCookLevinAxiomGate.poisonedMembership
-/
#guard_msgs in
assert_standard_axioms poisonedRoot

end ComplexityReduction.Agent.Hardness.Regression.NativeCookLevinAxiomGate
