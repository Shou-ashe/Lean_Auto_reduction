import ComplexityReduction.Certificate.VerifierAdapter

namespace Benchmark.Hardness.Inputs.Negative.MissingVerifierDiscipline

/-- The exact structured-3SAT endpoint of the backend verifier adapter. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Certificate.VerifierAdapter.threeSATStructuredProblem

/-!
This is a real `CertifiedVerifier`, but it is not an exact `NativeTMInNP source` declaration.
Passing it through the membership ABI must therefore fail before the Cook--Levin lane is entered.
-/
noncomputable abbrev verifierWithoutDiscipline :
    ComplexityReduction.Certificate.CertifiedVerifier source :=
  ComplexityReduction.Certificate.VerifierAdapter.threeSATStructuredVerifier

end Benchmark.Hardness.Inputs.Negative.MissingVerifierDiscipline
