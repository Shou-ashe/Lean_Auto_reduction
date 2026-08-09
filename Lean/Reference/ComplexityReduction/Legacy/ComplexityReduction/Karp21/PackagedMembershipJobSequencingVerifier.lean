/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencing

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

/-- Direct finite-certificate TM verifier for faithful structured Job Sequencing. -/
noncomputable def jobSequencingStructuredFiniteTMVerifier :
    TMVerifier jobSequencingStructuredDecisionProblem where
  Cert := JobSequencing.jobSequencingCertificateEncodedType
  verify := JobSequencing.jobSequencingStructuredFiniteVerify
  verifier_polytime := JobSequencing.jobSequencingStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hSublist, hFeasible, hProfit⟩
    rcases JobSequencing.exists_jobSequencingCertificate_of_sublist hSublist with
      ⟨bits, hLen, hSelected⟩
    refine ⟨bits, ?_, ?_⟩
    · simpa using JobSequencing.jobSequencingCertificate_inputSize_le_linear I bits hLen
    · exact (JobSequencing.jobSequencingStructuredFiniteVerify_eq_true_iff I bits).2
        ⟨by simpa [hSelected] using hFeasible, by simpa [hSelected] using hProfit⟩
  sound := by
    intro I bits hVerify
    have hSem :=
      (JobSequencing.jobSequencingStructuredFiniteVerify_eq_true_iff I bits).1 hVerify
    refine ⟨JobSequencing.selectedJobsFrom I.jobs bits 0,
      JobSequencing.selectedJobsFrom_sublist I.jobs bits 0, hSem.1, hSem.2⟩

theorem jobSequencingStructured_TMInNP :
    TMInNP jobSequencingStructuredDecisionProblem :=
  TMInNP.intro jobSequencingStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
