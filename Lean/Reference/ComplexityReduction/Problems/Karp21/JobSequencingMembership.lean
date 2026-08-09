/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencingVerifier
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencingBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.JobSequencing
import ComplexityReduction.Presentation.JobSequencingBinary

/-!
Backend-membership annotations for the exact unary and binary structured Job
Sequencing presentations.

The CR verifier records establish compatibility `TMInNP` at these distinct
presentation endpoints.  They are not V2 program-indexed checkers paired with
V2 encoding discipline, and both inherited construction chains contain
`native_decide`.  This leaf therefore exports backend membership only, never
native verifier, native membership, or completeness capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace JobSequencingMembership

open Certificate

/-- CR's existing direct-TM membership theorem at the exact unary Job Sequencing endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem jobSequencingStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.JobSequencing.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.jobSequencingStructuredDecisionProblem
  exact ComplexityReduction.Karp21.jobSequencingStructured_TMInNP

/-- The V2 alias retains the exact unary Job Sequencing presentation in its type. -/
theorem jobSequencingStructured_backendTMInNP :
    BackendTMInNP Presentation.JobSequencing.structuredProblem :=
  jobSequencingStructured_backendTMInNP_export

/-- CR's existing direct-TM membership theorem at the exact binary Job Sequencing endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem jobSequencingBinaryStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.JobSequencingBinary.binaryStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.jobSequencingBinaryStructuredDecisionProblem
  exact ComplexityReduction.Karp21.jobSequencingBinaryStructured_TMInNP

/-- The V2 alias retains the distinct binary Job Sequencing presentation in its type. -/
theorem jobSequencingBinaryStructured_backendTMInNP :
    BackendTMInNP Presentation.JobSequencingBinary.binaryStructuredProblem :=
  jobSequencingBinaryStructured_backendTMInNP_export

end JobSequencingMembership
end Karp21
end Problems
end ComplexityReduction
