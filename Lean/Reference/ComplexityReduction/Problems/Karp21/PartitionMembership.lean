/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartition
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartitionBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.Partition
import ComplexityReduction.Presentation.PartitionBinary

/-!
Backend-membership annotations for the exact unary and binary structured
Partition presentations.

The existing CR verifier proofs are direct backend `TMInNP` evidence at these
two distinct V2 endpoints.  Both inherited construction chains contain
`native_decide`, so this module deliberately exports only those backend
propositions.  It does not reconstruct a V2 program-indexed verifier,
encoding discipline, native membership, or completeness capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace PartitionMembership

open Certificate

/-- CR's existing direct-TM membership theorem at the exact unary Partition endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem partitionStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.Partition.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem
  exact ComplexityReduction.Karp21.partitionStructured_TMInNP

/-- The V2 alias retains the exact unary presentation in its type. -/
theorem partitionStructured_backendTMInNP :
    BackendTMInNP Presentation.Partition.structuredProblem :=
  partitionStructured_backendTMInNP_export

/-- CR's existing direct-TM membership theorem at the exact binary Partition endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem partitionBinaryStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.PartitionBinary.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.partitionBinaryStructuredDecisionProblem
  exact ComplexityReduction.Karp21.partitionBinaryStructured_TMInNP

/-- The V2 alias retains the distinct binary presentation in its type. -/
theorem partitionBinaryStructured_backendTMInNP :
    BackendTMInNP Presentation.PartitionBinary.structuredProblem :=
  partitionBinaryStructured_backendTMInNP_export

end PartitionMembership
end Karp21
end Problems
end ComplexityReduction
