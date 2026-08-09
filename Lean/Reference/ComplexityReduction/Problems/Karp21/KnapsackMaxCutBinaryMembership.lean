/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipMaxCutBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Presentation.MaxCutBinary

/-!
Backend-membership annotations for the exact binary structured Knapsack and
Max Cut presentations.

CR supplies direct backend `TMInNP` theorems at these exact endpoints, but
neither theorem supplies a V2 program-indexed checker paired with V2 encoding
discipline, and both inherited construction chains contain `native_decide`.
This leaf consequently exports backend membership only and never reclassifies
either theorem as native membership or completeness.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace KnapsackMaxCutBinaryMembership

open Certificate

/-- CR's direct-TM membership theorem at the exact binary Knapsack endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem knapsackBinaryStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.KnapsackBinary.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.knapsackBinaryStructuredDecisionProblem
  exact ComplexityReduction.Karp21.knapsackBinaryStructured_TMInNP

/-- The V2 alias retains the exact binary Knapsack presentation in its type. -/
theorem knapsackBinaryStructured_backendTMInNP :
    BackendTMInNP Presentation.KnapsackBinary.structuredProblem :=
  knapsackBinaryStructured_backendTMInNP_export

/-- CR's direct-TM membership theorem at the exact binary Max Cut endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem maxCutBinaryStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.MaxCutBinary.binaryStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.maxCutBinaryStructuredDecisionProblem
  exact ComplexityReduction.Karp21.maxCutBinaryStructured_TMInNP

/-- The V2 alias retains the exact binary Max Cut presentation in its type. -/
theorem maxCutBinaryStructured_backendTMInNP :
    BackendTMInNP Presentation.MaxCutBinary.binaryStructuredProblem :=
  maxCutBinaryStructured_backendTMInNP_export

end KnapsackMaxCutBinaryMembership
end Karp21
end Problems
end ComplexityReduction
