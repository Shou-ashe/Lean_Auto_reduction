/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipCliqueCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipThreeDimensionalMatchingScan
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.CliqueCover
import ComplexityReduction.Presentation.ThreeDimensionalMatching

/-!
Backend-membership annotations for the exact structured Clique Cover and
Three-Dimensional Matching presentations.

The underlying CR records establish compatibility `TMInNP` only.  Their
declaration types do not supply V2 program-indexed checkers or a native
encoding discipline, so this module exports no native capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace CliqueCoverThreeDimensionalMatchingMembership

open Certificate

@[complexity_reduction_ir_typed_verifier]
theorem cliqueCoverStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP Presentation.CliqueCover.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.cliqueCoverStructuredDecisionProblem
  exact ComplexityReduction.Karp21.cliqueCoverStructured_TMInNP

theorem cliqueCoverStructured_backendTMInNP :
    BackendTMInNP Presentation.CliqueCover.structuredProblem :=
  cliqueCoverStructured_backendTMInNP_export

@[complexity_reduction_ir_typed_verifier]
theorem threeDimensionalMatchingStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.ThreeDimensionalMatching.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.threeDimensionalMatchingStructuredDecisionProblem
  exact ComplexityReduction.Karp21.threeDimensionalMatchingStructured_TMInNP

theorem threeDimensionalMatchingStructured_backendTMInNP :
    BackendTMInNP Presentation.ThreeDimensionalMatching.structuredProblem :=
  threeDimensionalMatchingStructured_backendTMInNP_export

end CliqueCoverThreeDimensionalMatchingMembership
end Karp21
end Problems
end ComplexityReduction
