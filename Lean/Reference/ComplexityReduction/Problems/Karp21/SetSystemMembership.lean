/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetCovering
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Verifier
import ComplexityReduction.Presentation.SetSystem

/-!
Backend-only direct-TM membership bridges for canonical V2 SetSystem endpoints.

Both bridges reuse exact read-only CR structured decision-problem theorems.
They deliberately export only backend `TMInNP`: neither declaration reconstructs
a V2 verifier, supplies encoding discipline, claims `NativeTMInNP`, or exports
completeness.  Both reused CR proofs have inherited `native_decide` audit
dependencies, which are therefore confined to backend-only theorems.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SetSystemMembership

open Certificate

/--
CR's structured Set Covering membership theorem at the exact V2 presented
endpoint.  The tag is discovery-only; elaborated-type validation remains
backend membership only.  Its inherited `native_decide` audit remains outside
native verifier admission.
-/
@[complexity_reduction_ir_typed_verifier]
theorem setCoveringStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.SetSystem.setCoveringStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.setCoveringStructuredDecisionProblem
  exact ComplexityReduction.Karp21.setCoveringStructured_TMInNP

/-- The presentation-indexed V2 alias for the same Set Covering backend evidence. -/
theorem setCoveringStructured_backendTMInNP :
    BackendTMInNP Presentation.SetSystem.setCoveringStructuredProblem :=
  setCoveringStructured_backendTMInNP_export

/-- The Set Covering bridge is fixed to CR's exact structured backend endpoint. -/
@[simp]
theorem setCoveringStructured_backendTMInNP_endpoint :
    Presentation.SetSystem.setCoveringStructuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.setCoveringStructuredDecisionProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem_backendEndpoint_eq_legacy

/--
CR's structured Exact Cover membership theorem at the exact V2 presented
endpoint.  Its inherited `native_decide` audit is intentionally retained only
as backend membership, never as native verifier or encoding-discipline proof.
-/
@[complexity_reduction_ir_typed_verifier]
theorem exactCoverStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.SetSystem.exactCoverStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.exactCoverStructuredDecisionProblem
  exact ComplexityReduction.Karp21.exactCoverStructured_TMInNP

/-- The presentation-indexed V2 alias for the same Exact Cover backend evidence. -/
theorem exactCoverStructured_backendTMInNP :
    BackendTMInNP Presentation.SetSystem.exactCoverStructuredProblem :=
  exactCoverStructured_backendTMInNP_export

/-- The Exact Cover bridge is fixed to CR's exact structured backend endpoint. -/
@[simp]
theorem exactCoverStructured_backendTMInNP_endpoint :
    Presentation.SetSystem.exactCoverStructuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.exactCoverStructuredDecisionProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem_backendEndpoint_eq_legacy

/- Compile-time anchors for the two exact backend-only membership boundaries. -/
#check setCoveringStructured_backendTMInNP_export
#check setCoveringStructured_backendTMInNP
#check ComplexityReduction.Karp21.setCoveringStructured_TMInNP
#check exactCoverStructured_backendTMInNP_export
#check exactCoverStructured_backendTMInNP
#check ComplexityReduction.Karp21.exactCoverStructured_TMInNP

end SetSystemMembership
end Karp21
end Problems
end ComplexityReduction
