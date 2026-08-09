import Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring
import ComplexityReduction.Agent.Hardness.Regression.BackendCompletenessBoundary
import ComplexityReduction.Annotations.Attributes

/-!
Adversarial type-boundary fixture.  The exact target has native membership and
an attributed backend `TMNPCompleteEnc` declaration, but no V2
`NativeTMNPComplete` declaration and no forward path from a native-complete
hub.  The backend head must remain unusable by the completeness resolver.
-/

namespace Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly

open ComplexityReduction
open ComplexityReduction.Certificate

abbrev source : Encoding.PresentedProblem :=
  Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring.problem

@[complexity_reduction_ir_typed_native_membership]
theorem nativeMembership : NativeTMInNP source :=
  ComplexityReduction.Agent.Hardness.Authoring.NativeMembershipTemplate.toNativeMembership
    Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring.verifier
    Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring.witnessPresentation
    Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring.discipline

/-- Intentionally poisoned backend-only completeness evidence. -/
@[complexity_reduction_ir_typed_complete]
theorem backendCompleteness :
    ComplexityReduction.TMNPCompleteEnc source.toEncodedDecisionProblem :=
  ComplexityReduction.Agent.Hardness.Regression.BackendCompletenessBoundary.poisonedBackendCompleteness
    source

end Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly
