import Benchmark.Hardness.Inputs.Membership.DeterministicAuthoring
import ComplexityReduction.Certificate.NativeCookLevin

/-!
The exact target has valid native membership, but the only local edge points
from the target to canonical 3SAT.  That direction can run Cook--Levin; it
cannot establish hardness of the target.
-/

namespace Benchmark.Hardness.Inputs.Completeness.WrongDirection

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

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def targetToThreeSAT :
    CertifiedReduction source NativeCookLevin.canonicalThreeSAT :=
  NativeCookLevin.reduce nativeMembership

end Benchmark.Hardness.Inputs.Completeness.WrongDirection
