import Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership
import Benchmark.Hardness.Inputs.Gaps.MissingPrimitive
import Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch
import Benchmark.Hardness.Inputs.Negative.NoRoute
import ComplexityReduction.Agent.Hardness.Runtime
import ComplexityReduction.Problems.Karp21.CNFMembership
import Lean.Elab.Command

/-! Regression coverage for exact Lean-side typed gap classification. -/

namespace ComplexityReduction.Agent.Hardness.Regression.GapClassifier

open Lean Elab Command Meta

/-! A gap tag on an unsupported type must not refine any blocker. -/
@[complexity_reduction_ir_typed_gap]
private def forgedGapMetadata : Nat := 7

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    let expectReason (label : String) (failure : Protocol.ClosedResolver.Failure)
        (expected : Protocol.MissingCapabilityReason) := do
      match ← Agent.Hardness.Gap.classifyFailure environment failure with
      | none => throwError "{label}: classifier returned no typed gap"
      | some gap =>
          unless gap.reason == expected do
            throwError "{label}: expected {repr expected}, got {repr gap.reason}"

    expectReason "generic no-route"
      (.noRegistryPath
        (mkConst ``Benchmark.Hardness.Inputs.Negative.NoRoute.source)
        (mkConst ``Benchmark.Hardness.Inputs.Negative.NoRoute.target))
      .noRegistryPath

    expectReason "declared primitive"
      (.noRegistryPath
        (mkConst ``Benchmark.Hardness.Inputs.Gaps.MissingPrimitive.source)
        (mkConst ``Benchmark.Hardness.Inputs.Gaps.MissingPrimitive.target))
      .primitive

    expectReason "missing native membership"
      (.missingNativeMembership
        (mkConst ``Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership.problem))
      .nativeMembership

    expectReason "backend verifier without native discipline"
      (.missingNativeMembership
        (mkConst ``ComplexityReduction.Presentation.Satisfiability.structuredProblem))
      .verifierEncodingDiscipline

    expectReason "representation mismatch"
      (.noRegistryPath
        (mkConst ``Benchmark.Hardness.Inputs.Gaps.RepresentationMismatch.source)
        (mkConst
          ``ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem))
      .lawfulPresentation

end ComplexityReduction.Agent.Hardness.Regression.GapClassifier
