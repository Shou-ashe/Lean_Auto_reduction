import Benchmark.Hardness.Inputs.StageO.Inputs
import ComplexityReduction.AxiomGate
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier
import ComplexityReduction.Routes.CliqueToVertexCover.Unified
import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters
import ComplexityReduction.Routes.ThreeSATToClique.Unified

/-!
Lean regression for the mathematical endpoints used by Stage O.

This module is deliberately not imported by the Stage O input module or the
normal runtime registry.  It demonstrates that every positive benchmark
objective has standard-axioms evidence, while run-local discovery and promotion
remain the responsibility of the Python orchestration layer.
-/

namespace Benchmark.Hardness.Inputs.StageO.Regression

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Certificate

theorem predicateAdapter_exact
    (input : Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedTarget.Instance) :
    Benchmark.Hardness.Inputs.StageO.Inputs.predicateAdapterRoute input ↔
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedTarget.accepts input :=
  Iff.rfl

theorem parameterizedPredicateThree_exact
    (input : Problems.Karp21.Satisfiability.threeSATStructuredProblem.Instance) :
    Benchmark.Hardness.Inputs.StageO.Inputs.parameterizedPredicateThree input ↔
      Problems.Karp21.Satisfiability.threeSATStructuredProblem.accepts input := by
  simp [Benchmark.Hardness.Inputs.StageO.Inputs.parameterizedPredicateThree,
    Benchmark.Hardness.Inputs.StageO.Inputs.parameterizedPredicate]

theorem twoGapPresentation_exact
    (input : Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedSource.Instance) :
    Benchmark.Hardness.Inputs.StageO.Inputs.twoGapPresentationPredicate input ↔
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedSource.accepts input :=
  Iff.rfl

noncomputable def fixedTargetRoute :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedSource
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedTarget :=
  Routes.ThreeSATToClique.IngressAdapters.taggedFinalRoute

noncomputable def autoTargetCompleteness :
    NativeTMNPComplete
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedTarget :=
  CompletenessTransport.alongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step Routes.ThreeSATToClique.sharedGadget)
    Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

noncomputable def predicateAdapterRoute :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedTarget
      Benchmark.Hardness.Inputs.StageO.Inputs.predicateAdapterTarget :=
  Routes.CliqueToVertexCover.finalRoute

theorem parameterizedMembership :
    NativeTMInNP Problems.Karp21.Satisfiability.threeSATStructuredProblem :=
  Problems.Karp21.ThreeSATNativeVerifier.threeSATStructuredNativeTMInNP

noncomputable def twoGapPresentationRoute :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedSource
      Benchmark.Hardness.Inputs.StageO.Inputs.twoGapPresentationTarget :=
  Routes.ThreeSATToClique.IngressAdapters.taggedFinalRoute

/-- Gap 1 exposes the already checked direct-TM checker component. -/
noncomputable def twoGapCheckerDirectTM :=
  Problems.Karp21.CliqueNativeVerifier.checker_directTM

/-- Gap 2 packages exact native membership at the same endpoint. -/
theorem twoGapCheckerMembership :
    NativeTMInNP Benchmark.Hardness.Inputs.StageO.Inputs.twoGapCheckerProblem :=
  Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

noncomputable def producerCapability :
    CertifiedReduction
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerSource
      Benchmark.Hardness.Inputs.StageO.Inputs.capabilityProducerTarget :=
  Routes.ThreeSATToClique.sharedGadget

noncomputable def twoGapCheckerCompleteness :
    NativeTMNPComplete Benchmark.Hardness.Inputs.StageO.Inputs.twoGapCheckerProblem :=
  CompletenessTransport.alongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step producerCapability)
    twoGapCheckerMembership

noncomputable def consumerCompleteness :
    NativeTMNPComplete Benchmark.Hardness.Inputs.StageO.Inputs.capabilityConsumerProblem :=
  CompletenessTransport.alongPath
    NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step producerCapability)
    Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

end Benchmark.Hardness.Inputs.StageO.Regression

assert_standard_axioms
  Benchmark.Hardness.Inputs.StageO.Regression.predicateAdapter_exact,
  Benchmark.Hardness.Inputs.StageO.Regression.parameterizedPredicateThree_exact,
  Benchmark.Hardness.Inputs.StageO.Regression.twoGapPresentation_exact,
  Benchmark.Hardness.Inputs.StageO.Regression.fixedTargetRoute,
  Benchmark.Hardness.Inputs.StageO.Regression.autoTargetCompleteness,
  Benchmark.Hardness.Inputs.StageO.Regression.predicateAdapterRoute,
  Benchmark.Hardness.Inputs.StageO.Regression.parameterizedMembership,
  Benchmark.Hardness.Inputs.StageO.Regression.twoGapPresentationRoute,
  Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerDirectTM,
  Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerMembership,
  Benchmark.Hardness.Inputs.StageO.Regression.producerCapability,
  Benchmark.Hardness.Inputs.StageO.Regression.twoGapCheckerCompleteness,
  Benchmark.Hardness.Inputs.StageO.Regression.consumerCompleteness
