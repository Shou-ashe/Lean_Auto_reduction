import ComplexityReduction.Agent.Hardness.Runtime
import Benchmark.Hardness.Inputs.CookLevin.KnapsackNativeNP

/-! Final-resolver regressions for the Phase 2 native Cook--Levin root and suffix lane. -/

namespace Benchmark.Hardness.Regression.NativeCookLevin

abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  Benchmark.Hardness.Inputs.CookLevin.KnapsackNativeNP.source

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def nativeCookLevinRoot : ComplexityReduction.Certificate.CertifiedReduction
    source ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT :=
  ComplexityReduction.Certificate.NativeCookLevin.reduce
    Benchmark.Hardness.Inputs.CookLevin.KnapsackNativeNP.membership

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

def directRequest : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented source
  policy := policy
  objective := .reduceToKnownNP source
    ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem

@[complexity_reduction_ir_typed_final_result]
noncomputable def directResult :
    ComplexityReduction.Protocol.TypedAutoReductionResult directRequest :=
  by_hardness_resolver

def suffixRequest : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented source
  policy := policy
  objective := .reduceToKnownNP source
    ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

@[complexity_reduction_ir_typed_final_result]
noncomputable def suffixResult :
    ComplexityReduction.Protocol.TypedAutoReductionResult suffixRequest :=
  by_hardness_resolver

end Benchmark.Hardness.Regression.NativeCookLevin

assert_standard_axioms
  Benchmark.Hardness.Regression.NativeCookLevin.nativeCookLevinRoot,
  Benchmark.Hardness.Regression.NativeCookLevin.directResult,
  Benchmark.Hardness.Regression.NativeCookLevin.suffixResult
