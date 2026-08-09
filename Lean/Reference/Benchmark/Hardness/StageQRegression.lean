/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP
import ComplexityReduction.AxiomGate

/-! Kernel-level Stage-Q smoke test for class decisions and `prove_in_p`. -/

namespace Benchmark
namespace Hardness
namespace StageQRegression

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open ComplexityReduction.Domain.BooleanCSP.PAlgorithms

noncomputable section

/-- One finite Γ containing the full unary Boolean relation. -/
def fullUnaryGamma : Gamma where
  Symbol := Unit
  finiteSymbol := inferInstance
  relationOf := fun _ => BoolRel.full 1

theorem fullUnaryGamma_zeroValid : fullUnaryGamma.IsZeroValid := by
  intro symbol
  cases symbol
  exact BoolRel.holds_full 1 _

theorem fullUnaryGamma_decider_accepts_zeroValid :
    (gammaClassDecider fullUnaryGamma).zeroValid = true :=
  (gammaClassDecider_zeroValid_iff fullUnaryGamma).2 fullUnaryGamma_zeroValid

/-- Stable exact presentation used by versioned requests and artifact emitters. -/
abbrev fullUnaryProblem : ComplexityReduction.Encoding.PresentedProblem :=
  cspOf fullUnaryGamma

/-- A complete P witness whose program is the exact constant-true `PolyProg`. -/
def fullUnaryGamma_inP :
    ComplexityReduction.Certificate.NativeTMInP fullUnaryProblem :=
  zeroValid_inP fullUnaryGamma fullUnaryGamma_zeroValid

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := false }

def request : ComplexityReduction.Protocol.TypedInPRequestV1 where
  source := .fromPresented fullUnaryProblem
  policy := policy
  objective := .proveInP fullUnaryProblem

def result : ComplexityReduction.Protocol.TypedInPResultV1 request :=
  ComplexityReduction.Protocol.TypedInPResultV1.proveInP
    policy (by rfl) fullUnaryGamma_inP

end

end StageQRegression
end Hardness
end Benchmark

assert_standard_axioms
  Benchmark.Hardness.StageQRegression.fullUnaryGamma_decider_accepts_zeroValid,
  Benchmark.Hardness.StageQRegression.fullUnaryGamma_inP,
  Benchmark.Hardness.StageQRegression.result
