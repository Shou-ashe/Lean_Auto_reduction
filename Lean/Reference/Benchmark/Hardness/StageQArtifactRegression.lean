/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Runtime
import ComplexityReduction.Protocol.InP
import Benchmark.Hardness.StageQRegression

/-!
Compiled-shape regression for `build_stage_q_in_p_batch_artifact_source`.

The declarations below intentionally mirror the emitter output for the
`StageQRegression.fullUnaryProblem` smoke case.
-/

namespace Benchmark.Hardness.StageQInPBatch

noncomputable section

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := false }

namespace CaseStageQSmoke

def request : ComplexityReduction.Protocol.TypedInPRequestV1 where
  source := .fromPresented Benchmark.Hardness.StageQRegression.fullUnaryProblem
  policy := policy
  objective := .proveInP Benchmark.Hardness.StageQRegression.fullUnaryProblem

noncomputable def deterministicMembership :
    ComplexityReduction.Certificate.NativeTMInP
      Benchmark.Hardness.StageQRegression.fullUnaryProblem :=
  Benchmark.Hardness.StageQRegression.fullUnaryGamma_inP

noncomputable def result : ComplexityReduction.Protocol.TypedInPResultV1 request :=
  ComplexityReduction.Protocol.TypedInPResultV1.proveInP
    policy (by rfl) deterministicMembership

end CaseStageQSmoke
end

end Benchmark.Hardness.StageQInPBatch

assert_standard_axioms
  Benchmark.Hardness.StageQInPBatch.CaseStageQSmoke.deterministicMembership,
  Benchmark.Hardness.StageQInPBatch.CaseStageQSmoke.result
