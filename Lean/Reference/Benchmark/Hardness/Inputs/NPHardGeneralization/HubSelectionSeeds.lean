import ComplexityReduction.Agent.Hardness.Runtime
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Presentation.ZeroOneIP
import ComplexityReduction.Problems.Karp21.GraphAtoms

/-!
Benchmark-local native-hardness seeds for deterministic hub-selection tests.

Each declaration is derived by the production NP-hard resolver from the
canonical Cook--Levin root and an existing forward certified path.  They add
no extra axioms and no hidden reduction; their only purpose is to make several exact
hard endpoints simultaneously visible to the G-D planner.
-/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Protocol

def cliqueRequest : TypedNPHardRequestV1 where
  problem := ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

noncomputable def cliqueResult : TypedNPHardResultV1 cliqueRequest :=
  by_np_hard_resolver

@[complexity_reduction_ir_typed_native_hardness]
theorem cliqueHardness :
    NativeTMNPHard ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem :=
  cliqueResult.extractNativeHardness

def vertexCoverRequest : TypedNPHardRequestV1 where
  problem := ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

noncomputable def vertexCoverResult : TypedNPHardResultV1 vertexCoverRequest :=
  by_np_hard_resolver

@[complexity_reduction_ir_typed_native_hardness]
theorem vertexCoverHardness :
    NativeTMNPHard
      ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem :=
  vertexCoverResult.extractNativeHardness

def exactCoverRequest : TypedNPHardRequestV1 where
  problem := ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem

noncomputable def exactCoverResult : TypedNPHardResultV1 exactCoverRequest :=
  by_np_hard_resolver

@[complexity_reduction_ir_typed_native_hardness]
theorem exactCoverHardness :
    NativeTMNPHard
      ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem :=
  exactCoverResult.extractNativeHardness

def zeroOneIPRequest : TypedNPHardRequestV1 where
  problem := ComplexityReduction.Presentation.ZeroOneIP.structuredProblem

noncomputable def zeroOneIPResult : TypedNPHardResultV1 zeroOneIPRequest :=
  by_np_hard_resolver

@[complexity_reduction_ir_typed_native_hardness]
theorem zeroOneIPHardness :
    NativeTMNPHard ComplexityReduction.Presentation.ZeroOneIP.structuredProblem :=
  zeroOneIPResult.extractNativeHardness

end Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds

assert_standard_axioms
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.cliqueResult,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.cliqueHardness,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.vertexCoverResult,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.vertexCoverHardness,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.exactCoverResult,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.exactCoverHardness,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.zeroOneIPResult,
  Benchmark.Hardness.Inputs.NPHardGeneralization.HubSelectionSeeds.zeroOneIPHardness
