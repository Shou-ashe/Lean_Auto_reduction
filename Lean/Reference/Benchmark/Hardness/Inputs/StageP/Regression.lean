import Benchmark.Hardness.Inputs.StageP.ContractProbes
import ComplexityReduction.Problems.Karp21.ExactCoverStandardTM

/-! Contract-only type regression; this file contains no Stage P solution. -/

namespace Benchmark.Hardness.Inputs.StageP.Regression

#check Benchmark.Hardness.Inputs.StageP.Inputs.twoGapPresentationPredicate
#check Benchmark.Hardness.Inputs.StageP.Inputs.threeGapParameterizedPredicate
#check Benchmark.Hardness.Inputs.StageP.Inputs.threeGapParameterizedThree
#check Benchmark.Hardness.Inputs.StageP.Inputs.singleSemanticSource
#check Benchmark.Hardness.Inputs.StageP.Inputs.singleSemanticTarget
#check Benchmark.Hardness.Inputs.StageP.Inputs.singleProgramSource
#check Benchmark.Hardness.Inputs.StageP.Inputs.singleProgramTarget
#check Benchmark.Hardness.Inputs.StageP.Inputs.singleNativeMembershipSource
#check Benchmark.Hardness.Inputs.StageP.Inputs.capabilityProducerSource
#check Benchmark.Hardness.Inputs.StageP.Inputs.capabilityProducerTarget
#check Benchmark.Hardness.Inputs.StageP.ProducerSupport.targetNativeTMInNP
#check ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverStructuredFiniteVerify_tm_polytime
#check ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverIndexCertificate_inputSize_le_poly
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.proofProbe
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.programProbe
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.presentationProbe
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.directTMProbe
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.membershipProbe
#check Benchmark.Hardness.Inputs.StageP.ContractProbes.completenessProbe

end Benchmark.Hardness.Inputs.StageP.Regression
