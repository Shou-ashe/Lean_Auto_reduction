import ComplexityReduction.Agent.Hardness.Runtime
import Benchmark.Hardness.Inputs.IRFeasibility.Graph.GraphToRoleGraph
import Benchmark.Hardness.Inputs.IRFeasibility.Clause.ClauseToCSP
import Benchmark.Hardness.Inputs.IRFeasibility.Incidence.IncidenceToEON

/-!
Kernel regression for the matched IR-feasibility benchmark matrix.

This module is deliberately outside the production aggregate and carries no
typed-edge annotations.  It does not add a reduction facade: every path below
references only declarations that already exist in `ComplexityReduction`.
-/

namespace Benchmark.Hardness.IRFeasibilityRegression

open ComplexityReduction
open ComplexityReduction.Certificate ComplexityReduction.Encoding ComplexityReduction.Protocol

noncomputable section

def policy : AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

def request (source target : PresentedProblem) : TypedAutoReductionRequest where
  source := .fromPresented source
  policy := policy
  objective := .reduceTo source target

noncomputable def close {source target : PresentedProblem}
    (path : CertifiedPath source target) : TypedAutoReductionResult (request source target) :=
  TypedAutoReductionResult.reduceToPath policy (by rfl) path

private abbrev graphSource : PresentedProblem :=
  Inputs.IRFeasibility.Graph.GraphToRoleGraph.source
private abbrev graphTarget : PresentedProblem :=
  Inputs.IRFeasibility.Graph.GraphToRoleGraph.target

noncomputable def graphFlatPath : CertifiedPath graphSource graphTarget :=
  .step ComplexityReduction.Routes.GraphToRoleGraph.finalRoute

noncomputable def graphIRPath : CertifiedPath graphSource graphTarget :=
  .cons
    (.step ComplexityReduction.Domain.GraphToGraphIRAdapter.sourceAdapter)
    ComplexityReduction.Domain.GraphIRRoleAssignmentGadget.sharedGadget

noncomputable def graphFlatResult := close graphFlatPath
noncomputable def graphIRResult := close graphIRPath

private abbrev structuredCNFSource : PresentedProblem :=
  Inputs.IRFeasibility.Clause.ClauseToCSP.structuredCNFSource
private abbrev twoCNFSource : PresentedProblem :=
  Inputs.IRFeasibility.Clause.ClauseToCSP.twoCNFSource
private abbrev threeSATSource : PresentedProblem :=
  Inputs.IRFeasibility.Clause.ClauseToCSP.threeSATSource
private noncomputable abbrev cspTarget : PresentedProblem :=
  Inputs.IRFeasibility.Clause.ClauseToCSP.target

noncomputable def structuredCNFFlatPath : CertifiedPath structuredCNFSource cspTarget :=
  .step ComplexityReduction.Routes.ClauseToCSP.finalRoute

noncomputable def structuredCNFIRPath : CertifiedPath structuredCNFSource cspTarget :=
  .cons
    (.step ComplexityReduction.Domain.CNFToThreeSATStandardTM.sharedGadget)
    ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget

noncomputable def twoCNFFlatPath : CertifiedPath twoCNFSource cspTarget :=
  .step ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.twoCNFToCSPRoute

noncomputable def twoCNFIRPath : CertifiedPath twoCNFSource cspTarget :=
  .cons
    (.step ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.twoCNFIngress)
    ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget

noncomputable def threeSATFlatPath : CertifiedPath threeSATSource cspTarget :=
  .step ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.threeSATToCSPRoute

noncomputable def threeSATIRPath : CertifiedPath threeSATSource cspTarget :=
  .step ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget

noncomputable def structuredCNFFlatResult := close structuredCNFFlatPath
noncomputable def structuredCNFIRResult := close structuredCNFIRPath
noncomputable def twoCNFFlatResult := close twoCNFFlatPath
noncomputable def twoCNFIRResult := close twoCNFIRPath
noncomputable def threeSATFlatResult := close threeSATFlatPath
noncomputable def threeSATIRResult := close threeSATIRPath

private abbrev exactCoverSource : PresentedProblem :=
  Inputs.IRFeasibility.Incidence.IncidenceToEON.originalSource
private abbrev modifiedExactCoverSource : PresentedProblem :=
  Inputs.IRFeasibility.Incidence.IncidenceToEON.modifiedSource
private abbrev eonTarget : PresentedProblem :=
  Inputs.IRFeasibility.Incidence.IncidenceToEON.target

noncomputable def exactCoverFlatPath : CertifiedPath exactCoverSource eonTarget :=
  .step ComplexityReduction.Routes.IncidenceToRoleGraph.originalRoute

noncomputable def exactCoverIRPath : CertifiedPath exactCoverSource eonTarget :=
  .cons
    (.step ComplexityReduction.Domain.SetSystemToIncidenceAdapter.sourceAdapter)
    ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

noncomputable def modifiedExactCoverFlatPath :
    CertifiedPath modifiedExactCoverSource eonTarget :=
  .step ComplexityReduction.Routes.IncidenceToRoleGraph.modifiedRoute

noncomputable def modifiedExactCoverIRPath :
    CertifiedPath modifiedExactCoverSource eonTarget :=
  .cons
    (.step ComplexityReduction.Domain.ModifiedExactCoverInput.modifiedSourceAdapter)
    ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget

noncomputable def exactCoverFlatResult := close exactCoverFlatPath
noncomputable def exactCoverIRResult := close exactCoverIRPath
noncomputable def modifiedExactCoverFlatResult := close modifiedExactCoverFlatPath
noncomputable def modifiedExactCoverIRResult := close modifiedExactCoverIRPath

end

end Benchmark.Hardness.IRFeasibilityRegression

assert_standard_axioms
  Benchmark.Hardness.IRFeasibilityRegression.graphFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.graphIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.graphFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.graphIRResult,
  Benchmark.Hardness.IRFeasibilityRegression.structuredCNFFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.structuredCNFIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.twoCNFFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.twoCNFIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.threeSATFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.threeSATIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.structuredCNFFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.structuredCNFIRResult,
  Benchmark.Hardness.IRFeasibilityRegression.twoCNFFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.twoCNFIRResult,
  Benchmark.Hardness.IRFeasibilityRegression.threeSATFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.threeSATIRResult,
  Benchmark.Hardness.IRFeasibilityRegression.exactCoverFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.exactCoverIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.modifiedExactCoverFlatPath,
  Benchmark.Hardness.IRFeasibilityRegression.modifiedExactCoverIRPath,
  Benchmark.Hardness.IRFeasibilityRegression.exactCoverFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.exactCoverIRResult,
  Benchmark.Hardness.IRFeasibilityRegression.modifiedExactCoverFlatResult,
  Benchmark.Hardness.IRFeasibilityRegression.modifiedExactCoverIRResult
