import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Domain.BoolFiniteDomainCSPToStructuredCNF
import ComplexityReduction.Presentation.ThreeSATLike

namespace Benchmark.Hardness.Inputs.Authoring.ClosedFamily

/-!
The production CSP-to-CNF certificate is intentionally an attributed open
family.  Its declaration cannot enter the closed registry until the language
parameter is instantiated and the resulting wrapper is validated.
-/
noncomputable def source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Domain.BoolFiniteDomainCSPToStructuredCNF.sourceProblem
    ComplexityReduction.Presentation.ThreeSATLike.language

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .unresolvedFamilyPremise .sharedGadget source
      ComplexityReduction.Problems.Karp21.Satisfiability.cnfSATStructuredProblem :=
  .exact

end Benchmark.Hardness.Inputs.Authoring.ClosedFamily
