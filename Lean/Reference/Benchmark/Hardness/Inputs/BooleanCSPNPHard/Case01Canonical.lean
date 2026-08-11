import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
import ComplexityReduction.Presentation.ThreeSATLike

/-! Q-B01: the exact library presentation of the hard 3SAT-like Boolean CSP. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case01Canonical

open ComplexityReduction
open ComplexityReduction.Domain.BooleanCSP

noncomputable section

abbrev gamma : Gamma := ComplexityReduction.Presentation.ThreeSATLike.language

/-- Exact known Boolean-CSP endpoint; the zero-authoring baseline. -/
abbrev problem : Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.ThreeSATLike.presentedProblem

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case01Canonical
