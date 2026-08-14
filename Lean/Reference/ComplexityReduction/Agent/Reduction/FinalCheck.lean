/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Certificate.NativeCompleteness

/-! Stable imports and an exact-endpoint identity theorem for final artifacts. -/

namespace ComplexityReduction
namespace Agent
namespace Reduction
namespace FinalCheck

open ComplexityReduction Certificate

theorem exactEndpoint {problem : Encoding.PresentedProblem}
    (proof : NativeTMNPHard problem) : NativeTMNPHard problem := proof

end FinalCheck
end Reduction
end Agent
end ComplexityReduction
