/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.CostedMap
import ComplexityReduction.Legacy.ComplexityReduction.Core.NPClass
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Legacy.ComplexityReduction.Targets.ThreeSATCompleteBoundary

/-!
NP-completeness transfer from local 3SAT.

The boundary-explicit transfer theorem remains available for compatibility.
The local theorem uses the P14e `localThreeSATCompleteBoundary` witness.
-/

namespace ComplexityReduction
namespace Targets

/--
If local 3SAT is NP-complete, a costed Karp reduction from 3SAT to `A` and
membership of `A` in NP make `A` NP-complete.
-/
theorem npComplete_of_threeSAT_karp
    (A : EncodedDecisionProblem)
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem)
    (r : KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem A)
    (hAInNP : InNPEnc CostedPolyTimeModel A) :
    NPCompleteEnc CostedPolyTimeModel A :=
  NPCompleteEnc.transfer h3SAT ⟨r⟩ hAInNP

/-- Specialization for the 3SAT-like CSP reverse adapter. -/
theorem threeSATLikeNPComplete_of_threeSAT
    (A : EncodedDecisionProblem)
    (h3SAT : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem)
    (r : KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem A)
    (hAInNP : InNPEnc CostedPolyTimeModel A) :
    NPCompleteEnc CostedPolyTimeModel A :=
  npComplete_of_threeSAT_karp A h3SAT r hAInNP

/--
If a costed Karp reduction from local 3SAT to `A` and local NP membership of
`A` are available, the P14e local Cook-Levin witness makes `A` NP-complete.
-/
theorem npComplete_of_localThreeSAT_karp
    (A : EncodedDecisionProblem)
    (r : KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem A)
    (hAInNP : InNPEnc CostedPolyTimeModel A) :
    NPCompleteEnc CostedPolyTimeModel A :=
  npComplete_of_threeSAT_karp A localThreeSATCompleteBoundary.complete r hAInNP

end Targets
end ComplexityReduction
