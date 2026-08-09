/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin

/-!
Artifact-compatible boundary wrapper for local 3SAT NP-completeness.

The reusable standard-library theorem surface lives in
`ComplexityReduction.SAT.CookLevin`.  This target module only keeps the stable
wrapper used by generated artifacts and Schaefer/Karp transfer code.
-/

namespace ComplexityReduction
namespace Targets

/--
Explicit trusted boundary for local 3SAT NP-completeness under the costed
polynomial-time model.
-/
structure ThreeSATCompleteBoundary where
  complete : NPCompleteEnc CostedPolyTimeModel SAT.threeSATDecisionProblem

/--
Local 3SAT completeness witness discharged by the P14e locally verified
`InNPEnc` foundation.
-/
def localThreeSATCompleteBoundary : ThreeSATCompleteBoundary where
  complete := SAT.localCookLevinTheorem

/-- Instantiate the existing boundary wrapper from a supplied Cook-Levin theorem. -/
def threeSATCompleteBoundary_ofCookLevin (H : SAT.CookLevinTheorem) :
    ThreeSATCompleteBoundary where
  complete := SAT.threeSAT_npCompleteEnc_ofCookLevin H

/--
Instantiate the boundary wrapper from an explicit compatibility package that
turns every legacy verifier introduction into a machine-backed Cook tableau.
-/
def threeSATCompleteBoundary_ofCookLevinCompatibility
    (H : SAT.CookLevinCompatibility) :
    ThreeSATCompleteBoundary where
  complete := SAT.CookLevinCompatibility.threeSAT_npCompleteEnc H

end Targets
end ComplexityReduction
