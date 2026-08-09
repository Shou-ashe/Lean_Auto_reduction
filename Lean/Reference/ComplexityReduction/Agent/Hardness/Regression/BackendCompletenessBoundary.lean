/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.NativeCompleteness

/-!
Non-production negative fixture for the backend/native completeness boundary.

The declaration is intentionally poisoned and exists only so registry and
resolver regressions can observe an exact closed `TMNPCompleteEnc` head.  A
benchmark-facing alias may be attributed, but it must never be reclassified as
`NativeTMNPComplete` or survive a standard-axiom audit.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.BackendCompletenessBoundary

open ComplexityReduction.Encoding

axiom poisonedBackendCompleteness (problem : PresentedProblem) :
  ComplexityReduction.TMNPCompleteEnc problem.toEncodedDecisionProblem

end ComplexityReduction.Agent.Hardness.Regression.BackendCompletenessBoundary
