/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlySuffixValidityCNF

/-!
Bundled 3CNF surface for the x-only Cook-Levin verifier CNF.

This file packages the already checked x-only emitted CNF with the reusable CNF
splitter.  It is still only the semantic 3CNF layer; the direct standard-TM
`TMPolyTimeMap` witness for the generator is handled at the root layer.
-/

namespace ComplexityReduction
namespace SAT

/-- The x-only emitted Cook-Levin CNF, converted to bundled 3CNF. -/
noncomputable def tmVerifierXOnlyEmittedThreeCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) : ThreeCNF :=
  CNF.splitToThreeCNF
    (tmVerifierXOnlyEmittedCNF V (tmVerifierActivePushPayloadBoundary V) x)

/-- The bundled x-only 3CNF surface is satisfiable exactly for yes-instances. -/
theorem tmVerifierXOnlyEmittedThreeCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    ThreeCNF.Satisfiable (tmVerifierXOnlyEmittedThreeCNF V x) ↔ L.isYes x := by
  rw [tmVerifierXOnlyEmittedThreeCNF, CNF.splitToThreeCNF_satisfiable_iff,
    tmVerifierXOnlyEmittedCNF_satisfiable_iff_isYes]

end SAT
end ComplexityReduction
