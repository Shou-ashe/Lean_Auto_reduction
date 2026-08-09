/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityTransport

/-!
High-level direct-TM reduction composition API.

This module gives generated proofs stable theorem names for common direct-TM
route assembly patterns.  The declarations are wrappers around the existing
transport lemmas, with argument order chosen for straightforward `exact` and
`apply` use.
-/

namespace ComplexityReduction

namespace TMKarpReduction

/-- A concrete direct-TM Karp reduction is a direct-TM reducibility witness. -/
theorem toTMPolyReducible {A B : EncodedDecisionProblem}
    (r : TMKarpReduction A B) :
    TMPolyReducible A B :=
  ⟨r⟩

end TMKarpReduction

/-- Compose two direct-TM polynomial reductions. -/
theorem composeTMKarp {A B C : EncodedDecisionProblem}
    (rAB : TMPolyReducible A B)
    (rBC : TMPolyReducible B C) :
    TMPolyReducible A C :=
  TMPolyReducible.trans rAB rBC

/--
Lift ordinary direct-TM NP-completeness along a reduction from the complete
problem to the target problem.
-/
theorem liftNPCompleteAlongReduction {K L : EncodedDecisionProblem}
    (hK : TMNPCompleteEnc K)
    (rKL : TMPolyReducible K L)
    (hL : TMInNP L) :
    TMNPCompleteEnc L :=
  TMNPCompleteEnc.transfer hK rKL hL

/--
Transfer direct-TM NP-completeness across an explicitly supplied equivalence
route.  The reverse route is retained in the API so callers can pass a bundled
two-way bridge, although hardness only needs the forward complete-to-target
direction.
-/
theorem transferTMNPComplete {A B : EncodedDecisionProblem}
    (rAB : TMPolyReducible A B)
    (_rBA : TMPolyReducible B A)
    (hA : TMNPCompleteEnc A)
    (hBmem : TMInNP B) :
    TMNPCompleteEnc B :=
  TMNPCompleteEnc.transfer hA rAB hBmem

/-- Compose an explicit encoding bridge with a downstream direct-TM reduction. -/
theorem reduceViaEncodingBridge {A B C : EncodedDecisionProblem}
    (encode : TMKarpReduction A B)
    (hard : TMPolyReducible B C) :
    TMPolyReducible A C :=
  TMPolyReducible.trans encode.toTMPolyReducible hard

#check TMKarpReduction.toTMPolyReducible
#check composeTMKarp
#check liftNPCompleteAlongReduction
#check transferTMNPComplete
#check reduceViaEncodingBridge

end ComplexityReduction
