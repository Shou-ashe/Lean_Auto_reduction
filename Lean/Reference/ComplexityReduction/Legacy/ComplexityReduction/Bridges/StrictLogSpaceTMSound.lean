/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.StrictLogSpaceMap

namespace ComplexityReduction

/--
Soundness hook from strict project-local log-space certificates to TM2 semantics.

This is intentionally separate from `CostedTMSound`: a strict log-space/TM claim
requires this witness, not merely a costed output-size certificate.
-/
structure StrictLogSpaceTMSound : Type 1 where
  sound :
    {X Y : EncodedType} → {f : X.Carrier → Y.Carrier} →
      StrictLogSpaceMap (X := X) (Y := Y) f → TMPolyTimeMap X Y f

namespace StrictLogSpaceMap

/-- Interpret a strict log-space certificate as a TM polynomial-time map. -/
theorem to_TMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hSound : StrictLogSpaceTMSound)
    (h : StrictLogSpaceMap (X := X) (Y := Y) f) :
    TMPolyTimeMap X Y f :=
  hSound.sound h

end StrictLogSpaceMap

namespace StrictLogReductionCert

/-- Forget a strict log-space reduction to direct TM semantics using the strict soundness hook. -/
def toTMKarpReduction (hSound : StrictLogSpaceTMSound)
    {A B : EncodedDecisionProblem} (r : StrictLogReductionCert A B) :
    TMKarpReduction A B where
  f := r.f
  polytime := r.strict_logspace.to_TMPolyTimeMap hSound
  correct := r.correct

end StrictLogReductionCert

namespace StrictLogReducible

/-- Strict log-space reducibility implies TM reducibility when the strict layer is TM-sound. -/
theorem to_TMPolyReducible (hSound : StrictLogSpaceTMSound)
    {A B : EncodedDecisionProblem} :
    StrictLogReducible A B → TMPolyReducible A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toTMKarpReduction hSound⟩

end StrictLogReducible

end ComplexityReduction
