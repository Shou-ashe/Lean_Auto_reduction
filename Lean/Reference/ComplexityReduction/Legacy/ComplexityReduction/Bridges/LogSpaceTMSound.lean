/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.LogSpaceMap

namespace ComplexityReduction

/-- Soundness hook from project-local log-space certificates to TM2 semantics. -/
structure LogSpaceTMSound : Type 1 where
  sound :
    {X Y : EncodedType} → {f : X.Carrier → Y.Carrier} →
      LogSpaceMap (X := X) (Y := Y) f → TMPolyTimeMap X Y f

/-- A costed TM soundness theorem also interprets local log-space certificates as TM maps. -/
def logSpaceTMSoundOfCostedTMSound (hCosted : CostedTMSound) :
    LogSpaceTMSound where
  sound := fun h => hCosted.sound h.toCostedPolyTimeMap

namespace LogSpaceMap

/-- Interpret a log-space certificate as a TM polynomial-time map via soundness. -/
theorem to_TMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hSound : LogSpaceTMSound) (h : LogSpaceMap (X := X) (Y := Y) f) :
    TMPolyTimeMap X Y f :=
  hSound.sound h

end LogSpaceMap

namespace LogKarpReduction

/-- Forget a log-space reduction to direct TM semantics using log-space soundness. -/
def toTMReduction (hSound : LogSpaceTMSound)
    {A B : EncodedDecisionProblem} (r : LogKarpReduction A B) :
    TMKarpReduction A B where
  f := r.f
  polytime := r.logspace.to_TMPolyTimeMap hSound
  correct := r.correct

end LogKarpReduction

namespace LogReducible

/-- Log-space reducibility implies TM reducibility when the log-space layer is TM-sound. -/
theorem to_TMPolyReducible (hSound : LogSpaceTMSound)
    {A B : EncodedDecisionProblem} :
    LogReducible A B → TMPolyReducible A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toTMReduction hSound⟩

/-- Costed soundness is enough to interpret local log-space reductions as TM reductions. -/
theorem to_TMPolyReducible_ofCostedTMSound (hCosted : CostedTMSound)
    {A B : EncodedDecisionProblem} :
    LogReducible A B → TMPolyReducible A B :=
  to_TMPolyReducible (logSpaceTMSoundOfCostedTMSound hCosted)

end LogReducible

end ComplexityReduction
