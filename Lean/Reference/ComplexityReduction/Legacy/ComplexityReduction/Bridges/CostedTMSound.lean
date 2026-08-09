/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.CostedMap

namespace ComplexityReduction

/-- Soundness hook from the costed functional model to TM2 semantics. -/
structure CostedTMSound : Type 1 where
  sound :
    {X Y : EncodedType} → {f : X.Carrier → Y.Carrier} →
      CostedPolyTimeMap (X := X) (Y := Y) f → TMPolyTimeMap X Y f

namespace CostedPolyTimeMap

/-- Interpret a costed-model map as a TM polynomial-time map via a soundness theorem. -/
theorem to_TMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hSound : CostedTMSound) (h : CostedPolyTimeMap (X := X) (Y := Y) f) :
    TMPolyTimeMap X Y f :=
  hSound.sound h

end CostedPolyTimeMap

namespace CostedMap

/-- Interpret a primitive costed map as a TM polynomial-time map via soundness. -/
theorem to_TMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hSound : CostedTMSound) (h : CostedMap X Y f) :
    TMPolyTimeMap X Y f :=
  hSound.sound (CostedPolyTimeMap.of_costed h)

end CostedMap

namespace KarpReductionM

/-- Forget a costed-model reduction to direct TM semantics using costed soundness. -/
def toTMKarpReductionOfCostedTMSound (hSound : CostedTMSound)
    {A B : EncodedDecisionProblem} (r : KarpReductionM CostedPolyTimeModel A B) :
    TMKarpReduction A B where
  f := r.f.toFun
  polytime := hSound.sound r.f.polytime
  correct := r.correct

end KarpReductionM

namespace PolyReducibleM

/-- Costed-model reducibility implies TM reducibility when the costed model is TM-sound. -/
theorem toTMPolyReducibleOfCostedTMSound (hSound : CostedTMSound)
    {A B : EncodedDecisionProblem} :
    PolyReducibleM CostedPolyTimeModel A B → TMPolyReducible A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toTMKarpReductionOfCostedTMSound hSound⟩

end PolyReducibleM

end ComplexityReduction
