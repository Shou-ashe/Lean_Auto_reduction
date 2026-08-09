/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.PolyTimeModel

namespace ComplexityReduction

/-- A plain decision problem. -/
structure DecisionProblem : Type 1 where
  Instance : Type
  isYes : Instance → Prop

/-- A decision problem whose instances carry a fixed finite-alphabet encoding. -/
structure EncodedDecisionProblem : Type 1 where
  Instance : EncodedType
  isYes : Instance.Carrier → Prop

namespace DecisionProblem

/-- Bridge a plain problem to the encoded layer using the trivial raw encoding. -/
def withRawEncoding (L : DecisionProblem) : EncodedDecisionProblem where
  Instance := EncodedType.raw L.Instance
  isYes := L.isYes

/-- Bridge a plain problem to the encoded layer using a typeclass encoding. -/
def withEncoding (L : DecisionProblem) [HasEncoding L.Instance] : EncodedDecisionProblem where
  Instance := HasEncoding.toEncodedType L.Instance
  isYes := L.isYes

end DecisionProblem

/-- A polynomial-time Boolean decider for an encoded decision problem. -/
structure PolyTimeDecider (M : PolyTimeModel) (L : EncodedDecisionProblem) where
  decide : PolyTimeMap M L.Instance EncodedType.bool
  correct : ∀ x, decide.toFun x = true ↔ L.isYes x

/-- Deterministic polynomial time over encoded decision problems. -/
def InP (M : PolyTimeModel) (L : EncodedDecisionProblem) : Prop :=
  Nonempty (PolyTimeDecider M L)

/-- Bundled encoded decision problems in `P`, relative to a chosen model. -/
abbrev PClass (M : PolyTimeModel) : Type 1 :=
  { L : EncodedDecisionProblem // InP M L }

namespace InP

/-- Build `InP` from an explicit polynomial-time Boolean decider. -/
theorem intro {M : PolyTimeModel} {L : EncodedDecisionProblem}
    (decide : PolyTimeMap M L.Instance EncodedType.bool)
    (hCorrect : ∀ x, decide.toFun x = true ↔ L.isYes x) :
    InP M L :=
  ⟨{ decide := decide, correct := hCorrect }⟩

end InP

/-- A polynomial-time equivalence between two encodings. -/
structure PolyTimeEquiv (M : PolyTimeModel) (X Y : EncodedType) where
  toMap : PolyTimeMap M X Y
  invMap : PolyTimeMap M Y X
  left_inv : ∀ x, invMap.toFun (toMap.toFun x) = x
  right_inv : ∀ y, toMap.toFun (invMap.toFun y) = y

end ComplexityReduction
