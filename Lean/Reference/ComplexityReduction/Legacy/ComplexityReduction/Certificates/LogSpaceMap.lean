/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedTMSound
import ComplexityReduction.Legacy.ComplexityReduction.Core.NPClass

namespace ComplexityReduction

/--
Legacy project-local log-space map certificates between encoded types.

This older layer intentionally remains available for compatibility, but it has
an `of_costed` constructor and therefore should not be cited as a strict
streaming or machine-level log-space proof.  New reduction artifacts should use
`StrictLogSpaceMap` or `StrictStreamMap` when they need an auditable log-space
certificate.
-/
inductive LogSpaceMap : {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  | of_costed {X Y : EncodedType} {f : X.Carrier → Y.Carrier} :
      CostedMap X Y f → LogSpaceMap f
  | id_map {X : EncodedType} :
      LogSpaceMap (X := X) (Y := X) id
  | comp_map {X Y Z : EncodedType} {f : Y.Carrier → Z.Carrier} {g : X.Carrier → Y.Carrier}
      (hf : LogSpaceMap f) (hg : LogSpaceMap g) :
      LogSpaceMap (f ∘ g)
  | const_map {X Y : EncodedType} (y : Y.Carrier) :
      LogSpaceMap (X := X) (Y := Y) (fun _ => y)
  | fst_map {X Y : EncodedType} :
      LogSpaceMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  | snd_map {X Y : EncodedType} :
      LogSpaceMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  | prod_mk_map {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier}
      {g : X.Carrier → Z.Carrier}
      (hf : LogSpaceMap f) (hg : LogSpaceMap g) :
      LogSpaceMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  | inl_map {X Y : EncodedType} :
      LogSpaceMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  | inr_map {X Y : EncodedType} :
      LogSpaceMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  | list_map_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (hf : LogSpaceMap f) :
      LogSpaceMap (X := EncodedType.list X) (Y := EncodedType.list Y)
        (fun xs => xs.map f)
  | list_append_map {X : EncodedType} :
      LogSpaceMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  | list_foldl_map {X Y : EncodedType} {step : Y.Carrier × X.Carrier → Y.Carrier}
      (hstep : LogSpaceMap (X := EncodedType.prod Y X) (Y := Y) step)
      (init : Y.Carrier) :
      LogSpaceMap (X := EncodedType.list X) (Y := Y)
        (fun xs => xs.foldl (fun acc x => step (acc, x)) init)

namespace LogSpaceMap

/-- Every project-local log-space certificate induces a costed polytime certificate. -/
theorem toCostedPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : LogSpaceMap (X := X) (Y := Y) f) :
    CostedPolyTimeMap (X := X) (Y := Y) f := by
  induction h with
  | of_costed h => exact CostedPolyTimeMap.of_costed h
  | id_map => exact CostedPolyTimeMap.id_map
  | comp_map hf hg ihf ihg => exact CostedPolyTimeMap.comp_map ihf ihg
  | const_map y => exact CostedPolyTimeMap.const_map y
  | fst_map => exact CostedPolyTimeMap.fst_map
  | snd_map => exact CostedPolyTimeMap.snd_map
  | prod_mk_map hf hg ihf ihg => exact CostedPolyTimeMap.prod_mk_map ihf ihg
  | inl_map => exact CostedPolyTimeMap.inl_map
  | inr_map => exact CostedPolyTimeMap.inr_map
  | list_map_map hf ih => exact CostedPolyTimeMap.list_map_map ih
  | list_append_map => exact CostedPolyTimeMap.list_append_map
  | list_foldl_map hstep init ih => exact CostedPolyTimeMap.list_foldl_map ih init

end LogSpaceMap

/-- A log-space Karp reduction between encoded decision problems. -/
structure LogKarpReduction (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  logspace : LogSpaceMap (X := A.Instance) (Y := B.Instance) f
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)

/-- Log-space many-one reducibility. -/
def LogReducible (A B : EncodedDecisionProblem) : Prop :=
  Nonempty (LogKarpReduction A B)

namespace LogKarpReduction

/-- Forget a log-space reduction to the costed polynomial-time model. -/
def toCostedReduction {A B : EncodedDecisionProblem} (r : LogKarpReduction A B) :
    KarpReductionM CostedPolyTimeModel A B where
  f := { toFun := r.f, polytime := r.logspace.toCostedPolyTimeMap }
  correct := r.correct

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : LogKarpReduction A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

end LogKarpReduction

namespace LogReducible

/-- Log-space reducibility is reflexive. -/
theorem refl (A : EncodedDecisionProblem) : LogReducible A A :=
  ⟨{ f := id, logspace := LogSpaceMap.id_map, correct := fun _ => Iff.rfl }⟩

/-- Log-space reducibility is transitive. -/
theorem trans {A B C : EncodedDecisionProblem}
    (hAB : LogReducible A B) (hBC : LogReducible B C) :
    LogReducible A C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨{
    f := rBC.f ∘ rAB.f
    logspace := LogSpaceMap.comp_map rBC.logspace rAB.logspace
    correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x)) }⟩

/-- Project-local log-space reducibility implies costed-model reducibility. -/
theorem toCostedReducible {A B : EncodedDecisionProblem} :
    LogReducible A B → PolyReducibleM CostedPolyTimeModel A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toCostedReduction⟩

end LogReducible

namespace InNPEnc

/-- Encoded NP is downward closed under project-local log-space reductions. -/
theorem of_log_reduction {A B : EncodedDecisionProblem}
    (hAB : LogReducible A B) (hB : InNPEnc CostedPolyTimeModel B) :
    InNPEnc CostedPolyTimeModel A :=
  InNPEnc.of_reduction hAB.toCostedReducible hB

end InNPEnc

/-- Log-completeness in NP for encoded decision problems. -/
def LogCompleteInNP (L : EncodedDecisionProblem) : Prop :=
  InNPEnc CostedPolyTimeModel L ∧
    ∀ L', InNPEnc CostedPolyTimeModel L' → LogReducible L' L

namespace LogCompleteInNP

/-- Transfer log-completeness across a log-space reduction. -/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : LogCompleteInNP A) (hRed : LogReducible A B)
    (hB : InNPEnc CostedPolyTimeModel B) :
    LogCompleteInNP B := by
  constructor
  · exact hB
  · intro L hL
    exact LogReducible.trans (hA.2 L hL) hRed

end LogCompleteInNP

end ComplexityReduction
