/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.CostedMap

namespace ComplexityReduction

/--
Human-auditable metadata for a strict log-space primitive.

Unlike the legacy `LogSpaceMap`, the strict layer deliberately has no constructor
from arbitrary `CostedMap`.  A registered primitive is a reviewed streaming
construction; interpreting it as a concrete TM theorem still requires an
explicit `StrictLogSpaceTMSound` witness from the bridge layer.
-/
structure StrictLogSpacePrimitive (X Y : EncodedType) (f : X.Carrier → Y.Carrier) where
  name : String
  construction : String
  space_bound : String
  oracle_free : String
  costed : CostedPolyTimeMap (X := X) (Y := Y) f
  deriving Repr

/--
Strict project-local log-space map certificates.

This is a syntactic certificate DSL for reductions whose maps are explicitly
streaming/log-space at the project layer.  It intentionally does not include the
legacy costed-map shortcut, so a polynomial output-size proof cannot be
relabelled as strict log-space.
-/
inductive StrictLogSpaceMap : {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  | id_map {X : EncodedType} :
      StrictLogSpaceMap (X := X) (Y := X) id
  | comp_map {X Y Z : EncodedType} {f : Y.Carrier → Z.Carrier}
      {g : X.Carrier → Y.Carrier}
      (hf : StrictLogSpaceMap f) (hg : StrictLogSpaceMap g) :
      StrictLogSpaceMap (f ∘ g)
  | const_map {X Y : EncodedType} (y : Y.Carrier) :
      StrictLogSpaceMap (X := X) (Y := Y) (fun _ => y)
  | fst_map {X Y : EncodedType} :
      StrictLogSpaceMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  | snd_map {X Y : EncodedType} :
      StrictLogSpaceMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  | prod_mk_map {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier}
      {g : X.Carrier → Z.Carrier}
      (hf : StrictLogSpaceMap f) (hg : StrictLogSpaceMap g) :
      StrictLogSpaceMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  | inl_map {X Y : EncodedType} :
      StrictLogSpaceMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  | inr_map {X Y : EncodedType} :
      StrictLogSpaceMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  | list_map_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (hf : StrictLogSpaceMap f) :
      StrictLogSpaceMap (X := EncodedType.list X) (Y := EncodedType.list Y)
        (fun xs => xs.map f)
  | list_append_map {X : EncodedType} :
      StrictLogSpaceMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  | list_foldl_map {X Y : EncodedType} {step : Y.Carrier × X.Carrier → Y.Carrier}
      (hstep : StrictLogSpaceMap (X := EncodedType.prod Y X) (Y := Y) step)
      (init : Y.Carrier) :
      StrictLogSpaceMap (X := EncodedType.list X) (Y := Y)
        (fun xs => xs.foldl (fun acc x => step (acc, x)) init)
  | registeredPrimitive {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (p : StrictLogSpacePrimitive X Y f) :
      StrictLogSpaceMap (X := X) (Y := Y) f

namespace StrictLogSpaceMap

/--
Every strict project-local log-space certificate also exposes a project-local
costed polynomial-time certificate.  Registered primitives must carry this
costed witness explicitly; there is still no constructor from arbitrary
`CostedMap` to `StrictLogSpaceMap`.
-/
theorem toCostedPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : StrictLogSpaceMap (X := X) (Y := Y) f) :
    CostedPolyTimeMap (X := X) (Y := Y) f := by
  induction h with
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
  | registeredPrimitive p => exact p.costed

end StrictLogSpaceMap

/-- A strict log-space many-one reduction certificate. -/
structure StrictLogReductionCert (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)
  strict_logspace : StrictLogSpaceMap (X := A.Instance) (Y := B.Instance) f

namespace StrictLogReductionCert

/-- Underlying semantic reduction. -/
def toSemantic {A B : EncodedDecisionProblem} (r : StrictLogReductionCert A B) :
    SemanticReduction A B where
  f := r.f
  correct := r.correct

/-- Convert a strict log-space certificate to the project-local costed Karp model. -/
def toKarpReductionM {A B : EncodedDecisionProblem} (r : StrictLogReductionCert A B) :
    KarpReductionM CostedPolyTimeModel A B where
  f := { toFun := r.f, polytime := r.strict_logspace.toCostedPolyTimeMap }
  correct := r.correct

/-- Strict identity reduction. -/
def id (A : EncodedDecisionProblem) : StrictLogReductionCert A A where
  f := fun x => x
  correct := fun _ => Iff.rfl
  strict_logspace := StrictLogSpaceMap.id_map

end StrictLogReductionCert

/-- Strict log-space many-one reducibility. -/
def StrictLogReducible (A B : EncodedDecisionProblem) : Prop :=
  Nonempty (StrictLogReductionCert A B)

namespace StrictLogReducible

/-- Strict log-space reducibility is reflexive. -/
theorem refl (A : EncodedDecisionProblem) : StrictLogReducible A A :=
  ⟨StrictLogReductionCert.id A⟩

/-- Strict log-space reducibility is transitive. -/
theorem trans {A B C : EncodedDecisionProblem}
    (hAB : StrictLogReducible A B) (hBC : StrictLogReducible B C) :
    StrictLogReducible A C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨{
    f := rBC.f ∘ rAB.f
    correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))
    strict_logspace := StrictLogSpaceMap.comp_map rBC.strict_logspace rAB.strict_logspace }⟩

end StrictLogReducible

end ComplexityReduction
