/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Certificates.StrictStreamMap
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.StrictLogSpaceTMSound

/-!
Project-local machine semantics for strict log-space certificates.

This module fixes the P6 foundation choice: the repository uses a minimal
project-local machine/log-space semantics for the current CSP streaming maps.
It is intentionally separate from mathlib TM2 semantics.  A theorem in this
module is a checked certificate in this local machine model; interpreting the
same certificate as a direct TM2 polynomial-time map still goes through
`StrictLogSpaceTMSound`.
-/

namespace ComplexityReduction

/--
Strict machine-level log-space maps in the project-local foundation.

The constructors mirror the audited strict log-space DSL, so this is a real
structural proof object rather than a costed-map shortcut.  Registered
primitives are the only leaves; their metadata records the input/output
encoding discipline, workspace bound, and oracle-free construction.
-/
inductive StrictLogSpaceMachineMap :
    {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  | id_map {X : EncodedType} :
      StrictLogSpaceMachineMap (X := X) (Y := X) id
  | comp_map {X Y Z : EncodedType} {f : Y.Carrier → Z.Carrier}
      {g : X.Carrier → Y.Carrier}
      (hf : StrictLogSpaceMachineMap f) (hg : StrictLogSpaceMachineMap g) :
      StrictLogSpaceMachineMap (f ∘ g)
  | const_map {X Y : EncodedType} (y : Y.Carrier) :
      StrictLogSpaceMachineMap (X := X) (Y := Y) (fun _ => y)
  | fst_map {X Y : EncodedType} :
      StrictLogSpaceMachineMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  | snd_map {X Y : EncodedType} :
      StrictLogSpaceMachineMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  | prod_mk_map {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier}
      {g : X.Carrier → Z.Carrier}
      (hf : StrictLogSpaceMachineMap f) (hg : StrictLogSpaceMachineMap g) :
      StrictLogSpaceMachineMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  | inl_map {X Y : EncodedType} :
      StrictLogSpaceMachineMap
        (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  | inr_map {X Y : EncodedType} :
      StrictLogSpaceMachineMap
        (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  | list_map_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (hf : StrictLogSpaceMachineMap f) :
      StrictLogSpaceMachineMap (X := EncodedType.list X) (Y := EncodedType.list Y)
        (fun xs => xs.map f)
  | list_append_map {X : EncodedType} :
      StrictLogSpaceMachineMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  | list_foldl_map {X Y : EncodedType} {step : Y.Carrier × X.Carrier → Y.Carrier}
      (hstep : StrictLogSpaceMachineMap (X := EncodedType.prod Y X) (Y := Y) step)
      (init : Y.Carrier) :
      StrictLogSpaceMachineMap (X := EncodedType.list X) (Y := Y)
        (fun xs => xs.foldl (fun acc x => step (acc, x)) init)
  | registeredPrimitive {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (p : StrictLogSpacePrimitive X Y f) :
      StrictLogSpaceMachineMap (X := X) (Y := Y) f

namespace StrictLogSpaceMachineMap

/-- Forget the project-local machine semantics back to the strict log-space DSL. -/
theorem toStrictLogSpaceMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : StrictLogSpaceMachineMap (X := X) (Y := Y) f) :
    StrictLogSpaceMap (X := X) (Y := Y) f := by
  induction h with
  | id_map => exact StrictLogSpaceMap.id_map
  | comp_map hf hg ihf ihg => exact StrictLogSpaceMap.comp_map ihf ihg
  | const_map y => exact StrictLogSpaceMap.const_map y
  | fst_map => exact StrictLogSpaceMap.fst_map
  | snd_map => exact StrictLogSpaceMap.snd_map
  | prod_mk_map hf hg ihf ihg => exact StrictLogSpaceMap.prod_mk_map ihf ihg
  | inl_map => exact StrictLogSpaceMap.inl_map
  | inr_map => exact StrictLogSpaceMap.inr_map
  | list_map_map hf ih => exact StrictLogSpaceMap.list_map_map ih
  | list_append_map => exact StrictLogSpaceMap.list_append_map
  | list_foldl_map hstep init ih => exact StrictLogSpaceMap.list_foldl_map ih init
  | registeredPrimitive p => exact StrictLogSpaceMap.registeredPrimitive p

/-- Machine certificates still expose the existing project-local costed witness. -/
theorem toCostedPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : StrictLogSpaceMachineMap (X := X) (Y := Y) f) :
    CostedPolyTimeMap (X := X) (Y := Y) f :=
  h.toStrictLogSpaceMap.toCostedPolyTimeMap

/--
Interpret a project-local strict-machine certificate as a TM polynomial-time map
through the explicit strict-logspace soundness boundary.
-/
theorem to_TMPolyTimeMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (hSound : StrictLogSpaceTMSound)
    (h : StrictLogSpaceMachineMap (X := X) (Y := Y) f) :
    TMPolyTimeMap X Y f :=
  h.toStrictLogSpaceMap.to_TMPolyTimeMap hSound

end StrictLogSpaceMachineMap

namespace StrictLogSpaceMap

/-- Interpret a strict log-space certificate in the project-local machine model. -/
theorem toMachineMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : StrictLogSpaceMap (X := X) (Y := Y) f) :
    StrictLogSpaceMachineMap (X := X) (Y := Y) f := by
  induction h with
  | id_map => exact StrictLogSpaceMachineMap.id_map
  | comp_map hf hg ihf ihg => exact StrictLogSpaceMachineMap.comp_map ihf ihg
  | const_map y => exact StrictLogSpaceMachineMap.const_map y
  | fst_map => exact StrictLogSpaceMachineMap.fst_map
  | snd_map => exact StrictLogSpaceMachineMap.snd_map
  | prod_mk_map hf hg ihf ihg => exact StrictLogSpaceMachineMap.prod_mk_map ihf ihg
  | inl_map => exact StrictLogSpaceMachineMap.inl_map
  | inr_map => exact StrictLogSpaceMachineMap.inr_map
  | list_map_map hf ih => exact StrictLogSpaceMachineMap.list_map_map ih
  | list_append_map => exact StrictLogSpaceMachineMap.list_append_map
  | list_foldl_map hstep init ih => exact StrictLogSpaceMachineMap.list_foldl_map ih init
  | registeredPrimitive p => exact StrictLogSpaceMachineMap.registeredPrimitive p

end StrictLogSpaceMap

namespace StrictStreamMap

/-- Interpret a strict streaming certificate in the project-local machine model. -/
theorem toMachineMap {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
    (h : StrictStreamMap (X := X) (Y := Y) f) :
    StrictLogSpaceMachineMap (X := X) (Y := Y) f :=
  h.toStrictLogSpaceMap.toMachineMap

end StrictStreamMap

/-- A many-one reduction certified in the project-local strict machine model. -/
structure StrictLogSpaceMachineReductionCert (A B : EncodedDecisionProblem) where
  f : A.Instance.Carrier → B.Instance.Carrier
  correct : ∀ x, A.isYes x ↔ B.isYes (f x)
  machine_logspace : StrictLogSpaceMachineMap (X := A.Instance) (Y := B.Instance) f

namespace StrictLogSpaceMachineReductionCert

/-- Forget the project-local machine certificate to the strict log-space certificate. -/
def toStrictLogReductionCert {A B : EncodedDecisionProblem}
    (r : StrictLogSpaceMachineReductionCert A B) :
    StrictLogReductionCert A B where
  f := r.f
  correct := r.correct
  strict_logspace := r.machine_logspace.toStrictLogSpaceMap

/-- Forget the project-local machine certificate to the costed Karp model. -/
def toKarpReductionM {A B : EncodedDecisionProblem}
    (r : StrictLogSpaceMachineReductionCert A B) :
    KarpReductionM CostedPolyTimeModel A B where
  f := { toFun := r.f, polytime := r.machine_logspace.toCostedPolyTimeMap }
  correct := r.correct

/--
Interpret a project-local machine reduction as a direct TM-level Karp reduction,
conditional on the explicit strict-logspace soundness witness.
-/
def toTMKarpReduction (hSound : StrictLogSpaceTMSound)
    {A B : EncodedDecisionProblem}
    (r : StrictLogSpaceMachineReductionCert A B) :
    TMKarpReduction A B :=
  r.toStrictLogReductionCert.toTMKarpReduction hSound

/-- Strict identity reduction in the project-local machine model. -/
def id (A : EncodedDecisionProblem) : StrictLogSpaceMachineReductionCert A A where
  f := fun x => x
  correct := fun _ => Iff.rfl
  machine_logspace := StrictLogSpaceMachineMap.id_map

end StrictLogSpaceMachineReductionCert

/-- Project-local strict machine/log-space reducibility. -/
def StrictLogSpaceMachineReducible (A B : EncodedDecisionProblem) : Prop :=
  Nonempty (StrictLogSpaceMachineReductionCert A B)

namespace StrictLogSpaceMachineReducible

/-- Project-local strict machine reducibility is reflexive. -/
theorem refl (A : EncodedDecisionProblem) : StrictLogSpaceMachineReducible A A :=
  ⟨StrictLogSpaceMachineReductionCert.id A⟩

/-- Project-local strict machine reducibility is transitive. -/
theorem trans {A B C : EncodedDecisionProblem}
    (hAB : StrictLogSpaceMachineReducible A B)
    (hBC : StrictLogSpaceMachineReducible B C) :
    StrictLogSpaceMachineReducible A C := by
  rcases hAB with ⟨rAB⟩
  rcases hBC with ⟨rBC⟩
  exact ⟨{
    f := rBC.f ∘ rAB.f
    correct := fun x => Iff.trans (rAB.correct x) (rBC.correct (rAB.f x))
    machine_logspace :=
      StrictLogSpaceMachineMap.comp_map rBC.machine_logspace rAB.machine_logspace }⟩

/--
Project-local strict-machine reducibility implies TM reducibility once the
strict-logspace soundness boundary is supplied.
-/
theorem to_TMPolyReducible (hSound : StrictLogSpaceTMSound)
    {A B : EncodedDecisionProblem} :
    StrictLogSpaceMachineReducible A B → TMPolyReducible A B := by
  intro h
  rcases h with ⟨r⟩
  exact ⟨r.toTMKarpReduction hSound⟩

end StrictLogSpaceMachineReducible

end ComplexityReduction
