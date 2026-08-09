/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedType

namespace ComplexityReduction

/-- A model of polynomial-time maps between encoded types. -/
structure PolyTimeModel : Type 1 where
  IsPolyTimeMap : {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  id_map : {X : EncodedType} → IsPolyTimeMap (X := X) (Y := X) id
  comp_map :
    {X Y Z : EncodedType} →
    {f : Y.Carrier → Z.Carrier} →
    {g : X.Carrier → Y.Carrier} →
      IsPolyTimeMap f → IsPolyTimeMap g → IsPolyTimeMap (f ∘ g)
  const_map :
    {X Y : EncodedType} →
    (y : Y.Carrier) →
      IsPolyTimeMap (X := X) (Y := Y) (fun _ => y)
  fst_map :
    {X Y : EncodedType} →
      IsPolyTimeMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  snd_map :
    {X Y : EncodedType} →
      IsPolyTimeMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  prod_mk_map :
    {X Y Z : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
    {g : X.Carrier → Z.Carrier} →
      IsPolyTimeMap f → IsPolyTimeMap g →
        IsPolyTimeMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  inl_map :
    {X Y : EncodedType} →
      IsPolyTimeMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  inr_map :
    {X Y : EncodedType} →
      IsPolyTimeMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  list_map_map :
    {X Y : EncodedType} →
    {f : X.Carrier → Y.Carrier} →
      IsPolyTimeMap f →
        IsPolyTimeMap (X := EncodedType.list X) (Y := EncodedType.list Y)
          (fun xs => xs.map f)
  list_append_map :
    {X : EncodedType} →
      IsPolyTimeMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  list_foldl_map :
    {X Y : EncodedType} →
    {step : Y.Carrier × X.Carrier → Y.Carrier} →
      IsPolyTimeMap (X := EncodedType.prod Y X) (Y := Y) step →
      (init : Y.Carrier) →
        IsPolyTimeMap (X := EncodedType.list X) (Y := Y)
          (fun xs => xs.foldl (fun acc x => step (acc, x)) init)

/-- A bundled polynomial-time map between encoded types. -/
structure PolyTimeMap (M : PolyTimeModel) (X Y : EncodedType) where
  toFun : X.Carrier → Y.Carrier
  polytime : M.IsPolyTimeMap toFun

namespace PolyTimeMap

/-- Identity polynomial-time map. -/
def id (M : PolyTimeModel) (X : EncodedType) : PolyTimeMap M X X where
  toFun := fun x => x
  polytime := M.id_map

/-- Composition of polynomial-time maps. -/
def comp {M : PolyTimeModel} {X Y Z : EncodedType}
    (f : PolyTimeMap M Y Z) (g : PolyTimeMap M X Y) : PolyTimeMap M X Z where
  toFun := f.toFun ∘ g.toFun
  polytime := M.comp_map f.polytime g.polytime

/-- Constant polynomial-time map. -/
def const (M : PolyTimeModel) (X Y : EncodedType) (y : Y.Carrier) :
    PolyTimeMap M X Y where
  toFun := fun _ => y
  polytime := M.const_map y

/-- First projection. -/
def fst (M : PolyTimeModel) (X Y : EncodedType) :
    PolyTimeMap M (EncodedType.prod X Y) X where
  toFun := Prod.fst
  polytime := M.fst_map

/-- Second projection. -/
def snd (M : PolyTimeModel) (X Y : EncodedType) :
    PolyTimeMap M (EncodedType.prod X Y) Y where
  toFun := Prod.snd
  polytime := M.snd_map

/-- Pair two polynomial-time maps with the same input. -/
def prod_mk {M : PolyTimeModel} {X Y Z : EncodedType}
    (f : PolyTimeMap M X Y) (g : PolyTimeMap M X Z) :
    PolyTimeMap M X (EncodedType.prod Y Z) where
  toFun := fun x => (f.toFun x, g.toFun x)
  polytime := M.prod_mk_map f.polytime g.polytime

/-- Left sum injection. -/
def inl (M : PolyTimeModel) (X Y : EncodedType) :
    PolyTimeMap M X (EncodedType.sum X Y) where
  toFun := Sum.inl
  polytime := M.inl_map

/-- Right sum injection. -/
def inr (M : PolyTimeModel) (X Y : EncodedType) :
    PolyTimeMap M Y (EncodedType.sum X Y) where
  toFun := Sum.inr
  polytime := M.inr_map

/-- Map a polynomial-time function over lists. -/
def list_map {M : PolyTimeModel} {X Y : EncodedType}
    (f : PolyTimeMap M X Y) :
    PolyTimeMap M (EncodedType.list X) (EncodedType.list Y) where
  toFun := fun xs => xs.map f.toFun
  polytime := M.list_map_map f.polytime

/-- Append two encoded lists. -/
def list_append (M : PolyTimeModel) (X : EncodedType) :
    PolyTimeMap M
      (EncodedType.prod (EncodedType.list X) (EncodedType.list X))
      (EncodedType.list X) where
  toFun := fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2
  polytime := M.list_append_map

/-- Fold a list with a polynomial-time step and fixed initial value. -/
def list_foldl {M : PolyTimeModel} {X Y : EncodedType}
    (step : PolyTimeMap M (EncodedType.prod Y X) Y) (init : Y.Carrier) :
    PolyTimeMap M (EncodedType.list X) Y where
  toFun := fun xs => xs.foldl (fun acc x => step.toFun (acc, x)) init
  polytime := M.list_foldl_map step.polytime init

end PolyTimeMap

/-- The closure-generated map predicate used as the lightweight default model. -/
inductive ClosurePolyTimeMap : {X Y : EncodedType} → (X.Carrier → Y.Carrier) → Prop
  | id_map {X : EncodedType} :
      ClosurePolyTimeMap (X := X) (Y := X) id
  | comp_map {X Y Z : EncodedType} {f : Y.Carrier → Z.Carrier} {g : X.Carrier → Y.Carrier}
      (hf : ClosurePolyTimeMap f) (hg : ClosurePolyTimeMap g) :
      ClosurePolyTimeMap (f ∘ g)
  | const_map {X Y : EncodedType} (y : Y.Carrier) :
      ClosurePolyTimeMap (X := X) (Y := Y) (fun _ => y)
  | fst_map {X Y : EncodedType} :
      ClosurePolyTimeMap (X := EncodedType.prod X Y) (Y := X)
        (@Prod.fst X.Carrier Y.Carrier)
  | snd_map {X Y : EncodedType} :
      ClosurePolyTimeMap (X := EncodedType.prod X Y) (Y := Y)
        (@Prod.snd X.Carrier Y.Carrier)
  | prod_mk_map {X Y Z : EncodedType} {f : X.Carrier → Y.Carrier}
      {g : X.Carrier → Z.Carrier}
      (hf : ClosurePolyTimeMap f) (hg : ClosurePolyTimeMap g) :
      ClosurePolyTimeMap (X := X) (Y := EncodedType.prod Y Z) (fun x => (f x, g x))
  | inl_map {X Y : EncodedType} :
      ClosurePolyTimeMap (X := X) (Y := EncodedType.sum X Y) (@Sum.inl X.Carrier Y.Carrier)
  | inr_map {X Y : EncodedType} :
      ClosurePolyTimeMap (X := Y) (Y := EncodedType.sum X Y) (@Sum.inr X.Carrier Y.Carrier)
  | list_map_map {X Y : EncodedType} {f : X.Carrier → Y.Carrier}
      (hf : ClosurePolyTimeMap f) :
      ClosurePolyTimeMap (X := EncodedType.list X) (Y := EncodedType.list Y)
        (fun xs => xs.map f)
  | list_append_map {X : EncodedType} :
      ClosurePolyTimeMap
        (X := EncodedType.prod (EncodedType.list X) (EncodedType.list X))
        (Y := EncodedType.list X)
        (fun p : List X.Carrier × List X.Carrier => p.1 ++ p.2)
  | list_foldl_map {X Y : EncodedType} {step : Y.Carrier × X.Carrier → Y.Carrier}
      (hstep : ClosurePolyTimeMap (X := EncodedType.prod Y X) (Y := Y) step)
      (init : Y.Carrier) :
      ClosurePolyTimeMap (X := EncodedType.list X) (Y := Y)
        (fun xs => xs.foldl (fun acc x => step (acc, x)) init)

/-- The lightweight default model generated by generic map closures. -/
def ClosurePolyTimeModel : PolyTimeModel where
  IsPolyTimeMap := ClosurePolyTimeMap
  id_map := ClosurePolyTimeMap.id_map
  comp_map := ClosurePolyTimeMap.comp_map
  const_map := ClosurePolyTimeMap.const_map
  fst_map := ClosurePolyTimeMap.fst_map
  snd_map := ClosurePolyTimeMap.snd_map
  prod_mk_map := ClosurePolyTimeMap.prod_mk_map
  inl_map := ClosurePolyTimeMap.inl_map
  inr_map := ClosurePolyTimeMap.inr_map
  list_map_map := ClosurePolyTimeMap.list_map_map
  list_append_map := ClosurePolyTimeMap.list_append_map
  list_foldl_map := ClosurePolyTimeMap.list_foldl_map

end ComplexityReduction
