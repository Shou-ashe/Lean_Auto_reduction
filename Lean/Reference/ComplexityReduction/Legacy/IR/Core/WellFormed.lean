/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.IR.Core.Basic

/-!
Lookup and well-formedness lemmas for `UniversalRelIR`.
-/

namespace ComplexityReduction

namespace TupleFits

theorem length_eq {sortSize : SortId → Option Nat} {arity : List SortId}
    {tuple : List ObjId} (h : TupleFits sortSize arity tuple) :
    tuple.length = arity.length :=
  h.1

theorem obj_bound {sortSize : SortId → Option Nat} {arity : List SortId}
    {tuple : List ObjId} (h : TupleFits sortSize arity tuple)
    {k : Nat} {s : SortId} {x : ObjId}
    (hs : arity[k]? = some s) (hx : tuple[k]? = some x) :
    ∃ n, sortSize s = some n ∧ x < n :=
  h.2 k s x hs hx

end TupleFits

namespace UniversalRelIR

@[simp] theorem sortSize?_eq_some_iff (U : UniversalRelIR) (s : SortId) (n : Nat) :
    U.sortSize? s = some n ↔ U.sortSizes[s]? = some n :=
  Iff.rfl

@[simp] theorem relSig?_eq_some_iff (U : UniversalRelIR) (r : RelId) (sig : RelSig) :
    U.relSig? r = some sig ↔ U.relSigs[r]? = some sig :=
  Iff.rfl

@[simp] theorem tuples?_eq_some_iff
    (U : UniversalRelIR) (r : RelId) (ts : List (List ObjId)) :
    U.tuples? r = some ts ↔ U.relTuples[r]? = some ts :=
  Iff.rfl

theorem WellFormed.relTuple_wf {U : UniversalRelIR} (hU : U.WellFormed)
    {r : RelId} {ts : List (List ObjId)} {sig : RelSig} {t : List ObjId}
    (hsig : U.relSig? r = some sig) (htuples : U.tuples? r = some ts)
    (ht : t ∈ ts) :
    U.TupleWF sig t :=
  hU.2 r ts sig hsig htuples t ht

theorem RelHolds_tuple_wf {U : UniversalRelIR} (hU : U.WellFormed)
    {r : RelId} {sig : RelSig} {t : List ObjId}
    (hRel : U.RelHolds r t) (hsig : U.relSig? r = some sig) :
    U.TupleWF sig t := by
  rcases hRel with ⟨ts, htuples, ht⟩
  exact hU.relTuple_wf hsig htuples ht

@[simp] theorem relHoldsBool_eq_true_iff {U : UniversalRelIR}
    {r : RelId} {t : List ObjId} :
    U.RelHoldsBool r t = true ↔ U.RelHolds r t := by
  unfold RelHoldsBool RelHolds
  cases U.tuples? r <;> simp

theorem RelHoldsBool_tuple_wf {U : UniversalRelIR} (hU : U.WellFormed)
    {r : RelId} {sig : RelSig} {t : List ObjId}
    (hRel : U.RelHoldsBool r t = true) (hsig : U.relSig? r = some sig) :
    U.TupleWF sig t :=
  U.RelHolds_tuple_wf hU (relHoldsBool_eq_true_iff.mp hRel) hsig

theorem ObjWF_of_tuple_get? {U : UniversalRelIR} {sig : RelSig} {tuple : List ObjId}
    (hTuple : U.TupleWF sig tuple)
    {k : Nat} {s : SortId} {x : ObjId}
    (hs : sig.arity[k]? = some s) (hx : tuple[k]? = some x) :
    U.ObjWF s x :=
  hTuple.obj_bound hs hx

/-- Object enumeration for a sort, empty when the sort id is absent. -/
def objectsOfSort (U : UniversalRelIR) (s : SortId) : List ObjId :=
  match U.sortSize? s with
  | some n => List.range n
  | none => []

@[simp] theorem mem_objectsOfSort_iff {U : UniversalRelIR} {s : SortId} {x : ObjId} :
    x ∈ U.objectsOfSort s ↔ U.ObjWF s x := by
  unfold objectsOfSort ObjWF
  cases U.sortSize? s <;> simp

theorem objWF_of_mem_objectsOfSort {U : UniversalRelIR} {s : SortId} {x : ObjId}
    (h : x ∈ U.objectsOfSort s) :
    U.ObjWF s x :=
  mem_objectsOfSort_iff.mp h

theorem mem_objectsOfSort_of_objWF {U : UniversalRelIR} {s : SortId} {x : ObjId}
    (h : U.ObjWF s x) :
    x ∈ U.objectsOfSort s :=
  mem_objectsOfSort_iff.mpr h

theorem objectsOfSort_nodup (U : UniversalRelIR) (s : SortId) :
    (U.objectsOfSort s).Nodup := by
  unfold objectsOfSort
  cases U.sortSize? s with
  | none => simp
  | some _ => exact List.nodup_range

end UniversalRelIR

end ComplexityReduction
