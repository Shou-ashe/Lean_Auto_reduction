/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

/-!
Finite witness-list helpers for P15 Karp reductions over raw schemas.
-/

namespace ComplexityReduction
namespace Karp21
namespace FiniteWitness

/-- All lists of length `k` whose entries lie in `{0, ..., n - 1}`. -/
def indexListsOfLength (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 =>
      (List.range n).flatMap fun i =>
        (indexListsOfLength n k).map fun rest => i :: rest

theorem mem_indexListsOfLength_of_bounds {n : Nat} {xs : List Nat}
    (hBounds : ∀ x ∈ xs, x < n) :
    xs ∈ indexListsOfLength n xs.length := by
  induction xs with
  | nil =>
      simp [indexListsOfLength]
  | cons x xs ih =>
      have hx : x < n := hBounds x (by simp)
      have hxs : ∀ y ∈ xs, y < n := by
        intro y hy
        exact hBounds y (by simp [hy])
      simp [indexListsOfLength, hx, ih hxs]

theorem length_eq_of_mem_indexListsOfLength {n k : Nat} {xs : List Nat}
    (h : xs ∈ indexListsOfLength n k) :
    xs.length = k := by
  induction k generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        simpa [indexListsOfLength] using h
      subst xs
      simp
  | succ k ih =>
      simp [indexListsOfLength] at h
      rcases h with ⟨i, _hi, rest, hRest, rfl⟩
      simp [ih hRest]

theorem bounds_of_mem_indexListsOfLength {n k : Nat} {xs : List Nat}
    (h : xs ∈ indexListsOfLength n k) :
    ∀ x ∈ xs, x < n := by
  induction k generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        simpa [indexListsOfLength] using h
      subst xs
      simp
  | succ k ih =>
      simp [indexListsOfLength] at h
      rcases h with ⟨i, hi, rest, hRest, rfl⟩
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact hi
      · exact ih hRest x hx

/-- All bounded index lists of length at most `k`. -/
def indexListsUpTo (n k : Nat) : List (List Nat) :=
  (List.range (k + 1)).flatMap (indexListsOfLength n)

theorem mem_indexListsUpTo_of_bounds {n k : Nat} {xs : List Nat}
    (hLen : xs.length ≤ k) (hBounds : ∀ x ∈ xs, x < n) :
    xs ∈ indexListsUpTo n k := by
  have hLengthMem : xs.length ∈ List.range (k + 1) := by
    simp
    omega
  exact List.mem_flatMap.mpr
    ⟨xs.length, hLengthMem, mem_indexListsOfLength_of_bounds hBounds⟩

theorem length_le_of_mem_indexListsUpTo {n k : Nat} {xs : List Nat}
    (h : xs ∈ indexListsUpTo n k) :
    xs.length ≤ k := by
  rcases List.mem_flatMap.mp h with ⟨len, hLenMem, hXs⟩
  have hEq := length_eq_of_mem_indexListsOfLength hXs
  simp at hLenMem
  omega

theorem bounds_of_mem_indexListsUpTo {n k : Nat} {xs : List Nat}
    (h : xs ∈ indexListsUpTo n k) :
    ∀ x ∈ xs, x < n := by
  rcases List.mem_flatMap.mp h with ⟨len, _hLenMem, hXs⟩
  exact bounds_of_mem_indexListsOfLength hXs

/-- Decode indices into values using `getD`. -/
def valuesFromIndices {α : Type} (values : List α) (fallback : α) (idxs : List Nat) :
    List α :=
  idxs.map fun i => values.getD i fallback

theorem valuesFromIndices_mem_of_bounds {α : Type} {values : List α} {fallback : α}
    {idxs : List Nat} (hBounds : ∀ i ∈ idxs, i < values.length) :
    ∀ x ∈ valuesFromIndices values fallback idxs, x ∈ values := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  rw [List.getD_eq_getElem (l := values) (d := fallback) (hBounds i hi)]
  exact List.getElem_mem _

theorem valuesFromIdxOf_eq {α : Type} [BEq α] [LawfulBEq α] {values selected : List α}
    {fallback : α} (hSelected : ∀ x ∈ selected, x ∈ values) :
    valuesFromIndices values fallback (selected.map values.idxOf) = selected := by
  induction selected with
  | nil =>
      simp [valuesFromIndices]
  | cons x xs ih =>
      have hx : x ∈ values := hSelected x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ values := by
        intro y hy
        exact hSelected y (by simp [hy])
      have hIdx : values.idxOf x < values.length := List.idxOf_lt_length_iff.mpr hx
      have hHead : values.getD (values.idxOf x) fallback = x := by
        rw [List.getD_eq_getElem (l := values) (d := fallback) hIdx]
        exact List.idxOf_get hIdx
      change values.getD (values.idxOf x) fallback ::
          valuesFromIndices values fallback (xs.map values.idxOf) = x :: xs
      rw [hHead, ih hxs]

theorem nodup_length_le_of_mem {α : Type} [DecidableEq α] {xs univList : List α}
    (hNodup : xs.Nodup) (hMem : ∀ x ∈ xs, x ∈ univList) :
    xs.length ≤ univList.length := by
  let sx : Finset α := xs.toFinset
  let su : Finset α := univList.toFinset
  have hSub : sx ⊆ su := by
    intro x hx
    exact List.mem_toFinset.mpr (hMem x (by simpa [sx] using hx))
  have hCard := Finset.card_le_card hSub
  have hUniverseCard : su.card ≤ univList.length := by
    simpa [su] using List.toFinset_card_le (l := univList)
  have hXsCard : sx.card = xs.length := by
    simpa [sx] using List.toFinset_card_of_nodup hNodup
  omega

end FiniteWitness
end Karp21
end ComplexityReduction
