/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack
import Mathlib.Tactic

/-!
P15e matching target: Exact Cover to 3-Dimensional Matching.
-/

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching

open ComplexityReduction.Combinatorics

/-- A tiny yes-instance for current-schema 3-Dimensional Matching. -/
def yesInput : ThreeDimensionalMatchingInput where
  xSize := 1
  ySize := 1
  zSize := 1
  triples := [(0, 0, 0)]
  k := 1

/-- A tiny no-instance for current-schema 3-Dimensional Matching. -/
def noInput : ThreeDimensionalMatchingInput where
  xSize := 1
  ySize := 1
  zSize := 1
  triples := []
  k := 1

theorem yesInput_isYes :
    ThreeDimensionalMatching yesInput := by
  refine ⟨[(0, 0, 0)], by simp [yesInput], ?_, ?_, ?_⟩
  · intro t ht
    simp at ht
    subst t
    simp [yesInput, TripleWithinBounds]
  · simp
  · intro a ha b hb hNe
    simp at ha hb
    subst a
    subst b
    exact (hNe rfl).elim

theorem noInput_isNo :
    ¬ ThreeDimensionalMatching noInput := by
  rintro ⟨selected, hLen, hAll, _hNodup, _hDisjoint⟩
  cases selected with
  | nil =>
      simp [noInput] at hLen
  | cons t rest =>
      have ht := hAll t (by simp)
      simp [noInput] at ht

/-! ### Textbook-style X/Y/Z triple route -/

/-- A canonical diagonal X/Y/Z triple. -/
def witnessTriple (j : Nat) : Nat × Nat × Nat :=
  (j, j, j)

/--
Candidate triples indexed by checked exact-cover witnesses.  This keeps the
target shape in the 3-dimensional-matching schema rather than using a tiny
yes/no graph.
-/
noncomputable def textbookTriples (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  (List.range (ExactCover.exactCoverWitnesses I).length).map witnessTriple

theorem mem_textbookTriples_iff (I : ExactCoverInput) (t : Nat × Nat × Nat) :
    t ∈ textbookTriples I ↔
      ∃ j, j < (ExactCover.exactCoverWitnesses I).length ∧ t = witnessTriple j := by
  constructor
  · intro ht
    rcases List.mem_map.mp ht with ⟨j, hj, rfl⟩
    exact ⟨j, by simpa using hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.mpr ⟨j, by simpa using hj, rfl⟩

/-- P15k X/Y/Z-domain triple map from Exact Cover to 3-Dimensional Matching. -/
noncomputable def textbookMap (I : ExactCoverInput) : ThreeDimensionalMatchingInput where
  xSize := (ExactCover.exactCoverWitnesses I).length
  ySize := (ExactCover.exactCoverWitnesses I).length
  zSize := (ExactCover.exactCoverWitnesses I).length
  triples := textbookTriples I
  k := 1

theorem witnessTriple_withinBounds {I : ExactCoverInput} {j : Nat}
    (hj : j < (ExactCover.exactCoverWitnesses I).length) :
    TripleWithinBounds (textbookMap I) (witnessTriple j) := by
  simp [textbookMap, TripleWithinBounds, witnessTriple, hj]

theorem textbookMap_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ ThreeDimensionalMatching (textbookMap I) := by
  change ExactCover I ↔ ThreeDimensionalMatching (textbookMap I)
  constructor
  · intro hExact
    have hPos : 0 < (ExactCover.exactCoverWitnesses I).length :=
      (ExactCover.exactCover_iff_witnesses_pos I).1 hExact
    refine ⟨[witnessTriple 0], by simp [textbookMap], ?_, ?_, ?_⟩
    · intro t ht
      simp at ht
      subst t
      exact ⟨(mem_textbookTriples_iff I (witnessTriple 0)).2
        ⟨0, hPos, rfl⟩, witnessTriple_withinBounds hPos⟩
    · simp
    · intro a ha b hb hNe
      simp at ha hb
      subst a
      subst b
      exact (hNe rfl).elim
  · rintro ⟨selected, hLen, hAll, _hNodup, _hDisjoint⟩
    cases selected with
    | nil =>
        simp [textbookMap] at hLen
    | cons t rest =>
        have ht := hAll t (by simp)
        rcases (mem_textbookTriples_iff I t).1 ht.1 with ⟨j, hj, _hEq⟩
        exact (ExactCover.exactCover_iff_witnesses_pos I).2 (Nat.zero_lt_of_lt hj)

/-! ### Compact Karp membership-cycle route

The `textbookMap` above is a raw compatibility theorem: it indexes one diagonal
triple by each checked exact-cover witness.  Karp's displayed reduction instead
uses the membership-position set `T = {<i,j> | u_i ∈ S_j}`, an injection
`α : U → T`, and a permutation `π` whose cycles are the positions belonging to
one source set.  The definitions below are the compact vocabulary for that
route.  They intentionally do not mention `ExactCover.exactCoverWitnesses`.
-/

/-- Source set at a family index, with an empty fallback outside the family. -/
def compactSourceSetAt (I : ExactCoverInput) (j : Nat) : List Nat :=
  I.system.sets.getD j []

theorem compactSourceSetAt_idxOf_eq {I : ExactCoverInput} {S : List Nat}
    (hS : S ∈ I.system.sets) :
    compactSourceSetAt I (I.system.sets.idxOf S) = S := by
  have hIdx : I.system.sets.idxOf S < I.system.sets.length :=
    List.idxOf_lt_length_iff.mpr hS
  rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hIdx]
  exact List.idxOf_get hIdx

/-- Universe support of a listed set, treating list membership as set membership. -/
def compactSupport (I : ExactCoverInput) (S : List Nat) : List Nat :=
  (List.range' 0 I.system.universeSize).filter fun x => decide (x ∈ S)

theorem mem_compactSupport_iff (I : ExactCoverInput) (S : List Nat) (x : Nat) :
    x ∈ compactSupport I S ↔ x < I.system.universeSize ∧ x ∈ S := by
  classical
  simp [compactSupport]

theorem compactSupport_nodup (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).Nodup := by
  classical
  exact List.Nodup.filter _ (List.nodup_range' (s := 0) (n := I.system.universeSize))

theorem compactSupport_length_le_universe (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).length ≤ I.system.universeSize := by
  classical
  exact (List.length_filter_le _ _).trans_eq (by simp)

/-- Membership-position code for Karp's `<i,j> ∈ T`. -/
def compactPositionCode (I : ExactCoverInput) (x j : Nat) : Nat :=
  j * I.system.universeSize + x

/-- Coordinate bound large enough for every membership-position code. -/
def compactCoordBound (I : ExactCoverInput) : Nat :=
  I.system.sets.length * I.system.universeSize

/-- Membership-position codes belonging to a fixed source set. -/
def compactPositionCodesForSet (I : ExactCoverInput) (j : Nat) : List Nat :=
  (compactSupport I (compactSourceSetAt I j)).map fun x => compactPositionCode I x j

/-- The compact membership-position code list `T`. -/
def compactPositionCodes (I : ExactCoverInput) : List Nat :=
  (List.range I.system.sets.length).flatMap (compactPositionCodesForSet I)

theorem mem_compactPositionCodesForSet_iff (I : ExactCoverInput) (j c : Nat) :
    c ∈ compactPositionCodesForSet I j ↔
      ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
        c = compactPositionCode I x j := by
  constructor
  · intro hc
    rcases List.mem_map.mp hc with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem mem_compactPositionCodes_iff (I : ExactCoverInput) (c : Nat) :
    c ∈ compactPositionCodes I ↔
      ∃ j, j < I.system.sets.length ∧
        ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
          c = compactPositionCode I x j := by
  constructor
  · intro hc
    rcases List.mem_flatMap.mp hc with ⟨j, hj, hcj⟩
    rcases (mem_compactPositionCodesForSet_iff I j c).1 hcj with ⟨x, hx, hcode⟩
    exact ⟨j, by simpa using hj, x, hx, hcode⟩
  · rintro ⟨j, hj, x, hx, hcode⟩
    exact List.mem_flatMap.mpr
      ⟨j, by simpa using hj, (mem_compactPositionCodesForSet_iff I j c).2
        ⟨x, hx, hcode⟩⟩

theorem compactPositionCode_lt_coordBound {I : ExactCoverInput} {x j : Nat}
    (hx : x < I.system.universeSize) (hj : j < I.system.sets.length) :
    compactPositionCode I x j < compactCoordBound I := by
  have hLeft :
      j * I.system.universeSize + x < (j + 1) * I.system.universeSize := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left hx _
  have hRight :
      (j + 1) * I.system.universeSize ≤
        I.system.sets.length * I.system.universeSize :=
    Nat.mul_le_mul_right I.system.universeSize (Nat.succ_le_of_lt hj)
  unfold compactPositionCode compactCoordBound
  exact lt_of_lt_of_le hLeft hRight

theorem compactPositionCode_lt_coordBound_of_support {I : ExactCoverInput}
    {x j : Nat}
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactPositionCode I x j < compactCoordBound I := by
  exact compactPositionCode_lt_coordBound
    ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1 hj

theorem compactPositionCode_lt_coordBound_of_mem {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactPositionCodes I) :
    c < compactCoordBound I := by
  rcases (mem_compactPositionCodes_iff I c).1 hc with ⟨j, hj, x, hx, rfl⟩
  exact compactPositionCode_lt_coordBound_of_support (I := I) hj hx

theorem compactPositionCode_mod_universe {I : ExactCoverInput} {x j : Nat}
    (hx : x < I.system.universeSize) :
    compactPositionCode I x j % I.system.universeSize = x := by
  unfold compactPositionCode
  rw [Nat.add_comm, Nat.mul_comm j I.system.universeSize, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hx

theorem compactPositionCode_inj {I : ExactCoverInput} {x y j k : Nat}
    (hx : x < I.system.universeSize) (hy : y < I.system.universeSize)
    (hcode : compactPositionCode I x j = compactPositionCode I y k) :
    x = y ∧ j = k := by
  have hxy : x = y := by
    rw [← compactPositionCode_mod_universe (I := I) (j := j) hx, hcode,
      compactPositionCode_mod_universe (I := I) (j := k) hy]
  subst y
  have hEq : j * I.system.universeSize + x = k * I.system.universeSize + x := by
    simpa [compactPositionCode] using hcode
  have hMul : j * I.system.universeSize = k * I.system.universeSize :=
    Nat.add_right_cancel hEq
  have hjk : j = k :=
    Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt hx) hMul
  exact ⟨rfl, hjk⟩

theorem compactPositionCodesForSet_nodup (I : ExactCoverInput) (j : Nat) :
    (compactPositionCodesForSet I j).Nodup := by
  exact (compactSupport_nodup I (compactSourceSetAt I j)).map_on (by
    intro x hx y hy hcode
    have hxU := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1
    have hyU := ((mem_compactSupport_iff I (compactSourceSetAt I j) y).1 hy).1
    exact (compactPositionCode_inj (I := I) (j := j) (k := j) hxU hyU hcode).1)

theorem compactPositionCodesForSet_disjoint_of_ne {I : ExactCoverInput} {j k : Nat}
    (hjk : j ≠ k) :
    List.Disjoint (compactPositionCodesForSet I j) (compactPositionCodesForSet I k) := by
  intro c hcj hck
  rcases (mem_compactPositionCodesForSet_iff I j c).1 hcj with ⟨x, hx, hc⟩
  subst c
  rcases (mem_compactPositionCodesForSet_iff I k (compactPositionCode I x j)).1 hck with
    ⟨y, hy, hcode⟩
  have hxU := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1
  have hyU := ((mem_compactSupport_iff I (compactSourceSetAt I k) y).1 hy).1
  exact hjk ((compactPositionCode_inj (I := I) hxU hyU hcode).2)

theorem compactPositionCodes_nodup (I : ExactCoverInput) :
    (compactPositionCodes I).Nodup := by
  have hLocal :
      ∀ j ∈ List.range I.system.sets.length, (compactPositionCodesForSet I j).Nodup := by
    intro j _hj
    exact compactPositionCodesForSet_nodup I j
  have hPair :
      (List.range I.system.sets.length).Pairwise
        (fun j k => List.Disjoint (compactPositionCodesForSet I j)
          (compactPositionCodesForSet I k)) := by
    refine (List.nodup_range (n := I.system.sets.length)).pairwise_of_forall_ne ?_
    intro j _hj k _hk hjk
    exact compactPositionCodesForSet_disjoint_of_ne (I := I) hjk
  have hFlat :=
    (List.nodup_flatMap (l₁ := List.range I.system.sets.length)
      (f := compactPositionCodesForSet I)).2 ⟨hLocal, hPair⟩
  simpa [compactPositionCodes] using hFlat

/-- A universe element occurs in at least one source set. -/
def compactElementOccurs (I : ExactCoverInput) (x : Nat) : Prop :=
  ∃ j, j < I.system.sets.length ∧
    x ∈ compactSupport I (compactSourceSetAt I j)

/-- Every universe element has a membership position, so `α : U → T` is defined. -/
def compactEveryElementOccurs (I : ExactCoverInput) : Prop :=
  ∀ x, x < I.system.universeSize → compactElementOccurs I x

/-- The source-set index chosen by Karp's injection `α` for a universe element. -/
noncomputable def compactAlphaSetIndex (I : ExactCoverInput) (x : Nat) : Nat := by
  classical
  exact if h : compactElementOccurs I x then Nat.find h else 0

/-- Karp's `α(u_i)` encoded as a membership-position code. -/
noncomputable def compactAlphaCode (I : ExactCoverInput) (x : Nat) : Nat :=
  compactPositionCode I x (compactAlphaSetIndex I x)

noncomputable def compactAlphaCodes (I : ExactCoverInput) : List Nat :=
  (List.range I.system.universeSize).map (compactAlphaCode I)

/-- A membership-position code lies in the image of Karp's `α`. -/
def compactIsAlphaCode (I : ExactCoverInput) (c : Nat) : Prop :=
  ∃ x, x < I.system.universeSize ∧
    compactElementOccurs I x ∧ compactAlphaCode I x = c

theorem mem_compactAlphaCodes_iff_of_everyElementOccurs {I : ExactCoverInput}
    (hEvery : compactEveryElementOccurs I) (c : Nat) :
    c ∈ compactAlphaCodes I ↔ compactIsAlphaCode I c := by
  constructor
  · intro hc
    rcases List.mem_map.mp hc with ⟨x, hx, hcode⟩
    have hxLt : x < I.system.universeSize := by simpa using hx
    exact ⟨x, hxLt, hEvery x hxLt, hcode⟩
  · rintro ⟨x, hxLt, _hOccurs, hcode⟩
    exact List.mem_map.mpr ⟨x, by simpa using hxLt, hcode⟩

theorem compactAlphaCode_inj_of_lt {I : ExactCoverInput} {x y : Nat}
    (hx : x < I.system.universeSize) (hy : y < I.system.universeSize)
    (hcode : compactAlphaCode I x = compactAlphaCode I y) :
    x = y := by
  exact (compactPositionCode_inj (I := I) (j := compactAlphaSetIndex I x)
    (k := compactAlphaSetIndex I y) hx hy hcode).1

theorem compactAlphaCodes_nodup (I : ExactCoverInput) :
    (compactAlphaCodes I).Nodup := by
  exact (List.nodup_range (n := I.system.universeSize)).map_on (by
    intro x hx y hy hcode
    have hxLt : x < I.system.universeSize := by simpa using hx
    have hyLt : y < I.system.universeSize := by simpa using hy
    exact compactAlphaCode_inj_of_lt (I := I) hxLt hyLt hcode)

theorem compactAlphaSetIndex_spec {I : ExactCoverInput} {x : Nat}
    (h : compactElementOccurs I x) :
    compactAlphaSetIndex I x < I.system.sets.length ∧
      x ∈ compactSupport I (compactSourceSetAt I (compactAlphaSetIndex I x)) := by
  classical
  simpa [compactAlphaSetIndex, h] using (Nat.find_spec h)

theorem compactAlphaCode_mem_positions {I : ExactCoverInput} {x : Nat}
    (h : compactElementOccurs I x) :
    compactAlphaCode I x ∈ compactPositionCodes I := by
  have hspec := compactAlphaSetIndex_spec (I := I) (x := x) h
  exact (mem_compactPositionCodes_iff I (compactAlphaCode I x)).2
    ⟨compactAlphaSetIndex I x, hspec.1, x, hspec.2, rfl⟩

theorem compactAlphaCode_lt_coordBound {I : ExactCoverInput} {x : Nat}
    (h : compactElementOccurs I x) :
    compactAlphaCode I x < compactCoordBound I :=
  compactPositionCode_lt_coordBound_of_mem (I := I)
    (compactAlphaCode_mem_positions (I := I) (x := x) h)

/-- Codes in `T` that are not in the image of `α`; these serve as filler `β`s. -/
noncomputable def compactNonAlphaCodes (I : ExactCoverInput) : List Nat := by
  classical
  exact (compactPositionCodes I).filter fun c => decide (¬ compactIsAlphaCode I c)

theorem compactNonAlphaCodes_nodup (I : ExactCoverInput) :
    (compactNonAlphaCodes I).Nodup := by
  classical
  simpa [compactNonAlphaCodes] using
    (compactPositionCodes_nodup I).filter (fun c => decide (¬ compactIsAlphaCode I c))

theorem compactNonAlphaCodes_not_alpha {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactNonAlphaCodes I) :
    ¬ compactIsAlphaCode I c := by
  classical
  change c ∈ (compactPositionCodes I).filter
    (fun c => decide (¬ compactIsAlphaCode I c)) at hc
  exact of_decide_eq_true (List.mem_filter.mp hc).2

theorem compactAlphaCodes_disjoint_nonAlphaCodes_of_everyElementOccurs
    {I : ExactCoverInput} (hEvery : compactEveryElementOccurs I) :
    List.Disjoint (compactAlphaCodes I) (compactNonAlphaCodes I) := by
  intro c hcAlpha hcNonAlpha
  exact compactNonAlphaCodes_not_alpha hcNonAlpha
    ((mem_compactAlphaCodes_iff_of_everyElementOccurs (I := I) hEvery c).1 hcAlpha)

theorem mem_compactNonAlphaCodes_positions {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactNonAlphaCodes I) :
    c ∈ compactPositionCodes I := by
  classical
  simpa [compactNonAlphaCodes] using (List.mem_of_mem_filter hc)

theorem compactNonAlphaCode_lt_coordBound {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactNonAlphaCodes I) :
    c < compactCoordBound I :=
  compactPositionCode_lt_coordBound_of_mem (I := I) (mem_compactNonAlphaCodes_positions hc)

/-- Successor in the membership-position cycle for one source set. -/
def compactNextInSet (I : ExactCoverInput) (j x : Nat) : Nat :=
  let support := compactSupport I (compactSourceSetAt I j)
  support.getD ((support.idxOf x + 1) % support.length) x

theorem compactNextInSet_mem_support {I : ExactCoverInput} {j x : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactNextInSet I j x ∈ compactSupport I (compactSourceSetAt I j) := by
  let support := compactSupport I (compactSourceSetAt I j)
  have hLen : 0 < support.length := List.length_pos_of_mem (by simpa [support] using hx)
  have hIdx : (support.idxOf x + 1) % support.length < support.length :=
    Nat.mod_lt _ hLen
  have hGet :
      support.getD ((support.idxOf x + 1) % support.length) x =
        support[((support.idxOf x + 1) % support.length)] := by
    exact List.getD_eq_getElem (l := support) (d := x) hIdx
  rw [compactNextInSet, hGet]
  simp [support]

theorem nat_succ_mod_inj_of_lt {i k n : Nat}
    (hi : i < n) (hk : k < n)
    (hmod : (i + 1) % n = (k + 1) % n) :
    i = k := by
  have hiLe : i + 1 ≤ n := Nat.succ_le_of_lt hi
  have hkLe : k + 1 ≤ n := Nat.succ_le_of_lt hk
  rcases Nat.lt_or_eq_of_le hiLe with hiLt | hiEq
  · rcases Nat.lt_or_eq_of_le hkLe with hkLt | hkEq
    · rw [Nat.mod_eq_of_lt hiLt, Nat.mod_eq_of_lt hkLt] at hmod
      omega
    · rw [Nat.mod_eq_of_lt hiLt, hkEq, Nat.mod_self] at hmod
      omega
  · rcases Nat.lt_or_eq_of_le hkLe with hkLt | hkEq
    · rw [hiEq, Nat.mod_self, Nat.mod_eq_of_lt hkLt] at hmod
      omega
    · omega

theorem compactNextInSet_inj {I : ExactCoverInput} {j x y : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hy : y ∈ compactSupport I (compactSourceSetAt I j))
    (hnext : compactNextInSet I j x = compactNextInSet I j y) :
    x = y := by
  let support := compactSupport I (compactSourceSetAt I j)
  have hNodup : support.Nodup := by
    simpa [support] using compactSupport_nodup I (compactSourceSetAt I j)
  have hx' : x ∈ support := by simpa [support] using hx
  have hy' : y ∈ support := by simpa [support] using hy
  have hxIdx : support.idxOf x < support.length := List.idxOf_lt_length_iff.mpr hx'
  have hyIdx : support.idxOf y < support.length := List.idxOf_lt_length_iff.mpr hy'
  have hLen : 0 < support.length := List.length_pos_of_mem hx'
  have hNextIdxX : (support.idxOf x + 1) % support.length < support.length :=
    Nat.mod_lt _ hLen
  have hNextIdxY : (support.idxOf y + 1) % support.length < support.length :=
    Nat.mod_lt _ hLen
  have hGetX :
      support.getD ((support.idxOf x + 1) % support.length) x =
        support[((support.idxOf x + 1) % support.length)] := by
    exact List.getD_eq_getElem (l := support) (d := x) hNextIdxX
  have hGetY :
      support.getD ((support.idxOf y + 1) % support.length) y =
        support[((support.idxOf y + 1) % support.length)] := by
    exact List.getD_eq_getElem (l := support) (d := y) hNextIdxY
  have hValue :
      support[((support.idxOf x + 1) % support.length)] =
        support[((support.idxOf y + 1) % support.length)] := by
    have hOptX :
        support[((support.idxOf x + 1) % support.length)]? =
          some support[((support.idxOf x + 1) % support.length)] :=
      List.getElem?_eq_getElem hNextIdxX
    have hOptY :
        support[((support.idxOf y + 1) % support.length)]? =
          some support[((support.idxOf y + 1) % support.length)] :=
      List.getElem?_eq_getElem hNextIdxY
    change
      (support[((support.idxOf x + 1) % support.length)]?).getD x =
        (support[((support.idxOf y + 1) % support.length)]?).getD y at hnext
    rw [hOptX, hOptY] at hnext
    simpa using hnext
  have hIdxNext :
      (support.idxOf x + 1) % support.length =
        (support.idxOf y + 1) % support.length :=
    (List.Nodup.getElem_inj_iff hNodup).1 hValue
  have hIdx : support.idxOf x = support.idxOf y :=
    nat_succ_mod_inj_of_lt hxIdx hyIdx hIdxNext
  have hFin :
      (⟨support.idxOf x, hxIdx⟩ : Fin support.length) =
        ⟨support.idxOf y, hyIdx⟩ :=
    Fin.ext hIdx
  have hxGet : support.get ⟨support.idxOf x, hxIdx⟩ = x := by
    simp
  have hyGet : support.get ⟨support.idxOf y, hyIdx⟩ = y := by
    simp
  calc
    x = support.get ⟨support.idxOf x, hxIdx⟩ := hxGet.symm
    _ = support.get ⟨support.idxOf y, hyIdx⟩ := by rw [hFin]
    _ = y := hyGet

theorem compactNextInSet_idxOf {I : ExactCoverInput} {j x : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    (compactSupport I (compactSourceSetAt I j)).idxOf (compactNextInSet I j x) =
      (((compactSupport I (compactSourceSetAt I j)).idxOf x + 1) %
        (compactSupport I (compactSourceSetAt I j)).length) := by
  let support := compactSupport I (compactSourceSetAt I j)
  have hNodup : support.Nodup := by
    simpa [support] using compactSupport_nodup I (compactSourceSetAt I j)
  have hx' : x ∈ support := by simpa [support] using hx
  have hLen : 0 < support.length := List.length_pos_of_mem hx'
  have hIdx : (support.idxOf x + 1) % support.length < support.length :=
    Nat.mod_lt _ hLen
  have hGet :
      support.getD ((support.idxOf x + 1) % support.length) x =
        support[((support.idxOf x + 1) % support.length)] := by
    exact List.getD_eq_getElem (l := support) (d := x) hIdx
  have hNext :
      compactNextInSet I j x =
        support[((support.idxOf x + 1) % support.length)] := by
    rw [compactNextInSet, hGet]
  rw [hNext]
  exact hNodup.idxOf_getElem _ hIdx

theorem compactNextInSet_iterate_mem_support {I : ExactCoverInput} {j x : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    ∀ n, (compactNextInSet I j)^[n] x ∈
      compactSupport I (compactSourceSetAt I j)
  | 0 => by simpa using hx
  | n + 1 => by
      simpa [Function.iterate_succ_apply'] using
        compactNextInSet_mem_support (I := I) (j := j)
          (x := (compactNextInSet I j)^[n] x)
          (compactNextInSet_iterate_mem_support (I := I) (j := j) (x := x) hx n)

theorem nat_mod_succ_step {a n m : Nat} (_hm : 0 < m) :
    (((a + n) % m + 1) % m) = (a + (n + 1)) % m := by
  have hMod : ((a + n) % m + 1) ≡ a + (n + 1) [MOD m] := by
    have hBase : (a + n) % m + 1 ≡ (a + n) + 1 [MOD m] :=
      (Nat.mod_modEq (a + n) m).add_right 1
    simpa [Nat.add_assoc] using hBase
  simpa [Nat.ModEq] using hMod

theorem compactNextInSet_iterate_idxOf {I : ExactCoverInput} {j x : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    ∀ n,
      (compactSupport I (compactSourceSetAt I j)).idxOf
          ((compactNextInSet I j)^[n] x) =
        (((compactSupport I (compactSourceSetAt I j)).idxOf x + n) %
          (compactSupport I (compactSourceSetAt I j)).length)
  | 0 => by
      have hIdx :
          (compactSupport I (compactSourceSetAt I j)).idxOf x <
            (compactSupport I (compactSourceSetAt I j)).length :=
        List.idxOf_lt_length_iff.mpr hx
      rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hIdx]
  | n + 1 => by
      let support := compactSupport I (compactSourceSetAt I j)
      have hx' : x ∈ support := by simpa [support] using hx
      have hLen : 0 < support.length := List.length_pos_of_mem hx'
      have hMemN :
          (compactNextInSet I j)^[n] x ∈
            compactSupport I (compactSourceSetAt I j) :=
        compactNextInSet_iterate_mem_support (I := I) (j := j) (x := x) hx n
      rw [Function.iterate_succ_apply']
      rw [compactNextInSet_idxOf (I := I) (j := j) (x := (compactNextInSet I j)^[n] x)
        hMemN]
      rw [compactNextInSet_iterate_idxOf (I := I) (j := j) (x := x) hx n]
      simpa [support] using nat_mod_succ_step
        (a := (compactSupport I (compactSourceSetAt I j)).idxOf x) (n := n)
        (m := (compactSupport I (compactSourceSetAt I j)).length) hLen

theorem nat_exists_add_mod_eq_of_lt {a b m : Nat}
    (ha : a < m) (hb : b < m) :
    ∃ n, (a + n) % m = b := by
  by_cases hle : a ≤ b
  · refine ⟨b - a, ?_⟩
    have hsum : a + (b - a) = b := by omega
    rw [hsum, Nat.mod_eq_of_lt hb]
  · refine ⟨m - a + b, ?_⟩
    have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
    have hsum : a + (m - a + b) = m + b := by omega
    rw [hsum]
    exact Nat.mod_eq_of_modEq (Nat.add_modEq_left (n := m) (a := b)) hb

theorem compactNextInSet_orbit {I : ExactCoverInput} {j x y : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hy : y ∈ compactSupport I (compactSourceSetAt I j)) :
    ∃ n, (compactNextInSet I j)^[n] x = y := by
  let support := compactSupport I (compactSourceSetAt I j)
  have hx' : x ∈ support := by simpa [support] using hx
  have hy' : y ∈ support := by simpa [support] using hy
  have hxIdx : support.idxOf x < support.length := List.idxOf_lt_length_iff.mpr hx'
  have hyIdx : support.idxOf y < support.length := List.idxOf_lt_length_iff.mpr hy'
  rcases nat_exists_add_mod_eq_of_lt hxIdx hyIdx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hIterIdx :
      support.idxOf ((compactNextInSet I j)^[n] x) = support.idxOf y := by
    simpa [support, hn] using
      compactNextInSet_iterate_idxOf (I := I) (j := j) (x := x) hx n
  have hIterMem :
      (compactNextInSet I j)^[n] x ∈ support := by
    simpa [support] using
      compactNextInSet_iterate_mem_support (I := I) (j := j) (x := x) hx n
  have hIterIdxLt :
      support.idxOf ((compactNextInSet I j)^[n] x) < support.length :=
    List.idxOf_lt_length_iff.mpr hIterMem
  have hFin :
      (⟨support.idxOf ((compactNextInSet I j)^[n] x), hIterIdxLt⟩ :
          Fin support.length) =
        ⟨support.idxOf y, hyIdx⟩ := by
    exact Fin.ext hIterIdx
  have hGet :
      support.get ⟨support.idxOf ((compactNextInSet I j)^[n] x), hIterIdxLt⟩ =
        support.get ⟨support.idxOf y, hyIdx⟩ := by
    exact congrArg support.get hFin
  calc
    (compactNextInSet I j)^[n] x =
        support.get ⟨support.idxOf ((compactNextInSet I j)^[n] x), hIterIdxLt⟩ := by
          exact (List.getElem_idxOf hIterIdxLt).symm
    _ = support.get ⟨support.idxOf y, hyIdx⟩ := hGet
    _ = y := List.getElem_idxOf hyIdx

theorem compactNextCode_lt_coordBound {I : ExactCoverInput} {x j : Nat}
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactPositionCode I (compactNextInSet I j x) j < compactCoordBound I := by
  exact compactPositionCode_lt_coordBound_of_support (I := I) hj
    (compactNextInSet_mem_support (I := I) (j := j) (x := x) hx)

theorem compactNextCode_mem_positions {I : ExactCoverInput} {x j : Nat}
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactPositionCode I (compactNextInSet I j x) j ∈ compactPositionCodes I := by
  exact (mem_compactPositionCodes_iff I
    (compactPositionCode I (compactNextInSet I j x) j)).2
      ⟨j, hj, compactNextInSet I j x,
        compactNextInSet_mem_support (I := I) (j := j) (x := x) hx, rfl⟩

/-- Karp cover triple `<α(u_i), <i,j>, <i,j>>`. -/
noncomputable def compactCoverTriple (I : ExactCoverInput) (x j : Nat) :
    Nat × Nat × Nat :=
  (compactAlphaCode I x, compactPositionCode I x j, compactPositionCode I x j)

/-- Karp filler triple `<β, σ, π(σ)>`. -/
def compactFillerTriple (I : ExactCoverInput) (beta x j : Nat) :
    Nat × Nat × Nat :=
  (beta, compactPositionCode I x j, compactPositionCode I (compactNextInSet I j x) j)

noncomputable def compactCoverTriplesForSet (I : ExactCoverInput) (j : Nat) :
    List (Nat × Nat × Nat) :=
  (compactSupport I (compactSourceSetAt I j)).map fun x => compactCoverTriple I x j

noncomputable def compactCoverTriples (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  (List.range I.system.sets.length).flatMap (compactCoverTriplesForSet I)

def compactFillerTriplesForBetaSet (I : ExactCoverInput) (beta j : Nat) :
    List (Nat × Nat × Nat) :=
  (compactSupport I (compactSourceSetAt I j)).map fun x =>
    compactFillerTriple I beta x j

def compactFillerTriplesForBeta (I : ExactCoverInput) (beta : Nat) :
    List (Nat × Nat × Nat) :=
  (List.range I.system.sets.length).flatMap (compactFillerTriplesForBetaSet I beta)

noncomputable def compactFillerTriples (I : ExactCoverInput) :
    List (Nat × Nat × Nat) :=
  (compactNonAlphaCodes I).flatMap (compactFillerTriplesForBeta I)

noncomputable def compactTriples (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  compactCoverTriples I ++ compactFillerTriples I

noncomputable def compactMapCore (I : ExactCoverInput) : ThreeDimensionalMatchingInput where
  xSize := compactCoordBound I
  ySize := compactCoordBound I
  zSize := compactCoordBound I
  triples := compactTriples I
  k := (compactPositionCodes I).length

/-- Guard inputs without an `α` membership choice for every universe element. -/
noncomputable def compactMap (I : ExactCoverInput) : ThreeDimensionalMatchingInput := by
  classical
  exact if SetSystemWellFormed I.system ∧ compactEveryElementOccurs I then
    compactMapCore I
  else
    noInput

theorem compactCoverTriple_withinBounds {I : ExactCoverInput} {x j : Nat}
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    TripleWithinBounds (compactMapCore I) (compactCoverTriple I x j) := by
  have hOccurs : compactElementOccurs I x := ⟨j, hj, hx⟩
  have hAlpha := compactAlphaCode_lt_coordBound (I := I) hOccurs
  have hCode := compactPositionCode_lt_coordBound_of_support (I := I) hj hx
  simp [TripleWithinBounds, compactMapCore, compactCoverTriple, hAlpha, hCode]

theorem compactFillerTriple_withinBounds {I : ExactCoverInput} {beta x j : Nat}
    (hbeta : beta ∈ compactNonAlphaCodes I)
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    TripleWithinBounds (compactMapCore I) (compactFillerTriple I beta x j) := by
  have hBeta := compactNonAlphaCode_lt_coordBound (I := I) hbeta
  have hCode := compactPositionCode_lt_coordBound_of_support (I := I) hj hx
  have hNext := compactNextCode_lt_coordBound (I := I) hj hx
  simp [TripleWithinBounds, compactMapCore, compactFillerTriple, hBeta, hCode, hNext]

theorem mem_compactCoverTriplesForSet_iff (I : ExactCoverInput) (j : Nat)
    (t : Nat × Nat × Nat) :
    t ∈ compactCoverTriplesForSet I j ↔
      ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
        t = compactCoverTriple I x j := by
  constructor
  · intro ht
    rcases List.mem_map.mp ht with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem mem_compactCoverTriples_iff (I : ExactCoverInput) (t : Nat × Nat × Nat) :
    t ∈ compactCoverTriples I ↔
      ∃ j, j < I.system.sets.length ∧
        ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
          t = compactCoverTriple I x j := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨j, hj, htj⟩
    rcases (mem_compactCoverTriplesForSet_iff I j t).1 htj with ⟨x, hx, ht⟩
    exact ⟨j, by simpa using hj, x, hx, ht⟩
  · rintro ⟨j, hj, x, hx, ht⟩
    exact List.mem_flatMap.mpr
      ⟨j, by simpa using hj, (mem_compactCoverTriplesForSet_iff I j t).2
        ⟨x, hx, ht⟩⟩

theorem mem_compactFillerTriplesForBetaSet_iff (I : ExactCoverInput) (beta j : Nat)
    (t : Nat × Nat × Nat) :
    t ∈ compactFillerTriplesForBetaSet I beta j ↔
      ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
        t = compactFillerTriple I beta x j := by
  constructor
  · intro ht
    rcases List.mem_map.mp ht with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem mem_compactFillerTriplesForBeta_iff (I : ExactCoverInput) (beta : Nat)
    (t : Nat × Nat × Nat) :
    t ∈ compactFillerTriplesForBeta I beta ↔
      ∃ j, j < I.system.sets.length ∧
        ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
          t = compactFillerTriple I beta x j := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨j, hj, htj⟩
    rcases (mem_compactFillerTriplesForBetaSet_iff I beta j t).1 htj with
      ⟨x, hx, ht⟩
    exact ⟨j, by simpa using hj, x, hx, ht⟩
  · rintro ⟨j, hj, x, hx, ht⟩
    exact List.mem_flatMap.mpr
      ⟨j, by simpa using hj, (mem_compactFillerTriplesForBetaSet_iff I beta j t).2
        ⟨x, hx, ht⟩⟩

theorem mem_compactFillerTriples_iff (I : ExactCoverInput) (t : Nat × Nat × Nat) :
    t ∈ compactFillerTriples I ↔
      ∃ beta, beta ∈ compactNonAlphaCodes I ∧
        ∃ j, j < I.system.sets.length ∧
          ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
            t = compactFillerTriple I beta x j := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨beta, hbeta, htbeta⟩
    rcases (mem_compactFillerTriplesForBeta_iff I beta t).1 htbeta with
      ⟨j, hj, x, hx, ht⟩
    exact ⟨beta, hbeta, j, hj, x, hx, ht⟩
  · rintro ⟨beta, hbeta, j, hj, x, hx, ht⟩
    exact List.mem_flatMap.mpr
      ⟨beta, hbeta, (mem_compactFillerTriplesForBeta_iff I beta t).2
        ⟨j, hj, x, hx, ht⟩⟩

theorem compactTriple_withinBounds_of_mem {I : ExactCoverInput} {t : Nat × Nat × Nat}
    (ht : t ∈ compactTriples I) :
    TripleWithinBounds (compactMapCore I) t := by
  rcases List.mem_append.mp (by simpa [compactTriples] using ht) with hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with ⟨j, hj, x, hx, rfl⟩
    exact compactCoverTriple_withinBounds (I := I) hj hx
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨beta, hbeta, j, hj, x, hx, rfl⟩
    exact compactFillerTriple_withinBounds (I := I) hbeta hj hx

/-! ### Forward witness position lists -/

def compactSelectedSetIndex (I : ExactCoverInput) (S : List Nat) : Nat :=
  I.system.sets.idxOf S

def compactSelectedPositionCodesForSet (I : ExactCoverInput) (S : List Nat) : List Nat :=
  compactPositionCodesForSet I (compactSelectedSetIndex I S)

def compactSelectedPositionCodes (I : ExactCoverInput) (selected : List (List Nat)) :
    List Nat :=
  selected.flatMap (compactSelectedPositionCodesForSet I)

theorem compactSelectedSetIndex_lt_of_family {I : ExactCoverInput} {S : List Nat}
    (hS : IsSetInFamily I.system S) :
    compactSelectedSetIndex I S < I.system.sets.length := by
  simpa [compactSelectedSetIndex, IsSetInFamily] using
    (List.idxOf_lt_length_iff.mpr hS)

theorem compactSelectedPositionCodesForSet_length_eq_support
    {I : ExactCoverInput} {S : List Nat} (hS : IsSetInFamily I.system S) :
    (compactSelectedPositionCodesForSet I S).length = (compactSupport I S).length := by
  have hSource :
      compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
    compactSourceSetAt_idxOf_eq (I := I) (S := S) (by simpa [IsSetInFamily] using hS)
  simp [compactSelectedPositionCodesForSet, compactPositionCodesForSet, hSource]

theorem compactSelectedPositionCodes_length_eq_support_sum
    {I : ExactCoverInput} {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    (compactSelectedPositionCodes I selected).length =
      (selected.map fun S => (compactSupport I S).length).sum := by
  induction selected with
  | nil =>
      simp [compactSelectedPositionCodes]
  | cons S selected ih =>
      have hS : IsSetInFamily I.system S := hFamily S (by simp)
      have hTail : ∀ T ∈ selected, IsSetInFamily I.system T := by
        intro T hT
        exact hFamily T (by simp [hT])
      have hSlen := compactSelectedPositionCodesForSet_length_eq_support (I := I) hS
      have ihSum :
          (selected.map fun T => (compactSelectedPositionCodesForSet I T).length).sum =
            (selected.map fun T => (compactSupport I T).length).sum := by
        simpa [compactSelectedPositionCodes] using ih hTail
      simp [compactSelectedPositionCodes, hSlen, ihSum]

theorem compactSupportFrom_length_eq_digitCountsFrom_single_sum
    (start len : Nat) (S : List Nat) :
    ((List.range' start len).filter fun x => decide (x ∈ S)).length =
      (Knapsack.digitCountsFrom start len [S]).sum := by
  induction len generalizing start with
  | zero =>
      simp [Knapsack.digitCountsFrom]
  | succ len ih =>
      by_cases h : start ∈ S
      · simp [List.range'_succ, Knapsack.digitCountsFrom, Knapsack.elementCount, h, ih]
        omega
      · simp [List.range'_succ, Knapsack.digitCountsFrom, Knapsack.elementCount, h, ih]

theorem compactSupport_length_eq_digitCountsFrom_single_sum
    (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).length =
      (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).sum := by
  simpa [compactSupport] using
    compactSupportFrom_length_eq_digitCountsFrom_single_sum
      0 I.system.universeSize S

theorem list_sum_zipWith_add_of_length_eq {as bs : List Nat}
    (hLen : as.length = bs.length) :
    (as.zipWith (· + ·) bs).sum = as.sum + bs.sum := by
  induction as generalizing bs with
  | nil =>
      cases bs <;> simp at hLen ⊢
  | cons a as ih =>
      cases bs with
      | nil =>
          simp at hLen
      | cons b bs =>
          simp at hLen
          have hTail := ih hLen
          simp [hTail]
          omega

theorem compactSupport_lengths_sum_eq_digitCountsFrom_sum
    (I : ExactCoverInput) (selected : List (List Nat)) :
    (selected.map fun S => (compactSupport I S).length).sum =
      (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
  induction selected with
  | nil =>
      simp [Knapsack.digitCountsFrom_nil]
  | cons S selected ih =>
      have hLen :
          (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).length =
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).length := by
        simp [Knapsack.digitCountsFrom_length]
      calc
        (List.map (fun S => (compactSupport I S).length) (S :: selected)).sum
            =
          (compactSupport I S).length +
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
            simp [ih]
        _ =
          (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).sum +
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
            rw [compactSupport_length_eq_digitCountsFrom_single_sum]
        _ = (Knapsack.digitCountsFrom 0 I.system.universeSize (S :: selected)).sum := by
            conv_rhs => rw [Knapsack.digitCountsFrom_cons]
            exact (list_sum_zipWith_add_of_length_eq hLen).symm

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
