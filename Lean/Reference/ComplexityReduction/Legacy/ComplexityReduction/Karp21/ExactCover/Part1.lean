/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-!
P15e residual set-system target: Set Covering to Exact Cover.

The current exact-cover schema is raw.  The reduction enumerates bounded
set-covering witnesses and maps nonempty witness lists to a tiny exact-cover
instance under the current schema.
-/

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.FiniteWitness

/-- Decode a list of set-family indices into a selected subfamily. -/
def setsFromIndices (sets : List (List Nat)) (idxs : List Nat) : List (List Nat) :=
  valuesFromIndices sets [] idxs

/-- Bounded set-covering candidate subfamilies. -/
def setCoveringCandidates (I : SetCoveringInput) : List (List (List Nat)) :=
  (indexListsUpTo I.system.sets.length I.k).map (setsFromIndices I.system.sets)

theorem setCoveringCandidate_mem_family {I : SetCoveringInput} {selected : List (List Nat)}
    (hCandidate : selected ∈ setCoveringCandidates I) :
    ∀ S ∈ selected, IsSetInFamily I.system S := by
  rcases List.mem_map.mp hCandidate with ⟨idxs, hIdxs, rfl⟩
  exact valuesFromIndices_mem_of_bounds (bounds_of_mem_indexListsUpTo hIdxs)

theorem selected_mem_setCoveringCandidates {I : SetCoveringInput} {selected : List (List Nat)}
    (hLen : selected.length ≤ I.k)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    selected ∈ setCoveringCandidates I := by
  let idxs := selected.map I.system.sets.idxOf
  have hBounds : ∀ i ∈ idxs, i < I.system.sets.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  have hIdxs : idxs ∈ indexListsUpTo I.system.sets.length I.k := by
    exact mem_indexListsUpTo_of_bounds (by simpa [idxs] using hLen) hBounds
  have hDecode : setsFromIndices I.system.sets idxs = selected := by
    simpa [setsFromIndices, idxs] using
      (valuesFromIdxOf_eq (values := I.system.sets) (selected := selected)
        (fallback := ([] : List Nat)) hFamily)
  exact List.mem_map.mpr ⟨idxs, hIdxs, hDecode⟩

/-- Canonical bounded set-covering witnesses for an input. -/
noncomputable def setCoveringWitnesses (I : SetCoveringInput) : List (List (List Nat)) := by
  classical
  exact (setCoveringCandidates I).filter fun selected =>
    decide
      (selected.length ≤ I.k ∧
        (∀ S ∈ selected, IsSetInFamily I.system S) ∧
        CoversUniverse I.system selected)

theorem mem_setCoveringWitnesses_iff (I : SetCoveringInput) (selected : List (List Nat)) :
    selected ∈ setCoveringWitnesses I ↔
      selected ∈ setCoveringCandidates I ∧
        selected.length ≤ I.k ∧
          (∀ S ∈ selected, IsSetInFamily I.system S) ∧
          CoversUniverse I.system selected := by
  classical
  simp [setCoveringWitnesses]

theorem setCovering_iff_witnesses_pos (I : SetCoveringInput) :
    SetCovering I ↔ 0 < (setCoveringWitnesses I).length := by
  constructor
  · rintro ⟨selected, hLen, hFamily, hCovers⟩
    have hCandidate := selected_mem_setCoveringCandidates hLen hFamily
    have hMem : selected ∈ setCoveringWitnesses I :=
      (mem_setCoveringWitnesses_iff I selected).2
        ⟨hCandidate, hLen, hFamily, hCovers⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : setCoveringWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons selected rest =>
        have hMem : selected ∈ setCoveringWitnesses I := by
          simp [hList]
        rcases (mem_setCoveringWitnesses_iff I selected).1 hMem with
          ⟨_hCandidate, hLen, hFamily, hCovers⟩
        exact ⟨selected, hLen, hFamily, hCovers⟩

/-! ### Textbook-style slack/dummy Exact Cover route -/

/-- Slot marker used by the textbook Set Covering to Exact Cover route. -/
def slotCode (I : SetCoveringInput) (r : Nat) : Nat :=
  I.system.universeSize + r

/-- Source set at a family index, with a harmless fallback outside valid indices. -/
def sourceSetAt (I : SetCoveringInput) (i : Nat) : List Nat :=
  I.system.sets.getD i []

/-- A dummy block fills an unused set-selection slot. -/
def dummyBlock (I : SetCoveringInput) (r : Nat) : List Nat :=
  [slotCode I r]

/-- A source block fills one slot and covers the original elements assigned to that slot. -/
def sourceBlock (I : SetCoveringInput) (r : Nat) (assigned : List Nat) : List Nat :=
  slotCode I r :: assigned

/-- Some set in `cover` covers `x`, recorded by its slot. -/
def HasCoverSlot (cover : List (List Nat)) (x : Nat) : Prop :=
  ∃ r, r < cover.length ∧ x ∈ cover.getD r []

/-- The canonical slot chosen to cover `x`, when one exists. -/
noncomputable def chosenCoverSlot (cover : List (List Nat)) (x : Nat) : Nat := by
  classical
  exact if h : HasCoverSlot cover x then Nat.find h else 0

theorem chosenCoverSlot_spec {cover : List (List Nat)} {x : Nat}
    (h : HasCoverSlot cover x) :
    chosenCoverSlot cover x < cover.length ∧
      x ∈ cover.getD (chosenCoverSlot cover x) [] := by
  classical
  simpa [chosenCoverSlot, h] using (Nat.find_spec h)

/-- `x` is assigned to slot `r` when the canonical covering slot for `x` is `r`. -/
def AssignedToSlot (cover : List (List Nat)) (r x : Nat) : Prop :=
  HasCoverSlot cover x ∧ chosenCoverSlot cover x = r

/-- Original-universe elements assigned to one set-selection slot. -/
noncomputable def assignedBySlot (I : SetCoveringInput) (cover : List (List Nat))
    (r : Nat) : List Nat := by
  classical
  exact (List.range I.system.universeSize).filter fun x => decide (AssignedToSlot cover r x)

theorem mem_assignedBySlot_iff (I : SetCoveringInput) (cover : List (List Nat))
    (r x : Nat) :
    x ∈ assignedBySlot I cover r ↔
      x < I.system.universeSize ∧ AssignedToSlot cover r x := by
  classical
  simp [assignedBySlot]

/-- Assignment choices for one source set: any original-element sublist contained in it. -/
noncomputable def assignmentCandidates (I : SetCoveringInput) (i : Nat) : List (List Nat) := by
  classical
  exact (List.range I.system.universeSize).sublists.filter fun T =>
    decide (∀ x ∈ T, x ∈ sourceSetAt I i)

theorem mem_assignmentCandidates_iff (I : SetCoveringInput) (i : Nat) (T : List Nat) :
    T ∈ assignmentCandidates I i ↔
      List.Sublist T (List.range I.system.universeSize) ∧
        ∀ x ∈ T, x ∈ sourceSetAt I i := by
  classical
  simp [assignmentCandidates, List.mem_sublists]

/-- Source blocks for a fixed slot. -/
noncomputable def sourceBlocksForSlot (I : SetCoveringInput) (r : Nat) :
    List (List Nat) :=
  (List.range I.system.sets.length).flatMap fun i =>
    (assignmentCandidates I i).map (sourceBlock I r)

/-- All source blocks. -/
noncomputable def sourceBlocks (I : SetCoveringInput) : List (List Nat) :=
  (List.range I.k).flatMap fun r => sourceBlocksForSlot I r

/-- All dummy slot fillers. -/
def dummyBlocks (I : SetCoveringInput) : List (List Nat) :=
  (List.range I.k).map (dummyBlock I)

/-- The textbook slack/dummy exact-cover set system. -/
noncomputable def textbookSetSystem (I : SetCoveringInput) : SetSystemInput where
  universeSize := I.system.universeSize + I.k
  sets := dummyBlocks I ++ sourceBlocks I

/-- Textbook-style map from Set Covering to Exact Cover. -/
noncomputable def textbookMap (I : SetCoveringInput) : ExactCoverInput where
  system := textbookSetSystem I

/-- A source-block membership witness used for decoding exact-cover witnesses. -/
structure SourceBlockWitness (I : SetCoveringInput) (B : List Nat) where
  slot : Nat
  index : Nat
  assigned : List Nat
  slot_lt : slot < I.k
  index_lt : index < I.system.sets.length
  assigned_mem : assigned ∈ assignmentCandidates I index
  block_eq : B = sourceBlock I slot assigned

/-- A slot witness for any generated block. -/
structure SlotBlockWitness (I : SetCoveringInput) (B : List Nat) where
  slot : Nat
  slot_lt : slot < I.k
  slot_mem : slotCode I slot ∈ B

theorem sourceBlockWitness_of_mem_sourceBlocks {I : SetCoveringInput} {B : List Nat}
    (hB : B ∈ sourceBlocks I) :
    Nonempty (SourceBlockWitness I B) := by
  rcases List.mem_flatMap.mp hB with ⟨r, hr, hSlot⟩
  rcases List.mem_flatMap.mp hSlot with ⟨i, hi, hMap⟩
  rcases List.mem_map.mp hMap with ⟨T, hT, rfl⟩
  exact ⟨{ slot := r
           index := i
           assigned := T
           slot_lt := by simpa using hr
           index_lt := by simpa using hi
           assigned_mem := hT
           block_eq := rfl }⟩

theorem slotWitness_of_mem_textbookSetSystem {I : SetCoveringInput} {B : List Nat}
    (hB : B ∈ (textbookSetSystem I).sets) :
    Nonempty (SlotBlockWitness I B) := by
  simp [textbookSetSystem, dummyBlocks] at hB
  rcases hB with hDummy | hSource
  · rcases hDummy with ⟨r, hr, hEq⟩
    subst B
    exact ⟨{ slot := r
             slot_lt := hr
             slot_mem := by simp [dummyBlock] }⟩
  · rcases sourceBlockWitness_of_mem_sourceBlocks hSource with ⟨w⟩
    exact ⟨{ slot := w.slot
             slot_lt := w.slot_lt
             slot_mem := by simp [w.block_eq, sourceBlock] }⟩

/-- Decode the slot used by a generated exact-cover block. -/
noncomputable def slotOfBlock (I : SetCoveringInput) (B : List Nat) : Nat := by
  classical
  exact if h : Nonempty (SlotBlockWitness I B) then (Classical.choice h).slot else 0

theorem slotOfBlock_lt_of_mem {I : SetCoveringInput} {B : List Nat}
    (hB : B ∈ (textbookSetSystem I).sets) :
    slotOfBlock I B < I.k := by
  classical
  have h := slotWitness_of_mem_textbookSetSystem hB
  simpa [slotOfBlock, h] using (Classical.choice h).slot_lt

theorem slotCode_mem_slotOfBlock {I : SetCoveringInput} {B : List Nat}
    (hB : B ∈ (textbookSetSystem I).sets) :
    slotCode I (slotOfBlock I B) ∈ B := by
  classical
  have h := slotWitness_of_mem_textbookSetSystem hB
  simpa [slotOfBlock, h] using (Classical.choice h).slot_mem

/-- Decode the source set represented by a source block; dummy blocks decode to `none`. -/
noncomputable def sourceSetOfBlock (I : SetCoveringInput) (B : List Nat) :
    Option (List Nat) := by
  classical
  exact if h : Nonempty (SourceBlockWitness I B) then
    some (sourceSetAt I (Classical.choice h).index)
  else
    none

theorem sourceSetOfBlock_mem_family {I : SetCoveringInput} {B S : List Nat}
    (hEq : sourceSetOfBlock I B = some S) :
    IsSetInFamily I.system S := by
  classical
  unfold sourceSetOfBlock at hEq
  by_cases h : Nonempty (SourceBlockWitness I B)
  · simp [h] at hEq
    subst S
    have hi := (Classical.choice h).index_lt
    rw [sourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hi]
    exact List.getElem_mem _
  · simp [h] at hEq

theorem sourceSetOfBlock_covers_of_original_mem {I : SetCoveringInput} {B : List Nat}
    {x : Nat}
    (hB : B ∈ (textbookSetSystem I).sets)
    (hx : x < I.system.universeSize)
    (hxB : x ∈ B) :
    ∃ S, sourceSetOfBlock I B = some S ∧ x ∈ S := by
  classical
  have hCases := hB
  simp [textbookSetSystem, dummyBlocks] at hCases
  rcases hCases with hDummy | hSource
  · rcases hDummy with ⟨r, _hr, hEq⟩
    subst B
    simp [dummyBlock, slotCode] at hxB
    omega
  · have hNonempty := sourceBlockWitness_of_mem_sourceBlocks hSource
    refine ⟨sourceSetAt I (Classical.choice hNonempty).index, ?_, ?_⟩
    · simp [sourceSetOfBlock, hNonempty]
    · let w := Classical.choice hNonempty
      have hxBlock : x ∈ sourceBlock I w.slot w.assigned := by
        simpa [w.block_eq] using hxB
      change x ∈ sourceSetAt I w.index
      have hxAssigned : x ∈ w.assigned := by
        simp [sourceBlock, slotCode] at hxBlock
        rcases hxBlock with hxSlot | hxAssigned
        · omega
        · exact hxAssigned
      exact ((mem_assignmentCandidates_iff I w.index w.assigned).1 w.assigned_mem).2
        x hxAssigned

noncomputable def sourceIndexOfCoverSlot (I : SetCoveringInput)
    (cover : List (List Nat)) (r : Nat) : Nat :=
  I.system.sets.idxOf (cover.getD r [])

/-- The block used by a concrete set-cover witness at slot `r`. -/
noncomputable def blockForCoverSlot (I : SetCoveringInput) (cover : List (List Nat))
    (r : Nat) : List Nat := by
  classical
  exact if r < cover.length then
    sourceBlock I r (assignedBySlot I cover r)
  else
    dummyBlock I r

/-- Exact-cover blocks induced by a set-covering witness. -/
noncomputable def blocksFromCover (I : SetCoveringInput) (cover : List (List Nat)) :
    List (List Nat) :=
  (List.range I.k).map (blockForCoverSlot I cover)

theorem slotCode_not_mem_assignedBySlot (I : SetCoveringInput) (cover : List (List Nat))
    (r s : Nat) :
    slotCode I r ∉ assignedBySlot I cover s := by
  intro h
  have hlt := (mem_assignedBySlot_iff I cover s (slotCode I r)).1 h |>.1
  simp [slotCode] at hlt

theorem slotCode_mem_blockForCoverSlot_iff (I : SetCoveringInput)
    (cover : List (List Nat)) (r s : Nat) :
    slotCode I r ∈ blockForCoverSlot I cover s ↔ r = s := by
  classical
  by_cases hs : s < cover.length
  · constructor
    · intro h
      simp [blockForCoverSlot, hs, sourceBlock] at h
      rcases h with hEq | hAssigned
      · simp [slotCode] at hEq
        omega
      · exact (slotCode_not_mem_assignedBySlot I cover r s hAssigned).elim
    · intro h
      subst s
      simp [blockForCoverSlot, hs, sourceBlock]
  · constructor
    · intro h
      simp [blockForCoverSlot, hs, dummyBlock, slotCode] at h
      omega
    · intro h
      subst s
      simp [blockForCoverSlot, hs, dummyBlock]

theorem mem_blockForCoverSlot_cases {I : SetCoveringInput} {cover : List (List Nat)}
    {r x : Nat}
    (hx : x ∈ blockForCoverSlot I cover r) :
    x = slotCode I r ∨
      x < I.system.universeSize ∧ AssignedToSlot cover r x := by
  classical
  by_cases hr : r < cover.length
  · simp [blockForCoverSlot, hr, sourceBlock] at hx
    rcases hx with hxSlot | hxAssigned
    · exact Or.inl hxSlot
    · exact Or.inr ((mem_assignedBySlot_iff I cover r x).1 hxAssigned)
  · simp [blockForCoverSlot, hr, dummyBlock] at hx
    exact Or.inl hx

theorem blockForCoverSlot_mem_textbookSetSystem {I : SetCoveringInput}
    {cover : List (List Nat)}
    (hFamily : ∀ S ∈ cover, IsSetInFamily I.system S)
    {r : Nat}
    (hr : r ∈ List.range I.k) :
    blockForCoverSlot I cover r ∈ (textbookSetSystem I).sets := by
  classical
  have hrk : r < I.k := by simpa using hr
  simp [textbookSetSystem]
  by_cases hSlot : r < cover.length
  · right
    refine List.mem_flatMap.mpr ⟨r, by simpa using hrk, ?_⟩
    let i := sourceIndexOfCoverSlot I cover r
    have hCoverMem : cover.getD r [] ∈ cover := by
      rw [List.getD_eq_getElem (l := cover) (d := []) hSlot]
      exact List.getElem_mem _
    have hSourceFamily : cover.getD r [] ∈ I.system.sets := hFamily _ hCoverMem
    have hi : i < I.system.sets.length := by
      exact List.idxOf_lt_length_iff.mpr hSourceFamily
    have hSourceEq : sourceSetAt I i = cover.getD r [] := by
      dsimp [i, sourceSetAt, sourceIndexOfCoverSlot]
      have hi' : I.system.sets.idxOf (cover.getD r []) < I.system.sets.length :=
        List.idxOf_lt_length_iff.mpr hSourceFamily
      rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hi']
      exact List.idxOf_get hi'
    have hAssignedMem :
        assignedBySlot I cover r ∈ assignmentCandidates I i := by
      refine (mem_assignmentCandidates_iff I i (assignedBySlot I cover r)).2 ?_
      constructor
      · change List.Sublist
          ((List.range I.system.universeSize).filter fun x =>
            decide (AssignedToSlot cover r x))
          (List.range I.system.universeSize)
        exact List.filter_sublist
      · intro x hx
        have hxInfo := (mem_assignedBySlot_iff I cover r x).1 hx
        rcases hxInfo.2 with ⟨hHas, hChosen⟩
        have hSpec := chosenCoverSlot_spec hHas
        rw [hChosen] at hSpec
        simpa [hSourceEq] using hSpec.2
    refine List.mem_flatMap.mpr ⟨i, by simpa using hi, ?_⟩
    exact List.mem_map.mpr ⟨assignedBySlot I cover r, hAssignedMem, by
      simp [blockForCoverSlot, hSlot]⟩
  · left
    exact List.mem_map.mpr ⟨r, by simpa using hrk, by simp [blockForCoverSlot, hSlot]⟩

theorem blocksFromCover_nodup (I : SetCoveringInput) (cover : List (List Nat)) :
    (blocksFromCover I cover).Nodup := by
  classical
  unfold blocksFromCover
  exact (List.nodup_range (n := I.k)).map_on (by
    intro r hr s hs hEq
    have hMem : slotCode I r ∈ blockForCoverSlot I cover s := by
      rw [← hEq]
      exact (slotCode_mem_blockForCoverSlot_iff I cover r r).2 rfl
    exact (slotCode_mem_blockForCoverSlot_iff I cover r s).1 hMem)

theorem blocksFromCover_pairwiseDisjoint (I : SetCoveringInput)
    (cover : List (List Nat)) :
    PairwiseDisjointFamily (blocksFromCover I cover) := by
  classical
  intro A hA B hB hNe x hxA hxB
  rcases List.mem_map.mp hA with ⟨r, hr, rfl⟩
  rcases List.mem_map.mp hB with ⟨s, hs, rfl⟩
  have hrs : r ≠ s := by
    intro h
    subst s
    exact hNe rfl
  rcases mem_blockForCoverSlot_cases hxA with hxASlot | hxAAssigned
  · rcases mem_blockForCoverSlot_cases hxB with hxBSlot | hxBAssigned
    · have : r = s := by
        rw [hxASlot] at hxBSlot
        simp [slotCode] at hxBSlot
        omega
      exact hrs this
    · rw [hxASlot] at hxBAssigned
      simp [slotCode] at hxBAssigned
  · rcases mem_blockForCoverSlot_cases hxB with hxBSlot | hxBAssigned
    · rw [hxBSlot] at hxAAssigned
      simp [slotCode] at hxAAssigned
    · have hEq : r = s := by
        rw [← hxAAssigned.2.2, ← hxBAssigned.2.2]
      exact hrs hEq

theorem blocksFromCover_coversUniverse {I : SetCoveringInput} {cover : List (List Nat)}
    (hLen : cover.length ≤ I.k)
    (hCovers : CoversUniverse I.system cover) :
    CoversUniverse (textbookSetSystem I) (blocksFromCover I cover) := by
  classical
  intro x hx
  by_cases hxOrig : x < I.system.universeSize
  · rcases hCovers x hxOrig with ⟨S, hS, hxS⟩
    rcases List.mem_iff_get.mp hS with ⟨r, hrEq⟩
    have hHas : HasCoverSlot cover x := by
      refine ⟨r.val, r.isLt, ?_⟩
      have hGetD : cover.getD r.val [] = S := by
        rw [List.getD_eq_getElem (l := cover) (d := []) r.isLt]
        exact hrEq
      exact hGetD.symm ▸ hxS
    let c := chosenCoverSlot cover x
    have hSpec := chosenCoverSlot_spec hHas
    have hck : c < I.k := hSpec.1.trans_le hLen
    refine ⟨blockForCoverSlot I cover c, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨c, by simpa using hck, rfl⟩
    · simp [blockForCoverSlot, hSpec.1, sourceBlock, assignedBySlot, hxOrig,
        AssignedToSlot, hHas, c]
  · have hxSlot : ∃ r, r < I.k ∧ x = slotCode I r := by
      refine ⟨x - I.system.universeSize, ?_, ?_⟩
      · simp [textbookSetSystem] at hx
        omega
      · simp [slotCode]
        omega
    rcases hxSlot with ⟨r, hr, rfl⟩
    refine ⟨blockForCoverSlot I cover r, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩
    · exact (slotCode_mem_blockForCoverSlot_iff I cover r r).2 rfl

theorem blocksFromCover_family {I : SetCoveringInput} {cover : List (List Nat)}
    (hFamily : ∀ S ∈ cover, IsSetInFamily I.system S) :
    ∀ B ∈ blocksFromCover I cover, IsSetInFamily (textbookSetSystem I) B := by
  intro B hB
  rcases List.mem_map.mp hB with ⟨r, hr, rfl⟩
  exact blockForCoverSlot_mem_textbookSetSystem hFamily hr

theorem filterMap_length_le {α β : Type} (f : α → Option β) :
    ∀ xs : List α, (xs.filterMap f).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      cases h : f x with
      | none =>
          simp [h]
          exact Nat.le_trans (filterMap_length_le f xs) (Nat.le_succ xs.length)
      | some y =>
          simp [h]
          exact filterMap_length_le f xs

theorem selected_length_le_slots {I : SetCoveringInput} {selected : List (List Nat)}
    (hFamily : ∀ B ∈ selected, IsSetInFamily (textbookSetSystem I) B)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    selected.length ≤ I.k := by
  classical
  let slots := selected.map (slotOfBlock I)
  have hSlotsNodup : slots.Nodup := by
    exact hNodup.map_on (by
      intro A hA B hB hEq
      by_contra hNe
      have hAFamily := hFamily A hA
      have hBFamily := hFamily B hB
      have hAMem := slotCode_mem_slotOfBlock hAFamily
      have hBMem := slotCode_mem_slotOfBlock hBFamily
      have hSameCode :
          slotCode I (slotOfBlock I A) = slotCode I (slotOfBlock I B) := by
        simp [hEq]
      exact hDisjoint A hA B hB hNe (slotCode I (slotOfBlock I A)) hAMem
        (by simpa [hSameCode] using hBMem))
  have hSlotMem : ∀ r ∈ slots, r ∈ List.range I.k := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨B, hB, rfl⟩
    exact by simpa using (slotOfBlock_lt_of_mem (hFamily B hB))
  have hLen := nodup_length_le_of_mem hSlotsNodup hSlotMem
  simpa [slots] using hLen

theorem decodedCoverSets_family {I : SetCoveringInput} {selected : List (List Nat)} :
    ∀ S ∈ selected.filterMap (sourceSetOfBlock I), IsSetInFamily I.system S := by
  intro S hS
  rw [List.mem_filterMap] at hS
  rcases hS with ⟨B, _hB, hEq⟩
  exact sourceSetOfBlock_mem_family hEq

theorem decodedCoverSets_cover {I : SetCoveringInput} {selected : List (List Nat)}
    (hFamily : ∀ B ∈ selected, IsSetInFamily (textbookSetSystem I) B)
    (hCovers : CoversUniverse (textbookSetSystem I) selected) :
    CoversUniverse I.system (selected.filterMap (sourceSetOfBlock I)) := by
  intro x hx
  have hxTarget : x < (textbookSetSystem I).universeSize := by
    simp [textbookSetSystem]
    omega
  rcases hCovers x hxTarget with ⟨B, hB, hxB⟩
  rcases sourceSetOfBlock_covers_of_original_mem (hFamily B hB) hx hxB with
    ⟨S, hDecode, hxS⟩
  exact ⟨S, by rw [List.mem_filterMap]; exact ⟨B, hB, hDecode⟩, hxS⟩

theorem textbookSetSystem_wellFormed (I : SetCoveringInput) :
    SetSystemWellFormed (textbookSetSystem I) := by
  intro B hB x hxB
  have hCases := hB
  simp [textbookSetSystem, dummyBlocks] at hCases
  rcases hCases with hDummy | hSource
  · rcases hDummy with ⟨r, hr, hEq⟩
    subst B
    simp [dummyBlock, slotCode] at hxB
    subst x
    change I.system.universeSize + r < I.system.universeSize + I.k
    omega
  · rcases sourceBlockWitness_of_mem_sourceBlocks hSource with ⟨w⟩
    have hxBlock : x ∈ sourceBlock I w.slot w.assigned := by
      simpa [w.block_eq] using hxB
    simp [sourceBlock, slotCode] at hxBlock
    rcases hxBlock with hxSlot | hxAssigned
    · subst x
      change I.system.universeSize + w.slot < I.system.universeSize + I.k
      have hwSlot : w.slot < I.k := w.slot_lt
      omega
    · have hSub :
          List.Sublist w.assigned (List.range I.system.universeSize) :=
        ((mem_assignmentCandidates_iff I w.index w.assigned).1 w.assigned_mem).1
      have hxRange : x ∈ List.range I.system.universeSize := hSub.subset hxAssigned
      simp at hxRange
      change x < I.system.universeSize + I.k
      omega

theorem textbookMap_correct (I : SetCoveringInput) :
    setCoveringDecisionProblem.isYes I ↔ ExactCover (textbookMap I) := by
  change SetCovering I ↔ ExactCover (textbookMap I)
  constructor
  · rintro ⟨cover, hLen, hFamily, hCovers⟩
    refine ⟨by simpa [textbookMap] using textbookSetSystem_wellFormed I, ?_⟩
    refine ⟨blocksFromCover I cover, ?_, ?_, ?_, ?_⟩
    · simpa [textbookMap] using blocksFromCover_family hFamily
    · exact blocksFromCover_nodup I cover
    · exact blocksFromCover_pairwiseDisjoint I cover
    · simpa [textbookMap] using blocksFromCover_coversUniverse hLen hCovers
  · rintro ⟨_hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
    let coverSets := selected.filterMap (sourceSetOfBlock I)
    refine ⟨coverSets, ?_, ?_, ?_⟩
    · exact (filterMap_length_le (sourceSetOfBlock I) selected).trans
        (selected_length_le_slots hFamily hNodup hDisjoint)
    · simpa [coverSets] using (decodedCoverSets_family (I := I) (selected := selected))
    · simpa [coverSets] using
        (decodedCoverSets_cover (I := I) hFamily hCovers)

/-! ### Compact Set Covering CNF encoding

The old slack/dummy exact-cover map above is semantically correct, but it
enumerates all assignments of universe elements to source sets.  The following
CNF layer is the compact replacement foundation: it represents a set cover of
size at most `k` by `k` slots, each selecting one source set or a dummy choice.
-/

def setCoveringChoiceCount (I : SetCoveringInput) : Nat :=
  I.system.sets.length + 1

def setCoveringDummyChoice (I : SetCoveringInput) : Nat :=
  I.system.sets.length

def setCoveringChoiceVar (_I : SetCoveringInput) (slot choice : Nat) : Nat :=
  Nat.pair slot choice

def setCoveringChoiceLit (I : SetCoveringInput) (slot choice : Nat) : SAT.Literal :=
  SAT.Literal.positive (setCoveringChoiceVar I slot choice)

def setCoveringChoiceNegLit (I : SetCoveringInput) (slot choice : Nat) : SAT.Literal :=
  SAT.Literal.negative (setCoveringChoiceVar I slot choice)

def setCoveringSlotAtLeastClause (I : SetCoveringInput) (slot : Nat) : SAT.Clause :=
  (List.range (setCoveringChoiceCount I)).map (setCoveringChoiceLit I slot)

def setCoveringSlotAtMostClausesFor (I : SetCoveringInput) (slot choice : Nat) :
    SAT.CNF :=
  ((List.range (setCoveringChoiceCount I)).filter fun other => decide (choice < other)).map
    fun other => [setCoveringChoiceNegLit I slot choice, setCoveringChoiceNegLit I slot other]

def setCoveringSlotAtMostClauses (I : SetCoveringInput) (slot : Nat) : SAT.CNF :=
  (List.range (setCoveringChoiceCount I)).flatMap
    (setCoveringSlotAtMostClausesFor I slot)

def setCoveringSlotClausesFor (I : SetCoveringInput) (slot : Nat) : SAT.CNF :=
  setCoveringSlotAtLeastClause I slot :: setCoveringSlotAtMostClauses I slot

def setCoveringSlotClauses (I : SetCoveringInput) : SAT.CNF :=
  (List.range I.k).flatMap (setCoveringSlotClausesFor I)

def setCoveringCoverageLitsForSlot (I : SetCoveringInput) (x slot : Nat) :
    List SAT.Literal :=
  (List.range I.system.sets.length).filterMap fun idx =>
    if x ∈ sourceSetAt I idx then some (setCoveringChoiceLit I slot idx) else none

def setCoveringCoverageClause (I : SetCoveringInput) (x : Nat) : SAT.Clause :=
  (List.range I.k).flatMap (setCoveringCoverageLitsForSlot I x)

def setCoveringCoverageClauses (I : SetCoveringInput) : SAT.CNF :=
  (List.range I.system.universeSize).map (setCoveringCoverageClause I)

def setCoveringCNF (I : SetCoveringInput) : SAT.CNF :=
  setCoveringSlotClauses I ++ setCoveringCoverageClauses I

noncomputable def setCoveringChoiceIndexOfCover
    (I : SetCoveringInput) (cover : List (List Nat)) (slot : Nat) : Nat := by
  classical
  exact if slot < cover.length then I.system.sets.idxOf (cover.getD slot [])
    else setCoveringDummyChoice I

noncomputable def setCoveringCoverAssignment
    (I : SetCoveringInput) (cover : List (List Nat)) : SAT.Assignment := by
  classical
  exact fun v =>
    if ∃ slot, slot < I.k ∧
      v = setCoveringChoiceVar I slot (setCoveringChoiceIndexOfCover I cover slot)
    then true else false

theorem setCoveringChoiceIndexOfCover_lt_choiceCount {I : SetCoveringInput}
    {cover : List (List Nat)}
    (hFamily : ∀ S ∈ cover, IsSetInFamily I.system S) (slot : Nat) :
    setCoveringChoiceIndexOfCover I cover slot < setCoveringChoiceCount I := by
  classical
  by_cases hslot : slot < cover.length
  · have hMem : cover.getD slot [] ∈ cover := by
      rw [List.getD_eq_getElem (l := cover) (d := []) hslot]
      exact List.getElem_mem _
    have hSet : cover.getD slot [] ∈ I.system.sets := hFamily _ hMem
    have hIdx : I.system.sets.idxOf (cover.getD slot []) < I.system.sets.length :=
      List.idxOf_lt_length_iff.mpr hSet
    simpa [setCoveringChoiceIndexOfCover, hslot, setCoveringChoiceCount] using
      Nat.lt_succ_of_lt hIdx
  · simp [setCoveringChoiceIndexOfCover, hslot, setCoveringChoiceCount,
      setCoveringDummyChoice]

theorem setCoveringCoverAssignment_choice_true_iff
    (I : SetCoveringInput) (cover : List (List Nat)) {slot choice : Nat}
    (hslot : slot < I.k) :
    setCoveringCoverAssignment I cover (setCoveringChoiceVar I slot choice) = true ↔
      choice = setCoveringChoiceIndexOfCover I cover slot := by
  classical
  constructor
  · intro htrue
    unfold setCoveringCoverAssignment at htrue
    by_cases h :
        ∃ s, s < I.k ∧
          setCoveringChoiceVar I slot choice =
            setCoveringChoiceVar I s (setCoveringChoiceIndexOfCover I cover s)
    · simp [h] at htrue
      rcases h with ⟨s, _hs, hEq⟩
      have hPair :
          Nat.pair slot choice =
            Nat.pair s (setCoveringChoiceIndexOfCover I cover s) := by
        simpa [setCoveringChoiceVar] using hEq
      rcases Nat.pair_eq_pair.mp hPair with ⟨hslotEq, hchoiceEq⟩
      subst s
      exact hchoiceEq
    · simp [h] at htrue
  · intro hchoice
    unfold setCoveringCoverAssignment
    have h :
        ∃ s, s < I.k ∧
          setCoveringChoiceVar I slot choice =
            setCoveringChoiceVar I s (setCoveringChoiceIndexOfCover I cover s) := by
      refine ⟨slot, hslot, ?_⟩
      simp [setCoveringChoiceVar, hchoice]
    simp [h]

theorem setCoveringSlotAtMostClause_mem_cnf {I : SetCoveringInput}
    {slot choice other : Nat}
    (hslot : slot < I.k)
    (hchoice : choice < setCoveringChoiceCount I)
    (hother : other < setCoveringChoiceCount I)
    (hlt : choice < other) :
    [setCoveringChoiceNegLit I slot choice, setCoveringChoiceNegLit I slot other] ∈
      setCoveringCNF I := by
  classical
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨slot, by simpa using hslot, ?_⟩
  simp [setCoveringSlotClausesFor]
  right
  apply List.mem_flatMap.mpr
  refine ⟨choice, by simpa using hchoice, ?_⟩
  apply List.mem_map.mpr
  refine ⟨other, ?_, rfl⟩
  simp [hother, hlt]

theorem setCoveringSlotAtLeastClause_mem_cnf {I : SetCoveringInput} {slot : Nat}
    (hslot : slot < I.k) :
    setCoveringSlotAtLeastClause I slot ∈ setCoveringCNF I := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨slot, by simpa using hslot, ?_⟩
  simp [setCoveringSlotClausesFor]

theorem setCoveringCoverageClause_mem_cnf {I : SetCoveringInput} {x : Nat}
    (hx : x < I.system.universeSize) :
    setCoveringCoverageClause I x ∈ setCoveringCNF I := by
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩

theorem mem_setCoveringCoverageClause_iff
    (I : SetCoveringInput) (x : Nat) (lit : SAT.Literal) :
    lit ∈ setCoveringCoverageClause I x ↔
      ∃ slot, slot < I.k ∧ ∃ idx, idx < I.system.sets.length ∧
        x ∈ sourceSetAt I idx ∧ lit = setCoveringChoiceLit I slot idx := by
  classical
  constructor
  · intro h
    rcases List.mem_flatMap.mp h with ⟨slot, hslot, hlit⟩
    rw [setCoveringCoverageLitsForSlot, List.mem_filterMap] at hlit
    rcases hlit with ⟨idx, hidx, hSome⟩
    by_cases hx : x ∈ sourceSetAt I idx
    · simp [hx] at hSome
      exact ⟨slot, by simpa using hslot, idx, by simpa using hidx, hx, hSome.symm⟩
    · simp [hx] at hSome
  · rintro ⟨slot, hslot, idx, hidx, hx, rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨slot, by simpa using hslot, ?_⟩
    rw [setCoveringCoverageLitsForSlot, List.mem_filterMap]
    refine ⟨idx, by simpa using hidx, ?_⟩
    simp [hx]

theorem setCoveringCoverAssignment_atMost_clause
    {I : SetCoveringInput} {cover : List (List Nat)} {slot choice other : Nat}
    (hslot : slot < I.k) (hlt : choice < other) :
    SAT.Clause.Satisfies
      [setCoveringChoiceNegLit I slot choice, setCoveringChoiceNegLit I slot other]
      (setCoveringCoverAssignment I cover) := by
  classical
  by_cases hchoiceSel : choice = setCoveringChoiceIndexOfCover I cover slot
  · have hotherNe : other ≠ setCoveringChoiceIndexOfCover I cover slot := by
      intro hotherSel
      omega
    have hotherFalse :
        setCoveringCoverAssignment I cover (setCoveringChoiceVar I slot other) = false := by
      cases h :
          setCoveringCoverAssignment I cover (setCoveringChoiceVar I slot other) <;> simp
      have hSel :=
        (setCoveringCoverAssignment_choice_true_iff I cover hslot).1 h
      exact (hotherNe hSel).elim
    refine ⟨setCoveringChoiceNegLit I slot other, by simp, ?_⟩
    simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval, hotherFalse]
  · have hchoiceFalse :
        setCoveringCoverAssignment I cover (setCoveringChoiceVar I slot choice) = false := by
      cases h :
          setCoveringCoverAssignment I cover (setCoveringChoiceVar I slot choice) <;> simp
      have hSel :=
        (setCoveringCoverAssignment_choice_true_iff I cover hslot).1 h
      exact (hchoiceSel hSel).elim
    refine ⟨setCoveringChoiceNegLit I slot choice, by simp, ?_⟩
    simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval, hchoiceFalse]

theorem setCoveringCNF_satisfiable_of_setCovering (I : SetCoveringInput) :
    SetCovering I → SAT.CNF.Satisfiable (setCoveringCNF I) := by
  classical
  rintro ⟨cover, hLen, hFamily, hCovers⟩
  refine ⟨setCoveringCoverAssignment I cover, ?_⟩
  intro clause hclause
  rw [setCoveringCNF, List.mem_append] at hclause
  rcases hclause with hSlot | hCoverage
  · rw [setCoveringSlotClauses] at hSlot
    rcases List.mem_flatMap.mp hSlot with ⟨slot, hslotMem, hBlock⟩
    have hslot : slot < I.k := by simpa using hslotMem
    simp [setCoveringSlotClausesFor] at hBlock
    rcases hBlock with hAtLeast | hAtMost
    · subst clause
      let choice := setCoveringChoiceIndexOfCover I cover slot
      have hchoice := setCoveringChoiceIndexOfCover_lt_choiceCount
        (I := I) (cover := cover) hFamily slot
      refine ⟨setCoveringChoiceLit I slot choice, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨choice, by simpa using hchoice, rfl⟩
      · simp [setCoveringChoiceLit, SAT.Literal.positive, SAT.Literal.eval, choice,
          (setCoveringCoverAssignment_choice_true_iff I cover hslot).2 rfl]
    · rcases List.mem_flatMap.mp hAtMost with ⟨choice, hchoiceMem, hPair⟩
      rcases List.mem_map.mp hPair with ⟨other, hotherMem, hEq⟩
      subst clause
      have hlt : choice < other := by
        simpa using (List.mem_filter.mp hotherMem).2
      exact setCoveringCoverAssignment_atMost_clause (I := I) (cover := cover)
        (slot := slot) (choice := choice) (other := other) hslot hlt
  · rw [setCoveringCoverageClauses] at hCoverage
    rcases List.mem_map.mp hCoverage with ⟨x, hxMem, rfl⟩
    have hx : x < I.system.universeSize := by simpa using hxMem
    rcases hCovers x hx with ⟨S, hS, hxS⟩
    rcases List.mem_iff_get.mp hS with ⟨slotFin, hSlotEq⟩
    let slot := slotFin.val
    have hslotCover : slot < cover.length := slotFin.isLt
    have hslot : slot < I.k := hslotCover.trans_le hLen
    let idx := I.system.sets.idxOf S
    have hSFamily : S ∈ I.system.sets := hFamily S hS
    have hidx : idx < I.system.sets.length := by
      exact List.idxOf_lt_length_iff.mpr hSFamily
    have hSourceEq : sourceSetAt I idx = S := by
      dsimp [idx, sourceSetAt]
      have hidx' : I.system.sets.idxOf S < I.system.sets.length :=
        List.idxOf_lt_length_iff.mpr hSFamily
      rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hidx']
      exact List.idxOf_get hidx'
    have hChoiceEq : setCoveringChoiceIndexOfCover I cover slot = idx := by
      dsimp [setCoveringChoiceIndexOfCover, slot]
      have hget : cover.getD slotFin.val [] = S := by
        rw [List.getD_eq_getElem (l := cover) (d := []) slotFin.isLt]
        exact hSlotEq
      simpa [hslotCover, idx] using congrArg (fun T => I.system.sets.idxOf T) hget
    refine ⟨setCoveringChoiceLit I slot idx, ?_, ?_⟩
    · exact (mem_setCoveringCoverageClause_iff I x (setCoveringChoiceLit I slot idx)).2
        ⟨slot, hslot, idx, hidx, by simpa [hSourceEq] using hxS, rfl⟩
    · simpa [setCoveringChoiceLit, SAT.Literal.positive, SAT.Literal.eval] using
        (setCoveringCoverAssignment_choice_true_iff I cover hslot).2 hChoiceEq.symm

theorem setCoveringChoice_unique_of_cnf_satisfies {I : SetCoveringInput}
    {a : SAT.Assignment}
    (hSat : SAT.CNF.Satisfies (setCoveringCNF I) a)
    {slot choice other : Nat}
    (hslot : slot < I.k)
    (hchoice : choice < setCoveringChoiceCount I)
    (hother : other < setCoveringChoiceCount I)
    (hChoiceTrue : a (setCoveringChoiceVar I slot choice) = true)
    (hOtherTrue : a (setCoveringChoiceVar I slot other) = true) :
    choice = other := by
  classical
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hClauseSat := hSat _
      (setCoveringSlotAtMostClause_mem_cnf (I := I) hslot hchoice hother hlt)
    rcases hClauseSat with ⟨lit, hlit, hEval⟩
    simp at hlit
    rcases hlit with rfl | rfl
    · simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval,
        hChoiceTrue] at hEval
    · simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval,
        hOtherTrue] at hEval
  · have hClauseSat := hSat _
      (setCoveringSlotAtMostClause_mem_cnf (I := I) hslot hother hchoice hgt)
    rcases hClauseSat with ⟨lit, hlit, hEval⟩
    simp at hlit
    rcases hlit with rfl | rfl
    · simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval,
        hOtherTrue] at hEval
    · simp [setCoveringChoiceNegLit, SAT.Literal.negative, SAT.Literal.eval,
        hChoiceTrue] at hEval

end ExactCover
end Karp21
end ComplexityReduction
