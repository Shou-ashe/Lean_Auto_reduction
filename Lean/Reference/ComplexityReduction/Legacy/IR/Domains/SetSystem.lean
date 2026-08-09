/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Legacy.IR.Core.Builders
import ComplexityReduction.Legacy.IR.Views.IncidenceView
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.SetSystem

/-!
Set-system source normalization into the incidence-view fragment of the IR.

The right-hand incidence objects are set-family indices, not set values.  This
keeps duplicate sets distinct and matches the list representation of source
instances.
-/

namespace ComplexityReduction

namespace IncidenceView

/--
Selected right objects form a set covering of size at most `k`: every left
object is incident to at least one selected right object.
-/
def SetCoveringPredicate {U : UniversalRelIR} (V : IncidenceView U)
    (k : Nat) (selected : List ObjId) : Prop :=
  selected.length ≤ k ∧
    (∀ r ∈ selected, r ∈ V.RightObjects) ∧
    ∀ l ∈ V.LeftObjects, ∃ r ∈ selected, V.Mem l r

/-- Existential set-covering predicate on the right objects of an incidence view. -/
def ExistsSetCovering {U : UniversalRelIR} (V : IncidenceView U) (k : Nat) : Prop :=
  ∃ selected, V.SetCoveringPredicate k selected

/--
Selected right objects form a set packing of size at least `k`: each left object
is incident to at most one selected right object.
-/
def SetPackingPredicate {U : UniversalRelIR} (V : IncidenceView U)
    (k : Nat) (selected : List ObjId) : Prop :=
  selected.length >= k ∧
    selected.Nodup ∧
    (∀ r ∈ selected, r ∈ V.RightObjects) ∧
    ∀ l ∈ V.LeftObjects, ∀ r ∈ selected, ∀ r' ∈ selected,
      V.Mem l r → V.Mem l r' → r = r'

/-- Existential set-packing predicate on the right objects of an incidence view. -/
def ExistsSetPacking {U : UniversalRelIR} (V : IncidenceView U) (k : Nat) : Prop :=
  ∃ selected, V.SetPackingPredicate k selected

/--
Selected left objects form a hitting set of size at most `k`: every right object
is incident to at least one selected left object.
-/
def HittingSetPredicate {U : UniversalRelIR} (V : IncidenceView U)
    (k : Nat) (selected : List ObjId) : Prop :=
  selected.length ≤ k ∧
    (∀ l ∈ selected, l ∈ V.LeftObjects) ∧
    ∀ r ∈ V.RightObjects, ∃ l ∈ selected, V.Mem l r

/-- Existential hitting-set predicate on the left objects of an incidence view. -/
def ExistsHittingSet {U : UniversalRelIR} (V : IncidenceView U) (k : Nat) : Prop :=
  ∃ selected, V.HittingSetPredicate k selected

end IncidenceView

namespace SetSystem

open ComplexityReduction.Combinatorics

/-- Membership tuples generated from a set family, starting at set index `start`. -/
def membershipPairsFrom : Nat → List (List Nat) → List (Nat × Nat)
  | _, [] => []
  | j, S :: sets => S.map (fun x => (x, j)) ++ membershipPairsFrom (j + 1) sets

/-- Membership tuples `[x, j]` for `x ∈ sets[j]`. -/
def membershipPairs (I : SetSystemInput) : List (Nat × Nat) :=
  membershipPairsFrom 0 I.sets

theorem membershipPairsFrom_length (start : Nat) (sets : List (List Nat)) :
    (membershipPairsFrom start sets).length = (sets.map List.length).sum := by
  induction sets generalizing start with
  | nil =>
      simp [membershipPairsFrom]
  | cons S sets ih =>
      simp [membershipPairsFrom, ih]

theorem membershipPairs_length_eq (I : SetSystemInput) :
    (membershipPairs I).length = (I.sets.map List.length).sum := by
  simp [membershipPairs, membershipPairsFrom_length]

/-- Count source-generated relation tuples in the set-system incidence carrier. -/
def setSystemIRTupleCount (I : SetSystemInput) : Nat :=
  (membershipPairs I).length

theorem mem_membershipPairsFrom_right_lt
    {start : Nat} {sets : List (List Nat)} {p : Nat × Nat}
    (h : p ∈ membershipPairsFrom start sets) :
    p.2 < start + sets.length := by
  induction sets generalizing start with
  | nil =>
      simp [membershipPairsFrom] at h
  | cons S sets ih =>
      simp only [membershipPairsFrom, List.mem_append, List.mem_map] at h
      rcases h with h | h
      · rcases h with ⟨x, _hx, hpair⟩
        cases hpair
        simp
      · have hTail := ih h
        simp at hTail ⊢
        omega

theorem mem_membershipPairsFrom_left_mem
    {start : Nat} {sets : List (List Nat)} {p : Nat × Nat}
    (h : p ∈ membershipPairsFrom start sets) :
    ∃ S ∈ sets, p.1 ∈ S := by
  induction sets generalizing start with
  | nil =>
      simp [membershipPairsFrom] at h
  | cons S sets ih =>
      simp only [membershipPairsFrom, List.mem_append, List.mem_map] at h
      rcases h with h | h
      · rcases h with ⟨x, hx, hpair⟩
        cases hpair
        exact ⟨S, by simp, hx⟩
      · rcases ih h with ⟨T, hT, hpT⟩
        exact ⟨T, by simp [hT], hpT⟩

theorem membershipPairs_bounds {I : SetSystemInput}
    (hI : SetSystemWellFormed I) :
    ∀ p ∈ membershipPairs I, p.1 < I.universeSize ∧ p.2 < I.sets.length := by
  intro p hp
  constructor
  · rcases mem_membershipPairsFrom_left_mem (start := 0) hp with ⟨S, hS, hxS⟩
    exact hI S hS p.1 hxS
  · simpa [membershipPairs] using mem_membershipPairsFrom_right_lt (start := 0) hp

theorem mem_membershipPairsFrom_iff
    {start : Nat} {sets : List (List Nat)} {x j : Nat} :
    (x, j) ∈ membershipPairsFrom start sets ↔
      ∃ k S, sets[k]? = some S ∧ x ∈ S ∧ j = start + k := by
  induction sets generalizing start with
  | nil =>
      simp [membershipPairsFrom]
  | cons S sets ih =>
      constructor
      · intro h
        simp only [membershipPairsFrom, List.mem_append, List.mem_map] at h
        rcases h with h | h
        · rcases h with ⟨y, hy, hpair⟩
          cases hpair
          exact ⟨0, S, by simp, hy, by simp⟩
        · rcases (ih (start := start + 1)).mp h with ⟨k, T, hT, hxT, hj⟩
          refine ⟨k + 1, T, by simpa using hT, hxT, ?_⟩
          omega
      · rintro ⟨k, T, hT, hxT, hj⟩
        cases k with
        | zero =>
            simp at hT
            cases hT
            simp [membershipPairsFrom, hxT, hj]
        | succ k =>
            simp at hT
            simp only [membershipPairsFrom, List.mem_append, List.mem_map]
            right
            exact (ih (start := start + 1)).mpr ⟨k, T, hT, hxT, by omega⟩

/-- Source-side index predicate: element `x` belongs to set-family entry `j`. -/
def IndexedMembership (I : SetSystemInput) (x j : Nat) : Prop :=
  ∃ S, I.sets[j]? = some S ∧ x ∈ S

theorem mem_membershipPairs_iff {I : SetSystemInput} {x j : Nat} :
    (x, j) ∈ membershipPairs I ↔ IndexedMembership I x j := by
  constructor
  · intro h
    rcases (mem_membershipPairsFrom_iff (start := 0)
      (sets := I.sets) (x := x) (j := j)).mp h with ⟨k, S, hS, hxS, hj⟩
    simp at hj
    cases hj
    exact ⟨S, hS, hxS⟩
  · rintro ⟨S, hS, hxS⟩
    exact (mem_membershipPairsFrom_iff (start := 0)
      (sets := I.sets) (x := x) (j := j)).mpr ⟨j, S, hS, hxS, by simp⟩

theorem pairTuple_mem_relTuplesOfPairs_iff {pairs : List (Nat × Nat)} {x j : Nat} :
    [x, j] ∈ relTuplesOfPairs pairs ↔ (x, j) ∈ pairs := by
  rw [relTuplesOfPairs]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨p, hp, htuple⟩
    cases p with
    | mk a b =>
        simp at htuple
        rcases htuple with ⟨rfl, rfl⟩
        exact hp
  · intro h
    exact List.mem_map.mpr ⟨(x, j), h, rfl⟩

/-- Normalized incidence carrier for a set system. -/
def setSystemIR (I : SetSystemInput) : UniversalRelIR :=
  binaryRelationIR I.universeSize I.sets.length (membershipPairs I)

/-- The set-system carrier contains exactly the generated incidence tuple family. -/
theorem setSystemIR_relTuples_eq (I : SetSystemInput) :
    (setSystemIR I).relTuples = [relTuplesOfPairs (membershipPairs I)] :=
  rfl

/-- The set-system carrier relation-family length is the generated membership-pair count. -/
theorem setSystemIR_relTuples_lengths_eq (I : SetSystemInput) :
    ((setSystemIR I).relTuples.map List.length) = [(membershipPairs I).length] := by
  simp [setSystemIR, binaryRelationIR]

/-- Total relation tuples in the set-system carrier match the generated membership pairs. -/
theorem setSystemIR_tupleCount_eq_membershipPairs (I : SetSystemInput) :
    ((setSystemIR I).relTuples.map List.length).sum = (membershipPairs I).length := by
  simp [setSystemIR, binaryRelationIR]

/--
The set-system source-to-view construction contains exactly the generated
element/set-index membership tuples.
-/
theorem setSystemIR_tupleCount_eq (I : SetSystemInput) :
    ((setSystemIR I).relTuples.map List.length).sum = (I.sets.map List.length).sum := by
  simp [setSystemIR, binaryRelationIR, membershipPairs_length_eq]

/-- Incidence view over `setSystemIR`: sort 0 is elements, sort 1 is set indices. -/
def setSystemIncidenceView (I : SetSystemInput) : IncidenceView (setSystemIR I) where
  leftSort := 0
  rightSort := 1
  memRel := 0
  left_wf := by simp [setSystemIR, binaryRelationIR, UniversalRelIR.SortWF,
    UniversalRelIR.numSorts]
  right_wf := by simp [setSystemIR, binaryRelationIR, UniversalRelIR.SortWF,
    UniversalRelIR.numSorts]
  mem_sig := by simp [setSystemIR, binaryRelationIR, UniversalRelIR.relSig?]

theorem setSystemIR_wellFormed {I : SetSystemInput}
    (hI : SetSystemWellFormed I) :
    (setSystemIR I).WellFormed :=
  binaryRelationIR_wellFormed (membershipPairs_bounds hI)

theorem setSystemIncidenceView_mem_iff {I : SetSystemInput} {x j : Nat} :
    (setSystemIncidenceView I).Mem x j ↔ IndexedMembership I x j := by
  unfold IncidenceView.Mem UniversalRelIR.RelHolds setSystemIncidenceView setSystemIR
  simp [binaryRelationIR, pairTuple_mem_relTuplesOfPairs_iff, mem_membershipPairs_iff]

/--
Index-based exact cover predicate for set systems.  This is the predicate that
matches the normalized IR view even when duplicate set values occur.
-/
def ExactCoverIndexPredicate (I : SetSystemInput) (selected : List ObjId) : Prop :=
  selected.Nodup ∧
    (∀ j ∈ selected, j < I.sets.length) ∧
    ∀ x, x < I.universeSize →
      ∃ j ∈ selected,
        IndexedMembership I x j ∧
          ∀ j' ∈ selected, IndexedMembership I x j' → j' = j

/-- Existential index-based exact cover predicate. -/
def ExistsExactCoverIndex (I : SetSystemInput) : Prop :=
  ∃ selected, ExactCoverIndexPredicate I selected

theorem exactCoverIndexPredicate_iff_incidence
    (I : SetSystemInput) (selected : List ObjId) :
    ExactCoverIndexPredicate I selected ↔
      (setSystemIncidenceView I).ExactCoverPredicate selected := by
  constructor
  · rintro ⟨hNodup, hRight, hCover⟩
    refine ⟨hNodup, ?_, ?_⟩
    · intro j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hRight j hj
    · intro x hx
      have hxBound : x < I.universeSize := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      rcases hCover x hxBound with ⟨j, hj, hmem, huniq⟩
      exact ⟨j, hj, (setSystemIncidenceView_mem_iff).mpr hmem, by
        intro j' hj' hmem'
        exact huniq j' hj' ((setSystemIncidenceView_mem_iff).mp hmem')⟩
  · rintro ⟨hNodup, hRight, hCover⟩
    refine ⟨hNodup, ?_, ?_⟩
    · intro j hj
      have hjObj := hRight j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hjObj
    · intro x hx
      have hxObj : x ∈ (setSystemIncidenceView I).LeftObjects := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      rcases hCover x hxObj with ⟨j, hj, hmem, huniq⟩
      exact ⟨j, hj, (setSystemIncidenceView_mem_iff).mp hmem, by
        intro j' hj' hmem'
        exact huniq j' hj' ((setSystemIncidenceView_mem_iff).mpr hmem')⟩

theorem existsExactCoverIndex_iff_incidence (I : SetSystemInput) :
    ExistsExactCoverIndex I ↔
      IncidenceView.ExistsExactCover (setSystemIncidenceView I) := by
  constructor
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (exactCoverIndexPredicate_iff_incidence I selected).mp hselected⟩
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (exactCoverIndexPredicate_iff_incidence I selected).mpr hselected⟩

/--
Index-based set-covering predicate for set systems.  Unlike set packing, the
source semantics tolerate duplicate selected set values, so no extra
injectivity side condition is needed.
-/
def SetCoveringIndexPredicate (I : SetSystemInput) (k : Nat) (selected : List ObjId) : Prop :=
  selected.length ≤ k ∧
    (∀ j ∈ selected, j < I.sets.length) ∧
    ∀ x, x < I.universeSize → ∃ j ∈ selected, IndexedMembership I x j

/-- Existential index-based set-covering predicate. -/
def ExistsSetCoveringIndex (I : SetSystemInput) (k : Nat) : Prop :=
  ∃ selected, SetCoveringIndexPredicate I k selected

theorem setCoveringIndexPredicate_iff_incidence
    (I : SetSystemInput) (k : Nat) (selected : List ObjId) :
    SetCoveringIndexPredicate I k selected ↔
      (setSystemIncidenceView I).SetCoveringPredicate k selected := by
  constructor
  · rintro ⟨hLen, hRight, hCover⟩
    refine ⟨hLen, ?_, ?_⟩
    · intro j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hRight j hj
    · intro x hx
      have hxBound : x < I.universeSize := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      rcases hCover x hxBound with ⟨j, hj, hmem⟩
      exact ⟨j, hj, (setSystemIncidenceView_mem_iff).mpr hmem⟩
  · rintro ⟨hLen, hRight, hCover⟩
    refine ⟨hLen, ?_, ?_⟩
    · intro j hj
      have hjObj := hRight j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hjObj
    · intro x hx
      have hxObj : x ∈ (setSystemIncidenceView I).LeftObjects := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      rcases hCover x hxObj with ⟨j, hj, hmem⟩
      exact ⟨j, hj, (setSystemIncidenceView_mem_iff).mp hmem⟩

theorem existsSetCoveringIndex_iff_incidence (I : SetSystemInput) (k : Nat) :
    ExistsSetCoveringIndex I k ↔
      IncidenceView.ExistsSetCovering (setSystemIncidenceView I) k := by
  constructor
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (setCoveringIndexPredicate_iff_incidence I k selected).mp hselected⟩
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (setCoveringIndexPredicate_iff_incidence I k selected).mpr hselected⟩

theorem setCoveringIndexPredicate_of_source
    {I : SetCoveringInput} {selected : List (List Nat)}
    (hLen : selected.length ≤ I.k)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hCover : CoversUniverse I.system selected) :
    SetCoveringIndexPredicate I.system I.k (selected.map I.system.sets.idxOf) := by
  refine ⟨by simpa, ?_, ?_⟩
  · intro j hj
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  · intro x hx
    rcases hCover x hx with ⟨S, hS, hxS⟩
    exact ⟨I.system.sets.idxOf S, List.mem_map.mpr ⟨S, hS, rfl⟩,
      ⟨S, List.getElem?_idxOf (hFamily S hS), hxS⟩⟩

theorem setCoveringIndexPredicate_to_setCovering
    {I : SetCoveringInput} {selected : List ObjId}
    (hSelected : SetCoveringIndexPredicate I.system I.k selected) :
    SetCovering I := by
  rcases hSelected with ⟨hLen, hRight, hCover⟩
  refine ⟨selected.map (fun j => I.system.sets.getD j []), by simpa, ?_, ?_⟩
  · intro S hS
    rcases List.mem_map.mp hS with ⟨j, hj, rfl⟩
    have hjBound : j < I.system.sets.length := hRight j hj
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := j) hjBound]
    exact List.getElem_mem (l := I.system.sets) (n := j) hjBound
  · intro x hx
    rcases hCover x hx with ⟨j, hj, hmem⟩
    rcases hmem with ⟨S, hS, hxS⟩
    rcases List.getElem?_eq_some_iff.mp hS with ⟨hjBound, hEq⟩
    refine ⟨I.system.sets.getD j [], List.mem_map.mpr ⟨j, hj, rfl⟩, ?_⟩
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := j) hjBound, hEq]
    exact hxS

theorem setCovering_to_existsSetCoveringIndex (I : SetCoveringInput) :
    SetCovering I → ExistsSetCoveringIndex I.system I.k := by
  rintro ⟨selected, hLen, hFamily, hCover⟩
  exact ⟨selected.map I.system.sets.idxOf,
    setCoveringIndexPredicate_of_source hLen hFamily hCover⟩

/--
Set covering admits an honest index-based bridge on the normalized incidence
carrier: collapsing duplicate selected set values through `idxOf` is harmless
because duplicates neither improve nor invalidate the cover predicate.
-/
theorem setCovering_iff_existsSetCoveringIndex (I : SetCoveringInput) :
    SetCovering I ↔ ExistsSetCoveringIndex I.system I.k := by
  constructor
  · exact setCovering_to_existsSetCoveringIndex I
  · rintro ⟨selected, hSelected⟩
    exact setCoveringIndexPredicate_to_setCovering hSelected

theorem setCovering_iff_incidence (I : SetCoveringInput) :
    SetCovering I ↔
      IncidenceView.ExistsSetCovering (setSystemIncidenceView I.system) I.k := by
  exact (setCovering_iff_existsSetCoveringIndex I).trans
    (existsSetCoveringIndex_iff_incidence I.system I.k)

/--
Index-based hitting-set predicate for set systems.  Selected values are universe
elements, i.e. left objects of the normalized incidence view.
-/
def HittingSetIndexPredicate (I : SetSystemInput) (k : Nat) (selected : List ObjId) : Prop :=
  selected.length ≤ k ∧
    (∀ x ∈ selected, x < I.universeSize) ∧
    ∀ j, j < I.sets.length → ∃ x ∈ selected, IndexedMembership I x j

/-- Existential index-based hitting-set predicate. -/
def ExistsHittingSetIndex (I : SetSystemInput) (k : Nat) : Prop :=
  ∃ selected, HittingSetIndexPredicate I k selected

theorem hittingSetIndexPredicate_iff_incidence
    (I : SetSystemInput) (k : Nat) (selected : List ObjId) :
    HittingSetIndexPredicate I k selected ↔
      (setSystemIncidenceView I).HittingSetPredicate k selected := by
  constructor
  · rintro ⟨hLen, hLeft, hHits⟩
    refine ⟨hLen, ?_, ?_⟩
    · intro x hx
      simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hLeft x hx
    · intro j hj
      have hjBound : j < I.sets.length := by
        simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hj
      rcases hHits j hjBound with ⟨x, hx, hmem⟩
      exact ⟨x, hx, (setSystemIncidenceView_mem_iff).mpr hmem⟩
  · rintro ⟨hLen, hLeft, hHits⟩
    refine ⟨hLen, ?_, ?_⟩
    · intro x hx
      have hxObj := hLeft x hx
      simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hxObj
    · intro j hj
      have hjObj : j ∈ (setSystemIncidenceView I).RightObjects := by
        simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hj
      rcases hHits j hjObj with ⟨x, hx, hmem⟩
      exact ⟨x, hx, (setSystemIncidenceView_mem_iff).mp hmem⟩

theorem existsHittingSetIndex_iff_incidence (I : SetSystemInput) (k : Nat) :
    ExistsHittingSetIndex I k ↔
      IncidenceView.ExistsHittingSet (setSystemIncidenceView I) k := by
  constructor
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (hittingSetIndexPredicate_iff_incidence I k selected).mp hselected⟩
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (hittingSetIndexPredicate_iff_incidence I k selected).mpr hselected⟩

theorem hittingSetIndexPredicate_of_source
    {I : HittingSetInput} {selected : List Nat}
    (hLen : selected.length ≤ I.k)
    (hBounds : ∀ x ∈ selected, x < I.system.universeSize)
    (hHits : HitsEverySet I.system selected) :
    HittingSetIndexPredicate I.system I.k selected := by
  refine ⟨hLen, hBounds, ?_⟩
  intro j hj
  have hSetMem : I.system.sets.getD j [] ∈ I.system.sets := by
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := j) hj]
    exact List.getElem_mem (l := I.system.sets) (n := j) hj
  rcases hHits (I.system.sets.getD j []) hSetMem with ⟨x, hx, hxSet⟩
  refine ⟨x, hx, ?_⟩
  rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := j) hj] at hxSet
  exact ⟨I.system.sets[j], List.getElem?_eq_getElem hj, hxSet⟩

theorem hittingSetIndexPredicate_to_hittingSet
    {I : HittingSetInput} {selected : List ObjId}
    (hSelected : HittingSetIndexPredicate I.system I.k selected) :
    HittingSet I := by
  rcases hSelected with ⟨hLen, hBounds, hHits⟩
  refine ⟨selected, hLen, hBounds, ?_⟩
  intro S hS
  rcases List.mem_iff_getElem?.mp hS with ⟨j, hget⟩
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hj, hS_eq⟩
  rcases hHits j hj with ⟨x, hx, hmem⟩
  rcases hmem with ⟨T, hT, hxT⟩
  have hT_eq : T = S := by
    have hSome : some T = some S := by
      simpa [hT] using hget
    exact Option.some.inj hSome
  exact ⟨x, hx, by simpa [hT_eq] using hxT⟩

theorem hittingSet_to_existsHittingSetIndex (I : HittingSetInput) :
    HittingSet I → ExistsHittingSetIndex I.system I.k := by
  rintro ⟨selected, hLen, hBounds, hHits⟩
  exact ⟨selected, hittingSetIndexPredicate_of_source hLen hBounds hHits⟩

theorem hittingSet_iff_existsHittingSetIndex (I : HittingSetInput) :
    HittingSet I ↔ ExistsHittingSetIndex I.system I.k := by
  constructor
  · exact hittingSet_to_existsHittingSetIndex I
  · rintro ⟨selected, hSelected⟩
    exact hittingSetIndexPredicate_to_hittingSet hSelected

theorem hittingSet_iff_incidence (I : HittingSetInput) :
    HittingSet I ↔
      IncidenceView.ExistsHittingSet (setSystemIncidenceView I.system) I.k := by
  exact (hittingSet_iff_existsHittingSetIndex I).trans
    (existsHittingSetIndex_iff_incidence I.system I.k)

/--
Index-based set-packing predicate for set systems, restricted to in-universe
elements seen by the normalized incidence view.
-/
def SetPackingIndexPredicate (I : SetSystemInput) (k : Nat) (selected : List ObjId) : Prop :=
  selected.length ≥ k ∧
    selected.Nodup ∧
    (∀ j ∈ selected, j < I.sets.length) ∧
    ∀ x, x < I.universeSize →
      ∀ j ∈ selected, ∀ j' ∈ selected,
        IndexedMembership I x j → IndexedMembership I x j' → j = j'

/-- Existential index-based set-packing predicate. -/
def ExistsSetPackingIndex (I : SetSystemInput) (k : Nat) : Prop :=
  ∃ selected, SetPackingIndexPredicate I k selected

theorem setPackingIndexPredicate_iff_incidence
    (I : SetSystemInput) (k : Nat) (selected : List ObjId) :
    SetPackingIndexPredicate I k selected ↔
      (setSystemIncidenceView I).SetPackingPredicate k selected := by
  constructor
  · rintro ⟨hLen, hNodup, hRight, hPack⟩
    refine ⟨hLen, hNodup, ?_, ?_⟩
    · intro j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hRight j hj
    · intro x hx j hj j' hj' hmem hmem'
      have hxBound : x < I.universeSize := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      exact hPack x hxBound j hj j' hj'
        ((setSystemIncidenceView_mem_iff).mp hmem)
        ((setSystemIncidenceView_mem_iff).mp hmem')
  · rintro ⟨hLen, hNodup, hRight, hPack⟩
    refine ⟨hLen, hNodup, ?_, ?_⟩
    · intro j hj
      have hjObj := hRight j hj
      simpa [IncidenceView.RightObjects, setSystemIncidenceView, setSystemIR,
        binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
        UniversalRelIR.sortSize?] using hjObj
    · intro x hx j hj j' hj' hmem hmem'
      have hxObj : x ∈ (setSystemIncidenceView I).LeftObjects := by
        simpa [IncidenceView.LeftObjects, setSystemIncidenceView, setSystemIR,
          binaryRelationIR, UniversalRelIR.objectsOfSort, UniversalRelIR.ObjWF,
          UniversalRelIR.sortSize?] using hx
      exact hPack x hxObj j hj j' hj'
        ((setSystemIncidenceView_mem_iff).mpr hmem)
        ((setSystemIncidenceView_mem_iff).mpr hmem')

theorem existsSetPackingIndex_iff_incidence (I : SetSystemInput) (k : Nat) :
    ExistsSetPackingIndex I k ↔
      IncidenceView.ExistsSetPacking (setSystemIncidenceView I) k := by
  constructor
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (setPackingIndexPredicate_iff_incidence I k selected).mp hselected⟩
  · rintro ⟨selected, hselected⟩
    exact ⟨selected, (setPackingIndexPredicate_iff_incidence I k selected).mpr hselected⟩

theorem idxOf_inj_of_mem_family {I : SetSystemInput} {A B : List Nat}
    (hA : A ∈ I.sets) (hB : B ∈ I.sets)
    (hIdx : I.sets.idxOf A = I.sets.idxOf B) :
    A = B := by
  have hgetA := List.getElem?_idxOf hA
  have hgetB := List.getElem?_idxOf hB
  have hsome : some A = some B := by
    rw [← hgetA, ← hgetB, hIdx]
  exact Option.some.inj hsome

/-- Decode a selected list of family indices back to source set values using `getD`. -/
def selectedSetValues (I : SetSystemInput) (selected : List ObjId) : List (List Nat) :=
  selected.map fun j => I.sets.getD j []

/--
Localized duplicate/index semantic side condition: decoding selected indices back
to source set values is injective on the selected subfamily.
-/
def selectedSetValuesInjective (I : SetSystemInput) (selected : List ObjId) : Prop :=
  ∀ ⦃j j'⦄, j ∈ selected → j' ∈ selected →
    I.sets.getD j [] = I.sets.getD j' [] → j = j'

/--
Strengthened set-packing source-side predicate: the selected family indices
satisfy the incidence-side packing condition and decode injectively back to
source set values.

The extra value-injectivity side condition is what rules out false positives
from duplicate empty-set entries, which the bare incidence predicate cannot
distinguish.
-/
def SetPackingIndexValueInjectivePredicate
    (I : SetSystemInput) (k : Nat) (selected : List ObjId) : Prop :=
  SetPackingIndexPredicate I k selected ∧
    selectedSetValuesInjective I selected

/-- Existential strengthened set-packing source-side predicate. -/
def ExistsSetPackingIndexValueInjective
    (I : SetSystemInput) (k : Nat) : Prop :=
  ∃ selected, SetPackingIndexValueInjectivePredicate I k selected

theorem setPackingIndexValueInjectivePredicate_iff_incidence
    (I : SetSystemInput) (k : Nat) (selected : List ObjId) :
    SetPackingIndexValueInjectivePredicate I k selected ↔
      (setSystemIncidenceView I).SetPackingPredicate k selected ∧
        selectedSetValuesInjective I selected := by
  constructor
  · rintro ⟨hPack, hInj⟩
    exact ⟨(setPackingIndexPredicate_iff_incidence I k selected).mp hPack, hInj⟩
  · rintro ⟨hPack, hInj⟩
    exact ⟨(setPackingIndexPredicate_iff_incidence I k selected).mpr hPack, hInj⟩

theorem existsSetPackingIndexValueInjective_iff_incidence
    (I : SetSystemInput) (k : Nat) :
    ExistsSetPackingIndexValueInjective I k ↔
      ∃ selected,
        (setSystemIncidenceView I).SetPackingPredicate k selected ∧
          selectedSetValuesInjective I selected := by
  constructor
  · rintro ⟨selected, hselected⟩
    exact ⟨selected,
      (setPackingIndexValueInjectivePredicate_iff_incidence I k selected).mp hselected⟩
  · rintro ⟨selected, hselected⟩
    exact ⟨selected,
      (setPackingIndexValueInjectivePredicate_iff_incidence I k selected).mpr hselected⟩

theorem selectedSetValues_mem_family {I : SetSystemInput} {selected : List ObjId}
    (hRight : ∀ j ∈ selected, j < I.sets.length) :
    ∀ S ∈ selectedSetValues I selected, IsSetInFamily I S := by
  intro S hS
  rcases List.mem_map.mp hS with ⟨j, hj, rfl⟩
  have hjBound : j < I.sets.length := hRight j hj
  rw [List.getD_eq_getElem (l := I.sets) (d := []) (n := j) hjBound]
  exact List.getElem_mem (l := I.sets) (n := j) hjBound

theorem selectedSetValues_nodup_of_injective
    {I : SetSystemInput} {selected : List ObjId}
    (hNodup : selected.Nodup)
    (hInj : selectedSetValuesInjective I selected) :
    (selectedSetValues I selected).Nodup := by
  have hAux :
      ∀ {xs : List ObjId},
        xs.Nodup →
        selectedSetValuesInjective I xs →
        (selectedSetValues I xs).Nodup := by
    intro xs hNodupXs hInjXs
    induction xs with
    | nil =>
        simp [selectedSetValues]
    | cons j js ih =>
        have hNodupCons := List.nodup_cons.mp hNodupXs
        rw [selectedSetValues]
        simp only [List.map]
        simp only [List.nodup_cons]
        constructor
        · intro hMem
          rcases List.mem_map.mp hMem with ⟨j', hj', hEq⟩
          have hjEq : j = j' := hInjXs (by simp) (by simp [hj']) hEq.symm
          exact hNodupCons.1 (by simpa [hjEq] using hj')
        · exact ih hNodupCons.2 (by
            intro j j' hj hj' hEq
            exact hInjXs (by simp [hj]) (by simp [hj']) hEq)
  exact hAux hNodup hInj

theorem setPackingIndexPredicate_of_source
    {I : SetPackingInput} {selected : List (List Nat)}
    (hLen : selected.length ≥ I.k)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    SetPackingIndexPredicate I.system I.k (selected.map I.system.sets.idxOf) := by
  refine ⟨by simpa, ?_, ?_, ?_⟩
  · have hAux :
        ∀ {xs : List (List Nat)},
          (∀ S ∈ xs, IsSetInFamily I.system S) →
          xs.Nodup →
          (xs.map I.system.sets.idxOf).Nodup := by
      intro xs hFamilyXs hNodupXs
      induction xs with
      | nil =>
          simp
      | cons S xs ih =>
          have hNodupCons := List.nodup_cons.mp hNodupXs
          have hFamilyTail : ∀ T ∈ xs, IsSetInFamily I.system T := by
            intro T hT
            exact hFamilyXs T (by simp [hT])
          rw [List.map]
          simp only [List.nodup_cons]
          constructor
          · intro hMem
            rcases List.mem_map.mp hMem with ⟨T, hT, hIdx⟩
            have hST : S = T :=
              idxOf_inj_of_mem_family (hFamilyXs S (by simp)) (hFamilyTail T hT) hIdx.symm
            exact hNodupCons.1 (by simpa [hST] using hT)
          · exact ih hFamilyTail hNodupCons.2
    exact hAux hFamily hNodup
  · intro j hj
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  · intro x _hx j hj j' hj' hmem hmem'
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    rcases List.mem_map.mp hj' with ⟨T, hT, rfl⟩
    rcases hmem with ⟨U, hU, hxU⟩
    rcases hmem' with ⟨W, hW, hxW⟩
    have hSget := List.getElem?_idxOf (hFamily S hS)
    have hTget := List.getElem?_idxOf (hFamily T hT)
    have hUS : U = S := by
      have hSome : some U = some S := by
        simpa [hU] using hSget
      exact Option.some.inj hSome
    have hWT : W = T := by
      have hSome : some W = some T := by
        simpa [hW] using hTget
      exact Option.some.inj hSome
    subst U W
    have hST : S = T := by
      by_contra hne
      exact hDisjoint S hS T hT hne x hxU hxW
    subst T
    rfl

theorem setPacking_to_existsSetPackingIndex (I : SetPackingInput) :
    SetPacking I → ExistsSetPackingIndex I.system I.k := by
  rintro ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
  exact ⟨selected.map I.system.sets.idxOf,
    setPackingIndexPredicate_of_source hLen hFamily hNodup hDisjoint⟩

theorem setPacking_to_existsSetPackingIndexValueInjective (I : SetPackingInput) :
    SetPacking I → ExistsSetPackingIndexValueInjective I.system I.k := by
  rintro ⟨selected, hLen, hFamily, hNodup, hDisjoint⟩
  refine ⟨selected.map I.system.sets.idxOf,
    setPackingIndexPredicate_of_source hLen hFamily hNodup hDisjoint, ?_⟩
  intro j j' hj hj' hEq
  rcases List.mem_map.mp hj with ⟨A, hA, rfl⟩
  rcases List.mem_map.mp hj' with ⟨B, hB, rfl⟩
  have hAFamily : IsSetInFamily I.system A := hFamily A hA
  have hBFamily : IsSetInFamily I.system B := hFamily B hB
  have hAIdx : I.system.sets.idxOf A < I.system.sets.length :=
    List.idxOf_lt_length_iff.mpr hAFamily
  have hBIdx : I.system.sets.idxOf B < I.system.sets.length :=
    List.idxOf_lt_length_iff.mpr hBFamily
  have hAVal : I.system.sets.getD (I.system.sets.idxOf A) [] = A := by
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := I.system.sets.idxOf A) hAIdx]
    exact (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hAFamily)).2
  have hBVal : I.system.sets.getD (I.system.sets.idxOf B) [] = B := by
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (n := I.system.sets.idxOf B) hBIdx]
    exact (List.getElem?_eq_some_iff.mp (List.getElem?_idxOf hBFamily)).2
  have hAB : A = B := by
    calc
      A = I.system.sets.getD (I.system.sets.idxOf A) [] := hAVal.symm
      _ = I.system.sets.getD (I.system.sets.idxOf B) [] := hEq
      _ = B := hBVal
  simp [hAB]

theorem setPackingIndexPredicate_selectedSetValues_pairwiseDisjoint
    {I : SetSystemInput} {k : Nat} {selected : List ObjId}
    (hI : SetSystemWellFormed I)
    (hSelected : SetPackingIndexPredicate I k selected) :
    PairwiseDisjointFamily (selectedSetValues I selected) := by
  rcases hSelected with ⟨_hLen, _hNodup, hRight, hPack⟩
  intro A hA B hB hAB x hxA hxB
  rcases List.mem_map.mp hA with ⟨j, hj, rfl⟩
  rcases List.mem_map.mp hB with ⟨j', hj', rfl⟩
  have hjBound : j < I.sets.length := hRight j hj
  have hj'Bound : j' < I.sets.length := hRight j' hj'
  have hxj : x ∈ I.sets[j] := by
    simpa [List.getElem?_eq_getElem hjBound] using hxA
  have hxj' : x ∈ I.sets[j'] := by
    simpa [List.getElem?_eq_getElem hj'Bound] using hxB
  have hxBound : x < I.universeSize := by
    exact hI I.sets[j] (List.getElem_mem (l := I.sets) (n := j) hjBound) x hxj
  have hmemj : IndexedMembership I x j := ⟨I.sets[j], List.getElem?_eq_getElem hjBound, hxj⟩
  have hmemj' : IndexedMembership I x j' :=
    ⟨I.sets[j'], List.getElem?_eq_getElem hj'Bound, hxj'⟩
  have hEq : j = j' := hPack x hxBound j hj j' hj' hmemj hmemj'
  exact hAB (by simp [hEq])

/--
Converse helper for the set-packing source bridge.  The remaining source-side
blocker is now isolated to two explicit assumptions:
well-formedness and injective decoding of selected indices back to source sets.
-/
theorem setPackingIndexPredicate_to_setPacking_of_wellFormed_of_valuesInjective
    {I : SetPackingInput} {selected : List ObjId}
    (hI : SetSystemWellFormed I.system)
    (hSelected : SetPackingIndexPredicate I.system I.k selected)
    (hInj : selectedSetValuesInjective I.system selected) :
    SetPacking I := by
  rcases hSelected with ⟨hLen, hNodup, hRight, hPack⟩
  refine ⟨selectedSetValues I.system selected, ?_, ?_, ?_, ?_⟩
  · simpa [selectedSetValues] using hLen
  · exact selectedSetValues_mem_family hRight
  · exact selectedSetValues_nodup_of_injective hNodup hInj
  · exact setPackingIndexPredicate_selectedSetValues_pairwiseDisjoint hI
      ⟨hLen, hNodup, hRight, hPack⟩

theorem setPacking_iff_existsSetPackingIndexValueInjective
    (I : SetPackingInput) (hI : SetSystemWellFormed I.system) :
    SetPacking I ↔ ExistsSetPackingIndexValueInjective I.system I.k := by
  constructor
  · exact setPacking_to_existsSetPackingIndexValueInjective I
  · rintro ⟨selected, hSelected, hInj⟩
    exact setPackingIndexPredicate_to_setPacking_of_wellFormed_of_valuesInjective
      hI hSelected hInj

end SetSystem

export SetSystem
  (membershipPairsFrom membershipPairs IndexedMembership ExactCoverIndexPredicate
    ExistsExactCoverIndex SetCoveringIndexPredicate ExistsSetCoveringIndex
    HittingSetIndexPredicate ExistsHittingSetIndex
    SetPackingIndexPredicate ExistsSetPackingIndex
    SetPackingIndexValueInjectivePredicate ExistsSetPackingIndexValueInjective
    idxOf_inj_of_mem_family selectedSetValues selectedSetValuesInjective
    setSystemIR setSystemIncidenceView setSystemIR_wellFormed
    membershipPairsFrom_length membershipPairs_length_eq setSystemIRTupleCount
    setSystemIR_relTuples_eq setSystemIR_relTuples_lengths_eq
    setSystemIR_tupleCount_eq_membershipPairs setSystemIR_tupleCount_eq
    setSystemIncidenceView_mem_iff exactCoverIndexPredicate_iff_incidence
    existsExactCoverIndex_iff_incidence setCoveringIndexPredicate_iff_incidence
    existsSetCoveringIndex_iff_incidence setCoveringIndexPredicate_of_source
    setCovering_to_existsSetCoveringIndex setCoveringIndexPredicate_to_setCovering
    setCovering_iff_existsSetCoveringIndex setCovering_iff_incidence
    hittingSetIndexPredicate_iff_incidence existsHittingSetIndex_iff_incidence
    hittingSetIndexPredicate_of_source hittingSetIndexPredicate_to_hittingSet
    hittingSet_to_existsHittingSetIndex hittingSet_iff_existsHittingSetIndex
    hittingSet_iff_incidence
    setPackingIndexPredicate_iff_incidence
    existsSetPackingIndex_iff_incidence
    setPackingIndexValueInjectivePredicate_iff_incidence
    existsSetPackingIndexValueInjective_iff_incidence
    selectedSetValues_mem_family
    selectedSetValues_nodup_of_injective setPackingIndexPredicate_of_source
    setPacking_to_existsSetPackingIndex
    setPacking_to_existsSetPackingIndexValueInjective
    setPackingIndexPredicate_selectedSetValues_pairwiseDisjoint
    setPackingIndexPredicate_to_setPacking_of_wellFormed_of_valuesInjective
    setPacking_iff_existsSetPackingIndexValueInjective)

end ComplexityReduction
