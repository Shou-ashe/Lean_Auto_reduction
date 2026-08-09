import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching.Part2

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching
open ComplexityReduction.Combinatorics

theorem compactSelectedTriples_x_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hEvery : compactEveryElementOccurs I) :
    ((compactSelectedTriples I selected).map fun t => t.1).Nodup := by
  have hCover := compactSelectedCoverTriples_x_nodup
    (I := I) (selected := selected) hFamily hNodup hDisjoint
  have hFiller := compactSelectedFillerTriples_x_nodup I selected
  have hDisj :
      List.Disjoint
        ((compactSelectedCoverTriples I selected).map fun t => t.1)
        ((compactSelectedFillerTriples I selected).map fun t => t.1) := by
    intro c hcCover hcFiller
    have hcAlpha : c ∈ compactAlphaCodes I := by
      apply compactSelectedAlphaCodes_subset_alphaCodes (I := I) (selected := selected)
      rwa [← compactSelectedCoverTriples_x_eq_alphaCodes (I := I) hFamily]
    have hcNonAlpha : c ∈ compactNonAlphaCodes I :=
      compactSelectedFillerTriples_x_subset_nonAlpha I selected hcFiller
    exact compactAlphaCodes_disjoint_nonAlphaCodes_of_everyElementOccurs
      (I := I) hEvery hcAlpha hcNonAlpha
  simpa [compactSelectedTriples, List.map_append] using
    List.Nodup.append hCover hFiller hDisj

theorem compactSelectedTriples_y_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    ((compactSelectedTriples I selected).map fun t => t.2.1).Nodup := by
  have hCover := compactSelectedCoverTriples_y_nodup
    (I := I) (selected := selected) hFamily hNodup
  have hFiller := compactSelectedFillerTriples_y_nodup I selected
  have hDisj :
      List.Disjoint
        ((compactSelectedCoverTriples I selected).map fun t => t.2.1)
        ((compactSelectedFillerTriples I selected).map fun t => t.2.1) := by
    intro c hcCover hcFiller
    have hcSelected : c ∈ compactSelectedPositionCodes I selected := by
      rwa [← compactSelectedCoverTriples_y_eq_positions I selected]
    have hcUnselected : c ∈ compactUnselectedPositionCodes I selected :=
      compactSelectedFillerTriples_y_subset_unselected I selected hcFiller
    exact compactSelected_unselectedPositionCodes_disjoint I selected hcSelected hcUnselected
  simpa [compactSelectedTriples, List.map_append] using
    List.Nodup.append hCover hFiller hDisj

theorem compactSelectedTriples_z_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    ((compactSelectedTriples I selected).map fun t => t.2.2).Nodup := by
  have hCover := compactSelectedCoverTriples_z_nodup
    (I := I) (selected := selected) hFamily hNodup
  have hFiller := compactSelectedFillerTriples_z_nodup I selected
  have hDisj :
      List.Disjoint
        ((compactSelectedCoverTriples I selected).map fun t => t.2.2)
        ((compactSelectedFillerTriples I selected).map fun t => t.2.2) := by
    intro c hcCover hcFiller
    have hcSelected : c ∈ compactSelectedPositionCodes I selected := by
      rwa [← compactSelectedCoverTriples_z_eq_positions I selected]
    have hcNext :
        c ∈ (compactUnselectedPositionCodes I selected).map
          (compactDecodedNextCode I) :=
      compactSelectedFillerTriples_z_subset_nextCodes I selected hcFiller
    exact compactUnselected_nextCodes_disjoint_selected
      (I := I) (selected := selected) hFamily hcSelected hcNext
  simpa [compactSelectedTriples, List.map_append] using
    List.Nodup.append hCover hFiller hDisj

theorem disjointTriples_of_coordinate_nodup
    {triples : List (Nat × Nat × Nat)}
    (hx : (triples.map fun t => t.1).Nodup)
    (hy : (triples.map fun t => t.2.1).Nodup)
    (hz : (triples.map fun t => t.2.2).Nodup) :
    DisjointTriples triples := by
  intro a ha b hb hne
  have hxInj := List.inj_on_of_nodup_map hx
  have hyInj := List.inj_on_of_nodup_map hy
  have hzInj := List.inj_on_of_nodup_map hz
  exact ⟨fun h => hne (hxInj ha hb h),
    fun h => hne (hyInj ha hb h),
    fun h => hne (hzInj ha hb h)⟩

theorem compactSelectedTriples_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hEvery : compactEveryElementOccurs I) :
    (compactSelectedTriples I selected).Nodup := by
  exact List.Nodup.of_map (fun t : Nat × Nat × Nat => t.1)
    (compactSelectedTriples_x_nodup (I := I) (selected := selected)
      hFamily hNodup hDisjoint hEvery)

theorem compactSelectedTriples_disjointTriples {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hEvery : compactEveryElementOccurs I) :
    DisjointTriples (compactSelectedTriples I selected) := by
  exact disjointTriples_of_coordinate_nodup
    (compactSelectedTriples_x_nodup (I := I) (selected := selected)
      hFamily hNodup hDisjoint hEvery)
    (compactSelectedTriples_y_nodup (I := I) (selected := selected)
      hFamily hNodup)
    (compactSelectedTriples_z_nodup (I := I) (selected := selected)
      hFamily hNodup)

theorem compactSelectedCoverTriples_mem_compactTriples {I : ExactCoverInput}
    {selected : List (List Nat)} {t : Nat × Nat × Nat}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (ht : t ∈ compactSelectedCoverTriples I selected) :
    t ∈ compactTriples I := by
  rcases List.mem_flatMap.mp (by simpa [compactSelectedCoverTriples] using ht) with
    ⟨S, hSSelected, htS⟩
  have hIdx : compactSelectedSetIndex I S < I.system.sets.length :=
    compactSelectedSetIndex_lt_of_family (I := I) (hFamily S hSSelected)
  have htCover : t ∈ compactCoverTriples I := by
    exact List.mem_flatMap.mpr
      ⟨compactSelectedSetIndex I S, by simpa using hIdx,
        by simpa [compactSelectedCoverTriplesForSet] using htS⟩
  exact List.mem_append_left _ (by simpa [compactTriples] using htCover)

theorem compactSelectedFillerTriples_mem_compactTriples {I : ExactCoverInput}
    {selected : List (List Nat)} {t : Nat × Nat × Nat}
    (ht : t ∈ compactSelectedFillerTriples I selected) :
    t ∈ compactTriples I := by
  rcases mem_zipWith₂ (fun beta c => compactFillerTripleForCode I beta c) ht with
    ⟨beta, hbeta, c, hcUnselected, htEq⟩
  rcases (mem_compactUnselectedPositionCodes_iff I selected c).1 hcUnselected with
    ⟨hcPos, _hcNotSelected⟩
  have htFiller :
      t ∈ compactFillerTriples I := by
    rw [htEq]
    exact compactFillerTripleForCode_mem_filler (I := I) hbeta hcPos
  exact List.mem_append_right _ (by simpa [compactTriples] using htFiller)

theorem compactSelectedTriples_mem_and_bounds {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    ∀ t ∈ compactSelectedTriples I selected,
      t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t := by
  intro t ht
  rcases List.mem_append.mp (by simpa [compactSelectedTriples] using ht) with hCover | hFiller
  · have htCompact :=
      compactSelectedCoverTriples_mem_compactTriples (I := I)
        (selected := selected) hFamily hCover
    exact ⟨htCompact, compactTriple_withinBounds_of_mem (I := I) htCompact⟩
  · have htCompact :=
      compactSelectedFillerTriples_mem_compactTriples (I := I)
        (selected := selected) hFiller
    exact ⟨htCompact, compactTriple_withinBounds_of_mem (I := I) htCompact⟩

theorem compactEveryElementOccurs_of_cover {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hCovers : CoversUniverse I.system selected) :
    compactEveryElementOccurs I := by
  intro x hx
  rcases hCovers x hx with ⟨S, hSSelected, hxS⟩
  refine ⟨compactSelectedSetIndex I S,
    compactSelectedSetIndex_lt_of_family (I := I) (hFamily S hSSelected), ?_⟩
  have hSource :
      compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
    compactSourceSetAt_idxOf_eq (I := I) (S := S)
      (by simpa [IsSetInFamily] using hFamily S hSSelected)
  exact (mem_compactSupport_iff I (compactSourceSetAt I (compactSelectedSetIndex I S))
    x).2 ⟨hx, by simpa [hSource] using hxS⟩

theorem compactMapCore_threeDimensionalMatching_of_exact {I : ExactCoverInput}
    (hExact : ExactCover I) :
    ThreeDimensionalMatching (compactMapCore I) := by
  rcases hExact with ⟨_hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
  have hEvery : compactEveryElementOccurs I :=
    compactEveryElementOccurs_of_cover (I := I) (selected := selected) hFamily hCovers
  refine ⟨compactSelectedTriples I selected, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_of_eq
      (compactSelectedTriples_length_eq_k_of_exact
        (I := I) (selected := selected) hFamily hNodup hDisjoint hCovers hEvery).symm
  · exact compactSelectedTriples_mem_and_bounds
      (I := I) (selected := selected) hFamily
  · exact compactSelectedTriples_nodup
      (I := I) (selected := selected) hFamily hNodup hDisjoint hEvery
  · exact compactSelectedTriples_disjointTriples
      (I := I) (selected := selected) hFamily hNodup hDisjoint hEvery

theorem compactMap_threeDimensionalMatching_of_exact {I : ExactCoverInput}
    (hExact : ExactCover I) :
    ThreeDimensionalMatching (compactMap I) := by
  rcases hExact with ⟨hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
  have hEvery : compactEveryElementOccurs I :=
    compactEveryElementOccurs_of_cover (I := I) (selected := selected) hFamily hCovers
  have hCore : ThreeDimensionalMatching (compactMapCore I) := by
    exact compactMapCore_threeDimensionalMatching_of_exact
      (I := I) ⟨hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
  simpa [compactMap, hWellFormed, hEvery] using hCore

theorem compactTriple_x_mem_positions_of_mem {I : ExactCoverInput}
    {t : Nat × Nat × Nat}
    (ht : t ∈ compactTriples I) :
    t.1 ∈ compactPositionCodes I := by
  rcases List.mem_append.mp (by simpa [compactTriples] using ht) with hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with ⟨j, hj, x, hx, rfl⟩
    exact compactAlphaCode_mem_positions (I := I) ⟨j, hj, hx⟩
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨beta, hbeta, _j, _hj, _x, _hx, rfl⟩
    exact mem_compactNonAlphaCodes_positions hbeta

theorem compactTriple_y_mem_positions_of_mem {I : ExactCoverInput}
    {t : Nat × Nat × Nat}
    (ht : t ∈ compactTriples I) :
    t.2.1 ∈ compactPositionCodes I := by
  rcases List.mem_append.mp (by simpa [compactTriples] using ht) with hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with ⟨j, hj, x, hx, rfl⟩
    exact (mem_compactPositionCodes_iff I (compactPositionCode I x j)).2
      ⟨j, hj, x, hx, rfl⟩
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨_beta, _hbeta, j, hj, x, hx, rfl⟩
    exact (mem_compactPositionCodes_iff I (compactPositionCode I x j)).2
      ⟨j, hj, x, hx, rfl⟩

theorem compactTriple_z_mem_positions_of_mem {I : ExactCoverInput}
    {t : Nat × Nat × Nat}
    (ht : t ∈ compactTriples I) :
    t.2.2 ∈ compactPositionCodes I := by
  rcases List.mem_append.mp (by simpa [compactTriples] using ht) with hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with ⟨j, hj, x, hx, rfl⟩
    exact (mem_compactPositionCodes_iff I (compactPositionCode I x j)).2
      ⟨j, hj, x, hx, rfl⟩
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨_beta, _hbeta, j, hj, x, hx, rfl⟩
    exact compactNextCode_mem_positions (I := I) hj hx

theorem matching_x_projection_nodup_of_disjoint
    {selected : List (Nat × Nat × Nat)}
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    (selected.map fun t => t.1).Nodup := by
  exact hNodup.map_on (by
    intro a ha b hb hEq
    by_cases hab : a = b
    · exact hab
    · exact (hDisjoint a ha b hb hab).1 hEq |>.elim)

theorem matching_y_projection_nodup_of_disjoint
    {selected : List (Nat × Nat × Nat)}
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    (selected.map fun t => t.2.1).Nodup := by
  exact hNodup.map_on (by
    intro a ha b hb hEq
    by_cases hab : a = b
    · exact hab
    · exact (hDisjoint a ha b hb hab).2.1 hEq |>.elim)

theorem matching_z_projection_nodup_of_disjoint
    {selected : List (Nat × Nat × Nat)}
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    (selected.map fun t => t.2.2).Nodup := by
  exact hNodup.map_on (by
    intro a ha b hb hEq
    by_cases hab : a = b
    · exact hab
    · exact (hDisjoint a ha b hb hab).2.2 hEq |>.elim)

theorem nodup_subset_of_length_ge {α : Type*} {xs ys : List α}
    (hxs : xs.Nodup)
    (hsub : xs ⊆ ys) (hlen : ys.length ≤ xs.length) :
    ys ⊆ xs := by
  have hSubperm : List.Subperm xs ys := hxs.subperm hsub
  have hPerm : List.Perm xs ys := hSubperm.perm_of_length_le hlen
  exact hPerm.symm.subset

theorem compactMatching_x_covers_positions {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    compactPositionCodes I ⊆ selected.map fun t => t.1 := by
  have hProjNodup := matching_x_projection_nodup_of_disjoint hNodup hDisjoint
  have hProjSubset : (selected.map fun t => t.1) ⊆ compactPositionCodes I := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
    exact compactTriple_x_mem_positions_of_mem (I := I) (hAll t ht).1
  have hLen' : (compactPositionCodes I).length ≤ (selected.map fun t => t.1).length := by
    simpa using hLen
  exact nodup_subset_of_length_ge hProjNodup hProjSubset hLen'

theorem compactMatching_y_covers_positions {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    compactPositionCodes I ⊆ selected.map fun t => t.2.1 := by
  have hProjNodup := matching_y_projection_nodup_of_disjoint hNodup hDisjoint
  have hProjSubset : (selected.map fun t => t.2.1) ⊆ compactPositionCodes I := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
    exact compactTriple_y_mem_positions_of_mem (I := I) (hAll t ht).1
  have hLen' : (compactPositionCodes I).length ≤ (selected.map fun t => t.2.1).length := by
    simpa using hLen
  exact nodup_subset_of_length_ge hProjNodup hProjSubset hLen'

theorem compactMatching_z_covers_positions {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    compactPositionCodes I ⊆ selected.map fun t => t.2.2 := by
  have hProjNodup := matching_z_projection_nodup_of_disjoint hNodup hDisjoint
  have hProjSubset : (selected.map fun t => t.2.2) ⊆ compactPositionCodes I := by
    intro c hc
    rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
    exact compactTriple_z_mem_positions_of_mem (I := I) (hAll t ht).1
  have hLen' : (compactPositionCodes I).length ≤ (selected.map fun t => t.2.2).length := by
    simpa using hLen
  exact nodup_subset_of_length_ge hProjNodup hProjSubset hLen'

noncomputable def compactMatchedCoverSetIndices (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) : List Nat := by
  classical
  exact (List.range I.system.sets.length).filter fun j =>
    decide (∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
      compactCoverTriple I x j ∈ selected)

noncomputable def compactMatchedCoverSets (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) : List (List Nat) :=
  ((compactMatchedCoverSetIndices I selected).map (compactSourceSetAt I)).dedup

theorem mem_compactMatchedCoverSetIndices_iff (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) (j : Nat) :
    j ∈ compactMatchedCoverSetIndices I selected ↔
      j < I.system.sets.length ∧
        ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
          compactCoverTriple I x j ∈ selected := by
  classical
  simp [compactMatchedCoverSetIndices]

theorem compactMatchedCoverSets_nodup (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    (compactMatchedCoverSets I selected).Nodup :=
  List.nodup_dedup _

theorem compactMatchedCoverSets_family {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} :
    ∀ S ∈ compactMatchedCoverSets I selected, IsSetInFamily I.system S := by
  intro S hS
  have hMap :
      S ∈ (compactMatchedCoverSetIndices I selected).map (compactSourceSetAt I) := by
    simpa [compactMatchedCoverSets] using List.mem_dedup.mp hS
  rcases List.mem_map.mp hMap with ⟨j, hjUsed, rfl⟩
  have hj := ((mem_compactMatchedCoverSetIndices_iff I selected j).1 hjUsed).1
  rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
  exact List.getElem_mem _

theorem compactMatchedCoverSets_cover_of_matching {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hEvery : compactEveryElementOccurs I)
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    CoversUniverse I.system (compactMatchedCoverSets I selected) := by
  intro x hx
  have hOccurs : compactElementOccurs I x := hEvery x hx
  have hAlphaPos : compactAlphaCode I x ∈ compactPositionCodes I :=
    compactAlphaCode_mem_positions (I := I) hOccurs
  have hXCovers :=
    compactMatching_x_covers_positions (I := I) (selected := selected)
      hLen hAll hNodup hDisjoint hAlphaPos
  rcases List.mem_map.mp hXCovers with ⟨t, htSelected, htX⟩
  have htTriples := (hAll t htSelected).1
  rcases List.mem_append.mp (by simpa [compactTriples] using htTriples) with
    hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with
      ⟨j, hj, y, hy, htEq⟩
    subst t
    simp [compactCoverTriple] at htX
    have hyLt := ((mem_compactSupport_iff I (compactSourceSetAt I j) y).1 hy).1
    have hyx : y = x :=
      compactAlphaCode_inj_of_lt (I := I) hyLt hx htX
    subst y
    refine ⟨compactSourceSetAt I j, ?_, ?_⟩
    · exact List.mem_dedup.mpr (List.mem_map.mpr
        ⟨j, (mem_compactMatchedCoverSetIndices_iff I selected j).2
          ⟨hj, x, hy, by simpa [compactCoverTriple] using htSelected⟩, rfl⟩)
    · exact (mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hy |>.2
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨beta, hbeta, j, hj, y, hy, htEq⟩
    subst t
    simp [compactFillerTriple] at htX
    have hAlpha : compactIsAlphaCode I beta := by
      rw [htX]
      exact ⟨x, hx, hOccurs, rfl⟩
    exact (compactNonAlphaCodes_not_alpha hbeta hAlpha).elim

theorem compactCoverTriple_ne_fillerTriple_of_index {I : ExactCoverInput}
    {beta x y j k : Nat}
    (hj : j < I.system.sets.length)
    (hbeta : beta ∈ compactNonAlphaCodes I)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactCoverTriple I x j ≠ compactFillerTriple I beta y k := by
  intro hEq
  have hAlphaEq : compactAlphaCode I x = beta := by
    simpa [compactCoverTriple, compactFillerTriple] using
      congrArg (fun t : Nat × Nat × Nat => t.1) hEq
  have hxU := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1
  have hAlpha : compactIsAlphaCode I beta := by
    exact ⟨x, hxU, ⟨j, hj, hx⟩, hAlphaEq⟩
  exact compactNonAlphaCodes_not_alpha hbeta hAlpha

theorem compactCoverSelected_next_of_matching {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {j x : Nat}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected)
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hCoverSelected : compactCoverTriple I x j ∈ selected) :
    compactCoverTriple I (compactNextInSet I j x) j ∈ selected := by
  have hNextPos : compactPositionCode I (compactNextInSet I j x) j ∈ compactPositionCodes I :=
    compactNextCode_mem_positions (I := I) hj hx
  have hZCover :=
    compactMatching_z_covers_positions (I := I) (selected := selected)
      hLen hAll hNodup hDisjoint hNextPos
  rcases List.mem_map.mp hZCover with ⟨t, htSelected, htZ⟩
  have htTriples := (hAll t htSelected).1
  rcases List.mem_append.mp (by simpa [compactTriples] using htTriples) with
    hCover | hFiller
  · rcases (mem_compactCoverTriples_iff I t).1 hCover with
      ⟨k, hk, y, hy, htEq⟩
    subst t
    simp [compactCoverTriple] at htZ
    have hyU := ((mem_compactSupport_iff I (compactSourceSetAt I k) y).1 hy).1
    have hNextMem := compactNextInSet_mem_support (I := I) (j := j) (x := x) hx
    have hNextU := ((mem_compactSupport_iff I (compactSourceSetAt I j)
      (compactNextInSet I j x)).1 hNextMem).1
    have hInj := compactPositionCode_inj (I := I) hyU hNextU htZ
    rcases hInj with ⟨hyEq, hkEq⟩
    subst y
    subst k
    exact htSelected
  · rcases (mem_compactFillerTriples_iff I t).1 hFiller with
      ⟨beta, hbeta, k, hk, y, hy, htEq⟩
    subst t
    simp [compactFillerTriple] at htZ
    have hNextYMem := compactNextInSet_mem_support (I := I) (j := k) (x := y) hy
    have hNextXMem := compactNextInSet_mem_support (I := I) (j := j) (x := x) hx
    have hNextYU := ((mem_compactSupport_iff I (compactSourceSetAt I k)
      (compactNextInSet I k y)).1 hNextYMem).1
    have hNextXU := ((mem_compactSupport_iff I (compactSourceSetAt I j)
      (compactNextInSet I j x)).1 hNextXMem).1
    have hInj := compactPositionCode_inj (I := I) hNextYU hNextXU htZ
    rcases hInj with ⟨hNextEq, hkEq⟩
    subst k
    have hySame :
        y ∈ compactSupport I (compactSourceSetAt I j) := by
      simpa using hy
    have hyx : y = x :=
      compactNextInSet_inj (I := I) (j := j) hySame hx hNextEq
    subst y
    have hNe :
        compactCoverTriple I x j ≠ compactFillerTriple I beta x j :=
      compactCoverTriple_ne_fillerTriple_of_index
        (I := I) (j := j) (x := x) (beta := beta) (y := x) (k := j)
        hj hbeta hx
    have hYNe := (hDisjoint (compactCoverTriple I x j) hCoverSelected
      (compactFillerTriple I beta x j) htSelected hNe).2.1
    exact (hYNe rfl).elim

theorem compactCoverSelected_iterate_of_matching {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {j x : Nat}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected)
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hCoverSelected : compactCoverTriple I x j ∈ selected) :
    ∀ n, compactCoverTriple I ((compactNextInSet I j)^[n] x) j ∈ selected
  | 0 => by
      simpa using hCoverSelected
  | n + 1 => by
      have hMemN :
          (compactNextInSet I j)^[n] x ∈ compactSupport I (compactSourceSetAt I j) :=
        compactNextInSet_iterate_mem_support (I := I) (j := j) (x := x) hx n
      have hSelectedN :
          compactCoverTriple I ((compactNextInSet I j)^[n] x) j ∈ selected :=
        compactCoverSelected_iterate_of_matching
          (I := I) (selected := selected) (j := j) (x := x)
          hLen hAll hNodup hDisjoint hj hx hCoverSelected n
      simpa [Function.iterate_succ_apply'] using
        compactCoverSelected_next_of_matching
          (I := I) (selected := selected) (j := j)
          (x := (compactNextInSet I j)^[n] x)
          hLen hAll hNodup hDisjoint hj hMemN hSelectedN

theorem compactCoverSelected_of_same_support {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {j x y : Nat}
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected)
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hy : y ∈ compactSupport I (compactSourceSetAt I j))
    (hCoverSelected : compactCoverTriple I x j ∈ selected) :
    compactCoverTriple I y j ∈ selected := by
  rcases compactNextInSet_orbit (I := I) (j := j) (x := x) (y := y) hx hy with
    ⟨n, hn⟩
  rw [← hn]
  exact compactCoverSelected_iterate_of_matching
    (I := I) (selected := selected) (j := j) (x := x)
    hLen hAll hNodup hDisjoint hj hx hCoverSelected n

theorem mem_compactMatchedCoverSets_iff (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) (S : List Nat) :
    S ∈ compactMatchedCoverSets I selected ↔
      ∃ j, j < I.system.sets.length ∧
        S = compactSourceSetAt I j ∧
        ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
          compactCoverTriple I x j ∈ selected := by
  constructor
  · intro hS
    have hMap :
        S ∈ (compactMatchedCoverSetIndices I selected).map (compactSourceSetAt I) := by
      simpa [compactMatchedCoverSets] using List.mem_dedup.mp hS
    rcases List.mem_map.mp hMap with ⟨j, hjUsed, rfl⟩
    rcases (mem_compactMatchedCoverSetIndices_iff I selected j).1 hjUsed with
      ⟨hj, x, hx, hCover⟩
    exact ⟨j, hj, rfl, x, hx, hCover⟩
  · rintro ⟨j, hj, rfl, x, hx, hCover⟩
    exact List.mem_dedup.mpr (List.mem_map.mpr
      ⟨j, (mem_compactMatchedCoverSetIndices_iff I selected j).2
        ⟨hj, x, hx, hCover⟩, rfl⟩)

theorem compactMatchedCoverSets_pairwiseDisjoint_of_matching {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hWellFormed : SetSystemWellFormed I.system)
    (hLen : selected.length ≥ (compactPositionCodes I).length)
    (hAll : ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t)
    (hNodup : selected.Nodup)
    (hDisjoint : DisjointTriples selected) :
    PairwiseDisjointFamily (compactMatchedCoverSets I selected) := by
  intro A hA B hB hAB x hxA hxB
  rcases (mem_compactMatchedCoverSets_iff I selected A).1 hA with
    ⟨j, hj, hAeq, xj, hxj, hCoverJ⟩
  rcases (mem_compactMatchedCoverSets_iff I selected B).1 hB with
    ⟨k, hk, hBeq, xk, hxk, hCoverK⟩
  have hxU : x < I.system.universeSize := by
    exact hWellFormed A (compactMatchedCoverSets_family (I := I) (selected := selected) A hA)
      x hxA
  have hxSupportJ : x ∈ compactSupport I (compactSourceSetAt I j) := by
    exact (mem_compactSupport_iff I (compactSourceSetAt I j) x).2
      ⟨hxU, by simpa [hAeq] using hxA⟩
  have hxSupportK : x ∈ compactSupport I (compactSourceSetAt I k) := by
    exact (mem_compactSupport_iff I (compactSourceSetAt I k) x).2
      ⟨hxU, by simpa [hBeq] using hxB⟩
  have hCoverXJ : compactCoverTriple I x j ∈ selected :=
    compactCoverSelected_of_same_support
      (I := I) (selected := selected) (j := j) (x := xj) (y := x)
      hLen hAll hNodup hDisjoint hj hxj hxSupportJ hCoverJ
  have hCoverXK : compactCoverTriple I x k ∈ selected :=
    compactCoverSelected_of_same_support
      (I := I) (selected := selected) (j := k) (x := xk) (y := x)
      hLen hAll hNodup hDisjoint hk hxk hxSupportK hCoverK
  have hTriplesEq :
      compactCoverTriple I x j = compactCoverTriple I x k := by
    by_cases hEq : compactCoverTriple I x j = compactCoverTriple I x k
    · exact hEq
    · have hXNe :=
        (hDisjoint (compactCoverTriple I x j) hCoverXJ
          (compactCoverTriple I x k) hCoverXK hEq).1
      exact False.elim (hXNe rfl)
  have hCodeEq : compactPositionCode I x j = compactPositionCode I x k := by
    simpa [compactCoverTriple] using
      congrArg (fun t : Nat × Nat × Nat => t.2.1) hTriplesEq
  have hjk : j = k := (compactPositionCode_inj (I := I) hxU hxU hCodeEq).2
  have hABeq : A = B := by
    rw [hAeq, hBeq, hjk]
  exact hAB hABeq

theorem exactCover_of_compactMapCore_threeDimensionalMatching {I : ExactCoverInput}
    (hWellFormed : SetSystemWellFormed I.system)
    (hEvery : compactEveryElementOccurs I)
    (h3DM : ThreeDimensionalMatching (compactMapCore I)) :
    ExactCover I := by
  rcases h3DM with ⟨selected, hLen, hAll, hNodup, hDisjoint⟩
  have hLenCore : selected.length ≥ (compactPositionCodes I).length := by
    simpa [compactMapCore] using hLen
  have hAllCore :
      ∀ t ∈ selected, t ∈ compactTriples I ∧ TripleWithinBounds (compactMapCore I) t := by
    intro t ht
    simpa [compactMapCore] using hAll t ht
  refine ⟨hWellFormed, compactMatchedCoverSets I selected, ?_, ?_, ?_, ?_⟩
  · exact compactMatchedCoverSets_family (I := I) (selected := selected)
  · exact compactMatchedCoverSets_nodup I selected
  · exact compactMatchedCoverSets_pairwiseDisjoint_of_matching
      (I := I) (selected := selected) hWellFormed hLenCore hAllCore hNodup hDisjoint
  · exact compactMatchedCoverSets_cover_of_matching
      (I := I) (selected := selected) hEvery hLenCore hAllCore hNodup hDisjoint

theorem compactMapCore_correct (I : ExactCoverInput)
    (hWellFormed : SetSystemWellFormed I.system)
    (hEvery : compactEveryElementOccurs I) :
    ExactCover I ↔ ThreeDimensionalMatching (compactMapCore I) := by
  constructor
  · exact compactMapCore_threeDimensionalMatching_of_exact
  · exact exactCover_of_compactMapCore_threeDimensionalMatching
      (I := I) hWellFormed hEvery

theorem compactMap_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ ThreeDimensionalMatching (compactMap I) := by
  change ExactCover I ↔ ThreeDimensionalMatching (compactMap I)
  constructor
  · exact compactMap_threeDimensionalMatching_of_exact
  · intro h3DM
    by_cases hGuard : SetSystemWellFormed I.system ∧ compactEveryElementOccurs I
    · have hCore : ThreeDimensionalMatching (compactMapCore I) := by
        simpa [compactMap, hGuard] using h3DM
      exact exactCover_of_compactMapCore_threeDimensionalMatching
        (I := I) hGuard.1 hGuard.2 hCore
    · have hNo : ThreeDimensionalMatching noInput := by
        simpa [compactMap, hGuard] using h3DM
      exact (noInput_isNo hNo).elim

/-! ### Compact size bounds for the membership-cycle route -/

theorem compactFlatMap_length_le_mul {α β : Type*} (xs : List α) (f : α → List β)
    (B : Nat) (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length ≤ B := hB x (by simp)
      have hTail : ∀ y ∈ xs, (f y).length ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih hTail
      have hLen :
          ((x :: xs).flatMap f).length = (f x).length + (xs.flatMap f).length := by
        simp
      rw [hLen]
      calc
        (f x).length + (xs.flatMap f).length ≤ B + xs.length * B := by
          omega
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem compactPositionCodesForSet_length_le_universe (I : ExactCoverInput) (j : Nat) :
    (compactPositionCodesForSet I j).length ≤ I.system.universeSize := by
  simpa [compactPositionCodesForSet] using
    compactSupport_length_le_universe I (compactSourceSetAt I j)

theorem compactPositionCodes_length_le_coordBound (I : ExactCoverInput) :
    (compactPositionCodes I).length ≤ compactCoordBound I := by
  have hFlat :
      ((List.range I.system.sets.length).flatMap (compactPositionCodesForSet I)).length ≤
        I.system.sets.length * I.system.universeSize := by
    simpa using compactFlatMap_length_le_mul (List.range I.system.sets.length)
      (compactPositionCodesForSet I) I.system.universeSize (by
        intro j _hj
        exact compactPositionCodesForSet_length_le_universe I j)
  simpa [compactPositionCodes, compactCoordBound] using hFlat

theorem compactCoverTriplesForSet_length_le_universe (I : ExactCoverInput) (j : Nat) :
    (compactCoverTriplesForSet I j).length ≤ I.system.universeSize := by
  simpa [compactCoverTriplesForSet] using
    compactSupport_length_le_universe I (compactSourceSetAt I j)

theorem compactCoverTriples_length_le_coordBound (I : ExactCoverInput) :
    (compactCoverTriples I).length ≤ compactCoordBound I := by
  have hFlat :
      ((List.range I.system.sets.length).flatMap (compactCoverTriplesForSet I)).length ≤
        I.system.sets.length * I.system.universeSize := by
    simpa using compactFlatMap_length_le_mul (List.range I.system.sets.length)
      (compactCoverTriplesForSet I) I.system.universeSize (by
        intro j _hj
        exact compactCoverTriplesForSet_length_le_universe I j)
  simpa [compactCoverTriples, compactCoordBound] using hFlat

theorem compactFillerTriplesForBetaSet_length_le_universe
    (I : ExactCoverInput) (beta j : Nat) :
    (compactFillerTriplesForBetaSet I beta j).length ≤ I.system.universeSize := by
  simpa [compactFillerTriplesForBetaSet] using
    compactSupport_length_le_universe I (compactSourceSetAt I j)

theorem compactFillerTriplesForBeta_length_le_coordBound
    (I : ExactCoverInput) (beta : Nat) :
    (compactFillerTriplesForBeta I beta).length ≤ compactCoordBound I := by
  have hFlat :
      ((List.range I.system.sets.length).flatMap
          (compactFillerTriplesForBetaSet I beta)).length ≤
        I.system.sets.length * I.system.universeSize := by
    simpa using compactFlatMap_length_le_mul (List.range I.system.sets.length)
      (compactFillerTriplesForBetaSet I beta) I.system.universeSize (by
        intro j _hj
        exact compactFillerTriplesForBetaSet_length_le_universe I beta j)
  simpa [compactFillerTriplesForBeta, compactCoordBound] using hFlat

theorem compactNonAlphaCodes_length_le_positionCodes (I : ExactCoverInput) :
    (compactNonAlphaCodes I).length ≤ (compactPositionCodes I).length := by
  classical
  simpa [compactNonAlphaCodes] using
    (List.length_filter_le
      (fun c => decide (¬ compactIsAlphaCode I c)) (compactPositionCodes I))

theorem compactFillerTriples_length_le_coordBound_sq (I : ExactCoverInput) :
    (compactFillerTriples I).length ≤ compactCoordBound I * compactCoordBound I := by
  have hFlat :
      ((compactNonAlphaCodes I).flatMap (compactFillerTriplesForBeta I)).length ≤
        (compactNonAlphaCodes I).length * compactCoordBound I := by
    exact compactFlatMap_length_le_mul (compactNonAlphaCodes I)
      (compactFillerTriplesForBeta I) (compactCoordBound I) (by
        intro beta _hbeta
        exact compactFillerTriplesForBeta_length_le_coordBound I beta)
  have hBeta :
      (compactNonAlphaCodes I).length ≤ compactCoordBound I :=
    (compactNonAlphaCodes_length_le_positionCodes I).trans
      (compactPositionCodes_length_le_coordBound I)
  calc
    (compactFillerTriples I).length ≤
        (compactNonAlphaCodes I).length * compactCoordBound I := by
          simpa [compactFillerTriples] using hFlat
    _ ≤ compactCoordBound I * compactCoordBound I := by
          exact Nat.mul_le_mul_right (compactCoordBound I) hBeta

theorem compactTriples_length_le_coordBound_sq_add (I : ExactCoverInput) :
    (compactTriples I).length ≤
      compactCoordBound I + compactCoordBound I * compactCoordBound I := by
  have hCover := compactCoverTriples_length_le_coordBound I
  have hFiller := compactFillerTriples_length_le_coordBound_sq I
  calc
    (compactTriples I).length =
        (compactCoverTriples I).length + (compactFillerTriples I).length := by
          simp [compactTriples]
    _ ≤ compactCoordBound I + compactCoordBound I * compactCoordBound I := by
          omega

theorem compactCoordBound_le_source_sq (I : ExactCoverInput) :
    compactCoordBound I ≤ (exactCoverStructuredEncodedType.inputSize I) ^ 2 := by
  have hSets : I.system.sets.length ≤ exactCoverStructuredEncodedType.inputSize I :=
    Knapsack.exactCover_sets_length_le_structured_inputSize I
  have hUniverse : I.system.universeSize ≤ exactCoverStructuredEncodedType.inputSize I :=
    Knapsack.exactCover_universeSize_le_structured_inputSize I
  simpa [compactCoordBound, pow_two] using Nat.mul_le_mul hSets hUniverse

theorem compactPositionCodes_length_le_source_sq (I : ExactCoverInput) :
    (compactPositionCodes I).length ≤
      (exactCoverStructuredEncodedType.inputSize I) ^ 2 :=
  (compactPositionCodes_length_le_coordBound I).trans (compactCoordBound_le_source_sq I)

theorem compactCoordBound_le_source_succ_sq (I : ExactCoverInput) :
    compactCoordBound I ≤ (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hC0 : compactCoordBound I ≤ S ^ 2 := by
    simpa [S] using compactCoordBound_le_source_sq I
  exact hC0.trans (Nat.pow_le_pow_left (Nat.le_succ S) 2)

theorem compactTriples_length_le_source_poly_succ (I : ExactCoverInput) :
    (compactTriples I).length ≤
      2 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 4 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hLen := compactTriples_length_le_coordBound_sq_add I
  have hC0 : compactCoordBound I ≤ S ^ 2 := by
    simpa [S] using compactCoordBound_le_source_sq I
  have hC : compactCoordBound I ≤ (S + 1) ^ 2 := by
    exact hC0.trans (Nat.pow_le_pow_left (Nat.le_succ S) 2)
  have hSq :
      compactCoordBound I * compactCoordBound I ≤ (S + 1) ^ 4 := by
    calc
      compactCoordBound I * compactCoordBound I ≤ (S + 1) ^ 2 * (S + 1) ^ 2 := by
        exact Nat.mul_le_mul hC hC
      _ = (S + 1) ^ 4 := by ring
  have hPow : (S + 1) ^ 2 ≤ (S + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ S + 1) (by norm_num : 2 ≤ 4)
  calc
    (compactTriples I).length ≤
        compactCoordBound I + compactCoordBound I * compactCoordBound I := hLen
    _ ≤ (S + 1) ^ 2 + (S + 1) ^ 4 := by
        exact Nat.add_le_add hC hSq
    _ ≤ (S + 1) ^ 4 + (S + 1) ^ 4 := by
        exact Nat.add_le_add_right hPow ((S + 1) ^ 4)
    _ = 2 * (S + 1) ^ 4 := by ring

theorem compactTripleStructured_inputSize_le_source_poly_succ {I : ExactCoverInput}
    {t : Nat × Nat × Nat} (ht : t ∈ compactTriples I) :
    tripleStructuredEncodedType.inputSize t ≤
      4 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hC : compactCoordBound I ≤ (S + 1) ^ 2 := by
    simpa [S] using compactCoordBound_le_source_succ_sq I
  have hBounds := compactTriple_withinBounds_of_mem (I := I) ht
  cases t with
  | mk x yz =>
      cases yz with
      | mk y z =>
          simp [TripleWithinBounds, compactMapCore] at hBounds
          have hx : x + 1 ≤ (S + 1) ^ 2 := (Nat.succ_le_of_lt hBounds.1).trans hC
          have hy : y + 1 ≤ (S + 1) ^ 2 :=
            (Nat.succ_le_of_lt hBounds.2.1).trans hC
          have hz : z + 1 ≤ (S + 1) ^ 2 :=
            (Nat.succ_le_of_lt hBounds.2.2).trans hC
          have hSpos : 0 < S := by
            simpa [S] using Knapsack.exactCoverStructured_inputSize_pos I
          have hBaseTwo : 2 ≤ S + 1 := by omega
          have hFour : 4 ≤ (S + 1) ^ 2 := by
            have hPow := Nat.pow_le_pow_left hBaseTwo 2
            norm_num at hPow
            exact hPow
          simp [tripleStructuredEncodedType]
          nlinarith

theorem compactTriples_structured_inputSize_le_source_poly_succ (I : ExactCoverInput) :
    tripleListStructuredEncodedType.inputSize (compactTriples I) ≤
      10 * (exactCoverStructuredEncodedType.inputSize I + 1) ^ 6 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hLen : (compactTriples I).length ≤ 2 * (S + 1) ^ 4 := by
    simpa [S] using compactTriples_length_le_source_poly_succ I
  have hElements :
      ∀ t ∈ compactTriples I,
        tripleStructuredEncodedType.inputSize t ≤ 4 * (S + 1) ^ 2 := by
    intro t ht
    simpa [S] using compactTripleStructured_inputSize_le_source_poly_succ (I := I) ht
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound
      tripleStructuredEncodedType (compactTriples I) (4 * (S + 1) ^ 2) hElements
  have hMul :
      (compactTriples I).length * (4 * (S + 1) ^ 2 + 1) ≤
        (2 * (S + 1) ^ 4) * (4 * (S + 1) ^ 2 + 1) := by
    exact Nat.mul_le_mul_right (4 * (S + 1) ^ 2 + 1) hLen
  calc
    tripleListStructuredEncodedType.inputSize (compactTriples I)
        ≤ (compactTriples I).length * (4 * (S + 1) ^ 2 + 1) := hList
    _ ≤ (2 * (S + 1) ^ 4) * (4 * (S + 1) ^ 2 + 1) := hMul
    _ ≤ 10 * (S + 1) ^ 6 := by
          have hBase : 1 ≤ S + 1 := by omega
          have hPow : (S + 1) ^ 4 ≤ (S + 1) ^ 6 :=
            Nat.pow_le_pow_right hBase (by norm_num : 4 ≤ 6)
          nlinarith

theorem threeDimensionalMatchingStructured_inputSize_eq
    (J : ThreeDimensionalMatchingInput) :
    threeDimensionalMatchingStructuredEncodedType.inputSize J =
      EncodedType.nat.inputSize J.xSize + 1 +
        (EncodedType.nat.inputSize J.ySize + 1 +
          (EncodedType.nat.inputSize J.zSize + 1 +
            (tripleListStructuredEncodedType.inputSize J.triples + 1 +
              EncodedType.nat.inputSize J.k))) := by
  cases J with
  | mk xSize ySize zSize triples k =>
      change threeDimensionalMatchingTupleStructuredEncodedType.inputSize
          (xSize, (ySize, (zSize, (triples, k)))) =
        EncodedType.nat.inputSize xSize + 1 +
          (EncodedType.nat.inputSize ySize + 1 +
            (EncodedType.nat.inputSize zSize + 1 +
              (tripleListStructuredEncodedType.inputSize triples + 1 +
                EncodedType.nat.inputSize k)))
      simp [threeDimensionalMatchingTupleStructuredEncodedType]

theorem compactCoordBound_nat_inputSize_le_source_succ_sq (I : ExactCoverInput) :
    EncodedType.nat.inputSize (compactCoordBound I) ≤
      (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 + 1 := by
  simpa using Nat.add_le_add_right (compactCoordBound_le_source_succ_sq I) 1

theorem compactPositionCodes_nat_inputSize_le_source_succ_sq (I : ExactCoverInput) :
    EncodedType.nat.inputSize (compactPositionCodes I).length ≤
      (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 + 1 := by
  have hLen :
      (compactPositionCodes I).length ≤
        (exactCoverStructuredEncodedType.inputSize I + 1) ^ 2 :=
    (compactPositionCodes_length_le_coordBound I).trans
      (compactCoordBound_le_source_succ_sq I)
  simpa using Nat.add_le_add_right hLen 1

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
