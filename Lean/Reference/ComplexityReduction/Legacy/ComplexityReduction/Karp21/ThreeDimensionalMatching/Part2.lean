import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching.Part1

namespace ComplexityReduction
namespace Karp21
namespace ThreeDimensionalMatching
open ComplexityReduction.Combinatorics

theorem compactSupport_lengths_sum_eq_universe_of_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected) :
    (selected.map fun S => (compactSupport I S).length).sum = I.system.universeSize := by
  have hCounts :
      Knapsack.digitCountsFrom 0 I.system.universeSize selected =
        List.replicate I.system.universeSize 1 := by
    simpa using
      (Knapsack.digitCountsFrom_eq_replicate_one_of_exact
        (I := I) (sets := selected) hNodup hDisjoint hCovers
        (start := 0) (len := I.system.universeSize) (by omega))
  rw [compactSupport_lengths_sum_eq_digitCountsFrom_sum, hCounts]
  simp

theorem compactSelectedPositionCodes_length_eq_universe_of_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected) :
    (compactSelectedPositionCodes I selected).length = I.system.universeSize := by
  rw [compactSelectedPositionCodes_length_eq_support_sum hFamily]
  exact compactSupport_lengths_sum_eq_universe_of_exact hNodup hDisjoint hCovers

theorem compactSelectedSetIndex_eq_of_family {I : ExactCoverInput} {S T : List Nat}
    (hS : IsSetInFamily I.system S)
    (hT : IsSetInFamily I.system T)
    (hIdx : compactSelectedSetIndex I S = compactSelectedSetIndex I T) :
    S = T := by
  have hSourceS :
      compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
    compactSourceSetAt_idxOf_eq (I := I) (S := S) (by simpa [IsSetInFamily] using hS)
  have hSourceT :
      compactSourceSetAt I (compactSelectedSetIndex I T) = T :=
    compactSourceSetAt_idxOf_eq (I := I) (S := T) (by simpa [IsSetInFamily] using hT)
  rw [hIdx] at hSourceS
  rw [← hSourceS, hSourceT]

theorem compactSelectedPositionCodesForSet_nodup (I : ExactCoverInput)
    (S : List Nat) :
    (compactSelectedPositionCodesForSet I S).Nodup := by
  simpa [compactSelectedPositionCodesForSet] using
    compactPositionCodesForSet_nodup I (compactSelectedSetIndex I S)

theorem compactSelectedPositionCodesForSet_disjoint_of_ne {I : ExactCoverInput}
    {S T : List Nat}
    (hS : IsSetInFamily I.system S)
    (hT : IsSetInFamily I.system T)
    (hNe : S ≠ T) :
    List.Disjoint
      (compactSelectedPositionCodesForSet I S)
      (compactSelectedPositionCodesForSet I T) := by
  have hIdxNe : compactSelectedSetIndex I S ≠ compactSelectedSetIndex I T := by
    intro hIdx
    exact hNe (compactSelectedSetIndex_eq_of_family (I := I) hS hT hIdx)
  simpa [compactSelectedPositionCodesForSet] using
    compactPositionCodesForSet_disjoint_of_ne (I := I) hIdxNe

theorem compactSelectedPositionCodes_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    (compactSelectedPositionCodes I selected).Nodup := by
  have hLocal :
      ∀ S ∈ selected, (compactSelectedPositionCodesForSet I S).Nodup := by
    intro S _hS
    exact compactSelectedPositionCodesForSet_nodup I S
  have hPair :
      selected.Pairwise
        (fun S T =>
          List.Disjoint
            (compactSelectedPositionCodesForSet I S)
            (compactSelectedPositionCodesForSet I T)) := by
    refine hNodup.pairwise_of_forall_ne ?_
    intro S hS T hT hNe
    exact compactSelectedPositionCodesForSet_disjoint_of_ne
      (I := I) (hFamily S hS) (hFamily T hT) hNe
  have hFlat :=
    (List.nodup_flatMap (l₁ := selected)
      (f := compactSelectedPositionCodesForSet I)).2 ⟨hLocal, hPair⟩
  simpa [compactSelectedPositionCodes] using hFlat

theorem compactSelectedPositionCodes_subset_positions {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    compactSelectedPositionCodes I selected ⊆ compactPositionCodes I := by
  intro c hc
  rcases List.mem_flatMap.mp (by simpa [compactSelectedPositionCodes] using hc) with
    ⟨S, hSSelected, hcS⟩
  have hIdx : compactSelectedSetIndex I S < I.system.sets.length :=
    compactSelectedSetIndex_lt_of_family (I := I) (hFamily S hSSelected)
  exact List.mem_flatMap.mpr
    ⟨compactSelectedSetIndex I S, by simpa using hIdx,
      by simpa [compactSelectedPositionCodesForSet] using hcS⟩

theorem compactSelectedPositionCodes_subperm_positions {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    List.Subperm (compactSelectedPositionCodes I selected) (compactPositionCodes I) := by
  exact (compactSelectedPositionCodes_nodup (I := I) hFamily hNodup).subperm
    (compactSelectedPositionCodes_subset_positions (I := I) hFamily)

theorem mem_compactSelectedPositionCodes_iff_of_family {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (c : Nat) :
    c ∈ compactSelectedPositionCodes I selected ↔
      ∃ S, S ∈ selected ∧
        ∃ x, x ∈ compactSupport I S ∧
          c = compactPositionCode I x (compactSelectedSetIndex I S) := by
  constructor
  · intro hc
    rcases List.mem_flatMap.mp (by simpa [compactSelectedPositionCodes] using hc) with
      ⟨S, hSSelected, hcS⟩
    rcases (mem_compactPositionCodesForSet_iff I (compactSelectedSetIndex I S) c).1
        (by simpa [compactSelectedPositionCodesForSet] using hcS) with
      ⟨x, hx, hcode⟩
    have hSource :
        compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
      compactSourceSetAt_idxOf_eq (I := I) (S := S)
        (by simpa [IsSetInFamily] using hFamily S hSSelected)
    exact ⟨S, hSSelected, x, by simpa [hSource] using hx, hcode⟩
  · rintro ⟨S, hSSelected, x, hx, hcode⟩
    have hSource :
        compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
      compactSourceSetAt_idxOf_eq (I := I) (S := S)
        (by simpa [IsSetInFamily] using hFamily S hSSelected)
    exact List.mem_flatMap.mpr
      ⟨S, hSSelected, by
        simpa [compactSelectedPositionCodesForSet, hSource] using
          (mem_compactPositionCodesForSet_iff I (compactSelectedSetIndex I S) c).2
            ⟨x, by simpa [hSource] using hx, hcode⟩⟩

theorem compactSelectedPositionCode_of_same_source {I : ExactCoverInput}
    {selected : List (List Nat)} {j x y : Nat}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hj : j < I.system.sets.length)
    (hx : x ∈ compactSupport I (compactSourceSetAt I j))
    (hy : y ∈ compactSupport I (compactSourceSetAt I j))
    (hc : compactPositionCode I x j ∈ compactSelectedPositionCodes I selected) :
    compactPositionCode I y j ∈ compactSelectedPositionCodes I selected := by
  rcases (mem_compactSelectedPositionCodes_iff_of_family (I := I) hFamily
      (compactPositionCode I x j)).1 hc with
    ⟨S, hSSelected, z, hz, hcode⟩
  have hxU := ((mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hx).1
  have hzU := ((mem_compactSupport_iff I S z).1 hz).1
  have hIndex :
      j = compactSelectedSetIndex I S :=
    (compactPositionCode_inj (I := I) (x := x) (y := z)
      (j := j) (k := compactSelectedSetIndex I S) hxU hzU hcode).2
  subst j
  have hSource :
      compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
    compactSourceSetAt_idxOf_eq (I := I) (S := S)
      (by simpa [IsSetInFamily] using hFamily S hSSelected)
  exact (mem_compactSelectedPositionCodes_iff_of_family (I := I) hFamily
    (compactPositionCode I y (compactSelectedSetIndex I S))).2
      ⟨S, hSSelected, y, by simpa [hSource] using hy, rfl⟩

noncomputable def compactSelectedPositionFilter (I : ExactCoverInput)
    (selected : List (List Nat)) : List Nat := by
  classical
  exact (compactPositionCodes I).filter fun c =>
    decide (c ∈ compactSelectedPositionCodes I selected)

noncomputable def compactUnselectedPositionCodes (I : ExactCoverInput)
    (selected : List (List Nat)) : List Nat := by
  classical
  exact (compactPositionCodes I).filter fun c =>
    !decide (c ∈ compactSelectedPositionCodes I selected)

theorem mem_compactUnselectedPositionCodes_iff (I : ExactCoverInput)
    (selected : List (List Nat)) (c : Nat) :
    c ∈ compactUnselectedPositionCodes I selected ↔
      c ∈ compactPositionCodes I ∧ c ∉ compactSelectedPositionCodes I selected := by
  classical
  simp [compactUnselectedPositionCodes]

theorem compactSelectedPositionFilter_length_eq {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    (compactSelectedPositionFilter I selected).length =
      (compactSelectedPositionCodes I selected).length := by
  classical
  let filtered := compactSelectedPositionFilter I selected
  change filtered.length = (compactSelectedPositionCodes I selected).length
  have hFilteredNodup : filtered.Nodup := by
    simpa [filtered, compactSelectedPositionFilter] using
      (compactPositionCodes_nodup I).filter
        (fun c => decide (c ∈ compactSelectedPositionCodes I selected))
  have hFilteredSubset :
      filtered ⊆ compactSelectedPositionCodes I selected := by
    intro c hc
    have hPair :
        c ∈ compactPositionCodes I ∧
          c ∈ compactSelectedPositionCodes I selected := by
      simpa [filtered, compactSelectedPositionFilter] using hc
    exact hPair.2
  have hSelectedSubset :
      compactSelectedPositionCodes I selected ⊆ filtered := by
    intro c hc
    have hcPos :=
      compactSelectedPositionCodes_subset_positions (I := I) hFamily hc
    simp [filtered, compactSelectedPositionFilter, hcPos, hc]
  have hLe₁ :
      filtered.length ≤ (compactSelectedPositionCodes I selected).length :=
    (hFilteredNodup.subperm hFilteredSubset).length_le
  have hLe₂ :
      (compactSelectedPositionCodes I selected).length ≤ filtered.length :=
    ((compactSelectedPositionCodes_nodup (I := I) hFamily hNodup).subperm
      hSelectedSubset).length_le
  omega

theorem compactPositionCodes_length_eq_selected_add_unselected {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    (compactPositionCodes I).length =
      (compactSelectedPositionCodes I selected).length +
        (compactUnselectedPositionCodes I selected).length := by
  classical
  have hSplit :=
    List.length_eq_length_filter_add
      (l := compactPositionCodes I)
      (fun c => decide (c ∈ compactSelectedPositionCodes I selected))
  rw [← compactSelectedPositionFilter_length_eq (I := I) hFamily hNodup]
  simpa [compactSelectedPositionFilter, compactUnselectedPositionCodes] using hSplit

noncomputable def compactAlphaPositionFilter (I : ExactCoverInput) : List Nat := by
  classical
  exact (compactPositionCodes I).filter fun c => decide (compactIsAlphaCode I c)

theorem compactAlphaPositionFilter_length_eq_universe {I : ExactCoverInput}
    (hEvery : compactEveryElementOccurs I) :
    (compactAlphaPositionFilter I).length = I.system.universeSize := by
  classical
  let filtered := compactAlphaPositionFilter I
  change filtered.length = I.system.universeSize
  have hFilteredNodup : filtered.Nodup := by
    simpa [filtered, compactAlphaPositionFilter] using
      (compactPositionCodes_nodup I).filter fun c => decide (compactIsAlphaCode I c)
  have hFilteredSubset : filtered ⊆ compactAlphaCodes I := by
    intro c hc
    have hcAlpha : compactIsAlphaCode I c := by
      have hPair : c ∈ compactPositionCodes I ∧ compactIsAlphaCode I c := by
        simpa [filtered, compactAlphaPositionFilter] using hc
      exact hPair.2
    exact (mem_compactAlphaCodes_iff_of_everyElementOccurs (I := I) hEvery c).2 hcAlpha
  have hAlphaSubset : compactAlphaCodes I ⊆ filtered := by
    intro c hc
    have hcAlpha :=
      (mem_compactAlphaCodes_iff_of_everyElementOccurs (I := I) hEvery c).1 hc
    rcases hcAlpha with ⟨x, hxLt, hOccurs, hCode⟩
    have hcPos : c ∈ compactPositionCodes I := by
      rw [← hCode]
      exact compactAlphaCode_mem_positions (I := I) hOccurs
    have hcAlpha' : compactIsAlphaCode I c := ⟨x, hxLt, hOccurs, hCode⟩
    simp [filtered, compactAlphaPositionFilter, hcPos, hcAlpha']
  have hLe₁ : filtered.length ≤ (compactAlphaCodes I).length :=
    (hFilteredNodup.subperm hFilteredSubset).length_le
  have hLe₂ : (compactAlphaCodes I).length ≤ filtered.length :=
    ((compactAlphaCodes_nodup I).subperm hAlphaSubset).length_le
  have hLenRange : (compactAlphaCodes I).length = I.system.universeSize := by
    simp [compactAlphaCodes]
  omega

theorem compactPositionCodes_length_eq_alpha_add_nonAlpha {I : ExactCoverInput}
    (hEvery : compactEveryElementOccurs I) :
    (compactPositionCodes I).length =
      I.system.universeSize + (compactNonAlphaCodes I).length := by
  classical
  have hSplit :=
    List.length_eq_length_filter_add
      (l := compactPositionCodes I)
      (fun c => decide (compactIsAlphaCode I c))
  rw [← compactAlphaPositionFilter_length_eq_universe (I := I) hEvery]
  simpa [compactAlphaPositionFilter, compactNonAlphaCodes] using hSplit

theorem compactNonAlphaCodes_length_eq_unselected_of_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected)
    (hEvery : compactEveryElementOccurs I) :
    (compactNonAlphaCodes I).length =
      (compactUnselectedPositionCodes I selected).length := by
  have hSelectedLen :=
    compactSelectedPositionCodes_length_eq_universe_of_exact
      (I := I) (selected := selected) hFamily hNodup hDisjoint hCovers
  have hBySelected :=
    compactPositionCodes_length_eq_selected_add_unselected
      (I := I) (selected := selected) hFamily hNodup
  have hByAlpha := compactPositionCodes_length_eq_alpha_add_nonAlpha (I := I) hEvery
  omega

structure CompactPositionData (I : ExactCoverInput) (c : Nat) where
  j : Nat
  j_lt : j < I.system.sets.length
  x : Nat
  x_mem : x ∈ compactSupport I (compactSourceSetAt I j)
  code_eq : c = compactPositionCode I x j

theorem compactPositionData_exists_of_mem {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactPositionCodes I) :
    Nonempty (CompactPositionData I c) := by
  rcases (mem_compactPositionCodes_iff I c).1 hc with ⟨j, hj, x, hx, hcode⟩
  exact ⟨{ j := j, j_lt := hj, x := x, x_mem := hx, code_eq := hcode }⟩

noncomputable def compactDecodedPosition (I : ExactCoverInput) (c : Nat) :
    Nat × Nat := by
  classical
  exact if h : c ∈ compactPositionCodes I then
    let w := Classical.choice (compactPositionData_exists_of_mem (I := I) (c := c) h)
    (w.x, w.j)
  else
    (0, 0)

theorem compactDecodedPosition_spec {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactPositionCodes I) :
    (compactDecodedPosition I c).2 < I.system.sets.length ∧
      (compactDecodedPosition I c).1 ∈
        compactSupport I (compactSourceSetAt I (compactDecodedPosition I c).2) ∧
      c = compactPositionCode I (compactDecodedPosition I c).1
        (compactDecodedPosition I c).2 := by
  classical
  let w := Classical.choice (compactPositionData_exists_of_mem (I := I) (c := c) hc)
  have hEq : compactDecodedPosition I c = (w.x, w.j) := by
    simp [compactDecodedPosition, hc, w]
  rw [hEq]
  exact ⟨w.j_lt, w.x_mem, w.code_eq⟩

noncomputable def compactDecodedNextCode (I : ExactCoverInput) (c : Nat) : Nat :=
  let p := compactDecodedPosition I c
  compactPositionCode I (compactNextInSet I p.2 p.1) p.2

noncomputable def compactFillerTripleForCode (I : ExactCoverInput)
    (beta c : Nat) : Nat × Nat × Nat :=
  (beta, c, compactDecodedNextCode I c)

theorem compactFillerTripleForCode_mem_filler {I : ExactCoverInput}
    {beta c : Nat}
    (hbeta : beta ∈ compactNonAlphaCodes I)
    (hc : c ∈ compactPositionCodes I) :
    compactFillerTripleForCode I beta c ∈ compactFillerTriples I := by
  rcases compactDecodedPosition_spec (I := I) (c := c) hc with ⟨hj, hx, hcode⟩
  have hEq :
      compactFillerTripleForCode I beta c =
        compactFillerTriple I beta (compactDecodedPosition I c).1
          (compactDecodedPosition I c).2 := by
    unfold compactFillerTripleForCode compactFillerTriple
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hcode
      · rfl
  exact (mem_compactFillerTriples_iff I (compactFillerTripleForCode I beta c)).2
    ⟨beta, hbeta, (compactDecodedPosition I c).2, hj,
      (compactDecodedPosition I c).1, hx, hEq⟩

theorem compactFillerTripleForCode_withinBounds {I : ExactCoverInput}
    {beta c : Nat}
    (hbeta : beta ∈ compactNonAlphaCodes I)
    (hc : c ∈ compactPositionCodes I) :
    TripleWithinBounds (compactMapCore I) (compactFillerTripleForCode I beta c) := by
  rcases compactDecodedPosition_spec (I := I) (c := c) hc with ⟨hj, hx, hcode⟩
  have hEq :
      compactFillerTripleForCode I beta c =
        compactFillerTriple I beta (compactDecodedPosition I c).1
          (compactDecodedPosition I c).2 := by
    unfold compactFillerTripleForCode compactFillerTriple
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hcode
      · rfl
  rw [hEq]
  exact compactFillerTriple_withinBounds (I := I) (beta := beta)
    (x := (compactDecodedPosition I c).1)
    (j := (compactDecodedPosition I c).2) hbeta hj hx

theorem compactNextCode_unselected_of_unselected {I : ExactCoverInput}
    {selected : List (List Nat)} {c : Nat}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hc : c ∈ compactUnselectedPositionCodes I selected) :
    compactDecodedNextCode I c ∈ compactUnselectedPositionCodes I selected := by
  rcases (mem_compactUnselectedPositionCodes_iff I selected c).1 hc with
    ⟨hcPos, hcNotSelected⟩
  rcases compactDecodedPosition_spec (I := I) (c := c) hcPos with
    ⟨hj, hx, hcode⟩
  let nextCode := compactDecodedNextCode I c
  have hNextPos : nextCode ∈ compactPositionCodes I := by
    simpa [nextCode] using
      compactNextCode_mem_positions (I := I) (j := (compactDecodedPosition I c).2)
        (x := (compactDecodedPosition I c).1) hj hx
  have hNextNotSelected :
      nextCode ∉ compactSelectedPositionCodes I selected := by
    intro hNextSelected
    have hCurrentSelected :
        compactPositionCode I (compactDecodedPosition I c).1
            (compactDecodedPosition I c).2 ∈
          compactSelectedPositionCodes I selected :=
      compactSelectedPositionCode_of_same_source (I := I) (selected := selected)
        hFamily hj
        (compactNextInSet_mem_support (I := I)
          (j := (compactDecodedPosition I c).2)
          (x := (compactDecodedPosition I c).1) hx)
        hx hNextSelected
    have hcSelected : c ∈ compactSelectedPositionCodes I selected := by
      rw [hcode]
      exact hCurrentSelected
    exact hcNotSelected hcSelected
  exact (mem_compactUnselectedPositionCodes_iff I selected nextCode).2
    ⟨hNextPos, hNextNotSelected⟩

/-! ### Compact forward witness assembly -/

noncomputable def compactSelectedCoverTriplesForSet (I : ExactCoverInput)
    (S : List Nat) : List (Nat × Nat × Nat) :=
  compactCoverTriplesForSet I (compactSelectedSetIndex I S)

noncomputable def compactSelectedCoverTriples (I : ExactCoverInput)
    (selected : List (List Nat)) : List (Nat × Nat × Nat) :=
  selected.flatMap (compactSelectedCoverTriplesForSet I)

noncomputable def compactSelectedFillerTriples (I : ExactCoverInput)
    (selected : List (List Nat)) : List (Nat × Nat × Nat) :=
  List.zipWith (fun beta c => compactFillerTripleForCode I beta c)
    (compactNonAlphaCodes I) (compactUnselectedPositionCodes I selected)

noncomputable def compactSelectedTriples (I : ExactCoverInput)
    (selected : List (List Nat)) : List (Nat × Nat × Nat) :=
  compactSelectedCoverTriples I selected ++ compactSelectedFillerTriples I selected

theorem compactSelectedCoverTriplesForSet_length_eq_positions
    (I : ExactCoverInput) (S : List Nat) :
    (compactSelectedCoverTriplesForSet I S).length =
      (compactSelectedPositionCodesForSet I S).length := by
  simp [compactSelectedCoverTriplesForSet, compactSelectedPositionCodesForSet,
    compactCoverTriplesForSet, compactPositionCodesForSet]

theorem compactSelectedCoverTriples_length_eq_positions
    (I : ExactCoverInput) (selected : List (List Nat)) :
    (compactSelectedCoverTriples I selected).length =
      (compactSelectedPositionCodes I selected).length := by
  induction selected with
  | nil =>
      simp [compactSelectedCoverTriples, compactSelectedPositionCodes]
  | cons S selected ih =>
      simp [compactSelectedCoverTriples, compactSelectedPositionCodes,
        compactSelectedCoverTriplesForSet_length_eq_positions]

theorem compactSelectedFillerTriples_length_of_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected)
    (hEvery : compactEveryElementOccurs I) :
    (compactSelectedFillerTriples I selected).length =
      (compactNonAlphaCodes I).length := by
  have hLen :=
    compactNonAlphaCodes_length_eq_unselected_of_exact
      (I := I) (selected := selected) hFamily hNodup hDisjoint hCovers hEvery
  simp [compactSelectedFillerTriples, hLen]

theorem compactSelectedTriples_length_eq_k_of_exact {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected)
    (hEvery : compactEveryElementOccurs I) :
    (compactSelectedTriples I selected).length = (compactMapCore I).k := by
  have hCoverLen :=
    compactSelectedCoverTriples_length_eq_positions I selected
  have hSelectedLen :=
    compactSelectedPositionCodes_length_eq_universe_of_exact
      (I := I) (selected := selected) hFamily hNodup hDisjoint hCovers
  have hFillerLen :=
    compactSelectedFillerTriples_length_of_exact
      (I := I) (selected := selected) hFamily hNodup hDisjoint hCovers hEvery
  have hAlphaLen := compactPositionCodes_length_eq_alpha_add_nonAlpha (I := I) hEvery
  simp [compactSelectedTriples, compactMapCore, hCoverLen, hSelectedLen, hFillerLen] at *
  omega

theorem mem_zipWith₂ {α β γ : Type*} (f : α → β → γ)
    {xs : List α} {ys : List β} {z : γ}
    (hz : z ∈ List.zipWith f xs ys) :
    ∃ x, x ∈ xs ∧ ∃ y, y ∈ ys ∧ z = f x y := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp at hz
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hz
      | cons y ys =>
          simp at hz
          rcases hz with hz | hz
          · exact ⟨x, by simp, y, by simp, hz⟩
          · rcases ih hz with ⟨x', hx', y', hy', hz'⟩
            exact ⟨x', by simp [hx'], y', by simp [hy'], hz'⟩

theorem map_zipWith_left_sublist {α β γ δ : Type*}
    (f : α → β → γ) (g : γ → δ) (h : α → δ)
    (H : ∀ x y, g (f x y) = h x) :
    ∀ (xs : List α) (ys : List β),
      List.Sublist ((List.zipWith f xs ys).map g) (xs.map h)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
      change List.Sublist
        (g (f x y) :: (List.zipWith f xs ys).map g)
        (h x :: xs.map h)
      rw [H x y]
      exact List.Sublist.cons₂ _ (map_zipWith_left_sublist f g h H xs ys)

theorem map_zipWith_right_sublist {α β γ δ : Type*}
    (f : α → β → γ) (g : γ → δ) (h : β → δ)
    (H : ∀ x y, g (f x y) = h y) :
    ∀ (xs : List α) (ys : List β),
      List.Sublist ((List.zipWith f xs ys).map g) (ys.map h)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
      change List.Sublist
        (g (f x y) :: (List.zipWith f xs ys).map g)
        (h y :: ys.map h)
      rw [H x y]
      exact List.Sublist.cons₂ _ (map_zipWith_right_sublist f g h H xs ys)

theorem compactUnselectedPositionCodes_nodup (I : ExactCoverInput)
    (selected : List (List Nat)) :
    (compactUnselectedPositionCodes I selected).Nodup := by
  classical
  simpa [compactUnselectedPositionCodes] using
    (compactPositionCodes_nodup I).filter fun c =>
      !decide (c ∈ compactSelectedPositionCodes I selected)

theorem compactSelected_unselectedPositionCodes_disjoint (I : ExactCoverInput)
    (selected : List (List Nat)) :
    List.Disjoint
      (compactSelectedPositionCodes I selected)
      (compactUnselectedPositionCodes I selected) := by
  intro c hcSelected hcUnselected
  exact ((mem_compactUnselectedPositionCodes_iff I selected c).1 hcUnselected).2 hcSelected

theorem compactDecodedNextCode_mem_positions {I : ExactCoverInput} {c : Nat}
    (hc : c ∈ compactPositionCodes I) :
    compactDecodedNextCode I c ∈ compactPositionCodes I := by
  rcases compactDecodedPosition_spec (I := I) (c := c) hc with ⟨hj, hx, _hcode⟩
  simpa [compactDecodedNextCode] using
    compactNextCode_mem_positions (I := I)
      (j := (compactDecodedPosition I c).2)
      (x := (compactDecodedPosition I c).1) hj hx

theorem compactDecodedNextCode_inj_on_positions {I : ExactCoverInput}
    {c d : Nat}
    (hc : c ∈ compactPositionCodes I)
    (hd : d ∈ compactPositionCodes I)
    (hnext : compactDecodedNextCode I c = compactDecodedNextCode I d) :
    c = d := by
  rcases compactDecodedPosition_spec (I := I) (c := c) hc with ⟨hjc, hxc, hcodec⟩
  rcases compactDecodedPosition_spec (I := I) (c := d) hd with ⟨hjd, hxd, hcoded⟩
  have hNextMemC :=
    compactNextInSet_mem_support (I := I)
      (j := (compactDecodedPosition I c).2)
      (x := (compactDecodedPosition I c).1) hxc
  have hNextMemD :=
    compactNextInSet_mem_support (I := I)
      (j := (compactDecodedPosition I d).2)
      (x := (compactDecodedPosition I d).1) hxd
  have hNextLtC :=
    ((mem_compactSupport_iff I
      (compactSourceSetAt I (compactDecodedPosition I c).2)
      (compactNextInSet I (compactDecodedPosition I c).2
        (compactDecodedPosition I c).1)).1 hNextMemC).1
  have hNextLtD :=
    ((mem_compactSupport_iff I
      (compactSourceSetAt I (compactDecodedPosition I d).2)
      (compactNextInSet I (compactDecodedPosition I d).2
        (compactDecodedPosition I d).1)).1 hNextMemD).1
  have hCodeEq :
      compactPositionCode I
          (compactNextInSet I (compactDecodedPosition I c).2
            (compactDecodedPosition I c).1)
          (compactDecodedPosition I c).2 =
        compactPositionCode I
          (compactNextInSet I (compactDecodedPosition I d).2
            (compactDecodedPosition I d).1)
          (compactDecodedPosition I d).2 := by
    simpa [compactDecodedNextCode] using hnext
  have hNextInfo :=
    compactPositionCode_inj (I := I) hNextLtC hNextLtD hCodeEq
  have hSet :
      (compactDecodedPosition I c).2 = (compactDecodedPosition I d).2 := hNextInfo.2
  have hNextValue :
      compactNextInSet I (compactDecodedPosition I c).2
          (compactDecodedPosition I c).1 =
        compactNextInSet I (compactDecodedPosition I c).2
          (compactDecodedPosition I d).1 := by
    simpa [hSet] using hNextInfo.1
  have hxdSame :
      (compactDecodedPosition I d).1 ∈
        compactSupport I (compactSourceSetAt I (compactDecodedPosition I c).2) := by
    simpa [hSet] using hxd
  have hElem :
      (compactDecodedPosition I c).1 = (compactDecodedPosition I d).1 :=
    compactNextInSet_inj (I := I)
      (j := (compactDecodedPosition I c).2) hxc hxdSame hNextValue
  rw [hcodec, hcoded, hSet, hElem]

theorem compactUnselectedNextCodes_nodup (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactUnselectedPositionCodes I selected).map
      (compactDecodedNextCode I)).Nodup := by
  exact (compactUnselectedPositionCodes_nodup I selected).map_on (by
    intro c hc d hd hEq
    have hcPos := ((mem_compactUnselectedPositionCodes_iff I selected c).1 hc).1
    have hdPos := ((mem_compactUnselectedPositionCodes_iff I selected d).1 hd).1
    exact compactDecodedNextCode_inj_on_positions (I := I) hcPos hdPos hEq)

theorem compactUnselected_nextCodes_disjoint_selected {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    List.Disjoint
      (compactSelectedPositionCodes I selected)
      ((compactUnselectedPositionCodes I selected).map
        (compactDecodedNextCode I)) := by
  intro c hcSelected hcNext
  rcases List.mem_map.mp hcNext with ⟨d, hdUnselected, rfl⟩
  have hdNextUnselected :=
    compactNextCode_unselected_of_unselected (I := I)
      (selected := selected) hFamily hdUnselected
  exact ((mem_compactUnselectedPositionCodes_iff I selected
    (compactDecodedNextCode I d)).1 hdNextUnselected).2 hcSelected

theorem compactSelectedFillerTriples_x_nodup (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.1).Nodup := by
  have hSub :
      List.Sublist
        ((compactSelectedFillerTriples I selected).map fun t => t.1)
        ((compactNonAlphaCodes I).map id) := by
    simpa [compactSelectedFillerTriples] using
      map_zipWith_left_sublist
        (fun beta c => compactFillerTripleForCode I beta c)
        (fun t : Nat × Nat × Nat => t.1) id
        (by intro beta c; rfl)
        (compactNonAlphaCodes I) (compactUnselectedPositionCodes I selected)
  simpa using ((compactNonAlphaCodes_nodup I).map Function.injective_id).sublist hSub

theorem compactSelectedFillerTriples_y_nodup (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.2.1).Nodup := by
  have hSub :
      List.Sublist
        ((compactSelectedFillerTriples I selected).map fun t => t.2.1)
        ((compactUnselectedPositionCodes I selected).map id) := by
    simpa [compactSelectedFillerTriples, compactFillerTripleForCode] using
      map_zipWith_right_sublist
        (fun beta c => compactFillerTripleForCode I beta c)
        (fun t : Nat × Nat × Nat => t.2.1) id
        (by intro beta c; rfl)
        (compactNonAlphaCodes I) (compactUnselectedPositionCodes I selected)
  simpa using
    ((compactUnselectedPositionCodes_nodup I selected).map Function.injective_id).sublist hSub

theorem compactSelectedFillerTriples_z_nodup (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.2.2).Nodup := by
  have hSub :
      List.Sublist
        ((compactSelectedFillerTriples I selected).map fun t => t.2.2)
        ((compactUnselectedPositionCodes I selected).map (compactDecodedNextCode I)) := by
    simpa [compactSelectedFillerTriples, compactFillerTripleForCode] using
      map_zipWith_right_sublist
        (fun beta c => compactFillerTripleForCode I beta c)
        (fun t : Nat × Nat × Nat => t.2.2) (compactDecodedNextCode I)
        (by intro beta c; rfl)
        (compactNonAlphaCodes I) (compactUnselectedPositionCodes I selected)
  exact (compactUnselectedNextCodes_nodup I selected).sublist hSub

noncomputable def compactSelectedAlphaCodesForSet (I : ExactCoverInput)
    (S : List Nat) : List Nat :=
  (compactSupport I S).map (compactAlphaCode I)

noncomputable def compactSelectedAlphaCodes (I : ExactCoverInput)
    (selected : List (List Nat)) : List Nat :=
  selected.flatMap (compactSelectedAlphaCodesForSet I)

theorem compactSelectedAlphaCodesForSet_nodup (I : ExactCoverInput)
    (S : List Nat) :
    (compactSelectedAlphaCodesForSet I S).Nodup := by
  exact (compactSupport_nodup I S).map_on (by
    intro x hx y hy hcode
    have hxLt := ((mem_compactSupport_iff I S x).1 hx).1
    have hyLt := ((mem_compactSupport_iff I S y).1 hy).1
    exact compactAlphaCode_inj_of_lt (I := I) hxLt hyLt hcode)

theorem compactSelectedAlphaCodesForSet_disjoint_of_ne {I : ExactCoverInput}
    {selected : List (List Nat)} {S T : List Nat}
    (hSSelected : S ∈ selected)
    (hTSelected : T ∈ selected)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hNe : S ≠ T) :
    List.Disjoint
      (compactSelectedAlphaCodesForSet I S)
      (compactSelectedAlphaCodesForSet I T) := by
  intro c hcS hcT
  rcases List.mem_map.mp hcS with ⟨x, hx, hcx⟩
  rcases List.mem_map.mp hcT with ⟨y, hy, hcy⟩
  have hxLt := ((mem_compactSupport_iff I S x).1 hx).1
  have hyLt := ((mem_compactSupport_iff I T y).1 hy).1
  have hxy : x = y :=
    compactAlphaCode_inj_of_lt (I := I) hxLt hyLt (by rw [hcx, hcy])
  subst y
  exact hDisjoint S hSSelected T hTSelected hNe x
    ((mem_compactSupport_iff I S x).1 hx).2
    ((mem_compactSupport_iff I T x).1 hy).2

theorem compactSelectedAlphaCodes_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    (compactSelectedAlphaCodes I selected).Nodup := by
  have hLocal :
      ∀ S ∈ selected, (compactSelectedAlphaCodesForSet I S).Nodup := by
    intro S _hS
    exact compactSelectedAlphaCodesForSet_nodup I S
  have hPair :
      selected.Pairwise
        (fun S T =>
          List.Disjoint
            (compactSelectedAlphaCodesForSet I S)
            (compactSelectedAlphaCodesForSet I T)) := by
    refine hNodup.pairwise_of_forall_ne ?_
    intro S hS T hT hNe
    exact compactSelectedAlphaCodesForSet_disjoint_of_ne
      (I := I) (selected := selected) hS hT hDisjoint hNe
  have hFlat :=
    (List.nodup_flatMap (l₁ := selected)
      (f := compactSelectedAlphaCodesForSet I)).2 ⟨hLocal, hPair⟩
  simpa [compactSelectedAlphaCodes] using hFlat

theorem compactSelectedAlphaCodes_subset_alphaCodes {I : ExactCoverInput}
    {selected : List (List Nat)} :
    compactSelectedAlphaCodes I selected ⊆ compactAlphaCodes I := by
  intro c hc
  rcases List.mem_flatMap.mp (by simpa [compactSelectedAlphaCodes] using hc) with
    ⟨S, _hS, hcS⟩
  rcases List.mem_map.mp (by simpa [compactSelectedAlphaCodesForSet] using hcS) with
    ⟨x, hx, hcode⟩
  have hxLt := ((mem_compactSupport_iff I S x).1 hx).1
  exact List.mem_map.mpr ⟨x, by simpa using hxLt, hcode⟩

theorem compactSelectedCoverTriples_x_eq_alphaCodes {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    (compactSelectedCoverTriples I selected).map (fun t => t.1) =
      compactSelectedAlphaCodes I selected := by
  induction selected with
  | nil =>
      simp [compactSelectedCoverTriples, compactSelectedAlphaCodes]
  | cons S selected ih =>
      have hS : IsSetInFamily I.system S := hFamily S (by simp)
      have hTail : ∀ T ∈ selected, IsSetInFamily I.system T := by
        intro T hT
        exact hFamily T (by simp [hT])
      have hSource :
          compactSourceSetAt I (compactSelectedSetIndex I S) = S :=
        compactSourceSetAt_idxOf_eq (I := I) (S := S)
          (by simpa [IsSetInFamily] using hS)
      have hTailEq :
          List.map (fun t : Nat × Nat × Nat => t.1)
              (List.flatMap (compactSelectedCoverTriplesForSet I) selected) =
            List.flatMap (compactSelectedAlphaCodesForSet I) selected := by
        simpa [compactSelectedCoverTriples, compactSelectedAlphaCodes] using ih hTail
      simp [compactSelectedCoverTriples, compactSelectedCoverTriplesForSet,
        compactCoverTriplesForSet, compactCoverTriple, compactSelectedAlphaCodes,
        compactSelectedAlphaCodesForSet, hSource, Function.comp_def, hTailEq]

theorem compactSelectedCoverTriples_y_eq_positions (I : ExactCoverInput)
    (selected : List (List Nat)) :
    (compactSelectedCoverTriples I selected).map (fun t => t.2.1) =
      compactSelectedPositionCodes I selected := by
  induction selected with
  | nil =>
      simp [compactSelectedCoverTriples, compactSelectedPositionCodes]
  | cons S selected ih =>
      have hTailEq :
          List.map (fun t : Nat × Nat × Nat => t.2.1)
              (List.flatMap (compactSelectedCoverTriplesForSet I) selected) =
            List.flatMap (compactSelectedPositionCodesForSet I) selected := by
        simpa [compactSelectedCoverTriples, compactSelectedPositionCodes] using ih
      simp [compactSelectedCoverTriples, compactSelectedCoverTriplesForSet,
        compactCoverTriplesForSet, compactCoverTriple, compactSelectedPositionCodes,
        compactSelectedPositionCodesForSet, compactPositionCodesForSet,
        Function.comp_def, hTailEq]

theorem compactSelectedCoverTriples_z_eq_positions (I : ExactCoverInput)
    (selected : List (List Nat)) :
    (compactSelectedCoverTriples I selected).map (fun t => t.2.2) =
      compactSelectedPositionCodes I selected := by
  induction selected with
  | nil =>
      simp [compactSelectedCoverTriples, compactSelectedPositionCodes]
  | cons S selected ih =>
      have hTailEq :
          List.map (fun t : Nat × Nat × Nat => t.2.2)
              (List.flatMap (compactSelectedCoverTriplesForSet I) selected) =
            List.flatMap (compactSelectedPositionCodesForSet I) selected := by
        simpa [compactSelectedCoverTriples, compactSelectedPositionCodes] using ih
      simp [compactSelectedCoverTriples, compactSelectedCoverTriplesForSet,
        compactCoverTriplesForSet, compactCoverTriple, compactSelectedPositionCodes,
        compactSelectedPositionCodesForSet, compactPositionCodesForSet,
        Function.comp_def, hTailEq]

theorem compactSelectedCoverTriples_x_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected) :
    ((compactSelectedCoverTriples I selected).map fun t => t.1).Nodup := by
  rw [compactSelectedCoverTriples_x_eq_alphaCodes (I := I) hFamily]
  exact compactSelectedAlphaCodes_nodup (I := I) hNodup hDisjoint

theorem compactSelectedCoverTriples_y_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    ((compactSelectedCoverTriples I selected).map fun t => t.2.1).Nodup := by
  rw [compactSelectedCoverTriples_y_eq_positions]
  exact compactSelectedPositionCodes_nodup (I := I) hFamily hNodup

theorem compactSelectedCoverTriples_z_nodup {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup) :
    ((compactSelectedCoverTriples I selected).map fun t => t.2.2).Nodup := by
  rw [compactSelectedCoverTriples_z_eq_positions]
  exact compactSelectedPositionCodes_nodup (I := I) hFamily hNodup

theorem compactSelectedFillerTriples_x_subset_nonAlpha (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.1) ⊆
      compactNonAlphaCodes I := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
  rcases mem_zipWith₂ (fun beta c => compactFillerTripleForCode I beta c) ht with
    ⟨beta, hbeta, pos, _hpos, htEq⟩
  rw [htEq]
  exact hbeta

theorem compactSelectedFillerTriples_y_subset_unselected (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.2.1) ⊆
      compactUnselectedPositionCodes I selected := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
  rcases mem_zipWith₂ (fun beta c => compactFillerTripleForCode I beta c) ht with
    ⟨beta, _hbeta, pos, hpos, htEq⟩
  rw [htEq]
  exact hpos

theorem compactSelectedFillerTriples_z_subset_nextCodes (I : ExactCoverInput)
    (selected : List (List Nat)) :
    ((compactSelectedFillerTriples I selected).map fun t => t.2.2) ⊆
      (compactUnselectedPositionCodes I selected).map (compactDecodedNextCode I) := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨t, ht, rfl⟩
  rcases mem_zipWith₂ (fun beta c => compactFillerTripleForCode I beta c) ht with
    ⟨beta, _hbeta, pos, hpos, htEq⟩
  rw [htEq]
  exact List.mem_map.mpr ⟨pos, hpos, rfl⟩

end ThreeDimensionalMatching
end Karp21
end ComplexityReduction
