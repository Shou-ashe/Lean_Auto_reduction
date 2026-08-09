import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part1

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

/-- Entry arcs from selector vertices into the first incidence of a chosen source vertex. -/
noncomputable def textbookEntryArcs (I : VertexCoverInput) : List (Nat × Nat) := by
  classical
  exact (((List.range I.k).product (sourceIncidences I)).filter fun pair =>
    decide (FirstIncident I pair.2.1 pair.2.2)).map fun pair =>
      (textbookSelectorVertex pair.1,
        textbookIncidenceVertex I pair.2.1 pair.2.2 0)

theorem mem_textbookEntryArcs {I : VertexCoverInput} {slot u i : Nat}
    (hslot : slot < I.k) (hFirst : FirstIncident I u i) :
    (textbookSelectorVertex slot, textbookIncidenceVertex I u i 0) ∈
      textbookEntryArcs I := by
  classical
  have hInc : (u, i) ∈ sourceIncidences I := sourceIncidence_mem_of_first hFirst
  simp [textbookEntryArcs]
  refine ⟨slot, u, i, ?_, ?_⟩
  · exact ⟨⟨hslot, hInc⟩, hFirst⟩
  · exact ⟨rfl, rfl⟩

/-- Exit arcs from the last incidence of a chosen source vertex back to the next selector. -/
noncomputable def textbookExitArcs (I : VertexCoverInput) : List (Nat × Nat) := by
  classical
  exact (((List.range I.k).product (sourceIncidences I)).filter fun pair =>
    decide (LastIncident I pair.2.1 pair.2.2)).map fun pair =>
      (textbookIncidenceVertex I pair.2.1 pair.2.2 1,
        textbookSelectorVertex (textbookNextSelector I pair.1))

theorem mem_textbookExitArcs {I : VertexCoverInput} {slot u i : Nat}
    (hslot : slot < I.k) (hLast : LastIncident I u i) :
    (textbookIncidenceVertex I u i 1,
      textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookExitArcs I := by
  classical
  have hInc : (u, i) ∈ sourceIncidences I := sourceIncidence_mem_of_last hLast
  simp [textbookExitArcs]
  refine ⟨slot, u, i, ?_, ?_⟩
  · exact ⟨⟨hslot, hInc⟩, hLast⟩
  · exact ⟨rfl, rfl⟩

/-- Edge list for the partially reconstructed Karp selector/path gadget. -/
noncomputable def textbookEdgeList (I : VertexCoverInput) : List (Nat × Nat) :=
  textbookIncidenceArcs I ++
    textbookCrossArcs I ++
    textbookChainArcs I ++
    textbookTrackChainArcs I ++
    textbookSelectorSkipArcs I ++
    textbookEntryArcs I ++
    textbookExitArcs I ++
    textbookTrackEntryArcs I ++
    textbookTrackExitArcs I

theorem mem_textbookEdgeList_incidence {I : VertexCoverInput} {u i : Nat}
    (hInc : (u, i) ∈ sourceIncidences I) :
    (textbookIncidenceVertex I u i 0, textbookIncidenceVertex I u i 1) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookIncidenceArcs hInc]

theorem mem_textbookEdgeList_cross_bit0 {I : VertexCoverInput} {u v i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) (hv : (v, i) ∈ sourceIncidences I)
    (huv : u ≠ v) :
    (textbookIncidenceVertex I u i 0, textbookIncidenceVertex I v i 0) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookCrossArcs_bit0 hu hv huv]

theorem mem_textbookEdgeList_cross_bit1 {I : VertexCoverInput} {u v i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) (hv : (v, i) ∈ sourceIncidences I)
    (huv : u ≠ v) :
    (textbookIncidenceVertex I u i 1, textbookIncidenceVertex I v i 1) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookCrossArcs_bit1 hu hv huv]

theorem mem_textbookEdgeList_chain {I : VertexCoverInput} {u i j : Nat}
    (hConsec : ConsecutiveIncident I u i j) :
    (textbookIncidenceVertex I u i 1, textbookIncidenceVertex I u j 0) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookChainArcs hConsec]

theorem mem_textbookEdgeList_selector_skip {I : VertexCoverInput} {slot : Nat}
    (hslot : slot < I.k) :
    (textbookSelectorVertex slot, textbookSelectorVertex (textbookNextSelector I slot)) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookSelectorSkipArcs hslot]

theorem mem_textbookEdgeList_entry {I : VertexCoverInput} {slot u i : Nat}
    (hslot : slot < I.k) (hFirst : FirstIncident I u i) :
    (textbookSelectorVertex slot, textbookIncidenceVertex I u i 0) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookEntryArcs hslot hFirst]

theorem mem_textbookEdgeList_exit {I : VertexCoverInput} {slot u i : Nat}
    (hslot : slot < I.k) (hLast : LastIncident I u i) :
    (textbookIncidenceVertex I u i 1,
      textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookExitArcs hslot hLast]

theorem mem_textbookEdgeList_track_chain
    {I : VertexCoverInput} {u : Nat} (hu : u < I.graph.vertices) {ui uj : Nat × Nat}
    (hpair : (ui, uj) ∈ (incidencesOfVertex I u).consecutivePairs) :
    (textbookIncidenceVertex I ui.1 ui.2 1,
      textbookIncidenceVertex I uj.1 uj.2 0) ∈ textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookTrackChainArcs hu hpair]

theorem mem_textbookEdgeList_track_entry
    {I : VertexCoverInput} {slot u : Nat} {ui : Nat × Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices)
    (hHead : (incidencesOfVertex I u).head? = some ui) :
    (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0) ∈
      textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookTrackEntryArcs hslot hu hHead]

theorem mem_textbookEdgeList_track_exit
    {I : VertexCoverInput} {slot u : Nat} {ui : Nat × Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices)
    (hLast : (incidencesOfVertex I u).getLast? = some ui) :
    (textbookIncidenceVertex I ui.1 ui.2 1,
      textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookEdgeList I := by
  simp [textbookEdgeList, mem_textbookTrackExitArcs hslot hu hLast]

theorem textbookEdgeList_selector_out
    {I : VertexCoverInput} {slot y : Nat} (hslot : slot < I.k)
    (he : (textbookSelectorVertex slot, y) ∈ textbookEdgeList I) :
    y = textbookSelectorVertex (textbookNextSelector I slot) ∨
      ∃ u i, (u, i) ∈ sourceIncidences I ∧
        y = textbookIncidenceVertex I u i 0 := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, _hui, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨u, i, v, _hData, hEdge⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨hFirst, _hSecond⟩
      exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
    · rcases hEdge with ⟨hFirst, _hSecond⟩
      exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heChain with ⟨pair, _hpair, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨u, _hu, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, _hpair, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rcases List.mem_map.mp heSkip with ⟨slot', _hslotMem, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    have hSlotEq : slot' = slot := by
      simpa [textbookSelectorVertex] using hFirst
    have hSecond := congrArg Prod.snd hEq
    left
    simpa [hSlotEq] using hSecond.symm
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot', ui⟩
    rcases ui with ⟨u, i⟩
    have hFirstIncident : FirstIncident I u i := by
      simpa using (of_decide_eq_true hFilter.2)
    have hInc : (u, i) ∈ sourceIncidences I := sourceIncidence_mem_of_first hFirstIncident
    right
    exact ⟨u, i, hInc, hSecond.symm⟩
  · rcases List.mem_map.mp heExit with ⟨pair, _hpair, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, _hpair, hePair⟩
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨_hFirst, hSecond⟩
        rcases pair with ⟨slot', u⟩
        rcases ui with ⟨w, i⟩
        have hui : (w, i) ∈ incidencesOfVertex I u := mem_of_head?_eq_some hHead
        have hInc : (w, i) ∈ sourceIncidences I :=
          (mem_incidencesOfVertex_iff I u (w, i)).1 hui |>.1
        right
        exact ⟨w, i, hInc, hSecond⟩
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, _hpair, hePair⟩
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)

theorem textbookEdgeList_incidence_bit0_out
    {I : VertexCoverInput} {u i y : Nat} (hInc : (u, i) ∈ sourceIncidences I)
    (he : (textbookIncidenceVertex I u i 0, y) ∈ textbookEdgeList I) :
    y = textbookIncidenceVertex I u i 1 ∨
      ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        y = textbookIncidenceVertex I v i 0 := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, hui, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hui hInc (by omega) (by omega) hFirst).1
    left
    cases ui with
    | mk v j =>
        have hvu : v = u := (Prod.ext_iff.mp hPairEq).1
        have hji : j = i := (Prod.ext_iff.mp hPairEq).2
        simpa [hvu, hji] using hSecond.symm
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨v, j, w, hData, hEdge⟩
    rcases hData with ⟨⟨hvj, hwj⟩, hvw⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨hFirst, hSecond⟩
      have hPairEq := (textbookIncidenceVertex_inj hvj hInc (by omega) (by omega)
        hFirst.symm).1
      have hvu : v = u := (Prod.ext_iff.mp hPairEq).1
      have hji : j = i := (Prod.ext_iff.mp hPairEq).2
      right
      refine ⟨w, ?_, ?_, ?_⟩
      · simpa [hji] using hwj
      · intro hwu
        exact hvw (by omega)
      · simpa [hji] using hSecond
    · rcases hEdge with ⟨hFirst, _hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hvj hInc (by omega) (by omega) (by omega)
          hFirst.symm)
  · rcases List.mem_map.mp heChain with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hFilterData :
        pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := by
      simpa using of_decide_eq_true hFilter.2
    have hConsec : ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := hFilterData.2
    have hLeft : (pair.1.1, pair.1.2) ∈ sourceIncidences I :=
      sourceIncidence_mem_left_of_consecutive hConsec
    have hFirst := congrArg Prod.fst hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hLeft hInc (by omega) (by omega) (by omega)
        hFirst)
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨v, _hvRange, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, hpair, hEq⟩
    have hLeftMem : pair.1 ∈ incidencesOfVertex I v :=
      left_mem_of_mem_consecutivePairs hpair
    have hLeft : pair.1 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.1
    have hFirst := congrArg Prod.fst hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hLeft hInc (by omega) (by omega) (by omega)
        hFirst)
  · rcases List.mem_map.mp heSkip with ⟨slot, hslotMem, hEq⟩
    have hslot : slot < I.k := List.mem_range.mp hslotMem
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot, ui⟩
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : slot < I.k := List.mem_range.mp hSlotMem
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heExit with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hIncLeft : pair.2 ∈ sourceIncidences I := (List.mem_product.mp hFilter.1).2
    have hFirst := congrArg Prod.fst hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hIncLeft hInc (by omega) (by omega) (by omega)
        hFirst)
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, _hpair, hePair⟩
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        have hui : ui ∈ incidencesOfVertex I pair.2 := mem_of_getLast?_eq_some hLast
        have hIncLeft : ui ∈ sourceIncidences I :=
          (mem_incidencesOfVertex_iff I pair.2 ui).1 hui |>.1
        exact False.elim
          (textbookIncidenceVertex_ne_of_bit_ne hIncLeft hInc (by omega) (by omega)
            (by omega) hFirst.symm)

theorem textbookEdgeList_incidence_bit1_out
    {I : VertexCoverInput} {u i y : Nat} (hInc : (u, i) ∈ sourceIncidences I)
    (he : (textbookIncidenceVertex I u i 1, y) ∈ textbookEdgeList I) :
    (∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        y = textbookIncidenceVertex I v i 1) ∨
      (∃ j, (u, j) ∈ sourceIncidences I ∧
        y = textbookIncidenceVertex I u j 0) ∨
      ∃ slot, slot < I.k ∧
        y = textbookSelectorVertex (textbookNextSelector I slot) := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, hui, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hui hInc (by omega) (by omega) (by omega)
        hFirst)
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨v, j, w, hData, hEdge⟩
    rcases hData with ⟨⟨hvj, hwj⟩, hvw⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨hFirst, _hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hvj hInc (by omega) (by omega) (by omega)
          hFirst.symm)
    · rcases hEdge with ⟨hFirst, hSecond⟩
      have hPairEq := (textbookIncidenceVertex_inj hvj hInc (by omega) (by omega)
        hFirst.symm).1
      have hvu : v = u := (Prod.ext_iff.mp hPairEq).1
      have hji : j = i := (Prod.ext_iff.mp hPairEq).2
      left
      refine ⟨w, ?_, ?_, ?_⟩
      · simpa [hji] using hwj
      · intro hwu
        exact hvw (by omega)
      · simpa [hji] using hSecond
  · rcases List.mem_map.mp heChain with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hFilterData :
        pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := by
      simpa using of_decide_eq_true hFilter.2
    have hConsec : ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := hFilterData.2
    have hLeft : (pair.1.1, pair.1.2) ∈ sourceIncidences I :=
      sourceIncidence_mem_left_of_consecutive hConsec
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hLeft hInc (by omega) (by omega)
      hFirst).1
    have hpu : pair.1.1 = u := (Prod.ext_iff.mp hPairEq).1
    have hpi : pair.1.2 = i := (Prod.ext_iff.mp hPairEq).2
    right
    left
    refine ⟨pair.2.2, ?_, ?_⟩
    · have hSameSource : pair.2.1 = u := by
        exact hFilterData.1.symm.trans hpu
      have hRight : (u, pair.2.2) ∈ sourceIncidences I :=
        (mem_sourceIncidences_iff I (u, pair.2.2)).2 (by
          simpa [hpu] using hConsec.2.1)
      exact hRight
    · have hSameSource : pair.2.1 = u := by
        exact hFilterData.1.symm.trans hpu
      simpa [hSameSource] using hSecond.symm
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨v, _hvRange, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, hpair, hEq⟩
    have hLeftMem : pair.1 ∈ incidencesOfVertex I v :=
      left_mem_of_mem_consecutivePairs hpair
    have hRightMem : pair.2 ∈ incidencesOfVertex I v :=
      right_mem_of_mem_consecutivePairs hpair
    have hLeft : pair.1 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.1
    have hRight : pair.2 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.1
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hLeft hInc (by omega) (by omega)
      hFirst).1
    right
    left
    refine ⟨pair.2.2, ?_, ?_⟩
    · have hLeftSource : pair.1.1 = u := (Prod.ext_iff.mp hPairEq).1
      have hRightSource : pair.2.1 = u := by
        have hL := (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.2
        have hR := (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.2
        exact hR.trans hL.symm |>.trans hLeftSource
      have hPair2 : pair.2 = (u, pair.2.2) := by
        exact Prod.ext hRightSource rfl
      rw [hPair2] at hRight
      exact hRight
    · have hLeftSource : pair.1.1 = u := (Prod.ext_iff.mp hPairEq).1
      have hRightSource : pair.2.1 = u := by
        have hL := (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.2
        have hR := (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.2
        exact hR.trans hL.symm |>.trans hLeftSource
      simpa [hRightSource] using hSecond.symm
  · rcases List.mem_map.mp heSkip with ⟨slot, hslotMem, hEq⟩
    have hslot : slot < I.k := List.mem_range.mp hslotMem
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot, ui⟩
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : slot < I.k := List.mem_range.mp hSlotMem
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heExit with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : pair.1 < I.k := List.mem_range.mp hSlotMem
    have hIncLeft : pair.2 ∈ sourceIncidences I := (List.mem_product.mp hFilter.1).2
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hIncLeft hInc (by omega) (by omega)
      hFirst).1
    right
    right
    exact ⟨pair.1, hslot, hSecond.symm⟩
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨hFirst, hSecond⟩
        have hui : ui ∈ incidencesOfVertex I pair.2 := mem_of_getLast?_eq_some hLast
        have hIncLeft : ui ∈ sourceIncidences I :=
          (mem_incidencesOfVertex_iff I pair.2 ui).1 hui |>.1
        have hPairEq := (textbookIncidenceVertex_inj hIncLeft hInc (by omega) (by omega)
          hFirst.symm).1
        right
        right
        exact ⟨pair.1, hslot, hSecond⟩

theorem textbookEdgeList_incidence_bit0_in
    {I : VertexCoverInput} {u i x : Nat} (hInc : (u, i) ∈ sourceIncidences I)
    (he : (x, textbookIncidenceVertex I u i 0) ∈ textbookEdgeList I) :
    (∃ slot, slot < I.k ∧ x = textbookSelectorVertex slot) ∨
      (∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        x = textbookIncidenceVertex I v i 0) ∨
      ∃ j, (u, j) ∈ sourceIncidences I ∧
        x = textbookIncidenceVertex I u j 1 := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, hui, hEq⟩
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hui hInc (by omega) (by omega) (by omega)
        hSecond)
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨v, j, w, hData, hEdge⟩
    rcases hData with ⟨⟨hvj, hwj⟩, hvw⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨hFirst, hSecond⟩
      have hPairEq := (textbookIncidenceVertex_inj hwj hInc (by omega) (by omega)
        hSecond.symm).1
      have hwi : w = u := (Prod.ext_iff.mp hPairEq).1
      have hji : j = i := (Prod.ext_iff.mp hPairEq).2
      right
      left
      refine ⟨v, ?_, ?_, ?_⟩
      · simpa [hji] using hvj
      · intro hvu
        exact hvw (by omega)
      · simpa [hji] using hFirst
    · rcases hEdge with ⟨_hFirst, hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hwj hInc (by omega) (by omega) (by omega)
          hSecond.symm)
  · rcases List.mem_map.mp heChain with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hFilterData :
        pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := by
      simpa using of_decide_eq_true hFilter.2
    have hConsec : ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := hFilterData.2
    have hRight : (pair.2.1, pair.2.2) ∈ sourceIncidences I := by
      have hRight' : (pair.1.1, pair.2.2) ∈ sourceIncidences I :=
        sourceIncidence_mem_right_of_consecutive hConsec
      simpa [hFilterData.1] using hRight'
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hRight hInc (by omega) (by omega)
      hSecond).1
    have hSourceRight : pair.2.1 = u := (Prod.ext_iff.mp hPairEq).1
    have hSource : pair.1.1 = u := hFilterData.1.trans hSourceRight
    right
    right
    refine ⟨pair.1.2, ?_, ?_⟩
    · have hLeft : (pair.1.1, pair.1.2) ∈ sourceIncidences I :=
        sourceIncidence_mem_left_of_consecutive hConsec
      simpa [hSource] using hLeft
    · simpa [hSource] using hFirst.symm
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨v, _hvRange, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, hpair, hEq⟩
    have hLeftMem : pair.1 ∈ incidencesOfVertex I v :=
      left_mem_of_mem_consecutivePairs hpair
    have hRightMem : pair.2 ∈ incidencesOfVertex I v :=
      right_mem_of_mem_consecutivePairs hpair
    have hLeft : pair.1 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.1
    have hRight : pair.2 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.1
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hRight hInc (by omega) (by omega)
      hSecond).1
    have hRightSource : pair.2.1 = u := (Prod.ext_iff.mp hPairEq).1
    right
    right
    refine ⟨pair.1.2, ?_, ?_⟩
    · have hLeftSource : pair.1.1 = u := by
        have hL := (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.2
        have hR := (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.2
        exact hL.trans hR.symm |>.trans hRightSource
      have hPair1 : pair.1 = (u, pair.1.2) := Prod.ext hLeftSource rfl
      rw [hPair1] at hLeft
      exact hLeft
    · have hLeftSource : pair.1.1 = u := by
        have hL := (mem_incidencesOfVertex_iff I v pair.1).1 hLeftMem |>.2
        have hR := (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.2
        exact hL.trans hR.symm |>.trans hRightSource
      simpa [hLeftSource] using hFirst.symm
  · rcases List.mem_map.mp heSkip with ⟨slot, hslotMem, hEq⟩
    have hslot : slot < I.k := List.mem_range.mp hslotMem
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex
        (textbookNextSelector_lt hslot) hSecond)
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot, ui⟩
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : slot < I.k := List.mem_range.mp hSlotMem
    have hFirst := congrArg Prod.fst hEq
    left
    exact ⟨slot, hslot, hFirst.symm⟩
  · rcases List.mem_map.mp heExit with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : pair.1 < I.k := List.mem_range.mp hSlotMem
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex
        (textbookNextSelector_lt hslot) hSecond)
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        left
        exact ⟨pair.1, hslot, hFirst⟩
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨_hFirst, hSecond⟩
        exact False.elim
          (textbookSelectorVertex_ne_textbookIncidenceVertex
            (textbookNextSelector_lt hslot) hSecond.symm)

theorem textbookEdgeList_incidence_bit1_in
    {I : VertexCoverInput} {u i x : Nat} (hInc : (u, i) ∈ sourceIncidences I)
    (he : (x, textbookIncidenceVertex I u i 1) ∈ textbookEdgeList I) :
    x = textbookIncidenceVertex I u i 0 ∨
      ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        x = textbookIncidenceVertex I v i 1 := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, hui, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hPairEq := (textbookIncidenceVertex_inj hui hInc (by omega) (by omega)
      hSecond).1
    left
    cases ui with
    | mk v j =>
        have hvu : v = u := (Prod.ext_iff.mp hPairEq).1
        have hji : j = i := (Prod.ext_iff.mp hPairEq).2
        simpa [hvu, hji] using hFirst.symm
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨v, j, w, hData, hEdge⟩
    rcases hData with ⟨⟨hvj, hwj⟩, hvw⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨_hFirst, hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hwj hInc (by omega) (by omega) (by omega)
          hSecond.symm)
    · rcases hEdge with ⟨hFirst, hSecond⟩
      have hPairEq := (textbookIncidenceVertex_inj hwj hInc (by omega) (by omega)
        hSecond.symm).1
      have hwi : w = u := (Prod.ext_iff.mp hPairEq).1
      have hji : j = i := (Prod.ext_iff.mp hPairEq).2
      right
      refine ⟨v, ?_, ?_, ?_⟩
      · simpa [hji] using hvj
      · intro hvu
        exact hvw (hvu.trans hwi.symm)
      · simpa [hji] using hFirst
  · rcases List.mem_map.mp heChain with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hFilterData :
        pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := by
      simpa using of_decide_eq_true hFilter.2
    have hConsec : ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := hFilterData.2
    have hRight : (pair.2.1, pair.2.2) ∈ sourceIncidences I := by
      have hRight' : (pair.1.1, pair.2.2) ∈ sourceIncidences I :=
        sourceIncidence_mem_right_of_consecutive hConsec
      simpa [hFilterData.1] using hRight'
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hRight hInc (by omega) (by omega) (by omega)
        hSecond)
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨v, _hvRange, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, hpair, hEq⟩
    have hRightMem : pair.2 ∈ incidencesOfVertex I v :=
      right_mem_of_mem_consecutivePairs hpair
    have hRight : pair.2 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I v pair.2).1 hRightMem |>.1
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hRight hInc (by omega) (by omega) (by omega)
        hSecond)
  · rcases List.mem_map.mp heSkip with ⟨slot, hslotMem, hEq⟩
    have hslot : slot < I.k := List.mem_range.mp hslotMem
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex
        (textbookNextSelector_lt hslot) hSecond)
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot, ui⟩
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : slot < I.k := List.mem_range.mp hSlotMem
    have hIncEntry : ui ∈ sourceIncidences I := (List.mem_product.mp hFilter.1).2
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hIncEntry hInc (by omega) (by omega) (by omega)
        hSecond)
  · rcases List.mem_map.mp heExit with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hSlotMem := (List.mem_product.mp hFilter.1).1
    have hslot : pair.1 < I.k := List.mem_range.mp hSlotMem
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex
        (textbookNextSelector_lt hslot) hSecond)
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨_hFirst, hSecond⟩
        have hui : ui ∈ incidencesOfVertex I pair.2 := mem_of_head?_eq_some hHead
        have hIncEntry : ui ∈ sourceIncidences I :=
          (mem_incidencesOfVertex_iff I pair.2 ui).1 hui |>.1
        exact False.elim
          (textbookIncidenceVertex_ne_of_bit_ne hIncEntry hInc (by omega) (by omega)
            (by omega) hSecond.symm)
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨_hFirst, hSecond⟩
        exact False.elim
          (textbookSelectorVertex_ne_textbookIncidenceVertex
            (textbookNextSelector_lt hslot) hSecond.symm)

theorem textbookEdgeList_same_source_bit1_to_bit0_index_lt
    {I : VertexCoverInput} {u i j : Nat}
    (hFrom : (u, j) ∈ sourceIncidences I) (hTo : (u, i) ∈ sourceIncidences I)
    (he :
      (textbookIncidenceVertex I u j 1, textbookIncidenceVertex I u i 0) ∈
        textbookEdgeList I) :
    j < i := by
  classical
  simp [textbookEdgeList] at he
  rcases he with heInc | heCross | heChain | heTrackChain | heSkip | heEntry | heExit |
    heTrackEntry | heTrackExit
  · rcases List.mem_map.mp heInc with ⟨ui, hui, hEq⟩
    have hFirst := congrArg Prod.fst hEq
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hui hFrom (by omega) (by omega) (by omega)
        hFirst)
  · simp [textbookCrossArcs] at heCross
    rcases heCross with ⟨v, h, w, hData, hEdge⟩
    rcases hData with ⟨⟨hvh, hwh⟩, _hvw⟩
    rcases hEdge with hEdge | hEdge
    · rcases hEdge with ⟨hFirst, _hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hvh hFrom (by omega) (by omega) (by omega)
          hFirst.symm)
    · rcases hEdge with ⟨_hFirst, hSecond⟩
      exact False.elim
        (textbookIncidenceVertex_ne_of_bit_ne hwh hTo (by omega) (by omega) (by omega)
          hSecond.symm)
  · rcases List.mem_map.mp heChain with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hFilterData :
        pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := by
      simpa using of_decide_eq_true hFilter.2
    have hConsec : ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2 := hFilterData.2
    have hLeft : (pair.1.1, pair.1.2) ∈ sourceIncidences I :=
      sourceIncidence_mem_left_of_consecutive hConsec
    have hRight : (pair.2.1, pair.2.2) ∈ sourceIncidences I := by
      have hRight' : (pair.1.1, pair.2.2) ∈ sourceIncidences I :=
        sourceIncidence_mem_right_of_consecutive hConsec
      simpa [hFilterData.1] using hRight'
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hLeftEq := (textbookIncidenceVertex_inj hLeft hFrom (by omega) (by omega)
      hFirst).1
    have hRightEq := (textbookIncidenceVertex_inj hRight hTo (by omega) (by omega)
      hSecond).1
    have hjEq : pair.1.2 = j := (Prod.ext_iff.mp hLeftEq).2
    have hiEq : pair.2.2 = i := (Prod.ext_iff.mp hRightEq).2
    have hLt : pair.1.2 < pair.2.2 := hConsec.2.2.1
    omega
  · rcases List.mem_flatten.mp heTrackChain with ⟨arcs, harcs, heArc⟩
    rcases List.mem_map.mp harcs with ⟨w, _hwRange, rfl⟩
    rcases List.mem_map.mp heArc with ⟨pair, hpair, hEq⟩
    have hLeftMem : pair.1 ∈ incidencesOfVertex I w :=
      left_mem_of_mem_consecutivePairs hpair
    have hRightMem : pair.2 ∈ incidencesOfVertex I w :=
      right_mem_of_mem_consecutivePairs hpair
    have hLeft : pair.1 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I w pair.1).1 hLeftMem |>.1
    have hRight : pair.2 ∈ sourceIncidences I :=
      (mem_incidencesOfVertex_iff I w pair.2).1 hRightMem |>.1
    have hFirst := congrArg Prod.fst hEq
    have hSecond := congrArg Prod.snd hEq
    have hLeftEq := (textbookIncidenceVertex_inj hLeft hFrom (by omega) (by omega)
      hFirst).1
    have hRightEq := (textbookIncidenceVertex_inj hRight hTo (by omega) (by omega)
      hSecond).1
    have hjEq : pair.1.2 = j := (Prod.ext_iff.mp hLeftEq).2
    have hiEq : pair.2.2 = i := (Prod.ext_iff.mp hRightEq).2
    have hLt := edgeIndex_lt_of_mem_incidencesOfVertex_consecutivePairs hpair
    omega
  · rcases List.mem_map.mp heSkip with ⟨slot, hslotMem, hEq⟩
    have hslot : slot < I.k := List.mem_range.mp hslotMem
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heEntry with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    rcases pair with ⟨slot, ui⟩
    have hslot : slot < I.k := List.mem_range.mp (List.mem_product.mp hFilter.1).1
    have hFirst := congrArg Prod.fst hEq
    exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst)
  · rcases List.mem_map.mp heExit with ⟨pair, hpair, hEq⟩
    have hFilter := List.mem_filter.mp hpair
    have hslot : pair.1 < I.k := List.mem_range.mp (List.mem_product.mp hFilter.1).1
    have hSecond := congrArg Prod.snd hEq
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex
        (textbookNextSelector_lt hslot) hSecond)
  · rw [textbookTrackEntryArcs] at heTrackEntry
    rcases List.mem_flatMap.mp heTrackEntry with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hHead : (incidencesOfVertex I pair.2).head? with
    | none =>
        simp [hHead] at hePair
    | some ui =>
        simp [hHead] at hePair
        rcases hePair with ⟨hFirst, _hSecond⟩
        exact False.elim (textbookSelectorVertex_ne_textbookIncidenceVertex hslot hFirst.symm)
  · rw [textbookTrackExitArcs] at heTrackExit
    rcases List.mem_flatMap.mp heTrackExit with ⟨pair, hpair, hePair⟩
    rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
    have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
    cases hLast : (incidencesOfVertex I pair.2).getLast? with
    | none =>
        simp [hLast] at hePair
    | some ui =>
        simp [hLast] at hePair
        rcases hePair with ⟨_hFirst, hSecond⟩
        exact False.elim
          (textbookSelectorVertex_ne_textbookIncidenceVertex
            (textbookNextSelector_lt hslot) hSecond.symm)

/-- The successor of a vertex in a cyclic ordered witness, using `0` off-witness. -/
noncomputable def cycleSuccessor (cycle : List Nat) (v : Nat) : Nat :=
  if hLen : 0 < cycle.length then
    cycle.get ⟨(cycle.idxOf v + 1) % cycle.length, Nat.mod_lt _ hLen⟩
  else
    0

theorem orderedCycle_edge_to_cycleSuccessor
    {g : GraphInput} {cycle : List Nat} {v : Nat}
    (hSteps : OrderedDirectedCycleSteps g cycle) (hv : v ∈ cycle) :
    HasDirectedEdge g v (cycleSuccessor cycle v) := by
  classical
  have hIdx : cycle.idxOf v < cycle.length := List.idxOf_lt_length_iff.mpr hv
  have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le _) hIdx
  let i : Fin cycle.length := ⟨cycle.idxOf v, hIdx⟩
  have hGet : cycle.get i = v := by
    simp [i, List.getElem_idxOf hIdx]
  have hSucc :
      cyclicSuccIndex (cycle := cycle) i =
        ⟨(cycle.idxOf v + 1) % cycle.length, Nat.mod_lt _ hLen⟩ := by
    rfl
  have hEdge := hSteps i
  rw [hGet, hSucc] at hEdge
  simpa [cycleSuccessor, hLen] using hEdge

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
