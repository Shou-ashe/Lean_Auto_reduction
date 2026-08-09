import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part3

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

noncomputable def decodedCoverRaw
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) : List Nat :=
  (List.range I.k).filterMap (decodedSlotChoice I cycle hCycle)

noncomputable def decodedCover
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) : List Nat :=
  (decodedCoverRaw I cycle hCycle).dedup

theorem decodedCover_length_le
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) :
    (decodedCover I cycle hCycle).length ≤ I.k := by
  have hDedup :
      (decodedCover I cycle hCycle).length ≤ (decodedCoverRaw I cycle hCycle).length := by
    exact List.Sublist.length_le (List.dedup_sublist _)
  have hRaw :
      (decodedCoverRaw I cycle hCycle).length ≤ (List.range I.k).length := by
    exact filterMap_length_le (decodedSlotChoice I cycle hCycle) (List.range I.k)
  simpa [decodedCoverRaw] using le_trans hDedup hRaw

theorem decodedCover_nodup
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) :
    (decodedCover I cycle hCycle).Nodup := by
  classical
  simp [decodedCover, List.nodup_dedup]

theorem decodedCover_withinBounds
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) :
    VerticesWithinBounds I.graph (decodedCover I cycle hCycle) := by
  intro u hu
  have huRaw : u ∈ decodedCoverRaw I cycle hCycle := by
    simpa [decodedCover] using hu
  simp [decodedCoverRaw] at huRaw
  rcases huRaw with ⟨slot, _hslotMem, hChoice⟩
  rcases decodedSlotChoice_eq_some (I := I) (cycle := cycle) (hCycle := hCycle)
      (slot := slot) (u := u) hChoice with
    ⟨_hslot, i, hInc, _hSucc⟩
  exact ((mem_sourceIncidences_iff I (u, i)).1 hInc).2.1

theorem decodedCover_mem_of_slotChoice
    {I : VertexCoverInput} {cycle : List Nat}
    {hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle}
    {slot u : Nat} (hslot : slot < I.k)
    (hChoice : decodedSlotChoice I cycle hCycle slot = some u) :
    u ∈ decodedCover I cycle hCycle := by
  have huRaw : u ∈ decodedCoverRaw I cycle hCycle := by
    simp [decodedCoverRaw]
    exact ⟨slot, hslot, hChoice⟩
  simpa [decodedCover] using huRaw

theorem decodedCover_mem_of_selector_successor_incidence
    {I : VertexCoverInput} {cycle : List Nat}
    {hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle}
    {slot u i : Nat} (hslot : slot < I.k) (hInc : (u, i) ∈ sourceIncidences I)
    (hSucc :
      cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookIncidenceVertex I u i 0) :
    u ∈ decodedCover I cycle hCycle :=
  decodedCover_mem_of_slotChoice hslot
    (decodedSlotChoice_eq_some_of_successor_incidence hslot hInc hSucc)

theorem decodedCover_mem_of_selector_predecessor_incidence
    {I : VertexCoverInput} {cycle : List Nat}
    {hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle}
    {slot u i x : Nat} (hslot : slot < I.k) (hInc : (u, i) ∈ sourceIncidences I)
    (hx : x = textbookSelectorVertex slot)
    (hSucc : cycleSuccessor cycle x = textbookIncidenceVertex I u i 0) :
    u ∈ decodedCover I cycle hCycle := by
  subst x
  exact decodedCover_mem_of_selector_successor_incidence hslot hInc hSucc

theorem cross_bit0_predecessor_of_not_decoded
    {I : VertexCoverInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u i : Nat} (hInc : (u, i) ∈ sourceIncidences I)
    (huNot : u ∉ decodedCover I cycle hCycle) :
    ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
      cycleSuccessor cycle (textbookIncidenceVertex I v i 0) =
        textbookIncidenceVertex I u i 0 := by
  classical
  induction i using Nat.strong_induction_on generalizing u with
  | h i ih =>
      rcases cyclePredecessorSuccessor_incidence_bit0_choice hCycle hInc with
        ⟨x, hx, hSucc, hClass⟩
      rcases hClass with hSelector | hCross | hChain
      · rcases hSelector with ⟨slot, hslot, hxSel⟩
        exact False.elim
          (huNot (decodedCover_mem_of_selector_predecessor_incidence
            (hCycle := hCycle) hslot hInc hxSel hSucc))
      · rcases hCross with ⟨v, hv, hvu, hxCross⟩
        subst x
        exact ⟨v, hv, hvu, hSucc⟩
      · rcases hChain with ⟨j, hj, hxChain⟩
        subst x
        have hEdge :=
          orderedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hx
        have hEdgeList :
            (textbookIncidenceVertex I u j 1,
              textbookIncidenceVertex I u i 0) ∈ textbookEdgeList I := by
          simpa [HasDirectedEdge, textbookMap, hSucc] using hEdge
        have hji : j < i :=
          textbookEdgeList_same_source_bit1_to_bit0_index_lt hj hInc hEdgeList
        rcases ih j hji hj huNot with ⟨v, hv, hvu, hSuccCross⟩
        have hReturn :=
          cross_bit0_successor_forces_bit1_return hCycle hj hv hvu hSuccCross
        have hEq :
            textbookIncidenceVertex I v j 1 =
              textbookIncidenceVertex I u i 0 :=
          hReturn.symm.trans hSucc
        exact False.elim
          (textbookIncidenceVertex_ne_of_bit_ne hv hInc (by omega) (by omega)
            (by omega) hEq)

theorem decodedCover_mem_or_mem_of_source_edge_pair
    {I : VertexCoverInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u v i : Nat} (hu : (u, i) ∈ sourceIncidences I)
    (hv : (v, i) ∈ sourceIncidences I) (huv : u ≠ v) :
    u ∈ decodedCover I cycle hCycle ∨ v ∈ decodedCover I cycle hCycle := by
  classical
  by_cases huDec : u ∈ decodedCover I cycle hCycle
  · exact Or.inl huDec
  by_cases hvDec : v ∈ decodedCover I cycle hCycle
  · exact Or.inr hvDec
  rcases cross_bit0_predecessor_of_not_decoded hCycle hu huDec with
    ⟨w, hw, hwu, hSuccWU⟩
  have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hu
  have hSourceV : SourceIncidentAt I v i := (mem_sourceIncidences_iff I (v, i)).1 hv
  have hSourceW : SourceIncidentAt I w i := (mem_sourceIncidences_iff I (w, i)).1 hw
  have hwv : w = v :=
    sourceIncidentAt_other_endpoint_unique hSourceV hSourceU hSourceW
      (fun hvu => huv hvu.symm) hwu
  rcases cross_bit0_predecessor_of_not_decoded hCycle hv hvDec with
    ⟨z, hz, hzv, hSuccZV⟩
  have hSourceZ : SourceIncidentAt I z i := (mem_sourceIncidences_iff I (z, i)).1 hz
  have hzu : z = u :=
    sourceIncidentAt_other_endpoint_unique hSourceU hSourceV hSourceZ huv hzv
  have hSuccVU :
      cycleSuccessor cycle (textbookIncidenceVertex I v i 0) =
        textbookIncidenceVertex I u i 0 := by
    simpa [hwv] using hSuccWU
  have hSuccUV :
      cycleSuccessor cycle (textbookIncidenceVertex I u i 0) =
        textbookIncidenceVertex I v i 0 := by
    simpa [hzu] using hSuccZV
  have hxMem :
      textbookIncidenceVertex I v i 0 ∈ cycle := by
    exact OrderedDirectedHamiltonianCycle.mem_of_lt hCycle
      (by simpa [textbookMap] using textbookIncidenceVertex_lt hv (by omega))
  have hyMem :
      textbookIncidenceVertex I u i 0 ∈ cycle := by
    exact OrderedDirectedHamiltonianCycle.mem_of_lt hCycle
      (by simpa [textbookMap] using textbookIncidenceVertex_lt hu (by omega))
  have hzMem :
      textbookIncidenceVertex I u i 1 ∈ cycle := by
    exact OrderedDirectedHamiltonianCycle.mem_of_lt hCycle
      (by simpa [textbookMap] using textbookIncidenceVertex_lt hu (by omega))
  have hxy :
      textbookIncidenceVertex I v i 0 ≠ textbookIncidenceVertex I u i 0 := by
    exact textbookIncidenceVertex_ne_of_incidence_ne hv hu (by omega) (by omega)
      (by
        intro hPair
        exact huv (Prod.ext_iff.mp hPair).1.symm)
  have hzx :
      textbookIncidenceVertex I u i 1 ≠ textbookIncidenceVertex I v i 0 := by
    exact textbookIncidenceVertex_ne_of_bit_ne hu hv (by omega) (by omega) (by omega)
  have hzy :
      textbookIncidenceVertex I u i 1 ≠ textbookIncidenceVertex I u i 0 := by
    exact textbookIncidenceVertex_ne_of_bit_ne hu hu (by omega) (by omega) (by omega)
  exact False.elim
    (cycleSuccessor_two_cycle_no_extra hCycle.2.1 hxMem hyMem hzMem hxy hzx hzy
      hSuccVU hSuccUV)

theorem decodedCover_coversEdges_of_orderedCycle
    {I : VertexCoverInput} {cycle : List Nat}
    (hNoBad : ¬ FeedbackNodeSet.HasUncoverableEdge I.graph)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle) :
    CoversEdges I.graph (decodedCover I cycle hCycle) := by
  classical
  intro e he
  rcases List.mem_iff_get.mp he with ⟨idx, rfl⟩
  let i := idx.val
  have hi : i < I.graph.edges.length := idx.isLt
  by_cases hLeftBound : I.graph.edges[i].1 < I.graph.vertices
  · have hLeftInc : (I.graph.edges[i].1, i) ∈ sourceIncidences I :=
      sourceIncidence_left_of_edge_index hi hLeftBound
    by_cases hLeftDec : I.graph.edges[i].1 ∈ decodedCover I cycle hCycle
    · exact Or.inl hLeftDec
    · rcases cross_bit0_predecessor_of_not_decoded hCycle hLeftInc hLeftDec with
        ⟨v, hv, hvNeLeft, _hSucc⟩
      have hvDec : v ∈ decodedCover I cycle hCycle := by
        rcases decodedCover_mem_or_mem_of_source_edge_pair hCycle hLeftInc hv
            (fun h => hvNeLeft h.symm) with
          hLeft | hV
        · exact False.elim (hLeftDec hLeft)
        · exact hV
      have hvRight : v = I.graph.edges[i].2 := by
        rcases sourceIncidence_endpoint_eq_left_or_right hi hv with hvLeft | hvRight
        · exact False.elim (hvNeLeft hvLeft)
        · exact hvRight
      right
      simpa [hvRight] using hvDec
  · have hRightBound : I.graph.edges[i].2 < I.graph.vertices := by
      by_contra hRightBad
      exact hNoBad ⟨I.graph.edges[i], List.get_mem I.graph.edges idx, hLeftBound, hRightBad⟩
    have hRightInc : (I.graph.edges[i].2, i) ∈ sourceIncidences I :=
      sourceIncidence_right_of_edge_index hi hRightBound
    by_cases hRightDec : I.graph.edges[i].2 ∈ decodedCover I cycle hCycle
    · exact Or.inr hRightDec
    · rcases cross_bit0_predecessor_of_not_decoded hCycle hRightInc hRightDec with
        ⟨v, hv, hvNeRight, _hSucc⟩
      have hSourceV : SourceIncidentAt I v i := (mem_sourceIncidences_iff I (v, i)).1 hv
      rcases sourceIncidence_endpoint_eq_left_or_right hi hv with hvLeft | hvRight
      · exact False.elim (hLeftBound (by simpa [hvLeft] using hSourceV.2.1))
      · exact False.elim (hvNeRight hvRight)

/--
Unselected bounded endpoint-incidences for source edge `i`, excluding the current
owner endpoint `u`.
-/
noncomputable def detourOtherCandidates
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) : List Nat := by
  classical
  exact ((sourceIncidences I).filter fun vi =>
    decide (vi.2 = i ∧ vi.1 ≠ u ∧ vi.1 ∉ cover)).map Prod.fst

theorem mem_detourOtherCandidates_iff
    (I : VertexCoverInput) (cover : List Nat) (u i v : Nat) :
    v ∈ detourOtherCandidates I cover u i ↔
      (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧ v ∉ cover := by
  classical
  simp [detourOtherCandidates, and_assoc, and_comm]

/-- The optional unselected other endpoint to visit from an owner incidence. -/
noncomputable def detourOther? (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    Option Nat :=
  (detourOtherCandidates I cover u i).head?

theorem detourOther?_eq_some
    {I : VertexCoverInput} {cover : List Nat} {u i v : Nat}
    (h : detourOther? I cover u i = some v) :
    (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧ v ∉ cover := by
  classical
  unfold detourOther? at h
  cases hList : detourOtherCandidates I cover u i with
  | nil =>
      simp [hList] at h
  | cons w rest =>
      simp [hList] at h
      subst v
      have hw : w ∈ detourOtherCandidates I cover u i := by
        simp [hList]
      exact (mem_detourOtherCandidates_iff I cover u i w).1 hw

theorem detourOther?_isSome_of_candidate
    {I : VertexCoverInput} {cover : List Nat} {u i v : Nat}
    (hv : (v, i) ∈ sourceIncidences I) (hvu : v ≠ u) (hvCover : v ∉ cover) :
    (detourOther? I cover u i).isSome := by
  classical
  have hvMem : v ∈ detourOtherCandidates I cover u i :=
    (mem_detourOtherCandidates_iff I cover u i v).2 ⟨hv, hvu, hvCover⟩
  unfold detourOther?
  cases hList : detourOtherCandidates I cover u i with
  | nil =>
      simp [hList] at hvMem
  | cons w rest =>
      simp

theorem detourOther?_eq_some_of_unselected_other
    {I : VertexCoverInput} {cover : List Nat} {owner u i : Nat}
    (hOwner : (owner, i) ∈ sourceIncidences I) (hu : (u, i) ∈ sourceIncidences I)
    (huOwner : u ≠ owner) (huCover : u ∉ cover) :
    detourOther? I cover owner i = some u := by
  classical
  unfold detourOther?
  refine List.head?_eq_some_of_mem_forall_eq ?_ ?_
  · exact (mem_detourOtherCandidates_iff I cover owner i u).2
      ⟨hu, huOwner, huCover⟩
  · intro w hw
    have hwData := (mem_detourOtherCandidates_iff I cover owner i w).1 hw
    have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hu
    have hSourceOwner : SourceIncidentAt I owner i :=
      (mem_sourceIncidences_iff I (owner, i)).1 hOwner
    have hSourceW : SourceIncidentAt I w i :=
      (mem_sourceIncidences_iff I (w, i)).1 hwData.1
    exact sourceIncidentAt_other_endpoint_unique hSourceU hSourceOwner hSourceW
      huOwner hwData.2.1

/--
The local owner-incidence segment.  With no unselected other endpoint it is the
forced incidence arc; otherwise it crosses to the other endpoint, traverses its
forced incidence arc, and crosses back.
-/
noncomputable def ownerIncidenceSegment
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) : List Nat :=
  match detourOther? I cover u i with
  | none =>
      [textbookIncidenceVertex I u i 0,
        textbookIncidenceVertex I u i 1]
  | some v =>
      [textbookIncidenceVertex I u i 0,
        textbookIncidenceVertex I v i 0,
        textbookIncidenceVertex I v i 1,
        textbookIncidenceVertex I u i 1]

theorem ownerIncidenceSegment_withinBounds
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) :
    VerticesWithinBounds (textbookMap I).graph (ownerIncidenceSegment I cover u i) := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i with
  | none =>
      have hu0 : textbookIncidenceVertex I u i 0 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hu (by omega)
      have hu1 : textbookIncidenceVertex I u i 1 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hu (by omega)
      simp [VerticesWithinBounds, textbookMap, hu0, hu1]
  | some v =>
      have hv : (v, i) ∈ sourceIncidences I := (detourOther?_eq_some hOther).1
      have hu0 : textbookIncidenceVertex I u i 0 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hu (by omega)
      have hu1 : textbookIncidenceVertex I u i 1 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hu (by omega)
      have hv0 : textbookIncidenceVertex I v i 0 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hv (by omega)
      have hv1 : textbookIncidenceVertex I v i 1 < textbookVertexCount I :=
        textbookIncidenceVertex_lt hv (by omega)
      simp [VerticesWithinBounds, textbookMap, hu0, hu1, hv0, hv1]

theorem ownerIncidenceSegment_edgeChain
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) :
    (ownerIncidenceSegment I cover u i).IsChain fun a b => (a, b) ∈ textbookEdgeList I := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i with
  | none =>
      simp [mem_textbookEdgeList_incidence hu]
  | some v =>
      have hvData := detourOther?_eq_some hOther
      have hv : (v, i) ∈ sourceIncidences I := hvData.1
      have hvu : v ≠ u := hvData.2.1
      have huv : u ≠ v := fun h => hvu h.symm
      simp [mem_textbookEdgeList_cross_bit0 hu hv huv,
        mem_textbookEdgeList_incidence hv,
        mem_textbookEdgeList_cross_bit1 hv hu hvu]

theorem ownerIncidenceSegment_head?
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    (ownerIncidenceSegment I cover u i).head? =
      some (textbookIncidenceVertex I u i 0) := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i <;> simp

theorem ownerIncidenceSegment_getLast?
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    (ownerIncidenceSegment I cover u i).getLast? =
      some (textbookIncidenceVertex I u i 1) := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i <;> simp

theorem ownerIncidenceSegment_ne_nil
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    ownerIncidenceSegment I cover u i ≠ [] := by
  intro h
  have hHead := congr_arg List.head? h
  simp [ownerIncidenceSegment_head?] at hHead

theorem ownerIncidenceSegment_mem_owner_bit0
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    textbookIncidenceVertex I u i 0 ∈ ownerIncidenceSegment I cover u i := by
  classical
  unfold ownerIncidenceSegment
  cases detourOther? I cover u i <;> simp

theorem ownerIncidenceSegment_mem_owner_bit1
    (I : VertexCoverInput) (cover : List Nat) (u i : Nat) :
    textbookIncidenceVertex I u i 1 ∈ ownerIncidenceSegment I cover u i := by
  classical
  unfold ownerIncidenceSegment
  cases detourOther? I cover u i <;> simp

theorem ownerIncidenceSegment_mem_other_bit0
    {I : VertexCoverInput} {cover : List Nat} {owner other i : Nat}
    (hOther : detourOther? I cover owner i = some other) :
    textbookIncidenceVertex I other i 0 ∈ ownerIncidenceSegment I cover owner i := by
  unfold ownerIncidenceSegment
  rw [hOther]
  simp

theorem ownerIncidenceSegment_mem_other_bit1
    {I : VertexCoverInput} {cover : List Nat} {owner other i : Nat}
    (hOther : detourOther? I cover owner i = some other) :
    textbookIncidenceVertex I other i 1 ∈ ownerIncidenceSegment I cover owner i := by
  unfold ownerIncidenceSegment
  rw [hOther]
  simp

theorem mem_ownerIncidenceSegment_iff
    (I : VertexCoverInput) (cover : List Nat) (u i x : Nat) :
    x ∈ ownerIncidenceSegment I cover u i ↔
      x = textbookIncidenceVertex I u i 0 ∨
        x = textbookIncidenceVertex I u i 1 ∨
        ∃ v, detourOther? I cover u i = some v ∧
          (x = textbookIncidenceVertex I v i 0 ∨
            x = textbookIncidenceVertex I v i 1) := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i with
  | none =>
      simp
  | some v =>
      simp [or_left_comm, or_comm]

theorem exists_sourceIncidence_of_mem_ownerIncidenceSegment
    {I : VertexCoverInput} {cover : List Nat} {u i x : Nat}
    (hu : (u, i) ∈ sourceIncidences I)
    (hx : x ∈ ownerIncidenceSegment I cover u i) :
    ∃ w bit, (w, i) ∈ sourceIncidences I ∧ bit < 2 ∧
      x = textbookIncidenceVertex I w i bit := by
  classical
  rcases (mem_ownerIncidenceSegment_iff I cover u i x).1 hx with hOwner0 | hOwner1 | hOther
  · exact ⟨u, 0, hu, by omega, hOwner0⟩
  · exact ⟨u, 1, hu, by omega, hOwner1⟩
  · rcases hOther with ⟨v, hOther, hv0 | hv1⟩
    · exact ⟨v, 0, (detourOther?_eq_some hOther).1, by omega, hv0⟩
    · exact ⟨v, 1, (detourOther?_eq_some hOther).1, by omega, hv1⟩

theorem exists_sourceIncidence_owner_or_uncovered_of_mem_ownerIncidenceSegment
    {I : VertexCoverInput} {cover : List Nat} {u i x : Nat}
    (hu : (u, i) ∈ sourceIncidences I)
    (hx : x ∈ ownerIncidenceSegment I cover u i) :
    ∃ w bit, (w, i) ∈ sourceIncidences I ∧ bit < 2 ∧
      x = textbookIncidenceVertex I w i bit ∧ (w = u ∨ w ∉ cover) := by
  classical
  rcases (mem_ownerIncidenceSegment_iff I cover u i x).1 hx with hOwner0 | hOwner1 | hOther
  · exact ⟨u, 0, hu, by omega, hOwner0, Or.inl rfl⟩
  · exact ⟨u, 1, hu, by omega, hOwner1, Or.inl rfl⟩
  · rcases hOther with ⟨v, hOther, hv0 | hv1⟩
    · exact ⟨v, 0, (detourOther?_eq_some hOther).1, by omega, hv0,
        Or.inr (detourOther?_eq_some hOther).2.2⟩
    · exact ⟨v, 1, (detourOther?_eq_some hOther).1, by omega, hv1,
        Or.inr (detourOther?_eq_some hOther).2.2⟩

theorem ownerIncidenceSegment_nodup
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hu : (u, i) ∈ sourceIncidences I) :
    (ownerIncidenceSegment I cover u i).Nodup := by
  classical
  unfold ownerIncidenceSegment
  cases hOther : detourOther? I cover u i with
  | none =>
      have h01 :
          textbookIncidenceVertex I u i 0 ≠ textbookIncidenceVertex I u i 1 :=
        textbookIncidenceVertex_ne_of_bit_ne hu hu (by omega) (by omega) (by omega)
      simp [h01]
  | some v =>
      have hvData := detourOther?_eq_some hOther
      have hv : (v, i) ∈ sourceIncidences I := hvData.1
      have hvu : v ≠ u := hvData.2.1
      have huv : u ≠ v := fun h => hvu h.symm
      have hu_ne_v0 :
          textbookIncidenceVertex I u i 0 ≠ textbookIncidenceVertex I v i 0 :=
        textbookIncidenceVertex_ne_of_incidence_ne hu hv (by omega) (by omega)
          (by intro h; exact huv (Prod.ext_iff.mp h).1)
      have hu0_ne_v1 :
          textbookIncidenceVertex I u i 0 ≠ textbookIncidenceVertex I v i 1 :=
        textbookIncidenceVertex_ne_of_bit_ne hu hv (by omega) (by omega) (by omega)
      have hu0_ne_u1 :
          textbookIncidenceVertex I u i 0 ≠ textbookIncidenceVertex I u i 1 :=
        textbookIncidenceVertex_ne_of_bit_ne hu hu (by omega) (by omega) (by omega)
      have hv0_ne_v1 :
          textbookIncidenceVertex I v i 0 ≠ textbookIncidenceVertex I v i 1 :=
        textbookIncidenceVertex_ne_of_bit_ne hv hv (by omega) (by omega) (by omega)
      have hv0_ne_u1 :
          textbookIncidenceVertex I v i 0 ≠ textbookIncidenceVertex I u i 1 :=
        textbookIncidenceVertex_ne_of_bit_ne hv hu (by omega) (by omega) (by omega)
      have hv1_ne_u1 :
          textbookIncidenceVertex I v i 1 ≠ textbookIncidenceVertex I u i 1 :=
        textbookIncidenceVertex_ne_of_incidence_ne hv hu (by omega) (by omega)
          (by intro h; exact hvu (Prod.ext_iff.mp h).1)
      simp [hu_ne_v0, hu0_ne_v1, hu0_ne_u1, hv0_ne_v1, hv0_ne_u1, hv1_ne_u1]

theorem ownerIncidenceSegment_disjoint_of_edge_ne
    {I : VertexCoverInput} {cover : List Nat} {u i j x : Nat}
    (hui : (u, i) ∈ sourceIncidences I) (huj : (u, j) ∈ sourceIncidences I)
    (hij : i ≠ j)
    (hxI : x ∈ ownerIncidenceSegment I cover u i)
    (hxJ : x ∈ ownerIncidenceSegment I cover u j) :
    False := by
  rcases exists_sourceIncidence_of_mem_ownerIncidenceSegment hui hxI with
    ⟨wi, biti, hwi, hbiti, hxEqI⟩
  rcases exists_sourceIncidence_of_mem_ownerIncidenceSegment huj hxJ with
    ⟨wj, bitj, hwj, hbitj, hxEqJ⟩
  have hEq :
      textbookIncidenceVertex I wi i biti = textbookIncidenceVertex I wj j bitj := by
    exact hxEqI.symm.trans hxEqJ
  have hIncEq := (textbookIncidenceVertex_inj hwi hwj hbiti hbitj hEq).1
  exact hij (Prod.ext_iff.mp hIncEq).2

theorem ownerIncidenceSegment_chain_splice
    {I : VertexCoverInput} {cover : List Nat} {u i j : Nat}
    (hConsec : ConsecutiveIncident I u i j) :
    ∀ x ∈ (ownerIncidenceSegment I cover u i).getLast?,
      ∀ y ∈ (ownerIncidenceSegment I cover u j).head?,
        (x, y) ∈ textbookEdgeList I := by
  intro x hx y hy
  simp [ownerIncidenceSegment_getLast?, ownerIncidenceSegment_head?] at hx hy
  subst x
  subst y
  exact mem_textbookEdgeList_chain hConsec

theorem selector_entry_splice_ownerIncidenceSegment
    {I : VertexCoverInput} {cover : List Nat} {slot u i : Nat}
    (hslot : slot < I.k) (hFirst : FirstIncident I u i) :
    ∀ y ∈ (ownerIncidenceSegment I cover u i).head?,
      (textbookSelectorVertex slot, y) ∈ textbookEdgeList I := by
  intro y hy
  simp [ownerIncidenceSegment_head?] at hy
  subst y
  exact mem_textbookEdgeList_entry hslot hFirst

theorem ownerIncidenceSegment_exit_splice
    {I : VertexCoverInput} {cover : List Nat} {slot u i : Nat}
    (hslot : slot < I.k) (hLast : LastIncident I u i) :
    ∀ x ∈ (ownerIncidenceSegment I cover u i).getLast?,
      (x, textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookEdgeList I := by
  intro x hx
  simp [ownerIncidenceSegment_getLast?] at hx
  subst x
  exact mem_textbookEdgeList_exit hslot hLast

/-- The selected source-vertex incidence track after owner detours are inserted. -/
noncomputable def detouredVertexTrack
    (I : VertexCoverInput) (cover : List Nat) (u : Nat) : List Nat :=
  ((incidencesOfVertex I u).map fun ui =>
    ownerIncidenceSegment I cover u ui.2).flatten

theorem mem_detouredVertexTrack_of_mem_segment
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} {ui : Nat × Nat} {x : Nat}
    (hui : ui ∈ incidencesOfVertex I u)
    (hx : x ∈ ownerIncidenceSegment I cover u ui.2) :
    x ∈ detouredVertexTrack I cover u := by
  exact List.mem_flatten.mpr
    ⟨ownerIncidenceSegment I cover u ui.2,
      List.mem_map.mpr ⟨ui, hui, rfl⟩, hx⟩

theorem exists_sourceIncidence_of_mem_detouredVertexTrack
    {I : VertexCoverInput} {cover : List Nat} {u x : Nat}
    (hx : x ∈ detouredVertexTrack I cover u) :
    ∃ w i bit, (w, i) ∈ sourceIncidences I ∧ bit < 2 ∧
      x = textbookIncidenceVertex I w i bit := by
  rcases List.mem_flatten.mp hx with ⟨segment, hSegment, hxSegment⟩
  rcases List.mem_map.mp hSegment with ⟨ui, hui, rfl⟩
  have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
  have hInc : (u, ui.2) ∈ sourceIncidences I := by
    cases ui with
    | mk v i =>
        rcases hData with ⟨hSource, hvu⟩
        have hvu' : v = u := by simpa using hvu
        rw [hvu'] at hSource
        exact hSource
  rcases exists_sourceIncidence_of_mem_ownerIncidenceSegment hInc hxSegment with
    ⟨w, bit, hwi, hbit, hxEq⟩
  exact ⟨w, ui.2, bit, hwi, hbit, hxEq⟩

theorem exists_sourceIncidence_owner_or_uncovered_of_mem_detouredVertexTrack
    {I : VertexCoverInput} {cover : List Nat} {u x : Nat}
    (hx : x ∈ detouredVertexTrack I cover u) :
    ∃ w i bit, (u, i) ∈ sourceIncidences I ∧ (w, i) ∈ sourceIncidences I ∧
      bit < 2 ∧ x = textbookIncidenceVertex I w i bit ∧ (w = u ∨ w ∉ cover) := by
  rcases List.mem_flatten.mp hx with ⟨segment, hSegment, hxSegment⟩
  rcases List.mem_map.mp hSegment with ⟨ui, hui, rfl⟩
  have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
  have hOwner : (u, ui.2) ∈ sourceIncidences I := by
    cases ui with
    | mk v i =>
        rcases hData with ⟨hSource, hvu⟩
        have hvu' : v = u := by simpa using hvu
        rw [hvu'] at hSource
        exact hSource
  rcases exists_sourceIncidence_owner_or_uncovered_of_mem_ownerIncidenceSegment hOwner
      hxSegment with
    ⟨w, bit, hwi, hbit, hxEq, hOwnerOrUncovered⟩
  exact ⟨w, ui.2, bit, hOwner, hwi, hbit, hxEq, hOwnerOrUncovered⟩

theorem detouredVertexTrack_disjoint_of_cover_ne
    {I : VertexCoverInput} {cover : List Nat} {u v : Nat}
    (huCover : u ∈ cover) (hvCover : v ∈ cover) (huv : u ≠ v) :
    List.Disjoint (detouredVertexTrack I cover u) (detouredVertexTrack I cover v) := by
  intro x hxU hxV
  rcases exists_sourceIncidence_owner_or_uncovered_of_mem_detouredVertexTrack hxU with
    ⟨w, i, bit, hui, hwi, hbit, hxEqU, hOwnerU⟩
  rcases exists_sourceIncidence_owner_or_uncovered_of_mem_detouredVertexTrack hxV with
    ⟨w', j, bit', hvj, hwj, hbit', hxEqV, hOwnerV⟩
  have hVertexEq :
      textbookIncidenceVertex I w i bit = textbookIncidenceVertex I w' j bit' :=
    hxEqU.symm.trans hxEqV
  have hIncEq := (textbookIncidenceVertex_inj hwi hwj hbit hbit' hVertexEq).1
  have hW : w = w' := (Prod.ext_iff.mp hIncEq).1
  have hI : i = j := (Prod.ext_iff.mp hIncEq).2
  have hOwnerVw : w = v ∨ w ∉ cover := by
    simpa [hW] using hOwnerV
  have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hui
  have hSourceV : SourceIncidentAt I v i := by
    simpa [hI] using (mem_sourceIncidences_iff I (v, j)).1 hvj
  have hSourceW : SourceIncidentAt I w i := (mem_sourceIncidences_iff I (w, i)).1 hwi
  rcases hOwnerU with hwu | hwNotCover
  · rcases hOwnerVw with hwv | hwNotCover'
    · exact huv (hwu.symm.trans hwv)
    · exact hwNotCover' (hwu ▸ huCover)
  · rcases hOwnerVw with hwv | hwNotCover'
    · exact hwNotCover (hwv ▸ hvCover)
    · have hwvNe : w ≠ v := by
        intro hwv
        exact hwNotCover' (hwv ▸ hvCover)
      have hwu : w = u :=
        sourceIncidentAt_other_endpoint_unique hSourceU hSourceV hSourceW huv hwvNe
      exact hwNotCover (hwu ▸ huCover)

theorem detouredVertexTrack_withinBounds
    (I : VertexCoverInput) (cover : List Nat) (u : Nat) :
    VerticesWithinBounds (textbookMap I).graph (detouredVertexTrack I cover u) := by
  intro x hx
  rcases List.mem_flatten.mp hx with ⟨segment, hSegment, hxSegment⟩
  rcases List.mem_map.mp hSegment with ⟨ui, hui, rfl⟩
  have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
  have hInc : (u, ui.2) ∈ sourceIncidences I := by
    cases ui with
    | mk v i =>
        rcases hData with ⟨hSource, hvu⟩
        have hvu' : v = u := by simpa using hvu
        rw [hvu'] at hSource
        exact hSource
  exact ownerIncidenceSegment_withinBounds hInc x hxSegment

theorem detouredVertexTrack_nodup
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} :
    (detouredVertexTrack I cover u).Nodup := by
  classical
  unfold detouredVertexTrack
  let segmentOf : Nat × Nat → List Nat := fun ui => ownerIncidenceSegment I cover u ui.2
  have hLocal :
      ∀ ui ∈ incidencesOfVertex I u, (segmentOf ui).Nodup := by
    intro ui hui
    have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
    have hInc : (u, ui.2) ∈ sourceIncidences I := by
      cases ui with
      | mk v i =>
          rcases hData with ⟨hSource, hvu⟩
          have hvu' : v = u := by simpa using hvu
          rw [hvu'] at hSource
          exact hSource
    exact ownerIncidenceSegment_nodup hInc
  have hPair :
      (incidencesOfVertex I u).Pairwise
        (fun ui uj => List.Disjoint (segmentOf ui) (segmentOf uj)) := by
    refine (incidencesOfVertex_nodup I u).pairwise_of_forall_ne ?_
    intro ui hui uj huj huiNe
    have huiData := (mem_incidencesOfVertex_iff I u ui).1 hui
    have hujData := (mem_incidencesOfVertex_iff I u uj).1 huj
    have hUiFirst : ui.1 = u := huiData.2
    have hUjFirst : uj.1 = u := hujData.2
    have huiInc : (u, ui.2) ∈ sourceIncidences I := by
      cases ui with
      | mk v i =>
          have hvu : v = u := by simpa using hUiFirst
          simpa [hvu] using huiData.1
    have hujInc : (u, uj.2) ∈ sourceIncidences I := by
      cases uj with
      | mk v j =>
          have hvu : v = u := by simpa using hUjFirst
          simpa [hvu] using hujData.1
    have hij : ui.2 ≠ uj.2 := by
      intro hEq
      apply huiNe
      cases ui with
      | mk ui1 ui2 =>
          cases uj with
          | mk uj1 uj2 =>
              simp at hUiFirst hUjFirst hEq ⊢
              omega
    intro x hxI hxJ
    exact ownerIncidenceSegment_disjoint_of_edge_ne huiInc hujInc hij hxI hxJ
  have hFlat :=
    (List.nodup_flatMap (l₁ := incidencesOfVertex I u) (f := segmentOf)).2
      ⟨hLocal, hPair⟩
  simpa [List.flatMap, segmentOf] using hFlat

theorem textbookSelectorVertex_not_mem_detouredVertexTrack
    {I : VertexCoverInput} {cover : List Nat} {slot u : Nat} (hslot : slot < I.k) :
    textbookSelectorVertex slot ∉ detouredVertexTrack I cover u := by
  intro hx
  rcases exists_sourceIncidence_of_mem_detouredVertexTrack hx with
    ⟨w, i, bit, _hwi, _hbit, hEq⟩
  exact textbookSelectorVertex_ne_textbookIncidenceVertex hslot hEq

theorem detouredVertexTrack_edgeChain
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} (hu : u < I.graph.vertices) :
    (detouredVertexTrack I cover u).IsChain fun a b => (a, b) ∈ textbookEdgeList I := by
  classical
  unfold detouredVertexTrack
  let segmentOf : Nat × Nat → List Nat := fun ui => ownerIncidenceSegment I cover u ui.2
  let segments : List (List Nat) := (incidencesOfVertex I u).map segmentOf
  have hNoNil : [] ∉ segments := by
    intro hNil
    rcases List.mem_map.mp hNil with ⟨ui, _hui, hEq⟩
    exact ownerIncidenceSegment_ne_nil I cover u ui.2 hEq
  have hFlatten :
      segments.flatten.IsChain fun a b => (a, b) ∈ textbookEdgeList I := by
    rw [List.isChain_flatten hNoNil]
    constructor
    · intro segment hSegment
      rcases List.mem_map.mp hSegment with ⟨ui, hui, rfl⟩
      have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
      have hInc : (u, ui.2) ∈ sourceIncidences I := by
        cases ui with
        | mk v i =>
            rcases hData with ⟨hSource, hvu⟩
            have hvu' : v = u := by simpa using hvu
            rw [hvu'] at hSource
            exact hSource
      exact ownerIncidenceSegment_edgeChain hInc
    · rw [List.isChain_map]
      exact (isChain_mem_consecutivePairs (incidencesOfVertex I u)).imp fun ui uj hpair => by
        intro x hx y hy
        have huiMem : ui ∈ incidencesOfVertex I u :=
          left_mem_of_mem_consecutivePairs hpair
        have hujMem : uj ∈ incidencesOfVertex I u :=
          right_mem_of_mem_consecutivePairs hpair
        have huiEq : ui.1 = u := ((mem_incidencesOfVertex_iff I u ui).1 huiMem).2
        have hujEq : uj.1 = u := ((mem_incidencesOfVertex_iff I u uj).1 hujMem).2
        simp [segmentOf, ownerIncidenceSegment_getLast?,
          ownerIncidenceSegment_head?] at hx hy
        subst x
        subst y
        simpa [huiEq, hujEq] using
          mem_textbookEdgeList_track_chain (I := I) (u := u) hu hpair
  simpa [segments, segmentOf]
    using hFlatten

theorem detouredVertexTrack_head?_of_head?
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} {ui : Nat × Nat}
    (hHead : (incidencesOfVertex I u).head? = some ui) :
    (detouredVertexTrack I cover u).head? =
      some (textbookIncidenceVertex I u ui.2 0) := by
  classical
  cases hList : incidencesOfVertex I u with
  | nil =>
      simp [hList] at hHead
  | cons first rest =>
      simp [hList] at hHead
      subst ui
      simp [detouredVertexTrack, hList, ownerIncidenceSegment_head?]

theorem detouredSegments_getLast?_of_getLast?
    (I : VertexCoverInput) (cover : List Nat) (u : Nat) :
    ∀ {l : List (Nat × Nat)} {ui : Nat × Nat}, l.getLast? = some ui →
      ((l.map fun vi => ownerIncidenceSegment I cover u vi.2).flatten).getLast? =
        some (textbookIncidenceVertex I u ui.2 1)
  | [], ui, hLast => by
      simp at hLast
  | [first], ui, hLast => by
      simp at hLast
      subst ui
      simp [ownerIncidenceSegment_getLast?]
  | first :: second :: rest, ui, hLast => by
      have hTailLast : (second :: rest).getLast? = some ui := by
        simpa using hLast
      have hTailNonempty :
          (((second :: rest).map fun vi =>
            ownerIncidenceSegment I cover u vi.2).flatten) ≠ [] := by
        simp [ownerIncidenceSegment_ne_nil]
      rw [List.map_cons, List.flatten_cons,
        List.getLast?_append_of_ne_nil _ hTailNonempty]
      exact detouredSegments_getLast?_of_getLast? I cover u hTailLast

theorem detouredVertexTrack_getLast?_of_getLast?
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} {ui : Nat × Nat}
    (hLast : (incidencesOfVertex I u).getLast? = some ui) :
    (detouredVertexTrack I cover u).getLast? =
      some (textbookIncidenceVertex I u ui.2 1) := by
  simpa [detouredVertexTrack] using
    detouredSegments_getLast?_of_getLast? I cover u hLast

theorem detouredVertexTrack_entry_splice
    {I : VertexCoverInput} {cover : List Nat} {slot u : Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices) :
    ∀ y ∈ (detouredVertexTrack I cover u).head?,
      (textbookSelectorVertex slot, y) ∈ textbookEdgeList I := by
  classical
  cases hList : incidencesOfVertex I u with
  | nil =>
      simp [detouredVertexTrack, hList]
  | cons ui rest =>
      have hHead : (incidencesOfVertex I u).head? = some ui := by
        simp [hList]
      have huiMem : ui ∈ incidencesOfVertex I u := by
        simp [hList]
      have huiEq : ui.1 = u := ((mem_incidencesOfVertex_iff I u ui).1 huiMem).2
      intro y hy
      have hyEq := detouredVertexTrack_head?_of_head? (I := I) (cover := cover) hHead
      simp [hyEq] at hy
      subst y
      simpa [huiEq] using mem_textbookEdgeList_track_entry hslot hu hHead

theorem detouredVertexTrack_exit_splice
    {I : VertexCoverInput} {cover : List Nat} {slot u : Nat}
    (hslot : slot < I.k) (hu : u < I.graph.vertices) :
    ∀ x ∈ (detouredVertexTrack I cover u).getLast?,
      (x, textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookEdgeList I := by
  classical
  cases hList : incidencesOfVertex I u with
  | nil =>
      simp [detouredVertexTrack, hList]
  | cons ui rest =>
      cases hLast : (incidencesOfVertex I u).getLast? with
      | none =>
          simp [hList] at hLast
      | some lastUi =>
          have hLastMem : lastUi ∈ incidencesOfVertex I u :=
            mem_of_getLast?_eq_some hLast
          have hlastEq : lastUi.1 = u :=
            ((mem_incidencesOfVertex_iff I u lastUi).1 hLastMem).2
          intro x hx
          have hxEq :=
            detouredVertexTrack_getLast?_of_getLast? (I := I) (cover := cover) hLast
          simp [hxEq] at hx
          subst x
          simpa [hlastEq] using mem_textbookEdgeList_track_exit hslot hu hLast

/-- One selector slot, using a detoured selected-vertex track when the slot is occupied. -/
noncomputable def detouredSlotSkeleton
    (I : VertexCoverInput) (cover : List Nat) (slot : Nat) (choice : Option Nat) : List Nat :=
  [textbookSelectorVertex slot] ++
    match choice with
    | none => []
    | some u => detouredVertexTrack I cover u

theorem detouredSlotSkeleton_withinBounds
    {I : VertexCoverInput} {cover : List Nat} {slot : Nat} {choice : Option Nat}
    (hslot : slot < I.k) :
    VerticesWithinBounds (textbookMap I).graph
      (detouredSlotSkeleton I cover slot choice) := by
  intro v hv
  cases choice with
  | none =>
      simp [detouredSlotSkeleton] at hv
      subst v
      exact textbookSelectorVertex_lt hslot
  | some u =>
      simp [detouredSlotSkeleton] at hv
      rcases hv with hv | hv
      · subst v
        exact textbookSelectorVertex_lt hslot
      · exact detouredVertexTrack_withinBounds I cover u v hv

theorem detouredSlotSkeleton_edgeChain
    {I : VertexCoverInput} {cover : List Nat} {slot : Nat} {choice : Option Nat}
    (hslot : slot < I.k)
    (hChoice : ∀ u, choice = some u → u < I.graph.vertices) :
    (detouredSlotSkeleton I cover slot choice).IsChain
      fun a b => (a, b) ∈ textbookEdgeList I := by
  cases choice with
  | none =>
      simp [detouredSlotSkeleton]
  | some u =>
      have hu : u < I.graph.vertices := hChoice u rfl
      simp [detouredSlotSkeleton]
      rw [List.isChain_cons]
      exact ⟨detouredVertexTrack_entry_splice hslot hu, detouredVertexTrack_edgeChain hu⟩

theorem detouredSlotSkeleton_head?
    (I : VertexCoverInput) (cover : List Nat) (slot : Nat) (choice : Option Nat) :
    (detouredSlotSkeleton I cover slot choice).head? = some (textbookSelectorVertex slot) := by
  cases choice <;> simp [detouredSlotSkeleton]

theorem mem_detouredSlotSkeleton_iff
    (I : VertexCoverInput) (cover : List Nat) (slot x : Nat) (choice : Option Nat) :
    x ∈ detouredSlotSkeleton I cover slot choice ↔
      x = textbookSelectorVertex slot ∨
        ∃ u, choice = some u ∧ x ∈ detouredVertexTrack I cover u := by
  cases choice <;> simp [detouredSlotSkeleton]

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
