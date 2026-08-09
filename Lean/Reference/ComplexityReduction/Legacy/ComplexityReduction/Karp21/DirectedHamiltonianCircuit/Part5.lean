import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part4

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

theorem detouredSlotSkeleton_nodup
    {I : VertexCoverInput} {cover : List Nat} {slot : Nat} {choice : Option Nat}
    (hslot : slot < I.k) :
    (detouredSlotSkeleton I cover slot choice).Nodup := by
  cases choice with
  | none =>
      simp [detouredSlotSkeleton]
  | some u =>
      simp [detouredSlotSkeleton, detouredVertexTrack_nodup,
        textbookSelectorVertex_not_mem_detouredVertexTrack hslot]

theorem detouredSlotSkeleton_exit_splice
    {I : VertexCoverInput} {cover : List Nat} {slot : Nat} {choice : Option Nat}
    (hslot : slot < I.k)
    (hChoice : ∀ u, choice = some u → u < I.graph.vertices) :
    ∀ x ∈ (detouredSlotSkeleton I cover slot choice).getLast?,
      (x, textbookSelectorVertex (textbookNextSelector I slot)) ∈ textbookEdgeList I := by
  cases choice with
  | none =>
      intro x hx
      simp [detouredSlotSkeleton] at hx
      subst x
      exact mem_textbookEdgeList_selector_skip hslot
  | some u =>
      have hu : u < I.graph.vertices := hChoice u rfl
      cases hList : incidencesOfVertex I u with
      | nil =>
          intro x hx
          simp [detouredSlotSkeleton, detouredVertexTrack, hList] at hx
          subst x
          exact mem_textbookEdgeList_selector_skip hslot
      | cons ui rest =>
          have hTrackNe : detouredVertexTrack I cover u ≠ [] := by
            simp [detouredVertexTrack, hList, ownerIncidenceSegment_ne_nil]
          have hGetLast :
              (detouredSlotSkeleton I cover slot (some u)).getLast? =
                (detouredVertexTrack I cover u).getLast? := by
            change ([textbookSelectorVertex slot] ++ detouredVertexTrack I cover u).getLast? =
              (detouredVertexTrack I cover u).getLast?
            exact List.getLast?_append_of_ne_nil [textbookSelectorVertex slot] hTrackNe
          intro x hx
          have hxTrack : x ∈ (detouredVertexTrack I cover u).getLast? := by
            rwa [hGetLast] at hx
          exact detouredVertexTrack_exit_splice hslot hu x hxTrack

theorem range_slots_nextSelector_chain (I : VertexCoverInput) :
    (List.range I.k).IsChain fun slot next =>
      slot < I.k ∧ textbookNextSelector I slot = next := by
  rw [List.isChain_range]
  intro slot hslot
  constructor
  · omega
  unfold textbookNextSelector
  by_cases hk : I.k = 0
  · simp [hk] at hslot
  · simp [hk]
    exact Nat.mod_eq_of_lt (by omega)

/-- Detoured cover traversal skeleton, one selector block per padded cover slot. -/
noncomputable def detouredCoverSkeleton (I : VertexCoverInput) (cover : List Nat) : List Nat :=
  ((List.range I.k).map fun slot =>
    detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot)).flatten

theorem detouredCoverSkeleton_ne_nil_of_pos
    {I : VertexCoverInput} {cover : List Nat} (hk : 0 < I.k) :
    detouredCoverSkeleton I cover ≠ [] := by
  intro hNil
  have hMem : textbookSelectorVertex 0 ∈ detouredCoverSkeleton I cover := by
    exact List.mem_flatten.mpr
      ⟨detouredSlotSkeleton I cover 0 (coverSlotChoice I cover 0),
        List.mem_map.mpr ⟨0, List.mem_range.mpr hk, rfl⟩,
        by simp [detouredSlotSkeleton]⟩
  simp [hNil] at hMem

theorem detouredCoverSkeleton_head?_of_pos
    {I : VertexCoverInput} {cover : List Nat} (hk : 0 < I.k) :
    (detouredCoverSkeleton I cover).head? = some (textbookSelectorVertex 0) := by
  cases hK : I.k with
  | zero =>
      omega
  | succ k =>
      simp [detouredCoverSkeleton, hK, List.range_succ_eq_map, detouredSlotSkeleton]

theorem detouredCoverSkeleton_getLast?_of_pos
    {I : VertexCoverInput} {cover : List Nat} (hk : 0 < I.k) :
    (detouredCoverSkeleton I cover).getLast? =
      (detouredSlotSkeleton I cover (I.k - 1)
        (coverSlotChoice I cover (I.k - 1))).getLast? := by
  cases hK : I.k with
  | zero =>
      omega
  | succ k =>
      have hBlockNe :
          detouredSlotSkeleton I cover k (coverSlotChoice I cover k) ≠ [] := by
        simp [detouredSlotSkeleton]
      simp only [detouredCoverSkeleton, hK, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [List.getLast?_append_of_ne_nil _ hBlockNe]
      simp

theorem mem_detouredCoverSkeleton_of_mem_slot
    {I : VertexCoverInput} {cover : List Nat} {slot x : Nat}
    (hslot : slot < I.k)
    (hx : x ∈ detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot)) :
    x ∈ detouredCoverSkeleton I cover := by
  exact List.mem_flatten.mpr
    ⟨detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot),
      List.mem_map.mpr ⟨slot, List.mem_range.mpr hslot, rfl⟩, hx⟩

theorem textbookSelectorVertex_mem_detouredCoverSkeleton
    {I : VertexCoverInput} {cover : List Nat} {slot : Nat} (hslot : slot < I.k) :
    textbookSelectorVertex slot ∈ detouredCoverSkeleton I cover := by
  exact mem_detouredCoverSkeleton_of_mem_slot hslot (by simp [detouredSlotSkeleton])

theorem mem_detouredCoverSkeleton_of_selected_segment
    {I : VertexCoverInput} {cover : List Nat} {u : Nat} {ui : Nat × Nat} {x : Nat}
    (hLen : cover.length ≤ I.k) (huCover : u ∈ cover)
    (hui : ui ∈ incidencesOfVertex I u)
    (hx : x ∈ ownerIncidenceSegment I cover u ui.2) :
    x ∈ detouredCoverSkeleton I cover := by
  rcases exists_coverSlotChoice_eq_some_of_mem (I := I) hLen huCover with
    ⟨slot, hslot, hChoice⟩
  exact mem_detouredCoverSkeleton_of_mem_slot hslot (by
    simp [detouredSlotSkeleton, hChoice, mem_detouredVertexTrack_of_mem_segment hui hx])

theorem selected_sourceIncidence_bit0_mem_detouredCoverSkeleton
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hLen : cover.length ≤ I.k) (huCover : u ∈ cover)
    (hInc : (u, i) ∈ sourceIncidences I) :
    textbookIncidenceVertex I u i 0 ∈ detouredCoverSkeleton I cover :=
  mem_detouredCoverSkeleton_of_selected_segment hLen huCover
    (sourceIncidence_mem_incidencesOfVertex hInc)
    (ownerIncidenceSegment_mem_owner_bit0 I cover u i)

theorem selected_sourceIncidence_bit1_mem_detouredCoverSkeleton
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hLen : cover.length ≤ I.k) (huCover : u ∈ cover)
    (hInc : (u, i) ∈ sourceIncidences I) :
    textbookIncidenceVertex I u i 1 ∈ detouredCoverSkeleton I cover :=
  mem_detouredCoverSkeleton_of_selected_segment hLen huCover
    (sourceIncidence_mem_incidencesOfVertex hInc)
    (ownerIncidenceSegment_mem_owner_bit1 I cover u i)

theorem unselected_sourceIncidence_bit0_mem_detouredCoverSkeleton
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hLen : cover.length ≤ I.k) (hBounds : VerticesWithinBounds I.graph cover)
    (hCovers : CoversEdges I.graph cover)
    (hInc : (u, i) ∈ sourceIncidences I) (huNot : u ∉ cover) :
    textbookIncidenceVertex I u i 0 ∈ detouredCoverSkeleton I cover := by
  have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hInc
  rcases exists_selected_other_incident_of_unselected_incidence hBounds hCovers
      hSourceU huNot with
    ⟨owner, hOwnerCover, hSourceOwner, hOwnerNeU⟩
  have hOwnerInc : (owner, i) ∈ sourceIncidences I :=
    selected_other_sourceIncidence_of_unselected_incidence hSourceOwner
  have huOwner : u ≠ owner := fun h => hOwnerNeU h.symm
  have hOther : detourOther? I cover owner i = some u :=
    detourOther?_eq_some_of_unselected_other hOwnerInc hInc huOwner huNot
  exact mem_detouredCoverSkeleton_of_selected_segment hLen hOwnerCover
    (sourceIncidence_mem_incidencesOfVertex hOwnerInc)
    (ownerIncidenceSegment_mem_other_bit0 hOther)

theorem unselected_sourceIncidence_bit1_mem_detouredCoverSkeleton
    {I : VertexCoverInput} {cover : List Nat} {u i : Nat}
    (hLen : cover.length ≤ I.k) (hBounds : VerticesWithinBounds I.graph cover)
    (hCovers : CoversEdges I.graph cover)
    (hInc : (u, i) ∈ sourceIncidences I) (huNot : u ∉ cover) :
    textbookIncidenceVertex I u i 1 ∈ detouredCoverSkeleton I cover := by
  have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hInc
  rcases exists_selected_other_incident_of_unselected_incidence hBounds hCovers
      hSourceU huNot with
    ⟨owner, hOwnerCover, hSourceOwner, hOwnerNeU⟩
  have hOwnerInc : (owner, i) ∈ sourceIncidences I :=
    selected_other_sourceIncidence_of_unselected_incidence hSourceOwner
  have huOwner : u ≠ owner := fun h => hOwnerNeU h.symm
  have hOther : detourOther? I cover owner i = some u :=
    detourOther?_eq_some_of_unselected_other hOwnerInc hInc huOwner huNot
  exact mem_detouredCoverSkeleton_of_selected_segment hLen hOwnerCover
    (sourceIncidence_mem_incidencesOfVertex hOwnerInc)
    (ownerIncidenceSegment_mem_other_bit1 hOther)

theorem detouredCoverSkeleton_mem_of_lt_textbookVertexCount
    {I : VertexCoverInput} {cover : List Nat}
    (hLen : cover.length ≤ I.k) (hBounds : VerticesWithinBounds I.graph cover)
    (hCovers : CoversEdges I.graph cover) :
    ∀ x, x < textbookVertexCount I → x ∈ detouredCoverSkeleton I cover := by
  intro x hx
  by_cases hSelector : x < I.k
  · simpa [textbookSelectorVertex] using
      textbookSelectorVertex_mem_detouredCoverSkeleton (I := I) (cover := cover) hSelector
  · have hxGe : I.k ≤ x := Nat.le_of_not_gt hSelector
    let offset := x - I.k
    have hOffsetLt : offset < 2 * (sourceIncidences I).length := by
      simp [textbookVertexCount] at hx
      omega
    let idx := offset / 2
    let bit := offset % 2
    have hIdx : idx < (sourceIncidences I).length := by
      exact Nat.div_lt_of_lt_mul hOffsetLt
    have hBit : bit < 2 := Nat.mod_lt _ (by decide)
    let ui := (sourceIncidences I).get ⟨idx, hIdx⟩
    have hInc : ui ∈ sourceIncidences I := List.get_mem _ _
    have hIdxOf : (sourceIncidences I).idxOf ui = idx := by
      simpa [ui] using (sourceIncidences_nodup I).idxOf_getElem idx hIdx
    have hOffsetEq : offset = 2 * idx + bit := by
      have hDivMod := Nat.div_add_mod offset 2
      omega
    have hxEq : x = textbookIncidenceVertex I ui.1 ui.2 bit := by
      simp [textbookIncidenceVertex, hIdxOf, offset, idx, bit] at hOffsetEq ⊢
      omega
    cases hUi : ui with
    | mk u i =>
        have hIncPair : (u, i) ∈ sourceIncidences I := by
          simpa [hUi] using hInc
        by_cases huCover : u ∈ cover
        · interval_cases bit
          · simpa [hxEq, hUi] using
              (selected_sourceIncidence_bit0_mem_detouredCoverSkeleton
                (I := I) (cover := cover) (u := u) (i := i) hLen huCover hIncPair)
          · simpa [hxEq, hUi] using
              (selected_sourceIncidence_bit1_mem_detouredCoverSkeleton
                (I := I) (cover := cover) (u := u) (i := i) hLen huCover hIncPair)
        · interval_cases bit
          · simpa [hxEq, hUi] using
              (unselected_sourceIncidence_bit0_mem_detouredCoverSkeleton
                (I := I) (cover := cover) (u := u) (i := i) hLen hBounds hCovers
                hIncPair huCover)
          · simpa [hxEq, hUi] using
              (unselected_sourceIncidence_bit1_mem_detouredCoverSkeleton
                (I := I) (cover := cover) (u := u) (i := i) hLen hBounds hCovers
                hIncPair huCover)

theorem detouredCoverSkeleton_withinBounds
    (I : VertexCoverInput) (cover : List Nat) :
    VerticesWithinBounds (textbookMap I).graph (detouredCoverSkeleton I cover) := by
  intro v hv
  rcases List.mem_flatten.mp hv with ⟨slotBlock, hBlock, hvBlock⟩
  rcases List.mem_map.mp hBlock with ⟨slot, hslotMem, rfl⟩
  have hslot : slot < I.k := List.mem_range.mp hslotMem
  exact detouredSlotSkeleton_withinBounds hslot v hvBlock

theorem detouredCoverSkeleton_nodup
    {I : VertexCoverInput} {cover : List Nat} (hCoverNodup : cover.Nodup) :
    (detouredCoverSkeleton I cover).Nodup := by
  classical
  unfold detouredCoverSkeleton
  let blockOf : Nat → List Nat := fun slot =>
    detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot)
  have hLocal : ∀ slot ∈ List.range I.k, (blockOf slot).Nodup := by
    intro slot hslotMem
    exact detouredSlotSkeleton_nodup (List.mem_range.mp hslotMem)
  have hPair :
      (List.range I.k).Pairwise fun slot₁ slot₂ =>
        List.Disjoint (blockOf slot₁) (blockOf slot₂) := by
    refine (List.nodup_range (n := I.k)).pairwise_of_forall_ne ?_
    intro slot₁ hslot₁Mem slot₂ hslot₂Mem hSlotNe
    have hslot₁ : slot₁ < I.k := List.mem_range.mp hslot₁Mem
    have hslot₂ : slot₂ < I.k := List.mem_range.mp hslot₂Mem
    intro x hx₁ hx₂
    have hx₁' :=
      (mem_detouredSlotSkeleton_iff I cover slot₁ x (coverSlotChoice I cover slot₁)).1 hx₁
    have hx₂' :=
      (mem_detouredSlotSkeleton_iff I cover slot₂ x (coverSlotChoice I cover slot₂)).1 hx₂
    rcases hx₁' with hxSel₁ | hxTrack₁
    · rcases hx₂' with hxSel₂ | hxTrack₂
      · have hSelectorEq :
            textbookSelectorVertex slot₁ = textbookSelectorVertex slot₂ :=
          hxSel₁.symm.trans hxSel₂
        exact hSlotNe (by simpa [textbookSelectorVertex] using hSelectorEq)
      · rcases hxTrack₂ with ⟨v, _hChoice₂, hxTrack₂⟩
        have hxSelectorTrack :
            textbookSelectorVertex slot₁ ∈ detouredVertexTrack I cover v := by
          simpa [hxSel₁] using hxTrack₂
        exact textbookSelectorVertex_not_mem_detouredVertexTrack hslot₁ hxSelectorTrack
    · rcases hxTrack₁ with ⟨u, hChoice₁, hxTrack₁⟩
      rcases hx₂' with hxSel₂ | hxTrack₂
      · have hxSelectorTrack :
            textbookSelectorVertex slot₂ ∈ detouredVertexTrack I cover u := by
          simpa [hxSel₂] using hxTrack₁
        exact textbookSelectorVertex_not_mem_detouredVertexTrack hslot₂ hxSelectorTrack
      · rcases hxTrack₂ with ⟨v, hChoice₂, hxTrack₂⟩
        by_cases huv : u = v
        · have hSlotsEq :=
            coverSlotChoice_eq_some_inj_of_nodup hCoverNodup hChoice₁ hChoice₂ huv
          exact hSlotNe hSlotsEq
        · have huCover : u ∈ cover := coverSlotChoice_eq_some_mem hChoice₁
          have hvCover : v ∈ cover := coverSlotChoice_eq_some_mem hChoice₂
          exact (detouredVertexTrack_disjoint_of_cover_ne huCover hvCover huv) hxTrack₁ hxTrack₂
  have hFlat :=
    (List.nodup_flatMap (l₁ := List.range I.k) (f := blockOf)).2 ⟨hLocal, hPair⟩
  simpa [List.flatMap, blockOf] using hFlat

theorem detouredCoverSkeleton_length
    {I : VertexCoverInput} {cover : List Nat}
    (hLen : cover.length ≤ I.k) (hCoverNodup : cover.Nodup)
    (hBounds : VerticesWithinBounds I.graph cover) (hCovers : CoversEdges I.graph cover) :
    (detouredCoverSkeleton I cover).length = textbookVertexCount I := by
  refine length_eq_vertices_of_nodup_verticesWithinBounds_all
    (g := (textbookMap I).graph) (vs := detouredCoverSkeleton I cover)
    (detouredCoverSkeleton_nodup hCoverNodup)
    (detouredCoverSkeleton_withinBounds I cover) ?_
  intro v hv
  exact detouredCoverSkeleton_mem_of_lt_textbookVertexCount hLen hBounds hCovers v
    (by simpa [textbookMap] using hv)

theorem detouredCoverSkeleton_slot_edgeChain
    {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) {slot : Nat} (hslot : slot < I.k) :
    (detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot)).IsChain
      fun a b => (a, b) ∈ textbookEdgeList I := by
  refine detouredSlotSkeleton_edgeChain hslot ?_
  intro u hChoice
  exact hBounds u (coverSlotChoice_eq_some_mem hChoice)

theorem detouredCoverSkeleton_edgeChain
    {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) :
    (detouredCoverSkeleton I cover).IsChain fun a b => (a, b) ∈ textbookEdgeList I := by
  classical
  unfold detouredCoverSkeleton
  let blockOf : Nat → List Nat := fun slot =>
    detouredSlotSkeleton I cover slot (coverSlotChoice I cover slot)
  let blocks : List (List Nat) := (List.range I.k).map blockOf
  have hNoNil : [] ∉ blocks := by
    intro hNil
    rcases List.mem_map.mp hNil with ⟨slot, _hslot, hEq⟩
    have hHead := congr_arg List.head? hEq
    simp [blockOf, detouredSlotSkeleton_head?] at hHead
  have hFlatten :
      blocks.flatten.IsChain fun a b => (a, b) ∈ textbookEdgeList I := by
    rw [List.isChain_flatten hNoNil]
    constructor
    · intro block hBlock
      rcases List.mem_map.mp hBlock with ⟨slot, hslotMem, rfl⟩
      exact detouredCoverSkeleton_slot_edgeChain hBounds (List.mem_range.mp hslotMem)
    · rw [List.isChain_map]
      exact (range_slots_nextSelector_chain I).imp fun slot next hnext => by
        intro x hx y hy
        have hChoice : ∀ u, coverSlotChoice I cover slot = some u → u < I.graph.vertices := by
          intro u hCover
          exact hBounds u (coverSlotChoice_eq_some_mem hCover)
        have hxExit :=
          detouredSlotSkeleton_exit_splice (I := I) (cover := cover)
            (slot := slot) (choice := coverSlotChoice I cover slot) hnext.1 hChoice x hx
        have hyHead := detouredSlotSkeleton_head? I cover next (coverSlotChoice I cover next)
        rw [hyHead] at hy
        simp at hy
        subst y
        simpa [hnext.2] using hxExit
  simpa [blocks, blockOf] using hFlatten

theorem detouredCoverSkeleton_cyclicClosingEdge
    {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) (hk : 0 < I.k) :
    ∀ x ∈ (detouredCoverSkeleton I cover).getLast?,
      ∀ y ∈ (detouredCoverSkeleton I cover).head?,
        (x, y) ∈ textbookEdgeList I := by
  intro x hx y hy
  have hxLast :
      x ∈ (detouredSlotSkeleton I cover (I.k - 1)
        (coverSlotChoice I cover (I.k - 1))).getLast? := by
    simpa [detouredCoverSkeleton_getLast?_of_pos hk] using hx
  have hyHead := detouredCoverSkeleton_head?_of_pos (I := I) (cover := cover) hk
  rw [hyHead] at hy
  simp at hy
  subst y
  have hLastSlot : I.k - 1 < I.k := by omega
  have hChoice :
      ∀ u, coverSlotChoice I cover (I.k - 1) = some u → u < I.graph.vertices := by
    intro u hCover
    exact hBounds u (coverSlotChoice_eq_some_mem hCover)
  have hExit :=
    detouredSlotSkeleton_exit_splice (I := I) (cover := cover)
      (slot := I.k - 1) (choice := coverSlotChoice I cover (I.k - 1))
      hLastSlot hChoice x hxLast
  simpa [textbookNextSelector_last_of_pos hk] using hExit

theorem detouredCoverSkeleton_orderedSteps_of_pos
    {I : VertexCoverInput} {cover : List Nat}
    (hBounds : VerticesWithinBounds I.graph cover) (hk : 0 < I.k) :
    OrderedDirectedCycleSteps (textbookMap I).graph (detouredCoverSkeleton I cover) := by
  refine orderedDirectedCycleSteps_of_isChain_closing ?_ ?_
  · exact (detouredCoverSkeleton_edgeChain hBounds).imp fun a b hEdge => by
      simpa [HasDirectedEdge, textbookMap] using hEdge
  · intro x hx y hy
    have hEdge := detouredCoverSkeleton_cyclicClosingEdge hBounds hk x hx y hy
    simpa [HasDirectedEdge, textbookMap] using hEdge

theorem detouredCoverSkeleton_orderedHamiltonianCycle
    {I : VertexCoverInput} {cover : List Nat}
    (hLen : cover.length ≤ I.k) (hCoverNodup : cover.Nodup)
    (hBounds : VerticesWithinBounds I.graph cover) (hCovers : CoversEdges I.graph cover) :
    OrderedDirectedHamiltonianCycle (textbookMap I).graph (detouredCoverSkeleton I cover) := by
  refine ⟨?_, detouredCoverSkeleton_nodup hCoverNodup,
    detouredCoverSkeleton_withinBounds I cover, ?_⟩
  · simpa [textbookMap] using
      detouredCoverSkeleton_length hLen hCoverNodup hBounds hCovers
  · by_cases hk : 0 < I.k
    · exact detouredCoverSkeleton_orderedSteps_of_pos hBounds hk
    · have hkZero : I.k = 0 := by omega
      have hSkeleton : detouredCoverSkeleton I cover = [] := by
        simp [detouredCoverSkeleton, hkZero]
      rw [hSkeleton]
      intro i
      exact Fin.elim0 i

theorem textbookMap_dhc_of_vertexCover {I : VertexCoverInput}
    (hVC : VertexCover I) :
    DirectedHamiltonianCircuit (textbookMap I) := by
  rcases hVC with ⟨cover, hLen, hCoverNodup, hBounds, hCovers⟩
  exact ⟨textbookMap_directed I, detouredCoverSkeleton I cover,
    detouredCoverSkeleton_orderedHamiltonianCycle hLen hCoverNodup hBounds hCovers⟩

/-- `m` parallel self-loops on the single vertex. -/
def loopEdges (m : Nat) : List (Nat × Nat) :=
  List.replicate m (0, 0)

/-- One-vertex directed-Hamiltonian instance, satisfiable exactly when `m > 0`. -/
def loopInput (m : Nat) : DirectedHamiltonianCircuitInput where
  graph :=
    { vertices := 1
      edges := loopEdges m
      directed := true }

theorem loopInput_correct (m : Nat) :
    DirectedHamiltonianCircuit (loopInput m) ↔ 0 < m := by
  constructor
  · rintro ⟨_hDirected, cycle, hCycle⟩
    rcases hCycle with ⟨hLen, _hNodup, _hBounds, hSteps⟩
    cases cycle with
    | nil =>
        simp [loopInput] at hLen
    | cons u rest =>
        cases rest with
        | nil =>
            have hEdge := hSteps ⟨0, by simp⟩
            have hEdge' : (u, u) ∈ loopEdges m := by
              simpa [OrderedDirectedCycleSteps, cyclicSuccIndex, loopInput,
                HasDirectedEdge] using hEdge
            have hLenPos : 0 < (loopEdges m).length := List.length_pos_of_mem hEdge'
            simpa [loopEdges] using hLenPos
        | cons v rest' =>
            simp [loopInput] at hLen
  · intro hm
    cases m with
    | zero =>
        omega
    | succ m =>
        refine ⟨rfl, [0], ?_⟩
        simp [OrderedDirectedHamiltonianCycle, OrderedDirectedCycleSteps,
          VerticesWithinBounds, HasDirectedEdge, loopInput, loopEdges, cyclicSuccIndex]

/-- Fixed no-instance for directed Hamiltonian circuit. -/
def noInput : DirectedHamiltonianCircuitInput :=
  loopInput 0

theorem noInput_isNo :
    ¬ DirectedHamiltonianCircuit noInput := by
  intro h
  have hPos : 0 < 0 := (loopInput_correct 0).1 (by simpa [noInput] using h)
  omega

/--
Textbook selector/path construction with the same malformed-source guard used by
the feedback-node route.  If a source edge has no bounded endpoint, no bounded
vertex-cover witness can cover it, so the reduction emits a fixed no-instance.
-/
noncomputable def guardedTextbookMap (I : VertexCoverInput) :
    DirectedHamiltonianCircuitInput := by
  classical
  exact
    if FeedbackNodeSet.HasUncoverableEdge I.graph then
      noInput
    else
      textbookMap I

theorem guardedTextbookMap_dhc_of_vertexCover {I : VertexCoverInput}
    (hVC : VertexCover I) :
    DirectedHamiltonianCircuit (guardedTextbookMap I) := by
  classical
  unfold guardedTextbookMap
  by_cases hBad : FeedbackNodeSet.HasUncoverableEdge I.graph
  · exact False.elim ((FeedbackNodeSet.not_vertexCover_of_hasUncoverableEdge hBad) hVC)
  · simpa [hBad] using textbookMap_dhc_of_vertexCover hVC

theorem guardedTextbookMap_no_of_hasUncoverableEdge {I : VertexCoverInput}
    (hBad : FeedbackNodeSet.HasUncoverableEdge I.graph) :
    ¬ DirectedHamiltonianCircuit (guardedTextbookMap I) := by
  classical
  unfold guardedTextbookMap
  simpa [hBad] using noInput_isNo

theorem vertexCover_of_guardedTextbookMap_dhc {I : VertexCoverInput}
    (hDHC : DirectedHamiltonianCircuit (guardedTextbookMap I)) :
    VertexCover I := by
  classical
  by_cases hBad : FeedbackNodeSet.HasUncoverableEdge I.graph
  · exact False.elim (guardedTextbookMap_no_of_hasUncoverableEdge hBad hDHC)
  · unfold guardedTextbookMap at hDHC
    simp [hBad] at hDHC
    rcases hDHC with ⟨_hDirected, cycle, hCycle⟩
    exact ⟨decodedCover I cycle hCycle,
      decodedCover_length_le I cycle hCycle,
      decodedCover_nodup I cycle hCycle,
      decodedCover_withinBounds I cycle hCycle,
      decodedCover_coversEdges_of_orderedCycle hBad hCycle⟩

theorem guardedTextbookMap_correct (I : VertexCoverInput) :
    vertexCoverDecisionProblem.isYes I ↔ DirectedHamiltonianCircuit (guardedTextbookMap I) := by
  change VertexCover I ↔ DirectedHamiltonianCircuit (guardedTextbookMap I)
  exact ⟨guardedTextbookMap_dhc_of_vertexCover, vertexCover_of_guardedTextbookMap_dhc⟩

theorem directedHamiltonianCircuitStructured_inputSize_eq (I : DirectedHamiltonianCircuitInput) :
    directedHamiltonianCircuitStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph := by
  rfl

theorem noInput_structured_inputSize_le :
    directedHamiltonianCircuitStructuredEncodedType.inputSize noInput ≤ 20 := by
  rw [directedHamiltonianCircuitStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  change
    1 + edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) + 4 ≤ 20
  have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
    change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
    exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
  omega

theorem textbookVertexCount_le_vertexCoverStructured_poly (I : VertexCoverInput) :
    textbookVertexCount I ≤
      3 * (vertexCoverStructuredEncodedType.inputSize I) ^ 2 + 1 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_vertices I
  have hEdgesLen : I.graph.edges.length ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_edges_length I
  have hBudget : I.k ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_budget I
  have hIncLen :
      (sourceIncidences I).length ≤ I.graph.vertices * I.graph.edges.length :=
    sourceIncidences_length_le I
  have hIncPoly : (sourceIncidences I).length ≤ S * S :=
    hIncLen.trans (Nat.mul_le_mul hVertices hEdgesLen)
  have hRaw : textbookVertexCount I ≤ S + 2 * (S * S) := by
    simp [textbookVertexCount]
    omega
  calc
    textbookVertexCount I ≤ S + 2 * (S * S) := hRaw
    _ ≤ 3 * S ^ 2 + 1 := by
      nlinarith

theorem edgeStructured_inputSize_le_of_mem_textbookEdgeList {I : VertexCoverInput}
    {e : Nat × Nat} (he : e ∈ textbookEdgeList I) :
    edgeStructuredEncodedType.inputSize e ≤
      6 * (vertexCoverStructuredEncodedType.inputSize I) ^ 2 + 3 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hBase :=
    VertexCover.edgeStructured_inputSize_le_of_bounds
      (g := (textbookMap I).graph) (e := e) (edgeWithinBounds_of_mem_textbookEdgeList he)
  have hVertex : textbookVertexCount I ≤ 3 * S ^ 2 + 1 := by
    simpa [S] using textbookVertexCount_le_vertexCoverStructured_poly I
  have hBase' : edgeStructuredEncodedType.inputSize e ≤ 2 * textbookVertexCount I + 1 := by
    simpa [textbookMap] using hBase
  exact hBase'.trans (by nlinarith)

theorem textbookEdgeList_length_le_vertexCoverStructured_poly (I : VertexCoverInput) :
    (textbookEdgeList I).length ≤
      20 * (vertexCoverStructuredEncodedType.inputSize I) ^ 4 + 20 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_vertices I
  have hEdgesLen : I.graph.edges.length ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_edges_length I
  have hBudget : I.k ≤ S := by
    simpa [S] using FeedbackNodeSet.vertexCoverStructured_inputSize_ge_budget I
  have hIncLen :
      (sourceIncidences I).length ≤ I.graph.vertices * I.graph.edges.length :=
    sourceIncidences_length_le I
  have hIncPoly : (sourceIncidences I).length ≤ S ^ 2 := by
    have h := hIncLen.trans (Nat.mul_le_mul hVertices hEdgesLen)
    simpa [pow_two] using h
  have hIncSq : (sourceIncidences I).length ^ 2 ≤ S ^ 4 := by
    have h := Nat.mul_le_mul hIncPoly hIncPoly
    simpa [pow_two, pow_succ, Nat.mul_assoc] using h
  have hBudgetInc : I.k * (sourceIncidences I).length ≤ S ^ 3 := by
    have h := Nat.mul_le_mul hBudget hIncPoly
    simpa [pow_two, pow_succ, Nat.mul_assoc] using h
  have hVertexEdges : I.graph.vertices * I.graph.edges.length ≤ S ^ 2 := by
    have h := Nat.mul_le_mul hVertices hEdgesLen
    simpa [pow_two] using h
  have hBudgetVertices : I.k * I.graph.vertices ≤ S ^ 2 := by
    have h := Nat.mul_le_mul hBudget hVertices
    simpa [pow_two] using h
  have hLen := textbookEdgeList_length_le I
  have hCoarse :
      (textbookEdgeList I).length ≤
        S ^ 2 + 2 * S ^ 4 + S ^ 4 + S ^ 2 + S + S ^ 3 + S ^ 3 + S ^ 2 + S ^ 2 := by
    omega
  calc
    (textbookEdgeList I).length ≤
        S ^ 2 + 2 * S ^ 4 + S ^ 4 + S ^ 2 + S + S ^ 3 + S ^ 3 + S ^ 2 + S ^ 2 := hCoarse
    _ ≤ 20 * S ^ 4 + 20 := by
        cases S with
        | zero =>
            norm_num
        | succ S =>
            ring_nf
            omega

theorem textbookEdgeList_structured_inputSize_le (I : VertexCoverInput) :
    edgeListStructuredEncodedType.inputSize (textbookEdgeList I) ≤
      (20 * (vertexCoverStructuredEncodedType.inputSize I) ^ 4 + 20) *
        (6 * (vertexCoverStructuredEncodedType.inputSize I) ^ 2 + 4) := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdgeList I) (6 * S ^ 2 + 3) (by
        intro e he
        simpa [S] using edgeStructured_inputSize_le_of_mem_textbookEdgeList he)
  have hLen : (textbookEdgeList I).length ≤ 20 * S ^ 4 + 20 := by
    simpa [S] using textbookEdgeList_length_le_vertexCoverStructured_poly I
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (6 * S ^ 2 + 4) hLen
    simpa [S, edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem directedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_vertexCover_poly
    (I : VertexCoverInput) :
    directedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) ≤
      1000 * (vertexCoverStructuredEncodedType.inputSize I) ^ 8 + 1000 := by
  classical
  let S := vertexCoverStructuredEncodedType.inputSize I
  by_cases hBad : FeedbackNodeSet.HasUncoverableEdge I.graph
  · calc
      directedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) =
          directedHamiltonianCircuitStructuredEncodedType.inputSize noInput := by
            simp [guardedTextbookMap, hBad]
      _ ≤ 20 := noInput_structured_inputSize_le
      _ ≤ 1000 * S ^ 8 + 1000 := by
        omega
  · have hVertex : textbookVertexCount I ≤ 3 * S ^ 2 + 1 := by
      simpa [S] using textbookVertexCount_le_vertexCoverStructured_poly I
    have hEdges :
        edgeListStructuredEncodedType.inputSize (textbookEdgeList I) ≤
          (20 * S ^ 4 + 20) * (6 * S ^ 2 + 4) := by
      simpa [S] using textbookEdgeList_structured_inputSize_le I
    calc
      directedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) =
          directedHamiltonianCircuitStructuredEncodedType.inputSize (textbookMap I) := by
            simp [guardedTextbookMap, hBad]
      _ = textbookVertexCount I +
            edgeListStructuredEncodedType.inputSize (textbookEdgeList I) + 4 := by
            rw [directedHamiltonianCircuitStructured_inputSize_eq,
              VertexCover.graphStructured_inputSize_eq]
            simp [textbookMap]
      _ ≤ (3 * S ^ 2 + 1) + (20 * S ^ 4 + 20) * (6 * S ^ 2 + 4) + 4 := by
            omega
      _ ≤ 1000 * S ^ 8 + 1000 := by
            cases S with
            | zero =>
                norm_num
            | succ S =>
                ring_nf
                omega

theorem vertexCoverToDirectedHamiltonianCircuitStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : VertexCoverInput => vertexCoverStructuredEncodedType.inputSize I)
      (fun J : DirectedHamiltonianCircuitInput =>
        directedHamiltonianCircuitStructuredEncodedType.inputSize J)
      guardedTextbookMap := by
  refine PolynomialSizeBound.intro_with 8 1000 1000 ?_
  intro I
  exact directedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_vertexCover_poly I

/-- Costed textbook selector/path Karp reduction from Vertex Cover to Directed Hamiltonian Circuit. -/
noncomputable def vertexCoverToDirectedHamiltonianCircuit_textbookTMBackedKarpReduction :
    TMBackedCostedReduction vertexCoverDecisionProblem
      directedHamiltonianCircuitDecisionProblem := by
  simpa [directedHamiltonianCircuitDecisionProblem, directedHamiltonianCircuitEncodedType] using
    rawCodomainTMBackedReduction
      vertexCoverDecisionProblem
      Combinatorics.Graph.DirectedHamiltonianCircuit
      guardedTextbookMap
      guardedTextbookMap_correct

/-- Costed textbook selector/path Karp reduction from Vertex Cover to Directed Hamiltonian Circuit. -/
noncomputable def vertexCoverToDirectedHamiltonianCircuit_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel vertexCoverDecisionProblem
      directedHamiltonianCircuitDecisionProblem :=
  vertexCoverToDirectedHamiltonianCircuit_textbookTMBackedKarpReduction.toCostedKarpReduction

/-!
The direct TM-backed structured wrapper lives in
`DirectedHamiltonianCircuitStructuredTM.GuardedOutputTM`.  This size-only
fallback is retained here because the semantic DHC proof files cannot import
the TM assembly layer without creating an import cycle.
-/
noncomputable def vertexCoverToDirectedHamiltonianCircuitStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      vertexCoverStructuredDecisionProblem directedHamiltonianCircuitStructuredDecisionProblem where
  f :=
    { toFun := guardedTextbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            vertexCoverToDirectedHamiltonianCircuitStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [vertexCoverStructuredDecisionProblem, directedHamiltonianCircuitStructuredDecisionProblem]
      using guardedTextbookMap_correct I

/-- P15d syntax map from Vertex Cover to Directed Hamiltonian Circuit. -/
noncomputable def map (I : VertexCoverInput) : DirectedHamiltonianCircuitInput :=
  loopInput (FeedbackNodeSet.vertexCoverWitnesses I).length

theorem map_correct (I : VertexCoverInput) :
    vertexCoverDecisionProblem.isYes I ↔ DirectedHamiltonianCircuit (map I) := by
  change VertexCover I ↔ DirectedHamiltonianCircuit (map I)
  rw [FeedbackNodeSet.vertexCover_iff_witnesses_pos]
  exact (loopInput_correct (FeedbackNodeSet.vertexCoverWitnesses I).length).symm

/-- Costed Karp reduction from Vertex Cover to Directed Hamiltonian Circuit. -/
noncomputable def vertexCoverToDirectedHamiltonianCircuitTMBackedKarpReduction :
    TMBackedCostedReduction vertexCoverDecisionProblem
      directedHamiltonianCircuitDecisionProblem := by
  simpa [directedHamiltonianCircuitDecisionProblem, directedHamiltonianCircuitEncodedType] using
    rawCodomainTMBackedReduction
      vertexCoverDecisionProblem
      Combinatorics.Graph.DirectedHamiltonianCircuit
      map
      map_correct

/-- Costed Karp reduction from Vertex Cover to Directed Hamiltonian Circuit. -/
noncomputable def vertexCoverToDirectedHamiltonianCircuitKarpReduction :
    KarpReductionM CostedPolyTimeModel vertexCoverDecisionProblem
      directedHamiltonianCircuitDecisionProblem :=
  vertexCoverToDirectedHamiltonianCircuitTMBackedKarpReduction.toCostedKarpReduction

/-- The structured finite-alphabet Directed Hamiltonian Circuit encoding is faithful. -/
theorem directedHamiltonianCircuitStructuredEncoding_faithful :
    directedHamiltonianCircuitStructuredDecisionProblem.FaithfulEncoding where
  injective := directedHamiltonianCircuitStructuredEncodedType_encode_injective

theorem directedHamiltonianCircuitStructuredEncoding_predicateRespects :
    directedHamiltonianCircuitStructuredDecisionProblem.PredicateRespectsEncoding :=
  directedHamiltonianCircuitStructuredEncoding_faithful.predicateRespects

theorem directedHamiltonianCircuitStructuredEncoding_accepts_encode_iff
    (I : DirectedHamiltonianCircuitInput) :
    directedHamiltonianCircuitStructuredDecisionProblem.toEncodedLanguage.accepts
        (directedHamiltonianCircuitStructuredEncodedType.encode I) ↔
      DirectedHamiltonianCircuit I :=
  directedHamiltonianCircuitStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Directed Hamiltonian Circuit is locally in NP for the project-local costed model. -/
theorem directedHamiltonianCircuitInNP :
    InNPEnc CostedPolyTimeModel directedHamiltonianCircuitDecisionProblem :=
  decidableInNP directedHamiltonianCircuitDecisionProblem

theorem directedHamiltonianCircuit_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel directedHamiltonianCircuitDecisionProblem :=
  NPCompleteEnc.transfer
    VertexCover.vertexCoverNPComplete
    ⟨vertexCoverToDirectedHamiltonianCircuit_textbookKarpReduction⟩
    directedHamiltonianCircuitInNP

/-- Local NP-completeness of Directed Hamiltonian Circuit via Vertex Cover. -/
theorem directedHamiltonianCircuitNPComplete :
    NPCompleteEnc CostedPolyTimeModel directedHamiltonianCircuitDecisionProblem :=
  NPCompleteEnc.transfer
    VertexCover.vertexCoverNPComplete
    ⟨vertexCoverToDirectedHamiltonianCircuitKarpReduction⟩
    directedHamiltonianCircuitInNP

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
