import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuit.Part2

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

theorem cycleSuccessor_two_cycle_length
    {cycle : List Nat} {x y : Nat} (hNodup : cycle.Nodup)
    (hx : x ∈ cycle) (hy : y ∈ cycle) (hxy : x ≠ y)
    (hSuccXY : cycleSuccessor cycle x = y)
    (hSuccYX : cycleSuccessor cycle y = x) :
    cycle.length = 2 := by
  classical
  let n := cycle.length
  let ix := cycle.idxOf x
  let iy := cycle.idxOf y
  have hix : ix < n := by
    simpa [ix, n] using List.idxOf_lt_length_iff.mpr hx
  have hiy : iy < n := by
    simpa [iy, n] using List.idxOf_lt_length_iff.mpr hy
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le ix) hix
  have hSuccXYGet :
      cycle.get ⟨(ix + 1) % n, Nat.mod_lt _ hn⟩ = y := by
    simpa [cycleSuccessor, ix, n, hn] using hSuccXY
  have hSuccYXGet :
      cycle.get ⟨(iy + 1) % n, Nat.mod_lt _ hn⟩ = x := by
    simpa [cycleSuccessor, iy, n, hn] using hSuccYX
  have hiyEq : iy = (ix + 1) % n := by
    have hIdx := hNodup.idxOf_getElem ((ix + 1) % n) (Nat.mod_lt _ hn)
    change cycle.idxOf
        (cycle.get ⟨(ix + 1) % n, Nat.mod_lt _ hn⟩) = (ix + 1) % n at hIdx
    have hIdxY := congrArg (fun z => cycle.idxOf z) hSuccXYGet
    change cycle.idxOf
        (cycle.get ⟨(ix + 1) % n, Nat.mod_lt _ hn⟩) = cycle.idxOf y at hIdxY
    rw [hIdx] at hIdxY
    simpa [iy, n] using hIdxY.symm
  have hixEq : ix = (iy + 1) % n := by
    have hIdx := hNodup.idxOf_getElem ((iy + 1) % n) (Nat.mod_lt _ hn)
    change cycle.idxOf
        (cycle.get ⟨(iy + 1) % n, Nat.mod_lt _ hn⟩) = (iy + 1) % n at hIdx
    have hIdxX := congrArg (fun z => cycle.idxOf z) hSuccYXGet
    change cycle.idxOf
        (cycle.get ⟨(iy + 1) % n, Nat.mod_lt _ hn⟩) = cycle.idxOf x at hIdxX
    rw [hIdx] at hIdxX
    simpa [ix, n] using hIdxX.symm
  have hIdxNe : ix ≠ iy := by
    intro hEq
    have hxGet : cycle.get ⟨ix, hix⟩ = x := by
      exact List.getElem_idxOf (xs := cycle) (x := x) hix
    have hyGet : cycle.get ⟨iy, hiy⟩ = y := by
      exact List.getElem_idxOf (xs := cycle) (x := y) hiy
    have hFin : (⟨ix, hix⟩ : Fin n) = ⟨iy, hiy⟩ := by
      ext
      exact hEq
    exact hxy (hxGet.symm.trans ((congrArg (fun j : Fin n => cycle.get j) hFin).trans hyGet))
  by_cases hWrapX : ix + 1 < n
  · have hiySucc : iy = ix + 1 := by
      simpa [hiyEq] using Nat.mod_eq_of_lt hWrapX
    by_cases hWrapY : iy + 1 < n
    · have hixSucc : ix = iy + 1 := by
        simpa [hixEq] using Nat.mod_eq_of_lt hWrapY
      omega
    · have hiyEnd : iy + 1 = n := by omega
      have hixZero : ix = 0 := by
        have hMod : (iy + 1) % n = 0 := by
          rw [hiyEnd, Nat.mod_self]
        simp [hixEq, hMod]
      omega
  · have hixEnd : ix + 1 = n := by omega
    have hiyZero : iy = 0 := by
      have hMod : (ix + 1) % n = 0 := by
        rw [hixEnd, Nat.mod_self]
      simp [hiyEq, hMod]
    have hnGtOne : 1 < n := by
      by_contra hnNot
      have hnLe : n ≤ 1 := Nat.le_of_not_gt hnNot
      have hixZero : ix = 0 := by omega
      exact hIdxNe (by omega)
    have hixOne : ix = 1 := by
      have hMod : (iy + 1) % n = 1 := by
        rw [hiyZero]
        exact Nat.mod_eq_of_lt hnGtOne
      simp [hixEq, hMod]
    omega

theorem idxOf_ne_of_mem_ne
    {l : List Nat} {x y : Nat} (_hNodup : l.Nodup)
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    l.idxOf x ≠ l.idxOf y := by
  intro hIdx
  have hxLt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
  have hyLt : l.idxOf y < l.length := List.idxOf_lt_length_iff.mpr hy
  have hxGet : l.get ⟨l.idxOf x, hxLt⟩ = x := by
    exact List.getElem_idxOf (xs := l) (x := x) hxLt
  have hyGet : l.get ⟨l.idxOf y, hyLt⟩ = y := by
    exact List.getElem_idxOf (xs := l) (x := y) hyLt
  have hFin : (⟨l.idxOf x, hxLt⟩ : Fin l.length) = ⟨l.idxOf y, hyLt⟩ := by
    ext
    exact hIdx
  exact hxy (hxGet.symm.trans ((congrArg (fun j : Fin l.length => l.get j) hFin).trans hyGet))

theorem cycleSuccessor_two_cycle_no_extra
    {cycle : List Nat} {x y z : Nat} (hNodup : cycle.Nodup)
    (hx : x ∈ cycle) (hy : y ∈ cycle) (hz : z ∈ cycle)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hSuccXY : cycleSuccessor cycle x = y)
    (hSuccYX : cycleSuccessor cycle y = x) :
    False := by
  have hLen2 :=
    cycleSuccessor_two_cycle_length hNodup hx hy hxy hSuccXY hSuccYX
  have hxLt : cycle.idxOf x < cycle.length := List.idxOf_lt_length_iff.mpr hx
  have hyLt : cycle.idxOf y < cycle.length := List.idxOf_lt_length_iff.mpr hy
  have hzLt : cycle.idxOf z < cycle.length := List.idxOf_lt_length_iff.mpr hz
  have hxyIdx : cycle.idxOf x ≠ cycle.idxOf y :=
    idxOf_ne_of_mem_ne hNodup hx hy hxy
  have hxzIdx : cycle.idxOf x ≠ cycle.idxOf z :=
    idxOf_ne_of_mem_ne hNodup hx hz (fun hxz => hzx hxz.symm)
  have hyzIdx : cycle.idxOf y ≠ cycle.idxOf z :=
    idxOf_ne_of_mem_ne hNodup hy hz (fun hyz => hzy hyz.symm)
  have hLen3 : 3 ≤ cycle.length := by
    omega
  omega

theorem orderedCycle_exists_predecessor
    {g : GraphInput} {cycle : List Nat} {v : Nat}
    (hSteps : OrderedDirectedCycleSteps g cycle) (hv : v ∈ cycle) :
    ∃ u, u ∈ cycle ∧ HasDirectedEdge g u v := by
  rcases List.mem_iff_get.mp hv with ⟨i, rfl⟩
  by_cases hiZero : i.val = 0
  · have hLen : 0 < cycle.length := by
      exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    let last : Fin cycle.length := ⟨cycle.length - 1, by omega⟩
    refine ⟨cycle.get last, List.get_mem _ _, ?_⟩
    have hSucc : cyclicSuccIndex (cycle := cycle) last = i := by
      ext
      simp [cyclicSuccIndex, last, hiZero]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLen)]
      exact Nat.mod_self cycle.length
    simpa [hSucc] using hSteps last
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hiZero
    let pred : Fin cycle.length := ⟨i.val - 1, by omega⟩
    refine ⟨cycle.get pred, List.get_mem _ _, ?_⟩
    have hSucc : cyclicSuccIndex (cycle := cycle) pred = i := by
      ext
      simp [cyclicSuccIndex, pred]
      have hPredSucc : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (Nat.succ_le_of_lt hiPos)
      rw [hPredSucc]
      exact Nat.mod_eq_of_lt i.isLt
    simpa [hSucc] using hSteps pred

theorem orderedCycle_exists_predecessor_successor
    {g : GraphInput} {cycle : List Nat} {v : Nat}
    (hNodup : cycle.Nodup) (hSteps : OrderedDirectedCycleSteps g cycle) (hv : v ∈ cycle) :
    ∃ u, u ∈ cycle ∧ cycleSuccessor cycle u = v ∧ HasDirectedEdge g u v := by
  rcases List.mem_iff_get.mp hv with ⟨i, rfl⟩
  by_cases hiZero : i.val = 0
  · have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    let last : Fin cycle.length := ⟨cycle.length - 1, by omega⟩
    refine ⟨cycle.get last, List.get_mem _ _, ?_, ?_⟩
    · have hIdxOf : cycle.idxOf (cycle.get last) = last.val := by
        exact hNodup.idxOf_getElem last.val last.isLt
      have hSucc : cyclicSuccIndex (cycle := cycle) last = i := by
        ext
        simp [cyclicSuccIndex, last, hiZero]
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLen)]
        exact Nat.mod_self cycle.length
      have hGetSucc :
          cycle.get
              ⟨(cycle.idxOf (cycle.get last) + 1) % cycle.length,
                Nat.mod_lt _ hLen⟩ =
            cycle.get i := by
        rw [hIdxOf]
        exact congrArg (fun j : Fin cycle.length => cycle.get j) hSucc
      simpa [cycleSuccessor, hLen] using hGetSucc
    · have hSucc : cyclicSuccIndex (cycle := cycle) last = i := by
        ext
        simp [cyclicSuccIndex, last, hiZero]
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hLen)]
        exact Nat.mod_self cycle.length
      simpa [hSucc] using hSteps last
  · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hiZero
    let pred : Fin cycle.length := ⟨i.val - 1, by omega⟩
    refine ⟨cycle.get pred, List.get_mem _ _, ?_, ?_⟩
    · have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have hIdxOf : cycle.idxOf (cycle.get pred) = pred.val := by
        exact hNodup.idxOf_getElem pred.val pred.isLt
      have hSucc : cyclicSuccIndex (cycle := cycle) pred = i := by
        ext
        simp [cyclicSuccIndex, pred]
        have hPredSucc : i.val - 1 + 1 = i.val :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hiPos)
        rw [hPredSucc]
        exact Nat.mod_eq_of_lt i.isLt
      have hGetSucc :
          cycle.get
              ⟨(cycle.idxOf (cycle.get pred) + 1) % cycle.length,
                Nat.mod_lt _ hLen⟩ =
            cycle.get i := by
        rw [hIdxOf]
        exact congrArg (fun j : Fin cycle.length => cycle.get j) hSucc
      simpa [cycleSuccessor, hLen] using hGetSucc
    · have hSucc : cyclicSuccIndex (cycle := cycle) pred = i := by
        ext
        simp [cyclicSuccIndex, pred]
        have hPredSucc : i.val - 1 + 1 = i.val :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hiPos)
        rw [hPredSucc]
        exact Nat.mod_eq_of_lt i.isLt
      simpa [hSucc] using hSteps pred

/-- Syntax construction for the ordered DHC selector/path gadget. -/
noncomputable def textbookMap (I : VertexCoverInput) : DirectedHamiltonianCircuitInput where
  graph :=
    { vertices := textbookVertexCount I
      edges := textbookEdgeList I
      directed := true }

theorem cycleSuccessor_incidence_bit0_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    cycleSuccessor cycle (textbookIncidenceVertex I u i 0) =
        textbookIncidenceVertex I u i 1 ∨
      ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        cycleSuccessor cycle (textbookIncidenceVertex I u i 0) =
          textbookIncidenceVertex I v i 0 := by
  have hLt :
      textbookIncidenceVertex I u i 0 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 0 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  have hEdge :=
    orderedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hMem
  have hEdgeList :
      (textbookIncidenceVertex I u i 0,
          cycleSuccessor cycle (textbookIncidenceVertex I u i 0)) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact textbookEdgeList_incidence_bit0_out hInc hEdgeList

theorem cycleSuccessor_incidence_bit1_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    (∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
        cycleSuccessor cycle (textbookIncidenceVertex I u i 1) =
          textbookIncidenceVertex I v i 1) ∨
      (∃ j, (u, j) ∈ sourceIncidences I ∧
        cycleSuccessor cycle (textbookIncidenceVertex I u i 1) =
          textbookIncidenceVertex I u j 0) ∨
      ∃ slot, slot < I.k ∧
        cycleSuccessor cycle (textbookIncidenceVertex I u i 1) =
          textbookSelectorVertex (textbookNextSelector I slot) := by
  have hLt :
      textbookIncidenceVertex I u i 1 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 1 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  have hEdge :=
    orderedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hMem
  have hEdgeList :
      (textbookIncidenceVertex I u i 1,
          cycleSuccessor cycle (textbookIncidenceVertex I u i 1)) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact textbookEdgeList_incidence_bit1_out hInc hEdgeList

theorem cyclePredecessor_incidence_bit0_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    ∃ x, x ∈ cycle ∧
      ((∃ slot, slot < I.k ∧ x = textbookSelectorVertex slot) ∨
        (∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
          x = textbookIncidenceVertex I v i 0) ∨
        ∃ j, (u, j) ∈ sourceIncidences I ∧
          x = textbookIncidenceVertex I u j 1) := by
  have hLt :
      textbookIncidenceVertex I u i 0 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 0 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  rcases orderedCycle_exists_predecessor hCycle.2.2.2 hMem with ⟨x, hx, hEdge⟩
  have hEdgeList : (x, textbookIncidenceVertex I u i 0) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact ⟨x, hx, textbookEdgeList_incidence_bit0_in hInc hEdgeList⟩

theorem cyclePredecessor_incidence_bit1_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    ∃ x, x ∈ cycle ∧
      (x = textbookIncidenceVertex I u i 0 ∨
        ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
          x = textbookIncidenceVertex I v i 1) := by
  have hLt :
      textbookIncidenceVertex I u i 1 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 1 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  rcases orderedCycle_exists_predecessor hCycle.2.2.2 hMem with ⟨x, hx, hEdge⟩
  have hEdgeList : (x, textbookIncidenceVertex I u i 1) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact ⟨x, hx, textbookEdgeList_incidence_bit1_in hInc hEdgeList⟩

theorem cyclePredecessorSuccessor_incidence_bit0_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    ∃ x, x ∈ cycle ∧
      cycleSuccessor cycle x = textbookIncidenceVertex I u i 0 ∧
      ((∃ slot, slot < I.k ∧ x = textbookSelectorVertex slot) ∨
        (∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
          x = textbookIncidenceVertex I v i 0) ∨
        ∃ j, (u, j) ∈ sourceIncidences I ∧
          x = textbookIncidenceVertex I u j 1) := by
  have hLt :
      textbookIncidenceVertex I u i 0 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 0 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  rcases orderedCycle_exists_predecessor_successor hCycle.2.1 hCycle.2.2.2 hMem with
    ⟨x, hx, hSucc, hEdge⟩
  have hEdgeList : (x, textbookIncidenceVertex I u i 0) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact ⟨x, hx, hSucc, textbookEdgeList_incidence_bit0_in hInc hEdgeList⟩

theorem cyclePredecessorSuccessor_incidence_bit1_choice
    {I : VertexCoverInput} {cycle : List Nat} {u i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hInc : (u, i) ∈ sourceIncidences I) :
    ∃ x, x ∈ cycle ∧
      cycleSuccessor cycle x = textbookIncidenceVertex I u i 1 ∧
      (x = textbookIncidenceVertex I u i 0 ∨
        ∃ v, (v, i) ∈ sourceIncidences I ∧ v ≠ u ∧
          x = textbookIncidenceVertex I v i 1) := by
  have hLt :
      textbookIncidenceVertex I u i 1 < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookIncidenceVertex_lt hInc (by omega)
  have hMem :
      textbookIncidenceVertex I u i 1 ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hLt
  rcases orderedCycle_exists_predecessor_successor hCycle.2.1 hCycle.2.2.2 hMem with
    ⟨x, hx, hSucc, hEdge⟩
  have hEdgeList : (x, textbookIncidenceVertex I u i 1) ∈ textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact ⟨x, hx, hSucc, textbookEdgeList_incidence_bit1_in hInc hEdgeList⟩

theorem cross_bit0_successor_forces_bit1_return
    {I : VertexCoverInput} {cycle : List Nat} {u v i : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hu : (u, i) ∈ sourceIncidences I) (hv : (v, i) ∈ sourceIncidences I)
    (hvu : v ≠ u)
    (hSucc0 :
      cycleSuccessor cycle (textbookIncidenceVertex I v i 0) =
        textbookIncidenceVertex I u i 0) :
    cycleSuccessor cycle (textbookIncidenceVertex I u i 1) =
      textbookIncidenceVertex I v i 1 := by
  rcases cyclePredecessorSuccessor_incidence_bit1_choice hCycle hv with
    ⟨x, _hx, hSucc, hClass⟩
  rcases hClass with hxv0 | hCross
  · subst x
    have hEq :
        textbookIncidenceVertex I u i 0 = textbookIncidenceVertex I v i 1 :=
      hSucc0.symm.trans hSucc
    exact False.elim
      (textbookIncidenceVertex_ne_of_bit_ne hu hv (by omega) (by omega) (by omega) hEq)
  · rcases hCross with ⟨w, hw, hwv, hx⟩
    subst x
    have hSourceU : SourceIncidentAt I u i := (mem_sourceIncidences_iff I (u, i)).1 hu
    have hSourceV : SourceIncidentAt I v i := (mem_sourceIncidences_iff I (v, i)).1 hv
    have hSourceW : SourceIncidentAt I w i := (mem_sourceIncidences_iff I (w, i)).1 hw
    have hwu : w = u :=
      sourceIncidentAt_other_endpoint_unique hSourceU hSourceV hSourceW
        (fun huv => hvu huv.symm) hwv
    simpa [hwu] using hSucc

theorem edgeWithinBounds_of_mem_textbookIncidenceArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookIncidenceArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  rcases List.mem_map.mp he with ⟨ui, hui, rfl⟩
  exact ⟨textbookIncidenceVertex_lt hui (by omega),
    textbookIncidenceVertex_lt hui (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookCrossArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookCrossArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  simp [textbookCrossArcs] at he
  rcases he with ⟨u, i, v, hData, he⟩
  rcases hData with ⟨⟨hLeft, hRight⟩, _huv⟩
  rcases he with rfl | rfl
  · exact ⟨textbookIncidenceVertex_lt hLeft (by omega),
      textbookIncidenceVertex_lt hRight (by omega)⟩
  · exact ⟨textbookIncidenceVertex_lt hLeft (by omega),
      textbookIncidenceVertex_lt hRight (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookChainArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookChainArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rcases List.mem_map.mp he with ⟨pair, hpair, rfl⟩
  have hProd := (List.mem_filter.mp hpair).1
  rcases List.mem_product.mp hProd with ⟨hLeft, hRight⟩
  exact ⟨textbookIncidenceVertex_lt hLeft (by omega),
    textbookIncidenceVertex_lt hRight (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookTrackChainArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookTrackChainArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rcases List.mem_flatten.mp he with ⟨arcs, harcs, heArc⟩
  rcases List.mem_map.mp harcs with ⟨u, _huRange, rfl⟩
  rcases List.mem_map.mp heArc with ⟨pair, hpair, rfl⟩
  have hLeftMem : pair.1 ∈ incidencesOfVertex I u :=
    left_mem_of_mem_consecutivePairs hpair
  have hRightMem : pair.2 ∈ incidencesOfVertex I u :=
    right_mem_of_mem_consecutivePairs hpair
  have hLeft := (mem_incidencesOfVertex_iff I u pair.1).1 hLeftMem |>.1
  have hRight := (mem_incidencesOfVertex_iff I u pair.2).1 hRightMem |>.1
  exact ⟨textbookIncidenceVertex_lt hLeft (by omega),
    textbookIncidenceVertex_lt hRight (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookSelectorSkipArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookSelectorSkipArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  rcases List.mem_map.mp he with ⟨slot, hslotMem, rfl⟩
  have hslot : slot < I.k := List.mem_range.mp hslotMem
  exact ⟨textbookSelectorVertex_lt hslot,
    textbookSelectorVertex_lt (textbookNextSelector_lt hslot)⟩

theorem edgeWithinBounds_of_mem_textbookEntryArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookEntryArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rcases List.mem_map.mp he with ⟨pair, hpair, rfl⟩
  have hProd := (List.mem_filter.mp hpair).1
  rcases List.mem_product.mp hProd with ⟨hSlotMem, hInc⟩
  have hslot : pair.1 < I.k := List.mem_range.mp hSlotMem
  exact ⟨textbookSelectorVertex_lt hslot,
    textbookIncidenceVertex_lt hInc (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookExitArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookExitArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rcases List.mem_map.mp he with ⟨pair, hpair, rfl⟩
  have hProd := (List.mem_filter.mp hpair).1
  rcases List.mem_product.mp hProd with ⟨hSlotMem, hInc⟩
  have hslot : pair.1 < I.k := List.mem_range.mp hSlotMem
  exact ⟨textbookIncidenceVertex_lt hInc (by omega),
    textbookSelectorVertex_lt (textbookNextSelector_lt hslot)⟩

theorem edgeWithinBounds_of_mem_textbookTrackEntryArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookTrackEntryArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rw [textbookTrackEntryArcs] at he
  rcases List.mem_flatMap.mp he with ⟨pair, hpair, hePair⟩
  rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
  have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
  cases hHead : (incidencesOfVertex I pair.2).head? with
  | none =>
      simp [hHead] at hePair
  | some ui =>
      simp [hHead] at hePair
      subst e
      have hui : ui ∈ incidencesOfVertex I pair.2 := mem_of_head?_eq_some hHead
      have hInc := (mem_incidencesOfVertex_iff I pair.2 ui).1 hui |>.1
      exact ⟨textbookSelectorVertex_lt hslot,
        textbookIncidenceVertex_lt hInc (by omega)⟩

theorem edgeWithinBounds_of_mem_textbookTrackExitArcs
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookTrackExitArcs I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  classical
  rw [textbookTrackExitArcs] at he
  rcases List.mem_flatMap.mp he with ⟨pair, hpair, hePair⟩
  rcases List.mem_product.mp hpair with ⟨hslotMem, _huMem⟩
  have hslot : pair.1 < I.k := List.mem_range.mp hslotMem
  cases hLast : (incidencesOfVertex I pair.2).getLast? with
  | none =>
      simp [hLast] at hePair
  | some ui =>
      simp [hLast] at hePair
      subst e
      have hui : ui ∈ incidencesOfVertex I pair.2 := mem_of_getLast?_eq_some hLast
      have hInc := (mem_incidencesOfVertex_iff I pair.2 ui).1 hui |>.1
      exact ⟨textbookIncidenceVertex_lt hInc (by omega),
        textbookSelectorVertex_lt (textbookNextSelector_lt hslot)⟩

theorem edgeWithinBounds_of_mem_textbookEdgeList
    {I : VertexCoverInput} {e : Nat × Nat} (he : e ∈ textbookEdgeList I) :
    EdgeWithinBounds (textbookMap I).graph e := by
  simp [textbookEdgeList] at he
  rcases he with he | he | he | he | he | he | he | he | he
  · exact edgeWithinBounds_of_mem_textbookIncidenceArcs he
  · exact edgeWithinBounds_of_mem_textbookCrossArcs he
  · exact edgeWithinBounds_of_mem_textbookChainArcs he
  · exact edgeWithinBounds_of_mem_textbookTrackChainArcs he
  · exact edgeWithinBounds_of_mem_textbookSelectorSkipArcs he
  · exact edgeWithinBounds_of_mem_textbookEntryArcs he
  · exact edgeWithinBounds_of_mem_textbookExitArcs he
  · exact edgeWithinBounds_of_mem_textbookTrackEntryArcs he
  · exact edgeWithinBounds_of_mem_textbookTrackExitArcs he

theorem textbookMap_directed (I : VertexCoverInput) :
    (textbookMap I).graph.directed = true :=
  rfl

theorem textbookMap_wellFormed (I : VertexCoverInput) :
    WellFormed (textbookMap I).graph := by
  intro e he
  exact edgeWithinBounds_of_mem_textbookEdgeList he

theorem sourceIncidences_length_le (I : VertexCoverInput) :
    (sourceIncidences I).length ≤ I.graph.vertices * I.graph.edges.length := by
  classical
  unfold sourceIncidences
  let candidates := (List.range I.graph.vertices).product (List.range I.graph.edges.length)
  have hFilter :
      (candidates.filter fun ui : Nat × Nat =>
        decide (SourceIncidentAt I ui.1 ui.2)).length ≤ candidates.length :=
    VertexCover.filter_length_le (fun ui : Nat × Nat =>
      decide (SourceIncidentAt I ui.1 ui.2)) candidates
  have hCandidates : candidates.length = I.graph.vertices * I.graph.edges.length := by
    simpa [candidates, SProd.sprod] using
      (List.length_product (List.range I.graph.vertices) (List.range I.graph.edges.length))
  simpa [candidates] using hFilter.trans (le_of_eq hCandidates)

theorem incidencesOfVertex_length_le_edges (I : VertexCoverInput) (u : Nat) :
    (incidencesOfVertex I u).length ≤ I.graph.edges.length := by
  classical
  unfold incidencesOfVertex
  have hFilter :
      ((List.range I.graph.edges.length).filter fun i =>
        decide (SourceIncidentAt I u i)).length ≤ I.graph.edges.length := by
    have h :=
      VertexCover.filter_length_le
        (fun i : Nat => decide (SourceIncidentAt I u i)) (List.range I.graph.edges.length)
    simpa using h
  simpa using hFilter

theorem consecutivePairs_length_le {α : Type*} :
    ∀ xs : List α, xs.consecutivePairs.length ≤ xs.length
  | [] => by simp [List.consecutivePairs]
  | [_x] => by simp [List.consecutivePairs]
  | _x :: y :: ys => by
      have hTail := consecutivePairs_length_le (y :: ys)
      simp [List.consecutivePairs]

theorem flatMap_length_le_mul {α β : Type*} (xs : List α) (f : α → List β) (B : Nat)
    (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, (f y).length ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        ((x :: xs).flatMap f).length = (f x).length + (xs.flatMap f).length := by
          simp
        _ ≤ B + xs.length * B := by
          omega
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem flatten_map_length_le_mul {α β : Type*} (xs : List α) (f : α → List β) (B : Nat)
    (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.map f).flatten.length ≤ xs.length * B := by
  simpa [List.flatMap] using flatMap_length_le_mul xs f B hB

theorem textbookIncidenceArcs_length_eq (I : VertexCoverInput) :
    (textbookIncidenceArcs I).length = (sourceIncidences I).length := by
  simp [textbookIncidenceArcs]

theorem textbookCrossArcs_length_le (I : VertexCoverInput) :
    (textbookCrossArcs I).length ≤ 2 * (sourceIncidences I).length ^ 2 := by
  classical
  unfold textbookCrossArcs
  let pairs := ((sourceIncidences I).product (sourceIncidences I)).filter fun pair =>
    decide (pair.1.2 = pair.2.2 ∧ pair.1.1 ≠ pair.2.1)
  have hFlat :
      (pairs.map fun pair =>
        [ (textbookIncidenceVertex I pair.1.1 pair.1.2 0,
            textbookIncidenceVertex I pair.2.1 pair.2.2 0)
        , (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
            textbookIncidenceVertex I pair.2.1 pair.2.2 1)
        ]).flatten.length ≤ pairs.length * 2 :=
    flatten_map_length_le_mul pairs
      (fun pair =>
        [ (textbookIncidenceVertex I pair.1.1 pair.1.2 0,
            textbookIncidenceVertex I pair.2.1 pair.2.2 0)
        , (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
            textbookIncidenceVertex I pair.2.1 pair.2.2 1)
        ]) 2 (by intro pair hpair; simp)
  have hPairs :
      pairs.length ≤ (sourceIncidences I).length * (sourceIncidences I).length := by
    have hFilter :=
      VertexCover.filter_length_le
        (fun pair : (Nat × Nat) × (Nat × Nat) =>
          decide (pair.1.2 = pair.2.2 ∧ pair.1.1 ≠ pair.2.1))
        ((sourceIncidences I).product (sourceIncidences I))
    have hProduct :
        ((sourceIncidences I).product (sourceIncidences I)).length =
          (sourceIncidences I).length * (sourceIncidences I).length := by
      simpa [SProd.sprod] using
        (List.length_product (sourceIncidences I) (sourceIncidences I))
    simpa [pairs] using hFilter.trans (le_of_eq hProduct)
  calc
    (pairs.map fun pair =>
        [ (textbookIncidenceVertex I pair.1.1 pair.1.2 0,
            textbookIncidenceVertex I pair.2.1 pair.2.2 0)
        , (textbookIncidenceVertex I pair.1.1 pair.1.2 1,
            textbookIncidenceVertex I pair.2.1 pair.2.2 1)
        ]).flatten.length ≤ pairs.length * 2 := hFlat
    _ ≤ ((sourceIncidences I).length * (sourceIncidences I).length) * 2 := by
      exact Nat.mul_le_mul_right 2 hPairs
    _ ≤ 2 * (sourceIncidences I).length ^ 2 := by
      rw [pow_two, Nat.mul_comm ((sourceIncidences I).length * (sourceIncidences I).length) 2]

theorem textbookChainArcs_length_le (I : VertexCoverInput) :
    (textbookChainArcs I).length ≤ (sourceIncidences I).length ^ 2 := by
  classical
  unfold textbookChainArcs
  let pairs := ((sourceIncidences I).product (sourceIncidences I)).filter fun pair =>
    decide (pair.1.1 = pair.2.1 ∧ ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)
  have hFilter :
      pairs.length ≤ (sourceIncidences I).length * (sourceIncidences I).length := by
    have h :=
      VertexCover.filter_length_le
        (fun pair : (Nat × Nat) × (Nat × Nat) =>
          decide (pair.1.1 = pair.2.1 ∧
            ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2))
        ((sourceIncidences I).product (sourceIncidences I))
    have hProduct :
        ((sourceIncidences I).product (sourceIncidences I)).length =
          (sourceIncidences I).length * (sourceIncidences I).length := by
      simpa [SProd.sprod] using
        (List.length_product (sourceIncidences I) (sourceIncidences I))
    simpa [pairs] using h.trans (le_of_eq hProduct)
  simpa [pairs, pow_two] using hFilter

theorem textbookTrackChainArcsForVertex_length_le (I : VertexCoverInput) (u : Nat) :
    (textbookTrackChainArcsForVertex I u).length ≤ I.graph.edges.length := by
  have hConsec := consecutivePairs_length_le (incidencesOfVertex I u)
  have hInc := incidencesOfVertex_length_le_edges I u
  simpa [textbookTrackChainArcsForVertex] using hConsec.trans hInc

theorem textbookTrackChainArcs_length_le (I : VertexCoverInput) :
    (textbookTrackChainArcs I).length ≤ I.graph.vertices * I.graph.edges.length := by
  have hFlat :=
    flatten_map_length_le_mul (List.range I.graph.vertices)
      (fun u => textbookTrackChainArcsForVertex I u) I.graph.edges.length (by
        intro u _hu
        exact textbookTrackChainArcsForVertex_length_le I u)
  simpa [textbookTrackChainArcs] using hFlat

theorem textbookTrackEntryArcs_length_le (I : VertexCoverInput) :
    (textbookTrackEntryArcs I).length ≤ I.k * I.graph.vertices := by
  classical
  unfold textbookTrackEntryArcs
  let pairs := (List.range I.k).product (List.range I.graph.vertices)
  have hFlat :
      (pairs.flatMap (fun pair =>
        match (incidencesOfVertex I pair.2).head? with
        | none => []
        | some ui =>
            [(textbookSelectorVertex pair.1, textbookIncidenceVertex I ui.1 ui.2 0)])).length ≤
        pairs.length * 1 :=
    flatMap_length_le_mul pairs
      (fun pair =>
        match (incidencesOfVertex I pair.2).head? with
        | none => []
        | some ui =>
            [(textbookSelectorVertex pair.1, textbookIncidenceVertex I ui.1 ui.2 0)])
      1 (by
        intro pair hpair
        cases hHead : (incidencesOfVertex I pair.2).head? <;> simp [hHead])
  have hPairs : pairs.length = I.k * I.graph.vertices := by
    simpa [pairs, SProd.sprod] using
      (List.length_product (List.range I.k) (List.range I.graph.vertices))
  simpa [pairs, hPairs] using hFlat

theorem textbookTrackExitArcs_length_le (I : VertexCoverInput) :
    (textbookTrackExitArcs I).length ≤ I.k * I.graph.vertices := by
  classical
  unfold textbookTrackExitArcs
  let pairs := (List.range I.k).product (List.range I.graph.vertices)
  have hFlat :
      (pairs.flatMap (fun pair =>
        match (incidencesOfVertex I pair.2).getLast? with
        | none => []
        | some ui =>
            [(textbookIncidenceVertex I ui.1 ui.2 1,
              textbookSelectorVertex (textbookNextSelector I pair.1))])).length ≤
        pairs.length * 1 :=
    flatMap_length_le_mul pairs
      (fun pair =>
        match (incidencesOfVertex I pair.2).getLast? with
        | none => []
        | some ui =>
            [(textbookIncidenceVertex I ui.1 ui.2 1,
              textbookSelectorVertex (textbookNextSelector I pair.1))])
      1 (by
        intro pair hpair
        cases hLast : (incidencesOfVertex I pair.2).getLast? <;> simp [hLast])
  have hPairs : pairs.length = I.k * I.graph.vertices := by
    simpa [pairs, SProd.sprod] using
      (List.length_product (List.range I.k) (List.range I.graph.vertices))
  simpa [pairs, hPairs] using hFlat

theorem textbookEntryArcs_length_le (I : VertexCoverInput) :
    (textbookEntryArcs I).length ≤ I.k * (sourceIncidences I).length := by
  classical
  unfold textbookEntryArcs
  let pairs := ((List.range I.k).product (sourceIncidences I)).filter fun pair =>
    decide (FirstIncident I pair.2.1 pair.2.2)
  have hFilter :
      pairs.length ≤ I.k * (sourceIncidences I).length := by
    have h :=
      VertexCover.filter_length_le
        (fun pair : Nat × (Nat × Nat) => decide (FirstIncident I pair.2.1 pair.2.2))
        ((List.range I.k).product (sourceIncidences I))
    have hProduct :
        ((List.range I.k).product (sourceIncidences I)).length =
          I.k * (sourceIncidences I).length := by
      simpa [SProd.sprod] using (List.length_product (List.range I.k) (sourceIncidences I))
    simpa [pairs] using h.trans (le_of_eq hProduct)
  simpa [pairs] using hFilter

theorem textbookExitArcs_length_le (I : VertexCoverInput) :
    (textbookExitArcs I).length ≤ I.k * (sourceIncidences I).length := by
  classical
  unfold textbookExitArcs
  let pairs := ((List.range I.k).product (sourceIncidences I)).filter fun pair =>
    decide (LastIncident I pair.2.1 pair.2.2)
  have hFilter :
      pairs.length ≤ I.k * (sourceIncidences I).length := by
    have h :=
      VertexCover.filter_length_le
        (fun pair : Nat × (Nat × Nat) => decide (LastIncident I pair.2.1 pair.2.2))
        ((List.range I.k).product (sourceIncidences I))
    have hProduct :
        ((List.range I.k).product (sourceIncidences I)).length =
          I.k * (sourceIncidences I).length := by
      simpa [SProd.sprod] using (List.length_product (List.range I.k) (sourceIncidences I))
    simpa [pairs] using h.trans (le_of_eq hProduct)
  simpa [pairs] using hFilter

theorem textbookEdgeList_length_le (I : VertexCoverInput) :
    (textbookEdgeList I).length ≤
      (sourceIncidences I).length +
        2 * (sourceIncidences I).length ^ 2 +
        (sourceIncidences I).length ^ 2 +
        I.graph.vertices * I.graph.edges.length +
        I.k +
        I.k * (sourceIncidences I).length +
        I.k * (sourceIncidences I).length +
        I.k * I.graph.vertices +
        I.k * I.graph.vertices := by
  have hInc := textbookIncidenceArcs_length_eq I
  have hCross := textbookCrossArcs_length_le I
  have hChain := textbookChainArcs_length_le I
  have hTrackChain := textbookTrackChainArcs_length_le I
  have hEntry := textbookEntryArcs_length_le I
  have hExit := textbookExitArcs_length_le I
  have hTrackEntry := textbookTrackEntryArcs_length_le I
  have hTrackExit := textbookTrackExitArcs_length_le I
  simp [textbookEdgeList, textbookSelectorSkipArcs, hInc]
  omega

theorem selector_cycleSuccessor_choice
    {I : VertexCoverInput} {cycle : List Nat} {slot : Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hslot : slot < I.k) :
    cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookSelectorVertex (textbookNextSelector I slot) ∨
      ∃ u i, (u, i) ∈ sourceIncidences I ∧
        cycleSuccessor cycle (textbookSelectorVertex slot) =
          textbookIncidenceVertex I u i 0 := by
  have hSelectorLt :
      textbookSelectorVertex slot < (textbookMap I).graph.vertices := by
    simpa [textbookMap] using textbookSelectorVertex_lt hslot
  have hSelectorMem :
      textbookSelectorVertex slot ∈ cycle :=
    OrderedDirectedHamiltonianCycle.mem_of_lt hCycle hSelectorLt
  have hEdge :=
    orderedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hSelectorMem
  have hEdgeList :
      (textbookSelectorVertex slot, cycleSuccessor cycle (textbookSelectorVertex slot)) ∈
        textbookEdgeList I := by
    simpa [HasDirectedEdge, textbookMap] using hEdge
  exact textbookEdgeList_selector_out hslot hEdgeList

theorem filterMap_length_le {α β : Type*} (f : α → Option β) :
    ∀ l : List α, (l.filterMap f).length ≤ l.length
  | [] => by simp
  | a :: l => by
      cases h : f a with
      | none =>
          have ih := filterMap_length_le f l
          simp [h]
          omega
      | some b =>
          have ih := filterMap_length_le f l
          simp [h]
          omega

theorem selector_entry_exists_of_not_skip
    {I : VertexCoverInput} {cycle : List Nat}
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    {slot : Nat} (hslot : slot < I.k)
    (hNotSkip :
      cycleSuccessor cycle (textbookSelectorVertex slot) ≠
        textbookSelectorVertex (textbookNextSelector I slot)) :
    ∃ u i, (u, i) ∈ sourceIncidences I ∧
      cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookIncidenceVertex I u i 0 := by
  rcases selector_cycleSuccessor_choice hCycle hslot with hSkip | hEntry
  · exact False.elim (hNotSkip hSkip)
  · exact hEntry

noncomputable def decodedSlotChoice
    (I : VertexCoverInput) (cycle : List Nat)
    (hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle)
    (slot : Nat) : Option Nat :=
  if hslot : slot < I.k then
    if hSkip :
        cycleSuccessor cycle (textbookSelectorVertex slot) =
          textbookSelectorVertex (textbookNextSelector I slot) then
      none
    else
      some (Classical.choose (selector_entry_exists_of_not_skip hCycle hslot hSkip))
  else
    none

theorem decodedSlotChoice_eq_some
    {I : VertexCoverInput} {cycle : List Nat}
    {hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle}
    {slot u : Nat}
    (h : decodedSlotChoice I cycle hCycle slot = some u) :
    slot < I.k ∧ ∃ i, (u, i) ∈ sourceIncidences I ∧
      cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookIncidenceVertex I u i 0 := by
  classical
  unfold decodedSlotChoice at h
  by_cases hslot : slot < I.k
  · simp [hslot] at h
    by_cases hSkip :
        cycleSuccessor cycle (textbookSelectorVertex slot) =
          textbookSelectorVertex (textbookNextSelector I slot)
    · simp [hSkip] at h
    · simp [hSkip] at h
      let hEntry :
          ∃ u i, (u, i) ∈ sourceIncidences I ∧
            cycleSuccessor cycle (textbookSelectorVertex slot) =
              textbookIncidenceVertex I u i 0 :=
        selector_entry_exists_of_not_skip hCycle hslot hSkip
      have hu : Classical.choose hEntry = u := by
        exact h
      rcases Classical.choose_spec hEntry with ⟨i, hInc, hSucc⟩
      subst u
      exact ⟨hslot, i, hInc, hSucc⟩
  · simp [hslot] at h

theorem decodedSlotChoice_eq_some_of_successor_incidence
    {I : VertexCoverInput} {cycle : List Nat}
    {hCycle : OrderedDirectedHamiltonianCycle (textbookMap I).graph cycle}
    {slot u i : Nat} (hslot : slot < I.k) (hInc : (u, i) ∈ sourceIncidences I)
    (hSucc :
      cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookIncidenceVertex I u i 0) :
    decodedSlotChoice I cycle hCycle slot = some u := by
  classical
  unfold decodedSlotChoice
  simp [hslot]
  by_cases hSkip :
      cycleSuccessor cycle (textbookSelectorVertex slot) =
        textbookSelectorVertex (textbookNextSelector I slot)
  · have hNextEq :
        textbookSelectorVertex (textbookNextSelector I slot) =
          textbookIncidenceVertex I u i 0 :=
      hSkip.symm.trans hSucc
    exact False.elim
      (textbookSelectorVertex_ne_textbookIncidenceVertex (textbookNextSelector_lt hslot) hNextEq)
  · simp [hSkip]
    let hEntry := selector_entry_exists_of_not_skip hCycle hslot hSkip
    rcases Classical.choose_spec hEntry with ⟨j, hInc', hSucc'⟩
    have hVertexEq :
        textbookIncidenceVertex I (Classical.choose hEntry) j 0 =
          textbookIncidenceVertex I u i 0 :=
      hSucc'.symm.trans hSucc
    have hPairEq := (textbookIncidenceVertex_inj hInc' hInc (by omega) (by omega) hVertexEq).1
    have hu : Classical.choose hEntry = u := (Prod.ext_iff.mp hPairEq).1
    exact hu

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
