import ComplexityReduction.Legacy.ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.Part1

namespace ComplexityReduction
namespace Karp21
namespace UndirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

theorem cycleSuccessor_injective_on_cycle
    {cycle : List Nat} {x y : Nat} (hNodup : cycle.Nodup)
    (hx : x ∈ cycle) (hy : y ∈ cycle)
    (hSucc :
      DirectedHamiltonianCircuit.cycleSuccessor cycle x =
        DirectedHamiltonianCircuit.cycleSuccessor cycle y) :
    x = y := by
  classical
  let n := cycle.length
  let ix := cycle.idxOf x
  let iy := cycle.idxOf y
  have hix : ix < n := by
    simpa [ix, n] using List.idxOf_lt_length_iff.mpr hx
  have hiy : iy < n := by
    simpa [iy, n] using List.idxOf_lt_length_iff.mpr hy
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le ix) hix
  have hGetEq :
      cycle.get ⟨(ix + 1) % n, Nat.mod_lt _ hn⟩ =
        cycle.get ⟨(iy + 1) % n, Nat.mod_lt _ hn⟩ := by
    simpa [DirectedHamiltonianCircuit.cycleSuccessor, ix, iy, n, hn] using hSucc
  have hFinEq :
      (⟨(ix + 1) % n, Nat.mod_lt _ hn⟩ : Fin cycle.length) =
        ⟨(iy + 1) % n, Nat.mod_lt _ hn⟩ := by
    exact hNodup.injective_get hGetEq
  have hModEq : (ix + 1) % n = (iy + 1) % n := by
    exact congrArg Fin.val hFinEq
  have hIdxEq : ix = iy := by
    by_cases hixWrap : ix + 1 < n
    · have hixMod : (ix + 1) % n = ix + 1 := Nat.mod_eq_of_lt hixWrap
      by_cases hiyWrap : iy + 1 < n
      · have hiyMod : (iy + 1) % n = iy + 1 := Nat.mod_eq_of_lt hiyWrap
        omega
      · have hiyEnd : iy + 1 = n := by omega
        have hiyMod : (iy + 1) % n = 0 := by
          rw [hiyEnd, Nat.mod_self]
        omega
    · have hixEnd : ix + 1 = n := by omega
      have hixMod : (ix + 1) % n = 0 := by
        rw [hixEnd, Nat.mod_self]
      by_cases hiyWrap : iy + 1 < n
      · have hiyMod : (iy + 1) % n = iy + 1 := Nat.mod_eq_of_lt hiyWrap
        omega
      · omega
  have hxGet : cycle.get ⟨ix, hix⟩ = x := by
    exact List.getElem_idxOf (xs := cycle) (x := x) hix
  have hyGet : cycle.get ⟨iy, hiy⟩ = y := by
    exact List.getElem_idxOf (xs := cycle) (x := y) hiy
  have hFin : (⟨ix, hix⟩ : Fin cycle.length) = ⟨iy, hiy⟩ := by
    ext
    exact hIdxEq
  exact hxGet.symm.trans ((congrArg (fun j : Fin cycle.length => cycle.get j) hFin).trans hyGet)

theorem cycleSuccessor_get {cycle : List Nat} (hNodup : cycle.Nodup)
    (i : Fin cycle.length) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (cycle.get i) =
      cycle.get (cyclicSuccIndex i) := by
  have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hIdx : cycle.idxOf (cycle.get i) = i.val := by
    exact hNodup.idxOf_getElem i.val i.isLt
  unfold DirectedHamiltonianCircuit.cycleSuccessor
  simp [hLen]
  apply congrArg (fun j : Fin cycle.length => cycle.get j)
  ext
  simp [cyclicSuccIndex]
  have hIdx2 : List.idxOf cycle[i.val] cycle = i.val := by
    simpa using hIdx
  rw [hIdx2]

theorem cycleSuccessor_iterate_get {cycle : List Nat} (hNodup : cycle.Nodup)
    (i : Fin cycle.length) :
    ∀ k : Nat, ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[k]) (cycle.get i) =
      cycle.get
        ⟨(i.val + k) % cycle.length,
          Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ := by
  intro k
  induction k with
  | zero =>
      simp
      apply congrArg (fun j : Fin cycle.length => cycle.get j)
      ext
      exact (Nat.mod_eq_of_lt i.isLt).symm
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [cycleSuccessor_get hNodup]
      apply congrArg (fun j : Fin cycle.length => cycle.get j)
      ext
      simp [cyclicSuccIndex]
      rw [Nat.add_assoc]

theorem exists_cycleSuccessor_iterate_eq_of_mem
    {cycle : List Nat} (hNodup : cycle.Nodup) {a x : Nat}
    (ha : a ∈ cycle) (hx : x ∈ cycle) :
    ∃ k, ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[k]) a = x := by
  classical
  let n := cycle.length
  let ia := cycle.idxOf a
  let ix := cycle.idxOf x
  have hia : ia < n := by
    simpa [ia, n] using List.idxOf_lt_length_iff.mpr ha
  have hix : ix < n := by
    simpa [ix, n] using List.idxOf_lt_length_iff.mpr hx
  have haGet : cycle.get ⟨ia, hia⟩ = a := by
    exact List.getElem_idxOf (xs := cycle) (x := a) hia
  have hxGet : cycle.get ⟨ix, hix⟩ = x := by
    exact List.getElem_idxOf (xs := cycle) (x := x) hix
  by_cases hle : ia ≤ ix
  · let k := ix - ia
    refine ⟨k, ?_⟩
    have hIter := cycleSuccessor_iterate_get hNodup ⟨ia, hia⟩ k
    rw [haGet] at hIter
    have hIdx : (ia + k) % cycle.length = ix := by
      have hsum : ia + k = ix := by omega
      rw [hsum]
      exact Nat.mod_eq_of_lt (by simpa [n] using hix)
    rw [hIter]
    have hFin :
        (⟨(ia + k) % cycle.length,
          Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le ia) hia)⟩ : Fin cycle.length) =
          ⟨ix, by simpa [n] using hix⟩ := by
      ext
      exact hIdx
    exact (congrArg (fun j : Fin cycle.length => cycle.get j) hFin).trans hxGet
  · let k := n - ia + ix
    refine ⟨k, ?_⟩
    have hIter := cycleSuccessor_iterate_get hNodup ⟨ia, hia⟩ k
    rw [haGet] at hIter
    have hIdx : (ia + k) % cycle.length = ix := by
      have hsum : ia + k = n + ix := by omega
      rw [hsum, Nat.add_mod, Nat.mod_self]
      simp [n, Nat.mod_eq_of_lt hix]
    rw [hIter]
    have hFin :
        (⟨(ia + k) % cycle.length,
          Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le ia) hia)⟩ : Fin cycle.length) =
          ⟨ix, by simpa [n] using hix⟩ := by
      ext
      exact hIdx
    exact (congrArg (fun j : Fin cycle.length => cycle.get j) hFin).trans hxGet

theorem cycleSuccessor_mem {cycle : List Nat} {x : Nat} (hx : x ∈ cycle) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle x ∈ cycle := by
  classical
  have hIdx : cycle.idxOf x < cycle.length := List.idxOf_lt_length_iff.mpr hx
  have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le _) hIdx
  simp [DirectedHamiltonianCircuit.cycleSuccessor, hLen]

def InForwardBlock (I : DirectedHamiltonianCircuitInput) (cycle : List Nat) (x : Nat) :
    Prop :=
  ∃ v, v < I.graph.vertices ∧ x ∈ replacementBlock v ∧ BlockForward cycle v

def InReverseBlock (I : DirectedHamiltonianCircuitInput) (cycle : List Nat) (x : Nat) :
    Prop :=
  ∃ v, v < I.graph.vertices ∧ x ∈ replacementBlock v ∧ BlockReverse cycle v

theorem inVertex_mem_replacementBlock_eq {u v : Nat}
    (hMem : inVertex u ∈ replacementBlock v) :
    u = v := by
  simp [replacementBlock, inVertex, midVertex, outVertex] at hMem
  rcases hMem with h | h | h <;> omega

theorem outVertex_mem_replacementBlock_eq {u v : Nat}
    (hMem : outVertex u ∈ replacementBlock v) :
    u = v := by
  simp [replacementBlock, inVertex, midVertex, outVertex] at hMem
  rcases hMem with h | h | h <;> omega

theorem forwardBlock_cross_successor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u : Nat} (hu : u < I.graph.vertices) (hForward : BlockForward cycle u) :
    ∃ v, HasDirectedEdge I.graph u v ∧
      DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex u) = inVertex v := by
  have hOutMem := outVertex_mem_of_orderedUHC hCycle hu
  have hEdge :=
    orderedUndirectedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hOutMem
  rcases textbook_out_neighbor_choice hEdge with hMid | hCross
  · have hInMem := inVertex_mem_of_orderedUHC hCycle hu
    have hInOut : inVertex u = outVertex u :=
      cycleSuccessor_injective_on_cycle hCycle.2.1 hInMem hOutMem (by
        rw [hForward.1, hMid])
    unfold inVertex outVertex at hInOut
    omega
  · rcases hCross with ⟨v, hEdgeSource, hSucc⟩
    exact ⟨v, hEdgeSource, hSucc⟩

theorem forwardBlock_cross_successor_bounded
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u : Nat} (hu : u < I.graph.vertices) (hForward : BlockForward cycle u) :
    ∃ v, v < I.graph.vertices ∧ HasDirectedEdge I.graph u v ∧
      DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex u) = inVertex v := by
  rcases forwardBlock_cross_successor hCycle hu hForward with ⟨v, hEdge, hSucc⟩
  have hOutMem := outVertex_mem_of_orderedUHC hCycle hu
  have hSuccMem :
      DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex u) ∈ cycle := by
    classical
    have hIdx : cycle.idxOf (outVertex u) < cycle.length :=
      List.idxOf_lt_length_iff.mpr hOutMem
    have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le _) hIdx
    simp [DirectedHamiltonianCircuit.cycleSuccessor, hLen]
  have hBound := hCycle.2.2.1 (inVertex v) (by simpa [hSucc] using hSuccMem)
  have hv : v < I.graph.vertices := by
    simp [textbookMap, textbookVertexCount, inVertex] at hBound
    omega
  exact ⟨v, hv, hEdge, hSucc⟩

theorem reverseBlock_cross_successor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) (hReverse : BlockReverse cycle v) :
    ∃ u, HasDirectedEdge I.graph u v ∧
      DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = outVertex u := by
  have hInMem := inVertex_mem_of_orderedUHC hCycle hv
  have hEdge :=
    orderedUndirectedCycle_edge_to_cycleSuccessor hCycle.2.2.2 hInMem
  rcases textbook_in_neighbor_choice hEdge with hMid | hCross
  · have hOutMem := outVertex_mem_of_orderedUHC hCycle hv
    have hOutIn : outVertex v = inVertex v :=
      cycleSuccessor_injective_on_cycle hCycle.2.1 hOutMem hInMem (by
        rw [hReverse.1, hMid])
    unfold inVertex outVertex at hOutIn
    omega
  · rcases hCross with ⟨u, hEdgeSource, hSucc⟩
    exact ⟨u, hEdgeSource, hSucc⟩

theorem reverseBlock_cross_successor_bounded
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {v : Nat} (hv : v < I.graph.vertices) (hReverse : BlockReverse cycle v) :
    ∃ u, u < I.graph.vertices ∧ HasDirectedEdge I.graph u v ∧
      DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = outVertex u := by
  rcases reverseBlock_cross_successor hCycle hv hReverse with ⟨u, hEdge, hSucc⟩
  have hInMem := inVertex_mem_of_orderedUHC hCycle hv
  have hSuccMem :
      DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) ∈ cycle := by
    classical
    have hIdx : cycle.idxOf (inVertex v) < cycle.length :=
      List.idxOf_lt_length_iff.mpr hInMem
    have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le _) hIdx
    simp [DirectedHamiltonianCircuit.cycleSuccessor, hLen]
  have hBound := hCycle.2.2.1 (outVertex u) (by simpa [hSucc] using hSuccMem)
  have hu : u < I.graph.vertices := by
    simp [textbookMap, textbookVertexCount, outVertex] at hBound
    omega
  exact ⟨u, hu, hEdge, hSucc⟩

theorem forwardBlock_cross_forces_forward
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u v : Nat} (hu : u < I.graph.vertices) (hv : v < I.graph.vertices)
    (_hForward : BlockForward cycle u)
    (hCross :
      DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex u) = inVertex v) :
    BlockForward cycle v := by
  rcases replacementBlock_forced_orientation' hCycle hv with hVForward | hVReverse
  · exact hVForward
  · have hOutMem := outVertex_mem_of_orderedUHC hCycle hu
    have hMidMem := midVertex_mem_of_orderedUHC hCycle hv
    have hEq : outVertex u = midVertex v :=
      cycleSuccessor_injective_on_cycle hCycle.2.1 hOutMem hMidMem (by
        rw [hCross, hVReverse.2])
    unfold outVertex midVertex at hEq
    omega

theorem reverseBlock_cross_forces_reverse
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u v : Nat} (hu : u < I.graph.vertices) (hv : v < I.graph.vertices)
    (_hReverse : BlockReverse cycle v)
    (hCross :
      DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = outVertex u) :
    BlockReverse cycle u := by
  rcases replacementBlock_forced_orientation' hCycle hu with hUForward | hUReverse
  · have hInMem := inVertex_mem_of_orderedUHC hCycle hv
    have hMidMem := midVertex_mem_of_orderedUHC hCycle hu
    have hEq : inVertex v = midVertex u :=
      cycleSuccessor_injective_on_cycle hCycle.2.1 hInMem hMidMem (by
        rw [hCross, hUForward.2])
    unfold inVertex midVertex at hEq
    omega
  · exact hUReverse

theorem inForwardBlock_successor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {x : Nat} (hForward : InForwardBlock I cycle x) :
    InForwardBlock I cycle (DirectedHamiltonianCircuit.cycleSuccessor cycle x) := by
  rcases hForward with ⟨v, hv, hxBlock, hVForward⟩
  simp [replacementBlock] at hxBlock
  rcases hxBlock with rfl | rfl | rfl
  · exact ⟨v, hv, by rw [hVForward.1]; simp [replacementBlock], hVForward⟩
  · exact ⟨v, hv, by rw [hVForward.2]; simp [replacementBlock], hVForward⟩
  · rcases forwardBlock_cross_successor_bounded hCycle hv hVForward with
      ⟨w, hw, _hEdge, hSucc⟩
    have hWForward := forwardBlock_cross_forces_forward hCycle hv hw hVForward hSucc
    exact ⟨w, hw, by rw [hSucc]; simp [replacementBlock], hWForward⟩

theorem inReverseBlock_successor
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {x : Nat} (hReverse : InReverseBlock I cycle x) :
    InReverseBlock I cycle (DirectedHamiltonianCircuit.cycleSuccessor cycle x) := by
  rcases hReverse with ⟨v, hv, hxBlock, hVReverse⟩
  simp [replacementBlock] at hxBlock
  rcases hxBlock with rfl | rfl | rfl
  · rcases reverseBlock_cross_successor_bounded hCycle hv hVReverse with
      ⟨u, hu, _hEdge, hSucc⟩
    have hUReverse := reverseBlock_cross_forces_reverse hCycle hu hv hVReverse hSucc
    exact ⟨u, hu, by rw [hSucc]; simp [replacementBlock], hUReverse⟩
  · exact ⟨v, hv, by rw [hVReverse.2]; simp [replacementBlock], hVReverse⟩
  · exact ⟨v, hv, by rw [hVReverse.1]; simp [replacementBlock], hVReverse⟩

theorem inForwardBlock_iterate
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {x : Nat} (hForward : InForwardBlock I cycle x) :
    ∀ k : Nat, InForwardBlock I cycle
      (((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[k]) x)
  | 0 => by simpa using hForward
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact inForwardBlock_successor hCycle (inForwardBlock_iterate hCycle hForward k)

theorem inReverseBlock_iterate
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {x : Nat} (hReverse : InReverseBlock I cycle x) :
    ∀ k : Nat, InReverseBlock I cycle
      (((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[k]) x)
  | 0 => by simpa using hReverse
  | k + 1 => by
      rw [Function.iterate_succ_apply']
      exact inReverseBlock_successor hCycle (inReverseBlock_iterate hCycle hReverse k)

theorem allBlocksForward_of_blockForward
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {start : Nat} (hstart : start < I.graph.vertices) (hStartForward : BlockForward cycle start) :
    ∀ v, v < I.graph.vertices → BlockForward cycle v := by
  intro v hv
  have hStartMem := inVertex_mem_of_orderedUHC hCycle hstart
  have hTargetMem := inVertex_mem_of_orderedUHC hCycle hv
  rcases exists_cycleSuccessor_iterate_eq_of_mem hCycle.2.1 hStartMem hTargetMem with
    ⟨k, hReach⟩
  have hIterForward :=
    inForwardBlock_iterate hCycle
      (x := inVertex start)
      ⟨start, hstart, by simp [replacementBlock], hStartForward⟩ k
  rw [hReach] at hIterForward
  rcases hIterForward with ⟨w, _hw, hInBlock, hWForward⟩
  have hvw : v = w := inVertex_mem_replacementBlock_eq hInBlock
  simpa [hvw] using hWForward

theorem allBlocksReverse_of_blockReverse
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {start : Nat} (hstart : start < I.graph.vertices) (hStartReverse : BlockReverse cycle start) :
    ∀ v, v < I.graph.vertices → BlockReverse cycle v := by
  intro v hv
  have hStartMem := outVertex_mem_of_orderedUHC hCycle hstart
  have hTargetMem := outVertex_mem_of_orderedUHC hCycle hv
  rcases exists_cycleSuccessor_iterate_eq_of_mem hCycle.2.1 hStartMem hTargetMem with
    ⟨k, hReach⟩
  have hIterReverse :=
    inReverseBlock_iterate hCycle
      (x := outVertex start)
      ⟨start, hstart, by simp [replacementBlock], hStartReverse⟩ k
  rw [hReach] at hIterReverse
  rcases hIterReverse with ⟨w, _hw, hOutBlock, hWReverse⟩
  have hvw : v = w := outVertex_mem_replacementBlock_eq hOutBlock
  simpa [hvw] using hWReverse

noncomputable def forwardSourceSucc
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) : Fin I.graph.vertices := by
  classical
  let ex := forwardBlock_cross_successor_bounded hCycle u.isLt
    (hForwardAll u.val u.isLt)
  exact ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩

theorem forwardSourceSucc_edge
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) :
    HasDirectedEdge I.graph u.val (forwardSourceSucc I hCycle hForwardAll u).val := by
  classical
  unfold forwardSourceSucc
  exact (Classical.choose_spec
    (forwardBlock_cross_successor_bounded hCycle u.isLt
      (hForwardAll u.val u.isLt))).2.1

theorem forwardSourceSucc_cross
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (outVertex u.val) =
      inVertex (forwardSourceSucc I hCycle hForwardAll u).val := by
  classical
  unfold forwardSourceSucc
  exact (Classical.choose_spec
    (forwardBlock_cross_successor_bounded hCycle u.isLt
      (hForwardAll u.val u.isLt))).2.2

theorem forwardSourceSucc_three_steps
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) :
    ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3]) (inVertex u.val) =
      inVertex (forwardSourceSucc I hCycle hForwardAll u).val := by
  have hForward := hForwardAll u.val u.isLt
  rw [show (3 : Nat) = Nat.succ (Nat.succ (Nat.succ 0)) by rfl]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [hForward.1, hForward.2, forwardSourceSucc_cross hCycle hForwardAll u]

theorem forwardSourceSucc_iterate_three_steps
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) :
    ∀ k : Nat,
      ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * k]) (inVertex u.val) =
        inVertex (((forwardSourceSucc I hCycle hForwardAll)^[k]) u).val
  | 0 => by simp
  | k + 1 => by
      have hArith : 3 * (k + 1) = 3 + 3 * k := by omega
      rw [hArith, Function.iterate_add_apply]
      rw [forwardSourceSucc_iterate_three_steps hCycle hForwardAll u k]
      simpa [Function.iterate_succ_apply'] using
        forwardSourceSucc_three_steps hCycle hForwardAll
          (((forwardSourceSucc I hCycle hForwardAll)^[k]) u)

theorem cycleSuccessor_iterate_length_eq_self {cycle : List Nat}
    (hNodup : cycle.Nodup) {x : Nat} (hx : x ∈ cycle) :
    ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[cycle.length]) x = x := by
  rcases List.mem_iff_get.mp hx with ⟨i, rfl⟩
  have hIter := cycleSuccessor_iterate_get hNodup i cycle.length
  rw [hIter]
  apply congrArg (fun j : Fin cycle.length => cycle.get j)
  ext
  have hLen : 0 < cycle.length := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  change (i.val + cycle.length) % cycle.length = i.val
  rw [Nat.add_mod, Nat.mod_self]
  simp [Nat.mod_eq_of_lt i.isLt]

theorem cycleSuccessor_iterate_ne_self_of_pos_lt {cycle : List Nat}
    (hNodup : cycle.Nodup) {x k : Nat} (hx : x ∈ cycle)
    (hkpos : 0 < k) (hklt : k < cycle.length) :
    ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[k]) x ≠ x := by
  intro hReturn
  let p := cycle.idxOf x
  have hp : p < cycle.length := by
    simpa [p] using List.idxOf_lt_length_iff.mpr hx
  have hLenPos : 0 < cycle.length := lt_trans hkpos hklt
  have hxGet : cycle.get ⟨p, hp⟩ = x := by
    exact List.getElem_idxOf (xs := cycle) (x := x) hp
  have hIter := cycleSuccessor_iterate_get hNodup ⟨p, hp⟩ k
  rw [hxGet] at hIter
  have hGetEq :
      cycle.get
          ⟨(p + k) % cycle.length,
            Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le p) hp)⟩ =
        cycle.get ⟨p, hp⟩ := by
    rw [← hIter, hReturn, hxGet]
  have hFinEq :
      (⟨(p + k) % cycle.length,
            Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le p) hp)⟩ : Fin cycle.length) =
        ⟨p, hp⟩ := by
    exact hNodup.injective_get hGetEq
  have hMod : (p + k) % cycle.length = p := congrArg Fin.val hFinEq
  have hModEq : p + k ≡ p [MOD cycle.length] := by
    unfold Nat.ModEq
    rw [hMod, Nat.mod_eq_of_lt hp]
  have hdvd : cycle.length ∣ k := by
    exact (Nat.add_modEq_left_iff (a := p) (b := k) (n := cycle.length)).mp hModEq
  rcases hdvd with ⟨m, hm⟩
  cases m with
  | zero =>
      omega
  | succ m =>
      have hleMul : cycle.length ≤ cycle.length * Nat.succ m :=
        Nat.le_mul_of_pos_right cycle.length (Nat.succ_pos m)
      have hleK : cycle.length ≤ k := by
        rw [hm]
        exact hleMul
      exact (not_lt_of_ge hleK) hklt

theorem forwardSourceSucc_iterate_vertices_eq_self
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (u : Fin I.graph.vertices) :
    ((forwardSourceSucc I hCycle hForwardAll)^[I.graph.vertices]) u = u := by
  have hInMem := inVertex_mem_of_orderedUHC hCycle u.isLt
  have hTarget :=
    cycleSuccessor_iterate_length_eq_self hCycle.2.1 hInMem
  have hLen : cycle.length = 3 * I.graph.vertices := by
    simpa [textbookMap, textbookVertexCount] using hCycle.1
  have hIter :=
    forwardSourceSucc_iterate_three_steps hCycle hForwardAll u I.graph.vertices
  rw [hLen] at hTarget
  rw [hIter] at hTarget
  have hVal : (((forwardSourceSucc I hCycle hForwardAll)^[I.graph.vertices]) u).val = u.val := by
    unfold inVertex at hTarget
    omega
  exact Fin.ext hVal

noncomputable def forwardProjectedCycleOfPos
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) : List Nat :=
  List.ofFn fun i : Fin I.graph.vertices =>
    (((forwardSourceSucc I hCycle hForwardAll)^[i.val]) ⟨0, hpos⟩).val

theorem forwardProjectedCycleOfPos_length
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).length = I.graph.vertices := by
  simp [forwardProjectedCycleOfPos]

theorem forwardProjectedCycleOfPos_withinBounds
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    VerticesWithinBounds I.graph (forwardProjectedCycleOfPos I hCycle hForwardAll hpos) := by
  intro v hv
  simp [forwardProjectedCycleOfPos] at hv
  rcases hv with ⟨i, rfl⟩
  exact (((forwardSourceSucc I hCycle hForwardAll)^[i.val]) ⟨0, hpos⟩).isLt

theorem head?_ofFn_pos {α : Type*} {n : Nat} (f : Fin n → α) (hpos : 0 < n) :
    (List.ofFn f).head? = some (f ⟨0, hpos⟩) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      simp [List.ofFn_succ]

theorem getLast?_ofFn_pos {α : Type*} {n : Nat} (f : Fin n → α) (hpos : 0 < n) :
    (List.ofFn f).getLast? = some (f ⟨n - 1, by omega⟩) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      have hne : List.ofFn f ≠ [] := by
        simp
      have hGetLast : (List.ofFn f).getLast hne = f (Fin.last n) := by
        simpa using List.getLast_ofFn_succ (f := f)
      have hLast : (⟨Nat.succ n - 1, by omega⟩ : Fin (Nat.succ n)) = Fin.last n := by
        ext
        simp
      rw [List.getLast?_eq_getLast_of_ne_nil hne, hGetLast, hLast]

theorem iterate_pos_eq_apply_pred {α : Type*} (f : α → α) {n : Nat} (hpos : 0 < n)
    (x : α) :
    (f^[n]) x = f ((f^[n - 1]) x) := by
  have hComp := Function.comp_iterate_pred_of_pos (f := f) hpos
  simpa [Function.comp_apply, Nat.pred_eq_sub_one] using (congrFun hComp x).symm

theorem iterate_sub_apply {α : Type*} (f : α → α) {i j : Nat} (hij : i ≤ j)
    (x : α) :
    (f^[j - i]) ((f^[i]) x) = (f^[j]) x := by
  rw [← Function.iterate_add_apply]
  have hsum : j - i + i = j := by omega
  rw [hsum]

theorem forwardProjectedCycleOfPos_edgeChain
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).IsChain
      fun u v => HasDirectedEdge I.graph u v := by
  unfold forwardProjectedCycleOfPos
  rw [List.isChain_ofFn]
  intro i hi
  let f := forwardSourceSucc I hCycle hForwardAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  have hEdge := forwardSourceSucc_edge hCycle hForwardAll ((f^[i]) start)
  simpa [forwardProjectedCycleOfPos, f, start, Function.iterate_succ_apply'] using hEdge

theorem forwardProjectedCycleOfPos_cyclicClosingEdge
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    ∀ x ∈ (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).getLast?,
      ∀ y ∈ (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).head?,
        HasDirectedEdge I.graph x y := by
  intro x hx y hy
  let f := forwardSourceSucc I hCycle hForwardAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  have hHead : (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).head? = some start.val := by
    simpa [forwardProjectedCycleOfPos, start] using
      head?_ofFn_pos
        (fun i : Fin I.graph.vertices => (((forwardSourceSucc I hCycle hForwardAll)^[i.val])
          ⟨0, hpos⟩).val) hpos
  have hyEq : y = start.val := by
    have hyEq' : start.val = y := by
      simpa [hHead] using hy
    exact hyEq'.symm
  have hLast :
      (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).getLast? =
        some (((f^[I.graph.vertices - 1]) start).val) := by
    simpa [forwardProjectedCycleOfPos, f, start] using
      getLast?_ofFn_pos
        (fun i : Fin I.graph.vertices => (((forwardSourceSucc I hCycle hForwardAll)^[i.val])
          ⟨0, hpos⟩).val) hpos
  have hxEq : x = ((f^[I.graph.vertices - 1]) start).val := by
    have hxEq' : ((f^[I.graph.vertices - 1]) start).val = x := by
      simpa [hLast] using hx
    exact hxEq'.symm
  have hEdge := forwardSourceSucc_edge hCycle hForwardAll ((f^[I.graph.vertices - 1]) start)
  have hReturn := forwardSourceSucc_iterate_vertices_eq_self hCycle hForwardAll start
  have hSuccVal :
      (f ((f^[I.graph.vertices - 1]) start)).val = start.val := by
    have hIter :
        (f^[I.graph.vertices]) start = f ((f^[I.graph.vertices - 1]) start) := by
      exact iterate_pos_eq_apply_pred f hpos start
    rw [← hIter]
    exact congrArg Fin.val hReturn
  rw [hxEq, hyEq]
  simpa [f, hSuccVal] using hEdge

theorem forwardProjectedCycleOfPos_nodup
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    (forwardProjectedCycleOfPos I hCycle hForwardAll hpos).Nodup := by
  classical
  unfold forwardProjectedCycleOfPos
  apply List.nodup_ofFn_ofInjective
  intro i j hVal
  let f := forwardSourceSucc I hCycle hForwardAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  by_cases hijLe : i.val ≤ j.val
  · by_cases hijEq : i.val = j.val
    · exact Fin.ext hijEq
    · have hijLt : i.val < j.val := lt_of_le_of_ne hijLe hijEq
      have hFinEq : (f^[i.val]) start = (f^[j.val]) start := Fin.ext hVal
      exfalso
      let u : Fin I.graph.vertices := (f^[i.val]) start
      have huMem := inVertex_mem_of_orderedUHC hCycle u.isLt
      have hAdvance : (f^[j.val - i.val]) u = u := by
        dsimp [u]
        rw [iterate_sub_apply f hijLe start]
        exact hFinEq.symm
      have hReturnSmall :
          ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * (j.val - i.val)])
              (inVertex u.val) =
            inVertex u.val := by
        have hStep := forwardSourceSucc_iterate_three_steps hCycle hForwardAll u (j.val - i.val)
        rw [hStep]
        exact congrArg (fun w : Fin I.graph.vertices => inVertex w.val) hAdvance
      have hkpos : 0 < 3 * (j.val - i.val) := by omega
      have hklt : 3 * (j.val - i.val) < cycle.length := by
        have hLen : cycle.length = 3 * I.graph.vertices := by
          simpa [textbookMap, textbookVertexCount] using hCycle.1
        omega
      exact (cycleSuccessor_iterate_ne_self_of_pos_lt hCycle.2.1 huMem hkpos hklt)
        hReturnSmall
  · have hjiLt : j.val < i.val := Nat.lt_of_not_ge hijLe
    have hjiLe : j.val ≤ i.val := le_of_lt hjiLt
    have hFinEq : (f^[j.val]) start = (f^[i.val]) start := (Fin.ext hVal).symm
    exfalso
    let u : Fin I.graph.vertices := (f^[j.val]) start
    have huMem := inVertex_mem_of_orderedUHC hCycle u.isLt
    have hAdvance : (f^[i.val - j.val]) u = u := by
      dsimp [u]
      rw [iterate_sub_apply f hjiLe start]
      exact hFinEq.symm
    have hReturnSmall :
        ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * (i.val - j.val)])
            (inVertex u.val) =
          inVertex u.val := by
      have hStep := forwardSourceSucc_iterate_three_steps hCycle hForwardAll u (i.val - j.val)
      rw [hStep]
      exact congrArg (fun w : Fin I.graph.vertices => inVertex w.val) hAdvance
    have hkpos : 0 < 3 * (i.val - j.val) := by omega
    have hklt : 3 * (i.val - j.val) < cycle.length := by
      have hLen : cycle.length = 3 * I.graph.vertices := by
        simpa [textbookMap, textbookVertexCount] using hCycle.1
      omega
    exact (cycleSuccessor_iterate_ne_self_of_pos_lt hCycle.2.1 huMem hkpos hklt)
      hReturnSmall

theorem forwardProjectedCycleOfPos_orderedHamiltonianCycle
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v)
    (hpos : 0 < I.graph.vertices) :
    OrderedDirectedHamiltonianCycle I.graph
      (forwardProjectedCycleOfPos I hCycle hForwardAll hpos) := by
  refine ⟨forwardProjectedCycleOfPos_length I hCycle hForwardAll hpos,
    forwardProjectedCycleOfPos_nodup I hCycle hForwardAll hpos,
    forwardProjectedCycleOfPos_withinBounds I hCycle hForwardAll hpos, ?_⟩
  exact DirectedHamiltonianCircuit.orderedDirectedCycleSteps_of_isChain_closing
    (forwardProjectedCycleOfPos_edgeChain I hCycle hForwardAll hpos)
    (forwardProjectedCycleOfPos_cyclicClosingEdge I hCycle hForwardAll hpos)

theorem reverseBlock_cross_predecessor_bounded
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    {u : Nat} (hu : u < I.graph.vertices) (hReverse : BlockReverse cycle u) :
    ∃ v, v < I.graph.vertices ∧ HasDirectedEdge I.graph u v ∧
      DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v) = outVertex u := by
  have hOutMem := outVertex_mem_of_orderedUHC hCycle hu
  rcases orderedUndirectedCycle_exists_predecessor_successor
      hCycle.2.1 hCycle.2.2.2 hOutMem with
    ⟨p, hpMem, hpSucc, hpEdge⟩
  rcases textbook_out_neighbor_choice (hasUndirectedEdge_symm hpEdge) with hpMid | hCross
  · subst p
    have hInOut : inVertex u = outVertex u := by
      rw [← hReverse.2, hpSucc]
    unfold inVertex outVertex at hInOut
    omega
  · rcases hCross with ⟨v, hEdge, hpIn⟩
    have hpBound := hCycle.2.2.1 p hpMem
    have hv : v < I.graph.vertices := by
      rw [hpIn] at hpBound
      simp [textbookMap, textbookVertexCount, inVertex] at hpBound
      omega
    exact ⟨v, hv, hEdge, by simpa [hpIn] using hpSucc⟩

noncomputable def reverseSourcePred
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) : Fin I.graph.vertices := by
  classical
  let ex := reverseBlock_cross_successor_bounded hCycle v.isLt
    (hReverseAll v.val v.isLt)
  exact ⟨Classical.choose ex, (Classical.choose_spec ex).1⟩

theorem reverseSourcePred_edge
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) :
    HasDirectedEdge I.graph (reverseSourcePred I hCycle hReverseAll v).val v.val := by
  classical
  unfold reverseSourcePred
  exact (Classical.choose_spec
    (reverseBlock_cross_successor_bounded hCycle v.isLt
      (hReverseAll v.val v.isLt))).2.1

theorem reverseSourcePred_cross
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) :
    DirectedHamiltonianCircuit.cycleSuccessor cycle (inVertex v.val) =
      outVertex (reverseSourcePred I hCycle hReverseAll v).val := by
  classical
  unfold reverseSourcePred
  exact (Classical.choose_spec
    (reverseBlock_cross_successor_bounded hCycle v.isLt
      (hReverseAll v.val v.isLt))).2.2

theorem reverseSourcePred_three_steps
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) :
    ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3]) (outVertex v.val) =
      outVertex (reverseSourcePred I hCycle hReverseAll v).val := by
  have hReverse := hReverseAll v.val v.isLt
  rw [show (3 : Nat) = Nat.succ (Nat.succ (Nat.succ 0)) by rfl]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [hReverse.1, hReverse.2, reverseSourcePred_cross hCycle hReverseAll v]

theorem reverseSourcePred_iterate_three_steps
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) :
    ∀ k : Nat,
      ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * k]) (outVertex v.val) =
        outVertex (((reverseSourcePred I hCycle hReverseAll)^[k]) v).val
  | 0 => by simp
  | k + 1 => by
      have hArith : 3 * (k + 1) = 3 + 3 * k := by omega
      rw [hArith, Function.iterate_add_apply]
      rw [reverseSourcePred_iterate_three_steps hCycle hReverseAll v k]
      simpa [Function.iterate_succ_apply'] using
        reverseSourcePred_three_steps hCycle hReverseAll
          (((reverseSourcePred I hCycle hReverseAll)^[k]) v)

theorem reverseSourcePred_iterate_vertices_eq_self
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (v : Fin I.graph.vertices) :
    ((reverseSourcePred I hCycle hReverseAll)^[I.graph.vertices]) v = v := by
  have hOutMem := outVertex_mem_of_orderedUHC hCycle v.isLt
  have hTarget :=
    cycleSuccessor_iterate_length_eq_self hCycle.2.1 hOutMem
  have hLen : cycle.length = 3 * I.graph.vertices := by
    simpa [textbookMap, textbookVertexCount] using hCycle.1
  have hIter :=
    reverseSourcePred_iterate_three_steps hCycle hReverseAll v I.graph.vertices
  rw [hLen] at hTarget
  rw [hIter] at hTarget
  have hVal : (((reverseSourcePred I hCycle hReverseAll)^[I.graph.vertices]) v).val = v.val := by
    unfold outVertex at hTarget
    omega
  exact Fin.ext hVal

noncomputable def reverseProjectedCycleOfPos
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) : List Nat :=
  List.ofFn fun i : Fin I.graph.vertices =>
    (((reverseSourcePred I hCycle hReverseAll)^[I.graph.vertices - i.val]) ⟨0, hpos⟩).val

theorem reverseProjectedCycleOfPos_length
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).length = I.graph.vertices := by
  simp [reverseProjectedCycleOfPos]

theorem reverseProjectedCycleOfPos_withinBounds
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    VerticesWithinBounds I.graph (reverseProjectedCycleOfPos I hCycle hReverseAll hpos) := by
  intro v hv
  simp [reverseProjectedCycleOfPos] at hv
  rcases hv with ⟨i, rfl⟩
  exact (((reverseSourcePred I hCycle hReverseAll)^[I.graph.vertices - i.val]) ⟨0, hpos⟩).isLt

theorem reverseProjectedCycleOfPos_edgeChain
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).IsChain
      fun u v => HasDirectedEdge I.graph u v := by
  unfold reverseProjectedCycleOfPos
  rw [List.isChain_ofFn]
  intro i hi
  let r := reverseSourcePred I hCycle hReverseAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  let next : Fin I.graph.vertices := (r^[I.graph.vertices - (i + 1)]) start
  have hCurrent : r next = (r^[I.graph.vertices - i]) start := by
    dsimp [next]
    rw [← Function.iterate_succ_apply' r (I.graph.vertices - (i + 1)) start]
    have hExp : Nat.succ (I.graph.vertices - (i + 1)) = I.graph.vertices - i := by
      omega
    rw [hExp]
  have hEdge := reverseSourcePred_edge hCycle hReverseAll next
  simpa [reverseProjectedCycleOfPos, r, start, next, hCurrent] using hEdge

end UndirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
