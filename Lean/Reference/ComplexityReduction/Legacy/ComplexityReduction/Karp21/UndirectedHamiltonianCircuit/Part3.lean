import ComplexityReduction.Legacy.ComplexityReduction.Karp21.UndirectedHamiltonianCircuit.Part2

namespace ComplexityReduction
namespace Karp21
namespace UndirectedHamiltonianCircuit
open ComplexityReduction.Combinatorics.Graph

theorem reverseProjectedCycleOfPos_cyclicClosingEdge
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    ∀ x ∈ (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).getLast?,
      ∀ y ∈ (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).head?,
        HasDirectedEdge I.graph x y := by
  intro x hx y hy
  let r := reverseSourcePred I hCycle hReverseAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  have hHead :
      (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).head? =
        some (((r^[I.graph.vertices]) start).val) := by
    simpa [reverseProjectedCycleOfPos, r, start] using
      head?_ofFn_pos
        (fun i : Fin I.graph.vertices => (((reverseSourcePred I hCycle hReverseAll)^[
          I.graph.vertices - i.val]) ⟨0, hpos⟩).val) hpos
  have hReturn := reverseSourcePred_iterate_vertices_eq_self hCycle hReverseAll start
  have hyEq : y = start.val := by
    have hyEq' : ((r^[I.graph.vertices]) start).val = y := by
      simpa [hHead] using hy
    rw [hReturn] at hyEq'
    exact hyEq'.symm
  have hLast :
      (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).getLast? =
        some ((r start).val) := by
    have hRaw :=
      getLast?_ofFn_pos
        (fun i : Fin I.graph.vertices => (((reverseSourcePred I hCycle hReverseAll)^[
          I.graph.vertices - i.val]) ⟨0, hpos⟩).val) hpos
    have hExp : I.graph.vertices - (I.graph.vertices - 1) = 1 := by omega
    simpa [reverseProjectedCycleOfPos, r, start, hExp, Function.iterate_succ_apply'] using hRaw
  have hxEq : x = (r start).val := by
    have hxEq' : (r start).val = x := by
      simpa [hLast] using hx
    exact hxEq'.symm
  have hEdge := reverseSourcePred_edge hCycle hReverseAll start
  rw [hxEq, hyEq]
  exact hEdge

theorem reverseProjectedCycleOfPos_nodup
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    (reverseProjectedCycleOfPos I hCycle hReverseAll hpos).Nodup := by
  classical
  unfold reverseProjectedCycleOfPos
  apply List.nodup_ofFn_ofInjective
  intro i j hVal
  let r := reverseSourcePred I hCycle hReverseAll
  let start : Fin I.graph.vertices := ⟨0, hpos⟩
  let ai := I.graph.vertices - i.val
  let aj := I.graph.vertices - j.val
  have haiPos : 0 < ai := by
    dsimp [ai]
    omega
  have hajPos : 0 < aj := by
    dsimp [aj]
    omega
  have hFinEq : (r^[ai]) start = (r^[aj]) start := Fin.ext hVal
  by_cases haijLe : ai ≤ aj
  · by_cases haijEq : ai = aj
    · apply Fin.ext
      dsimp [ai, aj] at haijEq
      omega
    · have haijLt : ai < aj := lt_of_le_of_ne haijLe haijEq
      exfalso
      let u : Fin I.graph.vertices := (r^[ai]) start
      have huMem := outVertex_mem_of_orderedUHC hCycle u.isLt
      have hAdvance : (r^[aj - ai]) u = u := by
        dsimp [u]
        rw [iterate_sub_apply r haijLe start]
        exact hFinEq.symm
      have hReturnSmall :
          ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * (aj - ai)])
              (outVertex u.val) =
            outVertex u.val := by
        have hStep := reverseSourcePred_iterate_three_steps hCycle hReverseAll u (aj - ai)
        rw [hStep]
        exact congrArg (fun w : Fin I.graph.vertices => outVertex w.val) hAdvance
      have hkpos : 0 < 3 * (aj - ai) := by omega
      have hklt : 3 * (aj - ai) < cycle.length := by
        have hLen : cycle.length = 3 * I.graph.vertices := by
          simpa [textbookMap, textbookVertexCount] using hCycle.1
        dsimp [ai, aj] at haijLt
        omega
      exact (cycleSuccessor_iterate_ne_self_of_pos_lt hCycle.2.1 huMem hkpos hklt)
        hReturnSmall
  · have hajiLt : aj < ai := Nat.lt_of_not_ge haijLe
    have hajiLe : aj ≤ ai := le_of_lt hajiLt
    have hFinEq' : (r^[aj]) start = (r^[ai]) start := hFinEq.symm
    exfalso
    let u : Fin I.graph.vertices := (r^[aj]) start
    have huMem := outVertex_mem_of_orderedUHC hCycle u.isLt
    have hAdvance : (r^[ai - aj]) u = u := by
      dsimp [u]
      rw [iterate_sub_apply r hajiLe start]
      exact hFinEq'.symm
    have hReturnSmall :
        ((DirectedHamiltonianCircuit.cycleSuccessor cycle)^[3 * (ai - aj)])
            (outVertex u.val) =
          outVertex u.val := by
      have hStep := reverseSourcePred_iterate_three_steps hCycle hReverseAll u (ai - aj)
      rw [hStep]
      exact congrArg (fun w : Fin I.graph.vertices => outVertex w.val) hAdvance
    have hkpos : 0 < 3 * (ai - aj) := by omega
    have hklt : 3 * (ai - aj) < cycle.length := by
      have hLen : cycle.length = 3 * I.graph.vertices := by
        simpa [textbookMap, textbookVertexCount] using hCycle.1
      dsimp [ai, aj] at hajiLt
      omega
    exact (cycleSuccessor_iterate_ne_self_of_pos_lt hCycle.2.1 huMem hkpos hklt)
      hReturnSmall

theorem reverseProjectedCycleOfPos_orderedHamiltonianCycle
    (I : DirectedHamiltonianCircuitInput) {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v)
    (hpos : 0 < I.graph.vertices) :
    OrderedDirectedHamiltonianCycle I.graph
      (reverseProjectedCycleOfPos I hCycle hReverseAll hpos) := by
  refine ⟨reverseProjectedCycleOfPos_length I hCycle hReverseAll hpos,
    reverseProjectedCycleOfPos_nodup I hCycle hReverseAll hpos,
    reverseProjectedCycleOfPos_withinBounds I hCycle hReverseAll hpos, ?_⟩
  exact DirectedHamiltonianCircuit.orderedDirectedCycleSteps_of_isChain_closing
    (reverseProjectedCycleOfPos_edgeChain I hCycle hReverseAll hpos)
    (reverseProjectedCycleOfPos_cyclicClosingEdge I hCycle hReverseAll hpos)

def sourceOfInVertex (x : Nat) : Option Nat :=
  if x % 3 = 0 then some (x / 3) else none

def sourceProjection (cycle : List Nat) : List Nat :=
  cycle.filterMap sourceOfInVertex

theorem sourceOfInVertex_eq_some_iff {x v : Nat} :
    sourceOfInVertex x = some v ↔ x = inVertex v := by
  constructor
  · intro h
    by_cases hmod : x % 3 = 0
    · have hSome : some (x / 3) = some v := by
        simpa [sourceOfInVertex, hmod] using h
      have hdiv : x / 3 = v := Option.some.inj hSome
      have hdecomp := Nat.div_add_mod x 3
      rw [hmod, Nat.add_zero] at hdecomp
      rw [← hdecomp, hdiv]
      rfl
    · simp [sourceOfInVertex, hmod] at h
  · intro hx
    subst x
    simp [sourceOfInVertex, inVertex, Nat.mul_mod_right]

theorem sourceOfInVertex_in (v : Nat) :
    sourceOfInVertex (inVertex v) = some v := by
  exact sourceOfInVertex_eq_some_iff.mpr rfl

theorem sourceOfInVertex_mid (v : Nat) :
    sourceOfInVertex (midVertex v) = none := by
  unfold sourceOfInVertex midVertex
  have hmod : (3 * v + 1) % 3 = 1 := by
    norm_num [Nat.add_mod, Nat.mul_mod_right]
  simp [hmod]

theorem sourceOfInVertex_out (v : Nat) :
    sourceOfInVertex (outVertex v) = none := by
  unfold sourceOfInVertex outVertex
  have hmod : (3 * v + 2) % 3 = 2 := by
    norm_num [Nat.add_mod, Nat.mul_mod_right]
  simp [hmod]

theorem sourceProjection_nodup {cycle : List Nat}
    (hNodup : cycle.Nodup) :
    (sourceProjection cycle).Nodup := by
  unfold sourceProjection
  exact hNodup.filterMap (fun a a' b hb hb' => by
    have ha : sourceOfInVertex a = some b := by simpa using hb
    have ha' : sourceOfInVertex a' = some b := by simpa using hb'
    have hA := sourceOfInVertex_eq_some_iff.mp ha
    have hA' := sourceOfInVertex_eq_some_iff.mp ha'
    exact hA.trans hA'.symm)

theorem mem_sourceProjection_of_inVertex_mem {cycle : List Nat} {v : Nat}
    (hMem : inVertex v ∈ cycle) :
    v ∈ sourceProjection cycle := by
  unfold sourceProjection
  rw [List.mem_filterMap]
  exact ⟨inVertex v, hMem, sourceOfInVertex_in v⟩

theorem sourceProjection_withinBounds
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle) :
    VerticesWithinBounds I.graph (sourceProjection cycle) := by
  intro v hv
  unfold sourceProjection at hv
  rw [List.mem_filterMap] at hv
  rcases hv with ⟨x, hxMem, hxDecode⟩
  have hxEq := sourceOfInVertex_eq_some_iff.mp hxDecode
  have hxBound := hCycle.2.2.1 x hxMem
  rw [hxEq] at hxBound
  simp [textbookMap, textbookVertexCount, inVertex] at hxBound
  omega

theorem sourceProjection_contains_all
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle) :
    ∀ v, v < I.graph.vertices → v ∈ sourceProjection cycle := by
  intro v hv
  exact mem_sourceProjection_of_inVertex_mem (inVertex_mem_of_orderedUHC hCycle hv)

theorem sourceProjection_length
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle) :
    (sourceProjection cycle).length = I.graph.vertices := by
  exact length_eq_vertices_of_nodup_verticesWithinBounds_all
    (sourceProjection_nodup hCycle.2.1)
    (sourceProjection_withinBounds hCycle)
    (sourceProjection_contains_all hCycle)

theorem sourceProjection_directedCycle_of_allForward
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v) :
    DirectedHamiltonianCycle I.graph (sourceProjection cycle) := by
  refine ⟨sourceProjection_length hCycle, sourceProjection_nodup hCycle.2.1,
    sourceProjection_withinBounds hCycle, ?_⟩
  intro u hu
  have huBound := sourceProjection_withinBounds hCycle u hu
  rcases forwardBlock_cross_successor_bounded hCycle huBound (hForwardAll u huBound) with
    ⟨v, hvBound, hEdge, _hSucc⟩
  exact ⟨v, sourceProjection_contains_all hCycle v hvBound, hEdge⟩

/-- Empty directed Hamiltonian witness for the degenerate zero-vertex source graph. -/
theorem empty_orderedDirectedHamiltonianCycle_of_vertices_eq_zero
    {I : DirectedHamiltonianCircuitInput} (hzero : I.graph.vertices = 0) :
    OrderedDirectedHamiltonianCycle I.graph [] := by
  simp [OrderedDirectedHamiltonianCycle, OrderedDirectedCycleSteps, VerticesWithinBounds, hzero]

theorem directedHamiltonianCircuit_of_textbookMap_uhc_allForward
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hDirected : I.graph.directed = true)
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hForwardAll : ∀ v, v < I.graph.vertices → BlockForward cycle v) :
    DirectedHamiltonianCircuit I := by
  refine ⟨hDirected, ?_⟩
  by_cases hpos : 0 < I.graph.vertices
  · exact ⟨forwardProjectedCycleOfPos I hCycle hForwardAll hpos,
      forwardProjectedCycleOfPos_orderedHamiltonianCycle I hCycle hForwardAll hpos⟩
  · have hzero : I.graph.vertices = 0 := by omega
    exact ⟨[], empty_orderedDirectedHamiltonianCycle_of_vertices_eq_zero hzero⟩

theorem directedHamiltonianCircuit_of_textbookMap_uhc_allReverse
    {I : DirectedHamiltonianCircuitInput} {cycle : List Nat}
    (hDirected : I.graph.directed = true)
    (hCycle : OrderedUndirectedHamiltonianCycle (textbookMap I).graph cycle)
    (hReverseAll : ∀ v, v < I.graph.vertices → BlockReverse cycle v) :
    DirectedHamiltonianCircuit I := by
  refine ⟨hDirected, ?_⟩
  by_cases hpos : 0 < I.graph.vertices
  · exact ⟨reverseProjectedCycleOfPos I hCycle hReverseAll hpos,
      reverseProjectedCycleOfPos_orderedHamiltonianCycle I hCycle hReverseAll hpos⟩
  · have hzero : I.graph.vertices = 0 := by omega
    exact ⟨[], empty_orderedDirectedHamiltonianCycle_of_vertices_eq_zero hzero⟩

theorem directedHamiltonianCircuit_of_textbookMap_uhc
    {I : DirectedHamiltonianCircuitInput}
    (hDirected : I.graph.directed = true)
    (hUHC : UndirectedHamiltonianCircuit (textbookMap I)) :
    DirectedHamiltonianCircuit I := by
  rcases hUHC with ⟨_hUndirected, cycle, hCycle⟩
  by_cases hpos : 0 < I.graph.vertices
  · rcases replacementBlock_forced_orientation' hCycle (v := 0) hpos with
      hStartForward | hStartReverse
    · exact directedHamiltonianCircuit_of_textbookMap_uhc_allForward hDirected hCycle
        (allBlocksForward_of_blockForward hCycle hpos hStartForward)
    · exact directedHamiltonianCircuit_of_textbookMap_uhc_allReverse hDirected hCycle
        (allBlocksReverse_of_blockReverse hCycle hpos hStartReverse)
  · have hzero : I.graph.vertices = 0 := by omega
    exact ⟨hDirected, [], empty_orderedDirectedHamiltonianCycle_of_vertices_eq_zero hzero⟩

/-- Fixed no-instance for the guarded textbook undirected Hamiltonian target. -/
def noInput : UndirectedHamiltonianCircuitInput :=
  loopInput 0

theorem noInput_isNo :
    ¬ UndirectedHamiltonianCircuit noInput := by
  intro h
  have hPos : 0 < 0 := (loopInput_correct 0).1 (by simpa [noInput] using h)
  omega

/--
Textbook directed-to-undirected Hamiltonian replacement with a malformed-source
guard.  The Karp source problem is directed Hamiltonian circuit, so non-directed
source inputs are mapped to a fixed no-instance.
-/
noncomputable def guardedTextbookMap
    (I : DirectedHamiltonianCircuitInput) : UndirectedHamiltonianCircuitInput := by
  classical
  exact if I.graph.directed = true then textbookMap I else noInput

theorem guardedTextbookMap_uhc_of_directedHamiltonianCircuit
    {I : DirectedHamiltonianCircuitInput} (hDHC : DirectedHamiltonianCircuit I) :
    UndirectedHamiltonianCircuit (guardedTextbookMap I) := by
  unfold guardedTextbookMap
  simpa [hDHC.1] using textbookMap_uhc_of_directedHamiltonianCircuit hDHC

theorem directedHamiltonianCircuit_of_guardedTextbookMap_uhc
    {I : DirectedHamiltonianCircuitInput}
    (hUHC : UndirectedHamiltonianCircuit (guardedTextbookMap I)) :
    DirectedHamiltonianCircuit I := by
  unfold guardedTextbookMap at hUHC
  by_cases hDirected : I.graph.directed = true
  · simp [hDirected] at hUHC
    exact directedHamiltonianCircuit_of_textbookMap_uhc hDirected hUHC
  · simp [hDirected] at hUHC
    exact False.elim (noInput_isNo hUHC)

theorem guardedTextbookMap_correct (I : DirectedHamiltonianCircuitInput) :
    directedHamiltonianCircuitDecisionProblem.isYes I ↔
      UndirectedHamiltonianCircuit (guardedTextbookMap I) := by
  change DirectedHamiltonianCircuit I ↔ UndirectedHamiltonianCircuit (guardedTextbookMap I)
  exact ⟨guardedTextbookMap_uhc_of_directedHamiltonianCircuit,
    directedHamiltonianCircuit_of_guardedTextbookMap_uhc⟩

theorem undirectedHamiltonianCircuitStructured_inputSize_eq
    (I : UndirectedHamiltonianCircuitInput) :
    undirectedHamiltonianCircuitStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph := by
  rfl

theorem noInput_structured_inputSize_le :
    undirectedHamiltonianCircuitStructuredEncodedType.inputSize noInput ≤ 20 := by
  rw [undirectedHamiltonianCircuitStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  change
    1 + edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) + 4 ≤ 20
  have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
    change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
    exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
  omega

theorem directedHamiltonianCircuitStructured_inputSize_ge_vertices
    (I : DirectedHamiltonianCircuitInput) :
    I.graph.vertices ≤ directedHamiltonianCircuitStructuredEncodedType.inputSize I := by
  rw [DirectedHamiltonianCircuit.directedHamiltonianCircuitStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem directedHamiltonianCircuitStructured_inputSize_ge_edgeList
    (I : DirectedHamiltonianCircuitInput) :
    edgeListStructuredEncodedType.inputSize I.graph.edges ≤
      directedHamiltonianCircuitStructuredEncodedType.inputSize I := by
  rw [DirectedHamiltonianCircuit.directedHamiltonianCircuitStructured_inputSize_eq,
    VertexCover.graphStructured_inputSize_eq]
  omega

theorem directedHamiltonianCircuitStructured_inputSize_ge_edges_length
    (I : DirectedHamiltonianCircuitInput) :
    I.graph.edges.length ≤ directedHamiltonianCircuitStructuredEncodedType.inputSize I := by
  have hEdges :
      I.graph.edges.length ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
    simpa [edgeListStructuredEncodedType, EncodedType.inputSize] using
      (TM2Programs.listEncode_length_ge_length edgeStructuredEncodedType I.graph.edges)
  exact hEdges.trans (directedHamiltonianCircuitStructured_inputSize_ge_edgeList I)

theorem textbookVertexCount_le_directedHamiltonianCircuitStructured_linear
    (I : DirectedHamiltonianCircuitInput) :
    textbookVertexCount I ≤ 3 * directedHamiltonianCircuitStructuredEncodedType.inputSize I :=
  Nat.mul_le_mul_left 3 (directedHamiltonianCircuitStructured_inputSize_ge_vertices I)

theorem encodedList_element_inputSize_le {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem edgeStructured_inputSize_le_source_edges_inputSize_of_mem
    {I : DirectedHamiltonianCircuitInput} {e : Nat × Nat} (he : e ∈ I.graph.edges) :
    edgeStructuredEncodedType.inputSize e ≤ edgeListStructuredEncodedType.inputSize I.graph.edges := by
  simpa [edgeListStructuredEncodedType] using
    (encodedList_element_inputSize_le (X := edgeStructuredEncodedType) he)

theorem textbookInternalEdges_length_eq (I : DirectedHamiltonianCircuitInput) :
    (textbookInternalEdges I).length = 2 * I.graph.vertices := by
  simp [textbookInternalEdges, internalEdgesForVertex, Nat.mul_comm]

theorem textbookCrossEdges_length_eq (I : DirectedHamiltonianCircuitInput) :
    (textbookCrossEdges I).length = I.graph.edges.length := by
  simp [textbookCrossEdges]

theorem textbookEdgeList_length_le_directedHamiltonianCircuitStructured_linear
    (I : DirectedHamiltonianCircuitInput) :
    (textbookEdgeList I).length ≤
      3 * directedHamiltonianCircuitStructuredEncodedType.inputSize I + 1 := by
  let S := directedHamiltonianCircuitStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using directedHamiltonianCircuitStructured_inputSize_ge_vertices I
  have hEdgesLen : I.graph.edges.length ≤ S := by
    simpa [S] using directedHamiltonianCircuitStructured_inputSize_ge_edges_length I
  have hLen :
      (textbookEdgeList I).length = 2 * I.graph.vertices + I.graph.edges.length := by
    simp [textbookEdgeList, textbookInternalEdges_length_eq, textbookCrossEdges_length_eq]
  omega

theorem edgeStructured_inputSize_crossEdge_le_source (e : Nat × Nat) :
    edgeStructuredEncodedType.inputSize (crossEdgeOfDirectedEdge e) ≤
      3 * edgeStructuredEncodedType.inputSize e := by
  cases e with
  | mk u v =>
      simp [edgeStructuredEncodedType, crossEdgeOfDirectedEdge, inVertex, outVertex]
      omega

theorem edgeStructured_inputSize_le_of_mem_textbookInternalEdges
    {I : DirectedHamiltonianCircuitInput} {e : Nat × Nat}
    (he : e ∈ textbookInternalEdges I) :
    edgeStructuredEncodedType.inputSize e ≤ 6 * I.graph.vertices + 1 := by
  rcases List.mem_flatMap.mp he with ⟨v, hvRange, hvEdge⟩
  have hv : v < I.graph.vertices := List.mem_range.mp hvRange
  simp [internalEdgesForVertex] at hvEdge
  rcases hvEdge with hEdge | hEdge
  · rcases hEdge with ⟨rfl, rfl⟩
    simp [edgeStructuredEncodedType, inVertex, midVertex]
    omega
  · rcases hEdge with ⟨rfl, rfl⟩
    simp [edgeStructuredEncodedType, midVertex, outVertex]
    omega

theorem edgeStructured_inputSize_le_of_mem_textbookEdgeList
    {I : DirectedHamiltonianCircuitInput} {e : Nat × Nat} (he : e ∈ textbookEdgeList I) :
    edgeStructuredEncodedType.inputSize e ≤
      6 * directedHamiltonianCircuitStructuredEncodedType.inputSize I + 5 := by
  let S := directedHamiltonianCircuitStructuredEncodedType.inputSize I
  have hVertices : I.graph.vertices ≤ S := by
    simpa [S] using directedHamiltonianCircuitStructured_inputSize_ge_vertices I
  have hEdgeList : edgeListStructuredEncodedType.inputSize I.graph.edges ≤ S := by
    simpa [S] using directedHamiltonianCircuitStructured_inputSize_ge_edgeList I
  rcases List.mem_append.mp he with hInternal | hCross
  · have hInternalSize :=
      edgeStructured_inputSize_le_of_mem_textbookInternalEdges (I := I) hInternal
    omega
  · rcases List.mem_map.mp hCross with ⟨src, hsrc, rfl⟩
    have hSrcSize :
        edgeStructuredEncodedType.inputSize src ≤ S :=
      (edgeStructured_inputSize_le_source_edges_inputSize_of_mem (I := I) hsrc).trans
        hEdgeList
    have hCrossSize := edgeStructured_inputSize_crossEdge_le_source src
    omega

theorem textbookEdgeList_structured_inputSize_le (I : DirectedHamiltonianCircuitInput) :
    edgeListStructuredEncodedType.inputSize (textbookEdgeList I) ≤
      (3 * directedHamiltonianCircuitStructuredEncodedType.inputSize I + 1) *
        (6 * directedHamiltonianCircuitStructuredEncodedType.inputSize I + 6) := by
  let S := directedHamiltonianCircuitStructuredEncodedType.inputSize I
  have hList :=
    VertexCover.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdgeList I) (6 * S + 5) (by
        intro e he
        simpa [S] using edgeStructured_inputSize_le_of_mem_textbookEdgeList he)
  have hLen : (textbookEdgeList I).length ≤ 3 * S + 1 := by
    simpa [S] using textbookEdgeList_length_le_directedHamiltonianCircuitStructured_linear I
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (6 * S + 6) hLen
    simpa [S, edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem undirectedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_directed_poly
    (I : DirectedHamiltonianCircuitInput) :
    undirectedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) ≤
      1000 * (directedHamiltonianCircuitStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  classical
  let S := directedHamiltonianCircuitStructuredEncodedType.inputSize I
  by_cases hDirected : I.graph.directed = true
  · have hVertex : textbookVertexCount I ≤ 3 * S := by
      simpa [S] using textbookVertexCount_le_directedHamiltonianCircuitStructured_linear I
    have hEdges :
        edgeListStructuredEncodedType.inputSize (textbookEdgeList I) ≤
          (3 * S + 1) * (6 * S + 6) := by
      simpa [S] using textbookEdgeList_structured_inputSize_le I
    calc
      undirectedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) =
          undirectedHamiltonianCircuitStructuredEncodedType.inputSize (textbookMap I) := by
            simp [guardedTextbookMap, hDirected]
      _ = textbookVertexCount I +
            edgeListStructuredEncodedType.inputSize (textbookEdgeList I) + 4 := by
            rw [undirectedHamiltonianCircuitStructured_inputSize_eq,
              VertexCover.graphStructured_inputSize_eq]
            simp [textbookMap]
      _ ≤ 3 * S + (3 * S + 1) * (6 * S + 6) + 4 := by
            omega
      _ ≤ 1000 * S ^ 2 + 1000 := by
            cases S with
            | zero =>
                norm_num
            | succ S =>
                ring_nf
                omega
  · calc
      undirectedHamiltonianCircuitStructuredEncodedType.inputSize (guardedTextbookMap I) =
          undirectedHamiltonianCircuitStructuredEncodedType.inputSize noInput := by
            simp [guardedTextbookMap, hDirected]
      _ ≤ 20 := noInput_structured_inputSize_le
      _ ≤ 1000 * S ^ 2 + 1000 := by
            omega

theorem directedToUndirectedHamiltonianCircuitStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : DirectedHamiltonianCircuitInput =>
        directedHamiltonianCircuitStructuredEncodedType.inputSize I)
      (fun J : UndirectedHamiltonianCircuitInput =>
        undirectedHamiltonianCircuitStructuredEncodedType.inputSize J)
      guardedTextbookMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact undirectedHamiltonianCircuitStructured_inputSize_guardedTextbookMap_le_directed_poly I

noncomputable def directedToUndirectedHamiltonianCircuit_textbookTMBackedKarpReduction :
    TMBackedCostedReduction directedHamiltonianCircuitDecisionProblem
      undirectedHamiltonianCircuitDecisionProblem := by
  simpa [undirectedHamiltonianCircuitDecisionProblem,
    undirectedHamiltonianCircuitEncodedType] using
    rawCodomainTMBackedReduction
      directedHamiltonianCircuitDecisionProblem
      Combinatorics.Graph.UndirectedHamiltonianCircuit
      guardedTextbookMap
      guardedTextbookMap_correct

noncomputable def directedToUndirectedHamiltonianCircuit_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel directedHamiltonianCircuitDecisionProblem
      undirectedHamiltonianCircuitDecisionProblem :=
  directedToUndirectedHamiltonianCircuit_textbookTMBackedKarpReduction.toCostedKarpReduction

/--
Costed Karp reduction from the faithful finite-alphabet Directed Hamiltonian
Circuit encoding to the faithful finite-alphabet Undirected Hamiltonian Circuit
encoding by the P15w in/mid/out replacement gadget.

This is a structured `CostedPolyTimeModel` transport theorem, not a direct TM2
soundness theorem.
-/
noncomputable def directedToUndirectedHamiltonianCircuitStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      directedHamiltonianCircuitStructuredDecisionProblem
      undirectedHamiltonianCircuitStructuredDecisionProblem where
  f :=
    { toFun := guardedTextbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            directedToUndirectedHamiltonianCircuitStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [directedHamiltonianCircuitStructuredDecisionProblem,
      undirectedHamiltonianCircuitStructuredDecisionProblem] using guardedTextbookMap_correct I

/-- P15d syntax map from Directed to Undirected Hamiltonian Circuit. -/
noncomputable def map
    (I : DirectedHamiltonianCircuitInput) : UndirectedHamiltonianCircuitInput :=
  loopInput (DirectedHamiltonianCircuit.directedHamiltonianCircuitWitnesses I).length

theorem map_correct (I : DirectedHamiltonianCircuitInput) :
    directedHamiltonianCircuitDecisionProblem.isYes I ↔
      UndirectedHamiltonianCircuit (map I) := by
  change DirectedHamiltonianCircuit I ↔ UndirectedHamiltonianCircuit (map I)
  rw [DirectedHamiltonianCircuit.directedHamiltonianCircuit_iff_witnesses_pos]
  exact
    (loopInput_correct
      (DirectedHamiltonianCircuit.directedHamiltonianCircuitWitnesses I).length).symm

/-- Costed Karp reduction from Directed to Undirected Hamiltonian Circuit. -/
noncomputable def directedToUndirectedHamiltonianCircuitTMBackedKarpReduction :
    TMBackedCostedReduction directedHamiltonianCircuitDecisionProblem
      undirectedHamiltonianCircuitDecisionProblem := by
  simpa [undirectedHamiltonianCircuitDecisionProblem,
    undirectedHamiltonianCircuitEncodedType] using
    rawCodomainTMBackedReduction
      directedHamiltonianCircuitDecisionProblem
      Combinatorics.Graph.UndirectedHamiltonianCircuit
      map
      map_correct

/-- Costed Karp reduction from Directed to Undirected Hamiltonian Circuit. -/
noncomputable def directedToUndirectedHamiltonianCircuitKarpReduction :
    KarpReductionM CostedPolyTimeModel directedHamiltonianCircuitDecisionProblem
      undirectedHamiltonianCircuitDecisionProblem :=
  directedToUndirectedHamiltonianCircuitTMBackedKarpReduction.toCostedKarpReduction

/-- The structured finite-alphabet Undirected Hamiltonian Circuit encoding is faithful. -/
theorem undirectedHamiltonianCircuitStructuredEncoding_faithful :
    undirectedHamiltonianCircuitStructuredDecisionProblem.FaithfulEncoding where
  injective := undirectedHamiltonianCircuitStructuredEncodedType_encode_injective

theorem undirectedHamiltonianCircuitStructuredEncoding_predicateRespects :
    undirectedHamiltonianCircuitStructuredDecisionProblem.PredicateRespectsEncoding :=
  undirectedHamiltonianCircuitStructuredEncoding_faithful.predicateRespects

theorem undirectedHamiltonianCircuitStructuredEncoding_accepts_encode_iff
    (I : UndirectedHamiltonianCircuitInput) :
    undirectedHamiltonianCircuitStructuredDecisionProblem.toEncodedLanguage.accepts
        (undirectedHamiltonianCircuitStructuredEncodedType.encode I) ↔
      UndirectedHamiltonianCircuit I :=
  undirectedHamiltonianCircuitStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Undirected Hamiltonian Circuit is locally in NP for the project-local costed model. -/
theorem undirectedHamiltonianCircuitInNP :
    InNPEnc CostedPolyTimeModel undirectedHamiltonianCircuitDecisionProblem :=
  decidableInNP undirectedHamiltonianCircuitDecisionProblem

/-- Local NP-completeness of Undirected Hamiltonian Circuit via the directed target. -/
theorem undirectedHamiltonianCircuitNPComplete :
    NPCompleteEnc CostedPolyTimeModel undirectedHamiltonianCircuitDecisionProblem :=
  NPCompleteEnc.transfer
    DirectedHamiltonianCircuit.directedHamiltonianCircuitNPComplete
    ⟨directedToUndirectedHamiltonianCircuitKarpReduction⟩
    undirectedHamiltonianCircuitInNP

theorem undirectedHamiltonianCircuit_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel undirectedHamiltonianCircuitDecisionProblem :=
  NPCompleteEnc.transfer
    DirectedHamiltonianCircuit.directedHamiltonianCircuit_textbookNPComplete
    ⟨directedToUndirectedHamiltonianCircuit_textbookKarpReduction⟩
    undirectedHamiltonianCircuitInNP

end UndirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
