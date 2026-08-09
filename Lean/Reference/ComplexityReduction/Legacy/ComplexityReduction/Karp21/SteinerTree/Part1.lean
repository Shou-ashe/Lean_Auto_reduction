/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.WeightedGraph
import Mathlib.Tactic

/-!
P15e weighted-graph target: Exact Cover to Steiner Tree.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- A tiny yes-instance for current-schema Steiner Tree. -/
def yesInput : SteinerTreeInput where
  graph := { vertices := 1, edges := [(0, 0, 1)], directed := false }
  terminals := [0]
  weightBound := 1

/-- A tiny no-instance for current-schema Steiner Tree. -/
def noInput : SteinerTreeInput where
  graph := { vertices := 1, edges := [], directed := false }
  terminals := [0]
  weightBound := 0

theorem yesInput_isYes :
    SteinerTree yesInput := by
  refine ⟨[(0, 0, 1)], ?_, ?_, ?_⟩
  · intro e he
    simp [yesInput, WeightedEdgeInGraph] at he ⊢
    exact he
  · intro t ht
    have ht0 : t = 0 := by
      simpa [yesInput] using ht
    subst t
    constructor
    · exact ⟨(0, 0, 1), by simp, by simp [WeightedEdgeHasEndpoint]⟩
    · exact WeightedReachable.refl 0
  · simp [yesInput, WeightedEdgeListWeight]

theorem noInput_isNo :
    ¬ SteinerTree noInput := by
  rintro ⟨selected, hFamily, hContains, _hWeight⟩
  rcases hContains 0 (by simp [noInput]) with ⟨hPresent, _hReachable⟩
  rcases hPresent with ⟨e, heSelected, _hEndpoint⟩
  have he := hFamily e heSelected
  simp [noInput, WeightedEdgeInGraph] at he

/-! ### Textbook-style weighted connectivity route -/

/-- Root node used by the P15l weighted connectivity gadget. -/
def rootNode : Nat := 0

/-- Witness node for a checked exact-cover subfamily. -/
def witnessNode (j : Nat) : Nat := j + 1

/-- Terminal node for an original exact-cover universe element. -/
noncomputable def terminalNode (I : ExactCoverInput) (x : Nat) : Nat :=
  (ExactCover.exactCoverWitnesses I).length + x + 1

/-- Unit edge from the root to a checked exact-cover witness node. -/
def rootEdge (j : Nat) : Nat × Nat × Nat :=
  (rootNode, witnessNode j, 1)

/-- Zero-weight edge from a checked witness node to an original element terminal. -/
noncomputable def terminalEdge (I : ExactCoverInput) (j x : Nat) : Nat × Nat × Nat :=
  (witnessNode j, terminalNode I x, 0)

/-- Edges contributed by one checked exact-cover witness. -/
noncomputable def edgesForWitness (I : ExactCoverInput) (j : Nat) :
    List (Nat × Nat × Nat) :=
  rootEdge j :: (List.range I.system.universeSize).map (terminalEdge I j)

/-- The P15l weighted connectivity graph edge list. -/
noncomputable def textbookEdges (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  (List.range (ExactCover.exactCoverWitnesses I).length).flatMap (edgesForWitness I)

/-- Terminals are the root plus one terminal for each original universe element. -/
noncomputable def textbookTerminals (I : ExactCoverInput) : List Nat :=
  rootNode :: (List.range I.system.universeSize).map (terminalNode I)

/-- P15l root/witness/terminal weighted-connectivity map from Exact Cover to Steiner Tree. -/
noncomputable def textbookMap (I : ExactCoverInput) : SteinerTreeInput where
  graph :=
    { vertices := (ExactCover.exactCoverWitnesses I).length + I.system.universeSize + 1
      edges := textbookEdges I
      directed := true }
  terminals := textbookTerminals I
  weightBound := 1

theorem rootEdge_mem_edgesForWitness (I : ExactCoverInput) (j : Nat) :
    rootEdge j ∈ edgesForWitness I j := by
  simp [edgesForWitness]

theorem terminalEdge_mem_edgesForWitness {I : ExactCoverInput} {j x : Nat}
    (hx : x < I.system.universeSize) :
    terminalEdge I j x ∈ edgesForWitness I j := by
  exact List.mem_cons_of_mem (rootEdge j)
    (List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩)

theorem mem_textbookEdges_of_mem_edgesForWitness {I : ExactCoverInput} {j : Nat}
    (hj : j < (ExactCover.exactCoverWitnesses I).length) {e : Nat × Nat × Nat}
    (he : e ∈ edgesForWitness I j) :
    e ∈ textbookEdges I := by
  exact List.mem_flatMap.mpr ⟨j, by simpa using hj, he⟩

theorem textbookEdges_source_pos {I : ExactCoverInput} {e : Nat × Nat × Nat}
    (he : e ∈ textbookEdges I) :
    0 < (ExactCover.exactCoverWitnesses I).length := by
  rcases List.mem_flatMap.mp he with ⟨j, hj, _he⟩
  exact Nat.zero_lt_of_lt (by simpa using hj)

theorem edgesForWitness_weight (I : ExactCoverInput) (j : Nat) :
    WeightedEdgeListWeight (edgesForWitness I j) = 1 := by
  simp [edgesForWitness, rootEdge, terminalEdge, WeightedEdgeListWeight, Function.comp_def]

theorem textbookMap_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔ SteinerTree (textbookMap I) := by
  change ExactCover I ↔ SteinerTree (textbookMap I)
  constructor
  · intro hExact
    have hPos : 0 < (ExactCover.exactCoverWitnesses I).length :=
      (ExactCover.exactCover_iff_witnesses_pos I).1 hExact
    let selected := edgesForWitness I 0
    have hRootMem : rootEdge 0 ∈ selected := by
      simpa [selected] using rootEdge_mem_edgesForWitness I 0
    refine ⟨selected, ?_, ?_, ?_⟩
    · intro e he
      exact mem_textbookEdges_of_mem_edgesForWitness hPos (by simpa [selected] using he)
    · intro t ht
      have ht' :
          t = rootNode ∨
            ∃ x, x < I.system.universeSize ∧ terminalNode I x = t := by
        simpa [textbookMap, textbookTerminals] using ht
      constructor
      · rcases ht' with htRoot | htTerm
        · subst t
          exact ⟨rootEdge 0, hRootMem, by simp [rootEdge, rootNode, WeightedEdgeHasEndpoint]⟩
        · rcases htTerm with ⟨x, hx, htx⟩
          subst t
          exact ⟨terminalEdge I 0 x, by
              simpa [selected] using terminalEdge_mem_edgesForWitness (I := I) (j := 0) hx,
            by simp [terminalEdge, WeightedEdgeHasEndpoint]⟩
      · rcases ht' with htRoot | htTerm
        · subst t
          exact WeightedReachable.refl rootNode
        · rcases htTerm with ⟨x, hx, htx⟩
          subst t
          refine WeightedReachable.step (v := witnessNode 0) ?_ ?_
          · exact ⟨rootEdge 0, hRootMem, by
              simp [WeightedEdgeTraverses, rootEdge, rootNode, witnessNode]⟩
          · refine WeightedReachable.step (v := terminalNode I x) ?_
              (WeightedReachable.refl (terminalNode I x))
            exact ⟨terminalEdge I 0 x, by
                simpa [selected] using terminalEdge_mem_edgesForWitness (I := I) (j := 0) hx,
              by simp [WeightedEdgeTraverses, terminalEdge, witnessNode]⟩
    · simp [selected, textbookMap, edgesForWitness_weight]
  · rintro ⟨selected, hFamily, hContains, _hWeight⟩
    rcases hContains rootNode (by simp [textbookMap, textbookTerminals]) with
      ⟨hPresent, _hReachable⟩
    rcases hPresent with ⟨e, heSelected, _hEndpoint⟩
    have hGraph := hFamily e heSelected
    exact (ExactCover.exactCover_iff_witnesses_pos I).2
      (textbookEdges_source_pos (by simpa [textbookMap, WeightedEdgeInGraph] using hGraph))

/-! ### Compact weighted connectivity route

The earlier `textbookMap` above is retained for compatibility with the P15l
raw theorem surface, but it indexes graph nodes by enumerated exact-cover
witnesses.  The compact route below follows the natural-language construction:
one root, one node per source set, one terminal per universe element, root/set
edges weighted by universe support size, and zero-weight set/terminal edges.
-/

/-- Set node used by the compact Exact Cover to Steiner Tree gadget. -/
def compactSetNode (j : Nat) : Nat := j + 1

/-- Terminal node for a universe element in the compact gadget. -/
def compactTerminalNode (I : ExactCoverInput) (x : Nat) : Nat :=
  I.system.sets.length + x + 1

/-- Source set at a family index, with an empty fallback outside the family. -/
def compactSourceSetAt (I : ExactCoverInput) (j : Nat) : List Nat :=
  I.system.sets.getD j []

/-- Universe support of a listed set, deduplicated by ranging over the universe. -/
def compactSupport (I : ExactCoverInput) (S : List Nat) : List Nat :=
  (List.range' 0 I.system.universeSize).filter fun x => decide (x ∈ S)

theorem mem_compactSupport_iff (I : ExactCoverInput) (S : List Nat) (x : Nat) :
    x ∈ compactSupport I S ↔ x < I.system.universeSize ∧ x ∈ S := by
  classical
  simp [compactSupport]

theorem compactSupport_nodup (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).Nodup := by
  classical
  exact List.Nodup.filter _ (by simpa using
    (List.nodup_range' (s := 0) (n := I.system.universeSize)))

theorem compactSupport_length_le_universe (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).length ≤ I.system.universeSize := by
  classical
  exact (List.length_filter_le _ _).trans_eq
    (by simp [List.length_range'])

theorem compactSourceSetAt_idxOf_eq {I : ExactCoverInput} {S : List Nat}
    (hS : S ∈ I.system.sets) :
    compactSourceSetAt I (I.system.sets.idxOf S) = S := by
  have hIdx : I.system.sets.idxOf S < I.system.sets.length :=
    List.idxOf_lt_length_iff.mpr hS
  rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hIdx]
  exact List.idxOf_get hIdx

/-- Zero-weight root self-edge, used so the root terminal is endpoint-present. -/
def compactRootSelfEdge : Nat × Nat × Nat :=
  (rootNode, rootNode, 0)

/-- Root-to-source-set edge weighted by the source set's universe support size. -/
def compactRootEdge (I : ExactCoverInput) (j : Nat) : Nat × Nat × Nat :=
  (rootNode, compactSetNode j, (compactSupport I (compactSourceSetAt I j)).length)

/-- Zero-weight source-set-to-terminal edge for one supported universe element. -/
def compactTerminalEdge (I : ExactCoverInput) (j x : Nat) : Nat × Nat × Nat :=
  (compactSetNode j, compactTerminalNode I x, 0)

/-- Compact gadget edges contributed by one source-set index. -/
def compactEdgesForSet (I : ExactCoverInput) (j : Nat) : List (Nat × Nat × Nat) :=
  compactRootEdge I j ::
    (compactSupport I (compactSourceSetAt I j)).map (compactTerminalEdge I j)

/-- Compact Exact Cover to Steiner Tree edge list. -/
def compactEdges (I : ExactCoverInput) : List (Nat × Nat × Nat) :=
  compactRootSelfEdge :: (List.range I.system.sets.length).flatMap (compactEdgesForSet I)

/-- Compact terminals are the root plus one terminal for each universe element. -/
def compactTerminals (I : ExactCoverInput) : List Nat :=
  rootNode :: (List.range I.system.universeSize).map (compactTerminalNode I)

/-- Compact weighted-connectivity map for well-formed Exact Cover inputs. -/
def compactMapCore (I : ExactCoverInput) : SteinerTreeInput where
  graph :=
    { vertices := I.system.sets.length + I.system.universeSize + 1
      edges := compactEdges I
      directed := true }
  terminals := compactTerminals I
  weightBound := I.system.universeSize

/-- Guard malformed raw set systems with a fixed no-instance. -/
noncomputable def compactMap (I : ExactCoverInput) : SteinerTreeInput := by
  classical
  exact if SetSystemWellFormed I.system then compactMapCore I else noInput

theorem compactRootSelfEdge_mem_edges (I : ExactCoverInput) :
    compactRootSelfEdge ∈ compactEdges I := by
  simp [compactEdges]

theorem compactRootEdge_mem_edgesForSet (I : ExactCoverInput) (j : Nat) :
    compactRootEdge I j ∈ compactEdgesForSet I j := by
  simp [compactEdgesForSet]

theorem compactTerminalEdge_mem_edgesForSet {I : ExactCoverInput} {j x : Nat}
    (hx : x ∈ compactSupport I (compactSourceSetAt I j)) :
    compactTerminalEdge I j x ∈ compactEdgesForSet I j := by
  exact List.mem_cons_of_mem (compactRootEdge I j) (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem mem_compactEdges_of_mem_edgesForSet {I : ExactCoverInput} {j : Nat}
    (hj : j < I.system.sets.length) {e : Nat × Nat × Nat}
    (he : e ∈ compactEdgesForSet I j) :
    e ∈ compactEdges I := by
  exact List.mem_cons_of_mem compactRootSelfEdge
    (List.mem_flatMap.mpr ⟨j, by simpa using hj, he⟩)

theorem compactEdgesForSet_weight (I : ExactCoverInput) (j : Nat) :
    WeightedEdgeListWeight (compactEdgesForSet I j) =
      (compactSupport I (compactSourceSetAt I j)).length := by
  simp [compactEdgesForSet, compactRootEdge, compactTerminalEdge, WeightedEdgeListWeight,
    Function.comp_def]

theorem compactRootSelfEdge_weight :
    WeightedEdgeListWeight [compactRootSelfEdge] = 0 := by
  simp [compactRootSelfEdge, WeightedEdgeListWeight]

theorem weightedEdgeListWeight_append (xs ys : List (Nat × Nat × Nat)) :
    WeightedEdgeListWeight (xs ++ ys) =
      WeightedEdgeListWeight xs + WeightedEdgeListWeight ys := by
  simp [WeightedEdgeListWeight]

/-- Edges selected by one exact-cover source set in the compact forward map. -/
def compactSelectedEdgesForSet (I : ExactCoverInput) (S : List Nat) :
    List (Nat × Nat × Nat) :=
  let j := I.system.sets.idxOf S
  compactRootEdge I j :: (compactSupport I S).map (compactTerminalEdge I j)

/-- Compact forward witness edges induced by an exact-cover selected family. -/
def compactSelectedEdges (I : ExactCoverInput) (selected : List (List Nat)) :
    List (Nat × Nat × Nat) :=
  compactRootSelfEdge :: selected.flatMap (compactSelectedEdgesForSet I)

theorem compactRootEdge_mem_selectedEdgesForSet (I : ExactCoverInput) (S : List Nat) :
    compactRootEdge I (I.system.sets.idxOf S) ∈ compactSelectedEdgesForSet I S := by
  simp [compactSelectedEdgesForSet]

theorem compactTerminalEdge_mem_selectedEdgesForSet {I : ExactCoverInput} {S : List Nat}
    {x : Nat} (hx : x ∈ compactSupport I S) :
    compactTerminalEdge I (I.system.sets.idxOf S) x ∈ compactSelectedEdgesForSet I S := by
  exact List.mem_cons_of_mem (compactRootEdge I (I.system.sets.idxOf S))
    (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem compactRootSelfEdge_mem_selectedEdges (I : ExactCoverInput)
    (selected : List (List Nat)) :
    compactRootSelfEdge ∈ compactSelectedEdges I selected := by
  simp [compactSelectedEdges]

theorem mem_compactSelectedEdges_of_mem_set {I : ExactCoverInput}
    {selected : List (List Nat)} {S : List Nat} (hS : S ∈ selected)
    {e : Nat × Nat × Nat} (he : e ∈ compactSelectedEdgesForSet I S) :
    e ∈ compactSelectedEdges I selected := by
  exact List.mem_cons_of_mem compactRootSelfEdge (List.mem_flatMap.mpr ⟨S, hS, he⟩)

theorem compactSelectedEdgesForSet_subgraph {I : ExactCoverInput} {S : List Nat}
    (hFamily : IsSetInFamily I.system S) :
    ∀ e ∈ compactSelectedEdgesForSet I S, e ∈ compactEdges I := by
  intro e he
  let j := I.system.sets.idxOf S
  have hj : j < I.system.sets.length := List.idxOf_lt_length_iff.mpr hFamily
  have hAt : compactSourceSetAt I j = S := by
    simpa [j] using compactSourceSetAt_idxOf_eq (I := I) (S := S) hFamily
  apply mem_compactEdges_of_mem_edgesForSet (I := I) (j := j) hj
  simpa [compactSelectedEdgesForSet, compactEdgesForSet, j, hAt] using he

theorem compactSelectedEdges_subgraph {I : ExactCoverInput} {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    ∀ e ∈ compactSelectedEdges I selected, e ∈ compactEdges I := by
  intro e he
  simp [compactSelectedEdges] at he
  rcases he with rfl | he
  · exact compactRootSelfEdge_mem_edges I
  · rcases he with ⟨S, hS, heS⟩
    exact compactSelectedEdgesForSet_subgraph (I := I) (S := S) (hFamily S hS) e heS

theorem compactSelectedEdgesForSet_weight {I : ExactCoverInput} {S : List Nat}
    (hFamily : IsSetInFamily I.system S) :
    WeightedEdgeListWeight (compactSelectedEdgesForSet I S) =
      (compactSupport I S).length := by
  let j := I.system.sets.idxOf S
  have hAt : compactSourceSetAt I j = S := by
    simpa [j] using compactSourceSetAt_idxOf_eq (I := I) (S := S) hFamily
  simp [compactSelectedEdgesForSet, compactRootEdge, compactTerminalEdge,
    WeightedEdgeListWeight, Function.comp_def, j, hAt]

theorem compactSelectedFlatEdges_weight_eq {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    WeightedEdgeListWeight (selected.flatMap (compactSelectedEdgesForSet I)) =
      (selected.map fun S => (compactSupport I S).length).sum := by
  induction selected with
  | nil =>
      simp [WeightedEdgeListWeight]
  | cons S selected ih =>
      have hSFamily : IsSetInFamily I.system S := hFamily S (by simp)
      have hTailFamily : ∀ T ∈ selected, IsSetInFamily I.system T := by
        intro T hT
        exact hFamily T (by simp [hT])
      have hHead := compactSelectedEdgesForSet_weight (I := I) (S := S) hSFamily
      have hTail := ih hTailFamily
      change
        WeightedEdgeListWeight
            (compactSelectedEdgesForSet I S ++
              selected.flatMap (compactSelectedEdgesForSet I)) =
          (compactSupport I S).length +
            (selected.map fun S => (compactSupport I S).length).sum
      rw [weightedEdgeListWeight_append, hHead, hTail]

theorem compactSelectedEdges_weight_eq {I : ExactCoverInput} {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    WeightedEdgeListWeight (compactSelectedEdges I selected) =
      (selected.map fun S => (compactSupport I S).length).sum := by
  have hFlat := compactSelectedFlatEdges_weight_eq (I := I) (selected := selected) hFamily
  change
    WeightedEdgeListWeight
        ([compactRootSelfEdge] ++ selected.flatMap (compactSelectedEdgesForSet I)) =
      (selected.map fun S => (compactSupport I S).length).sum
  rw [weightedEdgeListWeight_append, compactRootSelfEdge_weight, hFlat]
  simp

theorem compactSelectedEdges_containsTerminals_of_cover {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hCovers : CoversUniverse I.system selected) :
    ContainsTerminals (compactSelectedEdges I selected) (compactTerminals I) true := by
  intro t ht
  have ht' :
      t = rootNode ∨
        ∃ x, x < I.system.universeSize ∧ compactTerminalNode I x = t := by
    simpa [compactTerminals] using ht
  constructor
  · rcases ht' with htRoot | htTerm
    · subst t
      exact ⟨compactRootSelfEdge, compactRootSelfEdge_mem_selectedEdges I selected, by
        simp [compactRootSelfEdge, rootNode, WeightedEdgeHasEndpoint]⟩
    · rcases htTerm with ⟨x, hx, htx⟩
      subst t
      rcases hCovers x hx with ⟨S, hSSelected, hxS⟩
      have hxSupport : x ∈ compactSupport I S := by
        exact (mem_compactSupport_iff I S x).2 ⟨hx, hxS⟩
      exact
        ⟨compactTerminalEdge I (I.system.sets.idxOf S) x,
          mem_compactSelectedEdges_of_mem_set hSSelected
            (compactTerminalEdge_mem_selectedEdgesForSet (I := I) (S := S) hxSupport),
          by simp [compactTerminalEdge, compactTerminalNode, WeightedEdgeHasEndpoint]⟩
  · rcases ht' with htRoot | htTerm
    · subst t
      exact WeightedReachable.refl rootNode
    · rcases htTerm with ⟨x, hx, htx⟩
      subst t
      rcases hCovers x hx with ⟨S, hSSelected, hxS⟩
      have hxSupport : x ∈ compactSupport I S := by
        exact (mem_compactSupport_iff I S x).2 ⟨hx, hxS⟩
      let j := I.system.sets.idxOf S
      have hRootEdge :
          compactRootEdge I j ∈ compactSelectedEdges I selected := by
        exact mem_compactSelectedEdges_of_mem_set hSSelected
          (by simpa [j] using compactRootEdge_mem_selectedEdgesForSet I S)
      have hTerminalEdge :
          compactTerminalEdge I j x ∈ compactSelectedEdges I selected := by
        exact mem_compactSelectedEdges_of_mem_set hSSelected
          (by simpa [j] using
            compactTerminalEdge_mem_selectedEdgesForSet (I := I) (S := S) hxSupport)
      refine WeightedReachable.step (v := compactSetNode j) ?_ ?_
      · exact ⟨compactRootEdge I j, hRootEdge, by
          simp [WeightedEdgeTraverses, compactRootEdge, rootNode, compactSetNode]⟩
      · refine WeightedReachable.step (v := compactTerminalNode I x) ?_
          (WeightedReachable.refl (compactTerminalNode I x))
        exact ⟨compactTerminalEdge I j x, hTerminalEdge, by
          simp [WeightedEdgeTraverses, compactTerminalEdge, compactSetNode,
            compactTerminalNode]⟩

theorem compactSupportFrom_length_eq_digitCountsFrom_single_sum
    (start len : Nat) (S : List Nat) :
    ((List.range' start len).filter fun x => decide (x ∈ S)).length =
      (Knapsack.digitCountsFrom start len [S]).sum := by
  induction len generalizing start with
  | zero =>
      simp [Knapsack.digitCountsFrom]
  | succ len ih =>
      by_cases h : start ∈ S
      · simp [List.range'_succ, Knapsack.digitCountsFrom, Knapsack.elementCount, h, ih]
        omega
      · simp [List.range'_succ, Knapsack.digitCountsFrom, Knapsack.elementCount, h, ih]

theorem compactSupport_length_eq_digitCountsFrom_single_sum
    (I : ExactCoverInput) (S : List Nat) :
    (compactSupport I S).length =
      (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).sum := by
  simpa [compactSupport] using
    compactSupportFrom_length_eq_digitCountsFrom_single_sum
      0 I.system.universeSize S

theorem list_sum_zipWith_add_of_length_eq {as bs : List Nat}
    (hLen : as.length = bs.length) :
    (as.zipWith (· + ·) bs).sum = as.sum + bs.sum := by
  induction as generalizing bs with
  | nil =>
      cases bs <;> simp at hLen ⊢
  | cons a as ih =>
      cases bs with
      | nil =>
          simp at hLen
      | cons b bs =>
          simp at hLen
          have hTail := ih hLen
          simp [hTail]
          omega

theorem compactSupport_lengths_sum_eq_digitCountsFrom_sum
    (I : ExactCoverInput) (selected : List (List Nat)) :
    (selected.map fun S => (compactSupport I S).length).sum =
      (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
  induction selected with
  | nil =>
      simp [Knapsack.digitCountsFrom_nil]
  | cons S selected ih =>
      have hLen :
          (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).length =
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).length := by
        simp [Knapsack.digitCountsFrom_length]
      calc
        (List.map (fun S => (compactSupport I S).length) (S :: selected)).sum
            =
          (compactSupport I S).length +
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
            simp [ih]
        _ =
          (Knapsack.digitCountsFrom 0 I.system.universeSize [S]).sum +
            (Knapsack.digitCountsFrom 0 I.system.universeSize selected).sum := by
            rw [compactSupport_length_eq_digitCountsFrom_single_sum]
        _ = (Knapsack.digitCountsFrom 0 I.system.universeSize (S :: selected)).sum := by
            conv_rhs => rw [Knapsack.digitCountsFrom_cons]
            exact (list_sum_zipWith_add_of_length_eq hLen).symm

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

theorem compactMapCore_steinerTree_of_exact {I : ExactCoverInput}
    (hExact : ExactCover I) :
    SteinerTree (compactMapCore I) := by
  rcases hExact with ⟨_hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
  refine ⟨compactSelectedEdges I selected, ?_, ?_, ?_⟩
  · intro e he
    exact compactSelectedEdges_subgraph (I := I) (selected := selected) hFamily e he
  · exact compactSelectedEdges_containsTerminals_of_cover (I := I) (selected := selected) hCovers
  · have hWeight := compactSelectedEdges_weight_eq (I := I) (selected := selected) hFamily
    have hSupport :=
      compactSupport_lengths_sum_eq_universe_of_exact
        (I := I) (selected := selected) hNodup hDisjoint hCovers
    rw [hWeight, hSupport]
    simp [compactMapCore]

theorem compactMap_steinerTree_of_exact {I : ExactCoverInput}
    (hExact : ExactCover I) :
    SteinerTree (compactMap I) := by
  have hWellFormed : SetSystemWellFormed I.system := hExact.1
  simpa [compactMap, hWellFormed] using compactMapCore_steinerTree_of_exact hExact

theorem compactSetNode_inj {i j : Nat} :
    compactSetNode i = compactSetNode j → i = j := by
  simp [compactSetNode]

theorem compactTerminalNode_inj {I : ExactCoverInput} {x y : Nat} :
    compactTerminalNode I x = compactTerminalNode I y → x = y := by
  simp [compactTerminalNode]

theorem mem_compactEdges_cases {I : ExactCoverInput} {e : Nat × Nat × Nat}
    (he : e ∈ compactEdges I) :
    e = compactRootSelfEdge ∨
      ∃ j, j < I.system.sets.length ∧
        (e = compactRootEdge I j ∨
          ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
            e = compactTerminalEdge I j x) := by
  simp [compactEdges, compactEdgesForSet] at he
  rcases he with hSelf | he
  · exact Or.inl hSelf
  · rcases he with ⟨j, hj, he⟩
    refine Or.inr ⟨j, hj, ?_⟩
    rcases he with hRoot | hTerm
    · exact Or.inl hRoot
    · rcases hTerm with ⟨x, hx, hEq⟩
      exact Or.inr ⟨x, hx, hEq.symm⟩

theorem compactRoot_out_cases {I : ExactCoverInput} {e : Nat × Nat × Nat} {v : Nat}
    (heGraph : e ∈ compactEdges I)
    (hTrav : WeightedEdgeTraverses true e rootNode v) :
    (e = compactRootSelfEdge ∧ v = rootNode) ∨
      ∃ j, j < I.system.sets.length ∧ e = compactRootEdge I j ∧
        v = compactSetNode j := by
  rcases mem_compactEdges_cases (I := I) heGraph with hSelf | hSet
  · subst e
    simp [WeightedEdgeTraverses, compactRootSelfEdge, rootNode] at hTrav
    exact Or.inl ⟨rfl, by simpa [rootNode] using hTrav.symm⟩
  · rcases hSet with ⟨j, hj, hCases⟩
    rcases hCases with hRoot | hTerm
    · subst e
      simp [WeightedEdgeTraverses, compactRootEdge, rootNode, compactSetNode] at hTrav
      exact Or.inr ⟨j, hj, rfl, by simpa [compactSetNode] using hTrav.symm⟩
    · rcases hTerm with ⟨x, hx, hEdge⟩
      subst e
      simp [WeightedEdgeTraverses, compactTerminalEdge, rootNode, compactSetNode] at hTrav

theorem compactSet_out_cases {I : ExactCoverInput} {e : Nat × Nat × Nat}
    {j v : Nat} (_hj : j < I.system.sets.length)
    (heGraph : e ∈ compactEdges I)
    (hTrav : WeightedEdgeTraverses true e (compactSetNode j) v) :
    ∃ x, x ∈ compactSupport I (compactSourceSetAt I j) ∧
      e = compactTerminalEdge I j x ∧ v = compactTerminalNode I x := by
  rcases mem_compactEdges_cases (I := I) heGraph with hSelf | hSet
  · subst e
    simp [WeightedEdgeTraverses, compactRootSelfEdge, rootNode, compactSetNode] at hTrav
  · rcases hSet with ⟨k, hk, hCases⟩
    rcases hCases with hRoot | hTerm
    · subst e
      simp [WeightedEdgeTraverses, compactRootEdge, rootNode, compactSetNode] at hTrav
    · rcases hTerm with ⟨x, hx, hEdge⟩
      subst e
      simp [WeightedEdgeTraverses, compactTerminalEdge, compactSetNode,
        compactTerminalNode] at hTrav
      have hkj : k = j := by omega
      subst k
      exact ⟨x, hx, rfl, by simpa [compactTerminalNode] using hTrav.2.symm⟩

theorem compactTerminal_no_out {I : ExactCoverInput} {e : Nat × Nat × Nat}
    {x v : Nat} (_hx : x < I.system.universeSize)
    (heGraph : e ∈ compactEdges I)
    (hTrav : WeightedEdgeTraverses true e (compactTerminalNode I x) v) :
    False := by
  rcases mem_compactEdges_cases (I := I) heGraph with hSelf | hSet
  · subst e
    simp [WeightedEdgeTraverses, compactRootSelfEdge, rootNode, compactTerminalNode] at hTrav
  · rcases hSet with ⟨j, hj, hCases⟩
    rcases hCases with hRoot | hTerm
    · subst e
      simp [WeightedEdgeTraverses, compactRootEdge, rootNode, compactTerminalNode] at hTrav
    · rcases hTerm with ⟨y, hy, hEdge⟩
      subst e
      simp [WeightedEdgeTraverses, compactTerminalEdge, compactSetNode,
        compactTerminalNode] at hTrav
      omega

theorem compactReachable_terminal_eq_aux {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {u w x y : Nat}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hy : y < I.system.universeSize) (hu : u = compactTerminalNode I y)
    (hw : w = compactTerminalNode I x)
    (hReach : WeightedReachable selected true u w) :
    y = x := by
  cases hReach with
  | refl u =>
      have hEq : compactTerminalNode I y = compactTerminalNode I x := by
        rw [← hu, hw]
      exact compactTerminalNode_inj (I := I) hEq
  | step hAdj _hRest =>
      rcases hAdj with ⟨e, heSelected, hTrav⟩
      exact (compactTerminal_no_out (I := I) (x := y) hy
        (hSubgraph e heSelected) (by simpa [hu] using hTrav)).elim

theorem compactReachable_terminal_eq {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {x y : Nat}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hy : y < I.system.universeSize)
    (hReach :
      WeightedReachable selected true (compactTerminalNode I y) (compactTerminalNode I x)) :
    y = x :=
  compactReachable_terminal_eq_aux
    (I := I) (selected := selected) (u := compactTerminalNode I y)
    (w := compactTerminalNode I x) (x := x) (y := y)
    hSubgraph hy rfl rfl hReach

theorem compactReachable_set_to_terminal {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {j x : Nat}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hj : j < I.system.sets.length)
    (hReach :
      WeightedReachable selected true (compactSetNode j) (compactTerminalNode I x)) :
    ∃ y, y ∈ compactSupport I (compactSourceSetAt I j) ∧
      compactTerminalEdge I j y ∈ selected ∧ y = x := by
  cases hReach with
  | refl u =>
      simp at hj
  | step hAdj hRest =>
      rcases hAdj with ⟨e, heSelected, hTrav⟩
      rcases compactSet_out_cases (I := I) (j := j) hj
          (hSubgraph e heSelected) hTrav with
        ⟨y, hySupport, hEdge, hv⟩
      subst e
      subst hv
      have hy : y < I.system.universeSize :=
        (mem_compactSupport_iff I (compactSourceSetAt I j) y).1 hySupport |>.1
      have hyx := compactReachable_terminal_eq
        (I := I) (selected := selected) (x := x) (y := y) hSubgraph hy hRest
      exact ⟨y, hySupport, heSelected, hyx⟩

theorem compactReachable_root_to_terminal_aux {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {u w x : Nat}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hx : x < I.system.universeSize) (hu : u = rootNode)
    (hw : w = compactTerminalNode I x)
    (hReach : WeightedReachable selected true u w) :
    ∃ j, j < I.system.sets.length ∧ compactRootEdge I j ∈ selected ∧
      x ∈ compactSupport I (compactSourceSetAt I j) := by
  induction hReach generalizing x with
  | refl u =>
      have hImpossible : rootNode = compactTerminalNode I x := by
        rw [← hu, hw]
      simp [rootNode, compactTerminalNode] at hImpossible
  | step hAdj hRest ih =>
      rcases hAdj with ⟨e, heSelected, hTrav⟩
      rcases compactRoot_out_cases (I := I) (e := e)
          (hSubgraph e heSelected) (by simpa [hu] using hTrav) with hSelf | hRoot
      · rcases hSelf with ⟨hEdge, hv⟩
        subst e
        exact ih hx hv hw
      · rcases hRoot with ⟨j, hj, hEdge, hv⟩
        subst e
        subst hv
        rcases compactReachable_set_to_terminal
            (I := I) (selected := selected) (j := j) (x := x)
            hSubgraph hj (by simpa [hw] using hRest) with
          ⟨y, hySupport, _hyEdge, hyx⟩
        subst x
        exact ⟨j, hj, heSelected, hySupport⟩

theorem compactReachable_root_to_terminal {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} {x : Nat}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hx : x < I.system.universeSize)
    (hReach :
      WeightedReachable selected true rootNode (compactTerminalNode I x)) :
    ∃ j, j < I.system.sets.length ∧ compactRootEdge I j ∈ selected ∧
      x ∈ compactSupport I (compactSourceSetAt I j) :=
  compactReachable_root_to_terminal_aux
    (I := I) (selected := selected) (u := rootNode) (w := compactTerminalNode I x)
    (x := x) hSubgraph hx rfl rfl hReach

/-- Source-set indices whose root edge is selected in a compact Steiner witness. -/
def compactUsedSetIndices (I : ExactCoverInput) (selected : List (Nat × Nat × Nat)) :
    List Nat :=
  (List.range I.system.sets.length).filter fun j => decide (compactRootEdge I j ∈ selected)

/-- Source sets decoded from selected root-to-set edges, deduplicated as set values. -/
def compactDecodedSets (I : ExactCoverInput) (selected : List (Nat × Nat × Nat)) :
    List (List Nat) :=
  ((compactUsedSetIndices I selected).map (compactSourceSetAt I)).dedup

/-- Selected root edges corresponding to `compactUsedSetIndices`. -/
def compactUsedRootEdges (I : ExactCoverInput) (selected : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  (compactUsedSetIndices I selected).map (compactRootEdge I)

theorem mem_compactUsedSetIndices_iff (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) (j : Nat) :
    j ∈ compactUsedSetIndices I selected ↔
      j < I.system.sets.length ∧ compactRootEdge I j ∈ selected := by
  classical
  simp [compactUsedSetIndices]

theorem compactUsedSetIndices_nodup (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    (compactUsedSetIndices I selected).Nodup := by
  classical
  exact List.Nodup.filter _ (by simpa using (List.nodup_range (n := I.system.sets.length)))

theorem compactSourceSetAt_mem_family {I : ExactCoverInput} {j : Nat}
    (hj : j < I.system.sets.length) :
    IsSetInFamily I.system (compactSourceSetAt I j) := by
  rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hj]
  exact List.getElem_mem _

theorem compactDecodedSets_nodup (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    (compactDecodedSets I selected).Nodup := by
  exact List.nodup_dedup _

theorem compactDecodedSets_family {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)} :
    ∀ S ∈ compactDecodedSets I selected, IsSetInFamily I.system S := by
  intro S hS
  have hMap : S ∈ (compactUsedSetIndices I selected).map (compactSourceSetAt I) := by
    simpa [compactDecodedSets] using List.mem_dedup.mp hS
  rcases List.mem_map.mp hMap with ⟨j, hjUsed, rfl⟩
  exact compactSourceSetAt_mem_family
    ((mem_compactUsedSetIndices_iff I selected j).1 hjUsed).1

theorem compactDecodedSets_cover_of_contains {I : ExactCoverInput}
    {selected : List (Nat × Nat × Nat)}
    (hSubgraph : ∀ e ∈ selected, e ∈ compactEdges I)
    (hContains : ContainsTerminals selected (compactTerminals I) true) :
    CoversUniverse I.system (compactDecodedSets I selected) := by
  intro x hx
  have hTermMem : compactTerminalNode I x ∈ compactTerminals I := by
    exact List.mem_cons_of_mem rootNode
      (List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩)
  rcases hContains (compactTerminalNode I x) hTermMem with ⟨_hPresent, hReach⟩
  rcases compactReachable_root_to_terminal
      (I := I) (selected := selected) (x := x) hSubgraph hx hReach with
    ⟨j, hj, hRootSelected, hxSupport⟩
  refine ⟨compactSourceSetAt I j, ?_, ?_⟩
  · have hjUsed : j ∈ compactUsedSetIndices I selected :=
      (mem_compactUsedSetIndices_iff I selected j).2 ⟨hj, hRootSelected⟩
    exact List.mem_dedup.mpr (List.mem_map.mpr ⟨j, hjUsed, rfl⟩)
  · exact (mem_compactSupport_iff I (compactSourceSetAt I j) x).1 hxSupport |>.2

theorem compactRootEdge_injective (I : ExactCoverInput) :
    Function.Injective (compactRootEdge I) := by
  intro i j h
  have hTarget : compactSetNode i = compactSetNode j := by
    simpa [compactRootEdge] using congrArg (fun e : Nat × Nat × Nat => e.2.1) h
  exact compactSetNode_inj hTarget

theorem compactUsedRootEdges_nodup (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    (compactUsedRootEdges I selected).Nodup := by
  exact (compactUsedSetIndices_nodup I selected).map (compactRootEdge_injective I)

theorem compactUsedRootEdges_subperm_selected (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    List.Subperm (compactUsedRootEdges I selected) selected := by
  apply (compactUsedRootEdges_nodup I selected).subperm
  intro e he
  rcases List.mem_map.mp (by simpa [compactUsedRootEdges] using he) with ⟨j, hjUsed, rfl⟩
  exact ((mem_compactUsedSetIndices_iff I selected j).1 hjUsed).2

theorem compactUsedRootEdges_weight_sum_eq (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    ((compactUsedRootEdges I selected).map fun e => e.2.2).sum =
      ((compactUsedSetIndices I selected).map fun j =>
        (compactSupport I (compactSourceSetAt I j)).length).sum := by
  rw [compactUsedRootEdges, List.map_map]
  simp [compactRootEdge, Function.comp_def]

theorem compactUsedSupportSum_le_weight (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    ((compactUsedSetIndices I selected).map fun j =>
        (compactSupport I (compactSourceSetAt I j)).length).sum ≤
      WeightedEdgeListWeight selected := by
  have hSubperm := compactUsedRootEdges_subperm_selected I selected
  have hLe :=
    Knapsack.sum_map_le_of_subperm (fun e : Nat × Nat × Nat => e.2.2) hSubperm
  rw [← compactUsedRootEdges_weight_sum_eq I selected]
  simpa [WeightedEdgeListWeight] using hLe

theorem compactDecodedSupportSum_le_usedSupportSum (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    ((compactDecodedSets I selected).map fun S => (compactSupport I S).length).sum ≤
      ((compactUsedSetIndices I selected).map fun j =>
        (compactSupport I (compactSourceSetAt I j)).length).sum := by
  have hSublist :
      List.Sublist (compactDecodedSets I selected)
        ((compactUsedSetIndices I selected).map (compactSourceSetAt I)) := by
    simpa [compactDecodedSets] using
      (List.dedup_sublist
        ((compactUsedSetIndices I selected).map (compactSourceSetAt I)))
  simpa [List.map_map, Function.comp_def] using
    Knapsack.sum_map_le_of_sublist (fun S => (compactSupport I S).length) hSublist

theorem compactDecodedSupportSum_le_weight (I : ExactCoverInput)
    (selected : List (Nat × Nat × Nat)) :
    ((compactDecodedSets I selected).map fun S => (compactSupport I S).length).sum ≤
      WeightedEdgeListWeight selected :=
  (compactDecodedSupportSum_le_usedSupportSum I selected).trans
    (compactUsedSupportSum_le_weight I selected)

theorem digitCountsFrom_sum_ge_len_of_covers {sets : List (List Nat)}
    {start len : Nat}
    (hCovers :
      ∀ x, start ≤ x → x < start + len → ∃ S ∈ sets, x ∈ S) :
    len ≤ (Knapsack.digitCountsFrom start len sets).sum := by
  induction len generalizing start with
  | zero =>
      simp [Knapsack.digitCountsFrom]
  | succ len ih =>
      have hHeadCover : ∃ S ∈ sets, start ∈ S := hCovers start (by omega) (by omega)
      rcases hHeadCover with ⟨S, hS, hxS⟩
      have hHeadPos : 0 < Knapsack.elementCount start sets :=
        Knapsack.elementCount_pos_of_mem hS hxS
      have hTailCover :
          ∀ x, start + 1 ≤ x → x < start + 1 + len → ∃ S ∈ sets, x ∈ S := by
        intro x hLo hHi
        exact hCovers x (by omega) (by omega)
      have hTail := ih hTailCover
      simp [Knapsack.digitCountsFrom]
      omega

end SteinerTree
end Karp21
end ComplexityReduction
