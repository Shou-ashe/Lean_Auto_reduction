/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor
import ComplexityReduction.Legacy.IR.Domains.SetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover

/-!
IR-backed lower-bound edge from Exact Cover to the canonical
Exactly-One-Neighbor target.

The construction uses the existing set-system incidence normalization: universe
elements become required vertices, set-family entries become selectable
vertices, and membership becomes an undirected edge.
-/

namespace ComplexityReduction

open ComplexityReduction.Combinatorics

namespace ExactCoverToExactlyOneNeighbor

/-- Executable finite well-formedness guard for mounted set-system inputs. -/
def setSystemWellFormedBool (I : SetSystemInput) : Bool :=
  I.sets.all fun S => S.all fun x => decide (x < I.universeSize)

theorem setSystemWellFormedBool_eq_true_iff (I : SetSystemInput) :
    setSystemWellFormedBool I = true ↔ SetSystemWellFormed I := by
  unfold setSystemWellFormedBool SetSystemWellFormed
  rw [List.all_eq_true]
  constructor
  · intro h S hS x hx
    have hSAll := h S hS
    rw [List.all_eq_true] at hSAll
    exact of_decide_eq_true (hSAll x hx)
  · intro h S hS
    rw [List.all_eq_true]
    intro x hx
    exact decide_eq_true (h S hS x hx)

/-- Vertex representing set-family entry `j`. -/
def setVertex (I : SetSystemInput) (j : Nat) : Nat :=
  I.universeSize + j

/-- Forward incidence edges from elements to set-entry vertices. -/
def forwardEdges (I : SetSystemInput) : List (Nat × Nat) :=
  (membershipPairs I).map fun p => (p.1, setVertex I p.2)

/-- Undirected graph edge list, represented by both orientations. -/
def incidenceGraphEdges (I : SetSystemInput) : List (Nat × Nat) :=
  forwardEdges I ++ (forwardEdges I).map fun e => (e.2, e.1)

/-- Graph produced from a well-formed Exact Cover set system. -/
def incidenceGraph (I : SetSystemInput) : Graph.GraphInput where
  vertices := I.universeSize + I.sets.length
  edges := incidenceGraphEdges I
  directed := false

/-- Core target instance before the well-formedness guard is applied. -/
def coreTarget (I : ExactCoverInput) : ExactlyOneNeighborInput where
  graph := incidenceGraph I.system
  R := List.range I.system.universeSize

/-- A fixed no-instance used when the source set system is ill formed. -/
def noTarget : ExactlyOneNeighborInput where
  graph := { vertices := 1, edges := [], directed := false }
  R := [0]

/--
Reduction map.  Ill-formed source instances are sent to a manifest no-instance,
because mounted `ExactCover` includes well-formedness in its yes predicate.
-/
def exactCoverToExactlyOneNeighbor (I : ExactCoverInput) : ExactlyOneNeighborInput :=
  if setSystemWellFormedBool I.system then coreTarget I else noTarget

theorem mem_forwardEdges_iff {I : SetSystemInput} {x j : Nat} :
    (x, setVertex I j) ∈ forwardEdges I ↔ IndexedMembership I x j := by
  constructor
  · intro h
    unfold forwardEdges at h
    rcases List.mem_map.mp h with ⟨p, hp, hpair⟩
    cases p with
    | mk y k =>
        simp [setVertex] at hpair
        rcases hpair with ⟨rfl, hk⟩
        subst k
        exact (SetSystem.mem_membershipPairs_iff (I := I) (x := y) (j := j)).mp hp
  · intro h
    unfold forwardEdges
    exact List.mem_map.mpr
      ⟨(x, j), (SetSystem.mem_membershipPairs_iff (I := I) (x := x) (j := j)).mpr h, rfl⟩

theorem not_setVertex_left_mem_forwardEdges
    {I : SetSystemInput} (hI : SetSystemWellFormed I) (j x : Nat) :
    (setVertex I j, x) ∉ forwardEdges I := by
  intro h
  unfold forwardEdges at h
  rcases List.mem_map.mp h with ⟨p, hp, hpair⟩
  cases p with
  | mk y k =>
      simp [setVertex] at hpair
      rcases hpair with ⟨hy, _hx⟩
      have hpBounds := SetSystem.membershipPairs_bounds hI (p := (y, k)) hp
      have hylt : setVertex I j < I.universeSize := by
        simpa [hy] using hpBounds.1
      unfold setVertex at hylt
      omega

theorem mem_incidenceGraphEdges_iff {I : SetSystemInput} {e : Nat × Nat} :
    e ∈ incidenceGraphEdges I ↔ e ∈ forwardEdges I ∨ (e.2, e.1) ∈ forwardEdges I := by
  constructor
  · intro h
    unfold incidenceGraphEdges at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · rcases List.mem_map.mp h with ⟨e', he', hswap⟩
      cases e with
      | mk a b =>
          cases e' with
          | mk c d =>
              simp at hswap
              rcases hswap with ⟨rfl, rfl⟩
              exact Or.inr he'
  · intro h
    unfold incidenceGraphEdges
    rcases h with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨(e.2, e.1), h, by cases e; rfl⟩)

theorem hasUndirectedEdge_core_iff
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    {x u : Nat} (hx : x < I.universeSize) :
    Graph.HasUndirectedEdge (incidenceGraph I) u x ↔
      ∃ j, j < I.sets.length ∧ u = setVertex I j ∧ IndexedMembership I x j := by
  constructor
  · intro h
    unfold Graph.HasUndirectedEdge incidenceGraph at h
    rcases h with h | h
    · have h' := mem_incidenceGraphEdges_iff.mp h
      rcases h' with hf | hr
      · exfalso
        unfold forwardEdges at hf
        rcases List.mem_map.mp hf with ⟨p, _hp, hpair⟩
        cases p with
        | mk y k =>
            simp [setVertex] at hpair
            rcases hpair with ⟨_hu, hxSet⟩
            have : setVertex I k = x := by
              simpa [setVertex] using hxSet
            unfold setVertex at this
            omega
      · unfold forwardEdges at hr
        rcases List.mem_map.mp hr with ⟨p, hp, hpair⟩
        cases p with
        | mk y k =>
            simp [setVertex] at hpair
            rcases hpair with ⟨rfl, rfl⟩
            have hpBounds := SetSystem.membershipPairs_bounds hI (p := (y, k)) hp
            exact ⟨k, hpBounds.2, rfl,
              (SetSystem.mem_membershipPairs_iff (I := I) (x := y) (j := k)).mp hp⟩
    · have h' := mem_incidenceGraphEdges_iff.mp h
      rcases h' with hf | hr
      · unfold forwardEdges at hf
        rcases List.mem_map.mp hf with ⟨p, hp, hpair⟩
        cases p with
        | mk y k =>
            simp [setVertex] at hpair
            rcases hpair with ⟨rfl, rfl⟩
            have hpBounds := SetSystem.membershipPairs_bounds hI (p := (y, k)) hp
            exact ⟨k, hpBounds.2, rfl,
              (SetSystem.mem_membershipPairs_iff (I := I) (x := y) (j := k)).mp hp⟩
      · exfalso
        unfold forwardEdges at hr
        rcases List.mem_map.mp hr with ⟨p, hp, hpair⟩
        cases p with
        | mk y k =>
            simp [setVertex] at hpair
            rcases hpair with ⟨_hu, hxSet⟩
            have : setVertex I k = x := by
              simpa [setVertex] using hxSet
            unfold setVertex at this
            omega
  · rintro ⟨j, _hj, rfl, hmem⟩
    unfold Graph.HasUndirectedEdge incidenceGraph
    right
    exact mem_incidenceGraphEdges_iff.mpr (Or.inl (mem_forwardEdges_iff.mpr hmem))

def selectedIndexVertices (I : SetSystemInput) (selected : List Nat) : List Nat :=
  selected.map (setVertex I)

theorem selectedIndexVertices_nodup {I : SetSystemInput} {selected : List Nat}
    (hSelected : selected.Nodup) :
    (selectedIndexVertices I selected).Nodup := by
  unfold selectedIndexVertices
  exact List.Pairwise.map (setVertex I)
    (fun a b hne hEq => hne (Nat.add_left_cancel hEq)) hSelected

theorem selectedIndexVertices_mem_iff {I : SetSystemInput} {selected : List Nat}
    {u : Nat} :
    u ∈ selectedIndexVertices I selected ↔ ∃ j ∈ selected, u = setVertex I j := by
  unfold selectedIndexVertices
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_map.mpr ⟨j, hj, rfl⟩

theorem incidence_exactCoverIndex_to_target
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    {selected : List Nat} (hSelected : ExactCoverIndexPredicate I selected) :
    ExactlyOneNeighborWitness (coreTarget { system := I }) (selectedIndexVertices I selected) := by
  rcases hSelected with ⟨hNodup, hRight, hCover⟩
  refine ⟨selectedIndexVertices_nodup hNodup, ?_, ?_, ?_⟩
  · intro u hu
    rcases selectedIndexVertices_mem_iff.mp hu with ⟨j, hj, rfl⟩
    exact Nat.add_lt_add_left (hRight j hj) I.universeSize
  · intro x hx
    simp [coreTarget, incidenceGraph] at hx ⊢
    exact Nat.lt_add_right I.sets.length hx
  · intro x hx
    have hxBound : x < I.universeSize := by
      simpa [coreTarget] using hx
    rcases hCover x hxBound with ⟨j, hj, hmem, huniq⟩
    refine ⟨setVertex I j, ?_, ?_, ?_⟩
    · exact selectedIndexVertices_mem_iff.mpr ⟨j, hj, rfl⟩
    · exact (hasUndirectedEdge_core_iff hI hxBound).mpr
        ⟨j, hRight j hj, rfl, hmem⟩
    · intro u' hu' hedge
      rcases selectedIndexVertices_mem_iff.mp hu' with ⟨j', hj', rfl⟩
      rcases (hasUndirectedEdge_core_iff hI hxBound).mp hedge with
        ⟨k, _hk, hVertex, hkMem⟩
      have hjk : j' = k := Nat.add_left_cancel hVertex
      subst k
      have hEq := huniq j' hj' hkMem
      subst j'
      rfl

theorem incidence_existsExactCoverIndex_to_target
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    (h : ExistsExactCoverIndex I) :
    ExactlyOneNeighborYes (coreTarget { system := I }) := by
  rcases h with ⟨selected, hSelected⟩
  exact ⟨selectedIndexVertices I selected, incidence_exactCoverIndex_to_target hI hSelected⟩

def witnessSelectedIndices (I : SetSystemInput) (S : List Nat) : List Nat :=
  (List.range I.sets.length).filter fun j => decide (setVertex I j ∈ S)

theorem mem_witnessSelectedIndices_iff {I : SetSystemInput} {S : List Nat} {j : Nat} :
    j ∈ witnessSelectedIndices I S ↔ j < I.sets.length ∧ setVertex I j ∈ S := by
  unfold witnessSelectedIndices
  rw [List.mem_filter]
  simp [List.mem_range, decide_eq_true_eq]

theorem witnessSelectedIndices_nodup (I : SetSystemInput) (S : List Nat) :
    (witnessSelectedIndices I S).Nodup := by
  unfold witnessSelectedIndices
  exact List.Sublist.nodup List.filter_sublist List.nodup_range

theorem target_to_incidence_existsExactCoverIndex
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    (h : ExactlyOneNeighborYes (coreTarget { system := I })) :
    ExistsExactCoverIndex I := by
  rcases h with ⟨S, hWitness⟩
  rcases hWitness with ⟨_hNodupS, _hSBounds, _hRBounds, hAll⟩
  refine ⟨witnessSelectedIndices I S, ?_⟩
  refine ⟨witnessSelectedIndices_nodup I S, ?_, ?_⟩
  · intro j hj
    exact (mem_witnessSelectedIndices_iff.mp hj).1
  · intro x hx
    have hxR : x ∈ (coreTarget { system := I }).R := by
      simp [coreTarget, hx]
    rcases hAll x hxR with ⟨u, huS, hEdge, hUnique⟩
    rcases (hasUndirectedEdge_core_iff hI hx).mp hEdge with
      ⟨j, hjBounds, hVertex, hmem⟩
    refine ⟨j, ?_, hmem, ?_⟩
    · exact mem_witnessSelectedIndices_iff.mpr
        ⟨hjBounds, by simpa [hVertex] using huS⟩
    · intro j' hj' hmem'
      have hj'Bounds := (mem_witnessSelectedIndices_iff.mp hj').1
      have hj'S := (mem_witnessSelectedIndices_iff.mp hj').2
      have hEdge' :
          Graph.HasUndirectedEdge (incidenceGraph I) (setVertex I j') x :=
        (hasUndirectedEdge_core_iff hI hx).mpr ⟨j', hj'Bounds, rfl, hmem'⟩
      have hVertexEq := hUnique (setVertex I j') hj'S hEdge'
      have hAddEq : setVertex I j' = setVertex I j := by
        simpa [hVertex] using hVertexEq
      exact Nat.add_left_cancel hAddEq

theorem incidence_existsExactCoverIndex_iff_target
    {I : SetSystemInput} (hI : SetSystemWellFormed I) :
    ExistsExactCoverIndex I ↔ ExactlyOneNeighborYes (coreTarget { system := I }) := by
  constructor
  · exact incidence_existsExactCoverIndex_to_target hI
  · exact target_to_incidence_existsExactCoverIndex hI

def selectedSetIndices (I : SetSystemInput) (selected : List (List Nat)) : List Nat :=
  selected.map fun S => I.sets.idxOf S

theorem idxOf_inj_of_mem_family {I : SetSystemInput} {A B : List Nat}
    (hA : A ∈ I.sets) (hB : B ∈ I.sets)
    (hIdx : I.sets.idxOf A = I.sets.idxOf B) :
    A = B := by
  have hgetA := List.getElem?_idxOf hA
  have hgetB := List.getElem?_idxOf hB
  have hsome : some A = some B := by
    rw [← hgetA, ← hgetB, hIdx]
  exact Option.some.inj hsome

theorem selectedSetIndices_nodup {I : SetSystemInput} {selected : List (List Nat)}
    (hFamily : ∀ S ∈ selected, S ∈ I.sets)
    (hSelected : selected.Nodup) :
    (selectedSetIndices I selected).Nodup := by
  induction selected with
  | nil =>
      simp [selectedSetIndices]
  | cons S rest ih =>
      have hSelectedCons := List.nodup_cons.mp hSelected
      have hSNot : S ∉ rest := by
        exact hSelectedCons.1
      have hRestNodup : rest.Nodup := by
        exact hSelectedCons.2
      unfold selectedSetIndices
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hMem
        rcases List.mem_map.mp hMem with ⟨T, hT, hIdx⟩
        have hEq : S = T :=
          idxOf_inj_of_mem_family
            (I := I)
            (hFamily S (by simp))
            (hFamily T (by simp [hT]))
            hIdx.symm
        exact hSNot (by simpa [hEq] using hT)
      · exact ih (by
          intro T hT
          exact hFamily T (by simp [hT])) hRestNodup

theorem exactCover_to_existsExactCoverIndex
    {I : SetSystemInput} (h : ExactCover { system := I }) :
    ExistsExactCoverIndex I := by
  rcases h with ⟨_hI, selected, hFamily, hNodup, hDisjoint, hCover⟩
  refine ⟨selectedSetIndices I selected, ?_⟩
  refine ⟨selectedSetIndices_nodup hFamily hNodup, ?_, ?_⟩
  · intro j hj
    unfold selectedSetIndices at hj
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  · intro x hx
    rcases hCover x hx with ⟨S, hS, hxS⟩
    refine ⟨I.sets.idxOf S, ?_, ?_, ?_⟩
    · unfold selectedSetIndices
      exact List.mem_map.mpr ⟨S, hS, rfl⟩
    · exact ⟨S, List.getElem?_idxOf (hFamily S hS), hxS⟩
    · intro j' hj' hmem'
      unfold selectedSetIndices at hj'
      rcases List.mem_map.mp hj' with ⟨T, hT, hj'⟩
      subst j'
      rcases hmem' with ⟨U, hU, hxU⟩
      have hTget := List.getElem?_idxOf (hFamily T hT)
      have hUT : U = T := by
        have hsome : some U = some T := by
          rw [← hU, ← hTget]
        exact Option.some.inj hsome
      subst U
      have hST : S = T := by
        by_contra hne
        exact hDisjoint S hS T hT hne x hxS hxU
      subst T
      rfl

def selectedNonemptySetValues (I : SetSystemInput) : List Nat → List (List Nat)
  | [] => []
  | j :: js =>
      match I.sets[j]? with
      | none => selectedNonemptySetValues I js
      | some S =>
          if S = [] then selectedNonemptySetValues I js
          else S :: selectedNonemptySetValues I js

theorem selectedNonemptySetValues_mem_iff
    {I : SetSystemInput} {selected : List Nat} {S : List Nat} :
    S ∈ selectedNonemptySetValues I selected ↔
      ∃ j ∈ selected, I.sets[j]? = some S ∧ S ≠ [] := by
  induction selected with
  | nil =>
      simp [selectedNonemptySetValues]
  | cons j js ih =>
      simp only [selectedNonemptySetValues]
      split
      · rename_i hgetNone
        constructor
        · intro h
          rcases ih.mp h with ⟨k, hk, hkget, hkne⟩
          exact ⟨k, by simp [hk], hkget, hkne⟩
        · rintro ⟨k, hk, hkget, hkne⟩
          rcases (by simpa using hk : k = j ∨ k ∈ js) with rfl | hkTail
          · simp [hgetNone] at hkget
          · exact ih.mpr ⟨k, hkTail, hkget, hkne⟩
      · rename_i T hget
        by_cases hEmpty : T = []
        · constructor
          · intro h
            rcases ih.mp (by simpa [hget, hEmpty, selectedNonemptySetValues] using h) with
              ⟨k, hk, hkget, hkne⟩
            exact ⟨k, by simp [hk], hkget, hkne⟩
          · rintro ⟨k, hk, hkget, hkne⟩
            rcases (by simpa using hk : k = j ∨ k ∈ js) with rfl | hkTail
            · have hST : S = T := by
                have hsome : some S = some T := by
                  rw [← hkget, ← hget]
                exact Option.some.inj hsome
              exact False.elim (hkne (by simpa [hST] using hEmpty.symm))
            · simpa [hget, hEmpty, selectedNonemptySetValues] using
                (ih.mpr ⟨k, hkTail, hkget, hkne⟩)
        · constructor
          · intro h
            have hHeadOrTail :
                S = T ∨ S ∈ selectedNonemptySetValues I js := by
              simpa [hget, hEmpty, selectedNonemptySetValues] using h
            rcases hHeadOrTail with rfl | hTail
            · exact ⟨j, by simp, hget, hEmpty⟩
            · rcases ih.mp hTail with ⟨k, hk, hkget, hkne⟩
              exact ⟨k, by simp [hk], hkget, hkne⟩
          · rintro ⟨k, hk, hkget, hkne⟩
            rcases (by simpa using hk : k = j ∨ k ∈ js) with rfl | hkTail
            · have hST : S = T := by
                have hsome : some S = some T := by
                  rw [← hkget, ← hget]
                exact Option.some.inj hsome
              simp [hEmpty, hST]
            · have hTail := ih.mpr ⟨k, hkTail, hkget, hkne⟩
              simpa [hget, hEmpty, selectedNonemptySetValues] using Or.inr hTail

theorem selectedNonemptySetValues_nodup_aux
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    {whole sub : List Nat}
    (hSub : ∀ k ∈ sub, k ∈ whole)
    (hSubNodup : sub.Nodup)
    (hCover :
      ∀ x, x < I.universeSize →
        ∃ k ∈ whole,
          IndexedMembership I x k ∧
            ∀ k' ∈ whole, IndexedMembership I x k' → k' = k) :
    (selectedNonemptySetValues I sub).Nodup := by
  induction sub with
  | nil =>
      simp [selectedNonemptySetValues]
  | cons j js ih =>
      have hNodupCons := List.nodup_cons.mp hSubNodup
      have hSubTail : ∀ k ∈ js, k ∈ whole := by
        intro k hk
        exact hSub k (by simp [hk])
      simp only [selectedNonemptySetValues]
      split
      · exact ih hSubTail hNodupCons.2
      · rename_i S hget
        by_cases hEmpty : S = []
        · simp [hEmpty]
          exact ih hSubTail hNodupCons.2
        · simp [hEmpty, List.nodup_cons]
          constructor
          · intro hMemTail
            rcases (selectedNonemptySetValues_mem_iff.mp hMemTail) with
              ⟨k, hkTail, hkGet, hkNonempty⟩
            rcases List.exists_mem_of_ne_nil S hEmpty with ⟨x, hxS⟩
            have hSFamily : S ∈ I.sets :=
              List.mem_iff_getElem?.mpr ⟨j, hget⟩
            have hxBound : x < I.universeSize := hI S hSFamily x hxS
            rcases hCover x hxBound with ⟨k0, hk0, _hmem0, huniq⟩
            have hjMem : IndexedMembership I x j := ⟨S, hget, hxS⟩
            have hkMem : IndexedMembership I x k := ⟨S, hkGet, hxS⟩
            have hjEq : j = k0 := huniq j (hSub j (by simp)) hjMem
            have hkEq : k = k0 := huniq k (hSubTail k hkTail) hkMem
            have hjk : j = k := hjEq.trans hkEq.symm
            exact hNodupCons.1 (by simpa [hjk] using hkTail)
          · exact ih hSubTail hNodupCons.2

theorem selectedNonemptySetValues_nodup
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    {selected : List Nat}
    (hSelected : ExactCoverIndexPredicate I selected) :
    (selectedNonemptySetValues I selected).Nodup := by
  rcases hSelected with ⟨hNodup, _hRight, hCover⟩
  exact selectedNonemptySetValues_nodup_aux hI
    (whole := selected) (sub := selected)
    (by intro k hk; exact hk)
    hNodup hCover

theorem existsExactCoverIndex_to_exactCover
    {I : SetSystemInput} (hI : SetSystemWellFormed I)
    (h : ExistsExactCoverIndex I) :
    ExactCover { system := I } := by
  rcases h with ⟨selected, hSelected⟩
  rcases hSelected with ⟨hNodup, hRight, hCover⟩
  refine ⟨hI, selectedNonemptySetValues I selected, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases (selectedNonemptySetValues_mem_iff.mp hS) with ⟨j, _hj, hget, _hne⟩
    exact List.mem_iff_getElem?.mpr ⟨j, hget⟩
  · exact selectedNonemptySetValues_nodup hI ⟨hNodup, hRight, hCover⟩
  · intro A hA B hB hAB x hxA hxB
    rcases (selectedNonemptySetValues_mem_iff.mp hA) with
      ⟨j, hj, hgetA, _hANonempty⟩
    rcases (selectedNonemptySetValues_mem_iff.mp hB) with
      ⟨k, hk, hgetB, _hBNonempty⟩
    have hAFamily : A ∈ I.sets := List.mem_iff_getElem?.mpr ⟨j, hgetA⟩
    have hxBound : x < I.universeSize := hI A hAFamily x hxA
    rcases hCover x hxBound with ⟨j0, _hj0, _hmem0, huniq⟩
    have hjMem : IndexedMembership I x j := ⟨A, hgetA, hxA⟩
    have hkMem : IndexedMembership I x k := ⟨B, hgetB, hxB⟩
    have hjEq : j = j0 := huniq j hj hjMem
    have hkEq : k = j0 := huniq k hk hkMem
    have hjk : j = k := hjEq.trans hkEq.symm
    have hABeq : A = B := by
      have hsome : some A = some B := by
        rw [← hgetA, ← hgetB, hjk]
      exact Option.some.inj hsome
    exact hAB hABeq
  · intro x hx
    rcases hCover x hx with ⟨j, hj, hmem, _huniq⟩
    rcases hmem with ⟨S, hget, hxS⟩
    refine ⟨S, ?_, hxS⟩
    exact selectedNonemptySetValues_mem_iff.mpr
      ⟨j, hj, hget, List.ne_nil_of_mem hxS⟩

theorem exactCover_iff_existsExactCoverIndex
    {I : SetSystemInput} (hI : SetSystemWellFormed I) :
    ExactCover { system := I } ↔ ExistsExactCoverIndex I := by
  constructor
  · exact exactCover_to_existsExactCoverIndex
  · exact existsExactCoverIndex_to_exactCover hI

/--
Value-based Exact Cover is equivalent to exact cover over the normalized
incidence view, with set-family indices used as right objects.
-/
theorem exactCover_iff_incidence
    {I : SetSystemInput} (hI : SetSystemWellFormed I) :
    ExactCover { system := I } ↔
      IncidenceView.ExistsExactCover (setSystemIncidenceView I) :=
  (exactCover_iff_existsExactCoverIndex hI).trans
    (existsExactCoverIndex_iff_incidence I)

theorem noTarget_not_yes :
    ¬ ExactlyOneNeighborYes noTarget := by
  rintro ⟨S, hWitness⟩
  rcases hWitness with ⟨_hNodup, _hSBounds, _hRBounds, hAll⟩
  rcases hAll 0 (by simp [noTarget]) with ⟨u, _huS, hEdge, _hUnique⟩
  simp [noTarget, Graph.HasUndirectedEdge] at hEdge

theorem exactCover_core_correct {I : SetSystemInput}
    (hI : SetSystemWellFormed I) :
    ExactCover { system := I } ↔ ExactlyOneNeighborYes (coreTarget { system := I }) :=
  (exactCover_iff_existsExactCoverIndex hI).trans
    (incidence_existsExactCoverIndex_iff_target hI)

theorem exactCoverToExactlyOneNeighbor_correct (I : ExactCoverInput) :
    exactCoverDecisionProblem.isYes I ↔
      ExactlyOneNeighborYes (exactCoverToExactlyOneNeighbor I) := by
  unfold exactCoverToExactlyOneNeighbor
  by_cases hBool : setSystemWellFormedBool I.system = true
  · have hI : SetSystemWellFormed I.system :=
      (setSystemWellFormedBool_eq_true_iff I.system).mp hBool
    simpa [hBool, exactCoverDecisionProblem] using exactCover_core_correct hI
  · have hNotWF : ¬ SetSystemWellFormed I.system := by
      intro hI
      exact hBool ((setSystemWellFormedBool_eq_true_iff I.system).mpr hI)
    constructor
    · intro h
      exact False.elim (hNotWF h.1)
    · intro h
      exact False.elim (noTarget_not_yes (by simpa [hBool] using h))

def exactCoverToExactlyOneNeighborCostedMap :
    CostedMap
      exactCoverDecisionProblem.Instance
      exactlyOneNeighborDecisionProblem.Instance
      exactCoverToExactlyOneNeighbor :=
  CostedMap.of_emptyOutputEncoding (by
    intro I
    rfl)

def exactCoverToExactlyOneNeighborKarpReduction :
    KarpReductionM
      CostedPolyTimeModel
      exactCoverDecisionProblem
      exactlyOneNeighborDecisionProblem where
  f :=
    { toFun := exactCoverToExactlyOneNeighbor
      polytime := CostedPolyTimeMap.of_costed exactCoverToExactlyOneNeighborCostedMap }
  correct := by
    intro I
    simpa [exactlyOneNeighborDecisionProblem] using
      exactCoverToExactlyOneNeighbor_correct I

theorem exactlyOneNeighbor_NPHard :
    NPHardEnc CostedPolyTimeModel exactlyOneNeighborDecisionProblem :=
  NPHardEnc.of_complete_source
    ComplexityReduction.Karp21.ExactCover.exactCoverNPComplete
    ⟨exactCoverToExactlyOneNeighborKarpReduction⟩

end ExactCoverToExactlyOneNeighbor

export ExactCoverToExactlyOneNeighbor
  (setSystemWellFormedBool setSystemWellFormedBool_eq_true_iff
    exactCoverToExactlyOneNeighbor setVertex incidenceGraph coreTarget noTarget
    incidence_existsExactCoverIndex_to_target target_to_incidence_existsExactCoverIndex
    incidence_existsExactCoverIndex_iff_target exactCover_to_existsExactCoverIndex
    existsExactCoverIndex_to_exactCover exactCover_iff_existsExactCoverIndex
    exactCover_iff_incidence noTarget_not_yes exactCoverToExactlyOneNeighbor_correct
    exactCoverToExactlyOneNeighborCostedMap exactCoverToExactlyOneNeighborKarpReduction
    exactlyOneNeighbor_NPHard)

end ComplexityReduction
