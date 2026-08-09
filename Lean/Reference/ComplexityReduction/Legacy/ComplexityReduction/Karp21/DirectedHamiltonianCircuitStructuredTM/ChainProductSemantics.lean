/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainAssemblySemantics

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Product/filter chain arcs agree with row-adjacent chain arcs -/

theorem list_filter_fst_eq_self_of_all
    (xs : List (Nat × Nat)) (u : Nat) (h : ∀ ui, ui ∈ xs → ui.1 = u) :
    (xs.filter fun ui => decide (ui.1 = u)) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : x.1 = u := h x (by simp)
      have hTail : ∀ ui, ui ∈ xs → ui.1 = u := by
        intro ui hui
        exact h ui (by simp [hui])
      simp [hx, ih hTail]

theorem list_filter_fst_eq_nil_of_all_ne
    (xs : List (Nat × Nat)) (u : Nat) (h : ∀ ui, ui ∈ xs → ui.1 ≠ u) :
    (xs.filter fun ui => decide (ui.1 = u)) = [] := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : x.1 ≠ u := h x (by simp)
      have hTail : ∀ ui, ui ∈ xs → ui.1 ≠ u := by
        intro ui hui
        exact h ui (by simp [hui])
      simp [hx, ih hTail]

theorem list_filter_flatMap_same_fst_eq_row
    (us : List Nat) (rows : Nat → List (Nat × Nat)) (target : Nat)
    (hNodup : us.Nodup)
    (hRows : ∀ u ui, ui ∈ rows u → ui.1 = u)
    (hEmptyTarget : target ∉ us → rows target = []) :
    ((us.flatMap rows).filter fun ui => decide (ui.1 = target)) = rows target := by
  induction us with
  | nil =>
      simpa using (hEmptyTarget (by simp)).symm
  | cons u us ih =>
      have huNot : u ∉ us := (List.nodup_cons.mp hNodup).1
      have hTailNodup : us.Nodup := (List.nodup_cons.mp hNodup).2
      rw [List.flatMap_cons, List.filter_append]
      by_cases hut : u = target
      · subst target
        have hHead :
            (rows u).filter (fun ui => decide (ui.1 = u)) = rows u :=
          list_filter_fst_eq_self_of_all (rows u) u (hRows u)
        have hTailAllNe : ∀ ui, ui ∈ us.flatMap rows → ui.1 ≠ u := by
          intro ui hui hEq
          rcases List.mem_flatMap.mp hui with ⟨v, hvUs, huiRow⟩
          have hv : ui.1 = v := hRows v ui huiRow
          have hvu : v = u := hv.symm.trans hEq
          exact huNot (by simpa [hvu] using hvUs)
        have hTail :
            ((us.flatMap rows).filter fun ui => decide (ui.1 = u)) = [] :=
          list_filter_fst_eq_nil_of_all_ne (us.flatMap rows) u hTailAllNe
        simp [hHead, hTail]
      · have hHead :
            (rows u).filter (fun ui => decide (ui.1 = target)) = [] := by
          refine list_filter_fst_eq_nil_of_all_ne (rows u) target ?_
          intro ui hui hEq
          exact hut ((hRows u ui hui).symm.trans hEq)
        have htu : target ≠ u := fun h => hut h.symm
        have hEmptyTail : target ∉ us → rows target = [] := by
          intro ht
          exact hEmptyTarget (by simp [htu, ht])
        have hTail := ih hTailNodup hEmptyTail
        simp [hHead, hTail]

theorem sourceIncidences_filter_fst_eq_incidencesOfVertex
    (I : VertexCoverInput) (u : Nat) :
    ((sourceIncidences I).filter fun ui => decide (ui.1 = u)) =
      incidencesOfVertex I u := by
  rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
  refine list_filter_flatMap_same_fst_eq_row
    (List.range I.graph.vertices) (fun u => incidencesOfVertex I u) u
    (List.nodup_range (n := I.graph.vertices)) ?_ ?_
  · intro v ui hui
    exact ((mem_incidencesOfVertex_iff I v ui).1 hui).2
  · intro huNot
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ui hui
    have hData := (mem_incidencesOfVertex_iff I u ui).1 hui
    have hSource := (mem_sourceIncidences_iff I ui).1 hData.1
    have huLt : u < I.graph.vertices := by
      simpa [hData.2] using hSource.2.1
    exact huNot (List.mem_range.mpr huLt)

theorem list_filter_eq_filter_filter_of_imp {α : Type*}
    (xs : List α) (p q : α → Prop) [∀ x, Decidable (p x)] [∀ x, Decidable (q x)]
    (hImp : ∀ x, x ∈ xs → p x → q x) :
    xs.filter (fun x => decide (p x)) =
      (xs.filter fun x => decide (q x)).filter fun x => decide (p x) := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hTail : ∀ y, y ∈ xs → p y → q y := by
        intro y hy hp
        exact hImp y (by simp [hy]) hp
      by_cases hp : p x
      · have hq : q x := hImp x (by simp) hp
        simp [hp, hq, ih hTail]
      · simp [hp, ih hTail]

theorem list_map_pair_filter_map {α β γ : Type*}
    (left : α) (rights : List β) (p : α → β → Prop)
    [∀ a b, Decidable (p a b)]
    (f : α × β → γ) :
    (((rights.map fun right => (left, right)).filter fun pair =>
        decide (p pair.1 pair.2)).map f) =
      (rights.filter fun right => decide (p left right)).map fun right => f (left, right) := by
  induction rights with
  | nil =>
      rfl
  | cons right rights ih =>
      by_cases hp : p left right <;> simp [hp, ih]

theorem list_product_filter_right_eq_of_filter_eq {α β γ : Type*}
    (lefts : List α) (rights subrights : List β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] (f : α × β → γ)
    (hFilter :
      ∀ left, left ∈ lefts →
        rights.filter (fun right => decide (p left right)) =
          subrights.filter (fun right => decide (p left right))) :
    (((lefts.product rights).filter fun pair => decide (p pair.1 pair.2)).map f) =
      (((lefts.product subrights).filter fun pair => decide (p pair.1 pair.2)).map f) := by
  induction lefts with
  | nil =>
      rfl
  | cons left lefts ih =>
      have hTail :
          ∀ a, a ∈ lefts →
            rights.filter (fun right => decide (p a right)) =
              subrights.filter (fun right => decide (p a right)) := by
        intro a ha
        exact hFilter a (by simp [ha])
      change
        (((List.map (fun right => (left, right)) rights ++ lefts.product rights).filter
              fun pair => decide (p pair.1 pair.2)).map f) =
          (((List.map (fun right => (left, right)) subrights ++
                lefts.product subrights).filter fun pair => decide (p pair.1 pair.2)).map f)
      rw [List.filter_append, List.filter_append, List.map_append, List.map_append]
      rw [list_map_pair_filter_map left rights p f]
      rw [list_map_pair_filter_map left subrights p f]
      rw [hFilter left (by simp)]
      rw [ih hTail]

noncomputable def dhcChainProductRowWithSource
    (I : VertexCoverInput) (u : Nat) : List (Nat × Nat) := by
  classical
  exact ((((incidencesOfVertex I u).product (sourceIncidences I)).filter fun pair =>
    decide (pair.1.1 = pair.2.1 ∧
      ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map fun pair =>
    (dhcIncidenceVertexFromSourceList I.k (sourceIncidences I) pair.1 1,
      dhcIncidenceVertexFromSourceList I.k (sourceIncidences I) pair.2 0))

theorem dhcChainProductRowWithSource_eq_productRow
    (I : VertexCoverInput) (u : Nat) :
    dhcChainProductRowWithSource I u =
      dhcChainArcsFromSourceProductRow I (sourceIncidences I) u := by
  classical
  let row := incidencesOfVertex I u
  let source := sourceIncidences I
  let p : (Nat × Nat) → (Nat × Nat) → Prop := fun left right =>
    left.1 = right.1 ∧ ConsecutiveIncident I left.1 left.2 right.2
  let f : ((Nat × Nat) × (Nat × Nat)) → Nat × Nat := fun pair =>
    (dhcIncidenceVertexFromSourceList I.k source pair.1 1,
      dhcIncidenceVertexFromSourceList I.k source pair.2 0)
  have hFilter :
      ∀ left, left ∈ row →
        source.filter (fun right => decide (p left right)) =
          row.filter (fun right => decide (p left right)) := by
    intro left hLeft
    have hLeftVertex : left.1 = u :=
      ((mem_incidencesOfVertex_iff I u left).1 hLeft).2
    have hSourceFst :
        source.filter (fun right => decide (right.1 = u)) = row := by
      simpa [source, row] using sourceIncidences_filter_fst_eq_incidencesOfVertex I u
    calc
      source.filter (fun right => decide (p left right))
          =
        (source.filter fun right => decide (right.1 = u)).filter
          fun right => decide (p left right) := by
          exact list_filter_eq_filter_filter_of_imp source (fun right => p left right)
            (fun right => right.1 = u) (by
              intro right _hright hp
              exact hp.1.symm.trans hLeftVertex)
      _ =
        row.filter (fun right => decide (p left right)) := by
          rw [hSourceFst]
  have hProduct :=
    list_product_filter_right_eq_of_filter_eq row source row p f hFilter
  rw [dhcChainProductRowWithSource, dhcChainArcsFromSourceProductRow]
  change
    (((row.product source).filter fun pair => decide (p pair.1 pair.2)).map f) =
      (((row.product row).filter fun pair => decide (p pair.1 pair.2)).map f)
  exact hProduct

theorem list_filter_map_flatten {α β : Type*}
    (xss : List (List α)) (p : α → Prop) [∀ x, Decidable (p x)] (f : α → β) :
    (((xss.flatten).filter fun x => decide (p x)).map f) =
      ((xss.map fun xs => (xs.filter fun x => decide (p x)).map f).flatten) := by
  induction xss with
  | nil =>
      rfl
  | cons xs xss _ =>
      simp [List.filter_append, List.map_append, Function.comp_def]

theorem list_product_append_left {α β : Type*}
    (xs ys : List α) (source : List β) :
    ((xs ++ ys).product source) = xs.product source ++ ys.product source := by
  induction xs with
  | nil =>
      rfl
  | cons x xs _ =>
      simp [List.product, List.append_assoc]

theorem list_product_flatMap_left {α β γ : Type*}
    (us : List α) (rows : α → List β) (source : List γ) :
    (us.flatMap rows).product source =
      ((us.map fun u => (rows u).product source).flatten) := by
  induction us with
  | nil =>
      rfl
  | cons u us ih =>
      change ((rows u ++ us.flatMap rows).product source) =
        (rows u).product source ++ (us.map fun u => (rows u).product source).flatten
      rw [list_product_append_left, ih]

theorem dhcChainArcsFromSourceList_sourceIncidences_eq_productRows
    (I : VertexCoverInput) :
    dhcChainArcsFromSourceList I (sourceIncidences I) =
      ((List.range I.graph.vertices).map fun u =>
        dhcChainArcsFromSourceProductRow I (sourceIncidences I) u).flatten := by
  classical
  let source := sourceIncidences I
  let rows := fun u => incidencesOfVertex I u
  let p : ((Nat × Nat) × (Nat × Nat)) → Prop := fun pair =>
    pair.1.1 = pair.2.1 ∧
      ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2
  let f : ((Nat × Nat) × (Nat × Nat)) → Nat × Nat := fun pair =>
    (dhcIncidenceVertexFromSourceList I.k source pair.1 1,
      dhcIncidenceVertexFromSourceList I.k source pair.2 0)
  have hSource : source = (List.range I.graph.vertices).flatMap rows := by
    simpa [source, rows] using sourceIncidences_eq_flatMap_incidencesOfVertex I
  calc
    dhcChainArcsFromSourceList I (sourceIncidences I)
        =
      (((source.product source).filter fun pair => decide (p pair)).map f) := by
        rfl
    _ =
      ((((((List.range I.graph.vertices).flatMap rows).product source).filter
          fun pair => decide (p pair)).map f)) := by
        rw [hSource]
    _ =
      ((((((List.range I.graph.vertices).map fun u =>
              (rows u).product source).flatten).filter fun pair =>
          decide (p pair)).map f)) := by
        rw [list_product_flatMap_left (List.range I.graph.vertices) rows source]
    _ =
      ((List.range I.graph.vertices).map fun u =>
        ((((rows u).product source).filter fun pair => decide (p pair)).map f)).flatten := by
        rw [list_filter_map_flatten
          ((List.range I.graph.vertices).map fun u => (rows u).product source) p f]
        simp [Function.comp_def]
    _ =
      ((List.range I.graph.vertices).map fun u =>
        dhcChainArcsFromSourceProductRow I source u).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro u _hu
        change
          ((((incidencesOfVertex I u).product (sourceIncidences I)).filter fun pair =>
            decide (pair.1.1 = pair.2.1 ∧
              ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map fun pair =>
            (dhcIncidenceVertexFromSourceList I.k (sourceIncidences I) pair.1 1,
              dhcIncidenceVertexFromSourceList I.k (sourceIncidences I) pair.2 0)) =
            dhcChainArcsFromSourceProductRow I (sourceIncidences I) u
        exact dhcChainProductRowWithSource_eq_productRow I u

theorem textbookChainArcs_eq_textbookTrackChainArcs
    (I : VertexCoverInput) :
    textbookChainArcs I = textbookTrackChainArcs I := by
  classical
  calc
    textbookChainArcs I
        =
      dhcChainArcsFromSourceList I (sourceIncidences I) := by
        simp [dhcChainArcsFromSourceList, textbookChainArcs,
          dhcIncidenceVertexFromSourceIncidences_eq_textbook]
    _ =
      ((List.range I.graph.vertices).map fun u =>
        dhcChainArcsFromSourceProductRow I (sourceIncidences I) u).flatten :=
        dhcChainArcsFromSourceList_sourceIncidences_eq_productRows I
    _ =
      ((List.range I.graph.vertices).map fun u =>
        dhcChainArcsForRowSourceBlocks I.k (sourceIncidences I)
          (incidencesOfVertex I u)).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro u _hu
        exact dhcChainArcsFromSourceProductRow_eq_row I (sourceIncidences I) u
    _ =
      textbookTrackChainArcs I := by
        simp [textbookTrackChainArcs, textbookTrackChainArcsForVertex,
          dhcChainArcsForRowSourceBlocks, dhcChainArcPairBlockFromSourceList,
          dhcIncidenceVertexFromSourceIncidences_eq_textbook]

theorem dhcChainArcsExecutableFromInput_eq_textbookChainArcs
    (I : VertexCoverInput) :
    dhcChainArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookChainArcs I := by
  rw [dhcChainArcsExecutableFromInput_eq_textbookTrackChainArcs]
  rw [textbookChainArcs_eq_textbookTrackChainArcs]

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
