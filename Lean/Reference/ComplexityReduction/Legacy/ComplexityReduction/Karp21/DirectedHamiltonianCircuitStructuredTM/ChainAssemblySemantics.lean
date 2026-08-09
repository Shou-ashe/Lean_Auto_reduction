/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainAssembly

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Semantic bridge for executable adjacent-chain arcs -/

theorem dhcChainArcsFromPrevIndexed_eq_consecutivePairs
    (budget : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier) :
    dhcChainArcsFromPrevIndexed budget prev xs =
      (((prev :: xs).consecutivePairs).map fun pair =>
        dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten := by
  induction xs generalizing prev with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        dhcChainArcsFromPrevIndexed budget prev (x :: xs)
            =
          dhcChainArcBlockFromIndexed (budget, (true, (prev, x))) ++
            dhcChainArcsFromPrevIndexed budget x xs := by
            rfl
        _ =
          dhcChainArcBlockFromIndexed (budget, (true, (prev, x))) ++
            (((x :: xs).consecutivePairs).map fun pair =>
              dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten := by
            rw [ih]
        _ =
          (((prev :: x :: xs).consecutivePairs).map fun pair =>
            dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten := by
            rfl

theorem dhcChainArcsFromAdjacentIndexed_eq_consecutivePairs
    (budget : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier) :
    dhcChainArcsFromAdjacentIndexed budget xs =
      (xs.consecutivePairs.map fun pair =>
        dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten := by
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      simpa [dhcChainArcsFromAdjacentIndexed] using
        dhcChainArcsFromPrevIndexed_eq_consecutivePairs budget x xs

def dhcChainArcPairBlockFromSourceList
    (budget : Nat) (source : List (Nat × Nat)) (pair : (Nat × Nat) × (Nat × Nat)) :
    List (Nat × Nat) :=
  [(dhcIncidenceVertexFromSourceList budget source pair.1 1,
    dhcIncidenceVertexFromSourceList budget source pair.2 0)]

theorem dhcChainArcBlockFromIndexed_eq_sourceListBlock_of_zipIdx_mem
    (budget : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    {left right : (Nat × Nat) × Nat}
    (hLeft : left ∈ source.zipIdx) (hRight : right ∈ source.zipIdx) :
    dhcChainArcBlockFromIndexed (budget, (true, (left, right))) =
      if decide (left.1.1 = right.1.1) then
        dhcChainArcPairBlockFromSourceList budget source (left.1, right.1)
      else [] := by
  have hLeftIdx : left.2 = source.idxOf left.1 :=
    dhcZipIdx_mem_idx_eq hNodup hLeft
  have hRightIdx : right.2 = source.idxOf right.1 :=
    dhcZipIdx_mem_idx_eq hNodup hRight
  by_cases hPred : left.1.1 = right.1.1
  · have hKeep : dhcChainArcCandidateBool (true, (left, right)) = true :=
      (dhcChainArcCandidateBool_eq_true_iff (true, (left, right))).2 ⟨rfl, hPred⟩
    simp [dhcChainArcBlockFromIndexed, hKeep, hPred, dhcChainArcPairBlock,
      dhcChainArcPairBlockFromSourceList, dhcChainArcFromIndexedRaw,
      dhcIncidenceVertexFromSourceList, hLeftIdx, hRightIdx]
  · have hKeep : dhcChainArcCandidateBool (true, (left, right)) = false := by
      cases h : dhcChainArcCandidateBool (true, (left, right))
      · rfl
      · exact False.elim (hPred ((dhcChainArcCandidateBool_eq_true_iff
          (true, (left, right))).1 h).2)
    simp [dhcChainArcBlockFromIndexed, hKeep, hPred]

theorem list_flatten_consecutivePairs_map_fst {α β γ : Type*}
    (xs : List (α × β)) (f : α × α → List γ) :
    ((xs.consecutivePairs).map fun pair => f (pair.1.1, pair.2.1)).flatten =
      (((xs.map Prod.fst).consecutivePairs).map f).flatten := by
  induction xs with
  | nil =>
      simp [List.consecutivePairs]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [List.consecutivePairs]
      | cons y ys =>
          simpa [List.consecutivePairs] using ih

def dhcChainArcsFromSourceConsecutiveBlocks
    (budget : Nat) (source xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (xs.consecutivePairs.map fun pair =>
    if decide (pair.1.1 = pair.2.1) then
      dhcChainArcPairBlockFromSourceList budget source pair
    else []).flatten

def dhcChainArcsForRowSourceBlocks
    (budget : Nat) (source xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (xs.consecutivePairs.map fun pair =>
    dhcChainArcPairBlockFromSourceList budget source pair).flatten

@[simp] theorem list_flatten_map_singleton {α β : Type*} (xs : List α) (f : α → β) :
    (xs.map fun x => [f x]).flatten = xs.map f := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

theorem not_mem_consecutivePairs_left_of_not_mem {α : Type*} {x y : α} {xs : List α}
    (hx : x ∉ xs) : (x, y) ∉ xs.consecutivePairs := by
  intro h
  exact hx (left_mem_of_mem_consecutivePairs h)

theorem not_mem_consecutivePairs_right_of_not_mem {α : Type*} {x y : α} {xs : List α}
    (hy : y ∉ xs) : (x, y) ∉ xs.consecutivePairs := by
  intro h
  exact hy (right_mem_of_mem_consecutivePairs h)

theorem list_product_filter_consecutivePairs_drop_right_head
    {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] (x : α) :
    ∀ (base lefts : List α), x ∉ base → (∀ a, a ∈ lefts → a ∈ base) →
      ((lefts.product (x :: base)).filter fun pair =>
          decide (pair ∈ (x :: base).consecutivePairs)) =
        ((lefts.product base).filter fun pair =>
          decide (pair ∈ base.consecutivePairs))
  | _base, [], _hx, _hLefts => by
      rfl
  | base, a :: lefts, hx, hLefts => by
      have haBase : a ∈ base := hLefts a (by simp)
      have hLeftsTail : ∀ b, b ∈ lefts → b ∈ base := by
        intro b hb
        exact hLefts b (by simp [hb])
      have haNeX : a ≠ x := by
        intro h
        exact hx (by simpa [h] using haBase)
      have hDropAX :
          decide ((a, x) ∈ (x :: base).consecutivePairs) = false := by
        apply decide_eq_false
        intro h
        cases base with
        | nil =>
            simp at haBase
        | cons b bs =>
            simp [List.consecutivePairs] at h
            rcases h with h | h
            · exact hx (by simp [h.2])
            · exact not_mem_consecutivePairs_right_of_not_mem hx h
      have hReduceRow :
          ∀ z ∈ base,
            decide ((a, z) ∈ (x :: base).consecutivePairs) =
              decide ((a, z) ∈ base.consecutivePairs) := by
        intro z hz
        have hiff :
            (a, z) ∈ (x :: base).consecutivePairs ↔
              (a, z) ∈ base.consecutivePairs := by
          constructor
          · intro h
            cases base with
            | nil =>
                simp at hz
            | cons b bs =>
                simp [List.consecutivePairs] at h
                rcases h with h | h
                · exact False.elim (haNeX h.1)
                · exact h
          · intro h
            cases base with
            | nil =>
                simp at h
            | cons b bs =>
                right
                simpa [List.consecutivePairs] using h
        by_cases hp : (a, z) ∈ (x :: base).consecutivePairs
        · have hq : (a, z) ∈ base.consecutivePairs := hiff.mp hp
          simp [hp, hq]
        · have hq : (a, z) ∉ base.consecutivePairs := by
            intro h
            exact hp (hiff.mpr h)
          simp [hp, hq]
      have hRow :
          ((List.map (fun z => (a, z)) (x :: base)).filter fun pair =>
              decide (pair ∈ (x :: base).consecutivePairs)) =
            ((List.map (fun z => (a, z)) base).filter fun pair =>
              decide (pair ∈ base.consecutivePairs)) := by
        simp [hDropAX]
        apply List.filter_congr
        intro pair hpair
        rcases List.mem_map.mp (by simpa using hpair) with ⟨z, hz, rfl⟩
        exact hReduceRow z hz
      calc
        (((a :: lefts).product (x :: base)).filter fun pair =>
            decide (pair ∈ (x :: base).consecutivePairs))
            =
          ((List.map (fun z => (a, z)) (x :: base)).filter fun pair =>
              decide (pair ∈ (x :: base).consecutivePairs)) ++
            ((lefts.product (x :: base)).filter fun pair =>
              decide (pair ∈ (x :: base).consecutivePairs)) := by
            rw [show (a :: lefts).product (x :: base) =
                List.map (fun z => (a, z)) (x :: base) ++
                  lefts.product (x :: base) by rfl, List.filter_append]
        _ =
          ((List.map (fun z => (a, z)) base).filter fun pair =>
              decide (pair ∈ base.consecutivePairs)) ++
            ((lefts.product base).filter fun pair =>
              decide (pair ∈ base.consecutivePairs)) := by
            rw [hRow,
              list_product_filter_consecutivePairs_drop_right_head
                x base lefts hx hLeftsTail]
        _ =
          (((a :: lefts).product base).filter fun pair =>
            decide (pair ∈ base.consecutivePairs)) := by
            rw [show (a :: lefts).product base =
                List.map (fun z => (a, z)) base ++ lefts.product base by rfl,
              List.filter_append]

theorem list_product_filter_consecutivePairs_eq
    {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] :
    ∀ (xs : List α), xs.Nodup →
      ((xs.product xs).filter fun pair => decide (pair ∈ xs.consecutivePairs)) =
        xs.consecutivePairs
  | [], _ => by
      simp [List.consecutivePairs]
  | [x], _ => by
      simp [List.consecutivePairs]
  | x :: y :: ys, hNodup => by
      have hxNotTail : x ∉ y :: ys := (List.nodup_cons.mp hNodup).1
      have hTailNodup : (y :: ys).Nodup := (List.nodup_cons.mp hNodup).2
      have hyNotYs : y ∉ ys := (List.nodup_cons.mp hTailNodup).1
      have hyNeX : y ≠ x := by
        intro h
        exact hxNotTail (by simp [h])
      have hXX :
          decide ((x, x) ∈ (x :: y :: ys).consecutivePairs) = false := by
        apply decide_eq_false
        intro h
        simp [List.consecutivePairs] at h
        rcases h with h | h
        · exact hxNotTail (by simp [h])
        · exact not_mem_consecutivePairs_left_of_not_mem hxNotTail h
      have hXY :
          decide ((x, y) ∈ (x :: y :: ys).consecutivePairs) = true := by
        simp [List.consecutivePairs]
      have hTailRow :
          ((List.map (fun z => (x, z)) ys).filter fun pair =>
              decide (pair ∈ (x :: y :: ys).consecutivePairs)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro pair hpair
        rcases List.mem_map.mp hpair with ⟨z, hz, rfl⟩
        intro hTrue
        have h : (x, z) ∈ (x :: y :: ys).consecutivePairs :=
          of_decide_eq_true hTrue
        simp [List.consecutivePairs] at h
        rcases h with h | h
        · exact hyNotYs (by simpa [h] using hz)
        · exact not_mem_consecutivePairs_left_of_not_mem hxNotTail h
      have hHeadRow :
          ((List.map (fun z => (x, z)) (x :: y :: ys)).filter fun pair =>
              decide (pair ∈ (x :: y :: ys).consecutivePairs)) = [(x, y)] := by
        simp [hXX, hXY, hTailRow]
      calc
        (((x :: y :: ys).product (x :: y :: ys)).filter fun pair =>
            decide (pair ∈ (x :: y :: ys).consecutivePairs))
            =
          ((List.map (fun z => (x, z)) (x :: y :: ys)).filter fun pair =>
              decide (pair ∈ (x :: y :: ys).consecutivePairs)) ++
            (((y :: ys).product (x :: y :: ys)).filter fun pair =>
              decide (pair ∈ (x :: y :: ys).consecutivePairs)) := by
            rw [show (x :: y :: ys).product (x :: y :: ys) =
                List.map (fun z => (x, z)) (x :: y :: ys) ++
                  (y :: ys).product (x :: y :: ys) by rfl, List.filter_append]
        _ =
          [(x, y)] ++
            (((y :: ys).product (y :: ys)).filter fun pair =>
              decide (pair ∈ (y :: ys).consecutivePairs)) := by
            rw [hHeadRow,
              list_product_filter_consecutivePairs_drop_right_head
                x (y :: ys) (y :: ys) hxNotTail (by intro a ha; exact ha)]
        _ =
          (x, y) :: (y :: ys).consecutivePairs := by
            rw [list_product_filter_consecutivePairs_eq (y :: ys) hTailNodup]
            rfl
        _ =
          (x :: y :: ys).consecutivePairs := by
            rfl

theorem dhcChainArcsFromSourceConsecutiveBlocks_append
    (budget : Nat) (source xs ys : List (Nat × Nat))
    (hBoundary :
      ∀ a b, a ∈ xs.getLast? → b ∈ ys.head? → a.1 ≠ b.1) :
    dhcChainArcsFromSourceConsecutiveBlocks budget source (xs ++ ys) =
      dhcChainArcsFromSourceConsecutiveBlocks budget source xs ++
        dhcChainArcsFromSourceConsecutiveBlocks budget source ys := by
  induction xs with
  | nil =>
      simp [dhcChainArcsFromSourceConsecutiveBlocks]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              simp [dhcChainArcsFromSourceConsecutiveBlocks]
          | cons y ys =>
              have hxy : x.1 ≠ y.1 := hBoundary x y (by simp) (by simp)
              simp [dhcChainArcsFromSourceConsecutiveBlocks, List.consecutivePairs, hxy]
      | cons y xs =>
          have hTailBoundary :
              ∀ a b, a ∈ (y :: xs).getLast? → b ∈ ys.head? → a.1 ≠ b.1 := by
            intro a b ha hb
            exact hBoundary a b (by simpa using ha) hb
          have hTail :=
            ih hTailBoundary
          change
            (if decide (x.1 = y.1) then
                dhcChainArcPairBlockFromSourceList budget source (x, y)
              else []) ++
                dhcChainArcsFromSourceConsecutiveBlocks budget source ((y :: xs) ++ ys) =
              ((if decide (x.1 = y.1) then
                  dhcChainArcPairBlockFromSourceList budget source (x, y)
                else []) ++
                  dhcChainArcsFromSourceConsecutiveBlocks budget source (y :: xs)) ++
                dhcChainArcsFromSourceConsecutiveBlocks budget source ys
          rw [hTail, List.append_assoc]

theorem dhcChainArcsFromSourceConsecutiveBlocks_eq_row
    (budget : Nat) (source xs : List (Nat × Nat)) (u : Nat)
    (hRows : ∀ ui, ui ∈ xs → ui.1 = u) :
    dhcChainArcsFromSourceConsecutiveBlocks budget source xs =
      dhcChainArcsForRowSourceBlocks budget source xs := by
  unfold dhcChainArcsFromSourceConsecutiveBlocks dhcChainArcsForRowSourceBlocks
  apply congrArg List.flatten
  apply List.map_congr_left
  intro pair hPair
  have hLeft : pair.1 ∈ xs := left_mem_of_mem_consecutivePairs hPair
  have hRight : pair.2 ∈ xs := right_mem_of_mem_consecutivePairs hPair
  have hSame : pair.1.1 = pair.2.1 := by
    exact (hRows pair.1 hLeft).trans (hRows pair.2 hRight).symm
  simp [hSame]

theorem no_snd_between_of_mem_consecutivePairs
    {xs : List (Nat × Nat)}
    (hPair : xs.Pairwise fun a b => a.2 < b.2)
    {a b c : Nat × Nat}
    (hpair : (a, b) ∈ xs.consecutivePairs) (hc : c ∈ xs)
    (hac : a.2 < c.2) (hcb : c.2 < b.2) : False := by
  induction xs with
  | nil =>
      simp [List.consecutivePairs] at hpair
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [List.consecutivePairs] at hpair
      | cons y ys =>
          cases hPair with
          | cons hHead hTail =>
              simp [List.consecutivePairs] at hpair
              rcases hpair with hxy | htail
              · rcases hxy with ⟨rfl, rfl⟩
                simp at hc
                rcases hc with rfl | hc
                · omega
                · rcases hc with rfl | hcys
                  · omega
                  · have hyc : b.2 < c.2 := hTail.rel_head_tail hcys
                    omega
              · simp at hc
                rcases hc with rfl | hcTail
                · have haTail : a ∈ _ := left_mem_of_mem_consecutivePairs htail
                  have hxa := hHead a haTail
                  omega
                · have hcTail' : c ∈ y :: ys := by simpa using hcTail
                  exact ih hTail htail hcTail'

theorem mem_consecutivePairs_of_snd_no_between
    {xs : List (Nat × Nat)}
    (hPair : xs.Pairwise fun a b => a.2 < b.2)
    {a b : Nat × Nat} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a.2 < b.2)
    (hNo : ∀ c, c ∈ xs → a.2 < c.2 → c.2 < b.2 → False) :
    (a, b) ∈ xs.consecutivePairs := by
  induction xs with
  | nil =>
      simp at ha
  | cons x xs ih =>
      cases hPair with
      | cons hHead hTail =>
          simp at ha hb
          rcases ha with hax | haTail
          · subst a
            rcases hb with hbx | hbTail
            · subst b
              omega
            · cases xs with
              | nil =>
                  simp at hbTail
              | cons y ys =>
                  simp at hbTail
                  rcases hbTail with hby | hbYs
                  · subst b
                    simp [List.consecutivePairs]
                  · have hxy : x.2 < y.2 := by
                      cases hTail with
                      | cons hYHead hYs =>
                          exact hHead y (by simp)
                    have hyb : y.2 < b.2 := by
                      cases hTail with
                      | cons hYHead hYs =>
                          exact hYHead b hbYs
                    exact False.elim (hNo y (by simp) hxy hyb)
          · rcases hb with hbx | hbTail
            · subst b
              have hxa : x.2 < a.2 := hHead a haTail
              omega
            · have hNoTail :
                  ∀ c, c ∈ xs → a.2 < c.2 → c.2 < b.2 → False := by
                intro c hc
                exact hNo c (by simp [hc])
              have hTailPair := ih hTail haTail hbTail hNoTail
              cases xs with
              | nil =>
                  simp at haTail
              | cons y ys =>
                  right
                  simpa [List.consecutivePairs] using hTailPair

theorem consecutiveIncident_iff_mem_incidencesOfVertex_consecutivePairs
    (I : VertexCoverInput) (u i j : Nat) :
    ConsecutiveIncident I u i j ↔
      ((u, i), (u, j)) ∈ (incidencesOfVertex I u).consecutivePairs := by
  constructor
  · intro hConsec
    have hi : (u, i) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, i)).2 hConsec.1)
    have hj : (u, j) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, j)).2 hConsec.2.1)
    refine mem_consecutivePairs_of_snd_no_between
      (incidencesOfVertex_pairwise_edge_lt I u) hi hj hConsec.2.2.1 ?_
    intro c hc hict hcjt
    have hcData := (mem_incidencesOfVertex_iff I u c).1 hc
    rcases c with ⟨v, h⟩
    have hvu : v = u := by simpa using hcData.2
    subst v
    exact hConsec.2.2.2 h hict hcjt ((mem_sourceIncidences_iff I (u, h)).1 hcData.1)
  · intro hpair
    have hiMem : (u, i) ∈ incidencesOfVertex I u :=
      left_mem_of_mem_consecutivePairs hpair
    have hjMem : (u, j) ∈ incidencesOfVertex I u :=
      right_mem_of_mem_consecutivePairs hpair
    have hiSource : SourceIncidentAt I u i :=
      (mem_sourceIncidences_iff I (u, i)).1
        ((mem_incidencesOfVertex_iff I u (u, i)).1 hiMem).1
    have hjSource : SourceIncidentAt I u j :=
      (mem_sourceIncidences_iff I (u, j)).1
        ((mem_incidencesOfVertex_iff I u (u, j)).1 hjMem).1
    have hij : i < j := edgeIndex_lt_of_mem_incidencesOfVertex_consecutivePairs hpair
    refine ⟨hiSource, hjSource, hij, ?_⟩
    intro h hih hhj hSource
    have hhMem : (u, h) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, h)).2 hSource)
    exact no_snd_between_of_mem_consecutivePairs
      (incidencesOfVertex_pairwise_edge_lt I u) hpair hhMem hih hhj

noncomputable def dhcChainArcsFromSourceProductRow
    (I : VertexCoverInput) (source : List (Nat × Nat)) (u : Nat) : List (Nat × Nat) := by
  classical
  exact ((((incidencesOfVertex I u).product (incidencesOfVertex I u)).filter fun pair =>
        decide (pair.1.1 = pair.2.1 ∧
          ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map fun pair =>
        (dhcIncidenceVertexFromSourceList I.k source pair.1 1,
          dhcIncidenceVertexFromSourceList I.k source pair.2 0))

theorem dhcChainArcsFromSourceProductRow_eq_row
    (I : VertexCoverInput) (source : List (Nat × Nat)) (u : Nat) :
    dhcChainArcsFromSourceProductRow I source u =
      dhcChainArcsForRowSourceBlocks I.k source (incidencesOfVertex I u) := by
  classical
  let row := incidencesOfVertex I u
  have hFilter :
      (((row.product row).filter fun pair =>
          decide (pair.1.1 = pair.2.1 ∧
            ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2))) =
        ((row.product row).filter fun pair =>
          decide (pair ∈ row.consecutivePairs)) := by
    apply List.filter_congr
    intro pair hpair
    rcases pair with ⟨left, right⟩
    rcases List.mem_product.mp hpair with ⟨hLeftMem, hRightMem⟩
    have hLeftVertex : left.1 = u :=
      ((mem_incidencesOfVertex_iff I u left).1 hLeftMem).2
    have hRightVertex : right.1 = u :=
      ((mem_incidencesOfVertex_iff I u right).1 hRightMem).2
    have hLeftEq : left = (u, left.2) := Prod.ext hLeftVertex rfl
    have hRightEq : right = (u, right.2) := Prod.ext hRightVertex rfl
    have hiff :
        (left.1 = right.1 ∧
            ConsecutiveIncident I left.1 left.2 right.2) ↔
          (left, right) ∈ row.consecutivePairs := by
      constructor
      · intro h
        have hConsec : ConsecutiveIncident I u left.2 right.2 := by
          exact hLeftVertex ▸ h.2
        rw [hLeftEq, hRightEq]
        simpa [row] using
          (consecutiveIncident_iff_mem_incidencesOfVertex_consecutivePairs
            I u left.2 right.2).1 hConsec
      · intro h
        have hPair :
            ((u, left.2), (u, right.2)) ∈
              (incidencesOfVertex I u).consecutivePairs := by
          rw [hLeftEq, hRightEq] at h
          simpa [row] using h
        have hConsec :
            ConsecutiveIncident I u left.2 right.2 :=
          (consecutiveIncident_iff_mem_incidencesOfVertex_consecutivePairs
            I u left.2 right.2).2 hPair
        exact ⟨hLeftVertex.trans hRightVertex.symm, by simpa [hLeftVertex] using hConsec⟩
    by_cases hPred :
        left.1 = right.1 ∧ ConsecutiveIncident I left.1 left.2 right.2
    · have hPair : (left, right) ∈ row.consecutivePairs := hiff.mp hPred
      have hDecPred :
          decide (left.1 = right.1 ∧
            ConsecutiveIncident I left.1 left.2 right.2) = true :=
        decide_eq_true hPred
      have hDecPair : decide ((left, right) ∈ row.consecutivePairs) = true :=
        decide_eq_true hPair
      simp [hDecPred, hDecPair]
    · have hPair : (left, right) ∉ row.consecutivePairs := by
        intro h
        exact hPred (hiff.mpr h)
      have hDecPred :
          decide (left.1 = right.1 ∧
            ConsecutiveIncident I left.1 left.2 right.2) = false :=
        decide_eq_false hPred
      have hDecPair : decide ((left, right) ∈ row.consecutivePairs) = false :=
        decide_eq_false hPair
      simp [hDecPred, hDecPair]
  let f : ((Nat × Nat) × (Nat × Nat)) → Nat × Nat := fun pair =>
    (dhcIncidenceVertexFromSourceList I.k source pair.1 1,
      dhcIncidenceVertexFromSourceList I.k source pair.2 0)
  calc
    dhcChainArcsFromSourceProductRow I source u
        =
      ((row.product row).filter fun pair =>
        decide (pair ∈ row.consecutivePairs)).map f := by
        rw [dhcChainArcsFromSourceProductRow]
        change
          ((row.product row).filter fun pair =>
            decide (pair.1.1 = pair.2.1 ∧
              ConsecutiveIncident I pair.1.1 pair.1.2 pair.2.2)).map f =
            ((row.product row).filter fun pair =>
              decide (pair ∈ row.consecutivePairs)).map f
        rw [hFilter]
    _ =
      row.consecutivePairs.map f := by
        simpa using congrArg (fun xs => xs.map f)
          (list_product_filter_consecutivePairs_eq row (incidencesOfVertex_nodup I u))
    _ =
      dhcChainArcsForRowSourceBlocks I.k source (incidencesOfVertex I u) := by
        simp [f, row, dhcChainArcsForRowSourceBlocks, dhcChainArcPairBlockFromSourceList]

theorem dhcChainArcsFromSourceConsecutiveBlocks_flatMap
    (budget : Nat) (source : List (Nat × Nat)) (us : List Nat)
    (rows : Nat → List (Nat × Nat)) (hNodup : us.Nodup)
    (hRows : ∀ u ui, ui ∈ rows u → ui.1 = u) :
    dhcChainArcsFromSourceConsecutiveBlocks budget source (us.flatMap rows) =
      (us.map fun u => dhcChainArcsForRowSourceBlocks budget source (rows u)).flatten := by
  induction us with
  | nil =>
      simp [dhcChainArcsFromSourceConsecutiveBlocks, dhcChainArcsForRowSourceBlocks]
  | cons u us ih =>
      have huNot : u ∉ us := by
        exact (List.nodup_cons.mp hNodup).1
      have hTailNodup : us.Nodup := by
        exact (List.nodup_cons.mp hNodup).2
      have hBoundary :
          ∀ a b, a ∈ (rows u).getLast? → b ∈ (us.flatMap rows).head? → a.1 ≠ b.1 := by
        intro a b ha hb hEq
        have haMem : a ∈ rows u := by
          rcases List.mem_getLast?_eq_getLast ha with ⟨hne, rfl⟩
          exact List.getLast_mem hne
        have hbMemFlat : b ∈ us.flatMap rows := by
          cases hHead : (us.flatMap rows).head? with
          | none =>
              simp [hHead] at hb
          | some z =>
              have hzb : z = b := by simpa [hHead] using hb
              simpa [hzb] using mem_of_head?_eq_some hHead
        rcases List.mem_flatMap.mp hbMemFlat with ⟨v, hvUs, hbRow⟩
        have haFirst : a.1 = u := hRows u a haMem
        have hbFirst : b.1 = v := hRows v b hbRow
        have huv : u = v := by
          exact haFirst.symm.trans (hEq.trans hbFirst)
        exact huNot (huv ▸ hvUs)
      calc
        dhcChainArcsFromSourceConsecutiveBlocks budget source ((u :: us).flatMap rows)
            =
          dhcChainArcsFromSourceConsecutiveBlocks budget source (rows u) ++
            dhcChainArcsFromSourceConsecutiveBlocks budget source (us.flatMap rows) := by
            simpa using
              dhcChainArcsFromSourceConsecutiveBlocks_append
                budget source (rows u) (us.flatMap rows) hBoundary
        _ =
          dhcChainArcsForRowSourceBlocks budget source (rows u) ++
            (us.map fun u => dhcChainArcsForRowSourceBlocks budget source (rows u)).flatten := by
            rw [ih hTailNodup]
            rw [dhcChainArcsFromSourceConsecutiveBlocks_eq_row budget source (rows u) u
              (hRows u)]
        _ =
          ((u :: us).map fun u =>
            dhcChainArcsForRowSourceBlocks budget source (rows u)).flatten := by
            rfl

theorem dhcChainArcsFromAdjacentIndexed_zipIdx_eq_sourceConsecutive
    (budget : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup) :
    dhcChainArcsFromAdjacentIndexed budget source.zipIdx =
      dhcChainArcsFromSourceConsecutiveBlocks budget source source := by
  rw [dhcChainArcsFromAdjacentIndexed_eq_consecutivePairs]
  have hBlock :
      (source.zipIdx.consecutivePairs.map fun pair =>
          dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten =
        (source.zipIdx.consecutivePairs.map fun pair =>
          if decide (pair.1.1.1 = pair.2.1.1) then
            dhcChainArcPairBlockFromSourceList budget source (pair.1.1, pair.2.1)
          else []).flatten := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro pair hPair
    have hLeft : pair.1 ∈ source.zipIdx := left_mem_of_mem_consecutivePairs hPair
    have hRight : pair.2 ∈ source.zipIdx := right_mem_of_mem_consecutivePairs hPair
    simpa using
      dhcChainArcBlockFromIndexed_eq_sourceListBlock_of_zipIdx_mem
        budget source hNodup hLeft hRight
  calc
    (source.zipIdx.consecutivePairs.map fun pair =>
        dhcChainArcBlockFromIndexed (budget, (true, pair))).flatten
        =
      (source.zipIdx.consecutivePairs.map fun pair =>
        if decide (pair.1.1.1 = pair.2.1.1) then
          dhcChainArcPairBlockFromSourceList budget source (pair.1.1, pair.2.1)
        else []).flatten := hBlock
    _ =
      dhcChainArcsFromSourceConsecutiveBlocks budget source source := by
        simpa [dhcChainArcsFromSourceConsecutiveBlocks] using
          list_flatten_consecutivePairs_map_fst (source.zipIdx)
            (fun pair : (Nat × Nat) × (Nat × Nat) =>
              if decide (pair.1.1 = pair.2.1) then
                dhcChainArcPairBlockFromSourceList budget source pair
              else [])

theorem dhcChainArcsExecutableFromInput_eq_textbookTrackChainArcs
    (I : VertexCoverInput) :
    dhcChainArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookTrackChainArcs I := by
  rw [dhcChainArcsExecutableFromIndexed_eq_adjacent]
  rw [dhcIndexedSourceIncidencesFromInput,
    dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]
  rw [dhcChainArcsFromAdjacentIndexed_zipIdx_eq_sourceConsecutive I.k
    (sourceIncidences I) (sourceIncidences_nodup I)]
  conv_lhs =>
    arg 3
    rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
  rw [dhcChainArcsFromSourceConsecutiveBlocks_flatMap I.k (sourceIncidences I)
    (List.range I.graph.vertices) (fun u => incidencesOfVertex I u)
    (List.nodup_range (n := I.graph.vertices))]
  · simp [textbookTrackChainArcs, textbookTrackChainArcsForVertex,
      dhcChainArcsForRowSourceBlocks, dhcChainArcPairBlockFromSourceList,
      dhcIncidenceVertexFromSourceIncidences_eq_textbook]
  · intro u ui hui
    exact ((mem_incidencesOfVertex_iff I u ui).1 hui).2

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
