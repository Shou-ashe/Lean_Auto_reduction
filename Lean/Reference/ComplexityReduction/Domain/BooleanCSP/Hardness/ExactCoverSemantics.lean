/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Hardness.ExactCoverToOneInThree

/-!
Exact-cover semantics of the 1-in-3 executable: the forward and reverse
directions of the many-one reduction `ExactCover ≤ₘ 1-in-3-SAT`.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace Hardness
namespace ExactCoverToOneInThree

open ComplexityReduction.CSP
open ComplexityReduction.Combinatorics

/-! ### The block-variable characterization -/

/-- The non-index variables of a block are auxiliary keys of its element. -/
theorem block_vars_aux (setsLength element level : Nat) (xs : List Nat)
    (hsmall : ∀ x ∈ xs, x < setsLength) :
    ∀ d ∈ exactlyOneBlock setsLength element level (blockChain setsLength element level) xs, ∀ i,
    d.vars i < setsLength ∨ ∃ position, d.vars i = auxiliaryVar setsLength element position := by
  induction xs generalizing level with
  | nil =>
      intro d dMember i
      rcases List.mem_cons.mp dMember with rfl | h'
      · fin_cases i
        · right
          exact ⟨5 * level + 4, rfl⟩
        · right
          exact ⟨5 * level, rfl⟩
        · right
          exact ⟨5 * level, rfl⟩
      · cases h'
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro d dMember i
          rcases List.mem_cons.mp dMember with rfl | h'
          · fin_cases i
            · right
              exact ⟨5 * level + 4, rfl⟩
            · left
              exact hsmall x (by simp)
            · right
              exact ⟨5 * level, rfl⟩
          · rcases List.mem_cons.mp h' with rfl | h''
            · fin_cases i
              · right
                exact ⟨5 * level + 1, rfl⟩
              · right
                exact ⟨5 * level, rfl⟩
              · right
                exact ⟨5 * level, rfl⟩
            · cases h''
      | cons y rest =>
          intro d dMember i
          rcases List.mem_append.mp dMember with inHead | inTail
          · rcases List.mem_cons.mp inHead with rfl | h2
            · fin_cases i
              · right
                exact ⟨5 * level + 4, rfl⟩
              · left
                exact hsmall x (by simp)
              · right
                exact ⟨5 * level, rfl⟩
            · rcases List.mem_cons.mp h2 with rfl | h3
              · fin_cases i
                · right
                  exact ⟨5 * level, rfl⟩
                · right
                  exact ⟨5 * (level + 1) + 4, rfl⟩
                · right
                  exact ⟨5 * level + 2, rfl⟩
              · rcases List.mem_cons.mp h3 with rfl | h4
                · fin_cases i
                  · right
                    exact ⟨5 * level + 3, rfl⟩
                  · right
                    exact ⟨5 * level + 2, rfl⟩
                  · right
                    exact ⟨5 * level + 2, rfl⟩
                · cases h4
          · exact ih (level + 1) (fun v hv => hsmall v (by simp [hv])) d inTail i

/-! ### List helpers -/

/-- Zip membership in position form. -/
theorem mem_zip' {α β : Type} [Inhabited β] (l₁ : List α) (l₂ : List β) (aa : α) (bb : β)
    (hLen : l₁.length = l₂.length) :
    (aa, bb) ∈ l₁.zip l₂ ↔ ∃ i, ∃ hi : i < l₁.length, l₁[i] = aa ∧ l₂.getD i default = bb := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp
      | cons y ys => simp at hLen
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at hLen
      | cons y ys =>
          rw [List.zip_cons_cons]
          constructor
          · intro h
            rw [List.mem_cons] at h
            rcases h with hHead | hTail
            · exact ⟨0, ⟨Nat.zero_lt_succ _, (congrArg Prod.fst hHead).symm,
                (congrArg Prod.snd hHead).symm⟩⟩
            · rcases (ih ys (by simpa using hLen)).1 hTail with ⟨i, hi, hx, hy⟩
              have hLen' : xs.length = ys.length := by simpa using hLen
              exact ⟨i + 1, ⟨by
                have h1 : i + 1 < xs.length + 1 := Nat.succ_lt_succ hi
                simpa [hLen'] using h1, by simpa using hx, by simpa using hy⟩⟩
          · rintro ⟨i, hi, hx, hy⟩
            cases i with
            | zero =>
                rw [List.mem_cons]
                left
                exact Prod.ext (by simpa using hx.symm) (by simpa using hy.symm)
            | succ i' =>
                rw [List.mem_cons]
                right
                have hLen' : xs.length = ys.length := by simpa using hLen
                exact (ih ys (by simpa using hLen)).2
                  ⟨i', Nat.lt_of_succ_lt_succ (by simpa using hi), by simpa using hx,
                    by simpa using hy⟩

/-- Zip-with-range membership. -/
theorem mem_zip_range (sets : List (List Nat)) (i : Nat) (S : List Nat) :
    (i, S) ∈ (List.range sets.length).zip sets ↔ ∃ hi : i < sets.length, sets[i] = S := by
  have h := mem_zip' (List.range sets.length) sets i S (List.length_range (n := sets.length))
  rw [h]
  constructor
  · rintro ⟨j, hj, hri, hsi⟩
    have hji : j = i := by
      rw [List.getElem_range (by simpa [List.length_range] using hj)] at hri
      exact hri
    refine ⟨by
      have hj' : j < sets.length := by simpa [List.length_range] using hj
      omega, ?_⟩
    cases hji
    rw [List.getD_eq_getElem sets default (by simpa [List.length_range] using hj)] at hsi
    exact hsi
  · rintro ⟨hi, hEq⟩
    refine ⟨i, ⟨by simpa [List.length_range] using hi, ?_, ?_⟩⟩
    · exact List.getElem_range (by simpa [List.length_range] using hi)
    · rw [List.getD_eq_getElem sets default hi]
      exact hEq

/-- Membership in the index list of one element. -/
theorem indicesOf_mem_iff (sets : List (List Nat)) (element i : Nat) :
    i ∈ indicesOf sets element ↔ ∃ hi : i < sets.length, element ∈ sets[i] := by
  unfold indicesOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨entry, hEntry, hSome⟩
    rcases (mem_zip_range sets entry.1 entry.2).1 hEntry with ⟨hEntryIdx, hEqS'⟩
    have hSomeEq : element ∈ entry.2 := by
      by_cases hMem : element ∈ entry.2
      · exact hMem
      · have hSomeNone : (if element ∈ entry.2 then some entry.1 else none) = none := by
          simp [hMem]
        have hBad : none = some i := by simpa [hSomeNone] using hSome
        cases hBad
    have hii : entry.1 = i := by
      have hSome' : some entry.1 = some i := by simpa [hSomeEq] using hSome
      exact Option.some.inj hSome'
    refine ⟨by simpa [hii] using hEntryIdx, ?_⟩
    simpa [← hii, hEqS'] using hSomeEq
  · rintro ⟨hi, hElem⟩
    refine ⟨(i, sets[i]), ?_, ?_⟩
    · exact (mem_zip_range sets i (sets[i])).2 ⟨hi, rfl⟩
    · simp [hElem]

/-- Shifting the first coordinate of a zip by one. -/
theorem zip_map_shift (l : List Nat) (sets : List (List Nat)) :
    (l.map (· + 1)).zip sets = (l.zip sets).map fun p => (p.1 + 1, p.2) := by
  induction l generalizing sets with
  | nil => simp
  | cons a as ih =>
      cases sets with
      | nil => simp
      | cons S rest => simp [ih]

/-- Shifting a filterMap over shifted first coordinates. -/
theorem filterMap_map_shift (l : List (Nat × List Nat)) (element : Nat) :
    ((l.map fun p => (p.1 + 1, p.2)).filterMap fun entry =>
        if element ∈ entry.2 then some entry.1 else none) =
      ((l.filterMap fun entry => if element ∈ entry.2 then some entry.1 else none)).map (· + 1) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      cases p with
      | mk a b =>
          by_cases hMem : element ∈ b
          · simp [hMem, ih]
          · simp [hMem, ih]

/-- The index list of one element is nodup. -/
theorem indicesOf_nodup (sets : List (List Nat)) (element : Nat) :
    (indicesOf sets element).Nodup := by
  induction sets with
  | nil => simp [indicesOf]
  | cons S rest ih =>
      unfold indicesOf
      change (List.filterMap (fun entry =>
        if element ∈ entry.2 then some entry.1 else none)
          ((List.range (rest.length + 1)).zip (S :: rest))).Nodup
      rw [List.range_succ_eq_map, List.zip_cons_cons]
      by_cases hMem : element ∈ S
      · have hrewrite : (List.filterMap (fun entry =>
            if element ∈ entry.2 then some entry.1 else none)
              ((0, S) :: (List.map Nat.succ (List.range rest.length)).zip rest)) =
            (0 :: (indicesOf rest element).map (· + 1)) := by
          rw [List.filterMap_cons]
          rw [if_pos hMem]
          rw [zip_map_shift]
          rw [filterMap_map_shift]
          rw [indicesOf]
        rw [hrewrite]
        rw [List.nodup_cons]
        constructor
        · intro h0
          rcases List.mem_map.mp h0 with ⟨i, hi, hEq⟩
          have hbound : i < rest.length := ((indicesOf_mem_iff rest element i).1 hi).1
          have hEq' : i + 1 = 0 := by simpa using hEq
          exact (Nat.succ_ne_zero i) hEq'
        · exact ih.map (by intro a b ha; exact (Nat.succ.inj (by simpa using ha)))
      · have hrewrite : (List.filterMap (fun entry =>
            if element ∈ entry.2 then some entry.1 else none)
              ((0, S) :: (List.map Nat.succ (List.range rest.length)).zip rest)) =
            (indicesOf rest element).map (· + 1) := by
          rw [List.filterMap_cons]
          rw [if_neg hMem]
          rw [zip_map_shift]
          rw [filterMap_map_shift]
          rw [indicesOf]
        rw [hrewrite]
        exact ih.map (by intro a b ha; exact (Nat.succ.inj (by simpa using ha)))

/-- Filtering by a selector that marks exactly one nodup element gives the singleton. -/
theorem filter_eq_singleton {α : Type} [DecidableEq α] (l : List α) (sel : α → Bool) (i : α)
    (hNodup : l.Nodup) (hAll : ∀ j ∈ l, sel j = true → j = i) (hMem : i ∈ l)
    (hSelI : sel i = true) : l.filter sel = [i] := by
  induction l with
  | nil => cases hMem
  | cons x xs ih =>
      cases hsel : sel x with
      | true =>
          have hxi : x = i := hAll x (by simp) hsel
          rw [hxi] at hsel
          rw [hxi]
          simp [hsel]
          have hAllXs : ∀ j ∈ xs, sel j = true → j = i := by
            intro j hjm hjsel
            exact hAll j (by simp [hjm]) hjsel
          have hxNotIn : i ∉ xs := by
            intro hxIn
            have hxIn' : x ∈ xs := by
              rw [hxi]
              exact hxIn
            exact (List.nodup_cons.mp hNodup).1 hxIn'
          have hFilterNil : xs.filter sel = [] := by
            rw [List.filter_eq_nil_iff]
            intro j hjm hjsel
            have hji : j = i := hAllXs j hjm hjsel
            exact hxNotIn (by rw [← hji]; exact hjm)
          simpa using (List.filter_eq_nil_iff).1 hFilterNil
      | false =>
          have hAllXs : ∀ j ∈ xs, sel j = true → j = i := by
            intro j hjm hjsel
            exact hAll j (by simp [hjm]) hjsel
          have hix : i ≠ x := by
            intro hEq
            rw [hEq] at hSelI
            simp [hsel] at hSelI
          have hMemXs : i ∈ xs := by
            have hMem' := (List.mem_cons.mp hMem)
            exact hMem'.elim (fun hEq => False.elim (hix hEq)) id
          simp [hsel]
          exact ih (List.nodup_cons.mp hNodup).2 hAllXs hMemXs

/-- Filtering the image by the Boolean truth equals filtering by the selector. -/
theorem map_selection_filter_length {α : Type} (l : List α) (sel : α → Bool) :
    (List.filter (fun b => b) (List.map sel l)).length = (List.filter sel l).length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      cases h : sel a with
      | true => simp [h, ih]
      | false => simp [h, ih]

/-- The selected-set auxiliary computation. -/
def selectedAux (sets : List (List Nat)) (assignment : SAT.Assignment) (acc : Nat) :
    List (List Nat) :=
  match sets with
  | [] => []
  | S :: rest => (if assignment acc then [S] else []) ++ selectedAux rest assignment (acc + 1)

/-- The selected sets of one assignment. -/
def selectedSets (sets : List (List Nat)) (assignment : SAT.Assignment) : List (List Nat) :=
  selectedAux sets assignment 0

theorem selectedAux_mem (sets : List (List Nat)) (assignment : SAT.Assignment) (acc : Nat)
    (S : List Nat) :
    S ∈ selectedAux sets assignment acc ↔
      ∃ i, acc ≤ i ∧ i < acc + sets.length ∧ sets.getD (i - acc) [] = S ∧ assignment i = true := by
  induction sets generalizing acc with
  | nil =>
      simp [selectedAux]
      rintro x hle hlt _hEq
      omega
  | cons T rest ih =>
      unfold selectedAux
      by_cases hSel : assignment acc
      · simp [hSel, ih]
        constructor
        · rintro (hHead | hTail)
          · have hEqST : S = T := by simpa using hHead
            refine ⟨acc, by omega, by omega, ?_, hSel⟩
            rw [hEqST]
            rw [show acc - acc = 0 by omega]
            simp
          · rcases hTail with ⟨i, hle, hlt, hEq, hSel'⟩
            refine ⟨i, by omega, by omega, ?_, hSel'⟩
            rw [show i - acc = (i - (acc + 1)) + 1 by omega]
            simpa using hEq
        · rintro ⟨i, hle, hlt, hEq, hSel'⟩
          by_cases hEqAcc : i = acc
          · left
            rw [hEqAcc] at hEq
            have hT : (T :: rest).getD (acc - acc) [] = T := by
              rw [show acc - acc = 0 by omega]
              simp
            exact (hEq.symm.trans hT)
          · right
            refine ⟨i, by omega, by omega, ?_, hSel'⟩
            rw [show i - (acc + 1) = i - acc - 1 by omega]
            rw [show i - acc = (i - acc - 1) + 1 by omega] at hEq
            simpa [List.getD_cons_succ] using hEq
      · simp [hSel, ih]
        constructor
        · rintro ⟨i, hle, hlt, hEq, hSel'⟩
          refine ⟨i, by omega, by omega, ?_, hSel'⟩
          rw [show i - acc = (i - (acc + 1)) + 1 by omega]
          rw [show i - (acc + 1) = i - acc - 1 by omega] at hEq
          simpa [List.getD_cons_succ] using hEq
        · rintro ⟨i, hle, hlt, hEq, hSel'⟩
          have hne : i ≠ acc := by
            intro hEqAcc
            rw [hEqAcc] at hSel'
            exact hSel hSel'
          refine ⟨i, by omega, by omega, ?_, hSel'⟩
          rw [show i - (acc + 1) = i - acc - 1 by omega]
          rw [show i - acc = (i - acc - 1) + 1 by omega] at hEq
          simpa [List.getD_cons_succ] using hEq

theorem mem_selectedSets_iff (sets : List (List Nat)) (assignment : SAT.Assignment) (S : List Nat) :
    S ∈ selectedSets sets assignment ↔
      ∃ i, i < sets.length ∧ sets.getD i [] = S ∧ assignment i = true := by
  unfold selectedSets
  have h := selectedAux_mem sets assignment 0 S
  simpa using h

theorem selectedAux_mem_rest (sets : List (List Nat)) (assignment : SAT.Assignment) (acc : Nat) :
    ∀ S' ∈ selectedAux sets assignment acc, S' ∈ sets := by
  intro S' hS'
  induction sets generalizing acc with
  | nil => simp [selectedAux] at hS'
  | cons T rest ih =>
      unfold selectedAux at hS'
      by_cases hSel : assignment acc
      · rw [if_pos hSel, List.mem_append] at hS'
        rcases hS' with hHead | hTail
        · have hEq : S' = T := by simpa using hHead
          simp [hEq]
        · have hRest := ih _ hTail
          simp [hRest]
      · rw [if_neg hSel] at hS'
        have hRest := ih _ hS'
        simp [hRest]

theorem selectedAux_nodup (sets : List (List Nat)) (hNodup : sets.Nodup)
    (assignment : SAT.Assignment) (acc : Nat) :
    (selectedAux sets assignment acc).Nodup := by
  induction sets generalizing assignment acc with
  | nil => simp [selectedAux]
  | cons S rest ih =>
      unfold selectedAux
      by_cases hSel : assignment acc
      · rw [if_pos hSel]
        simp
        constructor
        · intro hMem
          have hSnot : S ∉ rest := (List.nodup_cons.mp hNodup).1
          exact hSnot (selectedAux_mem_rest rest assignment (acc + 1) S hMem)
        · exact ih (List.nodup_cons.mp hNodup).2 assignment (acc + 1)
      · rw [if_neg hSel]
        exact ih (List.nodup_cons.mp hNodup).2 assignment (acc + 1)

theorem selectedSets_nodup (sets : List (List Nat)) (hNodup : sets.Nodup)
    (assignment : SAT.Assignment) :
    (selectedSets sets assignment).Nodup := by
  simpa [selectedSets] using selectedAux_nodup sets hNodup assignment 0

/-- A length-one list is a singleton. -/
theorem length_eq_one' {α : Type} (l : List α) (h : l.length = 1) :
    ∃ a : α, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
      cases l' with
      | nil => exact ⟨a, rfl⟩
      | cons b l'' => simp at h

/-- Erased-duplicates lists are nodup. -/
theorem nodup_eraseDups' {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    (l.eraseDups).Nodup := by
  unfold List.eraseDups
  have hLoop : ∀ (as bs : List α), bs.Nodup →
      (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) as bs).Nodup := by
    intro as
    induction as with
    | nil =>
        intro bs hbs
        rw [List.eraseDupsBy.loop.eq_1]
        exact List.nodup_reverse.mpr hbs
    | cons a as' ih =>
        intro bs hbs
        rw [List.eraseDupsBy.loop.eq_2]
        cases hAnyBool : bs.any (fun x => a == x) with
        | true =>
            simp [hAnyBool]
            exact ih bs hbs
        | false =>
            simp [hAnyBool]
            have hnotMem : a ∉ bs := by
              intro hMem
              have hAnyTrue : bs.any (fun x => a == x) = true := by
                rw [List.any_eq_true]
                exact ⟨a, hMem, (beq_iff_eq).2 rfl⟩
              simp [hAnyTrue] at hAnyBool
            exact ih (a :: bs) (List.nodup_cons.mpr ⟨hnotMem, hbs⟩)
  exact hLoop l [] (by simp)

/-- Distinct indices of a nodup list have distinct elements. -/
theorem nodup_getElem_ne {α : Type} (l : List α) (h : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    l[i] = l[j] → i = j := by
  intro hEq
  induction l generalizing i j with
  | nil => cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j' =>
              have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
              have hxj : xs[j'] = x := by
                have hEq' : x = xs[j'] := by simpa using hEq
                exact hEq'.symm
              have hxMem : x ∈ xs := by
                simpa [hxj] using List.getElem_mem (n := j') hj'
              have hnx : x ∉ xs := by
                simpa using (List.nodup_cons.mp h).1
              exact False.elim (hnx hxMem)
      | succ i' =>
          cases j with
          | zero =>
              have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
              have hxi : xs[i'] = x := by
                simpa using hEq
              have hxMem : x ∈ xs := by
                simpa [hxi] using List.getElem_mem (n := i') hi'
              have hnx : x ∉ xs := by
                simpa using (List.nodup_cons.mp h).1
              exact False.elim (hnx hxMem)
          | succ j' =>
              have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
              have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
              have htail : xs[i'] = xs[j'] := by
                simpa using hEq
              have hRec := ih (List.nodup_cons.mp h).2 hi' hj' htail
              simp [hRec]

/-- The witness assignment of the whole formula from a set selection. -/
noncomputable def forwardAssignment (sets : List (List Nat)) (selection : SAT.Assignment) :
    SAT.Assignment :=
  fun var =>
    if h : var < sets.length then selection var
    else
      let key := var - sets.length - 1
      let element := (Nat.unpair key).1
      let position := (Nat.unpair key).2
      elementWitness sets.length element (indicesOf sets element) selection var

theorem forwardAssignment_auxiliaryVar (sets : List (List Nat)) (selection : SAT.Assignment)
    (element position : Nat) :
    forwardAssignment sets selection (auxiliaryVar sets.length element position) =
      elementWitness sets.length element (indicesOf sets element) selection
        (auxiliaryVar sets.length element position) := by
  unfold forwardAssignment
  rw [dif_neg (Nat.not_lt_of_ge (Nat.le_of_lt (setsLength_lt_auxiliaryVar _ _ _)))]
  have hkey : (auxiliaryVar sets.length element position) - sets.length - 1 =
      Nat.pair element position := by
    unfold auxiliaryVar
    omega
  simp [hkey, Nat.unpair_pair]

/-- Forward direction: an exact cover gives a satisfying assignment. -/
theorem executable_satisfies_forward (I : ExactCoverInput) :
    ExactCover I → Satisfiable (executable I) := by
  rintro ⟨wellFormed, selected, inFamily, nodup, disjoint, covers⟩
  rw [executable]
  rw [dif_pos wellFormed]
  let sets := I.system.sets.eraseDups
  let selection : SAT.Assignment := fun i => decide (sets.getD i [] ∈ selected)
  have coversExactly : ∀ element, element < I.system.universeSize →
      exactlyOneOf ((indicesOf sets element).map selection) := by
    intro element elementBelow
    have hcover := covers element elementBelow
    rcases hcover with ⟨S, SSelected, elementInS⟩
    have SInSets : S ∈ sets := List.mem_eraseDups.mpr (inFamily S SSelected)
    rcases List.mem_iff_getElem.mp SInSets with ⟨i, hi, hEqS⟩
    have selI : selection i = true := by
      unfold selection
      have hget : sets.getD i [] = sets[i] := List.getD_eq_getElem (l := sets) (d := []) hi
      rw [hget]
      simp [hEqS, SSelected]
    have iInIndices : i ∈ indicesOf sets element :=
      (indicesOf_mem_iff sets element i).2 ⟨hi, by simpa [hEqS] using elementInS⟩
    have hatMost : ∀ j, j ∈ indicesOf sets element → selection j = true → j = i := by
      intro j hj selJ
      have hj' := (indicesOf_mem_iff sets element j).1 hj
      by_contra hne
      have hjB : j < sets.length := hj'.1
      let sj : List Nat := sets[j]'(hjB)
      let si : List Nat := sets[i]'(hi)
      have hsetNe : sj ≠ si := by
        intro hEq
        apply hne
        exact nodup_getElem_ne sets (nodup_eraseDups' I.system.sets) hjB hi hEq
      have hselj : sj ∈ selected := by
        unfold selection at selJ
        rw [List.getD_eq_getElem (l := sets) (d := []) hj'.1] at selJ
        exact (of_decide_eq_true selJ)
      exact (disjoint sj hselj si (by simpa [si, hEqS] using SSelected) hsetNe element hj'.2
        (by simpa [si, hEqS] using elementInS))
    have hfilter : (indicesOf sets element).filter selection = [i] :=
      filter_eq_singleton (indicesOf sets element) selection i
        (indicesOf_nodup sets element) (hatMost) (iInIndices) (selI)
    unfold exactlyOneOf
    rw [map_selection_filter_length]
    rw [hfilter]
    rfl
  refine ⟨forwardAssignment sets selection, ?_⟩
  intro constraint constraintMember
  rcases List.mem_flatMap.mp constraintMember with ⟨element, elementMember, blockMember⟩
  have elementBelow : element < I.system.universeSize := List.mem_range.mp elementMember
  have hsmall : ∀ x ∈ indicesOf sets element, x < sets.length := by
    intro x hx
    exact ((indicesOf_mem_iff sets element x).1 hx).1
  have hwitness := elementBlock_witness_satisfies sets.length element (indicesOf sets element)
    selection hsmall (coversExactly element elementBelow)
  apply formula_satisfies_of_vars_agree
    (φ := elementBlock sets.length element (indicesOf sets element))
    (a := forwardAssignment sets selection)
    (b := elementWitness sets.length element (indicesOf sets element) selection)
  · intro d dMember i
    by_cases hsmallVar : d.vars i < sets.length
    · unfold forwardAssignment elementWitness
      rw [dif_pos hsmallVar]
      rw [if_neg]
      · change selection (d.vars i) =
            blockWitness sets.length element 0 (blockChain sets.length element 0)
              (indicesOf sets element) (fun var =>
                if var = blockChain sets.length element 0 then false else selection var)
              (d.vars i)
        rw [blockWitness_smallVar sets.length element 0
          (blockChain sets.length element 0) (indicesOf sets element)
          (fun var => if var = blockChain sets.length element 0 then false else selection var)
          hsmallVar]
        rw [if_neg]
        intro hEq
        dsimp only [blockChain, auxiliaryVar] at hEq
        omega
      · intro hEq
        dsimp only [elementPin, auxiliaryVar] at hEq
        omega
    · have haux : d.vars i < sets.length ∨ ∃ position,
          d.vars i = auxiliaryVar sets.length element position :=
        by
          have hd : d ∈ [oneInThreeConstraint
              (elementPin sets.length element (indicesOf sets element).length)
              (blockChain sets.length element 0) (blockChain sets.length element 0)] ++
            exactlyOneBlock sets.length element 0 (blockChain sets.length element 0)
              (indicesOf sets element) := by
            simpa [elementBlock] using dMember
          rcases List.mem_append.mp hd with hHead | hRest
          · rcases List.mem_cons.mp hHead with rfl | hEmpty
            · fin_cases i
              · right
                exact ⟨5 * (indicesOf sets element).length + 5, rfl⟩
              · right
                exact ⟨5 * 0 + 4, rfl⟩
              · right
                exact ⟨5 * 0 + 4, rfl⟩
            · cases hEmpty
          · exact block_vars_aux sets.length element 0 (indicesOf sets element) hsmall d hRest i
      have haux2 : ∃ position, d.vars i = auxiliaryVar sets.length element position :=
        haux.elim (fun hsmall' => False.elim (hsmallVar hsmall')) id
      rcases haux2 with ⟨position, hEq⟩
      rw [hEq]
      exact forwardAssignment_auxiliaryVar sets selection element position
  · exact hwitness
  · exact blockMember

/-- Reverse direction: a satisfying assignment selects an exact cover. -/
theorem executable_satisfies_reverse (I : ExactCoverInput) (wellFormed : SetSystemWellFormed I.system)
    {assignment : SAT.Assignment} (satisfies : Satisfies (executable I) assignment) :
    ExactCover I := by
  rw [executable, dif_pos wellFormed] at satisfies
  let sets := I.system.sets.eraseDups
  let selected := selectedSets sets assignment
  have hsatisfies : Satisfies
      ((List.range I.system.universeSize).flatMap fun element =>
        elementBlock sets.length element (indicesOf sets element)) assignment := by
    simpa [sets] using satisfies
  refine ⟨wellFormed, ⟨selected, ?_, ?_, ?_, ?_⟩⟩
  · intro S hS
    rcases (mem_selectedSets_iff sets assignment S).1 hS with ⟨i, hi, hEq, _hSel⟩
    rw [List.getD_eq_getElem sets [] hi] at hEq
    exact List.mem_eraseDups.mp (by
      rw [← hEq]
      exact List.getElem_mem (n := i) hi)
  · exact selectedSets_nodup sets (nodup_eraseDups' I.system.sets) assignment
  · intro A hA B hB hAB x hxA hxB
    rcases (mem_selectedSets_iff sets assignment A).1 hA with ⟨i, hi, hAi, hSelI⟩
    rw [List.getD_eq_getElem sets [] hi] at hAi
    rcases (mem_selectedSets_iff sets assignment B).1 hB with ⟨j, hj, hBj, hSelJ⟩
    rw [List.getD_eq_getElem sets [] hj] at hBj
    have hxBelow : x < I.system.universeSize := by
      have hAOrig : A ∈ I.system.sets := List.mem_eraseDups.mp (by
        rw [← hAi]
        exact List.getElem_mem (n := i) hi)
      exact wellFormed A hAOrig x hxA
    have hblock : CSP.Formula.Satisfies
        (elementBlock sets.length x (indicesOf sets x)) assignment := by
      intro constraint constraintMember
      exact hsatisfies constraint
        (List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hxBelow, constraintMember⟩)
    have hExactly := elementBlock_satisfies_of sets.length x (indicesOf sets x) assignment hblock
    have hlen := length_eq_one' ((indicesOf sets x).filter assignment) (by
      unfold exactlyOneOf at hExactly
      simpa [map_selection_filter_length] using hExactly)
    rcases hlen with ⟨a, hEq⟩
    have hiIdx : i ∈ indicesOf sets x := (indicesOf_mem_iff sets x i).2 ⟨hi, by
      rw [hAi]
      exact hxA⟩
    have hjIdx : j ∈ indicesOf sets x := (indicesOf_mem_iff sets x j).2 ⟨hj, by
      rw [hBj]
      exact hxB⟩
    have hmemI : i ∈ (indicesOf sets x).filter assignment := by
      rw [List.mem_filter]
      exact ⟨hiIdx, hSelI⟩
    have hmemJ : j ∈ (indicesOf sets x).filter assignment := by
      rw [List.mem_filter]
      exact ⟨hjIdx, hSelJ⟩
    rw [hEq] at hmemI hmemJ
    have hia : i = a := List.eq_of_mem_singleton hmemI
    have hja : j = a := List.eq_of_mem_singleton hmemJ
    have hij : i = j := hia.trans hja.symm
    have hAB' : A = B := by
      subst j
      rw [← hAi, ← hBj]
      rw [← List.getD_eq_getElem sets [] hi, ← List.getD_eq_getElem sets [] hj]
      exact congrArg (fun k => sets.getD k []) hij
    exact hAB hAB'
  · intro x hx
    have hblock : CSP.Formula.Satisfies
        (elementBlock sets.length x (indicesOf sets x)) assignment := by
      intro constraint constraintMember
      exact hsatisfies constraint
        (List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, constraintMember⟩)
    have hExactly := elementBlock_satisfies_of sets.length x (indicesOf sets x) assignment hblock
    have hlen := length_eq_one' ((indicesOf sets x).filter assignment) (by
      unfold exactlyOneOf at hExactly
      simpa [map_selection_filter_length] using hExactly)
    rcases hlen with ⟨i, hEq⟩
    have hiMem : i ∈ (indicesOf sets x).filter assignment := by
      rw [hEq]
      simp
    rw [List.mem_filter] at hiMem
    have hiIdx := (indicesOf_mem_iff sets x i).1 hiMem.1
    refine ⟨sets[i]'(hiIdx.1), ?_, ?_⟩
    · exact (mem_selectedSets_iff sets assignment (sets[i]'(hiIdx.1))).2
        ⟨i, hiIdx.1, by rw [List.getD_eq_getElem sets [] hiIdx.1], hiMem.2⟩
    · exact hiIdx.2

/-- The exact-cover-to-1-in-3 executable is a valid many-one reduction. -/
theorem executable_correct (I : ExactCoverInput) :
    Satisfiable (executable I) ↔ ExactCover I := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    by_cases wellFormed : SetSystemWellFormed I.system
    · exact executable_satisfies_reverse I wellFormed satisfies
    · rw [executable, dif_neg wellFormed] at satisfies
      exact False.elim (contradictionBlock_unsatisfiable I.system.sets.length assignment satisfies)
  · intro h
    exact executable_satisfies_forward I h

end ExactCoverToOneInThree
end Hardness
end BooleanCSP
end Domain
end ComplexityReduction
