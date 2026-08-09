/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.ChainProductSemantics

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Executable entry/exit arcs from indexed source-incidence boundaries -/

def dhcNextSelectorFromBudget (budget slot : Nat) : Nat :=
  if budget = 0 then 0 else (slot + 1) % budget

theorem dhcNextSelectorFromBudget_eq_textbookNextSelector
    (I : VertexCoverInput) (slot : Nat) :
    dhcNextSelectorFromBudget I.k slot = textbookNextSelector I slot := by
  rfl

def dhcEntryArcForSlotFromIndexedRaw
    (budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier) : Nat × Nat :=
  (textbookSelectorVertex slot,
    dhcIncidenceVertexCode (budget, (inc.2, (0 : Nat))))

def dhcExitArcForSlotFromIndexedRaw
    (budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier) : Nat × Nat :=
  (dhcIncidenceVertexCode (budget, (inc.2, (1 : Nat))),
    textbookSelectorVertex (dhcNextSelectorFromBudget budget slot))

def dhcEntryArcForSlotFromIndexedInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)

def dhcExitArcForSlotFromIndexedInputEncodedType : EncodedType :=
  dhcEntryArcForSlotFromIndexedInputEncodedType

abbrev dhcSlotIndexedIncidenceRaw :=
  Nat × (Nat × dhcIndexedIncidenceEncodedType.Carrier)

def dhcEntryArcForSlotFromIndexed
    (p : dhcSlotIndexedIncidenceRaw) : Nat × Nat :=
  dhcEntryArcForSlotFromIndexedRaw p.1 p.2.1 p.2.2

def dhcExitArcForSlotFromIndexed
    (p : dhcSlotIndexedIncidenceRaw) : Nat × Nat :=
  dhcExitArcForSlotFromIndexedRaw p.1 p.2.1 p.2.2

def dhcEntryArcForSlotBlockFromIndexed
    (budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier) :
    List (Nat × Nat) :=
  [dhcEntryArcForSlotFromIndexedRaw budget slot inc]

def dhcExitArcForSlotBlockFromIndexed
    (budget slot : Nat) (inc : dhcIndexedIncidenceEncodedType.Carrier) :
    List (Nat × Nat) :=
  [dhcExitArcForSlotFromIndexedRaw budget slot inc]

def dhcEntryArcForSlotSourceBlock
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (inc : Nat × Nat) :
    List (Nat × Nat) :=
  [(textbookSelectorVertex slot,
    dhcIncidenceVertexFromSourceList budget source inc 0)]

def dhcExitArcForSlotSourceBlock
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (inc : Nat × Nat) :
    List (Nat × Nat) :=
  [(dhcIncidenceVertexFromSourceList budget source inc 1,
    textbookSelectorVertex (dhcNextSelectorFromBudget budget slot))]

def dhcEntryArcsForSlotFromPrevSource
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (prev : Nat × Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest =>
      (if prev.1 = inc.1 then []
        else dhcEntryArcForSlotSourceBlock budget source slot inc) ++
        dhcEntryArcsForSlotFromPrevSource budget source slot inc rest

def dhcEntryArcsForSlotFromBoundarySource
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest =>
      dhcEntryArcForSlotSourceBlock budget source slot inc ++
        dhcEntryArcsForSlotFromPrevSource budget source slot inc rest

def dhcExitArcsForSlotFromPrevSource
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (prev : Nat × Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => dhcExitArcForSlotSourceBlock budget source slot prev
  | inc :: rest =>
      (if prev.1 = inc.1 then []
        else dhcExitArcForSlotSourceBlock budget source slot prev) ++
        dhcExitArcsForSlotFromPrevSource budget source slot inc rest

def dhcExitArcsForSlotFromBoundarySource
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) :
    List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest => dhcExitArcsForSlotFromPrevSource budget source slot inc rest

theorem dhcEntryArcForSlotFromIndexed_tm_polytime :
    TMPolyTimeMap dhcEntryArcForSlotFromIndexedInputEncodedType
      edgeStructuredEncodedType
      dhcEntryArcForSlotFromIndexed := by
  let X := dhcEntryArcForSlotFromIndexedInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcEntryArcForSlotFromIndexedInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcEntryArcForSlotFromIndexedInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hInc : TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd vertexPairEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInc
    simpa [Function.comp, dhcIndexedIncidenceEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hIdx hZero
  have hCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.2.2, (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hIdxBit
  have hCode := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hCodeInput
  have hSelector : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => textbookSelectorVertex p.2.1) := by
    simpa [textbookSelectorVertex] using hSlot
  have hOut := TMPolyTimeMap.prod_mk hSelector hCode
  simpa [dhcEntryArcForSlotFromIndexed, dhcEntryArcForSlotFromIndexedRaw,
    edgeStructuredEncodedType, X, dhcEntryArcForSlotFromIndexedInputEncodedType] using hOut

def dhcEntryArcsForSlotFromPrevIndexed
    (budget slot : Nat) (prev : (Nat × Nat) × Nat) :
    List ((Nat × Nat) × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest =>
      (if (prev.1.1 : Nat) = inc.1.1 then []
        else dhcEntryArcForSlotBlockFromIndexed budget slot inc) ++
        dhcEntryArcsForSlotFromPrevIndexed budget slot inc rest

def dhcEntryArcsForSlotFromBoundaryIndexed
    (budget slot : Nat) : List ((Nat × Nat) × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest =>
      dhcEntryArcForSlotBlockFromIndexed budget slot inc ++
        dhcEntryArcsForSlotFromPrevIndexed budget slot inc rest

def dhcEntryArcsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  ((List.range p.1).map fun slot =>
    dhcEntryArcsForSlotFromBoundaryIndexed p.1 slot p.2).flatten

def dhcExitArcsForSlotFromPrevIndexed
    (budget slot : Nat) (prev : (Nat × Nat) × Nat) :
    List ((Nat × Nat) × Nat) → List (Nat × Nat)
  | [] => dhcExitArcForSlotBlockFromIndexed budget slot prev
  | inc :: rest =>
      (if (prev.1.1 : Nat) = inc.1.1 then []
        else dhcExitArcForSlotBlockFromIndexed budget slot prev) ++
        dhcExitArcsForSlotFromPrevIndexed budget slot inc rest

def dhcExitArcsForSlotFromBoundaryIndexed
    (budget slot : Nat) : List ((Nat × Nat) × Nat) → List (Nat × Nat)
  | [] => []
  | inc :: rest => dhcExitArcsForSlotFromPrevIndexed budget slot inc rest

def dhcExitArcsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  ((List.range p.1).map fun slot =>
    dhcExitArcsForSlotFromBoundaryIndexed p.1 slot p.2).flatten

theorem dhcEntryArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    {inc : (Nat × Nat) × Nat} (hInc : inc ∈ source.zipIdx) :
    dhcEntryArcForSlotBlockFromIndexed budget slot inc =
      dhcEntryArcForSlotSourceBlock budget source slot inc.1 := by
  have hIdx : inc.2 = source.idxOf inc.1 :=
    dhcZipIdx_mem_idx_eq hNodup hInc
  simp [dhcEntryArcForSlotBlockFromIndexed, dhcEntryArcForSlotFromIndexedRaw,
    dhcEntryArcForSlotSourceBlock, dhcIncidenceVertexFromSourceList, hIdx]

theorem dhcExitArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    {inc : (Nat × Nat) × Nat} (hInc : inc ∈ source.zipIdx) :
    dhcExitArcForSlotBlockFromIndexed budget slot inc =
      dhcExitArcForSlotSourceBlock budget source slot inc.1 := by
  have hIdx : inc.2 = source.idxOf inc.1 :=
    dhcZipIdx_mem_idx_eq hNodup hInc
  simp [dhcExitArcForSlotBlockFromIndexed, dhcExitArcForSlotFromIndexedRaw,
    dhcExitArcForSlotSourceBlock, dhcIncidenceVertexFromSourceList, hIdx]

theorem dhcEntryArcsForSlotFromPrevIndexed_zipIdx_eq_source
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    (prev : (Nat × Nat) × Nat) (xs : List ((Nat × Nat) × Nat))
    (hPrev : prev ∈ source.zipIdx) (hXs : ∀ x, x ∈ xs → x ∈ source.zipIdx) :
    dhcEntryArcsForSlotFromPrevIndexed budget slot prev xs =
      dhcEntryArcsForSlotFromPrevSource budget source slot prev.1 (xs.map Prod.fst) := by
  induction xs generalizing prev with
  | nil =>
      rfl
  | cons inc rest ih =>
      have hInc : inc ∈ source.zipIdx := hXs inc (by simp)
      have hRest : ∀ x, x ∈ rest → x ∈ source.zipIdx := by
        intro x hx
        exact hXs x (by simp [hx])
      by_cases hSame : prev.1.1 = inc.1.1
      · simp [dhcEntryArcsForSlotFromPrevIndexed, dhcEntryArcsForSlotFromPrevSource,
          hSame, ih inc hInc hRest]
      · have hBlock :=
          dhcEntryArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
            budget slot source hNodup hInc
        simp [dhcEntryArcsForSlotFromPrevIndexed, dhcEntryArcsForSlotFromPrevSource,
          hSame, hBlock, ih inc hInc hRest]

theorem dhcExitArcsForSlotFromPrevIndexed_zipIdx_eq_source
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    (prev : (Nat × Nat) × Nat) (xs : List ((Nat × Nat) × Nat))
    (hPrev : prev ∈ source.zipIdx) (hXs : ∀ x, x ∈ xs → x ∈ source.zipIdx) :
    dhcExitArcsForSlotFromPrevIndexed budget slot prev xs =
      dhcExitArcsForSlotFromPrevSource budget source slot prev.1 (xs.map Prod.fst) := by
  induction xs generalizing prev with
  | nil =>
      exact dhcExitArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
        budget slot source hNodup hPrev
  | cons inc rest ih =>
      have hInc : inc ∈ source.zipIdx := hXs inc (by simp)
      have hRest : ∀ x, x ∈ rest → x ∈ source.zipIdx := by
        intro x hx
        exact hXs x (by simp [hx])
      by_cases hSame : prev.1.1 = inc.1.1
      · simp [dhcExitArcsForSlotFromPrevIndexed, dhcExitArcsForSlotFromPrevSource,
          hSame, ih inc hInc hRest]
      · have hBlock :=
          dhcExitArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
            budget slot source hNodup hPrev
        simp [dhcExitArcsForSlotFromPrevIndexed, dhcExitArcsForSlotFromPrevSource,
          hSame, hBlock, ih inc hInc hRest]

theorem dhcEntryArcsForSlotFromBoundaryIndexed_zipIdx_eq_source
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup) :
    dhcEntryArcsForSlotFromBoundaryIndexed budget slot source.zipIdx =
      dhcEntryArcsForSlotFromBoundarySource budget source slot source := by
  cases hZip : source.zipIdx with
  | nil =>
      have hSourceNil : source = [] := by
        simpa using congrArg (List.map Prod.fst) hZip
      simp [hSourceNil, dhcEntryArcsForSlotFromBoundaryIndexed,
        dhcEntryArcsForSlotFromBoundarySource]
  | cons inc rest =>
      have hInc : inc ∈ source.zipIdx := by simp [hZip]
      have hRest : ∀ x, x ∈ rest → x ∈ source.zipIdx := by
        intro x hx
        simp [hZip, hx]
      have hMap : source = inc.1 :: rest.map Prod.fst := by
        rw [← List.zipIdx_map_fst 0 source]
        simp [hZip]
      conv_rhs =>
        arg 4
        rw [hMap]
      simp [dhcEntryArcsForSlotFromBoundaryIndexed,
        dhcEntryArcsForSlotFromBoundarySource]
      rw [dhcEntryArcForSlotBlockFromIndexed_eq_sourceBlock_of_zipIdx_mem
        budget slot source hNodup hInc]
      rw [dhcEntryArcsForSlotFromPrevIndexed_zipIdx_eq_source
        budget slot source hNodup inc rest hInc hRest]

theorem dhcExitArcsForSlotFromBoundaryIndexed_zipIdx_eq_source
    (budget slot : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup) :
    dhcExitArcsForSlotFromBoundaryIndexed budget slot source.zipIdx =
      dhcExitArcsForSlotFromBoundarySource budget source slot source := by
  cases hZip : source.zipIdx with
  | nil =>
      have hSourceNil : source = [] := by
        simpa using congrArg (List.map Prod.fst) hZip
      simp [hSourceNil, dhcExitArcsForSlotFromBoundaryIndexed,
        dhcExitArcsForSlotFromBoundarySource]
  | cons inc rest =>
      have hInc : inc ∈ source.zipIdx := by simp [hZip]
      have hRest : ∀ x, x ∈ rest → x ∈ source.zipIdx := by
        intro x hx
        simp [hZip, hx]
      have hMap : source = inc.1 :: rest.map Prod.fst := by
        rw [← List.zipIdx_map_fst 0 source]
        simp [hZip]
      conv_rhs =>
        arg 4
        rw [hMap]
      simp [dhcExitArcsForSlotFromBoundaryIndexed,
        dhcExitArcsForSlotFromBoundarySource]
      rw [dhcExitArcsForSlotFromPrevIndexed_zipIdx_eq_source
        budget slot source hNodup inc rest hInc hRest]

theorem dhcEntryArcsForSlotFromPrevSource_eq_boundary_of_ne
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (prev : Nat × Nat)
    (xs : List (Nat × Nat)) (hNe : ∀ x, x ∈ xs → prev.1 ≠ x.1) :
    dhcEntryArcsForSlotFromPrevSource budget source slot prev xs =
      dhcEntryArcsForSlotFromBoundarySource budget source slot xs := by
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      have hx : prev.1 ≠ x.1 := hNe x (by simp)
      simp [dhcEntryArcsForSlotFromPrevSource, dhcEntryArcsForSlotFromBoundarySource, hx]

theorem dhcEntryArcsForSlotFromPrevSource_same_append_boundary
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (prev : Nat × Nat)
    (same tail : List (Nat × Nat))
    (hSame : ∀ x, x ∈ same → x.1 = prev.1)
    (hTailNe : ∀ x, x ∈ tail → prev.1 ≠ x.1) :
    dhcEntryArcsForSlotFromPrevSource budget source slot prev (same ++ tail) =
      dhcEntryArcsForSlotFromBoundarySource budget source slot tail := by
  induction same generalizing prev with
  | nil =>
      simpa using
        dhcEntryArcsForSlotFromPrevSource_eq_boundary_of_ne
          budget source slot prev tail hTailNe
  | cons x xs ih =>
      have hxSame : x.1 = prev.1 := hSame x (by simp)
      have hXs : ∀ y, y ∈ xs → y.1 = x.1 := by
        intro y hy
        exact (hSame y (by simp [hy])).trans hxSame.symm
      have hTailNeX : ∀ y, y ∈ tail → x.1 ≠ y.1 := by
        intro y hy hEq
        exact hTailNe y hy (hxSame.symm.trans hEq)
      simp [dhcEntryArcsForSlotFromPrevSource, hxSame.symm,
        ih x hXs hTailNeX]

theorem match_getLast?_cons_irrel_none {α β : Type*}
    (x : α) (xs : List α) (a b : β) (f : α → β) :
    (match (x :: xs).getLast? with
      | none => a
      | some y => f y) =
      (match (x :: xs).getLast? with
        | none => b
        | some y => f y) := by
  rw [List.getLast?_eq_getLast_of_ne_nil (by simp : x :: xs ≠ [])]

theorem dhcExitArcsForSlotFromPrevSource_same_append_boundary
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat) (prev : Nat × Nat)
    (same tail : List (Nat × Nat))
    (hSame : ∀ x, x ∈ same → x.1 = prev.1)
    (hTailNe : ∀ x, x ∈ tail → prev.1 ≠ x.1) :
    dhcExitArcsForSlotFromPrevSource budget source slot prev (same ++ tail) =
      (match same.getLast? with
        | none => dhcExitArcForSlotSourceBlock budget source slot prev
        | some last => dhcExitArcForSlotSourceBlock budget source slot last) ++
        dhcExitArcsForSlotFromBoundarySource budget source slot tail := by
  induction same generalizing prev with
  | nil =>
      cases tail with
      | nil =>
          simp [dhcExitArcsForSlotFromPrevSource, dhcExitArcsForSlotFromBoundarySource]
      | cons x xs =>
          have hx : prev.1 ≠ x.1 := hTailNe x (by simp)
          simp [dhcExitArcsForSlotFromPrevSource, dhcExitArcsForSlotFromBoundarySource, hx]
  | cons x xs ih =>
      have hxSame : x.1 = prev.1 := hSame x (by simp)
      have hXs : ∀ y, y ∈ xs → y.1 = x.1 := by
        intro y hy
        exact (hSame y (by simp [hy])).trans hxSame.symm
      have hTailNeX : ∀ y, y ∈ tail → x.1 ≠ y.1 := by
        intro y hy hEq
        exact hTailNe y hy (hxSame.symm.trans hEq)
      have hMatch :
          (match xs.getLast? with
            | none => dhcExitArcForSlotSourceBlock budget source slot x
            | some last => dhcExitArcForSlotSourceBlock budget source slot last) =
            (match (x :: xs).getLast? with
              | none => dhcExitArcForSlotSourceBlock budget source slot prev
              | some last => dhcExitArcForSlotSourceBlock budget source slot last) := by
        cases xs with
        | nil =>
            simp
        | cons y ys =>
            simpa using
              match_getLast?_cons_irrel_none y ys
                (dhcExitArcForSlotSourceBlock budget source slot x)
                (dhcExitArcForSlotSourceBlock budget source slot prev)
                (fun last => dhcExitArcForSlotSourceBlock budget source slot last)
      simp [dhcExitArcsForSlotFromPrevSource, hxSame.symm]
      rw [ih x hXs hTailNeX, hMatch]

theorem dhcEntryArcsForSlotFromBoundarySource_flatMap
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat)
    (us : List Nat) (rows : Nat → List (Nat × Nat)) (hNodup : us.Nodup)
    (hRows : ∀ u ui, ui ∈ rows u → ui.1 = u) :
    dhcEntryArcsForSlotFromBoundarySource budget source slot (us.flatMap rows) =
      ((us.map fun u =>
        match (rows u).head? with
        | none => []
        | some ui => dhcEntryArcForSlotSourceBlock budget source slot ui)).flatten := by
  induction us with
  | nil =>
      simp [dhcEntryArcsForSlotFromBoundarySource]
  | cons u us ih =>
      have huNot : u ∉ us := (List.nodup_cons.mp hNodup).1
      have hTailNodup : us.Nodup := (List.nodup_cons.mp hNodup).2
      have hTailNe : ∀ y, y ∈ us.flatMap rows → u ≠ y.1 := by
        intro y hy hEq
        rcases List.mem_flatMap.mp hy with ⟨v, hv, hyRow⟩
        have hyv : y.1 = v := hRows v y hyRow
        have huv : u = v := hEq.trans hyv
        exact huNot (by simpa [huv] using hv)
      have ihTail := ih hTailNodup
      cases hRow : rows u with
      | nil =>
          simp [hRow, ihTail]
      | cons first rest =>
          have hFirst : first.1 = u := hRows u first (by simp [hRow])
          have hRest : ∀ y, y ∈ rest → y.1 = first.1 := by
            intro y hy
            exact (hRows u y (by simp [hRow, hy])).trans hFirst.symm
          have hTailNeFirst : ∀ y, y ∈ us.flatMap rows → first.1 ≠ y.1 := by
            intro y hy hEq
            exact hTailNe y hy (hFirst.symm.trans hEq)
          have hPrev :=
            dhcEntryArcsForSlotFromPrevSource_same_append_boundary
              budget source slot first rest (us.flatMap rows) hRest hTailNeFirst
          calc
            dhcEntryArcsForSlotFromBoundarySource budget source slot
                ((u :: us).flatMap rows)
                =
              dhcEntryArcForSlotSourceBlock budget source slot first ++
                dhcEntryArcsForSlotFromBoundarySource budget source slot
                  (us.flatMap rows) := by
                simp [hRow, dhcEntryArcsForSlotFromBoundarySource, hPrev]
            _ =
              ((List.map
                  (fun u =>
                    match (rows u).head? with
                    | none => []
                    | some ui => dhcEntryArcForSlotSourceBlock budget source slot ui)
                  (u :: us))).flatten := by
                simp [hRow, ihTail]

theorem dhcExitArcsForSlotFromBoundarySource_flatMap
    (budget : Nat) (source : List (Nat × Nat)) (slot : Nat)
    (us : List Nat) (rows : Nat → List (Nat × Nat)) (hNodup : us.Nodup)
    (hRows : ∀ u ui, ui ∈ rows u → ui.1 = u) :
    dhcExitArcsForSlotFromBoundarySource budget source slot (us.flatMap rows) =
      ((us.map fun u =>
        match (rows u).getLast? with
        | none => []
        | some ui => dhcExitArcForSlotSourceBlock budget source slot ui)).flatten := by
  induction us with
  | nil =>
      simp [dhcExitArcsForSlotFromBoundarySource]
  | cons u us ih =>
      have huNot : u ∉ us := (List.nodup_cons.mp hNodup).1
      have hTailNodup : us.Nodup := (List.nodup_cons.mp hNodup).2
      have hTailNe : ∀ y, y ∈ us.flatMap rows → u ≠ y.1 := by
        intro y hy hEq
        rcases List.mem_flatMap.mp hy with ⟨v, hv, hyRow⟩
        have hyv : y.1 = v := hRows v y hyRow
        have huv : u = v := hEq.trans hyv
        exact huNot (by simpa [huv] using hv)
      have ihTail := ih hTailNodup
      cases hRow : rows u with
      | nil =>
          simp [hRow, ihTail]
      | cons first rest =>
          have hFirst : first.1 = u := hRows u first (by simp [hRow])
          have hRest : ∀ y, y ∈ rest → y.1 = first.1 := by
            intro y hy
            exact (hRows u y (by simp [hRow, hy])).trans hFirst.symm
          have hTailNeFirst : ∀ y, y ∈ us.flatMap rows → first.1 ≠ y.1 := by
            intro y hy hEq
            exact hTailNe y hy (hFirst.symm.trans hEq)
          have hPrev :=
            dhcExitArcsForSlotFromPrevSource_same_append_boundary
              budget source slot first rest (us.flatMap rows) hRest hTailNeFirst
          calc
            dhcExitArcsForSlotFromBoundarySource budget source slot
                ((u :: us).flatMap rows)
                =
              (match rest.getLast? with
                | none => dhcExitArcForSlotSourceBlock budget source slot first
                | some last => dhcExitArcForSlotSourceBlock budget source slot last) ++
                dhcExitArcsForSlotFromBoundarySource budget source slot
                  (us.flatMap rows) := by
                simp [hRow, dhcExitArcsForSlotFromBoundarySource, hPrev]
            _ =
              ((List.map
                  (fun u =>
                    match (rows u).getLast? with
                    | none => []
                    | some ui => dhcExitArcForSlotSourceBlock budget source slot ui)
                  (u :: us))).flatten := by
                cases rest with
                | nil =>
                    simp [hRow, ihTail]
                | cons y ys =>
                    have hMatch :=
                      match_getLast?_cons_irrel_none y ys
                        (dhcExitArcForSlotSourceBlock budget source slot first)
                        ([] : List (Nat × Nat))
                        (fun last => dhcExitArcForSlotSourceBlock budget source slot last)
                    simpa [hRow, ihTail] using hMatch

theorem list_flatten_map_flatten_eq_product_flatMap {α β γ : Type*}
    (xs : List α) (ys : List β) (f : α → β → List γ) :
    ((xs.map fun x => (ys.map fun y => f x y).flatten).flatten) =
      ((xs.product ys).flatMap fun pair => f pair.1 pair.2) := by
  have hRow :
      ∀ x : α,
        (ys.map fun y => f x y).flatten =
          ((ys.map fun y => (x, y)).flatMap fun pair => f pair.1 pair.2) := by
    intro x
    induction ys with
    | nil =>
        simp
    | cons y ys ih =>
        simp [ih]
  induction xs with
  | nil =>
      simp [List.product]
  | cons x xs ih =>
      simp [List.product, ih, hRow x]

theorem dhcEntryArcsExecutableFromInput_eq_textbookTrackEntryArcs
    (I : VertexCoverInput) :
    dhcEntryArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookTrackEntryArcs I := by
  calc
    dhcEntryArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I)
        =
      ((List.range I.k).map fun slot =>
        dhcEntryArcsForSlotFromBoundaryIndexed I.k slot
          (dhcIndexedSourceIncidencesFromInput I)).flatten := by
        rfl
    _ =
      ((List.range I.k).map fun slot =>
        dhcEntryArcsForSlotFromBoundaryIndexed I.k slot
          (sourceIncidences I).zipIdx).flatten := by
        simp [dhcIndexedSourceIncidencesFromInput,
          dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]
    _ =
      ((List.range I.k).map fun slot =>
        dhcEntryArcsForSlotFromBoundarySource I.k (sourceIncidences I) slot
          (sourceIncidences I)).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        exact dhcEntryArcsForSlotFromBoundaryIndexed_zipIdx_eq_source
          I.k slot (sourceIncidences I) (sourceIncidences_nodup I)
    _ =
      ((List.range I.k).map fun slot =>
        ((List.range I.graph.vertices).map fun u =>
          match (incidencesOfVertex I u).head? with
          | none => []
          | some ui =>
              dhcEntryArcForSlotSourceBlock I.k (sourceIncidences I) slot ui).flatten).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        conv_lhs =>
          arg 4
          rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
        exact dhcEntryArcsForSlotFromBoundarySource_flatMap
          I.k (sourceIncidences I) slot (List.range I.graph.vertices)
          (fun u => incidencesOfVertex I u) (List.nodup_range (n := I.graph.vertices))
          (by
            intro u ui hui
            exact ((mem_incidencesOfVertex_iff I u ui).1 hui).2)
    _ =
      textbookTrackEntryArcs I := by
        rw [list_flatten_map_flatten_eq_product_flatMap]
        simp [textbookTrackEntryArcs, dhcEntryArcForSlotSourceBlock,
          dhcIncidenceVertexFromSourceIncidences_eq_textbook]
        rfl

theorem dhcExitArcsExecutableFromInput_eq_textbookTrackExitArcs
    (I : VertexCoverInput) :
    dhcExitArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookTrackExitArcs I := by
  calc
    dhcExitArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I)
        =
      ((List.range I.k).map fun slot =>
        dhcExitArcsForSlotFromBoundaryIndexed I.k slot
          (dhcIndexedSourceIncidencesFromInput I)).flatten := by
        rfl
    _ =
      ((List.range I.k).map fun slot =>
        dhcExitArcsForSlotFromBoundaryIndexed I.k slot
          (sourceIncidences I).zipIdx).flatten := by
        simp [dhcIndexedSourceIncidencesFromInput,
          dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]
    _ =
      ((List.range I.k).map fun slot =>
        dhcExitArcsForSlotFromBoundarySource I.k (sourceIncidences I) slot
          (sourceIncidences I)).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        exact dhcExitArcsForSlotFromBoundaryIndexed_zipIdx_eq_source
          I.k slot (sourceIncidences I) (sourceIncidences_nodup I)
    _ =
      ((List.range I.k).map fun slot =>
        ((List.range I.graph.vertices).map fun u =>
          match (incidencesOfVertex I u).getLast? with
          | none => []
          | some ui =>
              dhcExitArcForSlotSourceBlock I.k (sourceIncidences I) slot ui).flatten).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        conv_lhs =>
          arg 4
          rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
        exact dhcExitArcsForSlotFromBoundarySource_flatMap
          I.k (sourceIncidences I) slot (List.range I.graph.vertices)
          (fun u => incidencesOfVertex I u) (List.nodup_range (n := I.graph.vertices))
          (by
            intro u ui hui
            exact ((mem_incidencesOfVertex_iff I u ui).1 hui).2)
    _ =
      textbookTrackExitArcs I := by
        rw [list_flatten_map_flatten_eq_product_flatMap]
        simp [textbookTrackExitArcs, dhcExitArcForSlotSourceBlock,
          dhcIncidenceVertexFromSourceIncidences_eq_textbook,
          dhcNextSelectorFromBudget_eq_textbookNextSelector]
        rfl

theorem firstIncident_iff_head_incidencesOfVertex
    (I : VertexCoverInput) (u i : Nat) :
    FirstIncident I u i ↔ (incidencesOfVertex I u).head? = some (u, i) := by
  constructor
  · intro hFirst
    have hMem : (u, i) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, i)).2 hFirst.1)
    cases hList : incidencesOfVertex I u with
    | nil =>
        simp [hList] at hMem
    | cons head tail =>
        have hHeadMem : head ∈ incidencesOfVertex I u := by simp [hList]
        have hHeadData := (mem_incidencesOfVertex_iff I u head).1 hHeadMem
        have hHeadSource : SourceIncidentAt I u head.2 := by
          have hSrc := (mem_sourceIncidences_iff I head).1 hHeadData.1
          simpa [hHeadData.2] using hSrc
        have hCases : (u, i) = head ∨ (u, i) ∈ tail := by
          simpa [hList] using hMem
        rcases hCases with hEq | hTail
        · simp [hEq.symm]
        · have hPairwise :
              (head :: tail).Pairwise fun ui uj : Nat × Nat => ui.2 < uj.2 := by
            simpa [hList] using incidencesOfVertex_pairwise_edge_lt I u
          have hlt : head.2 < i := by
            simpa using hPairwise.rel_head_tail (by simpa using hTail)
          exact False.elim (hFirst.2 head.2 hlt hHeadSource)
  · intro hHead
    have hMem : (u, i) ∈ incidencesOfVertex I u :=
      mem_of_head?_eq_some hHead
    have hSource : SourceIncidentAt I u i :=
      (mem_sourceIncidences_iff I (u, i)).1
        ((mem_incidencesOfVertex_iff I u (u, i)).1 hMem).1
    refine ⟨hSource, ?_⟩
    intro h hlt hSrc
    have hhMem : (u, h) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, h)).2 hSrc)
    cases hList : incidencesOfVertex I u with
    | nil =>
        simp [hList] at hHead
    | cons head tail =>
        have hHeadEq : head = (u, i) := by
          simpa [hList] using hHead
        subst head
        have hCases : (u, h) = (u, i) ∨ (u, h) ∈ tail := by
          simpa [hList] using hhMem
        rcases hCases with hEq | hTail
        · have hhi : h = i := congrArg Prod.snd hEq
          omega
        · have hPairwise :
              ((u, i) :: tail).Pairwise fun ui uj : Nat × Nat => ui.2 < uj.2 := by
            simpa [hList] using incidencesOfVertex_pairwise_edge_lt I u
          have hih : i < h := by
            simpa using hPairwise.rel_head_tail (by simpa using hTail)
          omega

theorem lastIncident_iff_getLast_incidencesOfVertex
    (I : VertexCoverInput) (u i : Nat) :
    LastIncident I u i ↔ (incidencesOfVertex I u).getLast? = some (u, i) := by
  constructor
  · intro hLast
    let row := incidencesOfVertex I u
    have hMem : (u, i) ∈ row :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, i)).2 hLast.1)
    have hne : row ≠ [] := List.ne_nil_of_mem hMem
    rw [List.getLast?_eq_getLast_of_ne_nil hne]
    by_cases hEq : (u, i) = row.getLast hne
    · simp [hEq]
    · have hDrop : (u, i) ∈ row.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hMem hEq
      have hPairwise : row.Pairwise fun ui uj : Nat × Nat => ui.2 < uj.2 := by
        simpa [row] using incidencesOfVertex_pairwise_edge_lt I u
      have hiLtLast : i < (row.getLast hne).2 := by
        simpa using hPairwise.rel_dropLast_getLast hDrop
      have hLastMem : row.getLast hne ∈ row := List.getLast_mem hne
      have hLastData := (mem_incidencesOfVertex_iff I u (row.getLast hne)).1 hLastMem
      have hLastSource : SourceIncidentAt I u (row.getLast hne).2 := by
        have hSrc := (mem_sourceIncidences_iff I (row.getLast hne)).1 hLastData.1
        simpa [hLastData.2] using hSrc
      exact False.elim (hLast.2 (row.getLast hne).2 hiLtLast hLastSource.1 hLastSource)
  · intro hGetLast
    have hMem : (u, i) ∈ incidencesOfVertex I u :=
      mem_of_getLast?_eq_some hGetLast
    have hSource : SourceIncidentAt I u i :=
      (mem_sourceIncidences_iff I (u, i)).1
        ((mem_incidencesOfVertex_iff I u (u, i)).1 hMem).1
    refine ⟨hSource, ?_⟩
    intro h hlt hBound hSrc
    have hhMem : (u, h) ∈ incidencesOfVertex I u :=
      sourceIncidence_mem_incidencesOfVertex
        ((mem_sourceIncidences_iff I (u, h)).2 ⟨hBound, hSrc.2⟩)
    let row := incidencesOfVertex I u
    have hne : row ≠ [] := List.ne_nil_of_mem hMem
    have hGet : row.getLast hne = (u, i) := by
      have hSome := List.getLast?_eq_getLast_of_ne_nil hne
      rw [hGetLast] at hSome
      exact Option.some.inj hSome.symm
    by_cases hEq : (u, h) = row.getLast hne
    · have hhi : h = i := by
        have hPair : (u, h) = (u, i) := hEq.trans hGet
        exact congrArg Prod.snd hPair
      omega
    · have hDrop : (u, h) ∈ row.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast (by simpa [row] using hhMem) hEq
      have hPairwise : row.Pairwise fun ui uj : Nat × Nat => ui.2 < uj.2 := by
        simpa [row] using incidencesOfVertex_pairwise_edge_lt I u
      have hhLtLast : h < (row.getLast hne).2 := by
        simpa using hPairwise.rel_dropLast_getLast hDrop
      have hhLtI : h < i := by simpa [hGet] using hhLtLast
      omega

theorem list_filter_eq_nil_of_forall_not {α : Type*}
    (xs : List α) (p : α → Prop) [∀ x, Decidable (p x)]
    (h : ∀ x, x ∈ xs → ¬ p x) :
    (xs.filter fun x => decide (p x)) = [] := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : ¬ p x := h x (by simp)
      have hTail : ∀ y, y ∈ xs → ¬ p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hTail]

theorem list_filter_eq_singleton_of_unique {α : Type*} [DecidableEq α]
    (xs : List α) (p : α → Prop) [∀ x, Decidable (p x)] {x : α}
    (hxMem : x ∈ xs) (hNodup : xs.Nodup)
    (hUnique : ∀ y, y ∈ xs → (p y ↔ y = x)) :
    (xs.filter fun y => decide (p y)) = [x] := by
  induction xs with
  | nil =>
      simp at hxMem
  | cons y ys ih =>
      have hY : p y ↔ y = x := hUnique y (by simp)
      by_cases hyx : y = x
      · subst y
        have hxNotTail : x ∉ ys := (List.nodup_cons.mp hNodup).1
        have hTailNil :
            (ys.filter fun y => decide (p y)) = [] := by
          apply list_filter_eq_nil_of_forall_not
          intro z hz hpz
          have hzx : z = x := (hUnique z (by simp [hz])).1 hpz
          exact hxNotTail (by simpa [hzx] using hz)
        simp [hY.mpr rfl, hTailNil]
      · have hxTail : x ∈ ys := by
          have hxMemCons : x = y ∨ x ∈ ys := by
            simpa using hxMem
          cases hxMemCons with
          | inl hxy =>
              exact False.elim (hyx hxy.symm)
          | inr hxTail =>
              exact hxTail
        have hTailNodup : ys.Nodup := (List.nodup_cons.mp hNodup).2
        have hUniqueTail : ∀ z, z ∈ ys → (p z ↔ z = x) := by
          intro z hz
          exact hUnique z (by simp [hz])
        have hyNot : ¬ p y := by
          intro hp
          exact hyx ((hUnique y (by simp)).1 hp)
        simp [hyNot, ih hxTail hTailNodup hUniqueTail]

theorem incidencesOfVertex_filter_firstIncident_eq_head
    (I : VertexCoverInput) (u : Nat) :
    (by
      classical
      exact
        ((incidencesOfVertex I u).filter fun ui =>
            decide (FirstIncident I ui.1 ui.2)) =
          match (incidencesOfVertex I u).head? with
          | none => []
          | some ui => [ui]) := by
  classical
  cases hHead : (incidencesOfVertex I u).head? with
  | none =>
      cases hList : incidencesOfVertex I u with
      | nil =>
          simp
      | cons x xs =>
          simp [hList] at hHead
  | some head =>
      have hHeadMem : head ∈ incidencesOfVertex I u :=
        mem_of_head?_eq_some hHead
      have hHeadData := (mem_incidencesOfVertex_iff I u head).1 hHeadMem
      have hHeadEq : head = (u, head.2) := Prod.ext hHeadData.2 rfl
      have hHeadSome :
          (incidencesOfVertex I u).head? = some (u, head.2) := by
        rw [hHeadEq] at hHead
        exact hHead
      refine list_filter_eq_singleton_of_unique
        (incidencesOfVertex I u)
        (fun ui => FirstIncident I ui.1 ui.2)
        hHeadMem (incidencesOfVertex_nodup I u) ?_
      intro y hy
      have hyData := (mem_incidencesOfVertex_iff I u y).1 hy
      constructor
      · intro hFirst
        have hFirstU : FirstIncident I u y.2 := by
          simpa [hyData.2] using hFirst
        have hYHead :
            (incidencesOfVertex I u).head? = some (u, y.2) :=
          (firstIncident_iff_head_incidencesOfVertex I u y.2).1 hFirstU
        have hSomeEq : some (u, y.2) = some (u, head.2) :=
          hYHead.symm.trans hHeadSome
        have hPairEq : (u, y.2) = (u, head.2) := Option.some.inj hSomeEq
        have hSndEq : y.2 = head.2 := by
          simpa using congrArg (@Prod.snd Nat Nat) hPairEq
        exact Prod.ext (hyData.2.trans hHeadData.2.symm) hSndEq
      · intro hyHead
        subst y
        have hFirstU : FirstIncident I u head.2 :=
          (firstIncident_iff_head_incidencesOfVertex I u head.2).2 hHeadSome
        simpa [hHeadData.2] using hFirstU

theorem incidencesOfVertex_filter_lastIncident_eq_getLast
    (I : VertexCoverInput) (u : Nat) :
    (by
      classical
      exact
        ((incidencesOfVertex I u).filter fun ui =>
            decide (LastIncident I ui.1 ui.2)) =
          match (incidencesOfVertex I u).getLast? with
          | none => []
          | some ui => [ui]) := by
  classical
  cases hLast : (incidencesOfVertex I u).getLast? with
  | none =>
      cases hList : incidencesOfVertex I u with
      | nil =>
          simp
      | cons x xs =>
          rw [hList] at hLast
          simp at hLast
  | some last =>
      have hLastMem : last ∈ incidencesOfVertex I u :=
        mem_of_getLast?_eq_some hLast
      have hLastData := (mem_incidencesOfVertex_iff I u last).1 hLastMem
      have hLastEq : last = (u, last.2) := Prod.ext hLastData.2 rfl
      have hLastSome :
          (incidencesOfVertex I u).getLast? = some (u, last.2) := by
        rw [hLastEq] at hLast
        exact hLast
      refine list_filter_eq_singleton_of_unique
        (incidencesOfVertex I u)
        (fun ui => LastIncident I ui.1 ui.2)
        hLastMem (incidencesOfVertex_nodup I u) ?_
      intro y hy
      have hyData := (mem_incidencesOfVertex_iff I u y).1 hy
      constructor
      · intro hLastY
        have hLastYU : LastIncident I u y.2 := by
          simpa [hyData.2] using hLastY
        have hYLast :
            (incidencesOfVertex I u).getLast? = some (u, y.2) :=
          (lastIncident_iff_getLast_incidencesOfVertex I u y.2).1 hLastYU
        have hSomeEq : some (u, y.2) = some (u, last.2) :=
          hYLast.symm.trans hLastSome
        have hPairEq : (u, y.2) = (u, last.2) := Option.some.inj hSomeEq
        have hSndEq : y.2 = last.2 := by
          simpa using congrArg (@Prod.snd Nat Nat) hPairEq
        exact Prod.ext (hyData.2.trans hLastData.2.symm) hSndEq
      · intro hyLast
        subst y
        have hLastU : LastIncident I u last.2 :=
          (lastIncident_iff_getLast_incidencesOfVertex I u last.2).2 hLastSome
        simpa [hLastData.2] using hLastU

theorem list_product_filter_map_right {α β γ : Type*}
    (lefts : List α) (rights : List β) (p : β → Prop)
    [∀ y, Decidable (p y)] (f : α × β → γ) :
    (((lefts.product rights).filter fun pair => decide (p pair.2)).map f) =
      ((lefts.map fun left =>
        ((rights.filter fun right => decide (p right)).map fun right =>
          f (left, right))).flatten) := by
  induction lefts with
  | nil =>
      rfl
  | cons left lefts ih =>
      change
        ((((rights.map fun right => (left, right)) ++ lefts.product rights).filter
            fun pair => decide (p pair.2)).map f) =
          (((rights.filter fun right => decide (p right)).map fun right =>
              f (left, right)) ::
            (lefts.map fun left =>
              ((rights.filter fun right => decide (p right)).map fun right =>
                f (left, right)))).flatten
      rw [List.filter_append, List.map_append]
      rw [list_map_pair_filter_map left rights (fun _ right => p right) f]
      rw [ih]
      rfl

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
