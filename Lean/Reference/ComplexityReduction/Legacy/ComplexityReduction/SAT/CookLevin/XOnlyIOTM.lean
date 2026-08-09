/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyBaseTM

/-!
Direct standard-TM witnesses for the x-only Cook-Levin I/O stack blocks.

This module keeps the I/O endpoint generators separate from `XOnlyBaseTM` so the
base finite-control and stack-domain witnesses stay small.  The first completed
slice covers the empty-stack rows whose only input-dependent component is the
x-only cell range, plus the fixed output-true symbol rows.
-/

namespace ComplexityReduction
namespace SAT

theorem list_map_singleton_eq_flatMap_singleton
    {α β : Type} (f : α → β) :
    ∀ xs : List α, xs.map (fun x => [f x]) =
      xs.flatMap fun x => [[f x]]
  | [] => rfl
  | x :: xs => by
      simp [list_map_singleton_eq_flatMap_singleton f xs]

theorem tmVerifierUnitClauses_map_eq_flatMap_unitCNF
    {α : Type} (f : α → Literal) :
    ∀ xs : List α, tmVerifierUnitClauses (xs.map f) =
      xs.flatMap fun x => tmVerifierUnitCNF (f x)
  | xs => by
      simpa [tmVerifierUnitClauses, tmVerifierUnitCNF, List.map_map] using
        list_map_singleton_eq_flatMap_singleton f xs

@[simp]
theorem tmVerifierUnitClauses_append (xs ys : List Literal) :
    tmVerifierUnitClauses (xs ++ ys) =
      tmVerifierUnitClauses xs ++ tmVerifierUnitClauses ys := by
  simp [tmVerifierUnitClauses]

theorem tmVerifierUnitClauses_filter_map_eq_flatMap_unitCNF_le
    (bound : Nat) (f : Nat → Literal) :
    ∀ xs : List Nat,
      tmVerifierUnitClauses ((xs.filter fun cell => bound ≤ cell).map f) =
        xs.flatMap fun cell => if bound ≤ cell then tmVerifierUnitCNF (f cell) else []
  | [] => by
      simp [tmVerifierUnitClauses]
  | cell :: cells => by
      by_cases h : bound ≤ cell
      · have ih := tmVerifierUnitClauses_filter_map_eq_flatMap_unitCNF_le bound f cells
        simpa [tmVerifierUnitClauses, tmVerifierUnitCNF, h] using
          congrArg (fun tail : CNF => [f cell] :: tail) ih
      · have ih := tmVerifierUnitClauses_filter_map_eq_flatMap_unitCNF_le bound f cells
        simpa [tmVerifierUnitClauses, tmVerifierUnitCNF, h] using ih

/-! ### Fixed-list literal and CNF constructors -/

theorem tmVerifierOutputTrueSymbolLiteralsAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun _ : L.Instance.Carrier => tmVerifierOutputTrueSymbolLiteralsAt V t) :=
  TMPolyTimeMap.const L.Instance (EncodedType.list literalStructuredEncodedType)
    (tmVerifierOutputTrueSymbolLiteralsAt V t)

theorem tmVerifierOutputTrueSymbolUnitClausesAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun _ : L.Instance.Carrier =>
        tmVerifierUnitClauses (tmVerifierOutputTrueSymbolLiteralsAt V t)) := by
  have hLits := tmVerifierOutputTrueSymbolLiteralsAt_tm_polytime V t
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp] using hComp

theorem tmVerifierOutputStackSymbolAtom_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (cell : Nat) (s : (tmVerifierTM V).Γ (tmVerifierTM V).k₁) :
    TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
      (fun t : Nat => tmVerifierOutputStackSymbolAtom V t cell s) := by
  have hCell : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => cell) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat cell
  have hInput :
      TMPolyTimeMap EncodedType.nat tmVerifierTimeCellEncodedType
        (fun t : Nat => (t, cell)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hCell
  have hAtom :=
    tmVerifierStackSymbolAtom_timeCell_tm_polytime V (tmVerifierTM V).k₁
      (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₁ s)
  have hComp := TMPolyTimeMap.comp hAtom hInput
  simpa [Function.comp, tmVerifierOutputStackSymbolAtom, tmVerifierTimeCellEncodedType]
    using hComp

theorem tmVerifierOutputTrueSymbolLiteralsFor_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (entries : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₁ × Nat)) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun t : Nat =>
        entries.map fun entry => tmVerifierOutputStackSymbolAtom V t entry.2 entry.1) := by
  induction entries with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons entry entries ih =>
      have hHead := tmVerifierOutputStackSymbolAtom_time_tm_polytime V entry.2 entry.1
      have hTail := ih
      have hConsInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun t : Nat =>
              (tmVerifierOutputStackSymbolAtom V t entry.2 entry.1,
                entries.map fun entry =>
                  tmVerifierOutputStackSymbolAtom V t entry.2 entry.1)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType)
        hConsInput
      simpa [Function.comp] using hCons

theorem tmVerifierOutputTrueSymbolLiteralsAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
      (fun t : Nat => tmVerifierOutputTrueSymbolLiteralsAt V t) := by
  simpa [tmVerifierOutputTrueSymbolLiteralsAt] using
    tmVerifierOutputTrueSymbolLiteralsFor_time_tm_polytime V
      (tmVerifierBoolOutputWord V true).zipIdx

theorem tmVerifierOutputTrueSymbolUnitClausesAt_time_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun t : Nat =>
        tmVerifierUnitClauses (tmVerifierOutputTrueSymbolLiteralsAt V t)) := by
  have hLits := tmVerifierOutputTrueSymbolLiteralsAt_time_tm_polytime V
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp] using hComp

/-! ### Empty-stack literal rows over the x-only cell range -/

theorem tmVerifierStackEmptyLiteralsForCells_time_stack_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.list EncodedType.nat)
      (EncodedType.list literalStructuredEncodedType)
      (fun cells : List Nat => cells.map fun cell => tmVerifierStackEmptyAtom V t k cell) :=
  TMPolyTimeMap.list_map (tmVerifierStackEmptyAtom_cell_tm_polytime V t k)

theorem tmVerifierXOnlyStackEmptyLiteralsAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun x : L.Instance.Carrier =>
        (tmVerifierXOnlyCellRange V x).map fun cell => tmVerifierStackEmptyAtom V t k cell) := by
  have hRange := tmVerifierXOnlyCellRange_tm_polytime V
  have hMap := tmVerifierStackEmptyLiteralsForCells_time_stack_tm_polytime V t k
  have hComp := TMPolyTimeMap.comp hMap hRange
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyStackEmptyUnitCNFAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (k : tmVerifierStackIndex V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierUnitClauses
          ((tmVerifierXOnlyCellRange V x).map fun cell =>
            tmVerifierStackEmptyAtom V t k cell)) := by
  have hLits := tmVerifierXOnlyStackEmptyLiteralsAt_tm_polytime V t k
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyStackEmptyUnitCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierUnitClauses
          ((tmVerifierXOnlyCellRange V p.1).map fun cell =>
            tmVerifierStackEmptyAtom V p.2 k cell)) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun p : P.Carrier => tmVerifierXOnlyCellRange V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : P.Carrier => (p.2, tmVerifierXOnlyCellRange V p.1)) :=
    TMPolyTimeMap.prod_mk hTime hCells
  have hBlock :
      TMPolyTimeMap tmVerifierTimeCellEncodedType cnfStructuredEncodedType
        (fun p : Nat × Nat => tmVerifierUnitCNF (tmVerifierStackEmptyAtom V p.1 k p.2)) := by
    have hAtom := tmVerifierStackEmptyAtom_timeCell_tm_polytime V k
    have hComp := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hAtom
    simpa [Function.comp] using hComp
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.nat) (X := EncodedType.nat)
    (fun t cell => tmVerifierUnitCNF (tmVerifierStackEmptyAtom V t k cell))
    hBlock
  have hComp := TMPolyTimeMap.comp hFold hInput
  convert hComp using 1
  funext p
  exact tmVerifierUnitClauses_map_eq_flatMap_unitCNF
    (fun cell => tmVerifierStackEmptyAtom V p.2 k cell) (tmVerifierXOnlyCellRange V p.1)

theorem tmVerifierXOnlyEmptyStacksUnitCNFForListAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierUnitClauses
          (ks.flatMap fun k =>
            (tmVerifierXOnlyCellRange V p.1).map fun cell =>
              tmVerifierStackEmptyAtom V p.2 k cell)) := by
  induction ks with
  | nil =>
      exact TMPolyTimeMap.const (EncodedType.prod L.Instance EncodedType.nat)
        cnfStructuredEncodedType []
  | cons k ks ih =>
      have hHead := tmVerifierXOnlyStackEmptyUnitCNFAt_pair_tm_polytime V k
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
            (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
            (fun p : L.Instance.Carrier × Nat =>
              (tmVerifierUnitClauses
                ((tmVerifierXOnlyCellRange V p.1).map fun cell =>
                  tmVerifierStackEmptyAtom V p.2 k cell),
                tmVerifierUnitClauses
                  (ks.flatMap fun k =>
                    (tmVerifierXOnlyCellRange V p.1).map fun cell =>
                      tmVerifierStackEmptyAtom V p.2 k cell))) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
      convert hAppend using 1
      funext p
      rw [List.flatMap_cons, tmVerifierUnitClauses_append]
      rfl

theorem tmVerifierXOnlyEmptyStacksForListAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun x : L.Instance.Carrier =>
        ks.flatMap fun k =>
          (tmVerifierXOnlyCellRange V x).map fun cell => tmVerifierStackEmptyAtom V t k cell) := by
  induction ks with
  | nil =>
      exact TMPolyTimeMap.const L.Instance (EncodedType.list literalStructuredEncodedType) []
  | cons k ks ih =>
      have hHead := tmVerifierXOnlyStackEmptyLiteralsAt_tm_polytime V t k
      have hTail := ih
      have hAppendInput :
          TMPolyTimeMap L.Instance
            (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
              (EncodedType.list literalStructuredEncodedType))
            (fun x : L.Instance.Carrier =>
              ((tmVerifierXOnlyCellRange V x).map fun cell =>
                  tmVerifierStackEmptyAtom V t k cell,
                ks.flatMap fun k =>
                  (tmVerifierXOnlyCellRange V x).map fun cell =>
                    tmVerifierStackEmptyAtom V t k cell)) :=
        TMPolyTimeMap.prod_mk hHead hTail
      have hAppend := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
      simpa [Function.comp] using hAppend

theorem tmVerifierXOnlyEmptyStacksUnitCNFForListAt_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (ks : List (tmVerifierStackIndex V)) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierUnitClauses
          (ks.flatMap fun k =>
            (tmVerifierXOnlyCellRange V x).map fun cell =>
              tmVerifierStackEmptyAtom V t k cell)) := by
  have hLits := tmVerifierXOnlyEmptyStacksForListAt_tm_polytime V t ks
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp] using hComp

theorem tmVerifierXOnlyInitialNonInputEmptyLiterals_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyInitialNonInputEmptyLiterals V x) := by
  simpa [tmVerifierXOnlyInitialNonInputEmptyLiterals] using
    tmVerifierXOnlyEmptyStacksForListAt_tm_polytime V 0 (tmVerifierNonInputStacks V)

theorem tmVerifierXOnlyInitialNonInputEmptyStackCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyInitialNonInputEmptyStackCNF V x) := by
  have hLits := tmVerifierXOnlyInitialNonInputEmptyLiterals_tm_polytime V
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierXOnlyInitialNonInputEmptyStackCNF] using hComp

theorem tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt_fixedTime_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt V x t) := by
  simpa [tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt] using
    tmVerifierXOnlyEmptyStacksForListAt_tm_polytime V t (tmVerifierNonOutputStacks V)

theorem tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt_fixedTime_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt V x t) := by
  have hLits := tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt_fixedTime_tm_polytime V t
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt] using hComp

theorem tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt V p.1 p.2) := by
  simpa [tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt,
    tmVerifierXOnlyOutputTrueNonOutputEmptyLiteralsAt] using
    tmVerifierXOnlyEmptyStacksUnitCNFForListAt_pair_tm_polytime V
      (tmVerifierNonOutputStacks V)

/-! ### Conditional x-only tail rows and endpoint output block -/

theorem tmVerifierLowerBoundStackEmptyUnitCNF_block_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) :
    TMPolyTimeMap
      (EncodedType.prod
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      cnfStructuredEncodedType
      (fun q : (Nat × Nat) × Nat =>
        if q.1.2 ≤ q.2 then
          tmVerifierUnitCNF (tmVerifierStackEmptyAtom V q.1.1 k q.2)
        else
          ([] : CNF)) := by
  let X := EncodedType.prod
    (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
  have hCtx :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun q : X.Carrier => q.1) := by
    simpa [X] using
      TMPolyTimeMap.fst
        (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
  have hCell : TMPolyTimeMap X EncodedType.nat (fun q : X.Carrier => q.2) := by
    simpa [X] using
      TMPolyTimeMap.snd
        (EncodedType.prod EncodedType.nat EncodedType.nat) EncodedType.nat
  have hTime : TMPolyTimeMap X EncodedType.nat (fun q : X.Carrier => q.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, X] using hComp
  have hBound : TMPolyTimeMap X EncodedType.nat (fun q : X.Carrier => q.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun q : X.Carrier => (q.2, q.1.2)) :=
    TMPolyTimeMap.prod_mk hCell hBound
  have hLt :
      TMPolyTimeMap X EncodedType.bool
        (fun q : X.Carrier => natLtBool (q.2, q.1.2)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hLtInput
    simpa [Function.comp, X] using hComp
  have hTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun q : X.Carrier => (natLtBool (q.2, q.1.2), q)) :=
    TMPolyTimeMap.prod_mk hLt (TMPolyTimeMap.id X)
  have hEmpty :
      TMPolyTimeMap X cnfStructuredEncodedType (fun _ : X.Carrier => ([] : CNF)) :=
    TMPolyTimeMap.const X cnfStructuredEncodedType []
  have hAtomInput :
      TMPolyTimeMap X tmVerifierTimeCellEncodedType
        (fun q : X.Carrier => (q.1.1, q.2)) :=
    TMPolyTimeMap.prod_mk hTime hCell
  have hAtom := tmVerifierStackEmptyAtom_timeCell_tm_polytime V k
  have hUnit :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun q : X.Carrier => tmVerifierUnitCNF (tmVerifierStackEmptyAtom V q.1.1 k q.2)) := by
    have hAtomX := TMPolyTimeMap.comp hAtom hAtomInput
    have hComp := TMPolyTimeMap.comp tmVerifierUnitCNF_tm_polytime hAtomX
    simpa [Function.comp, X] using hComp
  have hDispatch :=
    boolProduct_dispatch_tm_polytime X cnfStructuredEncodedType
      (fFalse := fun q : X.Carrier =>
        tmVerifierUnitCNF (tmVerifierStackEmptyAtom V q.1.1 k q.2))
      (fTrue := fun _ : X.Carrier => ([] : CNF))
      hUnit hEmpty
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext q
  by_cases hlt : q.2 < q.1.2
  · have hnot : ¬ q.1.2 ≤ q.2 := by omega
    simp [Function.comp, natLtBool, hlt, hnot]
  · have hle : q.1.2 ≤ q.2 := by omega
    simp [Function.comp, natLtBool, hlt, hle]

theorem tmVerifierXOnlyOutputTrueEmptyTailUnitCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierUnitClauses
          (tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt V p.1 p.2)) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hX : TMPolyTimeMap P L.Instance (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hBound :
      TMPolyTimeMap P EncodedType.nat
        (fun _ : P.Carrier => (tmVerifierBoolOutputWord V true).length) :=
    TMPolyTimeMap.const P EncodedType.nat (tmVerifierBoolOutputWord V true).length
  have hCtx :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : P.Carrier => (p.2, (tmVerifierBoolOutputWord V true).length)) :=
    TMPolyTimeMap.prod_mk hTime hBound
  have hCells :
      TMPolyTimeMap P (EncodedType.list EncodedType.nat)
        (fun p : P.Carrier => tmVerifierXOnlyCellRange V p.1) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierXOnlyCellRange_tm_polytime V) hX
    simpa [Function.comp, P] using hComp
  have hInput :
      TMPolyTimeMap P
        (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun p : P.Carrier =>
          ((p.2, (tmVerifierBoolOutputWord V true).length),
            tmVerifierXOnlyCellRange V p.1)) :=
    TMPolyTimeMap.prod_mk hCtx hCells
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.prod EncodedType.nat EncodedType.nat) (X := EncodedType.nat)
    (fun (ctx : Nat × Nat) (cell : Nat) =>
      if ctx.2 ≤ cell then
        tmVerifierUnitCNF (tmVerifierStackEmptyAtom V ctx.1 (tmVerifierTM V).k₁ cell)
      else
        ([] : CNF))
    (tmVerifierLowerBoundStackEmptyUnitCNF_block_tm_polytime V (tmVerifierTM V).k₁)
  have hComp := TMPolyTimeMap.comp hFold hInput
  convert hComp using 1
  funext p
  rw [Function.comp]
  rw [tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt]
  exact tmVerifierUnitClauses_filter_map_eq_flatMap_unitCNF_le
    (tmVerifierBoolOutputWord V true).length
    (fun cell => tmVerifierStackEmptyAtom V p.2 (tmVerifierTM V).k₁ cell)
    (tmVerifierXOnlyCellRange V p.1)

theorem tmVerifierXOnlyOutputTrueStackCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyOutputTrueStackCNFAt V p.1 p.2) := by
  let P := EncodedType.prod L.Instance EncodedType.nat
  have hTime : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd L.Instance EncodedType.nat
  have hSymbolsAtTime := tmVerifierOutputTrueSymbolUnitClausesAt_time_tm_polytime V
  have hSymbols :
      TMPolyTimeMap P cnfStructuredEncodedType
        (fun p : P.Carrier =>
          tmVerifierUnitClauses (tmVerifierOutputTrueSymbolLiteralsAt V p.2)) := by
    have hComp := TMPolyTimeMap.comp hSymbolsAtTime hTime
    simpa [Function.comp, P] using hComp
  have hTail := tmVerifierXOnlyOutputTrueEmptyTailUnitCNFAt_pair_tm_polytime V
  have hAppendInput :
      TMPolyTimeMap P (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : P.Carrier =>
          (tmVerifierUnitClauses (tmVerifierOutputTrueSymbolLiteralsAt V p.2),
            tmVerifierUnitClauses
              (tmVerifierXOnlyOutputTrueEmptyTailLiteralsAt V p.1 p.2))) :=
    TMPolyTimeMap.prod_mk hSymbols hTail
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyOutputTrueStackCNFAt,
    tmVerifierUnitClauses_append, cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyOutputTrueCNFAt_pair_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat) cnfStructuredEncodedType
      (fun p : L.Instance.Carrier × Nat =>
        tmVerifierXOnlyOutputTrueCNFAt V p.1 p.2) := by
  have hStack := tmVerifierXOnlyOutputTrueStackCNFAt_pair_tm_polytime V
  have hNonOutput := tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt_pair_tm_polytime V
  have hAppendInput :
      TMPolyTimeMap (EncodedType.prod L.Instance EncodedType.nat)
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : L.Instance.Carrier × Nat =>
          (tmVerifierXOnlyOutputTrueStackCNFAt V p.1 p.2,
            tmVerifierXOnlyOutputTrueNonOutputEmptyStackCNFAt V p.1 p.2)) :=
    TMPolyTimeMap.prod_mk hStack hNonOutput
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyOutputTrueCNFAt, cnfStructuredEncodedType]
    using hAppend

theorem tmVerifierXOnlyEndpointCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyEndpointCNF V x) := by
  have hControl := tmVerifierXOnlyEndpointControlCNF_tm_polytime V
  have hTime := tmVerifierXOnlyTimeBound_tm_polytime V
  have hPair :
      TMPolyTimeMap L.Instance (EncodedType.prod L.Instance EncodedType.nat)
        (fun x : L.Instance.Carrier => (x, tmVerifierXOnlyTimeBound V x)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id L.Instance) hTime
  have hOutputPair := tmVerifierXOnlyOutputTrueCNFAt_pair_tm_polytime V
  have hOutput :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier =>
          tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x)) := by
    have hComp := TMPolyTimeMap.comp hOutputPair hPair
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierHaltingControlCNFAt V (tmVerifierXOnlyTimeBound V x) ++
            tmVerifierUnitCNF
              (tmVerifierStateAtom V (tmVerifierXOnlyTimeBound V x)
                (tmVerifierTM V).initialState),
            tmVerifierXOnlyOutputTrueCNFAt V x (tmVerifierXOnlyTimeBound V x))) :=
    TMPolyTimeMap.prod_mk hControl hOutput
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyEndpointCNF, cnfStructuredEncodedType]
    using hAppend

end SAT
end ComplexityReduction
