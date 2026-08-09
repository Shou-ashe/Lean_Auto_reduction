/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitProductSemantics

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-!
TM certificates for the entry/exit boundary layer.

The exit arc needs the selector successor modulo the budget.  The project has
direct unary certificates for successor and equality, but no primitive modulo
machine, so this file realizes `slot ↦ (slot + 1) % budget` by folding over
`slot + 1` raw units and carrying the current bounded selector.
-/

def dhcNextSelectorAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def dhcNextSelectorInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat (EncodedType.raw Unit)

def dhcNextSelectorInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcNextSelectorInstructionEncodedType

def dhcNextSelectorFoldInit : dhcNextSelectorAccEncodedType.Carrier :=
  ((0 : Nat), (0 : Nat))

def dhcNextSelectorAdvance (budget current : Nat) : Nat :=
  if budget = 0 then 0 else if current.succ = budget then 0 else current.succ

def dhcNextSelectorFoldLeftStep (budget : Nat) :
    dhcNextSelectorAccEncodedType.Carrier :=
  (budget, (0 : Nat))

def dhcNextSelectorFoldRightStep
    (p : dhcNextSelectorAccEncodedType.Carrier × Unit) :
    dhcNextSelectorAccEncodedType.Carrier :=
  (p.1.1, dhcNextSelectorAdvance p.1.1 p.1.2)

def dhcNextSelectorFoldStep
    (p : dhcNextSelectorAccEncodedType.Carrier ×
      dhcNextSelectorInstructionEncodedType.Carrier) :
    dhcNextSelectorAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl budget => dhcNextSelectorFoldLeftStep budget
  | Sum.inr u => dhcNextSelectorFoldRightStep (p.1, u)

def dhcNextSelectorInstructions (p : Nat × Nat) :
    dhcNextSelectorInstructionListEncodedType.Carrier :=
  Sum.inl p.1 :: (List.replicate p.2.succ ()).map Sum.inr

def dhcNextSelectorFoldResult
    (instrs : dhcNextSelectorInstructionListEncodedType.Carrier) : Nat :=
  (instrs.foldl
    (fun acc instr => dhcNextSelectorFoldStep (acc, instr))
    dhcNextSelectorFoldInit).2

def dhcNextSelectorFromFold (p : Nat × Nat) : Nat :=
  dhcNextSelectorFoldResult (dhcNextSelectorInstructions p)

theorem dhcNextSelectorAdvance_eq_mod
    {budget current : Nat} (hBudget : budget ≠ 0) (hCurrent : current < budget) :
    dhcNextSelectorAdvance budget current = (current + 1) % budget := by
  unfold dhcNextSelectorAdvance
  simp [hBudget]
  by_cases hLast : current.succ = budget
  · rw [if_pos hLast]
    rw [← hLast]
    simp
  · have hNextLt : current + 1 < budget := by
      omega
    simp [hLast, Nat.mod_eq_of_lt hNextLt]

theorem dhcNextSelectorFoldUnitInstrs_mod_aux
    (budget current n : Nat)
    (hZero : budget = 0 → current = 0)
    (hCurrent : budget ≠ 0 → current < budget) :
    (((List.replicate n ()).map Sum.inr).foldl
        (fun acc instr => dhcNextSelectorFoldStep (acc, instr))
        (budget, current)).2 =
      if budget = 0 then 0 else (current + n) % budget := by
  induction n generalizing current with
  | zero =>
      change current = if budget = 0 then 0 else (current + 0) % budget
      by_cases hBudget : budget = 0
      · simp [hBudget, hZero hBudget]
      · simp [hBudget, Nat.mod_eq_of_lt (hCurrent hBudget)]
  | succ n ih =>
      simp only [List.replicate_succ, List.map_cons]
      change
        (((List.replicate n ()).map Sum.inr).foldl
            (fun acc instr => dhcNextSelectorFoldStep (acc, instr))
            (budget, dhcNextSelectorAdvance budget current)).2 =
          if budget = 0 then 0 else (current + Nat.succ n) % budget
      have hZeroNext : budget = 0 → dhcNextSelectorAdvance budget current = 0 := by
        intro hBudget
        simp [dhcNextSelectorAdvance, hBudget]
      have hCurrentNext :
          budget ≠ 0 → dhcNextSelectorAdvance budget current < budget := by
        intro hBudget
        rw [dhcNextSelectorAdvance_eq_mod hBudget (hCurrent hBudget)]
        exact Nat.mod_lt _ (Nat.pos_of_ne_zero hBudget)
      rw [ih (dhcNextSelectorAdvance budget current) hZeroNext hCurrentNext]
      by_cases hBudget : budget = 0
      · simp [hBudget]
      · have hAdvance := dhcNextSelectorAdvance_eq_mod hBudget (hCurrent hBudget)
        simp [hBudget, hAdvance]
        congr 1
        omega

theorem dhcNextSelectorFromFold_eq (p : Nat × Nat) :
    dhcNextSelectorFromFold p = dhcNextSelectorFromBudget p.1 p.2 := by
  rcases p with ⟨budget, slot⟩
  rw [dhcNextSelectorFromFold, dhcNextSelectorFoldResult,
    dhcNextSelectorInstructions, List.foldl_cons]
  change
    (((List.replicate slot.succ ()).map Sum.inr).foldl
        (fun acc instr => dhcNextSelectorFoldStep (acc, instr))
        (budget, (0 : Nat))).2 =
      dhcNextSelectorFromBudget budget slot
  rw [dhcNextSelectorFoldUnitInstrs_mod_aux budget 0 slot.succ]
  · by_cases hBudget : budget = 0
    · simp [dhcNextSelectorFromBudget, hBudget]
    · simp [dhcNextSelectorFromBudget, hBudget, Nat.succ_eq_add_one]
  · intro _h
    rfl
  · intro hBudget
    exact Nat.pos_of_ne_zero hBudget

theorem dhcNextSelectorAdvance_tm_polytime :
    TMPolyTimeMap
      dhcNextSelectorAccEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => dhcNextSelectorAdvance p.1 p.2) := by
  let X := dhcNextSelectorAccEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcNextSelectorAccEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hCurrent : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, dhcNextSelectorAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hCurrentSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.succ) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hCurrent
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hBudgetZeroInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hBudget hZero
  have hBudgetZeroBool :
      TMPolyTimeMap X EncodedType.bool (fun p : Nat × Nat => decide (p.1 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hBudgetZeroInput
    simpa [Function.comp, X, dhcNextSelectorAccEncodedType] using hComp
  have hResetInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.succ, p.1)) :=
    TMPolyTimeMap.prod_mk hCurrentSucc hBudget
  have hResetBool :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => decide (p.2.succ = p.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hResetInput
    simpa [Function.comp, X, dhcNextSelectorAccEncodedType] using hComp
  have hResetPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : Nat × Nat => (decide (p.2.succ = p.1), p)) :=
    TMPolyTimeMap.prod_mk hResetBool (TMPolyTimeMap.id X)
  have hResetDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => (0 : Nat)
          | false => p.2.2.succ) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun p : Nat × Nat => p.2.succ)
      (fTrue := fun _ : Nat × Nat => (0 : Nat))
      hCurrentSucc hZero
  have hReset :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat => if p.2.succ = p.1 then (0 : Nat) else p.2.succ) := by
    have hComp := TMPolyTimeMap.comp hResetDispatch hResetPayload
    convert hComp using 1
    funext p
    by_cases hEq : p.2.succ = p.1
    · have hEq' : p.2 + 1 = p.1 := by
        simpa [Nat.succ_eq_add_one] using hEq
      simp [Function.comp, hEq']
    · simp [Function.comp, hEq]
  have hBudgetZeroPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : Nat × Nat => (decide (p.1 = 0), p)) :=
    TMPolyTimeMap.prod_mk hBudgetZeroBool (TMPolyTimeMap.id X)
  have hOuterDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => (0 : Nat)
          | false => if p.2.2.succ = p.2.1 then (0 : Nat) else p.2.2.succ) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun p : Nat × Nat => if p.2.succ = p.1 then (0 : Nat) else p.2.succ)
      (fTrue := fun _ : Nat × Nat => (0 : Nat))
      hReset hZero
  have hOut := TMPolyTimeMap.comp hOuterDispatch hBudgetZeroPayload
  convert hOut using 1
  funext p
  unfold dhcNextSelectorAdvance
  by_cases hBudget : p.1 = 0
  · simp [Function.comp, hBudget]
  · simp [Function.comp, hBudget]
    rfl

theorem dhcNextSelectorFoldLeftStep_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      dhcNextSelectorAccEncodedType
      dhcNextSelectorFoldLeftStep := by
  have hBudget : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n) :=
    TMPolyTimeMap.id EncodedType.nat
  have hZero :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat (0 : Nat)
  have hOut := TMPolyTimeMap.prod_mk hBudget hZero
  simpa [dhcNextSelectorFoldLeftStep, dhcNextSelectorAccEncodedType] using hOut

theorem dhcNextSelectorFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcNextSelectorAccEncodedType (EncodedType.raw Unit))
      dhcNextSelectorAccEncodedType
      dhcNextSelectorFoldRightStep := by
  let X := EncodedType.prod dhcNextSelectorAccEncodedType (EncodedType.raw Unit)
  have hAcc :
      TMPolyTimeMap X dhcNextSelectorAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst dhcNextSelectorAccEncodedType (EncodedType.raw Unit)
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcNextSelectorAccEncodedType, X] using hComp
  have hAdvance :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => dhcNextSelectorAdvance p.1.1 p.1.2) := by
    have hComp := TMPolyTimeMap.comp dhcNextSelectorAdvance_tm_polytime hAcc
    simpa [Function.comp, dhcNextSelectorAccEncodedType, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hBudget hAdvance
  simpa [dhcNextSelectorFoldRightStep, dhcNextSelectorAccEncodedType, X] using hOut

theorem dhcNextSelectorFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcNextSelectorAccEncodedType
        dhcNextSelectorInstructionEncodedType)
      dhcNextSelectorAccEncodedType
      dhcNextSelectorFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcNextSelectorAccEncodedType EncodedType.nat (EncodedType.raw Unit)
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcNextSelectorFoldLeftStep_tm_polytime
      dhcNextSelectorFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

noncomputable def dhcNextSelectorFoldBasePolynomial : Polynomial Nat :=
  Polynomial.C 10

noncomputable def dhcNextSelectorFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.X + Polynomial.C 10

@[simp] theorem dhcNextSelectorFoldBasePolynomial_eval (N : Nat) :
    dhcNextSelectorFoldBasePolynomial.eval N = 10 := by
  simp [dhcNextSelectorFoldBasePolynomial]

@[simp] theorem dhcNextSelectorFoldGrowPolynomial_eval (N : Nat) :
    dhcNextSelectorFoldGrowPolynomial.eval N = N + 10 := by
  simp [dhcNextSelectorFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_X]

theorem dhcNextSelectorFoldStep_growth
    (source : List dhcNextSelectorInstructionEncodedType.Carrier)
    (acc : dhcNextSelectorAccEncodedType.Carrier)
    (instr : dhcNextSelectorInstructionEncodedType.Carrier)
    (hInstr :
      dhcNextSelectorInstructionEncodedType.inputSize instr ≤
        dhcNextSelectorInstructionListEncodedType.inputSize source) :
    dhcNextSelectorAccEncodedType.inputSize (dhcNextSelectorFoldStep (acc, instr)) ≤
      dhcNextSelectorAccEncodedType.inputSize acc +
        dhcNextSelectorFoldGrowPolynomial.eval
          (dhcNextSelectorInstructionListEncodedType.inputSize source) := by
  let N := dhcNextSelectorInstructionListEncodedType.inputSize source
  rcases acc with ⟨budget, current⟩
  change Nat at budget
  change Nat at current
  cases instr with
  | inl newBudget =>
      change Nat at newBudget
      have hBudgetTagged : EncodedType.nat.inputSize newBudget + 1 ≤ N := by
        simpa [dhcNextSelectorInstructionEncodedType,
          dhcNextSelectorInstructionListEncodedType, EncodedType.inputSize,
          EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hBudgetLe : newBudget + 2 ≤ N := by
        simpa [EncodedType.inputSize_nat] using hBudgetTagged
      have hBudgetLe' : newBudget ≤ N := by
        omega
      simp [dhcNextSelectorFoldStep, dhcNextSelectorFoldLeftStep,
        dhcNextSelectorAccEncodedType, dhcNextSelectorFoldGrowPolynomial_eval,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat]
      omega
  | inr u =>
      have hAdvance :
          dhcNextSelectorAdvance budget current ≤ current.succ := by
        unfold dhcNextSelectorAdvance
        by_cases hBudget : budget = 0
        · rw [if_pos hBudget]
          omega
        · rw [if_neg hBudget]
          by_cases hReset : current.succ = budget
          · rw [if_pos hReset]
            omega
          · rw [if_neg hReset]
      simp [dhcNextSelectorFoldStep, dhcNextSelectorFoldRightStep,
        dhcNextSelectorAccEncodedType, dhcNextSelectorFoldGrowPolynomial_eval,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat]
      omega

theorem dhcNextSelectorFold_tm_polytime :
    TMPolyTimeMap
      dhcNextSelectorInstructionListEncodedType
      dhcNextSelectorAccEncodedType
      (fun instrs : List dhcNextSelectorInstructionEncodedType.Carrier =>
        instrs.foldl
          (fun acc instr => dhcNextSelectorFoldStep (acc, instr))
          dhcNextSelectorFoldInit) := by
  rcases dhcNextSelectorFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      dhcNextSelectorInstructionEncodedType dhcNextSelectorAccEncodedType
      dhcNextSelectorFoldStep dhcNextSelectorFoldInit hStep
      dhcNextSelectorFoldBasePolynomial dhcNextSelectorFoldGrowPolynomial ?_ ?_
  · intro xs
    simp [dhcNextSelectorFoldInit, dhcNextSelectorAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  · intro source acc instr hInstr
    simpa [dhcNextSelectorInstructionListEncodedType] using
      dhcNextSelectorFoldStep_growth source acc instr hInstr

theorem dhcNextSelectorFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcNextSelectorInstructionListEncodedType
      EncodedType.nat
      dhcNextSelectorFoldResult := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hComp := TMPolyTimeMap.comp hSnd dhcNextSelectorFold_tm_polytime
  simpa [Function.comp, dhcNextSelectorFoldResult, dhcNextSelectorAccEncodedType] using hComp

theorem dhcNextSelectorInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      dhcNextSelectorInstructionListEncodedType
      dhcNextSelectorInstructions := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSlotSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.succ) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hSlot
    simpa [Function.comp, X] using hComp
  have hUnits :
      TMPolyTimeMap X rawUnitListEncodedType
        (fun p : X.Carrier => List.replicate p.2.succ ()) := by
    have hComp := TMPolyTimeMap.comp natToRawUnitListTMBackedMap.tm_polytime hSlotSucc
    simpa [Function.comp, rawUnitListEncodedType, X] using hComp
  have hInit :
      TMPolyTimeMap X dhcNextSelectorInstructionEncodedType
        (fun p : X.Carrier => Sum.inl p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat (EncodedType.raw Unit)) hBudget
    simpa [Function.comp, dhcNextSelectorInstructionEncodedType, X] using hComp
  have hUnitInstrs :
      TMPolyTimeMap X dhcNextSelectorInstructionListEncodedType
        (fun p : X.Carrier => (List.replicate p.2.succ ()).map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr EncodedType.nat (EncodedType.raw Unit))
    have hComp := TMPolyTimeMap.comp hMap hUnits
    simpa [Function.comp, rawUnitListEncodedType,
      dhcNextSelectorInstructionListEncodedType,
      dhcNextSelectorInstructionEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcNextSelectorInstructionEncodedType
          dhcNextSelectorInstructionListEncodedType)
        (fun p : X.Carrier =>
          (Sum.inl p.1, (List.replicate p.2.succ ()).map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hUnitInstrs
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons dhcNextSelectorInstructionEncodedType) hConsInput
  simpa [Function.comp, dhcNextSelectorInstructions,
    dhcNextSelectorInstructionEncodedType, dhcNextSelectorInstructionListEncodedType, X] using hOut

theorem dhcNextSelectorFromBudget_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => dhcNextSelectorFromBudget p.1 p.2) := by
  have hComp :=
    TMPolyTimeMap.comp dhcNextSelectorFoldResult_tm_polytime
      dhcNextSelectorInstructions_tm_polytime
  convert hComp using 1
  funext p
  exact (dhcNextSelectorFromFold_eq p).symm

theorem dhcExitArcForSlotFromIndexed_tm_polytime :
    TMPolyTimeMap dhcExitArcForSlotFromIndexedInputEncodedType
      edgeStructuredEncodedType
      dhcExitArcForSlotFromIndexed := by
  let X := dhcExitArcForSlotFromIndexedInputEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcExitArcForSlotFromIndexedInputEncodedType,
      dhcEntryArcForSlotFromIndexedInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, dhcExitArcForSlotFromIndexedInputEncodedType,
      dhcEntryArcForSlotFromIndexedInputEncodedType] using
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
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hIdxBit :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hIdx hOne
  have hCodeInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : X.Carrier => (p.1, (p.2.2.2, (1 : Nat)))) :=
    TMPolyTimeMap.prod_mk hBudget hIdxBit
  have hCode : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => dhcIncidenceVertexCode (p.1, (p.2.2.2, (1 : Nat)))) := by
    have hComp := TMPolyTimeMap.comp dhcIncidenceVertexCode_tm_polytime hCodeInput
    simpa [Function.comp] using hComp
  have hNextInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBudget hSlot
  have hNext : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => dhcNextSelectorFromBudget p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp dhcNextSelectorFromBudget_tm_polytime hNextInput
    simpa [Function.comp] using hComp
  have hSelector : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => textbookSelectorVertex (dhcNextSelectorFromBudget p.1 p.2.1)) := by
    simpa [textbookSelectorVertex] using hNext
  have hOut := TMPolyTimeMap.prod_mk hCode hSelector
  simpa [dhcExitArcForSlotFromIndexed, dhcExitArcForSlotFromIndexedRaw,
    edgeStructuredEncodedType, X, dhcExitArcForSlotFromIndexedInputEncodedType,
    dhcEntryArcForSlotFromIndexedInputEncodedType] using hOut

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
