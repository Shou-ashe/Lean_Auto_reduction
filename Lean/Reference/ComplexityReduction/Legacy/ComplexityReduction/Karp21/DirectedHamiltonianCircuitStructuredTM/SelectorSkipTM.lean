/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.TracksTM

/-!
TM-backed selector-skip runner for the DHC selector/path gadget.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

def dhcSelectorSkipAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

def dhcSelectorSkipInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat EncodedType.nat

def dhcSelectorSkipInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcSelectorSkipInstructionEncodedType

def dhcSelectorSkipFoldInit : dhcSelectorSkipAccEncodedType.Carrier :=
  ((0 : Nat), ([] : List (Nat × Nat)))

def dhcSelectorSkipArcFromBudget (p : Nat × Nat) : Nat × Nat :=
  (textbookSelectorVertex p.2,
    textbookSelectorVertex (dhcNextSelectorFromBudget p.1 p.2))

def dhcSelectorSkipFoldLeftStep (budget : Nat) :
    dhcSelectorSkipAccEncodedType.Carrier :=
  (budget, ([] : List (Nat × Nat)))

def dhcSelectorSkipFoldRightStep
    (p : dhcSelectorSkipAccEncodedType.Carrier × Nat) :
    dhcSelectorSkipAccEncodedType.Carrier :=
  (p.1.1,
    (show List (Nat × Nat) from p.1.2) ++
      [dhcSelectorSkipArcFromBudget (p.1.1, p.2)])

def dhcSelectorSkipFoldStep
    (p : dhcSelectorSkipAccEncodedType.Carrier ×
      dhcSelectorSkipInstructionEncodedType.Carrier) :
    dhcSelectorSkipAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl budget => dhcSelectorSkipFoldLeftStep budget
  | Sum.inr slot => dhcSelectorSkipFoldRightStep (p.1, slot)

def dhcSelectorSkipInstructions (budget : Nat) :
    dhcSelectorSkipInstructionListEncodedType.Carrier :=
  Sum.inl budget :: (List.range budget).map Sum.inr

def dhcSelectorSkipFoldResult
    (instrs : dhcSelectorSkipInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
    dhcSelectorSkipFoldInit).2

def dhcSelectorSkipArcsExecutableFromBudget (budget : Nat) : List (Nat × Nat) :=
  dhcSelectorSkipFoldResult (dhcSelectorSkipInstructions budget)

def dhcSelectorSkipArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcSelectorSkipArcsExecutableFromBudget I.k

theorem dhcSelectorSkipArcFromBudget_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      edgeStructuredEncodedType
      dhcSelectorSkipArcFromBudget := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hNextInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBudget hSlot
  have hNext :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => dhcNextSelectorFromBudget p.1 p.2) := by
    have hComp := TMPolyTimeMap.comp dhcNextSelectorFromBudget_tm_polytime hNextInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hSlot hNext
  simpa [dhcSelectorSkipArcFromBudget, textbookSelectorVertex, edgeStructuredEncodedType, X]
    using hOut

theorem dhcSelectorSkipFoldLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.nat dhcSelectorSkipAccEncodedType
      dhcSelectorSkipFoldLeftStep := by
  have hEmpty :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun _ : Nat => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const EncodedType.nat edgeListStructuredEncodedType []
  have hOut := TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hEmpty
  simpa [dhcSelectorSkipFoldLeftStep, dhcSelectorSkipAccEncodedType] using hOut

theorem dhcSelectorSkipInstructions_tm_polytime :
    TMPolyTimeMap EncodedType.nat
      dhcSelectorSkipInstructionListEncodedType
      dhcSelectorSkipInstructions := by
  let X := EncodedType.nat
  have hInit :
      TMPolyTimeMap X dhcSelectorSkipInstructionEncodedType
        (fun budget : Nat => Sum.inl budget) := by
    simpa [dhcSelectorSkipInstructionEncodedType, X] using
      TMPolyTimeMap.inl EncodedType.nat EncodedType.nat
  have hInitSingleton :
      TMPolyTimeMap X dhcSelectorSkipInstructionListEncodedType
        (fun budget : Nat => [Sum.inl budget]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton dhcSelectorSkipInstructionEncodedType) hInit
    simpa [Function.comp, dhcSelectorSkipInstructionListEncodedType, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun budget : Nat => List.range budget) := by
    simpa [X] using natRange_tm_polytime
  have hSlotInstruction :
      TMPolyTimeMap EncodedType.nat dhcSelectorSkipInstructionEncodedType
        (fun slot : Nat => Sum.inr slot) := by
    simpa [dhcSelectorSkipInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat EncodedType.nat
  have hSlotInstrs :
      TMPolyTimeMap X dhcSelectorSkipInstructionListEncodedType
        (fun budget : Nat => (List.range budget).map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hSlotInstruction
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, dhcSelectorSkipInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcSelectorSkipInstructionListEncodedType
          dhcSelectorSkipInstructionListEncodedType)
        (fun budget : Nat => ([Sum.inl budget], (List.range budget).map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hSlotInstrs
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append dhcSelectorSkipInstructionEncodedType) hAppendInput
  simpa [Function.comp, dhcSelectorSkipInstructions,
    dhcSelectorSkipInstructionListEncodedType, X] using hAppend

theorem dhcSelectorSkipFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcSelectorSkipAccEncodedType EncodedType.nat)
      dhcSelectorSkipAccEncodedType
      dhcSelectorSkipFoldRightStep := by
  let X := EncodedType.prod dhcSelectorSkipAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X dhcSelectorSkipAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcSelectorSkipAccEncodedType EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcSelectorSkipAccEncodedType, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcSelectorSkipAccEncodedType, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcSelectorSkipAccEncodedType EncodedType.nat
  have hArcInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBudget hSlot
  have hArc :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : X.Carrier => dhcSelectorSkipArcFromBudget (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp dhcSelectorSkipArcFromBudget_tm_polytime hArcInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => [dhcSelectorSkipArcFromBudget (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hArc
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2, [dhcSelectorSkipArcFromBudget (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOutEdges hSingleton
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2) ++
            [dhcSelectorSkipArcFromBudget (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hBudget hAppend
  simpa [dhcSelectorSkipFoldRightStep, dhcSelectorSkipAccEncodedType, X] using hOut

theorem dhcSelectorSkipFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcSelectorSkipAccEncodedType
        dhcSelectorSkipInstructionEncodedType)
      dhcSelectorSkipAccEncodedType
      dhcSelectorSkipFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcSelectorSkipAccEncodedType EncodedType.nat EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcSelectorSkipFoldLeftStep_tm_polytime
      dhcSelectorSkipFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def dhcSelectorSkipFoldAccBound (N : Nat) (acc : dhcSelectorSkipAccEncodedType.Carrier) :
    Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1

noncomputable def dhcSelectorSkipFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 20 * Polynomial.X + Polynomial.C 50

theorem dhcSelectorSkipFoldGrowPolynomial_eval (N : Nat) :
    dhcSelectorSkipFoldGrowPolynomial.eval N = 20 * N + 50 := by
  simp [dhcSelectorSkipFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcNextSelectorFromBudget_le_budget (budget slot : Nat) :
    dhcNextSelectorFromBudget budget slot ≤ budget := by
  by_cases hZero : budget = 0
  · simp [dhcNextSelectorFromBudget, hZero]
  · have hPos : 0 < budget := Nat.pos_of_ne_zero hZero
    have hModLt : (slot + 1) % budget < budget := Nat.mod_lt _ hPos
    simpa [dhcNextSelectorFromBudget, hZero] using Nat.le_of_lt hModLt

theorem dhcSelectorSkipSingleton_inputSize_le
    (N budget slot : Nat)
    (hBudget : EncodedType.nat.inputSize budget ≤ N + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ N) :
    edgeListStructuredEncodedType.inputSize
        [dhcSelectorSkipArcFromBudget (budget, slot)] ≤ 20 * N + 50 := by
  have hBudgetNat : budget ≤ N := by
    simpa [EncodedType.inputSize_nat] using hBudget
  have hSlotNat : slot ≤ N := by
    have h := hSlot
    simp [EncodedType.inputSize_nat] at h
    omega
  have hNextNat : dhcNextSelectorFromBudget budget slot ≤ N :=
    (dhcNextSelectorFromBudget_le_budget budget slot).trans hBudgetNat
  simp [dhcSelectorSkipArcFromBudget, edgeListStructuredEncodedType,
    edgeStructuredEncodedType, textbookSelectorVertex, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  nlinarith

theorem dhcSelectorSkipFoldStep_growth
    (source : List dhcSelectorSkipInstructionEncodedType.Carrier)
    (acc : dhcSelectorSkipAccEncodedType.Carrier)
    (instr : dhcSelectorSkipInstructionEncodedType.Carrier)
    (hAcc : dhcSelectorSkipFoldAccBound
      (dhcSelectorSkipInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcSelectorSkipInstructionEncodedType.inputSize instr ≤
        dhcSelectorSkipInstructionListEncodedType.inputSize source) :
    dhcSelectorSkipFoldAccBound
        (dhcSelectorSkipInstructionListEncodedType.inputSize source)
        (dhcSelectorSkipFoldStep (acc, instr)) ∧
      dhcSelectorSkipAccEncodedType.inputSize (dhcSelectorSkipFoldStep (acc, instr)) ≤
        dhcSelectorSkipAccEncodedType.inputSize acc +
          dhcSelectorSkipFoldGrowPolynomial.eval
            (dhcSelectorSkipInstructionListEncodedType.inputSize source) := by
  let N := dhcSelectorSkipInstructionListEncodedType.inputSize source
  cases instr with
  | inl budget =>
      change Nat at budget
      have hBudgetElem :
          EncodedType.nat.inputSize budget ≤
            dhcSelectorSkipInstructionEncodedType.inputSize (Sum.inl budget) := by
        simp [dhcSelectorSkipInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum]
      have hBudgetN : EncodedType.nat.inputSize budget ≤ N := by
        exact hBudgetElem.trans (by simpa [N] using hInstr)
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 :=
        hBudgetN.trans (Nat.le_succ N)
      constructor
      · simpa [dhcSelectorSkipFoldAccBound, dhcSelectorSkipFoldStep,
          dhcSelectorSkipFoldLeftStep, N] using hBudget
      · have hNil :
            edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        have hBudgetNat : budget ≤ N := by
          have h : budget + 1 ≤ N := by
            simpa [EncodedType.inputSize_nat] using hBudgetN
          omega
        have hLeftSize :
            dhcSelectorSkipAccEncodedType.inputSize
                (dhcSelectorSkipFoldLeftStep budget) ≤ N + 2 := by
          simp [dhcSelectorSkipFoldLeftStep, dhcSelectorSkipAccEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
          omega
        have hTarget :
            N + 2 ≤
              dhcSelectorSkipAccEncodedType.inputSize acc +
                dhcSelectorSkipFoldGrowPolynomial.eval N := by
          rw [dhcSelectorSkipFoldGrowPolynomial_eval]
          nlinarith [Nat.zero_le (dhcSelectorSkipAccEncodedType.inputSize acc),
            Nat.zero_le N]
        simpa [dhcSelectorSkipFoldStep, N] using hLeftSize.trans hTarget
  | inr slot =>
      change Nat at slot
      have hSlotElem :
          EncodedType.nat.inputSize slot ≤
            dhcSelectorSkipInstructionEncodedType.inputSize (Sum.inr slot) := by
        simp [dhcSelectorSkipInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum]
      have hSlot : EncodedType.nat.inputSize slot ≤ N :=
        hSlotElem.trans (by simpa [N] using hInstr)
      constructor
      · simpa [dhcSelectorSkipFoldStep, dhcSelectorSkipFoldRightStep, N] using hAcc
      · let block : List (Nat × Nat) := [dhcSelectorSkipArcFromBudget (acc.1, slot)]
        have hAppend :
            edgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat) from acc.2) ++ block) =
              edgeListStructuredEncodedType.inputSize acc.2 +
                edgeListStructuredEncodedType.inputSize block := by
          simpa [edgeListStructuredEncodedType, block] using
            Clique.encodedList_inputSize_append edgeStructuredEncodedType
              (show List (Nat × Nat) from acc.2) block
        have hBlock :
            edgeListStructuredEncodedType.inputSize block ≤ 20 * N + 50 := by
          simpa [block] using
            dhcSelectorSkipSingleton_inputSize_le N acc.1 slot hAcc hSlot
        calc
          dhcSelectorSkipAccEncodedType.inputSize
              (dhcSelectorSkipFoldStep (acc, Sum.inr slot))
              =
            EncodedType.nat.inputSize acc.1 + 1 +
              edgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat) from acc.2) ++ block) := by
              simp [dhcSelectorSkipFoldStep, dhcSelectorSkipFoldRightStep,
                dhcSelectorSkipAccEncodedType, EncodedType.inputSize_prod, block]
          _ =
            EncodedType.nat.inputSize acc.1 + 1 +
              (edgeListStructuredEncodedType.inputSize acc.2 +
                edgeListStructuredEncodedType.inputSize block) := by
              rw [hAppend]
          _ ≤
            dhcSelectorSkipAccEncodedType.inputSize acc +
              dhcSelectorSkipFoldGrowPolynomial.eval N := by
              rw [dhcSelectorSkipFoldGrowPolynomial_eval]
              simp [dhcSelectorSkipAccEncodedType, EncodedType.inputSize_prod]
              nlinarith

theorem dhcSelectorSkipFold_tm_polytime :
    TMPolyTimeMap
      dhcSelectorSkipInstructionListEncodedType
      dhcSelectorSkipAccEncodedType
      (fun xs : List dhcSelectorSkipInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
          dhcSelectorSkipFoldInit) := by
  rcases dhcSelectorSkipFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcSelectorSkipInstructionEncodedType dhcSelectorSkipAccEncodedType
      dhcSelectorSkipFoldStep dhcSelectorSkipFoldInit hStep
      (Polynomial.C 5) dhcSelectorSkipFoldGrowPolynomial
      dhcSelectorSkipFoldAccBound ?_ ?_
  · intro xs
    constructor
    · simp [dhcSelectorSkipFoldInit, dhcSelectorSkipFoldAccBound, EncodedType.inputSize_nat]
    · have hNil :
          edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcSelectorSkipFoldInit, dhcSelectorSkipAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
  · intro source acc instr hAcc hInstr
    simpa [dhcSelectorSkipInstructionListEncodedType] using
      dhcSelectorSkipFoldStep_growth source acc instr hAcc hInstr

theorem dhcSelectorSkipFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcSelectorSkipInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcSelectorSkipFoldResult := by
  have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd dhcSelectorSkipFold_tm_polytime
  simpa [Function.comp, dhcSelectorSkipFoldResult, dhcSelectorSkipAccEncodedType] using hComp

theorem dhcSelectorSkipArcsExecutableFromBudget_tm_polytime :
    TMPolyTimeMap EncodedType.nat
      edgeListStructuredEncodedType
      dhcSelectorSkipArcsExecutableFromBudget := by
  have hComp := TMPolyTimeMap.comp
    dhcSelectorSkipFoldResult_tm_polytime
    dhcSelectorSkipInstructions_tm_polytime
  simpa [Function.comp, dhcSelectorSkipArcsExecutableFromBudget] using hComp

theorem dhcSelectorSkipArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcSelectorSkipArcsExecutableFromInput := by
  have hComp := TMPolyTimeMap.comp
    dhcSelectorSkipArcsExecutableFromBudget_tm_polytime
    vertexCoverBudgetTMBackedMap.tm_polytime
  simpa [Function.comp, dhcSelectorSkipArcsExecutableFromInput] using hComp

theorem dhcSelectorSkipFold_map_invariant
    (budget : Nat) (slots : List Nat) (out : List (Nat × Nat)) :
    (slots.map Sum.inr).foldl
        (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
        (budget, out) =
      (budget,
        out ++
          (slots.map fun slot => dhcSelectorSkipArcFromBudget (budget, slot))) := by
  induction slots generalizing out with
  | nil =>
      simp
      rfl
  | cons slot slots ih =>
      calc
        ((slot :: slots).map Sum.inr).foldl
            (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
            (budget, out)
            =
          (slots.map Sum.inr).foldl
            (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
            (budget, out ++ [dhcSelectorSkipArcFromBudget (budget, slot)]) := by
            rfl
        _ =
          (budget,
            (out ++ [dhcSelectorSkipArcFromBudget (budget, slot)]) ++
              (slots.map fun slot =>
                dhcSelectorSkipArcFromBudget (budget, slot))) :=
            ih (out ++ [dhcSelectorSkipArcFromBudget (budget, slot)])
        _ =
          (budget,
            out ++
              (dhcSelectorSkipArcFromBudget (budget, slot) ::
                slots.map fun slot =>
                  dhcSelectorSkipArcFromBudget (budget, slot))) := by
            simp [List.append_assoc]

theorem dhcSelectorSkipArcsExecutableFromBudget_eq (budget : Nat) :
    dhcSelectorSkipArcsExecutableFromBudget budget =
      (List.range budget).map fun slot =>
        dhcSelectorSkipArcFromBudget (budget, slot) := by
  rw [dhcSelectorSkipArcsExecutableFromBudget, dhcSelectorSkipFoldResult,
    dhcSelectorSkipInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcSelectorSkipFoldStep (dhcSelectorSkipFoldInit, Sum.inl budget) =
        (budget, ([] : List (Nat × Nat))) by
    rfl]
  change
    (List.foldl (fun acc instr => dhcSelectorSkipFoldStep (acc, instr))
      (budget, []) (List.map Sum.inr (List.range budget))).2 =
      (List.range budget).map fun slot =>
        dhcSelectorSkipArcFromBudget (budget, slot)
  have hFold :=
    congrArg (fun acc : dhcSelectorSkipAccEncodedType.Carrier => acc.2)
      (dhcSelectorSkipFold_map_invariant budget (List.range budget)
        ([] : List (Nat × Nat)))
  simpa using hFold

theorem dhcSelectorSkipArcsExecutableFromInput_eq_dhcSelectorSkipArcsFromInput
    (I : VertexCoverInput) :
    dhcSelectorSkipArcsExecutableFromInput I = dhcSelectorSkipArcsFromInput I := by
  simp [dhcSelectorSkipArcsExecutableFromInput,
    dhcSelectorSkipArcsExecutableFromBudget_eq,
    dhcSelectorSkipArcsFromInput, dhcSelectorSkipArcFromBudget,
    dhcNextSelectorFromBudget_eq_textbookNextSelector]

theorem dhcSelectorSkipArcsExecutableFromInput_eq_textbookSelectorSkipArcs
    (I : VertexCoverInput) :
    dhcSelectorSkipArcsExecutableFromInput I = textbookSelectorSkipArcs I := by
  rw [dhcSelectorSkipArcsExecutableFromInput_eq_dhcSelectorSkipArcsFromInput]
  exact dhcSelectorSkipArcsFromInput_eq_textbookSelectorSkipArcs I

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
