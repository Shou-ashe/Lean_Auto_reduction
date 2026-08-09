/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.FamilyEdges

/-!
Terminal-list assembly for the compact Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

def compactTerminalListAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)

def compactTerminalListInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat EncodedType.nat

def compactTerminalListInstructionListEncodedType : EncodedType :=
  EncodedType.list compactTerminalListInstructionEncodedType

def compactTerminalListInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def compactTerminalListInitAcc : Nat × List Nat :=
  (0, [])

def compactTerminalListInitInstruction (setCount : Nat) :
    compactTerminalListInstructionEncodedType.Carrier :=
  Sum.inl setCount

def compactTerminalListElementInstruction (x : Nat) :
    compactTerminalListInstructionEncodedType.Carrier :=
  Sum.inr x

def compactTerminalListInstructions (p : Nat × Nat) :
    List compactTerminalListInstructionEncodedType.Carrier :=
  compactTerminalListInitInstruction p.1 ::
    (List.range p.2).map compactTerminalListElementInstruction

def compactTerminalListElementStep (p : (Nat × List Nat) × Nat) :
    Nat × List Nat :=
  let terminal := compactTerminalNodeFromCounts (p.1.1, p.2)
  (p.1.1, p.1.2 ++ [terminal])

def compactTerminalListStep
    (p : (Nat × List Nat) × compactTerminalListInstructionEncodedType.Carrier) :
    Nat × List Nat :=
  match p.2 with
  | Sum.inl setCount => (setCount, [])
  | Sum.inr x => compactTerminalListElementStep (p.1, x)

def compactTerminalListFromInstructions
    (xs : List compactTerminalListInstructionEncodedType.Carrier) : List Nat :=
  rootNode ::
    (xs.foldl (fun acc instr => compactTerminalListStep (acc, instr))
      compactTerminalListInitAcc).2

def compactTerminalsExecutable (p : Nat × Nat) : List Nat :=
  compactTerminalListFromInstructions (compactTerminalListInstructions p)

/-! ### Semantics -/

theorem compactTerminalListElementFold_eq_append_map
    (xs : List Nat) (setCount : Nat) (out : List Nat) :
    ((xs.map compactTerminalListElementInstruction).foldl
        (fun acc instr => compactTerminalListStep (acc, instr))
        (setCount, out)).2 =
      out ++ xs.map (fun x => compactTerminalNodeFromCounts (setCount, x)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactTerminalListElementInstruction, compactTerminalListStep,
        compactTerminalListElementStep]
      have hTail := ih (out ++ [compactTerminalNodeFromCounts (setCount, x)])
      simpa [compactTerminalListStep, List.append_assoc] using hTail

theorem compactTerminalsExecutable_eq_map (p : Nat × Nat) :
    compactTerminalsExecutable p =
      rootNode :: (List.range p.2).map
        (fun x => compactTerminalNodeFromCounts (p.1, x)) := by
  change
    rootNode ::
        (((List.range p.2).map compactTerminalListElementInstruction).foldl
          (fun acc instr => compactTerminalListStep (acc, instr)) (p.1, [])).2 =
      rootNode :: (List.range p.2).map
        (fun x => compactTerminalNodeFromCounts (p.1, x))
  simpa using compactTerminalListElementFold_eq_append_map (List.range p.2) p.1 []

theorem compactTerminalsExecutable_eq_compactTerminals (I : ExactCoverInput) :
    compactTerminalsExecutable (I.system.sets.length, I.system.universeSize) =
      compactTerminals I := by
  simp [compactTerminalsExecutable_eq_map, compactTerminals,
    compactTerminalNodeFromCounts, compactTerminalNode]

/-! ### TM witnesses -/

theorem compactTerminalListInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactTerminalListInstructionEncodedType
      compactTerminalListInitInstruction := by
  simpa [compactTerminalListInstructionEncodedType, compactTerminalListInitInstruction] using
    TMPolyTimeMap.inl EncodedType.nat EncodedType.nat

theorem compactTerminalListElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactTerminalListInstructionEncodedType
      compactTerminalListElementInstruction := by
  simpa [compactTerminalListInstructionEncodedType, compactTerminalListElementInstruction] using
    TMPolyTimeMap.inr EncodedType.nat EncodedType.nat

theorem compactTerminalListInstructions_tm_polytime :
    TMPolyTimeMap
      compactTerminalListInputEncodedType
      compactTerminalListInstructionListEncodedType
      compactTerminalListInstructions := by
  let X := compactTerminalListInputEncodedType
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactTerminalListInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, compactTerminalListInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hInit :
      TMPolyTimeMap X compactTerminalListInstructionEncodedType
        (fun p : X.Carrier => compactTerminalListInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp compactTerminalListInitInstruction_tm_polytime hSetCount
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactTerminalListInstructionListEncodedType
        (fun p : X.Carrier =>
          (List.range p.2).map compactTerminalListElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactTerminalListElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactTerminalListInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactTerminalListInstructionEncodedType
          compactTerminalListInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactTerminalListInitInstruction p.1,
            (List.range p.2).map compactTerminalListElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactTerminalListInstructionEncodedType) hConsInput
  simpa [Function.comp, compactTerminalListInstructions,
    compactTerminalListInstructionListEncodedType, X] using hCons

theorem compactTerminalListStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactTerminalListAccEncodedType
      (fun setCount : Nat => (setCount, ([] : List Nat))) := by
  have hSetCount := TMPolyTimeMap.id EncodedType.nat
  have hEmpty :
      TMPolyTimeMap EncodedType.nat (EncodedType.list EncodedType.nat)
        (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat (EncodedType.list EncodedType.nat) []
  simpa [compactTerminalListAccEncodedType] using TMPolyTimeMap.prod_mk hSetCount hEmpty

theorem compactTerminalListElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactTerminalListAccEncodedType EncodedType.nat)
      compactTerminalListAccEncodedType
      compactTerminalListElementStep := by
  let X := EncodedType.prod compactTerminalListAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactTerminalListAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactTerminalListAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactTerminalListAccEncodedType EncodedType.nat
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactTerminalListAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactTerminalListAccEncodedType, X] using hComp
  have hTerminalInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hSetCount hX
  have hTerminal :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => compactTerminalNodeFromCounts (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactTerminalNodeFromCounts_tm_polytime hTerminalInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => [compactTerminalNodeFromCounts (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hTerminal
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.nat) (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier =>
          ((show List Nat from p.1.2), [compactTerminalNodeFromCounts (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier =>
          (show List Nat from p.1.2) ++ [compactTerminalNodeFromCounts (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, X] using hComp
  have hOutPair := TMPolyTimeMap.prod_mk hSetCount hAppend
  simpa [compactTerminalListElementStep, compactTerminalListAccEncodedType, X] using hOutPair

theorem compactTerminalListStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactTerminalListAccEncodedType compactTerminalListInstructionEncodedType)
      compactTerminalListAccEncodedType
      compactTerminalListStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactTerminalListAccEncodedType EncodedType.nat EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactTerminalListStepLeft_tm_polytime
      compactTerminalListElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactTerminalListFoldInv (N : Nat) (acc : compactTerminalListAccEncodedType.Carrier) :
    Prop :=
  acc = compactTerminalListInitAcc ∨ (show Nat from acc.1) + 1 ≤ N

theorem compactTerminalListInitAcc_bound
    (xs : List compactTerminalListInstructionEncodedType.Carrier) :
    compactTerminalListFoldInv (compactTerminalListInstructionListEncodedType.inputSize xs)
        compactTerminalListInitAcc ∧
      compactTerminalListAccEncodedType.inputSize compactTerminalListInitAcc ≤
        (Polynomial.C 10).eval (compactTerminalListInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNil :
        (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.nat
    simp [compactTerminalListInitAcc, compactTerminalListAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]

theorem compactTerminalListStep_growth
    (source : List compactTerminalListInstructionEncodedType.Carrier)
    (acc : compactTerminalListAccEncodedType.Carrier)
    (instr : compactTerminalListInstructionEncodedType.Carrier)
    (hInv :
      compactTerminalListFoldInv
        (compactTerminalListInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactTerminalListInstructionEncodedType.inputSize instr ≤
        compactTerminalListInstructionListEncodedType.inputSize source) :
    compactTerminalListFoldInv
        (compactTerminalListInstructionListEncodedType.inputSize source)
        (compactTerminalListStep (acc, instr)) ∧
      compactTerminalListAccEncodedType.inputSize (compactTerminalListStep (acc, instr)) ≤
        compactTerminalListAccEncodedType.inputSize acc +
          (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
            (compactTerminalListInstructionListEncodedType.inputSize source) := by
  let N := compactTerminalListInstructionListEncodedType.inputSize source
  rcases acc with ⟨setCount, out⟩
  change Nat at setCount
  cases instr with
  | inl newSetCount =>
      change Nat at newSetCount
      have hNewSetCount : newSetCount + 1 ≤ N := by
        have hTagged : newSetCount + 1 < N := by
          simpa [N, compactTerminalListInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      constructor
      · exact Or.inr hNewSetCount
      · have hNil :
            (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0 :=
          EncodedType.inputSize_list_nil EncodedType.nat
        simp [compactTerminalListStep, compactTerminalListAccEncodedType,
          EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
  | inr x =>
      change Nat at x
      have hx : x + 1 ≤ N := by
        have hTagged : x + 1 < N := by
          simpa [N, compactTerminalListInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hSetCount : setCount + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hSetCountEq _hOut
          subst setCount
          omega
        · exact hBound
      have hSingleton :
          (EncodedType.list EncodedType.nat).inputSize
              [compactTerminalNodeFromCounts (setCount, x)] ≤ 10 * N + 20 := by
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        simp [compactTerminalNodeFromCounts, EncodedType.inputSize_nat]
        omega
      have hTerminalSize :
          compactTerminalNodeFromCounts (setCount, x) + 2 ≤ 10 * N + 20 := by
        simp [compactTerminalNodeFromCounts]
        omega
      have hAppendSize :
          (EncodedType.list EncodedType.nat).inputSize
              ((show List Nat from out) ++ [compactTerminalNodeFromCounts (setCount, x)]) =
            (EncodedType.list EncodedType.nat).inputSize out +
              (EncodedType.list EncodedType.nat).inputSize
                [compactTerminalNodeFromCounts (setCount, x)] := by
        simpa using
          list_inputSize_append EncodedType.nat out [compactTerminalNodeFromCounts (setCount, x)]
      constructor
      · exact Or.inr hSetCount
      · simp [compactTerminalListStep, compactTerminalListElementStep,
          compactTerminalListAccEncodedType, EncodedType.inputSize_prod, hAppendSize,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega

theorem compactTerminalListFold_tm_polytime :
    TMPolyTimeMap
      compactTerminalListInstructionListEncodedType
      compactTerminalListAccEncodedType
      (fun xs : List compactTerminalListInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactTerminalListStep (acc, instr))
          compactTerminalListInitAcc) := by
  rcases compactTerminalListStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactTerminalListInstructionEncodedType compactTerminalListAccEncodedType
      compactTerminalListStep compactTerminalListInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20)
      compactTerminalListFoldInv ?_ ?_
  · intro xs
    exact compactTerminalListInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactTerminalListStep_growth source acc instr hInv hInstr

theorem compactTerminalListFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactTerminalListInstructionListEncodedType
      (EncodedType.list EncodedType.nat)
      compactTerminalListFromInstructions := by
  let X := compactTerminalListInstructionListEncodedType
  have hFold := compactTerminalListFold_tm_polytime
  have hTail :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun xs : X.Carrier =>
          (xs.foldl (fun acc instr => compactTerminalListStep (acc, instr))
            compactTerminalListInitAcc).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hFold
    simpa [Function.comp, compactTerminalListAccEncodedType, X] using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => rootNode) :=
    TMPolyTimeMap.const X EncodedType.nat rootNode
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun xs : X.Carrier =>
          (rootNode,
            (xs.foldl (fun acc instr => compactTerminalListStep (acc, instr))
              compactTerminalListInitAcc).2)) :=
    TMPolyTimeMap.prod_mk hRoot hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons EncodedType.nat) hConsInput
  simpa [Function.comp, compactTerminalListFromInstructions, X] using hCons

theorem compactTerminalsExecutable_tm_polytime :
    TMPolyTimeMap
      compactTerminalListInputEncodedType
      (EncodedType.list EncodedType.nat)
      compactTerminalsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactTerminalListFromInstructions_tm_polytime
      compactTerminalListInstructions_tm_polytime
  simpa [Function.comp, compactTerminalsExecutable] using hComp

end SteinerTree
end Karp21
end ComplexityReduction
