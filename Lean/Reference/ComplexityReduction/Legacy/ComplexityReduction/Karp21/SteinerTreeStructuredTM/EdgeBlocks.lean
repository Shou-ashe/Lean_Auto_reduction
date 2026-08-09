/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Support
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

/-!
Executable edge blocks for one source set in the compact
Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Node arithmetic and single weighted edges -/

def compactTerminalNodeFromCounts (p : Nat × Nat) : Nat :=
  p.1 + p.2 + 1

theorem compactTerminalNodeFromCounts_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      compactTerminalNodeFromCounts := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hAdd := natAdd_tm_polytime
  have hSucc := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAdd
  simpa [Function.comp, compactTerminalNodeFromCounts, Nat.succ_eq_add_one,
    natAddInputEncodedType, X] using hSucc

theorem compactSetNode_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat compactSetNode := by
  simpa [compactSetNode, Nat.succ_eq_add_one] using natSuccTMBackedMap.tm_polytime

def compactTerminalEdgeFromCounts (p : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (compactSetNode p.2.1, compactTerminalNodeFromCounts (p.1, p.2.2), 0)

def compactTerminalEdgeInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

theorem compactTerminalEdgeFromCounts_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeInputEncodedType
      weightedEdgeStructuredEncodedType
      compactTerminalEdgeFromCounts := by
  let X := compactTerminalEdgeInputEncodedType
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactTerminalEdgeInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactTerminalEdgeInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hSetNode : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => compactSetNode p.2.1) := by
    have hComp := TMPolyTimeMap.comp compactSetNode_tm_polytime hJ
    simpa [Function.comp, X] using hComp
  have hTerminalInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hSetCount hX
  have hTerminal :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => compactTerminalNodeFromCounts (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactTerminalNodeFromCounts_tm_polytime hTerminalInput
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (compactTerminalNodeFromCounts (p.1, p.2.2), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hTerminal hZero
  have hOut := TMPolyTimeMap.prod_mk hSetNode hTail
  simpa [compactTerminalEdgeFromCounts, weightedEdgeStructuredEncodedType, X] using hOut

theorem compactTerminalEdgeFromCounts_eq
    (I : ExactCoverInput) (j x : Nat) :
    compactTerminalEdgeFromCounts (I.system.sets.length, j, x) =
      compactTerminalEdge I j x := by
  simp [compactTerminalEdgeFromCounts, compactTerminalEdge,
    compactTerminalNodeFromCounts, compactTerminalNode]

/-! ### Terminal-edge list for one support list -/

def compactTerminalEdgeContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def compactTerminalEdgeAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)

def compactTerminalEdgeInstructionEncodedType : EncodedType :=
  EncodedType.sum compactTerminalEdgeContextEncodedType EncodedType.nat

def compactTerminalEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list compactTerminalEdgeInstructionEncodedType

def compactTerminalEdgeListInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))

def compactTerminalEdgeInitAcc : compactTerminalEdgeAccEncodedType.Carrier :=
  ((0 : Nat), ((0 : Nat), ([] : List (Nat × Nat × Nat))))

def compactTerminalEdgeInitInstruction (ctx : Nat × Nat) :
    compactTerminalEdgeInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactTerminalEdgeElementInstruction (x : Nat) :
    compactTerminalEdgeInstructionEncodedType.Carrier :=
  Sum.inr x

def compactTerminalEdgeInstructions (p : Nat × Nat × List Nat) :
    List compactTerminalEdgeInstructionEncodedType.Carrier :=
  compactTerminalEdgeInitInstruction (p.1, p.2.1) ::
    p.2.2.map compactTerminalEdgeElementInstruction

def compactTerminalEdgeElementStep
    (p : compactTerminalEdgeAccEncodedType.Carrier × Nat) :
    compactTerminalEdgeAccEncodedType.Carrier :=
  let edge := compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)
  (p.1.1, (p.1.2.1, (show List (Nat × Nat × Nat) from p.1.2.2) ++ [edge]))

def compactTerminalEdgeStep
    (p : compactTerminalEdgeAccEncodedType.Carrier ×
      compactTerminalEdgeInstructionEncodedType.Carrier) :
    compactTerminalEdgeAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx.1, (ctx.2, []))
  | Sum.inr x => compactTerminalEdgeElementStep (p.1, x)

def compactTerminalEdgesFromInstructions
    (xs : List compactTerminalEdgeInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactTerminalEdgeStep (acc, instr))
    compactTerminalEdgeInitAcc).2.2

def compactTerminalEdgesExecutable (p : Nat × Nat × List Nat) :
    List (Nat × Nat × Nat) :=
  compactTerminalEdgesFromInstructions (compactTerminalEdgeInstructions p)

theorem compactTerminalEdgeElementFold_eq_append_map
    (xs : List Nat) (setCount j : Nat) (out : List (Nat × Nat × Nat)) :
    ((xs.map compactTerminalEdgeElementInstruction).foldl
        (fun acc instr => compactTerminalEdgeStep (acc, instr))
        (setCount, (j, out))).2.2 =
      out ++ xs.map (fun x => compactTerminalEdgeFromCounts (setCount, j, x)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactTerminalEdgeElementInstruction, compactTerminalEdgeStep,
        compactTerminalEdgeElementStep]
      have hTail := ih (out ++ [compactTerminalEdgeFromCounts (setCount, j, x)])
      simpa [compactTerminalEdgeStep, List.append_assoc] using hTail

theorem compactTerminalEdgesExecutable_eq_map
    (setCount j : Nat) (support : List Nat) :
    compactTerminalEdgesExecutable (setCount, j, support) =
      support.map (fun x => compactTerminalEdgeFromCounts (setCount, j, x)) := by
  change
    ((support.map compactTerminalEdgeElementInstruction).foldl
        (fun acc instr => compactTerminalEdgeStep (acc, instr))
        (setCount, (j, []))).2.2 =
      support.map (fun x => compactTerminalEdgeFromCounts (setCount, j, x))
  simpa using compactTerminalEdgeElementFold_eq_append_map support setCount j []

theorem compactTerminalEdgesExecutable_eq_compact
    (I : ExactCoverInput) (j : Nat) (support : List Nat) :
    compactTerminalEdgesExecutable (I.system.sets.length, j, support) =
      support.map (compactTerminalEdge I j) := by
  rw [compactTerminalEdgesExecutable_eq_map]
  apply List.map_congr_left
  intro x _hx
  exact compactTerminalEdgeFromCounts_eq I j x

/-! ### TM certificates for terminal-edge lists -/

theorem compactTerminalEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeContextEncodedType
      compactTerminalEdgeInstructionEncodedType
      compactTerminalEdgeInitInstruction := by
  simpa [compactTerminalEdgeInstructionEncodedType, compactTerminalEdgeInitInstruction] using
    TMPolyTimeMap.inl compactTerminalEdgeContextEncodedType EncodedType.nat

theorem compactTerminalEdgeElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactTerminalEdgeInstructionEncodedType
      compactTerminalEdgeElementInstruction := by
  simpa [compactTerminalEdgeInstructionEncodedType,
    compactTerminalEdgeElementInstruction] using
    TMPolyTimeMap.inr compactTerminalEdgeContextEncodedType EncodedType.nat

theorem compactTerminalEdgeInstructions_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeListInputEncodedType
      compactTerminalEdgeInstructionListEncodedType
      compactTerminalEdgeInstructions := by
  let X := compactTerminalEdgeListInputEncodedType
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactTerminalEdgeListInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactTerminalEdgeListInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hSupport :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hCtx :
      TMPolyTimeMap X compactTerminalEdgeContextEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hSetCount hJ
  have hInit :
      TMPolyTimeMap X compactTerminalEdgeInstructionEncodedType
        (fun p : X.Carrier => compactTerminalEdgeInitInstruction (p.1, p.2.1)) := by
    have hComp := TMPolyTimeMap.comp compactTerminalEdgeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactTerminalEdgeInstructionListEncodedType
        (fun p : X.Carrier => p.2.2.map compactTerminalEdgeElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactTerminalEdgeElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSupport
    simpa [Function.comp, compactTerminalEdgeInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactTerminalEdgeInstructionEncodedType
          compactTerminalEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactTerminalEdgeInitInstruction (p.1, p.2.1),
            p.2.2.map compactTerminalEdgeElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactTerminalEdgeInstructionEncodedType) hConsInput
  simpa [Function.comp, compactTerminalEdgeInstructions,
    compactTerminalEdgeInstructionListEncodedType, X] using hCons

theorem compactTerminalEdgeStepLeft_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeContextEncodedType
      compactTerminalEdgeAccEncodedType
      (fun ctx : Nat × Nat => (ctx.1, (ctx.2, []))) := by
  let X := compactTerminalEdgeContextEncodedType
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.1) := by
    simpa [X, compactTerminalEdgeContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, compactTerminalEdgeContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hNil :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const X weightedEdgeListStructuredEncodedType []
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
        (fun ctx : X.Carrier => (ctx.2, [])) :=
    TMPolyTimeMap.prod_mk hJ hNil
  have hOut := TMPolyTimeMap.prod_mk hSetCount hTail
  simpa [compactTerminalEdgeAccEncodedType, X] using hOut

theorem compactTerminalEdgeElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactTerminalEdgeAccEncodedType EncodedType.nat)
      compactTerminalEdgeAccEncodedType
      compactTerminalEdgeElementStep := by
  let X := EncodedType.prod compactTerminalEdgeAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactTerminalEdgeAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactTerminalEdgeAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactTerminalEdgeAccEncodedType EncodedType.nat
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactTerminalEdgeAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactTerminalEdgeAccEncodedType, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat weightedEdgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hOutList :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat weightedEdgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hEdgeInput :
      TMPolyTimeMap X compactTerminalEdgeInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2.1, p.2)) := by
    have hJX : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1.2.1, p.2)) :=
      TMPolyTimeMap.prod_mk hJ hX
    simpa [compactTerminalEdgeInputEncodedType] using
      TMPolyTimeMap.prod_mk hSetCount hJX
  have hEdge :
      TMPolyTimeMap X weightedEdgeStructuredEncodedType
        (fun p : X.Carrier => compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactTerminalEdgeFromCounts_tm_polytime hEdgeInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier => [compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton weightedEdgeStructuredEncodedType) hEdge
    simpa [Function.comp, weightedEdgeListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod weightedEdgeListStructuredEncodedType
          weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2.2),
            [compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOutList hSingleton
  have hAppend :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2.2) ++
            [compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append weightedEdgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, weightedEdgeListStructuredEncodedType, X] using hComp
  have hTailOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.1,
            (show List (Nat × Nat × Nat) from p.1.2.2) ++
              [compactTerminalEdgeFromCounts (p.1.1, p.1.2.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hJ hAppend
  have hOut := TMPolyTimeMap.prod_mk hSetCount hTailOut
  simpa [compactTerminalEdgeElementStep, compactTerminalEdgeAccEncodedType, X] using hOut

theorem compactTerminalEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactTerminalEdgeAccEncodedType
        compactTerminalEdgeInstructionEncodedType)
      compactTerminalEdgeAccEncodedType
      compactTerminalEdgeStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactTerminalEdgeAccEncodedType compactTerminalEdgeContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactTerminalEdgeStepLeft_tm_polytime
      compactTerminalEdgeElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactTerminalEdgeFoldInv
    (N : Nat) (acc : compactTerminalEdgeAccEncodedType.Carrier) : Prop :=
  acc = compactTerminalEdgeInitAcc ∨
    ((show Nat from acc.1) + 1 ≤ N ∧ (show Nat from acc.2.1) + 1 ≤ N)

theorem compactTerminalEdgeInitAcc_bound
    (xs : List compactTerminalEdgeInstructionEncodedType.Carrier) :
    compactTerminalEdgeFoldInv (compactTerminalEdgeInstructionListEncodedType.inputSize xs)
        compactTerminalEdgeInitAcc ∧
      compactTerminalEdgeAccEncodedType.inputSize compactTerminalEdgeInitAcc ≤
        (Polynomial.C 10).eval (compactTerminalEdgeInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNil :
        weightedEdgeStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil weightedEdgeStructuredEncodedType
    simp [compactTerminalEdgeInitAcc, compactTerminalEdgeAccEncodedType,
      weightedEdgeListStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNil]

theorem compactTerminalEdgeSingleton_inputSize_le
    (N setCount j x : Nat)
    (hSetCount : setCount + 1 ≤ N) (hj : j + 1 ≤ N) (hx : x + 2 ≤ N) :
    weightedEdgeListStructuredEncodedType.inputSize
        [compactTerminalEdgeFromCounts (setCount, j, x)] ≤
      10 * N + 20 := by
  simp [weightedEdgeListStructuredEncodedType, weightedEdgeStructuredEncodedType,
    compactTerminalEdgeFromCounts, compactSetNode, compactTerminalNodeFromCounts,
    EncodedType.inputSize, EncodedType.list, EncodedType.prod, EncodedType.nat]
  omega

theorem compactTerminalEdgeStep_growth
    (source : List compactTerminalEdgeInstructionEncodedType.Carrier)
    (acc : compactTerminalEdgeAccEncodedType.Carrier)
    (instr : compactTerminalEdgeInstructionEncodedType.Carrier)
    (hInv :
      compactTerminalEdgeFoldInv
        (compactTerminalEdgeInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactTerminalEdgeInstructionEncodedType.inputSize instr ≤
        compactTerminalEdgeInstructionListEncodedType.inputSize source) :
    compactTerminalEdgeFoldInv
        (compactTerminalEdgeInstructionListEncodedType.inputSize source)
        (compactTerminalEdgeStep (acc, instr)) ∧
      compactTerminalEdgeAccEncodedType.inputSize (compactTerminalEdgeStep (acc, instr)) ≤
        compactTerminalEdgeAccEncodedType.inputSize acc +
          (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
            (compactTerminalEdgeInstructionListEncodedType.inputSize source) := by
  let N := compactTerminalEdgeInstructionListEncodedType.inputSize source
  rcases acc with ⟨setCount, j, out⟩
  change Nat at setCount
  change Nat at j
  cases instr with
  | inl ctx =>
      rcases ctx with ⟨newSetCount, newJ⟩
      change Nat at newSetCount
      change Nat at newJ
      have hCtx : compactTerminalEdgeContextEncodedType.inputSize (newSetCount, newJ) + 1 ≤ N := by
        simpa [N, compactTerminalEdgeInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewSet : newSetCount + 1 ≤ N := by
        simp [compactTerminalEdgeContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewJ : newJ + 1 ≤ N := by
        simp [compactTerminalEdgeContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewSet, hNewJ⟩
      · simp [compactTerminalEdgeStep, compactTerminalEdgeAccEncodedType,
          weightedEdgeListStructuredEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
  | inr x =>
      change Nat at x
      have hx : x + 2 ≤ N := by
        have hxTagged : x + 1 < N := by
          simpa [N, compactTerminalEdgeInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hBounds : setCount + 1 ≤ N ∧ j + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hSet hTail
          injection hTail with hJ _hOut
          subst setCount
          subst j
          omega
        · exact hBound
      have hSingleton :=
        compactTerminalEdgeSingleton_inputSize_le N setCount j x hBounds.1 hBounds.2 hx
      have hAppendSize :
          weightedEdgeListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++
                [compactTerminalEdgeFromCounts (setCount, j, x)]) =
            weightedEdgeListStructuredEncodedType.inputSize out +
              weightedEdgeListStructuredEncodedType.inputSize
                [compactTerminalEdgeFromCounts (setCount, j, x)] := by
        simpa [weightedEdgeListStructuredEncodedType] using
          list_inputSize_append weightedEdgeStructuredEncodedType out
            [compactTerminalEdgeFromCounts (setCount, j, x)]
      constructor
      · exact Or.inr hBounds
      · simp [compactTerminalEdgeStep, compactTerminalEdgeElementStep,
          compactTerminalEdgeAccEncodedType, EncodedType.inputSize_prod, hAppendSize,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega

theorem compactTerminalEdgeFold_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeInstructionListEncodedType
      compactTerminalEdgeAccEncodedType
      (fun xs : List compactTerminalEdgeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactTerminalEdgeStep (acc, instr))
          compactTerminalEdgeInitAcc) := by
  rcases compactTerminalEdgeStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactTerminalEdgeInstructionEncodedType compactTerminalEdgeAccEncodedType
      compactTerminalEdgeStep compactTerminalEdgeInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20)
      compactTerminalEdgeFoldInv ?_ ?_
  · intro xs
    exact compactTerminalEdgeInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactTerminalEdgeStep_growth source acc instr hInv hInstr

theorem compactTerminalEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeInstructionListEncodedType
      weightedEdgeListStructuredEncodedType
      compactTerminalEdgesFromInstructions := by
  have hFold := compactTerminalEdgeFold_tm_polytime
  have hTail := TMPolyTimeMap.snd EncodedType.nat
    (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
  have hOutList := TMPolyTimeMap.snd EncodedType.nat weightedEdgeListStructuredEncodedType
  have hCompTail := TMPolyTimeMap.comp hTail hFold
  have hComp := TMPolyTimeMap.comp hOutList hCompTail
  simpa [Function.comp, compactTerminalEdgesFromInstructions,
    compactTerminalEdgeAccEncodedType] using hComp

theorem compactTerminalEdgesExecutable_tm_polytime :
    TMPolyTimeMap
      compactTerminalEdgeListInputEncodedType
      weightedEdgeListStructuredEncodedType
      compactTerminalEdgesExecutable := by
  have hComp := TMPolyTimeMap.comp compactTerminalEdgesFromInstructions_tm_polytime
    compactTerminalEdgeInstructions_tm_polytime
  simpa [Function.comp, compactTerminalEdgesExecutable] using hComp

/-! ### One source-set block -/

def compactRootEdgeInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat setStructuredEncodedType)

def compactRootEdgeFromSource (p : Nat × Nat × List Nat) : Nat × Nat × Nat :=
  (rootNode, compactSetNode p.2.1, (compactSupportExecutable (p.1, p.2.2)).length)

theorem compactRootEdgeFromSource_tm_polytime :
    TMPolyTimeMap
      compactRootEdgeInputEncodedType
      weightedEdgeStructuredEncodedType
      compactRootEdgeFromSource := by
  let X := compactRootEdgeInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactRootEdgeInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactRootEdgeInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hSupportInput :
      TMPolyTimeMap X compactSupportInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSet
  have hSupport :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => compactSupportExecutable (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactSupportExecutable_tm_polytime hSupportInput
    simpa [Function.comp, X] using hComp
  have hWeight :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => (compactSupportExecutable (p.1, p.2.2)).length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hSupport
    simpa [Function.comp, X] using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => rootNode) :=
    TMPolyTimeMap.const X EncodedType.nat rootNode
  have hSetNode :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => compactSetNode p.2.1) := by
    have hComp := TMPolyTimeMap.comp compactSetNode_tm_polytime hJ
    simpa [Function.comp, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          (compactSetNode p.2.1, (compactSupportExecutable (p.1, p.2.2)).length)) :=
    TMPolyTimeMap.prod_mk hSetNode hWeight
  have hOut := TMPolyTimeMap.prod_mk hRoot hTail
  simpa [compactRootEdgeFromSource, weightedEdgeStructuredEncodedType, X] using hOut

theorem compactRootEdgeFromSource_eq
    (I : ExactCoverInput) (j : Nat) :
    compactRootEdgeFromSource
        (I.system.universeSize, j, compactSourceSetAt I j) =
      compactRootEdge I j := by
  simp [compactRootEdgeFromSource, compactRootEdge,
    compactSupportExecutable_eq_compactSupport]

def compactEdgeBlockInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat setStructuredEncodedType))

def compactEdgesForSourceSetExecutable
    (p : Nat × Nat × Nat × List Nat) : List (Nat × Nat × Nat) :=
  let support := compactSupportExecutable (p.1, p.2.2.2)
  compactRootEdgeFromSource (p.1, p.2.2.1, p.2.2.2) ::
    compactTerminalEdgesExecutable (p.2.1, p.2.2.1, support)

theorem compactEdgesForSourceSetExecutable_tm_polytime :
    TMPolyTimeMap
      compactEdgeBlockInputEncodedType
      weightedEdgeListStructuredEncodedType
      compactEdgesForSourceSetExecutable := by
  let X := compactEdgeBlockInputEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactEdgeBlockInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactEdgeBlockInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat setStructuredEncodedType))
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInner :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInner
    simpa [Function.comp, X] using hComp
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInner
    simpa [Function.comp, X] using hComp
  have hSupportInput :
      TMPolyTimeMap X compactSupportInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSet
  have hSupport :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => compactSupportExecutable (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactSupportExecutable_tm_polytime hSupportInput
    simpa [Function.comp, X] using hComp
  have hRootInput :
      TMPolyTimeMap X compactRootEdgeInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2.1, p.2.2.2)) := by
    have hInnerPair :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.2.2.1, p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hJ hSet
    simpa [compactRootEdgeInputEncodedType] using
      TMPolyTimeMap.prod_mk hUniverse hInnerPair
  have hRoot :
      TMPolyTimeMap X weightedEdgeStructuredEncodedType
        (fun p : X.Carrier => compactRootEdgeFromSource (p.1, p.2.2.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp compactRootEdgeFromSource_tm_polytime hRootInput
    simpa [Function.comp, X] using hComp
  have hTerminalInput :
      TMPolyTimeMap X compactTerminalEdgeListInputEncodedType
        (fun p : X.Carrier =>
          (p.2.1, p.2.2.1, compactSupportExecutable (p.1, p.2.2.2))) := by
    have hTail :
        TMPolyTimeMap X
          (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
          (fun p : X.Carrier =>
            (p.2.2.1, compactSupportExecutable (p.1, p.2.2.2))) :=
      TMPolyTimeMap.prod_mk hJ hSupport
    simpa [compactTerminalEdgeListInputEncodedType] using
      TMPolyTimeMap.prod_mk hSetCount hTail
  have hTerminalEdges :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier =>
          compactTerminalEdgesExecutable
            (p.2.1, p.2.2.1, compactSupportExecutable (p.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp compactTerminalEdgesExecutable_tm_polytime hTerminalInput
    simpa [Function.comp, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod weightedEdgeStructuredEncodedType weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (compactRootEdgeFromSource (p.1, p.2.2.1, p.2.2.2),
            compactTerminalEdgesExecutable
              (p.2.1, p.2.2.1, compactSupportExecutable (p.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hRoot hTerminalEdges
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons weightedEdgeStructuredEncodedType) hConsInput
  simpa [Function.comp, compactEdgesForSourceSetExecutable,
    weightedEdgeListStructuredEncodedType, X] using hCons

theorem compactEdgesForSourceSetExecutable_eq_compactEdgesForSet
    (I : ExactCoverInput) (j : Nat) :
    compactEdgesForSourceSetExecutable
        (I.system.universeSize, I.system.sets.length, j, compactSourceSetAt I j) =
      compactEdgesForSet I j := by
  simp [compactEdgesForSourceSetExecutable, compactEdgesForSet,
    compactRootEdgeFromSource_eq, compactSupportExecutable_eq_compactSupport,
    compactTerminalEdgesExecutable_eq_compact]

end SteinerTree
end Karp21
end ComplexityReduction
