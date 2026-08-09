/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Lookup

/-!
Family-level edge assembly for the compact Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

def compactFamilyEdgeContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)

def compactFamilyEdgeAccEncodedType : EncodedType :=
  EncodedType.prod compactFamilyEdgeContextEncodedType weightedEdgeListStructuredEncodedType

def compactFamilyEdgeInstructionEncodedType : EncodedType :=
  EncodedType.sum compactFamilyEdgeContextEncodedType EncodedType.nat

def compactFamilyEdgeInstructionListEncodedType : EncodedType :=
  EncodedType.list compactFamilyEdgeInstructionEncodedType

def compactFamilyEdgeInputEncodedType : EncodedType :=
  compactFamilyEdgeContextEncodedType

abbrev CompactFamilyEdgeContext := Nat × Nat × List (List Nat)
abbrev CompactFamilyEdgeAcc := CompactFamilyEdgeContext × List (Nat × Nat × Nat)

def compactFamilyEdgeInitAcc : CompactFamilyEdgeAcc :=
  ((0, (0, [])), [])

def compactFamilyEdgeInitInstruction (ctx : CompactFamilyEdgeContext) :
    compactFamilyEdgeInstructionEncodedType.Carrier :=
  Sum.inl ctx

def compactFamilyEdgeIndexInstruction (j : Nat) :
    compactFamilyEdgeInstructionEncodedType.Carrier :=
  Sum.inr j

def compactFamilyEdgeInstructions (p : CompactFamilyEdgeContext) :
    List compactFamilyEdgeInstructionEncodedType.Carrier :=
  compactFamilyEdgeInitInstruction p ::
    (List.range p.2.1).map compactFamilyEdgeIndexInstruction

def compactFamilyEdgeIndexStep (p : CompactFamilyEdgeAcc × Nat) :
    CompactFamilyEdgeAcc :=
  let ctx := p.1.1
  let out := p.1.2
  let j := p.2
  let S := setFamilyGetD (ctx.2.2, j)
  (ctx, out ++ compactEdgesForSourceSetExecutable (ctx.1, ctx.2.1, j, S))

def compactFamilyEdgeStep
    (p : CompactFamilyEdgeAcc × compactFamilyEdgeInstructionEncodedType.Carrier) :
    CompactFamilyEdgeAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, [])
  | Sum.inr j => compactFamilyEdgeIndexStep (p.1, j)

def compactFamilyEdgesFromInstructions
    (xs : List compactFamilyEdgeInstructionEncodedType.Carrier) :
    List (Nat × Nat × Nat) :=
  (xs.foldl (fun acc instr => compactFamilyEdgeStep (acc, instr))
    compactFamilyEdgeInitAcc).2

def compactFamilyEdgesExecutable (p : CompactFamilyEdgeContext) :
    List (Nat × Nat × Nat) :=
  compactFamilyEdgesFromInstructions (compactFamilyEdgeInstructions p)

/-! ### Semantics -/

theorem compactFamilyEdgeIndexFold_eq_append_flatMap
    (ctx : CompactFamilyEdgeContext) (xs : List Nat) (out : List (Nat × Nat × Nat)) :
    ((xs.map compactFamilyEdgeIndexInstruction).foldl
        (fun acc instr => compactFamilyEdgeStep (acc, instr)) (ctx, out)).2 =
      out ++ xs.flatMap (fun j =>
        compactEdgesForSourceSetExecutable
          (ctx.1, ctx.2.1, j, setFamilyGetD (ctx.2.2, j))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons j js ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [compactFamilyEdgeIndexInstruction, compactFamilyEdgeStep,
        compactFamilyEdgeIndexStep]
      have hTail := ih (out ++
        compactEdgesForSourceSetExecutable
          (ctx.1, ctx.2.1, j, setFamilyGetD (ctx.2.2, j)))
      simpa [List.append_assoc] using hTail

theorem compactFamilyEdgesExecutable_eq_flatMap
    (p : CompactFamilyEdgeContext) :
    compactFamilyEdgesExecutable p =
      (List.range p.2.1).flatMap (fun j =>
        compactEdgesForSourceSetExecutable
          (p.1, p.2.1, j, setFamilyGetD (p.2.2, j))) := by
  change
    (((List.range p.2.1).map compactFamilyEdgeIndexInstruction).foldl
        (fun acc instr => compactFamilyEdgeStep (acc, instr)) (p, [])).2 =
      (List.range p.2.1).flatMap (fun j =>
        compactEdgesForSourceSetExecutable
          (p.1, p.2.1, j, setFamilyGetD (p.2.2, j)))
  simpa using compactFamilyEdgeIndexFold_eq_append_flatMap p (List.range p.2.1) []

theorem compactFamilyEdgesExecutable_eq_compactEdges_tail (I : ExactCoverInput) :
    compactFamilyEdgesExecutable
        (I.system.universeSize, I.system.sets.length, I.system.sets) =
      (List.range I.system.sets.length).flatMap (compactEdgesForSet I) := by
  rw [compactFamilyEdgesExecutable_eq_flatMap]
  apply List.flatMap_congr
  intro j _hj
  have hGet :
      setFamilyGetD (I.system.sets, j) = compactSourceSetAt I j := by
    rfl
  rw [hGet]
  exact compactEdgesForSourceSetExecutable_eq_compactEdgesForSet I j

/-! ### Local size facts for the fold -/

theorem mem_compactSupportExecutable_lt {bound : Nat} {S : List Nat} {x : Nat}
    (hx : x ∈ compactSupportExecutable (bound, S)) :
    x < bound := by
  rw [compactSupportExecutable_eq_filter] at hx
  simp only [List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem compactSupportExecutable_length_le (bound : Nat) (S : List Nat) :
    (compactSupportExecutable (bound, S)).length ≤ bound := by
  rw [compactSupportExecutable_eq_filter]
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem compactRootEdgeFromSource_inputSize_le
    (N universeSize j : Nat) (S : List Nat)
    (hUniverse : universeSize + 1 ≤ N) (hj : j + 1 ≤ N) :
    weightedEdgeStructuredEncodedType.inputSize
        (compactRootEdgeFromSource (universeSize, j, S)) ≤
      10 * N + 20 := by
  have hLen := compactSupportExecutable_length_le universeSize S
  simp [weightedEdgeStructuredEncodedType, compactRootEdgeFromSource, rootNode,
    compactSetNode, EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
  omega

theorem compactTerminalEdgeFromCounts_inputSize_le
    (N setCount j x : Nat)
    (hSetCount : setCount + 1 ≤ N) (hj : j + 1 ≤ N) (hx : x < N) :
    weightedEdgeStructuredEncodedType.inputSize
        (compactTerminalEdgeFromCounts (setCount, j, x)) ≤
      10 * N + 20 := by
  simp [weightedEdgeStructuredEncodedType, compactTerminalEdgeFromCounts,
    compactSetNode, compactTerminalNodeFromCounts, EncodedType.inputSize,
    EncodedType.prod, EncodedType.nat]
  omega

theorem compactEdgesForSourceSetExecutable_length_le
    (universeSize setCount j : Nat) (S : List Nat) :
    (compactEdgesForSourceSetExecutable (universeSize, setCount, j, S)).length ≤
      universeSize + 1 := by
  have hSupport := compactSupportExecutable_length_le universeSize S
  rw [compactEdgesForSourceSetExecutable]
  rw [compactTerminalEdgesExecutable_eq_map]
  simp
  omega

theorem compactEdgesForSourceSetExecutable_inputSize_le
    (N universeSize setCount j : Nat) (S : List Nat)
    (hUniverse : universeSize + 1 ≤ N)
    (hSetCount : setCount + 1 ≤ N)
    (hj : j + 1 ≤ N) :
    weightedEdgeListStructuredEncodedType.inputSize
        (compactEdgesForSourceSetExecutable (universeSize, setCount, j, S)) ≤
      200 * (N + 1) ^ 2 := by
  let block := compactEdgesForSourceSetExecutable (universeSize, setCount, j, S)
  have hLen : block.length ≤ N + 1 := by
    have hBase :=
      compactEdgesForSourceSetExecutable_length_le universeSize setCount j S
    dsimp [block]
    omega
  have hEach :
      ∀ e ∈ block, weightedEdgeStructuredEncodedType.inputSize e ≤ 10 * N + 20 := by
    intro e he
    dsimp [block] at he
    rw [compactEdgesForSourceSetExecutable] at he
    rw [compactTerminalEdgesExecutable_eq_map] at he
    simp only [List.mem_cons, List.mem_map] at he
    rcases he with hRoot | hTerm
    · subst e
      exact compactRootEdgeFromSource_inputSize_le N universeSize j S hUniverse hj
    · rcases hTerm with ⟨x, hx, rfl⟩
      have hxLtUniverse := mem_compactSupportExecutable_lt hx
      exact compactTerminalEdgeFromCounts_inputSize_le N setCount j x
        hSetCount hj (by omega)
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      weightedEdgeStructuredEncodedType block (10 * N + 20) hEach
  have hPoly :
      block.length * (10 * N + 20 + 1) ≤ 200 * (N + 1) ^ 2 := by
    have hPos : 1 ≤ N + 1 := by omega
    nlinarith [sq_nonneg (N : Int)]
  exact hList.trans hPoly

/-! ### TM witnesses -/

theorem compactFamilyEdgeInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeContextEncodedType
      compactFamilyEdgeInstructionEncodedType
      compactFamilyEdgeInitInstruction := by
  simpa [compactFamilyEdgeInstructionEncodedType, compactFamilyEdgeInitInstruction] using
    TMPolyTimeMap.inl compactFamilyEdgeContextEncodedType EncodedType.nat

theorem compactFamilyEdgeIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactFamilyEdgeInstructionEncodedType
      compactFamilyEdgeIndexInstruction := by
  simpa [compactFamilyEdgeInstructionEncodedType, compactFamilyEdgeIndexInstruction] using
    TMPolyTimeMap.inr compactFamilyEdgeContextEncodedType EncodedType.nat

theorem compactFamilyEdgeInstructions_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeInputEncodedType
      compactFamilyEdgeInstructionListEncodedType
      compactFamilyEdgeInstructions := by
  let X := compactFamilyEdgeInputEncodedType
  have hCtx : TMPolyTimeMap X compactFamilyEdgeContextEncodedType (fun p : X.Carrier => p) :=
    TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, compactFamilyEdgeInputEncodedType, compactFamilyEdgeContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hInit :
      TMPolyTimeMap X compactFamilyEdgeInstructionEncodedType
        (fun p : X.Carrier => compactFamilyEdgeInitInstruction p) := by
    have hComp := TMPolyTimeMap.comp compactFamilyEdgeInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hSetCount
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X compactFamilyEdgeInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2.1).map compactFamilyEdgeIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactFamilyEdgeIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactFamilyEdgeInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactFamilyEdgeInstructionEncodedType
          compactFamilyEdgeInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactFamilyEdgeInitInstruction p,
            (List.range p.2.1).map compactFamilyEdgeIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons compactFamilyEdgeInstructionEncodedType)
      hConsInput
  simpa [Function.comp, compactFamilyEdgeInstructions,
    compactFamilyEdgeInstructionListEncodedType, X] using hCons

theorem compactFamilyEdgeStepLeft_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeContextEncodedType
      compactFamilyEdgeAccEncodedType
      (fun ctx : CompactFamilyEdgeContext => (ctx, ([] : List (Nat × Nat × Nat)))) := by
  have hCtx := TMPolyTimeMap.id compactFamilyEdgeContextEncodedType
  have hEmpty :
      TMPolyTimeMap compactFamilyEdgeContextEncodedType weightedEdgeListStructuredEncodedType
        (fun _ : CompactFamilyEdgeContext => ([] : List (Nat × Nat × Nat))) :=
    TMPolyTimeMap.const compactFamilyEdgeContextEncodedType weightedEdgeListStructuredEncodedType []
  simpa [compactFamilyEdgeAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hEmpty

theorem compactFamilyEdgeIndexStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFamilyEdgeAccEncodedType EncodedType.nat)
      compactFamilyEdgeAccEncodedType
      compactFamilyEdgeIndexStep := by
  let X := EncodedType.prod compactFamilyEdgeAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactFamilyEdgeAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactFamilyEdgeAccEncodedType EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactFamilyEdgeAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X compactFamilyEdgeContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst compactFamilyEdgeContextEncodedType
      weightedEdgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactFamilyEdgeAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd compactFamilyEdgeContextEncodedType
      weightedEdgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactFamilyEdgeAccEncodedType, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, compactFamilyEdgeContextEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
        (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, compactFamilyEdgeContextEncodedType, X] using hComp
  have hSetCount : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1.2.2, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hJ
  have hSet :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => setFamilyGetD (p.1.1.2.2, p.2)) := by
    have hComp := TMPolyTimeMap.comp setFamilyGetD_tm_polytime hLookupInput
    simpa [Function.comp, X] using hComp
  have hBlockInput :
      TMPolyTimeMap X compactEdgeBlockInputEncodedType
        (fun p : X.Carrier =>
          (p.1.1.1, p.1.1.2.1, p.2, setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hInner :
        TMPolyTimeMap X (EncodedType.prod EncodedType.nat setStructuredEncodedType)
          (fun p : X.Carrier => (p.2, setFamilyGetD (p.1.1.2.2, p.2))) :=
      TMPolyTimeMap.prod_mk hJ hSet
    have hTail :
        TMPolyTimeMap X
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat setStructuredEncodedType))
          (fun p : X.Carrier =>
            (p.1.1.2.1, (p.2, setFamilyGetD (p.1.1.2.2, p.2)))) :=
      TMPolyTimeMap.prod_mk hSetCount hInner
    simpa [compactEdgeBlockInputEncodedType] using TMPolyTimeMap.prod_mk hUniverse hTail
  have hBlock :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier =>
          compactEdgesForSourceSetExecutable
            (p.1.1.1, p.1.1.2.1, p.2, setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp compactEdgesForSourceSetExecutable_tm_polytime hBlockInput
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod weightedEdgeListStructuredEncodedType
          weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (Nat × Nat × Nat) from p.1.2),
            compactEdgesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.1, p.2, setFamilyGetD (p.1.1.2.2, p.2)))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat × Nat) from p.1.2) ++
            compactEdgesForSourceSetExecutable
              (p.1.1.1, p.1.1.2.1, p.2, setFamilyGetD (p.1.1.2.2, p.2))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append weightedEdgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, weightedEdgeListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCtx hAppend
  simpa [compactFamilyEdgeIndexStep, compactFamilyEdgeAccEncodedType, X] using hPair

theorem compactFamilyEdgeStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactFamilyEdgeAccEncodedType compactFamilyEdgeInstructionEncodedType)
      compactFamilyEdgeAccEncodedType
      compactFamilyEdgeStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactFamilyEdgeAccEncodedType compactFamilyEdgeContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactFamilyEdgeStepLeft_tm_polytime
      compactFamilyEdgeIndexStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def compactFamilyEdgeFoldInv (N : Nat) (acc : compactFamilyEdgeAccEncodedType.Carrier) :
    Prop :=
  acc = compactFamilyEdgeInitAcc ∨
    ((show Nat from acc.1.1) + 1 ≤ N ∧ (show Nat from acc.1.2.1) + 1 ≤ N)

theorem compactFamilyEdgeInitAcc_bound
    (xs : List compactFamilyEdgeInstructionEncodedType.Carrier) :
    compactFamilyEdgeFoldInv (compactFamilyEdgeInstructionListEncodedType.inputSize xs)
        compactFamilyEdgeInitAcc ∧
      compactFamilyEdgeAccEncodedType.inputSize compactFamilyEdgeInitAcc ≤
        (Polynomial.C 10).eval (compactFamilyEdgeInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · have hNilEdges :
        weightedEdgeStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil weightedEdgeStructuredEncodedType
    have hNilSets :
        setStructuredEncodedType.list.inputSize ([] : List (List Nat)) = 0 :=
      EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [compactFamilyEdgeInitAcc, compactFamilyEdgeAccEncodedType,
      compactFamilyEdgeContextEncodedType, weightedEdgeListStructuredEncodedType,
      setFamilyStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hNilEdges, hNilSets]

theorem compactFamilyEdgeStep_growth
    (source : List compactFamilyEdgeInstructionEncodedType.Carrier)
    (acc : compactFamilyEdgeAccEncodedType.Carrier)
    (instr : compactFamilyEdgeInstructionEncodedType.Carrier)
    (hInv :
      compactFamilyEdgeFoldInv
        (compactFamilyEdgeInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactFamilyEdgeInstructionEncodedType.inputSize instr ≤
        compactFamilyEdgeInstructionListEncodedType.inputSize source) :
    compactFamilyEdgeFoldInv
        (compactFamilyEdgeInstructionListEncodedType.inputSize source)
        (compactFamilyEdgeStep (acc, instr)) ∧
      compactFamilyEdgeAccEncodedType.inputSize (compactFamilyEdgeStep (acc, instr)) ≤
        compactFamilyEdgeAccEncodedType.inputSize acc +
          (Polynomial.C 500 * (Polynomial.X * Polynomial.X) + Polynomial.C 500).eval
            (compactFamilyEdgeInstructionListEncodedType.inputSize source) := by
  let N := compactFamilyEdgeInstructionListEncodedType.inputSize source
  rcases acc with ⟨ctx, out⟩
  rcases ctx with ⟨universeSize, setCount, sets⟩
  change Nat at universeSize
  change Nat at setCount
  cases instr with
  | inl newCtx =>
      rcases newCtx with ⟨newUniverse, newSetCount, newSets⟩
      change Nat at newUniverse
      change Nat at newSetCount
      have hCtx :
          compactFamilyEdgeContextEncodedType.inputSize
              (newUniverse, newSetCount, newSets) + 1 ≤ N := by
        simpa [N, compactFamilyEdgeInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      have hNewUniverse : newUniverse + 1 ≤ N := by
        simp [compactFamilyEdgeContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      have hNewSetCount : newSetCount + 1 ≤ N := by
        simp [compactFamilyEdgeContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat] at hCtx
        omega
      constructor
      · exact Or.inr ⟨hNewUniverse, hNewSetCount⟩
      · have hNilEdges :
            weightedEdgeStructuredEncodedType.list.inputSize ([] : List (Nat × Nat × Nat)) = 0 :=
          EncodedType.inputSize_list_nil weightedEdgeStructuredEncodedType
        have hNewAcc :
            compactFamilyEdgeAccEncodedType.inputSize
                ((newUniverse, newSetCount, newSets), ([] : List (Nat × Nat × Nat))) ≤ N := by
          simpa [compactFamilyEdgeAccEncodedType, compactFamilyEdgeContextEncodedType,
            weightedEdgeListStructuredEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, hNilEdges] using hCtx
        have hPolyN :
            N ≤
              compactFamilyEdgeAccEncodedType.inputSize
                  ((universeSize, setCount, sets), out) +
                (Polynomial.C 500 * (Polynomial.X * Polynomial.X) + Polynomial.C 500).eval N := by
          have hBase :
              N ≤ (Polynomial.C 500 * (Polynomial.X * Polynomial.X) + Polynomial.C 500).eval N := by
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
            nlinarith [sq_nonneg (N : Int)]
          exact hBase.trans (Nat.le_add_left _ _)
        simpa [compactFamilyEdgeStep, N] using hNewAcc.trans (by simpa [N] using hPolyN)
  | inr j =>
      change Nat at j
      have hj : j + 1 ≤ N := by
        have hjTagged : j + 1 < N := by
          simpa [N, compactFamilyEdgeInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      have hBounds : universeSize + 1 ≤ N ∧ setCount + 1 ≤ N := by
        rcases hInv with hInit | hBound
        · injection hInit with hCtxEq _hOut
          injection hCtxEq with hUniverse hTail
          injection hTail with hSetCount _hSets
          subst universeSize
          subst setCount
          omega
        · exact hBound
      let S := setFamilyGetD (sets, j)
      have hBlock :=
        compactEdgesForSourceSetExecutable_inputSize_le
          N universeSize setCount j S hBounds.1 hBounds.2 hj
      have hAppendSize :
          weightedEdgeListStructuredEncodedType.inputSize
              ((show List (Nat × Nat × Nat) from out) ++
                compactEdgesForSourceSetExecutable (universeSize, setCount, j, S)) =
            weightedEdgeListStructuredEncodedType.inputSize out +
              weightedEdgeListStructuredEncodedType.inputSize
                (compactEdgesForSourceSetExecutable (universeSize, setCount, j, S)) := by
        simpa [weightedEdgeListStructuredEncodedType] using
          list_inputSize_append weightedEdgeStructuredEncodedType out
            (compactEdgesForSourceSetExecutable (universeSize, setCount, j, S))
      constructor
      · exact Or.inr hBounds
      · simp [compactFamilyEdgeStep, compactFamilyEdgeIndexStep,
          compactFamilyEdgeAccEncodedType, EncodedType.inputSize_prod, hAppendSize,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, S]
        have hPoly :
            200 * (N + 1) ^ 2 ≤ 500 * (N * N) + 500 := by
          nlinarith [sq_nonneg (N : Int)]
        have hPolySource :
            200 * (N + 1) ^ 2 ≤
              500 *
                  (compactFamilyEdgeInstructionListEncodedType.inputSize source *
                    compactFamilyEdgeInstructionListEncodedType.inputSize source) +
                500 := by
          simpa [N] using hPoly
        have hBlockPoly :
            weightedEdgeListStructuredEncodedType.inputSize
                (compactEdgesForSourceSetExecutable
                  (universeSize, setCount, j, setFamilyGetD (sets, j))) ≤
              500 *
                  (compactFamilyEdgeInstructionListEncodedType.inputSize source *
                    compactFamilyEdgeInstructionListEncodedType.inputSize source) +
                500 := by
          simpa [S] using hBlock.trans hPolySource
        have hAppendLe :
            weightedEdgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat × Nat) from out) ++
                  compactEdgesForSourceSetExecutable
                    (universeSize, setCount, j, setFamilyGetD (sets, j))) ≤
              weightedEdgeListStructuredEncodedType.inputSize out +
                (500 *
                    (compactFamilyEdgeInstructionListEncodedType.inputSize source *
                      compactFamilyEdgeInstructionListEncodedType.inputSize source) +
                  500) := by
          have hAppendSizeRaw :
              weightedEdgeListStructuredEncodedType.inputSize
                  ((show List (Nat × Nat × Nat) from out) ++
                    compactEdgesForSourceSetExecutable
                      (universeSize, setCount, j, setFamilyGetD (sets, j))) =
                weightedEdgeListStructuredEncodedType.inputSize out +
                  weightedEdgeListStructuredEncodedType.inputSize
                    (compactEdgesForSourceSetExecutable
                      (universeSize, setCount, j, setFamilyGetD (sets, j))) := by
            simpa [S] using hAppendSize
          rw [hAppendSizeRaw]
          exact Nat.add_le_add_left hBlockPoly _
        omega

theorem compactFamilyEdgeFold_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeInstructionListEncodedType
      compactFamilyEdgeAccEncodedType
      (fun xs : List compactFamilyEdgeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactFamilyEdgeStep (acc, instr))
          compactFamilyEdgeInitAcc) := by
  rcases compactFamilyEdgeStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactFamilyEdgeInstructionEncodedType compactFamilyEdgeAccEncodedType
      compactFamilyEdgeStep compactFamilyEdgeInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 500 * (Polynomial.X * Polynomial.X) + Polynomial.C 500)
      compactFamilyEdgeFoldInv ?_ ?_
  · intro xs
    exact compactFamilyEdgeInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactFamilyEdgeStep_growth source acc instr hInv hInstr

theorem compactFamilyEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeInstructionListEncodedType
      weightedEdgeListStructuredEncodedType
      compactFamilyEdgesFromInstructions := by
  have hFold := compactFamilyEdgeFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd compactFamilyEdgeContextEncodedType
    weightedEdgeListStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactFamilyEdgesFromInstructions,
    compactFamilyEdgeAccEncodedType] using hComp

theorem compactFamilyEdgesExecutable_tm_polytime :
    TMPolyTimeMap
      compactFamilyEdgeInputEncodedType
      weightedEdgeListStructuredEncodedType
      compactFamilyEdgesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp compactFamilyEdgesFromInstructions_tm_polytime
      compactFamilyEdgeInstructions_tm_polytime
  simpa [Function.comp, compactFamilyEdgesExecutable] using hComp

end SteinerTree
end Karp21
end ComplexityReduction
