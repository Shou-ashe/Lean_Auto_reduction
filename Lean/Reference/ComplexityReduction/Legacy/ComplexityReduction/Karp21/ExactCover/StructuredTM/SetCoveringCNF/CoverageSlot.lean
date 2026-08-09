import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.SlotFor

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable coverage literals for one fixed slot and a precomputed list of source
set indices containing the covered universe element.
-/

def setCoveringCoverageSlotContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)

abbrev SetCoveringCoverageSlotContext := Nat × List Nat

def setCoveringCoverageSlotInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat EncodedType.nat

def setCoveringCoverageSlotInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringCoverageSlotInstructionEncodedType

def setCoveringCoverageSlotAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clauseStructuredEncodedType

def setCoveringCoverageSlotInitAcc :
    setCoveringCoverageSlotAccEncodedType.Carrier :=
  ((0 : Nat), ([] : SAT.Clause))

def setCoveringCoverageSlotInitInstruction
    (slot : Nat) : setCoveringCoverageSlotInstructionEncodedType.Carrier :=
  Sum.inl slot

def setCoveringCoverageSlotIndexInstruction
    (idx : Nat) : setCoveringCoverageSlotInstructionEncodedType.Carrier :=
  Sum.inr idx

def setCoveringCoverageSlotInstructions
    (ctx : SetCoveringCoverageSlotContext) :
    List setCoveringCoverageSlotInstructionEncodedType.Carrier :=
  setCoveringCoverageSlotInitInstruction ctx.1 ::
    ctx.2.map setCoveringCoverageSlotIndexInstruction

def setCoveringCoverageSlotStep
    (p : setCoveringCoverageSlotAccEncodedType.Carrier ×
      setCoveringCoverageSlotInstructionEncodedType.Carrier) :
    setCoveringCoverageSlotAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl slot => (slot, [])
  | Sum.inr idx =>
      (p.1.1, (show SAT.Clause from p.1.2) ++
        [setCoveringChoiceLitFromPair (p.1.1, idx)])

def setCoveringCoverageSlotFromInstructions
    (xs : List setCoveringCoverageSlotInstructionEncodedType.Carrier) :
    SAT.Clause :=
  (xs.foldl (fun acc instr => setCoveringCoverageSlotStep (acc, instr))
    setCoveringCoverageSlotInitAcc).2

def setCoveringCoverageSlotLitsExecutable
    (ctx : SetCoveringCoverageSlotContext) : SAT.Clause :=
  setCoveringCoverageSlotFromInstructions
    (setCoveringCoverageSlotInstructions ctx)

/-! ### Semantics -/

theorem setCoveringCoverageSlotIndexFold_eq_append_map
    (slot : Nat) (idxs : List Nat) (out : SAT.Clause) :
    ((idxs.map setCoveringCoverageSlotIndexInstruction).foldl
        (fun acc instr => setCoveringCoverageSlotStep (acc, instr)) (slot, out)).2 =
      out ++ idxs.map (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
  induction idxs generalizing out with
  | nil =>
      simp
  | cons idx rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simpa [setCoveringCoverageSlotIndexInstruction, setCoveringCoverageSlotStep,
        List.append_assoc] using
        ih (out ++ [setCoveringChoiceLitFromPair (slot, idx)])

theorem setCoveringCoverageSlotLitsExecutable_eq_map
    (ctx : SetCoveringCoverageSlotContext) :
    setCoveringCoverageSlotLitsExecutable ctx =
      ctx.2.map (fun idx => setCoveringChoiceLitFromPair (ctx.1, idx)) := by
  change
    ((ctx.2.map setCoveringCoverageSlotIndexInstruction).foldl
        (fun acc instr => setCoveringCoverageSlotStep (acc, instr)) (ctx.1, [])).2 =
      ctx.2.map (fun idx => setCoveringChoiceLitFromPair (ctx.1, idx))
  simpa using setCoveringCoverageSlotIndexFold_eq_append_map ctx.1 ctx.2 []

/-! ### TM witnesses -/

theorem setCoveringCoverageSlotInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringCoverageSlotInstructionEncodedType
      setCoveringCoverageSlotInitInstruction := by
  simpa [setCoveringCoverageSlotInstructionEncodedType,
    setCoveringCoverageSlotInitInstruction] using
    TMPolyTimeMap.inl EncodedType.nat EncodedType.nat

theorem setCoveringCoverageSlotIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringCoverageSlotInstructionEncodedType
      setCoveringCoverageSlotIndexInstruction := by
  simpa [setCoveringCoverageSlotInstructionEncodedType,
    setCoveringCoverageSlotIndexInstruction] using
    TMPolyTimeMap.inr EncodedType.nat EncodedType.nat

theorem setCoveringCoverageSlotInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageSlotContextEncodedType
      setCoveringCoverageSlotInstructionListEncodedType
      setCoveringCoverageSlotInstructions := by
  let X := setCoveringCoverageSlotContextEncodedType
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.1) := by
    simpa [X, setCoveringCoverageSlotContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
  have hIdxs :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun ctx : X.Carrier => ctx.2) := by
    simpa [X, setCoveringCoverageSlotContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
  have hInit :
      TMPolyTimeMap X setCoveringCoverageSlotInstructionEncodedType
        (fun ctx : X.Carrier => setCoveringCoverageSlotInitInstruction ctx.1) := by
    have hComp := TMPolyTimeMap.comp setCoveringCoverageSlotInitInstruction_tm_polytime hSlot
    simpa [Function.comp, X] using hComp
  have hIndexInstructions :
      TMPolyTimeMap X setCoveringCoverageSlotInstructionListEncodedType
        (fun ctx : X.Carrier =>
          ctx.2.map setCoveringCoverageSlotIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map setCoveringCoverageSlotIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hIdxs
    simpa [Function.comp, setCoveringCoverageSlotInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringCoverageSlotInstructionEncodedType
          setCoveringCoverageSlotInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (setCoveringCoverageSlotInitInstruction ctx.1,
            ctx.2.map setCoveringCoverageSlotIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringCoverageSlotInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringCoverageSlotInstructions,
    setCoveringCoverageSlotInstructionListEncodedType, X] using hCons

theorem setCoveringCoverageSlotStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringCoverageSlotAccEncodedType
      (fun slot : Nat => (slot, ([] : SAT.Clause))) := by
  have hSlot := TMPolyTimeMap.id EncodedType.nat
  have hEmpty :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun _ : Nat => ([] : SAT.Clause)) :=
    TMPolyTimeMap.const EncodedType.nat clauseStructuredEncodedType []
  simpa [setCoveringCoverageSlotAccEncodedType] using TMPolyTimeMap.prod_mk hSlot hEmpty

theorem setCoveringCoverageSlotStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageSlotAccEncodedType EncodedType.nat)
      setCoveringCoverageSlotAccEncodedType
      (fun p : setCoveringCoverageSlotAccEncodedType.Carrier × Nat =>
        (p.1.1, (show SAT.Clause from p.1.2) ++
          [setCoveringChoiceLitFromPair (p.1.1, p.2)])) := by
  let X := EncodedType.prod setCoveringCoverageSlotAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringCoverageSlotAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringCoverageSlotAccEncodedType EncodedType.nat
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringCoverageSlotAccEncodedType EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringCoverageSlotAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringCoverageSlotAccEncodedType, X] using hComp
  have hPair :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSlot hIdx
  have hLit :
      TMPolyTimeMap X literalStructuredEncodedType
        (fun p : X.Carrier => setCoveringChoiceLitFromPair (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp setCoveringChoiceLitFromPair_tm_polytime hPair
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier => [setCoveringChoiceLitFromPair (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hLit
    simpa [Function.comp, clauseStructuredEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.Clause from p.1.2), [setCoveringChoiceLitFromPair (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.Clause from p.1.2) ++
            [setCoveringChoiceLitFromPair (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
    simpa [Function.comp, clauseStructuredEncodedType, X] using hComp
  simpa [setCoveringCoverageSlotAccEncodedType] using TMPolyTimeMap.prod_mk hSlot hAppend

theorem setCoveringCoverageSlotStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageSlotAccEncodedType
        setCoveringCoverageSlotInstructionEncodedType)
      setCoveringCoverageSlotAccEncodedType
      setCoveringCoverageSlotStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringCoverageSlotAccEncodedType EncodedType.nat EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringCoverageSlotStepLeft_tm_polytime
      setCoveringCoverageSlotStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Bounded fold certificate -/

def setCoveringCoverageSlotFoldInv (N : Nat)
    (acc : setCoveringCoverageSlotAccEncodedType.Carrier) : Prop :=
  acc = setCoveringCoverageSlotInitAcc ∨ EncodedType.nat.inputSize acc.1 ≤ N

noncomputable def setCoveringCoverageSlotFoldBase : Polynomial Nat :=
  Polynomial.C 20

noncomputable def setCoveringCoverageSlotFoldGrow : Polynomial Nat :=
  Polynomial.X ^ 2 + Polynomial.C 10

@[simp] theorem setCoveringCoverageSlotFoldGrow_eval (N : Nat) :
    setCoveringCoverageSlotFoldGrow.eval N = N ^ 2 + 10 := by
  simp [setCoveringCoverageSlotFoldGrow, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X]

theorem setCoveringCoverageSlotInitAcc_bound
    (xs : List setCoveringCoverageSlotInstructionEncodedType.Carrier) :
    setCoveringCoverageSlotFoldInv
        (setCoveringCoverageSlotInstructionListEncodedType.inputSize xs)
        setCoveringCoverageSlotInitAcc ∧
      setCoveringCoverageSlotAccEncodedType.inputSize setCoveringCoverageSlotInitAcc ≤
        setCoveringCoverageSlotFoldBase.eval
          (setCoveringCoverageSlotInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageSlotFoldBase]
    native_decide

theorem setCoveringCoverageLiteralFromSlotIndex_inputSize_le
    {N slot idx : Nat}
    (hSlot : EncodedType.nat.inputSize slot ≤ N)
    (hIdx : EncodedType.nat.inputSize idx ≤ N) :
    literalStructuredEncodedType.inputSize
        (setCoveringChoiceLitFromPair (slot, idx)) ≤ N ^ 2 + 3 := by
  have hSlotN : slot + 1 ≤ N := by simpa [EncodedType.inputSize_nat] using hSlot
  have hIdxN : idx + 1 ≤ N := by simpa [EncodedType.inputSize_nat] using hIdx
  have hMax : max slot idx + 1 ≤ N := by omega
  have hPair : Nat.pair slot idx ≤ N ^ 2 := by
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot idx)).trans
      (Nat.pow_le_pow_left hMax 2)
  rw [literalStructured_inputSize_eq]
  simp [setCoveringChoiceLitFromPair, SAT.Literal.positive]
  omega

theorem setCoveringCoverageSlotStep_growth
    (source : List setCoveringCoverageSlotInstructionEncodedType.Carrier)
    (acc : setCoveringCoverageSlotAccEncodedType.Carrier)
    (instr : setCoveringCoverageSlotInstructionEncodedType.Carrier)
    (hInv :
      setCoveringCoverageSlotFoldInv
        (setCoveringCoverageSlotInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringCoverageSlotInstructionEncodedType.inputSize instr ≤
        setCoveringCoverageSlotInstructionListEncodedType.inputSize source) :
    setCoveringCoverageSlotFoldInv
        (setCoveringCoverageSlotInstructionListEncodedType.inputSize source)
        (setCoveringCoverageSlotStep (acc, instr)) ∧
      setCoveringCoverageSlotAccEncodedType.inputSize
          (setCoveringCoverageSlotStep (acc, instr)) ≤
        setCoveringCoverageSlotAccEncodedType.inputSize acc +
          setCoveringCoverageSlotFoldGrow.eval
            (setCoveringCoverageSlotInstructionListEncodedType.inputSize source) := by
  let N := setCoveringCoverageSlotInstructionListEncodedType.inputSize source
  rcases acc with ⟨slot, out⟩
  change Nat at slot
  cases instr with
  | inl newSlot =>
      change Nat at newSlot
      have hNewSlot : EncodedType.nat.inputSize newSlot ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageSlotInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      constructor
      · exact Or.inr hNewSlot
      · have hEmpty :
            clauseStructuredEncodedType.inputSize ([] : SAT.Clause) = 0 := by
          change (EncodedType.list literalStructuredEncodedType).inputSize ([] : SAT.Clause) = 0
          exact EncodedType.inputSize_list_nil literalStructuredEncodedType
        have hNewAcc :
            setCoveringCoverageSlotAccEncodedType.inputSize (newSlot, ([] : SAT.Clause)) ≤
              N + 1 := by
          have hNewSlotLt : newSlot < N := by
            simpa [EncodedType.inputSize_nat] using hNewSlot
          simp [setCoveringCoverageSlotAccEncodedType, EncodedType.inputSize_prod, hEmpty,
            EncodedType.inputSize_nat]
          omega
        have hGrowLarge :
            N + 1 ≤ setCoveringCoverageSlotAccEncodedType.inputSize (slot, out) +
              setCoveringCoverageSlotFoldGrow.eval N := by
          have hPoly : N + 1 ≤ setCoveringCoverageSlotFoldGrow.eval N := by
            rw [setCoveringCoverageSlotFoldGrow_eval]
            nlinarith [sq_nonneg (N : Int)]
          exact hPoly.trans (Nat.le_add_left _ _)
        simpa [setCoveringCoverageSlotStep, N] using hNewAcc.trans hGrowLarge
  | inr idx =>
      change Nat at idx
      have hIdx : EncodedType.nat.inputSize idx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageSlotInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hSlot :
          EncodedType.nat.inputSize slot ≤ N := by
        rcases hInv with hInit | hSlot
        · injection hInit with hSlotEq _hOut
          rw [hSlotEq]
          have hOneLeIdx : 1 ≤ EncodedType.nat.inputSize idx := by
            simp [EncodedType.inputSize_nat]
          simpa [EncodedType.inputSize_nat] using hOneLeIdx.trans hIdx
        · exact hSlot
      have hLit :=
        setCoveringCoverageLiteralFromSlotIndex_inputSize_le
          (N := N) hSlot hIdx
      have hSingleton :
          clauseStructuredEncodedType.inputSize
              [setCoveringChoiceLitFromPair (slot, idx)] ≤ N ^ 2 + 4 := by
        change (EncodedType.list literalStructuredEncodedType).inputSize
            [setCoveringChoiceLitFromPair (slot, idx)] ≤ N ^ 2 + 4
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        omega
      have hAppend :
          clauseStructuredEncodedType.inputSize
              ((show SAT.Clause from out) ++ [setCoveringChoiceLitFromPair (slot, idx)]) =
            clauseStructuredEncodedType.inputSize out +
              clauseStructuredEncodedType.inputSize [setCoveringChoiceLitFromPair (slot, idx)] := by
        simpa [clauseStructuredEncodedType] using
          list_inputSize_append literalStructuredEncodedType out
            [setCoveringChoiceLitFromPair (slot, idx)]
      constructor
      · exact Or.inr hSlot
      · change
          setCoveringCoverageSlotAccEncodedType.inputSize
              (slot, (show SAT.Clause from out) ++
                [setCoveringChoiceLitFromPair (slot, idx)]) ≤
            setCoveringCoverageSlotAccEncodedType.inputSize (slot, out) +
              setCoveringCoverageSlotFoldGrow.eval N
        simp [setCoveringCoverageSlotAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem setCoveringCoverageSlotFold_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageSlotInstructionListEncodedType
      setCoveringCoverageSlotAccEncodedType
      (fun xs : List setCoveringCoverageSlotInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringCoverageSlotStep (acc, instr))
          setCoveringCoverageSlotInitAcc) := by
  rcases setCoveringCoverageSlotStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringCoverageSlotInstructionEncodedType setCoveringCoverageSlotAccEncodedType
      setCoveringCoverageSlotStep setCoveringCoverageSlotInitAcc hStep
      setCoveringCoverageSlotFoldBase setCoveringCoverageSlotFoldGrow
      setCoveringCoverageSlotFoldInv ?_ ?_
  · intro xs
    exact setCoveringCoverageSlotInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringCoverageSlotStep_growth source acc instr hInv hInstr

theorem setCoveringCoverageSlotFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageSlotInstructionListEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageSlotFromInstructions := by
  have hFold := setCoveringCoverageSlotFold_tm_polytime
  have hOut := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringCoverageSlotFromInstructions,
    setCoveringCoverageSlotAccEncodedType] using hComp

theorem setCoveringCoverageSlotLitsExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageSlotContextEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageSlotLitsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringCoverageSlotFromInstructions_tm_polytime
      setCoveringCoverageSlotInstructions_tm_polytime
  simpa [Function.comp, setCoveringCoverageSlotLitsExecutable] using hComp

theorem encodedList_element_inputSize_le_local {X : EncodedType} {x : X.Carrier}
    {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      rcases List.mem_cons.mp hx with hxy | hxys
      · subst x
        omega
      · have hTail := ih hxys
        omega

theorem setCoveringCoverageSlotLitsExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringCoverageSlotContext}
    (hCtx : setCoveringCoverageSlotContextEncodedType.inputSize ctx ≤ N) :
    clauseStructuredEncodedType.inputSize
        (setCoveringCoverageSlotLitsExecutable ctx) ≤
      N * (N ^ 2 + 4) := by
  rcases ctx with ⟨slot, idxs⟩
  have hCtxProd :
      EncodedType.nat.inputSize slot + 1 +
          (EncodedType.list EncodedType.nat).inputSize idxs ≤ N := by
    change
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)).inputSize
          (slot, idxs) ≤ N at hCtx
    rw [EncodedType.inputSize_prod] at hCtx
    exact hCtx
  have hSlotN : EncodedType.nat.inputSize slot ≤ N := by
    omega
  have hIdxsN : (EncodedType.list EncodedType.nat).inputSize idxs ≤ N := by
    omega
  rw [setCoveringCoverageSlotLitsExecutable_eq_map]
  let clause := idxs.map (fun idx => setCoveringChoiceLitFromPair (slot, idx))
  have hVar : ∀ l ∈ clause, l.var ≤ N ^ 2 := by
    intro l hl
    dsimp [clause] at hl
    rcases List.mem_map.mp hl with ⟨idx, hIdxMem, rfl⟩
    have hIdxN : EncodedType.nat.inputSize idx ≤ N :=
      (encodedList_element_inputSize_le_local hIdxMem).trans hIdxsN
    have hSlotNat : slot + 1 ≤ N := by
      simpa [EncodedType.inputSize_nat] using hSlotN
    have hIdxNat : idx + 1 ≤ N := by
      simpa [EncodedType.inputSize_nat] using hIdxN
    have hMax : max slot idx + 1 ≤ N := by omega
    have hPair : Nat.pair slot idx ≤ N ^ 2 :=
      (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot idx)).trans
        (Nat.pow_le_pow_left hMax 2)
    simpa [setCoveringChoiceLitFromPair, SAT.Literal.positive] using hPair
  have hClause :=
    clauseStructured_inputSize_le_length_mul_of_lit_var_le
      (c := clause) (V := N ^ 2) hVar
  have hLen : clause.length ≤ N := by
    have hBase := setCoveringEncodedList_length_le_inputSize EncodedType.nat idxs
    simpa [clause] using hBase.trans hIdxsN
  change clauseStructuredEncodedType.inputSize clause ≤ N * (N ^ 2 + 4)
  exact hClause.trans (Nat.mul_le_mul_right _ hLen)

end ExactCover
end Karp21
end ComplexityReduction
