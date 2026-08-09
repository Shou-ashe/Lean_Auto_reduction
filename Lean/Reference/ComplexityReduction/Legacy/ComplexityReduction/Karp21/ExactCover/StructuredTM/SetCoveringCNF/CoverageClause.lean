import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.CoverageSlot
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.IndexRunner

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable coverage clause for one universe element.

The runner first reuses the Hitting Set index scanner to compute the source-set
indices containing the covered element.  A bounded fold then scans the slot
range and appends the precomputed per-slot literal block from `CoverageSlot`.
-/

def setCoveringCoverageClauseContextEncodedType : EncodedType :=
  EncodedType.prod setCoveringStructuredEncodedType EncodedType.nat

abbrev SetCoveringCoverageClauseContext := SetCoveringInput × Nat

def setCoveringCoverageClauseCoreContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)

abbrev SetCoveringCoverageClauseCoreContext := Nat × List Nat

def setCoveringCoverageClauseInstructionEncodedType : EncodedType :=
  EncodedType.sum setCoveringCoverageClauseCoreContextEncodedType EncodedType.nat

def setCoveringCoverageClauseInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringCoverageClauseInstructionEncodedType

def setCoveringCoverageClauseAccEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list EncodedType.nat) clauseStructuredEncodedType

def setCoveringCoverageClauseInitAcc :
    setCoveringCoverageClauseAccEncodedType.Carrier :=
  (([] : List Nat), ([] : SAT.Clause))

def setCoveringCoverageClauseInitInstruction
    (ctx : SetCoveringCoverageClauseCoreContext) :
    setCoveringCoverageClauseInstructionEncodedType.Carrier :=
  Sum.inl ctx

def setCoveringCoverageClauseSlotInstruction
    (slot : Nat) : setCoveringCoverageClauseInstructionEncodedType.Carrier :=
  Sum.inr slot

def setCoveringCoverageClauseInstructions
    (ctx : SetCoveringCoverageClauseCoreContext) :
    List setCoveringCoverageClauseInstructionEncodedType.Carrier :=
  setCoveringCoverageClauseInitInstruction ctx ::
    (List.range ctx.1).map setCoveringCoverageClauseSlotInstruction

def setCoveringCoverageClauseStep
    (p : setCoveringCoverageClauseAccEncodedType.Carrier ×
      setCoveringCoverageClauseInstructionEncodedType.Carrier) :
    setCoveringCoverageClauseAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx.2, [])
  | Sum.inr slot =>
      (p.1.1, (show SAT.Clause from p.1.2) ++
        setCoveringCoverageSlotLitsExecutable (slot, p.1.1))

def setCoveringCoverageClauseFromInstructions
    (xs : List setCoveringCoverageClauseInstructionEncodedType.Carrier) :
    SAT.Clause :=
  (xs.foldl (fun acc instr => setCoveringCoverageClauseStep (acc, instr))
    setCoveringCoverageClauseInitAcc).2

def setCoveringCoverageClauseCoreExecutable
    (ctx : SetCoveringCoverageClauseCoreContext) : SAT.Clause :=
  setCoveringCoverageClauseFromInstructions
    (setCoveringCoverageClauseInstructions ctx)

def setCoveringCoverageClauseIndexInput
    (ctx : SetCoveringCoverageClauseContext) :
    HittingSet.setIndexInstructionInputEncodedType.Carrier :=
  (ctx.2, ctx.1.system.sets)

def setCoveringCoverageClauseCoreContext
    (ctx : SetCoveringCoverageClauseContext) :
    SetCoveringCoverageClauseCoreContext :=
  (ctx.1.k, HittingSet.setIndexIndicesFromFamily
    (setCoveringCoverageClauseIndexInput ctx))

def setCoveringCoverageClauseExecutable
    (ctx : SetCoveringCoverageClauseContext) : SAT.Clause :=
  setCoveringCoverageClauseCoreExecutable
    (setCoveringCoverageClauseCoreContext ctx)

/-! ### Semantics -/

def setCoveringCoverageLitsFromSets
    (sets : List (List Nat)) (x slot : Nat) : List SAT.Literal :=
  (List.range sets.length).filterMap fun idx =>
    if x ∈ sets.getD idx [] then some (setCoveringChoiceLitFromPair (slot, idx)) else none

def setCoveringCoverageLitsFromSetsAt
    (sets : List (List Nat)) (x slot start : Nat) : List SAT.Literal :=
  (List.range sets.length).filterMap fun offset =>
    if x ∈ sets.getD offset [] then
      some (setCoveringChoiceLitFromPair (slot, start + offset))
    else
      none

theorem setCoveringCoverageLitsFromSetsAt_eq_findIdxs_map
    (sets : List (List Nat)) (x slot start : Nat) :
    setCoveringCoverageLitsFromSetsAt sets x slot start =
      (sets.findIdxs (fun S => decide (x ∈ S)) start).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
  induction sets generalizing start with
  | nil =>
      simp [setCoveringCoverageLitsFromSetsAt]
  | cons S sets ih =>
      by_cases hx : x ∈ S
      · rw [List.findIdxs_cons]
        simp [setCoveringCoverageLitsFromSetsAt, hx, List.range_succ_eq_map,
          List.filterMap_map]
        simpa [setCoveringCoverageLitsFromSetsAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih (start + 1)
      · rw [List.findIdxs_cons]
        simp [setCoveringCoverageLitsFromSetsAt, hx, List.range_succ_eq_map,
          List.filterMap_map]
        simpa [setCoveringCoverageLitsFromSetsAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ih (start + 1)

theorem setCoveringCoverageLitsFromSets_eq_findIdxs_map
    (sets : List (List Nat)) (x slot : Nat) :
    setCoveringCoverageLitsFromSets sets x slot =
      (sets.findIdxs (fun S => decide (x ∈ S))).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
  simpa [setCoveringCoverageLitsFromSets, setCoveringCoverageLitsFromSetsAt] using
    setCoveringCoverageLitsFromSetsAt_eq_findIdxs_map sets x slot 0

theorem setCoveringCoverageLitsForSlot_eq_index_map
    (I : SetCoveringInput) (x slot : Nat) :
    setCoveringCoverageLitsForSlot I x slot =
      (HittingSet.setIndexIndicesFromFamily (x, I.system.sets)).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
  calc
    setCoveringCoverageLitsForSlot I x slot =
        setCoveringCoverageLitsFromSets I.system.sets x slot := by
          simp [setCoveringCoverageLitsFromSets, setCoveringCoverageLitsForSlot,
            sourceSetAt, setCoveringChoiceLitFromPair, setCoveringChoiceLit,
            setCoveringChoiceVar]
    _ = (I.system.sets.findIdxs (fun S => decide (x ∈ S))).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) :=
          setCoveringCoverageLitsFromSets_eq_findIdxs_map I.system.sets x slot
    _ = (I.system.sets.findIdxs
          (fun S => HittingSet.setContainsBool (x, S))).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
          simp [HittingSet.setContainsBool_eq_decide]
    _ = (HittingSet.setIndexIndicesFromFamily (x, I.system.sets)).map
        (fun idx => setCoveringChoiceLitFromPair (slot, idx)) := by
          rw [HittingSet.setIndexIndicesFromFamily_eq_findIdxs]

theorem setCoveringCoverageClauseIndexFold_eq_append_flatMap
    (idxs : List Nat) (slots : List Nat) (out : SAT.Clause) :
    ((slots.map setCoveringCoverageClauseSlotInstruction).foldl
        (fun acc instr => setCoveringCoverageClauseStep (acc, instr)) (idxs, out)).2 =
      out ++ slots.flatMap fun slot =>
        setCoveringCoverageSlotLitsExecutable (slot, idxs) := by
  induction slots generalizing out with
  | nil =>
      simp
  | cons slot rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simpa [setCoveringCoverageClauseSlotInstruction, setCoveringCoverageClauseStep,
        List.append_assoc] using
        ih (out ++ setCoveringCoverageSlotLitsExecutable (slot, idxs))

theorem setCoveringCoverageClauseCoreExecutable_eq_flatMap
    (ctx : SetCoveringCoverageClauseCoreContext) :
    setCoveringCoverageClauseCoreExecutable ctx =
      (List.range ctx.1).flatMap fun slot =>
        setCoveringCoverageSlotLitsExecutable (slot, ctx.2) := by
  change
    (((List.range ctx.1).map setCoveringCoverageClauseSlotInstruction).foldl
        (fun acc instr => setCoveringCoverageClauseStep (acc, instr)) (ctx.2, [])).2 =
      (List.range ctx.1).flatMap fun slot =>
        setCoveringCoverageSlotLitsExecutable (slot, ctx.2)
  simpa using
    setCoveringCoverageClauseIndexFold_eq_append_flatMap ctx.2 (List.range ctx.1) []

theorem setCoveringCoverageClauseExecutable_eq
    (I : SetCoveringInput) (x : Nat) :
    setCoveringCoverageClauseExecutable (I, x) =
      setCoveringCoverageClause I x := by
  rw [setCoveringCoverageClauseExecutable, setCoveringCoverageClauseCoreExecutable_eq_flatMap,
    setCoveringCoverageClauseCoreContext, setCoveringCoverageClause,
    setCoveringCoverageClauseIndexInput]
  apply List.flatMap_congr
  intro slot _hslot
  rw [setCoveringCoverageSlotLitsExecutable_eq_map]
  exact (setCoveringCoverageLitsForSlot_eq_index_map I x slot).symm

/-! ### TM witnesses -/

theorem setCoveringCoverageClauseInitInstruction_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseCoreContextEncodedType
      setCoveringCoverageClauseInstructionEncodedType
      setCoveringCoverageClauseInitInstruction := by
  simpa [setCoveringCoverageClauseInstructionEncodedType,
    setCoveringCoverageClauseInitInstruction] using
    TMPolyTimeMap.inl setCoveringCoverageClauseCoreContextEncodedType EncodedType.nat

theorem setCoveringCoverageClauseSlotInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringCoverageClauseInstructionEncodedType
      setCoveringCoverageClauseSlotInstruction := by
  simpa [setCoveringCoverageClauseInstructionEncodedType,
    setCoveringCoverageClauseSlotInstruction] using
    TMPolyTimeMap.inr setCoveringCoverageClauseCoreContextEncodedType EncodedType.nat

theorem setCoveringCoverageClauseInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseCoreContextEncodedType
      setCoveringCoverageClauseInstructionListEncodedType
      setCoveringCoverageClauseInstructions := by
  let X := setCoveringCoverageClauseCoreContextEncodedType
  have hCtx : TMPolyTimeMap X X (fun ctx : X.Carrier => ctx) := TMPolyTimeMap.id X
  have hSlotCount : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.1) := by
    simpa [X, setCoveringCoverageClauseCoreContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
  have hInit :
      TMPolyTimeMap X setCoveringCoverageClauseInstructionEncodedType
        (fun ctx : X.Carrier => setCoveringCoverageClauseInitInstruction ctx) := by
    have hComp := TMPolyTimeMap.comp setCoveringCoverageClauseInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier => List.range ctx.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hSlotCount
    simpa [Function.comp, X] using hComp
  have hSlotInstructions :
      TMPolyTimeMap X setCoveringCoverageClauseInstructionListEncodedType
        (fun ctx : X.Carrier =>
          (List.range ctx.1).map setCoveringCoverageClauseSlotInstruction) := by
    have hMap := TMPolyTimeMap.list_map setCoveringCoverageClauseSlotInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, setCoveringCoverageClauseInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringCoverageClauseInstructionEncodedType
          setCoveringCoverageClauseInstructionListEncodedType)
        (fun ctx : X.Carrier =>
          (setCoveringCoverageClauseInitInstruction ctx,
            (List.range ctx.1).map setCoveringCoverageClauseSlotInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hSlotInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringCoverageClauseInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringCoverageClauseInstructions,
    setCoveringCoverageClauseInstructionListEncodedType, X] using hCons

theorem setCoveringCoverageClauseStepLeft_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseCoreContextEncodedType
      setCoveringCoverageClauseAccEncodedType
      (fun ctx : SetCoveringCoverageClauseCoreContext =>
        (ctx.2, ([] : SAT.Clause))) := by
  have hIdxs :
      TMPolyTimeMap setCoveringCoverageClauseCoreContextEncodedType
        (EncodedType.list EncodedType.nat)
        (fun ctx : SetCoveringCoverageClauseCoreContext => ctx.2) := by
    simpa [setCoveringCoverageClauseCoreContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
  have hEmpty :
      TMPolyTimeMap setCoveringCoverageClauseCoreContextEncodedType
        clauseStructuredEncodedType
        (fun _ : SetCoveringCoverageClauseCoreContext => ([] : SAT.Clause)) :=
    TMPolyTimeMap.const setCoveringCoverageClauseCoreContextEncodedType
      clauseStructuredEncodedType []
  simpa [setCoveringCoverageClauseAccEncodedType] using TMPolyTimeMap.prod_mk hIdxs hEmpty

theorem setCoveringCoverageClauseStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClauseAccEncodedType EncodedType.nat)
      setCoveringCoverageClauseAccEncodedType
      (fun p : setCoveringCoverageClauseAccEncodedType.Carrier × Nat =>
        (p.1.1, (show SAT.Clause from p.1.2) ++
          setCoveringCoverageSlotLitsExecutable (p.2, p.1.1))) := by
  let X := EncodedType.prod setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringCoverageClauseAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hIdxs :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst (EncodedType.list EncodedType.nat)
      clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringCoverageClauseAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd (EncodedType.list EncodedType.nat)
      clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringCoverageClauseAccEncodedType, X] using hComp
  have hCoverageCtx :
      TMPolyTimeMap X setCoveringCoverageSlotContextEncodedType
        (fun p : X.Carrier => (p.2, p.1.1)) := by
    simpa [setCoveringCoverageSlotContextEncodedType] using TMPolyTimeMap.prod_mk hSlot hIdxs
  have hBlock :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier =>
          setCoveringCoverageSlotLitsExecutable (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setCoveringCoverageSlotLitsExecutable_tm_polytime
      hCoverageCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.Clause from p.1.2),
            setCoveringCoverageSlotLitsExecutable (p.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.Clause from p.1.2) ++
            setCoveringCoverageSlotLitsExecutable (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
    simpa [Function.comp, clauseStructuredEncodedType, X] using hComp
  simpa [setCoveringCoverageClauseAccEncodedType] using TMPolyTimeMap.prod_mk hIdxs hAppend

theorem setCoveringCoverageClauseStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClauseAccEncodedType
        setCoveringCoverageClauseInstructionEncodedType)
      setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseCoreContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringCoverageClauseStepLeft_tm_polytime
      setCoveringCoverageClauseStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Bounded fold certificate -/

def setCoveringCoverageClauseFoldInv (N : Nat)
    (acc : setCoveringCoverageClauseAccEncodedType.Carrier) : Prop :=
  acc = setCoveringCoverageClauseInitAcc ∨
    (EncodedType.list EncodedType.nat).inputSize acc.1 ≤ N

noncomputable def setCoveringCoverageClauseFoldBase : Polynomial Nat :=
  Polynomial.C 20

noncomputable def setCoveringCoverageClauseFoldGrow : Polynomial Nat :=
  (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) *
    ((Polynomial.C 2 * Polynomial.X + Polynomial.C 1) ^ 2 + Polynomial.C 4) +
      Polynomial.C 10

@[simp] theorem setCoveringCoverageClauseFoldGrow_eval (N : Nat) :
    setCoveringCoverageClauseFoldGrow.eval N =
      (2 * N + 1) * ((2 * N + 1) ^ 2 + 4) + 10 := by
  simp [setCoveringCoverageClauseFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem setCoveringCoverageClauseInitAcc_bound
    (xs : List setCoveringCoverageClauseInstructionEncodedType.Carrier) :
    setCoveringCoverageClauseFoldInv
        (setCoveringCoverageClauseInstructionListEncodedType.inputSize xs)
        setCoveringCoverageClauseInitAcc ∧
      setCoveringCoverageClauseAccEncodedType.inputSize setCoveringCoverageClauseInitAcc ≤
        setCoveringCoverageClauseFoldBase.eval
          (setCoveringCoverageClauseInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageClauseFoldBase, setCoveringCoverageClauseInitAcc,
      setCoveringCoverageClauseAccEncodedType]
    native_decide

theorem setCoveringCoverageClauseStep_growth
    (source : List setCoveringCoverageClauseInstructionEncodedType.Carrier)
    (acc : setCoveringCoverageClauseAccEncodedType.Carrier)
    (instr : setCoveringCoverageClauseInstructionEncodedType.Carrier)
    (hInv :
      setCoveringCoverageClauseFoldInv
        (setCoveringCoverageClauseInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringCoverageClauseInstructionEncodedType.inputSize instr ≤
        setCoveringCoverageClauseInstructionListEncodedType.inputSize source) :
    setCoveringCoverageClauseFoldInv
        (setCoveringCoverageClauseInstructionListEncodedType.inputSize source)
        (setCoveringCoverageClauseStep (acc, instr)) ∧
      setCoveringCoverageClauseAccEncodedType.inputSize
          (setCoveringCoverageClauseStep (acc, instr)) ≤
        setCoveringCoverageClauseAccEncodedType.inputSize acc +
          setCoveringCoverageClauseFoldGrow.eval
            (setCoveringCoverageClauseInstructionListEncodedType.inputSize source) := by
  let N := setCoveringCoverageClauseInstructionListEncodedType.inputSize source
  rcases acc with ⟨idxs, out⟩
  cases instr with
  | inl ctx =>
      rcases ctx with ⟨slotCount, newIdxs⟩
      have hCtx : setCoveringCoverageClauseCoreContextEncodedType.inputSize (slotCount, newIdxs) ≤
          N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageClauseInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hIdxs : (EncodedType.list EncodedType.nat).inputSize newIdxs ≤ N := by
        have hCtxProd :
            EncodedType.nat.inputSize slotCount + 1 +
                (EncodedType.list EncodedType.nat).inputSize newIdxs ≤ N := by
          simpa [setCoveringCoverageClauseCoreContextEncodedType,
            EncodedType.inputSize_prod] using hCtx
        omega
      constructor
      · exact Or.inr hIdxs
      · have hEmpty :
            clauseStructuredEncodedType.inputSize ([] : SAT.Clause) = 0 := by
          change (EncodedType.list literalStructuredEncodedType).inputSize ([] : SAT.Clause) = 0
          exact EncodedType.inputSize_list_nil literalStructuredEncodedType
        have hNewAcc :
            setCoveringCoverageClauseAccEncodedType.inputSize (newIdxs, ([] : SAT.Clause)) ≤
              N + 1 := by
          simp [setCoveringCoverageClauseAccEncodedType, EncodedType.inputSize_prod, hEmpty]
          omega
        have hGrowLarge :
            N + 1 ≤ setCoveringCoverageClauseAccEncodedType.inputSize (idxs, out) +
              setCoveringCoverageClauseFoldGrow.eval N := by
          have hPoly : N + 1 ≤ setCoveringCoverageClauseFoldGrow.eval N := by
            rw [setCoveringCoverageClauseFoldGrow_eval]
            nlinarith [sq_nonneg (N : Int)]
          exact hPoly.trans (Nat.le_add_left _ _)
        simpa [setCoveringCoverageClauseStep, N] using hNewAcc.trans hGrowLarge
  | inr slot =>
      change Nat at slot
      have hSlot : EncodedType.nat.inputSize slot ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageClauseInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hIdxs :
          (EncodedType.list EncodedType.nat).inputSize idxs ≤ N := by
        rcases hInv with hInit | hIdxs
        · injection hInit with hIdxsEq _hOut
          rw [hIdxsEq]
          have hNil : EncodedType.nat.list.inputSize ([] : List Nat) = 0 := by
            rfl
          rw [hNil]
          exact Nat.zero_le N
        · exact hIdxs
      have hCoverageCtx :
          setCoveringCoverageSlotContextEncodedType.inputSize (slot, idxs) ≤ 2 * N + 1 := by
        have hSlotLt : slot < N := by
          simpa [EncodedType.inputSize_nat] using hSlot
        simp [setCoveringCoverageSlotContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      have hBlock :=
        setCoveringCoverageSlotLitsExecutable_inputSize_le
          (N := 2 * N + 1) (ctx := (slot, idxs)) hCoverageCtx
      have hGrowBlock :
          clauseStructuredEncodedType.inputSize
              (setCoveringCoverageSlotLitsExecutable (slot, idxs)) ≤
            setCoveringCoverageClauseFoldGrow.eval N := by
        rw [setCoveringCoverageClauseFoldGrow_eval]
        nlinarith [hBlock, sq_nonneg (N : Int)]
      have hAppend :
          clauseStructuredEncodedType.inputSize
              ((show SAT.Clause from out) ++
                setCoveringCoverageSlotLitsExecutable (slot, idxs)) =
            clauseStructuredEncodedType.inputSize out +
              clauseStructuredEncodedType.inputSize
                (setCoveringCoverageSlotLitsExecutable (slot, idxs)) := by
        simpa [clauseStructuredEncodedType] using
          list_inputSize_append literalStructuredEncodedType out
            (setCoveringCoverageSlotLitsExecutable (slot, idxs))
      constructor
      · exact Or.inr hIdxs
      · change
          setCoveringCoverageClauseAccEncodedType.inputSize
              (idxs, (show SAT.Clause from out) ++
                setCoveringCoverageSlotLitsExecutable (slot, idxs)) ≤
            setCoveringCoverageClauseAccEncodedType.inputSize (idxs, out) +
              setCoveringCoverageClauseFoldGrow.eval N
        simp [setCoveringCoverageClauseAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        omega

theorem setCoveringCoverageClauseFold_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseInstructionListEncodedType
      setCoveringCoverageClauseAccEncodedType
      (fun xs : List setCoveringCoverageClauseInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringCoverageClauseStep (acc, instr))
          setCoveringCoverageClauseInitAcc) := by
  rcases setCoveringCoverageClauseStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringCoverageClauseInstructionEncodedType setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseStep setCoveringCoverageClauseInitAcc hStep
      setCoveringCoverageClauseFoldBase setCoveringCoverageClauseFoldGrow
      setCoveringCoverageClauseFoldInv ?_ ?_
  · intro xs
    exact setCoveringCoverageClauseInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringCoverageClauseStep_growth source acc instr hInv hInstr

theorem setCoveringCoverageClauseFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseInstructionListEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageClauseFromInstructions := by
  have hFold := setCoveringCoverageClauseFold_tm_polytime
  have hOut := TMPolyTimeMap.snd (EncodedType.list EncodedType.nat) clauseStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringCoverageClauseFromInstructions,
    setCoveringCoverageClauseAccEncodedType] using hComp

theorem setCoveringCoverageClauseCoreExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseCoreContextEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageClauseCoreExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringCoverageClauseFromInstructions_tm_polytime
      setCoveringCoverageClauseInstructions_tm_polytime
  simpa [Function.comp, setCoveringCoverageClauseCoreExecutable] using hComp

theorem setCoveringCoverageClauseIndexInput_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseContextEncodedType
      HittingSet.setIndexInstructionInputEncodedType
      setCoveringCoverageClauseIndexInput := by
  let X := setCoveringCoverageClauseContextEncodedType
  have hI :
      TMPolyTimeMap X setCoveringStructuredEncodedType (fun ctx : X.Carrier => ctx.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringStructuredEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringStructuredEncodedType EncodedType.nat
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun ctx : X.Carrier => ctx.1.system.sets) := by
    have hComp := TMPolyTimeMap.comp setCoveringSets_tm_polytime hI
    simpa [Function.comp, X] using hComp
  simpa [setCoveringCoverageClauseIndexInput,
    HittingSet.setIndexInstructionInputEncodedType, X] using TMPolyTimeMap.prod_mk hX hSets

theorem setCoveringCoverageClauseCoreContext_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseContextEncodedType
      setCoveringCoverageClauseCoreContextEncodedType
      setCoveringCoverageClauseCoreContext := by
  let X := setCoveringCoverageClauseContextEncodedType
  have hI :
      TMPolyTimeMap X setCoveringStructuredEncodedType (fun ctx : X.Carrier => ctx.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringStructuredEncodedType EncodedType.nat
  have hSourceTuple :
      TMPolyTimeMap X setCoveringTupleStructuredEncodedType
        (fun ctx : X.Carrier => HittingSet.setCoveringInputToTuple ctx.1) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setCoveringInputToTupleTMBackedMap.tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hBudget :
      TMPolyTimeMap X EncodedType.nat (fun ctx : X.Carrier => ctx.1.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hSourceTuple
    simpa [Function.comp, HittingSet.setCoveringInputToTuple,
      setCoveringTupleStructuredEncodedType, X] using hComp
  have hIndexInput := setCoveringCoverageClauseIndexInput_tm_polytime
  have hIndices :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun ctx : X.Carrier =>
          HittingSet.setIndexIndicesFromFamily (setCoveringCoverageClauseIndexInput ctx)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setIndexIndicesFromFamily_tm_polytime hIndexInput
    simpa [Function.comp, X] using hComp
  simpa [setCoveringCoverageClauseCoreContext,
    setCoveringCoverageClauseCoreContextEncodedType, X] using
    TMPolyTimeMap.prod_mk hBudget hIndices

theorem setCoveringCoverageClauseExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseContextEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageClauseExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringCoverageClauseCoreExecutable_tm_polytime
      setCoveringCoverageClauseCoreContext_tm_polytime
  simpa [Function.comp, setCoveringCoverageClauseExecutable] using hComp

/-! ### Output-size bound for the all-coverage fold -/

theorem setCoveringCoverageClauseExecutable_inputSize_le
    {N : Nat} {ctx : SetCoveringCoverageClauseContext}
    (hCtx : setCoveringCoverageClauseContextEncodedType.inputSize ctx ≤ N) :
    clauseStructuredEncodedType.inputSize
        (setCoveringCoverageClauseExecutable ctx) ≤
      N * N * (N ^ 2 + 4) := by
  rcases ctx with ⟨I, x⟩
  rw [setCoveringCoverageClauseExecutable_eq]
  let clause := setCoveringCoverageClause I x
  have hCtxProd :
      setCoveringStructuredEncodedType.inputSize I + 1 + EncodedType.nat.inputSize x ≤ N := by
    change
      (EncodedType.prod setCoveringStructuredEncodedType EncodedType.nat).inputSize (I, x) ≤
        N at hCtx
    rw [EncodedType.inputSize_prod] at hCtx
    exact hCtx
  have hI_N : setCoveringStructuredEncodedType.inputSize I ≤ N := by omega
  have hK_N : I.k ≤ N := by
    rw [SetCovering.setCoveringStructured_inputSize_eq] at hI_N
    omega
  have hSetsLen_N : I.system.sets.length ≤ N :=
    (HittingSet.setCoveringStructured_inputSize_ge_sets_length I).trans hI_N
  have hVar : ∀ l ∈ clause, l.var ≤ N ^ 2 := by
    intro l hl
    dsimp [clause] at hl
    rw [mem_setCoveringCoverageClause_iff] at hl
    rcases hl with ⟨slot, hslot, idx, hidx, _hx, rfl⟩
    have hSlotN : slot + 1 ≤ N := by omega
    have hIdxN : idx + 1 ≤ N := by omega
    have hMax : max slot idx + 1 ≤ N := by omega
    exact (Nat.le_of_lt (Nat.pair_lt_max_add_one_sq slot idx)).trans
      (Nat.pow_le_pow_left hMax 2)
  have hClause :=
    clauseStructured_inputSize_le_length_mul_of_lit_var_le
      (c := clause) (V := N ^ 2) hVar
  have hLen : clause.length ≤ N * N := by
    dsimp [clause]
    rw [setCoveringCoverageClause]
    have hFlat :
        ((List.range I.k).flatMap (setCoveringCoverageLitsForSlot I x)).length ≤
          I.k * I.system.sets.length := by
      have hRaw :=
        setCoveringFlatMap_length_le_mul (List.range I.k)
          (setCoveringCoverageLitsForSlot I x) I.system.sets.length
          (by
            intro slot _hslot
            unfold setCoveringCoverageLitsForSlot
            have hFilter :=
              List.length_filterMap_le
                (fun idx =>
                  if x ∈ sourceSetAt I idx then some (setCoveringChoiceLit I slot idx)
                  else none)
                (List.range I.system.sets.length)
            simpa using hFilter)
      simpa using hRaw
    exact hFlat.trans (Nat.mul_le_mul hK_N hSetsLen_N)
  change clauseStructuredEncodedType.inputSize clause ≤ N * N * (N ^ 2 + 4)
  exact hClause.trans (by
    nlinarith [Nat.mul_le_mul_right (N ^ 2 + 4) hLen])

end ExactCover
end Karp21
end ComplexityReduction
