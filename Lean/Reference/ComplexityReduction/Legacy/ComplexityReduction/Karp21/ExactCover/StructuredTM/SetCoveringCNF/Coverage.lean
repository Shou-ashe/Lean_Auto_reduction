import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.CoverageClause

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Executable all-coverage clauses for the Set-Covering-to-CNF route.

This module builds the `(I, x)` context list for all universe elements using a
bounded fold, then maps each context through the single-element coverage-clause
runner from `CoverageClause`.
-/

def setCoveringCoverageClausesInstructionEncodedType : EncodedType :=
  EncodedType.sum setCoveringCoverageClauseContextEncodedType EncodedType.nat

def setCoveringCoverageClausesInstructionListEncodedType : EncodedType :=
  EncodedType.list setCoveringCoverageClausesInstructionEncodedType

def setCoveringCoverageClausesContextListEncodedType : EncodedType :=
  EncodedType.list setCoveringCoverageClauseContextEncodedType

def setCoveringCoverageClausesAccEncodedType : EncodedType :=
  EncodedType.prod setCoveringStructuredEncodedType
    setCoveringCoverageClausesContextListEncodedType

def setCoveringCoverageClausesZeroInput : SetCoveringInput where
  system := { universeSize := 0, sets := [] }
  k := 0

def setCoveringCoverageClausesInitAcc :
    setCoveringCoverageClausesAccEncodedType.Carrier :=
  (setCoveringCoverageClausesZeroInput, ([] : List SetCoveringCoverageClauseContext))

def setCoveringCoverageClausesInitInstruction
    (I : SetCoveringInput) :
    setCoveringCoverageClausesInstructionEncodedType.Carrier :=
  Sum.inl (I, (show EncodedType.nat.Carrier from (0 : Nat)))

def setCoveringCoverageClausesElementInstruction
    (x : Nat) : setCoveringCoverageClausesInstructionEncodedType.Carrier :=
  Sum.inr x

def setCoveringCoverageClausesInstructions
    (I : SetCoveringInput) :
    List setCoveringCoverageClausesInstructionEncodedType.Carrier :=
  setCoveringCoverageClausesInitInstruction I ::
    (List.range I.system.universeSize).map
      setCoveringCoverageClausesElementInstruction

def setCoveringCoverageClausesContextStep
    (p : setCoveringCoverageClausesAccEncodedType.Carrier ×
      setCoveringCoverageClausesInstructionEncodedType.Carrier) :
    setCoveringCoverageClausesAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx.1, [])
  | Sum.inr x =>
      (p.1.1,
        (show List SetCoveringCoverageClauseContext from p.1.2) ++
          ([(p.1.1, x)] : List SetCoveringCoverageClauseContext))

def setCoveringCoverageClausesContextsFromInstructions
    (xs : List setCoveringCoverageClausesInstructionEncodedType.Carrier) :
    List SetCoveringCoverageClauseContext :=
  (xs.foldl (fun acc instr => setCoveringCoverageClausesContextStep (acc, instr))
    setCoveringCoverageClausesInitAcc).2

def setCoveringCoverageClausesContextsExecutable
    (I : SetCoveringInput) : List SetCoveringCoverageClauseContext :=
  setCoveringCoverageClausesContextsFromInstructions
    (setCoveringCoverageClausesInstructions I)

def setCoveringCoverageClausesExecutable
    (I : SetCoveringInput) : SAT.CNF :=
  (setCoveringCoverageClausesContextsExecutable I).map
    setCoveringCoverageClauseExecutable

/-! ### Semantics -/

theorem setCoveringCoverageClausesElementFold_eq_append_map
    (I : SetCoveringInput) (xs : List Nat)
    (out : List SetCoveringCoverageClauseContext) :
    ((xs.map setCoveringCoverageClausesElementInstruction).foldl
        (fun acc instr => setCoveringCoverageClausesContextStep (acc, instr)) (I, out)).2 =
      out ++ xs.map (fun x => (I, x)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x rest ih =>
      rw [List.map_cons, List.foldl_cons]
      simpa [setCoveringCoverageClausesElementInstruction,
        setCoveringCoverageClausesContextStep, List.append_assoc] using
        ih (out ++ [(I, x)])

theorem setCoveringCoverageClausesContextsExecutable_eq
    (I : SetCoveringInput) :
    setCoveringCoverageClausesContextsExecutable I =
      (List.range I.system.universeSize).map fun x => (I, x) := by
  change
    (((List.range I.system.universeSize).map
        setCoveringCoverageClausesElementInstruction).foldl
        (fun acc instr => setCoveringCoverageClausesContextStep (acc, instr)) (I, [])).2 =
      (List.range I.system.universeSize).map fun x => (I, x)
  simpa using
    setCoveringCoverageClausesElementFold_eq_append_map I
      (List.range I.system.universeSize) []

theorem setCoveringCoverageClausesExecutable_eq
    (I : SetCoveringInput) :
    setCoveringCoverageClausesExecutable I =
      setCoveringCoverageClauses I := by
  rw [setCoveringCoverageClausesExecutable,
    setCoveringCoverageClausesContextsExecutable_eq, setCoveringCoverageClauses]
  rw [List.map_map]
  apply List.map_congr_left
  intro x _hx
  exact setCoveringCoverageClauseExecutable_eq I x

/-! ### TM witnesses -/

theorem setCoveringCoverageClausesInitInstruction_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringCoverageClausesInstructionEncodedType
      setCoveringCoverageClausesInitInstruction := by
  let X := setCoveringStructuredEncodedType
  have hI : TMPolyTimeMap X setCoveringStructuredEncodedType (fun I : X.Carrier => I) :=
    TMPolyTimeMap.id X
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  have hCtx :
      TMPolyTimeMap X setCoveringCoverageClauseContextEncodedType
        (fun I : X.Carrier => (I, (0 : Nat))) := by
    simpa [setCoveringCoverageClauseContextEncodedType, X] using
      TMPolyTimeMap.prod_mk hI hZero
  have hInl :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.inl setCoveringCoverageClauseContextEncodedType EncodedType.nat)
      hCtx
  simpa [Function.comp, setCoveringCoverageClausesInitInstruction,
    setCoveringCoverageClausesInstructionEncodedType, X] using hInl

theorem setCoveringCoverageClausesElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setCoveringCoverageClausesInstructionEncodedType
      setCoveringCoverageClausesElementInstruction := by
  simpa [setCoveringCoverageClausesInstructionEncodedType,
    setCoveringCoverageClausesElementInstruction] using
    TMPolyTimeMap.inr setCoveringCoverageClauseContextEncodedType EncodedType.nat

theorem setCoveringUniverseSize_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      EncodedType.nat
      (fun I : SetCoveringInput => I.system.universeSize) := by
  let X := setCoveringStructuredEncodedType
  have hSystem := setCoveringSystem_tm_polytime
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun I : SetCoveringInput => HittingSet.setSystemInputToTuple I.system) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, X] using hComp
  have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hFst hSystemTuple
  simpa [Function.comp, HittingSet.setSystemInputToTuple,
    setSystemTupleStructuredEncodedType, X] using hComp

theorem setCoveringCoverageClausesInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringCoverageClausesInstructionListEncodedType
      setCoveringCoverageClausesInstructions := by
  let X := setCoveringStructuredEncodedType
  have hInit := setCoveringCoverageClausesInitInstruction_tm_polytime
  have hUniverse := setCoveringUniverseSize_tm_polytime
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun I : X.Carrier => List.range I.system.universeSize) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X setCoveringCoverageClausesInstructionListEncodedType
        (fun I : X.Carrier =>
          (List.range I.system.universeSize).map
            setCoveringCoverageClausesElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map
      setCoveringCoverageClausesElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, setCoveringCoverageClausesInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringCoverageClausesInstructionEncodedType
          setCoveringCoverageClausesInstructionListEncodedType)
        (fun I : X.Carrier =>
          (setCoveringCoverageClausesInitInstruction I,
            (List.range I.system.universeSize).map
              setCoveringCoverageClausesElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hElementInstructions
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setCoveringCoverageClausesInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setCoveringCoverageClausesInstructions,
    setCoveringCoverageClausesInstructionListEncodedType, X] using hCons

theorem setCoveringCoverageClausesStepLeft_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClauseContextEncodedType
      setCoveringCoverageClausesAccEncodedType
      (fun ctx : SetCoveringCoverageClauseContext =>
        (ctx.1, ([] : List SetCoveringCoverageClauseContext))) := by
  have hSource :
      TMPolyTimeMap setCoveringCoverageClauseContextEncodedType
        setCoveringStructuredEncodedType
        (fun ctx : SetCoveringCoverageClauseContext => ctx.1) := by
    simpa [setCoveringCoverageClauseContextEncodedType] using
      TMPolyTimeMap.fst setCoveringStructuredEncodedType EncodedType.nat
  have hEmpty :
      TMPolyTimeMap setCoveringCoverageClauseContextEncodedType
        setCoveringCoverageClausesContextListEncodedType
        (fun _ : SetCoveringCoverageClauseContext =>
          ([] : List SetCoveringCoverageClauseContext)) :=
    TMPolyTimeMap.const setCoveringCoverageClauseContextEncodedType
      setCoveringCoverageClausesContextListEncodedType []
  simpa [setCoveringCoverageClausesAccEncodedType] using TMPolyTimeMap.prod_mk hSource hEmpty

theorem setCoveringCoverageClausesStepRight_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClausesAccEncodedType EncodedType.nat)
      setCoveringCoverageClausesAccEncodedType
      (fun p : setCoveringCoverageClausesAccEncodedType.Carrier × Nat =>
        (p.1.1,
          (show List SetCoveringCoverageClauseContext from p.1.2) ++
            ([(p.1.1, p.2)] : List SetCoveringCoverageClauseContext))) := by
  let X := EncodedType.prod setCoveringCoverageClausesAccEncodedType EncodedType.nat
  have hAcc :
      TMPolyTimeMap X setCoveringCoverageClausesAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringCoverageClausesAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringCoverageClausesAccEncodedType EncodedType.nat
  have hSource :
      TMPolyTimeMap X setCoveringStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setCoveringStructuredEncodedType
      setCoveringCoverageClausesContextListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringCoverageClausesAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X setCoveringCoverageClausesContextListEncodedType
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setCoveringStructuredEncodedType
      setCoveringCoverageClausesContextListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringCoverageClausesAccEncodedType, X] using hComp
  have hCtx :
      TMPolyTimeMap X setCoveringCoverageClauseContextEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) := by
    simpa [setCoveringCoverageClauseContextEncodedType] using
      TMPolyTimeMap.prod_mk hSource hX
  have hSingleton :
      TMPolyTimeMap X setCoveringCoverageClausesContextListEncodedType
        (fun p : X.Carrier => ([(p.1.1, p.2)] : List SetCoveringCoverageClauseContext)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton setCoveringCoverageClauseContextEncodedType) hCtx
    simpa [Function.comp, setCoveringCoverageClausesContextListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setCoveringCoverageClausesContextListEncodedType
          setCoveringCoverageClausesContextListEncodedType)
        (fun p : X.Carrier =>
          ((show List SetCoveringCoverageClauseContext from p.1.2),
            ([(p.1.1, p.2)] : List SetCoveringCoverageClauseContext))) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X setCoveringCoverageClausesContextListEncodedType
        (fun p : X.Carrier =>
          (show List SetCoveringCoverageClauseContext from p.1.2) ++
            ([(p.1.1, p.2)] : List SetCoveringCoverageClauseContext)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append setCoveringCoverageClauseContextEncodedType) hAppendInput
    simpa [Function.comp, setCoveringCoverageClausesContextListEncodedType, X] using hComp
  simpa [setCoveringCoverageClausesAccEncodedType] using TMPolyTimeMap.prod_mk hSource hAppend

theorem setCoveringCoverageClausesContextStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClausesAccEncodedType
        setCoveringCoverageClausesInstructionEncodedType)
      setCoveringCoverageClausesAccEncodedType
      setCoveringCoverageClausesContextStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringCoverageClausesAccEncodedType
      setCoveringCoverageClauseContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringCoverageClausesStepLeft_tm_polytime
      setCoveringCoverageClausesStepRight_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def setCoveringCoverageClausesFoldInv (N : Nat)
    (acc : setCoveringCoverageClausesAccEncodedType.Carrier) : Prop :=
  acc = setCoveringCoverageClausesInitAcc ∨
    acc.1 = setCoveringCoverageClausesZeroInput ∨
      setCoveringStructuredEncodedType.inputSize acc.1 ≤ N

noncomputable def setCoveringCoverageClausesFoldBase : Polynomial Nat :=
  Polynomial.C 20

noncomputable def setCoveringCoverageClausesFoldGrow : Polynomial Nat :=
  Polynomial.C 4 * Polynomial.X + Polynomial.C 10

@[simp] theorem setCoveringCoverageClausesFoldGrow_eval (N : Nat) :
    setCoveringCoverageClausesFoldGrow.eval N = 4 * N + 10 := by
  simp [setCoveringCoverageClausesFoldGrow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem setCoveringCoverageClausesInitAcc_bound
    (xs : List setCoveringCoverageClausesInstructionEncodedType.Carrier) :
    setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize xs)
        setCoveringCoverageClausesInitAcc ∧
      setCoveringCoverageClausesAccEncodedType.inputSize setCoveringCoverageClausesInitAcc ≤
        setCoveringCoverageClausesFoldBase.eval
          (setCoveringCoverageClausesInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageClausesFoldBase, setCoveringCoverageClausesInitAcc,
      setCoveringCoverageClausesAccEncodedType]
    native_decide

theorem setCoveringCoverageClausesContextStep_growth
    (source : List setCoveringCoverageClausesInstructionEncodedType.Carrier)
    (acc : setCoveringCoverageClausesAccEncodedType.Carrier)
    (instr : setCoveringCoverageClausesInstructionEncodedType.Carrier)
    (hInv :
      setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringCoverageClausesInstructionEncodedType.inputSize instr ≤
        setCoveringCoverageClausesInstructionListEncodedType.inputSize source) :
    setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize source)
        (setCoveringCoverageClausesContextStep (acc, instr)) ∧
      setCoveringCoverageClausesAccEncodedType.inputSize
          (setCoveringCoverageClausesContextStep (acc, instr)) ≤
        setCoveringCoverageClausesAccEncodedType.inputSize acc +
          setCoveringCoverageClausesFoldGrow.eval
            (setCoveringCoverageClausesInstructionListEncodedType.inputSize source) := by
  let N := setCoveringCoverageClausesInstructionListEncodedType.inputSize source
  rcases acc with ⟨I, out⟩
  cases instr with
  | inl ctx =>
      have hCtx : setCoveringCoverageClauseContextEncodedType.inputSize ctx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageClausesInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hSource : setCoveringStructuredEncodedType.inputSize ctx.1 ≤ N := by
        have hCtxProd :
            setCoveringStructuredEncodedType.inputSize ctx.1 + 1 +
                EncodedType.nat.inputSize ctx.2 ≤ N := by
          simpa [setCoveringCoverageClauseContextEncodedType,
            EncodedType.inputSize_prod] using hCtx
        omega
      constructor
      · exact Or.inr (Or.inr hSource)
      · have hEmpty :
            setCoveringCoverageClausesContextListEncodedType.inputSize
                ([] : List SetCoveringCoverageClauseContext) = 0 := by
          exact EncodedType.inputSize_list_nil setCoveringCoverageClauseContextEncodedType
        have hNewAcc :
            setCoveringCoverageClausesAccEncodedType.inputSize
                (ctx.1, ([] : List SetCoveringCoverageClauseContext)) ≤ N + 1 := by
          simp [setCoveringCoverageClausesAccEncodedType, EncodedType.inputSize_prod, hEmpty]
          omega
        have hGrowLarge :
            N + 1 ≤ setCoveringCoverageClausesAccEncodedType.inputSize (I, out) +
              setCoveringCoverageClausesFoldGrow.eval N := by
          have hPoly : N + 1 ≤ setCoveringCoverageClausesFoldGrow.eval N := by
            rw [setCoveringCoverageClausesFoldGrow_eval]
            omega
          exact hPoly.trans (Nat.le_add_left _ _)
        simpa [setCoveringCoverageClausesContextStep, N] using hNewAcc.trans hGrowLarge
  | inr x =>
      change Nat at x
      have hNatLtN : EncodedType.nat.inputSize x < N := by
        simpa [N, setCoveringCoverageClausesInstructionEncodedType,
          EncodedType.inputSize, EncodedType.sum] using hInstr
      have hX : EncodedType.nat.inputSize x ≤ N :=
        Nat.le_of_lt hNatLtN
      have hNge2 : 2 ≤ N := by
        have hOne : 1 ≤ EncodedType.nat.inputSize x := by
          simp [EncodedType.inputSize_nat]
        omega
      have hZeroSize :
          setCoveringStructuredEncodedType.inputSize setCoveringCoverageClausesZeroInput = 4 := by
        change setCoveringTupleStructuredEncodedType.inputSize
          ({ universeSize := 0, sets := [] }, (0 : Nat)) = 4
        simp [setCoveringTupleStructuredEncodedType, setSystemStructuredEncodedType,
          setSystemTupleStructuredEncodedType, setFamilyStructuredEncodedType]
        native_decide
      have hxSize : x + 1 ≤ N := by
        simpa [EncodedType.inputSize_nat] using hX
      have hZeroBound :
          setCoveringStructuredEncodedType.inputSize setCoveringCoverageClausesZeroInput ≤
            N + 2 := by
        rw [hZeroSize]
        omega
      have hSourceInv :
          I = setCoveringCoverageClausesZeroInput ∨
            setCoveringStructuredEncodedType.inputSize I ≤ N := by
        rcases hInv with hInit | hSource
        · injection hInit with hIEq _hOut
          exact Or.inl hIEq
        · rcases hSource with hZero | hSource
          · exact Or.inl hZero
          · exact Or.inr hSource
      have hSourceBound : setCoveringStructuredEncodedType.inputSize I ≤ N + 2 := by
        rcases hSourceInv with hZero | hSource
        · rw [hZero]
          exact hZeroBound
        · omega
      have hCtx :
          setCoveringCoverageClauseContextEncodedType.inputSize (I, x) ≤ 2 * N + 3 := by
        simp [setCoveringCoverageClauseContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      have hSingleton :
          setCoveringCoverageClausesContextListEncodedType.inputSize [(I, x)] ≤ 2 * N + 4 := by
        change (EncodedType.list setCoveringCoverageClauseContextEncodedType).inputSize
            [(I, x)] ≤ 2 * N + 4
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        omega
      have hSingletonGrow :
          setCoveringCoverageClausesContextListEncodedType.inputSize [(I, x)] ≤
            setCoveringCoverageClausesFoldGrow.eval N := by
        rw [setCoveringCoverageClausesFoldGrow_eval]
        omega
      have hAppend :
          setCoveringCoverageClausesContextListEncodedType.inputSize
              ((show List SetCoveringCoverageClauseContext from out) ++
                ([(I, x)] : List SetCoveringCoverageClauseContext)) =
            setCoveringCoverageClausesContextListEncodedType.inputSize out +
              setCoveringCoverageClausesContextListEncodedType.inputSize
                ([(I, x)] : List SetCoveringCoverageClauseContext) := by
        simpa [setCoveringCoverageClausesContextListEncodedType] using
          list_inputSize_append setCoveringCoverageClauseContextEncodedType out
            ([(I, x)] : List SetCoveringCoverageClauseContext)
      constructor
      · exact Or.inr hSourceInv
      · change
          setCoveringCoverageClausesAccEncodedType.inputSize
              (I,
                (show List SetCoveringCoverageClauseContext from out) ++
                  ([(I, x)] : List SetCoveringCoverageClauseContext)) ≤
            setCoveringCoverageClausesAccEncodedType.inputSize (I, out) +
              setCoveringCoverageClausesFoldGrow.eval N
        simp [setCoveringCoverageClausesAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        rw [setCoveringCoverageClausesFoldGrow_eval] at hSingletonGrow
        let A := setCoveringStructuredEncodedType.inputSize I
        let B := setCoveringCoverageClausesContextListEncodedType.inputSize out
        let S :=
          setCoveringCoverageClausesContextListEncodedType.inputSize
            ([(I, x)] : List SetCoveringCoverageClauseContext)
        have hS : S ≤ 4 * N + 10 := by
          simpa [S] using hSingletonGrow
        change A + 1 + (B + S) ≤ A + 1 + B + (4 * N + 10)
        omega

theorem setCoveringCoverageClausesContextsFromInstructions_tm_polytime :
    TMPolyTimeMap
      setCoveringCoverageClausesInstructionListEncodedType
      setCoveringCoverageClausesContextListEncodedType
      setCoveringCoverageClausesContextsFromInstructions := by
  rcases setCoveringCoverageClausesContextStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        setCoveringCoverageClausesInstructionListEncodedType
        setCoveringCoverageClausesAccEncodedType
        (fun xs : List setCoveringCoverageClausesInstructionEncodedType.Carrier =>
          xs.foldl (fun acc instr => setCoveringCoverageClausesContextStep (acc, instr))
            setCoveringCoverageClausesInitAcc) := by
    refine
      TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
        setCoveringCoverageClausesInstructionEncodedType setCoveringCoverageClausesAccEncodedType
        setCoveringCoverageClausesContextStep setCoveringCoverageClausesInitAcc hStep
        setCoveringCoverageClausesFoldBase setCoveringCoverageClausesFoldGrow
        setCoveringCoverageClausesFoldInv ?_ ?_
    · intro xs
      exact setCoveringCoverageClausesInitAcc_bound xs
    · intro source acc instr hInv hInstr
      exact setCoveringCoverageClausesContextStep_growth source acc instr hInv hInstr
  have hOut := TMPolyTimeMap.snd setCoveringStructuredEncodedType
    setCoveringCoverageClausesContextListEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringCoverageClausesContextsFromInstructions,
    setCoveringCoverageClausesAccEncodedType] using hComp

theorem setCoveringCoverageClausesContextsExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringCoverageClausesContextListEncodedType
      setCoveringCoverageClausesContextsExecutable := by
  have hComp :=
    TMPolyTimeMap.comp setCoveringCoverageClausesContextsFromInstructions_tm_polytime
      setCoveringCoverageClausesInstructions_tm_polytime
  simpa [Function.comp, setCoveringCoverageClausesContextsExecutable] using hComp

theorem setCoveringCoverageClausesExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringCoverageClausesExecutable := by
  have hContexts := setCoveringCoverageClausesContextsExecutable_tm_polytime
  have hMap := TMPolyTimeMap.list_map setCoveringCoverageClauseExecutable_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap hContexts
  simpa [Function.comp, setCoveringCoverageClausesExecutable,
    setCoveringCoverageClausesContextListEncodedType, cnfStructuredEncodedType] using hComp

end ExactCover
end Karp21
end ComplexityReduction
