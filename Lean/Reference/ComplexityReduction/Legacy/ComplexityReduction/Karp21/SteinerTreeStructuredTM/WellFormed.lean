/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Projections
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ProductSumChoice

/-!
Executable well-formedness guard for the compact Exact-Cover-to-Steiner-Tree
route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics

/-! ### Unary strict comparison -/

def natLtBool (p : Nat × Nat) : Bool :=
  decide (p.1 < p.2)

theorem natLtBool_eq_true_iff (p : Nat × Nat) :
    natLtBool p = true ↔ p.1 < p.2 := by
  simp [natLtBool]

theorem natLtBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      natLtBool := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSuccLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1 + 1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hLeft
    simpa [Function.comp, Nat.succ_eq_add_one, X] using hComp
  have hSubInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1 + 1, p.2)) :=
    TMPolyTimeMap.prod_mk hSuccLeft hRight
  have hSub : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat => p.1 + 1 - p.2) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat =>
          (p.1 + 1 - p.2, (show EncodedType.nat.Carrier from (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hSub hZero
  have hEq := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
  convert hEq using 1
  funext p
  rcases p with ⟨a, b⟩
  by_cases h : a < b
  · have hzero : a + 1 - b = 0 := by omega
    simp [Function.comp, natLtBool, h, hzero]
  · have hnzero : a + 1 - b ≠ 0 := by omega
    simp [Function.comp, natLtBool, h, hnzero]

/-! ### One set: all elements are below the universe bound -/

def setAllLtAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

def setAllLtInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat EncodedType.nat

def setAllLtInstructionListEncodedType : EncodedType :=
  EncodedType.list setAllLtInstructionEncodedType

def setAllLtInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def setAllLtInitAcc : Nat × Bool :=
  (0, true)

def setAllLtInitInstruction (bound : Nat) :
    setAllLtInstructionEncodedType.Carrier :=
  Sum.inl bound

def setAllLtElementInstruction (x : Nat) :
    setAllLtInstructionEncodedType.Carrier :=
  Sum.inr x

def setAllLtInstructions (p : Nat × List Nat) :
    List setAllLtInstructionEncodedType.Carrier :=
  setAllLtInitInstruction p.1 :: p.2.map setAllLtElementInstruction

def setAllLtElementStep (p : (Nat × Bool) × Nat) : Nat × Bool :=
  (p.1.1, graphBoolAndPair (p.1.2, natLtBool (p.2, p.1.1)))

def setAllLtStep
    (p : (Nat × Bool) × setAllLtInstructionEncodedType.Carrier) : Nat × Bool :=
  match p.2 with
  | Sum.inl bound => (bound, true)
  | Sum.inr x => setAllLtElementStep (p.1, x)

def setAllLtFromInstructions
    (xs : List setAllLtInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => setAllLtStep (acc, instr)) setAllLtInitAcc).2

def setAllLtBool (p : Nat × List Nat) : Bool :=
  setAllLtFromInstructions (setAllLtInstructions p)

theorem setAllLtElementFold_eq_true_iff (xs : List Nat) (bound : Nat) (ok : Bool) :
    ((xs.map setAllLtElementInstruction).foldl
        (fun acc instr => setAllLtStep (acc, instr)) (bound, ok)).2 = true ↔
      ok = true ∧ ∀ x ∈ xs, x < bound := by
  induction xs generalizing ok with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      have hTail := ih (graphBoolAndPair (ok, natLtBool (x, bound)))
      simpa [setAllLtElementInstruction, setAllLtStep, setAllLtElementStep,
        graphBoolAndPair_eq_true_iff, natLtBool_eq_true_iff, and_assoc] using hTail

theorem setAllLtBool_eq_true_iff (p : Nat × List Nat) :
    setAllLtBool p = true ↔ ∀ x ∈ p.2, x < p.1 := by
  rcases p with ⟨bound, xs⟩
  simpa [setAllLtBool, setAllLtFromInstructions, setAllLtInstructions,
    setAllLtInitInstruction, setAllLtStep, setAllLtInitAcc] using
    (setAllLtElementFold_eq_true_iff xs bound true)

theorem setAllLtInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setAllLtInstructionEncodedType
      setAllLtInitInstruction := by
  simpa [setAllLtInstructionEncodedType, setAllLtInitInstruction] using
    TMPolyTimeMap.inl EncodedType.nat EncodedType.nat

theorem setAllLtElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setAllLtInstructionEncodedType
      setAllLtElementInstruction := by
  simpa [setAllLtInstructionEncodedType, setAllLtElementInstruction] using
    TMPolyTimeMap.inr EncodedType.nat EncodedType.nat

theorem setAllLtInstructions_tm_polytime :
    TMPolyTimeMap
      setAllLtInputEncodedType
      setAllLtInstructionListEncodedType
      setAllLtInstructions := by
  let X := setAllLtInputEncodedType
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, setAllLtInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setAllLtInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X setAllLtInstructionEncodedType
        (fun p : X.Carrier => setAllLtInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp setAllLtInitInstruction_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X setAllLtInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setAllLtElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map setAllLtElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSet
    simpa [Function.comp, setAllLtInstructionListEncodedType, setStructuredEncodedType, X]
      using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setAllLtInstructionEncodedType setAllLtInstructionListEncodedType)
        (fun p : X.Carrier =>
          (setAllLtInitInstruction p.1, p.2.map setAllLtElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons setAllLtInstructionEncodedType) hConsInput
  simpa [Function.comp, setAllLtInstructions, setAllLtInstructionListEncodedType, X]
    using hCons

theorem setAllLtElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setAllLtAccEncodedType EncodedType.nat)
      setAllLtAccEncodedType
      setAllLtElementStep := by
  let X := EncodedType.prod setAllLtAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setAllLtAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setAllLtAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setAllLtAccEncodedType EncodedType.nat
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setAllLtAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setAllLtAccEncodedType, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hX hBound
  have hLt : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLtBool (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hLtInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, natLtBool (p.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hLt
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolAndPair (p.1.2, natLtBool (p.2, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hBound hAnd
  simpa [setAllLtElementStep, setAllLtAccEncodedType, X] using hOut

theorem setAllLtStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setAllLtAccEncodedType
      (fun bound : Nat => (bound, true)) := by
  have hBound := TMPolyTimeMap.id EncodedType.nat
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  simpa [setAllLtAccEncodedType] using TMPolyTimeMap.prod_mk hBound hTrue

theorem setAllLtStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setAllLtAccEncodedType setAllLtInstructionEncodedType)
      setAllLtAccEncodedType
      setAllLtStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime setAllLtAccEncodedType EncodedType.nat EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setAllLtStepLeft_tm_polytime
      setAllLtElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem setAllLtInitAcc_bound
    (xs : List setAllLtInstructionEncodedType.Carrier) :
    setAllLtAccEncodedType.inputSize setAllLtInitAcc ≤
      (Polynomial.C 5).eval (setAllLtInstructionListEncodedType.inputSize xs) := by
  simp [setAllLtInitAcc, setAllLtAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]

theorem setAllLtStep_growth
    (source : List setAllLtInstructionEncodedType.Carrier)
    (acc : setAllLtAccEncodedType.Carrier)
    (instr : setAllLtInstructionEncodedType.Carrier)
    (hInstr :
      setAllLtInstructionEncodedType.inputSize instr ≤
        setAllLtInstructionListEncodedType.inputSize source) :
    setAllLtAccEncodedType.inputSize (setAllLtStep (acc, instr)) ≤
      setAllLtAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (setAllLtInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bound, ok⟩
  cases instr with
  | inl newBound =>
      change Nat at newBound
      have hNew : newBound + 2 ≤ setAllLtInstructionListEncodedType.inputSize source := by
        have hNewLt : newBound + 1 <
            setAllLtInstructionListEncodedType.inputSize source := by
          simpa [setAllLtInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
            EncodedType.nat] using hInstr
        omega
      simp [setAllLtStep, setAllLtAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      omega
  | inr x =>
      change Nat at x
      simp [setAllLtStep, setAllLtElementStep, setAllLtAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem setAllLtFold_tm_polytime :
    TMPolyTimeMap
      setAllLtInstructionListEncodedType
      setAllLtAccEncodedType
      (fun xs : List setAllLtInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setAllLtStep (acc, instr)) setAllLtInitAcc) := by
  rcases setAllLtStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      setAllLtInstructionEncodedType setAllLtAccEncodedType
      setAllLtStep setAllLtInitAcc hStep
      (Polynomial.C 5) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact setAllLtInitAcc_bound xs
  · intro source acc instr hInstr
    exact setAllLtStep_growth source acc instr hInstr

theorem setAllLtFromInstructions_tm_polytime :
    TMPolyTimeMap
      setAllLtInstructionListEncodedType
      EncodedType.bool
      setAllLtFromInstructions := by
  have hFold := setAllLtFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, setAllLtFromInstructions, setAllLtAccEncodedType] using hComp

theorem setAllLtBool_tm_polytime :
    TMPolyTimeMap
      setAllLtInputEncodedType
      EncodedType.bool
      setAllLtBool := by
  have hComp := TMPolyTimeMap.comp setAllLtFromInstructions_tm_polytime
    setAllLtInstructions_tm_polytime
  simpa [Function.comp, setAllLtBool] using hComp

/-! ### Whole set-system guard -/

def setSystemWellFormedAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

def setSystemWellFormedInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat setStructuredEncodedType

def setSystemWellFormedInstructionListEncodedType : EncodedType :=
  EncodedType.list setSystemWellFormedInstructionEncodedType

def setSystemWellFormedInitAcc : Nat × Bool :=
  (0, true)

def setSystemWellFormedInitInstruction (bound : Nat) :
    setSystemWellFormedInstructionEncodedType.Carrier :=
  Sum.inl bound

def setSystemWellFormedSetInstruction (S : List Nat) :
    setSystemWellFormedInstructionEncodedType.Carrier :=
  Sum.inr S

def setSystemWellFormedInstructions (S : SetSystemInput) :
    List setSystemWellFormedInstructionEncodedType.Carrier :=
  setSystemWellFormedInitInstruction S.universeSize ::
    S.sets.map setSystemWellFormedSetInstruction

def setSystemWellFormedSetStep (p : (Nat × Bool) × List Nat) : Nat × Bool :=
  (p.1.1, graphBoolAndPair (p.1.2, setAllLtBool (p.1.1, p.2)))

def setSystemWellFormedStep
    (p : (Nat × Bool) × setSystemWellFormedInstructionEncodedType.Carrier) : Nat × Bool :=
  match p.2 with
  | Sum.inl bound => (bound, true)
  | Sum.inr S => setSystemWellFormedSetStep (p.1, S)

def setSystemWellFormedFromInstructions
    (xs : List setSystemWellFormedInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => setSystemWellFormedStep (acc, instr))
    setSystemWellFormedInitAcc).2

def setSystemWellFormedBool (S : SetSystemInput) : Bool :=
  setSystemWellFormedFromInstructions (setSystemWellFormedInstructions S)

def exactCoverWellFormedBool (I : ExactCoverInput) : Bool :=
  setSystemWellFormedBool I.system

theorem setSystemWellFormedSetFold_eq_true_iff
    (sets : List (List Nat)) (bound : Nat) (ok : Bool) :
    ((sets.map setSystemWellFormedSetInstruction).foldl
        (fun acc instr => setSystemWellFormedStep (acc, instr)) (bound, ok)).2 = true ↔
      ok = true ∧ ∀ S ∈ sets, ∀ x ∈ S, x < bound := by
  induction sets generalizing ok with
  | nil =>
      simp
  | cons S sets ih =>
      rw [List.map_cons, List.foldl_cons]
      have hTail := ih (graphBoolAndPair (ok, setAllLtBool (bound, S)))
      simpa [setSystemWellFormedSetInstruction, setSystemWellFormedStep,
        setSystemWellFormedSetStep, graphBoolAndPair_eq_true_iff,
        setAllLtBool_eq_true_iff, and_assoc] using hTail

theorem setSystemWellFormedBool_eq_true_iff (S : SetSystemInput) :
    setSystemWellFormedBool S = true ↔ SetSystemWellFormed S := by
  cases S with
  | mk universeSize sets =>
      simpa [setSystemWellFormedBool, setSystemWellFormedFromInstructions,
        setSystemWellFormedInstructions, setSystemWellFormedInitInstruction,
        setSystemWellFormedStep, setSystemWellFormedInitAcc, SetSystemWellFormed]
        using setSystemWellFormedSetFold_eq_true_iff sets universeSize true

theorem exactCoverWellFormedBool_eq_true_iff (I : ExactCoverInput) :
    exactCoverWellFormedBool I = true ↔ SetSystemWellFormed I.system := by
  simpa [exactCoverWellFormedBool] using setSystemWellFormedBool_eq_true_iff I.system

theorem setSystemWellFormedInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setSystemWellFormedInstructionEncodedType
      setSystemWellFormedInitInstruction := by
  simpa [setSystemWellFormedInstructionEncodedType, setSystemWellFormedInitInstruction] using
    TMPolyTimeMap.inl EncodedType.nat setStructuredEncodedType

theorem setSystemWellFormedSetInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      setSystemWellFormedInstructionEncodedType
      setSystemWellFormedSetInstruction := by
  simpa [setSystemWellFormedInstructionEncodedType, setSystemWellFormedSetInstruction] using
    TMPolyTimeMap.inr EncodedType.nat setStructuredEncodedType

theorem setSystemWellFormedInstructions_tm_polytime :
    TMPolyTimeMap
      setSystemStructuredEncodedType
      setSystemWellFormedInstructionListEncodedType
      setSystemWellFormedInstructions := by
  let X := setSystemStructuredEncodedType
  have hTuple := HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun S : SetSystemInput => S.universeSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, HittingSet.setSystemInputToTuple, setSystemTupleStructuredEncodedType, X]
      using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun S : SetSystemInput => S.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, HittingSet.setSystemInputToTuple, setSystemTupleStructuredEncodedType, X]
      using hComp
  have hInit :
      TMPolyTimeMap X setSystemWellFormedInstructionEncodedType
        (fun S : SetSystemInput => setSystemWellFormedInitInstruction S.universeSize) := by
    have hComp := TMPolyTimeMap.comp setSystemWellFormedInitInstruction_tm_polytime hUniverse
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X setSystemWellFormedInstructionListEncodedType
        (fun S : SetSystemInput => S.sets.map setSystemWellFormedSetInstruction) := by
    have hMap := TMPolyTimeMap.list_map setSystemWellFormedSetInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSets
    simpa [Function.comp, setSystemWellFormedInstructionListEncodedType,
      setFamilyStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setSystemWellFormedInstructionEncodedType
          setSystemWellFormedInstructionListEncodedType)
        (fun S : SetSystemInput =>
          (setSystemWellFormedInitInstruction S.universeSize,
            S.sets.map setSystemWellFormedSetInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons setSystemWellFormedInstructionEncodedType) hConsInput
  simpa [Function.comp, setSystemWellFormedInstructions,
    setSystemWellFormedInstructionListEncodedType, X] using hCons

theorem setSystemWellFormedSetStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setSystemWellFormedAccEncodedType setStructuredEncodedType)
      setSystemWellFormedAccEncodedType
      setSystemWellFormedSetStep := by
  let X := EncodedType.prod setSystemWellFormedAccEncodedType setStructuredEncodedType
  have hAcc : TMPolyTimeMap X setSystemWellFormedAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setSystemWellFormedAccEncodedType setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setSystemWellFormedAccEncodedType setStructuredEncodedType
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setSystemWellFormedAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setSystemWellFormedAccEncodedType, X] using hComp
  have hSetCheckInput :
      TMPolyTimeMap X setAllLtInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBound hSet
  have hSetCheck : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => setAllLtBool (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp setAllLtBool_tm_polytime hSetCheckInput
    simpa [Function.comp, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, setAllLtBool (p.1.1, p.2))) :=
    TMPolyTimeMap.prod_mk hOk hSetCheck
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolAndPair (p.1.2, setAllLtBool (p.1.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hBound hAnd
  simpa [setSystemWellFormedSetStep, setSystemWellFormedAccEncodedType, X] using hOut

theorem setSystemWellFormedStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setSystemWellFormedAccEncodedType
      (fun bound : Nat => (bound, true)) := by
  have hBound := TMPolyTimeMap.id EncodedType.nat
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  simpa [setSystemWellFormedAccEncodedType] using TMPolyTimeMap.prod_mk hBound hTrue

theorem setSystemWellFormedStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setSystemWellFormedAccEncodedType
        setSystemWellFormedInstructionEncodedType)
      setSystemWellFormedAccEncodedType
      setSystemWellFormedStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setSystemWellFormedAccEncodedType EncodedType.nat setStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setSystemWellFormedStepLeft_tm_polytime
      setSystemWellFormedSetStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem setSystemWellFormedInitAcc_bound
    (xs : List setSystemWellFormedInstructionEncodedType.Carrier) :
    setSystemWellFormedAccEncodedType.inputSize setSystemWellFormedInitAcc ≤
      (Polynomial.C 5).eval (setSystemWellFormedInstructionListEncodedType.inputSize xs) := by
  simp [setSystemWellFormedInitAcc, setSystemWellFormedAccEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool]

theorem setSystemWellFormedStep_growth
    (source : List setSystemWellFormedInstructionEncodedType.Carrier)
    (acc : setSystemWellFormedAccEncodedType.Carrier)
    (instr : setSystemWellFormedInstructionEncodedType.Carrier)
    (hInstr :
      setSystemWellFormedInstructionEncodedType.inputSize instr ≤
        setSystemWellFormedInstructionListEncodedType.inputSize source) :
    setSystemWellFormedAccEncodedType.inputSize
        (setSystemWellFormedStep (acc, instr)) ≤
      setSystemWellFormedAccEncodedType.inputSize acc +
        (Polynomial.C 20 * Polynomial.X + Polynomial.C 50).eval
          (setSystemWellFormedInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bound, ok⟩
  cases instr with
  | inl newBound =>
      change Nat at newBound
      have hNew : newBound + 2 ≤
          setSystemWellFormedInstructionListEncodedType.inputSize source := by
        have hNewLt : newBound + 1 <
            setSystemWellFormedInstructionListEncodedType.inputSize source := by
          simpa [setSystemWellFormedInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      simp [setSystemWellFormedStep, setSystemWellFormedAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      omega
  | inr S =>
      simp [setSystemWellFormedStep, setSystemWellFormedSetStep,
        setSystemWellFormedAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X]

theorem setSystemWellFormedFold_tm_polytime :
    TMPolyTimeMap
      setSystemWellFormedInstructionListEncodedType
      setSystemWellFormedAccEncodedType
      (fun xs : List setSystemWellFormedInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setSystemWellFormedStep (acc, instr))
          setSystemWellFormedInitAcc) := by
  rcases setSystemWellFormedStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      setSystemWellFormedInstructionEncodedType setSystemWellFormedAccEncodedType
      setSystemWellFormedStep setSystemWellFormedInitAcc hStep
      (Polynomial.C 5) (Polynomial.C 20 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    exact setSystemWellFormedInitAcc_bound xs
  · intro source acc instr hInstr
    exact setSystemWellFormedStep_growth source acc instr hInstr

theorem setSystemWellFormedFromInstructions_tm_polytime :
    TMPolyTimeMap
      setSystemWellFormedInstructionListEncodedType
      EncodedType.bool
      setSystemWellFormedFromInstructions := by
  have hFold := setSystemWellFormedFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, setSystemWellFormedFromInstructions,
    setSystemWellFormedAccEncodedType] using hComp

theorem setSystemWellFormedBool_tm_polytime :
    TMPolyTimeMap
      setSystemStructuredEncodedType
      EncodedType.bool
      setSystemWellFormedBool := by
  have hComp := TMPolyTimeMap.comp setSystemWellFormedFromInstructions_tm_polytime
    setSystemWellFormedInstructions_tm_polytime
  simpa [Function.comp, setSystemWellFormedBool] using hComp

theorem exactCoverWellFormedBool_tm_polytime :
    TMPolyTimeMap
      exactCoverStructuredEncodedType
      EncodedType.bool
      exactCoverWellFormedBool := by
  have hComp := TMPolyTimeMap.comp setSystemWellFormedBool_tm_polytime
    exactCoverSystemTMBackedMap.tm_polytime
  simpa [Function.comp, exactCoverWellFormedBool] using hComp

end SteinerTree
end Karp21
end ComplexityReduction
