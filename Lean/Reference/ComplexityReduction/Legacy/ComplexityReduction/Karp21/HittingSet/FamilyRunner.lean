/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.IndexRunner

/-!
TM-backed dual-family runner for the faithful structured Set Covering to Hitting
Set route.
-/

namespace ComplexityReduction
namespace Karp21
namespace HittingSet

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### TM-facing dual-family instruction layer -/

def dualFamilyPayloadEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat

def dualFamilyInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool dualFamilyPayloadEncodedType

def dualFamilyInstructionListEncodedType : EncodedType :=
  EncodedType.list dualFamilyInstructionEncodedType

def dualFamilyInstructionInputEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat

def dualFamilyAccEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType

def dualFamilyStepInputEncodedType : EncodedType :=
  EncodedType.prod dualFamilyAccEncodedType dualFamilyInstructionEncodedType

def dualFamilyInitAcc : List (List Nat) × List (List Nat) :=
  (([] : List (List Nat)), ([] : List (List Nat)))

def dualFamilyInitInstruction (sets : List (List Nat)) :
    Bool × (List (List Nat) × Nat) :=
  (false, (sets, 0))

def dualFamilyElementInstruction (x : Nat) :
    Bool × (List (List Nat) × Nat) :=
  (true, (([] : List (List Nat)), x))

def dualFamilyInstructions (p : List (List Nat) × Nat) :
    List (Bool × (List (List Nat) × Nat)) :=
  dualFamilyInitInstruction p.1 ::
    (List.range p.2).map dualFamilyElementInstruction

def dualFamilyStep
    (p :
      (List (List Nat) × List (List Nat)) ×
        (Bool × (List (List Nat) × Nat))) :
    List (List Nat) × List (List Nat) :=
  if p.2.1 then
    let source := p.1.1
    let family := p.1.2
    let x := p.2.2.2
    (source, family ++ [setIndexIndicesFromFamily (x, source)])
  else
    (p.2.2.1, [])

def dualFamilyFromInstructions
    (xs : List (Bool × (List (List Nat) × Nat))) : List (List Nat) :=
  (xs.foldl (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc).2

def dualFamilyFromSetFamily (p : List (List Nat) × Nat) : List (List Nat) :=
  dualFamilyFromInstructions (dualFamilyInstructions p)

/-! ### Semantics -/

theorem dualFamilyElementInstructions_fold
    (source : List (List Nat)) (xs : List Nat) (out : List (List Nat)) :
    ((xs.map dualFamilyElementInstruction).foldl
        (fun acc instr => dualFamilyStep (acc, instr)) (source, out)) =
      (source, out ++ xs.map (fun x => setIndexIndicesFromFamily (x, source))) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      change
        ((xs.map dualFamilyElementInstruction).foldl
            (fun acc instr => dualFamilyStep (acc, instr))
            (source, out ++ [setIndexIndicesFromFamily (x, source)])) =
          (source,
            out ++ setIndexIndicesFromFamily (x, source) ::
              xs.map (fun x => setIndexIndicesFromFamily (x, source)))
      rw [ih (out ++ [setIndexIndicesFromFamily (x, source)])]
      simp [List.append_assoc]

theorem dualFamilyFromSetFamily_eq_map
    (sets : List (List Nat)) (universeSize : Nat) :
    dualFamilyFromSetFamily (sets, universeSize) =
      (List.range universeSize).map (fun x => setIndexIndicesFromFamily (x, sets)) := by
  change
    ((dualFamilyInitInstruction sets ::
        (List.range universeSize).map dualFamilyElementInstruction).foldl
        (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc).2 =
      (List.range universeSize).map (fun x => setIndexIndicesFromFamily (x, sets))
  rw [List.foldl_cons]
  simp [dualFamilyInitInstruction, dualFamilyStep]
  have h := dualFamilyElementInstructions_fold sets (List.range universeSize) []
  simpa using congrArg Prod.snd h

theorem dualFamilyFromSetFamily_eq_dualSystem_sets
    (I : SetCoveringInput) :
    dualFamilyFromSetFamily (I.system.sets, I.system.universeSize) =
      (dualSystem I).sets := by
  rw [dualFamilyFromSetFamily_eq_map]
  simp [dualSystem]
  intro x _hx
  exact setIndexIndicesFromFamily_eq_indicesContaining I x

/-! ### TM witnesses for the instruction layer and step -/

theorem dualFamilyInitInstruction_tm_polytime :
    TMPolyTimeMap
      setFamilyStructuredEncodedType
      dualFamilyInstructionEncodedType
      dualFamilyInitInstruction := by
  have hFalse :
      TMPolyTimeMap setFamilyStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const setFamilyStructuredEncodedType EncodedType.bool false
  have hSets :
      TMPolyTimeMap setFamilyStructuredEncodedType setFamilyStructuredEncodedType id :=
    TMPolyTimeMap.id setFamilyStructuredEncodedType
  have hZero :
      TMPolyTimeMap setFamilyStructuredEncodedType EncodedType.nat (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const setFamilyStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap setFamilyStructuredEncodedType dualFamilyPayloadEncodedType
        (fun sets : List (List Nat) => (sets, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hSets hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [dualFamilyInitInstruction, dualFamilyInstructionEncodedType,
    dualFamilyPayloadEncodedType] using hOut

theorem dualFamilyElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      dualFamilyInstructionEncodedType
      dualFamilyElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.nat setFamilyStructuredEncodedType
        (fun _ => ([] : List (List Nat))) :=
    TMPolyTimeMap.const EncodedType.nat setFamilyStructuredEncodedType []
  have hElement : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat dualFamilyPayloadEncodedType
        (fun x : Nat => (([] : List (List Nat)), x)) :=
    TMPolyTimeMap.prod_mk hEmpty hElement
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [dualFamilyElementInstruction, dualFamilyInstructionEncodedType,
    dualFamilyPayloadEncodedType] using hOut

theorem dualFamilyInstructions_tm_polytime :
    TMPolyTimeMap
      dualFamilyInstructionInputEncodedType
      dualFamilyInstructionListEncodedType
      dualFamilyInstructions := by
  let X := dualFamilyInstructionInputEncodedType
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, dualFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.fst setFamilyStructuredEncodedType EncodedType.nat
  have hUniverseSize : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, dualFamilyInstructionInputEncodedType] using
      TMPolyTimeMap.snd setFamilyStructuredEncodedType EncodedType.nat
  have hInit :
      TMPolyTimeMap X dualFamilyInstructionEncodedType
        (fun p : X.Carrier => dualFamilyInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp dualFamilyInitInstruction_tm_polytime hSets
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverseSize
    simpa [Function.comp, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X dualFamilyInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.2).map dualFamilyElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map dualFamilyElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, dualFamilyInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dualFamilyInstructionEncodedType
          dualFamilyInstructionListEncodedType)
        (fun p : X.Carrier =>
          (dualFamilyInitInstruction p.1,
            (List.range p.2).map dualFamilyElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hElementInstructions
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons dualFamilyInstructionEncodedType) hConsInput
  simpa [Function.comp, dualFamilyInstructions, dualFamilyInstructionListEncodedType, X]
    using hOut

theorem dualFamilyStep_tm_polytime :
    TMPolyTimeMap
      dualFamilyStepInputEncodedType
      dualFamilyAccEncodedType
      dualFamilyStep := by
  let X := dualFamilyStepInputEncodedType
  let A := dualFamilyAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, dualFamilyStepInputEncodedType] using
      TMPolyTimeMap.fst dualFamilyAccEncodedType dualFamilyInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X dualFamilyInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dualFamilyStepInputEncodedType] using
      TMPolyTimeMap.snd dualFamilyAccEncodedType dualFamilyInstructionEncodedType
  have hSource : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, dualFamilyAccEncodedType, X] using hComp
  have hFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, dualFamilyAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool dualFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, dualFamilyInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X dualFamilyPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool dualFamilyPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, dualFamilyInstructionEncodedType, X] using hComp
  have hInitSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, dualFamilyPayloadEncodedType, X] using hComp
  have hElement :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, dualFamilyPayloadEncodedType, X] using hComp
  have hEmptyFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun _ => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X setFamilyStructuredEncodedType []
  have hInitBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat)))) :=
    TMPolyTimeMap.prod_mk hInitSets hEmptyFamily
  have hIndexInput :
      TMPolyTimeMap X setIndexInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hElement hSource
  have hIndex :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => setIndexIndicesFromFamily (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setIndexIndicesFromFamily_tm_polytime hIndexInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hIndexSingleton :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => [setIndexIndicesFromFamily (p.2.2.2, p.1.1)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton setStructuredEncodedType)
      hIndex
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List (List Nat) from p.1.2),
            [setIndexIndicesFromFamily (p.2.2.2, p.1.1)])) :=
    TMPolyTimeMap.prod_mk hFamily hIndexSingleton
  have hAppendFamily :
      TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier =>
          List.append (show List (List Nat) from p.1.2)
            [setIndexIndicesFromFamily (p.2.2.2, p.1.1)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append setStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hElementBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1, List.append (show List (List Nat) from p.1.2)
            [setIndexIndicesFromFamily (p.2.2.2, p.1.1)])) :=
    TMPolyTimeMap.prod_mk hSource hAppendFamily
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                List.append (show List (List Nat) from p.2.1.2)
                  [setIndexIndicesFromFamily (p.2.2.2.2, p.2.1.1)])
          | false => (p.2.2.2.1, ([] : List (List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List (List Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, List.append (show List (List Nat) from p.1.2)
          [setIndexIndicesFromFamily (p.2.2.2, p.1.1)]))
      hInitBranch hElementBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨sets, family⟩, ⟨tag, initSets, x⟩⟩
  cases tag <;> rfl

/-! ### Reachable fold bounds and family runner -/

noncomputable def dualFamilySetBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 50

@[simp] theorem dualFamilySetBoundPolynomial_eval (N : Nat) :
    dualFamilySetBoundPolynomial.eval N = 20 * (N * N) + 50 := by
  simp [dualFamilySetBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def dualFamilyFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X * Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem dualFamilyFoldAccBoundPolynomial_eval (N : Nat) :
    dualFamilyFoldAccBoundPolynomial.eval N = 100 * (N * N * N) + 100 := by
  simp [dualFamilyFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def dualFamilyAccBound
    (N processed : Nat) (acc : List (List Nat) × List (List Nat)) : Prop :=
  setFamilyStructuredEncodedType.inputSize acc.1 ≤ N ∧
    (∀ S ∈ acc.2, setStructuredEncodedType.inputSize S ≤
      dualFamilySetBoundPolynomial.eval N) ∧
      acc.2.length ≤ processed

theorem dualFamilyInstruction_payload_sets_inputSize_le
    {N : Nat} {instr : dualFamilyInstructionEncodedType.Carrier}
    (hInstr : dualFamilyInstructionEncodedType.inputSize instr ≤ N) :
    setFamilyStructuredEncodedType.inputSize instr.2.1 ≤ N := by
  rcases instr with ⟨tag, sets, x⟩
  change setFamilyStructuredEncodedType.inputSize sets ≤ N
  simp [dualFamilyInstructionEncodedType, dualFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool] at hInstr
  omega

theorem dualFamilyInstruction_element_inputSize_le
    {N : Nat} {instr : dualFamilyInstructionEncodedType.Carrier}
    (hInstr : dualFamilyInstructionEncodedType.inputSize instr ≤ N) :
    EncodedType.nat.inputSize instr.2.2 ≤ N := by
  rcases instr with ⟨tag, sets, x⟩
  simp [dualFamilyInstructionEncodedType, dualFamilyPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr ⊢
  omega

theorem dualFamilyIndexSet_inputSize_le
    {N : Nat} {sets : List (List Nat)} {x : Nat}
    (hSets : setFamilyStructuredEncodedType.inputSize sets ≤ N)
    (hElement : EncodedType.nat.inputSize x ≤ N) :
    setStructuredEncodedType.inputSize (setIndexIndicesFromFamily (x, sets)) ≤
      dualFamilySetBoundPolynomial.eval N := by
  have hPair :
      setIndexInstructionInputEncodedType.inputSize (x, sets) ≤ 2 * N + 1 := by
    have hElementNat : x + 1 ≤ N := by
      simpa [EncodedType.inputSize_nat] using hElement
    simp [setIndexInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hBase := setIndexIndicesFromFamily_inputSize_le (x, sets)
  have hPow :
      setIndexInstructionInputEncodedType.inputSize (x, sets) ^ 2 ≤
        (2 * N + 1) ^ 2 :=
    Nat.pow_le_pow_left hPair 2
  calc
    setStructuredEncodedType.inputSize (setIndexIndicesFromFamily (x, sets))
        ≤ 3 * setIndexInstructionInputEncodedType.inputSize (x, sets) ^ 2 + 10 := by
          simpa [setStructuredEncodedType] using hBase
    _ ≤ 3 * (2 * N + 1) ^ 2 + 10 := by
          nlinarith
    _ ≤ dualFamilySetBoundPolynomial.eval N := by
          simp [dualFamilySetBoundPolynomial_eval]
          nlinarith [sq_nonneg (N : Int)]

theorem dualFamilyStep_bound {N processed : Nat}
    {acc : dualFamilyAccEncodedType.Carrier}
    {instr : dualFamilyInstructionEncodedType.Carrier}
    (hAcc : dualFamilyAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : dualFamilyInstructionEncodedType.inputSize instr ≤ N) :
    dualFamilyAccBound N (processed + 1) (dualFamilyStep (acc, instr)) := by
  rcases acc with ⟨sets, family⟩
  rcases instr with ⟨tag, initSets, x⟩
  rcases hAcc with ⟨hSets, hFamilyMem, hFamilyLen⟩
  cases tag
  · have hInitSets :
        setFamilyStructuredEncodedType.inputSize initSets ≤ N :=
      dualFamilyInstruction_payload_sets_inputSize_le
        (N := N) (instr := (false, (initSets, x))) hInstr
    simp [dualFamilyStep, dualFamilyAccBound]
    exact hInitSets
  · have hElement :
        EncodedType.nat.inputSize x ≤ N :=
      dualFamilyInstruction_element_inputSize_le
        (N := N) (instr := (true, (initSets, x))) hInstr
    have hIndex :=
      dualFamilyIndexSet_inputSize_le (N := N) (sets := sets) (x := x)
        hSets hElement
    simp [dualFamilyStep, dualFamilyAccBound]
    refine ⟨hSets, ?_, by simp [hFamilyLen]⟩
    intro S hS
    rcases hS with hOld | hNew
    · simpa using hFamilyMem S hOld
    · have hEq : S = setIndexIndicesFromFamily (x, sets) := by
        simpa using hNew
      simpa [hEq] using hIndex

theorem dualFamilyFold_bound_aux
    {N processed : Nat}
    (xs : List dualFamilyInstructionEncodedType.Carrier)
    (acc : dualFamilyAccEncodedType.Carrier)
    (hAcc : dualFamilyAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, dualFamilyInstructionEncodedType.inputSize instr ≤ N) :
    dualFamilyAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => dualFamilyStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : dualFamilyInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := dualFamilyStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, dualFamilyInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1) (acc := dualFamilyStep (acc, x))
          hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem dualFamilyFold_bound_of_inputSize_le
    {N : Nat} (xs : List dualFamilyInstructionEncodedType.Carrier)
    (hSize : dualFamilyInstructionListEncodedType.inputSize xs ≤ N) :
    dualFamilyAccBound N xs.length
      (xs.foldl (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc) := by
  have hInit : dualFamilyAccBound N 0 dualFamilyInitAcc := by
    have hEmptySets : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 :=
      rfl
    simp [dualFamilyAccBound, dualFamilyInitAcc, hEmptySets]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      SetCovering.incidentEncodedList_length_le_inputSize dualFamilyInstructionEncodedType xs
    have hLenInput' : xs.length ≤ dualFamilyInstructionListEncodedType.inputSize xs := by
      simpa [dualFamilyInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, dualFamilyInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      SetCovering.incidentEncodedList_element_inputSize_le
        (X := dualFamilyInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : dualFamilyInstructionEncodedType.inputSize instr ≤
        dualFamilyInstructionListEncodedType.inputSize xs := by
      simpa [dualFamilyInstructionListEncodedType] using hElem
    omega
  have h :=
    dualFamilyFold_bound_aux (N := N) (processed := 0) xs dualFamilyInitAcc
      hInit hLen hInstr
  simpa using h

theorem dualFamilyAccBound_inputSize_le {N processed : Nat}
    {acc : dualFamilyAccEncodedType.Carrier}
    (hAcc : dualFamilyAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    dualFamilyAccEncodedType.inputSize acc ≤
      dualFamilyFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨sets, family⟩
  rcases hAcc with ⟨hSets, hFamilyMem, hFamilyLen⟩
  let Bset := dualFamilySetBoundPolynomial.eval N
  have hFamilySize :
      setFamilyStructuredEncodedType.inputSize family ≤ processed * (Bset + 1) := by
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        setStructuredEncodedType family Bset (by
          intro S hS
          exact hFamilyMem S hS)
    exact hList.trans (Nat.mul_le_mul_right (Bset + 1) hFamilyLen)
  have hFamilySizeN :
      setFamilyStructuredEncodedType.inputSize family ≤ N * (Bset + 1) :=
    hFamilySize.trans (Nat.mul_le_mul_right (Bset + 1) hProcessed)
  simp [dualFamilyAccEncodedType, EncodedType.inputSize_prod]
  have hBset : Bset = 20 * (N * N) + 50 := by
    simp [Bset]
  nlinarith [sq_nonneg (N : Int), hSets, hFamilySizeN]

noncomputable def dualFamilyFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod dualFamilyAccEncodedType
          dualFamilyInstructionEncodedType).encode
        dualFamilyAccEncodedType.encode
        dualFamilyStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm dualFamilyFoldAccBoundPolynomial
    (hStep.time.comp
      (dualFamilyFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem dualFamilyFold_tm_polytime :
    TMPolyTimeMap
      dualFamilyInstructionListEncodedType
      dualFamilyAccEncodedType
      (fun xs : List dualFamilyInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc) := by
  rcases dualFamilyStep_tm_polytime with ⟨hStep⟩
  let time := dualFamilyFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      dualFamilyInstructionEncodedType dualFamilyAccEncodedType
      dualFamilyStep dualFamilyInitAcc hStep time ?_
  intro source
  let N := dualFamilyInstructionListEncodedType.inputSize source
  let B := dualFamilyFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List dualFamilyInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              dualFamilyInstructionEncodedType dualFamilyAccEncodedType
              dualFamilyStep hStep
              (pref.foldl (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc)
              rest ≤
            C * (EncodedType.list dualFamilyInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          simp
        have hxN : dualFamilyInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            SetCovering.incidentEncodedList_element_inputSize_le
              (X := dualFamilyInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, dualFamilyInstructionListEncodedType] using hElem
        have hPrefixSize : dualFamilyInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              dualFamilyInstructionListEncodedType.inputSize source =
                dualFamilyInstructionListEncodedType.inputSize pref +
                  dualFamilyInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact SetCovering.incidentEncodedList_inputSize_append dualFamilyInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          dualFamilyFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            SetCovering.incidentEncodedList_length_le_inputSize dualFamilyInstructionEncodedType pref
          have hLen' :
              pref.length ≤ dualFamilyInstructionListEncodedType.inputSize pref := by
            simpa [dualFamilyInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            dualFamilyAccEncodedType.inputSize
                (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                  dualFamilyInitAcc) ≤ B := by
          simpa [B] using
            dualFamilyAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          have hSourceLenN : source.length ≤ N := by
            have hLen :=
              SetCovering.incidentEncodedList_length_le_inputSize dualFamilyInstructionEncodedType source
            simpa [N, dualFamilyInstructionListEncodedType] using hLen
          omega
        have hStepBound :=
          dualFamilyStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            dualFamilyAccEncodedType.inputSize
                (dualFamilyStep
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x)) ≤ B := by
          simpa [B] using
            dualFamilyAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod dualFamilyAccEncodedType
                  dualFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod dualFamilyAccEncodedType
                dualFamilyInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              dualFamilyAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                      dualFamilyInitAcc) +
                  1 + dualFamilyInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (dualFamilyInstructionEncodedType.encode x).length
                (dualFamilyAccEncodedType.encode
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc)).length
                (dualFamilyAccEncodedType.encode
                  (dualFamilyStep
                    (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                      dualFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod dualFamilyAccEncodedType
                    dualFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                      dualFamilyInitAcc, x))) ≤
              C * (dualFamilyInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [x]) ++ xs := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [x]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                dualFamilyInstructionEncodedType dualFamilyAccEncodedType
                dualFamilyStep hStep
                (dualFamilyStep
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x)) xs ≤
              C * (EncodedType.list dualFamilyInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc =
                dualFamilyStep
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                dualFamilyInstructionEncodedType dualFamilyAccEncodedType
                dualFamilyStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              dualFamilyInstructionEncodedType dualFamilyAccEncodedType
              dualFamilyStep hStep
              (pref.foldl (fun acc instr => dualFamilyStep (acc, instr)) dualFamilyInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                dualFamilyInstructionEncodedType dualFamilyAccEncodedType
                dualFamilyStep hStep
                (dualFamilyStep
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (dualFamilyInstructionEncodedType.encode x).length
                (dualFamilyAccEncodedType.encode
                  (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                    dualFamilyInitAcc)).length
                (dualFamilyAccEncodedType.encode
                  (dualFamilyStep
                    (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                      dualFamilyInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod dualFamilyAccEncodedType
                    dualFamilyInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dualFamilyStep (acc, instr))
                      dualFamilyInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list dualFamilyInstructionEncodedType).inputSize xs +
                C * (dualFamilyInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list dualFamilyInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          dualFamilyInstructionEncodedType dualFamilyAccEncodedType
          dualFamilyStep hStep dualFamilyInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, dualFamilyInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, dualFamilyFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        dualFamilyInstructionEncodedType dualFamilyAccEncodedType
        dualFamilyStep hStep dualFamilyInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem dualFamilyFromInstructions_tm_polytime :
    TMPolyTimeMap
      dualFamilyInstructionListEncodedType
      setFamilyStructuredEncodedType
      dualFamilyFromInstructions := by
  have hFold := dualFamilyFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType setFamilyStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, dualFamilyFromInstructions, dualFamilyAccEncodedType]
    using hComp

theorem dualFamilyFromSetFamily_tm_polytime :
    TMPolyTimeMap
      dualFamilyInstructionInputEncodedType
      setFamilyStructuredEncodedType
      dualFamilyFromSetFamily := by
  have hComp :=
    TMPolyTimeMap.comp dualFamilyFromInstructions_tm_polytime
      dualFamilyInstructions_tm_polytime
  simpa [Function.comp, dualFamilyFromSetFamily] using hComp

theorem dualFamilyFromSetFamily_inputSize_le
    (p : dualFamilyInstructionInputEncodedType.Carrier) :
    setFamilyStructuredEncodedType.inputSize (dualFamilyFromSetFamily p) ≤
      1000 * dualFamilyInstructionInputEncodedType.inputSize p ^ 3 + 1000 := by
  rcases p with ⟨sets, universeSize⟩
  change Nat at universeSize
  let N := dualFamilyInstructionInputEncodedType.inputSize (sets, universeSize)
  change setFamilyStructuredEncodedType.inputSize
      (dualFamilyFromSetFamily (sets, universeSize)) ≤ 1000 * N ^ 3 + 1000
  have hSetsSize : setFamilyStructuredEncodedType.inputSize sets ≤ N := by
    unfold N
    simp [dualFamilyInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hUniverseSize : universeSize ≤ N := by
    unfold N
    simp [dualFamilyInstructionInputEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat]
    omega
  have hSetMem :
      ∀ S ∈ dualFamilyFromSetFamily (sets, universeSize),
        setStructuredEncodedType.inputSize S ≤ dualFamilySetBoundPolynomial.eval N := by
    intro S hS
    rw [dualFamilyFromSetFamily_eq_map] at hS
    rcases List.mem_map.mp hS with ⟨x, hx, rfl⟩
    have hxLt : x < universeSize := by
      simpa using List.mem_range.mp hx
    have hElementSize : EncodedType.nat.inputSize x ≤ N := by
      simp [EncodedType.inputSize_nat]
      omega
    exact dualFamilyIndexSet_inputSize_le (N := N) hSetsSize hElementSize
  have hFamilyList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (dualFamilyFromSetFamily (sets, universeSize))
      (dualFamilySetBoundPolynomial.eval N) hSetMem
  have hLen : (dualFamilyFromSetFamily (sets, universeSize)).length = universeSize := by
    rw [dualFamilyFromSetFamily_eq_map]
    simp
  have hSizeN :
      setFamilyStructuredEncodedType.inputSize (dualFamilyFromSetFamily (sets, universeSize)) ≤
        N * (dualFamilySetBoundPolynomial.eval N + 1) := by
    have hLenLe : (dualFamilyFromSetFamily (sets, universeSize)).length ≤ N := by
      omega
    exact hFamilyList.trans
      (Nat.mul_le_mul_right (dualFamilySetBoundPolynomial.eval N + 1) hLenLe)
  have hPoly :
      N * (dualFamilySetBoundPolynomial.eval N + 1) ≤ 1000 * N ^ 3 + 1000 := by
    by_cases hZero : N = 0
    · simp [hZero, dualFamilySetBoundPolynomial_eval]
    · have hPos : 1 ≤ N := by omega
      simp [dualFamilySetBoundPolynomial_eval]
      nlinarith [sq_nonneg (N : Int), hPos]
  exact hSizeN.trans hPoly

theorem dualFamilyFromSetFamily_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : dualFamilyInstructionInputEncodedType.Carrier =>
        dualFamilyInstructionInputEncodedType.inputSize p)
      (fun xs : List (List Nat) => setFamilyStructuredEncodedType.inputSize xs)
      dualFamilyFromSetFamily :=
  PolynomialSizeBound.intro_with 3 1000 1000 dualFamilyFromSetFamily_inputSize_le

noncomputable def dualFamilyFromSetFamilyTMBackedMap :
    TMBackedCostedMap
      dualFamilyInstructionInputEncodedType
      setFamilyStructuredEncodedType
      dualFamilyFromSetFamily where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      dualFamilyFromSetFamily_polynomialSizeBound
  tm_polytime := dualFamilyFromSetFamily_tm_polytime

end HittingSet
end Karp21
end ComplexityReduction
