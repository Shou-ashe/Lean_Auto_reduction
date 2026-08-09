/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.Base

/-!
TM-backed source-set membership runner for the faithful structured Set Covering
to Hitting Set route.
-/

namespace ComplexityReduction
namespace Karp21
namespace HittingSet

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Source-set membership predicate -/

def setContainsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.nat

def setContainsInstructionListEncodedType : EncodedType :=
  EncodedType.list setContainsInstructionEncodedType

def setContainsInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def setContainsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

def setContainsInitInstruction (x : Nat) : Bool × Nat :=
  (false, x)

def setContainsElementInstruction (y : Nat) : Bool × Nat :=
  (true, y)

def setContainsInstructions (p : Nat × List Nat) : List (Bool × Nat) :=
  setContainsInitInstruction p.1 :: p.2.map setContainsElementInstruction

def setContainsRunnerInit : Nat × Bool :=
  (0, false)

def setContainsStep (p : (Nat × Bool) × (Bool × Nat)) : Nat × Bool :=
  if p.2.1 then
    (p.1.1, graphBoolOrPair (p.1.2, decide (p.2.2 = p.1.1)))
  else
    (p.2.2, false)

def setContainsFromInstructions (xs : List (Bool × Nat)) : Bool :=
  (xs.foldl (fun acc x => setContainsStep (acc, x)) setContainsRunnerInit).2

def setContainsBool (p : Nat × List Nat) : Bool :=
  setContainsFromInstructions (setContainsInstructions p)

theorem setContainsElementInstructions_fold_eq_true_iff
    (ys : List Nat) (x : Nat) (found : Bool) :
    ((ys.map setContainsElementInstruction).foldl
        (fun acc instr => setContainsStep (acc, instr)) (x, found)).2 = true ↔
      found = true ∨ x ∈ ys := by
  induction ys generalizing found with
  | nil =>
      simp
  | cons y ys ih =>
      rw [List.map_cons, List.foldl_cons]
      simp [setContainsElementInstruction, setContainsStep]
      change
        ((ys.map setContainsElementInstruction).foldl
            (fun acc instr => setContainsStep (acc, instr))
            (x, graphBoolOrPair (found, decide (y = x)))).2 = true ↔
          found = true ∨ x = y ∨ x ∈ ys
      rw [ih]
      by_cases hy : y = x
      · subst y
        cases found <;> simp [graphBoolOrPair_eq_true_iff]
      · have hxy : x ≠ y := Ne.symm hy
        cases found <;> simp [graphBoolOrPair_eq_true_iff, hy, hxy]

theorem setContainsBool_eq_true_iff (p : Nat × List Nat) :
    setContainsBool p = true ↔ p.1 ∈ p.2 := by
  rcases p with ⟨x, ys⟩
  change
    (((setContainsInitInstruction x :: ys.map setContainsElementInstruction).foldl
        (fun acc instr => setContainsStep (acc, instr)) setContainsRunnerInit).2 = true) ↔
      x ∈ ys
  rw [List.foldl_cons]
  simpa [setContainsRunnerInit, setContainsInitInstruction, setContainsStep] using
    setContainsElementInstructions_fold_eq_true_iff ys x false

theorem setContainsBool_eq_decide (p : Nat × List Nat) :
    setContainsBool p = decide (p.1 ∈ p.2) := by
  cases h : setContainsBool p
  · have hNot : ¬ p.1 ∈ p.2 := by
      intro hp
      have hTrue := (setContainsBool_eq_true_iff p).2 hp
      simp [h] at hTrue
    simp [hNot]
  · have hMem := (setContainsBool_eq_true_iff p).1 h
    simp [hMem]

theorem setContainsInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setContainsInstructionEncodedType
      setContainsInitInstruction := by
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hPayload : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [setContainsInitInstruction, setContainsInstructionEncodedType] using hOut

theorem setContainsElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setContainsInstructionEncodedType
      setContainsElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hPayload : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [setContainsElementInstruction, setContainsInstructionEncodedType] using hOut

theorem setContainsInstructions_tm_polytime :
    TMPolyTimeMap
      setContainsInstructionInputEncodedType
      setContainsInstructionListEncodedType
      setContainsInstructions := by
  let X := setContainsInstructionInputEncodedType
  have hNeedle : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, setContainsInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setContainsInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X setContainsInstructionEncodedType
        (fun p : X.Carrier => setContainsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp setContainsInitInstruction_tm_polytime hNeedle
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X setContainsInstructionListEncodedType
        (fun p : X.Carrier => [setContainsInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton setContainsInstructionEncodedType)
        hInit
    simpa [Function.comp, setContainsInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X setContainsInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setContainsElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map setContainsElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSet
    simpa [Function.comp, setContainsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setContainsInstructionListEncodedType
          setContainsInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([setContainsInitInstruction p.1],
            p.2.map setContainsElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append setContainsInstructionEncodedType)
      hAppendInput
  simpa [Function.comp, setContainsInstructions, setContainsInstructionListEncodedType, X]
    using hOut

theorem setContainsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setContainsAccEncodedType setContainsInstructionEncodedType)
      setContainsAccEncodedType
      setContainsStep := by
  classical
  let X := EncodedType.prod setContainsAccEncodedType setContainsInstructionEncodedType
  let A := setContainsAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setContainsAccEncodedType setContainsInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X setContainsInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setContainsAccEncodedType setContainsInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, setContainsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, setContainsInstructionEncodedType, X] using hComp
  have hNeedle : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setContainsAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setContainsAccEncodedType, X] using hComp
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayload hNeedle
  have hEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (Nat × Bool) × (Bool × Nat) => decide (p.2.2 = p.1.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp] using hComp
  have hOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : (Nat × Bool) × (Bool × Nat) => (p.1.2, decide (p.2.2 = p.1.1))) :=
    TMPolyTimeMap.prod_mk hFound hEq
  have hOr :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (Nat × Bool) × (Bool × Nat) =>
          graphBoolOrPair (p.1.2, decide (p.2.2 = p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
    simpa [Function.comp] using hComp
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : (Nat × Bool) × (Bool × Nat) =>
          (p.1.1, graphBoolOrPair (p.1.2, decide (p.2.2 = p.1.1)))) :=
    TMPolyTimeMap.prod_mk hNeedle hOr
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hFalseBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2, false)) :=
    TMPolyTimeMap.prod_mk hPayload hFalse
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × ((Nat × Bool) × (Bool × Nat)) =>
          match p.1 with
          | true =>
              (p.2.1.1, graphBoolOrPair (p.2.1.2, decide (p.2.2.2 = p.2.1.1)))
          | false => (p.2.2.2, false)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2, false))
      (fTrue := fun p : (Nat × Bool) × (Bool × Nat) =>
        (p.1.1, graphBoolOrPair (p.1.2, decide (p.2.2 = p.1.1))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨needle, found⟩, ⟨tag, payload⟩⟩
  cases tag <;> rfl

theorem setContainsStep_inputSize_le
    (source : setContainsInstructionListEncodedType.Carrier)
    (acc : setContainsAccEncodedType.Carrier)
    (instr : setContainsInstructionEncodedType.Carrier)
    (hAcc :
      setContainsAccEncodedType.inputSize acc ≤
        setContainsInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      setContainsInstructionEncodedType.inputSize instr ≤
        setContainsInstructionListEncodedType.inputSize source) :
    setContainsAccEncodedType.inputSize (setContainsStep (acc, instr)) ≤
      setContainsInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨needle, found⟩
  rcases instr with ⟨tag, payload⟩
  cases tag
  · have hLocal :
        setContainsAccEncodedType.inputSize (payload, false) ≤
          setContainsInstructionEncodedType.inputSize (false, payload) + 10 := by
      simp [setContainsAccEncodedType, setContainsInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
    exact
      (by
        simpa [setContainsStep] using
          hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        setContainsAccEncodedType.inputSize
            (setContainsStep ((needle, found), (true, payload))) ≤
          setContainsAccEncodedType.inputSize (needle, found) := by
      by_cases h : payload = needle <;>
        cases found <;>
          simp [setContainsStep, h, setContainsAccEncodedType, EncodedType.inputSize,
            EncodedType.prod, EncodedType.bool, EncodedType.nat]
    exact hLocal.trans hAcc

theorem setContainsFold_tm_polytime :
    TMPolyTimeMap
      setContainsInstructionListEncodedType
      setContainsAccEncodedType
      (fun xs : setContainsInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => setContainsStep (acc, x)) setContainsRunnerInit) := by
  rcases setContainsStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      setContainsInstructionEncodedType setContainsAccEncodedType
      setContainsStep setContainsRunnerInit hStep bound ?_ ?_
  · intro xs
    change setContainsAccEncodedType.inputSize setContainsRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (setContainsInstructionEncodedType.list.inputSize xs)
    have hInit : setContainsAccEncodedType.inputSize setContainsRunnerInit ≤ 10 := by
      simp [setContainsRunnerInit, setContainsAccEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (setContainsInstructionEncodedType.list.inputSize xs) =
          setContainsInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        setContainsAccEncodedType.inputSize acc ≤
          setContainsInstructionListEncodedType.inputSize source + 10 := by
      simpa [setContainsInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        setContainsInstructionEncodedType.inputSize instr ≤
          setContainsInstructionListEncodedType.inputSize source := by
      simpa [setContainsInstructionListEncodedType] using hInstr
    simpa [setContainsInstructionListEncodedType, bound, Polynomial.eval_add] using
      setContainsStep_inputSize_le source acc instr hAcc' hInstr'

theorem setContainsFromInstructions_tm_polytime :
    TMPolyTimeMap
      setContainsInstructionListEncodedType
      EncodedType.bool
      setContainsFromInstructions := by
  have hFold := setContainsFold_tm_polytime
  have hFound := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound hFold
  simpa [Function.comp, setContainsFromInstructions, setContainsAccEncodedType] using hComp

theorem setContainsBool_tm_polytime :
    TMPolyTimeMap
      setContainsInstructionInputEncodedType
      EncodedType.bool
      setContainsBool := by
  have hComp :=
    TMPolyTimeMap.comp setContainsFromInstructions_tm_polytime
      setContainsInstructions_tm_polytime
  simpa [Function.comp, setContainsBool] using hComp

noncomputable def setContainsBoolTMBackedMap :
    TMBackedCostedMap
      setContainsInstructionInputEncodedType
      EncodedType.bool
      setContainsBool where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      (PolynomialSizeBound.const 1 (by
        intro p
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime := setContainsBool_tm_polytime

end HittingSet
end Karp21
end ComplexityReduction
