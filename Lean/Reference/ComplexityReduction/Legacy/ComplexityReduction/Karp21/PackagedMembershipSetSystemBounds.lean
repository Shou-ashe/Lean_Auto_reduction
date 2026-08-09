/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import Mathlib.Tactic

/-!
Direct standard-TM Boolean runners for bounded unary natural certificates.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace HittingSet

def natLeBool (p : Nat × Nat) : Bool :=
  !natLtBool (p.2, p.1)

theorem natLeBool_eq_true_iff (p : Nat × Nat) :
    natLeBool p = true ↔ p.1 ≤ p.2 := by
  rcases p with ⟨a, b⟩
  simp [natLeBool, natLtBool]

theorem natLeBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      natLeBool := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSwap :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hLeft
  have hLt : TMPolyTimeMap X EncodedType.bool (fun p : Nat × Nat => natLtBool (p.2, p.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hSwap
    simpa [Function.comp, X] using hComp
  have hNot := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hLt
  simpa [Function.comp, natLeBool, X] using hNot

def boundedNatInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool EncodedType.nat

def boundedNatInstructionListEncodedType : EncodedType :=
  EncodedType.list boundedNatInstructionEncodedType

def boundedNatInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def boundedNatAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

def boundedNatInitInstruction (bound : Nat) : Bool × Nat :=
  (false, bound)

def boundedNatElementInstruction (x : Nat) : Bool × Nat :=
  (true, x)

def boundedNatInstructions (p : Nat × List Nat) : List (Bool × Nat) :=
  boundedNatInitInstruction p.1 :: p.2.map boundedNatElementInstruction

def boundedNatRunnerInit : Nat × Bool :=
  (0, true)

def boundedNatStep (p : (Nat × Bool) × (Bool × Nat)) : Nat × Bool :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, natLtBool (p.2.2, p.1.1)))
  else
    (p.2.2, true)

def boundedNatFromInstructions (xs : List (Bool × Nat)) : Bool :=
  (xs.foldl (fun acc x => boundedNatStep (acc, x)) boundedNatRunnerInit).2

def boundedNatListBool (p : Nat × List Nat) : Bool :=
  boundedNatFromInstructions (boundedNatInstructions p)

theorem boundedNatElementInstructions_fold_eq_true_iff
    (xs : List Nat) (bound : Nat) (ok : Bool) :
    ((xs.map boundedNatElementInstruction).foldl
        (fun acc instr => boundedNatStep (acc, instr)) (bound, ok)).2 = true ↔
      ok = true ∧ ∀ x ∈ xs, x < bound := by
  induction xs generalizing ok with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((xs.map boundedNatElementInstruction).foldl
            (fun acc instr => boundedNatStep (acc, instr))
            (bound, graphBoolAndPair (ok, natLtBool (x, bound)))).2 = true ↔
          ok = true ∧ (∀ y ∈ x :: xs, y < bound)
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, natLtBool (x, bound))).1 hHead with
          ⟨hok, hxBool⟩
        refine ⟨hok, ?_⟩
        intro y hy
        simp at hy
        rcases hy with hxy | hy
        · subst y
          exact (natLtBool_eq_true_iff (x, bound)).1 hxBool
        · exact hTail y hy
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff (ok, natLtBool (x, bound))).2
            ⟨hok, (natLtBool_eq_true_iff (x, bound)).2 (hAll x (by simp))⟩
        · intro y hy
          exact hAll y (List.mem_cons_of_mem x hy)

theorem boundedNatListBool_eq_true_iff (p : Nat × List Nat) :
    boundedNatListBool p = true ↔ ∀ x ∈ p.2, x < p.1 := by
  rcases p with ⟨bound, xs⟩
  change
    (((boundedNatInitInstruction bound :: xs.map boundedNatElementInstruction).foldl
        (fun acc instr => boundedNatStep (acc, instr)) boundedNatRunnerInit).2 = true) ↔
      ∀ x ∈ xs, x < bound
  rw [List.foldl_cons]
  simpa [boundedNatRunnerInit, boundedNatInitInstruction, boundedNatStep] using
    boundedNatElementInstructions_fold_eq_true_iff xs bound true

theorem boundedNatInitInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat boundedNatInstructionEncodedType boundedNatInitInstruction := by
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hPayload : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [boundedNatInitInstruction, boundedNatInstructionEncodedType] using hOut

theorem boundedNatElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat boundedNatInstructionEncodedType boundedNatElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hPayload : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [boundedNatElementInstruction, boundedNatInstructionEncodedType] using hOut

theorem boundedNatInstructions_tm_polytime :
    TMPolyTimeMap
      boundedNatInstructionInputEncodedType
      boundedNatInstructionListEncodedType
      boundedNatInstructions := by
  let X := boundedNatInstructionInputEncodedType
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, boundedNatInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hList : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, boundedNatInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X boundedNatInstructionEncodedType
        (fun p : X.Carrier => boundedNatInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp boundedNatInitInstruction_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X boundedNatInstructionListEncodedType
        (fun p : X.Carrier => [boundedNatInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton boundedNatInstructionEncodedType) hInit
    simpa [Function.comp, boundedNatInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X boundedNatInstructionListEncodedType
        (fun p : X.Carrier => p.2.map boundedNatElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map boundedNatElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hList
    simpa [Function.comp, boundedNatInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod boundedNatInstructionListEncodedType boundedNatInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([boundedNatInitInstruction p.1], p.2.map boundedNatElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append boundedNatInstructionEncodedType) hAppendInput
  simpa [Function.comp, boundedNatInstructions, boundedNatInstructionListEncodedType, X] using hOut

theorem boundedNatStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod boundedNatAccEncodedType boundedNatInstructionEncodedType)
      boundedNatAccEncodedType
      boundedNatStep := by
  let X := EncodedType.prod boundedNatAccEncodedType boundedNatInstructionEncodedType
  let A := boundedNatAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst boundedNatAccEncodedType boundedNatInstructionEncodedType
  have hInstr : TMPolyTimeMap X boundedNatInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd boundedNatAccEncodedType boundedNatInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, boundedNatInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, boundedNatInstructionEncodedType, X] using hComp
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, boundedNatAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, boundedNatAccEncodedType, X] using hComp
  have hLtInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayload hBound
  have hLt : TMPolyTimeMap X EncodedType.bool
      (fun p : (Nat × Bool) × (Bool × Nat) => natLtBool (p.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hLtInput
    simpa [Function.comp] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : (Nat × Bool) × (Bool × Nat) => (p.1.2, natLtBool (p.2.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hLt
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : (Nat × Bool) × (Bool × Nat) =>
        graphBoolAndPair (p.1.2, natLtBool (p.2.2, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : (Nat × Bool) × (Bool × Nat) =>
        (p.1.1, graphBoolAndPair (p.1.2, natLtBool (p.2.2, p.1.1)))) :=
    TMPolyTimeMap.prod_mk hBound hAnd
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2, true)) :=
    TMPolyTimeMap.prod_mk hPayload hTrueConst
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × ((Nat × Bool) × (Bool × Nat)) =>
          match p.1 with
          | true =>
              (p.2.1.1, graphBoolAndPair (p.2.1.2, natLtBool (p.2.2.2, p.2.1.1)))
          | false => (p.2.2.2, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2, true))
      (fTrue := fun p : (Nat × Bool) × (Bool × Nat) =>
        (p.1.1, graphBoolAndPair (p.1.2, natLtBool (p.2.2, p.1.1))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨bound, ok⟩, ⟨tag, payload⟩⟩
  cases tag <;> rfl

theorem boundedNatStep_inputSize_le
    (source : boundedNatInstructionListEncodedType.Carrier)
    (acc : boundedNatAccEncodedType.Carrier)
    (instr : boundedNatInstructionEncodedType.Carrier)
    (hAcc :
      boundedNatAccEncodedType.inputSize acc ≤
        boundedNatInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      boundedNatInstructionEncodedType.inputSize instr ≤
        boundedNatInstructionListEncodedType.inputSize source) :
    boundedNatAccEncodedType.inputSize (boundedNatStep (acc, instr)) ≤
      boundedNatInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨bound, ok⟩
  rcases instr with ⟨tag, payload⟩
  cases tag
  · have hLocal :
        boundedNatAccEncodedType.inputSize (payload, true) ≤
          boundedNatInstructionEncodedType.inputSize (false, payload) + 10 := by
      simp [boundedNatAccEncodedType, boundedNatInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
    exact (by
      simpa [boundedNatStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        boundedNatAccEncodedType.inputSize
            (boundedNatStep ((bound, ok), (true, payload))) ≤
          boundedNatAccEncodedType.inputSize (bound, ok) := by
      cases h : natLtBool (payload, bound) <;>
        cases ok <;>
          simp [boundedNatStep, h, boundedNatAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
    exact hLocal.trans hAcc

theorem boundedNatFold_tm_polytime :
    TMPolyTimeMap
      boundedNatInstructionListEncodedType
      boundedNatAccEncodedType
      (fun xs : boundedNatInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => boundedNatStep (acc, x)) boundedNatRunnerInit) := by
  rcases boundedNatStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      boundedNatInstructionEncodedType boundedNatAccEncodedType
      boundedNatStep boundedNatRunnerInit hStep bound ?_ ?_
  · intro xs
    change boundedNatAccEncodedType.inputSize boundedNatRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (boundedNatInstructionEncodedType.list.inputSize xs)
    have hInit : boundedNatAccEncodedType.inputSize boundedNatRunnerInit ≤ 10 := by
      simp [boundedNatRunnerInit, boundedNatAccEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (boundedNatInstructionEncodedType.list.inputSize xs) =
          boundedNatInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        boundedNatAccEncodedType.inputSize acc ≤
          boundedNatInstructionListEncodedType.inputSize source + 10 := by
      simpa [boundedNatInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        boundedNatInstructionEncodedType.inputSize instr ≤
          boundedNatInstructionListEncodedType.inputSize source := by
      simpa [boundedNatInstructionListEncodedType] using hInstr
    simpa [boundedNatInstructionListEncodedType, bound, Polynomial.eval_add] using
      boundedNatStep_inputSize_le source acc instr hAcc' hInstr'

theorem boundedNatFromInstructions_tm_polytime :
    TMPolyTimeMap boundedNatInstructionListEncodedType EncodedType.bool boundedNatFromInstructions := by
  have hFold := boundedNatFold_tm_polytime
  have hOk := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, boundedNatFromInstructions, boundedNatAccEncodedType] using hComp

theorem boundedNatListBool_tm_polytime :
    TMPolyTimeMap boundedNatInstructionInputEncodedType EncodedType.bool boundedNatListBool := by
  have hComp := TMPolyTimeMap.comp boundedNatFromInstructions_tm_polytime
    boundedNatInstructions_tm_polytime
  simpa [Function.comp, boundedNatListBool] using hComp

end HittingSet
end Karp21
end ComplexityReduction
