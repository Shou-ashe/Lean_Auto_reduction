/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witnesses for Karp21 set-system targets.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace HittingSet

/-! ### One source set hit by a certificate list -/

def setHitInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod setStructuredEncodedType EncodedType.nat)

def setHitInstructionListEncodedType : EncodedType :=
  EncodedType.list setHitInstructionEncodedType

def setHitInstructionInputEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

def setHitAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.bool

def setHitInitInstruction (S : List Nat) : Bool × (List Nat × Nat) :=
  (false, (S, 0))

def setHitElementInstruction (x : Nat) : Bool × (List Nat × Nat) :=
  (true, ([], x))

def setHitInstructions (p : List Nat × List Nat) : List (Bool × (List Nat × Nat)) :=
  setHitInitInstruction p.1 :: p.2.map setHitElementInstruction

def setHitRunnerInit : List Nat × Bool :=
  ([], false)

def setHitStep (p : (List Nat × Bool) × (Bool × (List Nat × Nat))) : List Nat × Bool :=
  if p.2.1 then
    (p.1.1, graphBoolOrPair (p.1.2, setContainsBool (p.2.2.2, p.1.1)))
  else
    (p.2.2.1, false)

def setHitFromInstructions (xs : List (Bool × (List Nat × Nat))) : Bool :=
  (xs.foldl (fun acc x => setHitStep (acc, x)) setHitRunnerInit).2

def setHitBool (p : List Nat × List Nat) : Bool :=
  setHitFromInstructions (setHitInstructions p)

theorem setHitElementInstructions_fold_eq_true_iff
    (hitting : List Nat) (S : List Nat) (found : Bool) :
    ((hitting.map setHitElementInstruction).foldl
        (fun acc instr => setHitStep (acc, instr)) (S, found)).2 = true ↔
      found = true ∨ ∃ x ∈ hitting, x ∈ S := by
  induction hitting generalizing found with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((xs.map setHitElementInstruction).foldl
            (fun acc instr => setHitStep (acc, instr))
            (S, graphBoolOrPair (found, setContainsBool (x, S)))).2 = true ↔
          found = true ∨ ∃ y ∈ x :: xs, y ∈ S
      rw [ih]
      constructor
      · intro h
        rcases h with hHead | hTail
        · rcases (graphBoolOrPair_eq_true_iff (found, setContainsBool (x, S))).1 hHead with
            hFound | hxBool
          · exact Or.inl hFound
          · exact Or.inr ⟨x, by simp, (setContainsBool_eq_true_iff (x, S)).1 hxBool⟩
        · rcases hTail with ⟨y, hy, hys⟩
          exact Or.inr ⟨y, List.mem_cons_of_mem x hy, hys⟩
      · intro h
        rcases h with hFound | hWitness
        · exact Or.inl
            ((graphBoolOrPair_eq_true_iff (found, setContainsBool (x, S))).2
              (Or.inl hFound))
        · rcases hWitness with ⟨y, hy, hyS⟩
          simp at hy
          rcases hy with hxy | hy
          · subst y
            exact Or.inl
              ((graphBoolOrPair_eq_true_iff (found, setContainsBool (x, S))).2
                (Or.inr ((setContainsBool_eq_true_iff (x, S)).2 hyS)))
          · exact Or.inr ⟨y, hy, hyS⟩

theorem setHitBool_eq_true_iff (p : List Nat × List Nat) :
    setHitBool p = true ↔ ∃ x ∈ p.2, x ∈ p.1 := by
  rcases p with ⟨S, hitting⟩
  change
    (((setHitInitInstruction S :: hitting.map setHitElementInstruction).foldl
        (fun acc instr => setHitStep (acc, instr)) setHitRunnerInit).2 = true) ↔
      ∃ x ∈ hitting, x ∈ S
  rw [List.foldl_cons]
  simpa [setHitRunnerInit, setHitInitInstruction, setHitStep] using
    setHitElementInstructions_fold_eq_true_iff hitting S false

theorem setHitInitInstruction_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType setHitInstructionEncodedType setHitInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hSet : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hZero : TMPolyTimeMap setStructuredEncodedType EncodedType.nat (fun _ => (0 : Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap setStructuredEncodedType
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun S : List Nat => (S, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hSet hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [setHitInitInstruction, setHitInstructionEncodedType] using hOut

theorem setHitElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat setHitInstructionEncodedType setHitElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty :
      TMPolyTimeMap EncodedType.nat setStructuredEncodedType (fun _ => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hNat : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun x : Nat => (([] : List Nat), x)) :=
    TMPolyTimeMap.prod_mk hEmpty hNat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [setHitElementInstruction, setHitInstructionEncodedType] using hOut

theorem setHitInstructions_tm_polytime :
    TMPolyTimeMap
      setHitInstructionInputEncodedType
      setHitInstructionListEncodedType
      setHitInstructions := by
  let X := setHitInstructionInputEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, setHitInstructionInputEncodedType] using
      TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
  have hHitting : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setHitInstructionInputEncodedType] using
      TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X setHitInstructionEncodedType
        (fun p : X.Carrier => setHitInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp setHitInitInstruction_tm_polytime hSet
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X setHitInstructionListEncodedType
        (fun p : X.Carrier => [setHitInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton setHitInstructionEncodedType) hInit
    simpa [Function.comp, setHitInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X setHitInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setHitElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map setHitElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hHitting
    simpa [Function.comp, setHitInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setHitInstructionListEncodedType setHitInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([setHitInitInstruction p.1], p.2.map setHitElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append setHitInstructionEncodedType) hAppendInput
  simpa [Function.comp, setHitInstructions, setHitInstructionListEncodedType, X] using hOut

theorem setHitStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setHitAccEncodedType setHitInstructionEncodedType)
      setHitAccEncodedType
      setHitStep := by
  let X := EncodedType.prod setHitAccEncodedType setHitInstructionEncodedType
  let A := setHitAccEncodedType
  let Payload := EncodedType.prod setStructuredEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setHitAccEncodedType setHitInstructionEncodedType
  have hInstr : TMPolyTimeMap X setHitInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setHitAccEncodedType setHitInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, setHitInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, setHitInstructionEncodedType, Payload, X] using hComp
  have hAccSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setHitAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setHitAccEncodedType, X] using hComp
  have hPayloadSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadNat : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hContainsInput :
      TMPolyTimeMap X setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayloadNat hAccSet
  have hContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (List Nat × Bool) × (Bool × (List Nat × Nat)) =>
          setContainsBool (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, setContainsInstructionInputEncodedType] using hComp
  have hOrInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : (List Nat × Bool) × (Bool × (List Nat × Nat)) =>
          (p.1.2, setContainsBool (p.2.2.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hFound hContains
  have hOr :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (List Nat × Bool) × (Bool × (List Nat × Nat)) =>
          graphBoolOrPair (p.1.2, setContainsBool (p.2.2.2, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
    simpa [Function.comp] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : (List Nat × Bool) × (Bool × (List Nat × Nat)) =>
        (p.1.1, graphBoolOrPair (p.1.2, setContainsBool (p.2.2.2, p.1.1)))) :=
    TMPolyTimeMap.prod_mk hAccSet hOr
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, false)) :=
    TMPolyTimeMap.prod_mk hPayloadSet hFalse
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × ((List Nat × Bool) × (Bool × (List Nat × Nat))) =>
          match p.1 with
          | true =>
              (p.2.1.1,
                graphBoolOrPair (p.2.1.2, setContainsBool (p.2.2.2.2, p.2.1.1)))
          | false => (p.2.2.2.1, false)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, false))
      (fTrue := fun p : (List Nat × Bool) × (Bool × (List Nat × Nat)) =>
        (p.1.1, graphBoolOrPair (p.1.2, setContainsBool (p.2.2.2, p.1.1))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨S, found⟩, ⟨tag, payloadSet, payloadNat⟩⟩
  cases tag <;> rfl

theorem setHitStep_inputSize_le
    (source : setHitInstructionListEncodedType.Carrier)
    (acc : setHitAccEncodedType.Carrier)
    (instr : setHitInstructionEncodedType.Carrier)
    (hAcc :
      setHitAccEncodedType.inputSize acc ≤
        setHitInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      setHitInstructionEncodedType.inputSize instr ≤
        setHitInstructionListEncodedType.inputSize source) :
    setHitAccEncodedType.inputSize (setHitStep (acc, instr)) ≤
      setHitInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨S, found⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadSet, payloadNat⟩
  cases tag
  · have hLocal :
        setHitAccEncodedType.inputSize (payloadSet, false) ≤
          setHitInstructionEncodedType.inputSize (false, (payloadSet, payloadNat)) + 10 := by
      simp [setHitAccEncodedType, setHitInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool, EncodedType.nat]
      omega
    exact (by simpa [setHitStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        setHitAccEncodedType.inputSize
            (setHitStep ((S, found), (true, (payloadSet, payloadNat)))) ≤
          setHitAccEncodedType.inputSize (S, found) := by
      cases h : setContainsBool (payloadNat, S) <;>
        cases found <;>
          simp [setHitStep, h, setHitAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem setHitFold_tm_polytime :
    TMPolyTimeMap
      setHitInstructionListEncodedType
      setHitAccEncodedType
      (fun xs : setHitInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => setHitStep (acc, x)) setHitRunnerInit) := by
  rcases setHitStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      setHitInstructionEncodedType setHitAccEncodedType
      setHitStep setHitRunnerInit hStep bound ?_ ?_
  · intro xs
    change setHitAccEncodedType.inputSize setHitRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (setHitInstructionEncodedType.list.inputSize xs)
    have hInit : setHitAccEncodedType.inputSize setHitRunnerInit ≤ 10 := by
      native_decide
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (setHitInstructionEncodedType.list.inputSize xs) =
          setHitInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        setHitAccEncodedType.inputSize acc ≤
          setHitInstructionListEncodedType.inputSize source + 10 := by
      simpa [setHitInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        setHitInstructionEncodedType.inputSize instr ≤
          setHitInstructionListEncodedType.inputSize source := by
      simpa [setHitInstructionListEncodedType] using hInstr
    simpa [setHitInstructionListEncodedType, bound, Polynomial.eval_add] using
      setHitStep_inputSize_le source acc instr hAcc' hInstr'

theorem setHitFromInstructions_tm_polytime :
    TMPolyTimeMap setHitInstructionListEncodedType EncodedType.bool setHitFromInstructions := by
  have hFold := setHitFold_tm_polytime
  have hFound := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound hFold
  simpa [Function.comp, setHitFromInstructions, setHitAccEncodedType] using hComp

theorem setHitBool_tm_polytime :
    TMPolyTimeMap setHitInstructionInputEncodedType EncodedType.bool setHitBool := by
  have hComp := TMPolyTimeMap.comp setHitFromInstructions_tm_polytime setHitInstructions_tm_polytime
  simpa [Function.comp, setHitBool] using hComp

/-! ### Every source set is hit by the certificate list -/

def allSetsHitInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)

def allSetsHitInstructionListEncodedType : EncodedType :=
  EncodedType.list allSetsHitInstructionEncodedType

def allSetsHitInstructionInputEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType

def allSetsHitAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.bool

def allSetsHitInitInstruction (hitting : List Nat) : Bool × (List Nat × List Nat) :=
  (false, ([], hitting))

def allSetsHitElementInstruction (S : List Nat) : Bool × (List Nat × List Nat) :=
  (true, (S, []))

def allSetsHitInstructions (p : List (List Nat) × List Nat) :
    List (Bool × (List Nat × List Nat)) :=
  allSetsHitInitInstruction p.2 :: p.1.map allSetsHitElementInstruction

def allSetsHitRunnerInit : List Nat × Bool :=
  ([], true)

def allSetsHitStep
    (p : (List Nat × Bool) × (Bool × (List Nat × List Nat))) : List Nat × Bool :=
  if p.2.1 then
    (p.1.1, graphBoolAndPair (p.1.2, setHitBool (p.2.2.1, p.1.1)))
  else
    (p.2.2.2, true)

def allSetsHitFromInstructions (xs : List (Bool × (List Nat × List Nat))) : Bool :=
  (xs.foldl (fun acc x => allSetsHitStep (acc, x)) allSetsHitRunnerInit).2

def allSetsHitBool (p : List (List Nat) × List Nat) : Bool :=
  allSetsHitFromInstructions (allSetsHitInstructions p)

theorem allSetsHitElementInstructions_fold_eq_true_iff
    (sets : List (List Nat)) (hitting : List Nat) (ok : Bool) :
    ((sets.map allSetsHitElementInstruction).foldl
        (fun acc instr => allSetsHitStep (acc, instr)) (hitting, ok)).2 = true ↔
      ok = true ∧ ∀ S ∈ sets, ∃ x ∈ hitting, x ∈ S := by
  induction sets generalizing ok with
  | nil =>
      simp
  | cons S sets ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((sets.map allSetsHitElementInstruction).foldl
            (fun acc instr => allSetsHitStep (acc, instr))
            (hitting, graphBoolAndPair (ok, setHitBool (S, hitting)))).2 = true ↔
          ok = true ∧ ∀ T ∈ S :: sets, ∃ x ∈ hitting, x ∈ T
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff (ok, setHitBool (S, hitting))).1 hHead with
          ⟨hok, hSBool⟩
        refine ⟨hok, ?_⟩
        intro T hT
        simp at hT
        rcases hT with hTS | hT
        · subst T
          exact (setHitBool_eq_true_iff (S, hitting)).1 hSBool
        · exact hTail T hT
      · rintro ⟨hok, hAll⟩
        refine ⟨?_, ?_⟩
        · exact (graphBoolAndPair_eq_true_iff (ok, setHitBool (S, hitting))).2
            ⟨hok, (setHitBool_eq_true_iff (S, hitting)).2 (hAll S (by simp))⟩
        · intro T hT
          exact hAll T (List.mem_cons_of_mem S hT)

theorem allSetsHitBool_eq_true_iff (p : List (List Nat) × List Nat) :
    allSetsHitBool p = true ↔ ∀ S ∈ p.1, ∃ x ∈ p.2, x ∈ S := by
  rcases p with ⟨sets, hitting⟩
  change
    (((allSetsHitInitInstruction hitting :: sets.map allSetsHitElementInstruction).foldl
        (fun acc instr => allSetsHitStep (acc, instr)) allSetsHitRunnerInit).2 = true) ↔
      ∀ S ∈ sets, ∃ x ∈ hitting, x ∈ S
  rw [List.foldl_cons]
  simpa [allSetsHitRunnerInit, allSetsHitInitInstruction, allSetsHitStep] using
    allSetsHitElementInstructions_fold_eq_true_iff sets hitting true

theorem allSetsHitInitInstruction_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType allSetsHitInstructionEncodedType
      allSetsHitInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool (fun _ => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hEmpty :
      TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType (fun _ => ([] : List Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType setStructuredEncodedType []
  have hHitting : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hPayload :
      TMPolyTimeMap setStructuredEncodedType
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun hitting : List Nat => (([] : List Nat), hitting)) :=
    TMPolyTimeMap.prod_mk hEmpty hHitting
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [allSetsHitInitInstruction, allSetsHitInstructionEncodedType] using hOut

theorem allSetsHitElementInstruction_tm_polytime :
    TMPolyTimeMap setStructuredEncodedType allSetsHitInstructionEncodedType
      allSetsHitElementInstruction := by
  have hTrue : TMPolyTimeMap setStructuredEncodedType EncodedType.bool (fun _ => true) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool true
  have hSet : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hEmpty :
      TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType (fun _ => ([] : List Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType setStructuredEncodedType []
  have hPayload :
      TMPolyTimeMap setStructuredEncodedType
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun S : List Nat => (S, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hSet hEmpty
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [allSetsHitElementInstruction, allSetsHitInstructionEncodedType] using hOut

theorem allSetsHitInstructions_tm_polytime :
    TMPolyTimeMap
      allSetsHitInstructionInputEncodedType
      allSetsHitInstructionListEncodedType
      allSetsHitInstructions := by
  let X := allSetsHitInstructionInputEncodedType
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, allSetsHitInstructionInputEncodedType] using
      TMPolyTimeMap.fst setFamilyStructuredEncodedType setStructuredEncodedType
  have hHitting : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, allSetsHitInstructionInputEncodedType] using
      TMPolyTimeMap.snd setFamilyStructuredEncodedType setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X allSetsHitInstructionEncodedType
        (fun p : X.Carrier => allSetsHitInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp allSetsHitInitInstruction_tm_polytime hHitting
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X allSetsHitInstructionListEncodedType
        (fun p : X.Carrier => [allSetsHitInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton allSetsHitInstructionEncodedType) hInit
    simpa [Function.comp, allSetsHitInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X allSetsHitInstructionListEncodedType
        (fun p : X.Carrier => p.1.map allSetsHitElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map allSetsHitElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSets
    simpa [Function.comp, allSetsHitInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod allSetsHitInstructionListEncodedType allSetsHitInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([allSetsHitInitInstruction p.2], p.1.map allSetsHitElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append allSetsHitInstructionEncodedType) hAppendInput
  simpa [Function.comp, allSetsHitInstructions, allSetsHitInstructionListEncodedType, X] using hOut

theorem allSetsHitStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod allSetsHitAccEncodedType allSetsHitInstructionEncodedType)
      allSetsHitAccEncodedType
      allSetsHitStep := by
  let X := EncodedType.prod allSetsHitAccEncodedType allSetsHitInstructionEncodedType
  let A := allSetsHitAccEncodedType
  let Payload := EncodedType.prod setStructuredEncodedType setStructuredEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst allSetsHitAccEncodedType allSetsHitInstructionEncodedType
  have hInstr : TMPolyTimeMap X allSetsHitInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd allSetsHitAccEncodedType allSetsHitInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, allSetsHitInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, allSetsHitInstructionEncodedType, Payload, X] using hComp
  have hHitting : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, allSetsHitAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, allSetsHitAccEncodedType, X] using hComp
  have hPayloadSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadHitting :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hSetHitInput :
      TMPolyTimeMap X setHitInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayloadSet hHitting
  have hSetHit :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
          setHitBool (p.2.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setHitBool_tm_polytime hSetHitInput
    simpa [Function.comp, setHitInstructionInputEncodedType] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
          (p.1.2, setHitBool (p.2.2.1, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hSetHit
  have hAnd :
      TMPolyTimeMap X EncodedType.bool
        (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
          graphBoolAndPair (p.1.2, setHitBool (p.2.2.1, p.1.1))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
        (p.1.1, graphBoolAndPair (p.1.2, setHitBool (p.2.2.1, p.1.1)))) :=
    TMPolyTimeMap.prod_mk hHitting hAnd
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.2, true)) :=
    TMPolyTimeMap.prod_mk hPayloadHitting hTrueConst
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × ((List Nat × Bool) × (Bool × (List Nat × List Nat))) =>
          match p.1 with
          | true =>
              (p.2.1.1, graphBoolAndPair (p.2.1.2, setHitBool (p.2.2.2.1, p.2.1.1)))
          | false => (p.2.2.2.2, true)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.2, true))
      (fTrue := fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
        (p.1.1, graphBoolAndPair (p.1.2, setHitBool (p.2.2.1, p.1.1))))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranchOnProduct hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨hitting, ok⟩, ⟨tag, payloadSet, payloadHitting⟩⟩
  cases tag <;> rfl

theorem allSetsHitStep_inputSize_le
    (source : allSetsHitInstructionListEncodedType.Carrier)
    (acc : allSetsHitAccEncodedType.Carrier)
    (instr : allSetsHitInstructionEncodedType.Carrier)
    (hAcc :
      allSetsHitAccEncodedType.inputSize acc ≤
        allSetsHitInstructionListEncodedType.inputSize source + 10)
    (hInstr :
      allSetsHitInstructionEncodedType.inputSize instr ≤
        allSetsHitInstructionListEncodedType.inputSize source) :
    allSetsHitAccEncodedType.inputSize (allSetsHitStep (acc, instr)) ≤
      allSetsHitInstructionListEncodedType.inputSize source + 10 := by
  rcases acc with ⟨hitting, ok⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadSet, payloadHitting⟩
  cases tag
  · have hLocal :
        allSetsHitAccEncodedType.inputSize (payloadHitting, true) ≤
          allSetsHitInstructionEncodedType.inputSize (false, (payloadSet, payloadHitting)) + 10 := by
      simp [allSetsHitAccEncodedType, allSetsHitInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      omega
    exact (by simpa [allSetsHitStep] using hLocal.trans (Nat.add_le_add_right hInstr 10))
  · have hLocal :
        allSetsHitAccEncodedType.inputSize
            (allSetsHitStep ((hitting, ok), (true, (payloadSet, payloadHitting)))) ≤
          allSetsHitAccEncodedType.inputSize (hitting, ok) := by
      by_cases h : setHitBool (payloadSet, hitting) = true <;>
        cases ok <;>
          simp [allSetsHitStep, h, allSetsHitAccEncodedType, EncodedType.inputSize,
            EncodedType.prod, EncodedType.bool]
    exact hLocal.trans hAcc

theorem allSetsHitFold_tm_polytime :
    TMPolyTimeMap
      allSetsHitInstructionListEncodedType
      allSetsHitAccEncodedType
      (fun xs : allSetsHitInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => allSetsHitStep (acc, x)) allSetsHitRunnerInit) := by
  rcases allSetsHitStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 10
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      allSetsHitInstructionEncodedType allSetsHitAccEncodedType
      allSetsHitStep allSetsHitRunnerInit hStep bound ?_ ?_
  · intro xs
    change allSetsHitAccEncodedType.inputSize allSetsHitRunnerInit ≤
      (Polynomial.X + Polynomial.C 10).eval
        (allSetsHitInstructionEncodedType.list.inputSize xs)
    have hInit : allSetsHitAccEncodedType.inputSize allSetsHitRunnerInit ≤ 10 := by
      native_decide
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (allSetsHitInstructionEncodedType.list.inputSize xs) =
          allSetsHitInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        allSetsHitAccEncodedType.inputSize acc ≤
          allSetsHitInstructionListEncodedType.inputSize source + 10 := by
      simpa [allSetsHitInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        allSetsHitInstructionEncodedType.inputSize instr ≤
          allSetsHitInstructionListEncodedType.inputSize source := by
      simpa [allSetsHitInstructionListEncodedType] using hInstr
    simpa [allSetsHitInstructionListEncodedType, bound, Polynomial.eval_add] using
      allSetsHitStep_inputSize_le source acc instr hAcc' hInstr'

theorem allSetsHitFromInstructions_tm_polytime :
    TMPolyTimeMap allSetsHitInstructionListEncodedType EncodedType.bool
      allSetsHitFromInstructions := by
  have hFold := allSetsHitFold_tm_polytime
  have hOk := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk hFold
  simpa [Function.comp, allSetsHitFromInstructions, allSetsHitAccEncodedType] using hComp

theorem allSetsHitBool_tm_polytime :
    TMPolyTimeMap allSetsHitInstructionInputEncodedType EncodedType.bool allSetsHitBool := by
  have hComp := TMPolyTimeMap.comp allSetsHitFromInstructions_tm_polytime
    allSetsHitInstructions_tm_polytime
  simpa [Function.comp, allSetsHitBool] using hComp

/-! ### Hitting Set finite verifier -/

def hittingSetInputToTuple
    (I : hittingSetStructuredEncodedType.Carrier) :
    hittingSetTupleStructuredEncodedType.Carrier :=
  (I.system, I.k)

theorem hittingSetInputToTuple_encode (I : hittingSetStructuredEncodedType.Carrier) :
    hittingSetTupleStructuredEncodedType.encode (hittingSetInputToTuple I) =
      hittingSetStructuredEncodedType.encode I := by
  cases I
  rfl

noncomputable def hittingSetInputToTupleTMBackedMap :
    TMBackedCostedMap
      hittingSetStructuredEncodedType
      hittingSetTupleStructuredEncodedType
      hittingSetInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    hittingSetStructuredEncodedType
    hittingSetTupleStructuredEncodedType
    hittingSetInputToTuple
    (Equiv.refl hittingSetTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change hittingSetTupleStructuredEncodedType.encode (hittingSetInputToTuple I) =
        (hittingSetStructuredEncodedType.encode I).map id
      simp [hittingSetInputToTuple_encode])

def hittingSetStructuredFiniteVerify (I : HittingSetInput) (hitting : List Nat) : Bool :=
  graphBoolAndPair
    (natLeBool (hitting.length, I.k),
      graphBoolAndPair
        (boundedNatListBool (I.system.universeSize, hitting),
          allSetsHitBool (I.system.sets, hitting)))

theorem hittingSetStructuredFiniteVerify_eq_true_iff
    (I : HittingSetInput) (hitting : List Nat) :
    hittingSetStructuredFiniteVerify I hitting = true ↔
      hitting.length ≤ I.k ∧
        (∀ x ∈ hitting, x < I.system.universeSize) ∧
        HitsEverySet I.system hitting := by
  rw [hittingSetStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, natLeBool_eq_true_iff,
    boundedNatListBool_eq_true_iff, allSetsHitBool_eq_true_iff]
  rfl

theorem hittingSetStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod hittingSetStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : HittingSetInput × List Nat =>
        hittingSetStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod hittingSetStructuredEncodedType setStructuredEncodedType
  have hInstance : TMPolyTimeMap X hittingSetStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst hittingSetStructuredEncodedType setStructuredEncodedType
  have hCert : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd hittingSetStructuredEncodedType setStructuredEncodedType
  have hInstanceTuple :
      TMPolyTimeMap X hittingSetTupleStructuredEncodedType
        (fun p : X.Carrier => (p.1.system, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp hittingSetInputToTupleTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, hittingSetInputToTuple, X] using hComp
  have hSystem :
      TMPolyTimeMap X setSystemStructuredEncodedType (fun p : X.Carrier => p.1.system) := by
    have hFst := TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hInstanceTuple
    simpa [Function.comp, hittingSetTupleStructuredEncodedType, X] using hComp
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInstanceTuple
    simpa [Function.comp, hittingSetTupleStructuredEncodedType, X] using hComp
  have hSystemTuple :
      TMPolyTimeMap X setSystemTupleStructuredEncodedType
        (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp setSystemInputToTupleTMBackedMap.tm_polytime hSystem
    simpa [Function.comp, setSystemInputToTuple, X] using hComp
  have hUniverse :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.system.universeSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hCertLength : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp (listLengthTMBackedMap EncodedType.nat).tm_polytime hCert
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hLengthInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.length, p.1.k)) :=
    TMPolyTimeMap.prod_mk hCertLength hBudget
  have hLengthOK :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => natLeBool (p.2.length, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp natLeBool_tm_polytime hLengthInput
    simpa [Function.comp] using hComp
  have hWithinInput :
      TMPolyTimeMap X boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.system.universeSize, p.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hCert
  have hWithin :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => boundedNatListBool (p.1.system.universeSize, p.2)) := by
    have hComp := TMPolyTimeMap.comp boundedNatListBool_tm_polytime hWithinInput
    simpa [Function.comp, boundedNatInstructionInputEncodedType] using hComp
  have hHitsInput :
      TMPolyTimeMap X allSetsHitInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.system.sets, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hCert
  have hHits :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => allSetsHitBool (p.1.system.sets, p.2)) := by
    have hComp := TMPolyTimeMap.comp allSetsHitBool_tm_polytime hHitsInput
    simpa [Function.comp, allSetsHitInstructionInputEncodedType] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (boundedNatListBool (p.1.system.universeSize, p.2),
            allSetsHitBool (p.1.system.sets, p.2))) :=
    TMPolyTimeMap.prod_mk hWithin hHits
  have hTail :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier =>
          graphBoolAndPair
            (boundedNatListBool (p.1.system.universeSize, p.2),
              allSetsHitBool (p.1.system.sets, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (natLeBool (p.2.length, p.1.k),
            graphBoolAndPair
              (boundedNatListBool (p.1.system.universeSize, p.2),
                allSetsHitBool (p.1.system.sets, p.2)))) :=
    TMPolyTimeMap.prod_mk hLengthOK hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, hittingSetStructuredFiniteVerify, X] using hAll

theorem boundedNatList_inputSize_le
    (bound : Nat) (xs : List Nat) (hBound : ∀ x ∈ xs, x < bound) :
    setStructuredEncodedType.inputSize xs ≤ xs.length * (bound + 1) := by
  induction xs with
  | nil =>
      have hNil : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
        native_decide
      simpa using (le_of_eq hNil)
  | cons x xs ih =>
      have hx : x < bound := hBound x (by simp)
      have hxs : ∀ y ∈ xs, y < bound := by
        intro y hy
        exact hBound y (List.mem_cons_of_mem x hy)
      have hxSize : EncodedType.nat.inputSize x + 1 ≤ bound + 1 := by
        simp [EncodedType.inputSize, EncodedType.nat]
        omega
      have hTail := ih hxs
      have hCons :
          setStructuredEncodedType.inputSize (x :: xs) =
            EncodedType.nat.inputSize x + 1 + setStructuredEncodedType.inputSize xs := by
        simp [setStructuredEncodedType]
      refine le_trans (le_of_eq hCons) ?_
      calc
        EncodedType.nat.inputSize x + 1 + setStructuredEncodedType.inputSize xs
            ≤ (bound + 1) + xs.length * (bound + 1) := by
              exact Nat.add_le_add hxSize hTail
        _ = (x :: xs).length * (bound + 1) := by
            simp
            ring_nf

theorem hittingSetCertificate_inputSize_le_square
    (I : HittingSetInput) (hitting : List Nat)
    (hLen : hitting.length ≤ I.k)
    (hWithin : ∀ x ∈ hitting, x < I.system.universeSize) :
    setStructuredEncodedType.inputSize hitting ≤
      (hittingSetStructuredEncodedType.inputSize I) ^ 2 := by
  let S := hittingSetStructuredEncodedType.inputSize I
  have hCert := boundedNatList_inputSize_le I.system.universeSize hitting hWithin
  have hK : I.k ≤ S := by
    simp [S, hittingSetStructuredEncodedType, hittingSetTupleStructuredEncodedType,
      EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
    omega
  have hUniverse : I.system.universeSize + 1 ≤ S := by
    simp [S, hittingSetStructuredEncodedType, hittingSetTupleStructuredEncodedType,
      setSystemStructuredEncodedType, setSystemTupleStructuredEncodedType,
      EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
  calc
    setStructuredEncodedType.inputSize hitting
        ≤ hitting.length * (I.system.universeSize + 1) := hCert
    _ ≤ I.k * (I.system.universeSize + 1) :=
        Nat.mul_le_mul_right (I.system.universeSize + 1) hLen
    _ ≤ S * S := Nat.mul_le_mul hK hUniverse
    _ = S ^ 2 := by ring

end HittingSet

/-- Direct finite-certificate TM verifier for faithful structured Hitting Set. -/
noncomputable def hittingSetStructuredFiniteTMVerifier :
    TMVerifier hittingSetStructuredDecisionProblem where
  Cert := setStructuredEncodedType
  verify := HittingSet.hittingSetStructuredFiniteVerify
  verifier_polytime := HittingSet.hittingSetStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨hitting, hLen, hWithin, hHits⟩
    refine ⟨hitting, ?_, ?_⟩
    · simpa using HittingSet.hittingSetCertificate_inputSize_le_square I hitting hLen hWithin
    · exact (HittingSet.hittingSetStructuredFiniteVerify_eq_true_iff I hitting).2
        ⟨hLen, hWithin, hHits⟩
  sound := by
    intro I hitting hVerify
    rcases (HittingSet.hittingSetStructuredFiniteVerify_eq_true_iff I hitting).1 hVerify with
      ⟨hLen, hWithin, hHits⟩
    exact ⟨hitting, hLen, hWithin, hHits⟩

theorem hittingSetStructured_TMInNP :
    TMInNP hittingSetStructuredDecisionProblem :=
  TMInNP.intro hittingSetStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
