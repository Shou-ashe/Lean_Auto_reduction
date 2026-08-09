/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import Mathlib.Tactic

/-!
Direct standard-TM helper runners for the Exact Cover finite verifier.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace ExactCover

/-! ### At-most-one hit by a selected index list -/

def atMostOneHitAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.nat

def atMostOneHitInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod setStructuredEncodedType EncodedType.nat)

def atMostOneHitInstructionListEncodedType : EncodedType :=
  EncodedType.list atMostOneHitInstructionEncodedType

def atMostOneHitInputEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

def atMostOneHitInitInstruction (target : List Nat) :
    Bool × (List Nat × Nat) :=
  (false, (target, 0))

def atMostOneHitElementInstruction (j : Nat) :
    Bool × (List Nat × Nat) :=
  (true, ([], j))

def atMostOneHitInstructions (p : List Nat × List Nat) :
    List (Bool × (List Nat × Nat)) :=
  atMostOneHitInitInstruction p.1 :: p.2.map atMostOneHitElementInstruction

def atMostOneHitRunnerInit : List Nat × Nat :=
  ([], 0)

def atMostOneHitStep
    (p : (List Nat × Nat) × (Bool × (List Nat × Nat))) : List Nat × Nat :=
  if p.2.1 then
    if HittingSet.setContainsBool (p.2.2.2, p.1.1) then
      (p.1.1, p.1.2 + 1)
    else
      p.1
  else
    (p.2.2.1, 0)

def atMostOneHitFromInstructions
    (xs : List (Bool × (List Nat × Nat))) : Bool :=
  HittingSet.natLeBool
    ((xs.foldl (fun acc x => atMostOneHitStep (acc, x)) atMostOneHitRunnerInit).2, 1)

def atMostOneHitBool (p : List Nat × List Nat) : Bool :=
  atMostOneHitFromInstructions (atMostOneHitInstructions p)

def selectedHitCount (target : List Nat) : List Nat → Nat
  | [] => 0
  | j :: js =>
      (if j ∈ target then 1 else 0) + selectedHitCount target js

def AtMostOneHitList (target : List Nat) : List Nat → Prop
  | [] => True
  | j :: js =>
      (j ∈ target → ∀ k ∈ js, k ∉ target) ∧ AtMostOneHitList target js

theorem atMostOneHitElementInstructions_fold_eq
    (selected target : List Nat) (count : Nat) :
    ((selected.map atMostOneHitElementInstruction).foldl
        (fun acc instr => atMostOneHitStep (acc, instr)) (target, count)) =
      (target, count + selectedHitCount target selected) := by
  induction selected generalizing count with
  | nil =>
      simp [selectedHitCount]
  | cons j js ih =>
      rw [List.map_cons, List.foldl_cons]
      by_cases hj : j ∈ target
      · have hContains :
          HittingSet.setContainsBool (j, target) = true :=
            (HittingSet.setContainsBool_eq_true_iff (j, target)).2 hj
        simp [atMostOneHitElementInstruction, atMostOneHitStep, hContains,
          selectedHitCount, hj]
        simpa [Nat.add_assoc] using ih (count + 1)
      · have hContains :
          HittingSet.setContainsBool (j, target) = false := by
            cases h : HittingSet.setContainsBool (j, target)
            · rfl
            · have hj' := (HittingSet.setContainsBool_eq_true_iff (j, target)).1 h
              exact False.elim (hj hj')
        simp [atMostOneHitElementInstruction, atMostOneHitStep, hContains,
          selectedHitCount, hj]
        exact ih count

theorem atMostOneHitBool_count_iff (p : List Nat × List Nat) :
    atMostOneHitBool p = true ↔ selectedHitCount p.1 p.2 ≤ 1 := by
  rcases p with ⟨target, selected⟩
  change
    HittingSet.natLeBool
        ((((atMostOneHitInitInstruction target ::
          selected.map atMostOneHitElementInstruction).foldl
          (fun acc instr => atMostOneHitStep (acc, instr))
          atMostOneHitRunnerInit).2), 1) = true ↔
      selectedHitCount target selected ≤ 1
  rw [List.foldl_cons]
  have hFold := atMostOneHitElementInstructions_fold_eq selected target 0
  change
    HittingSet.natLeBool
        ((((selected.map atMostOneHitElementInstruction).foldl
          (fun acc instr => atMostOneHitStep (acc, instr)) (target, 0)).2), 1) =
        true ↔
      selectedHitCount target selected ≤ 1
  rw [hFold]
  simp [HittingSet.natLeBool_eq_true_iff]

theorem selectedHitCount_eq_zero_iff (target xs : List Nat) :
    selectedHitCount target xs = 0 ↔ ∀ j ∈ xs, j ∉ target := by
  induction xs with
  | nil =>
      simp [selectedHitCount]
  | cons j js ih =>
      by_cases hj : j ∈ target
      · simp [selectedHitCount, hj]
      · simp [selectedHitCount, hj, ih]

theorem selectedHitCount_le_one_iff_atMostOne (target xs : List Nat) :
    selectedHitCount target xs ≤ 1 ↔ AtMostOneHitList target xs := by
  induction xs with
  | nil =>
      simp [selectedHitCount, AtMostOneHitList]
  | cons j js ih =>
      by_cases hj : j ∈ target
      · have hZero := selectedHitCount_eq_zero_iff target js
        constructor
        · intro h
          have hTailZero : selectedHitCount target js = 0 := by
            simp [selectedHitCount, hj] at h
            omega
          refine ⟨?_, ?_⟩
          · intro _hj
            exact hZero.1 hTailZero
          exact ih.1 (by omega)
        · rintro ⟨hNoTail, _hTail⟩
          have hTailZero : selectedHitCount target js = 0 := hZero.2 (hNoTail hj)
          simp [selectedHitCount, hj, hTailZero]
      · simp [selectedHitCount, AtMostOneHitList, hj, ih]

theorem atMostOneHitBool_eq_true_iff (p : List Nat × List Nat) :
    atMostOneHitBool p = true ↔ AtMostOneHitList p.1 p.2 := by
  rw [atMostOneHitBool_count_iff, selectedHitCount_le_one_iff_atMostOne]

theorem AtMostOneHitList.eq_of_mem {target xs : List Nat}
    (h : AtMostOneHitList target xs) {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (haT : a ∈ target) (hbT : b ∈ target) :
    a = b := by
  induction xs with
  | nil =>
      simp at ha
  | cons j js ih =>
      simp [AtMostOneHitList] at h
      rcases h with ⟨hHead, hTail⟩
      simp at ha hb
      rcases ha with rfl | haTail
      · rcases hb with rfl | hbTail
        · rfl
        · exact False.elim (hHead haT b hbTail hbT)
      · rcases hb with rfl | hbTail
        · exact False.elim (hHead hbT a haTail haT)
        · exact ih hTail haTail hbTail

theorem AtMostOneHitList.of_nodup_unique {target xs : List Nat}
    (hNodup : xs.Nodup)
    (hUnique :
      ∀ a ∈ xs, ∀ b ∈ xs, a ∈ target → b ∈ target → a = b) :
    AtMostOneHitList target xs := by
  induction xs with
  | nil =>
      simp [AtMostOneHitList]
  | cons j js ih =>
      have hTailNodup : js.Nodup := hNodup.of_cons
      have hUniqueTail :
          ∀ a ∈ js, ∀ b ∈ js, a ∈ target → b ∈ target → a = b := by
        intro a ha b hb haT hbT
        exact hUnique a (by simp [ha]) b (by simp [hb]) haT hbT
      refine ⟨?_, ih hTailNodup hUniqueTail⟩
      intro hj k hk hkT
      have hEq : j = k :=
        hUnique j (by simp) k (by simp [hk]) hj hkT
      exact hNodup.notMem (by simpa [hEq] using hk)

theorem atMostOneHitInitInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      atMostOneHitInstructionEncodedType
      atMostOneHitInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool
      (fun _ : List Nat => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hTarget : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hZero : TMPolyTimeMap setStructuredEncodedType EncodedType.nat
      (fun _ : List Nat => (0 : Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :=
    TMPolyTimeMap.prod_mk hTarget hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [atMostOneHitInitInstruction, atMostOneHitInstructionEncodedType] using hOut

theorem atMostOneHitElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      atMostOneHitInstructionEncodedType
      atMostOneHitElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty : TMPolyTimeMap EncodedType.nat setStructuredEncodedType
      (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hNat : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload := TMPolyTimeMap.prod_mk hEmpty hNat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [atMostOneHitElementInstruction, atMostOneHitInstructionEncodedType] using hOut

theorem atMostOneHitInstructions_tm_polytime :
    TMPolyTimeMap
      atMostOneHitInputEncodedType
      atMostOneHitInstructionListEncodedType
      atMostOneHitInstructions := by
  let X := atMostOneHitInputEncodedType
  have hTarget : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, atMostOneHitInputEncodedType] using
      TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
  have hSelected : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, atMostOneHitInputEncodedType] using
      TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X atMostOneHitInstructionEncodedType
        (fun p : X.Carrier => atMostOneHitInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp atMostOneHitInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X atMostOneHitInstructionListEncodedType
        (fun p : X.Carrier => [atMostOneHitInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton atMostOneHitInstructionEncodedType) hInit
    simpa [Function.comp, atMostOneHitInstructionListEncodedType, X] using hComp
  have hElements :
      TMPolyTimeMap X atMostOneHitInstructionListEncodedType
        (fun p : X.Carrier => p.2.map atMostOneHitElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map atMostOneHitElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSelected
    simpa [Function.comp, atMostOneHitInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod atMostOneHitInstructionListEncodedType
          atMostOneHitInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([atMostOneHitInitInstruction p.1],
            p.2.map atMostOneHitElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append atMostOneHitInstructionEncodedType) hAppendInput
  simpa [Function.comp, atMostOneHitInstructions, atMostOneHitInstructionListEncodedType, X]
    using hOut

theorem atMostOneHitStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod atMostOneHitAccEncodedType atMostOneHitInstructionEncodedType)
      atMostOneHitAccEncodedType
      atMostOneHitStep := by
  let X := EncodedType.prod atMostOneHitAccEncodedType atMostOneHitInstructionEncodedType
  let A := atMostOneHitAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A atMostOneHitInstructionEncodedType
  have hInstr : TMPolyTimeMap X atMostOneHitInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A atMostOneHitInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod setStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, atMostOneHitInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod setStructuredEncodedType EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, atMostOneHitInstructionEncodedType, X] using hComp
  have hPayloadTarget : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hPayloadNat : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hAccTarget : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, X] using hComp
  have hAccCount : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, X] using hComp
  have hCountSucc : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => Nat.succ p.1.2) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAccCount
    simpa [Function.comp, X] using hComp
  have hContainsInput :
      TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayloadNat hAccTarget
  have hContains : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, HittingSet.setContainsInstructionInputEncodedType, X] using hComp
  have hHit : TMPolyTimeMap X A
      (fun p : X.Carrier => (p.1.1, Nat.succ p.1.2)) :=
    TMPolyTimeMap.prod_mk hAccTarget hCountSucc
  have hMiss : TMPolyTimeMap X A (fun p : X.Carrier => p.1) :=
    hAcc
  have hContainsBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (HittingSet.setContainsBool (p.2.2.2, p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hContains (TMPolyTimeMap.id X)
  have hContainsBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => (p.2.1.1, Nat.succ p.2.1.2)
          | false => p.2.1) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => p.1)
      (fTrue := fun p : X.Carrier => (p.1.1, Nat.succ p.1.2))
      hMiss hHit
  have hSelectedBranch : TMPolyTimeMap X A
        (fun p : X.Carrier =>
        if HittingSet.setContainsBool (p.2.2.2, p.1.1) then
          (p.1.1, Nat.succ p.1.2)
        else
          p.1) := by
    have hComp := TMPolyTimeMap.comp hContainsBranch hContainsBranchInput
    convert hComp using 1
    funext p
    cases h : HittingSet.setContainsBool (p.2.2.2, p.1.1) <;> simp [Function.comp, h]
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hInitBranch : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hPayloadTarget hZero
  have hTagBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hTagBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              if HittingSet.setContainsBool (p.2.2.2.2, p.2.1.1) then
                (p.2.1.1, Nat.succ p.2.1.2)
              else
                p.2.1
          | false => (p.2.2.2.1, (0 : Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, (0 : Nat)))
      (fTrue := fun p : X.Carrier =>
        if HittingSet.setContainsBool (p.2.2.2, p.1.1) then
          (p.1.1, Nat.succ p.1.2)
        else
          p.1)
      hInitBranch hSelectedBranch
  have hOut := TMPolyTimeMap.comp hTagBranch hTagBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨target, count⟩, ⟨tag, payloadTarget, j⟩⟩
  cases tag <;> simp [Function.comp, atMostOneHitStep] <;> rfl

theorem atMostOneHitStep_growth
    (source : List atMostOneHitInstructionEncodedType.Carrier)
    (acc : atMostOneHitAccEncodedType.Carrier)
    (instr : atMostOneHitInstructionEncodedType.Carrier)
    (hInstr :
      atMostOneHitInstructionEncodedType.inputSize instr ≤
        atMostOneHitInstructionListEncodedType.inputSize source) :
    atMostOneHitAccEncodedType.inputSize (atMostOneHitStep (acc, instr)) ≤
      atMostOneHitAccEncodedType.inputSize acc +
        (Polynomial.X + Polynomial.C 20).eval
          (atMostOneHitInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨target, count⟩
  rcases instr with ⟨tag, payloadTarget, j⟩
  cases tag
  ·
    have hLocal :
        atMostOneHitAccEncodedType.inputSize (payloadTarget, (0 : Nat)) ≤
          atMostOneHitInstructionEncodedType.inputSize
              (false, (payloadTarget, j)) + 20 := by
      simp [atMostOneHitAccEncodedType, atMostOneHitInstructionEncodedType,
        EncodedType.inputSize, EncodedType.prod,
        EncodedType.bool, EncodedType.nat]
      omega
    exact calc
      atMostOneHitAccEncodedType.inputSize
          (atMostOneHitStep ((target, count), (false, (payloadTarget, j))))
          ≤ atMostOneHitInstructionEncodedType.inputSize
              (false, (payloadTarget, j)) + 20 := by
            simpa [atMostOneHitStep] using hLocal
      _ ≤ atMostOneHitInstructionListEncodedType.inputSize source + 20 :=
            Nat.add_le_add_right hInstr 20
      _ ≤ atMostOneHitAccEncodedType.inputSize (target, count) +
            (Polynomial.X + Polynomial.C 20).eval
              (atMostOneHitInstructionListEncodedType.inputSize source) := by
            simp [Polynomial.eval_add]
  · cases h : HittingSet.setContainsBool (j, target)
    · simp [atMostOneHitStep, h, atMostOneHitAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, Polynomial.eval_add]
    · simp [atMostOneHitStep, h, atMostOneHitAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, Polynomial.eval_add]
      omega

theorem atMostOneHitFold_tm_polytime :
    TMPolyTimeMap
      atMostOneHitInstructionListEncodedType
      atMostOneHitAccEncodedType
      (fun xs : List atMostOneHitInstructionEncodedType.Carrier =>
        xs.foldl (fun acc x => atMostOneHitStep (acc, x)) atMostOneHitRunnerInit) := by
  rcases atMostOneHitStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      atMostOneHitInstructionEncodedType atMostOneHitAccEncodedType
      atMostOneHitStep atMostOneHitRunnerInit hStep
      (Polynomial.C 20) (Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    have hNil : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
      native_decide
    simp [atMostOneHitRunnerInit, atMostOneHitAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
  · intro source acc instr hInstr
    exact atMostOneHitStep_growth source acc instr hInstr

theorem atMostOneHitFromInstructions_tm_polytime :
    TMPolyTimeMap
      atMostOneHitInstructionListEncodedType
      EncodedType.bool
      atMostOneHitFromInstructions := by
  have hFold := atMostOneHitFold_tm_polytime
  have hCount :
      TMPolyTimeMap atMostOneHitInstructionListEncodedType EncodedType.nat
        (fun xs : atMostOneHitInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc x => atMostOneHitStep (acc, x)) atMostOneHitRunnerInit).2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hFold
    simpa [Function.comp, atMostOneHitAccEncodedType] using hComp
  have hOne : TMPolyTimeMap atMostOneHitInstructionListEncodedType EncodedType.nat
      (fun _ => (1 : Nat)) :=
    TMPolyTimeMap.const atMostOneHitInstructionListEncodedType EncodedType.nat (1 : Nat)
  have hInput :
      TMPolyTimeMap atMostOneHitInstructionListEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun xs => ((xs.foldl (fun acc x => atMostOneHitStep (acc, x))
          atMostOneHitRunnerInit).2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hCount hOne
  have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hInput
  simpa [Function.comp, atMostOneHitFromInstructions] using hComp

theorem atMostOneHitBool_tm_polytime :
    TMPolyTimeMap
      atMostOneHitInputEncodedType
      EncodedType.bool
      atMostOneHitBool := by
  have hComp := TMPolyTimeMap.comp atMostOneHitFromInstructions_tm_polytime
    atMostOneHitInstructions_tm_polytime
  simpa [Function.comp, atMostOneHitBool] using hComp


end ExactCover
end Karp21
end ComplexityReduction
