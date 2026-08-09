/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSATFiniteVerifier
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part1
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding
import Mathlib.Tactic

/-!
Direct-TM runner components for the finite-certificate 3SAT verifier.

This file starts with the executable lookup layer used by the verifier runner:
finite Boolean certificates are scanned by a fold with an explicit finite
accumulator, and the result is proved equal to `finiteAssignment`.
-/

namespace ComplexityReduction
namespace SAT

open ComplexityReduction.Karp21

/-- Input for Boolean certificate lookup: a certificate and a variable index. -/
abbrev lookupBoolInputEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType EncodedType.nat

/-- Lookup accumulator: remaining index, found flag, and selected value. -/
abbrev lookupBoolAcc : Type :=
  Nat × (Bool × Bool)

/-- Encoding for the lookup accumulator. -/
abbrev lookupBoolAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.bool EncodedType.bool)

/-- One lookup scan step over a certificate bit. -/
def lookupBoolConsumeStep (p : lookupBoolAcc × Bool) : lookupBoolAcc :=
  let acc := p.1
  let bit := p.2
  if acc.2.1 then
    acc
  else if acc.1 = 0 then
    (0, (true, bit))
  else
    (acc.1 - 1, (false, false))

/-- Encoded input type for one lookup scan step. -/
abbrev lookupBoolConsumeStepInputEncodedType : EncodedType :=
  EncodedType.prod lookupBoolAccEncodedType EncodedType.bool

/-- Executable finite-certificate lookup used by the future TM verifier. -/
def lookupBoolAt (p : List Bool × Nat) : Bool :=
  ((p.1.foldl (fun acc bit => lookupBoolConsumeStep (acc, bit))
    (p.2, (false, false))).2).2

theorem lookupBoolConsumeStep_found {acc : lookupBoolAcc} (h : acc.2.1 = true)
    (bit : Bool) :
    lookupBoolConsumeStep (acc, bit) = acc := by
  simp [lookupBoolConsumeStep, h]

theorem lookupBoolConsumeStep_zero (bit : Bool) :
    lookupBoolConsumeStep ((0, (false, false)), bit) = (0, (true, bit)) := by
  simp [lookupBoolConsumeStep]

theorem lookupBoolConsumeStep_succ (n : Nat) (bit : Bool) :
    lookupBoolConsumeStep ((n + 1, (false, false)), bit) =
      (n, (false, false)) := by
  simp [lookupBoolConsumeStep]

theorem lookupBoolConsumeStep_preserves_found_value
    (bits : List Bool) (n : Nat) (value : Bool) :
    ((bits.foldl (fun acc bit => lookupBoolConsumeStep (acc, bit))
      (n, (true, value))).2).2 = value := by
  induction bits generalizing n value with
  | nil =>
      simp
  | cons bit rest ih =>
      simp [lookupBoolConsumeStep_found (acc := (n, (true, value))) rfl bit, ih]

theorem lookupBoolAt_fold_eq_getD (bits : List Bool) (idx : Nat) :
    ((bits.foldl (fun acc bit => lookupBoolConsumeStep (acc, bit))
      (idx, (false, false))).2).2 = bits.getD idx false := by
  induction bits generalizing idx with
  | nil =>
      cases idx <;> simp
  | cons bit rest ih =>
      cases idx with
      | zero =>
          simp [lookupBoolConsumeStep_zero, lookupBoolConsumeStep_preserves_found_value]
      | succ idx =>
          simp [lookupBoolConsumeStep_succ, ih]

theorem lookupBoolAt_eq_getD (bits : List Bool) (idx : Nat) :
    lookupBoolAt (bits, idx) = bits.getD idx false := by
  exact lookupBoolAt_fold_eq_getD bits idx

theorem lookupBoolAt_eq_finiteAssignment (bits : List Bool) (idx : Nat) :
    lookupBoolAt (bits, idx) = finiteAssignment bits idx := by
  rw [lookupBoolAt_eq_getD]
  rfl

/-! ### Instruction-list lookup runner -/

/--
Lookup instructions.  A `false` tag initializes the countdown index from the
natural payload; a `true` tag consumes the Boolean payload as the next
certificate bit.
-/
abbrev lookupBoolInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod EncodedType.nat EncodedType.bool)

/-- Encoded lists of lookup instructions. -/
abbrev lookupBoolInstructionListEncodedType : EncodedType :=
  EncodedType.list lookupBoolInstructionEncodedType

/-- Fixed initial accumulator used by the typed fold. -/
def lookupBoolInitAcc : lookupBoolAcc :=
  ((0 : Nat), (false, false))

/-- Initializer instruction carrying the target variable index. -/
def lookupBoolInitInstruction (idx : Nat) :
    lookupBoolInstructionEncodedType.Carrier :=
  (false, (idx, false))

/-- Bit instruction carrying one certificate bit. -/
def lookupBoolBitInstruction (bit : Bool) :
    lookupBoolInstructionEncodedType.Carrier :=
  (true, ((0 : Nat), bit))

/-- Instruction list for finite lookup: initialize the index, then scan bits. -/
def lookupBoolInstructions (p : List Bool × Nat) :
    List lookupBoolInstructionEncodedType.Carrier :=
  lookupBoolInitInstruction p.2 :: p.1.map lookupBoolBitInstruction

/-- One instruction-fold step for finite lookup. -/
def lookupBoolStep (p : lookupBoolAcc × lookupBoolInstructionEncodedType.Carrier) :
    lookupBoolAcc :=
  match p.2.1 with
  | true => lookupBoolConsumeStep (p.1, p.2.2.2)
  | false => (p.2.2.1, (false, false))

/-- Execute a lookup instruction list and return the selected Boolean value. -/
def lookupBoolFromInstructions
    (xs : List lookupBoolInstructionEncodedType.Carrier) : Bool :=
  ((xs.foldl (fun acc instr => lookupBoolStep (acc, instr)) lookupBoolInitAcc).2).2

/-- Execute finite lookup from the certificate/index input. -/
def lookupBoolFromInput (p : List Bool × Nat) : Bool :=
  lookupBoolFromInstructions (lookupBoolInstructions p)

theorem lookupBoolBitInstructions_fold_eq
    (bits : List Bool) (acc : lookupBoolAcc) :
    (bits.map lookupBoolBitInstruction).foldl
        (fun acc instr => lookupBoolStep (acc, instr)) acc =
      bits.foldl (fun acc bit => lookupBoolConsumeStep (acc, bit)) acc := by
  induction bits generalizing acc with
  | nil =>
      simp
  | cons bit rest ih =>
      simpa [lookupBoolBitInstruction, lookupBoolStep] using
        ih (lookupBoolConsumeStep (acc, bit))

theorem lookupBoolFromInput_eq_lookupBoolAt (p : List Bool × Nat) :
    lookupBoolFromInput p = lookupBoolAt p := by
  rcases p with ⟨bits, idx⟩
  change
    (((lookupBoolInitInstruction idx :: bits.map lookupBoolBitInstruction).foldl
      (fun acc instr => lookupBoolStep (acc, instr)) lookupBoolInitAcc).2).2 =
      ((bits.foldl (fun acc bit => lookupBoolConsumeStep (acc, bit))
        (idx, (false, false))).2).2
  simp [lookupBoolInitInstruction, lookupBoolInitAcc, lookupBoolStep]
  exact congrArg (fun acc : lookupBoolAcc => acc.2.2)
    (lookupBoolBitInstructions_fold_eq bits (idx, (false, false)))

@[simp] theorem lookupBoolAccEncodedType_inputSize
    (remaining : Nat) (found value : Bool) :
    lookupBoolAccEncodedType.inputSize
        ((remaining, (found, value)) : lookupBoolAcc) =
      remaining + 5 := by
  simp [lookupBoolAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]

@[simp] theorem lookupBoolInstructionEncodedType_inputSize
    (tag : Bool) (idx : Nat) (bit : Bool) :
    lookupBoolInstructionEncodedType.inputSize
        ((tag, (idx, bit)) : lookupBoolInstructionEncodedType.Carrier) =
      idx + 5 := by
  simp [lookupBoolInstructionEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]
  omega

theorem lookupBoolConsumeStep_tm_polytime :
    TMPolyTimeMap
      lookupBoolConsumeStepInputEncodedType
      lookupBoolAccEncodedType
      lookupBoolConsumeStep := by
  let X := lookupBoolConsumeStepInputEncodedType
  let Acc := lookupBoolAccEncodedType
  have hAcc : TMPolyTimeMap X Acc (fun p : lookupBoolAcc × Bool => p.1) := by
    simpa [X, Acc, lookupBoolConsumeStepInputEncodedType] using
      TMPolyTimeMap.fst lookupBoolAccEncodedType EncodedType.bool
  have hBit : TMPolyTimeMap X EncodedType.bool (fun p : lookupBoolAcc × Bool => p.2) := by
    simpa [X, lookupBoolConsumeStepInputEncodedType] using
      TMPolyTimeMap.snd lookupBoolAccEncodedType EncodedType.bool
  have hRemaining : TMPolyTimeMap X EncodedType.nat
      (fun p : lookupBoolAcc × Bool => p.1.1) := by
    have hFstAcc := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hFstAcc hAcc
    simpa [Function.comp, X, Acc] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool
      (fun p : lookupBoolAcc × Bool => p.1.2.1) := by
    have hSndAcc := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool EncodedType.bool)
    have hBoolPair : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : lookupBoolAcc × Bool => p.1.2) := by
      have hComp := TMPolyTimeMap.comp hSndAcc hAcc
      simpa [Function.comp, X, Acc] using hComp
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hBoolPair
    simpa [Function.comp, X] using hComp
  have hKeep : TMPolyTimeMap X Acc (fun p : lookupBoolAcc × Bool => p.1) := hAcc
  have hSetValue : TMPolyTimeMap X Acc
      (fun p : lookupBoolAcc × Bool => ((0 : Nat), (true, p.2))) := by
    have hZero : TMPolyTimeMap X EncodedType.nat
        (fun _ : lookupBoolAcc × Bool => (0 : Nat)) :=
      TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
    have hTrue : TMPolyTimeMap X EncodedType.bool
        (fun _ : lookupBoolAcc × Bool => true) :=
      TMPolyTimeMap.const X EncodedType.bool true
    have hPair : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : lookupBoolAcc × Bool => (true, p.2)) :=
      TMPolyTimeMap.prod_mk hTrue hBit
    exact TMPolyTimeMap.prod_mk hZero hPair
  have hDecrement : TMPolyTimeMap X Acc
      (fun p : lookupBoolAcc × Bool => (p.1.1 - 1, (false, false))) := by
    have hOne : TMPolyTimeMap X EncodedType.nat
        (fun _ : lookupBoolAcc × Bool => (1 : Nat)) :=
      TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
    have hSubInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : lookupBoolAcc × Bool => (p.1.1, (1 : Nat))) :=
      TMPolyTimeMap.prod_mk hRemaining hOne
    have hSub : TMPolyTimeMap X EncodedType.nat
        (fun p : lookupBoolAcc × Bool => p.1.1 - 1) := by
      have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput
      simpa [Function.comp, X] using hComp
    have hFalse₁ : TMPolyTimeMap X EncodedType.bool
        (fun _ : lookupBoolAcc × Bool => false) :=
      TMPolyTimeMap.const X EncodedType.bool false
    have hFalse₂ : TMPolyTimeMap X EncodedType.bool
        (fun _ : lookupBoolAcc × Bool => false) :=
      TMPolyTimeMap.const X EncodedType.bool false
    have hPair : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun _ : lookupBoolAcc × Bool => (false, false)) :=
      TMPolyTimeMap.prod_mk hFalse₁ hFalse₂
    exact TMPolyTimeMap.prod_mk hSub hPair
  have hEqZero : TMPolyTimeMap X EncodedType.bool
      (fun p : lookupBoolAcc × Bool => decide (p.1.1 = (0 : Nat))) := by
    have hZero : TMPolyTimeMap X EncodedType.nat
        (fun _ : lookupBoolAcc × Bool => (0 : Nat)) :=
      TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
    have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : lookupBoolAcc × Bool => (p.1.1, (0 : Nat))) :=
      TMPolyTimeMap.prod_mk hRemaining hZero
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp, X] using hComp
  have hEqZeroTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : lookupBoolAcc × Bool => (decide (p.1.1 = (0 : Nat)), p)) :=
    TMPolyTimeMap.prod_mk hEqZero (TMPolyTimeMap.id X)
  have hZeroBranch : TMPolyTimeMap X Acc
      (fun p : lookupBoolAcc × Bool =>
        match decide (p.1.1 = (0 : Nat)) with
        | true => ((0 : Nat), (true, p.2))
        | false => (p.1.1 - 1, (false, false))) := by
    have hDispatch :=
      Karp21.Clique.boolProduct_dispatch_tm_polytime X Acc
        (fFalse := fun p : lookupBoolAcc × Bool => (p.1.1 - 1, (false, false)))
        (fTrue := fun p : lookupBoolAcc × Bool => ((0 : Nat), (true, p.2)))
        hDecrement hSetValue
    have hComp := TMPolyTimeMap.comp hDispatch hEqZeroTagged
    simpa [Function.comp] using hComp
  have hFoundTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : lookupBoolAcc × Bool => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hFound (TMPolyTimeMap.id X)
  have hDispatch :=
    Karp21.Clique.boolProduct_dispatch_tm_polytime X Acc
      (fFalse := fun p : lookupBoolAcc × Bool =>
        match decide (p.1.1 = (0 : Nat)) with
        | true => ((0 : Nat), (true, p.2))
        | false => (p.1.1 - 1, (false, false)))
      (fTrue := fun p : lookupBoolAcc × Bool => p.1)
      hZeroBranch hKeep
  have hComp := TMPolyTimeMap.comp hDispatch hFoundTagged
  convert hComp using 1
  funext p
  rcases p with ⟨⟨remaining, ⟨found, value⟩⟩, bit⟩
  cases found
  · cases remaining with
    | zero =>
        rfl
    | succ n =>
        simp [Function.comp, lookupBoolConsumeStep]
        apply Prod.ext
        · exact (Nat.add_sub_cancel n 1).symm
        · rfl
  · rfl

theorem lookupBoolStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod lookupBoolAccEncodedType lookupBoolInstructionEncodedType)
      lookupBoolAccEncodedType
      lookupBoolStep := by
  let X := EncodedType.prod lookupBoolAccEncodedType lookupBoolInstructionEncodedType
  let A := lookupBoolAccEncodedType
  let I := lookupBoolInstructionEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : lookupBoolAcc × I.Carrier => p.1) := by
    simpa [X, A, I] using TMPolyTimeMap.fst lookupBoolAccEncodedType
      lookupBoolInstructionEncodedType
  have hInstr : TMPolyTimeMap X I (fun p : lookupBoolAcc × I.Carrier => p.2) := by
    simpa [X, I] using TMPolyTimeMap.snd lookupBoolAccEncodedType
      lookupBoolInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : lookupBoolAcc × I.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, X, I, lookupBoolInstructionEncodedType] using hComp
  have hPayload : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : lookupBoolAcc × I.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, X, I, lookupBoolInstructionEncodedType] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : lookupBoolAcc × I.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hBit : TMPolyTimeMap X EncodedType.bool
      (fun p : lookupBoolAcc × I.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hFalse₁ : TMPolyTimeMap X EncodedType.bool
      (fun _ : lookupBoolAcc × I.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hFalse₂ : TMPolyTimeMap X EncodedType.bool
      (fun _ : lookupBoolAcc × I.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInitTail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun _ : lookupBoolAcc × I.Carrier => (false, false)) :=
    TMPolyTimeMap.prod_mk hFalse₁ hFalse₂
  have hInit : TMPolyTimeMap X A
      (fun p : lookupBoolAcc × I.Carrier => (p.2.2.1, (false, false))) :=
    TMPolyTimeMap.prod_mk hIdx hInitTail
  have hConsumeInput : TMPolyTimeMap X lookupBoolConsumeStepInputEncodedType
      (fun p : lookupBoolAcc × I.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hBit
  have hConsume : TMPolyTimeMap X A
      (fun p : lookupBoolAcc × I.Carrier => lookupBoolConsumeStep (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp lookupBoolConsumeStep_tm_polytime hConsumeInput
    simpa [Function.comp, A, lookupBoolConsumeStepInputEncodedType] using hComp
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : lookupBoolAcc × I.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :=
    Karp21.Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : lookupBoolAcc × I.Carrier => (p.2.2.1, (false, false)))
      (fTrue := fun p : lookupBoolAcc × I.Carrier =>
        lookupBoolConsumeStep (p.1, p.2.2.2))
      hInit hConsume
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1

theorem lookupBoolInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      lookupBoolInstructionEncodedType
      lookupBoolInitInstruction := by
  have hFalse₁ : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hIdx : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun idx : Nat => idx) :=
    TMPolyTimeMap.id EncodedType.nat
  have hFalse₂ : TMPolyTimeMap EncodedType.nat EncodedType.bool
      (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hPayload : TMPolyTimeMap EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun idx : Nat => (idx, false)) :=
    TMPolyTimeMap.prod_mk hIdx hFalse₂
  have hOut := TMPolyTimeMap.prod_mk hFalse₁ hPayload
  simpa [lookupBoolInitInstruction, lookupBoolInstructionEncodedType] using hOut

theorem lookupBoolBitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.bool
      lookupBoolInstructionEncodedType
      lookupBoolBitInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool
      (fun _ : Bool => true) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.bool true
  have hZero : TMPolyTimeMap EncodedType.bool EncodedType.nat
      (fun _ : Bool => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.nat (0 : Nat)
  have hBit : TMPolyTimeMap EncodedType.bool EncodedType.bool
      (fun bit : Bool => bit) :=
    TMPolyTimeMap.id EncodedType.bool
  have hPayload : TMPolyTimeMap EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun bit : Bool => ((0 : Nat), bit)) :=
    TMPolyTimeMap.prod_mk hZero hBit
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  convert hOut using 1

theorem lookupBoolInstructions_tm_polytime :
    TMPolyTimeMap
      lookupBoolInputEncodedType
      lookupBoolInstructionListEncodedType
      lookupBoolInstructions := by
  let X := lookupBoolInputEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, lookupBoolInputEncodedType] using
      TMPolyTimeMap.fst finiteAssignmentCertEncodedType EncodedType.nat
  have hIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2) := by
    simpa [X, lookupBoolInputEncodedType] using
      TMPolyTimeMap.snd finiteAssignmentCertEncodedType EncodedType.nat
  have hInit : TMPolyTimeMap X lookupBoolInstructionEncodedType
      (fun p : X.Carrier => lookupBoolInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp lookupBoolInitInstruction_tm_polytime hIdx
    simpa [Function.comp, X] using hComp
  have hMappedBits : TMPolyTimeMap X lookupBoolInstructionListEncodedType
      (fun p : X.Carrier => p.1.map lookupBoolBitInstruction) := by
    have hMap := TMPolyTimeMap.list_map lookupBoolBitInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hBits
    simpa [Function.comp, lookupBoolInstructionListEncodedType, finiteAssignmentCertEncodedType,
      X] using hComp
  have hConsInput : TMPolyTimeMap X
      (EncodedType.prod lookupBoolInstructionEncodedType lookupBoolInstructionListEncodedType)
      (fun p : X.Carrier =>
        (lookupBoolInitInstruction p.2, p.1.map lookupBoolBitInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedBits
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons lookupBoolInstructionEncodedType) hConsInput
  simpa [Function.comp, lookupBoolInstructions, lookupBoolInstructionListEncodedType, X]
    using hCons

theorem lookupBoolInitAcc_bound
    (xs : List lookupBoolInstructionEncodedType.Carrier) :
    lookupBoolAccEncodedType.inputSize lookupBoolInitAcc ≤
      (Polynomial.C 10).eval (lookupBoolInstructionListEncodedType.inputSize xs) := by
  simp [lookupBoolInitAcc, lookupBoolAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]

theorem lookupBoolStep_growth
    (source : List lookupBoolInstructionEncodedType.Carrier)
    (acc : lookupBoolAccEncodedType.Carrier)
    (instr : lookupBoolInstructionEncodedType.Carrier)
    (hInstr :
      lookupBoolInstructionEncodedType.inputSize instr ≤
        lookupBoolInstructionListEncodedType.inputSize source) :
    lookupBoolAccEncodedType.inputSize (lookupBoolStep (acc, instr)) ≤
      lookupBoolAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (lookupBoolInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨remaining, found, value⟩
  rcases instr with ⟨tag, idx, bit⟩
  change Nat at remaining
  change Bool at found value tag bit
  change Nat at idx
  cases tag
  · have hIdxSize :
        idx + 5 ≤ lookupBoolInstructionListEncodedType.inputSize source := by
      have hRaw := hInstr
      simp [lookupBoolInstructionEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool] at hRaw
      omega
    simp [lookupBoolStep, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    omega
  · cases found <;> by_cases hZero : remaining = 0 <;>
      simp [lookupBoolStep, lookupBoolConsumeStep, hZero,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] ; omega

theorem lookupBoolFold_tm_polytime :
    TMPolyTimeMap
      lookupBoolInstructionListEncodedType
      lookupBoolAccEncodedType
      (fun xs : List lookupBoolInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => lookupBoolStep (acc, instr)) lookupBoolInitAcc) := by
  rcases lookupBoolStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      lookupBoolInstructionEncodedType lookupBoolAccEncodedType
      lookupBoolStep lookupBoolInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact lookupBoolInitAcc_bound xs
  · intro source acc instr hInstr
    exact lookupBoolStep_growth source acc instr hInstr

theorem lookupBoolFromInstructions_tm_polytime :
    TMPolyTimeMap
      lookupBoolInstructionListEncodedType
      EncodedType.bool
      lookupBoolFromInstructions := by
  have hFold := lookupBoolFold_tm_polytime
  have hTail :=
    TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool EncodedType.bool)
  have hValue := TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hValueComp := TMPolyTimeMap.comp hValue hTailComp
  simpa [Function.comp, lookupBoolFromInstructions, lookupBoolAccEncodedType]
    using hValueComp

theorem lookupBoolFromInput_tm_polytime :
    TMPolyTimeMap
      lookupBoolInputEncodedType
      EncodedType.bool
      lookupBoolFromInput := by
  have hComp :=
    TMPolyTimeMap.comp lookupBoolFromInstructions_tm_polytime
      lookupBoolInstructions_tm_polytime
  simpa [Function.comp, lookupBoolFromInput] using hComp

theorem lookupBoolAt_tm_polytime :
    TMPolyTimeMap
      lookupBoolInputEncodedType
      EncodedType.bool
      lookupBoolAt := by
  convert lookupBoolFromInput_tm_polytime using 1
  funext p
  exact (lookupBoolFromInput_eq_lookupBoolAt p).symm

/-! ### Literal evaluation runner -/

/-- Input for executable literal evaluation: certificate bits and one literal. -/
abbrev literalFiniteEvalInputEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType

/-- Executable finite-certificate literal evaluation. -/
def literalFiniteEvalBool (p : List Bool × Literal) : Bool :=
  let value := lookupBoolAt (p.1, p.2.var)
  match p.2.neg with
  | true => Bool.not value
  | false => value

theorem literalFiniteEvalBool_eq_eval (bits : List Bool) (l : Literal) :
    literalFiniteEvalBool (bits, l) = l.eval (finiteAssignment bits) := by
  cases l with
  | mk var neg =>
      cases neg <;>
        simp [literalFiniteEvalBool, Literal.eval, lookupBoolAt_eq_finiteAssignment]

theorem literalFiniteEvalBool_tm_polytime :
    TMPolyTimeMap
      literalFiniteEvalInputEncodedType
      EncodedType.bool
      literalFiniteEvalBool := by
  let X := literalFiniteEvalInputEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, literalFiniteEvalInputEncodedType] using
      TMPolyTimeMap.fst finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType
  have hLiteral : TMPolyTimeMap X Karp21.literalStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, literalFiniteEvalInputEncodedType] using
      TMPolyTimeMap.snd finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType
  have hVar : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.var) := by
    have hComp := TMPolyTimeMap.comp Karp21.Clique.literal_var_tm_polytime hLiteral
    simpa [Function.comp, X] using hComp
  have hNeg : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.2.neg) := by
    have hComp := TMPolyTimeMap.comp Karp21.Clique.literal_neg_tm_polytime hLiteral
    simpa [Function.comp, X] using hComp
  have hLookupInput : TMPolyTimeMap X lookupBoolInputEncodedType
      (fun p : X.Carrier => (p.1, p.2.var)) :=
    TMPolyTimeMap.prod_mk hBits hVar
  have hValue : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => lookupBoolAt (p.1, p.2.var)) := by
    have hComp := TMPolyTimeMap.comp lookupBoolAt_tm_polytime hLookupInput
    simpa [Function.comp, lookupBoolInputEncodedType, X] using hComp
  have hNotValue : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => Bool.not (lookupBoolAt (p.1, p.2.var))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hValue
    simpa [Function.comp, X] using hComp
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.neg, p)) :=
    TMPolyTimeMap.prod_mk hNeg (TMPolyTimeMap.id X)
  have hDispatch :=
    Karp21.Clique.boolProduct_dispatch_tm_polytime X EncodedType.bool
      (fFalse := fun p : X.Carrier => lookupBoolAt (p.1, p.2.var))
      (fTrue := fun p : X.Carrier => Bool.not (lookupBoolAt (p.1, p.2.var)))
      hValue hNotValue
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1

end SAT
end ComplexityReduction
