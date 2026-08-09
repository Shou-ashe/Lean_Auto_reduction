/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import Mathlib.Tactic

/-!
Direct standard-TM helpers for faithful structured Set Packing membership.

This file supplies exact equality for structured `List Nat` sets and a
family-membership scan over `List (List Nat)`.  The Set Packing verifier uses
these helpers to avoid assuming that the source set family is duplicate-free.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace SetPackingMembership

/-! ### Exact equality for finite unary natural lists -/

def natListEqAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.bool)

def natListEqPayloadEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.nat

def natListEqInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool natListEqPayloadEncodedType

def natListEqInstructionListEncodedType : EncodedType :=
  EncodedType.list natListEqInstructionEncodedType

def natListEqInputEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

abbrev NatListEqAccCarrier := List Nat × (Nat × Bool)

abbrev NatListEqPayloadCarrier := List Nat × Nat

abbrev NatListEqInstructionCarrier := Bool × NatListEqPayloadCarrier

abbrev NatListEqStepCarrier := NatListEqAccCarrier × NatListEqInstructionCarrier

def natListEqRunnerInit : NatListEqAccCarrier :=
  (([] : List Nat), ((0 : Nat), false))

def natListEqInitInstruction (rhs : List Nat) :
    natListEqInstructionEncodedType.Carrier :=
  (false, (rhs, (0 : Nat)))

def natListEqElementInstruction (x : Nat) :
    natListEqInstructionEncodedType.Carrier :=
  (true, ([], x))

def natListEqInstructions (p : List Nat × List Nat) :
    List natListEqInstructionEncodedType.Carrier :=
  natListEqInitInstruction p.2 :: p.1.map natListEqElementInstruction

def natListEqStep
    (p : NatListEqStepCarrier) :
    NatListEqAccCarrier :=
  match p.2.1 with
  | true =>
      let rhs : List Nat := p.1.1
      let idx : Nat := p.1.2.1
      let ok : Bool := p.1.2.2
      let x : Nat := p.2.2.2
      (rhs, (idx.succ, graphBoolAndPair (ok, decide (x = rhs.getD idx (0 : Nat)))))
  | false => (p.2.2.1, ((0 : Nat), true))

def natListEqPrefixFromInstructions
    (xs : List natListEqInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => natListEqStep (acc, instr)) natListEqRunnerInit).2.2

def natListEqPrefixBool (p : List Nat × List Nat) : Bool :=
  natListEqPrefixFromInstructions (natListEqInstructions p)

def NatListPrefixEqAt (rhs : List Nat) : Nat → List Nat → Prop
  | _idx, [] => True
  | idx, x :: xs => x = rhs.getD idx (0 : Nat) ∧ NatListPrefixEqAt rhs idx.succ xs

theorem natListEqElementInstructions_fold_eq_true_iff
    (lhs rhs : List Nat) (idx : Nat) (ok : Bool) :
    ((lhs.map natListEqElementInstruction).foldl
        (fun acc instr => natListEqStep (acc, instr)) (rhs, (idx, ok))).2.2 = true ↔
      ok = true ∧ NatListPrefixEqAt rhs idx lhs := by
  induction lhs generalizing idx ok with
  | nil =>
      change ok = true ↔ ok = true ∧ True
      exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | cons x xs ih =>
      simp only [List.map_cons]
      change
        ((xs.map natListEqElementInstruction).foldl
            (fun acc instr => natListEqStep (acc, instr))
            (rhs, (idx.succ,
              graphBoolAndPair (ok, decide (x = rhs.getD idx (0 : Nat)))))).2.2 =
            true ↔
          ok = true ∧
            x = rhs.getD idx (0 : Nat) ∧ NatListPrefixEqAt rhs idx.succ xs
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩
        rcases (graphBoolAndPair_eq_true_iff
            (ok, decide (x = rhs.getD idx (0 : Nat)))).1 hHead with ⟨hok, hx⟩
        exact ⟨hok, of_decide_eq_true hx, hTail⟩
      · rintro ⟨hok, hx, hTail⟩
        exact ⟨(graphBoolAndPair_eq_true_iff
            (ok, decide (x = rhs.getD idx (0 : Nat)))).2
            ⟨hok, decide_eq_true hx⟩, hTail⟩

theorem natListEqPrefixBool_eq_true_iff (lhs rhs : List Nat) :
    natListEqPrefixBool (lhs, rhs) = true ↔ NatListPrefixEqAt rhs 0 lhs := by
  change
    (((natListEqInitInstruction rhs :: lhs.map natListEqElementInstruction).foldl
        (fun acc instr => natListEqStep (acc, instr)) natListEqRunnerInit).2.2 = true) ↔
      NatListPrefixEqAt rhs 0 lhs
  change
    (((lhs.map natListEqElementInstruction).foldl
        (fun acc instr => natListEqStep (acc, instr)) (rhs, ((0 : Nat), true))).2.2 =
        true) ↔
      NatListPrefixEqAt rhs 0 lhs
  simpa using
    natListEqElementInstructions_fold_eq_true_iff lhs rhs 0 true

theorem NatListPrefixEqAt_cons_succ
    (head : Nat) (tail xs : List Nat) (idx : Nat) :
    NatListPrefixEqAt (head :: tail) idx.succ xs ↔ NatListPrefixEqAt tail idx xs := by
  induction xs generalizing idx with
  | nil =>
      simp [NatListPrefixEqAt]
  | cons x xs ih =>
      simp [NatListPrefixEqAt, ih, Nat.succ_eq_add_one]

theorem natListPrefixEqAt_zero_of_eq (xs : List Nat) :
    NatListPrefixEqAt xs 0 xs := by
  induction xs with
  | nil =>
      simp [NatListPrefixEqAt]
  | cons x xs ih =>
      exact ⟨rfl, (NatListPrefixEqAt_cons_succ x xs xs 0).2 ih⟩

theorem natList_eq_of_prefix_length_eq
    {lhs rhs : List Nat}
    (hPrefix : NatListPrefixEqAt rhs 0 lhs)
    (hLen : lhs.length = rhs.length) :
    lhs = rhs := by
  induction lhs generalizing rhs with
  | nil =>
      cases rhs with
      | nil => rfl
      | cons y ys => simp at hLen
  | cons x xs ih =>
      cases rhs with
      | nil => simp at hLen
      | cons y ys =>
          rcases hPrefix with ⟨hxy, hTail⟩
          have hTail' : NatListPrefixEqAt ys 0 xs :=
            (NatListPrefixEqAt_cons_succ y ys xs 0).1 hTail
          have hLen' : xs.length = ys.length := by
            simpa using hLen
          have hEqTail := ih hTail' hLen'
          simp at hxy
          subst x
          subst xs
          rfl

def natListEqBool (p : List Nat × List Nat) : Bool :=
  graphBoolAndPair
    (natListEqPrefixBool p, decide (p.1.length = p.2.length))

theorem natListEqBool_eq_true_iff (p : List Nat × List Nat) :
    natListEqBool p = true ↔ p.1 = p.2 := by
  rcases p with ⟨lhs, rhs⟩
  rw [natListEqBool, graphBoolAndPair_eq_true_iff,
    natListEqPrefixBool_eq_true_iff]
  constructor
  · rintro ⟨hPrefix, hLenBool⟩
    exact natList_eq_of_prefix_length_eq hPrefix (of_decide_eq_true hLenBool)
  · intro h
    change lhs = rhs at h
    subst rhs
    exact ⟨natListPrefixEqAt_zero_of_eq lhs, decide_eq_true rfl⟩

theorem natListEqInitInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      natListEqInstructionEncodedType
      natListEqInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool
      (fun _ : List Nat => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hRhs : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hZero : TMPolyTimeMap setStructuredEncodedType EncodedType.nat
      (fun _ : List Nat => (0 : Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload : TMPolyTimeMap setStructuredEncodedType natListEqPayloadEncodedType
      (fun rhs : List Nat => (rhs, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRhs hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [natListEqInitInstruction, natListEqInstructionEncodedType,
    natListEqPayloadEncodedType] using hOut

theorem natListEqElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat natListEqInstructionEncodedType
      natListEqElementInstruction := by
  have hTrue : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hEmpty : TMPolyTimeMap EncodedType.nat setStructuredEncodedType
      (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hNat : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload : TMPolyTimeMap EncodedType.nat natListEqPayloadEncodedType
      (fun x : Nat => (([] : List Nat), x)) :=
    TMPolyTimeMap.prod_mk hEmpty hNat
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [natListEqElementInstruction, natListEqInstructionEncodedType,
    natListEqPayloadEncodedType] using hOut

theorem natListEqInstructions_tm_polytime :
    TMPolyTimeMap
      natListEqInputEncodedType
      natListEqInstructionListEncodedType
      natListEqInstructions := by
  let X := natListEqInputEncodedType
  have hLhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, natListEqInputEncodedType] using
      TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
  have hRhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, natListEqInputEncodedType] using
      TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
  have hInit : TMPolyTimeMap X natListEqInstructionEncodedType
      (fun p : X.Carrier => natListEqInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp natListEqInitInstruction_tm_polytime hRhs
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X natListEqInstructionListEncodedType
      (fun p : X.Carrier => [natListEqInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton natListEqInstructionEncodedType) hInit
    simpa [Function.comp, natListEqInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X natListEqInstructionListEncodedType
      (fun p : X.Carrier => p.1.map natListEqElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map natListEqElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hLhs
    simpa [Function.comp, natListEqInstructionListEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod natListEqInstructionListEncodedType natListEqInstructionListEncodedType)
      (fun p : X.Carrier =>
        ([natListEqInitInstruction p.2], p.1.map natListEqElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append natListEqInstructionEncodedType) hAppendInput
  simpa [Function.comp, natListEqInstructions, natListEqInstructionListEncodedType, X] using hOut

theorem natListEqStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod natListEqAccEncodedType natListEqInstructionEncodedType)
      natListEqAccEncodedType
      natListEqStep := by
  let X := EncodedType.prod natListEqAccEncodedType natListEqInstructionEncodedType
  let A := natListEqAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst natListEqAccEncodedType natListEqInstructionEncodedType
  have hInstr : TMPolyTimeMap X natListEqInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd natListEqAccEncodedType natListEqInstructionEncodedType
  have hRhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, natListEqAccEncodedType, X] using hComp
  have hAccTail : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.bool)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, natListEqAccEncodedType, X] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool natListEqPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, natListEqInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X natListEqPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool natListEqPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, natListEqInstructionEncodedType, X] using hComp
  have hInitRhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, natListEqPayloadEncodedType, X] using hComp
  have hXNat : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, natListEqPayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseOut : TMPolyTimeMap X A
      (fun p : X.Carrier => (p.2.2.1, ((0 : Nat), true))) := by
    have hTail := TMPolyTimeMap.prod_mk hZero hTrue
    have hOut := TMPolyTimeMap.prod_mk hInitRhs hTail
    simpa [A, natListEqAccEncodedType] using hOut
  have hIdxSucc : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1.succ) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hIdx
    simpa [Function.comp] using hComp
  have hGetInput :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hRhs hIdx
  have hGet : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.1.getD p.1.2.1 (0 : Nat)) := by
    have hComp := TMPolyTimeMap.comp MaxCut.natListGetD_tm_polytime hGetInput
    simpa [Function.comp, MaxCut.natListGetD, setStructuredEncodedType,
      partitionWeightsStructuredEncodedType, X] using hComp
  have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.2.2, p.1.1.getD p.1.2.1 (0 : Nat))) := by
    exact @TMPolyTimeMap.prod_mk X EncodedType.nat EncodedType.nat
      (fun p : X.Carrier => p.2.2.2)
      (fun p : X.Carrier => p.1.1.getD p.1.2.1 (0 : Nat))
      hXNat hGet
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : NatListEqStepCarrier =>
        decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    convert hComp using 1
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : NatListEqStepCarrier =>
        (p.1.2.2, decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hOk hEq
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : NatListEqStepCarrier =>
        graphBoolAndPair
          (p.1.2.2, decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hTrueTail : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : NatListEqStepCarrier =>
        (p.1.2.1.succ,
          graphBoolAndPair
            (p.1.2.2, decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat))))) :=
    TMPolyTimeMap.prod_mk hIdxSucc hAnd
  have hTrueOut : TMPolyTimeMap X A
      (fun p : NatListEqStepCarrier =>
        (p.1.1,
          (p.1.2.1.succ,
            graphBoolAndPair (p.1.2.2,
              decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat)))))) :=
    TMPolyTimeMap.prod_mk hRhs hTrueTail
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × NatListEqStepCarrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (p.2.1.2.1.succ,
                  graphBoolAndPair (p.2.1.2.2,
                    decide (p.2.2.2.2 = p.2.1.1.getD p.2.1.2.1 (0 : Nat)))))
          | false => (p.2.2.2.1, ((0 : Nat), true))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : NatListEqStepCarrier => (p.2.2.1, ((0 : Nat), true)))
      (fTrue := fun p : NatListEqStepCarrier =>
        (p.1.1,
          (p.1.2.1.succ,
            graphBoolAndPair (p.1.2.2,
              decide (p.2.2.2 = p.1.1.getD p.1.2.1 (0 : Nat))))))
      hFalseOut hTrueOut
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1

theorem natListEqFold_tm_polytime :
    TMPolyTimeMap
      natListEqInstructionListEncodedType
      natListEqAccEncodedType
      (fun xs : natListEqInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => natListEqStep (acc, instr)) natListEqRunnerInit) := by
  rcases natListEqStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      natListEqInstructionEncodedType natListEqAccEncodedType
      natListEqStep natListEqRunnerInit hStep
      (Polynomial.C 20) (Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    change natListEqAccEncodedType.inputSize natListEqRunnerInit ≤
      (Polynomial.C 20).eval
        (natListEqInstructionEncodedType.list.inputSize xs)
    have hInit : natListEqAccEncodedType.inputSize natListEqRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    rcases acc with ⟨rhs, idx, ok⟩
    rcases instr with ⟨tag, payload⟩
    rcases payload with ⟨newRhs, x⟩
    cases tag <;>
      simp [natListEqStep, natListEqAccEncodedType, natListEqInstructionEncodedType,
        natListEqPayloadEncodedType, setStructuredEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool, Polynomial.eval_add] at hInstr ⊢ <;>
      omega

theorem natListEqPrefixFromInstructions_tm_polytime :
    TMPolyTimeMap
      natListEqInstructionListEncodedType
      EncodedType.bool
      natListEqPrefixFromInstructions := by
  have hFold := natListEqFold_tm_polytime
  have hTail := TMPolyTimeMap.snd setStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.bool)
  have hBool := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp1 := TMPolyTimeMap.comp hTail hFold
  have hComp2 := TMPolyTimeMap.comp hBool hComp1
  simpa [Function.comp, natListEqPrefixFromInstructions, natListEqAccEncodedType] using hComp2

theorem natListEqPrefixBool_tm_polytime :
    TMPolyTimeMap natListEqInputEncodedType EncodedType.bool natListEqPrefixBool := by
  have hComp := TMPolyTimeMap.comp natListEqPrefixFromInstructions_tm_polytime
    natListEqInstructions_tm_polytime
  simpa [Function.comp, natListEqPrefixBool] using hComp

theorem natListEqBool_tm_polytime :
    TMPolyTimeMap natListEqInputEncodedType EncodedType.bool natListEqBool := by
  let X := natListEqInputEncodedType
  have hLhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, natListEqInputEncodedType] using
      TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
  have hRhs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, natListEqInputEncodedType] using
      TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
  have hPrefix : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natListEqPrefixBool p) := by
    simpa [X] using natListEqPrefixBool_tm_polytime
  have hLhsLen : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hLhs
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hRhsLen : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hRhs
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hLenInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.length, p.2.length)) :=
    TMPolyTimeMap.prod_mk hLhsLen hRhsLen
  have hLenEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => decide (p.1.length = p.2.length)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLenInput
    simpa [Function.comp, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (natListEqPrefixBool p, decide (p.1.length = p.2.length))) :=
    TMPolyTimeMap.prod_mk hPrefix hLenEq
  have hOut := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, natListEqBool, X] using hOut

/-! ### Membership of one set in a finite set family -/

def setFamilyContainsAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType EncodedType.bool

def setFamilyContainsPayloadEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

def setFamilyContainsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool setFamilyContainsPayloadEncodedType

def setFamilyContainsInstructionListEncodedType : EncodedType :=
  EncodedType.list setFamilyContainsInstructionEncodedType

def setFamilyContainsInputEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setFamilyStructuredEncodedType

abbrev SetFamilyContainsAccCarrier := List Nat × Bool

abbrev SetFamilyContainsPayloadCarrier := List Nat × List Nat

abbrev SetFamilyContainsInstructionCarrier := Bool × SetFamilyContainsPayloadCarrier

abbrev SetFamilyContainsStepCarrier :=
  SetFamilyContainsAccCarrier × SetFamilyContainsInstructionCarrier

def setFamilyContainsRunnerInit : SetFamilyContainsAccCarrier := ([], false)

def setFamilyContainsInitInstruction (target : List Nat) :
    setFamilyContainsInstructionEncodedType.Carrier :=
  (false, (target, []))

def setFamilyContainsElementInstruction (S : List Nat) :
    setFamilyContainsInstructionEncodedType.Carrier :=
  (true, ([], S))

def setFamilyContainsInstructions (p : List Nat × List (List Nat)) :
    List setFamilyContainsInstructionEncodedType.Carrier :=
  setFamilyContainsInitInstruction p.1 :: p.2.map setFamilyContainsElementInstruction

def setFamilyContainsStep
    (p : SetFamilyContainsStepCarrier) :
    SetFamilyContainsAccCarrier :=
  match p.2.1 with
  | true => (p.1.1, graphBoolOrPair (p.1.2, natListEqBool (p.1.1, p.2.2.2)))
  | false => (p.2.2.1, false)

def setFamilyContainsFromInstructions
    (xs : List setFamilyContainsInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => setFamilyContainsStep (acc, instr))
    setFamilyContainsRunnerInit).2

def setFamilyContainsBool (p : List Nat × List (List Nat)) : Bool :=
  setFamilyContainsFromInstructions (setFamilyContainsInstructions p)

theorem setFamilyContainsElementInstructions_fold_iff
    (sets : List (List Nat)) (target : List Nat) (found : Bool) :
    ((sets.map setFamilyContainsElementInstruction).foldl
        (fun acc instr => setFamilyContainsStep (acc, instr)) (target, found)).2 = true ↔
      found = true ∨ target ∈ sets := by
  induction sets generalizing found with
  | nil =>
      cases found
      · change false = true ↔ false = true ∨ target ∈ ([] : List (List Nat))
        simp
      · change true = true ↔ true = true ∨ target ∈ ([] : List (List Nat))
        simp
  | cons S rest ih =>
      simp only [List.map_cons]
      change
        ((rest.map setFamilyContainsElementInstruction).foldl
            (fun acc instr => setFamilyContainsStep (acc, instr))
            (target, graphBoolOrPair (found, natListEqBool (target, S)))).2 = true ↔
          found = true ∨ target ∈ S :: rest
      rw [ih]
      constructor
      · intro h
        rcases h with hHead | hTail
        · rcases (graphBoolOrPair_eq_true_iff
            (found, natListEqBool (target, S))).1 hHead with hFound | hEq
          · exact Or.inl hFound
          · exact Or.inr (by
              have hTS : target = S := (natListEqBool_eq_true_iff (target, S)).1 hEq
              subst S
              simp)
        · exact Or.inr (by simp [hTail])
      · intro h
        rcases h with hFound | hMem
        · exact Or.inl ((graphBoolOrPair_eq_true_iff
            (found, natListEqBool (target, S))).2 (Or.inl hFound))
        · simp at hMem
          rcases hMem with hEq | hTail
          · exact Or.inl ((graphBoolOrPair_eq_true_iff
              (found, natListEqBool (target, S))).2
              (Or.inr ((natListEqBool_eq_true_iff (target, S)).2 hEq)))
          · exact Or.inr hTail

theorem setFamilyContainsBool_eq_true_iff (target : List Nat) (sets : List (List Nat)) :
    setFamilyContainsBool (target, sets) = true ↔ target ∈ sets := by
  change
    (((setFamilyContainsInitInstruction target ::
        sets.map setFamilyContainsElementInstruction).foldl
        (fun acc instr => setFamilyContainsStep (acc, instr))
        setFamilyContainsRunnerInit).2 = true) ↔ target ∈ sets
  change
    (((sets.map setFamilyContainsElementInstruction).foldl
        (fun acc instr => setFamilyContainsStep (acc, instr)) (target, false)).2 =
        true) ↔
      target ∈ sets
  simpa using
    setFamilyContainsElementInstructions_fold_iff sets target false

theorem setFamilyContainsInitInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      setFamilyContainsInstructionEncodedType
      setFamilyContainsInitInstruction := by
  have hFalse : TMPolyTimeMap setStructuredEncodedType EncodedType.bool
      (fun _ : List Nat => false) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool false
  have hTarget : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hEmpty : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType
      (fun _ : List Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType setStructuredEncodedType []
  have hPayload : TMPolyTimeMap setStructuredEncodedType setFamilyContainsPayloadEncodedType
      (fun target : List Nat => (target, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hTarget hEmpty
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [setFamilyContainsInitInstruction, setFamilyContainsInstructionEncodedType,
    setFamilyContainsPayloadEncodedType] using hOut

theorem setFamilyContainsElementInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      setFamilyContainsInstructionEncodedType
      setFamilyContainsElementInstruction := by
  have hTrue : TMPolyTimeMap setStructuredEncodedType EncodedType.bool
      (fun _ : List Nat => true) :=
    TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool true
  have hEmpty : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType
      (fun _ : List Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType setStructuredEncodedType []
  have hSet : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
    TMPolyTimeMap.id setStructuredEncodedType
  have hPayload : TMPolyTimeMap setStructuredEncodedType setFamilyContainsPayloadEncodedType
      (fun S : List Nat => (([] : List Nat), S)) :=
    TMPolyTimeMap.prod_mk hEmpty hSet
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [setFamilyContainsElementInstruction, setFamilyContainsInstructionEncodedType,
    setFamilyContainsPayloadEncodedType] using hOut

theorem setFamilyContainsInstructions_tm_polytime :
    TMPolyTimeMap
      setFamilyContainsInputEncodedType
      setFamilyContainsInstructionListEncodedType
      setFamilyContainsInstructions := by
  let X := setFamilyContainsInputEncodedType
  have hTarget : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, setFamilyContainsInputEncodedType] using
      TMPolyTimeMap.fst setStructuredEncodedType setFamilyStructuredEncodedType
  have hFamily : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setFamilyContainsInputEncodedType] using
      TMPolyTimeMap.snd setStructuredEncodedType setFamilyStructuredEncodedType
  have hInit : TMPolyTimeMap X setFamilyContainsInstructionEncodedType
      (fun p : X.Carrier => setFamilyContainsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp setFamilyContainsInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X setFamilyContainsInstructionListEncodedType
      (fun p : X.Carrier => [setFamilyContainsInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton setFamilyContainsInstructionEncodedType) hInit
    simpa [Function.comp, setFamilyContainsInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X setFamilyContainsInstructionListEncodedType
      (fun p : X.Carrier => p.2.map setFamilyContainsElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map setFamilyContainsElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hFamily
    simpa [Function.comp, setFamilyContainsInstructionListEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod setFamilyContainsInstructionListEncodedType
        setFamilyContainsInstructionListEncodedType)
      (fun p : X.Carrier =>
        ([setFamilyContainsInitInstruction p.1],
          p.2.map setFamilyContainsElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append setFamilyContainsInstructionEncodedType) hAppendInput
  simpa [Function.comp, setFamilyContainsInstructions,
    setFamilyContainsInstructionListEncodedType, X] using hOut

theorem setFamilyContainsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setFamilyContainsAccEncodedType setFamilyContainsInstructionEncodedType)
      setFamilyContainsAccEncodedType
      setFamilyContainsStep := by
  let X := EncodedType.prod setFamilyContainsAccEncodedType setFamilyContainsInstructionEncodedType
  let A := setFamilyContainsAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst setFamilyContainsAccEncodedType setFamilyContainsInstructionEncodedType
  have hInstr : TMPolyTimeMap X setFamilyContainsInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd setFamilyContainsAccEncodedType setFamilyContainsInstructionEncodedType
  have hTarget : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setFamilyContainsAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setFamilyContainsAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool setFamilyContainsPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, setFamilyContainsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X setFamilyContainsPayloadEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool setFamilyContainsPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, setFamilyContainsInstructionEncodedType, X] using hComp
  have hInitTarget : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, setFamilyContainsPayloadEncodedType, X] using hComp
  have hCandidate : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, setFamilyContainsPayloadEncodedType, X] using hComp
  have hEqInput : TMPolyTimeMap X natListEqInputEncodedType
      (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hTarget hCandidate
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : SetFamilyContainsStepCarrier => natListEqBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp natListEqBool_tm_polytime hEqInput
    convert hComp using 1
  have hOrInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : SetFamilyContainsStepCarrier =>
        (p.1.2, natListEqBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hFound hEq
  have hOr : TMPolyTimeMap X EncodedType.bool
      (fun p : SetFamilyContainsStepCarrier =>
        graphBoolOrPair (p.1.2, natListEqBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
    simpa [Function.comp, X] using hComp
  have hTrueOut : TMPolyTimeMap X A
      (fun p : SetFamilyContainsStepCarrier =>
        (p.1.1, graphBoolOrPair (p.1.2, natListEqBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hTarget hOr
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hFalseOut : TMPolyTimeMap X A
      (fun p : SetFamilyContainsStepCarrier => (p.2.2.1, false)) :=
    TMPolyTimeMap.prod_mk hInitTarget hFalse
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun p : Bool × SetFamilyContainsStepCarrier =>
        match p.1 with
        | true => (p.2.1.1, graphBoolOrPair (p.2.1.2, natListEqBool (p.2.1.1, p.2.2.2.2)))
        | false => (p.2.2.2.1, false)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : SetFamilyContainsStepCarrier => (p.2.2.1, false))
      (fTrue := fun p : SetFamilyContainsStepCarrier =>
        (p.1.1, graphBoolOrPair (p.1.2, natListEqBool (p.1.1, p.2.2.2))))
      hFalseOut hTrueOut
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1

theorem setFamilyContainsFold_tm_polytime :
    TMPolyTimeMap
      setFamilyContainsInstructionListEncodedType
      setFamilyContainsAccEncodedType
      (fun xs : setFamilyContainsInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => setFamilyContainsStep (acc, instr))
          setFamilyContainsRunnerInit) := by
  rcases setFamilyContainsStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      setFamilyContainsInstructionEncodedType setFamilyContainsAccEncodedType
      setFamilyContainsStep setFamilyContainsRunnerInit hStep
      (Polynomial.C 1000) (Polynomial.X + Polynomial.C 1000) ?_ ?_
  · intro xs
    change setFamilyContainsAccEncodedType.inputSize setFamilyContainsRunnerInit ≤
      (Polynomial.C 1000).eval
        (setFamilyContainsInstructionEncodedType.list.inputSize xs)
    have hInit : setFamilyContainsAccEncodedType.inputSize setFamilyContainsRunnerInit ≤
        1000 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    rcases acc with ⟨target, found⟩
    rcases instr with ⟨tag, payload⟩
    rcases payload with ⟨initTarget, candidate⟩
    cases tag
    · simp [setFamilyContainsStep, setFamilyContainsAccEncodedType,
        setFamilyContainsInstructionEncodedType, setFamilyContainsPayloadEncodedType,
        setStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        Polynomial.eval_add] at hInstr ⊢
      omega
    · simp [setFamilyContainsStep, setFamilyContainsAccEncodedType,
        setFamilyContainsInstructionEncodedType, setFamilyContainsPayloadEncodedType,
        setStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        Polynomial.eval_add] at hInstr ⊢

theorem setFamilyContainsFromInstructions_tm_polytime :
    TMPolyTimeMap
      setFamilyContainsInstructionListEncodedType
      EncodedType.bool
      setFamilyContainsFromInstructions := by
  have hFold := setFamilyContainsFold_tm_polytime
  have hFound := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound hFold
  simpa [Function.comp, setFamilyContainsFromInstructions,
    setFamilyContainsAccEncodedType] using hComp

theorem setFamilyContainsBool_tm_polytime :
    TMPolyTimeMap
      setFamilyContainsInputEncodedType
      EncodedType.bool
      setFamilyContainsBool := by
  have hComp := TMPolyTimeMap.comp setFamilyContainsFromInstructions_tm_polytime
    setFamilyContainsInstructions_tm_polytime
  simpa [Function.comp, setFamilyContainsBool] using hComp

end SetPackingMembership
end Karp21
end ComplexityReduction
