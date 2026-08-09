/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.MembershipRunner

/-!
TM-backed index-list runner for the faithful structured Set Covering to Hitting
Set route.  Given a source set family and an element `x`, it scans the family
and returns exactly the indices of source sets that contain `x`.
-/

namespace ComplexityReduction
namespace Karp21
namespace HittingSet

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### TM-facing source-family index instruction layer -/

def setIndexPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def setIndexInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool setIndexPayloadEncodedType

def setIndexInstructionListEncodedType : EncodedType :=
  EncodedType.list setIndexInstructionEncodedType

def setIndexInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def setIndexScanAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))

def setIndexScanInputEncodedType : EncodedType :=
  EncodedType.prod setIndexScanAccEncodedType setIndexInstructionEncodedType

def setIndexInitInstruction (x : Nat) : Bool × (Nat × List Nat) :=
  (false, (x, []))

def setIndexSetInstruction (S : List Nat) : Bool × (Nat × List Nat) :=
  (true, ((0 : Nat), S))

def setIndexInstructions (p : Nat × List (List Nat)) :
    List (Bool × (Nat × List Nat)) :=
  setIndexInitInstruction p.1 :: p.2.map setIndexSetInstruction

def setIndexScanInit : Nat × (Nat × List Nat) :=
  (0, (0, []))

def setIndexScanStep
    (p : (Nat × (Nat × List Nat)) × (Bool × (Nat × List Nat))) :
    Nat × (Nat × List Nat) :=
  if p.2.1 then
    let needle := p.1.1
    let next := p.1.2.1
    let out := p.1.2.2
    let S := p.2.2.2
    if setContainsBool (needle, S) then
      (needle, (next + 1, out ++ [next]))
    else
      (needle, (next + 1, out))
  else
    (p.2.2.1, (0, []))

def setIndexIndicesFromInstructions
    (xs : List (Bool × (Nat × List Nat))) : List Nat :=
  (xs.foldl (fun acc x => setIndexScanStep (acc, x)) setIndexScanInit).2.2

def setIndexIndicesFromFamily (p : Nat × List (List Nat)) : List Nat :=
  setIndexIndicesFromInstructions (setIndexInstructions p)

/-! ### Semantics -/

theorem setIndexSetInstructions_fold_findIdxs
    (sets : List (List Nat)) (x next : Nat) (out : List Nat) :
    (sets.map setIndexSetInstruction).foldl
        (fun acc instr => setIndexScanStep (acc, instr)) (x, (next, out)) =
      (x, (next + sets.length,
        out ++ sets.findIdxs (fun S => setContainsBool (x, S)) next)) := by
  induction sets generalizing next out with
  | nil =>
      simp
  | cons S sets ih =>
      cases hContains : setContainsBool (x, S)
      · simp [setIndexSetInstruction, setIndexScanStep, hContains]
        change (sets.map setIndexSetInstruction).foldl
            (fun acc instr => setIndexScanStep (acc, instr)) (x, (next + 1, out)) =
          (x, (next + (sets.length + 1),
            out ++ sets.findIdxs (fun S => setContainsBool (x, S)) (next + 1)))
        rw [ih (next + 1) out]
        simp [Nat.add_comm, Nat.add_left_comm]
      · simp [setIndexSetInstruction, setIndexScanStep, hContains]
        change (sets.map setIndexSetInstruction).foldl
            (fun acc instr => setIndexScanStep (acc, instr)) (x, (next + 1, out ++ [next])) =
          (x, (next + (sets.length + 1),
            out ++ next :: sets.findIdxs (fun S => setContainsBool (x, S)) (next + 1)))
        rw [ih (next + 1) (out ++ [next])]
        simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem setIndexIndicesFromFamily_eq_findIdxs
    (sets : List (List Nat)) (x : Nat) :
    setIndexIndicesFromFamily (x, sets) =
      sets.findIdxs (fun S => setContainsBool (x, S)) := by
  change
    ((setIndexInitInstruction x :: sets.map setIndexSetInstruction).foldl
        (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit).2.2 =
      sets.findIdxs (fun S => setContainsBool (x, S))
  rw [List.foldl_cons]
  simp [setIndexInitInstruction, setIndexScanStep]
  have h := setIndexSetInstructions_fold_findIdxs sets x 0 []
  simpa using congrArg (fun p : Nat × (Nat × List Nat) => p.2.2) h

theorem setIndexIndicesFromFamily_eq_indicesContaining
    (I : SetCoveringInput) (x : Nat) :
    setIndexIndicesFromFamily (x, I.system.sets) = indicesContaining I x := by
  rw [setIndexIndicesFromFamily_eq_findIdxs]
  simp [indicesContaining, setContainsBool_eq_decide]

/-! ### TM witnesses for instructions and step -/

theorem setIndexSetInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      setIndexInstructionEncodedType
      setIndexSetInstruction := by
  let X := setStructuredEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X setIndexPayloadEncodedType
        (fun S : X.Carrier => ((0 : Nat), S)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hInstruction :
      TMPolyTimeMap X setIndexInstructionEncodedType
        (fun S : X.Carrier => (true, ((0 : Nat), S))) :=
    TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [setIndexSetInstruction, X, setIndexInstructionEncodedType,
    setIndexPayloadEncodedType] using hInstruction

theorem setIndexInstructions_tm_polytime :
    TMPolyTimeMap
      setIndexInstructionInputEncodedType
      setIndexInstructionListEncodedType
      setIndexInstructions := by
  let X := setIndexInstructionInputEncodedType
  have hNeedle : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, setIndexInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setIndexInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hEmptySet :
      TMPolyTimeMap X setStructuredEncodedType (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X setStructuredEncodedType []
  have hInitPayload :
      TMPolyTimeMap X setIndexPayloadEncodedType
        (fun p : X.Carrier => (p.1, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hNeedle hEmptySet
  have hInitInstruction :
      TMPolyTimeMap X setIndexInstructionEncodedType
        (fun p : X.Carrier => setIndexInitInstruction p.1) := by
    have hPair := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [setIndexInitInstruction, setIndexInstructionEncodedType,
      setIndexPayloadEncodedType] using hPair
  have hInitSingleton :
      TMPolyTimeMap X setIndexInstructionListEncodedType
        (fun p : X.Carrier => [setIndexInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton setIndexInstructionEncodedType)
        hInitInstruction
    simpa [Function.comp, setIndexInstructionListEncodedType] using hComp
  have hSetInstructions :
      TMPolyTimeMap X setIndexInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setIndexSetInstruction) := by
    have hMap := TMPolyTimeMap.list_map setIndexSetInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hSets
    simpa [Function.comp, setIndexInstructionListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setIndexInstructionListEncodedType
          setIndexInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([setIndexInitInstruction p.1], p.2.map setIndexSetInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hSetInstructions
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append setIndexInstructionEncodedType) hAppendInput
  simpa [Function.comp, setIndexInstructions, setIndexInstructionListEncodedType] using hAppend

theorem setIndexScanStep_tm_polytime :
    TMPolyTimeMap
      setIndexScanInputEncodedType
      setIndexScanAccEncodedType
      setIndexScanStep := by
  let X := setIndexScanInputEncodedType
  let A := setIndexScanAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, setIndexScanInputEncodedType] using
      TMPolyTimeMap.fst setIndexScanAccEncodedType setIndexInstructionEncodedType
  have hInstruction :
      TMPolyTimeMap X setIndexInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setIndexScanInputEncodedType] using
      TMPolyTimeMap.snd setIndexScanAccEncodedType setIndexInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool setIndexPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstruction
    simpa [Function.comp, setIndexInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X setIndexPayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool setIndexPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstruction
    simpa [Function.comp, setIndexInstructionEncodedType, X] using hComp
  have hPayloadNeedle : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, setIndexPayloadEncodedType, X] using hComp
  have hPayloadSet :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, setIndexPayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEmptyNatList :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X (EncodedType.list EncodedType.nat) ([] : List Nat)
  have hInitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun _ : X.Carrier => ((0 : Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hZero hEmptyNatList
  have hInitBranch :
      TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ((0 : Nat), ([] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadNeedle hInitTail
  have hAccNeedle : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setIndexScanAccEncodedType, X] using hComp
  have hAccTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setIndexScanAccEncodedType, X] using hComp
  have hAccNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, X] using hComp
  have hAccOut :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, X] using hComp
  have hNextSucc : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAccNext
    simpa [Function.comp, X] using hComp
  have hNextSingleton :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => ([p.1.2.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hAccNext
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => (p.1.2.2, ([p.1.2.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hAccOut hNextSingleton
  have hOutAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier =>
          List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, X] using hComp
  have hHitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier =>
          (Nat.succ p.1.2.1,
            List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hNextSucc hOutAppend
  have hMissTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))) :=
    TMPolyTimeMap.prod_mk hNextSucc hAccOut
  have hHit :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          (p.1.1,
            (Nat.succ p.1.2.1,
              List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hAccNeedle hHitTail
  have hMiss :
      TMPolyTimeMap X A
        (fun p : X.Carrier => (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat)))) :=
    TMPolyTimeMap.prod_mk hAccNeedle hMissTail
  have hContainsInput :
      TMPolyTimeMap X setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccNeedle hPayloadSet
  have hContains :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => setContainsBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, X] using hComp
  have hContainsBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (setContainsBool (p.1.1, p.2.2.2), p)) :=
    TMPolyTimeMap.prod_mk hContains (TMPolyTimeMap.id X)
  have hSetBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (Nat.succ p.2.1.2.1,
                  List.append (p.2.1.2.2 : List Nat) ([p.2.1.2.1] : List Nat)))
          | false => (p.2.1.1, (Nat.succ p.2.1.2.1, (p.2.1.2.2 : List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          (Nat.succ p.1.2.1,
            List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat))))
      hMiss hHit
  have hSetBranch :
      TMPolyTimeMap X A
        (fun p : X.Carrier =>
          if setContainsBool (p.1.1, p.2.2.2) then
            (p.1.1,
              (Nat.succ p.1.2.1,
                List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))
          else
            (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat)))) := by
    have hComp := TMPolyTimeMap.comp hSetBranchOnProduct hContainsBranchInput
    convert hComp using 1
    funext p
    cases h : setContainsBool (p.1.1, p.2.2.2) <;> simp [Function.comp, h]
  have hTagBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hTagBranchOnProduct :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              if setContainsBool (p.2.1.1, p.2.2.2.2) then
                (p.2.1.1,
                  (Nat.succ p.2.1.2.1,
                    List.append (p.2.1.2.2 : List Nat) ([p.2.1.2.1] : List Nat)))
              else
                (p.2.1.1, (Nat.succ p.2.1.2.1, (p.2.1.2.2 : List Nat)))
          | false => (p.2.2.2.1, ((0 : Nat), ([] : List Nat)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ((0 : Nat), ([] : List Nat))))
      (fTrue := fun p : X.Carrier =>
        if setContainsBool (p.1.1, p.2.2.2) then
          (p.1.1,
            (Nat.succ p.1.2.1,
              List.append (p.1.2.2 : List Nat) ([p.1.2.1] : List Nat)))
        else
          (p.1.1, (Nat.succ p.1.2.1, (p.1.2.2 : List Nat))))
      hInitBranch hSetBranch
  have hOut := TMPolyTimeMap.comp hTagBranchOnProduct hTagBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨needle, next, out⟩, ⟨tag, payloadNeedle, S⟩⟩
  cases tag
  · rfl
  · cases hContainsVal : setContainsBool (needle, S)
    · simp [Function.comp, setIndexScanStep, hContainsVal, Nat.succ_eq_add_one]
      rfl
    · simp [Function.comp, setIndexScanStep, hContainsVal, Nat.succ_eq_add_one]
      rfl

/-! ### Reachable fold bounds and the index runner -/

def setIndexScanAccBound (N processed : Nat) (acc : Nat × (Nat × List Nat)) : Prop :=
  acc.1 ≤ N ∧
    acc.2.1 ≤ processed ∧
      (∀ j ∈ acc.2.2, j ≤ processed) ∧ acc.2.2.length ≤ processed

theorem setIndexScanStep_bound {N processed : Nat}
    {acc : Nat × (Nat × List Nat)}
    {instr : Bool × (Nat × List Nat)}
    (hAcc : setIndexScanAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : setIndexInstructionEncodedType.inputSize instr ≤ N) :
    setIndexScanAccBound N (processed + 1) (setIndexScanStep (acc, instr)) := by
  rcases acc with ⟨needle, next, out⟩
  rcases instr with ⟨tag, payloadNeedle, S⟩
  rcases hAcc with ⟨hNeedle, hNext, hOutMem, hOutLen⟩
  change needle ≤ N at hNeedle
  change next ≤ processed at hNext
  change (∀ j ∈ out, j ≤ processed) at hOutMem
  change out.length ≤ processed at hOutLen
  cases tag
  · have hPayloadNeedle : payloadNeedle ≤ N := by
      simp [setIndexInstructionEncodedType, setIndexPayloadEncodedType,
        setStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat] at hInstr
      omega
    simp [setIndexScanStep, setIndexScanAccBound]
    exact hPayloadNeedle
  · cases hContains : setContainsBool (needle, S)
    · simp [setIndexScanStep, hContains, setIndexScanAccBound]
      refine ⟨hNeedle, by omega, ?_, by omega⟩
      intro j hj
      exact (hOutMem j hj).trans (by omega)
    · simp [setIndexScanStep, hContains, setIndexScanAccBound]
      refine ⟨hNeedle, by omega, ?_, by simp [hOutLen]⟩
      intro j hj
      rcases hj with hjOut | hjNext
      · exact (hOutMem j hjOut).trans (by omega)
      · subst j
        omega

theorem setIndexScanFold_bound_aux
    {N processed : Nat}
    (xs : List setIndexInstructionEncodedType.Carrier)
    (acc : setIndexScanAccEncodedType.Carrier)
    (hAcc : setIndexScanAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, setIndexInstructionEncodedType.inputSize instr ≤ N) :
    setIndexScanAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => setIndexScanStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : setIndexInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := setIndexScanStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, setIndexInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1)
          (acc := setIndexScanStep (acc, x)) hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem setIndexScanFold_bound_of_inputSize_le
    {N : Nat} (xs : List setIndexInstructionEncodedType.Carrier)
    (hSize : setIndexInstructionListEncodedType.inputSize xs ≤ N) :
    setIndexScanAccBound N xs.length
      (xs.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit) := by
  have hInit : setIndexScanAccBound N 0 setIndexScanInit := by
    simp [setIndexScanAccBound, setIndexScanInit]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      SetCovering.incidentEncodedList_length_le_inputSize setIndexInstructionEncodedType xs
    have hLenInput' : xs.length ≤ setIndexInstructionListEncodedType.inputSize xs := by
      simpa [setIndexInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, setIndexInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      SetCovering.incidentEncodedList_element_inputSize_le
        (X := setIndexInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : setIndexInstructionEncodedType.inputSize instr ≤
        setIndexInstructionListEncodedType.inputSize xs := by
      simpa [setIndexInstructionListEncodedType] using hElem
    omega
  have h :=
    setIndexScanFold_bound_aux (N := N) (processed := 0) xs setIndexScanInit
      hInit hLen hInstr
  simpa using h

noncomputable def setIndexScanFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem setIndexScanFoldAccBoundPolynomial_eval (N : Nat) :
    setIndexScanFoldAccBoundPolynomial.eval N = 10 * (N * N) + 100 := by
  simp [setIndexScanFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem setIndexScanAccBound_inputSize_le {N processed : Nat}
    {acc : Nat × (Nat × List Nat)}
    (hAcc : setIndexScanAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    setIndexScanAccEncodedType.inputSize acc ≤
      setIndexScanFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨needle, next, out⟩
  rcases hAcc with ⟨hNeedle, hNext, hOutMem, hOutLen⟩
  have hNextN : next ≤ N := hNext.trans hProcessed
  have hOutSize :
      (EncodedType.list EncodedType.nat).inputSize out ≤ processed * (N + 2) := by
    have hElems : ∀ j ∈ out, EncodedType.nat.inputSize j ≤ N + 1 := by
      intro j hj
      have hjN : j ≤ N := (hOutMem j hj).trans hProcessed
      simp [EncodedType.inputSize_nat]
      omega
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        EncodedType.nat out (N + 1) hElems
    exact hList.trans (Nat.mul_le_mul_right (N + 2) hOutLen)
  have hOutSizeN :
      (EncodedType.list EncodedType.nat).inputSize out ≤ N * (N + 2) := by
    exact hOutSize.trans (Nat.mul_le_mul_right (N + 2) hProcessed)
  simp [setIndexScanAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  nlinarith [sq_nonneg (N : Int), hNeedle, hNextN, hOutSizeN]

noncomputable def setIndexScanFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod setIndexScanAccEncodedType
          setIndexInstructionEncodedType).encode
        setIndexScanAccEncodedType.encode
        setIndexScanStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm setIndexScanFoldAccBoundPolynomial
    (hStep.time.comp
      (setIndexScanFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem setIndexScanFold_tm_polytime :
    TMPolyTimeMap
      setIndexInstructionListEncodedType
      setIndexScanAccEncodedType
      (fun xs : List setIndexInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit) := by
  rcases setIndexScanStep_tm_polytime with ⟨hStep⟩
  let time := setIndexScanFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      setIndexInstructionEncodedType setIndexScanAccEncodedType
      setIndexScanStep setIndexScanInit hStep time ?_
  intro source
  let N := setIndexInstructionListEncodedType.inputSize source
  let B := setIndexScanFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List setIndexInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              setIndexInstructionEncodedType setIndexScanAccEncodedType
              setIndexScanStep hStep
              (pref.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit)
              rest ≤
            C * (EncodedType.list setIndexInstructionEncodedType).inputSize rest := by
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
        have hxN : setIndexInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            SetCovering.incidentEncodedList_element_inputSize_le
              (X := setIndexInstructionEncodedType) (x := x) (xs := source) hxMemSource
          simpa [N, setIndexInstructionListEncodedType] using hElem
        have hPrefixSize : setIndexInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              setIndexInstructionListEncodedType.inputSize source =
                setIndexInstructionListEncodedType.inputSize pref +
                  setIndexInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact SetCovering.incidentEncodedList_inputSize_append setIndexInstructionEncodedType
              pref (x :: xs)
          omega
        have hPrefixBound :=
          setIndexScanFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            SetCovering.incidentEncodedList_length_le_inputSize setIndexInstructionEncodedType pref
          have hLen' : pref.length ≤ setIndexInstructionListEncodedType.inputSize pref := by
            simpa [setIndexInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            setIndexScanAccEncodedType.inputSize
                (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                  setIndexScanInit) ≤ B := by
          simpa [B] using
            setIndexScanAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (x :: xs).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          have hSourceLenN : source.length ≤ N := by
            have hLen :=
              SetCovering.incidentEncodedList_length_le_inputSize setIndexInstructionEncodedType source
            simpa [N, setIndexInstructionListEncodedType] using hLen
          omega
        have hStepBound :=
          setIndexScanStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            setIndexScanAccEncodedType.inputSize
                (setIndexScanStep
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x)) ≤ B := by
          have hProcessedN : pref.length + 1 ≤ N := hStepProcessed
          simpa [B] using
            setIndexScanAccBound_inputSize_le hStepBound hProcessedN
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod setIndexScanAccEncodedType
                  setIndexInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x)) ≤ T := by
          have hArg :
              (EncodedType.prod setIndexScanAccEncodedType
                setIndexInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              setIndexScanAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                      setIndexScanInit) +
                  1 + setIndexInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (setIndexInstructionEncodedType.encode x).length
                (setIndexScanAccEncodedType.encode
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit)).length
                (setIndexScanAccEncodedType.encode
                  (setIndexScanStep
                    (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                      setIndexScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod setIndexScanAccEncodedType
                    setIndexInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                      setIndexScanInit, x))) ≤
              C * (setIndexInstructionEncodedType.inputSize x + 1) := by
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
                setIndexInstructionEncodedType setIndexScanAccEncodedType
                setIndexScanStep hStep
                (setIndexScanStep
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x)) xs ≤
              C * (EncodedType.list setIndexInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit =
                setIndexScanStep
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x) := by
            exact
              List.foldl_concat
                (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                setIndexInstructionEncodedType setIndexScanAccEncodedType
                setIndexScanStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              setIndexInstructionEncodedType setIndexScanAccEncodedType
              setIndexScanStep hStep
              (pref.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                setIndexInstructionEncodedType setIndexScanAccEncodedType
                setIndexScanStep hStep
                (setIndexScanStep
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (setIndexInstructionEncodedType.encode x).length
                (setIndexScanAccEncodedType.encode
                  (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                    setIndexScanInit)).length
                (setIndexScanAccEncodedType.encode
                  (setIndexScanStep
                    (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                      setIndexScanInit, x))).length
                (hStep.time.eval
                  ((EncodedType.prod setIndexScanAccEncodedType
                    setIndexInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => setIndexScanStep (acc, instr))
                      setIndexScanInit, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list setIndexInstructionEncodedType).inputSize xs +
                C * (setIndexInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list setIndexInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          setIndexInstructionEncodedType setIndexScanAccEncodedType
          setIndexScanStep hStep setIndexScanInit source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, setIndexInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, setIndexScanFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        setIndexInstructionEncodedType setIndexScanAccEncodedType
        setIndexScanStep hStep setIndexScanInit source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem setIndexIndicesFromInstructions_tm_polytime :
    TMPolyTimeMap
      setIndexInstructionListEncodedType
      (EncodedType.list EncodedType.nat)
      setIndexIndicesFromInstructions := by
  have hFold := setIndexScanFold_tm_polytime
  have hTail :
      TMPolyTimeMap setIndexInstructionListEncodedType
        (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
        (fun xs : setIndexInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
    have hComp := TMPolyTimeMap.comp hSnd hFold
    simpa [Function.comp, setIndexScanAccEncodedType] using hComp
  have hOut :
      TMPolyTimeMap setIndexInstructionListEncodedType
        (EncodedType.list EncodedType.nat)
        (fun xs : setIndexInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc instr => setIndexScanStep (acc, instr)) setIndexScanInit).2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp] using hComp
  simpa [setIndexIndicesFromInstructions] using hOut

theorem setIndexIndicesFromFamily_tm_polytime :
    TMPolyTimeMap
      setIndexInstructionInputEncodedType
      (EncodedType.list EncodedType.nat)
      setIndexIndicesFromFamily := by
  have hComp :=
    TMPolyTimeMap.comp setIndexIndicesFromInstructions_tm_polytime
      setIndexInstructions_tm_polytime
  simpa [Function.comp, setIndexIndicesFromFamily] using hComp

theorem setIndexIndicesFromFamily_length_le
    (p : setIndexInstructionInputEncodedType.Carrier) :
    (setIndexIndicesFromFamily p).length ≤ p.2.length := by
  rcases p with ⟨x, sets⟩
  change (setIndexIndicesFromFamily (x, sets)).length ≤ sets.length
  rw [setIndexIndicesFromFamily_eq_findIdxs sets x]
  simpa using
    (List.countP_le_length (l := sets)
      (p := fun S : List Nat => setContainsBool (x, S)))

theorem mem_setIndexIndicesFromFamily_lt
    {p : setIndexInstructionInputEncodedType.Carrier} {j : Nat}
    (hj : j ∈ setIndexIndicesFromFamily p) :
    j < p.2.length := by
  rcases p with ⟨x, sets⟩
  change j ∈ setIndexIndicesFromFamily (x, sets) at hj
  change j < sets.length
  rw [setIndexIndicesFromFamily_eq_findIdxs sets x] at hj
  rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := sets)
      (p := fun S : List Nat => setContainsBool (x, S))).1 hj with
    ⟨hjLt, _hPred⟩
  exact hjLt

theorem setIndexIndicesFromFamily_inputSize_le
    (p : setIndexInstructionInputEncodedType.Carrier) :
    (EncodedType.list EncodedType.nat).inputSize (setIndexIndicesFromFamily p) ≤
      3 * setIndexInstructionInputEncodedType.inputSize p ^ 2 + 10 := by
  let N := setIndexInstructionInputEncodedType.inputSize p
  have hSetsLen :
      p.2.length ≤ N := by
    have hLen := SetCovering.incidentEncodedList_length_le_inputSize setStructuredEncodedType p.2
    have hList :
        p.2.length ≤ setFamilyStructuredEncodedType.inputSize p.2 := by
      simpa [setFamilyStructuredEncodedType] using hLen
    simp [N, setIndexInstructionInputEncodedType, EncodedType.inputSize_prod]
    omega
  have hOutputSize :
      (EncodedType.list EncodedType.nat).inputSize (setIndexIndicesFromFamily p) ≤
        (setIndexIndicesFromFamily p).length * (p.2.length + 2) := by
    have hList :=
      ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
        EncodedType.nat (setIndexIndicesFromFamily p) (p.2.length + 1)
        (by
          intro j hj
          have hjLt := mem_setIndexIndicesFromFamily_lt (p := p) hj
          simp [EncodedType.inputSize, EncodedType.nat]
          omega)
    simpa [Nat.add_assoc] using hList
  have hLen := setIndexIndicesFromFamily_length_le p
  have hOutLenN : (setIndexIndicesFromFamily p).length ≤ N :=
    hLen.trans hSetsLen
  have hQuadratic :
      (setIndexIndicesFromFamily p).length * (p.2.length + 2) ≤
        N * (N + 2) := by
    exact Nat.mul_le_mul hOutLenN (Nat.add_le_add_right hSetsLen 2)
  have hPoly : N * (N + 2) ≤ 3 * N ^ 2 + 10 := by
    nlinarith [sq_nonneg (N : Int)]
  exact hOutputSize.trans (hQuadratic.trans hPoly)

theorem setIndexIndicesFromFamily_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : setIndexInstructionInputEncodedType.Carrier =>
        setIndexInstructionInputEncodedType.inputSize p)
      (fun xs : List Nat => (EncodedType.list EncodedType.nat).inputSize xs)
      setIndexIndicesFromFamily :=
  PolynomialSizeBound.intro_with 2 3 10 setIndexIndicesFromFamily_inputSize_le

noncomputable def setIndexIndicesFromFamilyTMBackedMap :
    TMBackedCostedMap
      setIndexInstructionInputEncodedType
      (EncodedType.list EncodedType.nat)
      setIndexIndicesFromFamily where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      setIndexIndicesFromFamily_polynomialSizeBound
  tm_polytime := setIndexIndicesFromFamily_tm_polytime

end HittingSet
end Karp21
end ComplexityReduction
