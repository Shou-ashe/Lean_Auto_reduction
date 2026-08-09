/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem

/-!
Standard-axiom replacements for the three closed arithmetic proof leaves in
the structured Hitting Set verifier.  These theorems are deliberately kept at
the existing exact CR executable boundary; a later V2 checker can compose
them without importing a legacy `TMInNP` theorem.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace HittingSetStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.HittingSet

/-- Kernel-checked size of the `setHit` fold initial accumulator. -/
theorem setHitRunnerInit_inputSize_le_ten :
    setHitAccEncodedType.inputSize setHitRunnerInit ≤ 10 := by
  have hEmpty : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
    exact EncodedType.inputSize_list_nil EncodedType.nat
  simp [setHitAccEncodedType, setHitRunnerInit, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, hEmpty]

/-- Standard direct-TM proof for the `setHit` bounded fold. -/
theorem setHitFold_tm_polytime :
    TMPolyTimeMap setHitInstructionListEncodedType setHitAccEncodedType
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
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (setHitInstructionEncodedType.list.inputSize xs) =
          setHitInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    exact setHitRunnerInit_inputSize_le_ten.trans (Nat.le_add_left 10 _)
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

/-- Standard projection from the reconstructed `setHit` fold. -/
theorem setHitFromInstructions_tm_polytime :
    TMPolyTimeMap setHitInstructionListEncodedType EncodedType.bool setHitFromInstructions := by
  have hFound := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFound setHitFold_tm_polytime
  simpa [Function.comp, setHitFromInstructions, setHitAccEncodedType] using hComp

/-- Standard direct-TM evidence for the one-source-set hit checker. -/
theorem setHitBool_tm_polytime :
    TMPolyTimeMap setHitInstructionInputEncodedType EncodedType.bool setHitBool := by
  have hComp := TMPolyTimeMap.comp setHitFromInstructions_tm_polytime setHitInstructions_tm_polytime
  simpa [Function.comp, setHitBool] using hComp

/-- Kernel-checked size of the `allSetsHit` fold initial accumulator. -/
theorem allSetsHitRunnerInit_inputSize_le_ten :
    allSetsHitAccEncodedType.inputSize allSetsHitRunnerInit ≤ 10 := by
  have hEmpty : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
    exact EncodedType.inputSize_list_nil EncodedType.nat
  simp [allSetsHitAccEncodedType, allSetsHitRunnerInit, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, hEmpty]

/--
Standard direct-TM realization of the outer Hitting-Set fold step.  The sole
deviation from the legacy proof is its use of the reconstructed local
`setHitBool_tm_polytime` above.
-/
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
  have hPayloadHitting : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hSetHitInput : TMPolyTimeMap X setHitInstructionInputEncodedType
      (fun p : X.Carrier => (p.2.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hPayloadSet hHitting
  have hSetHit : TMPolyTimeMap X EncodedType.bool
      (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
        setHitBool (p.2.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setHitBool_tm_polytime hSetHitInput
    simpa [Function.comp, setHitInstructionInputEncodedType] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : (List Nat × Bool) × (Bool × (List Nat × List Nat)) =>
        (p.1.2, setHitBool (p.2.2.1, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOk hSetHit
  have hAnd : TMPolyTimeMap X EncodedType.bool
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
  have hBranchOnProduct : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
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

/-- Standard direct-TM proof for the `allSetsHit` bounded fold. -/
theorem allSetsHitFold_tm_polytime :
    TMPolyTimeMap allSetsHitInstructionListEncodedType allSetsHitAccEncodedType
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
    have hEval :
        (Polynomial.X + Polynomial.C 10).eval
            (allSetsHitInstructionEncodedType.list.inputSize xs) =
          allSetsHitInstructionEncodedType.list.inputSize xs + 10 := by
      simp [Polynomial.eval_add]
    rw [hEval]
    exact allSetsHitRunnerInit_inputSize_le_ten.trans (Nat.le_add_left 10 _)
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

/-- Standard projection from the reconstructed outer Hitting-Set fold. -/
theorem allSetsHitFromInstructions_tm_polytime :
    TMPolyTimeMap allSetsHitInstructionListEncodedType EncodedType.bool
      allSetsHitFromInstructions := by
  have hOk := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOk allSetsHitFold_tm_polytime
  simpa [Function.comp, allSetsHitFromInstructions, allSetsHitAccEncodedType] using hComp

/-- Standard direct-TM evidence for the every-set-hit Boolean checker. -/
theorem allSetsHitBool_tm_polytime :
    TMPolyTimeMap allSetsHitInstructionInputEncodedType EncodedType.bool allSetsHitBool := by
  have hComp := TMPolyTimeMap.comp allSetsHitFromInstructions_tm_polytime
    allSetsHitInstructions_tm_polytime
  simpa [Function.comp, allSetsHitBool] using hComp

/-- Standard direct-TM realization of the structured Hitting-Set checker. -/
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
  have hInstanceTuple : TMPolyTimeMap X hittingSetTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp hittingSetInputToTupleTMBackedMap.tm_polytime hInstance
    simpa [Function.comp, hittingSetInputToTuple, X] using hComp
  have hSystem : TMPolyTimeMap X setSystemStructuredEncodedType
      (fun p : X.Carrier => p.1.system) := by
    have hFst := TMPolyTimeMap.fst setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hInstanceTuple
    simpa [Function.comp, hittingSetTupleStructuredEncodedType, X] using hComp
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.k) := by
    have hSnd := TMPolyTimeMap.snd setSystemStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hInstanceTuple
    simpa [Function.comp, hittingSetTupleStructuredEncodedType, X] using hComp
  have hSystemTuple : TMPolyTimeMap X setSystemTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp setSystemInputToTupleTMBackedMap.tm_polytime hSystem
    simpa [Function.comp, setSystemInputToTuple, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.system.universeSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hSystemTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hCertLength : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.length) := by
    have hComp := TMPolyTimeMap.comp (listLengthTMBackedMap EncodedType.nat).tm_polytime hCert
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hLengthInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.length, p.1.k)) :=
    TMPolyTimeMap.prod_mk hCertLength hBudget
  have hLengthOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLeBool (p.2.length, p.1.k)) := by
    have hComp := TMPolyTimeMap.comp natLeBool_tm_polytime hLengthInput
    simpa [Function.comp] using hComp
  have hWithinInput : TMPolyTimeMap X boundedNatInstructionInputEncodedType
      (fun p : X.Carrier => (p.1.system.universeSize, p.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hCert
  have hWithin : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => boundedNatListBool (p.1.system.universeSize, p.2)) := by
    have hComp := TMPolyTimeMap.comp boundedNatListBool_tm_polytime hWithinInput
    simpa [Function.comp, boundedNatInstructionInputEncodedType] using hComp
  have hHitsInput : TMPolyTimeMap X allSetsHitInstructionInputEncodedType
      (fun p : X.Carrier => (p.1.system.sets, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hCert
  have hHits : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => allSetsHitBool (p.1.system.sets, p.2)) := by
    have hComp := TMPolyTimeMap.comp allSetsHitBool_tm_polytime hHitsInput
    simpa [Function.comp, allSetsHitInstructionInputEncodedType] using hComp
  have hTailInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (boundedNatListBool (p.1.system.universeSize, p.2),
          allSetsHitBool (p.1.system.sets, p.2))) :=
    TMPolyTimeMap.prod_mk hWithin hHits
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolAndPair
        (boundedNatListBool (p.1.system.universeSize, p.2),
          allSetsHitBool (p.1.system.sets, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp] using hComp
  have hAllInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (natLeBool (p.2.length, p.1.k), graphBoolAndPair
          (boundedNatListBool (p.1.system.universeSize, p.2),
            allSetsHitBool (p.1.system.sets, p.2)))) :=
    TMPolyTimeMap.prod_mk hLengthOK hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, hittingSetStructuredFiniteVerify, X] using hAll

/-- Standard replacement for the bounded unary-natural certificate-size lemma. -/
theorem boundedNatList_inputSize_le
    (bound : Nat) (xs : List Nat) (hBound : ∀ x ∈ xs, x < bound) :
    setStructuredEncodedType.inputSize xs ≤ xs.length * (bound + 1) := by
  induction xs with
  | nil =>
      have hNil : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
        exact EncodedType.inputSize_list_nil EncodedType.nat
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
            ≤ (bound + 1) + xs.length * (bound + 1) :=
              Nat.add_le_add hxSize hTail
        _ = (x :: xs).length * (bound + 1) := by
              simp
              ring_nf

#print axioms setHitFold_tm_polytime
#print axioms allSetsHitFold_tm_polytime
#print axioms hittingSetStructuredFiniteVerify_tm_polytime
#print axioms boundedNatList_inputSize_le

end HittingSetStandardTM
end Karp21
end Problems
end ComplexityReduction
