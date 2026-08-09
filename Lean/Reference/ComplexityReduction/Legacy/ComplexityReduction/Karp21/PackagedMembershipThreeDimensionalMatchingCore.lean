/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching.Part3
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured
3-Dimensional Matching.

The certificate is a list of selected triples.  The verifier checks that the
certificate has enough triples, that every certificate triple is a member of the
input triple family and lies inside the declared X/Y/Z bounds, and that no
coordinate is reused.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace ThreeDimensionalMatchingMembership

abbrev Triple := Nat × Nat × Nat

abbrev threeDMCertificateEncodedType : EncodedType :=
  tripleListStructuredEncodedType

def defaultTriple : Triple := (0, 0, 0)

abbrev tripleEqInputEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType tripleStructuredEncodedType

def tripleEqBool (p : Triple × Triple) : Bool :=
  graphBoolAndPair
    (decide (p.1.1 = p.2.1),
      graphBoolAndPair
        (decide (p.1.2.1 = p.2.2.1), decide (p.1.2.2 = p.2.2.2)))

theorem tripleEqBool_eq_true_iff (p : Triple × Triple) :
    tripleEqBool p = true ↔ p.1 = p.2 := by
  rcases p with ⟨a, b⟩
  rcases a with ⟨ax, ayz⟩
  rcases ayz with ⟨ay, az⟩
  rcases b with ⟨bx, byz⟩
  rcases byz with ⟨byy, bz⟩
  simp [tripleEqBool, graphBoolAndPair_eq_true_iff]

theorem tripleEqBool_tm_polytime :
    TMPolyTimeMap tripleEqInputEncodedType EncodedType.bool tripleEqBool := by
  let X := tripleEqInputEncodedType
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, tripleEqInputEncodedType] using
      TMPolyTimeMap.fst tripleStructuredEncodedType tripleStructuredEncodedType
  have hRight : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, tripleEqInputEncodedType] using
      TMPolyTimeMap.snd tripleStructuredEncodedType tripleStructuredEncodedType
  have hLeftX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hFst hLeft
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hLeftTail : TMPolyTimeMap X Pair (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hSnd hLeft
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hLeftY : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hLeftTail
    simpa [Function.comp, Pair, X] using hComp
  have hLeftZ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hLeftTail
    simpa [Function.comp, Pair, X] using hComp
  have hRightX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hFst hRight
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hRightTail : TMPolyTimeMap X Pair (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hSnd hRight
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hRightY : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hRightTail
    simpa [Function.comp, Pair, X] using hComp
  have hRightZ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRightTail
    simpa [Function.comp, Pair, X] using hComp
  have hXInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hLeftX hRightX
  have hYInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.1, p.2.2.1)) :=
    TMPolyTimeMap.prod_mk hLeftY hRightY
  have hZInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.2, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hLeftZ hRightZ
  have hX : TMPolyTimeMap X EncodedType.bool
      (fun p : Triple × Triple => decide (p.1.1 = p.2.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hXInput
    simpa [Function.comp, X] using hComp
  have hY : TMPolyTimeMap X EncodedType.bool
      (fun p : Triple × Triple => decide (p.1.2.1 = p.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hYInput
    simpa [Function.comp, X] using hComp
  have hZ : TMPolyTimeMap X EncodedType.bool
      (fun p : Triple × Triple => decide (p.1.2.2 = p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hZInput
    simpa [Function.comp, X] using hComp
  have hYZInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : Triple × Triple => (decide (p.1.2.1 = p.2.2.1),
        decide (p.1.2.2 = p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hY hZ
  have hYZ : TMPolyTimeMap X EncodedType.bool
      (fun p : Triple × Triple =>
        graphBoolAndPair
          (decide (p.1.2.1 = p.2.2.1), decide (p.1.2.2 = p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hYZInput
    simpa [Function.comp, X] using hComp
  have hAllInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : Triple × Triple =>
        (decide (p.1.1 = p.2.1),
          graphBoolAndPair
            (decide (p.1.2.1 = p.2.2.1), decide (p.1.2.2 = p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hX hYZ
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, tripleEqBool, X, tripleEqInputEncodedType] using hAll

abbrev tripleBoundsInputEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType tripleStructuredEncodedType

def tripleWithinBoundsForBounds (bounds t : Triple) : Prop :=
  t.1 < bounds.1 ∧ t.2.1 < bounds.2.1 ∧ t.2.2 < bounds.2.2

def tripleWithinBoundsBool (p : Triple × Triple) : Bool :=
  graphBoolAndPair
    (natLtBool (p.2.1, p.1.1),
      graphBoolAndPair
        (natLtBool (p.2.2.1, p.1.2.1), natLtBool (p.2.2.2, p.1.2.2)))

theorem tripleWithinBoundsBool_eq_true_iff (bounds t : Triple) :
    tripleWithinBoundsBool (bounds, t) = true ↔
      tripleWithinBoundsForBounds bounds t := by
  rw [tripleWithinBoundsBool, tripleWithinBoundsForBounds,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    natLtBool_eq_true_iff, natLtBool_eq_true_iff, natLtBool_eq_true_iff]

theorem tripleWithinBoundsForBounds_iff (I : ThreeDimensionalMatchingInput) (t : Triple) :
    tripleWithinBoundsForBounds (I.xSize, I.ySize, I.zSize) t ↔ TripleWithinBounds I t := by
  rfl

theorem tripleWithinBoundsBool_tm_polytime :
    TMPolyTimeMap tripleBoundsInputEncodedType EncodedType.bool tripleWithinBoundsBool := by
  let X := tripleBoundsInputEncodedType
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  have hBounds : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, tripleBoundsInputEncodedType] using
      TMPolyTimeMap.fst tripleStructuredEncodedType tripleStructuredEncodedType
  have hTriple : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, tripleBoundsInputEncodedType] using
      TMPolyTimeMap.snd tripleStructuredEncodedType tripleStructuredEncodedType
  have hBoundsX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hBoundsTail : TMPolyTimeMap X Pair (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hBoundsY : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hBoundsTail
    simpa [Function.comp, Pair, X] using hComp
  have hBoundsZ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hBoundsTail
    simpa [Function.comp, Pair, X] using hComp
  have hTripleX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hFst hTriple
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hTripleTail : TMPolyTimeMap X Pair (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Pair
    have hComp := TMPolyTimeMap.comp hSnd hTriple
    simpa [Function.comp, tripleStructuredEncodedType, Pair, X] using hComp
  have hTripleY : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTripleTail
    simpa [Function.comp, Pair, X] using hComp
  have hTripleZ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTripleTail
    simpa [Function.comp, Pair, X] using hComp
  have hXInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hTripleX hBoundsX
  have hYInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.2.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hTripleY hBoundsY
  have hZInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.2.2, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hTripleZ hBoundsZ
  have hX : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLtBool (p.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hXInput
    simpa [Function.comp, X] using hComp
  have hY : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLtBool (p.2.2.1, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hYInput
    simpa [Function.comp, X] using hComp
  have hZ : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natLtBool (p.2.2.2, p.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hZInput
    simpa [Function.comp, X] using hComp
  have hYZInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (natLtBool (p.2.2.1, p.1.2.1), natLtBool (p.2.2.2, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hY hZ
  have hYZ : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (natLtBool (p.2.2.1, p.1.2.1), natLtBool (p.2.2.2, p.1.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hYZInput
    simpa [Function.comp, X] using hComp
  have hAllInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (natLtBool (p.2.1, p.1.1),
          graphBoolAndPair
            (natLtBool (p.2.2.1, p.1.2.1), natLtBool (p.2.2.2, p.1.2.2)))) :=
    TMPolyTimeMap.prod_mk hX hYZ
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, tripleWithinBoundsBool, X, tripleBoundsInputEncodedType] using hAll

/-! ### Triple-list membership -/

abbrev tripleContainsAccEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType EncodedType.bool

abbrev tripleContainsInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType tripleStructuredEncodedType

abbrev tripleContainsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool tripleContainsInstructionPayloadEncodedType

abbrev tripleContainsInstructionListEncodedType : EncodedType :=
  EncodedType.list tripleContainsInstructionEncodedType

abbrev tripleContainsInputEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType tripleListStructuredEncodedType

def tripleContainsRunnerInit : Triple × Bool := (defaultTriple, false)

def tripleContainsInitInstruction (target : Triple) :
    tripleContainsInstructionEncodedType.Carrier :=
  (false, (target, defaultTriple))

def tripleContainsElementInstruction (t : Triple) :
    tripleContainsInstructionEncodedType.Carrier :=
  (true, (defaultTriple, t))

def tripleContainsInstructions (p : Triple × List Triple) :
    List tripleContainsInstructionEncodedType.Carrier :=
  tripleContainsInitInstruction p.1 :: p.2.map tripleContainsElementInstruction

def tripleContainsStep
    (p : tripleContainsAccEncodedType.Carrier × tripleContainsInstructionEncodedType.Carrier) :
    tripleContainsAccEncodedType.Carrier :=
  match p.2.1 with
  | true => (p.1.1, graphBoolOrPair (p.1.2, tripleEqBool (p.1.1, p.2.2.2)))
  | false => (p.2.2.1, false)

def tripleContainsFromInstructions
    (xs : List tripleContainsInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc x => tripleContainsStep (acc, x)) tripleContainsRunnerInit).2

def tripleContainsBool (p : Triple × List Triple) : Bool :=
  tripleContainsFromInstructions (tripleContainsInstructions p)

theorem tripleContainsElementInstructions_fold_iff
    (xs : List Triple) (target : Triple) (found : Bool) :
    ((xs.map tripleContainsElementInstruction).foldl
        (fun acc instr => tripleContainsStep (acc, instr)) (target, found)).2 = true ↔
      found = true ∨ target ∈ xs := by
  induction xs generalizing found with
  | nil =>
      cases found <;> simp
  | cons t ts ih =>
      rw [List.map_cons, List.foldl_cons]
      have hStep :
          tripleContainsStep ((target, found), tripleContainsElementInstruction t) =
            (target, graphBoolOrPair (found, tripleEqBool (target, t))) := by
        rfl
      rw [hStep]
      constructor
      · intro h
        rcases (ih (graphBoolOrPair (found, tripleEqBool (target, t)))).1 h with
          hFound | hTail
        · rcases (graphBoolOrPair_eq_true_iff _).1 hFound with hFound' | hEq
          · exact Or.inl hFound'
          · have ht : target = t := (tripleEqBool_eq_true_iff (target, t)).1 hEq
            exact Or.inr (by simp [ht])
        · exact Or.inr (by simp [hTail])
      · intro h
        apply (ih (graphBoolOrPair (found, tripleEqBool (target, t)))).2
        rcases h with hFound | hMem
        · exact Or.inl ((graphBoolOrPair_eq_true_iff _).2 (Or.inl hFound))
        · simp at hMem
          rcases hMem with hEq | hTail
          · exact Or.inl
              ((graphBoolOrPair_eq_true_iff _).2
                (Or.inr ((tripleEqBool_eq_true_iff (target, t)).2 hEq)))
          · exact Or.inr hTail

theorem tripleContainsBool_eq_true_iff (target : Triple) (xs : List Triple) :
    tripleContainsBool (target, xs) = true ↔ target ∈ xs := by
  change
    (((tripleContainsInitInstruction target :: xs.map tripleContainsElementInstruction).foldl
        (fun acc instr => tripleContainsStep (acc, instr)) tripleContainsRunnerInit).2 =
      true) ↔ target ∈ xs
  rw [List.foldl_cons]
  simpa [tripleContainsRunnerInit, tripleContainsInitInstruction, tripleContainsStep] using
    tripleContainsElementInstructions_fold_iff xs target false

theorem tripleContainsInitInstruction_tm_polytime :
    TMPolyTimeMap
      tripleStructuredEncodedType
      tripleContainsInstructionEncodedType
      tripleContainsInitInstruction := by
  have hFalse : TMPolyTimeMap tripleStructuredEncodedType EncodedType.bool
      (fun _ : Triple => false) :=
    TMPolyTimeMap.const tripleStructuredEncodedType EncodedType.bool false
  have hTarget : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType id :=
    TMPolyTimeMap.id tripleStructuredEncodedType
  have hDefault : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType
      (fun _ : Triple => defaultTriple) :=
    TMPolyTimeMap.const tripleStructuredEncodedType tripleStructuredEncodedType defaultTriple
  have hPayload := TMPolyTimeMap.prod_mk hTarget hDefault
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [tripleContainsInitInstruction, tripleContainsInstructionEncodedType,
    tripleContainsInstructionPayloadEncodedType] using hOut

theorem tripleContainsElementInstruction_tm_polytime :
    TMPolyTimeMap
      tripleStructuredEncodedType
      tripleContainsInstructionEncodedType
      tripleContainsElementInstruction := by
  have hTrue : TMPolyTimeMap tripleStructuredEncodedType EncodedType.bool
      (fun _ : Triple => true) :=
    TMPolyTimeMap.const tripleStructuredEncodedType EncodedType.bool true
  have hDefault : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType
      (fun _ : Triple => defaultTriple) :=
    TMPolyTimeMap.const tripleStructuredEncodedType tripleStructuredEncodedType defaultTriple
  have hTriple : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType id :=
    TMPolyTimeMap.id tripleStructuredEncodedType
  have hPayload := TMPolyTimeMap.prod_mk hDefault hTriple
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [tripleContainsElementInstruction, tripleContainsInstructionEncodedType,
    tripleContainsInstructionPayloadEncodedType] using hOut

theorem tripleContainsInstructions_tm_polytime :
    TMPolyTimeMap
      tripleContainsInputEncodedType
      tripleContainsInstructionListEncodedType
      tripleContainsInstructions := by
  let X := tripleContainsInputEncodedType
  have hTarget : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, tripleContainsInputEncodedType] using
      TMPolyTimeMap.fst tripleStructuredEncodedType tripleListStructuredEncodedType
  have hTriples : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, tripleContainsInputEncodedType] using
      TMPolyTimeMap.snd tripleStructuredEncodedType tripleListStructuredEncodedType
  have hInit : TMPolyTimeMap X tripleContainsInstructionEncodedType
      (fun p : X.Carrier => tripleContainsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp tripleContainsInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hInitSingleton : TMPolyTimeMap X tripleContainsInstructionListEncodedType
      (fun p : X.Carrier => [tripleContainsInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton tripleContainsInstructionEncodedType) hInit
    simpa [Function.comp, tripleContainsInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X tripleContainsInstructionListEncodedType
      (fun p : X.Carrier => p.2.map tripleContainsElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map tripleContainsElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hTriples
    simpa [Function.comp, tripleContainsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod tripleContainsInstructionListEncodedType
          tripleContainsInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([tripleContainsInitInstruction p.1], p.2.map tripleContainsElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append tripleContainsInstructionEncodedType) hAppendInput
  simpa [Function.comp, tripleContainsInstructions, tripleContainsInstructionListEncodedType, X]
    using hOut

theorem tripleContainsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod tripleContainsAccEncodedType tripleContainsInstructionEncodedType)
      tripleContainsAccEncodedType
      tripleContainsStep := by
  let X := EncodedType.prod tripleContainsAccEncodedType tripleContainsInstructionEncodedType
  have hAcc : TMPolyTimeMap X tripleContainsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst tripleContainsAccEncodedType tripleContainsInstructionEncodedType
  have hInstr : TMPolyTimeMap X tripleContainsInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd tripleContainsAccEncodedType tripleContainsInstructionEncodedType
  have hTarget : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst tripleStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, tripleContainsAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd tripleStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, tripleContainsAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool tripleContainsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, tripleContainsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X tripleContainsInstructionPayloadEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool tripleContainsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, tripleContainsInstructionEncodedType, X] using hComp
  have hInitTarget : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst tripleStructuredEncodedType tripleStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, tripleContainsInstructionPayloadEncodedType, X] using hComp
  have hElement : TMPolyTimeMap X tripleStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd tripleStructuredEncodedType tripleStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, tripleContainsInstructionPayloadEncodedType, X] using hComp
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInitOut : TMPolyTimeMap X tripleContainsAccEncodedType
      (fun p : X.Carrier => (p.2.2.1, false)) :=
    TMPolyTimeMap.prod_mk hInitTarget hFalse
  have hEqInput : TMPolyTimeMap X tripleEqInputEncodedType
      (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hTarget hElement
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => tripleEqBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp tripleEqBool_tm_polytime hEqInput
    simpa [Function.comp, tripleEqInputEncodedType, X] using hComp
  have hOrInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (p.1.2, tripleEqBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hFound hEq
  have hOr : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolOrPair (p.1.2, tripleEqBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
    simpa [Function.comp, X] using hComp
  have hScanOut : TMPolyTimeMap X tripleContainsAccEncodedType
      (fun p : X.Carrier => (p.1.1, graphBoolOrPair
        (p.1.2, tripleEqBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hTarget hOr
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) tripleContainsAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1, graphBoolOrPair
                (p.2.1.2, tripleEqBool (p.2.1.1, p.2.2.2.2)))
          | false => (p.2.2.2.1, false)) :=
    graphBoolProduct_dispatch_tm_polytime X tripleContainsAccEncodedType
      (fFalse := fun p : X.Carrier => (p.2.2.1, false))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, graphBoolOrPair (p.1.2, tripleEqBool (p.1.1, p.2.2.2))))
      hInitOut hScanOut
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  simpa [Function.comp, tripleContainsStep] using hOut

theorem tripleContainsStep_inputSize_le
    (source : tripleContainsInstructionListEncodedType.Carrier)
    (acc : tripleContainsAccEncodedType.Carrier)
    (instr : tripleContainsInstructionEncodedType.Carrier)
    (hAcc :
      tripleContainsAccEncodedType.inputSize acc ≤
        tripleContainsInstructionListEncodedType.inputSize source + 200)
    (hInstr :
      tripleContainsInstructionEncodedType.inputSize instr ≤
        tripleContainsInstructionListEncodedType.inputSize source) :
    tripleContainsAccEncodedType.inputSize (tripleContainsStep (acc, instr)) ≤
      tripleContainsInstructionListEncodedType.inputSize source + 200 := by
  rcases acc with ⟨target, found⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨initTarget, elem⟩
  cases tag
  · have hLocal :
        tripleContainsAccEncodedType.inputSize (initTarget, false) ≤
          tripleContainsInstructionEncodedType.inputSize (false, (initTarget, elem)) + 200 := by
      simp [tripleContainsAccEncodedType, tripleContainsInstructionEncodedType,
        tripleContainsInstructionPayloadEncodedType, tripleStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat]
      omega
    simpa [tripleContainsStep] using hLocal.trans (Nat.add_le_add_right hInstr 200)
  · have hLocal :
        tripleContainsAccEncodedType.inputSize
            (target, graphBoolOrPair (found, tripleEqBool (target, elem))) ≤
          tripleContainsAccEncodedType.inputSize (target, found) := by
      simp [tripleContainsAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool]
    simpa [tripleContainsStep] using hLocal.trans hAcc

theorem tripleContainsFold_tm_polytime :
    TMPolyTimeMap
      tripleContainsInstructionListEncodedType
      tripleContainsAccEncodedType
      (fun xs : tripleContainsInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => tripleContainsStep (acc, x)) tripleContainsRunnerInit) := by
  rcases tripleContainsStep_tm_polytime with ⟨hStep⟩
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C 200
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      tripleContainsInstructionEncodedType tripleContainsAccEncodedType
      tripleContainsStep tripleContainsRunnerInit hStep bound ?_ ?_
  · intro xs
    change tripleContainsAccEncodedType.inputSize tripleContainsRunnerInit ≤
      (Polynomial.X + Polynomial.C 200).eval
        (tripleContainsInstructionEncodedType.list.inputSize xs)
    have hInit : tripleContainsAccEncodedType.inputSize tripleContainsRunnerInit ≤ 200 := by
      simp [tripleContainsRunnerInit, defaultTriple, tripleContainsAccEncodedType,
        tripleStructuredEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_nat]
    exact hInit.trans (by
      simp [Polynomial.eval_add])
  · intro source acc instr hAcc hInstr
    have hAcc' :
        tripleContainsAccEncodedType.inputSize acc ≤
          tripleContainsInstructionListEncodedType.inputSize source + 200 := by
      simp [tripleContainsAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, tripleContainsInstructionListEncodedType,
        bound, Polynomial.eval_add] at hAcc ⊢
      omega
    have hInstr' :
        tripleContainsInstructionEncodedType.inputSize instr ≤
          tripleContainsInstructionListEncodedType.inputSize source := by
      simpa [tripleContainsInstructionListEncodedType] using hInstr
    have hStepBound := tripleContainsStep_inputSize_le source acc instr hAcc' hInstr'
    change tripleContainsAccEncodedType.inputSize (tripleContainsStep (acc, instr)) ≤
      (Polynomial.X + Polynomial.C 200).eval
        ((EncodedType.list tripleContainsInstructionEncodedType).inputSize source)
    simp [tripleContainsAccEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_bool, tripleContainsInstructionListEncodedType,
      Polynomial.eval_add] at hStepBound ⊢
    omega

theorem tripleContainsFromInstructions_tm_polytime :
    TMPolyTimeMap
      tripleContainsInstructionListEncodedType
      EncodedType.bool
      tripleContainsFromInstructions := by
  have hFold := tripleContainsFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd tripleStructuredEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, tripleContainsFromInstructions, tripleContainsAccEncodedType] using hComp

theorem tripleContainsBool_tm_polytime :
    TMPolyTimeMap
      tripleContainsInputEncodedType
      EncodedType.bool
      tripleContainsBool := by
  have hComp := TMPolyTimeMap.comp tripleContainsFromInstructions_tm_polytime
    tripleContainsInstructions_tm_polytime
  simpa [Function.comp, tripleContainsBool] using hComp

/-! ### Matching-certificate scan -/

abbrev matchingScanSeenEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType
    (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)

abbrev matchingScanAccEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType
    (EncodedType.prod tripleListStructuredEncodedType
      (EncodedType.prod matchingScanSeenEncodedType EncodedType.bool))

abbrev matchingScanPayloadEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType
    (EncodedType.prod tripleListStructuredEncodedType tripleStructuredEncodedType)

abbrev matchingScanInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool matchingScanPayloadEncodedType

abbrev matchingScanInstructionListEncodedType : EncodedType :=
  EncodedType.list matchingScanInstructionEncodedType

abbrev matchingScanInputEncodedType : EncodedType :=
  EncodedType.prod tripleStructuredEncodedType
    (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)

def matchingScanRunnerInit : matchingScanAccEncodedType.Carrier :=
  (defaultTriple, ([], (([], ([], [])), false)))

def matchingScanInitInstruction (bounds : Triple) (source : List Triple) :
    matchingScanInstructionEncodedType.Carrier :=
  (false, (bounds, (source, defaultTriple)))

def matchingScanTripleInstruction (t : Triple) :
    matchingScanInstructionEncodedType.Carrier :=
  (true, (defaultTriple, ([], t)))

def matchingScanInstructions
    (p : Triple × (List Triple × List Triple)) :
    List matchingScanInstructionEncodedType.Carrier :=
  matchingScanInitInstruction p.1 p.2.1 :: p.2.2.map matchingScanTripleInstruction

def matchingLocalFreshBool (seen : matchingScanSeenEncodedType.Carrier) (t : Triple) : Bool :=
  graphBoolAndPair
    (Bool.not (HittingSet.setContainsBool (t.1, seen.1)),
      graphBoolAndPair
        (Bool.not (HittingSet.setContainsBool (t.2.1, seen.2.1)),
          Bool.not (HittingSet.setContainsBool (t.2.2, seen.2.2))))

def matchingLocalOKBool
    (bounds : Triple) (source : List Triple)
    (seen : matchingScanSeenEncodedType.Carrier) (t : Triple) : Bool :=
  graphBoolAndPair
    (tripleWithinBoundsBool (bounds, t),
      graphBoolAndPair
        (tripleContainsBool (t, source), matchingLocalFreshBool seen t))

def matchingScanElementStep
    (acc : matchingScanAccEncodedType.Carrier) (t : Triple) :
    matchingScanAccEncodedType.Carrier :=
  let bounds := acc.1
  let source := acc.2.1
  let seen := acc.2.2.1
  let ok := acc.2.2.2
  (bounds,
    (source,
      ((t.1 :: seen.1, (t.2.1 :: seen.2.1, t.2.2 :: seen.2.2)),
        graphBoolAndPair (ok, matchingLocalOKBool bounds source seen t))))

def matchingScanStep
    (p : matchingScanAccEncodedType.Carrier × matchingScanInstructionEncodedType.Carrier) :
    matchingScanAccEncodedType.Carrier :=
  match p.2.1 with
  | true => matchingScanElementStep p.1 p.2.2.2.2
  | false => (p.2.2.1, (p.2.2.2.1, (([], ([], [])), true)))

def matchingScanFromInstructions
    (xs : List matchingScanInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc x => matchingScanStep (acc, x)) matchingScanRunnerInit).2.2.2

def matchingScanBool (p : Triple × (List Triple × List Triple)) : Bool :=
  matchingScanFromInstructions (matchingScanInstructions p)

def MatchingFreshOK
    (bounds : Triple) (source : List Triple)
    (seenX seenY seenZ : List Nat) : List Triple → Prop
  | [] => True
  | t :: ts =>
      tripleWithinBoundsForBounds bounds t ∧
        t ∈ source ∧
        t.1 ∉ seenX ∧
        t.2.1 ∉ seenY ∧
        t.2.2 ∉ seenZ ∧
        MatchingFreshOK bounds source
          (t.1 :: seenX) (t.2.1 :: seenY) (t.2.2 :: seenZ) ts

theorem matchingLocalFreshBool_eq_true_iff
    (seen : List Nat × (List Nat × List Nat)) (t : Triple) :
    matchingLocalFreshBool seen t = true ↔
      t.1 ∉ seen.1 ∧ t.2.1 ∉ seen.2.1 ∧ t.2.2 ∉ seen.2.2 := by
  rcases seen with ⟨seenX, seenYZ⟩
  rcases seenYZ with ⟨seenY, seenZ⟩
  rw [matchingLocalFreshBool, graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff]
  simp [HittingSet.setContainsBool_eq_decide]

theorem matchingLocalOKBool_eq_true_iff
    (bounds : Triple) (source : List Triple)
    (seen : List Nat × (List Nat × List Nat)) (t : Triple) :
    matchingLocalOKBool bounds source seen t = true ↔
      tripleWithinBoundsForBounds bounds t ∧ t ∈ source ∧
        t.1 ∉ seen.1 ∧ t.2.1 ∉ seen.2.1 ∧ t.2.2 ∉ seen.2.2 := by
  rw [matchingLocalOKBool, graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    tripleWithinBoundsBool_eq_true_iff, tripleContainsBool_eq_true_iff,
    matchingLocalFreshBool_eq_true_iff]

theorem matchingScanElementInstructions_fold_iff
    (xs : List Triple) (bounds : Triple) (source : List Triple)
    (seen : List Nat × (List Nat × List Nat)) (ok : Bool) :
    (((xs.map matchingScanTripleInstruction).foldl
        (fun acc instr => matchingScanStep (acc, instr))
        (bounds, (source, (seen, ok)))).2.2.2 = true) ↔
      ok = true ∧ MatchingFreshOK bounds source seen.1 seen.2.1 seen.2.2 xs := by
  induction xs generalizing seen ok with
  | nil =>
      cases ok <;> simp [MatchingFreshOK]
  | cons t ts ih =>
      rw [List.map_cons, List.foldl_cons]
      have hStep :
          matchingScanStep ((bounds, (source, (seen, ok))), matchingScanTripleInstruction t) =
            matchingScanElementStep (bounds, (source, (seen, ok))) t := by
        rfl
      rw [hStep]
      simp only [matchingScanElementStep]
      rw [ih]
      simp [MatchingFreshOK, graphBoolAndPair_eq_true_iff, matchingLocalOKBool_eq_true_iff,
        and_assoc]
      tauto

theorem matchingScanBool_eq_true_iff
    (bounds : Triple) (source cert : List Triple) :
    matchingScanBool (bounds, (source, cert)) = true ↔
      MatchingFreshOK bounds source [] [] [] cert := by
  change
    (((matchingScanInitInstruction bounds source ::
      cert.map matchingScanTripleInstruction).foldl
        (fun acc instr => matchingScanStep (acc, instr)) matchingScanRunnerInit).2.2.2 =
      true) ↔ _
  rw [List.foldl_cons]
  simpa [matchingScanRunnerInit, matchingScanInitInstruction, matchingScanStep] using
    matchingScanElementInstructions_fold_iff cert bounds source ([], ([], [])) true

theorem MatchingFreshOK.mem_bounds
    {bounds : Triple} {source : List Triple} {seenX seenY seenZ : List Nat}
    {xs : List Triple}
    (h : MatchingFreshOK bounds source seenX seenY seenZ xs) :
    ∀ t ∈ xs, t ∈ source ∧ tripleWithinBoundsForBounds bounds t := by
  induction xs generalizing seenX seenY seenZ with
  | nil =>
      simp
  | cons t ts ih =>
      simp [MatchingFreshOK] at h
      rcases h with ⟨hBounds, hMem, _hx, _hy, _hz, hTail⟩
      intro u hu
      simp at hu
      rcases hu with rfl | hu
      · exact ⟨hMem, hBounds⟩
      · exact ih hTail u hu

theorem MatchingFreshOK.seen_not_mem
    {bounds : Triple} {source : List Triple} {seenX seenY seenZ : List Nat}
    {xs : List Triple}
    (h : MatchingFreshOK bounds source seenX seenY seenZ xs) :
    (∀ x ∈ seenX, x ∉ xs.map fun t => t.1) ∧
      (∀ y ∈ seenY, y ∉ xs.map fun t => t.2.1) ∧
      (∀ z ∈ seenZ, z ∉ xs.map fun t => t.2.2) := by
  induction xs generalizing seenX seenY seenZ with
  | nil =>
      simp
  | cons t ts ih =>
      simp [MatchingFreshOK] at h
      rcases h with ⟨_hBounds, _hMem, hxFresh, hyFresh, hzFresh, hTail⟩
      rcases ih hTail with ⟨hxTail, hyTail, hzTail⟩
      refine ⟨?_, ?_, ?_⟩
      · intro x hx hmem
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · exact hxFresh (by simpa [hEq] using hx)
        · exact hxTail x (by simp [hx]) hmem
      · intro y hy hmem
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · exact hyFresh (by simpa [hEq] using hy)
        · exact hyTail y (by simp [hy]) hmem
      · intro z hz hmem
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with hEq | hmem
        · exact hzFresh (by simpa [hEq] using hz)
        · exact hzTail z (by simp [hz]) hmem

theorem MatchingFreshOK.projections_nodup
    {bounds : Triple} {source : List Triple} {seenX seenY seenZ : List Nat}
    {xs : List Triple}
    (h : MatchingFreshOK bounds source seenX seenY seenZ xs) :
    (xs.map fun t => t.1).Nodup ∧
      (xs.map fun t => t.2.1).Nodup ∧
      (xs.map fun t => t.2.2).Nodup := by
  induction xs generalizing seenX seenY seenZ with
  | nil =>
      simp
  | cons t ts ih =>
      simp [MatchingFreshOK] at h
      rcases h with ⟨_hBounds, _hMem, hxFresh, hyFresh, hzFresh, hTail⟩
      rcases ih hTail with ⟨hx, hy, hz⟩
      rcases MatchingFreshOK.seen_not_mem hTail with ⟨hxSeenTail, hySeenTail, hzSeenTail⟩
      refine ⟨?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨hxSeenTail t.1 (by simp), hx⟩
      · exact List.nodup_cons.mpr ⟨hySeenTail t.2.1 (by simp), hy⟩
      · exact List.nodup_cons.mpr ⟨hzSeenTail t.2.2 (by simp), hz⟩

theorem MatchingFreshOK.of_props_with_seen
    {bounds : Triple} {source xs : List Triple} {seenX seenY seenZ : List Nat}
    (hMemBounds : ∀ t ∈ xs, t ∈ source ∧ tripleWithinBoundsForBounds bounds t)
    (hxSeen : ∀ x ∈ seenX, x ∉ xs.map fun t => t.1)
    (hySeen : ∀ y ∈ seenY, y ∉ xs.map fun t => t.2.1)
    (hzSeen : ∀ z ∈ seenZ, z ∉ xs.map fun t => t.2.2)
    (hx : (xs.map fun t => t.1).Nodup)
    (hy : (xs.map fun t => t.2.1).Nodup)
    (hz : (xs.map fun t => t.2.2).Nodup) :
    MatchingFreshOK bounds source seenX seenY seenZ xs := by
  induction xs generalizing seenX seenY seenZ with
  | nil =>
      simp [MatchingFreshOK]
  | cons t ts ih =>
      have hHead := hMemBounds t (by simp)
      have hTail :
          ∀ u ∈ ts, u ∈ source ∧ tripleWithinBoundsForBounds bounds u := by
        intro u hu
        exact hMemBounds u (by simp [hu])
      have hxCons : (t.1 :: ts.map fun u => u.1).Nodup := by simpa using hx
      have hyCons : (t.2.1 :: ts.map fun u => u.2.1).Nodup := by simpa using hy
      have hzCons : (t.2.2 :: ts.map fun u => u.2.2).Nodup := by simpa using hz
      rcases List.nodup_cons.mp hxCons with ⟨hxFreshTail, hxTail⟩
      rcases List.nodup_cons.mp hyCons with ⟨hyFreshTail, hyTail⟩
      rcases List.nodup_cons.mp hzCons with ⟨hzFreshTail, hzTail⟩
      have hxFreshSeen : t.1 ∉ seenX := by
        intro hmem
        exact hxSeen t.1 hmem (by simp)
      have hyFreshSeen : t.2.1 ∉ seenY := by
        intro hmem
        exact hySeen t.2.1 hmem (by simp)
      have hzFreshSeen : t.2.2 ∉ seenZ := by
        intro hmem
        exact hzSeen t.2.2 hmem (by simp)
      have hxSeenTail : ∀ x ∈ t.1 :: seenX, x ∉ ts.map fun u => u.1 := by
        intro x hxmem hmem
        simp at hxmem
        rcases hxmem with rfl | hxmem
        · exact hxFreshTail hmem
        · exact hxSeen x hxmem (by simp [hmem])
      have hySeenTail : ∀ y ∈ t.2.1 :: seenY, y ∉ ts.map fun u => u.2.1 := by
        intro y hymem hmem
        simp at hymem
        rcases hymem with rfl | hymem
        · exact hyFreshTail hmem
        · exact hySeen y hymem (by simp [hmem])
      have hzSeenTail : ∀ z ∈ t.2.2 :: seenZ, z ∉ ts.map fun u => u.2.2 := by
        intro z hzmem hmem
        simp at hzmem
        rcases hzmem with rfl | hzmem
        · exact hzFreshTail hmem
        · exact hzSeen z hzmem (by simp [hmem])
      simp [MatchingFreshOK, hHead.2, hHead.1, hxFreshSeen, hyFreshSeen, hzFreshSeen,
        ih hTail hxSeenTail hySeenTail hzSeenTail hxTail hyTail hzTail]

theorem MatchingFreshOK.of_props
    {bounds : Triple} {source xs : List Triple}
    (hMemBounds : ∀ t ∈ xs, t ∈ source ∧ tripleWithinBoundsForBounds bounds t)
    (hx : (xs.map fun t => t.1).Nodup)
    (hy : (xs.map fun t => t.2.1).Nodup)
    (hz : (xs.map fun t => t.2.2).Nodup) :
    MatchingFreshOK bounds source [] [] [] xs := by
  exact MatchingFreshOK.of_props_with_seen hMemBounds (by simp) (by simp) (by simp)
    hx hy hz

theorem matchingScanInstructions_tm_polytime :
    TMPolyTimeMap
      matchingScanInputEncodedType
      matchingScanInstructionListEncodedType
      matchingScanInstructions := by
  let X := matchingScanInputEncodedType
  have hBounds : TMPolyTimeMap X tripleStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, matchingScanInputEncodedType] using
      TMPolyTimeMap.fst tripleStructuredEncodedType
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
  have hTail : TMPolyTimeMap X
      (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
      (fun p : X.Carrier => p.2) := by
    simpa [X, matchingScanInputEncodedType] using
      TMPolyTimeMap.snd tripleStructuredEncodedType
        (EncodedType.prod tripleListStructuredEncodedType tripleListStructuredEncodedType)
  have hSource : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst tripleListStructuredEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hCert : TMPolyTimeMap X tripleListStructuredEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd tripleListStructuredEncodedType tripleListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hPayload : TMPolyTimeMap X matchingScanPayloadEncodedType
      (fun p : X.Carrier => (p.1, (p.2.1, defaultTriple))) := by
    have hDefault : TMPolyTimeMap X tripleStructuredEncodedType
        (fun _ : X.Carrier => defaultTriple) :=
      TMPolyTimeMap.const X tripleStructuredEncodedType defaultTriple
    have hTailPayload := TMPolyTimeMap.prod_mk hSource hDefault
    exact TMPolyTimeMap.prod_mk hBounds hTailPayload
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInit : TMPolyTimeMap X matchingScanInstructionEncodedType
      (fun p : X.Carrier => matchingScanInitInstruction p.1 p.2.1) := by
    have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
    simpa [matchingScanInitInstruction, matchingScanInstructionEncodedType,
      matchingScanPayloadEncodedType] using hOut
  have hInitSingleton : TMPolyTimeMap X matchingScanInstructionListEncodedType
      (fun p : X.Carrier => [matchingScanInitInstruction p.1 p.2.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton matchingScanInstructionEncodedType) hInit
    simpa [Function.comp, matchingScanInstructionListEncodedType, X] using hComp
  have hElements : TMPolyTimeMap X matchingScanInstructionListEncodedType
      (fun p : X.Carrier => p.2.2.map matchingScanTripleInstruction) := by
    have hMap : TMPolyTimeMap tripleListStructuredEncodedType matchingScanInstructionListEncodedType
        (fun xs : List Triple => xs.map matchingScanTripleInstruction) := by
      have hElem : TMPolyTimeMap tripleStructuredEncodedType matchingScanInstructionEncodedType
          matchingScanTripleInstruction := by
        have hTrue : TMPolyTimeMap tripleStructuredEncodedType EncodedType.bool
            (fun _ : Triple => true) :=
          TMPolyTimeMap.const tripleStructuredEncodedType EncodedType.bool true
        have hDefault : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType
            (fun _ : Triple => defaultTriple) :=
          TMPolyTimeMap.const tripleStructuredEncodedType tripleStructuredEncodedType defaultTriple
        have hEmpty : TMPolyTimeMap tripleStructuredEncodedType tripleListStructuredEncodedType
            (fun _ : Triple => ([] : List Triple)) :=
          TMPolyTimeMap.const tripleStructuredEncodedType tripleListStructuredEncodedType []
        have hTriple : TMPolyTimeMap tripleStructuredEncodedType tripleStructuredEncodedType id :=
          TMPolyTimeMap.id tripleStructuredEncodedType
        have hTailPayload := TMPolyTimeMap.prod_mk hEmpty hTriple
        have hPayload := TMPolyTimeMap.prod_mk hDefault hTailPayload
        have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
        simpa [matchingScanTripleInstruction, matchingScanInstructionEncodedType,
          matchingScanPayloadEncodedType] using hOut
      simpa [tripleListStructuredEncodedType, matchingScanInstructionListEncodedType] using
        TMPolyTimeMap.list_map hElem
    have hComp := TMPolyTimeMap.comp hMap hCert
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod matchingScanInstructionListEncodedType
          matchingScanInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([matchingScanInitInstruction p.1 p.2.1],
            p.2.2.map matchingScanTripleInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append matchingScanInstructionEncodedType) hAppendInput
  simpa [Function.comp, matchingScanInstructions, matchingScanInstructionListEncodedType, X]
    using hOut

end ThreeDimensionalMatchingMembership
end Karp21
end ComplexityReduction
