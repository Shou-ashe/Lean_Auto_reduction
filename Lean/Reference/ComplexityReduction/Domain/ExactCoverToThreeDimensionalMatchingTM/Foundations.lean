/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.SetSystemMembershipPairs
import ComplexityReduction.Program.ContextListAll
import ComplexityReduction.Program.ContextListAny
import ComplexityReduction.Program.List
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Support
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching.Part1

/-!
Standard direct-TM foundations for the compact Exact-Cover-to-3DM map.

The legacy construction is mathematically correct, but its injection chooses a
family position with `Nat.find` and its cyclic successor is written with
`List.idxOf` and `%`.  This module supplies extensionally equal executable
forms assembled solely from checked unary-TM scans, bounded support filters,
list lookup, and typed list combinators.  It deliberately stops before triple
or target-instance assembly.
-/

namespace ComplexityReduction
namespace Domain
namespace ExactCoverToThreeDimensionalMatchingTM
namespace Foundations

open ComplexityReduction.Combinatorics
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ThreeDimensionalMatching

abbrev natListEncodedType : EncodedType := EncodedType.list EncodedType.nat

abbrev supportInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType setStructuredEncodedType

abbrev elementInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType EncodedType.nat

abbrev familyScanInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

/-! ### Exact structured source projections -/

theorem exactCoverUniverseSize_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.nat
      (fun input : ExactCoverInput => input.system.universeSize) :=
  Karp21.SteinerTree.exactCoverUniverseSize_tm_polytime

theorem exactCoverSets_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType setFamilyStructuredEncodedType
      (fun input : ExactCoverInput => input.system.sets) :=
  Karp21.SteinerTree.exactCoverSets_tm_polytime

/-- Public executable source-universe projection. -/
def universeSizeExecutable (input : ExactCoverInput) : Nat :=
  input.system.universeSize

@[simp] theorem universeSizeExecutable_eq (I : ExactCoverInput) :
    universeSizeExecutable I = I.system.universeSize :=
  rfl

theorem universeSizeExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.nat
      universeSizeExecutable :=
  exactCoverUniverseSize_tmPolyTime

/-- Public executable source-family length projection. -/
def setCountExecutable (input : ExactCoverInput) : Nat :=
  input.system.sets.length

@[simp] theorem setCountExecutable_eq (I : ExactCoverInput) :
    setCountExecutable I = I.system.sets.length :=
  rfl

theorem setCountExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.nat
      setCountExecutable :=
  Karp21.SteinerTree.exactCoverSetsLength_tm_polytime

/-- Public executable coordinate bound of the compact construction. -/
def coordBoundExecutable (input : ExactCoverInput) : Nat :=
  setCountExecutable input * universeSizeExecutable input

theorem coordBoundExecutable_eq_legacy (I : ExactCoverInput) :
    coordBoundExecutable I = compactCoordBound I :=
  rfl

theorem coordBoundExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.nat
      coordBoundExecutable := by
  have packed : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput =>
        (setCountExecutable input, universeSizeExecutable input)) :=
    TMPolyTimeMap.prod_mk setCountExecutable_tmPolyTime
      universeSizeExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime packed
  simpa [coordBoundExecutable, Function.comp] using composed

/-- Total source-set lookup with the same empty fallback as the legacy map. -/
def sourceSetAtExecutable (input : ExactCoverInput × Nat) : List Nat :=
  input.1.system.sets.getD input.2 []

theorem sourceSetAtExecutable_eq_legacy (I : ExactCoverInput) (j : Nat) :
    sourceSetAtExecutable (I, j) = compactSourceSetAt I j :=
  rfl

theorem sourceSetAtExecutable_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType setStructuredEncodedType
      sourceSetAtExecutable := by
  let X := elementInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have hIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1.system.sets) := by
    have composed := TMPolyTimeMap.comp exactCoverSets_tmPolyTime hSource
    simpa [Function.comp, X] using composed
  have packed : TMPolyTimeMap X
      (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
      (fun input : ExactCoverInput × Nat => (input.1.system.sets, input.2)) :=
    TMPolyTimeMap.prod_mk hSets hIndex
  have composed := TMPolyTimeMap.comp
    (Karp21.EncodedListLookup.getD_tm_polytime setStructuredEncodedType
      ([] : List Nat)) packed
  simpa [sourceSetAtExecutable, Karp21.EncodedListLookup.getD,
    Function.comp, setFamilyStructuredEncodedType, X] using composed

/-! ### Bounded support -/

/-- Executable bounded support of one source set. -/
def compactSupportExecutable (input : ExactCoverInput × List Nat) : List Nat :=
  Karp21.SteinerTree.compactSupportExecutable
    (input.1.system.universeSize, input.2)

theorem compactSupportExecutable_eq_legacy (I : ExactCoverInput) (S : List Nat) :
    compactSupportExecutable (I, S) = compactSupport I S := by
  exact Karp21.SteinerTree.compactSupportExecutable_eq_compactSupport I S

theorem compactSupportExecutable_tmPolyTime :
    TMPolyTimeMap supportInputEncodedType natListEncodedType compactSupportExecutable := by
  let X := supportInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × List Nat => input.1) := by
    simpa [X, supportInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType
      (fun input : ExactCoverInput × List Nat => input.2) := by
    simpa [X, supportInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType setStructuredEncodedType
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × List Nat => input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp exactCoverUniverseSize_tmPolyTime hSource
    simpa [Function.comp, X] using composed
  have packed : TMPolyTimeMap X Karp21.SteinerTree.compactSupportInputEncodedType
      (fun input : ExactCoverInput × List Nat =>
        (input.1.system.universeSize, input.2)) :=
    TMPolyTimeMap.prod_mk hUniverse hSet
  have composed := TMPolyTimeMap.comp
    Karp21.SteinerTree.compactSupportExecutable_tm_polytime packed
  simpa [compactSupportExecutable, Function.comp, natListEncodedType, X] using composed

/-! ### First containing family position -/

/-- All family positions containing the requested element. -/
def containingSetIndicesExecutable (input : ExactCoverInput × Nat) : List Nat :=
  Karp21.HittingSet.setIndexIndicesFromFamily
    (input.2, input.1.system.sets)

theorem containingSetIndicesExecutable_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType natListEncodedType
      containingSetIndicesExecutable := by
  let X := elementInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1.system.sets) := by
    have composed := TMPolyTimeMap.comp exactCoverSets_tmPolyTime hSource
    simpa [Function.comp, X] using composed
  have packed : TMPolyTimeMap X familyScanInputEncodedType
      (fun input : ExactCoverInput × Nat => (input.2, input.1.system.sets)) :=
    TMPolyTimeMap.prod_mk hElement hSets
  have composed := TMPolyTimeMap.comp
    Karp21.HittingSet.setIndexIndicesFromFamily_tm_polytime packed
  simpa [containingSetIndicesExecutable, Function.comp, familyScanInputEncodedType,
    Karp21.HittingSet.setIndexInstructionInputEncodedType, natListEncodedType, X] using composed

/-- The first scan result, with zero as the total no-result value. -/
def firstContainingSetIndexRaw (input : ExactCoverInput × Nat) : Nat :=
  (containingSetIndicesExecutable input).getD 0 0

theorem firstContainingSetIndexRaw_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.nat
      firstContainingSetIndexRaw := by
  let X := elementInputEncodedType
  have indices := containingSetIndicesExecutable_tmPolyTime
  have zero : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  have lookupInput :
      TMPolyTimeMap X (EncodedType.prod natListEncodedType EncodedType.nat)
        (fun input : X.Carrier => (containingSetIndicesExecutable input, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk indices zero
  have composed := TMPolyTimeMap.comp
    (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat)) lookupInput
  simpa [firstContainingSetIndexRaw, Karp21.EncodedListLookup.getD,
    Function.comp, natListEncodedType, X] using composed

private theorem findIdxs_head?_eq_findIdx?_map_add {α : Type}
    (predicate : α → Bool) :
    ∀ (entries : List α) (start : Nat),
      (entries.findIdxs predicate start).head? =
        (entries.findIdx? predicate).map (fun index => index + start) := by
  intro entries
  induction entries with
  | nil =>
      intro start
      simp
  | cons entry entries inductionHypothesis =>
      intro start
      rw [List.findIdxs_cons]
      by_cases accepted : predicate entry = true
      · rw [List.findIdx?_cons]
        simp [accepted]
      · have rejected : predicate entry = false := by
          cases value : predicate entry
          · rfl
          · exact False.elim (accepted value)
        rw [if_neg accepted]
        rw [inductionHypothesis (start + 1)]
        rw [List.findIdx?_cons, if_neg accepted]
        rw [Option.map_map]
        congr 1
        funext offset
        change offset + (start + 1) = (offset + 1) + start
        omega

private theorem list_getD_zero_eq_head_getD {α : Type} (entries : List α) (fallback : α) :
    entries.getD 0 fallback = entries.head?.getD fallback := by
  cases entries <;> rfl

private theorem firstContainingSetIndexRaw_eq_findIdx_getD
    (I : ExactCoverInput) (x : Nat) :
    firstContainingSetIndexRaw (I, x) =
      (I.system.sets.findIdx? (fun S => Karp21.HittingSet.setContainsBool (x, S))).getD 0 := by
  rw [firstContainingSetIndexRaw, containingSetIndicesExecutable,
    Karp21.HittingSet.setIndexIndicesFromFamily_eq_findIdxs]
  rw [list_getD_zero_eq_head_getD]
  rw [findIdxs_head?_eq_findIdx?_map_add _ I.system.sets 0]
  simp

/-- Boolean occurrence check, including the compact construction's universe bound. -/
def elementOccursBool (input : ExactCoverInput × Nat) : Bool :=
  decide (input.2 < input.1.system.universeSize) &&
    decide (0 < (containingSetIndicesExecutable input).length)

theorem elementOccursBool_eq_true_iff (I : ExactCoverInput) (x : Nat) :
    elementOccursBool (I, x) = true ↔ compactElementOccurs I x := by
  rw [elementOccursBool]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨xBound, indicesPositive⟩
    have nonempty : containingSetIndicesExecutable (I, x) ≠ [] :=
      List.ne_nil_iff_length_pos.mpr indicesPositive
    obtain ⟨index, indexMember⟩ := List.exists_mem_of_ne_nil _ nonempty
    have indexBound : index < I.system.sets.length :=
      Karp21.HittingSet.mem_setIndexIndicesFromFamily_lt indexMember
    rw [containingSetIndicesExecutable,
      Karp21.HittingSet.setIndexIndicesFromFamily_eq_findIdxs] at indexMember
    obtain ⟨_indexBound, contains⟩ :=
      (List.mem_findIdxs_iff_exists_getElem_pos.mp indexMember)
    refine ⟨index, indexBound, ?_⟩
    rw [mem_compactSupport_iff]
    constructor
    · exact xBound
    · have sourceAt : compactSourceSetAt I index = I.system.sets[index] := by
        rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) indexBound]
      rw [sourceAt]
      simpa [Karp21.HittingSet.setContainsBool_eq_decide] using contains
  · rintro ⟨index, indexBound, supportMember⟩
    have xBound := (mem_compactSupport_iff I (compactSourceSetAt I index) x).mp
      supportMember |>.1
    have sourceAt : compactSourceSetAt I index = I.system.sets[index] := by
      rw [compactSourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) indexBound]
    have contains : Karp21.HittingSet.setContainsBool (x, I.system.sets[index]) = true := by
      simpa [sourceAt, Karp21.HittingSet.setContainsBool_eq_decide] using
        (mem_compactSupport_iff I (compactSourceSetAt I index) x).mp supportMember |>.2
    have indexMember :
        index ∈ Karp21.HittingSet.setIndexIndicesFromFamily (x, I.system.sets) := by
      rw [Karp21.HittingSet.setIndexIndicesFromFamily_eq_findIdxs]
      exact List.mem_findIdxs_iff_exists_getElem_pos.mpr ⟨indexBound, contains⟩
    have positive : 0 < (containingSetIndicesExecutable (I, x)).length :=
      List.length_pos_of_mem (by simpa [containingSetIndicesExecutable] using indexMember)
    exact ⟨xBound, positive⟩

theorem elementOccursBool_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.bool elementOccursBool := by
  let X := elementInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp exactCoverUniverseSize_tmPolyTime hSource
    simpa [Function.comp, X] using composed
  have boundInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × Nat =>
        (input.2, input.1.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hElement hUniverse
  have bounded : TMPolyTimeMap X EncodedType.bool
      (fun input : ExactCoverInput × Nat =>
        decide (input.2 < input.1.system.universeSize)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime boundInput
    simpa [natLtBool, Function.comp, X] using composed
  have indicesLength : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat =>
        (containingSetIndicesExecutable input).length) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
      containingSetIndicesExecutable_tmPolyTime
    simpa [Function.comp, natListEncodedType, X] using composed
  have zero : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  have positiveInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × Nat =>
        ((0 : Nat), (containingSetIndicesExecutable input).length)) :=
    TMPolyTimeMap.prod_mk zero indicesLength
  have positive : TMPolyTimeMap X EncodedType.bool
      (fun input : ExactCoverInput × Nat =>
        decide (0 < (containingSetIndicesExecutable input).length)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime positiveInput
    simpa [natLtBool, Function.comp, X] using composed
  have checks : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : ExactCoverInput × Nat =>
        (decide (input.2 < input.1.system.universeSize),
          decide (0 < (containingSetIndicesExecutable input).length))) :=
    TMPolyTimeMap.prod_mk bounded positive
  have composed := TMPolyTimeMap.comp Program.ContextListAll.boolAnd_tmPolyTime checks
  simpa [elementOccursBool, Program.ContextListAll.boolAnd, Function.comp, X] using composed

/-- Total executable replacement for the legacy `Nat.find` family choice. -/
def firstContainingSetIndexExecutable (input : ExactCoverInput × Nat) : Nat :=
  if elementOccursBool input then firstContainingSetIndexRaw input else 0

theorem firstContainingSetIndexExecutable_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.nat
      firstContainingSetIndexExecutable := by
  let X := elementInputEncodedType
  have zero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (show EncodedType.nat.Carrier from (0 : Nat))
  have tagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (elementOccursBool input, input)) :=
    TMPolyTimeMap.prod_mk elementOccursBool_tmPolyTime (TMPolyTimeMap.id X)
  have branch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => firstContainingSetIndexRaw input.2
        | false => (show EncodedType.nat.Carrier from (0 : Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun _ : X.Carrier =>
        (show EncodedType.nat.Carrier from (0 : Nat)))
      (fTrue := firstContainingSetIndexRaw)
      zero firstContainingSetIndexRaw_tmPolyTime
  have composed := TMPolyTimeMap.comp branch tagged
  convert composed using 1
  funext input
  cases occurrence : elementOccursBool input <;>
    simp [firstContainingSetIndexExecutable, occurrence, Function.comp]

theorem firstContainingSetIndexExecutable_eq_legacy (I : ExactCoverInput) (x : Nat) :
    firstContainingSetIndexExecutable (I, x) = compactAlphaSetIndex I x := by
  classical
  by_cases occurs : compactElementOccurs I x
  · have occursBool : elementOccursBool (I, x) = true :=
      (elementOccursBool_eq_true_iff I x).2 occurs
    simp only [firstContainingSetIndexExecutable, occursBool, if_true]
    rw [firstContainingSetIndexRaw_eq_findIdx_getD]
    let predicate := fun S : List Nat => Karp21.HittingSet.setContainsBool (x, S)
    have finderNonempty : I.system.sets.findIdx? predicate ≠ none := by
      intro finderEmpty
      have allRejected := (List.findIdx?_eq_none_iff.mp finderEmpty)
      obtain ⟨index, indexBound, supportMember⟩ := occurs
      have sourceAt : compactSourceSetAt I index = I.system.sets[index] := by
        rw [compactSourceSetAt,
          List.getD_eq_getElem (l := I.system.sets) (d := []) indexBound]
      have accepted : predicate I.system.sets[index] = true := by
        simpa [predicate, sourceAt, Karp21.HittingSet.setContainsBool_eq_decide] using
          (mem_compactSupport_iff I (compactSourceSetAt I index) x).mp supportMember |>.2
      exact Bool.noConfusion (accepted.symm.trans (allRejected _ (List.getElem_mem indexBound)))
    obtain ⟨chosen, chosenEq⟩ := Option.ne_none_iff_exists'.mp finderNonempty
    rw [chosenEq, Option.getD_some]
    have chosenSpec :=
      (List.findIdx?_eq_some_iff_getElem.mp chosenEq)
    obtain ⟨chosenBound, chosenAccepted, chosenMinimal⟩ := chosenSpec
    have xBound : x < I.system.universeSize := by
      obtain ⟨index, _indexBound, supportMember⟩ := occurs
      exact (mem_compactSupport_iff I (compactSourceSetAt I index) x).mp supportMember |>.1
    have chosenLegacy :
        chosen < I.system.sets.length ∧
          x ∈ compactSupport I (compactSourceSetAt I chosen) := by
      refine ⟨chosenBound, ?_⟩
      rw [mem_compactSupport_iff]
      refine ⟨xBound, ?_⟩
      have sourceAt : compactSourceSetAt I chosen = I.system.sets[chosen] := by
        rw [compactSourceSetAt,
          List.getD_eq_getElem (l := I.system.sets) (d := []) chosenBound]
      rw [sourceAt]
      simpa [predicate, Karp21.HittingSet.setContainsBool_eq_decide] using chosenAccepted
    have legacyLe : Nat.find occurs ≤ chosen := Nat.find_min' occurs chosenLegacy
    have chosenLe : chosen ≤ Nat.find occurs := by
      by_contra notLe
      have findLt : Nat.find occurs < chosen := Nat.lt_of_not_ge notLe
      have findSpec := Nat.find_spec occurs
      have rejected := chosenMinimal (Nat.find occurs) findLt
      have sourceAt : compactSourceSetAt I (Nat.find occurs) =
          I.system.sets[Nat.find occurs] := by
        rw [compactSourceSetAt,
          List.getD_eq_getElem (l := I.system.sets) (d := []) findSpec.1]
      have accepted : predicate I.system.sets[Nat.find occurs] = true := by
        simpa [predicate, sourceAt, Karp21.HittingSet.setContainsBool_eq_decide] using
          (mem_compactSupport_iff I
            (compactSourceSetAt I (Nat.find occurs)) x).mp findSpec.2 |>.2
      exact rejected accepted
    have equal : chosen = Nat.find occurs := Nat.le_antisymm chosenLe legacyLe
    simp [compactAlphaSetIndex, occurs, equal]
  · have occursBool : elementOccursBool (I, x) = false := by
      cases value : elementOccursBool (I, x)
      · rfl
      · exact False.elim (occurs ((elementOccursBool_eq_true_iff I x).1 value))
    simp [firstContainingSetIndexExecutable, compactAlphaSetIndex, occursBool, occurs]

/-! ### Alpha codes -/

/-- Executable membership-position arithmetic. -/
def positionCodeExecutable (input : ExactCoverInput × (Nat × Nat)) : Nat :=
  input.2.2 * input.1.system.universeSize + input.2.1

abbrev positionCodeInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

theorem positionCodeExecutable_eq_legacy (I : ExactCoverInput) (x j : Nat) :
    positionCodeExecutable (I, (x, j)) = compactPositionCode I x j :=
  rfl

theorem positionCodeExecutable_tmPolyTime :
    TMPolyTimeMap positionCodeInputEncodedType EncodedType.nat
      positionCodeExecutable := by
  let X := positionCodeInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => input.1) := by
    simpa [X, positionCodeInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hCoordinate : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) => input.2) := by
    simpa [X, positionCodeInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) hCoordinate
    simpa [Function.comp, X] using composed
  have hIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) hCoordinate
    simpa [Function.comp, X] using composed
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp exactCoverUniverseSize_tmPolyTime hSource
    simpa [Function.comp, X] using composed
  have multiplyInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (input.2.2, input.1.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hIndex hUniverse
  have multiplied : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) =>
        input.2.2 * input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime multiplyInput
    simpa [Function.comp, X] using composed
  have addInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (input.2.2 * input.1.system.universeSize, input.2.1)) :=
    TMPolyTimeMap.prod_mk multiplied hElement
  have composed := TMPolyTimeMap.comp natAdd_tm_polytime addInput
  simpa [positionCodeExecutable, Function.comp, X] using composed

/-- Executable version of Karp's alpha code. -/
def alphaCodeExecutable (input : ExactCoverInput × Nat) : Nat :=
  positionCodeExecutable
    (input.1, (input.2, firstContainingSetIndexExecutable input))

theorem alphaCodeExecutable_eq_legacy (I : ExactCoverInput) (x : Nat) :
    alphaCodeExecutable (I, x) = compactAlphaCode I x := by
  rw [alphaCodeExecutable, positionCodeExecutable_eq_legacy,
    firstContainingSetIndexExecutable_eq_legacy]
  rfl

theorem alphaCodeExecutable_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.nat alphaCodeExecutable := by
  let X := elementInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have coordinate : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × Nat =>
        (input.2, firstContainingSetIndexExecutable input)) :=
    TMPolyTimeMap.prod_mk hElement firstContainingSetIndexExecutable_tmPolyTime
  have packed : TMPolyTimeMap X positionCodeInputEncodedType
      (fun input : ExactCoverInput × Nat =>
        (input.1, (input.2, firstContainingSetIndexExecutable input))) :=
    TMPolyTimeMap.prod_mk hSource coordinate
  have composed := TMPolyTimeMap.comp positionCodeExecutable_tmPolyTime packed
  simpa [alphaCodeExecutable, Function.comp, X] using composed

/-- The complete executable alpha-code list in universe order. -/
def alphaCodesExecutable (input : ExactCoverInput) : List Nat :=
  (Program.contextListMapExecutable
      (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
      (input, List.range input.system.universeSize)).map alphaCodeExecutable

theorem alphaCodesExecutable_eq_legacy (I : ExactCoverInput) :
    alphaCodesExecutable I = compactAlphaCodes I := by
  unfold compactAlphaCodes
  rw [alphaCodesExecutable,
    Program.contextListMapExecutable_eq_map
      (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)]
  generalize List.range I.system.universeSize = entries
  induction entries with
  | nil => rfl
  | cons x entries inductionHypothesis =>
      change
        alphaCodeExecutable (I, x) ::
            List.map alphaCodeExecutable
              (List.map (fun element : Nat => (I, element)) entries) =
          compactAlphaCode I x :: List.map (compactAlphaCode I) entries
      rw [alphaCodeExecutable_eq_legacy]
      change
        List.map alphaCodeExecutable
            (List.map (fun element : Nat => (I, element)) entries) =
          List.map (compactAlphaCode I) entries at inductionHypothesis
      exact congrArg (fun tail : List Nat => compactAlphaCode I x :: tail)
        inductionHypothesis

theorem alphaCodesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType natListEncodedType
      alphaCodesExecutable := by
  have hRange : TMPolyTimeMap exactCoverStructuredEncodedType natListEncodedType
      (fun input : ExactCoverInput => List.range input.system.universeSize) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime
      universeSizeExecutable_tmPolyTime
    simpa [Function.comp, universeSizeExecutable, natListEncodedType] using composed
  have packed : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
      (fun input : ExactCoverInput =>
        (input, List.range input.system.universeSize)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id exactCoverStructuredEncodedType) hRange
  have attached : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list elementInputEncodedType)
      (fun input : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (input, List.range input.system.universeSize)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType EncodedType.nat) packed
    simpa [Function.comp, elementInputEncodedType, natListEncodedType] using composed
  have mapped := TMPolyTimeMap.list_map alphaCodeExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [alphaCodesExecutable, Function.comp, natListEncodedType] using composed

/-! ### Alpha/non-alpha membership -/

abbrev alphaMembershipContextEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType EncodedType.nat

abbrev alphaCandidateInputEncodedType : EncodedType :=
  EncodedType.prod alphaMembershipContextEncodedType EncodedType.nat

/-- Check one universe candidate against one requested alpha code. -/
def alphaCandidateBool
    (input : (ExactCoverInput × Nat) × Nat) : Bool :=
  elementOccursBool (input.1.1, input.2) &&
    decide (alphaCodeExecutable (input.1.1, input.2) = input.1.2)

theorem alphaCandidateBool_tmPolyTime :
    TMPolyTimeMap alphaCandidateInputEncodedType EncodedType.bool
      alphaCandidateBool := by
  let X := alphaCandidateInputEncodedType
  have hContext : TMPolyTimeMap X alphaMembershipContextEncodedType
      (fun input : (ExactCoverInput × Nat) × Nat => input.1) := by
    simpa [X, alphaCandidateInputEncodedType] using
      TMPolyTimeMap.fst alphaMembershipContextEncodedType EncodedType.nat
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × Nat => input.2) := by
    simpa [X, alphaCandidateInputEncodedType] using
      TMPolyTimeMap.snd alphaMembershipContextEncodedType EncodedType.nat
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : (ExactCoverInput × Nat) × Nat => input.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat) hContext
    simpa [Function.comp, alphaMembershipContextEncodedType, X] using composed
  have hRequestedCode : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × Nat => input.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat) hContext
    simpa [Function.comp, alphaMembershipContextEncodedType, X] using composed
  have hElementInput : TMPolyTimeMap X elementInputEncodedType
      (fun input : (ExactCoverInput × Nat) × Nat => (input.1.1, input.2)) :=
    TMPolyTimeMap.prod_mk hSource hElement
  have hOccurs : TMPolyTimeMap X EncodedType.bool
      (fun input : (ExactCoverInput × Nat) × Nat =>
        elementOccursBool (input.1.1, input.2)) := by
    have composed := TMPolyTimeMap.comp elementOccursBool_tmPolyTime hElementInput
    simpa [Function.comp, X] using composed
  have hAlphaCode : TMPolyTimeMap X EncodedType.nat
      (fun input : (ExactCoverInput × Nat) × Nat =>
        alphaCodeExecutable (input.1.1, input.2)) := by
    have composed := TMPolyTimeMap.comp alphaCodeExecutable_tmPolyTime hElementInput
    simpa [Function.comp, X] using composed
  have hEqualityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (ExactCoverInput × Nat) × Nat =>
        (alphaCodeExecutable (input.1.1, input.2), input.1.2)) :=
    TMPolyTimeMap.prod_mk hAlphaCode hRequestedCode
  have hEqual : TMPolyTimeMap X EncodedType.bool
      (fun input : (ExactCoverInput × Nat) × Nat =>
        decide (alphaCodeExecutable (input.1.1, input.2) = input.1.2)) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqualityInput
    simpa [Function.comp, X] using composed
  have checks : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : (ExactCoverInput × Nat) × Nat =>
        (elementOccursBool (input.1.1, input.2),
          decide (alphaCodeExecutable (input.1.1, input.2) = input.1.2))) :=
    TMPolyTimeMap.prod_mk hOccurs hEqual
  have composed := TMPolyTimeMap.comp Program.ContextListAll.boolAnd_tmPolyTime checks
  simpa [alphaCandidateBool, Program.ContextListAll.boolAnd, Function.comp, X] using composed

/-- Decide membership in the image of the legacy alpha injection. -/
def isAlphaCodeBool (input : ExactCoverInput × Nat) : Bool :=
  Program.ContextListAny.executable
    (C := alphaMembershipContextEncodedType) (X := EncodedType.nat)
    alphaCandidateBool
    ((input.1, input.2), List.range input.1.system.universeSize)

theorem isAlphaCodeBool_eq_true_iff (I : ExactCoverInput) (code : Nat) :
    isAlphaCodeBool (I, code) = true ↔ compactIsAlphaCode I code := by
  rw [isAlphaCodeBool,
    Program.ContextListAny.executable_eq_true_iff
      (C := alphaMembershipContextEncodedType) (X := EncodedType.nat)
      alphaCandidateBool
      (I, code) (List.range I.system.universeSize)]
  change
    (∃ x : Nat, x ∈ List.range I.system.universeSize ∧
      alphaCandidateBool ((I, code), x) = true) ↔ compactIsAlphaCode I code
  constructor
  · rintro ⟨x, xMember, candidate⟩
    have xBound : x < I.system.universeSize := by simpa using xMember
    have checks :
        elementOccursBool (I, x) = true ∧
          decide (alphaCodeExecutable (I, x) = code) = true := by
      simpa [alphaCandidateBool] using candidate
    exact ⟨x, xBound, (elementOccursBool_eq_true_iff I x).1 checks.1, by
      simpa [alphaCodeExecutable_eq_legacy] using of_decide_eq_true checks.2⟩
  · rintro ⟨x, xBound, occurrence, codeEquality⟩
    refine ⟨x, by simpa using xBound, ?_⟩
    simp [alphaCandidateBool, (elementOccursBool_eq_true_iff I x).2 occurrence,
      alphaCodeExecutable_eq_legacy, codeEquality]

theorem isAlphaCodeBool_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.bool isAlphaCodeBool := by
  let X := elementInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × Nat => input.1) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType EncodedType.nat
  have hCode : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp universeSizeExecutable_tmPolyTime hSource
    simpa [universeSizeExecutable, Function.comp, X] using composed
  have hRange : TMPolyTimeMap X natListEncodedType
      (fun input : ExactCoverInput × Nat => List.range input.1.system.universeSize) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, natListEncodedType, X] using composed
  have hContext : TMPolyTimeMap X alphaMembershipContextEncodedType
      (fun input : ExactCoverInput × Nat => (input.1, input.2)) :=
    TMPolyTimeMap.prod_mk hSource hCode
  have packed : TMPolyTimeMap X
      (EncodedType.prod alphaMembershipContextEncodedType natListEncodedType)
      (fun input : ExactCoverInput × Nat =>
        ((input.1, input.2), List.range input.1.system.universeSize)) :=
    TMPolyTimeMap.prod_mk hContext hRange
  have composed := TMPolyTimeMap.comp
    (Program.ContextListAny.executable_tmPolyTime
      (C := alphaMembershipContextEncodedType) (X := EncodedType.nat)
      alphaCandidateBool
      alphaCandidateBool_tmPolyTime) packed
  simpa [isAlphaCodeBool, Function.comp, alphaMembershipContextEncodedType,
    natListEncodedType, X] using composed

/-- Executable complement of alpha-image membership. -/
def isNonAlphaCodeBool (input : ExactCoverInput × Nat) : Bool :=
  Bool.not (isAlphaCodeBool input)

theorem isNonAlphaCodeBool_eq_true_iff (I : ExactCoverInput) (code : Nat) :
    isNonAlphaCodeBool (I, code) = true ↔ ¬ compactIsAlphaCode I code := by
  rw [isNonAlphaCodeBool, Bool.not_eq_true']
  constructor
  · intro alphaFalse alpha
    have alphaTrue := (isAlphaCodeBool_eq_true_iff I code).2 alpha
    rw [alphaFalse] at alphaTrue
    contradiction
  · intro notAlpha
    cases alphaValue : isAlphaCodeBool (I, code)
    · rfl
    · exact False.elim
        (notAlpha ((isAlphaCodeBool_eq_true_iff I code).1 alphaValue))

theorem isNonAlphaCodeBool_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType EncodedType.bool
      isNonAlphaCodeBool := by
  have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not
    isAlphaCodeBool_tmPolyTime
  simpa [isNonAlphaCodeBool, Function.comp] using composed

/-! ### Complete membership-position list -/

/-- Compute every bounded support list while preserving source-family order. -/
def supportFamilyExecutable (input : ExactCoverInput) : List (List Nat) :=
  (Program.contextListMapExecutable
      (C := exactCoverStructuredEncodedType) (X := setStructuredEncodedType)
      (input, input.system.sets)).map compactSupportExecutable

theorem supportFamilyExecutable_eq (I : ExactCoverInput) :
    supportFamilyExecutable I = I.system.sets.map (compactSupport I) := by
  rw [supportFamilyExecutable,
    Program.contextListMapExecutable_eq_map
      (C := exactCoverStructuredEncodedType) (X := setStructuredEncodedType)]
  generalize I.system.sets = entries
  induction entries with
  | nil => rfl
  | cons set entries inductionHypothesis =>
      change
        compactSupportExecutable (I, set) ::
            List.map compactSupportExecutable
              (List.map (fun entry : List Nat => (I, entry)) entries) =
          compactSupport I set :: List.map (compactSupport I) entries
      rw [compactSupportExecutable_eq_legacy]
      change
        List.map compactSupportExecutable
            (List.map (fun entry : List Nat => (I, entry)) entries) =
          List.map (compactSupport I) entries at inductionHypothesis
      exact congrArg (fun tail : List (List Nat) => compactSupport I set :: tail)
        inductionHypothesis

theorem supportFamilyExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType setFamilyStructuredEncodedType
      supportFamilyExecutable := by
  have hSets := exactCoverSets_tmPolyTime
  have packed : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.prod exactCoverStructuredEncodedType setFamilyStructuredEncodedType)
      (fun input : ExactCoverInput => (input, input.system.sets)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id exactCoverStructuredEncodedType) hSets
  have attached : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list supportInputEncodedType)
      (fun input : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := setStructuredEncodedType)
          (input, input.system.sets)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType setStructuredEncodedType) packed
    simpa [Function.comp, supportInputEncodedType, setFamilyStructuredEncodedType]
      using composed
  have mapped := TMPolyTimeMap.list_map compactSupportExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [supportFamilyExecutable, Function.comp, setFamilyStructuredEncodedType]
    using composed

/-- Ordered `(element,setIndex)` pairs for all bounded supports. -/
def positionPairsExecutable (input : ExactCoverInput) : List (Nat × Nat) :=
  SetSystemMembershipPairs.fromSetFamily (supportFamilyExecutable input)

theorem positionPairsExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType
      SetSystemMembershipPairs.pairListEncodedType positionPairsExecutable := by
  have composed := TMPolyTimeMap.comp
    SetSystemMembershipPairs.fromSetFamily_tmPolyTime
    supportFamilyExecutable_tmPolyTime
  simpa [positionPairsExecutable, Function.comp,
    SetSystemMembershipPairs.setFamilyInputEncodedType,
    setFamilyStructuredEncodedType] using composed

private def positionCodesFrom (bound start : Nat) :
    List (List Nat) → List Nat
  | [] => []
  | set :: sets =>
      ((List.range bound).filter fun x => decide (x ∈ set)).map
          (fun x => start * bound + x) ++
        positionCodesFrom bound (start + 1) sets

private theorem compactSupport_eq_plain (I : ExactCoverInput) (set : List Nat) :
    compactSupport I set =
      (List.range I.system.universeSize).filter fun x => decide (x ∈ set) := by
  simp [compactSupport, List.range_eq_range']

private theorem membershipPairsFrom_supports_map_code
    (bound start : Nat) :
    ∀ sets : List (List Nat),
      (SetSystemMembershipPairs.membershipPairsFrom start
          (sets.map fun set =>
            (List.range bound).filter fun x => decide (x ∈ set))).map
          (fun pair => pair.2 * bound + pair.1) =
        positionCodesFrom bound start sets := by
  intro sets
  induction sets generalizing start with
  | nil => rfl
  | cons set sets inductionHypothesis =>
      simp [SetSystemMembershipPairs.membershipPairsFrom, positionCodesFrom,
        List.map_append, inductionHypothesis]

private theorem range_succ_eq_zero_map (length : Nat) :
    List.range (length + 1) =
      0 :: (List.range length).map (fun index => index + 1) := by
  induction length with
  | zero => rfl
  | succ length inductionHypothesis =>
      change List.range ((length + 1) + 1) =
        0 :: (List.range (length + 1)).map (fun index => index + 1)
      rw [List.range_succ, inductionHypothesis]
      have shifted := congrArg (List.map fun index : Nat => index + 1)
        inductionHypothesis
      simpa [List.range_succ, List.map_append, List.map_map, Function.comp_def,
        Nat.add_assoc] using shifted

private theorem range_flatMap_support_eq_positionCodesFrom
    (bound start : Nat) :
    ∀ sets : List (List Nat),
      (List.range sets.length).flatMap (fun offset =>
        ((List.range bound).filter fun x =>
          decide (x ∈ sets.getD offset [])).map
            (fun x => (start + offset) * bound + x)) =
        positionCodesFrom bound start sets := by
  intro sets
  induction sets generalizing start with
  | nil => rfl
  | cons set sets inductionHypothesis =>
      rw [show (set :: sets).length = sets.length + 1 by simp]
      rw [range_succ_eq_zero_map]
      simp only [List.flatMap_cons, List.getD_cons_zero, Nat.add_zero]
      rw [List.flatMap_map]
      simp only [List.getD_cons_succ]
      rw [positionCodesFrom]
      congr 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (start + 1)

private theorem compactPositionCodes_eq_positionCodesFrom (I : ExactCoverInput) :
    compactPositionCodes I =
      positionCodesFrom I.system.universeSize 0 I.system.sets := by
  have hLocal (offset : Nat) :
      compactPositionCodesForSet I offset =
        ((List.range I.system.universeSize).filter fun x =>
          decide (x ∈ I.system.sets.getD offset [])).map
            (fun x => offset * I.system.universeSize + x) := by
    rw [compactPositionCodesForSet, compactSourceSetAt]
    rw [compactSupport_eq_plain]
    rfl
  rw [compactPositionCodes]
  calc
    (List.range I.system.sets.length).flatMap (compactPositionCodesForSet I) =
        (List.range I.system.sets.length).flatMap (fun offset =>
          ((List.range I.system.universeSize).filter fun x =>
            decide (x ∈ I.system.sets.getD offset [])).map
              (fun x => offset * I.system.universeSize + x)) := by
      exact List.flatMap_congr (fun offset _offsetMember => hLocal offset)
    _ = positionCodesFrom I.system.universeSize 0 I.system.sets := by
      simpa using
        range_flatMap_support_eq_positionCodesFrom
          I.system.universeSize 0 I.system.sets

/-- Exact executable list of compact membership-position codes. -/
def positionCodesExecutable (input : ExactCoverInput) : List Nat :=
  (Program.contextListMapExecutable
      (C := exactCoverStructuredEncodedType)
      (X := SetSystemMembershipPairs.pairEncodedType)
      (input, positionPairsExecutable input)).map positionCodeExecutable

private theorem attachedPositionCodes_eq_map (I : ExactCoverInput)
    (pairs : List (Nat × Nat)) :
    (Program.contextListMapExecutable
        (C := exactCoverStructuredEncodedType)
        (X := SetSystemMembershipPairs.pairEncodedType)
        (I, pairs)).map positionCodeExecutable =
      pairs.map (fun pair => pair.2 * I.system.universeSize + pair.1) := by
  rw [Program.contextListMapExecutable_eq_map
    (C := exactCoverStructuredEncodedType)
    (X := SetSystemMembershipPairs.pairEncodedType)]
  induction pairs with
  | nil => rfl
  | cons pair pairs inductionHypothesis =>
      change
        positionCodeExecutable (I, pair) ::
            List.map positionCodeExecutable
              (List.map (fun entry : Nat × Nat => (I, entry)) pairs) =
          (pair.2 * I.system.universeSize + pair.1) ::
            List.map (fun entry => entry.2 * I.system.universeSize + entry.1) pairs
      rw [positionCodeExecutable]
      change
        List.map positionCodeExecutable
            (List.map (fun entry : Nat × Nat => (I, entry)) pairs) =
          List.map (fun entry => entry.2 * I.system.universeSize + entry.1) pairs
        at inductionHypothesis
      exact congrArg
        (fun tail : List Nat =>
          (pair.2 * I.system.universeSize + pair.1) :: tail)
        inductionHypothesis

theorem positionCodesExecutable_eq_legacy (I : ExactCoverInput) :
    positionCodesExecutable I = compactPositionCodes I := by
  rw [positionCodesExecutable, attachedPositionCodes_eq_map]
  rw [positionPairsExecutable, SetSystemMembershipPairs.fromSetFamily_eq_membershipPairsFrom,
    supportFamilyExecutable_eq]
  rw [compactPositionCodes_eq_positionCodesFrom]
  have legacySupports :
      I.system.sets.map (compactSupport I) =
        I.system.sets.map (fun set =>
          (List.range I.system.universeSize).filter fun x => decide (x ∈ set)) := by
    apply List.map_congr_left
    intro set setMember
    exact compactSupport_eq_plain I set
  rw [legacySupports]
  exact membershipPairsFrom_supports_map_code
    I.system.universeSize 0 I.system.sets

theorem positionCodesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType natListEncodedType
      positionCodesExecutable := by
  have packed : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.prod exactCoverStructuredEncodedType
        (EncodedType.list SetSystemMembershipPairs.pairEncodedType))
      (fun input : ExactCoverInput => (input, positionPairsExecutable input)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id exactCoverStructuredEncodedType)
      positionPairsExecutable_tmPolyTime
  have attached : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list positionCodeInputEncodedType)
      (fun input : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType)
          (X := SetSystemMembershipPairs.pairEncodedType)
          (input, positionPairsExecutable input)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType SetSystemMembershipPairs.pairEncodedType) packed
    simpa [Function.comp, positionCodeInputEncodedType,
      SetSystemMembershipPairs.pairListEncodedType] using composed
  have mapped := TMPolyTimeMap.list_map positionCodeExecutable_tmPolyTime
  have composed := TMPolyTimeMap.comp mapped attached
  simpa [positionCodesExecutable, Function.comp, natListEncodedType] using composed

/-! ### Cyclic support successor without `idxOf` or `%` machines -/

abbrev firstNatIndexInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat natListEncodedType

abbrev nextInSupportInputEncodedType : EncodedType :=
  EncodedType.prod natListEncodedType EncodedType.nat

/-- Replace each natural by its singleton set for reuse of the family-index scan. -/
def singletonFamilyExecutable (entries : List Nat) : List (List Nat) :=
  entries.map fun entry => [entry]

theorem singletonFamilyExecutable_tmPolyTime :
    TMPolyTimeMap natListEncodedType setFamilyStructuredEncodedType
      singletonFamilyExecutable := by
  have singleton := TMPolyTimeMap.list_singleton EncodedType.nat
  have mapped := TMPolyTimeMap.list_map singleton
  simpa [singletonFamilyExecutable, natListEncodedType,
    setFamilyStructuredEncodedType, setStructuredEncodedType] using mapped

/-- First matching natural-list index, totalized to zero when absent. -/
def firstNatIndexExecutable (input : Nat × List Nat) : Nat :=
  (Karp21.HittingSet.setIndexIndicesFromFamily
    (input.1, singletonFamilyExecutable input.2)).getD 0 0

theorem firstNatIndexExecutable_tmPolyTime :
    TMPolyTimeMap firstNatIndexInputEncodedType EncodedType.nat
      firstNatIndexExecutable := by
  let X := firstNatIndexInputEncodedType
  have hNeedle : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × List Nat => input.1) := by
    simpa [X, firstNatIndexInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat natListEncodedType
  have hEntries : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat => input.2) := by
    simpa [X, firstNatIndexInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat natListEncodedType
  have hSingletons : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun input : Nat × List Nat => singletonFamilyExecutable input.2) := by
    have composed := TMPolyTimeMap.comp singletonFamilyExecutable_tmPolyTime hEntries
    simpa [Function.comp, X] using composed
  have hScanInput : TMPolyTimeMap X familyScanInputEncodedType
      (fun input : Nat × List Nat =>
        (input.1, singletonFamilyExecutable input.2)) :=
    TMPolyTimeMap.prod_mk hNeedle hSingletons
  have hIndices : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat =>
        Karp21.HittingSet.setIndexIndicesFromFamily
          (input.1, singletonFamilyExecutable input.2)) := by
    have composed := TMPolyTimeMap.comp
      Karp21.HittingSet.setIndexIndicesFromFamily_tm_polytime hScanInput
    simpa [Function.comp, familyScanInputEncodedType,
      Karp21.HittingSet.setIndexInstructionInputEncodedType, X] using composed
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hLookupInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : Nat × List Nat =>
        (Karp21.HittingSet.setIndexIndicesFromFamily
          (input.1, singletonFamilyExecutable input.2), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hIndices hZero
  have composed := TMPolyTimeMap.comp
    (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat))
    hLookupInput
  simpa [firstNatIndexExecutable, Karp21.EncodedListLookup.getD,
    Function.comp, natListEncodedType, X] using composed

private theorem findIdx_singletons_eq_idxOf_of_mem (needle : Nat) :
    ∀ {entries : List Nat}, needle ∈ entries →
      (singletonFamilyExecutable entries).findIdx?
          (fun set => Karp21.HittingSet.setContainsBool (needle, set)) =
        some (entries.idxOf needle) := by
  intro entries needleMember
  induction entries with
  | nil => simp at needleMember
  | cons entry entries inductionHypothesis =>
      rw [singletonFamilyExecutable, List.map_cons, List.findIdx?_cons]
      by_cases headEqual : entry = needle
      · subst entry
        simp [Karp21.HittingSet.setContainsBool_eq_decide]
      · have tailMember : needle ∈ entries := by
          rcases List.mem_cons.mp needleMember with headMembership | tailMembership
          · exact False.elim (headEqual headMembership.symm)
          · exact tailMembership
        have tailResult := inductionHypothesis tailMember
        have rejected :
            Karp21.HittingSet.setContainsBool (needle, [entry]) ≠ true := by
          have reverseNe : needle ≠ entry := fun equality => headEqual equality.symm
          simp [Karp21.HittingSet.setContainsBool_eq_decide, reverseNe]
        rw [if_neg rejected]
        change
          List.findIdx?
              (fun set => Karp21.HittingSet.setContainsBool (needle, set))
              (List.map (fun entry : Nat => [entry]) entries) =
            some (entries.idxOf needle) at tailResult
        rw [tailResult]
        simp [headEqual]

theorem firstNatIndexExecutable_eq_idxOf {needle : Nat} {entries : List Nat}
    (needleMember : needle ∈ entries) :
    firstNatIndexExecutable (needle, entries) = entries.idxOf needle := by
  rw [firstNatIndexExecutable,
    Karp21.HittingSet.setIndexIndicesFromFamily_eq_findIdxs]
  rw [list_getD_zero_eq_head_getD]
  rw [findIdxs_head?_eq_findIdx?_map_add _
    (singletonFamilyExecutable entries) 0]
  rw [findIdx_singletons_eq_idxOf_of_mem needle needleMember]
  simp

/--
Executable cyclic successor.  A present element uses its first matching index
and total lookup; the final element wraps to the first.  The absent cases are
spelled out to retain the legacy `idxOf = length` and `%` semantics exactly.
-/
def nextInSupportExecutable (input : List Nat × Nat) : Nat :=
  let entries := input.1
  let needle := input.2
  match Karp21.HittingSet.setContainsBool (needle, entries) with
  | true =>
      let nextIndex := firstNatIndexExecutable (needle, entries) + 1
      match decide (nextIndex < entries.length) with
      | true => entries.getD nextIndex 0
      | false => entries.getD 0 0
  | false =>
      match decide (0 < entries.length) with
      | true =>
          match decide (1 < entries.length) with
          | true => entries.getD 1 0
          | false => entries.getD 0 0
      | false => needle

theorem nextInSupportExecutable_tmPolyTime :
    TMPolyTimeMap nextInSupportInputEncodedType EncodedType.nat
      nextInSupportExecutable := by
  let X := nextInSupportInputEncodedType
  have hEntries : TMPolyTimeMap X natListEncodedType
      (fun input : List Nat × Nat => input.1) := by
    simpa [X, nextInSupportInputEncodedType] using
      TMPolyTimeMap.fst natListEncodedType EncodedType.nat
  have hNeedle : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat => input.2) := by
    simpa [X, nextInSupportInputEncodedType] using
      TMPolyTimeMap.snd natListEncodedType EncodedType.nat
  have hContainsInput : TMPolyTimeMap X
      Karp21.HittingSet.setContainsInstructionInputEncodedType
      (fun input : List Nat × Nat => (input.2, input.1)) :=
    TMPolyTimeMap.prod_mk hNeedle hEntries
  have hContains : TMPolyTimeMap X EncodedType.bool
      (fun input : List Nat × Nat =>
        Karp21.HittingSet.setContainsBool (input.2, input.1)) := by
    have composed := TMPolyTimeMap.comp
      Karp21.HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, X] using composed
  have hLength : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat => input.1.length) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime hEntries
    simpa [Function.comp, natListEncodedType, X] using composed
  have hFirstInput : TMPolyTimeMap X firstNatIndexInputEncodedType
      (fun input : List Nat × Nat => (input.2, input.1)) :=
    TMPolyTimeMap.prod_mk hNeedle hEntries
  have hFirst : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat => firstNatIndexExecutable (input.2, input.1)) := by
    have composed := TMPolyTimeMap.comp firstNatIndexExecutable_tmPolyTime hFirstInput
    simpa [Function.comp, X] using composed
  have hNextIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat =>
        firstNatIndexExecutable (input.2, input.1) + 1) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hFirst
    simpa [Function.comp, X] using composed
  have hNextBoundInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : List Nat × Nat =>
        (firstNatIndexExecutable (input.2, input.1) + 1, input.1.length)) :=
    TMPolyTimeMap.prod_mk hNextIndex hLength
  have hNextBound : TMPolyTimeMap X EncodedType.bool
      (fun input : List Nat × Nat =>
        decide (firstNatIndexExecutable (input.2, input.1) + 1 < input.1.length)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime hNextBoundInput
    simpa [natLtBool, Function.comp, X] using composed
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hOne : TMPolyTimeMap X EncodedType.nat
      (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (1 : Nat))
  have hLookupZeroInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : List Nat × Nat => (input.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hEntries hZero
  have hLookupOneInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : List Nat × Nat => (input.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hEntries hOne
  have hLookupNextInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : List Nat × Nat =>
        (input.1, firstNatIndexExecutable (input.2, input.1) + 1)) :=
    TMPolyTimeMap.prod_mk hEntries hNextIndex
  have hLookupZero : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat => input.1.getD 0 0) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat))
      hLookupZeroInput
    simpa [Karp21.EncodedListLookup.getD, Function.comp, natListEncodedType, X]
      using composed
  have hLookupOne : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat => input.1.getD 1 0) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat))
      hLookupOneInput
    simpa [Karp21.EncodedListLookup.getD, Function.comp, natListEncodedType, X]
      using composed
  have hLookupNext : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat =>
        input.1.getD (firstNatIndexExecutable (input.2, input.1) + 1) 0) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat))
      hLookupNextInput
    simpa [Karp21.EncodedListLookup.getD, Function.comp, natListEncodedType, X]
      using composed
  have hPresentTag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (decide
        (firstNatIndexExecutable (input.2, input.1) + 1 < input.1.length), input)) :=
    TMPolyTimeMap.prod_mk hNextBound (TMPolyTimeMap.id X)
  have hPresentBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
      EncodedType.nat
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => input.2.1.getD
            (firstNatIndexExecutable (input.2.2, input.2.1) + 1) (0 : Nat)
        | false => input.2.1.getD 0 (0 : Nat)) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun input : X.Carrier => input.1.getD 0 (0 : Nat))
      (fTrue := fun input : X.Carrier =>
        input.1.getD (firstNatIndexExecutable (input.2, input.1) + 1) (0 : Nat))
      hLookupZero hLookupNext
  have hPresent : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat =>
        match decide
            (firstNatIndexExecutable (input.2, input.1) + 1 < input.1.length) with
        | true =>
            input.1.getD (firstNatIndexExecutable (input.2, input.1) + 1) 0
        | false => input.1.getD 0 0) := by
    have composed := TMPolyTimeMap.comp hPresentBranch hPresentTag
    simpa [Function.comp] using composed
  have hPositiveInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : List Nat × Nat => ((0 : Nat), input.1.length)) :=
    TMPolyTimeMap.prod_mk hZero hLength
  have hPositive : TMPolyTimeMap X EncodedType.bool
      (fun input : List Nat × Nat => decide (0 < input.1.length)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime hPositiveInput
    simpa [natLtBool, Function.comp, X] using composed
  have hLongInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : List Nat × Nat => ((1 : Nat), input.1.length)) :=
    TMPolyTimeMap.prod_mk hOne hLength
  have hLong : TMPolyTimeMap X EncodedType.bool
      (fun input : List Nat × Nat => decide (1 < input.1.length)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime hLongInput
    simpa [natLtBool, Function.comp, X] using composed
  have hLongTag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (decide (1 < input.1.length), input)) :=
    TMPolyTimeMap.prod_mk hLong (TMPolyTimeMap.id X)
  have hLongBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
      EncodedType.nat
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => input.2.1.getD 1 (0 : Nat)
        | false => input.2.1.getD 0 (0 : Nat)) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun input : X.Carrier => input.1.getD 0 (0 : Nat))
      (fTrue := fun input : X.Carrier => input.1.getD 1 (0 : Nat))
      hLookupZero hLookupOne
  have hPositiveValue : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat =>
        match decide (1 < input.1.length) with
        | true => input.1.getD 1 0
        | false => input.1.getD 0 0) := by
    have composed := TMPolyTimeMap.comp hLongBranch hLongTag
    simpa [Function.comp] using composed
  have hPositiveTag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (decide (0 < input.1.length), input)) :=
    TMPolyTimeMap.prod_mk hPositive (TMPolyTimeMap.id X)
  have hAbsentBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
      EncodedType.nat
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true =>
            match decide (1 < input.2.1.length) with
            | true => input.2.1.getD 1 (0 : Nat)
            | false => input.2.1.getD 0 (0 : Nat)
        | false => input.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun input : X.Carrier => input.2)
      (fTrue := fun input : X.Carrier =>
        match decide (1 < input.1.length) with
        | true => input.1.getD 1 (0 : Nat)
        | false => input.1.getD 0 (0 : Nat))
      hNeedle hPositiveValue
  have hAbsent : TMPolyTimeMap X EncodedType.nat
      (fun input : List Nat × Nat =>
        match decide (0 < input.1.length) with
        | true =>
            match decide (1 < input.1.length) with
            | true => input.1.getD 1 0
            | false => input.1.getD 0 0
        | false => input.2) := by
    have composed := TMPolyTimeMap.comp hAbsentBranch hPositiveTag
    simpa [Function.comp] using composed
  have hOuterTag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier =>
        (Karp21.HittingSet.setContainsBool (input.2, input.1), input)) :=
    TMPolyTimeMap.prod_mk hContains (TMPolyTimeMap.id X)
  have hOuterBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
      EncodedType.nat
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true =>
            match decide (firstNatIndexExecutable (input.2.2, input.2.1) + 1 <
                input.2.1.length) with
            | true => input.2.1.getD
                (firstNatIndexExecutable (input.2.2, input.2.1) + 1) (0 : Nat)
            | false => input.2.1.getD 0 (0 : Nat)
        | false =>
            match decide (0 < input.2.1.length) with
            | true =>
                match decide (1 < input.2.1.length) with
                | true => input.2.1.getD 1 (0 : Nat)
                | false => input.2.1.getD 0 (0 : Nat)
            | false => input.2.2) :=
    graphBoolProduct_dispatch_tm_polytime X EncodedType.nat
      (fFalse := fun input : X.Carrier =>
        match decide (0 < input.1.length) with
        | true =>
            match decide (1 < input.1.length) with
            | true => input.1.getD 1 (0 : Nat)
            | false => input.1.getD 0 (0 : Nat)
        | false => input.2)
      (fTrue := fun input : X.Carrier =>
        match decide
            (firstNatIndexExecutable (input.2, input.1) + 1 < input.1.length) with
        | true => input.1.getD
            (firstNatIndexExecutable (input.2, input.1) + 1) (0 : Nat)
        | false => input.1.getD 0 (0 : Nat))
      hAbsent hPresent
  have composed := TMPolyTimeMap.comp hOuterBranch hOuterTag
  simpa [nextInSupportExecutable, Function.comp] using composed

theorem nextInSupportExecutable_eq_legacy (entries : List Nat) (needle : Nat) :
    nextInSupportExecutable (entries, needle) =
      entries.getD ((entries.idxOf needle + 1) % entries.length) needle := by
  classical
  by_cases member : needle ∈ entries
  · have contains : Karp21.HittingSet.setContainsBool (needle, entries) = true := by
      simpa [Karp21.HittingSet.setContainsBool_eq_decide] using member
    have indexBound : entries.idxOf needle < entries.length :=
      List.idxOf_lt_length_iff.mpr member
    simp only [nextInSupportExecutable, contains,
      firstNatIndexExecutable_eq_idxOf member]
    by_cases nextBound : entries.idxOf needle + 1 < entries.length
    · have decided :
          decide (entries.idxOf needle + 1 < entries.length) = true := by
        simp [nextBound]
      rw [decided]
      rw [Nat.mod_eq_of_lt nextBound]
      rw [List.getD_eq_getElem entries 0 nextBound,
        List.getD_eq_getElem entries needle nextBound]
    · have nextEqual : entries.idxOf needle + 1 = entries.length := by omega
      have positive : 0 < entries.length := by omega
      have decided :
          decide (entries.idxOf needle + 1 < entries.length) = false := by
        simp [nextBound]
      rw [decided]
      rw [nextEqual, Nat.mod_self]
      rw [List.getD_eq_getElem entries 0 positive,
        List.getD_eq_getElem entries needle positive]
  · have contains : Karp21.HittingSet.setContainsBool (needle, entries) = false := by
      simp [Karp21.HittingSet.setContainsBool_eq_decide, member]
    have indexEqual : entries.idxOf needle = entries.length :=
      List.idxOf_eq_length_iff.mpr member
    simp only [nextInSupportExecutable, contains, indexEqual]
    by_cases positive : 0 < entries.length
    · have positiveDecided : decide (0 < entries.length) = true := by
        simp [positive]
      rw [positiveDecided]
      have modReduce : (entries.length + 1) % entries.length = 1 % entries.length := by
        rw [Nat.add_mod]
        simp
      rw [modReduce]
      by_cases long : 1 < entries.length
      · have longDecided : decide (1 < entries.length) = true := by simp [long]
        rw [longDecided]
        rw [Nat.mod_eq_of_lt long]
        rw [List.getD_eq_getElem entries 0 long,
          List.getD_eq_getElem entries needle long]
      · have lengthOne : entries.length = 1 := by omega
        have longDecided : decide (1 < entries.length) = false := by simp [long]
        rw [longDecided]
        rw [lengthOne, Nat.mod_one]
        have zeroBound : 0 < entries.length := positive
        rw [List.getD_eq_getElem entries 0 zeroBound,
          List.getD_eq_getElem entries needle zeroBound]
    · have positiveDecided : decide (0 < entries.length) = false := by
        simp [positive]
      rw [positiveDecided]
      have empty : entries = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos positive)
      subst entries
      simp

abbrev nextInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Exact executable wrapper for the legacy source-set cyclic successor. -/
def compactNextInSetExecutable
    (input : ExactCoverInput × (Nat × Nat)) : Nat :=
  nextInSupportExecutable
    (compactSupportExecutable
      (input.1, sourceSetAtExecutable (input.1, input.2.1)), input.2.2)

theorem compactNextInSetExecutable_eq_legacy
    (I : ExactCoverInput) (j x : Nat) :
    compactNextInSetExecutable (I, (j, x)) = compactNextInSet I j x := by
  rw [compactNextInSetExecutable, nextInSupportExecutable_eq_legacy,
    compactSupportExecutable_eq_legacy, sourceSetAtExecutable_eq_legacy]
  rfl

theorem compactNextInSetExecutable_tmPolyTime :
    TMPolyTimeMap nextInputEncodedType EncodedType.nat
      compactNextInSetExecutable := by
  let X := nextInputEncodedType
  have hSource : TMPolyTimeMap X exactCoverStructuredEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => input.1) := by
    simpa [X, nextInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hCoordinate : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : ExactCoverInput × (Nat × Nat) => input.2) := by
    simpa [X, nextInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hSetIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) hCoordinate
    simpa [Function.comp, X] using composed
  have hElement : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) hCoordinate
    simpa [Function.comp, X] using composed
  have hSourceSetInput : TMPolyTimeMap X elementInputEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) => (input.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk hSource hSetIndex
  have hSourceSet : TMPolyTimeMap X setStructuredEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) =>
        sourceSetAtExecutable (input.1, input.2.1)) := by
    have composed := TMPolyTimeMap.comp sourceSetAtExecutable_tmPolyTime hSourceSetInput
    simpa [Function.comp, X] using composed
  have hSupportInput : TMPolyTimeMap X supportInputEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (input.1, sourceSetAtExecutable (input.1, input.2.1))) :=
    TMPolyTimeMap.prod_mk hSource hSourceSet
  have hSupport : TMPolyTimeMap X natListEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) =>
        compactSupportExecutable
          (input.1, sourceSetAtExecutable (input.1, input.2.1))) := by
    have composed := TMPolyTimeMap.comp compactSupportExecutable_tmPolyTime hSupportInput
    simpa [Function.comp, X] using composed
  have hNextInput : TMPolyTimeMap X nextInSupportInputEncodedType
      (fun input : ExactCoverInput × (Nat × Nat) =>
        (compactSupportExecutable
          (input.1, sourceSetAtExecutable (input.1, input.2.1)), input.2.2)) :=
    TMPolyTimeMap.prod_mk hSupport hElement
  have composed := TMPolyTimeMap.comp nextInSupportExecutable_tmPolyTime hNextInput
  simpa [compactNextInSetExecutable, Function.comp, X] using composed

/-! ### Executable non-alpha filtering -/

/-- Emit one retained code as a singleton, or no code when it is alpha. -/
def nonAlphaItemExecutable (input : ExactCoverInput × Nat) : List Nat :=
  match isAlphaCodeBool input with
  | true => []
  | false => [input.2]

theorem nonAlphaItemExecutable_tmPolyTime :
    TMPolyTimeMap elementInputEncodedType natListEncodedType
      nonAlphaItemExecutable := by
  let X := elementInputEncodedType
  have hCode : TMPolyTimeMap X EncodedType.nat
      (fun input : ExactCoverInput × Nat => input.2) := by
    simpa [X, elementInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType EncodedType.nat
  have hSingleton : TMPolyTimeMap X natListEncodedType
      (fun input : ExactCoverInput × Nat => [input.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, natListEncodedType, X] using composed
  have hEmpty : TMPolyTimeMap X natListEncodedType
      (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X natListEncodedType
      (show natListEncodedType.Carrier from ([] : List Nat))
  have hTag : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun input : X.Carrier => (isAlphaCodeBool input, input)) :=
    TMPolyTimeMap.prod_mk isAlphaCodeBool_tmPolyTime (TMPolyTimeMap.id X)
  have hBranch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X)
      natListEncodedType
      (fun input : Bool × X.Carrier =>
        match input.1 with
        | true => ([] : List Nat)
        | false => [input.2.2]) :=
    graphBoolProduct_dispatch_tm_polytime X natListEncodedType
      (fFalse := fun input : X.Carrier => [input.2])
      (fTrue := fun _ : X.Carrier => ([] : List Nat))
      hSingleton hEmpty
  have composed := TMPolyTimeMap.comp hBranch hTag
  simpa [nonAlphaItemExecutable, Function.comp, X] using composed

/--
Executable position-code filter.  Every item is first paired with the fixed
source instance, mapped to either a singleton or the empty list, then flattened
with the standard reachable-fold list primitive.
-/
def nonAlphaCodesExecutable (input : ExactCoverInput) : List Nat :=
  ((Program.contextListMapExecutable
      (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
      (input, positionCodesExecutable input)).map nonAlphaItemExecutable).flatten

private theorem nonAlphaItemsFlatten_eq_filter
    (I : ExactCoverInput) (codes : List Nat) :
    (codes.map fun code => nonAlphaItemExecutable (I, code)).flatten =
      codes.filter (fun code => !isAlphaCodeBool (I, code)) := by
  induction codes with
  | nil => rfl
  | cons code codes inductionHypothesis =>
      rw [List.map_cons, List.flatten_cons]
      cases alphaBool : isAlphaCodeBool (I, code)
      · have head : nonAlphaItemExecutable (I, code) = [code] := by
          simp [nonAlphaItemExecutable, alphaBool]
        rw [head, inductionHypothesis]
        simp [alphaBool]
      · have head : nonAlphaItemExecutable (I, code) = [] := by
          simp [nonAlphaItemExecutable, alphaBool]
        rw [head, inductionHypothesis]
        simp [alphaBool]

theorem nonAlphaCodesExecutable_eq_legacy (I : ExactCoverInput) :
    nonAlphaCodesExecutable I = compactNonAlphaCodes I := by
  classical
  unfold compactNonAlphaCodes
  rw [nonAlphaCodesExecutable,
    Program.contextListMapExecutable_eq_map
      (C := exactCoverStructuredEncodedType) (X := EncodedType.nat),
    positionCodesExecutable_eq_legacy]
  calc
    (List.map nonAlphaItemExecutable
          (List.map (fun code : Nat => (I, code)) (compactPositionCodes I))).flatten =
        (compactPositionCodes I).filter
          (fun code => !isAlphaCodeBool (I, code)) := by
      simpa [List.map_map, Function.comp_def] using
        nonAlphaItemsFlatten_eq_filter I (compactPositionCodes I)
    _ = (compactPositionCodes I).filter
          (fun code => decide (¬ compactIsAlphaCode I code)) := by
      apply List.filter_congr
      intro code _codeMember
      by_cases alpha : compactIsAlphaCode I code
      · have alphaBool : isAlphaCodeBool (I, code) = true :=
          (isAlphaCodeBool_eq_true_iff I code).2 alpha
        simp [alphaBool, alpha]
      · have alphaBool : isAlphaCodeBool (I, code) = false := by
          cases value : isAlphaCodeBool (I, code)
          · rfl
          · exact False.elim
              (alpha ((isAlphaCodeBool_eq_true_iff I code).1 value))
        simp [alphaBool, alpha]

theorem nonAlphaCodesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType natListEncodedType
      nonAlphaCodesExecutable := by
  have packed : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.prod exactCoverStructuredEncodedType natListEncodedType)
      (fun input : ExactCoverInput => (input, positionCodesExecutable input)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id exactCoverStructuredEncodedType)
      positionCodesExecutable_tmPolyTime
  have attached : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list elementInputEncodedType)
      (fun input : ExactCoverInput =>
        Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (input, positionCodesExecutable input)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime
        exactCoverStructuredEncodedType EncodedType.nat) packed
    simpa [Function.comp, elementInputEncodedType, natListEncodedType] using composed
  have mapped : TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list natListEncodedType)
      (fun input : ExactCoverInput =>
        (Program.contextListMapExecutable
          (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
          (input, positionCodesExecutable input)).map nonAlphaItemExecutable) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map nonAlphaItemExecutable_tmPolyTime) attached
    simpa [Function.comp, elementInputEncodedType, natListEncodedType] using composed
  have composed := TMPolyTimeMap.comp
    (Program.listFlatten_tmPolyTime EncodedType.nat) mapped
  simpa [nonAlphaCodesExecutable, Function.comp, natListEncodedType] using composed

assert_standard_axioms
  compactSupportExecutable_eq_legacy,
  compactSupportExecutable_tmPolyTime,
  firstContainingSetIndexExecutable_eq_legacy,
  firstContainingSetIndexExecutable_tmPolyTime,
  alphaCodesExecutable_eq_legacy,
  alphaCodesExecutable_tmPolyTime,
  isAlphaCodeBool_eq_true_iff,
  isAlphaCodeBool_tmPolyTime,
  isNonAlphaCodeBool_eq_true_iff,
  isNonAlphaCodeBool_tmPolyTime,
  positionCodesExecutable_eq_legacy,
  positionCodesExecutable_tmPolyTime,
  compactNextInSetExecutable_eq_legacy,
  compactNextInSetExecutable_tmPolyTime,
  nonAlphaCodesExecutable_eq_legacy,
  nonAlphaCodesExecutable_tmPolyTime

end Foundations
end ExactCoverToThreeDimensionalMatchingTM
end Domain
end ComplexityReduction
