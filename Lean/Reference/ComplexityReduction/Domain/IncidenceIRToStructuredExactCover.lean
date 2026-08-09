/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.IncidenceIR
import ComplexityReduction.Domain.Core.IncidenceIRValidation
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Legacy.IR.Domains.SetSystem
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor.ExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part2

/-!
Canonical semantic construction for the `IncidenceIR -> structured Exact Cover`
egress.  Every right-vertex index receives one set containing precisely its
listed left neighbours; indices with no members are retained as empty sets.

The public executable is total: malformed raw incidence inputs are sent to a
fixed Exact-Cover no-instance.  On well-formed inputs it is definitionally the
canonical materialization below.  Its direct-TM/program proof is constructed
in a companion only after it is tied to this exact guarded executable and
these semantic lemmas.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceIRToStructuredExactCover

open ComplexityReduction.Combinatorics

/-- Collect the left neighbours of one retained right-vertex identity. -/
def membersOf (right : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | pair :: pairs =>
      if pair.2 = right then pair.1 :: membersOf right pairs else membersOf right pairs

/-- Materialize every right vertex, including isolated ones, as one ordered set. -/
def setFamily (input : IncidenceIR) : List (List Nat) :=
  (List.range input.rightSize).map (fun right => membersOf right input.membershipPairs)

/-- The exact structured set-system carrier represented by the incidence hub. -/
def toSetSystem (input : IncidenceIR) : SetSystemInput where
  universeSize := input.leftSize
  sets := setFamily input

/-- The exact structured Exact-Cover materialization before source validation. -/
def coreExecutable (input : IncidenceIR) : ExactCoverInput where
  system := toSetSystem input

/-- A fixed non-yes Exact-Cover target for malformed raw incidence tables. -/
def noTarget : ExactCoverInput :=
  ComplexityReduction.Karp21.ExactCover.noInput

/--
The total egress executable.  A raw incidence table must satisfy its canonical
hub bounds before the materialized set system can receive trusted semantics.
-/
def executable (input : IncidenceIR) : ExactCoverInput :=
  if IncidenceIRValidation.wellFormedBool input then coreExecutable input else noTarget

/-- A grouped member is present precisely at its retained pair identity. -/
theorem mem_membersOf_iff (right element : Nat) (pairs : List (Nat × Nat)) :
    element ∈ membersOf right pairs ↔ (element, right) ∈ pairs := by
  induction pairs with
  | nil => simp [membersOf]
  | cons pair pairs ih =>
      by_cases h : pair.2 = right
      · simp only [membersOf, if_pos h, List.mem_cons, ih]
        constructor
        · rintro (element_eq | member)
          · left
            apply Prod.ext
            · exact element_eq
            · exact h.symm
          · exact Or.inr member
        · rintro (pair_eq | member)
          · exact Or.inl (congrArg Prod.fst pair_eq)
          · exact Or.inr member
      · simp only [membersOf, if_neg h, ih, List.mem_cons]
        constructor
        · intro member
          exact Or.inr member
        · rintro (pair_eq | member)
          · have right_eq : pair.2 = right := (congrArg Prod.snd pair_eq).symm
            exact False.elim (h right_eq)
          · exact member

/-- The set family has exactly one position for every retained right identity. -/
theorem setFamily_length (input : IncidenceIR) :
    (setFamily input).length = input.rightSize := by
  simp [setFamily]

/-- A bounded right index addresses exactly its materialized neighbour set. -/
theorem setFamily_getElem (input : IncidenceIR) (right : Nat) (bound : right < input.rightSize) :
    (setFamily input)[right]'(by rw [setFamily_length]; exact bound) =
      membersOf right input.membershipPairs := by
  simp [setFamily]

/-- Membership in a materialized right set is exactly incidence membership. -/
theorem setFamily_membership_iff (input : IncidenceIR) (left right : Nat)
    (rightBound : right < input.rightSize) :
    left ∈ (setFamily input)[right]'(by rw [setFamily_length]; exact rightBound) ↔
      (left, right) ∈ input.membershipPairs := by
  rw [setFamily_getElem input right rightBound]
  exact mem_membersOf_iff right left input.membershipPairs

/-- Incidence well-formedness makes the materialized Exact-Cover set system well formed. -/
theorem toSetSystem_wellFormed {input : IncidenceIR} (wellFormed : input.WellFormed) :
    SetSystemWellFormed (toSetSystem input) := by
  intro set setMember element elementMember
  rcases List.mem_iff_getElem.mp setMember with ⟨right, rightBound, rightValue⟩
  have rawRightBound : right < input.rightSize := by
    simpa [toSetSystem, setFamily_length] using rightBound
  have groupedMember :
      element ∈ (setFamily input)[right]'(by rw [setFamily_length]; exact rawRightBound) := by
    have groupedValue :
        (setFamily input)[right]'(by rw [setFamily_length]; exact rawRightBound) = set := by
      simpa [toSetSystem] using rightValue
    rw [groupedValue]
    exact elementMember
  have pairMember : (element, right) ∈ input.membershipPairs :=
    (setFamily_membership_iff input element right rawRightBound).mp groupedMember
  exact (wellFormed (element, right) pairMember).1

/-- The legacy index witness predicate is exactly the canonical incidence relation. -/
theorem indexedMembership_iff (input : IncidenceIR) (left right : Nat)
    (rightBound : right < input.rightSize) :
    ComplexityReduction.SetSystem.IndexedMembership (toSetSystem input) left right ↔
      (left, right) ∈ input.membershipPairs := by
  constructor
  · rintro ⟨set, getSet, leftMember⟩
    have indexBound : right < (toSetSystem input).sets.length := by
      simpa [toSetSystem, setFamily_length] using rightBound
    have setValue :
        (setFamily input)[right]'(by rw [setFamily_length]; exact rightBound) = set := by
      have getValue := List.getElem?_eq_getElem indexBound
      simpa [toSetSystem] using getValue.symm.trans getSet
    have groupedMember :
        left ∈ (setFamily input)[right]'(by rw [setFamily_length]; exact rightBound) := by
      rw [setValue]
      exact leftMember
    exact (setFamily_membership_iff input left right rightBound).mp groupedMember
  · intro pairMember
    refine ⟨(setFamily input)[right]'(by rw [setFamily_length]; exact rightBound), ?_, ?_⟩
    · have indexBound : right < (toSetSystem input).sets.length := by
        simpa [toSetSystem, setFamily_length] using rightBound
      exact List.getElem?_eq_getElem indexBound
    · exact (setFamily_membership_iff input left right rightBound).mpr pairMember

private theorem selectedRight_nodup {input : IncidenceIR} {selected : List Nat}
    (selectedNodup : selected.Nodup)
    (selectedBounds : ∀ right ∈ selected, right < input.rightSize) :
    (selected.attach.map fun entry : { right // right ∈ selected } =>
      (⟨entry.val, selectedBounds entry.val entry.property⟩ : IncidenceIR.RightVertex input)).Nodup := by
  apply selectedNodup.attach.map
  intro first second equality
  apply Subtype.ext
  exact congrArg Fin.val equality

/-- Index-based exact covers of the materialized system are exactly IncidenceIR exact covers. -/
theorem existsExactCoverIndex_iff_incidenceIR (input : IncidenceIR)
    (wellFormed : input.WellFormed) :
    ComplexityReduction.SetSystem.ExistsExactCoverIndex (toSetSystem input) ↔
      input.ExistsExactCover := by
  constructor
  · rintro ⟨selected, selectedNodup, selectedBounds, covers⟩
    let selectedRight : List (IncidenceIR.RightVertex input) :=
      selected.attach.map fun entry : { right // right ∈ selected } =>
        ⟨entry.val, by
          have hLength : (toSetSystem input).sets.length = input.rightSize := by
            simp [toSetSystem, setFamily_length]
          exact hLength ▸ selectedBounds entry.val entry.property⟩
    refine ⟨wellFormed, selectedRight, ?_, ?_⟩
    · unfold selectedRight
      exact selectedRight_nodup (input := input) selectedNodup (by
        intro right rightSelected
        have hLength : (toSetSystem input).sets.length = input.rightSize := by
          simp [toSetSystem, setFamily_length]
        exact hLength ▸ selectedBounds right rightSelected)
    · intro left
      rcases covers left.val left.isLt with ⟨right, rightSelected, member, unique⟩
      have rightBound : right < input.rightSize := by
        have hLength : (toSetSystem input).sets.length = input.rightSize := by
          simp [toSetSystem, setFamily_length]
        exact hLength ▸ selectedBounds right rightSelected
      let boundedRight : IncidenceIR.RightVertex input := ⟨right, rightBound⟩
      refine ⟨boundedRight, ?_, ?_⟩
      · constructor
        · unfold selectedRight
          apply List.mem_map.mpr
          exact ⟨⟨right, rightSelected⟩, by simp, rfl⟩
        · exact (indexedMembership_iff input left.val right rightBound).mp member
      · intro other otherWitness
        rcases otherWitness with ⟨otherSelected, otherMembership⟩
        have otherSelectedNat : other.val ∈ selected := by
          unfold selectedRight at otherSelected
          rcases List.mem_map.mp otherSelected with ⟨entry, _entryMember, equality⟩
          have valueEquality : entry.val = other.val := congrArg Fin.val equality
          rw [← valueEquality]
          exact entry.property
        have otherMember : ComplexityReduction.SetSystem.IndexedMembership
            (toSetSystem input) left.val other.val :=
          (indexedMembership_iff input left.val other.val other.isLt).mpr otherMembership
        have valueEquality : other.val = right := unique other.val otherSelectedNat otherMember
        apply Fin.ext
        simpa [boundedRight] using valueEquality
  · rintro ⟨_hubWellFormed, selectedRight, selectedNodup, covers⟩
    let selected : List Nat := selectedRight.map Fin.val
    refine ⟨selected, selectedNodup.map Fin.val_injective, ?_, ?_⟩
    · intro right rightSelected
      rcases List.mem_map.mp rightSelected with ⟨boundedRight, _member, equality⟩
      rw [← equality]
      change boundedRight.val < (setFamily input).length
      rw [setFamily_length]
      exact boundedRight.isLt
    · intro left leftBound
      let boundedLeft : IncidenceIR.LeftVertex input := ⟨left, leftBound⟩
      rcases covers boundedLeft with ⟨boundedRight, ⟨boundedSelected, boundedMember⟩, unique⟩
      refine ⟨boundedRight.val, ?_, ?_, ?_⟩
      · unfold selected
        exact List.mem_map.mpr ⟨boundedRight, boundedSelected, rfl⟩
      · exact (indexedMembership_iff input left boundedRight.val boundedRight.isLt).mpr boundedMember
      · intro other otherSelected otherMember
        unfold selected at otherSelected
        rcases List.mem_map.mp otherSelected with ⟨otherRight, otherRightSelected, equality⟩
        have otherIndexed : ComplexityReduction.SetSystem.IndexedMembership
            (toSetSystem input) boundedLeft.val otherRight.val := by
          change ComplexityReduction.SetSystem.IndexedMembership (toSetSystem input) left otherRight.val
          rw [equality]
          exact otherMember
        have otherRightMember : IncidenceIR.Membership input boundedLeft otherRight :=
          (indexedMembership_iff input left otherRight.val otherRight.isLt).mp otherIndexed
        have sameRight : otherRight = boundedRight :=
          unique otherRight ⟨otherRightSelected, otherRightMember⟩
        exact equality.symm.trans (congrArg Fin.val sameRight)

/-- On a well-formed hub input, the total executable is the canonical materialization. -/
theorem executable_eq_core {input : IncidenceIR} (wellFormed : input.WellFormed) :
    executable input = coreExecutable input := by
  simp [executable,
    (IncidenceIRValidation.wellFormedBool_eq_true_iff input).mpr wellFormed]

/-- The unguarded materialization preserves exact-cover semantics on valid hub inputs. -/
theorem coreExactCover_iff_incidenceIR (input : IncidenceIR) (wellFormed : input.WellFormed) :
    Presentation.SetSystem.exactCoverStructuredProblem.accepts (coreExecutable input) ↔
      input.ExistsExactCover := by
  change ExactCover { system := toSetSystem input } ↔ input.ExistsExactCover
  exact
    (_root_.ComplexityReduction.ExactCoverToExactlyOneNeighbor.exactCover_iff_existsExactCoverIndex
      (toSetSystem_wellFormed wellFormed)).trans
      (existsExactCoverIndex_iff_incidenceIR input wellFormed)

/-- The guarded structured egress is a total equivalence at its exact endpoints. -/
theorem exactCover_iff_incidenceIR (input : IncidenceIR) :
    Presentation.SetSystem.exactCoverStructuredProblem.accepts (executable input) ↔
      input.ExistsExactCover := by
  constructor
  · intro targetAccepts
    by_cases wellFormed : input.WellFormed
    · have coreAccepts :
        Presentation.SetSystem.exactCoverStructuredProblem.accepts (coreExecutable input) := by
        simpa [executable,
          (IncidenceIRValidation.wellFormedBool_eq_true_iff input).mpr wellFormed] using
          targetAccepts
      exact (coreExactCover_iff_incidenceIR input wellFormed).mp coreAccepts
    · have guardFalse : IncidenceIRValidation.wellFormedBool input = false := by
        cases guard : IncidenceIRValidation.wellFormedBool input with
        | false => rfl
        | true => exact (wellFormed
            ((IncidenceIRValidation.wellFormedBool_eq_true_iff input).mp guard)).elim
      have impossible : ExactCover noTarget := by
        simpa [executable, guardFalse] using targetAccepts
      exact (ComplexityReduction.Karp21.ExactCover.noInput_isNo (by
        simpa [noTarget] using impossible)).elim
  · intro sourceAccepts
    have coreAccepts :
        Presentation.SetSystem.exactCoverStructuredProblem.accepts (coreExecutable input) :=
      (coreExactCover_iff_incidenceIR input sourceAccepts.1).mpr sourceAccepts
    simpa [executable,
      (IncidenceIRValidation.wellFormedBool_eq_true_iff input).mpr sourceAccepts.1] using
      coreAccepts

end IncidenceIRToStructuredExactCover
end Domain
end ComplexityReduction
