/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.Core.IncidenceIR
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor.ExactCover

/-!
Source-specific semantic bridge from legacy structured set systems to the
canonical `Domain.IncidenceIR` exact-cover endpoint.

This file does not define an executable adapter, cost, TM, or route. It merely
identifies the source's existing membership-pair incidence data and transports
the retained exact-cover semantics to the hub predicate. The hub itself stays
independent of `SetSystemInput` and all legacy route assembly.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceIRSetSystemBridge

open ComplexityReduction.Combinatorics
open ComplexityReduction

/-- The source-specific canonical incidence value, retaining set-family indices as right vertices. -/
def toIncidenceIR (input : SetSystemInput) : IncidenceIR :=
  IncidenceIR.mk input.universeSize input.sets.length (SetSystem.membershipPairs input)

/-- Existing source well-formedness proves the canonical incidence-table bounds. -/
theorem toIncidenceIR_wellFormed {input : SetSystemInput}
    (wellFormed : SetSystemWellFormed input) :
    (toIncidenceIR input).WellFormed := by
  simpa [toIncidenceIR, IncidenceIR.WellFormed, IncidenceIR.leftSize,
    IncidenceIR.rightSize, IncidenceIR.membershipPairs] using
    SetSystem.membershipPairs_bounds wellFormed

/-- The canonical incidence-table bounds retain exactly the source set-system bounds. -/
theorem toIncidenceIR_wellFormed_iff (input : SetSystemInput) :
    (toIncidenceIR input).WellFormed ↔ SetSystemWellFormed input := by
  constructor
  · intro hubWellFormed set setMember element elementMember
    rcases List.mem_iff_getElem.mp setMember with ⟨index, indexBound, indexValue⟩
    have pairMember : (element, index) ∈ SetSystem.membershipPairs input :=
      SetSystem.mem_membershipPairs_iff.mpr ⟨set, by
        rw [List.getElem?_eq_getElem indexBound, indexValue], elementMember⟩
    exact (hubWellFormed (element, index) (by
      simpa [toIncidenceIR, IncidenceIR.membershipPairs] using pairMember)).1
  · exact toIncidenceIR_wellFormed

private theorem selectedRight_nodup {input : SetSystemInput} {selected : List Nat}
    (selectedNodup : selected.Nodup)
    (selectedBounds : ∀ right ∈ selected, right < input.sets.length) :
    (selected.attach.map fun entry : { right // right ∈ selected } =>
      (⟨entry.val, selectedBounds entry.val entry.property⟩ : Fin input.sets.length)).Nodup := by
  apply selectedNodup.attach.map
  intro first second equality
  apply Subtype.ext
  exact congrArg Fin.val equality

/--
The source's index-based exact-cover semantics coincide with the canonical
incidence-hub predicate. This reuses the existing source membership-pair
normalization; no `UniversalRelIR` result is treated as an executable adapter.
-/
theorem existsExactCoverIndex_iff_incidenceIR (input : SetSystemInput)
    (wellFormed : SetSystemWellFormed input) :
    SetSystem.ExistsExactCoverIndex input ↔ IncidenceIR.ExistsExactCover (toIncidenceIR input) := by
  constructor
  · rintro ⟨selected, selectedNodup, selectedBounds, covers⟩
    let selectedRight : List (IncidenceIR.RightVertex (toIncidenceIR input)) :=
      selected.attach.map fun entry : { right // right ∈ selected } =>
        ⟨entry.val, selectedBounds entry.val entry.property⟩
    refine ⟨toIncidenceIR_wellFormed wellFormed, selectedRight,
      selectedRight_nodup selectedNodup selectedBounds, ?_⟩
    intro left
    rcases covers left.val left.isLt with ⟨right, rightSelected, member, unique⟩
    let boundedRight : IncidenceIR.RightVertex (toIncidenceIR input) :=
      ⟨right, selectedBounds right rightSelected⟩
    refine ⟨boundedRight, ?_, ?_⟩
    · constructor
      · unfold selectedRight
        apply List.mem_map.mpr
        exact ⟨⟨right, rightSelected⟩, by simp, rfl⟩
      · exact SetSystem.mem_membershipPairs_iff.mpr member
    · intro other otherWitness
      rcases otherWitness with ⟨otherSelected, otherMembership⟩
      have otherSelectedNat : other.val ∈ selected := by
        unfold selectedRight at otherSelected
        rcases List.mem_map.mp otherSelected with ⟨entry, _entryMember, equality⟩
        have valueEquality : entry.val = other.val := congrArg Fin.val equality
        rw [← valueEquality]
        exact entry.property
      have otherMember : SetSystem.IndexedMembership input left.val other.val :=
        SetSystem.mem_membershipPairs_iff.mp otherMembership
      have valueEquality : other.val = right := unique other.val otherSelectedNat otherMember
      apply Fin.ext
      simpa [boundedRight] using valueEquality
  · rintro ⟨_hubWellFormed, selectedRight, selectedNodup, covers⟩
    let selected : List Nat := selectedRight.map Fin.val
    refine ⟨selected, selectedNodup.map Fin.val_injective, ?_, ?_⟩
    · intro right rightSelected
      rcases List.mem_map.mp rightSelected with ⟨boundedRight, _member, equality⟩
      rw [← equality]
      exact boundedRight.isLt
    · intro left leftBound
      let boundedLeft : IncidenceIR.LeftVertex (toIncidenceIR input) := ⟨left, leftBound⟩
      rcases covers boundedLeft with ⟨boundedRight, ⟨boundedSelected, boundedMember⟩, unique⟩
      refine ⟨boundedRight.val, ?_, ?_, ?_⟩
      · unfold selected
        exact List.mem_map.mpr ⟨boundedRight, boundedSelected, rfl⟩
      · exact SetSystem.mem_membershipPairs_iff.mp boundedMember
      · intro other otherSelected otherMember
        unfold selected at otherSelected
        rcases List.mem_map.mp otherSelected with ⟨otherRight, otherRightSelected, equality⟩
        have otherIndexed :
            SetSystem.IndexedMembership input boundedLeft.val otherRight.val := by
          change SetSystem.IndexedMembership input left otherRight.val
          rw [equality]
          exact otherMember
        have otherRightMember :
            IncidenceIR.Membership (toIncidenceIR input) boundedLeft otherRight :=
          SetSystem.mem_membershipPairs_iff.mpr otherIndexed
        have sameRight : otherRight = boundedRight :=
          unique otherRight ⟨otherRightSelected, otherRightMember⟩
        exact equality.symm.trans (congrArg Fin.val sameRight)

/-- Existing erased incidence-view semantics transport to the canonical typed hub. -/
theorem legacyIncidence_iff_incidenceIR (input : SetSystemInput)
    (wellFormed : SetSystemWellFormed input) :
    IncidenceView.ExistsExactCover (SetSystem.setSystemIncidenceView input) ↔
      IncidenceIR.ExistsExactCover (toIncidenceIR input) :=
  (SetSystem.existsExactCoverIndex_iff_incidence input).symm.trans
    (existsExactCoverIndex_iff_incidenceIR input wellFormed)

/-- The source Exact Cover theorem reaches the canonical incidence endpoint through existing evidence. -/
theorem exactCover_iff_incidenceIR {input : SetSystemInput}
    (wellFormed : SetSystemWellFormed input) :
    ExactCover { system := input } ↔ IncidenceIR.ExistsExactCover (toIncidenceIR input) :=
  (ExactCoverToExactlyOneNeighbor.exactCover_iff_incidence wellFormed).trans
    (legacyIncidence_iff_incidenceIR input wellFormed)

/-- The V2 structured Exact Cover endpoint has the same source-specific hub semantics. -/
theorem structuredExactCover_accepts_iff_incidenceIR {input : SetSystemInput}
    (wellFormed : SetSystemWellFormed input) :
    Presentation.SetSystem.exactCoverStructuredProblem.accepts { system := input } ↔
      IncidenceIR.ExistsExactCover (toIncidenceIR input) := by
  simpa using exactCover_iff_incidenceIR wellFormed

end IncidenceIRSetSystemBridge
end Domain
end ComplexityReduction
