/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering

/-!
Fourth P15b target: Set Covering to Hitting Set.
-/

namespace ComplexityReduction
namespace Karp21
namespace HittingSet

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/--
In the dual hitting-set instance, one set is created for every original universe
element; it contains the indices of the original sets that cover that element.
-/
def indicesContaining (I : SetCoveringInput) (x : Nat) : List Nat :=
  I.system.sets.findIdxs fun S => decide (x ∈ S)

theorem mem_indicesContaining_iff (I : SetCoveringInput) (x j : Nat) :
    j ∈ indicesContaining I x ↔
      j < I.system.sets.length ∧ x ∈ I.system.sets.getD j [] := by
  constructor
  · intro hj
    rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.system.sets)
        (p := fun S : List Nat => decide (x ∈ S))).1 hj with
      ⟨hjLt, hPred⟩
    refine ⟨hjLt, ?_⟩
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hjLt]
    exact of_decide_eq_true hPred
  · rintro ⟨hjLt, hx⟩
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hjLt] at hx
    exact
      (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.system.sets)
        (p := fun S : List Nat => decide (x ∈ S))).2
        ⟨hjLt, by exact decide_eq_true hx⟩

/-- Dual set-system used by the standard Set Covering to Hitting Set reduction. -/
def dualSystem (I : SetCoveringInput) : SetSystemInput where
  universeSize := I.system.sets.length
  sets := (List.range I.system.universeSize).map (indicesContaining I)

theorem mem_dualSystem_sets_iff (I : SetCoveringInput) (S : List Nat) :
    S ∈ (dualSystem I).sets ↔
      ∃ x, x < I.system.universeSize ∧ S = indicesContaining I x := by
  constructor
  · intro hS
    rcases List.mem_map.mp hS with ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩

/-- P15b syntax map from Set Covering to the dual Hitting Set instance. -/
def map (I : SetCoveringInput) : HittingSetInput where
  system := dualSystem I
  k := I.k

theorem map_correct (I : SetCoveringInput) :
    setCoveringDecisionProblem.isYes I ↔ HittingSet (map I) := by
  constructor
  · rintro ⟨selected, hLen, hFamily, hCovers⟩
    let hitting := selected.map fun S => I.system.sets.idxOf S
    refine ⟨hitting, by simpa [hitting] using hLen, ?_, ?_⟩
    · intro j hj
      rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
      exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
    · intro T hT
      rcases (mem_dualSystem_sets_iff I T).1 hT with ⟨x, hx, rfl⟩
      rcases hCovers x hx with ⟨S, hSSelected, hxS⟩
      refine ⟨I.system.sets.idxOf S, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨S, hSSelected, rfl⟩
      · rw [mem_indicesContaining_iff]
        refine ⟨List.idxOf_lt_length_iff.mpr (hFamily S hSSelected), ?_⟩
        rw [List.getD_eq_getElem
          (l := I.system.sets) (d := [])
          (List.idxOf_lt_length_iff.mpr (hFamily S hSSelected))]
        simpa [List.idxOf_get] using hxS
  · rintro ⟨hitting, hLen, hBounds, hHits⟩
    let selected := hitting.map fun j => I.system.sets.getD j []
    refine ⟨selected, by simpa [selected] using hLen, ?_, ?_⟩
    · intro S hS
      rcases List.mem_map.mp hS with ⟨j, hj, rfl⟩
      have hjLen : j < I.system.sets.length := by
        simpa [map, dualSystem] using hBounds j hj
      rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hjLen]
      exact List.getElem_mem _
    · intro x hx
      have hDualMem : indicesContaining I x ∈ (dualSystem I).sets :=
        (mem_dualSystem_sets_iff I (indicesContaining I x)).2 ⟨x, hx, rfl⟩
      rcases hHits (indicesContaining I x) hDualMem with ⟨j, hj, hjx⟩
      refine ⟨I.system.sets.getD j [], ?_, ?_⟩
      · exact List.mem_map.mpr ⟨j, hj, rfl⟩
      · exact (mem_indicesContaining_iff I x j).1 hjx |>.2

/-- Each dual incidence list is no longer than the source family. -/
theorem indicesContaining_length_le (I : SetCoveringInput) (x : Nat) :
    (indicesContaining I x).length ≤ I.system.sets.length := by
  unfold indicesContaining
  simpa using
    (List.countP_le_length (l := I.system.sets)
      (p := fun S : List Nat => decide (x ∈ S)))

/-- Structured size of one dual incidence set is quadratic in the source family size. -/
theorem indicesContaining_structured_inputSize_le (I : SetCoveringInput) (x : Nat) :
    setStructuredEncodedType.inputSize (indicesContaining I x) ≤
      I.system.sets.length * (I.system.sets.length + 2) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      EncodedType.nat (indicesContaining I x) (I.system.sets.length + 1)
      (by
        intro j hj
        have hjLt := (mem_indicesContaining_iff I x j).1 hj |>.1
        simp [EncodedType.inputSize, EncodedType.nat]
        omega)
  have hLen := indicesContaining_length_le I x
  exact hList.trans (by
    have hMul := Nat.mul_le_mul_right (I.system.sets.length + 2) hLen
    simpa [setStructuredEncodedType, Nat.add_assoc] using hMul)

/-- Structured size of the dual family is polynomial in source universe and family sizes. -/
theorem dualSystem_family_structured_inputSize_le (I : SetCoveringInput) :
    setFamilyStructuredEncodedType.inputSize (dualSystem I).sets ≤
      I.system.universeSize *
        (I.system.sets.length * (I.system.sets.length + 2) + 1) := by
  have hList :=
    ComplexityReduction.Karp21.VertexCover.encodedList_inputSize_le_length_mul_bound
      setStructuredEncodedType (dualSystem I).sets
      (I.system.sets.length * (I.system.sets.length + 2))
      (by
        intro S hS
        rcases (mem_dualSystem_sets_iff I S).1 hS with ⟨x, _hx, rfl⟩
        exact indicesContaining_structured_inputSize_le I x)
  have hLen : (dualSystem I).sets.length = I.system.universeSize := by
    simp [dualSystem]
  exact hList.trans (by
    exact Nat.mul_le_mul_right
      (I.system.sets.length * (I.system.sets.length + 2) + 1)
      (le_of_eq hLen))

/-- Structured size of the dual set-system is polynomial in source dimensions. -/
theorem dualSystem_structured_inputSize_le (I : SetCoveringInput) :
    setSystemStructuredEncodedType.inputSize (dualSystem I) ≤
      I.system.sets.length +
        I.system.universeSize *
          (I.system.sets.length * (I.system.sets.length + 2) + 1) + 2 := by
  have hFamily := dualSystem_family_structured_inputSize_le I
  rw [SetCovering.setSystemStructured_inputSize_eq]
  change
    I.system.sets.length + setFamilyStructuredEncodedType.inputSize (dualSystem I).sets + 2 ≤
      I.system.sets.length +
        I.system.universeSize *
          (I.system.sets.length * (I.system.sets.length + 2) + 1) + 2
  omega

/-- Exact structured Hitting Set input size under the project-local field encoding. -/
theorem hittingSetStructured_inputSize_eq (I : HittingSetInput) :
    hittingSetStructuredEncodedType.inputSize I =
      setSystemStructuredEncodedType.inputSize I.system + I.k + 2 := by
  change hittingSetTupleStructuredEncodedType.inputSize (I.system, I.k) =
    setSystemStructuredEncodedType.inputSize I.system + I.k + 2
  simp [hittingSetTupleStructuredEncodedType]
  omega

theorem setCoveringStructured_inputSize_ge_universeSize (I : SetCoveringInput) :
    I.system.universeSize ≤ setCoveringStructuredEncodedType.inputSize I := by
  rw [SetCovering.setCoveringStructured_inputSize_eq,
    SetCovering.setSystemStructured_inputSize_eq]
  omega

theorem setCoveringStructured_inputSize_ge_sets_length (I : SetCoveringInput) :
    I.system.sets.length ≤ setCoveringStructuredEncodedType.inputSize I := by
  have hSets :
      I.system.sets.length ≤ setFamilyStructuredEncodedType.inputSize I.system.sets := by
    simpa [setFamilyStructuredEncodedType, EncodedType.inputSize] using
      (TM2Programs.listEncode_length_ge_length setStructuredEncodedType I.system.sets)
  rw [SetCovering.setCoveringStructured_inputSize_eq,
    SetCovering.setSystemStructured_inputSize_eq]
  omega

theorem setCoveringStructured_inputSize_ge_budget (I : SetCoveringInput) :
    I.k ≤ setCoveringStructuredEncodedType.inputSize I := by
  rw [SetCovering.setCoveringStructured_inputSize_eq]
  omega

/-- Structured output size of the Set-Covering-to-Hitting-Set map is polynomial in
the structured source size. -/
theorem hittingSetStructured_inputSize_map_le_setCovering_poly (I : SetCoveringInput) :
    hittingSetStructuredEncodedType.inputSize (map I) ≤
      10 * (setCoveringStructuredEncodedType.inputSize I + 1) ^ 3 + 20 := by
  let S := setCoveringStructuredEncodedType.inputSize I
  have hSystem := dualSystem_structured_inputSize_le I
  have hU : I.system.universeSize ≤ S :=
    setCoveringStructured_inputSize_ge_universeSize I
  have hM : I.system.sets.length ≤ S :=
    setCoveringStructured_inputSize_ge_sets_length I
  have hK : I.k ≤ S := setCoveringStructured_inputSize_ge_budget I
  have hM2 : I.system.sets.length + 2 ≤ S + 2 := Nat.add_le_add_right hM 2
  have hMM :
      I.system.sets.length * (I.system.sets.length + 2) ≤ S * (S + 2) :=
    Nat.mul_le_mul hM hM2
  have hUMM :
      I.system.universeSize *
          (I.system.sets.length * (I.system.sets.length + 2)) ≤
        S * (S * (S + 2)) := by
    exact Nat.mul_le_mul hU hMM
  have hFamilyTerm :
      I.system.universeSize *
          (I.system.sets.length * (I.system.sets.length + 2) + 1) ≤
        S * (S * (S + 2)) + S := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add hUMM hU
  calc
    hittingSetStructuredEncodedType.inputSize (map I)
        = setSystemStructuredEncodedType.inputSize (dualSystem I) + I.k + 2 := by
            simp [map, hittingSetStructured_inputSize_eq]
    _ ≤ (I.system.sets.length +
          I.system.universeSize *
            (I.system.sets.length * (I.system.sets.length + 2) + 1) + 2) +
          I.k + 2 := by
            omega
    _ ≤ S + (S * (S * (S + 2)) + S) + 2 + S + 2 := by
            omega
    _ ≤ 10 * (S + 1) ^ 3 + 20 := by
            nlinarith

/-- Polynomial output-size bound for the structured Set-Covering-to-Hitting-Set map. -/
theorem setCoveringToHittingSetStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : SetCoveringInput => setCoveringStructuredEncodedType.inputSize I)
      (fun J : HittingSetInput => hittingSetStructuredEncodedType.inputSize J)
      map := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro I
  let S := setCoveringStructuredEncodedType.inputSize I
  have hBase := hittingSetStructured_inputSize_map_le_setCovering_poly I
  have hPoly : 10 * (S + 1) ^ 3 + 20 ≤ 1000 * S ^ 3 + 1000 := by
    cases S with
    | zero =>
        norm_num
    | succ S =>
        ring_nf
        omega
  exact hBase.trans hPoly

/--
Proof-carrying TM2/costed reduction for the current raw-encoded Hitting Set
target.  This is not a natural-language encoding conformance theorem.
-/
noncomputable def setCoveringToHittingSetTMBackedKarpReduction :
    TMBackedCostedReduction setCoveringDecisionProblem hittingSetDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    (TMBackedCostedMap.rawCodomain setCoveringDecisionProblem.Instance HittingSetInput map)
    map_correct

/-- Costed Karp reduction from Set Covering to Hitting Set. -/
noncomputable def setCoveringToHittingSetKarpReduction :
    KarpReductionM CostedPolyTimeModel setCoveringDecisionProblem hittingSetDecisionProblem :=
  setCoveringToHittingSetTMBackedKarpReduction.toCostedKarpReduction

/--
Proof-carrying composed raw-codomain reduction from Clique to Hitting Set via
Vertex Cover and Set Covering.
-/
noncomputable def cliqueToHittingSetViaSetCoveringTMBackedKarpReduction :
    TMBackedCostedReduction cliqueDecisionProblem hittingSetDecisionProblem :=
  TMBackedCostedReduction.comp
    setCoveringToHittingSetTMBackedKarpReduction
    SetCovering.cliqueToSetCoveringViaVertexCoverTMBackedKarpReduction

/-- First witness in the raw-encoding collision for Hitting Set. -/
def rawEncodingCollisionA : HittingSetInput where
  system := { universeSize := 0, sets := [] }
  k := 0

/-- Second witness in the raw-encoding collision for Hitting Set. -/
def rawEncodingCollisionB : HittingSetInput where
  system := { universeSize := 1, sets := [] }
  k := 0

theorem rawEncodingCollisionA_ne_rawEncodingCollisionB :
    rawEncodingCollisionA ≠ rawEncodingCollisionB := by
  intro h
  have hu :
      rawEncodingCollisionA.system.universeSize =
        rawEncodingCollisionB.system.universeSize :=
    congrArg (fun I : HittingSetInput => I.system.universeSize) h
  norm_num [rawEncodingCollisionA, rawEncodingCollisionB] at hu

/--
The current raw encoding for Hitting Set is not faithful: two different formal
instances encode as the same empty string.
-/
theorem hittingSetRawEncoding_not_faithful :
    ¬ hittingSetDecisionProblem.FaithfulEncoding := by
  refine EncodedDecisionProblem.EncodingCollision.not_faithful ?_
  exact
    ⟨rawEncodingCollisionA, rawEncodingCollisionB,
      rawEncodingCollisionA_ne_rawEncodingCollisionB, rfl⟩

/-- The structured finite-alphabet Hitting Set encoding is faithful. -/
theorem hittingSetStructuredEncoding_faithful :
    hittingSetStructuredDecisionProblem.FaithfulEncoding where
  injective := hittingSetStructuredEncodedType_encode_injective

theorem hittingSetStructuredEncoding_predicateRespects :
    hittingSetStructuredDecisionProblem.PredicateRespectsEncoding :=
  hittingSetStructuredEncoding_faithful.predicateRespects

theorem hittingSetStructuredEncoding_accepts_encode_iff (I : HittingSetInput) :
    hittingSetStructuredDecisionProblem.toEncodedLanguage.accepts
        (hittingSetStructuredEncodedType.encode I) ↔
      HittingSet I :=
  hittingSetStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Hitting Set is locally in NP for the project-local costed model. -/
theorem hittingSetInNP :
    InNPEnc CostedPolyTimeModel hittingSetDecisionProblem :=
  decidableInNP hittingSetDecisionProblem

/-- Local NP-completeness of Hitting Set via Set Covering. -/
theorem hittingSetNPComplete :
    NPCompleteEnc CostedPolyTimeModel hittingSetDecisionProblem :=
  NPCompleteEnc.transfer
    SetCovering.setCoveringNPComplete
    ⟨setCoveringToHittingSetKarpReduction⟩
    hittingSetInNP

end HittingSet
end Karp21
end ComplexityReduction
