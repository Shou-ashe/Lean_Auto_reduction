/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Set Covering.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

/--
Finite-certificate verifier for faithful structured Set Covering, using the
verified direct-TM Set-Covering-to-Hitting-Set map and the Hitting Set verifier.
-/
def setCoveringStructuredFiniteVerify (I : SetCoveringInput) (indices : List Nat) :
    Bool :=
  HittingSet.hittingSetStructuredFiniteVerify (HittingSet.map I) indices

theorem setCoveringStructuredFiniteVerify_eq_true_iff
    (I : SetCoveringInput) (indices : List Nat) :
    setCoveringStructuredFiniteVerify I indices = true ↔
      indices.length ≤ I.k ∧
        (∀ j ∈ indices, j < I.system.sets.length) ∧
        ∀ x, x < I.system.universeSize →
          ∃ j ∈ indices, x ∈ I.system.sets.getD j [] := by
  rw [setCoveringStructuredFiniteVerify,
    HittingSet.hittingSetStructuredFiniteVerify_eq_true_iff]
  constructor
  · rintro ⟨hLen, hWithin, hHits⟩
    refine ⟨by simpa [HittingSet.map] using hLen,
      by simpa [HittingSet.map, HittingSet.dualSystem] using hWithin, ?_⟩
    intro x hx
    have hDualMem :
        HittingSet.indicesContaining I x ∈ (HittingSet.map I).system.sets := by
      have hMem :
          HittingSet.indicesContaining I x ∈ (HittingSet.dualSystem I).sets :=
        (HittingSet.mem_dualSystem_sets_iff I (HittingSet.indicesContaining I x)).2
          ⟨x, hx, rfl⟩
      simpa [HittingSet.map] using hMem
    rcases hHits (HittingSet.indicesContaining I x) hDualMem with ⟨j, hj, hjx⟩
    exact ⟨j, hj, (HittingSet.mem_indicesContaining_iff I x j).1 hjx |>.2⟩
  · rintro ⟨hLen, hWithin, hCover⟩
    refine ⟨by simpa [HittingSet.map] using hLen,
      by simpa [HittingSet.map, HittingSet.dualSystem] using hWithin, ?_⟩
    intro S hS
    have hS' : S ∈ (HittingSet.dualSystem I).sets := by
      simpa [HittingSet.map] using hS
    rcases (HittingSet.mem_dualSystem_sets_iff I S).1 hS' with ⟨x, hx, rfl⟩
    rcases hCover x hx with ⟨j, hj, hxj⟩
    exact ⟨j, hj, (HittingSet.mem_indicesContaining_iff I x j).2
      ⟨hWithin j hj, hxj⟩⟩

theorem setCoveringStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : SetCoveringInput × List Nat =>
        setCoveringStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod setCoveringStructuredEncodedType setStructuredEncodedType
  have hInstance : TMPolyTimeMap X setCoveringStructuredEncodedType
      (fun p : SetCoveringInput × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringStructuredEncodedType setStructuredEncodedType
  have hCert : TMPolyTimeMap X setStructuredEncodedType
      (fun p : SetCoveringInput × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringStructuredEncodedType setStructuredEncodedType
  have hMapped : TMPolyTimeMap X hittingSetStructuredEncodedType
      (fun p : SetCoveringInput × List Nat => HittingSet.map p.1) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setCoveringToHittingSetStructured_tm_polytime
      hInstance
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X
      (EncodedType.prod hittingSetStructuredEncodedType setStructuredEncodedType)
      (fun p : SetCoveringInput × List Nat => (HittingSet.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp HittingSet.hittingSetStructuredFiniteVerify_tm_polytime
    hInput
  simpa [Function.comp, setCoveringStructuredFiniteVerify, X] using hComp

theorem setCoveringCertificate_inputSize_le_poly
    (I : SetCoveringInput) (indices : List Nat)
    (hLen : indices.length ≤ I.k)
    (hWithin : ∀ j ∈ indices, j < I.system.sets.length) :
    setStructuredEncodedType.inputSize indices ≤
      2 * (setCoveringStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := setCoveringStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le
    I.system.sets.length indices hWithin
  have hK : I.k ≤ S := by
    simpa [S] using HittingSet.setCoveringStructured_inputSize_ge_budget I
  have hSets : I.system.sets.length ≤ S := by
    simpa [S] using HittingSet.setCoveringStructured_inputSize_ge_sets_length I
  calc
    setStructuredEncodedType.inputSize indices
        ≤ indices.length * (I.system.sets.length + 1) := hCert
    _ ≤ I.k * (I.system.sets.length + 1) :=
        Nat.mul_le_mul_right (I.system.sets.length + 1) hLen
    _ ≤ S * (S + 1) := Nat.mul_le_mul hK (Nat.succ_le_succ hSets)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

/-- Direct finite-certificate TM verifier for faithful structured Set Covering. -/
noncomputable def setCoveringStructuredFiniteTMVerifier :
    TMVerifier setCoveringStructuredDecisionProblem where
  Cert := setStructuredEncodedType
  verify := setCoveringStructuredFiniteVerify
  verifier_polytime := setCoveringStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    have hSetCovering : setCoveringDecisionProblem.isYes I := by
      simpa [setCoveringStructuredDecisionProblem, setCoveringDecisionProblem] using hYes
    have hHit : HittingSet (HittingSet.map I) :=
      (HittingSet.map_correct I).1 hSetCovering
    rcases hHit with ⟨indices, hLen, hWithin, hHits⟩
    refine ⟨indices, ?_, ?_⟩
    · exact setCoveringCertificate_inputSize_le_poly I indices
        (by simpa [HittingSet.map] using hLen)
        (by simpa [HittingSet.map, HittingSet.dualSystem] using hWithin)
    · simpa [setCoveringStructuredFiniteVerify] using
        (HittingSet.hittingSetStructuredFiniteVerify_eq_true_iff
          (HittingSet.map I) indices).2 ⟨hLen, hWithin, hHits⟩
  sound := by
    intro I indices hVerify
    have hVerifyHit :
        HittingSet.hittingSetStructuredFiniteVerify (HittingSet.map I) indices = true := by
      simpa [setCoveringStructuredFiniteVerify] using hVerify
    have hHitParts :=
      (HittingSet.hittingSetStructuredFiniteVerify_eq_true_iff
        (HittingSet.map I) indices).1 hVerifyHit
    have hHit : HittingSet (HittingSet.map I) := ⟨indices, hHitParts⟩
    have hSetCovering := (HittingSet.map_correct I).2 hHit
    simpa [setCoveringStructuredDecisionProblem, setCoveringDecisionProblem] using hSetCovering

theorem setCoveringStructured_TMInNP :
    TMInNP setCoveringStructuredDecisionProblem :=
  TMInNP.intro setCoveringStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
