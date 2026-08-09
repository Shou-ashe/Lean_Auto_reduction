/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipClique
import ComplexityReduction.Problems.Karp21.HittingSetStandardTM

/-!
Standard direct-TM checker compositions for Set Covering, Vertex Cover, and
Clique.  Each theorem retains CR's exact executable; only the Hitting-Set
checker dependency is replaced by V2's standard-audited companion evidence.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace CliqueStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- Standard direct-TM realization of the structured Set Covering checker. -/
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
    have hComp := TMPolyTimeMap.comp HittingSet.setCoveringToHittingSetStructured_tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X
      (EncodedType.prod hittingSetStructuredEncodedType setStructuredEncodedType)
      (fun p : SetCoveringInput × List Nat => (HittingSet.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp HittingSetStandardTM.hittingSetStructuredFiniteVerify_tm_polytime
    hInput
  simpa [Function.comp, setCoveringStructuredFiniteVerify, X] using hComp

/-- Standard direct-TM realization of the structured Vertex Cover checker. -/
theorem vertexCoverStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : VertexCoverInput × List Nat =>
        VertexCover.vertexCoverStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType
  have hInstance : TMPolyTimeMap X vertexCoverStructuredEncodedType
      (fun p : VertexCoverInput × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst vertexCoverStructuredEncodedType setStructuredEncodedType
  have hCert : TMPolyTimeMap X setStructuredEncodedType
      (fun p : VertexCoverInput × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd vertexCoverStructuredEncodedType setStructuredEncodedType
  have hMapped : TMPolyTimeMap X setCoveringStructuredEncodedType
      (fun p : VertexCoverInput × List Nat => SetCovering.map p.1) := by
    have hComp := TMPolyTimeMap.comp SetCovering.vertexCoverToSetCoveringStructured_tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X
      (EncodedType.prod setCoveringStructuredEncodedType setStructuredEncodedType)
      (fun p : VertexCoverInput × List Nat => (SetCovering.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp setCoveringStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, VertexCover.vertexCoverStructuredFiniteVerify, X] using hComp

/-- Standard direct-TM realization of the structured Clique checker. -/
theorem cliqueStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cliqueStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : CliqueInput × List Nat =>
        Clique.cliqueStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod cliqueStructuredEncodedType setStructuredEncodedType
  have hInstance : TMPolyTimeMap X cliqueStructuredEncodedType
      (fun p : CliqueInput × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cliqueStructuredEncodedType setStructuredEncodedType
  have hCert : TMPolyTimeMap X setStructuredEncodedType
      (fun p : CliqueInput × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cliqueStructuredEncodedType setStructuredEncodedType
  have hMapped : TMPolyTimeMap X vertexCoverStructuredEncodedType
      (fun p : CliqueInput × List Nat => VertexCover.map p.1) := by
    have hComp := TMPolyTimeMap.comp VertexCover.cliqueToVertexCoverStructured_tm_polytime hInstance
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X
      (EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType)
      (fun p : CliqueInput × List Nat => (VertexCover.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp vertexCoverStructuredFiniteVerify_tm_polytime hInput
  simpa [Function.comp, Clique.cliqueStructuredFiniteVerify, X] using hComp

/-- Standard certificate-size bound for structured Set Covering. -/
theorem setCoveringCertificate_inputSize_le_poly
    (I : SetCoveringInput) (indices : List Nat)
    (hLen : indices.length ≤ I.k)
    (hWithin : ∀ j ∈ indices, j < I.system.sets.length) :
    setStructuredEncodedType.inputSize indices ≤
      2 * (setCoveringStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := setCoveringStructuredEncodedType.inputSize I
  have hCert := HittingSetStandardTM.boundedNatList_inputSize_le
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

/-- Standard certificate-size bound for structured Vertex Cover. -/
theorem vertexCoverCertificate_inputSize_le_square
    (I : VertexCoverInput) (cover : List Nat)
    (hLen : cover.length ≤ I.k)
    (hWithin : VerticesWithinBounds I.graph cover) :
    setStructuredEncodedType.inputSize cover ≤
      (vertexCoverStructuredEncodedType.inputSize I) ^ 2 := by
  let S := vertexCoverStructuredEncodedType.inputSize I
  have hCert := HittingSetStandardTM.boundedNatList_inputSize_le
    I.graph.vertices cover hWithin
  have hK : I.k ≤ S := by
    simpa [S] using SetCovering.vertexCoverStructured_inputSize_ge_budget I
  have hVertices : I.graph.vertices + 1 ≤ S := by
    change I.graph.vertices + 1 ≤ vertexCoverStructuredEncodedType.inputSize I
    rw [VertexCover.vertexCoverStructured_inputSize_eq, VertexCover.graphStructured_inputSize_eq]
    omega
  calc
    setStructuredEncodedType.inputSize cover
        ≤ cover.length * (I.graph.vertices + 1) := hCert
    _ ≤ I.k * (I.graph.vertices + 1) :=
        Nat.mul_le_mul_right (I.graph.vertices + 1) hLen
    _ ≤ S * S := Nat.mul_le_mul hK hVertices
    _ = S ^ 2 := by ring

/-- Standard certificate-size bound for structured Clique via Vertex Cover. -/
theorem cliqueViaVertexCoverCertificate_inputSize_le_poly
    (I : CliqueInput) (cover : List Nat)
    (hLen : cover.length ≤ (VertexCover.map I).k)
    (hWithin : VerticesWithinBounds (VertexCover.map I).graph cover) :
    setStructuredEncodedType.inputSize cover ≤
      1000 * (cliqueStructuredEncodedType.inputSize I) ^ 6 + 1000 := by
  let S := cliqueStructuredEncodedType.inputSize I
  have hCert := vertexCoverCertificate_inputSize_le_square
    (VertexCover.map I) cover hLen hWithin
  have hMap : vertexCoverStructuredEncodedType.inputSize (VertexCover.map I) ≤
      10 * S ^ 3 + 20 := by
    simpa [S] using Clique.vertexCoverMap_inputSize_le_clique_poly I
  calc
    setStructuredEncodedType.inputSize cover
        ≤ (vertexCoverStructuredEncodedType.inputSize (VertexCover.map I)) ^ 2 := hCert
    _ ≤ (10 * S ^ 3 + 20) ^ 2 := Nat.pow_le_pow_left hMap 2
    _ ≤ 1000 * S ^ 6 + 1000 := by
        nlinarith [sq_nonneg ((S : Int) ^ 3)]

#print axioms setCoveringStructuredFiniteVerify_tm_polytime
#print axioms vertexCoverStructuredFiniteVerify_tm_polytime
#print axioms cliqueStructuredFiniteVerify_tm_polytime
#print axioms cliqueViaVertexCoverCertificate_inputSize_le_poly

end CliqueStandardTM
end Karp21
end Problems
end ComplexityReduction
