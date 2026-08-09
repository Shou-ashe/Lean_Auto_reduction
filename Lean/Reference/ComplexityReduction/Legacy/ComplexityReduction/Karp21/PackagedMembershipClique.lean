/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipVertexCover
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Clique.

The finite verifier is obtained by composing the already verified direct
Clique-to-Vertex-Cover TM map with the direct Vertex Cover finite verifier.
This keeps the target membership proof inside direct TM-backed reductions and
does not use a costed-to-TM soundness boundary.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace Clique

/--
Finite-certificate verifier for faithful structured Clique, routed through the
verified direct-TM Clique-to-Vertex-Cover map.
-/
noncomputable def cliqueStructuredFiniteVerify (I : CliqueInput) (cover : List Nat) : Bool :=
  VertexCover.vertexCoverStructuredFiniteVerify (VertexCover.map I) cover

theorem cliqueStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cliqueStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : CliqueInput × List Nat =>
        cliqueStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod cliqueStructuredEncodedType setStructuredEncodedType
  have hInstance :
      TMPolyTimeMap X cliqueStructuredEncodedType
        (fun p : CliqueInput × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cliqueStructuredEncodedType setStructuredEncodedType
  have hCert :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : CliqueInput × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cliqueStructuredEncodedType setStructuredEncodedType
  have hMapped :
      TMPolyTimeMap X vertexCoverStructuredEncodedType
        (fun p : CliqueInput × List Nat => VertexCover.map p.1) := by
    have hComp := TMPolyTimeMap.comp VertexCover.cliqueToVertexCoverStructured_tm_polytime
      hInstance
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod vertexCoverStructuredEncodedType setStructuredEncodedType)
        (fun p : CliqueInput × List Nat => (VertexCover.map p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hMapped hCert
  have hComp := TMPolyTimeMap.comp VertexCover.vertexCoverStructuredFiniteVerify_tm_polytime
    hInput
  simpa [Function.comp, cliqueStructuredFiniteVerify, X] using hComp

theorem vertexCoverMap_inputSize_le_clique_poly (I : CliqueInput) :
    vertexCoverStructuredEncodedType.inputSize (VertexCover.map I) ≤
      10 * (cliqueStructuredEncodedType.inputSize I) ^ 3 + 20 := by
  let S := cliqueStructuredEncodedType.inputSize I
  have hVertex := VertexCover.vertexCoverStructured_inputSize_map_le_vertices_poly I
  have hInput : I.graph.vertices + 1 ≤ S := by
    simpa [S] using VertexCover.cliqueStructured_inputSize_ge_vertices_succ I
  have hPow : (I.graph.vertices + 1) ^ 3 ≤ S ^ 3 :=
    Nat.pow_le_pow_left hInput 3
  calc
    vertexCoverStructuredEncodedType.inputSize (VertexCover.map I)
        ≤ 10 * (I.graph.vertices + 1) ^ 3 + 20 := hVertex
    _ ≤ 10 * S ^ 3 + 20 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 hPow) 20

theorem cliqueViaVertexCoverCertificate_inputSize_le_poly
    (I : CliqueInput) (cover : List Nat)
    (hLen : cover.length ≤ (VertexCover.map I).k)
    (hWithin : VerticesWithinBounds (VertexCover.map I).graph cover) :
    setStructuredEncodedType.inputSize cover ≤
      1000 * (cliqueStructuredEncodedType.inputSize I) ^ 6 + 1000 := by
  let S := cliqueStructuredEncodedType.inputSize I
  have hCert :=
    VertexCover.vertexCoverCertificate_inputSize_le_square
      (VertexCover.map I) cover hLen hWithin
  have hMap : vertexCoverStructuredEncodedType.inputSize (VertexCover.map I) ≤
      10 * S ^ 3 + 20 := by
    simpa [S] using vertexCoverMap_inputSize_le_clique_poly I
  calc
    setStructuredEncodedType.inputSize cover
        ≤ (vertexCoverStructuredEncodedType.inputSize (VertexCover.map I)) ^ 2 := hCert
    _ ≤ (10 * S ^ 3 + 20) ^ 2 := Nat.pow_le_pow_left hMap 2
    _ ≤ 1000 * S ^ 6 + 1000 := by
        nlinarith [sq_nonneg ((S : Int) ^ 3)]

end Clique

/-- Direct finite-certificate TM verifier for faithful structured Clique. -/
noncomputable def cliqueStructuredFiniteTMVerifier :
    TMVerifier cliqueStructuredDecisionProblem where
  Cert := setStructuredEncodedType
  verify := Clique.cliqueStructuredFiniteVerify
  verifier_polytime := Clique.cliqueStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨6, 1000, 1000, ?_⟩
    intro I hYes
    have hVC :
        vertexCoverStructuredDecisionProblem.isYes (VertexCover.map I) :=
      (VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction.correct I).1 hYes
    rcases hVC with ⟨cover, hLen, _hNodup, hWithin, hCovers⟩
    refine ⟨cover, ?_, ?_⟩
    · exact Clique.cliqueViaVertexCoverCertificate_inputSize_le_poly
        I cover hLen hWithin
    · exact (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff
        (VertexCover.map I) cover).2 ⟨hLen, hWithin, hCovers⟩
  sound := by
    intro I cover hVerify
    have hVC :
        vertexCoverStructuredDecisionProblem.isYes (VertexCover.map I) :=
      vertexCoverStructuredFiniteTMVerifier.sound (VertexCover.map I) cover hVerify
    exact (VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction.correct I).2 hVC

theorem cliqueStructured_TMInNP :
    TMInNP cliqueStructuredDecisionProblem :=
  TMInNP.intro cliqueStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
