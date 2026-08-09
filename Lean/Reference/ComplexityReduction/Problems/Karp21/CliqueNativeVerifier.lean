/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDisciplineTemplates
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactEncodedSuffixDecodersTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.CheckedDecoderDiscipline
import ComplexityReduction.Problems.Karp21.CliqueStandardTM
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Protocol.TrustPolicy

/-!
Standard-axiom native verifier for the canonical structured Clique endpoint.

The checker follows the established Clique -> Vertex Cover -> Set Covering ->
Hitting Set executable chain.  Its direct-TM proofs are reconstructed from
the standard companion leaves, while the native certificate discipline is
indexed by the exact V2 verifier and its `List Nat` witness representation.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace CliqueNativeVerifier

open Encoding Certificate Program
open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- The exact V2 witness presentation for structured subset certificates. -/
abbrev witnessPresentation : LawfulEncodedType :=
  Presentation.SetSystem.setObjectPresentation

/-- The canonical V2 primitive for the standard structured Clique checker. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def checkerPrimitive :
    Primitive
      (StandardInstances.prod GraphAtoms.cliqueStructuredPresentation witnessPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input => Clique.cliqueStructuredFiniteVerify input.1 input.2)
    (by
      simpa [GraphAtoms.cliqueStructuredPresentation, witnessPresentation] using
        CliqueStandardTM.cliqueStructuredFiniteVerify_tm_polytime)

/-- The one typed checker program used by all V2 Clique verifier evidence. -/
noncomputable def checker :
    PolyProg
      (StandardInstances.prod GraphAtoms.cliqueStructuredPresentation witnessPresentation)
      StandardInstances.bool :=
  .atom checkerPrimitive

@[simp]
theorem checker_run
    (input : (StandardInstances.prod GraphAtoms.cliqueStructuredPresentation
      witnessPresentation).Carrier) :
    checker.run input = Clique.cliqueStructuredFiniteVerify input.1 input.2 :=
  rfl

/-- The V2 checker compilation is the standard reconstructed direct-TM witness. -/
theorem checker_directTM :
    TMPolyTimeMap
      (StandardInstances.prod GraphAtoms.cliqueStructuredPresentation witnessPresentation).encodedType
      StandardInstances.bool.encodedType
      (fun input => Clique.cliqueStructuredFiniteVerify input.1 input.2) := by
  simpa only [checker_run] using checker.compileTM

/-- Exact certified verifier for the canonical structured Clique presentation. -/
@[complexity_reduction_ir_typed_verifier]
noncomputable def verifier : CertifiedVerifier GraphAtoms.cliqueStructuredProblem where
  witness := witnessPresentation
  checker := checker
  witnessBound := fun input =>
    1000 * GraphAtoms.cliqueStructuredPresentation.encodedType.inputSize input ^ 6 + 1000
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 6 1000 1000 (by
    intro input
    change 1000 * ComplexityReduction.Combinatorics.Graph.cliqueStructuredEncodedType.inputSize input ^ 6 +
        1000 ≤
      1000 * ComplexityReduction.Combinatorics.Graph.cliqueStructuredEncodedType.inputSize input ^ 6 +
        1000
    rfl)
  correct := by
    letI : DecidableEq Nat := inferInstance
    intro input
    change Clique input ↔ ∃ cover : List Nat,
      setStructuredEncodedType.inputSize cover ≤
          1000 * cliqueStructuredEncodedType.inputSize input ^ 6 + 1000 ∧
        Clique.cliqueStructuredFiniteVerify input cover = true
    constructor
    · intro hClique
      have hVertexCover : VertexCover (VertexCover.map input) :=
        (VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction.correct input).1 hClique
      rcases hVertexCover with ⟨cover, hLength, _hNodup, hWithin, hCovers⟩
      refine ⟨cover, ?_, ?_⟩
      · exact CliqueStandardTM.cliqueViaVertexCoverCertificate_inputSize_le_poly
          input cover hLength hWithin
      · exact (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff
          (VertexCover.map input) cover).2 ⟨hLength, hWithin, hCovers⟩
    · rintro ⟨cover, _, accepted⟩
      rcases (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff
          (VertexCover.map input) cover).1 accepted with
        ⟨hLength, hWithin, hCovers⟩
      have hVertexCover : VertexCover (VertexCover.map input) := by
        refine ⟨cover.dedup, ?_, List.nodup_dedup cover, ?_, ?_⟩
        · exact (List.Sublist.length_le (List.dedup_sublist cover)).trans hLength
        · intro vertex hVertex
          exact hWithin vertex (List.mem_dedup.mp hVertex)
        · intro edge hEdge
          rcases hCovers edge hEdge with hLeft | hRight
          · exact Or.inl (List.mem_dedup.mpr hLeft)
          · exact Or.inr (List.mem_dedup.mpr hRight)
      exact (VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction.correct input).2 hVertexCover
  checkerSound := by
    letI : DecidableEq Nat := inferInstance
    letI : DecidableEq StandardInstances.unaryNat.encodedType.Carrier := by
      change DecidableEq Nat
      infer_instance
    intro input cover accepted
    rcases (VertexCover.vertexCoverStructuredFiniteVerify_eq_true_iff
        (VertexCover.map input) cover).1 accepted with
      ⟨hLength, hWithin, hCovers⟩
    have hVertexCover : VertexCover (VertexCover.map input) := by
      refine ⟨cover.dedup, ?_, List.nodup_dedup cover, ?_, ?_⟩
      · exact (List.Sublist.length_le (List.dedup_sublist cover)).trans hLength
      · intro vertex hVertex
        exact hWithin vertex (List.mem_dedup.mp hVertex)
      · intro edge hEdge
        rcases hCovers edge hEdge with hLeft | hRight
        · exact Or.inl (List.mem_dedup.mpr hLeft)
        · exact Or.inr (List.mem_dedup.mpr hRight)
    exact (VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction.correct input).2 hVertexCover

/-- Exact suffix decoder for the verifier's injectively encoded nat-list witness. -/
noncomputable def encodedSuffixDecoder :
    ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder verifier.toTMVerifier :=
  ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    verifier.toTMVerifier
    setStructuredEncodedType_encode_injective

private def natListEncodingEntry (n : Nat) : List (Option Bool) :=
  (EncodedType.nat.encode n).map some ++ [none]

private theorem setStructuredEncodedType_encode_cons (n : Nat) (xs : List Nat) :
    (show List (Option Bool) from setStructuredEncodedType.encode (n :: xs)) =
      natListEncodingEntry n ++
        (show List (Option Bool) from setStructuredEncodedType.encode xs) := by
  simp [natListEncodingEntry, setStructuredEncodedType, EncodedType.list]
  exact (List.append_assoc
    (List.map some (EncodedType.nat.encode n))
    ([none] : List (Option Bool))
    (List.flatMap (fun x => List.map some (EncodedType.nat.encode x) ++ [none]) xs)).symm

private theorem natListEncodingEntry_eq_symbols (n : Nat) :
    natListEncodingEntry n =
      List.replicate n (some true) ++ [some false, none] := by
  simpa only [natListEncodingEntry, EncodedType.nat, List.map_append,
    List.map_replicate, List.map_cons, List.map_nil] using
    List.append_assoc (List.replicate n (some true)) [some false] [none]

theorem natListCertificateSymbols_eq_encode (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
      (V := verifier.toTMVerifier) (some true) (some false) none xs =
      setStructuredEncodedType.encode xs := by
  induction xs with
  | nil =>
      rfl
  | cons n xs ih =>
      rw [ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols_cons, ih]
      exact (congrArg
        (fun symbols : List (Option Bool) =>
          symbols ++ (show List (Option Bool) from setStructuredEncodedType.encode xs))
        (natListEncodingEntry_eq_symbols n).symm).trans
        (setStructuredEncodedType_encode_cons n xs).symm

theorem certificateInputSuffixEncoded_eq_natListSymbols (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded verifier.toTMVerifier xs =
      (ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
        (V := verifier.toTMVerifier) (some true) (some false) none xs).map
        (ComplexityReduction.SAT.tmVerifierInputRightSymbol (V := verifier.toTMVerifier)) := by
  simpa [ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded, verifier,
    CertifiedVerifier.toTMVerifier, witnessPresentation] using
    congrArg
      (fun symbols : List setStructuredEncodedType.Symbol =>
        symbols.map (fun symbol =>
          (some (Sum.inr symbol) :
            (ComplexityReduction.SAT.tmVerifierInputEncodedType verifier.toTMVerifier).Symbol)))
      (natListCertificateSymbols_eq_encode xs).symm

/-- Checked nat-list decoder discipline indexed by the exact V2 verifier. -/
@[complexity_reduction_ir_typed_verifier_discipline]
noncomputable def checkedDecoderDiscipline : CertifiedVerifierEncodingDiscipline verifier :=
  CheckedDecoderNativeDiscipline.ofBackend
    (ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofNatListCertificate
      verifier.toTMVerifier
      (some true) (some false) none
      (by intro h; cases h)
      (by intro h; cases h)
      (by intro h; cases h)
      encodedSuffixDecoder
      (fun xs : List Nat => xs)
      (fun xs : List Nat => xs)
      certificateInputSuffixEncoded_eq_natListSymbols
      certificateInputSuffixEncoded_eq_natListSymbols)

/-- Native capability admitted only from the exact standard verifier/discipline pair. -/
@[complexity_reduction_ir_typed_verifier]
noncomputable def nativeCapability : NativeVerifierCapability GraphAtoms.cliqueStructuredProblem :=
  CheckedDecoderNativeDiscipline.toNativeVerifierCapability checkedDecoderDiscipline

@[complexity_reduction_ir_typed_verifier]
theorem backendTMInNP_export :
    ComplexityReduction.TMInNP GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem :=
  verifier.toBackendTMInNP

@[complexity_reduction_ir_typed_native_membership]
theorem nativeTMInNP : NativeTMInNP GraphAtoms.cliqueStructuredProblem :=
  NativeTMInNP.ofCapability nativeCapability

noncomputable def nativeVerifierOutcome :
    Protocol.TrustedNativeVerifierOutcome GraphAtoms.cliqueStructuredProblem :=
  Protocol.acceptNativeVerifier nativeCapability

#print axioms checker_directTM
#print axioms verifier
#print axioms checkedDecoderDiscipline
#print axioms nativeCapability

end CliqueNativeVerifier
end Karp21
end Problems
end ComplexityReduction
