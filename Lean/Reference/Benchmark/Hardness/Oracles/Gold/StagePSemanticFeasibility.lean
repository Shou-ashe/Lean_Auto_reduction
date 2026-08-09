import Benchmark.Hardness.Inputs.StageP.Inputs
import ComplexityReduction.AxiomGate
import ComplexityReduction.Certificate.CheckedDecoderDiscipline
import ComplexityReduction.Domain.GraphColoringToChromaticNumberAdapter
import ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactEncodedSuffixDecodersTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Problems.Karp21.ExactCoverStandardTM
import ComplexityReduction.Routes.ChromaticNumberToExactCover.Unified
import ComplexityReduction.Routes.ThreeSATToClique.Unified

/-!
Hidden semantic-feasibility witnesses for Stage P.

This module is compiled by the benchmark qualification gate but is never an
allowed import, helper source, prompt input, candidate dependency, or runtime
registry module.  Its only purpose is to prevent the public benchmark from
freezing mathematically impossible positive cases.
-/

namespace Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program

namespace ExactCover

abbrev problem : PresentedProblem :=
  Benchmark.Hardness.Inputs.StageP.Inputs.fullBundleSetCompletenessSource

abbrev witnessPresentation : LawfulEncodedType :=
  ComplexityReduction.Presentation.SetSystem.setObjectPresentation

noncomputable def checkerPrimitive :
    Primitive
      (StandardInstances.prod problem.representation witnessPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input =>
      ComplexityReduction.Karp21.ExactCover.exactCoverStructuredFiniteVerify
        input.1 input.2)
    (by
      simpa [problem, Benchmark.Hardness.Inputs.StageP.Inputs.fullBundleSetCompletenessSource,
        witnessPresentation] using
        ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverStructuredFiniteVerify_tm_polytime)

noncomputable def checker :
    PolyProg
      (StandardInstances.prod problem.representation witnessPresentation)
      StandardInstances.bool :=
  .atom checkerPrimitive

@[simp]
theorem checker_run (input : problem.Instance × witnessPresentation.Carrier) :
    checker.run input =
      ComplexityReduction.Karp21.ExactCover.exactCoverStructuredFiniteVerify
        input.1 input.2 :=
  rfl

noncomputable def verifier : CertifiedVerifier problem where
  witness := witnessPresentation
  checker := checker
  witnessBound := fun input =>
    2 * problem.representation.encodedType.inputSize input ^ 2 + 2
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 2 2 2 (by
    intro input
    rfl)
  correct := by
    intro input
    change ComplexityReduction.Combinatorics.ExactCover input ↔
      ∃ candidate : List Nat,
        ComplexityReduction.Combinatorics.setStructuredEncodedType.inputSize candidate ≤
            2 * ComplexityReduction.Combinatorics.exactCoverStructuredEncodedType.inputSize
              input ^ 2 + 2 ∧
          ComplexityReduction.Karp21.ExactCover.exactCoverStructuredFiniteVerify
            input candidate = true
    constructor
    · intro accepted
      rcases accepted with
        ⟨wellFormed, selected, family, nodup, disjoint, covers⟩
      let candidate := selected.map input.system.sets.idxOf
      have bounds : ∀ j ∈ candidate, j < input.system.sets.length := by
        intro j hj
        rcases List.mem_map.mp hj with ⟨set, setMem, rfl⟩
        exact List.idxOf_lt_length_iff.mpr (family set setMem)
      have lengthBound : candidate.length ≤ input.system.sets.length := by
        have selectedLength : selected.length ≤ input.system.sets.length :=
          ComplexityReduction.Karp21.FiniteWitness.nodup_length_le_of_mem
            nodup family
        simpa [candidate] using selectedLength
      refine ⟨candidate, ?_, ?_⟩
      · exact
          ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverIndexCertificate_inputSize_le_poly
            input candidate lengthBound bounds
      · exact ComplexityReduction.Karp21.ExactCover.exactCoverVerifier_complete
          wellFormed family nodup disjoint covers
    · rintro ⟨candidate, _, checkerAccepts⟩
      exact ComplexityReduction.Karp21.ExactCover.exactCoverVerifier_sound checkerAccepts
  checkerSound := by
    intro input candidate checkerAccepts
    exact ComplexityReduction.Karp21.ExactCover.exactCoverVerifier_sound checkerAccepts

@[simp]
theorem verifier_toTMVerifier_eq_legacy :
    verifier.toTMVerifier =
      ComplexityReduction.Karp21.exactCoverStructuredFiniteTMVerifier :=
  rfl

noncomputable def encodedSuffixDecoder :
    ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder verifier.toTMVerifier :=
  ComplexityReduction.SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofInjectiveCertificateEncoding
    verifier.toTMVerifier
    ComplexityReduction.Combinatorics.setStructuredEncodedType_encode_injective

private def natListEncodingEntry (n : Nat) : List (Option Bool) :=
  (ComplexityReduction.EncodedType.nat.encode n).map some ++ [none]

private theorem setStructuredEncodedType_encode_cons (n : Nat) (xs : List Nat) :
    (show List (Option Bool) from
      ComplexityReduction.Combinatorics.setStructuredEncodedType.encode (n :: xs)) =
      natListEncodingEntry n ++
        (show List (Option Bool) from
          ComplexityReduction.Combinatorics.setStructuredEncodedType.encode xs) := by
  simp [natListEncodingEntry, ComplexityReduction.Combinatorics.setStructuredEncodedType,
    ComplexityReduction.EncodedType.list]
  exact (List.append_assoc
    (List.map some (ComplexityReduction.EncodedType.nat.encode n))
    ([none] : List (Option Bool))
    (List.flatMap
      (fun x => List.map some (ComplexityReduction.EncodedType.nat.encode x) ++ [none]) xs)).symm

private theorem natListEncodingEntry_eq_symbols (n : Nat) :
    natListEncodingEntry n =
      List.replicate n (some true) ++ [some false, none] := by
  simpa only [natListEncodingEntry, ComplexityReduction.EncodedType.nat,
    List.map_append, List.map_replicate, List.map_cons, List.map_nil] using
    List.append_assoc (List.replicate n (some true)) [some false] [none]

theorem natListCertificateSymbols_eq_encode (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
        (V := verifier.toTMVerifier) (some true) (some false) none xs =
      ComplexityReduction.Combinatorics.setStructuredEncodedType.encode xs := by
  induction xs with
  | nil =>
      rfl
  | cons n xs ih =>
      rw [ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols_cons, ih]
      exact (congrArg
        (fun symbols : List (Option Bool) =>
          symbols ++
            (show List (Option Bool) from
              ComplexityReduction.Combinatorics.setStructuredEncodedType.encode xs))
        (natListEncodingEntry_eq_symbols n).symm).trans
        (setStructuredEncodedType_encode_cons n xs).symm

theorem certificateInputSuffixEncoded_eq_natListSymbols (xs : List Nat) :
    ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded verifier.toTMVerifier xs =
      (ComplexityReduction.SAT.tmVerifierNatListCertificateSymbols
        (V := verifier.toTMVerifier) (some true) (some false) none xs).map
        (ComplexityReduction.SAT.tmVerifierInputRightSymbol (V := verifier.toTMVerifier)) := by
  simpa [ComplexityReduction.SAT.tmVerifierCertificateInputSuffixEncoded, verifier,
    CertifiedVerifier.toTMVerifier, witnessPresentation, problem,
    Benchmark.Hardness.Inputs.StageP.Inputs.fullBundleSetCompletenessSource] using
    congrArg
      (fun symbols : List (Option Bool) =>
        symbols.map (fun symbol =>
          (some (Sum.inr symbol) :
            (ComplexityReduction.SAT.tmVerifierInputEncodedType
              verifier.toTMVerifier).Symbol)))
      (natListCertificateSymbols_eq_encode xs).symm

noncomputable def discipline : CertifiedVerifierEncodingDiscipline verifier :=
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

noncomputable def capability : NativeVerifierCapability problem :=
  CheckedDecoderNativeDiscipline.toNativeVerifierCapability discipline

theorem membership : NativeTMInNP problem :=
  NativeTMInNP.ofCapability capability

noncomputable def canonicalThreeSATToExactCover :
    CertifiedReduction
      ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT
      problem :=
  CertifiedReduction.comp
    ComplexityReduction.Routes.ChromaticNumberToExactCover.finalRoute
    (CertifiedReduction.comp
      ComplexityReduction.Domain.GraphColoringToChromaticNumberAdapter.targetAdapter
      ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM.sharedGadget)

noncomputable def completeness : NativeTMNPComplete problem where
  membership := membership
  hardness := fun _source sourceMembership =>
    ⟨CertifiedReduction.comp canonicalThreeSATToExactCover
      (ComplexityReduction.Certificate.NativeCookLevin.reduce sourceMembership)⟩

end ExactCover

namespace ProducerConsumer

open Benchmark.Hardness.Inputs.StageP

noncomputable def producerReduction :
    CertifiedReduction Inputs.capabilityProducerSource Inputs.capabilityProducerTarget := by
  rw [show Inputs.capabilityProducerTarget = Inputs.capabilityProducerSource from
    ProducerSupport.target_eq_source]
  exact CertifiedReduction.refl Inputs.capabilityProducerSource

noncomputable def producerSourceCompleteness :
    NativeTMNPComplete Inputs.capabilityProducerSource where
  membership :=
    ComplexityReduction.Problems.Karp21.CliqueNativeVerifier.nativeTMInNP
  hardness := fun _source sourceMembership =>
    ⟨CertifiedReduction.comp
      ComplexityReduction.Routes.ThreeSATToClique.finalRoute
      (ComplexityReduction.Certificate.NativeCookLevin.reduce sourceMembership)⟩

noncomputable def consumerCompleteness :
    NativeTMNPComplete Inputs.capabilityConsumerSource where
  membership := ProducerSupport.targetNativeTMInNP
  hardness := by
    intro source sourceMembership
    rcases producerSourceCompleteness.hardness source sourceMembership with
      ⟨toProducerSource⟩
    exact ⟨CertifiedReduction.comp producerReduction toProducerSource⟩

end ProducerConsumer

end Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility

assert_standard_axioms
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ExactCover.verifier,
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ExactCover.discipline,
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ExactCover.membership,
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ExactCover.completeness,
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ProducerConsumer.producerReduction,
  Benchmark.Hardness.Oracles.Gold.StagePSemanticFeasibility.ProducerConsumer.consumerCompleteness
