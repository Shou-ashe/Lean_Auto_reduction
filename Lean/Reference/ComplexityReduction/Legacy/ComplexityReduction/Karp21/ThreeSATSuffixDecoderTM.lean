/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMStandard
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawNormalizationTM

/-!
Certificate-suffix decoders for the finite Boolean certificates used by the
structured and bundled 3SAT finite TM verifiers.

These decoders only identify well-formed encoded certificate suffixes.  They do
not assert that an accepting raw machine run must be in the decoder domain.
-/

namespace ComplexityReduction
namespace SAT

/-- Decoder for `List Bool` certificates in the project list encoding. -/
def finiteAssignmentCertDecode :
    List finiteAssignmentCertEncodedType.Symbol → Option finiteAssignmentCertEncodedType.Carrier
  | [] => some []
  | some b :: none :: rest =>
      match finiteAssignmentCertDecode rest with
      | none => none
      | some bits => some (b :: bits)
  | _ => none

theorem finiteAssignmentCertDecode_complete (bits : List Bool) :
    finiteAssignmentCertDecode (finiteAssignmentCertEncodedType.encode bits) = some bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change finiteAssignmentCertDecode
          (some b :: none :: finiteAssignmentCertEncodedType.encode bits) =
        some (b :: bits)
      simp [finiteAssignmentCertDecode, ih]
      rfl

theorem finiteAssignmentCertDecode_sound :
    ∀ {symbols : List finiteAssignmentCertEncodedType.Symbol} {bits : List Bool},
      finiteAssignmentCertDecode symbols = some bits →
        symbols = finiteAssignmentCertEncodedType.encode bits
  | [], bits, h => by
      cases bits with
      | nil =>
          rfl
      | cons _ _ =>
          cases h
  | none :: rest, bits, h => by
      cases h
  | some b :: [], bits, h => by
      cases h
  | some b :: some b' :: rest, bits, h => by
      cases h
  | some b :: none :: rest, bits, h => by
      cases hRest : finiteAssignmentCertDecode rest with
      | none =>
          simp [finiteAssignmentCertDecode, hRest] at h
      | some bits' =>
          have hbits : b :: bits' = bits := by
            have hSome : some (b :: bits') = some bits := by
              simpa [finiteAssignmentCertDecode, hRest] using h
            exact Option.some.inj hSome
          subst bits
          have hRestEq := finiteAssignmentCertDecode_sound hRest
          rw [hRestEq]
          rfl

theorem threeSATStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    tmVerifierFiniteBoolCertificateSymbols (V := threeSATStructuredFiniteTMVerifier)
        (fun b : Bool => some b) none bits =
      finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            tmVerifierFiniteBoolCertificateSymbols (V := threeSATStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem threeSATFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    tmVerifierFiniteBoolCertificateSymbols (V := threeSATFiniteTMVerifier)
        (fun b : Bool => some b) none bits =
      finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            tmVerifierFiniteBoolCertificateSymbols (V := threeSATFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: finiteAssignmentCertEncodedType.encode bits
      rw [ih]

/--
Encoded certificate-suffix decoder for the faithful structured 3SAT verifier.
The accepting-run normalizer remains a separate, machine-specific obligation.
-/
noncomputable def threeSATStructuredFiniteEncodedSuffixDecoder :
    TMVerifierXOnlyEncodedSuffixDecoder threeSATStructuredFiniteTMVerifier :=
  TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    threeSATStructuredFiniteTMVerifier
    finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact finiteAssignmentCertDecode_sound h)
    finiteAssignmentCertDecode_complete

/-! ### Direct checked finite-Boolean suffix CNFs -/

/-- Checked suffix-pattern CNF for the faithful structured finite 3SAT verifier. -/
noncomputable def threeSATStructuredFiniteSuffixPatternCNF
    (φ : Karp21.threeSATStructuredDecisionProblem.Instance.Carrier) : CNF :=
  tmVerifierFiniteBoolSuffixPatternCNF threeSATStructuredFiniteTMVerifier
    (fun b : Bool => some b) none φ

theorem threeSATStructuredFiniteSuffixPatternCNF_tm_polytime :
    TMPolyTimeMap Karp21.threeSATStructuredDecisionProblem.Instance
      cnfStructuredEncodedType
      threeSATStructuredFiniteSuffixPatternCNF := by
  simpa [threeSATStructuredFiniteSuffixPatternCNF] using
    tmVerifierFiniteBoolSuffixPatternCNF_tm_polytime threeSATStructuredFiniteTMVerifier
      (fun b : Bool => some b) none

noncomputable def threeSATStructuredFiniteEncodedSuffixDecoder_decode_of_satisfies
    {B : TMVerifierPushPayloadBoundary threeSATStructuredFiniteTMVerifier}
    {φ : Karp21.threeSATStructuredDecisionProblem.Instance.Carrier}
    {a : Assignment}
    (E : TMVerifierXOnlyGlobalTableauEvidence threeSATStructuredFiniteTMVerifier B φ a)
    (hSuffix :
      CNF.Satisfies (threeSATStructuredFiniteSuffixPatternCNF φ) a) :
    { bits : List Bool //
      threeSATStructuredFiniteEncodedSuffixDecoder.decode φ
        (E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet) =
          some bits } := by
  classical
  let hDecoded :=
    E.decodedInitialCertificateSuffixWord_finiteBoolDecode_symbols
      (fun b : Bool => some b) none (by simpa [threeSATStructuredFiniteSuffixPatternCNF]
        using hSuffix)
  let bits : List Bool := Classical.choose hDecoded
  have hDecodedSpec := Classical.choose_spec hDecoded
  have hSymbols := hDecodedSpec.2
  have hSymbolsEncode :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet =
        (finiteAssignmentCertEncodedType.encode bits).map fun s => some (Sum.inr s) := by
    simpa [threeSATStructuredFiniteBoolCertificateSymbols_eq_encode bits] using hSymbols
  have hEncodedSuffix :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet =
        tmVerifierCertificateInputSuffixEncoded threeSATStructuredFiniteTMVerifier bits := by
    simpa [tmVerifierCertificateInputSuffixEncoded] using hSymbolsEncode
  have hLen :
      finiteAssignmentCertEncodedType.inputSize bits =
        E.decodedInitialCertificateSuffixWord.length := by
    have hLen' := congrArg List.length hEncodedSuffix
    calc
      finiteAssignmentCertEncodedType.inputSize bits =
          (tmVerifierCertificateInputSuffixEncoded threeSATStructuredFiniteTMVerifier bits).length := by
            simp [threeSATStructuredFiniteTMVerifier]
      _ = (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet).length :=
            hLen'.symm
      _ = E.decodedInitialCertificateSuffixWord.length := by simp
  have hSize :
      finiteAssignmentCertEncodedType.inputSize bits ≤
        tmVerifierCertificateSizeBound threeSATStructuredFiniteTMVerifier φ := by
    rw [hLen]
    exact E.decodedInitialCertificateSuffixWord_length_le_certificateSizeBound
  have hSizeV :
      threeSATStructuredFiniteTMVerifier.Cert.inputSize bits ≤
        tmVerifierCertificateSizeBound threeSATStructuredFiniteTMVerifier φ := by
    simpa [threeSATStructuredFiniteTMVerifier] using hSize
  refine ⟨bits, ?_⟩
  rw [hEncodedSuffix]
  exact threeSATStructuredFiniteEncodedSuffixDecoder.decode_complete hSizeV

/--
Encoded certificate-suffix decoder for the historical bundled 3SAT verifier.
This is still only the decoder half of the raw-suffix normalization package.
-/
noncomputable def threeSATFiniteEncodedSuffixDecoder :
    TMVerifierXOnlyEncodedSuffixDecoder threeSATFiniteTMVerifier :=
  TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    threeSATFiniteTMVerifier
    finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact finiteAssignmentCertDecode_sound h)
    finiteAssignmentCertDecode_complete

/-- Checked suffix-pattern CNF for the historical bundled finite 3SAT verifier. -/
noncomputable def threeSATFiniteSuffixPatternCNF
    (φ : threeSATDecisionProblem.Instance.Carrier) : CNF :=
  tmVerifierFiniteBoolSuffixPatternCNF threeSATFiniteTMVerifier
    (fun b : Bool => some b) none φ

theorem threeSATFiniteSuffixPatternCNF_tm_polytime :
    TMPolyTimeMap threeSATDecisionProblem.Instance
      cnfStructuredEncodedType
      threeSATFiniteSuffixPatternCNF := by
  simpa [threeSATFiniteSuffixPatternCNF] using
    tmVerifierFiniteBoolSuffixPatternCNF_tm_polytime threeSATFiniteTMVerifier
      (fun b : Bool => some b) none

noncomputable def threeSATFiniteEncodedSuffixDecoder_decode_of_satisfies
    {B : TMVerifierPushPayloadBoundary threeSATFiniteTMVerifier}
    {φ : threeSATDecisionProblem.Instance.Carrier}
    {a : Assignment}
    (E : TMVerifierXOnlyGlobalTableauEvidence threeSATFiniteTMVerifier B φ a)
    (hSuffix :
      CNF.Satisfies (threeSATFiniteSuffixPatternCNF φ) a) :
    { bits : List Bool //
      threeSATFiniteEncodedSuffixDecoder.decode φ
        (E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet) =
          some bits } := by
  classical
  let hDecoded :=
    E.decodedInitialCertificateSuffixWord_finiteBoolDecode_symbols
      (fun b : Bool => some b) none (by simpa [threeSATFiniteSuffixPatternCNF]
        using hSuffix)
  let bits : List Bool := Classical.choose hDecoded
  have hDecodedSpec := Classical.choose_spec hDecoded
  have hSymbols := hDecodedSpec.2
  have hSymbolsEncode :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet =
        (finiteAssignmentCertEncodedType.encode bits).map fun s => some (Sum.inr s) := by
    simpa [threeSATFiniteBoolCertificateSymbols_eq_encode bits] using hSymbols
  have hEncodedSuffix :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet =
        tmVerifierCertificateInputSuffixEncoded threeSATFiniteTMVerifier bits := by
    simpa [tmVerifierCertificateInputSuffixEncoded] using hSymbolsEncode
  have hLen :
      finiteAssignmentCertEncodedType.inputSize bits =
        E.decodedInitialCertificateSuffixWord.length := by
    have hLen' := congrArg List.length hEncodedSuffix
    calc
      finiteAssignmentCertEncodedType.inputSize bits =
          (tmVerifierCertificateInputSuffixEncoded threeSATFiniteTMVerifier bits).length := by
            simp [threeSATFiniteTMVerifier, threeSATFiniteTMVerifier_of_clauses_projection]
      _ = (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet).length :=
            hLen'.symm
      _ = E.decodedInitialCertificateSuffixWord.length := by simp
  have hSize :
      finiteAssignmentCertEncodedType.inputSize bits ≤
        tmVerifierCertificateSizeBound threeSATFiniteTMVerifier φ := by
    rw [hLen]
    exact E.decodedInitialCertificateSuffixWord_length_le_certificateSizeBound
  have hSizeV :
      threeSATFiniteTMVerifier.Cert.inputSize bits ≤
        tmVerifierCertificateSizeBound threeSATFiniteTMVerifier φ := by
    simpa [threeSATFiniteTMVerifier, threeSATFiniteTMVerifier_of_clauses_projection] using hSize
  refine ⟨bits, ?_⟩
  rw [hEncodedSuffix]
  exact threeSATFiniteEncodedSuffixDecoder.decode_complete hSizeV

/-! ### Checked decoder packages -/

/--
Checked finite-Boolean suffix decoder package for the faithful structured 3SAT
verifier.  The CNF completeness side is proved directly from the valid typed
certificate suffix.
-/
noncomputable def threeSATStructuredFiniteCheckedSuffixDecoder :
    TMVerifierXOnlyCheckedSuffixDecoder threeSATStructuredFiniteTMVerifier where
  decoder := threeSATStructuredFiniteEncodedSuffixDecoder
  suffixValidityCNF := threeSATStructuredFiniteSuffixPatternCNF
  suffixValidityCNF_tm_polytime := threeSATStructuredFiniteSuffixPatternCNF_tm_polytime
  validSuffixSeed_satisfies := by
    intro B φ a w
    let E := w.evidence
    let bits : List Bool := w.valid_suffix.cert
    have hEncoded :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded threeSATStructuredFiniteTMVerifier bits := by
      change
        ((tmVerifierXOnlyGlobalTableauCNF_evidence threeSATStructuredFiniteTMVerifier B φ a
            w.global_tableau).decodedInitialCertificateSuffixWord).map
            (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded threeSATStructuredFiniteTMVerifier bits
      rw [w.valid_suffix.suffix_eq]
      simp [tmVerifierCertificateInputSuffixWord, tmVerifierCertificateInputSuffixEncoded, bits]
    have hSymbols :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATStructuredFiniteTMVerifier).inputAlphabet =
          (tmVerifierFiniteBoolCertificateSymbols (V := threeSATStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits).map fun s => some (Sum.inr s) := by
      simpa [tmVerifierCertificateInputSuffixEncoded,
        threeSATStructuredFiniteBoolCertificateSymbols_eq_encode bits] using hEncoded
    simpa [threeSATStructuredFiniteSuffixPatternCNF] using
      E.finiteBoolSuffixPatternCNF_satisfies_of_mapped_suffix
        (fun b : Bool => some b) none bits hSymbols
  decodedSuffix_decode_of_satisfies := by
    intro B φ a E hSuffix
    exact threeSATStructuredFiniteEncodedSuffixDecoder_decode_of_satisfies E hSuffix

/--
Checked finite-Boolean suffix decoder package for the historical bundled 3SAT
verifier.
-/
noncomputable def threeSATFiniteCheckedSuffixDecoder :
    TMVerifierXOnlyCheckedSuffixDecoder threeSATFiniteTMVerifier where
  decoder := threeSATFiniteEncodedSuffixDecoder
  suffixValidityCNF := threeSATFiniteSuffixPatternCNF
  suffixValidityCNF_tm_polytime := threeSATFiniteSuffixPatternCNF_tm_polytime
  validSuffixSeed_satisfies := by
    intro B φ a w
    let E := w.evidence
    let bits : List Bool := w.valid_suffix.cert
    have hEncoded :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded threeSATFiniteTMVerifier bits := by
      change
        ((tmVerifierXOnlyGlobalTableauCNF_evidence threeSATFiniteTMVerifier B φ a
            w.global_tableau).decodedInitialCertificateSuffixWord).map
            (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded threeSATFiniteTMVerifier bits
      rw [w.valid_suffix.suffix_eq]
      simp [tmVerifierCertificateInputSuffixWord, tmVerifierCertificateInputSuffixEncoded, bits]
    have hSymbols :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness threeSATFiniteTMVerifier).inputAlphabet =
          (tmVerifierFiniteBoolCertificateSymbols (V := threeSATFiniteTMVerifier)
              (fun b : Bool => some b) none bits).map fun s => some (Sum.inr s) := by
      simpa [tmVerifierCertificateInputSuffixEncoded,
        threeSATFiniteBoolCertificateSymbols_eq_encode bits] using hEncoded
    simpa [threeSATFiniteSuffixPatternCNF] using
      E.finiteBoolSuffixPatternCNF_satisfies_of_mapped_suffix
        (fun b : Bool => some b) none bits hSymbols
  decodedSuffix_decode_of_satisfies := by
    intro B φ a E hSuffix
    exact threeSATFiniteEncodedSuffixDecoder_decode_of_satisfies E hSuffix

end SAT
end ComplexityReduction
