/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixDecoderTM

/-!
Reusable checked-decoder package for finite Boolean certificate suffixes.

The long finite-Boolean suffix-pattern file proves the local CNF semantics.
This file packages that result into `TMVerifierXOnlyCheckedSuffixDecoder` for
any verifier whose certificate encoding can be presented as the finite Boolean
bit/delimiter stream used by `tmVerifierFiniteBoolSuffixPatternCNF`.
-/

namespace ComplexityReduction
namespace SAT

/--
Build a checked suffix-decoder package from the finite-Boolean suffix-pattern
CNF and an encoded suffix decoder for the verifier certificate encoding.

The two suffix-equality hypotheses are deliberately explicit: they are the
place where a concrete verifier proves that its certificate encoding is exactly
the finite Boolean bit/delimiter stream enforced by the CNF.
-/
noncomputable def tmVerifierFiniteBoolCheckedSuffixDecoder
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfBits : List Bool → V.Cert.Carrier)
    (bitsOfCert : V.Cert.Carrier → List Bool)
    (certOfBits_suffix_eq :
      ∀ bits : List Bool,
        tmVerifierCertificateInputSuffixEncoded V (certOfBits bits) =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol bits).map
            (fun s => some (Sum.inr s)))
    (cert_suffix_eq :
      ∀ c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol
              (bitsOfCert c)).map (fun s => some (Sum.inr s))) :
    TMVerifierXOnlyCheckedSuffixDecoder V where
  decoder := D
  suffixValidityCNF := tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol
  suffixValidityCNF_tm_polytime :=
    tmVerifierFiniteBoolSuffixPatternCNF_tm_polytime V bitSymbol delimiterSymbol
  validSuffixSeed_satisfies := by
    intro B x a w
    let E := w.evidence
    let c : V.Cert.Carrier := w.valid_suffix.cert
    have hMapped :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded V c := by
      change
        ((tmVerifierXOnlyGlobalTableauCNF_evidence V B x a
            w.global_tableau).decodedInitialCertificateSuffixWord).map
            (tmVerifierComputableWitness V).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded V c
      rw [w.valid_suffix.suffix_eq]
      simp [tmVerifierCertificateInputSuffixWord, c]
    have hSymbols :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol
              (bitsOfCert c)).map (fun s => some (Sum.inr s)) := by
      rw [hMapped, cert_suffix_eq c]
    simpa using
      E.finiteBoolSuffixPatternCNF_satisfies_of_mapped_suffix
        bitSymbol delimiterSymbol (bitsOfCert c) hSymbols
  decodedSuffix_decode_of_satisfies := by
    intro B x a E hSuffix
    let hDecoded :=
      E.decodedInitialCertificateSuffixWord_finiteBoolDecode_symbols
        bitSymbol delimiterSymbol hSuffix
    let bits : List Bool := Classical.choose hDecoded
    have hDecodedSpec := Classical.choose_spec hDecoded
    have hSymbols := hDecodedSpec.2
    have hEncodedSuffix :
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          tmVerifierCertificateInputSuffixEncoded V (certOfBits bits) := by
      rw [hSymbols, certOfBits_suffix_eq bits]
    have hLen :
        V.Cert.inputSize (certOfBits bits) =
          E.decodedInitialCertificateSuffixWord.length := by
      have hLen' := congrArg List.length hEncodedSuffix
      calc
        V.Cert.inputSize (certOfBits bits) =
            (tmVerifierCertificateInputSuffixEncoded V (certOfBits bits)).length := by
              rw [tmVerifierCertificateInputSuffixEncoded_length]
        _ = (E.decodedInitialCertificateSuffixWord.map
              (tmVerifierComputableWitness V).inputAlphabet).length := by
              exact hLen'.symm
        _ = E.decodedInitialCertificateSuffixWord.length := by
              simp
    have hSize :
        V.Cert.inputSize (certOfBits bits) ≤ tmVerifierCertificateSizeBound V x := by
      rw [hLen]
      exact E.decodedInitialCertificateSuffixWord_length_le_certificateSizeBound
    refine ⟨certOfBits bits, ?_⟩
    rw [hEncodedSuffix]
    exact D.decode_complete hSize

end SAT
end ComplexityReduction
