/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawNormalizationTM

/-!
Checked suffix-validity with an explicit encoded suffix decoder.

`TMVerifierXOnlyCheckedSuffixValidity` only needs to recover a
`TMVerifierCertificateWordSuffix`.  This file records the slightly stronger
shape useful for direct certificate-image recognizers: the checked suffix CNF
must make the decoded initial suffix accepted by a named encoded-suffix decoder.

This is still a checked-CNF interface.  It does not assert that accepting raw
machine runs over malformed suffixes decode; that remains the separate
`TMVerifierXOnlyRawSuffixDecodingNormalizer.accepting_decode` obligation.
-/

namespace ComplexityReduction
namespace SAT

/--
A checked x-only suffix layer that proves decoder-domain membership.

The explicit decoder is reusable by machine-specific raw-normalization proofs:
the CNF side shows which suffix image is intended, while raw accepting-run
normalization still has to prove that every accepting raw suffix lands there.
-/
structure TMVerifierXOnlyCheckedSuffixDecoder
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  decoder : TMVerifierXOnlyEncodedSuffixDecoder V
  suffixValidityCNF : L.Instance.Carrier → CNF
  suffixValidityCNF_tm_polytime :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType suffixValidityCNF
  validSuffixSeed_satisfies :
    {B : TMVerifierPushPayloadBoundary V} →
      {x : L.Instance.Carrier} →
        {a : Assignment} →
          TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a →
            CNF.Satisfies (suffixValidityCNF x) a
  decodedSuffix_decode_of_satisfies :
    {B : TMVerifierPushPayloadBoundary V} →
      {x : L.Instance.Carrier} →
        {a : Assignment} →
          (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) →
            CNF.Satisfies (suffixValidityCNF x) a →
              { c : V.Cert.Carrier //
                decoder.decode x
                  (E.decodedInitialCertificateSuffixWord.map
                    (tmVerifierComputableWitness V).inputAlphabet) = some c }

namespace TMVerifierXOnlyCheckedSuffixDecoder

/--
Forget the explicit decoder-domain proof to the existing checked suffix-validity
interface by turning a successful decode into a word-suffix witness.
-/
noncomputable def toCheckedSuffixValidity
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixDecoder V) :
    TMVerifierXOnlyCheckedSuffixValidity V where
  suffixValidityCNF := G.suffixValidityCNF
  suffixValidityCNF_tm_polytime := G.suffixValidityCNF_tm_polytime
  validSuffixSeed_satisfies := by
    intro B x a w
    exact G.validSuffixSeed_satisfies w
  decodedSuffix_valid_of_satisfies := by
    intro B x a E hSuffix
    rcases G.decodedSuffix_decode_of_satisfies E hSuffix with ⟨c, hDecode⟩
    exact G.decoder.wordSuffix_of_rawDecode hDecode

/--
Any existing checked suffix-validity package can be viewed in decoder-shaped
form once an encoded suffix decoder for its certificate encoding is supplied.
-/
noncomputable def ofCheckedSuffixValidity
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (G : TMVerifierXOnlyCheckedSuffixValidity V) :
    TMVerifierXOnlyCheckedSuffixDecoder V where
  decoder := D
  suffixValidityCNF := G.suffixValidityCNF
  suffixValidityCNF_tm_polytime := G.suffixValidityCNF_tm_polytime
  validSuffixSeed_satisfies := by
    intro B x a w
    exact G.validSuffixSeed_satisfies w
  decodedSuffix_decode_of_satisfies := by
    intro B x a E hSuffix
    let w := G.decodedSuffix_valid_of_satisfies E hSuffix
    exact ⟨w.cert, D.decode_complete_wordSuffix w⟩

end TMVerifierXOnlyCheckedSuffixDecoder

namespace TMVerifierXOnlyRawSuffixDecodingNormalizer

/--
A raw-suffix decoding normalizer also supplies a checked-decoder package with an
empty suffix CNF: the global tableau already extracts a true-output raw run, and
the normalizer proves that this raw suffix is accepted by the same decoder.
-/
noncomputable def toCheckedSuffixDecoder
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyRawSuffixDecodingNormalizer V) :
    TMVerifierXOnlyCheckedSuffixDecoder V where
  decoder := D.decoder
  suffixValidityCNF := fun _ => ([] : CNF)
  suffixValidityCNF_tm_polytime := by
    simpa using TMPolyTimeMap.const L.Instance cnfStructuredEncodedType ([] : CNF)
  validSuffixSeed_satisfies := by
    intro B x a w
    simp
  decodedSuffix_decode_of_satisfies := by
    intro B x a E _hSuffix
    have hRun :
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++
              E.decodedInitialCertificateSuffixWord))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) := by
      simpa [E.decodedCfg_initial_eq_rawInput] using E.rawOutputsTrueInTime
    exact D.accepting_decode hRun

end TMVerifierXOnlyRawSuffixDecodingNormalizer

end SAT
end ComplexityReduction
