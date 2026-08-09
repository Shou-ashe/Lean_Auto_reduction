/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawSoundTM

/-!
Raw-input normalization route for the x-only Cook-Levin surface.

`TMVerifierXOnlyRawInputSound` is the minimal soundness condition needed by the
raw route.  This file records the stronger, proof-relevant normalization shape:
every true-output raw run from the fixed instance prefix must decode to a
bounded typed accepting certificate.
-/

namespace ComplexityReduction
namespace SAT

/--
Raw accepting-run normalization for one direct verifier machine.

The field is intentionally stronger than raw soundness: it recovers a bounded
typed accepting certificate, not merely `L.isYes x`.
-/
structure TMVerifierXOnlyRawInputNormalizer
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  normalize :
    {x : L.Instance.Carrier} →
      {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)} →
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++ suffix))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) →
          TMVerifierBoundedAcceptingCertificate V x

/--
Certificate-suffix normalization for one direct verifier machine.

This is the narrower remaining obligation behind raw-input normalization: it
only has to recognize that an accepting raw suffix is the bounded input-stack
image of some typed certificate.  The existing verifier-machine bridge then
turns that suffix witness into a bounded accepting certificate.
-/
structure TMVerifierXOnlyRawSuffixNormalizer
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  normalize_suffix :
    {x : L.Instance.Carrier} →
      {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)} →
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++ suffix))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) →
          TMVerifierCertificateWordSuffix V x suffix

/--
An explicit decoder for bounded certificate suffix encodings.

This is intentionally only an encoding-level API: it says how to recognize the
typed certificate-suffix image, but it does not by itself claim anything about
how the verifier machine behaves on malformed raw suffix words.
-/
structure TMVerifierXOnlyEncodedSuffixDecoder
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  decode :
    L.Instance.Carrier →
      List (tmVerifierInputEncodedType V).Symbol → Option V.Cert.Carrier
  decode_sound :
    {x : L.Instance.Carrier} →
      {suffix : List (tmVerifierInputEncodedType V).Symbol} →
        {c : V.Cert.Carrier} →
          decode x suffix = some c →
            V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
              suffix = tmVerifierCertificateInputSuffixEncoded V c
  decode_complete :
    {x : L.Instance.Carrier} →
      {c : V.Cert.Carrier} →
        V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x →
          decode x (tmVerifierCertificateInputSuffixEncoded V c) = some c

/--
A raw-suffix decoding normalizer separates two obligations:
an explicit decoder for the certificate-suffix image, and a machine-specific
proof that every accepting raw suffix lands in that decoder's domain.
-/
structure TMVerifierXOnlyRawSuffixDecodingNormalizer
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  decoder : TMVerifierXOnlyEncodedSuffixDecoder V
  accepting_decode :
    {x : L.Instance.Carrier} →
      {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)} →
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++ suffix))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) →
          { c : V.Cert.Carrier //
            decoder.decode x
              (suffix.map (tmVerifierComputableWitness V).inputAlphabet) = some c }

end SAT

namespace EncodedType

/-- Decode a suffix that is entirely in the right component of a product encoding. -/
def prodRightSuffixDecode {X Y : EncodedType} :
    List (EncodedType.prod X Y).Symbol → Option (List Y.Symbol)
  | [] => some []
  | some (Sum.inr y) :: rest => (prodRightSuffixDecode rest).map fun ys => y :: ys
  | _ => none

theorem prodRightSuffixDecode_complete {X Y : EncodedType}
    (ys : List Y.Symbol) :
    prodRightSuffixDecode (X := X) (Y := Y)
      (ys.map fun y => some (Sum.inr y)) = some ys := by
  induction ys with
  | nil =>
      rfl
  | cons y ys ih =>
      simp [prodRightSuffixDecode, ih]

theorem prodRightSuffixDecode_sound {X Y : EncodedType} :
    ∀ {suffix : List (EncodedType.prod X Y).Symbol} {ys : List Y.Symbol},
      prodRightSuffixDecode (X := X) (Y := Y) suffix = some ys →
        suffix = ys.map fun y => some (Sum.inr y)
  | [], ys, h => by
      cases ys with
      | nil =>
          rfl
      | cons _ _ =>
          simp [prodRightSuffixDecode] at h
  | none :: rest, ys, h => by
      simp [prodRightSuffixDecode] at h
  | some (Sum.inl _) :: rest, ys, h => by
      simp [prodRightSuffixDecode] at h
  | some (Sum.inr y) :: rest, ys, h => by
      cases hRest : prodRightSuffixDecode (X := X) (Y := Y) rest with
      | none =>
          simp [prodRightSuffixDecode, hRest] at h
      | some ys' =>
          have hys : ys = y :: ys' := by
            simpa [prodRightSuffixDecode, hRest] using h.symm
          subst ys
          have hRestEq := prodRightSuffixDecode_sound (X := X) (Y := Y) hRest
          rw [hRestEq]
          rfl

end EncodedType

namespace SAT

namespace TMVerifierXOnlyEncodedSuffixDecoder

/--
Build an encoded suffix decoder from a decoder for the certificate encoding
itself.  This only parses the right side of the verifier-product input and
checks the chosen certificate-size bound; raw machine behavior is still a
separate normalizer obligation.
-/
noncomputable def ofCertificateDecoder
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (decodeCert : List V.Cert.Symbol → Option V.Cert.Carrier)
    (decodeCert_sound :
      ∀ {symbols : List V.Cert.Symbol} {c : V.Cert.Carrier},
        decodeCert symbols = some c → symbols = V.Cert.encode c)
    (decodeCert_complete :
      ∀ c : V.Cert.Carrier, decodeCert (V.Cert.encode c) = some c) :
    TMVerifierXOnlyEncodedSuffixDecoder V where
  decode x suffix :=
    match EncodedType.prodRightSuffixDecode (X := L.Instance) (Y := V.Cert) suffix with
    | none => none
    | some symbols =>
        match decodeCert symbols with
        | none => none
        | some c =>
            if V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x then some c else none
  decode_sound := by
    intro x suffix c hDecode
    cases hRight :
        EncodedType.prodRightSuffixDecode (X := L.Instance) (Y := V.Cert) suffix with
    | none =>
        simp [hRight] at hDecode
    | some symbols =>
        cases hCert : decodeCert symbols with
        | none =>
            simp [hRight, hCert] at hDecode
        | some c' =>
            by_cases hSize : V.Cert.inputSize c' ≤ tmVerifierCertificateSizeBound V x
            · have hc : c' = c := by
                simpa [hRight, hCert, hSize] using hDecode
              subst c'
              constructor
              · exact hSize
              · have hSuffix :=
                  EncodedType.prodRightSuffixDecode_sound (X := L.Instance) (Y := V.Cert)
                    hRight
                have hSymbols : symbols = V.Cert.encode c := decodeCert_sound hCert
                rw [hSuffix, hSymbols]
                rfl
            · simp [hRight, hCert, hSize] at hDecode
  decode_complete := by
    intro x c hSize
    have hRight :
        EncodedType.prodRightSuffixDecode (X := L.Instance) (Y := V.Cert)
          (tmVerifierCertificateInputSuffixEncoded V c) = some (V.Cert.encode c) := by
      simpa [tmVerifierCertificateInputSuffixEncoded] using
        EncodedType.prodRightSuffixDecode_complete (X := L.Instance) (Y := V.Cert)
          (V.Cert.encode c)
    simp [hRight, decodeCert_complete c, hSize]

/-- Decoding a raw word suffix gives the corresponding certificate-word suffix witness. -/
def wordSuffix_of_rawDecode
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    {c : V.Cert.Carrier}
    (hDecode :
      D.decode x (suffix.map (tmVerifierComputableWitness V).inputAlphabet) = some c) :
    TMVerifierCertificateWordSuffix V x suffix where
  cert := c
  cert_size := (D.decode_sound hDecode).1
  suffix_eq := by
    have hEnc := (D.decode_sound hDecode).2
    have hBack :
        (suffix.map (tmVerifierComputableWitness V).inputAlphabet).map
            (tmVerifierComputableWitness V).inputAlphabet.invFun = suffix := by
      simp [List.map_map, Function.comp_def]
    calc
      suffix =
          (suffix.map (tmVerifierComputableWitness V).inputAlphabet).map
            (tmVerifierComputableWitness V).inputAlphabet.invFun := hBack.symm
      _ = tmVerifierCertificateInputSuffixWord V c := by
          rw [hEnc]
          rfl

/-- A valid word-suffix witness is accepted by the encoded suffix decoder. -/
theorem decode_complete_wordSuffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) :
    D.decode x (suffix.map (tmVerifierComputableWitness V).inputAlphabet) =
      some w.cert := by
  cases w with
  | mk cert hSize hSuffix =>
      subst suffix
      simpa [tmVerifierCertificateInputSuffixWord, List.map_map, Function.comp_def]
        using D.decode_complete hSize

end TMVerifierXOnlyEncodedSuffixDecoder

namespace TMVerifierXOnlyRawSuffixDecodingNormalizer

/--
The decoder API is strong enough to inhabit the existing raw-suffix normalizer
interface, and therefore all downstream raw/checked Cook-Levin routes.
-/
def toRawSuffixNormalizer
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyRawSuffixDecodingNormalizer V) :
    TMVerifierXOnlyRawSuffixNormalizer V where
  normalize_suffix := by
    intro x suffix hRun
    rcases D.accepting_decode hRun with ⟨c, hDecode⟩
    exact D.decoder.wordSuffix_of_rawDecode hDecode

end TMVerifierXOnlyRawSuffixDecodingNormalizer

namespace TMVerifierXOnlyRawInputNormalizer

/-- A raw normalizer implies the raw soundness package used by the x-only root. -/
def toRawInputSound
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (N : TMVerifierXOnlyRawInputNormalizer V) :
    TMVerifierXOnlyRawInputSound V where
  accept_true_of_raw_run := by
    intro x suffix hRun
    let w := N.normalize hRun
    exact V.sound x w.cert w.verify_true

/--
A uniform raw normalizer yields the standard Cook-Levin theorem through the
existing raw-sound route, given a direct TM witness for CNF splitting.
-/
noncomputable def toCookLevinTheorem
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMCookLevinTheorem :=
  TMVerifierXOnlyRawInputSound.toCookLevinTheorem hSplit
    (fun V => (hNormalize V).toRawInputSound)

/--
Strict-logspace soundness plus a uniform raw normalizer gives the standard
Cook-Levin theorem through the raw-sound x-only route.
-/
noncomputable def toCookLevinTheoremOfStrictSound
    (hSound : StrictLogSpaceTMSound)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMCookLevinTheorem :=
  TMVerifierXOnlyRawInputSound.toCookLevinTheoremOfStrictSound hSound
    (fun V => (hNormalize V).toRawInputSound)

end TMVerifierXOnlyRawInputNormalizer

namespace TMVerifierXOnlyRawSuffixNormalizer

/--
A raw suffix normalizer induces the proof-relevant raw-input normalizer by
replaying the accepting run as a typed verifier run for the recovered
certificate.
-/
def toRawInputNormalizer
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (S : TMVerifierXOnlyRawSuffixNormalizer V) :
    TMVerifierXOnlyRawInputNormalizer V where
  normalize := by
    intro x suffix hRun
    let w := S.normalize_suffix hRun
    refine
      { cert := w.cert
        cert_size := w.cert_size
        verify_true := ?_ }
    have hOut :
        Turing.TM2OutputsInTime (tmVerifierTM V) (tmVerifierInputWord V (x, w.cert))
          (some (tmVerifierBoolOutputWord V true)) (tmVerifierXOnlyTimeBound V x) := by
      simpa [Turing.TM2OutputsInTime, tmVerifierOutputCfg, w.prefix_append_suffix_eq_inputWord]
        using hRun
    exact tmVerifier_verify_eq_true_of_outputs_true_in_arbitrary_time V (x, w.cert) hOut

/-- A raw suffix normalizer implies the raw soundness package used by the root. -/
def toRawInputSound
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (S : TMVerifierXOnlyRawSuffixNormalizer V) :
    TMVerifierXOnlyRawInputSound V :=
  S.toRawInputNormalizer.toRawInputSound

/--
A raw suffix normalizer also supplies checked suffix validity with an empty
suffix CNF: satisfying the global tableau already gives an accepting raw run,
and the normalizer recovers the certificate-suffix witness.
-/
noncomputable def toCheckedSuffixValidity
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (S : TMVerifierXOnlyRawSuffixNormalizer V) :
    TMVerifierXOnlyCheckedSuffixValidity V where
  suffixValidityCNF := fun _ => ([] : CNF)
  suffixValidityCNF_tm_polytime := by
    simpa using TMPolyTimeMap.const L.Instance cnfStructuredEncodedType ([] : CNF)
  validSuffixSeed_satisfies := by
    intro B x a w
    simp
  decodedSuffix_valid_of_satisfies := by
    intro B x a E _hSuffix
    have hRun :
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++
              E.decodedInitialCertificateSuffixWord))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) := by
      simpa [E.decodedCfg_initial_eq_rawInput] using E.rawOutputsTrueInTime
    exact S.normalize_suffix hRun

/--
A uniform raw suffix normalizer yields the standard Cook-Levin theorem through
the proof-relevant raw normalizer route.
-/
noncomputable def toCookLevinTheorem
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMCookLevinTheorem :=
  TMVerifierXOnlyRawInputNormalizer.toCookLevinTheorem hSplit
    (fun V => (hNormalize V).toRawInputNormalizer)

/--
Strict-logspace soundness plus a uniform raw suffix normalizer gives the
standard Cook-Levin theorem through the raw-normalization route.
-/
noncomputable def toCookLevinTheoremOfStrictSound
    (hSound : StrictLogSpaceTMSound)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMCookLevinTheorem :=
  TMVerifierXOnlyRawInputNormalizer.toCookLevinTheoremOfStrictSound hSound
    (fun V => (hNormalize V).toRawInputNormalizer)

end TMVerifierXOnlyRawSuffixNormalizer

end SAT
end ComplexityReduction
