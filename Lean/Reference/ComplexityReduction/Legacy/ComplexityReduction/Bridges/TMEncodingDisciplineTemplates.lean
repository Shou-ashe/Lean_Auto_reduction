/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDiscipline
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolCheckedSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyNatListSuffixCompletenessTM

/-!
Reusable certificate-encoding discipline templates.

These are thin public wrappers around the checked suffix-decoder constructors.
They let verifier packages expose the `TMVerifierEncodingDiscipline` premise
needed by the disciplined standard-TM Cook-Levin root without making generated
proofs rebuild the suffix-decoder records manually.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierEncodingDiscipline

/-- Package a finite Boolean certificate suffix decoder as encoding discipline. -/
noncomputable def ofFiniteBoolCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool -> V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfBits : List Bool -> V.Cert.Carrier)
    (bitsOfCert : V.Cert.Carrier -> List Bool)
    (certOfBits_suffix_eq :
      forall bits : List Bool,
        tmVerifierCertificateInputSuffixEncoded V (certOfBits bits) =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol bits).map
            (fun s => some (Sum.inr s)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol
              (bitsOfCert c)).map (fun s => some (Sum.inr s))) :
    TMVerifierEncodingDiscipline V :=
  ofCheckedSuffixDecoder
    (tmVerifierFiniteBoolCheckedSuffixDecoder V bitSymbol delimiterSymbol D certOfBits
      bitsOfCert certOfBits_suffix_eq cert_suffix_eq)

/-- Alias for finite Boolean list certificates. -/
noncomputable def ofBoolListCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool -> V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfBits : List Bool -> V.Cert.Carrier)
    (bitsOfCert : V.Cert.Carrier -> List Bool)
    (certOfBits_suffix_eq :
      forall bits : List Bool,
        tmVerifierCertificateInputSuffixEncoded V (certOfBits bits) =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol bits).map
            (fun s => some (Sum.inr s)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol
              (bitsOfCert c)).map (fun s => some (Sum.inr s))) :
    TMVerifierEncodingDiscipline V :=
  ofFiniteBoolCertificate V bitSymbol delimiterSymbol D certOfBits bitsOfCert
    certOfBits_suffix_eq cert_suffix_eq

/-- Package a unary nat-list certificate suffix decoder as encoding discipline. -/
noncomputable def ofNatListCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat -> V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier -> List Nat)
    (certOfNats_suffix_eq :
      forall xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V))) :
    TMVerifierEncodingDiscipline V :=
  ofCheckedSuffixDecoder
    (tmVerifierNatListCheckedSuffixDecoderComplete V trueSymbol falseSymbol delimiterSymbol
      hTrueFalse hTrueDelimiter hFalseDelimiter D certOfNats natsOfCert
      certOfNats_suffix_eq cert_suffix_eq)

/--
Finite-domain list certificates use the nat-list stream once the concrete
verifier has chosen its finite-value-to-nat presentation.
-/
noncomputable def ofFinListCertificate
    {_arity : Nat}
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat -> V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier -> List Nat)
    (certOfNats_suffix_eq :
      forall xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V))) :
    TMVerifierEncodingDiscipline V :=
  ofNatListCertificate V trueSymbol falseSymbol delimiterSymbol hTrueFalse hTrueDelimiter
    hFalseDelimiter D certOfNats natsOfCert certOfNats_suffix_eq cert_suffix_eq

/-- Assignment certificates are finite Boolean certificate streams. -/
noncomputable def ofAssignmentCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool -> V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfBits : List Bool -> V.Cert.Carrier)
    (bitsOfCert : V.Cert.Carrier -> List Bool)
    (certOfBits_suffix_eq :
      forall bits : List Bool,
        tmVerifierCertificateInputSuffixEncoded V (certOfBits bits) =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol bits).map
            (fun s => some (Sum.inr s)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierFiniteBoolCertificateSymbols (V := V) bitSymbol delimiterSymbol
              (bitsOfCert c)).map (fun s => some (Sum.inr s))) :
    TMVerifierEncodingDiscipline V :=
  ofFiniteBoolCertificate V bitSymbol delimiterSymbol D certOfBits bitsOfCert
    certOfBits_suffix_eq cert_suffix_eq

/-- Subset certificates use the nat-list stream for selected indices. -/
noncomputable def ofSubsetCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat -> V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier -> List Nat)
    (certOfNats_suffix_eq :
      forall xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V))) :
    TMVerifierEncodingDiscipline V :=
  ofNatListCertificate V trueSymbol falseSymbol delimiterSymbol hTrueFalse hTrueDelimiter
    hFalseDelimiter D certOfNats natsOfCert certOfNats_suffix_eq cert_suffix_eq

/-- Ordering certificates use the nat-list stream for the ordered vertex/item indices. -/
noncomputable def ofOrderingCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (hTrueFalse : trueSymbol ≠ falseSymbol)
    (hTrueDelimiter : trueSymbol ≠ delimiterSymbol)
    (hFalseDelimiter : falseSymbol ≠ delimiterSymbol)
    (D : TMVerifierXOnlyEncodedSuffixDecoder V)
    (certOfNats : List Nat -> V.Cert.Carrier)
    (natsOfCert : V.Cert.Carrier -> List Nat)
    (certOfNats_suffix_eq :
      forall xs : List Nat,
        tmVerifierCertificateInputSuffixEncoded V (certOfNats xs) =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol xs).map (tmVerifierInputRightSymbol (V := V)))
    (cert_suffix_eq :
      forall c : V.Cert.Carrier,
        tmVerifierCertificateInputSuffixEncoded V c =
          (tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
              delimiterSymbol (natsOfCert c)).map (tmVerifierInputRightSymbol (V := V))) :
    TMVerifierEncodingDiscipline V :=
  ofNatListCertificate V trueSymbol falseSymbol delimiterSymbol hTrueFalse hTrueDelimiter
    hFalseDelimiter D certOfNats natsOfCert certOfNats_suffix_eq cert_suffix_eq

#check TMVerifierEncodingDiscipline.ofFiniteBoolCertificate
#check TMVerifierEncodingDiscipline.ofBoolListCertificate
#check TMVerifierEncodingDiscipline.ofNatListCertificate
#check TMVerifierEncodingDiscipline.ofFinListCertificate
#check TMVerifierEncodingDiscipline.ofAssignmentCertificate
#check TMVerifierEncodingDiscipline.ofSubsetCertificate
#check TMVerifierEncodingDiscipline.ofOrderingCertificate

end TMVerifierEncodingDiscipline

end SAT
end ComplexityReduction
