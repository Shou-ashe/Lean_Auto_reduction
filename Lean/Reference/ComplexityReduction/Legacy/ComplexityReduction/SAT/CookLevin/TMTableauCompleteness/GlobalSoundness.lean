/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauSoundness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalRun
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalTableauAccepted

/-!
Positive soundness for the global fixed-micro x-only tableau seed.

`GlobalRun` extracts a true-output verifier-machine run from a satisfied global
tableau.  This file compares that run with the verifier's deterministic
`TM2ComputableInPolyTime` witness and packages the verifier-level iff.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyGlobalTableauSeed

/-- A satisfied x-only global tableau seed forces its chosen certificate to be accepted. -/
theorem verify_eq_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    V.verify x wSeed.cert = true :=
  tmVerifier_verify_eq_true_of_outputs_true_in_time V (x, wSeed.cert)
    wSeed.outputs_true_in_time

/-- A satisfied x-only global tableau seed yields a bounded accepting certificate. -/
def boundedAcceptingCertificate
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    TMVerifierBoundedAcceptingCertificate V x where
  cert := wSeed.cert
  cert_size := wSeed.cert_size
  verify_true := wSeed.verify_eq_true

/-- Seed-level positive soundness: the global tableau seed gives an accepted certificate. -/
theorem exists_verify_eq_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
      V.verify x c = true :=
  ⟨wSeed.cert, wSeed.cert_size, wSeed.verify_eq_true⟩

/-- Seed-level language soundness via the verifier's soundness field. -/
theorem isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    L.isYes x :=
  V.sound x wSeed.cert wSeed.verify_eq_true

end TMVerifierXOnlyGlobalTableauSeed

/-- CNF-level positive soundness for the global x-only tableau-seed surface. -/
theorem tmVerifierXOnlyGlobalTableauSeed_satisfiable_sound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauSeed V B x a)) →
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        V.verify x c = true := by
  rintro ⟨a, ⟨wSeed⟩⟩
  exact wSeed.exists_verify_eq_true

/-- CNF-level positive language soundness for the global x-only tableau-seed surface. -/
theorem tmVerifierXOnlyGlobalTableauSeed_satisfiable_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauSeed V B x a)) → L.isYes x := by
  intro h
  rcases tmVerifierXOnlyGlobalTableauSeed_satisfiable_sound V B x h with
    ⟨c, _hSize, hVerify⟩
  exact V.sound x c hVerify

/-- Bounded-certificate packaging of global x-only tableau-seed positive soundness. -/
theorem tmVerifierXOnlyGlobalTableauSeed_satisfiable_boundedCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauSeed V B x a)) →
      Nonempty (TMVerifierBoundedAcceptingCertificate V x) := by
  rintro ⟨a, ⟨wSeed⟩⟩
  exact ⟨wSeed.boundedAcceptingCertificate⟩

/--
Verifier-level iff for the active-boundary global x-only tableau seed.

This is the semantic bridge consumed by the next tableau-to-3CNF generator
slice.
-/
theorem tmVerifierXOnlyGlobalTableauSeed_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier) :
    (∃ a, Nonempty
      (TMVerifierXOnlyGlobalTableauSeed V (tmVerifierActivePushPayloadBoundary V) x a)) ↔
      L.isYes x := by
  constructor
  · exact tmVerifierXOnlyGlobalTableauSeed_satisfiable_isYes V
      (tmVerifierActivePushPayloadBoundary V) x
  · exact tmVerifierXOnlyGlobalTableauSeed_satisfiable_complete V x

end SAT
end ComplexityReduction
