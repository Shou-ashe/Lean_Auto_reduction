/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixDecoderTM

/-!
Encoding-discipline gate for the standard-TM Cook-Levin root.

The core `TMVerifier` API exposes an arbitrary `EncodedType` for certificates.
It does not include a generic decoder or image recognizer for certificate
suffixes.  This module records the extra proof-carrying discipline needed by
the x-only checked suffix route without changing the low-level verifier API.
-/

namespace ComplexityReduction
namespace SAT

/--
Extra certificate-suffix discipline for one direct `TMVerifier`.

The checked decoder supplies a direct-TM suffix CNF and proves that satisfying
that CNF makes the decoded x-only suffix a bounded certificate suffix.
-/
structure TMVerifierEncodingDiscipline
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  checkedSuffixDecoder : TMVerifierXOnlyCheckedSuffixDecoder V

namespace TMVerifierEncodingDiscipline

/-- Build the discipline directly from the existing checked suffix decoder. -/
def ofCheckedSuffixDecoder
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierXOnlyCheckedSuffixDecoder V) :
    TMVerifierEncodingDiscipline V where
  checkedSuffixDecoder := D

/-- Forget the discipline to the checked decoder interface. -/
def toCheckedSuffixDecoder
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierEncodingDiscipline V) :
    TMVerifierXOnlyCheckedSuffixDecoder V :=
  D.checkedSuffixDecoder

/-- Forget the explicit decoder to the checked suffix-validity package. -/
noncomputable def toCheckedSuffixValidity
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (D : TMVerifierEncodingDiscipline V) :
    TMVerifierXOnlyCheckedSuffixValidity V :=
  D.checkedSuffixDecoder.toCheckedSuffixValidity

end TMVerifierEncodingDiscipline

/--
Uniform discipline obligation for the current arbitrary-`EncodedType`
`TMVerifier` surface.

This is intentionally a proposition rather than a supplied theorem: the current
`TMVerifier` fields do not determine such a decoder for all certificate
encodings.
-/
def UniformTMVerifierEncodingDiscipline : Prop :=
  {L : EncodedDecisionProblem} ->
    (V : TMVerifier L) -> Nonempty (TMVerifierEncodingDiscipline V)

/-- A uniform encoding discipline supplies the uniform checked suffix package. -/
noncomputable def uniformCheckedSuffixValidityOfEncodingDiscipline
    (hDiscipline : UniformTMVerifierEncodingDiscipline) :
    {L : EncodedDecisionProblem} ->
      (V : TMVerifier L) -> TMVerifierXOnlyCheckedSuffixValidity V :=
  fun V => (Classical.choice (hDiscipline V)).toCheckedSuffixValidity

/--
Given a direct CNF splitter and a uniform encoding discipline, the existing
checked x-only route yields the current standard-TM Cook-Levin proof object.
-/
noncomputable def standardTMCookLevinTheoremOfEncodingDiscipline
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hDiscipline : UniformTMVerifierEncodingDiscipline) :
    TMCookLevinTheorem :=
  TMVerifierXOnlyCheckedSuffixValidity.toCookLevinTheorem hSplit
    (uniformCheckedSuffixValidityOfEncodingDiscipline hDiscipline)

#check TMVerifierEncodingDiscipline
#check TMVerifierEncodingDiscipline.ofCheckedSuffixDecoder
#check TMVerifierEncodingDiscipline.toCheckedSuffixDecoder
#check TMVerifierEncodingDiscipline.toCheckedSuffixValidity
#check UniformTMVerifierEncodingDiscipline
#check uniformCheckedSuffixValidityOfEncodingDiscipline
#check standardTMCookLevinTheoremOfEncodingDiscipline

end SAT
end ComplexityReduction
