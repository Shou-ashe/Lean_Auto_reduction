/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTransitionRowSemantics
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMXOnlyCertificate
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauBlocks
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauExtraction
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauControlUniqueness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauWindowEffects
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauMicroDomains
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauGuardSelection
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStepAux
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauWindowSelection
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauMacroSteps
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauIOStacks
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauRun
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauSoundness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMRootXOnly
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawNormalizationTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityTransport
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.CNFSplit
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMStandard
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATStructuredEncoderTM

/-!
Conditional standard-TM root surface for bundled 3SAT.

P16h supplies direct bundled-3SAT membership.  A future full standard-TM
Cook-Levin theorem can be combined with that membership here, without using the
project-local `SAT.localCookLevinTheorem` as a substitute.
-/

namespace ComplexityReduction
namespace SAT

/--
If the missing standard-TM Cook-Levin theorem is supplied, bundled 3SAT becomes
standard-TM NP-complete using the direct P16h finite-certificate verifier.
-/
theorem threeSAT_TMNPComplete_of_tMCookLevin
    (H : TMCookLevinTheorem) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  H.threeSAT_TMNPComplete_of_membership threeSAT_TMInNP

/--
The checked x-only Cook-Levin route is enough for bundled 3SAT standard-TM
NP-completeness once its two remaining direct generator obligations are supplied.
-/
theorem threeSAT_TMNPComplete_of_checkedXOnlyCookLevin
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyCheckedSuffixValidity.toCookLevinTheorem hSplit hSuffix)

/--
Version of the checked x-only root using the reviewed strict CNF splitter and
an explicit strict-logspace soundness boundary.
-/
theorem threeSAT_TMNPComplete_of_checkedXOnlyCookLevin_strictSound
    (hSound : StrictLogSpaceTMSound)
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyCheckedSuffixValidity.toCookLevinTheoremOfStrictSound hSound hSuffix)

/--
The raw-input x-only Cook-Levin route is enough for bundled 3SAT standard-TM
NP-completeness once raw accepting soundness is supplied uniformly.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyCookLevin
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawInputSound.toCookLevinTheorem hSplit hRawSound)

/--
The normalized raw-input route is enough for bundled 3SAT standard-TM
NP-completeness once normalization is supplied uniformly.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyNormalizer
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawInputNormalizer.toCookLevinTheorem hSplit hNormalize)

/--
The raw-suffix normalization route is enough for bundled 3SAT standard-TM
NP-completeness once certificate-suffix recovery is supplied uniformly.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawSuffixNormalizer.toCookLevinTheorem hSplit hNormalize)

/--
Version of the raw-input x-only root using the reviewed strict CNF splitter and
an explicit strict-logspace soundness boundary.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyCookLevin_strictSound
    (hSound : StrictLogSpaceTMSound)
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawInputSound.toCookLevinTheoremOfStrictSound hSound hRawSound)

/--
Version of the normalized raw-input root using the reviewed strict CNF splitter
and an explicit strict-logspace soundness boundary.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyNormalizer_strictSound
    (hSound : StrictLogSpaceTMSound)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawInputNormalizer.toCookLevinTheoremOfStrictSound
      hSound hNormalize)

/--
Version of the raw-suffix normalization root using the reviewed strict CNF
splitter and an explicit strict-logspace soundness boundary.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_strictSound
    (hSound : StrictLogSpaceTMSound)
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_tMCookLevin
    (TMVerifierXOnlyRawSuffixNormalizer.toCookLevinTheoremOfStrictSound
      hSound hNormalize)

/-! ### Direct structured-3SAT root via the TM-backed Karp21 splitter -/

/--
The checked x-only emitted CNF followed by the direct Karp21 structured splitter
gives a TM Karp reduction to faithful structured 3SAT without the strict
log-space splitter boundary.
-/
noncomputable def checkedXOnlyCookLevinStructuredTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V) :
    TMKarpReduction L Karp21.threeSATStructuredDecisionProblem where
  f := fun x =>
    Karp21.cnfSplitFromStructuredBoundToThreeCNF
      (G.emittedCNF (tmVerifierActivePushPayloadBoundary V) x)
  polytime := by
    have hCNF := G.emittedCNF_tm_polytime (tmVerifierActivePushPayloadBoundary V)
    have hComp := TMPolyTimeMap.comp Karp21.cnfSATToThreeSATStructured_tm_polytime hCNF
    simpa [Function.comp, Karp21.threeSATStructuredDecisionProblem] using hComp
  correct := by
    intro x
    exact Iff.trans (G.emittedCNF_satisfiable_iff_isYes x).symm
      (Karp21.cnfSplitFromStructuredBound_satisfiable_iff _).symm

/--
Uniform checked suffix validity is enough to make faithful structured 3SAT
TM-NP-complete using the direct Karp21 splitter.  This intentionally targets
`Karp21.threeSATStructuredDecisionProblem`, not the historical bundled 3SAT
encoding.
-/
theorem threeSATStructured_TMNPComplete_of_checkedXOnlyCookLevin
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMNPCompleteEnc Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨V⟩
    exact ⟨checkedXOnlyCookLevinStructuredTMKarpReduction (hSuffix V)⟩

/--
The raw-sound x-only emitted CNF followed by the direct Karp21 structured
splitter gives a TM Karp reduction to faithful structured 3SAT without the
strict log-space splitter boundary.
-/
noncomputable def rawXOnlyCookLevinStructuredTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V) :
    TMKarpReduction L Karp21.threeSATStructuredDecisionProblem where
  f := fun x =>
    Karp21.cnfSplitFromStructuredBoundToThreeCNF
      (R.emittedCNF (tmVerifierActivePushPayloadBoundary V) x)
  polytime := by
    have hCNF := R.emittedCNF_tm_polytime (tmVerifierActivePushPayloadBoundary V)
    have hComp := TMPolyTimeMap.comp Karp21.cnfSATToThreeSATStructured_tm_polytime hCNF
    simpa [Function.comp, Karp21.threeSATStructuredDecisionProblem] using hComp
  correct := by
    intro x
    exact Iff.trans (R.emittedCNF_satisfiable_iff_isYes x).symm
      (Karp21.cnfSplitFromStructuredBound_satisfiable_iff _).symm

/--
The normalized raw route followed by the direct Karp21 structured splitter gives
a TM Karp reduction to faithful structured 3SAT.
-/
noncomputable def rawNormalizerXOnlyCookLevinStructuredTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (N : TMVerifierXOnlyRawInputNormalizer V) :
    TMKarpReduction L Karp21.threeSATStructuredDecisionProblem :=
  rawXOnlyCookLevinStructuredTMKarpReduction N.toRawInputSound

/--
The raw-suffix normalizer followed by the direct Karp21 structured splitter
gives a TM Karp reduction to faithful structured 3SAT.
-/
noncomputable def rawSuffixNormalizerXOnlyCookLevinStructuredTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (S : TMVerifierXOnlyRawSuffixNormalizer V) :
    TMKarpReduction L Karp21.threeSATStructuredDecisionProblem :=
  rawNormalizerXOnlyCookLevinStructuredTMKarpReduction S.toRawInputNormalizer

/--
Uniform raw accepting soundness is enough to make faithful structured 3SAT
TM-NP-complete using the direct Karp21 splitter.  This still leaves the raw
soundness normalization obligation explicit.
-/
theorem threeSATStructured_TMNPComplete_of_rawXOnlyCookLevin
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMNPCompleteEnc Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨V⟩
    exact ⟨rawXOnlyCookLevinStructuredTMKarpReduction (hRawSound V)⟩

/--
Uniform raw normalization is enough to make faithful structured 3SAT
TM-NP-complete using the direct Karp21 splitter.
-/
theorem threeSATStructured_TMNPComplete_of_rawXOnlyNormalizer
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMNPCompleteEnc Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨V⟩
    exact ⟨rawNormalizerXOnlyCookLevinStructuredTMKarpReduction (hNormalize V)⟩

/--
Uniform raw-suffix normalization is enough to make faithful structured 3SAT
TM-NP-complete using the direct Karp21 splitter.
-/
theorem threeSATStructured_TMNPComplete_of_rawXOnlySuffixNormalizer
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMNPCompleteEnc Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨V⟩
    exact ⟨rawSuffixNormalizerXOnlyCookLevinStructuredTMKarpReduction (hNormalize V)⟩

/-! ### Conditional transfer from faithful structured 3SAT to bundled 3SAT -/

/--
Identity reduction from faithful structured 3SAT to the historical bundled
3SAT target, conditional on the missing direct structured-to-standard encoder.

The premise is intentionally a direct `TMPolyTimeMap`: this wrapper isolates the
remaining encoding direction without using `CostedTMSound` or a size-only
shortcut.
-/
noncomputable def threeSATStructuredToStandardTMKarpReduction
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ)) :
    TMKarpReduction Karp21.threeSATStructuredDecisionProblem threeSATDecisionProblem where
  f := fun φ => φ
  polytime := hEncode
  correct := by
    intro φ
    rfl

/-! ### Per-verifier bundled 3SAT reductions through the direct encoder -/

/--
Checked-suffix x-only Cook-Levin gives a direct TM Karp reduction to the
historical bundled 3SAT target after composing the faithful structured route
with the verified structured-to-standard encoder.
-/
noncomputable def checkedXOnlyCookLevinBundledTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V) :
    TMKarpReduction L threeSATDecisionProblem :=
  TMKarpReduction.comp
    (threeSATStructuredToStandardTMKarpReduction threeCNFStructuredToStandard_tm_polytime)
    (checkedXOnlyCookLevinStructuredTMKarpReduction G)

/--
Raw-sound x-only Cook-Levin gives a direct TM Karp reduction to the historical
bundled 3SAT target after composing through the verified structured encoder.
-/
noncomputable def rawXOnlyCookLevinBundledTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V) :
    TMKarpReduction L threeSATDecisionProblem :=
  TMKarpReduction.comp
    (threeSATStructuredToStandardTMKarpReduction threeCNFStructuredToStandard_tm_polytime)
    (rawXOnlyCookLevinStructuredTMKarpReduction R)

/--
Raw-normalizer x-only Cook-Levin gives a direct TM Karp reduction to the
historical bundled 3SAT target after composing through the verified structured
encoder.
-/
noncomputable def rawNormalizerXOnlyCookLevinBundledTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (N : TMVerifierXOnlyRawInputNormalizer V) :
    TMKarpReduction L threeSATDecisionProblem :=
  rawXOnlyCookLevinBundledTMKarpReduction N.toRawInputSound

/--
Raw-suffix-normalizer x-only Cook-Levin gives a direct TM Karp reduction to the
historical bundled 3SAT target after composing through the verified structured
encoder.
-/
noncomputable def rawSuffixNormalizerXOnlyCookLevinBundledTMKarpReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (S : TMVerifierXOnlyRawSuffixNormalizer V) :
    TMKarpReduction L threeSATDecisionProblem :=
  rawNormalizerXOnlyCookLevinBundledTMKarpReduction S.toRawInputNormalizer

/-! ### Witnessed NP packages for the remaining suffix/raw obligation -/

/--
A language has an NP verifier equipped with a checked suffix-validity package.
This is weaker than requiring every verifier for the language to carry the
package, and records the exact remaining witness needed by the checked route.
-/
def TMInNPWithCheckedSuffixValidity (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierXOnlyCheckedSuffixValidity V)

/--
A language has an NP verifier equipped with raw-input soundness for arbitrary
certificate suffix words.
-/
def TMInNPWithRawInputSound (L : EncodedDecisionProblem) : Prop :=
  ∃ V : TMVerifier L, TMVerifierXOnlyRawInputSound V

/--
A language has an NP verifier equipped with raw-input normalization, recovering
a bounded typed certificate from every accepting raw suffix run.
-/
def TMInNPWithRawInputNormalizer (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierXOnlyRawInputNormalizer V)

/--
A language has an NP verifier equipped with raw-suffix normalization, recovering
a certificate-suffix image witness from every accepting raw suffix run.
-/
def TMInNPWithRawSuffixNormalizer (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierXOnlyRawSuffixNormalizer V)

namespace TMInNPWithCheckedSuffixValidity

/-- Forgetting the checked suffix package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithCheckedSuffixValidity L) : TMInNP L := by
  rcases h with ⟨⟨V, _G⟩⟩
  exact ⟨V⟩

end TMInNPWithCheckedSuffixValidity

namespace TMInNPWithRawInputSound

/-- Forgetting the raw-input soundness package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithRawInputSound L) : TMInNP L := by
  rcases h with ⟨V, _R⟩
  exact ⟨V⟩

end TMInNPWithRawInputSound

namespace TMInNPWithRawInputNormalizer

/-- Forgetting the raw-input normalizer package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithRawInputNormalizer L) : TMInNP L := by
  rcases h with ⟨⟨V, _N⟩⟩
  exact ⟨V⟩

/-- A normalizing verifier is in particular raw-input sound. -/
def toRawInputSound {L : EncodedDecisionProblem}
    (h : TMInNPWithRawInputNormalizer L) : TMInNPWithRawInputSound L := by
  rcases h with ⟨⟨V, N⟩⟩
  exact ⟨V, N.toRawInputSound⟩

end TMInNPWithRawInputNormalizer

namespace TMInNPWithRawSuffixNormalizer

/-- Forgetting the raw-suffix normalizer package recovers ordinary direct TM `NP`. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixNormalizer L) : TMInNP L := by
  rcases h with ⟨⟨V, _S⟩⟩
  exact ⟨V⟩

/-- A raw-suffix normalizing verifier is in particular raw-input normalizing. -/
def toRawInputNormalizer {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixNormalizer L) : TMInNPWithRawInputNormalizer L := by
  rcases h with ⟨⟨V, S⟩⟩
  exact ⟨⟨V, S.toRawInputNormalizer⟩⟩

/-- A raw-suffix normalizing verifier is in particular raw-input sound. -/
def toRawInputSound {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixNormalizer L) : TMInNPWithRawInputSound L :=
  h.toRawInputNormalizer.toRawInputSound

/--
A raw-suffix normalizing verifier also supplies checked suffix validity: the
checked suffix CNF can be empty because the normalizer recovers the typed
certificate suffix from the accepting raw tableau run.
-/
noncomputable def toCheckedSuffixValidity {L : EncodedDecisionProblem}
    (h : TMInNPWithRawSuffixNormalizer L) : TMInNPWithCheckedSuffixValidity L := by
  rcases h with ⟨⟨V, S⟩⟩
  exact ⟨⟨V, S.toCheckedSuffixValidity⟩⟩

end TMInNPWithRawSuffixNormalizer

/--
If every direct-TM NP language admits some verifier with checked suffix validity,
then historical bundled 3SAT is standard-TM NP-complete.  The premise is the
remaining semantic witness obligation; the reduction itself is a direct
`TMKarpReduction`.
-/
theorem threeSAT_TMNPComplete_of_checkedXOnlyCookLevin_witnessed
    (hSuffix :
      {L : EncodedDecisionProblem} →
        TMInNP L → TMInNPWithCheckedSuffixValidity L) :
    TMNPCompleteEnc threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hSuffix hL with ⟨⟨V, G⟩⟩
    exact ⟨checkedXOnlyCookLevinBundledTMKarpReduction G⟩

/--
If every direct-TM NP language admits some raw-sound verifier, bundled 3SAT is
standard-TM NP-complete through the raw-input x-only route.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyCookLevin_witnessed
    (hRawSound :
      {L : EncodedDecisionProblem} →
        TMInNP L → TMInNPWithRawInputSound L) :
    TMNPCompleteEnc threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hRawSound hL with ⟨V, R⟩
    exact ⟨rawXOnlyCookLevinBundledTMKarpReduction R⟩

/--
If every direct-TM NP language admits some raw-normalizing verifier, bundled
3SAT is standard-TM NP-complete through the normalization route.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyNormalizer_witnessed
    (hNormalize :
      {L : EncodedDecisionProblem} →
        TMInNP L → TMInNPWithRawInputNormalizer L) :
    TMNPCompleteEnc threeSATDecisionProblem := by
  refine threeSAT_TMNPComplete_of_rawXOnlyCookLevin_witnessed ?_
  intro L hL
  exact (hNormalize hL).toRawInputSound

/--
If every direct-TM NP language admits some raw-suffix-normalizing verifier,
bundled 3SAT is standard-TM NP-complete through the suffix-normalization route.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_witnessed
    (hNormalize :
      {L : EncodedDecisionProblem} →
        TMInNP L → TMInNPWithRawSuffixNormalizer L) :
    TMNPCompleteEnc threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hNormalize hL with ⟨⟨V, S⟩⟩
    exact ⟨rawSuffixNormalizerXOnlyCookLevinBundledTMKarpReduction S⟩

/-! ### Complete roots for explicitly packaged NP witnesses -/

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying an explicit checked suffix-validity witness.  Unlike the
ordinary `TMNPCompleteEnc` wrapper above, this target has no global premise
converting arbitrary `TMInNP` witnesses into checked packages.
-/
def TMNPCompleteEncWithCheckedSuffixValidity (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithCheckedSuffixValidity L → TMPolyReducible L K

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying an explicit raw-input soundness witness.
-/
def TMNPCompleteEncWithRawInputSound (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithRawInputSound L → TMPolyReducible L K

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying an explicit proof-relevant raw-input normalizer.
-/
def TMNPCompleteEncWithRawInputNormalizer (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithRawInputNormalizer L → TMPolyReducible L K

/--
Bundled 3SAT is ordinary direct-TM `NP` and hard for the class of direct-TM NP
languages carrying an explicit raw-suffix normalizer.
-/
def TMNPCompleteEncWithRawSuffixNormalizer (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithRawSuffixNormalizer L → TMPolyReducible L K

namespace TMNPCompleteEncWithCheckedSuffixValidity

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixValidity K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixValidity K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithCheckedSuffixValidity L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer checked-suffix packaged NP-completeness along a direct TM many-one
reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithCheckedSuffixValidity A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithCheckedSuffixValidity B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

/--
Checked-suffix hardness also covers raw-suffix-normalizing witnesses, since a
raw-suffix normalizer gives checked suffix validity with the empty suffix CNF.
-/
theorem toRawSuffixNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithCheckedSuffixValidity K) :
    TMNPCompleteEncWithRawSuffixNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    rcases hL with ⟨⟨V, S⟩⟩
    exact h.hard L ⟨⟨V, S.toCheckedSuffixValidity⟩⟩

end TMNPCompleteEncWithCheckedSuffixValidity

namespace TMNPCompleteEncWithRawInputSound

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputSound K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputSound K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithRawInputSound L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer raw-sound packaged NP-completeness along a direct TM many-one
reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithRawInputSound A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithRawInputSound B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

/-- Raw-input-sound hardness covers the narrower raw-normalizing package. -/
theorem toRawInputNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputSound K) :
    TMNPCompleteEncWithRawInputNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawInputSound

/-- Raw-input-sound hardness covers the narrower raw-suffix-normalizing package. -/
theorem toRawSuffixNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputSound K) :
    TMNPCompleteEncWithRawSuffixNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawInputSound

end TMNPCompleteEncWithRawInputSound

namespace TMNPCompleteEncWithRawInputNormalizer

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputNormalizer K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputNormalizer K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithRawInputNormalizer L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer raw-normalizer packaged NP-completeness along a direct TM many-one
reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithRawInputNormalizer A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithRawInputNormalizer B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

/-- Raw-normalizer hardness covers the narrower raw-suffix-normalizing package. -/
theorem toRawSuffixNormalizer {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawInputNormalizer K) :
    TMNPCompleteEncWithRawSuffixNormalizer K := by
  constructor
  · exact h.mem_np
  · intro L hL
    exact h.hard L hL.toRawInputNormalizer

end TMNPCompleteEncWithRawInputNormalizer

namespace TMNPCompleteEncWithRawSuffixNormalizer

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawSuffixNormalizer K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithRawSuffixNormalizer K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithRawSuffixNormalizer L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Transfer raw-suffix-normalizer packaged NP-completeness along a direct TM
many-one reduction.  The target membership hypothesis remains explicit.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithRawSuffixNormalizer A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithRawSuffixNormalizer B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

end TMNPCompleteEncWithRawSuffixNormalizer

/--
The checked-suffix Cook-Levin route gives an unconditional complete root for
the explicitly packaged checked-suffix NP class.
-/
theorem threeSAT_TMNPComplete_with_checkedSuffixValidity :
    TMNPCompleteEncWithCheckedSuffixValidity threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, G⟩⟩
    exact ⟨checkedXOnlyCookLevinBundledTMKarpReduction G⟩

/--
The raw-input soundness route gives an unconditional complete root for the
explicitly packaged raw-sound NP class.
-/
theorem threeSAT_TMNPComplete_with_rawInputSound :
    TMNPCompleteEncWithRawInputSound threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hL with ⟨V, R⟩
    exact ⟨rawXOnlyCookLevinBundledTMKarpReduction R⟩

/--
The raw-input normalizer route gives an unconditional complete root for the
explicitly packaged raw-normalizing NP class.
-/
theorem threeSAT_TMNPComplete_with_rawInputNormalizer :
    TMNPCompleteEncWithRawInputNormalizer threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, N⟩⟩
    exact ⟨rawNormalizerXOnlyCookLevinBundledTMKarpReduction N⟩

/--
The raw-suffix normalizer route gives an unconditional complete root for the
explicitly packaged raw-suffix-normalizing NP class.
-/
theorem threeSAT_TMNPComplete_with_rawSuffixNormalizer :
    TMNPCompleteEncWithRawSuffixNormalizer threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, S⟩⟩
    exact ⟨rawSuffixNormalizerXOnlyCookLevinBundledTMKarpReduction S⟩

/-! ### Complete packaged roots for faithful structured 3SAT -/

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged checked-suffix NP class.
-/
theorem threeSATStructured_TMNPComplete_with_checkedSuffixValidity :
    TMNPCompleteEncWithCheckedSuffixValidity Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, G⟩⟩
    exact ⟨checkedXOnlyCookLevinStructuredTMKarpReduction G⟩

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged raw-sound NP class.
-/
theorem threeSATStructured_TMNPComplete_with_rawInputSound :
    TMNPCompleteEncWithRawInputSound Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨V, R⟩
    exact ⟨rawXOnlyCookLevinStructuredTMKarpReduction R⟩

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged raw-normalizing NP class.
-/
theorem threeSATStructured_TMNPComplete_with_rawInputNormalizer :
    TMNPCompleteEncWithRawInputNormalizer Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, N⟩⟩
    exact ⟨rawNormalizerXOnlyCookLevinStructuredTMKarpReduction N⟩

/--
Faithful structured 3SAT is ordinary direct-TM `NP` and hard for the explicitly
packaged raw-suffix-normalizing NP class.
-/
theorem threeSATStructured_TMNPComplete_with_rawSuffixNormalizer :
    TMNPCompleteEncWithRawSuffixNormalizer Karp21.threeSATStructuredDecisionProblem := by
  constructor
  · exact threeSATStructuredFinite_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, S⟩⟩
    exact ⟨rawSuffixNormalizerXOnlyCookLevinStructuredTMKarpReduction S⟩

/--
Transfer TM-NP-completeness from faithful structured 3SAT to the historical
bundled 3SAT target once the direct structured-to-standard encoder is supplied.
-/
theorem threeSAT_TMNPComplete_of_structuredRoot
    (hStructured : TMNPCompleteEnc Karp21.threeSATStructuredDecisionProblem)
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ)) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  TMNPCompleteEnc.transfer hStructured
    ⟨threeSATStructuredToStandardTMKarpReduction hEncode⟩
    threeSAT_TMInNP

/--
Checked-suffix structured root transferred to bundled 3SAT through an explicit
direct structured-to-standard encoder witness.
-/
theorem threeSAT_TMNPComplete_of_checkedXOnlyCookLevin_structuredEncoder
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ))
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_structuredRoot
    (threeSATStructured_TMNPComplete_of_checkedXOnlyCookLevin hSuffix)
    hEncode

/--
Raw-sound structured root transferred to bundled 3SAT through an explicit
direct structured-to-standard encoder witness.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyCookLevin_structuredEncoder
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ))
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_structuredRoot
    (threeSATStructured_TMNPComplete_of_rawXOnlyCookLevin hRawSound)
    hEncode

/--
Raw-normalizer structured root transferred to bundled 3SAT through an explicit
direct structured-to-standard encoder witness.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyNormalizer_structuredEncoder
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ))
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_structuredRoot
    (threeSATStructured_TMNPComplete_of_rawXOnlyNormalizer hNormalize)
    hEncode

/--
Raw-suffix-normalizer structured root transferred to bundled 3SAT through an
explicit direct structured-to-standard encoder witness.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_structuredEncoder
    (hEncode :
      TMPolyTimeMap
        Karp21.threeSATStructuredDecisionProblem.Instance
        threeSATDecisionProblem.Instance
        (fun φ : ThreeCNF => φ))
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_structuredRoot
    (threeSATStructured_TMNPComplete_of_rawXOnlySuffixNormalizer hNormalize)
    hEncode

/-! ### Bundled 3SAT root through the direct structured-to-standard encoder -/

/--
Checked-suffix structured root transferred to bundled 3SAT through the direct
structured-to-standard encoder constructed in `ThreeSATStructuredEncoderTM`.
-/
theorem threeSAT_TMNPComplete_of_checkedXOnlyCookLevin_structured
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_checkedXOnlyCookLevin_structuredEncoder
    threeCNFStructuredToStandard_tm_polytime hSuffix

/--
Raw-sound structured root transferred to bundled 3SAT through the direct
structured-to-standard encoder constructed in `ThreeSATStructuredEncoderTM`.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyCookLevin_structured
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_rawXOnlyCookLevin_structuredEncoder
    threeCNFStructuredToStandard_tm_polytime hRawSound

/--
Raw-normalizer structured root transferred to bundled 3SAT through the direct
structured-to-standard encoder constructed in `ThreeSATStructuredEncoderTM`.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlyNormalizer_structured
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_rawXOnlyNormalizer_structuredEncoder
    threeCNFStructuredToStandard_tm_polytime hNormalize

/--
Raw-suffix-normalizer structured root transferred to bundled 3SAT through the
direct structured-to-standard encoder constructed in
`ThreeSATStructuredEncoderTM`.
-/
theorem threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_structured
    (hNormalize :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawSuffixNormalizer V) :
    TMNPCompleteEnc threeSATDecisionProblem :=
  threeSAT_TMNPComplete_of_rawXOnlySuffixNormalizer_structuredEncoder
    threeCNFStructuredToStandard_tm_polytime hNormalize

end SAT
end ComplexityReduction
