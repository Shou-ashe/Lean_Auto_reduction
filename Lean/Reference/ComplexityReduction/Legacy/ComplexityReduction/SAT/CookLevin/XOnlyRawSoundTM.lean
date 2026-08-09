/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixValidityTM

/-!
Raw-input soundness route for the x-only Cook-Levin surface.

The checked suffix-validity route proves soundness by recovering a typed
certificate from the decoded suffix.  This file records the other honest route:
if the extracted verifier machine is known to be sound on every raw input word
with the fixed instance prefix, the suffix-validity CNF can be empty.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyGlobalTableauEvidence

/--
The decoded initial row of a satisfied x-only tableau is the raw TM initial
configuration for the fixed instance prefix followed by the decoded suffix.
-/
theorem decodedCfg_initial_eq_rawInput
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x) =
      Turing.initList (tmVerifierTM V)
        (tmVerifierInstanceInputPrefixWord V x ++ E.decodedInitialCertificateSuffixWord) := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  have hStacks :
      (E.decodedCfg 0 ht0).stk =
        (Turing.initList (tmVerifierTM V)
          (tmVerifierInstanceInputPrefixWord V x ++
            E.decodedInitialCertificateSuffixWord)).stk := by
    funext k
    by_cases hk : k = (tmVerifierTM V).k₀
    · subst k
      simpa [Turing.initList] using
        E.decodedCfg_initial_input_stack_eq_prefix_append_decoded_suffix
    · calc
        (E.decodedCfg 0 ht0).stk k = [] :=
          E.decodedCfg_initial_noninput_stack_empty k hk
        _ =
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++
              E.decodedInitialCertificateSuffixWord)).stk k := by
            simp [Turing.initList, hk]
  change
    { l := (E.controlRow 0 ht0).label
      var := (E.controlRow 0 ht0).state
      stk := (E.decodedCfg 0 ht0).stk } =
      Turing.initList (tmVerifierTM V)
        (tmVerifierInstanceInputPrefixWord V x ++ E.decodedInitialCertificateSuffixWord)
  rw [E.initialControlRow_label, E.initialControlRow_state]
  exact Turing.TM2.Cfg.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, hStacks⟩

end TMVerifierXOnlyGlobalTableauEvidence

/--
Raw accepting soundness for one direct verifier machine.

The premise says: any true-output run of the extracted machine from a raw input
word beginning with the encoded instance prefix is semantically sound for `x`.
This is stronger than the typed `TMVerifier.sound` field and is exactly the
normalization obligation needed if the suffix-validity CNF is omitted.
-/
structure TMVerifierXOnlyRawInputSound
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  accept_true_of_raw_run :
    {x : L.Instance.Carrier} →
      {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)} →
        StateTransition.EvalsToInTime (tmVerifierTM V).step
          (Turing.initList (tmVerifierTM V)
            (tmVerifierInstanceInputPrefixWord V x ++ suffix))
          (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) →
          L.isYes x

namespace TMVerifierXOnlyRawInputSound

/-- The raw-soundness route emits only the x-only global tableau CNF. -/
noncomputable def emittedCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (_R : TMVerifierXOnlyRawInputSound V)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) : CNF :=
  tmVerifierXOnlyGlobalTableauCNF V B x

theorem emittedCNF_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => R.emittedCNF B x) := by
  simpa [emittedCNF] using tmVerifierXOnlyGlobalTableauCNF_tm_polytime V B

theorem isYes_of_globalTableauCNF_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment}
    (h : CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a) :
    L.isYes x := by
  let E := tmVerifierXOnlyGlobalTableauCNF_evidence V B x a h
  have hRun :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (Turing.initList (tmVerifierTM V)
          (tmVerifierInstanceInputPrefixWord V x ++
            E.decodedInitialCertificateSuffixWord))
        (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) := by
    simpa [E.decodedCfg_initial_eq_rawInput] using E.rawOutputsTrueInTime
  exact R.accept_true_of_raw_run hRun

theorem globalTableauCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (x : L.Instance.Carrier) :
    CNF.Satisfiable
        (tmVerifierXOnlyGlobalTableauCNF V (tmVerifierActivePushPayloadBoundary V) x) ↔
      L.isYes x := by
  constructor
  · rintro ⟨a, h⟩
    exact R.isYes_of_globalTableauCNF_satisfies h
  · intro hx
    rcases tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_complete V x hx with
      ⟨a, ⟨w⟩⟩
    exact ⟨a, w.global_tableau⟩

theorem emittedCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (x : L.Instance.Carrier) :
    CNF.Satisfiable (R.emittedCNF (tmVerifierActivePushPayloadBoundary V) x) ↔
      L.isYes x := by
  simpa [emittedCNF] using R.globalTableauCNF_satisfiable_iff_isYes x

/-- The raw-sound emitted CNF converted to bundled 3CNF. -/
noncomputable def emittedThreeCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (x : L.Instance.Carrier) : ThreeCNF :=
  CNF.splitToThreeCNF (R.emittedCNF (tmVerifierActivePushPayloadBoundary V) x)

theorem emittedThreeCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (x : L.Instance.Carrier) :
    ThreeCNF.Satisfiable (R.emittedThreeCNF x) ↔ L.isYes x := by
  rw [emittedThreeCNF, CNF.splitToThreeCNF_satisfiable_iff,
    R.emittedCNF_satisfiable_iff_isYes]

theorem emittedThreeCNF_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF) :
    TMPolyTimeMap L.Instance threeSATDecisionProblem.Instance
      (fun x : L.Instance.Carrier => R.emittedThreeCNF x) := by
  have hCNF := R.emittedCNF_tm_polytime (tmVerifierActivePushPayloadBoundary V)
  have hComp := TMPolyTimeMap.comp hSplit hCNF
  simpa [Function.comp, emittedThreeCNF] using hComp

/-- Package a raw-sound verifier as one direct Cook-Levin verifier reduction. -/
noncomputable def toVerifierReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (R : TMVerifierXOnlyRawInputSound V)
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF) :
    TMCookLevinVerifierReduction V where
  cookTableauThreeCNF := R.emittedThreeCNF
  cookTableauThreeCNF_polytime := R.emittedThreeCNF_tm_polytime hSplit
  cookTableauThreeCNF_correct := by
    intro x
    exact (R.emittedThreeCNF_satisfiable_iff_isYes x).symm

/--
The raw-input route yields the standard Cook-Levin theorem from a uniform raw
soundness package and a direct TM witness for CNF splitting.
-/
noncomputable def toCookLevinTheorem
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMCookLevinTheorem where
  reduceVerifier := fun V =>
    (hRawSound V).toVerifierReduction hSplit

/--
Strict-logspace soundness plus uniform raw-input soundness gives the standard
Cook-Levin theorem through the raw-sound x-only route.
-/
noncomputable def toCookLevinTheoremOfStrictSound
    (hSound : StrictLogSpaceTMSound)
    (hRawSound :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyRawInputSound V) :
    TMCookLevinTheorem :=
  toCookLevinTheorem (splitToThreeCNF_tm_polytime_of_strictSound hSound) hRawSound

end TMVerifierXOnlyRawInputSound

end SAT
end ComplexityReduction
