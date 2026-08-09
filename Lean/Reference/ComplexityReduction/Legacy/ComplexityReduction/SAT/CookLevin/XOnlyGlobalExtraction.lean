/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyIOStacks
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauControlUniqueness

/-!
Decoded macro configurations for x-only global Cook-Levin tableau evidence.

This file turns `TMVerifierXOnlyGlobalTableauEvidence` into concrete TM2
configurations using the x-only stack decoder.  The initial row facts remain
raw prefix/empty-stack facts: no arbitrary input-stack suffix is interpreted as
a typed verifier certificate here.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only time-range bookkeeping -/

theorem tmVerifierXOnlyTableauTimeRange_zero_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    0 ∈ tmVerifierXOnlyTableauTimeRange V x :=
  tmVerifierXOnlyTableauTimeRange_mem_of_le V x (Nat.zero_le _)

theorem tmVerifierXOnlyTableauTimeRange_timeBound_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    tmVerifierXOnlyTimeBound V x ∈ tmVerifierXOnlyTableauTimeRange V x :=
  tmVerifierXOnlyTableauTimeRange_mem_of_le V x le_rfl

theorem tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) {t : Nat}
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    t ∈ tmVerifierXOnlyTableauTimeRange V x := by
  rw [tmVerifierXOnlyTransitionTimeRange, List.mem_range] at ht
  exact tmVerifierXOnlyTableauTimeRange_mem_of_le V x (Nat.le_of_lt ht)

theorem tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) {t : Nat}
    (ht : t ∈ tmVerifierXOnlyTransitionTimeRange V x) :
    t + 1 ∈ tmVerifierXOnlyTableauTimeRange V x := by
  rw [tmVerifierXOnlyTransitionTimeRange, List.mem_range] at ht
  exact tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by omega)

namespace TMVerifierXOnlyGlobalTableauEvidence

/-- The decoded TM2 configuration represented by one macro row of an x-only tableau. -/
noncomputable def decodedCfg
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (t : Nat) (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x) : (tmVerifierTM V).Cfg where
  l := (E.controlRow t ht).label
  var := (E.controlRow t ht).state
  stk := fun k => tmVerifierXOnlyDecodedStackList V x t k a (E.stackCellDomainsAt t ht k)

theorem decodedCfg_proof_irrel
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t : Nat} (ht ht' : t ∈ tmVerifierXOnlyTableauTimeRange V x) :
    E.decodedCfg t ht = E.decodedCfg t ht' := by
  have hproof : ht = ht' := Subsingleton.elim ht ht'
  cases hproof
  rfl

theorem decodedCfg_eq_of_time_eq
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {t u : Nat} (ht : t ∈ tmVerifierXOnlyTableauTimeRange V x)
    (hu : u ∈ tmVerifierXOnlyTableauTimeRange V x) (htu : t = u) :
    E.decodedCfg t ht = E.decodedCfg u hu := by
  subst u
  exact E.decodedCfg_proof_irrel _ _

theorem initialControlRow_label
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (E.controlRow 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).label =
      some (tmVerifierTM V).main := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).label_true E.initial_label

theorem initialControlRow_state
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (E.controlRow 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).state =
      (tmVerifierTM V).initialState := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).state_true E.initial_state

theorem endpointControlRow_label
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (E.controlRow (tmVerifierXOnlyTimeBound V x)
      (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x)).label = none := by
  let htEnd := tmVerifierXOnlyTableauTimeRange_timeBound_mem V x
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V
    (tmVerifierXOnlyTimeBound V x) a
    (E.controlDomainRow (tmVerifierXOnlyTimeBound V x) htEnd)
    (E.controlRow (tmVerifierXOnlyTimeBound V x) htEnd).label_true E.endpoint_halted

theorem endpointControlRow_state
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (E.controlRow (tmVerifierXOnlyTimeBound V x)
      (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x)).state =
      (tmVerifierTM V).initialState := by
  let htEnd := tmVerifierXOnlyTableauTimeRange_timeBound_mem V x
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V
    (tmVerifierXOnlyTimeBound V x) a
    (E.controlDomainRow (tmVerifierXOnlyTimeBound V x) htEnd)
    (E.controlRow (tmVerifierXOnlyTimeBound V x) htEnd).state_true E.endpoint_state

theorem initialInputChoicePrefix_symbol
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat} (hi : i < (tmVerifierInstanceInputPrefixWord V x).length) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a
      (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
        (tmVerifierTM V).k₀))[i]? =
      some
        (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            (tmVerifierInstanceInputPrefixWord V x)[i])
          (tmVerifierInstanceInputPrefixWord V x)[i]) :=
  tmVerifierXOnlyDecodedInputStackChoicePrefix_prefix_symbol V x a E.initial_stack
    (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
      (tmVerifierTM V).k₀) hi

theorem initialInputChoicePrefix_empty_at_inputBound
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    ((tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a
      (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
        (tmVerifierTM V).k₀))[tmVerifierXOnlyInputLengthBound V x]?) =
      some (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
  tmVerifierXOnlyDecodedInputStackChoicePrefix_empty_at_inputBound V x a E.initial_stack
    (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
      (tmVerifierTM V).k₀)

theorem decodedCfg_initial_noninput_stack_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (k : tmVerifierStackIndex V) (hk : k ≠ (tmVerifierTM V).k₀) :
    (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk k = [] := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  simpa [decodedCfg] using
    tmVerifierXOnlyDecodedStackList_initial_noninput_eq V x a E.initial_stack k hk
      (E.stackCellDomainsAt 0 ht0 k)

theorem decodedCfg_endpoint_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    E.decodedCfg (tmVerifierXOnlyTimeBound V x)
        (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x) =
      tmVerifierOutputCfg V true := by
  let htEnd := tmVerifierXOnlyTableauTimeRange_timeBound_mem V x
  let tEnd := tmVerifierXOnlyTimeBound V x
  have hStacks :
      (fun k => tmVerifierXOnlyDecodedStackList V x tEnd k a
          (E.stackCellDomainsAt tEnd htEnd k)) =
        (tmVerifierOutputCfg V true).stk := by
    funext k
    by_cases hk : k = (tmVerifierTM V).k₁
    · subst k
      simpa [tmVerifierOutputCfg_output_stack] using
        tmVerifierXOnlyDecodedStackList_output_true_eq V x tEnd a E.endpoint_output_true
          (E.stackCellDomainsAt tEnd htEnd (tmVerifierTM V).k₁)
    · simpa [tmVerifierOutputCfg_nonoutput_stack_empty V true k hk] using
        tmVerifierXOnlyDecodedStackList_output_true_nonoutput_eq V x tEnd a
          E.endpoint_output_true k hk (E.stackCellDomainsAt tEnd htEnd k)
  change
    { l := (E.controlRow tEnd htEnd).label
      var := (E.controlRow tEnd htEnd).state
      stk := fun k => tmVerifierXOnlyDecodedStackList V x tEnd k a
        (E.stackCellDomainsAt tEnd htEnd k) } =
      tmVerifierOutputCfg V true
  rw [E.endpointControlRow_label, E.endpointControlRow_state]
  exact Turing.TM2.Cfg.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, hStacks⟩

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
