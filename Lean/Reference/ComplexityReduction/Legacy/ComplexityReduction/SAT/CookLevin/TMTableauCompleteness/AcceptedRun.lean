/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.ActionTrace

namespace ComplexityReduction
namespace SAT

@[simp]
theorem tmVerifierRunCfgAt_zero
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    tmVerifierRunCfgAt V p 0 = tmVerifierInitialCfg V p := by
  simp [tmVerifierRunCfgAt]

theorem tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (h : tmVerifierOutputsBoolInTime V p true) :
    tmVerifierRunCfgAt V p (tmVerifierTimeBound V p) =
      tmVerifierOutputCfg V true := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h.steps_le_m
  have hN : tmVerifierTimeBound V p = d + h.steps := by
    simpa [Nat.add_comm] using hd
  have hSteps :
      (flip bind (tmVerifierTM V).step)^[h.steps] (some (tmVerifierInitialCfg V p)) =
        some (tmVerifierOutputCfg V true) := by
    simpa [tmVerifierOutputsBoolInTime, tmVerifierInitialCfg, tmVerifierOutputCfg] using
      h.evals_in_steps
  rw [tmVerifierRunCfgAt, hN, Function.iterate_add_apply, hSteps]
  cases d with
  | zero =>
      rfl
  | succ d =>
      have hStop : (tmVerifierTM V).step (tmVerifierOutputCfg V true) = none := by
        simp [tmVerifierOutputCfg, Turing.FinTM2.step, Turing.TM2.step, Turing.haltList]
        rfl
      have hNone :
          (flip bind (tmVerifierTM V).step)^[d.succ] (some (tmVerifierOutputCfg V true)) =
            none := by
        rw [Function.iterate_succ_apply]
        change (flip bind (tmVerifierTM V).step)^[d]
          ((tmVerifierTM V).step (tmVerifierOutputCfg V true)) = none
        rw [hStop]
        exact optionStep_iterate_none (tmVerifierTM V).step d
      rw [hNone]

theorem tmVerifierInitialControlCNF_satisfies_controlRunAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialControlCNF V)
      (tmVerifierControlRunAssignment V p) := by
  rw [tmVerifierInitialControlCNF, CNF.satisfies_append]
  constructor
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main))
      (tmVerifierControlRunAssignment V p)).2 (by
        rw [tmVerifierLabelAtom_eval_controlRunAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)
      (tmVerifierControlRunAssignment V p)).2 (by
        rw [tmVerifierStateAtom_eval_controlRunAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])

theorem tmVerifierHaltingControlCNFAt_satisfies_controlRunAssignment_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (h : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V p))
      (tmVerifierControlRunAssignment V p) := by
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none)
    (tmVerifierControlRunAssignment V p)).2 (by
      rw [tmVerifierLabelAtom_eval_controlRunAssignment_iff]
      rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p h]
      simp [tmVerifierOutputCfg, Turing.haltList])

theorem tmVerifierEndpointStateCNF_satisfies_controlRunAssignment_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (h : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies
      (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V p)
        (tmVerifierTM V).initialState))
      (tmVerifierControlRunAssignment V p) := by
  exact (tmVerifierUnitCNF_satisfies
    (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState)
    (tmVerifierControlRunAssignment V p)).2 (by
      rw [tmVerifierStateAtom_eval_controlRunAssignment_iff]
      rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p h]
      simp [tmVerifierOutputCfg, Turing.haltList])

theorem tmVerifierInitialControlCNF_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialControlCNF V)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierInitialControlCNF, CNF.satisfies_append]
  constructor
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main))
      (tmVerifierControlBoundaryAssignment V p)).2 (by
        rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)
      (tmVerifierControlBoundaryAssignment V p)).2 (by
        rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])

theorem tmVerifierEndpointCNF_satisfies_controlBoundaryAssignment_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (h : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierEndpointCNF V p)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierEndpointCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none)
        (tmVerifierControlBoundaryAssignment V p)).2 (by
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p h]
          simp [tmVerifierOutputCfg, Turing.haltList])
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState)
        (tmVerifierControlBoundaryAssignment V p)).2 (by
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p h]
          simp [tmVerifierOutputCfg, Turing.haltList])
  · exact tmVerifierOutputTrueCNFAt_satisfies_controlBoundaryAssignment V p
      (tmVerifierTimeBound V p)

theorem tmVerifierFixedPairBoundaryCNF_satisfies_controlBoundaryAssignment_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (h : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierFixedPairBoundaryCNF V p)
      (tmVerifierControlBoundaryAssignment V p) := by
  rw [tmVerifierFixedPairBoundaryCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact
      ⟨tmVerifierInitialControlCNF_satisfies_controlBoundaryAssignment V p,
        tmVerifierInitialStackCNF_satisfies_controlBoundaryAssignment V p⟩
  · exact tmVerifierEndpointCNF_satisfies_controlBoundaryAssignment_of_outputs_true V p h

namespace TMVerifierAcceptedRun

noncomputable def controlRunAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierControlRunAssignment V (x, c)

noncomputable def controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierControlBoundaryAssignment V (x, c)

noncomputable def emptyStackAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierControlEmptyStackAssignment V (x, c)

noncomputable def initialInputStackAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierInitialInputStackAssignment V (x, c)

noncomputable def endpointOutputStackAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) : Assignment :=
  tmVerifierEndpointOutputStackAssignment V (x, c)

noncomputable def runStackAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (_run : TMVerifierAcceptedRun V x c) (t : Nat) : Assignment :=
  tmVerifierRunStackAssignment V (x, c) t

theorem controlDomainRows_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V (x, c))
      run.controlRunAssignment := by
  simpa [controlRunAssignment] using
    tmVerifierControlDomainRowsCNF_satisfies_controlRunAssignment V (x, c)

theorem initialControl_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierInitialControlCNF V) run.controlRunAssignment := by
  simpa [controlRunAssignment] using
    tmVerifierInitialControlCNF_satisfies_controlRunAssignment V (x, c)

theorem endpointHaltingControl_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierHaltingControlCNFAt V (tmVerifierTimeBound V (x, c)))
      run.controlRunAssignment := by
  simpa [controlRunAssignment] using
    tmVerifierHaltingControlCNFAt_satisfies_controlRunAssignment_of_outputs_true V (x, c)
      run.output_true

theorem endpointState_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies
      (tmVerifierUnitCNF (tmVerifierStateAtom V (tmVerifierTimeBound V (x, c))
        (tmVerifierTM V).initialState))
      run.controlRunAssignment := by
  simpa [controlRunAssignment] using
    tmVerifierEndpointStateCNF_satisfies_controlRunAssignment_of_outputs_true V (x, c)
      run.output_true

theorem boundaryCNF_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierFixedPairBoundaryCNF V (x, c))
      run.controlBoundaryAssignment := by
  simpa [controlBoundaryAssignment] using
    tmVerifierFixedPairBoundaryCNF_satisfies_controlBoundaryAssignment_of_outputs_true V
      (x, c) run.output_true

theorem controlDomainRows_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V (x, c))
      run.controlBoundaryAssignment := by
  simpa [controlBoundaryAssignment] using
    tmVerifierControlDomainRowsCNF_satisfies_controlBoundaryAssignment V (x, c)

theorem controlDomainRows_satisfies_emptyStackAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V (x, c))
      run.emptyStackAssignment := by
  simpa [emptyStackAssignment] using
    tmVerifierControlDomainRowsCNF_satisfies_controlEmptyStackAssignment V (x, c)

theorem emptyStackWellFormedAt_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) (t : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V (x, c) t)
      run.emptyStackAssignment := by
  simpa [emptyStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_controlEmptyStackAssignment V (x, c) t

theorem initialInputStackWellFormedAt_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) (t : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V (x, c) t)
      run.initialInputStackAssignment := by
  simpa [initialInputStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_initialInputStackAssignment V (x, c) t

theorem endpointOutputStackWellFormedAt_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) (t : Nat) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V (x, c) t)
      run.endpointOutputStackAssignment := by
  simpa [endpointOutputStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_endpointOutputStackAssignment V (x, c) t

theorem runStackWellFormedAt_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) {t : Nat}
    (ht : t ≤ tmVerifierTimeBound V (x, c)) :
    CNF.Satisfies (tmVerifierAllStackWellFormedCNFAt V (x, c) t)
      (run.runStackAssignment t) := by
  simpa [runStackAssignment] using
    tmVerifierAllStackWellFormedCNFAt_satisfies_runStackAssignment V (x, c) ht

theorem initialStack_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierInitialStackCNF V (x, c))
      run.controlBoundaryAssignment := by
  simpa [controlBoundaryAssignment] using
    tmVerifierInitialStackCNF_satisfies_controlBoundaryAssignment V (x, c)

theorem endpointOutputTrue_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V (x, c)
      (tmVerifierTimeBound V (x, c))) run.controlBoundaryAssignment := by
  simpa [controlBoundaryAssignment] using
    tmVerifierOutputTrueCNFAt_satisfies_controlBoundaryAssignment V (x, c)
      (tmVerifierTimeBound V (x, c))

theorem instancePrefix_satisfies_controlBoundaryAssignment
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x)
      run.controlBoundaryAssignment :=
  tmVerifierInitialStackCNF_satisfies_instancePrefix V x c run.controlBoundaryAssignment
    run.initialStack_satisfies_controlBoundaryAssignment

end TMVerifierAcceptedRun

end SAT
end ComplexityReduction
