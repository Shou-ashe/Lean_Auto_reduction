/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalAcceptedRows

/-!
Accepted-run satisfaction for the aggregate global fixed-pair tableau.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierControlDomainCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    CNF.Satisfies (tmVerifierControlDomainCNFAt V t)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  rw [tmVerifierControlDomainCNFAt, CNF.satisfies_append]
  constructor
  · let selected := (tmVerifierRunCfgAt V p t).l
    apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
    · exact tmVerifierLabelAtomsAt_nodup V t
    · exact ⟨tmVerifierLabelAtom V t selected, tmVerifierLabelAtomsAt_mem V t selected, by
        rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
    · intro x hx y hy hxTrue hyTrue
      rcases List.mem_map.mp hx with ⟨label₁, _hlabel₁, rfl⟩
      rcases List.mem_map.mp hy with ⟨label₂, _hlabel₂, rfl⟩
      have h₁ :
          label₁ = (tmVerifierRunCfgAt V p t).l := by
        have hBoundary :
            (tmVerifierLabelAtom V t label₁).eval
                (tmVerifierControlBoundaryAssignment V p) = true := by
          rw [← tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          exact hxTrue
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₁).1
          hBoundary
      have h₂ :
          label₂ = (tmVerifierRunCfgAt V p t).l := by
        have hBoundary :
            (tmVerifierLabelAtom V t label₂).eval
                (tmVerifierControlBoundaryAssignment V p) = true := by
          rw [← tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          exact hyTrue
        exact (tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff V p t label₂).1
          hBoundary
      subst label₁
      subst label₂
      rfl
  · let selected := (tmVerifierRunCfgAt V p t).var
    apply CookLevin.exactlyOneCNF_satisfies_of_exists_unique
    · exact tmVerifierStateAtomsAt_nodup V t
    · exact ⟨tmVerifierStateAtom V t selected, tmVerifierStateAtomsAt_mem V t selected, by
        rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t selected).2 rfl⟩
    · intro x hx y hy hxTrue hyTrue
      rcases List.mem_map.mp hx with ⟨state₁, _hstate₁, rfl⟩
      rcases List.mem_map.mp hy with ⟨state₂, _hstate₂, rfl⟩
      have h₁ :
          state₁ = (tmVerifierRunCfgAt V p t).var := by
        have hBoundary :
            (tmVerifierStateAtom V t state₁).eval
                (tmVerifierControlBoundaryAssignment V p) = true := by
          rw [← tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          exact hxTrue
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₁).1
          hBoundary
      have h₂ :
          state₂ = (tmVerifierRunCfgAt V p t).var := by
        have hBoundary :
            (tmVerifierStateAtom V t state₂).eval
                (tmVerifierControlBoundaryAssignment V p) = true := by
          rw [← tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          exact hyTrue
        exact (tmVerifierStateAtom_eval_controlBoundaryAssignment_iff V p t state₂).1
          hBoundary
      subst state₁
      subst state₂
      rfl

theorem tmVerifierControlDomainRowsCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierControlDomainRowsCNF V p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierControlDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, _ht, hc⟩
  exact tmVerifierControlDomainCNFAt_satisfies_acceptedRunGlobalStacks V p t c hc

theorem tmVerifierInitialControlCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialControlCNF V)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  rw [tmVerifierInitialControlCNF, CNF.satisfies_append]
  constructor
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main))
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))).2
      (by
        rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])
  · exact (tmVerifierUnitCNF_satisfies
      (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))).2
      (by
        rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
        simp [tmVerifierInitialCfg, Turing.initList])

theorem tmVerifierInitialStackCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierInitialStackCNF V p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  rw [tmVerifierInitialStackCNF_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierInputStackSymbolLiterals] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, hentry, rfl⟩
      have hZip := List.mem_zipIdx hentry
      have hEntryLt : entry.2 < (tmVerifierInputWord V p).length := by
        simpa using hZip.2.1
      have hEntryEq : entry.1 = (tmVerifierInputWord V p)[entry.2] := by
        simpa using hZip.2.2
      have hStack0 :
          tmVerifierAcceptedRunGlobalStacks V p 0 (tmVerifierTM V).k₀ =
            tmVerifierInputWord V p := by
        rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega)]
        simp [tmVerifierInitialCfg, Turing.initList]
      have hcell : entry.2 < (tmVerifierAcceptedRunGlobalStacks V p 0
          (tmVerifierTM V).k₀).length := by
        simpa [hStack0] using hEntryLt
      have hsym :
          ((tmVerifierAcceptedRunGlobalStacks V p 0 (tmVerifierTM V).k₀)[entry.2]'hcell) =
            entry.1 := by
        have hget :
            (tmVerifierAcceptedRunGlobalStacks V p 0 (tmVerifierTM V).k₀)[entry.2]'hcell =
              (tmVerifierInputWord V p)[entry.2] := by
          simp [hStack0]
        simpa [hEntryEq] using hget
      simpa [tmVerifierInputStackSymbolAtom, hsym] using
        tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V p
          (tmVerifierAcceptedRunGlobalStacks V p) 0 (tmVerifierTM V).k₀ hcell
    · rw [tmVerifierInputStackEmptyTailLiterals] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, hcell, rfl⟩
      have hlen : (tmVerifierAcceptedRunGlobalStacks V p 0 (tmVerifierTM V).k₀).length ≤
          cell := by
        have hStack0 :
            tmVerifierAcceptedRunGlobalStacks V p 0 (tmVerifierTM V).k₀ =
              tmVerifierInputWord V p := by
          rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega)]
          simp [tmVerifierInitialCfg, Turing.initList]
        have hTailInfo :
            cell ∈ tmVerifierCellRange V p ∧ (tmVerifierInputWord V p).length ≤ cell := by
          simpa [tmVerifierTailCells] using hcell
        simpa [hStack0] using hTailInfo.2
      exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p
        (tmVerifierAcceptedRunGlobalStacks V p) (u := 0) (j := (tmVerifierTM V).k₀)
        (cell := cell) (by omega)
  · intro l hl
    rw [tmVerifierInitialNonInputEmptyLiterals] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    have hkNe : k ≠ (tmVerifierTM V).k₀ := by
      simpa [tmVerifierNonInputStacks] using hk
    have hlen : (tmVerifierAcceptedRunGlobalStacks V p 0 k).length = 0 := by
      rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega)]
      simp [tmVerifierInitialCfg_noninput_stack_empty V p k hkNe]
    exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p
      (tmVerifierAcceptedRunGlobalStacks V p) (u := 0) (j := k) (cell := cell)
      (by omega)

theorem tmVerifierStackWellFormedRowsCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierStackWellFormedRowsCNF V p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierStackWellFormedRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, ht, hc⟩
  have htLe : t ≤ tmVerifierTimeBound V p := by
    simpa [tmVerifierTableauTimeRange, List.mem_range] using ht
  have hActive :
      tmVerifierStacksActive V (tmVerifierAcceptedRunGlobalStacks V p t) := by
    rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p htLe]
    exact tmVerifierRunCfgAt_stacksActive V p t
  have hlen :
      ∀ k : tmVerifierStackIndex V,
        (tmVerifierAcceptedRunGlobalStacks V p t k).length ≤ tmVerifierCellBound V p := by
    intro k
    rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p htLe]
    exact tmVerifierRunCfgAt_stack_length_le_cellBound V p htLe k
  exact tmVerifierAllStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p
    (tmVerifierAcceptedRunGlobalStacks V p) t hActive hlen c hc

theorem tmVerifierOutputTrueCNFAt_satisfies_acceptedRunGlobalStacks_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierOutputTrueCNFAt V p (tmVerifierTimeBound V p))
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  rw [tmVerifierOutputTrueCNFAt_satisfies]
  constructor
  · intro l hl
    rw [List.mem_append] at hl
    rcases hl with hSymbol | hTail
    · rw [tmVerifierOutputTrueSymbolLiteralsAt] at hSymbol
      rcases List.mem_map.mp hSymbol with ⟨entry, hentry, rfl⟩
      have hZip := List.mem_zipIdx hentry
      have hEntryLt : entry.2 < (tmVerifierBoolOutputWord V true).length := by
        simpa using hZip.2.1
      have hEntryEq : entry.1 = (tmVerifierBoolOutputWord V true)[entry.2] := by
        simpa using hZip.2.2
      have hcfg := tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p hOut
      have hStackEnd :
          tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p)
              (tmVerifierTM V).k₁ =
            tmVerifierBoolOutputWord V true := by
        rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega), hcfg]
        simp [tmVerifierOutputCfg, Turing.haltList]
      have hcell : entry.2 < (tmVerifierAcceptedRunGlobalStacks V p
          (tmVerifierTimeBound V p) (tmVerifierTM V).k₁).length := by
        simpa [hStackEnd] using hEntryLt
      have hsym :
          ((tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p)
              (tmVerifierTM V).k₁)[entry.2]'hcell) = entry.1 := by
        have hget :
            (tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p)
                (tmVerifierTM V).k₁)[entry.2]'hcell =
              (tmVerifierBoolOutputWord V true)[entry.2] := by
          simp [hStackEnd]
        simpa [hEntryEq] using hget
      simpa [tmVerifierOutputStackSymbolAtom, hsym] using
        tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V p
          (tmVerifierAcceptedRunGlobalStacks V p) (tmVerifierTimeBound V p)
          (tmVerifierTM V).k₁ hcell
    · rw [tmVerifierOutputTrueEmptyTailLiteralsAt] at hTail
      rcases List.mem_map.mp hTail with ⟨cell, hcell, rfl⟩
      have hcfg := tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p hOut
      have hlen :
          (tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p)
              (tmVerifierTM V).k₁).length ≤ cell := by
        have hStackEnd :
            tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p)
                (tmVerifierTM V).k₁ =
              tmVerifierBoolOutputWord V true := by
          rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega), hcfg]
          simp [tmVerifierOutputCfg, Turing.haltList]
        have hTailInfo :
            cell ∈ tmVerifierCellRange V p ∧
              (tmVerifierBoolOutputWord V true).length ≤ cell := by
          simpa [tmVerifierTailCells] using hcell
        simpa [hStackEnd] using hTailInfo.2
      exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p
        (tmVerifierAcceptedRunGlobalStacks V p) (u := tmVerifierTimeBound V p)
        (j := (tmVerifierTM V).k₁) (cell := cell) (by omega)
  · intro l hl
    rw [tmVerifierOutputTrueNonOutputEmptyLiteralsAt] at hl
    rcases List.mem_flatMap.mp hl with ⟨k, hk, hcellLit⟩
    rcases List.mem_map.mp hcellLit with ⟨cell, _hcell, rfl⟩
    have hkNe : k ≠ (tmVerifierTM V).k₁ := by
      simpa [tmVerifierNonOutputStacks] using hk
    have hcfg := tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p hOut
    have hlen :
        (tmVerifierAcceptedRunGlobalStacks V p (tmVerifierTimeBound V p) k).length = 0 := by
      rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (by omega), hcfg]
      simp [tmVerifierOutputCfg_nonoutput_stack_empty V true k hkNe]
    exact tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p
      (tmVerifierAcceptedRunGlobalStacks V p) (u := tmVerifierTimeBound V p) (j := k)
      (cell := cell) (by omega)

theorem tmVerifierEndpointCNF_satisfies_acceptedRunGlobalStacks_of_outputs_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierEndpointCNF V p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  rw [tmVerifierEndpointCNF, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierLabelAtom V (tmVerifierTimeBound V p) none)
        (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))).2
        (by
          rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p hOut]
          simp [tmVerifierOutputCfg, Turing.haltList])
    · exact (tmVerifierUnitCNF_satisfies
        (tmVerifierStateAtom V (tmVerifierTimeBound V p) (tmVerifierTM V).initialState)
        (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))).2
        (by
          rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          rw [tmVerifierRunCfgAt_timeBound_of_outputs_true_in_time V p hOut]
          simp [tmVerifierOutputCfg, Turing.haltList])
  · exact tmVerifierOutputTrueCNFAt_satisfies_acceptedRunGlobalStacks_of_outputs_true V p hOut

theorem tmVerifierGlobalTableauCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V p true) :
    CNF.Satisfies (tmVerifierGlobalTableauCNF V
        (tmVerifierActivePushPayloadBoundary V) p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierGlobalTableauCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨block, hblock, hc⟩
  rw [tmVerifierGlobalTableauBlocks] at hblock
  simp only [List.mem_cons, List.not_mem_nil] at hblock
  rcases hblock with hblock | hblock | hblock | hblock | hblock | hblock | hblock
  · subst block
    exact tmVerifierControlDomainRowsCNF_satisfies_acceptedRunGlobalStacks V p c hc
  · subst block
    exact tmVerifierInitialControlCNF_satisfies_acceptedRunGlobalStacks V p c hc
  · subst block
    exact tmVerifierInitialStackCNF_satisfies_acceptedRunGlobalStacks V p c hc
  · subst block
    exact tmVerifierStackWellFormedRowsCNF_satisfies_acceptedRunGlobalStacks V p c hc
  · subst block
    exact tmVerifierTransitionFixedMicroDomainRowsCNF_satisfies_acceptedRunGlobalStacks V p
      c hc
  · subst block
    exact tmVerifierTransitionFixedRowsCNF_satisfies_acceptedRunGlobalStacks V p hOut c hc
  · rcases hblock with hblock | hfalse
    · subst block
      exact tmVerifierEndpointCNF_satisfies_acceptedRunGlobalStacks_of_outputs_true V p hOut
        c hc
    · cases hfalse

theorem TMVerifierAcceptedRun.globalTableau_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c) :
    CNF.Satisfies (tmVerifierGlobalTableauCNF V
        (tmVerifierActivePushPayloadBoundary V) (x, c))
      (tmVerifierStackFamilyAssignment V (x, c)
        (tmVerifierAcceptedRunGlobalStacks V (x, c))) :=
  tmVerifierGlobalTableauCNF_satisfies_acceptedRunGlobalStacks V (x, c) run.output_true

noncomputable def TMVerifierAcceptedRun.toXOnlyGlobalTableauSeed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {c : V.Cert.Carrier}
    (run : TMVerifierAcceptedRun V x c)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    TMVerifierXOnlyGlobalTableauSeed V (tmVerifierActivePushPayloadBoundary V) x
      (tmVerifierStackFamilyAssignment V (x, c)
        (tmVerifierAcceptedRunGlobalStacks V (x, c))) where
  cert := c
  cert_size := hSize
  global_tableau := run.globalTableau_satisfies

/--
Verifier-level completeness for the global x-only tableau seed: every yes
instance has a bounded accepting certificate whose accepted run satisfies the
aggregate global tableau CNF.
-/
theorem tmVerifierXOnlyGlobalTableauSeed_satisfiable_complete
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    L.isYes x →
      ∃ a, Nonempty
        (TMVerifierXOnlyGlobalTableauSeed V (tmVerifierActivePushPayloadBoundary V) x a) := by
  intro hx
  rcases (TMVerifierBoundedAcceptingCertificate.nonempty_iff_isYes V x).2 hx with ⟨w⟩
  let run := w.acceptedRun
  let a := tmVerifierStackFamilyAssignment V (x, w.cert)
    (tmVerifierAcceptedRunGlobalStacks V (x, w.cert))
  exact ⟨a, ⟨run.toXOnlyGlobalTableauSeed w.cert_size⟩⟩

end SAT
end ComplexityReduction
