/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauExtraction

/-!
Uniqueness alignment for decoded aggregate-tableau control rows.

The extraction layer gives a true label atom and a true state atom for each
satisfied control-domain row.  This file uses the at-most-one half of those
rows to align decoded rows with the fixed initial and endpoint unit clauses.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierLabelAtomsAt_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    tmVerifierLabelAtom V t label ∈ tmVerifierLabelAtomsAt V t := by
  simp [tmVerifierLabelAtomsAt]

theorem tmVerifierStateAtomsAt_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) (state : (tmVerifierTM V).σ) :
    tmVerifierStateAtom V t state ∈ tmVerifierStateAtomsAt V t := by
  simp [tmVerifierStateAtomsAt]

theorem tmVerifierLabelAtom_injective {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) :
    Function.Injective (fun label : Option (tmVerifierTM V).Λ =>
      tmVerifierLabelAtom V t label) := by
  intro label₁ label₂ h
  cases label₁ with
  | none =>
      cases label₂ with
      | none => rfl
      | some q =>
          simp [tmVerifierLabelAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
            tmVerifierLabelCode, TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] at h
  | some q₁ =>
      cases label₂ with
      | none =>
          simp [tmVerifierLabelAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
            tmVerifierLabelCode, TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] at h
      | some q₂ =>
          letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
          have hPayload :
              tmVerifierLabelCode V (some q₁) = tmVerifierLabelCode V (some q₂) := by
            simpa [tmVerifierLabelAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
              TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] using congrArg Literal.var h
          have hVal :
              ((Fintype.equivFin (tmVerifierTM V).Λ) q₁).val =
                ((Fintype.equivFin (tmVerifierTM V).Λ) q₂).val := by
            exact Nat.succ.inj (by simpa [tmVerifierLabelCode] using hPayload)
          have hFin :
              (Fintype.equivFin (tmVerifierTM V).Λ) q₁ =
                (Fintype.equivFin (tmVerifierTM V).Λ) q₂ := Fin.ext hVal
          exact congrArg some ((Fintype.equivFin (tmVerifierTM V).Λ).injective hFin)

theorem tmVerifierStateAtom_injective {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) :
    Function.Injective (fun state : (tmVerifierTM V).σ => tmVerifierStateAtom V t state) := by
  intro state₁ state₂ h
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  have hPayload :
      tmVerifierStateCode V state₁ = tmVerifierStateCode V state₂ := by
    simpa [tmVerifierStateAtom, tmVerifierTableauAtom, tmVerifierTableauVar,
      TMVerifierTableauVarKind.tag, Nat.pair_eq_pair] using congrArg Literal.var h
  have hVal :
      ((Fintype.equivFin (tmVerifierTM V).σ) state₁).val =
        ((Fintype.equivFin (tmVerifierTM V).σ) state₂).val := by
    simpa [tmVerifierStateCode] using hPayload
  have hFin :
      (Fintype.equivFin (tmVerifierTM V).σ) state₁ =
        (Fintype.equivFin (tmVerifierTM V).σ) state₂ := Fin.ext hVal
  exact (Fintype.equivFin (tmVerifierTM V).σ).injective hFin

theorem tmVerifierExactlyOneLabelCNFAt_satisfies_label_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierExactlyOneLabelCNFAt V t) a)
    {label₁ label₂ : Option (tmVerifierTM V).Λ}
    (h₁ : (tmVerifierLabelAtom V t label₁).eval a = true)
    (h₂ : (tmVerifierLabelAtom V t label₂).eval a = true) :
    label₁ = label₂ := by
  let atoms := tmVerifierLabelAtomsAt V t
  have hsplit :
      CNF.Satisfies (CookLevin.atLeastOneCNF atoms) a ∧
        CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    simpa [tmVerifierExactlyOneLabelCNFAt, CookLevin.exactlyOneCNF, atoms]
      using (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
        (CookLevin.atMostOneCNF atoms) a).1 h
  have hLit :
      tmVerifierLabelAtom V t label₁ = tmVerifierLabelAtom V t label₂ :=
    CookLevin.atMostOneCNF_satisfies_eq_of_mem_eval atoms a hsplit.2
      (by simpa [atoms] using tmVerifierLabelAtomsAt_mem V t label₁)
      (by simpa [atoms] using tmVerifierLabelAtomsAt_mem V t label₂) h₁ h₂
  exact tmVerifierLabelAtom_injective V t hLit

theorem tmVerifierExactlyOneStateCNFAt_satisfies_state_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierExactlyOneStateCNFAt V t) a)
    {state₁ state₂ : (tmVerifierTM V).σ}
    (h₁ : (tmVerifierStateAtom V t state₁).eval a = true)
    (h₂ : (tmVerifierStateAtom V t state₂).eval a = true) :
    state₁ = state₂ := by
  let atoms := tmVerifierStateAtomsAt V t
  have hsplit :
      CNF.Satisfies (CookLevin.atLeastOneCNF atoms) a ∧
        CNF.Satisfies (CookLevin.atMostOneCNF atoms) a := by
    simpa [tmVerifierExactlyOneStateCNFAt, CookLevin.exactlyOneCNF, atoms]
      using (CNF.satisfies_append (CookLevin.atLeastOneCNF atoms)
        (CookLevin.atMostOneCNF atoms) a).1 h
  have hLit :
      tmVerifierStateAtom V t state₁ = tmVerifierStateAtom V t state₂ :=
    CookLevin.atMostOneCNF_satisfies_eq_of_mem_eval atoms a hsplit.2
      (by simpa [atoms] using tmVerifierStateAtomsAt_mem V t state₁)
      (by simpa [atoms] using tmVerifierStateAtomsAt_mem V t state₂) h₁ h₂
  exact tmVerifierStateAtom_injective V t hLit

theorem tmVerifierControlDomainCNFAt_satisfies_label_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a)
    {label₁ label₂ : Option (tmVerifierTM V).Λ}
    (h₁ : (tmVerifierLabelAtom V t label₁).eval a = true)
    (h₂ : (tmVerifierLabelAtom V t label₂).eval a = true) :
    label₁ = label₂ := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierExactlyOneLabelCNFAt V t)
    (tmVerifierExactlyOneStateCNFAt V t) a).1
      (by simpa [tmVerifierControlDomainCNFAt] using h)
  exact tmVerifierExactlyOneLabelCNFAt_satisfies_label_eq V t a hsplit.1 h₁ h₂

theorem tmVerifierControlDomainCNFAt_satisfies_state_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierControlDomainCNFAt V t) a)
    {state₁ state₂ : (tmVerifierTM V).σ}
    (h₁ : (tmVerifierStateAtom V t state₁).eval a = true)
    (h₂ : (tmVerifierStateAtom V t state₂).eval a = true) :
    state₁ = state₂ := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierExactlyOneLabelCNFAt V t)
    (tmVerifierExactlyOneStateCNFAt V t) a).1
      (by simpa [tmVerifierControlDomainCNFAt] using h)
  exact tmVerifierExactlyOneStateCNFAt_satisfies_state_eq V t a hsplit.2 h₁ h₂

theorem tmVerifierTableauTimeRange_zero_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) :
    0 ∈ tmVerifierTableauTimeRange V p := by
  simp [tmVerifierTableauTimeRange]

theorem tmVerifierTableauTimeRange_timeBound_mem {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) :
    tmVerifierTimeBound V p ∈ tmVerifierTableauTimeRange V p := by
  simp [tmVerifierTableauTimeRange]

namespace TMVerifierFixedPairTableauEvidence

theorem initialControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
    (E.controlRow 0 (tmVerifierTableauTimeRange_zero_mem V p)).label =
      some (tmVerifierTM V).main := by
  let ht0 := tmVerifierTableauTimeRange_zero_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).label_true E.initial_label

theorem initialControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
    (E.controlRow 0 (tmVerifierTableauTimeRange_zero_mem V p)).state =
      (tmVerifierTM V).initialState := by
  let ht0 := tmVerifierTableauTimeRange_zero_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V 0 a
    (E.controlDomainRow 0 ht0)
    (E.controlRow 0 ht0).state_true E.initial_state

theorem endpointControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
    (E.controlRow (tmVerifierTimeBound V p)
      (tmVerifierTableauTimeRange_timeBound_mem V p)).label = none := by
  let htEnd := tmVerifierTableauTimeRange_timeBound_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_label_eq V (tmVerifierTimeBound V p) a
    (E.controlDomainRow (tmVerifierTimeBound V p) htEnd)
    (E.controlRow (tmVerifierTimeBound V p) htEnd).label_true E.endpoint_halted

theorem endpointControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a) :
    (E.controlRow (tmVerifierTimeBound V p)
      (tmVerifierTableauTimeRange_timeBound_mem V p)).state =
      (tmVerifierTM V).initialState := by
  let htEnd := tmVerifierTableauTimeRange_timeBound_mem V p
  exact tmVerifierControlDomainCNFAt_satisfies_state_eq V (tmVerifierTimeBound V p) a
    (E.controlDomainRow (tmVerifierTimeBound V p) htEnd)
    (E.controlRow (tmVerifierTimeBound V p) htEnd).state_true E.endpoint_state

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

theorem initialControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (w.fixedPairEvidence.controlRow 0
      (tmVerifierTableauTimeRange_zero_mem V (x, w.cert))).label =
      some (tmVerifierTM V).main :=
  w.fixedPairEvidence.initialControlRow_label

theorem initialControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (w.fixedPairEvidence.controlRow 0
      (tmVerifierTableauTimeRange_zero_mem V (x, w.cert))).state =
      (tmVerifierTM V).initialState :=
  w.fixedPairEvidence.initialControlRow_state

theorem endpointControlRow_label {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (w.fixedPairEvidence.controlRow (tmVerifierTimeBound V (x, w.cert))
      (tmVerifierTableauTimeRange_timeBound_mem V (x, w.cert))).label = none :=
  w.fixedPairEvidence.endpointControlRow_label

theorem endpointControlRow_state {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyTableauSeed V B x a) :
    (w.fixedPairEvidence.controlRow (tmVerifierTimeBound V (x, w.cert))
      (tmVerifierTableauTimeRange_timeBound_mem V (x, w.cert))).state =
      (tmVerifierTM V).initialState :=
  w.fixedPairEvidence.endpointControlRow_state

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
