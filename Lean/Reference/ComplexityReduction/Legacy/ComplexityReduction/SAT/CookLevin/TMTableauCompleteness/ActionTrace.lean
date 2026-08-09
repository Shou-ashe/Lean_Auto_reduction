/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.MicroDomain
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackActionCompleteness

namespace ComplexityReduction
namespace SAT

/-! ### Concrete selected-window action traces -/

theorem tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell payload : Nat}
    (hcell : cell < (stkAt t k).length)
    (hpayload :
      payload = tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell)) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  subst payload
  exact tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V p stkAt t k
    hcell

noncomputable def tmVerifierActivePushPayloadBoundary
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMVerifierPushPayloadBoundary V where
  payload raw := tmVerifierActiveStackSymbolPayload V raw.stack raw.symbol
  covered := by
    intro raw hraw
    classical
    have hActive : tmVerifierStackSymbolActive V raw.stack raw.symbol :=
      tmVerifierStackSymbolActive_of_controlPush V raw hraw
    let named := Classical.choose hActive
    have hspec :
        named ∈ tmVerifierActiveStackSymbols V ∧
          named.stack = raw.stack ∧ HEq named.symbol raw.symbol :=
      Classical.choose_spec hActive
    refine ⟨named, hspec.1, hspec.2.1, ?_, hspec.2.2⟩
    change named.payload = tmVerifierActiveStackSymbolPayload V raw.stack raw.symbol
    unfold tmVerifierActiveStackSymbolPayload
    rw [dif_pos hActive]

theorem tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V) {cell payload : Nat}
    (hcell : cell < (stkAt t k).length)
    (hpayload :
      payload ≠ tmVerifierActiveStackSymbolPayload V k ((stkAt t k)[cell]'hcell)) :
    (tmVerifierStackSymbolAtom V t k cell payload).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = false := by
  by_cases hEval :
      (tmVerifierStackSymbolAtom V t k cell payload).eval
        (tmVerifierStackFamilyAssignment V p stkAt) = true
  · exact False.elim
      (hpayload
        (tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment V p stkAt t k
          hcell hEval))
  · cases h :
      (tmVerifierStackSymbolAtom V t k cell payload).eval
        (tmVerifierStackFamilyAssignment V p stkAt) <;> simp [h] at hEval ⊢

theorem tmVerifierStackReadChoice_exists_top_eval_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (k : tmVerifierStackIndex V)
    (hActive : tmVerifierStacksActive V (stkAt t)) :
    ∃ choice : TMVerifierStackReadChoice V k,
      choice ∈ tmVerifierStackReadChoices V k ∧
        choice.toOption = (stkAt t k).head? ∧
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice).eval
            (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  cases hstk : stkAt t k with
  | nil =>
      refine ⟨TMVerifierStackReadChoice.empty, tmVerifierStackReadChoices_empty_mem V k,
        ?_, ?_⟩
      · simp [TMVerifierStackReadChoice.toOption]
      · have hnot : ¬ 0 < (stkAt t k).length := by
          simp [hstk]
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := t) (j := k) (cell := 0) hnot
  | cons head tail =>
      let choice : TMVerifierStackReadChoice V k :=
        TMVerifierStackReadChoice.symbol (V := V) (k := k)
          (tmVerifierActiveStackSymbolPayload V k head) head
      have hcell : 0 < (stkAt t k).length := by
        simp [hstk]
      have hget : ((stkAt t k)[0]'hcell) = head := by
        simp [hstk]
      have hSymbolActive : tmVerifierStackSymbolActive V k head := by
        exact hActive k 0 head (by simp [hstk])
      have hmem : choice ∈ tmVerifierStackReadChoices V k := by
        simpa [choice] using
          tmVerifierActiveStackSymbolPayload_mem V k head hSymbolActive
      refine ⟨choice, hmem, ?_, ?_⟩
      · simp [choice, TMVerifierStackReadChoice.toOption]
      · simpa [choice, TMVerifierStackReadChoice.atomAt, hget] using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            t k hcell (by simp [hget])

theorem tmVerifierWindowMicroStackFamilyAssignment_exists_top_readChoice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (micro : Nat)
    (k : tmVerifierStackIndex V)
    (hActive : tmVerifierStacksActive V (tmVerifierWindowMicroStacks V p t w micro)) :
    ∃ choice : TMVerifierStackReadChoice V k,
      choice ∈ tmVerifierStackReadChoices V k ∧
        choice.toOption = (tmVerifierWindowMicroStacks V p t w micro k).head? ∧
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t micro) 0 choice).eval
              (tmVerifierWindowMicroStackFamilyAssignment V p t w) = true := by
  have hUnpair : (Nat.unpair (tmVerifierMicroTime t micro)).2 = micro := by
    simp
  simpa [tmVerifierWindowMicroStackFamilyAssignment, hUnpair] using
    tmVerifierStackReadChoice_exists_top_eval_stackFamilyAssignment V p
      (fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2))
      (tmVerifierMicroTime t micro) k (by simpa [hUnpair] using hActive)

noncomputable def tmVerifierTopStackReadChoice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) : TMVerifierStackReadChoice V k :=
  match stk k with
  | [] => TMVerifierStackReadChoice.empty
  | head :: _ =>
      TMVerifierStackReadChoice.symbol (V := V) (k := k)
        (tmVerifierActiveStackSymbolPayload V k head) head

theorem tmVerifierTopStackReadChoice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive : tmVerifierStacksActive V stk)
    (k : tmVerifierStackIndex V) :
    tmVerifierTopStackReadChoice V stk k ∈ tmVerifierStackReadChoices V k := by
  cases hstk : stk k with
  | nil =>
      simp [tmVerifierTopStackReadChoice, hstk, tmVerifierStackReadChoices]
  | cons head tail =>
      have hSymbolActive : tmVerifierStackSymbolActive V k head :=
        hActive k 0 head (by simp [hstk])
      simpa [tmVerifierTopStackReadChoice, hstk] using
        tmVerifierActiveStackSymbolPayload_mem V k head hSymbolActive

theorem tmVerifierTopStackReadChoice_toOption
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) :
    (tmVerifierTopStackReadChoice V stk k).toOption = (stk k).head? := by
  cases hstk : stk k <;>
    simp [tmVerifierTopStackReadChoice, hstk, TMVerifierStackReadChoice.toOption]

theorem tmVerifierTopStackReadChoice_atomAt_eval_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V)
    (hStack : stkAt t k = stk k) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0
        (tmVerifierTopStackReadChoice V stk k)).eval
      (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  cases hstk : stk k with
  | nil =>
      have hnot : ¬ 0 < (stkAt t k).length := by
        rw [hStack, hstk]
        simp
      simpa [tmVerifierTopStackReadChoice, hstk] using
        tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
          (u := t) (j := k) (cell := 0) hnot
  | cons head tail =>
      have hcell : 0 < (stkAt t k).length := by
        rw [hStack, hstk]
        simp
      have hget : ((stkAt t k)[0]'hcell) = head := by
        simp [hStack, hstk]
      simpa [tmVerifierTopStackReadChoice, hstk, TMVerifierStackReadChoice.atomAt, hget]
        using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            t k hcell (by simp [hget])

theorem TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k)
    (hStack : stkAt tout k = stkAt tin k) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt) =
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt) := by
  cases choice with
  | empty =>
      by_cases hcell : cell < (stkAt tin k).length
      · have hcellOut : cell < (stkAt tout k).length := by simpa [hStack] using hcell
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt tin k
            hcell,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt tout k
            hcellOut]
      · have hcellOut : ¬ cell < (stkAt tout k).length := by simpa [hStack] using hcell
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tin) (j := k) (cell := cell) hcell,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tout) (j := k) (cell := cell) hcellOut]
  | symbol payload symbol =>
      by_cases hcell : cell < (stkAt tin k).length
      · have hcellOut : cell < (stkAt tout k).length := by simpa [hStack] using hcell
        have hget :
            ((stkAt tout k)[cell]'hcellOut) = ((stkAt tin k)[cell]'hcell) := by
          simp [hStack]
        by_cases hp :
            payload = tmVerifierActiveStackSymbolPayload V k ((stkAt tin k)[cell]'hcell)
        · have hpOut :
            payload =
              tmVerifierActiveStackSymbolPayload V k ((stkAt tout k)[cell]'hcellOut) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
              tin k hcell hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
              tout k hcellOut hpOut]
        · have hpOut :
            payload ≠
              tmVerifierActiveStackSymbolPayload V k ((stkAt tout k)[cell]'hcellOut) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt tin k hcell hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt tout k hcellOut hpOut]
      · have hcellOut : ¬ cell < (stkAt tout k).length := by simpa [hStack] using hcell
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tin) (j := k) (cell := cell) (payload := payload) hcell,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tout) (j := k) (cell := cell) (payload := payload) hcellOut]

theorem TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_push_shift
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (raw : TMVerifierStackSymbol V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V raw.stack)
    (hStack : stkAt tout raw.stack = raw.symbol :: stkAt tin raw.stack)
    (hTrue :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tin cell choice).eval
          (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := raw.stack) tout (cell + 1)
        choice).eval (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  cases choice with
  | empty =>
      by_cases hcell : cell < (stkAt tin raw.stack).length
      · have hFalse :=
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt tin
            raw.stack hcell
        simp [TMVerifierStackReadChoice.atomAt, hFalse] at hTrue
      · have hOut : ¬ cell + 1 < (stkAt tout raw.stack).length := by
          simp [hStack]
          omega
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tout) (j := raw.stack) (cell := cell + 1) hOut]
  | symbol payload symbol =>
      by_cases hcell : cell < (stkAt tin raw.stack).length
      · have hpayload :
            payload =
              tmVerifierActiveStackSymbolPayload V raw.stack
                ((stkAt tin raw.stack)[cell]'hcell) :=
          tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment V p stkAt tin
            raw.stack hcell (by simpa [TMVerifierStackReadChoice.atomAt] using hTrue)
        have hOut : cell + 1 < (stkAt tout raw.stack).length := by
          simp [hStack, hcell]
        have hget :
            ((stkAt tout raw.stack)[cell + 1]'hOut) =
              ((stkAt tin raw.stack)[cell]'hcell) := by
          simp [hStack]
        have hpayloadOut :
            payload =
              tmVerifierActiveStackSymbolPayload V raw.stack
                ((stkAt tout raw.stack)[cell + 1]'hOut) := by
          simpa [hget] using hpayload
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            tout raw.stack hOut hpayloadOut
      · have hFalse :=
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tin) (j := raw.stack) (cell := cell) (payload := payload) hcell
        simp [TMVerifierStackReadChoice.atomAt, hFalse] at hTrue

theorem TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_pop_shift
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k)
    (hStack : stkAt tout k = (stkAt tin k).tail)
    (hTrue :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice).eval
          (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt) = true := by
  cases choice with
  | empty =>
      by_cases hcell : cell + 1 < (stkAt tin k).length
      · have hFalse :=
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt tin k
            hcell
        simp [TMVerifierStackReadChoice.atomAt, hFalse] at hTrue
      · have hOut : ¬ cell < (stkAt tout k).length := by
          intro h
          have : cell + 1 < (stkAt tin k).length := by
            rw [hStack] at h
            have hpred : cell < (stkAt tin k).length.pred := by
              simpa [List.length_tail] using h
            exact Nat.lt_pred_iff.mp hpred
          exact hcell this
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tout) (j := k) (cell := cell) hOut]
  | symbol payload symbol =>
      by_cases hcell : cell + 1 < (stkAt tin k).length
      · have hpayload :
            payload =
              tmVerifierActiveStackSymbolPayload V k ((stkAt tin k)[cell + 1]'hcell) :=
          tmVerifierStackSymbolAtom_payload_eq_of_eval_stackFamilyAssignment V p stkAt tin k
            hcell (by simpa [TMVerifierStackReadChoice.atomAt] using hTrue)
        have hOut : cell < (stkAt tout k).length := by
          rw [hStack]
          have hpred : cell < (stkAt tin k).length.pred :=
            Nat.lt_pred_iff.mpr hcell
          simpa [List.length_tail] using hpred
        have hget : ((stkAt tout k)[cell]'hOut) = ((stkAt tin k)[cell + 1]'hcell) := by
          simp [hStack]
        have hpayloadOut :
            payload = tmVerifierActiveStackSymbolPayload V k ((stkAt tout k)[cell]'hOut) := by
          simpa [hget] using hpayload
        simpa [TMVerifierStackReadChoice.atomAt] using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            tout k hOut hpayloadOut
      · have hFalse :=
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt
            (u := tin) (j := k) (cell := cell + 1) (payload := payload) hcell
        simp [TMVerifierStackReadChoice.atomAt, hFalse] at hTrue

theorem tmVerifierStackActionEffectCNFBetween_satisfies_active_applyStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V) :
    stkAt tout = tmVerifierStackActionApplyStacks act (stkAt tin) →
    CNF.Satisfies
      (tmVerifierStackActionEffectCNFBetween V (tmVerifierActivePushPayloadBoundary V)
        p tin tout antecedents act)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro hApply
  cases act with
  | push raw =>
      have hStack :
          stkAt tout raw.stack = raw.symbol :: stkAt tin raw.stack := by
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          congrFun hApply raw.stack
      apply tmVerifierPushActionCNFBetween_satisfies_of_transfer
      · have hcell : 0 < (stkAt tout raw.stack).length := by
          simp [hStack]
        have htop : ((stkAt tout raw.stack)[0]'hcell) = raw.symbol := by
          simp [hStack]
        simpa [tmVerifierActivePushPayloadBoundary] using
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt
            tout raw.stack hcell (by simp [htop])
      · intro cell _hcell choice _hchoice hTrue
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_push_shift V p
          stkAt tin tout raw cell choice hStack hTrue
      · intro k hk cell _hcell choice _hchoice
        have hne : k ≠ raw.stack := by
          classical
          simpa [tmVerifierOtherStacks] using hk
        have hStackOther : stkAt tout k = stkAt tin k := by
          simpa [tmVerifierStackActionApplyStacks, Function.update, hne] using
            congrFun hApply k
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt tin tout k cell choice hStackOther
  | pop k choice =>
      have hStack : stkAt tout k = (stkAt tin k).tail := by
        simpa [tmVerifierStackActionApplyStacks, Function.update] using congrFun hApply k
      apply tmVerifierPopActionCNFBetween_satisfies_of_transfer
      · intro cell _hcell choice _hchoice hTrue
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_pop_shift V p
          stkAt tin tout k cell choice hStack hTrue
      · intro j hj cell _hcell choice _hchoice
        have hne : j ≠ k := by
          classical
          simpa [tmVerifierOtherStacks] using hj
        have hStackOther : stkAt tout j = stkAt tin j := by
          simpa [tmVerifierStackActionApplyStacks, Function.update, hne] using
            congrFun hApply j
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt tin tout j cell choice hStackOther
  | peek k choice =>
      apply tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack
  | load =>
      apply tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack
  | branch tag =>
      apply tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_eval_eq
      intro j _hj cell _hcell choice _hchoice
      have hStack : stkAt tout j = stkAt tin j := by
        simpa [tmVerifierStackActionApplyStacks] using congrFun hApply j
      exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
        V p stkAt tin tout j cell choice hStack

theorem tmVerifierStackActionCNFBetween_satisfies_active_applyStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (hApply : stkAt tout = tmVerifierStackActionApplyStacks act (stkAt tin))
    (hRead :
      TMVerifierStackActionReadAtomTrue tin
        (tmVerifierStackFamilyAssignment V p stkAt) act) :
    CNF.Satisfies
      (tmVerifierStackActionCNFBetween V (tmVerifierActivePushPayloadBoundary V)
        p tin tout antecedents act)
      (tmVerifierStackFamilyAssignment V p stkAt) :=
  tmVerifierStackActionCNFBetween_satisfies_of_parts V
    (tmVerifierActivePushPayloadBoundary V) p tin tout antecedents act
    (tmVerifierStackFamilyAssignment V p stkAt)
    (tmVerifierStackActionEffectCNFBetween_satisfies_active_applyStacks V p stkAt tin tout
      antecedents act hApply)
    hRead

theorem tmVerifierWindowActionsApplyStacks_append
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (left right : List (TMVerifierStackAction V))
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) :
    tmVerifierWindowActionsApplyStacks (left ++ right) stk =
      tmVerifierWindowActionsApplyStacks right
        (tmVerifierWindowActionsApplyStacks left stk) := by
  induction left generalizing stk with
  | nil =>
      simp [tmVerifierWindowActionsApplyStacks]
  | cons act rest ih =>
      simp [tmVerifierWindowActionsApplyStacks, ih]

theorem tmVerifierWindowActionsApplyStacks_take_succ_of_zipIdx_mem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {actions : List (TMVerifierStackAction V)}
    {entry : TMVerifierStackAction V × Nat}
    (hentry : entry ∈ actions.zipIdx)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) :
    tmVerifierWindowActionsApplyStacks (actions.take (entry.2 + 1)) stk =
      tmVerifierStackActionApplyStacks entry.1
        (tmVerifierWindowActionsApplyStacks (actions.take entry.2) stk) := by
  have hZip := List.mem_zipIdx hentry
  have hLt : entry.2 < actions.length := by
    simpa using hZip.2.1
  have hAct : entry.1 = actions[entry.2] := by
    simpa using hZip.2.2
  calc
    tmVerifierWindowActionsApplyStacks (actions.take (entry.2 + 1)) stk =
        tmVerifierWindowActionsApplyStacks (actions.take entry.2 ++ [actions[entry.2]]) stk := by
          rw [List.take_concat_get' actions entry.2 hLt]
    _ =
        tmVerifierWindowActionsApplyStacks [actions[entry.2]]
          (tmVerifierWindowActionsApplyStacks (actions.take entry.2) stk) := by
          rw [tmVerifierWindowActionsApplyStacks_append]
    _ =
        tmVerifierStackActionApplyStacks actions[entry.2]
          (tmVerifierWindowActionsApplyStacks (actions.take entry.2) stk) := by
          simp [tmVerifierWindowActionsApplyStacks]
    _ =
        tmVerifierStackActionApplyStacks entry.1
          (tmVerifierWindowActionsApplyStacks (actions.take entry.2) stk) := by
          rw [hAct]

theorem tmVerifierWindowMicroStacks_apply_succ_of_zipIdx_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V)
    (entry : TMVerifierStackAction V × Nat)
    (hentry : entry ∈ w.actions.zipIdx) :
    tmVerifierWindowMicroStacks V p t w (entry.2 + 1) =
      tmVerifierStackActionApplyStacks entry.1
        (tmVerifierWindowMicroStacks V p t w entry.2) := by
  simpa [tmVerifierWindowMicroStacks] using
    tmVerifierWindowActionsApplyStacks_take_succ_of_zipIdx_mem hentry
      (tmVerifierRunCfgAt V p t).stk

theorem tmVerifierStmtWindowsAt_exists_true_actionReadGuardsFrom_topStack
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (idx : Nat) (preActions : List (TMVerifierStackAction V))
    (stk0 : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hidx : idx = preActions.length)
    (hActive :
      tmVerifierStacksActive V (tmVerifierWindowActionsApplyStacks preActions stk0))
    (hStmtPush :
      ∀ raw, raw ∈ tmVerifierStmtPushSymbols V stmt →
        raw ∈ tmVerifierControlPushSymbols V) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t stmt s ∧
        (∀ g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions idx,
          g.eval
            (tmVerifierStackFamilyAssignment V p fun u =>
              tmVerifierWindowActionsApplyStacks
                ((preActions ++ w.actions).take ((Nat.unpair u).2)) stk0) = true) ∧
          tmVerifierWindowActionsMatchStacks w.actions
            (tmVerifierWindowActionsApplyStacks preActions stk0) := by
  induction stmt generalizing s idx preActions stk0 with
  | push k f q ih =>
      let act : TMVerifierStackAction V :=
        TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }
      have hraw :
          ({ stack := k, symbol := f s } : TMVerifierStackSymbol V) ∈
            tmVerifierControlPushSymbols V :=
        hStmtPush ({ stack := k, symbol := f s } : TMVerifierStackSymbol V)
          (tmVerifierStmtPushSymbols_push_mem V k f q s)
      have hActiveNext :
          tmVerifierStacksActive V
            (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
        have hStep :
            tmVerifierStacksActive V
              (tmVerifierStackActionApplyStacks act
                (tmVerifierWindowActionsApplyStacks preActions stk0)) :=
          tmVerifierStackActionApplyStacks_stacksActive act hActive (by
            simpa [act, TMVerifierStackActionPushSymbolMem] using hraw)
        simpa [tmVerifierWindowActionsApplyStacks_append,
          tmVerifierWindowActionsApplyStacks] using hStep
      have hTailStmt :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hrawQ
        exact hStmtPush raw (by
          simp [tmVerifierStmtPushSymbols, List.mem_append]
          exact Or.inr hrawQ)
      rcases ih s (idx + 1) (preActions ++ [act]) stk0
          (by simp [hidx]) hActiveNext hTailStmt with
        ⟨w, hw, hguards, hmatch⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩,
        ?_, ?_⟩
      · intro g hg
        simpa [act, TMVerifierStmtWindow.consAction, List.append_assoc] using
          hguards g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg)
      · have hStart :
            tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
              tmVerifierStackActionApplyStacks act
                (tmVerifierWindowActionsApplyStacks preActions stk0) := by
          simp [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks]
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
          tmVerifierStackActionReadsCurrent, hStart] using hmatch
  | peek k f q ih =>
      let current :=
        tmVerifierWindowActionsApplyStacks preActions stk0
      let choice : TMVerifierStackReadChoice V k :=
        tmVerifierTopStackReadChoice V current k
      let act : TMVerifierStackAction V :=
        TMVerifierStackAction.peek (V := V) k choice
      have hchoice : choice ∈ tmVerifierStackReadChoices V k := by
        simpa [choice, current] using
          tmVerifierTopStackReadChoice_mem V current hActive k
      have hActiveNext :
          tmVerifierStacksActive V
            (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
        have hStep :
            tmVerifierStacksActive V
              (tmVerifierStackActionApplyStacks act current) :=
          tmVerifierStackActionApplyStacks_stacksActive act hActive (by
            simp [act, TMVerifierStackActionPushSymbolMem])
        simpa [current, tmVerifierWindowActionsApplyStacks_append,
          tmVerifierWindowActionsApplyStacks, act, tmVerifierStackActionApplyStacks] using hStep
      have hTailStmt :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hrawQ
        exact hStmtPush raw (by simpa [tmVerifierStmtPushSymbols] using hrawQ)
      rcases ih (f s choice.toOption) (idx + 1) (preActions ++ [act]) stk0
          (by simp [hidx]) hActiveNext hTailStmt with
        ⟨w, hw, hguards, hmatch⟩
      let selected : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction act
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
      refine ⟨selected, ?_, ?_, ?_⟩
      · exact List.mem_flatMap.mpr
          ⟨choice, hchoice, List.mem_map.mpr ⟨w, hw, by simp [selected, act, choice]⟩⟩
      · intro g hg
        have hHead :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice).eval
                (tmVerifierStackFamilyAssignment V p fun u =>
                  tmVerifierWindowActionsApplyStacks
                    ((preActions ++ selected.actions).take ((Nat.unpair u).2)) stk0) = true := by
          have hTake :
              (preActions ++ selected.actions).take idx = preActions := by
            simp [hidx]
          have hStack :
              (tmVerifierWindowActionsApplyStacks
                ((preActions ++ selected.actions).take
                  ((Nat.unpair (tmVerifierMicroTime t idx)).2)) stk0) k =
                current k := by
            simp [tmVerifierMicroTime, hTake, current]
          simpa [selected, act, choice] using
            tmVerifierTopStackReadChoice_atomAt_eval_stackFamilyAssignment V p
              (fun u =>
                tmVerifierWindowActionsApplyStacks
                  ((preActions ++ selected.actions).take ((Nat.unpair u).2)) stk0)
              (tmVerifierMicroTime t idx) current k hStack
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∨
              g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions (idx + 1) := by
          simpa [selected, act, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg
        rcases hg' with rfl | htail
        · exact hHead
        · simpa [selected, act, List.append_assoc] using hguards g htail
      · have hStart :
            tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
              tmVerifierStackActionApplyStacks act current := by
          simp [current, tmVerifierWindowActionsApplyStacks_append,
            tmVerifierWindowActionsApplyStacks]
        have hRead : choice.toOption = (current k).head? := by
          simpa [choice] using tmVerifierTopStackReadChoice_toOption V current k
        refine ⟨?_, ?_⟩
        · simpa [current, act, tmVerifierStackActionReadsCurrent] using hRead
        · simpa [current, act, tmVerifierStackActionApplyStacks, hStart] using hmatch
  | pop k f q ih =>
      let current :=
        tmVerifierWindowActionsApplyStacks preActions stk0
      let choice : TMVerifierStackReadChoice V k :=
        tmVerifierTopStackReadChoice V current k
      let act : TMVerifierStackAction V :=
        TMVerifierStackAction.pop (V := V) k choice
      have hchoice : choice ∈ tmVerifierStackReadChoices V k := by
        simpa [choice, current] using
          tmVerifierTopStackReadChoice_mem V current hActive k
      have hActiveNext :
          tmVerifierStacksActive V
            (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
        have hStep :
            tmVerifierStacksActive V
              (tmVerifierStackActionApplyStacks act current) :=
          tmVerifierStackActionApplyStacks_stacksActive act hActive (by
            simp [act, TMVerifierStackActionPushSymbolMem])
        simpa [current, tmVerifierWindowActionsApplyStacks_append,
          tmVerifierWindowActionsApplyStacks] using hStep
      have hTailStmt :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hrawQ
        exact hStmtPush raw (by simpa [tmVerifierStmtPushSymbols] using hrawQ)
      rcases ih (f s choice.toOption) (idx + 1) (preActions ++ [act]) stk0
          (by simp [hidx]) hActiveNext hTailStmt with
        ⟨w, hw, hguards, hmatch⟩
      let selected : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction act
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
      refine ⟨selected, ?_, ?_, ?_⟩
      · exact List.mem_flatMap.mpr
          ⟨choice, hchoice, List.mem_map.mpr ⟨w, hw, by simp [selected, act, choice]⟩⟩
      · intro g hg
        have hHead :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice).eval
                (tmVerifierStackFamilyAssignment V p fun u =>
                  tmVerifierWindowActionsApplyStacks
                    ((preActions ++ selected.actions).take ((Nat.unpair u).2)) stk0) = true := by
          have hTake :
              (preActions ++ selected.actions).take idx = preActions := by
            simp [hidx]
          have hStack :
              (tmVerifierWindowActionsApplyStacks
                ((preActions ++ selected.actions).take
                  ((Nat.unpair (tmVerifierMicroTime t idx)).2)) stk0) k =
                current k := by
            simp [tmVerifierMicroTime, hTake, current]
          simpa [selected, act, choice] using
            tmVerifierTopStackReadChoice_atomAt_eval_stackFamilyAssignment V p
              (fun u =>
                tmVerifierWindowActionsApplyStacks
                  ((preActions ++ selected.actions).take ((Nat.unpair u).2)) stk0)
              (tmVerifierMicroTime t idx) current k hStack
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∨
              g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions (idx + 1) := by
          simpa [selected, act, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg
        rcases hg' with rfl | htail
        · exact hHead
        · simpa [selected, act, List.append_assoc] using hguards g htail
      · have hStart :
            tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
              tmVerifierStackActionApplyStacks act current := by
          simp [current, tmVerifierWindowActionsApplyStacks_append,
            tmVerifierWindowActionsApplyStacks]
        have hRead : choice.toOption = (current k).head? := by
          simpa [choice] using tmVerifierTopStackReadChoice_toOption V current k
        refine ⟨?_, ?_⟩
        · simpa [current, act, tmVerifierStackActionReadsCurrent] using hRead
        · simpa [current, act, tmVerifierStackActionApplyStacks, hStart] using hmatch
  | load f q ih =>
      let act : TMVerifierStackAction V := TMVerifierStackAction.load (V := V)
      have hActiveNext :
          tmVerifierStacksActive V
            (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
        simpa [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks,
          act, tmVerifierStackActionApplyStacks] using hActive
      have hTailStmt :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hrawQ
        exact hStmtPush raw (by simpa [tmVerifierStmtPushSymbols] using hrawQ)
      rcases ih (f s) (idx + 1) (preActions ++ [act]) stk0
          (by simp [hidx]) hActiveNext hTailStmt with
        ⟨w, hw, hguards, hmatch⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩,
        ?_, ?_⟩
      · intro g hg
        simpa [act, TMVerifierStmtWindow.consAction, List.append_assoc] using
          hguards g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg)
      · have hStart :
            tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
              tmVerifierStackActionApplyStacks act
                (tmVerifierWindowActionsApplyStacks preActions stk0) := by
          simp [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks]
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
          tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks, hStart]
          using hmatch
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue
        have hActiveNext :
            tmVerifierStacksActive V
              (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
          simpa [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks,
            act, tmVerifierStackActionApplyStacks] using hActive
        have hTailStmt :
            ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q₁ →
              raw ∈ tmVerifierControlPushSymbols V := by
          intro raw hrawQ
          exact hStmtPush raw (by simp [tmVerifierStmtPushSymbols, hrawQ])
        rcases ih₁ s (idx + 1) (preActions ++ [act]) stk0
            (by simp [hidx]) hActiveNext hTailStmt with
          ⟨w, hw, hguards, hmatch⟩
        refine ⟨TMVerifierStmtWindow.consAction act w, ?_, ?_, ?_⟩
        · simp [tmVerifierStmtWindowsAt, hBranch, act]
          exact ⟨w, hw, rfl⟩
        · intro g hg
          simpa [act, TMVerifierStmtWindow.consAction, List.append_assoc] using
            hguards g (by
            simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
              TMVerifierStackAction.readGuardAt] using hg)
        · have hStart :
              tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
                tmVerifierStackActionApplyStacks act
                  (tmVerifierWindowActionsApplyStacks preActions stk0) := by
            simp [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks]
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
            tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks, hStart]
            using hmatch
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse
        have hActiveNext :
            tmVerifierStacksActive V
              (tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0) := by
          simpa [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks,
            act, tmVerifierStackActionApplyStacks] using hActive
        have hTailStmt :
            ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q₂ →
              raw ∈ tmVerifierControlPushSymbols V := by
          intro raw hrawQ
          exact hStmtPush raw (by simp [tmVerifierStmtPushSymbols, hrawQ])
        rcases ih₂ s (idx + 1) (preActions ++ [act]) stk0
            (by simp [hidx]) hActiveNext hTailStmt with
          ⟨w, hw, hguards, hmatch⟩
        refine ⟨TMVerifierStmtWindow.consAction act w, ?_, ?_, ?_⟩
        · simp [tmVerifierStmtWindowsAt, hBranch, act]
          exact ⟨w, hw, rfl⟩
        · intro g hg
          simpa [act, TMVerifierStmtWindow.consAction, List.append_assoc] using
            hguards g (by
            simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
              TMVerifierStackAction.readGuardAt] using hg)
        · have hStart :
              tmVerifierWindowActionsApplyStacks (preActions ++ [act]) stk0 =
                tmVerifierStackActionApplyStacks act
                  (tmVerifierWindowActionsApplyStacks preActions stk0) := by
            simp [tmVerifierWindowActionsApplyStacks_append, tmVerifierWindowActionsApplyStacks]
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
            tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks, hStart]
            using hmatch
  | goto f =>
      refine ⟨{ guards := [], actions := [], nextLabel := some (f s), nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_, ?_⟩
      · intro g hg
        simp [tmVerifierWindowActionReadGuardsFrom] at hg
      · simp [tmVerifierWindowActionsMatchStacks]
  | halt =>
      refine ⟨{ guards := [], actions := [], nextLabel := none, nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_, ?_⟩
      · intro g hg
        simp [tmVerifierWindowActionReadGuardsFrom] at hg
      · simp [tmVerifierWindowActionsMatchStacks]

theorem tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        (∀ g ∈ tmVerifierWindowActionReadGuards t w,
          g.eval (tmVerifierWindowMicroStackFamilyAssignment V p t w) = true) ∧
          tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk := by
  rcases tmVerifierStmtWindowsAt_exists_true_actionReadGuardsFrom_topStack V p t
      ((tmVerifierTM V).m l) s 0 [] (tmVerifierRunCfgAt V p t).stk rfl
      (tmVerifierRunCfgAt_stacksActive V p t)
      (fun raw hraw => tmVerifierControlPushSymbols_label_mem V l raw hraw) with
    ⟨w, hw, hguards, hmatch⟩
  refine ⟨w, hw, ?_, ?_⟩
  · intro g hg
    simpa [tmVerifierWindowActionReadGuards, tmVerifierWindowMicroStackFamilyAssignment,
      tmVerifierWindowMicroStacks] using hguards g hg
  · simpa [tmVerifierWindowActionsApplyStacks] using hmatch

theorem tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_reads
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (hReads :
      ∀ entry ∈ w.actions.zipIdx,
        TMVerifierStackActionReadAtomTrue (tmVerifierMicroTime t entry.2)
          (tmVerifierWindowMicroStackFamilyAssignment V p t w) entry.1) :
    CNF.Satisfies
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierWindowMicroStackFamilyAssignment V p t w) := by
  apply tmVerifierWindowStackActionCNFAt_satisfies_of_actions
  intro entry hentry
  have hUnpairIn :
      (Nat.unpair (tmVerifierMicroTime t entry.2)).2 = entry.2 := by
    simp
  have hUnpairOut :
      (Nat.unpair (tmVerifierMicroTime t (entry.2 + 1))).2 = entry.2 + 1 := by
    simp
  have hApply :=
    tmVerifierWindowMicroStacks_apply_succ_of_zipIdx_mem V p t w entry hentry
  exact
    tmVerifierStackActionCNFBetween_satisfies_active_applyStacks V p
      (fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2))
      (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
      antecedents entry.1
      (by simpa [hUnpairIn, hUnpairOut] using hApply)
      (by simpa [tmVerifierWindowMicroStackFamilyAssignment] using hReads entry hentry)

theorem TMVerifierStackActionReadAtomTrue.of_readGuardAt_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {t actionIdx : Nat} {act : TMVerifierStackAction V} {a : Assignment}
    (hGuards : ∀ g ∈ act.readGuardAt t actionIdx, g.eval a = true) :
    TMVerifierStackActionReadAtomTrue (tmVerifierMicroTime t actionIdx) a act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionReadAtomTrue]
  | peek k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierMicroTime t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.readGuardAt])
  | pop k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierMicroTime t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.readGuardAt])
  | load =>
      simp [TMVerifierStackActionReadAtomTrue]
  | branch tag =>
      simp [TMVerifierStackActionReadAtomTrue]

theorem tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_readGuards
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (hGuards :
      ∀ g ∈ tmVerifierWindowActionReadGuards t w,
        g.eval (tmVerifierWindowMicroStackFamilyAssignment V p t w) = true) :
    CNF.Satisfies
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierWindowMicroStackFamilyAssignment V p t w) := by
  apply tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_reads
  intro entry hentry
  exact TMVerifierStackActionReadAtomTrue.of_readGuardAt_true (by
    intro g hg
    exact hGuards g (by
      rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
      exact List.mem_flatMap.mpr ⟨entry, hentry, hg⟩))

theorem tmVerifierStmtWindowsAt_exists_selected_window_actionCNF
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (antecedents : List Literal) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        CNF.Satisfies
          (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t w antecedents)
          (tmVerifierWindowMicroStackFamilyAssignment V p t w) ∧
          tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk := by
  rcases tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l s with
    ⟨w, hw, hguards, hmatch⟩
  exact
    ⟨w, hw,
      tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_readGuards V p t w
        antecedents hguards,
      hmatch⟩

end SAT
end ComplexityReduction
