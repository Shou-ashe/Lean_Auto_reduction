/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauSoundness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalAccepted
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalRun

/-!
Certificate-suffix bridge for x-only Cook-Levin tableaux.

The raw x-only run extraction intentionally does not decode arbitrary SAT suffix
cells as a typed verifier certificate.  This file records the exact semantic
bridge needed by the next CNF layer: once the decoded initial input stack is
known to be the x-prefix followed by a valid certificate word suffix, the raw
true-output run is a genuine typed verifier acceptance.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierReadChoicePrefixToStack_take_eq_of_symbols
    {L : EncodedDecisionProblem} {V : TMVerifier L} {k : tmVerifierStackIndex V}
    (payload : (tmVerifierTM V).Γ k → Nat)
    (word : List ((tmVerifierTM V).Γ k))
    (choices : List (TMVerifierStackReadChoice V k))
    (hSymbols :
      ∀ i, (hi : i < word.length) →
        choices[i]? = some
          (TMVerifierStackReadChoice.symbol (V := V) (k := k) (payload word[i]) word[i])) :
    (tmVerifierReadChoicePrefixToStack choices).take word.length = word := by
  induction word generalizing choices with
  | nil =>
      simp
  | cons head tail ih =>
      cases choices with
      | nil =>
          have h0 := hSymbols 0 (by simp)
          simp at h0
      | cons choice rest =>
          have h0 := hSymbols 0 (by simp)
          cases choice with
          | empty =>
              simp at h0
          | symbol pl s =>
              simp at h0
              rcases h0 with ⟨_hPayload, hSymbol⟩
              subst s
              simp [tmVerifierReadChoicePrefixToStack]
              exact ih rest (by
                intro i hi
                have hSym := hSymbols (i + 1) (by simp [hi])
                simpa using hSym)

theorem tmVerifier_verify_eq_true_of_outputs_true_in_arbitrary_time
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {n : Nat}
    (hTrue :
      Turing.TM2OutputsInTime (tmVerifierTM V) (tmVerifierInputWord V p)
        (some (tmVerifierBoolOutputWord V true)) n) :
    V.verify p.1 p.2 = true := by
  have hOut :
      tmVerifierBoolOutputWord V true =
        tmVerifierBoolOutputWord V (V.verify p.1 p.2) :=
    tm2OutputsInTime_some_unique hTrue (tmVerifierOutputsVerifyBoolInTime V p)
  exact tmVerifierBoolOutputWord_injective V hOut.symm

theorem tmVerifierXOnlyDecodedStackList_initial_input_eq_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hDomain :
      CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x 0
        (tmVerifierTM V).k₀) (tmVerifierXOnlyAcceptedRunAssignment V x c)) :
    tmVerifierXOnlyDecodedStackList V x 0 (tmVerifierTM V).k₀
        (tmVerifierXOnlyAcceptedRunAssignment V x c) hDomain =
      tmVerifierInputWord V (x, c) := by
  let a := tmVerifierXOnlyAcceptedRunAssignment V x c
  let stkAt := tmVerifierXOnlyAcceptedRunGlobalStacks V x c
  have hStack0 :
      tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 (tmVerifierTM V).k₀ =
        tmVerifierInputWord V (x, c) := by
    rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (Nat.zero_le _)]
    simp [tmVerifierInitialCfg, Turing.initList]
  have hInputLe :
      (tmVerifierInputWord V (x, c)).length ≤ tmVerifierXOnlyInputLengthBound V x :=
    tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize
  change
    tmVerifierReadChoicePrefixToStack
        (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain) =
      tmVerifierInputWord V (x, c)
  refine tmVerifierReadChoicePrefixToStack_eq_of_symbols_empty
    (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)
    (tmVerifierInputWord V (x, c))
    (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)
    ?_ ?_
  · intro i hi
    have hiStack :
        i < (tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0 (tmVerifierTM V).k₀).length := by
      simpa [hStack0] using hi
    have hiCell : i ∈ tmVerifierXOnlyCellRange V x := by
      exact tmVerifierXOnlyCellRange_mem_of_le V x (by
        have hlt : i < tmVerifierXOnlyInputLengthBound V x := lt_of_lt_of_le hi hInputLe
        have hBound : tmVerifierXOnlyInputLengthBound V x ≤ tmVerifierXOnlyCellBound V x := by
          unfold tmVerifierXOnlyCellBound
          omega
        omega)
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀
      a hDomain i hiCell]
    let d :=
      tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ i a hDomain hiCell
    have hSelected :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0 i
            (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
              (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
                ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
                  (tmVerifierTM V).k₀)[i]'hiStack))
              ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
                (tmVerifierTM V).k₀)[i]'hiStack))).eval a = true := by
      simpa [TMVerifierStackReadChoice.atomAt, a, tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected V (x, c)
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) 0 (tmVerifierTM V).k₀ hiStack
    have hChoice :
        d.choice =
          TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
            (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
              ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
                (tmVerifierTM V).k₀)[i]'hiStack))
            ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
              (tmVerifierTM V).k₀)[i]'hiStack) := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ i a hDomain hiCell d.choice
        (TMVerifierStackReadChoice.symbol (V := V) (k := (tmVerifierTM V).k₀)
          (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀
            ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
              (tmVerifierTM V).k₀)[i]'hiStack))
          ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
            (tmVerifierTM V).k₀)[i]'hiStack))
        d.choice_mem
        (tmVerifierConcreteStack_word_payload_mem V
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0)
          (tmVerifierXOnlyAcceptedRunGlobalStacks_macro_stacksActive V x c (by omega))
          (tmVerifierTM V).k₀ i hiStack)
        d.atom_true hSelected
    have hSym :
        ((tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
          (tmVerifierTM V).k₀)[i]'hiStack) =
          (tmVerifierInputWord V (x, c))[i] := by
      simp [hStack0]
    simp [d, hChoice, hSym]
  · have hCell : (tmVerifierInputWord V (x, c)).length ∈
        tmVerifierXOnlyCellRange V x := by
      exact tmVerifierXOnlyCellRange_mem_of_le V x (by
        have hBound : tmVerifierXOnlyInputLengthBound V x ≤ tmVerifierXOnlyCellBound V x := by
          unfold tmVerifierXOnlyCellBound
          omega
        omega)
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀
      a hDomain (tmVerifierInputWord V (x, c)).length hCell]
    let d :=
      tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀
        (tmVerifierInputWord V (x, c)).length a hDomain hCell
    have hEmptyTrue :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
            (tmVerifierInputWord V (x, c)).length
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
      have hnot :
          ¬ (tmVerifierInputWord V (x, c)).length <
              (tmVerifierXOnlyAcceptedRunGlobalStacks V x c 0
                (tmVerifierTM V).k₀).length := by
        simp [hStack0]
      simpa [TMVerifierStackReadChoice.atomAt, a, tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V (x, c)
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (u := 0) (j := (tmVerifierTM V).k₀)
          (cell := (tmVerifierInputWord V (x, c)).length) hnot
    have hChoice :
        d.choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ (tmVerifierInputWord V (x, c)).length a hDomain hCell
        d.choice TMVerifierStackReadChoice.empty d.choice_mem
        (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀)
        d.atom_true hEmptyTrue
    simp [d, hChoice]

namespace TMVerifierXOnlyGlobalTableauEvidence

noncomputable def decodedInitialCertificateSuffixWord
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) :=
  ((E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
      (tmVerifierTM V).k₀).drop (tmVerifierInstanceInputPrefixWord V x).length

theorem decodedCfg_initial_input_stack_take_prefix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    ((E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
        (tmVerifierTM V).k₀).take (tmVerifierInstanceInputPrefixWord V x).length =
      tmVerifierInstanceInputPrefixWord V x := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  let hDomain := E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀
  change
    (tmVerifierXOnlyDecodedStackList V x 0 (tmVerifierTM V).k₀ a hDomain).take
        (tmVerifierInstanceInputPrefixWord V x).length =
      tmVerifierInstanceInputPrefixWord V x
  unfold tmVerifierXOnlyDecodedStackList
  exact
    tmVerifierReadChoicePrefixToStack_take_eq_of_symbols
      (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)
      (tmVerifierInstanceInputPrefixWord V x)
      (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)
      (by
        intro i hi
        exact E.initialInputChoicePrefix_symbol hi)

theorem decodedCfg_initial_input_stack_eq_prefix_append_decoded_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
        (tmVerifierTM V).k₀ =
      tmVerifierInstanceInputPrefixWord V x ++ E.decodedInitialCertificateSuffixWord := by
  let stack :=
    (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
      (tmVerifierTM V).k₀
  calc
    stack = stack.take (tmVerifierInstanceInputPrefixWord V x).length ++
        stack.drop (tmVerifierInstanceInputPrefixWord V x).length := by
          exact (List.take_append_drop (tmVerifierInstanceInputPrefixWord V x).length stack).symm
    _ = tmVerifierInstanceInputPrefixWord V x ++
        E.decodedInitialCertificateSuffixWord := by
          rw [E.decodedCfg_initial_input_stack_take_prefix]
          rfl

theorem decodedCfg_initial_eq_of_certificate_word_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix)
    (hInput :
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
          (tmVerifierTM V).k₀ =
        tmVerifierInstanceInputPrefixWord V x ++ suffix) :
    E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x) =
      tmVerifierInitialCfg V (x, w.cert) := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  have hStacks :
      (E.decodedCfg 0 ht0).stk = (tmVerifierInitialCfg V (x, w.cert)).stk := by
    funext k
    by_cases hk : k = (tmVerifierTM V).k₀
    · subst k
      calc
        (E.decodedCfg 0 ht0).stk (tmVerifierTM V).k₀ =
            tmVerifierInstanceInputPrefixWord V x ++ suffix := hInput
        _ = tmVerifierInputWord V (x, w.cert) :=
            w.prefix_append_suffix_eq_inputWord
        _ = (tmVerifierInitialCfg V (x, w.cert)).stk (tmVerifierTM V).k₀ := by
            simp
    · calc
        (E.decodedCfg 0 ht0).stk k = [] :=
            E.decodedCfg_initial_noninput_stack_empty k hk
        _ = (tmVerifierInitialCfg V (x, w.cert)).stk k := by
            rw [tmVerifierInitialCfg_noninput_stack_empty V (x, w.cert) k hk]
  change
    { l := (E.controlRow 0 ht0).label
      var := (E.controlRow 0 ht0).state
      stk := (E.decodedCfg 0 ht0).stk } =
      tmVerifierInitialCfg V (x, w.cert)
  rw [E.initialControlRow_label, E.initialControlRow_state]
  exact Turing.TM2.Cfg.mk.injEq _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, hStacks⟩

noncomputable def outputs_true_in_arbitrary_time_of_initial_eq
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (c : V.Cert.Carrier)
    (hInit :
      E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x) =
        tmVerifierInitialCfg V (x, c)) :
    Turing.TM2OutputsInTime (tmVerifierTM V) (tmVerifierInputWord V (x, c))
      (some (tmVerifierBoolOutputWord V true)) (tmVerifierXOnlyTimeBound V x) := by
  have hRun := E.rawOutputsTrueInTime
  unfold Turing.TM2OutputsInTime
  simpa [tmVerifierInitialCfg, tmVerifierOutputCfg, hInit] using hRun

theorem verify_eq_true_of_initial_eq
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (c : V.Cert.Carrier)
    (hInit :
      E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x) =
        tmVerifierInitialCfg V (x, c)) :
    V.verify x c = true :=
  tmVerifier_verify_eq_true_of_outputs_true_in_arbitrary_time V (x, c)
    (E.outputs_true_in_arbitrary_time_of_initial_eq c hInit)

theorem verify_eq_true_of_certificate_word_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix)
    (hInput :
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
          (tmVerifierTM V).k₀ =
        tmVerifierInstanceInputPrefixWord V x ++ suffix) :
    V.verify x w.cert = true :=
  E.verify_eq_true_of_initial_eq w.cert
    (E.decodedCfg_initial_eq_of_certificate_word_suffix w hInput)

theorem verify_eq_true_of_decoded_initial_suffix_valid
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (w : TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord) :
    V.verify x w.cert = true :=
  E.verify_eq_true_of_certificate_word_suffix w
    E.decodedCfg_initial_input_stack_eq_prefix_append_decoded_suffix

def boundedAcceptingCertificate_of_certificate_word_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix)
    (hInput :
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
          (tmVerifierTM V).k₀ =
        tmVerifierInstanceInputPrefixWord V x ++ suffix) :
    TMVerifierBoundedAcceptingCertificate V x where
  cert := w.cert
  cert_size := w.cert_size
  verify_true := E.verify_eq_true_of_certificate_word_suffix w hInput

theorem isYes_of_certificate_word_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix)
    (hInput :
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)).stk
          (tmVerifierTM V).k₀ =
        tmVerifierInstanceInputPrefixWord V x ++ suffix) :
    L.isYes x :=
  V.sound x w.cert (E.verify_eq_true_of_certificate_word_suffix w hInput)

theorem isYes_of_decoded_initial_suffix_valid
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (w : TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord) :
    L.isYes x :=
  V.sound x w.cert (E.verify_eq_true_of_decoded_initial_suffix_valid w)

end TMVerifierXOnlyGlobalTableauEvidence

theorem tmVerifierXOnlyGlobalTableauEvidence_decodedInitialCertificateSuffixWord_eq_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hGlobal :
      CNF.Satisfies
        (tmVerifierXOnlyGlobalTableauCNF V (tmVerifierActivePushPayloadBoundary V) x)
        (tmVerifierXOnlyAcceptedRunAssignment V x c)) :
    TMVerifierXOnlyGlobalTableauEvidence.decodedInitialCertificateSuffixWord
      (tmVerifierXOnlyGlobalTableauCNF_evidence V (tmVerifierActivePushPayloadBoundary V)
        x (tmVerifierXOnlyAcceptedRunAssignment V x c) hGlobal) =
      tmVerifierCertificateInputSuffixWord V c := by
  let E :=
    tmVerifierXOnlyGlobalTableauCNF_evidence V (tmVerifierActivePushPayloadBoundary V)
      x (tmVerifierXOnlyAcceptedRunAssignment V x c) hGlobal
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  have hStack :
      tmVerifierXOnlyDecodedStackList V x 0 (tmVerifierTM V).k₀
          (tmVerifierXOnlyAcceptedRunAssignment V x c)
          (E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀) =
        tmVerifierInputWord V (x, c) :=
    tmVerifierXOnlyDecodedStackList_initial_input_eq_acceptedRun V x c hSize
      (E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀)
  change
    ((E.decodedCfg 0 ht0).stk (tmVerifierTM V).k₀).drop
        (tmVerifierInstanceInputPrefixWord V x).length =
      tmVerifierCertificateInputSuffixWord V c
  dsimp [TMVerifierXOnlyGlobalTableauEvidence.decodedCfg]
  rw [hStack, tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix]
  simp

/--
CNF assignment plus a typed validity witness for the decoded x-only certificate
suffix.  This is the precise surface the next clause layer must realize.
-/
structure TMVerifierXOnlyGlobalTableauValidSuffixSeed
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (a : Assignment) : Type where
  global_tableau :
    CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a
  valid_suffix :
    TMVerifierCertificateWordSuffix V x
      (tmVerifierXOnlyGlobalTableauCNF_evidence V B x a
        global_tableau).decodedInitialCertificateSuffixWord

namespace TMVerifierXOnlyGlobalTableauValidSuffixSeed

noncomputable def evidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    TMVerifierXOnlyGlobalTableauEvidence V B x a :=
  tmVerifierXOnlyGlobalTableauCNF_evidence V B x a w.global_tableau

theorem verify_eq_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    V.verify x w.valid_suffix.cert = true :=
  w.evidence.verify_eq_true_of_decoded_initial_suffix_valid w.valid_suffix

def boundedAcceptingCertificate
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    TMVerifierBoundedAcceptingCertificate V x where
  cert := w.valid_suffix.cert
  cert_size := w.valid_suffix.cert_size
  verify_true := w.verify_eq_true

theorem isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    L.isYes x :=
  V.sound x w.valid_suffix.cert w.verify_eq_true

end TMVerifierXOnlyGlobalTableauValidSuffixSeed

theorem tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_sound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a)) →
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        V.verify x c = true := by
  rintro ⟨a, ⟨w⟩⟩
  exact ⟨w.valid_suffix.cert, w.valid_suffix.cert_size, w.verify_eq_true⟩

theorem tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a)) →
      L.isYes x := by
  rintro ⟨a, ⟨w⟩⟩
  exact w.isYes

theorem tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_complete
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    L.isYes x →
      ∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V
        (tmVerifierActivePushPayloadBoundary V) x a) := by
  intro hx
  rcases (TMVerifierBoundedAcceptingCertificate.nonempty_iff_isYes V x).2 hx with ⟨w⟩
  let a := tmVerifierXOnlyAcceptedRunAssignment V x w.cert
  let hGlobal :
      CNF.Satisfies
        (tmVerifierXOnlyGlobalTableauCNF V (tmVerifierActivePushPayloadBoundary V) x) a :=
    tmVerifierXOnlyGlobalTableauCNF_satisfies_acceptedRun V x w.cert w.cert_size
      w.acceptedRun.output_true
  refine ⟨a, ⟨{ global_tableau := hGlobal, valid_suffix := ?_ }⟩⟩
  have hSuffix :
      (tmVerifierXOnlyGlobalTableauCNF_evidence V (tmVerifierActivePushPayloadBoundary V)
          x a hGlobal).decodedInitialCertificateSuffixWord =
        tmVerifierCertificateInputSuffixWord V w.cert := by
    exact tmVerifierXOnlyGlobalTableauEvidence_decodedInitialCertificateSuffixWord_eq_acceptedRun
      V x w.cert w.cert_size hGlobal
  rw [hSuffix]
  exact TMVerifierCertificateWordSuffix.ofCertificate V x w.cert w.cert_size

theorem tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V
      (tmVerifierActivePushPayloadBoundary V) x a)) ↔ L.isYes x := by
  constructor
  · exact tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_isYes V
      (tmVerifierActivePushPayloadBoundary V) x
  · exact tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_complete V x

end SAT
end ComplexityReduction
