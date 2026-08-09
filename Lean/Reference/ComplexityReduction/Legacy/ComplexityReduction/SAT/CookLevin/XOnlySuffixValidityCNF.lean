/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCertificateBridge

/-!
Pure certificate-suffix validity clauses for the x-only Cook-Levin surface.

The checked bridge in `XOnlyCertificateBridge` still carries a Lean-side
`TMVerifierCertificateWordSuffix` witness.  This file starts removing that
witness from the emitted SAT surface by adding ordinary CNF clauses which forbid
bounded initial input-stack choice prefixes whose decoded word is not the input
word of any bounded typed certificate.

This is a semantic finite-CNF layer.  It deliberately does not yet claim the
final polynomial-time generator required by the root theorem.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Read-choice prefix utilities -/

theorem tmVerifierReadChoicePrefixToStack_eq_append_of_symbols
    {L : EncodedDecisionProblem} {V : TMVerifier L} {k : tmVerifierStackIndex V}
    (payload : (tmVerifierTM V).Γ k → Nat) :
    (word : List ((tmVerifierTM V).Γ k)) →
      (choices : List (TMVerifierStackReadChoice V k)) →
      (∀ i, (hi : i < word.length) →
        choices[i]? = some
          (TMVerifierStackReadChoice.symbol (V := V) (k := k)
            (payload word[i]) word[i])) →
      tmVerifierReadChoicePrefixToStack choices =
        word ++ tmVerifierReadChoicePrefixToStack (choices.drop word.length)
  | [], choices, _ => by
      simp
  | head :: tail, [], hSymbols => by
      have h0 := hSymbols 0 (by simp)
      simp at h0
  | head :: tail, choice :: rest, hSymbols => by
      have h0 := hSymbols 0 (by simp)
      cases choice with
      | empty =>
          simp at h0
      | symbol payload' symbol =>
          simp at h0
          rcases h0 with ⟨_hPayload, hSymbol⟩
          subst symbol
          simp [tmVerifierReadChoicePrefixToStack,
            tmVerifierReadChoicePrefixToStack_eq_append_of_symbols payload tail rest
              (by
                intro i hi
                have hSym := hSymbols (i + 1) (by simp [hi])
                simpa using hSym)]

theorem tmVerifierReadChoicePrefixToStack_take_eq_of_getElem?_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L} {k : tmVerifierStackIndex V}
    (choices : List (TMVerifierStackReadChoice V k)) {n : Nat}
    (hEmpty :
      choices[n]? = some (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V k)) :
    tmVerifierReadChoicePrefixToStack (choices.take n) =
      tmVerifierReadChoicePrefixToStack choices := by
  induction n generalizing choices with
  | zero =>
      cases choices with
      | nil =>
          simp at hEmpty
      | cons choice rest =>
          cases choice <;> simp [tmVerifierReadChoicePrefixToStack] at hEmpty ⊢
  | succ n ih =>
      cases choices with
      | nil =>
          simp at hEmpty
      | cons choice rest =>
          cases choice with
          | empty =>
              simp [tmVerifierReadChoicePrefixToStack]
          | symbol payload symbol =>
              have hTail :
                  rest[n]? = some (TMVerifierStackReadChoice.empty :
                    TMVerifierStackReadChoice V k) := by
                simpa using hEmpty
              simp [tmVerifierReadChoicePrefixToStack, ih rest hTail]

/-! ### Bounded input-stack choice prefixes -/

/-- All input-stack read-choice prefixes of one fixed length. -/
noncomputable def tmVerifierXOnlyInputChoicePrefixesOfLength
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Nat → List (List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀))
  | 0 => [[]]
  | n + 1 =>
      (tmVerifierStackReadChoices V (tmVerifierTM V).k₀).flatMap fun choice =>
        (tmVerifierXOnlyInputChoicePrefixesOfLength V n).map fun rest => choice :: rest

/-- All input-stack read-choice prefixes up to the certificate-size bound. -/
noncomputable def tmVerifierXOnlyInputChoicePrefixesUpTo
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier) :
    List (List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :=
  (List.range (tmVerifierCertificateSizeBound V x + 1)).flatMap
    (tmVerifierXOnlyInputChoicePrefixesOfLength V)

theorem tmVerifierXOnlyInputChoicePrefixesOfLength_mem_of_forall_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (hmem :
      ∀ choice ∈ choices, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀) :
    choices ∈ tmVerifierXOnlyInputChoicePrefixesOfLength V choices.length := by
  induction choices with
  | nil =>
      simp [tmVerifierXOnlyInputChoicePrefixesOfLength]
  | cons choice rest ih =>
      have hChoice : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
        hmem choice (by simp)
      have hRest :
          ∀ choice ∈ rest, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
        intro choice hchoice
        exact hmem choice (by simp [hchoice])
      have hTail := ih hRest
      simp [tmVerifierXOnlyInputChoicePrefixesOfLength, hChoice, hTail]

theorem tmVerifierXOnlyInputChoicePrefixesOfLength_length_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n : Nat} {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (h : choices ∈ tmVerifierXOnlyInputChoicePrefixesOfLength V n) :
    choices.length = n := by
  induction n generalizing choices with
  | zero =>
      simpa [tmVerifierXOnlyInputChoicePrefixesOfLength] using h
  | succ n ih =>
      simp [tmVerifierXOnlyInputChoicePrefixesOfLength] at h
      rcases h with ⟨choice, _hchoice, rest, hrest, rfl⟩
      simp [ih hrest]

theorem tmVerifierXOnlyInputChoicePrefixesOfLength_forall_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {n : Nat} {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (h : choices ∈ tmVerifierXOnlyInputChoicePrefixesOfLength V n) :
    ∀ choice ∈ choices, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
  induction n generalizing choices with
  | zero =>
      intro choice hchoice
      have hchoices : choices = [] := by
        simpa [tmVerifierXOnlyInputChoicePrefixesOfLength] using h
      subst choices
      cases hchoice
  | succ n ih =>
      simp [tmVerifierXOnlyInputChoicePrefixesOfLength] at h
      rcases h with ⟨head, hhead, rest, hrest, rfl⟩
      intro choice hchoice
      rcases List.mem_cons.mp hchoice with rfl | htail
      · exact hhead
      · exact ih hrest choice htail

theorem tmVerifierXOnlyInputChoicePrefixesUpTo_mem_of_forall_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (hLen : choices.length ≤ tmVerifierCertificateSizeBound V x)
    (hmem :
      ∀ choice ∈ choices, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀) :
    choices ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x := by
  have hLengthMem : choices.length ∈ List.range (tmVerifierCertificateSizeBound V x + 1) := by
    simp
    omega
  exact List.mem_flatMap.mpr
    ⟨choices.length, hLengthMem,
      tmVerifierXOnlyInputChoicePrefixesOfLength_mem_of_forall_mem V hmem⟩

theorem tmVerifierXOnlyInputChoicePrefixesUpTo_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (h : choices ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x) :
    choices.length ≤ tmVerifierCertificateSizeBound V x := by
  rcases List.mem_flatMap.mp h with ⟨n, hn, hchoices⟩
  have hlen := tmVerifierXOnlyInputChoicePrefixesOfLength_length_eq V hchoices
  simp at hn
  omega

theorem tmVerifierXOnlyInputChoicePrefixesUpTo_forall_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (h : choices ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x) :
    ∀ choice ∈ choices, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
  rcases List.mem_flatMap.mp h with ⟨n, _hn, hchoices⟩
  exact tmVerifierXOnlyInputChoicePrefixesOfLength_forall_mem V hchoices

theorem tmVerifierXOnlyDecodedStackChoicePrefix_length
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a) :
    (tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h).length =
      tmVerifierXOnlyCellBound V x + 1 := by
  simp [tmVerifierXOnlyDecodedStackChoicePrefix, tmVerifierXOnlyCellSuccessorRange]

theorem tmVerifierXOnlyDecodedStackChoicePrefix_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (k : tmVerifierStackIndex V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyStackCellDomainsCNFAt V x t k) a)
    {choice : TMVerifierStackReadChoice V k}
    (hchoice : choice ∈ tmVerifierXOnlyDecodedStackChoicePrefix V x t k a h) :
    choice ∈ tmVerifierStackReadChoices V k := by
  rw [tmVerifierXOnlyDecodedStackChoicePrefix] at hchoice
  rcases List.mem_cons.mp hchoice with hHead | hTail
  · subst choice
    exact (tmVerifierXOnlyDecodedStackCellOf V x t k 0 a h
      (tmVerifierXOnlyCellRange_zero_mem V x)).choice_mem
  · rcases List.mem_map.mp hTail with ⟨cell, _hcell, hEq⟩
    subst choice
    exact (tmVerifierXOnlyDecodedStackCellOf V x t k (cell.1 + 1) a h
      (tmVerifierXOnlyCellSuccessorRange_succ_mem_cellRange V x cell.1 cell.2)).choice_mem

/-! ### Decoded initial suffix choices -/

namespace TMVerifierXOnlyGlobalTableauEvidence

noncomputable def decodedInitialCertificateChoicePrefix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain).drop
    (tmVerifierInstanceInputPrefixWord V x).length |>.take
      (tmVerifierCertificateSizeBound V x)

theorem decodedInitialCertificateChoicePrefix_length
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    E.decodedInitialCertificateChoicePrefix.length =
      tmVerifierCertificateSizeBound V x := by
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hPrefixLen :
      (tmVerifierInstanceInputPrefixWord V x).length ≤
        (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain).length := by
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_length]
    have hPrefix := tmVerifierInstanceInputPrefixWord_length_le_xOnlyCellBound V x
    omega
  rw [decodedInitialCertificateChoicePrefix, List.length_take]
  simp only [List.length_drop]
  have hLen :
      (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain).length -
          (tmVerifierInstanceInputPrefixWord V x).length =
        tmVerifierXOnlyCellBound V x + 1 -
          (tmVerifierInstanceInputPrefixWord V x).length := by
    rw [tmVerifierXOnlyDecodedStackChoicePrefix_length]
  rw [hLen]
  apply Nat.min_eq_left
  have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
  have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
  omega

theorem decodedInitialCertificateChoicePrefix_mem
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hchoice : choice ∈ E.decodedInitialCertificateChoicePrefix) :
    choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  apply tmVerifierXOnlyDecodedStackChoicePrefix_mem V x 0 (tmVerifierTM V).k₀ a hDomain
  apply List.mem_of_mem_drop
  apply List.mem_of_mem_take
  simpa [decodedInitialCertificateChoicePrefix] using hchoice

theorem decodedInitialCertificateChoicePrefix_mem_upTo
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    E.decodedInitialCertificateChoicePrefix ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x := by
  refine tmVerifierXOnlyInputChoicePrefixesUpTo_mem_of_forall_mem V x ?_ ?_
  · rw [E.decodedInitialCertificateChoicePrefix_length]
  · intro choice hchoice
    exact E.decodedInitialCertificateChoicePrefix_mem hchoice

theorem decodedInitialCertificateChoicePrefix_empty_after
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀
      ((tmVerifierInstanceInputPrefixWord V x).length +
        E.decodedInitialCertificateChoicePrefix.length)).eval a = true := by
  have hLen := E.decodedInitialCertificateChoicePrefix_length
  have hInput :
      (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length =
        tmVerifierXOnlyInputLengthBound V x := by
    rw [hLen, tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound]
  have hCell :
      tmVerifierXOnlyInputLengthBound V x ∈ tmVerifierXOnlyCellRange V x := by
    simp [tmVerifierXOnlyCellRange]
    exact tmVerifierXOnlyInputLengthBound_le_cellBound V x
  rw [hInput]
  exact tmVerifierXOnlyInitialStackCNF_satisfies_input_empty_tail V x a E.initial_stack
    (hcell := hCell) (hTail := le_rfl)

end TMVerifierXOnlyGlobalTableauEvidence

/-! ### Invalid-prefix exclusion clauses -/

/-- The machine-word suffix decoded by one bounded input-stack choice prefix. -/
noncomputable def tmVerifierXOnlyInputChoicePrefixWord
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) :=
  tmVerifierReadChoicePrefixToStack choices

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    tmVerifierXOnlyInputChoicePrefixWord V E.decodedInitialCertificateChoicePrefix =
      E.decodedInitialCertificateSuffixWord := by
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  let hDomain := E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀
  let full :=
    tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain
  let prefixWord := tmVerifierInstanceInputPrefixWord V x
  have hFullStack :
      tmVerifierReadChoicePrefixToStack full =
        prefixWord ++ E.decodedInitialCertificateSuffixWord := by
    simpa [full, prefixWord, ht0, hDomain,
      TMVerifierXOnlyGlobalTableauEvidence.decodedCfg,
      tmVerifierXOnlyDecodedStackList] using
        E.decodedCfg_initial_input_stack_eq_prefix_append_decoded_suffix
  have hSplit :
      tmVerifierReadChoicePrefixToStack full =
        prefixWord ++ tmVerifierReadChoicePrefixToStack (full.drop prefixWord.length) := by
    exact
      tmVerifierReadChoicePrefixToStack_eq_append_of_symbols
        (fun s => tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ s)
        prefixWord full (by
          intro i hi
          exact E.initialInputChoicePrefix_symbol hi)
  have hTail :
      tmVerifierReadChoicePrefixToStack (full.drop prefixWord.length) =
        E.decodedInitialCertificateSuffixWord := by
    apply List.append_cancel_left (as := prefixWord)
    rw [← hSplit, hFullStack]
  have hEmptyDrop :
      (full.drop prefixWord.length)[tmVerifierCertificateSizeBound V x]? =
        some (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    have hEmpty := E.initialInputChoicePrefix_empty_at_inputBound
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    rw [List.getElem?_drop]
    simpa [full, prefixWord, ht0, hDomain, hBoundEq, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hEmpty
  have hTake :
      tmVerifierReadChoicePrefixToStack
          ((full.drop prefixWord.length).take (tmVerifierCertificateSizeBound V x)) =
        tmVerifierReadChoicePrefixToStack (full.drop prefixWord.length) :=
    tmVerifierReadChoicePrefixToStack_take_eq_of_getElem?_empty
      (full.drop prefixWord.length) hEmptyDrop
  calc
    tmVerifierXOnlyInputChoicePrefixWord V E.decodedInitialCertificateChoicePrefix =
        tmVerifierReadChoicePrefixToStack
          ((full.drop prefixWord.length).take (tmVerifierCertificateSizeBound V x)) := by
          simp [tmVerifierXOnlyInputChoicePrefixWord,
            decodedInitialCertificateChoicePrefix, full, prefixWord]
    _ = tmVerifierReadChoicePrefixToStack (full.drop prefixWord.length) := hTake
    _ = E.decodedInitialCertificateSuffixWord := hTail

theorem decodedInitialCertificateChoicePrefix_getElem?
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat} (hi : i < E.decodedInitialCertificateChoicePrefix.length) :
    E.decodedInitialCertificateChoicePrefix[i]? =
      (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a
        (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
          (tmVerifierTM V).k₀))[
        (tmVerifierInstanceInputPrefixWord V x).length + i]? := by
  have hiBound : i < tmVerifierCertificateSizeBound V x := by
    simpa [E.decodedInitialCertificateChoicePrefix_length] using hi
  simp [decodedInitialCertificateChoicePrefix, List.getElem?_drop, hiBound, Nat.add_comm]

theorem decodedInitialCertificateChoicePrefix_atom_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat} (hi : i < E.decodedInitialCertificateChoicePrefix.length) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
      ((tmVerifierInstanceInputPrefixWord V x).length + i)
      (E.decodedInitialCertificateChoicePrefix[i]'hi)).eval a = true := by
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  let cell := (tmVerifierInstanceInputPrefixWord V x).length + i
  have hiBound : i < tmVerifierCertificateSizeBound V x := by
    simpa [E.decodedInitialCertificateChoicePrefix_length] using hi
  have hCell : cell ∈ tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    dsimp [cell]
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    omega
  let d :=
    tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ cell a hDomain hCell
  have hDecoded :
      (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)[cell]? =
        some d.choice := by
    simpa [d, cell] using
      tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀ a
        hDomain cell hCell
  have hSelected :
      (tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain)[cell]? =
        some (E.decodedInitialCertificateChoicePrefix[i]'hi) := by
    rw [← E.decodedInitialCertificateChoicePrefix_getElem? hi]
    exact List.getElem?_eq_getElem hi
  have hChoice : d.choice = E.decodedInitialCertificateChoicePrefix[i]'hi := by
    rw [hDecoded] at hSelected
    simpa using hSelected
  simpa [d, hChoice, cell] using d.atom_true

end TMVerifierXOnlyGlobalTableauEvidence

/-- A bounded input-stack choice prefix is certificate-valid when its word has a typed witness. -/
def tmVerifierXOnlyInputChoicePrefixValid
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) : Prop :=
  Nonempty (TMVerifierCertificateWordSuffix V x
    (tmVerifierXOnlyInputChoicePrefixWord V choices))

/-- Bounded choice prefixes whose decoded word is not a bounded typed certificate suffix. -/
noncomputable def tmVerifierXOnlyInvalidInputChoicePrefixes
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier) :
    List (List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) := by
  classical
  exact (tmVerifierXOnlyInputChoicePrefixesUpTo V x).filter fun choices =>
    ¬ tmVerifierXOnlyInputChoicePrefixValid V x choices

theorem tmVerifierXOnlyInvalidInputChoicePrefixes_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (h : choices ∈ tmVerifierXOnlyInvalidInputChoicePrefixes V x) :
    choices ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x ∧
      ¬ tmVerifierXOnlyInputChoicePrefixValid V x choices := by
  classical
  simpa [tmVerifierXOnlyInvalidInputChoicePrefixes] using h

/--
The positive literals saying that the initial input stack starts with `choices`
after the fixed instance prefix and is empty immediately afterward.
-/
noncomputable def tmVerifierXOnlyInputChoicePrefixMatchLiterals
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) : List Literal :=
  ((choices.zipIdx (tmVerifierInstanceInputPrefixWord V x).length).map fun entry =>
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0 entry.2 entry.1)
    ++ [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀
      ((tmVerifierInstanceInputPrefixWord V x).length + choices.length)]

/-- A single CNF clause forbidding one invalid input-stack choice prefix. -/
noncomputable def tmVerifierXOnlyInvalidInputChoicePrefixClause
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) : Clause :=
  (tmVerifierXOnlyInputChoicePrefixMatchLiterals V x choices).map Clause.negate

/-- The pure CNF layer excluding all bounded invalid certificate suffix choice prefixes. -/
noncomputable def tmVerifierXOnlySuffixValidityCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier) : CNF :=
  (tmVerifierXOnlyInvalidInputChoicePrefixes V x).map
    (tmVerifierXOnlyInvalidInputChoicePrefixClause V x)

/--
The emitted x-only CNF for the current semantic bridge: global tableau clauses
plus pure suffix-validity exclusion clauses.
-/
noncomputable def tmVerifierXOnlyEmittedCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) : CNF :=
  tmVerifierXOnlyGlobalTableauCNF V B x ++ tmVerifierXOnlySuffixValidityCNF V x

theorem tmVerifierXOnlySuffixValidityCNF_satisfies_invalid_clause
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (hinvalid : choices ∈ tmVerifierXOnlyInvalidInputChoicePrefixes V x) :
    Clause.Satisfies (tmVerifierXOnlyInvalidInputChoicePrefixClause V x choices) a := by
  exact h _ (by
    rw [tmVerifierXOnlySuffixValidityCNF]
    exact List.mem_map.mpr ⟨choices, hinvalid, rfl⟩)

theorem tmVerifierXOnlySuffixValidityCNF_no_invalid_matching_prefix
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (hinvalid : choices ∈ tmVerifierXOnlyInvalidInputChoicePrefixes V x)
    (hMatch :
      ∀ l ∈ tmVerifierXOnlyInputChoicePrefixMatchLiterals V x choices,
        l.eval a = true) :
    False := by
  have hClause :=
    tmVerifierXOnlySuffixValidityCNF_satisfies_invalid_clause V x a h hinvalid
  rcases hClause with ⟨lit, hlit, heval⟩
  rw [tmVerifierXOnlyInvalidInputChoicePrefixClause] at hlit
  rcases List.mem_map.mp hlit with ⟨base, hbase, rfl⟩
  have hFalse := (Clause.negate_eval_true_iff base a).1 heval
  have hTrue := hMatch base hbase
  simp [hTrue] at hFalse

namespace TMVerifierXOnlyGlobalTableauEvidence

theorem decodedInitialCertificateChoicePrefix_match_literals_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    ∀ l ∈ tmVerifierXOnlyInputChoicePrefixMatchLiterals V x
        E.decodedInitialCertificateChoicePrefix,
      l.eval a = true := by
  intro l hl
  rw [tmVerifierXOnlyInputChoicePrefixMatchLiterals] at hl
  rcases List.mem_append.mp hl with hChoices | hEmpty
  · rcases List.mem_map.mp hChoices with ⟨entry, hentry, rfl⟩
    have hEntry :
        ∀ entry ∈ E.decodedInitialCertificateChoicePrefix.zipIdx
            (tmVerifierInstanceInputPrefixWord V x).length,
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
            entry.2 entry.1).eval a = true := by
      rw [List.forall_mem_zipIdx]
      intro i hi
      simpa using E.decodedInitialCertificateChoicePrefix_atom_true hi
    exact hEntry entry hentry
  · simp at hEmpty
    subst l
    simpa using E.decodedInitialCertificateChoicePrefix_empty_after

noncomputable def decodedInitialCertificateSuffixWord_valid_of_suffixValidityCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix : CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a) :
    TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord := by
  classical
  have hNonempty :
      Nonempty
        (TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord) := by
    by_contra hInvalidSuffix
    have hInvalidChoices :
        ¬ tmVerifierXOnlyInputChoicePrefixValid V x
          E.decodedInitialCertificateChoicePrefix := by
      intro hValid
      rw [tmVerifierXOnlyInputChoicePrefixValid] at hValid
      rw [E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix] at hValid
      exact hInvalidSuffix hValid
    have hInInvalid :
        E.decodedInitialCertificateChoicePrefix ∈
          tmVerifierXOnlyInvalidInputChoicePrefixes V x := by
      rw [tmVerifierXOnlyInvalidInputChoicePrefixes]
      exact List.mem_filter.mpr
        ⟨E.decodedInitialCertificateChoicePrefix_mem_upTo, decide_eq_true hInvalidChoices⟩
    exact tmVerifierXOnlySuffixValidityCNF_no_invalid_matching_prefix V x a hSuffix hInInvalid
      E.decodedInitialCertificateChoicePrefix_match_literals_true
  exact Classical.choice hNonempty

end TMVerifierXOnlyGlobalTableauEvidence

theorem tmVerifierXOnlyInputChoicePrefixWord_eq_decoded_suffix_of_match
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
    (hBounded : choices ∈ tmVerifierXOnlyInputChoicePrefixesUpTo V x)
    (hMatch :
      ∀ l ∈ tmVerifierXOnlyInputChoicePrefixMatchLiterals V x choices,
        l.eval a = true) :
    tmVerifierXOnlyInputChoicePrefixWord V choices =
      E.decodedInitialCertificateSuffixWord := by
  classical
  let ht0 := tmVerifierXOnlyTableauTimeRange_zero_mem V x
  let hDomain := E.stackCellDomainsAt 0 ht0 (tmVerifierTM V).k₀
  let full :=
    tmVerifierXOnlyDecodedStackChoicePrefix V x 0 (tmVerifierTM V).k₀ a hDomain
  let prefixWord := tmVerifierInstanceInputPrefixWord V x
  have hChoicesLen :
      choices.length ≤ tmVerifierCertificateSizeBound V x :=
    tmVerifierXOnlyInputChoicePrefixesUpTo_length_le V x hBounded
  have hChoicesMem :
      ∀ choice ∈ choices, choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    tmVerifierXOnlyInputChoicePrefixesUpTo_forall_mem V x hBounded
  have hZippedMatch :
      ∀ entry ∈ choices.zipIdx prefixWord.length,
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
          entry.2 entry.1).eval a = true := by
    intro entry hentry
    exact hMatch _ (by
      rw [tmVerifierXOnlyInputChoicePrefixMatchLiterals]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hChoiceEq :
      ∀ i, (hi : i < choices.length) →
        choices[i] =
          E.decodedInitialCertificateChoicePrefix[i]'(by
            rw [E.decodedInitialCertificateChoicePrefix_length]
            omega) := by
    intro i hi
    let cell := prefixWord.length + i
    have hiCert : i < tmVerifierCertificateSizeBound V x := by omega
    have hiE : i < E.decodedInitialCertificateChoicePrefix.length := by
      simpa [E.decodedInitialCertificateChoicePrefix_length] using hiCert
    have hCell : cell ∈ tmVerifierXOnlyCellRange V x := by
      apply tmVerifierXOnlyCellRange_mem_of_le V x
      dsimp [cell, prefixWord]
      have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
      have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
      omega
    let d :=
      tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ cell a hDomain hCell
    have hMatched :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
          cell choices[i]).eval a = true := by
      have hAtIndex := (List.forall_mem_zipIdx).1 hZippedMatch i hi
      simpa [cell] using hAtIndex
    have hDecoded :
        full[cell]? = some d.choice := by
      simpa [d, cell, full] using
        tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀ a
          hDomain cell hCell
    have hSelected :
        full[cell]? =
          some (E.decodedInitialCertificateChoicePrefix[i]'hiE) := by
      rw [← E.decodedInitialCertificateChoicePrefix_getElem? hiE]
      exact List.getElem?_eq_getElem hiE
    have hDChoice : d.choice = E.decodedInitialCertificateChoicePrefix[i]'hiE := by
      rw [hDecoded] at hSelected
      simpa using hSelected
    have hChoice : choices[i] = d.choice := by
      exact (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀ cell a hDomain hCell d.choice choices[i]
        d.choice_mem (hChoicesMem choices[i] (List.getElem_mem hi))
        d.atom_true hMatched).symm
    exact hChoice.trans hDChoice
  have hChoicesTake :
      choices =
        E.decodedInitialCertificateChoicePrefix.take choices.length := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < choices.length
    · have hiE : i < E.decodedInitialCertificateChoicePrefix.length := by
        rw [E.decodedInitialCertificateChoicePrefix_length]
        omega
      rw [List.getElem?_eq_getElem hi]
      rw [List.getElem?_take_of_lt hi]
      rw [List.getElem?_eq_getElem hiE]
      exact congrArg some (hChoiceEq i hi)
    · have hChoicesNone : choices[i]? = none :=
        List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hi)
      have hTakeNone :
          (E.decodedInitialCertificateChoicePrefix.take choices.length)[i]? = none := by
        apply List.getElem?_eq_none_iff.mpr
        rw [List.length_take]
        exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_not_gt hi)
      rw [hChoicesNone, hTakeNone]
  have hLenLeE :
      choices.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
    rw [E.decodedInitialCertificateChoicePrefix_length]
    exact hChoicesLen
  by_cases hLenEq : choices.length = E.decodedInitialCertificateChoicePrefix.length
  · calc
      tmVerifierXOnlyInputChoicePrefixWord V choices =
          tmVerifierReadChoicePrefixToStack
            E.decodedInitialCertificateChoicePrefix := by
          rw [hChoicesTake, hLenEq]
          simp [tmVerifierXOnlyInputChoicePrefixWord]
      _ = E.decodedInitialCertificateSuffixWord :=
          E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  · have hLenLt : choices.length < E.decodedInitialCertificateChoicePrefix.length :=
      lt_of_le_of_ne hLenLeE hLenEq
    have hEmpty :
        E.decodedInitialCertificateChoicePrefix[choices.length]? =
          some (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
      have hEmptyLit :
          (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀
            (prefixWord.length + choices.length)).eval a = true :=
        hMatch _ (by
          rw [tmVerifierXOnlyInputChoicePrefixMatchLiterals]
          apply List.mem_append_right
          simp [prefixWord])
      let cell := prefixWord.length + choices.length
      have hCell : cell ∈ tmVerifierXOnlyCellRange V x := by
        apply tmVerifierXOnlyCellRange_mem_of_le V x
        dsimp [cell, prefixWord]
        have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
        have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
        omega
      let d :=
        tmVerifierXOnlyDecodedStackCellOf V x 0 (tmVerifierTM V).k₀ cell a hDomain hCell
      have hDChoiceEmpty :
          d.choice = (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a hDomain hCell d.choice TMVerifierStackReadChoice.empty
          d.choice_mem (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀)
          d.atom_true (by simpa [TMVerifierStackReadChoice.atomAt, cell] using hEmptyLit)
      have hDecoded :
          full[cell]? = some d.choice := by
        simpa [d, cell, full] using
          tmVerifierXOnlyDecodedStackChoicePrefix_getElem? V x 0 (tmVerifierTM V).k₀ a
            hDomain cell hCell
      have hSelected :
          full[cell]? =
            some (E.decodedInitialCertificateChoicePrefix[choices.length]'hLenLt) := by
        rw [← E.decodedInitialCertificateChoicePrefix_getElem? hLenLt]
        exact List.getElem?_eq_getElem hLenLt
      have hPrefChoice :
          E.decodedInitialCertificateChoicePrefix[choices.length]'hLenLt =
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        have hDChoice :
            d.choice =
              E.decodedInitialCertificateChoicePrefix[choices.length]'hLenLt := by
          rw [hDecoded] at hSelected
          simpa using hSelected
        exact hDChoice.symm.trans hDChoiceEmpty
      rw [List.getElem?_eq_getElem hLenLt, hPrefChoice]
    calc
      tmVerifierXOnlyInputChoicePrefixWord V choices =
          tmVerifierReadChoicePrefixToStack
            (E.decodedInitialCertificateChoicePrefix.take choices.length) := by
          rw [hChoicesTake]
          simp [tmVerifierXOnlyInputChoicePrefixWord,
            Nat.min_eq_left (Nat.le_of_lt hLenLt)]
      _ = tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix :=
          tmVerifierReadChoicePrefixToStack_take_eq_of_getElem?_empty
            E.decodedInitialCertificateChoicePrefix hEmpty
      _ = E.decodedInitialCertificateSuffixWord :=
          E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix

theorem tmVerifierXOnlySuffixValidityCNF_satisfies_of_validSuffixSeed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a := by
  classical
  intro clause hclause
  rw [tmVerifierXOnlySuffixValidityCNF] at hclause
  rcases List.mem_map.mp hclause with ⟨choices, hinvalid, rfl⟩
  rw [tmVerifierXOnlyInvalidInputChoicePrefixClause]
  by_cases hMatch :
      ∀ l ∈ tmVerifierXOnlyInputChoicePrefixMatchLiterals V x choices, l.eval a = true
  · rcases tmVerifierXOnlyInvalidInputChoicePrefixes_mem V x hinvalid with
      ⟨hBounded, hInvalid⟩
    let E :=
      tmVerifierXOnlyGlobalTableauCNF_evidence V B x a w.global_tableau
    have hWord :
        tmVerifierXOnlyInputChoicePrefixWord V choices =
          E.decodedInitialCertificateSuffixWord :=
      tmVerifierXOnlyInputChoicePrefixWord_eq_decoded_suffix_of_match E hBounded hMatch
    have hValid : tmVerifierXOnlyInputChoicePrefixValid V x choices := by
      rw [tmVerifierXOnlyInputChoicePrefixValid, hWord]
      exact ⟨w.valid_suffix⟩
    exact False.elim (hInvalid hValid)
  · rw [not_forall] at hMatch
    rcases hMatch with ⟨lit, hLit⟩
    rw [not_forall] at hLit
    rcases hLit with ⟨hmem, hEvalNotTrue⟩
    refine ⟨Clause.negate lit, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨lit, hmem, rfl⟩
    · have hEvalFalse : lit.eval a = false := by
        cases h : lit.eval a <;> simp [h] at hEvalNotTrue ⊢
      exact (Clause.negate_eval_true_iff lit a).2 hEvalFalse

theorem tmVerifierXOnlyEmittedCNF_satisfies_of_validSuffixSeed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    CNF.Satisfies (tmVerifierXOnlyEmittedCNF V B x) a := by
  rw [tmVerifierXOnlyEmittedCNF, CNF.satisfies_append]
  exact ⟨w.global_tableau, tmVerifierXOnlySuffixValidityCNF_satisfies_of_validSuffixSeed w⟩

noncomputable def tmVerifierXOnlyEmittedCNF_validSuffixSeed_of_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (h : CNF.Satisfies (tmVerifierXOnlyEmittedCNF V B x) a) :
    TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a := by
  have hPair :
      CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a ∧
        CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a := by
    exact (CNF.satisfies_append
      (tmVerifierXOnlyGlobalTableauCNF V B x)
      (tmVerifierXOnlySuffixValidityCNF V x) a).1
        (by simpa [tmVerifierXOnlyEmittedCNF] using h)
  let hGlobal := hPair.1
  let E := tmVerifierXOnlyGlobalTableauCNF_evidence V B x a hGlobal
  exact
    { global_tableau := hGlobal
      valid_suffix :=
        E.decodedInitialCertificateSuffixWord_valid_of_suffixValidityCNF
          hPair.2 }

theorem tmVerifierXOnlyEmittedCNF_satisfiable_iff_validSuffixSeed_satisfiable
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    CNF.Satisfiable (tmVerifierXOnlyEmittedCNF V B x) ↔
      ∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, ⟨tmVerifierXOnlyEmittedCNF_validSuffixSeed_of_satisfies h⟩⟩
  · rintro ⟨a, ⟨w⟩⟩
    exact ⟨a, tmVerifierXOnlyEmittedCNF_satisfies_of_validSuffixSeed w⟩

theorem tmVerifierXOnlyEmittedCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    CNF.Satisfiable
        (tmVerifierXOnlyEmittedCNF V (tmVerifierActivePushPayloadBoundary V) x) ↔
      L.isYes x := by
  rw [tmVerifierXOnlyEmittedCNF_satisfiable_iff_validSuffixSeed_satisfiable,
    tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_iff_isYes]

theorem tmVerifierXOnlyEmittedCNF_satisfies_global
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyEmittedCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a :=
  (CNF.satisfies_append
    (tmVerifierXOnlyGlobalTableauCNF V B x)
    (tmVerifierXOnlySuffixValidityCNF V x) a).1
      (by simpa [tmVerifierXOnlyEmittedCNF] using h) |>.1

theorem tmVerifierXOnlyEmittedCNF_satisfies_suffixValidity
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierXOnlyEmittedCNF V B x) a) :
    CNF.Satisfies (tmVerifierXOnlySuffixValidityCNF V x) a :=
  (CNF.satisfies_append
    (tmVerifierXOnlyGlobalTableauCNF V B x)
    (tmVerifierXOnlySuffixValidityCNF V x) a).1
      (by simpa [tmVerifierXOnlyEmittedCNF] using h) |>.2

end SAT
end ComplexityReduction
