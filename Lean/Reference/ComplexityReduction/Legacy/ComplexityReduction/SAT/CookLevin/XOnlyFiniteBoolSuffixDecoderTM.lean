/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixPatternTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackListEffects
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSATFiniteVerifier

/-!
Semantic decoder bridge for finite Boolean certificate suffixes.

The local pattern CNF is generated in `XOnlyFiniteBoolSuffixPatternTM`.  This
file starts the assignment-level bridge needed to instantiate
`TMVerifierXOnlyCheckedSuffixDecoder` for finite `List Bool` certificates.
-/

namespace ComplexityReduction
namespace SAT

noncomputable local instance finiteBoolSuffixDecoderDecidableProp (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

/-! ### Choice-level finite Boolean decoder -/

theorem tmVerifierReadChoicePrefixToStack_length_le
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    (choices : List (TMVerifierStackReadChoice V k)) :
    (tmVerifierReadChoicePrefixToStack choices).length ≤ choices.length := by
  induction choices with
  | nil =>
      simp
  | cons choice rest ih =>
      cases choice <;> simp [tmVerifierReadChoicePrefixToStack, ih]

theorem tmVerifierReadChoicePrefixToStack_getElem?_toOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    {choices : List (TMVerifierStackReadChoice V k)}
    {word : List ((tmVerifierTM V).Γ k)}
    (hWord : tmVerifierReadChoicePrefixToStack choices = word)
    {i : Nat} (hi : i < word.length) :
    ∃ choice,
      choices[i]? = some choice ∧ choice.toOption = some word[i] := by
  induction choices generalizing word i with
  | nil =>
      simp [tmVerifierReadChoicePrefixToStack] at hWord
      subst word
      simp at hi
  | cons choice rest ih =>
      cases choice with
      | empty =>
          simp [tmVerifierReadChoicePrefixToStack] at hWord
          subst word
          simp at hi
      | symbol payload s =>
          cases word with
          | nil =>
              simp [tmVerifierReadChoicePrefixToStack] at hWord
          | cons head tail =>
              have hHead : s = head := (List.cons.inj hWord).1
              have hTail : tmVerifierReadChoicePrefixToStack rest = tail :=
                (List.cons.inj hWord).2
              subst head
              cases i with
              | zero =>
                  refine ⟨TMVerifierStackReadChoice.symbol payload s, ?_, ?_⟩
                  · simp
                  · rfl
              | succ i =>
                  rcases ih (word := tail) hTail (i := i) (by simpa using hi) with
                    ⟨tailChoice, hGet, hOpt⟩
                  refine ⟨tailChoice, ?_, ?_⟩
                  · simpa using hGet
                  · simpa using hOpt

theorem tmVerifierReadChoicePrefixToStack_getElem?_length_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V}
    {choices : List (TMVerifierStackReadChoice V k)}
    {word : List ((tmVerifierTM V).Γ k)}
    (hWord : tmVerifierReadChoicePrefixToStack choices = word)
    (hLen : word.length < choices.length) :
    choices[word.length]? =
      some (TMVerifierStackReadChoice.empty : TMVerifierStackReadChoice V k) := by
  induction choices generalizing word with
  | nil =>
      simp at hLen
  | cons choice rest ih =>
      cases choice with
      | empty =>
          simp [tmVerifierReadChoicePrefixToStack] at hWord
          subst word
          simp
      | symbol payload s =>
          cases word with
          | nil =>
              simp [tmVerifierReadChoicePrefixToStack] at hWord
          | cons head tail =>
              have hHead : s = head := (List.cons.inj hWord).1
              have hTail : tmVerifierReadChoicePrefixToStack rest = tail :=
                (List.cons.inj hWord).2
              subst head
              have hTailLen : tail.length < rest.length := by
                simpa using hLen
              simpa using
                ih (word := tail) hTail hTailLen

/--
If a read choice belongs to the right-symbol choice set, then the concrete word
projection starts with the corresponding product-right input symbol.
-/
theorem tmVerifierReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    {s : V.Cert.Symbol}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V s)
    (rest : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    (tmVerifierReadChoicePrefixToStack (choice :: rest)).map
        (tmVerifierComputableWitness V).inputAlphabet =
      some (Sum.inr s) ::
        (tmVerifierReadChoicePrefixToStack rest).map
          (tmVerifierComputableWitness V).inputAlphabet := by
  classical
  have hSpec := (tmVerifierCertificateRightReadChoices_spec V s hChoice).2
  cases choice with
  | empty =>
      simp [TMVerifierStackReadChoice.toOption] at hSpec
  | symbol payload word =>
      have hWord :
          (tmVerifierComputableWitness V).inputAlphabet word =
            some (Sum.inr s) := by
        have hSpec' :
            some ((tmVerifierComputableWitness V).inputAlphabet word) =
              some (some (Sum.inr s)) := by
          simpa [TMVerifierStackReadChoice.toOption] using hSpec
        exact Option.some.inj hSpec'
      change
        (tmVerifierComputableWitness V).inputAlphabet word ::
            (tmVerifierReadChoicePrefixToStack rest).map
              (tmVerifierComputableWitness V).inputAlphabet =
          some (Sum.inr s) ::
            (tmVerifierReadChoicePrefixToStack rest).map
              (tmVerifierComputableWitness V).inputAlphabet
      rw [hWord]
      rfl

/-- Certificate-symbol stream represented by a decoded finite Boolean list. -/
def tmVerifierFiniteBoolCertificateSymbols
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (bits : List Bool) : List V.Cert.Symbol :=
  bits.flatMap fun b => [bitSymbol b, delimiterSymbol]

@[simp]
theorem tmVerifierFiniteBoolCertificateSymbols_length
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (bits : List Bool) :
    (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits).length =
      bits.length * 2 := by
  induction bits with
  | nil =>
      simp [tmVerifierFiniteBoolCertificateSymbols]
  | cons b bits ih =>
      simp [tmVerifierFiniteBoolCertificateSymbols, ih, Nat.succ_mul]

theorem tmVerifierFiniteBoolCertificateSymbols_getElem?_bit
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {bits : List Bool} {idx : Nat} (hidx : idx < bits.length) :
    (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits)[idx * 2]? =
      some (bitSymbol bits[idx]) := by
  induction bits generalizing idx with
  | nil =>
      simp at hidx
  | cons b bits ih =>
      cases idx with
      | zero =>
          simp [tmVerifierFiniteBoolCertificateSymbols]
      | succ idx =>
          have hidxTail : idx < bits.length := by
            simpa using hidx
          have hTail := ih hidxTail
          have hIndex : (idx + 1) * 2 = idx * 2 + 2 := by
            omega
          rw [hIndex]
          simpa [tmVerifierFiniteBoolCertificateSymbols, Nat.add_assoc] using hTail

theorem tmVerifierFiniteBoolCertificateSymbols_getElem?_delimiter
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {bits : List Bool} {idx : Nat} (hidx : idx < bits.length) :
    (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits)[idx * 2 + 1]? =
      some delimiterSymbol := by
  induction bits generalizing idx with
  | nil =>
      simp at hidx
  | cons b bits ih =>
      cases idx with
      | zero =>
          simp [tmVerifierFiniteBoolCertificateSymbols]
      | succ idx =>
          have hidxTail : idx < bits.length := by
            simpa using hidx
          have hTail := ih hidxTail
          have hIndex : (idx + 1) * 2 + 1 = (idx * 2 + 1) + 2 := by
            omega
          rw [hIndex]
          simpa [tmVerifierFiniteBoolCertificateSymbols, Nat.add_assoc] using hTail

/--
Choice-level decoder for a finite Boolean suffix pattern.  It stops at the first
empty cell; otherwise each Boolean symbol must be followed by the delimiter.
-/
noncomputable def tmVerifierFiniteBoolChoicePrefixDecode
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) → Option (List Bool)
  | [] => some []
  | choice :: [] =>
      if choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) then
        some []
      else
        none
  | choice :: delimiterChoice :: rest =>
      if choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) then
        some []
      else if choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) then
        if delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol then
          (tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest).map
            fun bits => false :: bits
        else
          none
      else if choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) then
        if delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol then
          (tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest).map
            fun bits => true :: bits
        else
          none
      else
        none

theorem tmVerifierFiniteBoolChoicePrefixDecode_sound_symbols
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    ∀ {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
      {bits : List Bool},
      tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol choices =
          some bits →
        (tmVerifierReadChoicePrefixToStack choices).map
            (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits).map
            fun s => some (Sum.inr s)
  | [], bits, hDecode => by
      cases hDecode
      rfl
  | choice :: [], bits, hDecode => by
      by_cases hEmpty :
          choice = (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
      · subst choice
        have hBits : bits = [] := by
          simpa [tmVerifierFiniteBoolChoicePrefixDecode] using hDecode.symm
        subst bits
        rfl
      · simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty] at hDecode
  | choice :: delimiterChoice :: rest, bits, hDecode => by
      by_cases hEmpty :
          choice = (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
      · subst choice
        have hBits : bits = [] := by
          simpa [tmVerifierFiniteBoolChoicePrefixDecode] using hDecode.symm
        subst bits
        rfl
      · by_cases hFalse :
            choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false)
        · by_cases hDelimiter :
              delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol
          · cases hRest :
                tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest with
            | none =>
                simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hDelimiter,
                  hRest] at hDecode
            | some restBits =>
                have hBits : bits = false :: restBits := by
                  simpa [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse,
                    hDelimiter, hRest] using hDecode.symm
                subst bits
                have hRestSound :=
                  tmVerifierFiniteBoolChoicePrefixDecode_sound_symbols V bitSymbol
                    delimiterSymbol hRest
                rw [tmVerifierReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                  (V := V) (s := bitSymbol false) hFalse]
                have hDelimiterMap :=
                  tmVerifierReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                    (V := V) (choice := delimiterChoice) (s := delimiterSymbol)
                    hDelimiter rest
                have hPairMap :
                    some (Sum.inr (bitSymbol false)) ::
                        (tmVerifierReadChoicePrefixToStack
                            (delimiterChoice :: rest)).map
                          (tmVerifierComputableWitness V).inputAlphabet =
                      some (Sum.inr (bitSymbol false)) ::
                        some (Sum.inr delimiterSymbol) ::
                          (tmVerifierReadChoicePrefixToStack rest).map
                            (tmVerifierComputableWitness V).inputAlphabet :=
                  congrArg (fun tail =>
                    some (Sum.inr (bitSymbol false)) :: tail) hDelimiterMap
                rw [hPairMap]
                have hRestSound' :
                    (tmVerifierReadChoicePrefixToStack rest).map
                        (tmVerifierComputableWitness V).inputAlphabet =
                      (List.flatMap (fun b => [bitSymbol b, delimiterSymbol]) restBits).map
                        fun s => some (Sum.inr s) := by
                  simpa [tmVerifierFiniteBoolCertificateSymbols] using hRestSound
                exact congrArg (fun tail =>
                  some (Sum.inr (bitSymbol false)) ::
                    some (Sum.inr delimiterSymbol) :: tail) hRestSound'
          · simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hDelimiter]
              at hDecode
        · by_cases hTrue :
              choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true)
          · by_cases hDelimiter :
                delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol
            · cases hRest :
                  tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest with
              | none =>
                  simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hTrue,
                    hDelimiter, hRest] at hDecode
              | some restBits =>
                  have hBits : bits = true :: restBits := by
                    simpa [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hTrue,
                      hDelimiter, hRest] using hDecode.symm
                  subst bits
                  have hRestSound :=
                    tmVerifierFiniteBoolChoicePrefixDecode_sound_symbols V bitSymbol
                      delimiterSymbol hRest
                  rw [tmVerifierReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                    (V := V) (s := bitSymbol true) hTrue]
                  have hDelimiterMap :=
                    tmVerifierReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                      (V := V) (choice := delimiterChoice) (s := delimiterSymbol)
                      hDelimiter rest
                  have hPairMap :
                      some (Sum.inr (bitSymbol true)) ::
                          (tmVerifierReadChoicePrefixToStack
                              (delimiterChoice :: rest)).map
                            (tmVerifierComputableWitness V).inputAlphabet =
                        some (Sum.inr (bitSymbol true)) ::
                          some (Sum.inr delimiterSymbol) ::
                            (tmVerifierReadChoicePrefixToStack rest).map
                              (tmVerifierComputableWitness V).inputAlphabet :=
                    congrArg (fun tail =>
                      some (Sum.inr (bitSymbol true)) :: tail) hDelimiterMap
                  rw [hPairMap]
                  have hRestSound' :
                      (tmVerifierReadChoicePrefixToStack rest).map
                          (tmVerifierComputableWitness V).inputAlphabet =
                        (List.flatMap (fun b => [bitSymbol b, delimiterSymbol]) restBits).map
                          fun s => some (Sum.inr s) := by
                    simpa [tmVerifierFiniteBoolCertificateSymbols] using hRestSound
                  exact congrArg (fun tail =>
                    some (Sum.inr (bitSymbol true)) ::
                      some (Sum.inr delimiterSymbol) :: tail) hRestSound'
            · simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hTrue,
                hDelimiter] at hDecode
          · simp [tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse, hTrue] at hDecode

theorem tmVerifierCertificateRightReadChoices_ne_empty
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {s : V.Cert.Symbol}
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V s) :
    choice ≠ TMVerifierStackReadChoice.empty := by
  intro hEmpty
  subst choice
  have hSpec := (tmVerifierCertificateRightReadChoices_spec V s hChoice).2
  simp [TMVerifierStackReadChoice.toOption] at hSpec

namespace TMVerifierXOnlyGlobalTableauEvidence

/--
At the initial input stack, empty cells propagate through the decoded
certificate window.  This is the x-only stack well-formedness monotonicity
specialized to the certificate suffix coordinate.
-/
theorem decodedInitialCertificateChoicePrefix_empty_successor_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat}
    (hi : i + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hEmpty :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + i)
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
      ((tmVerifierInstanceInputPrefixWord V x).length + (i + 1))
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
  let cell := (tmVerifierInstanceInputPrefixWord V x).length + i
  have hSuccRange : cell ∈ tmVerifierXOnlyCellSuccessorRange V x := by
    rw [tmVerifierXOnlyCellSuccessorRange]
    apply List.mem_range.mpr
    have hiBound : i + 1 < tmVerifierCertificateSizeBound V x := by
      simpa [E.decodedInitialCertificateChoicePrefix_length] using hi
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    dsimp [cell]
    omega
  have hWF :
      CNF.Satisfies
        (tmVerifierXOnlyStackWellFormedCNFAt V x 0 (tmVerifierTM V).k₀) a := by
    exact tmVerifierXOnlyAllStackWellFormedCNFAt_satisfies_stack V x 0
      (tmVerifierTM V).k₀ a
      (E.stackWellFormedRow 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
  have hNext :=
    tmVerifierXOnlyStackWellFormedCNFAt_satisfies_empty_successor V x 0
      (tmVerifierTM V).k₀ cell a hWF hSuccRange
      (by simpa [TMVerifierStackReadChoice.atomAt, cell] using hEmpty)
  have hCell : cell + 1 =
      (tmVerifierInstanceInputPrefixWord V x).length + (i + 1) := by
    omega
  simpa [TMVerifierStackReadChoice.atomAt, hCell] using hNext

/--
If the decoded certificate-window choice at position `i` is empty, then the
decoded choice at `i+1` is empty.
-/
theorem decodedInitialCertificateChoicePrefix_empty_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat}
    (hi : i + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hEmpty :
      E.decodedInitialCertificateChoicePrefix[i]'(by omega) =
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    E.decodedInitialCertificateChoicePrefix[i + 1]'hi =
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  let nextChoice := E.decodedInitialCertificateChoicePrefix[i + 1]'hi
  have hAtomNext :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + (i + 1))
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
    exact E.decodedInitialCertificateChoicePrefix_empty_successor_atom hi
      (by
        simpa [hEmpty] using
          E.decodedInitialCertificateChoicePrefix_atom_true (i := i) (by omega))
  have hChoiceMem :
      nextChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hi)
  have hEmptyMem :
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) ∈
          tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length + (i + 1) ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hiBound : i + 1 < tmVerifierCertificateSizeBound V x := by
      simpa [E.decodedInitialCertificateChoicePrefix_length] using hi
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    omega
  have hSelected :=
    E.decodedInitialCertificateChoicePrefix_atom_true (i := i + 1) hi
  simpa [nextChoice] using
    (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
    (tmVerifierTM V).k₀
    ((tmVerifierInstanceInputPrefixWord V x).length + (i + 1)) a hDomain hCell
    nextChoice TMVerifierStackReadChoice.empty hChoiceMem hEmptyMem hSelected hAtomNext)

theorem decodedInitialCertificateChoicePrefix_toOption_eq_decoded_suffix_get
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat}
    (hiSuffix : i < E.decodedInitialCertificateSuffixWord.length)
    (hiPrefix : i < E.decodedInitialCertificateChoicePrefix.length) :
    (E.decodedInitialCertificateChoicePrefix[i]'hiPrefix).toOption =
      some E.decodedInitialCertificateSuffixWord[i] := by
  have hWord :
      tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
        E.decodedInitialCertificateSuffixWord := by
    simpa [tmVerifierXOnlyInputChoicePrefixWord] using
      E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  rcases tmVerifierReadChoicePrefixToStack_getElem?_toOption hWord hiSuffix with
    ⟨choice, hGet, hOpt⟩
  have hSelected :
      E.decodedInitialCertificateChoicePrefix[i]? =
        some (E.decodedInitialCertificateChoicePrefix[i]'hiPrefix) :=
    List.getElem?_eq_getElem hiPrefix
  rw [hSelected] at hGet
  have hEq :
      choice = E.decodedInitialCertificateChoicePrefix[i]'hiPrefix :=
    (Option.some.inj hGet).symm
  simpa [hEq] using hOpt

theorem decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {symbols : List V.Cert.Symbol}
    (hSymbols :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness V).inputAlphabet =
        symbols.map fun s => some (Sum.inr s))
    {i : Nat} (hiSymbols : i < symbols.length)
    (hiPrefix : i < E.decodedInitialCertificateChoicePrefix.length) :
    E.decodedInitialCertificateChoicePrefix[i]'hiPrefix ∈
      tmVerifierCertificateRightReadChoices V symbols[i] := by
  classical
  have hLen :
      E.decodedInitialCertificateSuffixWord.length = symbols.length := by
    calc
      E.decodedInitialCertificateSuffixWord.length =
          (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet).length := by
            simp
      _ = (symbols.map fun s => some (Sum.inr s)).length := by
            rw [hSymbols]
            rfl
      _ = symbols.length := by
            simp
  have hiSuffix : i < E.decodedInitialCertificateSuffixWord.length := by
    simpa [hLen] using hiSymbols
  have hToOption :=
    E.decodedInitialCertificateChoicePrefix_toOption_eq_decoded_suffix_get
      hiSuffix hiPrefix
  have hMapSymbol :
      (tmVerifierComputableWitness V).inputAlphabet
          E.decodedInitialCertificateSuffixWord[i] =
        some (Sum.inr (α := L.Instance.Symbol) symbols[i]) := by
    have hGet := congrArg (fun xs => xs[i]?) hSymbols
    have hLeft :
        (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet)[i]? =
          some
            ((tmVerifierComputableWitness V).inputAlphabet
              E.decodedInitialCertificateSuffixWord[i]) := by
      simp [List.getElem?_map, hiSuffix]
    have hRight :
        (symbols.map fun s =>
            (some (Sum.inr (α := L.Instance.Symbol) s) :
              (tmVerifierInputEncodedType V).Symbol))[i]? =
          some (some (Sum.inr (α := L.Instance.Symbol) symbols[i])) := by
      simp [List.getElem?_map, hiSymbols]
    have hGet0 :
        (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet)[i]? =
          (symbols.map fun s =>
            (some (Sum.inr (α := L.Instance.Symbol) s) :
              (tmVerifierInputEncodedType V).Symbol))[i]? := by
      exact hGet
    rw [hLeft, hRight] at hGet0
    have hGet' :
        some
            ((tmVerifierComputableWitness V).inputAlphabet
              E.decodedInitialCertificateSuffixWord[i]) =
          some (some (Sum.inr (α := L.Instance.Symbol) symbols[i])) := by
      exact hGet0
    exact Option.some.inj hGet'
  exact List.mem_filter.mpr
    ⟨E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hiPrefix), by
      apply decide_eq_true
      change
        (E.decodedInitialCertificateChoicePrefix[i]'hiPrefix).toOption.map
            (tmVerifierComputableWitness V).inputAlphabet =
          some (some (Sum.inr symbols[i]))
      rw [hToOption]
      change
        some
            ((tmVerifierComputableWitness V).inputAlphabet
              E.decodedInitialCertificateSuffixWord[i]) =
          some (some (Sum.inr (α := L.Instance.Symbol) symbols[i]))
      exact congrArg some hMapSymbol⟩

theorem decodedInitialCertificateChoicePrefix_empty_at_decoded_suffix_length
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hLen :
      E.decodedInitialCertificateSuffixWord.length <
        E.decodedInitialCertificateChoicePrefix.length) :
    (E.decodedInitialCertificateChoicePrefix[E.decodedInitialCertificateSuffixWord.length]'hLen) =
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  have hWord :
      tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
        E.decodedInitialCertificateSuffixWord := by
    simpa [tmVerifierXOnlyInputChoicePrefixWord] using
      E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  have hGet :=
    tmVerifierReadChoicePrefixToStack_getElem?_length_empty hWord hLen
  have hSelected :
      E.decodedInitialCertificateChoicePrefix[E.decodedInitialCertificateSuffixWord.length]? =
        some
          (E.decodedInitialCertificateChoicePrefix[E.decodedInitialCertificateSuffixWord.length]'hLen) :=
    List.getElem?_eq_getElem hLen
  rw [hSelected] at hGet
  exact Option.some.inj hGet

theorem decodedInitialCertificateChoicePrefix_empty_of_decoded_suffix_length_le
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {i : Nat}
    (hLe : E.decodedInitialCertificateSuffixWord.length ≤ i)
    (hi : i < E.decodedInitialCertificateChoicePrefix.length) :
    E.decodedInitialCertificateChoicePrefix[i]'hi =
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  refine Nat.le_induction ?base ?step i hLe hi
  · intro hBase
    exact E.decodedInitialCertificateChoicePrefix_empty_at_decoded_suffix_length hBase
  · intro j hj ih hSucc
    have hjLt : j < E.decodedInitialCertificateChoicePrefix.length := by
      omega
    exact E.decodedInitialCertificateChoicePrefix_empty_successor hSucc (ih hjLt)

theorem finiteBoolBitCellCNFAt_satisfies_of_empty_atom
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    (hEmpty :
      (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true) :
    CNF.Satisfies
      (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierFiniteBoolBitCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [tmVerifierFiniteBoolInvalidBitChoiceClausesAt, tmVerifierUnitClauses_satisfies]
    intro lit hlit
    rcases List.mem_map.mp hlit with ⟨choice, hInvalid, rfl⟩
    apply (Clause.negate_eval_true_iff _ a).2
    by_cases hAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a = true
    · have hInvalidSpec :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
            choice ≠ TMVerifierStackReadChoice.empty ∧
              choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∧
                choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
        simpa [tmVerifierFiniteBoolInvalidBitChoices] using hInvalid
      have hEq :
          choice =
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell choice TMVerifierStackReadChoice.empty hInvalidSpec.1
          (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
          (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
      exact False.elim (hInvalidSpec.2.1 hEq)
    · cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a <;> simp [hEval] at hAtom ⊢
  · rw [tmVerifierFiniteBoolBitDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨choice, hChoice, rfl⟩
    refine ⟨Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice), by simp, ?_⟩
    apply (Clause.negate_eval_true_iff _ a).2
    by_cases hAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a = true
    · have hChoiceMem :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
        rw [tmVerifierFiniteBoolBitChoices] at hChoice
        rcases List.mem_append.mp hChoice with hFalse | hTrue
        · exact (tmVerifierCertificateRightReadChoices_spec V (bitSymbol false) hFalse).1
        · exact (tmVerifierCertificateRightReadChoices_spec V (bitSymbol true) hTrue).1
      have hChoiceNonempty :
          choice ≠
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        rw [tmVerifierFiniteBoolBitChoices] at hChoice
        rcases List.mem_append.mp hChoice with hFalse | hTrue
        · exact tmVerifierCertificateRightReadChoices_ne_empty hFalse
        · exact tmVerifierCertificateRightReadChoices_ne_empty hTrue
      have hEq :
          choice =
            (TMVerifierStackReadChoice.empty :
              TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell choice TMVerifierStackReadChoice.empty hChoiceMem
          (tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀) hAtom
          (by simpa [TMVerifierStackReadChoice.atomAt] using hEmpty)
      exact False.elim (hChoiceNonempty hEq)
    · cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a <;> simp [hEval] at hAtom ⊢

theorem finiteBoolBitCellCNFAt_satisfies_of_bit_delimiter_atoms
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {cell : Nat}
    (hCell : cell ∈ tmVerifierXOnlyCellRange V x)
    {bitChoice delimiterChoice :
      TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hBitChoice :
      bitChoice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
        bitChoice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true))
    (hBitAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell bitChoice).eval a = true)
    (hDelimiterChoice :
      delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol)
    (hDelimiterAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true) :
    CNF.Satisfies
      (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) a := by
  classical
  rw [tmVerifierFiniteBoolBitCellCNFAt, CNF.satisfies_append]
  constructor
  · rw [tmVerifierFiniteBoolInvalidBitChoiceClausesAt, tmVerifierUnitClauses_satisfies]
    intro lit hlit
    rcases List.mem_map.mp hlit with ⟨choice, hInvalid, rfl⟩
    apply (Clause.negate_eval_true_iff _ a).2
    by_cases hAtom :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a = true
    · have hInvalidSpec :
          choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
            choice ≠ TMVerifierStackReadChoice.empty ∧
              choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∧
                choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
        simpa [tmVerifierFiniteBoolInvalidBitChoices] using hInvalid
      have hBitMem :
          bitChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
        rcases hBitChoice with hFalse | hTrue
        · exact (tmVerifierCertificateRightReadChoices_spec V (bitSymbol false) hFalse).1
        · exact (tmVerifierCertificateRightReadChoices_spec V (bitSymbol true) hTrue).1
      have hEq : choice = bitChoice := by
        exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
          (tmVerifierTM V).k₀ cell a
          (E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
            (tmVerifierTM V).k₀)
          hCell choice bitChoice hInvalidSpec.1 hBitMem hAtom hBitAtom
      rcases hBitChoice with hFalse | hTrue
      · exact False.elim (hInvalidSpec.2.2.1 (by simpa [hEq] using hFalse))
      · exact False.elim (hInvalidSpec.2.2.2 (by simpa [hEq] using hTrue))
    · cases hEval :
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice).eval a <;> simp [hEval] at hAtom ⊢
  · rw [tmVerifierFiniteBoolBitDelimiterClausesAt]
    intro clause hclause
    rcases List.mem_map.mp hclause with ⟨choice, _hChoice, rfl⟩
    refine ⟨
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice, ?_, hDelimiterAtom⟩
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨delimiterChoice, hDelimiterChoice, rfl⟩

theorem finiteBoolSuffixPatternCNF_satisfies_of_mapped_suffix
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (bits : List Bool)
    (hSymbols :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness V).inputAlphabet =
        (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits).map
          fun s => some (Sum.inr s)) :
    CNF.Satisfies (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a := by
  classical
  let symbols := tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits
  have hSymbols' :
      E.decodedInitialCertificateSuffixWord.map
          (tmVerifierComputableWitness V).inputAlphabet =
        symbols.map fun s => some (Sum.inr s) := by
    simpa [symbols] using hSymbols
  have hSuffixLen : E.decodedInitialCertificateSuffixWord.length = symbols.length := by
    calc
      E.decodedInitialCertificateSuffixWord.length =
          (E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet).length := by
            simp
      _ = (symbols.map fun s => some (Sum.inr s)).length := by
            rw [hSymbols']
            rfl
      _ = symbols.length := by
            simp
  have hSuffixLeChoice :
      E.decodedInitialCertificateSuffixWord.length ≤
        E.decodedInitialCertificateChoicePrefix.length := by
    have hWord :
        tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
          E.decodedInitialCertificateSuffixWord := by
      simpa [tmVerifierXOnlyInputChoicePrefixWord] using
        E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
    rw [← hWord]
    exact tmVerifierReadChoicePrefixToStack_length_le
      E.decodedInitialCertificateChoicePrefix
  intro clause hclause
  rw [tmVerifierFiniteBoolSuffixPatternCNF, tmVerifierFiniteBoolSuffixPatternCNFForBound]
    at hclause
  rcases List.mem_flatMap.mp hclause with ⟨idx, hidxMem, hclauseCell⟩
  have hidx : idx < tmVerifierCertificateSizeBound V x := by
    simpa using List.mem_range.mp hidxMem
  let bound := tmVerifierCertificateSizeBound V x
  let offset := Nat.min (idx * 2) bound
  let cell := L.Instance.inputSize x + 1 + offset
  have hPrefixLen :
      (tmVerifierInstanceInputPrefixWord V x).length = L.Instance.inputSize x + 1 := by
    simp
  have hCellEq :
      L.Instance.inputSize x + 1 + Nat.min (idx * 2) bound = cell := rfl
  have hOffsetLe : offset ≤ bound := Nat.min_le_right (idx * 2) bound
  have hCellRange : cell ∈ tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hCellLeInput : cell ≤ tmVerifierXOnlyInputLengthBound V x := by
      dsimp [cell]
      simpa [tmVerifierXOnlyInputLengthBound, offset, bound, Nat.add_assoc] using
        Nat.add_le_add_left hOffsetLe (L.Instance.inputSize x + 1)
    exact Nat.le_trans hCellLeInput hInputLe
  have hChoiceLen :
      E.decodedInitialCertificateChoicePrefix.length = bound := by
    simpa [bound] using E.decodedInitialCertificateChoicePrefix_length
  have hCellSat :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) a := by
    by_cases hOffsetAtBound : offset = bound
    · have hCellBound :
          cell =
            (tmVerifierInstanceInputPrefixWord V x).length +
              E.decodedInitialCertificateChoicePrefix.length := by
        dsimp [cell]
        rw [hOffsetAtBound, hChoiceLen, hPrefixLen]
      have hEmpty :
          (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true := by
        simpa [hCellBound] using E.decodedInitialCertificateChoicePrefix_empty_after
      exact E.finiteBoolBitCellCNFAt_satisfies_of_empty_atom bitSymbol delimiterSymbol
        hCellRange hEmpty
    · have hOffsetLt : offset < bound := lt_of_le_of_ne hOffsetLe hOffsetAtBound
      have hOffsetEq : offset = idx * 2 := by
        by_cases hle : idx * 2 ≤ bound
        · dsimp [offset]
          exact Nat.min_eq_left hle
        · have hboundle : bound ≤ idx * 2 := Nat.le_of_lt (Nat.lt_of_not_ge hle)
          have hMin : offset = bound := by
            dsimp [offset]
            exact Nat.min_eq_right hboundle
          exact False.elim (hOffsetAtBound hMin)
      have hOffsetPrefix : offset < E.decodedInitialCertificateChoicePrefix.length := by
        simpa [hChoiceLen] using hOffsetLt
      by_cases hOffsetSuffix : offset < symbols.length
      · have hidxBits : idx < bits.length := by
          have hLenSymbols :
              symbols.length =
                (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits).length :=
            rfl
          simp [symbols] at hOffsetSuffix
          dsimp [offset] at hOffsetEq
          omega
        have hOffsetSymbols : idx * 2 < symbols.length := by
          simpa [hOffsetEq] using hOffsetSuffix
        have hNextSymbols : idx * 2 + 1 < symbols.length := by
          simp [symbols]
          omega
        have hNextPrefix : idx * 2 + 1 <
            E.decodedInitialCertificateChoicePrefix.length := by
          have hSuffixLe :
              symbols.length ≤ E.decodedInitialCertificateChoicePrefix.length := by
            rw [← hSuffixLen]
            exact hSuffixLeChoice
          omega
        have hBitGet :=
          tmVerifierFiniteBoolCertificateSymbols_getElem?_bit bitSymbol delimiterSymbol hidxBits
        have hDelimiterGet :=
          tmVerifierFiniteBoolCertificateSymbols_getElem?_delimiter bitSymbol
            delimiterSymbol hidxBits
        have hBitSymbol :
            symbols[idx * 2]'hOffsetSymbols = bitSymbol bits[idx] := by
          have hGetElem :
              symbols[idx * 2]? = some (symbols[idx * 2]'hOffsetSymbols) :=
            List.getElem?_eq_getElem hOffsetSymbols
          rw [hGetElem] at hBitGet
          exact Option.some.inj hBitGet
        have hDelimiterSymbol :
            symbols[idx * 2 + 1]'hNextSymbols = delimiterSymbol := by
          have hGetElem :
              symbols[idx * 2 + 1]? = some (symbols[idx * 2 + 1]'hNextSymbols) :=
            List.getElem?_eq_getElem hNextSymbols
          rw [hGetElem] at hDelimiterGet
          exact Option.some.inj hDelimiterGet
        have hBitChoice :
            E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix ∈
              tmVerifierCertificateRightReadChoices V (bitSymbol bits[idx]) := by
          have hChoice :=
            E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
              hSymbols' hOffsetSymbols (by simpa [hOffsetEq] using hOffsetPrefix)
          simpa [hOffsetEq, hBitSymbol] using hChoice
        have hDelimiterChoice :
            E.decodedInitialCertificateChoicePrefix[idx * 2 + 1]'hNextPrefix ∈
              tmVerifierCertificateRightReadChoices V delimiterSymbol := by
          have hChoice :=
            E.decodedInitialCertificateChoicePrefix_rightChoice_of_mapped_suffix
              hSymbols' hNextSymbols hNextPrefix
          simpa [hDelimiterSymbol] using hChoice
        have hBitAtom :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 cell
              (E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix)).eval a =
              true := by
          have hAtom :=
            E.decodedInitialCertificateChoicePrefix_atom_true
              (i := offset) hOffsetPrefix
          dsimp [cell]
          rw [← hPrefixLen]
          simpa using hAtom
        have hDelimiterAtom :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 (cell + 1)
              (E.decodedInitialCertificateChoicePrefix[idx * 2 + 1]'hNextPrefix)).eval a =
              true := by
          have hAtom :=
            E.decodedInitialCertificateChoicePrefix_atom_true
              (i := idx * 2 + 1) hNextPrefix
          have hCellNext :
              (tmVerifierInstanceInputPrefixWord V x).length + (idx * 2 + 1) =
                cell + 1 := by
            dsimp [cell]
            rw [← hPrefixLen, hOffsetEq]
            omega
          simpa [← hCellNext] using hAtom
        have hBitChoiceEither :
            E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix ∈
                tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
              E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix ∈
                tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
          cases hbit : bits[idx] with
          | false =>
              left
              simpa [hbit] using hBitChoice
          | true =>
              right
              simpa [hbit] using hBitChoice
        exact E.finiteBoolBitCellCNFAt_satisfies_of_bit_delimiter_atoms
          bitSymbol delimiterSymbol hCellRange hBitChoiceEither hBitAtom
          hDelimiterChoice hDelimiterAtom
      · have hSuffixLeOffset : E.decodedInitialCertificateSuffixWord.length ≤ offset := by
          rw [hSuffixLen]
          exact Nat.le_of_not_gt hOffsetSuffix
        have hEmptyChoice :
            E.decodedInitialCertificateChoicePrefix[offset]'hOffsetPrefix =
              (TMVerifierStackReadChoice.empty :
                TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
          E.decodedInitialCertificateChoicePrefix_empty_of_decoded_suffix_length_le
            hSuffixLeOffset hOffsetPrefix
        have hEmpty :
            (tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell).eval a = true := by
          have hAtom :=
            E.decodedInitialCertificateChoicePrefix_atom_true
              (i := offset) hOffsetPrefix
          dsimp [cell]
          rw [← hPrefixLen]
          simpa [hEmptyChoice, TMVerifierStackReadChoice.atomAt] using hAtom
        exact E.finiteBoolBitCellCNFAt_satisfies_of_empty_atom bitSymbol delimiterSymbol
          hCellRange hEmpty
  exact hCellSat clause (by simpa [hCellEq, offset, bound, cell] using hclauseCell)

/--
At an even finite-Boolean bit-start position, the checked suffix-pattern CNF
allows only empty, false-bit, or true-bit read choices.
-/
theorem decodedInitialCertificateChoicePrefix_finiteBool_allowed_at_even
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx * 2 < E.decodedInitialCertificateChoicePrefix.length) :
    let choice := E.decodedInitialCertificateChoicePrefix[idx * 2]'hidx
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
  classical
  intro choice
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierFiniteBoolSuffixPatternCNF_bitCell_satisfies V bitSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) = idx * 2 := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx * 2 := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hChoiceMem :
      choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hidx)
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x)) choice).eval a =
        true := by
    simpa [choice, hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx * 2) hidx
  exact tmVerifierFiniteBoolBitCellCNFAt_allowed_of_atom_true V bitSymbol
    delimiterSymbol hCellCNF hChoiceMem hAtom

/--
If an even finite-Boolean bit-start position selects a bit choice and the next
certificate-window cell exists, that next decoded choice is a delimiter choice.
-/
theorem decodedInitialCertificateChoicePrefix_finiteBool_delimiter_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx * 2 < E.decodedInitialCertificateChoicePrefix.length)
    (hnext : idx * 2 + 1 < E.decodedInitialCertificateChoicePrefix.length)
    (hBit :
      E.decodedInitialCertificateChoicePrefix[idx * 2]'hidx ∈
        tmVerifierFiniteBoolBitChoices V bitSymbol) :
    E.decodedInitialCertificateChoicePrefix[idx * 2 + 1]'hnext ∈
      tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  classical
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierFiniteBoolSuffixPatternCNF_bitCell_satisfies V bitSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) = idx * 2 := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx * 2 := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx * 2]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx * 2) hidx
  rcases tmVerifierFiniteBoolBitCellCNFAt_delimiter_of_atom_true V bitSymbol
      delimiterSymbol hCellCNF hBit hAtom with
    ⟨delimiterChoice, hDelimiterChoice, hDelimiterAtom⟩
  let nextChoice := E.decodedInitialCertificateChoicePrefix[idx * 2 + 1]'hnext
  have hNextMem :
      nextChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    E.decodedInitialCertificateChoicePrefix_mem (List.getElem_mem hnext)
  have hDelimiterMem :
      delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length + (idx * 2 + 1) ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hSelected :=
    E.decodedInitialCertificateChoicePrefix_atom_true (i := idx * 2 + 1) hnext
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length + (idx * 2 + 1) := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hDelimiterAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx * 2 + 1))
        delimiterChoice).eval a = true := by
    simpa [hCellSucc] using hDelimiterAtom
  have hEq :
      nextChoice = delimiterChoice := by
    simpa [nextChoice] using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length + (idx * 2 + 1)) a hDomain
        hCell nextChoice delimiterChoice hNextMem hDelimiterMem hSelected hDelimiterAtom')
  simpa [nextChoice, hEq] using hDelimiterChoice

/--
A selected bit at an even bit-start position cannot be the final certificate
window cell: the delimiter clause would force a nonempty delimiter exactly
where the initial-stack boundary clauses force emptiness.
-/
theorem decodedInitialCertificateChoicePrefix_finiteBool_bit_has_successor
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a)
    {idx : Nat}
    (hidx : idx * 2 < E.decodedInitialCertificateChoicePrefix.length)
    (hBit :
      E.decodedInitialCertificateChoicePrefix[idx * 2]'hidx ∈
        tmVerifierFiniteBoolBitChoices V bitSymbol) :
    idx * 2 + 1 < E.decodedInitialCertificateChoicePrefix.length := by
  classical
  by_contra hnot
  have hBoundary : idx * 2 + 1 = E.decodedInitialCertificateChoicePrefix.length := by
    omega
  have hidxBound : idx < tmVerifierCertificateSizeBound V x := by
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellCNF :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
          (L.Instance.inputSize x + 1 +
            Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))) a :=
    tmVerifierFiniteBoolSuffixPatternCNF_bitCell_satisfies V bitSymbol
      delimiterSymbol hSuffix hidxBound
  have hMin : Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) = idx * 2 := by
    apply Nat.min_eq_left
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hCellEq :
      L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) =
        (tmVerifierInstanceInputPrefixWord V x).length + idx * 2 := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
  have hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        (L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))
        (E.decodedInitialCertificateChoicePrefix[idx * 2]'hidx)).eval a = true := by
    simpa [hCellEq] using
      E.decodedInitialCertificateChoicePrefix_atom_true (i := idx * 2) hidx
  rcases tmVerifierFiniteBoolBitCellCNFAt_delimiter_of_atom_true V bitSymbol
      delimiterSymbol hCellCNF hBit hAtom with
    ⟨delimiterChoice, hDelimiterChoice, hDelimiterAtom⟩
  let hDomain := E.stackCellDomainsAt 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x)
    (tmVerifierTM V).k₀
  have hCell :
      (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length ∈
        tmVerifierXOnlyCellRange V x := by
    apply tmVerifierXOnlyCellRange_mem_of_le V x
    have hBoundEq := tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound V x
    have hInputLe := tmVerifierXOnlyInputLengthBound_le_cellBound V x
    have hLen := E.decodedInitialCertificateChoicePrefix_length
    omega
  have hDelimiterMem :
      delimiterChoice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    (tmVerifierCertificateRightReadChoices_spec V delimiterSymbol hDelimiterChoice).1
  have hEmptyMem :
      (TMVerifierStackReadChoice.empty :
        TMVerifierStackReadChoice V (tmVerifierTM V).k₀) ∈
          tmVerifierStackReadChoices V (tmVerifierTM V).k₀ :=
    tmVerifierStackReadChoices_empty_mem V (tmVerifierTM V).k₀
  have hCellSucc :
      L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x) + 1 =
        (tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length := by
    rw [tmVerifierInstanceInputPrefixWord_length, hMin]
    omega
  have hDelimiterAtom' :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        delimiterChoice).eval a = true := by
    simpa [hCellSucc] using hDelimiterAtom
  have hEmptyAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length)
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).eval a = true := by
    simpa [tmVerifierStackEmptyAtom, TMVerifierStackReadChoice.atomAt] using
      E.decodedInitialCertificateChoicePrefix_empty_after
  have hEq :
      delimiterChoice =
        (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
    simpa using
      (tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x 0
        (tmVerifierTM V).k₀
        ((tmVerifierInstanceInputPrefixWord V x).length +
          E.decodedInitialCertificateChoicePrefix.length) a hDomain hCell
        delimiterChoice TMVerifierStackReadChoice.empty hDelimiterMem hEmptyMem
        hDelimiterAtom' hEmptyAtom)
  exact tmVerifierCertificateRightReadChoices_ne_empty hDelimiterChoice hEq

/--
Every even-offset suffix of the decoded certificate choice window is accepted
by the finite-Boolean choice decoder when the suffix-pattern CNF is satisfied.
-/
theorem decodedInitialCertificateChoicePrefix_finiteBoolChoicePrefixDecode_drop
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a)
    {offset : Nat}
    (hoffset : offset ≤ E.decodedInitialCertificateChoicePrefix.length)
    (heven : ∃ idx : Nat, offset = idx * 2) :
    ∃ bits : List Bool,
      tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol
        (E.decodedInitialCertificateChoicePrefix.drop offset) = some bits := by
  classical
  let choicesAll := E.decodedInitialCertificateChoicePrefix
  let len := choicesAll.length
  suffices hMain :
      ∀ n : Nat, ∀ offset : Nat,
        len - offset = n →
          offset ≤ len →
            (∃ idx : Nat, offset = idx * 2) →
              ∃ bits : List Bool,
                tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol
                  (choicesAll.drop offset) = some bits by
    simpa [choicesAll, len] using
      hMain (len - offset) offset rfl (by simpa [choicesAll, len] using hoffset) heven
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro offset hn hoffset heven
      by_cases hEnd : offset = len
      · subst offset
        refine ⟨[], ?_⟩
        have hDropEnd : choicesAll.drop len = [] := by
          simp [len]
        simp [hDropEnd, tmVerifierFiniteBoolChoicePrefixDecode]
      · have hlt : offset < len := lt_of_le_of_ne hoffset hEnd
        rcases heven with ⟨idx, hidxEq⟩
        subst offset
        have hidx : idx * 2 < E.decodedInitialCertificateChoicePrefix.length := by
          simpa [choicesAll, len] using hlt
        cases hDrop : choicesAll.drop (idx * 2) with
        | nil =>
            have hLenDrop := congrArg List.length hDrop
            have hDropLen : (choicesAll.drop (idx * 2)).length = len - idx * 2 := by
              simp [len]
            rw [hDropLen] at hLenDrop
            simp at hLenDrop
            omega
        | cons choice tail =>
            have hHead? :
                choicesAll[idx * 2]? = some choice := by
              have hDropHead : (choicesAll.drop (idx * 2))[0]? = some choice := by
                simp [hDrop]
              simpa [List.getElem?_drop] using hDropHead
            have hHeadEq :
                choice = choicesAll[idx * 2]'(by simpa [choicesAll] using hidx) := by
              have hOrig :
                  choicesAll[idx * 2]? =
                    some (choicesAll[idx * 2]'(by simpa [choicesAll] using hidx)) :=
                List.getElem?_eq_getElem (by simpa [choicesAll] using hidx)
              rw [hOrig] at hHead?
              exact (Option.some.inj hHead?).symm
            have hAllowed :
                choice = TMVerifierStackReadChoice.empty ∨
                  choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
                  choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
              have hAllowed0 :=
                E.decodedInitialCertificateChoicePrefix_finiteBool_allowed_at_even
                  bitSymbol delimiterSymbol hSuffix (idx := idx) hidx
              simpa [hHeadEq] using hAllowed0
            by_cases hEmpty :
                choice = (TMVerifierStackReadChoice.empty :
                  TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
            · refine ⟨[], ?_⟩
              cases tail with
              | nil =>
                  simp [hDrop, tmVerifierFiniteBoolChoicePrefixDecode, hEmpty]
              | cons delimiterChoice rest =>
                  simp [hDrop, tmVerifierFiniteBoolChoicePrefixDecode, hEmpty]
            · by_cases hFalse :
                  choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false)
              · have hBit :
                    choicesAll[idx * 2]'(by simpa [choicesAll] using hidx) ∈
                      tmVerifierFiniteBoolBitChoices V bitSymbol := by
                  rw [← hHeadEq]
                  rw [tmVerifierFiniteBoolBitChoices]
                  exact List.mem_append_left
                    (tmVerifierCertificateRightReadChoices V (bitSymbol true)) hFalse
                have hnext :
                    idx * 2 + 1 < E.decodedInitialCertificateChoicePrefix.length :=
                  E.decodedInitialCertificateChoicePrefix_finiteBool_bit_has_successor
                    bitSymbol delimiterSymbol hSuffix hidx hBit
                cases tail with
                | nil =>
                    have hLenDrop := congrArg List.length hDrop
                    have hDropLen : (choicesAll.drop (idx * 2)).length = len - idx * 2 := by
                      simp [len]
                    rw [hDropLen] at hLenDrop
                    simp at hLenDrop
                    have hnextLen : idx * 2 + 1 < len := by
                      simpa [choicesAll, len] using hnext
                    omega
                | cons delimiterChoice rest =>
                    have hTailHead? :
                        choicesAll[idx * 2 + 1]? = some delimiterChoice := by
                      have hDropHead :
                          (choicesAll.drop (idx * 2))[1]? = some delimiterChoice := by
                        simp [hDrop]
                      simpa [List.getElem?_drop, Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using hDropHead
                    have hTailEq :
                        delimiterChoice =
                          choicesAll[idx * 2 + 1]'(by simpa [choicesAll] using hnext) := by
                      have hOrig :
                          choicesAll[idx * 2 + 1]? =
                            some (choicesAll[idx * 2 + 1]'(by
                              simpa [choicesAll] using hnext)) :=
                        List.getElem?_eq_getElem (by simpa [choicesAll] using hnext)
                      rw [hOrig] at hTailHead?
                      exact (Option.some.inj hTailHead?).symm
                    have hDelimiter :
                        delimiterChoice ∈
                          tmVerifierCertificateRightReadChoices V delimiterSymbol := by
                      have hDelim0 :=
                        E.decodedInitialCertificateChoicePrefix_finiteBool_delimiter_successor
                          bitSymbol delimiterSymbol hSuffix hidx hnext hBit
                      simpa [hTailEq] using hDelim0
                    have hleNext : idx * 2 + 2 ≤ len := by
                      simpa [choicesAll, len] using Nat.succ_le_of_lt hnext
                    have hEvenNext : ∃ j : Nat, idx * 2 + 2 = j * 2 := by
                      refine ⟨idx + 1, ?_⟩
                      omega
                    have hRestDrop : rest = choicesAll.drop (idx * 2 + 2) := by
                      have hDrop2 : (choicesAll.drop (idx * 2)).drop 2 = rest := by
                        simp [hDrop]
                      simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                        using hDrop2.symm
                    have hSmall : len - (idx * 2 + 2) < n := by
                      omega
                    rcases ih (len - (idx * 2 + 2)) hSmall (idx * 2 + 2) rfl hleNext
                        hEvenNext with
                      ⟨restBits, hRestDecode0⟩
                    have hRestDecode :
                        tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest =
                          some restBits := by
                      simpa [hRestDrop] using hRestDecode0
                    refine ⟨false :: restBits, ?_⟩
                    simp [hDrop, tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse,
                      hDelimiter, hRestDecode]
              · have hTrue :
                    choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
                  rcases hAllowed with hAllowedEmpty | hAllowedBit
                  · exact False.elim (hEmpty hAllowedEmpty)
                  · rcases hAllowedBit with hAllowedFalse | hAllowedTrue
                    · exact False.elim (hFalse hAllowedFalse)
                    · exact hAllowedTrue
                have hBit :
                    choicesAll[idx * 2]'(by simpa [choicesAll] using hidx) ∈
                      tmVerifierFiniteBoolBitChoices V bitSymbol := by
                  rw [← hHeadEq]
                  rw [tmVerifierFiniteBoolBitChoices]
                  exact List.mem_append_right
                    (tmVerifierCertificateRightReadChoices V (bitSymbol false)) hTrue
                have hnext :
                    idx * 2 + 1 < E.decodedInitialCertificateChoicePrefix.length :=
                  E.decodedInitialCertificateChoicePrefix_finiteBool_bit_has_successor
                    bitSymbol delimiterSymbol hSuffix hidx hBit
                cases tail with
                | nil =>
                    have hLenDrop := congrArg List.length hDrop
                    have hDropLen : (choicesAll.drop (idx * 2)).length = len - idx * 2 := by
                      simp [len]
                    rw [hDropLen] at hLenDrop
                    simp at hLenDrop
                    have hnextLen : idx * 2 + 1 < len := by
                      simpa [choicesAll, len] using hnext
                    omega
                | cons delimiterChoice rest =>
                    have hTailHead? :
                        choicesAll[idx * 2 + 1]? = some delimiterChoice := by
                      have hDropHead :
                          (choicesAll.drop (idx * 2))[1]? = some delimiterChoice := by
                        simp [hDrop]
                      simpa [List.getElem?_drop, Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using hDropHead
                    have hTailEq :
                        delimiterChoice =
                          choicesAll[idx * 2 + 1]'(by simpa [choicesAll] using hnext) := by
                      have hOrig :
                          choicesAll[idx * 2 + 1]? =
                            some (choicesAll[idx * 2 + 1]'(by
                              simpa [choicesAll] using hnext)) :=
                        List.getElem?_eq_getElem (by simpa [choicesAll] using hnext)
                      rw [hOrig] at hTailHead?
                      exact (Option.some.inj hTailHead?).symm
                    have hDelimiter :
                        delimiterChoice ∈
                          tmVerifierCertificateRightReadChoices V delimiterSymbol := by
                      have hDelim0 :=
                        E.decodedInitialCertificateChoicePrefix_finiteBool_delimiter_successor
                          bitSymbol delimiterSymbol hSuffix hidx hnext hBit
                      simpa [hTailEq] using hDelim0
                    have hleNext : idx * 2 + 2 ≤ len := by
                      simpa [choicesAll, len] using Nat.succ_le_of_lt hnext
                    have hEvenNext : ∃ j : Nat, idx * 2 + 2 = j * 2 := by
                      refine ⟨idx + 1, ?_⟩
                      omega
                    have hRestDrop : rest = choicesAll.drop (idx * 2 + 2) := by
                      have hDrop2 : (choicesAll.drop (idx * 2)).drop 2 = rest := by
                        simp [hDrop]
                      simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                        using hDrop2.symm
                    have hSmall : len - (idx * 2 + 2) < n := by
                      omega
                    rcases ih (len - (idx * 2 + 2)) hSmall (idx * 2 + 2) rfl hleNext
                        hEvenNext with
                      ⟨restBits, hRestDecode0⟩
                    have hRestDecode :
                        tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol rest =
                          some restBits := by
                      simpa [hRestDrop] using hRestDecode0
                    refine ⟨true :: restBits, ?_⟩
                    simp [hDrop, tmVerifierFiniteBoolChoicePrefixDecode, hEmpty, hFalse,
                      hTrue, hDelimiter, hRestDecode]

/-- The whole decoded certificate choice window is accepted by the finite-Boolean decoder. -/
theorem decodedInitialCertificateChoicePrefix_finiteBoolChoicePrefixDecode
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a) :
    ∃ bits : List Bool,
      tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol
        E.decodedInitialCertificateChoicePrefix = some bits := by
  simpa using
    E.decodedInitialCertificateChoicePrefix_finiteBoolChoicePrefixDecode_drop
      bitSymbol delimiterSymbol hSuffix (offset := 0) (by omega) ⟨0, by simp⟩

/--
The assignment-level decoded suffix word has the certificate-symbol stream
returned by the finite-Boolean choice decoder.
-/
theorem decodedInitialCertificateSuffixWord_finiteBoolDecode_symbols
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    (hSuffix :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a) :
    ∃ bits : List Bool,
      tmVerifierFiniteBoolChoicePrefixDecode V bitSymbol delimiterSymbol
          E.decodedInitialCertificateChoicePrefix = some bits ∧
        E.decodedInitialCertificateSuffixWord.map
            (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierFiniteBoolCertificateSymbols bitSymbol delimiterSymbol bits).map
            fun s => some (Sum.inr s) := by
  rcases E.decodedInitialCertificateChoicePrefix_finiteBoolChoicePrefixDecode
      bitSymbol delimiterSymbol hSuffix with
    ⟨bits, hDecode⟩
  refine ⟨bits, hDecode, ?_⟩
  have hSymbols :=
    tmVerifierFiniteBoolChoicePrefixDecode_sound_symbols V bitSymbol delimiterSymbol
      hDecode
  have hWord :
      tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
        E.decodedInitialCertificateSuffixWord := by
    simpa [tmVerifierXOnlyInputChoicePrefixWord] using
      E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  rw [← hWord]
  exact hSymbols

theorem decodedInitialCertificateSuffixWord_length_le_certificateSizeBound
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    E.decodedInitialCertificateSuffixWord.length ≤ tmVerifierCertificateSizeBound V x := by
  have hWord :
      tmVerifierReadChoicePrefixToStack E.decodedInitialCertificateChoicePrefix =
        E.decodedInitialCertificateSuffixWord := by
    simpa [tmVerifierXOnlyInputChoicePrefixWord] using
      E.decodedInitialCertificateChoicePrefix_word_eq_decoded_suffix
  rw [← hWord]
  exact Nat.le_trans
    (tmVerifierReadChoicePrefixToStack_length_le E.decodedInitialCertificateChoicePrefix)
    (by rw [E.decodedInitialCertificateChoicePrefix_length])

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
