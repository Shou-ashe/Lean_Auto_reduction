/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyNatListSuffixPatternTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackListEffects
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.SetSystem

/-!
Certificate-level decoder for unary natural-list suffixes.

This file supplies the structural decoder for `EncodedType.list EncodedType.nat`
certificate streams.  It is intentionally only the certificate-image parser;
the assignment-level CNF bridge is layered on top of the local pattern CNF.
-/

namespace ComplexityReduction
namespace SAT

open Combinatorics

noncomputable local instance natListSuffixDecoderDecidableProp (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

abbrev natListCertificateSymbol : Type :=
  Option EncodedType.nat.Symbol

theorem natList_replicate_append_cons {α : Type} (a : α) (n : Nat) (tail : List α) :
    List.replicate n a ++ a :: tail = List.replicate (n + 1) a ++ tail := by
  induction n generalizing tail with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg (fun xs => a :: xs) (ih tail)

theorem natList_append_singleton_cons {α : Type} (pref : List α) (a : α)
    (tail : List α) :
    pref ++ [a] ++ tail = pref ++ a :: tail := by
  simp [List.append_assoc]

/-! ### Symbol stream for unary natural lists -/

/-- Certificate-symbol stream represented by a decoded unary natural list. -/
def tmVerifierNatListCertificateSymbols
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (xs : List Nat) : List V.Cert.Symbol :=
  xs.flatMap fun n => List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol]

@[simp]
theorem tmVerifierNatListCertificateSymbols_nil
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol delimiterSymbol [] =
      [] :=
  rfl

@[simp]
theorem tmVerifierNatListCertificateSymbols_cons
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (n : Nat) (xs : List Nat) :
    tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol delimiterSymbol
        (n :: xs) =
      List.replicate n trueSymbol ++ [falseSymbol, delimiterSymbol] ++
        tmVerifierNatListCertificateSymbols (V := V) trueSymbol falseSymbol
          delimiterSymbol xs := by
  simp [tmVerifierNatListCertificateSymbols, List.append_assoc]

/-! ### Structural decoder -/

mutual

/-- Decode a full `EncodedType.list EncodedType.nat` symbol stream. -/
def natListCertDecode : List natListCertificateSymbol → Option (List Nat)
  | [] => some []
  | none :: _ => none
  | some true :: rest => natListCertDecodeNat 1 rest
  | some false :: none :: rest =>
      (natListCertDecode rest).map fun xs => 0 :: xs
  | some false :: _ => none

/-- Decode the remainder of one unary natural after `seen` true symbols. -/
def natListCertDecodeNat (seen : Nat) :
    List natListCertificateSymbol → Option (List Nat)
  | [] => none
  | none :: _ => none
  | some true :: rest => natListCertDecodeNat (seen + 1) rest
  | some false :: none :: rest =>
      (natListCertDecode rest).map fun xs => seen :: xs
  | some false :: _ => none

end

mutual

theorem natListCertDecode_sound :
    ∀ {symbols : List natListCertificateSymbol} {xs : List Nat},
      natListCertDecode symbols = some xs →
        symbols = (EncodedType.list EncodedType.nat).encode xs
  | [], xs, h => by
      cases h
      rfl
  | none :: _rest, _xs, h => by
      cases h
  | some true :: rest, xs, h => by
      have hNat := natListCertDecodeNat_sound (seen := 1) h
      simpa [natListCertDecode] using hNat
  | some false :: [], _xs, h => by
      cases h
  | some false :: none :: rest, xs, h => by
      cases hRest : natListCertDecode rest with
      | none =>
          simp [natListCertDecode, hRest] at h
      | some restXs =>
          have hxs : 0 :: restXs = xs := by
            simpa [natListCertDecode, hRest] using h
          subst xs
          have hRestSound := natListCertDecode_sound hRest
          rw [hRestSound]
          rfl
  | some false :: some _ :: _rest, _xs, h => by
      cases h

theorem natListCertDecodeNat_sound :
    ∀ {symbols : List natListCertificateSymbol} {xs : List Nat} {seen : Nat},
      natListCertDecodeNat seen symbols = some xs →
        List.replicate seen (some true : natListCertificateSymbol) ++ symbols =
          (EncodedType.list EncodedType.nat).encode xs
  | [], _xs, _seen, h => by
      cases h
  | none :: _rest, _xs, _seen, h => by
      cases h
  | some true :: rest, xs, seen, h => by
      have hTail := natListCertDecodeNat_sound (seen := seen + 1) h
      rw [natList_replicate_append_cons (some true : natListCertificateSymbol) seen rest]
      exact hTail
  | some false :: [], _xs, _seen, h => by
      cases h
  | some false :: none :: rest, xs, seen, h => by
      cases hRest : natListCertDecode rest with
      | none =>
          simp [natListCertDecodeNat, hRest] at h
      | some restXs =>
          have hxs : seen :: restXs = xs := by
            simpa [natListCertDecodeNat, hRest] using h
          subst xs
          have hRestSound := natListCertDecode_sound hRest
          rw [hRestSound]
          simp only [EncodedType.list, EncodedType.nat, List.flatMap_cons, List.map_append,
            List.map_cons, List.map_nil, List.map_replicate, List.cons_append,
            List.nil_append, List.append_assoc]
          rfl
  | some false :: some _ :: _rest, _xs, _seen, h => by
      cases h

end

theorem natListCertDecode_complete (xs : List Nat) :
    natListCertDecode ((EncodedType.list EncodedType.nat).encode xs) = some xs := by
  induction xs with
  | nil =>
      rfl
  | cons n xs ih =>
      have hNat :
          ∀ seen remaining : Nat,
            natListCertDecodeNat seen
              ((EncodedType.nat.encode remaining).map some ++
                none :: (EncodedType.list EncodedType.nat).encode xs) =
              some ((seen + remaining) :: xs) := by
        intro seen remaining
        induction remaining generalizing seen with
        | zero =>
            change
              natListCertDecodeNat seen
                (some false :: none :: (EncodedType.list EncodedType.nat).encode xs) =
                some ((seen + 0) :: xs)
            simp [natListCertDecodeNat, ih]
        | succ remaining ihRemaining =>
            change
              natListCertDecodeNat seen
                (some true ::
                  ((EncodedType.nat.encode remaining).map some ++
                    none :: (EncodedType.list EncodedType.nat).encode xs)) =
                some ((seen + Nat.succ remaining) :: xs)
            rw [natListCertDecodeNat]
            have h := ihRemaining (seen + 1)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      cases n with
      | zero =>
          change
            natListCertDecode
              (some false :: none :: (EncodedType.list EncodedType.nat).encode xs) =
              some (0 :: xs)
          simp [natListCertDecode, ih]
      | succ n =>
          have h := hNat 1 n
          have hBase :
              natListCertDecodeNat 1
                (List.replicate n (some true : natListCertificateSymbol) ++
                  [(some false : natListCertificateSymbol)] ++
                    (none : natListCertificateSymbol) ::
                      (EncodedType.list EncodedType.nat).encode xs) =
                some ((n + 1) :: xs) := by
            simpa [EncodedType.nat, List.map_append, List.map_replicate, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using h
          have h' :
              natListCertDecodeNat 1
                (List.replicate n (some true : natListCertificateSymbol) ++
                  (some false : natListCertificateSymbol) ::
                    (none : natListCertificateSymbol) ::
                      (EncodedType.list EncodedType.nat).encode xs) =
                some ((n + 1) :: xs) := by
            simpa [natList_append_singleton_cons, List.cons_append, List.nil_append] using hBase
          simpa [EncodedType.list, EncodedType.nat, natListCertDecode,
            List.replicate_succ, List.append_assoc, Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using h'

theorem natListCertDecodeNat_complete (seen remaining : Nat) (xs : List Nat) :
    natListCertDecodeNat seen
        ((EncodedType.nat.encode remaining).map some ++
          none :: (EncodedType.list EncodedType.nat).encode xs) =
      some ((seen + remaining) :: xs) := by
  induction remaining generalizing seen with
  | zero =>
      change
        natListCertDecodeNat seen
          (some false :: none :: (EncodedType.list EncodedType.nat).encode xs) =
          some ((seen + 0) :: xs)
      simp [natListCertDecodeNat, natListCertDecode_complete]
  | succ remaining ih =>
      change
        natListCertDecodeNat seen
          (some true ::
            ((EncodedType.nat.encode remaining).map some ++
              none :: (EncodedType.list EncodedType.nat).encode xs)) =
          some ((seen + Nat.succ remaining) :: xs)
      rw [natListCertDecodeNat]
      have h := ih (seen + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem natListCertDecode_sound_setStructured
    {symbols : List natListCertificateSymbol} {xs : List Nat}
    (h : natListCertDecode symbols = some xs) :
    symbols = setStructuredEncodedType.encode xs := by
  simpa [setStructuredEncodedType] using natListCertDecode_sound h

theorem natListCertDecode_complete_setStructured (xs : List Nat) :
    natListCertDecode (setStructuredEncodedType.encode xs) = some xs := by
  simpa [setStructuredEncodedType] using natListCertDecode_complete xs

/-! ### Choice-level decoder for unary natural lists -/

def tmVerifierInputRightSymbol
    {L : EncodedDecisionProblem} {V : TMVerifier L} (s : V.Cert.Symbol) :
    (tmVerifierInputEncodedType V).Symbol :=
  some (Sum.inr s)

/--
If a read choice belongs to the right-symbol choice set, then the concrete word
projection starts with the corresponding product-right input symbol.
-/
theorem tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    {s : V.Cert.Symbol}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V s)
    (rest : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    (tmVerifierReadChoicePrefixToStack (choice :: rest)).map
        (tmVerifierComputableWitness V).inputAlphabet =
      tmVerifierInputRightSymbol (V := V) s ::
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

mutual

/--
Choice-level decoder for a unary natural-list suffix pattern.  It stops at the
first empty cell; otherwise each unary natural is a run of true symbols,
followed by false and the list delimiter.
-/
noncomputable def tmVerifierNatListChoicePrefixDecode
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) → Option (List Nat)
  | [] => some []
  | choice :: rest =>
      if choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) then
        some []
      else if choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol then
        tmVerifierNatListChoicePrefixDecodeNat V trueSymbol falseSymbol delimiterSymbol 1 rest
      else if choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol then
        match rest with
        | [] => none
        | delimiterChoice :: rest =>
            if delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol then
              (tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol
                rest).map fun xs => 0 :: xs
            else
              none
      else
        none

/-- Decode the rest of one unary natural after `seen` true choices. -/
noncomputable def tmVerifierNatListChoicePrefixDecodeNat
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) (seen : Nat) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) → Option (List Nat)
  | [] => none
  | choice :: rest =>
      if choice = (TMVerifierStackReadChoice.empty :
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀) then
        none
      else if choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol then
        tmVerifierNatListChoicePrefixDecodeNat V trueSymbol falseSymbol delimiterSymbol
          (seen + 1) rest
      else if choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol then
        match rest with
        | [] => none
        | delimiterChoice :: rest =>
            if delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol then
              (tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol
                rest).map fun xs => seen :: xs
            else
              none
      else
        none

end

mutual

theorem tmVerifierNatListChoicePrefixDecode_sound_symbols
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    ∀ {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
      {xs : List Nat},
      tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol delimiterSymbol choices =
          some xs →
        (tmVerifierReadChoicePrefixToStack choices).map
            (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierNatListCertificateSymbols trueSymbol falseSymbol delimiterSymbol xs).map
            (tmVerifierInputRightSymbol (V := V))
  | [], xs, hDecode => by
      cases hDecode
      rfl
  | choice :: rest, xs, hDecode => by
      rw [tmVerifierNatListChoicePrefixDecode.eq_def] at hDecode
      by_cases hEmpty :
          choice = (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
      · subst choice
        have hxs : xs = [] := by
          simpa using hDecode.symm
        subst xs
        rfl
      · by_cases hTrue :
            choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol
        · have hNat :=
            tmVerifierNatListChoicePrefixDecodeNat_sound_symbols V trueSymbol falseSymbol
              delimiterSymbol (seen := 1)
              (by
                simpa [hEmpty, hTrue] using hDecode)
          rw [tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
            (V := V) (s := trueSymbol) hTrue]
          simpa using hNat
        · by_cases hFalse :
              choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol
          · cases rest with
            | nil =>
                simp [hEmpty, hTrue, hFalse] at hDecode
            | cons delimiterChoice rest =>
                by_cases hDelimiter :
                    delimiterChoice ∈
                      tmVerifierCertificateRightReadChoices V delimiterSymbol
                · cases hRest :
                    tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol
                      delimiterSymbol rest with
                  | none =>
                      simp [tmVerifierNatListChoicePrefixDecode, hEmpty, hTrue, hFalse,
                        hDelimiter, hRest] at hDecode
                  | some restXs =>
                      have hxs : xs = 0 :: restXs := by
                        simpa [tmVerifierNatListChoicePrefixDecode, hEmpty, hTrue,
                          hFalse, hDelimiter, hRest] using hDecode.symm
                      subst xs
                      have hRestSound :=
                        tmVerifierNatListChoicePrefixDecode_sound_symbols V trueSymbol
                          falseSymbol delimiterSymbol hRest
                      rw [tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                        (V := V) (s := falseSymbol) hFalse]
                      have hDelimiterMap :=
                        tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                          (V := V) (choice := delimiterChoice) (s := delimiterSymbol)
                          hDelimiter rest
                      rw [hDelimiterMap, hRestSound]
                      simp [tmVerifierNatListCertificateSymbols, tmVerifierInputRightSymbol,
                        List.map_append]
                · simp [hEmpty, hTrue, hFalse, hDelimiter] at hDecode
          · simp [hEmpty, hTrue, hFalse] at hDecode

theorem tmVerifierNatListChoicePrefixDecodeNat_sound_symbols
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    ∀ {choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)}
      {xs : List Nat} {seen : Nat},
      tmVerifierNatListChoicePrefixDecodeNat V trueSymbol falseSymbol delimiterSymbol seen
          choices = some xs →
        List.replicate seen (tmVerifierInputRightSymbol (V := V) trueSymbol) ++
            (tmVerifierReadChoicePrefixToStack choices).map
              (tmVerifierComputableWitness V).inputAlphabet =
          (tmVerifierNatListCertificateSymbols trueSymbol falseSymbol delimiterSymbol xs).map
            (tmVerifierInputRightSymbol (V := V))
  | [], _xs, _seen, hDecode => by
      cases hDecode
  | choice :: rest, xs, seen, hDecode => by
      rw [tmVerifierNatListChoicePrefixDecodeNat.eq_def] at hDecode
      by_cases hEmpty :
          choice = (TMVerifierStackReadChoice.empty :
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀)
      · simp [hEmpty] at hDecode
      · by_cases hTrue :
            choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol
        · have hNat :=
            tmVerifierNatListChoicePrefixDecodeNat_sound_symbols V trueSymbol falseSymbol
              delimiterSymbol (seen := seen + 1)
              (by
                simpa [hEmpty, hTrue] using hDecode)
          rw [tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
            (V := V) (s := trueSymbol) hTrue]
          rw [natList_replicate_append_cons
            (tmVerifierInputRightSymbol (V := V) trueSymbol) seen
            ((tmVerifierReadChoicePrefixToStack rest).map
              (tmVerifierComputableWitness V).inputAlphabet)]
          exact hNat
        · by_cases hFalse :
              choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol
          · cases rest with
            | nil =>
                simp [tmVerifierNatListChoicePrefixDecodeNat, hEmpty, hTrue, hFalse]
                  at hDecode
            | cons delimiterChoice rest =>
                by_cases hDelimiter :
                    delimiterChoice ∈
                      tmVerifierCertificateRightReadChoices V delimiterSymbol
                · cases hRest :
                    tmVerifierNatListChoicePrefixDecode V trueSymbol falseSymbol
                      delimiterSymbol rest with
                  | none =>
                      simp [tmVerifierNatListChoicePrefixDecodeNat, hEmpty, hTrue,
                        hFalse, hDelimiter, hRest] at hDecode
                  | some restXs =>
                      have hxs : xs = seen :: restXs := by
                        simpa [tmVerifierNatListChoicePrefixDecodeNat, hEmpty, hTrue,
                          hFalse, hDelimiter, hRest] using hDecode.symm
                      subst xs
                      have hRestSound :=
                        tmVerifierNatListChoicePrefixDecode_sound_symbols V trueSymbol
                          falseSymbol delimiterSymbol hRest
                      rw [tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                        (V := V) (s := falseSymbol) hFalse]
                      have hDelimiterMap :=
                        tmVerifierNatListReadChoicePrefixToStack_map_inputAlphabet_cons_of_rightChoice
                          (V := V) (choice := delimiterChoice) (s := delimiterSymbol)
                          hDelimiter rest
                      rw [hDelimiterMap, hRestSound]
                      simp [tmVerifierNatListCertificateSymbols, tmVerifierInputRightSymbol,
                        List.map_append, List.map_replicate, List.append_assoc]
                · simp [tmVerifierNatListChoicePrefixDecodeNat, hEmpty, hTrue, hFalse,
                    hDelimiter] at hDecode
          · simp [tmVerifierNatListChoicePrefixDecodeNat, hEmpty, hTrue, hFalse]
              at hDecode

end

end SAT
end ComplexityReduction
