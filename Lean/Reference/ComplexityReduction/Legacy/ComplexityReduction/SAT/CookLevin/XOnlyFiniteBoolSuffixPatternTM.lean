/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.ContextCNFFoldTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixDecoderTM

/-!
Direct local CNF shape for finite Boolean certificate suffixes.

The finite 3SAT verifiers use `List Bool` certificates.  Their certificate
encoding is the regular stream

* `some b`, then
* `none`,

for each Boolean bit.  This file records the local x-only input-stack clauses
that enforce that shape over the certificate window: at every bit position, the
selected stack choice is either empty or one of the two Boolean-symbol choices;
if a Boolean symbol is selected, the next cell must be the list delimiter.

The semantic bridge to `TMVerifierXOnlyCheckedSuffixDecoder` is intentionally
kept for a later file; this file is the reusable direct-CNF surface.
-/

namespace ComplexityReduction
namespace SAT

/-- The raw input-stack symbol for a certificate-side product symbol. -/
noncomputable def tmVerifierCertificateRightWordSymbol
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    (tmVerifierTM V).Γ (tmVerifierTM V).k₀ :=
  (tmVerifierComputableWitness V).inputAlphabet.invFun (some (Sum.inr s))

@[simp]
theorem tmVerifierCertificateRightWordSymbol_inputAlphabet
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    (tmVerifierComputableWitness V).inputAlphabet
      (tmVerifierCertificateRightWordSymbol V s) = some (Sum.inr s) := by
  simp [tmVerifierCertificateRightWordSymbol]

/-- The audited read-choice for a certificate-side product symbol. -/
noncomputable def tmVerifierCertificateRightReadChoice
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    TMVerifierStackReadChoice V (tmVerifierTM V).k₀ :=
  let w := tmVerifierCertificateRightWordSymbol V s
  TMVerifierStackReadChoice.symbol
    (tmVerifierActiveStackSymbolPayload V (tmVerifierTM V).k₀ w) w

theorem tmVerifierCertificateRightReadChoice_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    tmVerifierCertificateRightReadChoice V s ∈
      tmVerifierStackReadChoices V (tmVerifierTM V).k₀ := by
  dsimp [tmVerifierCertificateRightReadChoice]
  exact tmVerifierInputStackSymbol_choice_mem V (tmVerifierCertificateRightWordSymbol V s)

@[simp]
theorem tmVerifierCertificateRightReadChoice_toOption
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    (tmVerifierCertificateRightReadChoice V s).toOption =
      some (tmVerifierCertificateRightWordSymbol V s) := by
  rfl

/--
All read choices whose concrete stack symbol decodes as one certificate-side
product symbol.  We allow all such choices, not just the canonical input-symbol
payload, because the decoded suffix semantics is word-based.
-/
noncomputable def tmVerifierCertificateRightReadChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  classical
  exact (tmVerifierStackReadChoices V (tmVerifierTM V).k₀).filter fun choice =>
    choice.toOption.map (tmVerifierComputableWitness V).inputAlphabet =
      some (some (Sum.inr s))

theorem tmVerifierCertificateRightReadChoices_spec
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V s) :
    choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀ ∧
      choice.toOption.map (tmVerifierComputableWitness V).inputAlphabet =
        some (some (Sum.inr s)) := by
  classical
  simpa [tmVerifierCertificateRightReadChoices] using hChoice

theorem tmVerifierCertificateRightReadChoice_mem_rightChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : V.Cert.Symbol) :
    tmVerifierCertificateRightReadChoice V s ∈
      tmVerifierCertificateRightReadChoices V s := by
  classical
  exact List.mem_filter.mpr
    ⟨tmVerifierCertificateRightReadChoice_mem V s, by
      apply decide_eq_true
      change
        (tmVerifierCertificateRightReadChoice V s).toOption.map
            (tmVerifierComputableWitness V).inputAlphabet =
          some (some (Sum.inr s))
      rw [tmVerifierCertificateRightReadChoice_toOption]
      exact congrArg some (tmVerifierCertificateRightWordSymbol_inputAlphabet V s)⟩

/-- The allowed Boolean-symbol choices at a finite-assignment bit cell. -/
noncomputable def tmVerifierFiniteBoolBitChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
  tmVerifierCertificateRightReadChoices V (bitSymbol false) ++
    tmVerifierCertificateRightReadChoices V (bitSymbol true)

/--
Read choices forbidden at bit cells.  This list is finite and depends only on
the verifier, not on the instance; it is therefore a legitimate fixed table for
the direct generator.
-/
noncomputable def tmVerifierFiniteBoolInvalidBitChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  classical
  exact (tmVerifierStackReadChoices V (tmVerifierTM V).k₀).filter fun choice =>
    choice ≠ TMVerifierStackReadChoice.empty ∧
      choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∧
      choice ∉ tmVerifierCertificateRightReadChoices V (bitSymbol true)

theorem tmVerifierFiniteBoolInvalidBitChoices_spec
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hNotInvalid :
      choice ∉ tmVerifierFiniteBoolInvalidBitChoices V bitSymbol) :
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
  classical
  by_cases hEmpty : choice = TMVerifierStackReadChoice.empty
  · exact Or.inl hEmpty
  · right
    by_cases hFalse : choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false)
    · exact Or.inl hFalse
    · right
      by_cases hTrue : choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true)
      · exact hTrue
      · have hInvalid :
            choice ∈ tmVerifierFiniteBoolInvalidBitChoices V bitSymbol := by
          simp [tmVerifierFiniteBoolInvalidBitChoices, hChoice, hEmpty, hFalse, hTrue]
        exact False.elim (hNotInvalid hInvalid)

/-- Unit clauses forbidding all nonempty non-Boolean choices at a bit cell. -/
noncomputable def tmVerifierFiniteBoolInvalidBitChoiceClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (cell : Nat) : CNF :=
  tmVerifierUnitClauses <|
    (tmVerifierFiniteBoolInvalidBitChoices V bitSymbol).map fun choice =>
      Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice)

/-- If a Boolean symbol is selected at `cell`, the next cell is the delimiter. -/
noncomputable def tmVerifierFiniteBoolBitDelimiterClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (cell : Nat) : CNF :=
  (tmVerifierFiniteBoolBitChoices V bitSymbol).map fun choice =>
    [Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)] ++
      (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun delimiterChoice =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 (cell + 1) delimiterChoice

/-- Local finite-Boolean suffix clauses for one bit-position cell. -/
noncomputable def tmVerifierFiniteBoolBitCellCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (cell : Nat) : CNF :=
  tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell ++
    tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell

theorem tmVerifierFiniteBoolInvalidBitChoiceClausesAt_not_invalid_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    choice ∉ tmVerifierFiniteBoolInvalidBitChoices V bitSymbol := by
  intro hInvalid
  have hUnits :=
    (tmVerifierUnitClauses_satisfies
      ((tmVerifierFiniteBoolInvalidBitChoices V bitSymbol).map fun choice =>
        Clause.negate
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice)) a).1
      (by simpa [tmVerifierFiniteBoolInvalidBitChoiceClausesAt] using h)
  let lit :=
    Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)
  have hLit : lit.eval a = true := by
    exact hUnits lit (List.mem_map.mpr ⟨choice, hInvalid, rfl⟩)
  have hFalse :=
    (Clause.negate_eval_true_iff
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice) a).1 hLit
  simp [hAtom] at hFalse

theorem tmVerifierFiniteBoolBitCellCNFAt_allowed_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol false) ∨
      choice ∈ tmVerifierCertificateRightReadChoices V (bitSymbol true) := by
  have hInvalidCNF :
      CNF.Satisfies
        (tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell) a := by
    exact (CNF.satisfies_append
      (tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell)
      (tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell) a).1
      (by simpa [tmVerifierFiniteBoolBitCellCNFAt] using h) |>.1
  exact tmVerifierFiniteBoolInvalidBitChoices_spec V bitSymbol hChoice
    (tmVerifierFiniteBoolInvalidBitChoiceClausesAt_not_invalid_of_atom_true V bitSymbol
      hInvalidCNF hAtom)

theorem tmVerifierFiniteBoolBitDelimiterClausesAt_delimiter_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierFiniteBoolBitChoices V bitSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true := by
  let bitAtom :=
    TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell choice
  let delimiterLits :=
    (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun delimiterChoice =>
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice
  have hClause : Clause.Satisfies ([Clause.negate bitAtom] ++ delimiterLits) a := by
    exact h _ (by
      rw [tmVerifierFiniteBoolBitDelimiterClausesAt]
      exact List.mem_map.mpr ⟨choice, hChoice, rfl⟩)
  rcases hClause with ⟨lit, hlit, heval⟩
  rw [List.mem_append] at hlit
  rcases hlit with hNeg | hDelim
  · simp [bitAtom] at hNeg
    subst lit
    have hFalse := (Clause.negate_eval_true_iff bitAtom a).1 heval
    simp [bitAtom, hAtom] at hFalse
  · rcases List.mem_map.mp hDelim with ⟨delimiterChoice, hDelimiterChoice, rfl⟩
    exact ⟨delimiterChoice, hDelimiterChoice, heval⟩

theorem tmVerifierFiniteBoolBitCellCNFAt_delimiter_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierFiniteBoolBitChoices V bitSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true := by
  have hDelimiterCNF :
      CNF.Satisfies
        (tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell) a := by
    exact (CNF.satisfies_append
      (tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell)
      (tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell) a).1
      (by simpa [tmVerifierFiniteBoolBitCellCNFAt] using h) |>.2
  exact tmVerifierFiniteBoolBitDelimiterClausesAt_delimiter_of_atom_true V bitSymbol
    delimiterSymbol hDelimiterCNF hChoice hAtom

theorem tmVerifierFiniteBoolInvalidBitChoiceClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell) := by
  have hLits :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.list literalStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierFiniteBoolInvalidBitChoices V bitSymbol).map fun choice =>
            Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)) := by
    induction tmVerifierFiniteBoolInvalidBitChoices V bitSymbol with
    | nil =>
        exact TMPolyTimeMap.const EncodedType.nat
          (EncodedType.list literalStructuredEncodedType) []
    | cons choice choices ih =>
        have hHead :=
          tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
            (tmVerifierTM V).k₀ choice
        have hConsInput :
            TMPolyTimeMap EncodedType.nat
              (EncodedType.prod literalStructuredEncodedType
                (EncodedType.list literalStructuredEncodedType))
              (fun cell : Nat =>
                (Clause.negate
                    (TMVerifierStackReadChoice.atomAt
                      (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice),
                  choices.map fun choice =>
                    Clause.negate
                      (TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice))) :=
          TMPolyTimeMap.prod_mk hHead ih
        have hCons := TMPolyTimeMap.comp
          (TMPolyTimeMap.list_cons literalStructuredEncodedType) hConsInput
        simpa [Function.comp] using hCons
  have hCNF := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierFiniteBoolInvalidBitChoiceClausesAt] using hCNF

theorem tmVerifierFiniteBoolBitDelimiterClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell) := by
  have hSucc :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun cell : Nat => cell + 1) :=
    nat_add_const_tm_polytime 1
  have hDelimiterLits :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.list literalStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
            fun delimiterChoice =>
              TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) delimiterChoice) := by
    induction tmVerifierCertificateRightReadChoices V delimiterSymbol with
    | nil =>
        exact TMPolyTimeMap.const EncodedType.nat
          (EncodedType.list literalStructuredEncodedType) []
    | cons delimiterChoice delimiterChoices ih =>
        have hHead :
            TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
              (fun cell : Nat =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                  delimiterChoice) := by
          have hAtom :=
            tmVerifierStackReadChoice_atomAt_cell_tm_polytime V 0 (tmVerifierTM V).k₀
              delimiterChoice
          have hComp := TMPolyTimeMap.comp hAtom hSucc
          simpa [Function.comp] using hComp
        have hConsInput :
            TMPolyTimeMap EncodedType.nat
              (EncodedType.prod literalStructuredEncodedType
                (EncodedType.list literalStructuredEncodedType))
              (fun cell : Nat =>
                (TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                    delimiterChoice,
                  delimiterChoices.map fun delimiterChoice =>
                    TMVerifierStackReadChoice.atomAt
                      (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                      delimiterChoice)) :=
          TMPolyTimeMap.prod_mk hHead ih
        have hCons := TMPolyTimeMap.comp
          (TMPolyTimeMap.list_cons literalStructuredEncodedType) hConsInput
        simpa [Function.comp] using hCons
  have hOne
      (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun cell : Nat =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
              fun delimiterChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                  delimiterChoice) := by
    have hNeg :=
      tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0 (tmVerifierTM V).k₀ choice
    have hConsInput :
        TMPolyTimeMap EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType
            (EncodedType.list literalStructuredEncodedType))
          (fun cell : Nat =>
            (Clause.negate
                (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice),
              (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                fun delimiterChoice =>
                  TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                    delimiterChoice)) :=
      TMPolyTimeMap.prod_mk hNeg hDelimiterLits
    have hClause := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons literalStructuredEncodedType) hConsInput
    simpa [Function.comp] using hClause
  have hList :
      TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
        (fun cell : Nat =>
          (tmVerifierFiniteBoolBitChoices V bitSymbol).map fun choice =>
            [Clause.negate
                (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
              (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                fun delimiterChoice =>
                  TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                    delimiterChoice) := by
    induction tmVerifierFiniteBoolBitChoices V bitSymbol with
    | nil =>
        exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
    | cons choice choices ih =>
        have hHead := hOne choice
        have hAppendInput :
            TMPolyTimeMap EncodedType.nat
              (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
              (fun cell : Nat =>
                ([ [Clause.negate
                      (TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                    (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                      fun delimiterChoice =>
                        TMVerifierStackReadChoice.atomAt
                          (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                          delimiterChoice ],
                  choices.map fun choice =>
                    [Clause.negate
                        (TMVerifierStackReadChoice.atomAt
                          (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                      (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                        fun delimiterChoice =>
                          TMVerifierStackReadChoice.atomAt
                            (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                            delimiterChoice)) :=
          TMPolyTimeMap.prod_mk
            (TMPolyTimeMap.comp clauseSingletonTMBackedMap.tm_polytime hHead) ih
        have hAppend := TMPolyTimeMap.comp
          (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
        simpa [Function.comp, cnfStructuredEncodedType] using hAppend
  simpa [tmVerifierFiniteBoolBitDelimiterClausesAt, cnfStructuredEncodedType] using hList

theorem tmVerifierFiniteBoolBitCellCNFAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol cell) := by
  have hInvalid := tmVerifierFiniteBoolInvalidBitChoiceClausesAt_cell_tm_polytime V bitSymbol
  have hDelim :=
    tmVerifierFiniteBoolBitDelimiterClausesAt_cell_tm_polytime V bitSymbol delimiterSymbol
  have hInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierFiniteBoolInvalidBitChoiceClausesAt V bitSymbol cell,
            tmVerifierFiniteBoolBitDelimiterClausesAt V bitSymbol delimiterSymbol cell)) :=
    TMPolyTimeMap.prod_mk hInvalid hDelim
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hInput
  simpa [Function.comp, tmVerifierFiniteBoolBitCellCNFAt, cnfStructuredEncodedType]
    using hAppend

/--
Finite-Boolean suffix clauses for all candidate bit-start cells.  The `bound`
is the encoded certificate-symbol budget.  Iterating `bound` times is a
polynomial over-approximation; the `min` clips every redundant start back to
the first cell after the certificate window, where the global initial-stack
clauses already force emptiness.
-/
noncomputable def tmVerifierFiniteBoolSuffixPatternCNFForBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (start bound : Nat) : CNF :=
  (List.range bound).flatMap fun idx =>
    tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
      (start + Nat.min (idx * 2) bound)

/-- Instance-specialized finite-Boolean suffix pattern CNF. -/
noncomputable def tmVerifierFiniteBoolSuffixPatternCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierFiniteBoolSuffixPatternCNFForBound V bitSymbol delimiterSymbol
    (L.Instance.inputSize x + 1) (tmVerifierCertificateSizeBound V x)

theorem tmVerifierFiniteBoolSuffixPatternCNFForBound_bitCell_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {start bound idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNFForBound V bitSymbol delimiterSymbol
          start bound) a)
    (hidx : idx ∈ List.range bound) :
    CNF.Satisfies
      (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
        (start + Nat.min (idx * 2) bound)) a := by
  intro clause hclause
  exact h clause (by
    rw [tmVerifierFiniteBoolSuffixPatternCNFForBound]
    exact List.mem_flatMap.mpr ⟨idx, hidx, hclause⟩)

theorem tmVerifierFiniteBoolSuffixPatternCNF_bitCell_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol)
    {x : L.Instance.Carrier} {idx : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) a)
    (hidx : idx < tmVerifierCertificateSizeBound V x) :
    CNF.Satisfies
      (tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
        (L.Instance.inputSize x + 1 +
          Nat.min (idx * 2) (tmVerifierCertificateSizeBound V x))) a := by
  exact tmVerifierFiniteBoolSuffixPatternCNFForBound_bitCell_satisfies V bitSymbol
    delimiterSymbol (by simpa [tmVerifierFiniteBoolSuffixPatternCNF] using h)
    (by simpa using hidx)

theorem nat_min_tm_polytime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat (fun p : Nat × Nat => Nat.min p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hA : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hB : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSubInput₁ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hA hB
  have hSub₁ : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat => p.1 - p.2) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput₁
    simpa [Function.comp, X] using hComp
  have hSubInput₂ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1, p.1 - p.2)) :=
    TMPolyTimeMap.prod_mk hA hSub₁
  have hSub₂ : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × Nat => p.1 - (p.1 - p.2)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput₂
    simpa [Function.comp, X] using hComp
  convert hSub₂ using 1
  ext p
  by_cases h : p.1 ≤ p.2
  · simp [Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]
  · have hle : p.2 ≤ p.1 := Nat.le_of_not_ge h
    simp [Nat.min_eq_right hle, Nat.sub_sub_self hle]

theorem tmVerifierFiniteBoolBitCellCNFAt_index_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      cnfStructuredEncodedType
      (fun p : (Nat × Nat) × Nat =>
        tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
          (p.1.1 + Nat.min (p.2 * 2) p.1.2)) := by
  let C := EncodedType.prod EncodedType.nat EncodedType.nat
  let X := EncodedType.prod C EncodedType.nat
  have hContext : TMPolyTimeMap X C (fun p : (Nat × Nat) × Nat => p.1) := by
    simpa [X, C] using TMPolyTimeMap.fst C EncodedType.nat
  have hStart : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hContext
    simpa [Function.comp, X, C] using hComp
  have hBound : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hContext
    simpa [Function.comp, X, C] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : (Nat × Nat) × Nat => p.2) := by
    simpa [X, C] using TMPolyTimeMap.snd C EncodedType.nat
  have hDouble : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.2 * 2) := by
    have hMul := nat_mul_const_tm_polytime 2
    have hComp := TMPolyTimeMap.comp hMul hIdx
    simpa [Function.comp, X] using hComp
  have hMinInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : (Nat × Nat) × Nat => (p.2 * 2, p.1.2)) :=
    TMPolyTimeMap.prod_mk hDouble hBound
  have hMin : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => Nat.min (p.2 * 2) p.1.2) := by
    have hComp := TMPolyTimeMap.comp nat_min_tm_polytime hMinInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : (Nat × Nat) × Nat => (p.1.1, Nat.min (p.2 * 2) p.1.2)) :=
    TMPolyTimeMap.prod_mk hStart hMin
  have hCell : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.1.1 + Nat.min (p.2 * 2) p.1.2) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
    simpa [Function.comp, natAddInputEncodedType, X] using hComp
  have hBlock :=
    tmVerifierFiniteBoolBitCellCNFAt_cell_tm_polytime V bitSymbol delimiterSymbol
  have hComp := TMPolyTimeMap.comp hBlock hCell
  simpa [Function.comp, X] using hComp

theorem tmVerifierFiniteBoolSuffixPatternCNFForBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        tmVerifierFiniteBoolSuffixPatternCNFForBound V bitSymbol delimiterSymbol p.1 p.2) := by
  let C := EncodedType.prod EncodedType.nat EncodedType.nat
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  let block : (Nat × Nat) → Nat → CNF :=
    fun ctx idx =>
      tmVerifierFiniteBoolBitCellCNFAt V bitSymbol delimiterSymbol
        (ctx.1 + Nat.min (idx * 2) ctx.2)
  have hBlock :
      TMPolyTimeMap (EncodedType.prod C EncodedType.nat)
        cnfStructuredEncodedType
        (fun p : (Nat × Nat) × Nat => block p.1 p.2) := by
    simpa [block] using
      tmVerifierFiniteBoolBitCellCNFAt_index_tm_polytime V bitSymbol delimiterSymbol
  have hFlat :=
    cnfContextFlatMap_tm_polytime
      (C := C) (X := EncodedType.nat) block hBlock
  have hStart : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun p : Nat × Nat => List.range p.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod C (EncodedType.list EncodedType.nat))
        (fun p : Nat × Nat => ((p.1, p.2), List.range p.2)) := by
    have hContext : TMPolyTimeMap X C (fun p : Nat × Nat => (p.1, p.2)) :=
      TMPolyTimeMap.prod_mk hStart hBound
    exact TMPolyTimeMap.prod_mk hContext hRange
  have hComp := TMPolyTimeMap.comp hFlat hInput
  simpa [Function.comp, tmVerifierFiniteBoolSuffixPatternCNFForBound, block, C, X]
    using hComp

theorem tmVerifierFiniteBoolSuffixPatternCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (bitSymbol : Bool → V.Cert.Symbol) (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierFiniteBoolSuffixPatternCNF V bitSymbol delimiterSymbol x) := by
  have hSize :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => L.Instance.inputSize x) :=
    (encodedInputSizeNatTMBackedMap L.Instance).tm_polytime
  have hPrefix :
      TMPolyTimeMap L.Instance EncodedType.nat
        (fun x : L.Instance.Carrier => L.Instance.inputSize x + 1) := by
    have hAdd := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hAdd hSize
    simpa [Function.comp] using hComp
  have hBound := tmVerifierCertificateSizeBound_tm_polytime V
  have hInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun x : L.Instance.Carrier =>
          (L.Instance.inputSize x + 1, tmVerifierCertificateSizeBound V x)) :=
    TMPolyTimeMap.prod_mk hPrefix hBound
  have hPattern :=
    tmVerifierFiniteBoolSuffixPatternCNFForBound_tm_polytime V bitSymbol delimiterSymbol
  have hComp := TMPolyTimeMap.comp hPattern hInput
  simpa [Function.comp, tmVerifierFiniteBoolSuffixPatternCNF] using hComp

end SAT
end ComplexityReduction
