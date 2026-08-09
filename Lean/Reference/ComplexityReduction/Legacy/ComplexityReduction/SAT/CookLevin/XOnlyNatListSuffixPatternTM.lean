/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolSuffixPatternTM

/-!
Direct local CNF shape for unary natural-list certificate suffixes.

For certificates encoded as `EncodedType.list EncodedType.nat`, the certificate
symbol stream is

* zero or more `true` symbols,
* one terminating `false` symbol,
* one list-element delimiter,

repeated once for each natural number.  This file records the x-only initial
input-stack clauses that enforce that local regular shape over the certificate
window.  It is the non-Boolean analogue of `XOnlyFiniteBoolSuffixPatternTM`.
-/

namespace ComplexityReduction
namespace SAT

noncomputable local instance natListSuffixPatternDecidableProp (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

/-! ### Fixed right-symbol choice sets -/

/-- Choices allowed at a unary-natural-list certificate cell. -/
noncomputable def tmVerifierNatListSymbolChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :=
  tmVerifierCertificateRightReadChoices V trueSymbol ++
    tmVerifierCertificateRightReadChoices V falseSymbol ++
      tmVerifierCertificateRightReadChoices V delimiterSymbol

/-- Nonempty choices that are not one of the three unary-list certificate symbols. -/
noncomputable def tmVerifierNatListInvalidSymbolChoices
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) := by
  classical
  exact (tmVerifierStackReadChoices V (tmVerifierTM V).k₀).filter fun choice =>
    choice ≠ TMVerifierStackReadChoice.empty ∧
      choice ∉ tmVerifierCertificateRightReadChoices V trueSymbol ∧
        choice ∉ tmVerifierCertificateRightReadChoices V falseSymbol ∧
          choice ∉ tmVerifierCertificateRightReadChoices V delimiterSymbol

theorem tmVerifierNatListInvalidSymbolChoices_spec
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hNotInvalid :
      choice ∉ tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol) :
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol ∨
        choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol ∨
          choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  classical
  by_cases hEmpty : choice = TMVerifierStackReadChoice.empty
  · exact Or.inl hEmpty
  · right
    by_cases hTrue : choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol
    · exact Or.inl hTrue
    · right
      by_cases hFalse : choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol
      · exact Or.inl hFalse
      · right
        by_cases hDelimiter :
            choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol
        · exact hDelimiter
        · have hInvalid :
              choice ∈
                tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol
                  delimiterSymbol := by
            simp [tmVerifierNatListInvalidSymbolChoices, hChoice, hEmpty, hTrue, hFalse,
              hDelimiter]
          exact False.elim (hNotInvalid hInvalid)

/-! ### Local clauses -/

/-- Unit clauses forbidding all nonempty non-unary-list symbols at one cell. -/
noncomputable def tmVerifierNatListInvalidSymbolChoiceClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  tmVerifierUnitClauses <|
    (tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol).map
      fun choice =>
        Clause.negate
          (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice)

/-- If a `true` unary payload is selected, the next cell must continue or end the number. -/
noncomputable def tmVerifierNatListTrueContinuationClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  (tmVerifierCertificateRightReadChoices V trueSymbol).map fun choice =>
    [Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)] ++
      ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
        (tmVerifierCertificateRightReadChoices V falseSymbol)).map fun nextChoice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 (cell + 1) nextChoice

/-- If a `false` unary terminator is selected, the next cell must be the list delimiter. -/
noncomputable def tmVerifierNatListFalseDelimiterClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  (tmVerifierCertificateRightReadChoices V falseSymbol).map fun choice =>
    [Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)] ++
      (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun delimiterChoice =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 (cell + 1) delimiterChoice

/-- The first certificate cell cannot be a list-element delimiter. -/
noncomputable def tmVerifierNatListStartDelimiterClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (delimiterSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  tmVerifierUnitClauses <|
    (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun choice =>
      Clause.negate
        (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 cell choice)

/-- Any delimiter cell must be immediately preceded by a `false` unary terminator. -/
noncomputable def tmVerifierNatListDelimiterPreviousClausesAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun choice =>
    [Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)] ++
      (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 (cell - 1) falseChoice

/-- Main per-cell unary-list clauses: symbol alphabet plus forward transitions. -/
noncomputable def tmVerifierNatListMainCellCNFAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) (cell : Nat) : CNF :=
  tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol delimiterSymbol cell ++
    tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell ++
      tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell

/-- All local unary-list clauses for a bounded certificate window. -/
noncomputable def tmVerifierNatListSuffixPatternCNFForBound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (start bound : Nat) : CNF :=
  ((List.range bound).flatMap fun idx =>
    tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
      (start + Nat.min idx bound)) ++
    tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol start ++
      ((List.range bound).flatMap fun idx =>
        tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
          (start + Nat.min (idx + 1) bound))

/-- Instance-specialized unary-natural-list suffix pattern CNF. -/
noncomputable def tmVerifierNatListSuffixPatternCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    (x : L.Instance.Carrier) : CNF :=
  tmVerifierNatListSuffixPatternCNFForBound V trueSymbol falseSymbol delimiterSymbol
    (L.Instance.inputSize x + 1) (tmVerifierCertificateSizeBound V x)

/-! ### Assignment-level consequences of local clauses -/

theorem tmVerifierNatListInvalidSymbolChoiceClausesAt_not_invalid_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
          delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    choice ∉ tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol := by
  intro hInvalid
  have hUnits :=
    (tmVerifierUnitClauses_satisfies
      ((tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol).map
        fun choice =>
          Clause.negate
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 cell choice)) a).1
      (by
        simpa [tmVerifierNatListInvalidSymbolChoiceClausesAt] using h)
  let lit :=
    Clause.negate
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice)
  have hLit : lit.eval a = true :=
    hUnits lit (List.mem_map.mpr ⟨choice, hInvalid, rfl⟩)
  have hFalse :=
    (Clause.negate_eval_true_iff
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice) a).1 hLit
  simp [hAtom] at hFalse

theorem tmVerifierNatListMainCellCNFAt_allowed_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol)
    {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierStackReadChoices V (tmVerifierTM V).k₀)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    choice = TMVerifierStackReadChoice.empty ∨
      choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol ∨
        choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol ∨
          choice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol := by
  have hInvalidCNF :
      CNF.Satisfies
        (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
          delimiterSymbol cell) a := by
    have h₁ := (CNF.satisfies_append
      (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
        delimiterSymbol cell)
      (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell ++
        tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a).1
      (by
        simpa [tmVerifierNatListMainCellCNFAt, List.append_assoc] using h)
    exact h₁.1
  exact tmVerifierNatListInvalidSymbolChoices_spec V trueSymbol falseSymbol delimiterSymbol
    hChoice
    (tmVerifierNatListInvalidSymbolChoiceClausesAt_not_invalid_of_atom_true V trueSymbol
      falseSymbol delimiterSymbol hInvalidCNF hAtom)

theorem tmVerifierNatListTrueContinuationClausesAt_next_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol : V.Cert.Symbol) {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V trueSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ nextChoice ∈
        tmVerifierCertificateRightReadChoices V trueSymbol ++
          tmVerifierCertificateRightReadChoices V falseSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) nextChoice).eval a = true := by
  let headAtom :=
    TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell choice
  let nextLits :=
    ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
      (tmVerifierCertificateRightReadChoices V falseSymbol)).map fun nextChoice =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 (cell + 1) nextChoice
  have hClause : Clause.Satisfies ([Clause.negate headAtom] ++ nextLits) a := by
    exact h _ (by
      rw [tmVerifierNatListTrueContinuationClausesAt]
      exact List.mem_map.mpr ⟨choice, hChoice, rfl⟩)
  rcases hClause with ⟨lit, hlit, heval⟩
  rw [List.mem_append] at hlit
  rcases hlit with hNeg | hNext
  · simp [headAtom] at hNeg
    subst lit
    have hFalse := (Clause.negate_eval_true_iff headAtom a).1 heval
    simp [headAtom, hAtom] at hFalse
  · rcases List.mem_map.mp hNext with ⟨nextChoice, hNextChoice, rfl⟩
    exact ⟨nextChoice, hNextChoice, heval⟩

theorem tmVerifierNatListFalseDelimiterClausesAt_delimiter_of_atom_true
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) {cell : Nat} {a : Assignment}
    (h :
      CNF.Satisfies
        (tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) a)
    {choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀}
    (hChoice : choice ∈ tmVerifierCertificateRightReadChoices V falseSymbol)
    (hAtom :
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 cell choice).eval a = true) :
    ∃ delimiterChoice ∈ tmVerifierCertificateRightReadChoices V delimiterSymbol,
      (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice).eval a = true := by
  let headAtom :=
    TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
      0 cell choice
  let delimiterLits :=
    (tmVerifierCertificateRightReadChoices V delimiterSymbol).map fun delimiterChoice =>
      TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
        0 (cell + 1) delimiterChoice
  have hClause : Clause.Satisfies ([Clause.negate headAtom] ++ delimiterLits) a := by
    exact h _ (by
      rw [tmVerifierNatListFalseDelimiterClausesAt]
      exact List.mem_map.mpr ⟨choice, hChoice, rfl⟩)
  rcases hClause with ⟨lit, hlit, heval⟩
  rw [List.mem_append] at hlit
  rcases hlit with hNeg | hDelimiter
  · simp [headAtom] at hNeg
    subst lit
    have hFalse := (Clause.negate_eval_true_iff headAtom a).1 heval
    simp [headAtom, hAtom] at hFalse
  · rcases List.mem_map.mp hDelimiter with ⟨delimiterChoice, hDelimiterChoice, rfl⟩
    exact ⟨delimiterChoice, hDelimiterChoice, heval⟩

/-! ### Direct polynomial-time generation -/

theorem nat_sub_const_tm_polytime (k : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n - k) := by
  have hRight :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => k) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat k
  have hInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun n : Nat => (n, k)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hRight
  have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hInput
  simpa [Function.comp] using hComp

theorem tmVerifierCertificateRightChoiceAtomsAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat =>
        (tmVerifierCertificateRightReadChoices V s).map fun choice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 cell choice) := by
  induction tmVerifierCertificateRightReadChoices V s with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons choice choices ih =>
      have hHead :=
        tmVerifierStackReadChoice_atomAt_cell_tm_polytime V 0 (tmVerifierTM V).k₀ choice
      have hInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod literalStructuredEncodedType
              (EncodedType.list literalStructuredEncodedType))
            (fun cell : Nat =>
              (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice,
                choices.map fun choice =>
                  TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)) :=
        TMPolyTimeMap.prod_mk hHead ih
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
      simpa [Function.comp] using hCons

theorem tmVerifierCertificateRightChoiceNegAtomsAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat =>
        (tmVerifierCertificateRightReadChoices V s).map fun choice =>
          Clause.negate
            (TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 cell choice)) := by
  induction tmVerifierCertificateRightReadChoices V s with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat
        (EncodedType.list literalStructuredEncodedType) []
  | cons choice choices ih =>
      have hHead :=
        tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
          (tmVerifierTM V).k₀ choice
      have hInput :
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
        (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
      simpa [Function.comp] using hCons

theorem tmVerifierCertificateRightChoiceAtomsAt_succ_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat =>
        (tmVerifierCertificateRightReadChoices V s).map fun choice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 (cell + 1) choice) := by
  have hSucc :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun cell : Nat => cell + 1) :=
    nat_add_const_tm_polytime 1
  have hAtoms := tmVerifierCertificateRightChoiceAtomsAt_cell_tm_polytime V s
  have hComp := TMPolyTimeMap.comp hAtoms hSucc
  simpa [Function.comp] using hComp

theorem tmVerifierNatListInvalidSymbolChoiceClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
          delimiterSymbol cell) := by
  have hLits :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.list literalStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol).map
            fun choice =>
              Clause.negate
                (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)) := by
    induction tmVerifierNatListInvalidSymbolChoices V trueSymbol falseSymbol delimiterSymbol with
    | nil =>
        exact TMPolyTimeMap.const EncodedType.nat
          (EncodedType.list literalStructuredEncodedType) []
    | cons choice choices ih =>
        have hHead :=
          tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
            (tmVerifierTM V).k₀ choice
        have hInput :
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
          (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
        simpa [Function.comp] using hCons
  have hCNF := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierNatListInvalidSymbolChoiceClausesAt] using hCNF

theorem tmVerifierCertificateRightChoiceAtomsAt_pred_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) (s : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
      (fun cell : Nat =>
        (tmVerifierCertificateRightReadChoices V s).map fun choice =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 (cell - 1) choice) := by
  have hPred :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun cell : Nat => cell - 1) :=
    nat_sub_const_tm_polytime 1
  have hAtoms := tmVerifierCertificateRightChoiceAtomsAt_cell_tm_polytime V s
  have hComp := TMPolyTimeMap.comp hAtoms hPred
  simpa [Function.comp] using hComp

theorem tmVerifierNatListTrueContinuationClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell) := by
  have hTrueNext :=
    tmVerifierCertificateRightChoiceAtomsAt_succ_cell_tm_polytime V trueSymbol
  have hFalseNext :=
    tmVerifierCertificateRightChoiceAtomsAt_succ_cell_tm_polytime V falseSymbol
  have hNext :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.list literalStructuredEncodedType)
        (fun cell : Nat =>
          ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
            (tmVerifierCertificateRightReadChoices V falseSymbol)).map fun nextChoice =>
              TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) nextChoice) := by
    have hInput :
        TMPolyTimeMap EncodedType.nat
          (EncodedType.prod
            (EncodedType.list literalStructuredEncodedType)
            (EncodedType.list literalStructuredEncodedType))
          (fun cell : Nat =>
            ((tmVerifierCertificateRightReadChoices V trueSymbol).map fun nextChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) nextChoice,
              (tmVerifierCertificateRightReadChoices V falseSymbol).map fun nextChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) nextChoice)) :=
      TMPolyTimeMap.prod_mk hTrueNext hFalseNext
    have hAppend := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hInput
    simpa [Function.comp, List.map_append] using hAppend
  have hOne
      (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun cell : Nat =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
              (tmVerifierCertificateRightReadChoices V falseSymbol)).map fun nextChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) nextChoice) := by
    have hHead :=
      tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
        (tmVerifierTM V).k₀ choice
    have hInput :
        TMPolyTimeMap EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType
            (EncodedType.list literalStructuredEncodedType))
          (fun cell : Nat =>
            (Clause.negate
                (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice),
              ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
                (tmVerifierCertificateRightReadChoices V falseSymbol)).map
                  fun nextChoice =>
                    TMVerifierStackReadChoice.atomAt
                      (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                      nextChoice)) :=
      TMPolyTimeMap.prod_mk hHead hNext
    have hCons := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
    simpa [Function.comp] using hCons
  let choices := tmVerifierCertificateRightReadChoices V trueSymbol
  change
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        choices.map fun choice =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
              (tmVerifierCertificateRightReadChoices V falseSymbol)).map
                fun nextChoice =>
                  TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1) nextChoice)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := hOne choice
      have hInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun cell : Nat =>
              ([Clause.negate
                  (TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
                  (tmVerifierCertificateRightReadChoices V falseSymbol)).map
                    fun nextChoice =>
                      TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                        nextChoice,
                choices.map fun choice =>
                  [Clause.negate
                      (TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                    ((tmVerifierCertificateRightReadChoices V trueSymbol) ++
                      (tmVerifierCertificateRightReadChoices V falseSymbol)).map
                        fun nextChoice =>
                          TMVerifierStackReadChoice.atomAt
                            (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                            nextChoice)) :=
        TMPolyTimeMap.prod_mk hHead ih
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hInput
      simpa [Function.comp, tmVerifierNatListTrueContinuationClausesAt,
        cnfStructuredEncodedType] using hCons

theorem tmVerifierNatListFalseDelimiterClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell) := by
  have hDelimiterNext :=
    tmVerifierCertificateRightChoiceAtomsAt_succ_cell_tm_polytime V delimiterSymbol
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
    have hHead :=
      tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
        (tmVerifierTM V).k₀ choice
    have hInput :
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
      TMPolyTimeMap.prod_mk hHead hDelimiterNext
    have hCons := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
    simpa [Function.comp] using hCons
  let choices := tmVerifierCertificateRightReadChoices V falseSymbol
  change
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        choices.map fun choice =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
              fun delimiterChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                  delimiterChoice)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := hOne choice
      have hInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun cell : Nat =>
              ([Clause.negate
                  (TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                  fun delimiterChoice =>
                    TMVerifierStackReadChoice.atomAt
                      (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                      delimiterChoice,
                choices.map fun choice =>
                  [Clause.negate
                      (TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                    (tmVerifierCertificateRightReadChoices V delimiterSymbol).map
                      fun delimiterChoice =>
                        TMVerifierStackReadChoice.atomAt
                          (V := V) (k := (tmVerifierTM V).k₀) 0 (cell + 1)
                          delimiterChoice)) :=
        TMPolyTimeMap.prod_mk hHead ih
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hInput
      simpa [Function.comp, tmVerifierNatListFalseDelimiterClausesAt,
        cnfStructuredEncodedType] using hCons

theorem tmVerifierNatListStartDelimiterClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol cell) := by
  have hLits := tmVerifierCertificateRightChoiceNegAtomsAt_cell_tm_polytime V delimiterSymbol
  have hCNF := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierNatListStartDelimiterClausesAt] using hCNF

theorem tmVerifierNatListDelimiterPreviousClausesAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol cell) := by
  have hFalsePrev :=
    tmVerifierCertificateRightChoiceAtomsAt_pred_cell_tm_polytime V falseSymbol
  have hOne
      (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun cell : Nat =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
              TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 (cell - 1) falseChoice) := by
    have hHead :=
      tmVerifierStackReadChoice_negAtomAt_cell_tm_polytime V 0
        (tmVerifierTM V).k₀ choice
    have hInput :
        TMPolyTimeMap EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType
            (EncodedType.list literalStructuredEncodedType))
          (fun cell : Nat =>
            (Clause.negate
                (TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice),
              (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
                TMVerifierStackReadChoice.atomAt
                  (V := V) (k := (tmVerifierTM V).k₀) 0 (cell - 1) falseChoice)) :=
      TMPolyTimeMap.prod_mk hHead hFalsePrev
    have hCons := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons literalStructuredEncodedType) hInput
    simpa [Function.comp] using hCons
  let choices := tmVerifierCertificateRightReadChoices V delimiterSymbol
  change
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        choices.map fun choice =>
          [Clause.negate
              (TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
            (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
              TMVerifierStackReadChoice.atomAt
                (V := V) (k := (tmVerifierTM V).k₀) 0 (cell - 1) falseChoice)
  induction choices with
  | nil =>
      exact TMPolyTimeMap.const EncodedType.nat cnfStructuredEncodedType []
  | cons choice choices ih =>
      have hHead := hOne choice
      have hInput :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
            (fun cell : Nat =>
              ([Clause.negate
                  (TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                (tmVerifierCertificateRightReadChoices V falseSymbol).map fun falseChoice =>
                  TMVerifierStackReadChoice.atomAt
                    (V := V) (k := (tmVerifierTM V).k₀) 0 (cell - 1) falseChoice,
                choices.map fun choice =>
                  [Clause.negate
                      (TMVerifierStackReadChoice.atomAt
                        (V := V) (k := (tmVerifierTM V).k₀) 0 cell choice)] ++
                    (tmVerifierCertificateRightReadChoices V falseSymbol).map
                      fun falseChoice =>
                        TMVerifierStackReadChoice.atomAt
                          (V := V) (k := (tmVerifierTM V).k₀) 0 (cell - 1)
                          falseChoice)) :=
        TMPolyTimeMap.prod_mk hHead ih
      have hCons := TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hInput
      simpa [Function.comp, tmVerifierNatListDelimiterPreviousClausesAt,
        cnfStructuredEncodedType] using hCons

theorem tmVerifierNatListMainCellCNFAt_cell_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap EncodedType.nat cnfStructuredEncodedType
      (fun cell : Nat =>
        tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol cell) := by
  have hInvalid :=
    tmVerifierNatListInvalidSymbolChoiceClausesAt_cell_tm_polytime V trueSymbol falseSymbol
      delimiterSymbol
  have hTrue := tmVerifierNatListTrueContinuationClausesAt_cell_tm_polytime V
    trueSymbol falseSymbol
  have hFalse := tmVerifierNatListFalseDelimiterClausesAt_cell_tm_polytime V
    falseSymbol delimiterSymbol
  have hTailInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell,
            tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell)) :=
    TMPolyTimeMap.prod_mk hTrue hFalse
  have hTail := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hTailInput
  have hInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun cell : Nat =>
          (tmVerifierNatListInvalidSymbolChoiceClausesAt V trueSymbol falseSymbol
              delimiterSymbol cell,
            tmVerifierNatListTrueContinuationClausesAt V trueSymbol falseSymbol cell ++
              tmVerifierNatListFalseDelimiterClausesAt V falseSymbol delimiterSymbol cell)) :=
    TMPolyTimeMap.prod_mk hInvalid (by simpa [Function.comp, cnfStructuredEncodedType] using hTail)
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hInput
  simpa [Function.comp, tmVerifierNatListMainCellCNFAt, cnfStructuredEncodedType,
    List.append_assoc] using hAppend

theorem tmVerifierNatListCellFromBoundIndex_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.1.1 + Nat.min p.2 p.1.2) := by
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
  have hMinInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : (Nat × Nat) × Nat => (p.2, p.1.2)) :=
    TMPolyTimeMap.prod_mk hIdx hBound
  have hMin : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => Nat.min p.2 p.1.2) := by
    have hComp := TMPolyTimeMap.comp nat_min_tm_polytime hMinInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : (Nat × Nat) × Nat => (p.1.1, Nat.min p.2 p.1.2)) :=
    TMPolyTimeMap.prod_mk hStart hMin
  have hCell := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natAddInputEncodedType, X] using hCell

theorem tmVerifierNatListCellFromSuccBoundIndex_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.1.1 + Nat.min (p.2 + 1) p.1.2) := by
  let C := EncodedType.prod EncodedType.nat EncodedType.nat
  let X := EncodedType.prod C EncodedType.nat
  have hIdx : TMPolyTimeMap X EncodedType.nat (fun p : (Nat × Nat) × Nat => p.2) := by
    simpa [X, C] using TMPolyTimeMap.snd C EncodedType.nat
  have hSuccIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : (Nat × Nat) × Nat => p.2 + 1) := by
    have hSucc := nat_add_const_tm_polytime 1
    have hComp := TMPolyTimeMap.comp hSucc hIdx
    simpa [Function.comp, X] using hComp
  have hContext : TMPolyTimeMap X C (fun p : (Nat × Nat) × Nat => p.1) := by
    simpa [X, C] using TMPolyTimeMap.fst C EncodedType.nat
  have hInput :
      TMPolyTimeMap X (EncodedType.prod C EncodedType.nat)
        (fun p : (Nat × Nat) × Nat => (p.1, p.2 + 1)) :=
    TMPolyTimeMap.prod_mk hContext hSuccIdx
  have hCell := TMPolyTimeMap.comp tmVerifierNatListCellFromBoundIndex_tm_polytime hInput
  simpa [Function.comp, X, C] using hCell

theorem tmVerifierNatListMainCellCNFAt_index_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      cnfStructuredEncodedType
      (fun p : (Nat × Nat) × Nat =>
        tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
          (p.1.1 + Nat.min p.2 p.1.2)) := by
  have hBlock :=
    tmVerifierNatListMainCellCNFAt_cell_tm_polytime V trueSymbol falseSymbol delimiterSymbol
  have hComp := TMPolyTimeMap.comp hBlock tmVerifierNatListCellFromBoundIndex_tm_polytime
  simpa [Function.comp] using hComp

theorem tmVerifierNatListDelimiterPreviousClausesAt_index_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat)
      cnfStructuredEncodedType
      (fun p : (Nat × Nat) × Nat =>
        tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
          (p.1.1 + Nat.min (p.2 + 1) p.1.2)) := by
  have hBlock := tmVerifierNatListDelimiterPreviousClausesAt_cell_tm_polytime V
    falseSymbol delimiterSymbol
  have hComp := TMPolyTimeMap.comp hBlock tmVerifierNatListCellFromSuccBoundIndex_tm_polytime
  simpa [Function.comp] using hComp

theorem tmVerifierNatListSuffixPatternCNFForBound_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        tmVerifierNatListSuffixPatternCNFForBound V trueSymbol falseSymbol delimiterSymbol
          p.1 p.2) := by
  let C := EncodedType.prod EncodedType.nat EncodedType.nat
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  let mainBlock : (Nat × Nat) → Nat → CNF :=
    fun ctx idx =>
      tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
        (ctx.1 + Nat.min idx ctx.2)
  have hMainBlock :
      TMPolyTimeMap (EncodedType.prod C EncodedType.nat)
        cnfStructuredEncodedType
        (fun p : (Nat × Nat) × Nat => mainBlock p.1 p.2) := by
    simpa [mainBlock] using
      tmVerifierNatListMainCellCNFAt_index_tm_polytime V trueSymbol falseSymbol
        delimiterSymbol
  have hMainFlat :=
    cnfContextFlatMap_tm_polytime
      (C := C) (X := EncodedType.nat) mainBlock hMainBlock
  let prevBlock : (Nat × Nat) → Nat → CNF :=
    fun ctx idx =>
      tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
        (ctx.1 + Nat.min (idx + 1) ctx.2)
  have hPrevBlock :
      TMPolyTimeMap (EncodedType.prod C EncodedType.nat)
        cnfStructuredEncodedType
        (fun p : (Nat × Nat) × Nat => prevBlock p.1 p.2) := by
    simpa [prevBlock] using
      tmVerifierNatListDelimiterPreviousClausesAt_index_tm_polytime V falseSymbol
        delimiterSymbol
  have hPrevFlat :=
    cnfContextFlatMap_tm_polytime
      (C := C) (X := EncodedType.nat) prevBlock hPrevBlock
  have hStart : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hContext : TMPolyTimeMap X C (fun p : Nat × Nat => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hStart hBound
  have hRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun p : Nat × Nat => List.range p.2) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hFlatInput :
      TMPolyTimeMap X
        (EncodedType.prod C (EncodedType.list EncodedType.nat))
        (fun p : Nat × Nat => ((p.1, p.2), List.range p.2)) :=
    TMPolyTimeMap.prod_mk hContext hRange
  have hMain : TMPolyTimeMap X cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        (List.range p.2).flatMap fun idx =>
          tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
            (p.1 + Nat.min idx p.2)) := by
    have hComp := TMPolyTimeMap.comp hMainFlat hFlatInput
    simpa [Function.comp, mainBlock, X, C] using hComp
  have hPrev : TMPolyTimeMap X cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        (List.range p.2).flatMap fun idx =>
          tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
            (p.1 + Nat.min (idx + 1) p.2)) := by
    have hComp := TMPolyTimeMap.comp hPrevFlat hFlatInput
    simpa [Function.comp, prevBlock, X, C] using hComp
  have hStartCNF : TMPolyTimeMap X cnfStructuredEncodedType
      (fun p : Nat × Nat =>
        tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol p.1) := by
    have hCell := tmVerifierNatListStartDelimiterClausesAt_cell_tm_polytime V delimiterSymbol
    have hComp := TMPolyTimeMap.comp hCell hStart
    simpa [Function.comp, X] using hComp
  have hMainStartInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : Nat × Nat =>
          ((List.range p.2).flatMap fun idx =>
              tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
                (p.1 + Nat.min idx p.2),
            tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol p.1)) :=
    TMPolyTimeMap.prod_mk hMain hStartCNF
  have hMainStart := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hMainStartInput
  have hAllInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : Nat × Nat =>
          (((List.range p.2).flatMap fun idx =>
              tmVerifierNatListMainCellCNFAt V trueSymbol falseSymbol delimiterSymbol
                (p.1 + Nat.min idx p.2)) ++
            tmVerifierNatListStartDelimiterClausesAt V delimiterSymbol p.1,
            (List.range p.2).flatMap fun idx =>
              tmVerifierNatListDelimiterPreviousClausesAt V falseSymbol delimiterSymbol
                (p.1 + Nat.min (idx + 1) p.2))) := by
    refine TMPolyTimeMap.prod_mk ?_ hPrev
    simpa [Function.comp, cnfStructuredEncodedType] using hMainStart
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAllInput
  convert hAll using 1

theorem tmVerifierNatListSuffixPatternCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (trueSymbol falseSymbol delimiterSymbol : V.Cert.Symbol) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierNatListSuffixPatternCNF V trueSymbol falseSymbol delimiterSymbol x) := by
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
    tmVerifierNatListSuffixPatternCNFForBound_tm_polytime V trueSymbol falseSymbol
      delimiterSymbol
  have hComp := TMPolyTimeMap.comp hPattern hInput
  simpa [Function.comp, tmVerifierNatListSuffixPatternCNF] using hComp

end SAT
end ComplexityReduction
