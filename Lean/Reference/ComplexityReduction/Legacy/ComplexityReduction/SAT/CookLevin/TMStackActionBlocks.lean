/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTransitionWindows

/-!
Primitive stack-action blocks for the future standard-TM Cook-Levin tableau.

`TMTransitionWindows` records the sequence of stack actions in one recursively
expanded `TM2.Stmt` window.  This file turns those actions into micro-step CNF
surfaces.  It deliberately keeps the hard part of naming pushed symbols as an
explicit boundary record: the active-symbol slice proves that pushed symbols are
finitely collected, but a canonical payload/equality theorem for every pushed
dependent stack symbol is still a later proof obligation.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Push payload boundary -/

/--
Boundary required to turn a raw pushed stack symbol into the payload used by a
stack-symbol atom.

The `represents` field records the dependent-symbol equality as `HEq` because
the named and raw symbols live in stack alphabets indexed by propositionally
equal stack indices.
-/
structure TMVerifierPushPayloadBoundary {L : EncodedDecisionProblem}
    (V : TMVerifier L) where
  payload : TMVerifierStackSymbol V → Nat
  covered :
    ∀ raw : TMVerifierStackSymbol V,
      raw ∈ tmVerifierControlPushSymbols V →
        ∃ named ∈ tmVerifierActiveStackSymbols V,
          named.stack = raw.stack ∧ named.payload = payload raw ∧ HEq named.symbol raw.symbol

/-! ### Finite stack/cell domains -/

/-- All finite stack indices of the extracted verifier machine. -/
noncomputable def tmVerifierStackList {L : EncodedDecisionProblem}
    (V : TMVerifier L) : List (tmVerifierStackIndex V) :=
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  letI : DecidableEq (tmVerifierTM V).K := (tmVerifierTM V).kDecidableEq
  (Finset.univ : Finset (tmVerifierStackIndex V)).toList

/-- All finite stack indices except a selected stack. -/
noncomputable def tmVerifierOtherStacks {L : EncodedDecisionProblem}
    (V : TMVerifier L) (k : tmVerifierStackIndex V) : List (tmVerifierStackIndex V) :=
  letI : Fintype (tmVerifierTM V).K := (tmVerifierTM V).kFin
  letI : DecidableEq (tmVerifierTM V).K := (tmVerifierTM V).kDecidableEq
  ((Finset.univ : Finset (tmVerifierStackIndex V)).filter (fun j => j ≠ k)).toList

/-! ### Primitive implication clauses for stack frames and shifts -/

/-- If one read-choice atom holds before a micro-step, the same atom holds after it. -/
noncomputable def tmVerifierFrameForwardClause {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal) : Clause :=
  tmVerifierImplicationClause
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice)

/-- If one read-choice atom holds after a micro-step, the same atom held before it. -/
noncomputable def tmVerifierFrameBackwardClause {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal) : Clause :=
  tmVerifierImplicationClause
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice)

/-- Bi-implication frame clauses for one choice at one cell. -/
noncomputable def tmVerifierFrameChoiceCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal) : CNF :=
  [ tmVerifierFrameForwardClause V tin tout k cell choice antecedents
  , tmVerifierFrameBackwardClause V tin tout k cell choice antecedents ]

/-- Frame clauses for all audited choices at one stack cell. -/
noncomputable def tmVerifierFrameCellCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) : CNF :=
  (tmVerifierStackReadChoices V k).flatMap fun choice =>
    tmVerifierFrameChoiceCNFBetween V tin tout k cell choice antecedents

/-- Frame clauses for every bounded cell of one stack. -/
noncomputable def tmVerifierFrameStackCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal) : CNF :=
  (tmVerifierCellRange V p).flatMap fun cell =>
    tmVerifierFrameCellCNFBetween V tin tout k cell antecedents

/-- Frame clauses for every stack in the bounded tableau. -/
noncomputable def tmVerifierFrameAllStacksCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) : CNF :=
  (tmVerifierStackList V).flatMap fun k =>
    tmVerifierFrameStackCNFBetween V p tin tout k antecedents

/-- Push shift clause: old cell `cell` becomes next cell `cell + 1`. -/
noncomputable def tmVerifierPushShiftClause {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal) : Clause :=
  tmVerifierImplicationClause
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice)

/-- Push shift clauses for every audited choice at one old cell. -/
noncomputable def tmVerifierPushShiftCellCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) : CNF :=
  (tmVerifierStackReadChoices V k).map fun choice =>
    tmVerifierPushShiftClause V tin tout k cell choice antecedents

/-- Pop shift clause: old cell `cell + 1` becomes next cell `cell`. -/
noncomputable def tmVerifierPopShiftClause {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal) : Clause :=
  tmVerifierImplicationClause
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice)

/-- Pop shift clauses for every audited choice at one new cell. -/
noncomputable def tmVerifierPopShiftCellCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) : CNF :=
  (tmVerifierStackReadChoices V k).map fun choice =>
    tmVerifierPopShiftClause V tin tout k cell choice antecedents

theorem tmVerifierFrameForwardClause_satisfies {L : EncodedDecisionProblem}
    (V : TMVerifier L) (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment) :
    CNF.Satisfies [tmVerifierFrameForwardClause V tin tout k cell choice antecedents] a →
      (∀ l ∈ antecedents, l.eval a = true) →
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice).eval a = true →
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice).eval a = true := by
  intro h hAntecedents hChoice
  exact tmVerifierImplicationClause_satisfies_of_antecedents
    (antecedents ++
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice])
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) a h (by
      intro l hl
      rcases List.mem_append.mp hl with hlAnt | hlChoice
      · exact hAntecedents l hlAnt
      · have hEq :
            l = TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice := by
          simpa using hlChoice
        simpa [hEq] using hChoice)

/-! ### Primitive action CNF blocks -/

/-- Clauses for a pushed symbol appearing at the new top cell. -/
noncomputable def tmVerifierPushTopCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (tout : Nat) (raw : TMVerifierStackSymbol V) (antecedents : List Literal) : CNF :=
  [tmVerifierImplicationClause antecedents
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw))]

/-- Clauses for one push micro-step on the selected stack plus frames for all other stacks. -/
noncomputable def tmVerifierPushActionCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal) : CNF :=
  tmVerifierPushTopCNF V B tout raw antecedents ++
    (tmVerifierCellRange V p).flatMap
      (fun cell => tmVerifierPushShiftCellCNF V tin tout raw.stack cell antecedents) ++
    (tmVerifierOtherStacks V raw.stack).flatMap fun k =>
      tmVerifierFrameStackCNFBetween V p tin tout k antecedents

/-- Clauses for one pop micro-step on the selected stack plus frames for all other stacks. -/
noncomputable def tmVerifierPopActionCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal) : CNF :=
  (tmVerifierCellRange V p).flatMap
      (fun cell => tmVerifierPopShiftCellCNF V tin tout k cell antecedents) ++
    (tmVerifierOtherStacks V k).flatMap fun j =>
      tmVerifierFrameStackCNFBetween V p tin tout j antecedents

/-- Clauses for a micro-step that preserves every stack. -/
noncomputable def tmVerifierPreserveAllStacksActionCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) : CNF :=
  tmVerifierFrameAllStacksCNFBetween V p tin tout antecedents

/-- Effect clauses for one recorded stack/control action, excluding read-choice guards. -/
noncomputable def tmVerifierStackActionEffectCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (antecedents : List Literal) : TMVerifierStackAction V → CNF
  | TMVerifierStackAction.push raw => tmVerifierPushActionCNFBetween V B p tin tout raw antecedents
  | TMVerifierStackAction.pop k _ => tmVerifierPopActionCNFBetween V p tin tout k antecedents
  | TMVerifierStackAction.peek _ _ => tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents
  | TMVerifierStackAction.load => tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents
  | TMVerifierStackAction.branch _ => tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents

/--
Read-choice guard clauses for actions that inspect a stack head.

For a `peek`/`pop` micro-step, the window's recorded read choice must be the
choice selected by the input micro-row top cell.  Non-reading actions add no
clauses.
-/
noncomputable def tmVerifierStackActionReadCNFAt {L : EncodedDecisionProblem}
    {V : TMVerifier L} (tin : Nat) (antecedents : List Literal) :
    TMVerifierStackAction V → CNF
  | TMVerifierStackAction.peek k choice =>
      [tmVerifierImplicationClause antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice)]
  | TMVerifierStackAction.pop k choice =>
      [tmVerifierImplicationClause antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice)]
  | _ => []

/-- The read atom forced by a recorded `peek`/`pop` action. -/
def TMVerifierStackActionReadAtomTrue {L : EncodedDecisionProblem} {V : TMVerifier L}
    (tin : Nat) (a : Assignment) : TMVerifierStackAction V → Prop
  | TMVerifierStackAction.peek k choice =>
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice).eval a = true
  | TMVerifierStackAction.pop k choice =>
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice).eval a = true
  | _ => True

/-- Primitive clauses for one recorded stack/control action. -/
noncomputable def tmVerifierStackActionCNFBetween {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) : CNF :=
  tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act ++
    tmVerifierStackActionReadCNFAt tin antecedents act

theorem tmVerifierStackActionCNFBetween_satisfies_effect_cnf
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackActionCNFBetween V B p tin tout antecedents act) a) :
    CNF.Satisfies (tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act) a :=
  (CNF.satisfies_append
    (tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act)
    (tmVerifierStackActionReadCNFAt tin antecedents act) a).1 h |>.1

theorem tmVerifierStackActionReadCNFAt_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (tin : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackActionReadCNFAt tin antecedents act) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionReadAtomTrue tin a act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionReadAtomTrue]
  | peek k choice =>
      exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) a
        (by simpa [tmVerifierStackActionReadCNFAt] using h) hAntecedents
  | pop k choice =>
      exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) a
        (by simpa [tmVerifierStackActionReadCNFAt] using h) hAntecedents
  | load =>
      simp [TMVerifierStackActionReadAtomTrue]
  | branch tag =>
      simp [TMVerifierStackActionReadAtomTrue]

theorem tmVerifierStackActionCNFBetween_satisfies_read
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment)
    (h : CNF.Satisfies (tmVerifierStackActionCNFBetween V B p tin tout antecedents act) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionReadAtomTrue tin a act := by
  have hRead :
      CNF.Satisfies (tmVerifierStackActionReadCNFAt tin antecedents act) a :=
    (CNF.satisfies_append
      (tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act)
      (tmVerifierStackActionReadCNFAt tin antecedents act) a).1 h |>.2
  exact tmVerifierStackActionReadCNFAt_satisfies tin antecedents act a hRead hAntecedents

/-- Clauses for the action sequence of one statement window, using micro-time rows. -/
noncomputable def tmVerifierWindowStackActionCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) : CNF :=
  w.actions.zipIdx.flatMap fun entry =>
    let tin := tmVerifierMicroTime t entry.2
    let tout := tmVerifierMicroTime t (entry.2 + 1)
    tmVerifierStackActionCNFBetween V B p tin tout antecedents entry.1

end SAT
end ComplexityReduction
