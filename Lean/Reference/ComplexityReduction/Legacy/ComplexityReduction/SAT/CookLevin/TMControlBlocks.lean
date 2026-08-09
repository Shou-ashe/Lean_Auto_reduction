/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauData

/-!
Finite-control CNF blocks for the future standard-TM Cook-Levin tableau.

This file starts the actual block-generation layer: labels and internal states
of the extracted `FinTM2` verifier are finite, so they can be encoded as stable
SAT atoms and constrained by exactly-one clauses at each time row.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Stable payload codes for finite-control values -/

/-- Stable payload code for a verifier machine label, with `none` reserved for halting. -/
noncomputable def tmVerifierLabelCode {L : EncodedDecisionProblem} (V : TMVerifier L)
    (l : Option (tmVerifierTM V).Λ) : Nat :=
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  match l with
  | none => 0
  | some q => ((Fintype.equivFin (tmVerifierTM V).Λ) q).val + 1

/-- Stable payload code for a verifier machine internal state. -/
noncomputable def tmVerifierStateCode {L : EncodedDecisionProblem} (V : TMVerifier L)
    (s : (tmVerifierTM V).σ) : Nat :=
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  ((Fintype.equivFin (tmVerifierTM V).σ) s).val

/-- Positive atom saying that the verifier machine has label `l` at time `t`. -/
noncomputable def tmVerifierLabelAtom {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (l : Option (tmVerifierTM V).Λ) : Literal :=
  tmVerifierTableauAtom TMVerifierTableauVarKind.label t 0 0 (tmVerifierLabelCode V l)

/-- Negative atom saying that the verifier machine does not have label `l` at time `t`. -/
noncomputable def negTMVerifierLabelAtom {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (l : Option (tmVerifierTM V).Λ) : Literal :=
  negTMVerifierTableauAtom TMVerifierTableauVarKind.label t 0 0 (tmVerifierLabelCode V l)

/-- Positive atom saying that the verifier machine has internal state `s` at time `t`. -/
noncomputable def tmVerifierStateAtom {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (s : (tmVerifierTM V).σ) : Literal :=
  tmVerifierTableauAtom TMVerifierTableauVarKind.state t 0 0 (tmVerifierStateCode V s)

/-- Negative atom saying that the verifier machine does not have internal state `s` at time `t`. -/
noncomputable def negTMVerifierStateAtom {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) (s : (tmVerifierTM V).σ) : Literal :=
  negTMVerifierTableauAtom TMVerifierTableauVarKind.state t 0 0 (tmVerifierStateCode V s)

/-! ### Finite-control rows -/

/-- All label atoms for the extracted verifier machine at one time row. -/
noncomputable def tmVerifierLabelAtomsAt {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) : List Literal :=
  letI : Fintype (tmVerifierTM V).Λ := (tmVerifierTM V).ΛFin
  letI := Classical.decEq (Option (tmVerifierTM V).Λ)
  ((Finset.univ : Finset (Option (tmVerifierTM V).Λ)).toList).map
    (fun l => tmVerifierLabelAtom V t l)

/-- All internal-state atoms for the extracted verifier machine at one time row. -/
noncomputable def tmVerifierStateAtomsAt {L : EncodedDecisionProblem} (V : TMVerifier L)
    (t : Nat) : List Literal :=
  letI : Fintype (tmVerifierTM V).σ := (tmVerifierTM V).σFin
  letI := Classical.decEq (tmVerifierTM V).σ
  ((Finset.univ : Finset (tmVerifierTM V).σ).toList).map
    (fun s => tmVerifierStateAtom V t s)

/-- Exactly one machine label is selected at time row `t`. -/
noncomputable def tmVerifierExactlyOneLabelCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : CNF :=
  CookLevin.exactlyOneCNF (tmVerifierLabelAtomsAt V t)

/-- Exactly one internal state is selected at time row `t`. -/
noncomputable def tmVerifierExactlyOneStateCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : CNF :=
  CookLevin.exactlyOneCNF (tmVerifierStateAtomsAt V t)

/-- A one-literal CNF block. -/
def tmVerifierUnitCNF (l : Literal) : CNF :=
  [[l]]

theorem tmVerifierUnitCNF_satisfies (l : Literal) (a : Assignment) :
    CNF.Satisfies (tmVerifierUnitCNF l) a ↔ l.eval a = true := by
  simp [tmVerifierUnitCNF, CNF.Satisfies, Clause.Satisfies]

/-- Initial finite-control clauses: start at the main label and initial internal state. -/
noncomputable def tmVerifierInitialControlCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) : CNF :=
  tmVerifierUnitCNF (tmVerifierLabelAtom V 0 (some (tmVerifierTM V).main)) ++
    tmVerifierUnitCNF (tmVerifierStateAtom V 0 (tmVerifierTM V).initialState)

/-- Accepting finite-control clause at a selected time row: the machine has halted. -/
noncomputable def tmVerifierHaltingControlCNFAt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat) : CNF :=
  tmVerifierUnitCNF (tmVerifierLabelAtom V t none)

end SAT
end ComplexityReduction
