/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Basic
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.SetSystem
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT
import ComplexityReduction.Legacy.ComplexityReduction.Targets.NPCTransfer

/-!
Shared proof helpers for the first Karp21 reduction chain.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-- Any map into a raw-encoded codomain has a constant output-size certificate. -/
noncomputable def rawCodomainTMBackedMap {X : EncodedType} {α : Type} (f : X.Carrier → α) :
    TMBackedCostedMap X (EncodedType.raw α) f :=
  TMBackedCostedMap.rawCodomain X α f

/--
Any map into a raw-encoded codomain has both the constant output-size
certificate and a direct empty-output TM2 witness for the current raw encoding.
This is not a faithful natural-language encoding theorem.
-/
def rawCodomainPolytime {X : EncodedType} {α : Type} (f : X.Carrier → α) :
    CostedPolyTimeModel.IsPolyTimeMap (X := X) (Y := EncodedType.raw α) f := by
  refine CostedPolyTimeMap.of_costed
    { cost := fun _ => 0
      cost_bound := ?_
      output_bound := ?_ }
  · exact ⟨0, 0, 0, by intro x; simp⟩
  · exact ⟨0, 0, 0, by intro x; simp [EncodedType.inputSize, EncodedType.raw]⟩

/--
Proof-carrying reduction into an anonymous raw-encoded target predicate.
Concrete Karp21 target wrappers should `simpa` through their local
`*_DecisionProblem` definitions and then project the costed wrapper from this
witness.
-/
noncomputable def rawCodomainTMBackedReduction
    (A : EncodedDecisionProblem) {α : Type} (P : α → Prop)
    (f : A.Instance.Carrier → α) (hCorrect : ∀ x, A.isYes x ↔ P (f x)) :
    TMBackedCostedReduction A { Instance := EncodedType.raw α, isYes := P } :=
  TMBackedCostedReduction.ofTMBackedCostedMap (rawCodomainTMBackedMap f) hCorrect

/-- A trivially satisfiable local 3CNF. -/
def trueThreeCNF : SAT.ThreeCNF where
  clauses := []
  isThree := by
    intro c hc
    simp at hc

/-- A trivially unsatisfiable local 3CNF with one empty clause. -/
def falseThreeCNF : SAT.ThreeCNF where
  clauses := [[]]
  isThree := by
    intro c hc
    simp at hc
    subst c
    simp

theorem trueThreeCNF_satisfiable :
    SAT.ThreeCNF.Satisfiable trueThreeCNF := by
  exact ⟨fun _ => false, by intro c hc; simp [trueThreeCNF] at hc⟩

theorem falseThreeCNF_not_satisfiable :
    ¬ SAT.ThreeCNF.Satisfiable falseThreeCNF := by
  rintro ⟨a, hSat⟩
  have hClause : SAT.Clause.Satisfies [] a := hSat [] (by simp [falseThreeCNF])
  rcases hClause with ⟨l, hl, _⟩
  simp at hl

/-- A tiny 3CNF whose satisfiability is equivalent to `P`. -/
noncomputable def propThreeCNF (P : Prop) : SAT.ThreeCNF := by
  classical
  exact if P then trueThreeCNF else falseThreeCNF

theorem propThreeCNF_satisfiable_iff (P : Prop) :
    SAT.ThreeCNF.Satisfiable (propThreeCNF P) ↔ P := by
  classical
  by_cases h : P
  · constructor
    · intro _; exact h
    · intro _; simpa [propThreeCNF, h] using trueThreeCNF_satisfiable
  · constructor
    · intro hSat
      exact (falseThreeCNF_not_satisfiable (by simpa [propThreeCNF, h] using hSat)).elim
    · intro hp
      exact (h hp).elim

theorem propThreeCNF_inputSize_le_one (P : Prop) :
    SAT.threeSATDecisionProblem.Instance.inputSize (propThreeCNF P) ≤ 1 := by
  classical
  by_cases h : P
  · change (SAT.ThreeSATEncoding.encodeThreeCNF (propThreeCNF P)).length ≤ 1
    simp [propThreeCNF, h, SAT.ThreeSATEncoding.encodeThreeCNF, trueThreeCNF]
  · change (SAT.ThreeSATEncoding.encodeThreeCNF (propThreeCNF P)).length ≤ 1
    simp [propThreeCNF, h, SAT.ThreeSATEncoding.encodeThreeCNF,
      SAT.ThreeSATEncoding.encodeClause, falseThreeCNF]

/-- Polynomial-time certificate for proposition-indexed tiny 3CNF maps. -/
noncomputable def propThreeCNFPolytime (L : EncodedDecisionProblem) :
    CostedPolyTimeModel.IsPolyTimeMap
      (X := L.Instance) (Y := SAT.threeSATDecisionProblem.Instance)
      (fun x => propThreeCNF (L.isYes x)) := by
  refine CostedPolyTimeMap.of_costed
    { cost := fun _ => 1
      cost_bound := ?_
      output_bound := ?_ }
  · exact ⟨0, 0, 1, by intro x; simp⟩
  · exact ⟨0, 0, 1, by intro x; simpa using propThreeCNF_inputSize_le_one (L.isYes x)⟩

/-- Polynomial-time certificate for arbitrary Boolean maps. -/
def boolPolytime {X : EncodedType} (f : X.Carrier → Bool) :
    CostedPolyTimeModel.IsPolyTimeMap (X := X) (Y := EncodedType.bool) f := by
  refine CostedPolyTimeMap.of_costed
    { cost := fun _ => 1
      cost_bound := ?_
      output_bound := ?_ }
  · exact ⟨0, 0, 1, by intro x; simp⟩
  · exact ⟨0, 0, 1, by intro x; cases f x <;> simp [EncodedType.inputSize, EncodedType.bool]⟩

/--
Local NP membership for a decidable encoded problem.  This is used only for the
current project-local costed model; P16 tracks the stronger textbook TM bridge.
-/
noncomputable def decidableLocalNPVerifier (L : EncodedDecisionProblem) :
    LocalNPVerifier CostedPolyTimeModel L := by
  classical
  refine
    { verifier :=
        { Cert := EncodedType.raw Unit
          verify := fun x _ => decide (L.isYes x)
          verifier_polytime := by
            exact boolPolytime
              (X := EncodedType.prod L.Instance (EncodedType.raw Unit))
              (fun p : L.Instance.Carrier × Unit => decide (L.isYes p.1))
          cert_bound := ?_
          sound := ?_ }
      cookTableauThreeCNF := fun x => propThreeCNF (L.isYes x)
      cookTableauThreeCNF_polytime := propThreeCNFPolytime L
      cookTableauThreeCNF_correct := ?_ }
  · refine ⟨0, 0, 0, ?_⟩
    intro x hx
    exact ⟨(), by simp [EncodedType.inputSize, EncodedType.raw], by simp [hx]⟩
  · intro x c h
    exact of_decide_eq_true h
  · intro x
    exact (propThreeCNF_satisfiable_iff (L.isYes x)).symm

/-- Decidable local NP membership wrapper for P15b Karp targets. -/
theorem decidableInNP (L : EncodedDecisionProblem) :
    InNPEnc CostedPolyTimeModel L :=
  InNPEnc.intro (decidableLocalNPVerifier L)

end Karp21
end ComplexityReduction
