/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.Examples.ThreeSATLike

/-!
Reverse semantic adapter from local bundled 3SAT to the CSP 3SAT-like language.

This is the first hard-case direction in the local Boolean CSP library.  The
map is also packaged with a project-local costed/Karp certificate; NPC transfer
is packaged in `ThreeSATLikeNPC.lean` through the P14e local 3SAT theorem.
-/

namespace ComplexityReduction
namespace CSP
namespace Hardness
namespace ThreeSATLike

open SAT
open ComplexityReduction.CSP.Examples

/-- The 3SAT-like relation symbol determined by three literal polarity bits. -/
def symbolOfNegs : Bool → Bool → Bool → ThreeSATLikeSymbol
  | false, false, false => ThreeSATLikeSymbol.posPosPos
  | true, false, false => ThreeSATLikeSymbol.negPosPos
  | false, true, false => ThreeSATLikeSymbol.posNegPos
  | false, false, true => ThreeSATLikeSymbol.posPosNeg
  | true, true, false => ThreeSATLikeSymbol.negNegPos
  | true, false, true => ThreeSATLikeSymbol.negPosNeg
  | false, true, true => ThreeSATLikeSymbol.posNegNeg
  | true, true, true => ThreeSATLikeSymbol.negNegNeg

/-- A ternary CSP constraint representing one ternary SAT clause. -/
def constraintOfLiterals (l₁ l₂ l₃ : Literal) : Constraint threeSATLikeLanguage where
  symbol := symbolOfNegs l₁.neg l₂.neg l₃.neg
  vars := fun i =>
    match i.val with
    | 0 => l₁.var
    | 1 => l₂.var
    | _ => l₃.var

theorem ternaryClauseRel_holds_iff (n₁ n₂ n₃ : Bool) (t : BoolTuple 3) :
    (StandardRelations.ternaryClauseRel n₁ n₂ n₃).Holds t ↔
      StandardRelations.literalValue n₁ (t ⟨0, by decide⟩) = true ∨
        StandardRelations.literalValue n₂ (t ⟨1, by decide⟩) = true ∨
          StandardRelations.literalValue n₃ (t ⟨2, by decide⟩) = true := by
  classical
  cases n₁ <;> cases n₂ <;> cases n₃ <;>
    unfold StandardRelations.ternaryClauseRel StandardRelations.clauseRel <;>
    rw [BoolRel.holds_ofPredicate_iff]
  all_goals
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (by simpa [StandardRelations.literalValue] using hi)
      · exact Or.inr (Or.inl (by simpa [StandardRelations.literalValue] using hi))
      · exact Or.inr (Or.inr (by simpa [StandardRelations.literalValue] using hi))
    · intro h
      rcases h with h₁ | h₂ | h₃
      · exact ⟨⟨0, by decide⟩, by simpa [StandardRelations.literalValue] using h₁⟩
      · exact ⟨⟨1, by decide⟩, by simpa [StandardRelations.literalValue] using h₂⟩
      · exact ⟨⟨2, by decide⟩, by simpa [StandardRelations.literalValue] using h₃⟩

theorem constraintOfLiterals_satisfies_iff (l₁ l₂ l₃ : Literal) (a : Assignment) :
    Constraint.Satisfies (constraintOfLiterals l₁ l₂ l₃) a ↔
      l₁.eval a = true ∨ l₂.eval a = true ∨ l₃.eval a = true := by
  cases l₁ with
  | mk v₁ n₁ =>
      cases l₂ with
      | mk v₂ n₂ =>
          cases l₃ with
          | mk v₃ n₃ =>
              cases n₁ <;> cases n₂ <;> cases n₃ <;>
                (simp only [Constraint.Satisfies, constraintOfLiterals, symbolOfNegs,
                 threeSATLikeLanguage, threeSATLikeRelationOf]
                 rw [ternaryClauseRel_holds_iff]
                 simp [Constraint.assignmentTuple, Literal.eval, StandardRelations.literalValue])

/-- A fixed contradictory CSP block used for empty SAT clauses. -/
def contradictionBlock : Formula threeSATLikeLanguage :=
  [ constraintOfLiterals (Literal.positive 0) (Literal.positive 0) (Literal.positive 0)
  , constraintOfLiterals (Literal.negative 0) (Literal.negative 0) (Literal.negative 0)
  ]

theorem contradictionBlock_unsat (a : Assignment) :
    ¬ Formula.Satisfies contradictionBlock a := by
  intro h
  have hpos :
      Constraint.Satisfies
        (constraintOfLiterals (Literal.positive 0) (Literal.positive 0)
          (Literal.positive 0))
        a := by
    exact h _ (by simp [contradictionBlock])
  have hneg :
      Constraint.Satisfies
        (constraintOfLiterals (Literal.negative 0) (Literal.negative 0)
          (Literal.negative 0))
        a := by
    exact h _ (by simp [contradictionBlock])
  have htrue : a 0 = true := by
    have h :=
      (constraintOfLiterals_satisfies_iff (Literal.positive 0) (Literal.positive 0)
        (Literal.positive 0) a).1 hpos
    simpa using h
  have hfalse : a 0 = false := by
    have h :=
      (constraintOfLiterals_satisfies_iff (Literal.negative 0) (Literal.negative 0)
        (Literal.negative 0) a).1 hneg
    cases h0 : a 0
    · rfl
    · simp [Literal.negative, Literal.eval, h0] at h
  simp [htrue] at hfalse

/-- Translate one local 3SAT clause into one or more 3SAT-like CSP constraints. -/
def clauseToFormula : Clause → Formula threeSATLikeLanguage
  | [] => contradictionBlock
  | [l₁] => [constraintOfLiterals l₁ l₁ l₁]
  | [l₁, l₂] => [constraintOfLiterals l₁ l₂ l₂]
  | l₁ :: l₂ :: l₃ :: _ => [constraintOfLiterals l₁ l₂ l₃]

theorem clauseToFormula_satisfies_iff {c : Clause} (hlen : c.length ≤ 3)
    (a : Assignment) :
    Formula.Satisfies (clauseToFormula c) a ↔ Clause.Satisfies c a := by
  cases c with
  | nil =>
      constructor
      · intro h
        exact False.elim ((contradictionBlock_unsat a) h)
      · intro h
        rcases h with ⟨l, hl, _⟩
        cases hl
  | cons l₁ rest =>
      cases rest with
      | nil =>
          constructor
          · intro h
            have hc : Constraint.Satisfies (constraintOfLiterals l₁ l₁ l₁) a :=
              h _ (by simp [clauseToFormula])
            have hlit := (constraintOfLiterals_satisfies_iff l₁ l₁ l₁ a).1 hc
            exact ⟨l₁, by simp, by simpa using hlit⟩
          · rintro ⟨l, hl, hlEval⟩ d hd
            have hEq : d = constraintOfLiterals l₁ l₁ l₁ := by
              simpa [clauseToFormula] using hd
            subst d
            have hl' : l = l₁ := by
              simpa using hl
            subst l
            exact (constraintOfLiterals_satisfies_iff l₁ l₁ l₁ a).2 (by
              simpa using hlEval)
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              constructor
              · intro h
                have hc : Constraint.Satisfies (constraintOfLiterals l₁ l₂ l₂) a :=
                  h _ (by simp [clauseToFormula])
                have hlit := (constraintOfLiterals_satisfies_iff l₁ l₂ l₂ a).1 hc
                rcases hlit with h₁ | h₂
                · exact ⟨l₁, by simp, h₁⟩
                · exact ⟨l₂, by simp, h₂.elim id id⟩
              · rintro ⟨l, hl, hlEval⟩ d hd
                have hEq : d = constraintOfLiterals l₁ l₂ l₂ := by
                  simpa [clauseToFormula] using hd
                subst d
                rcases List.mem_cons.mp hl with h₁ | h₂
                · subst l
                  exact (constraintOfLiterals_satisfies_iff l₁ l₂ l₂ a).2
                    (Or.inl hlEval)
                · have h₂' : l = l₂ := by simpa using h₂
                  subst l
                  exact (constraintOfLiterals_satisfies_iff l₁ l₂ l₂ a).2
                    (Or.inr (Or.inl hlEval))
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  constructor
                  · intro h
                    have hc : Constraint.Satisfies (constraintOfLiterals l₁ l₂ l₃) a :=
                      h _ (by simp [clauseToFormula])
                    have hlit := (constraintOfLiterals_satisfies_iff l₁ l₂ l₃ a).1 hc
                    rcases hlit with h₁ | h₂ | h₃
                    · exact ⟨l₁, by simp, h₁⟩
                    · exact ⟨l₂, by simp, h₂⟩
                    · exact ⟨l₃, by simp, h₃⟩
                  · rintro ⟨l, hl, hlEval⟩ d hd
                    have hEq : d = constraintOfLiterals l₁ l₂ l₃ := by
                      simpa [clauseToFormula] using hd
                    subst d
                    rcases List.mem_cons.mp hl with h₁ | htail
                    · subst l
                      exact (constraintOfLiterals_satisfies_iff l₁ l₂ l₃ a).2
                        (Or.inl hlEval)
                    rcases List.mem_cons.mp htail with h₂ | htail
                    · subst l
                      exact (constraintOfLiterals_satisfies_iff l₁ l₂ l₃ a).2
                        (Or.inr (Or.inl hlEval))
                    · have h₃ : l = l₃ := by simpa using htail
                      subst l
                      exact (constraintOfLiterals_satisfies_iff l₁ l₂ l₃ a).2
                        (Or.inr (Or.inr hlEval))
              | cons l₄ rest₄ =>
                  simp at hlen

/-- Translate a bundled local 3CNF formula into the 3SAT-like CSP language. -/
def threeCNFToFormula (φ : ThreeCNF) : Formula threeSATLikeLanguage :=
  φ.clauses.flatMap clauseToFormula

theorem cnfToFormula_satisfies_iff (clauses : CNF)
    (hThree : CNF.IsThreeCNF clauses) (a : Assignment) :
    Formula.Satisfies (clauses.flatMap clauseToFormula) a ↔ CNF.Satisfies clauses a := by
  induction clauses with
  | nil =>
      simp [Formula.Satisfies, CNF.Satisfies]
  | cons c cs ih =>
      have hc : c.length ≤ 3 := hThree c (by simp)
      have hcs : CNF.IsThreeCNF cs := by
        intro d hd
        exact hThree d (by simp [hd])
      rw [List.flatMap_cons, Formula.satisfies_append,
        clauseToFormula_satisfies_iff hc a, ih hcs]
      constructor
      · intro h d hd
        rcases List.mem_cons.mp hd with hdc | hdcs
        · subst d
          exact h.1
        · exact h.2 d hdcs
      · intro h
        exact ⟨h c (by simp), fun d hd => h d (by simp [hd])⟩

theorem threeCNFToFormula_satisfies_iff (φ : ThreeCNF) (a : Assignment) :
    Formula.Satisfies (threeCNFToFormula φ) a ↔ φ.Satisfies a :=
  cnfToFormula_satisfies_iff φ.clauses φ.isThree a

theorem threeCNFToFormula_satisfiable_iff (φ : ThreeCNF) :
    Formula.Satisfiable (threeCNFToFormula φ) ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (threeCNFToFormula_satisfies_iff φ a).1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (threeCNFToFormula_satisfies_iff φ a).2 h⟩

/-- Semantic reverse reduction from local 3SAT to the 3SAT-like CSP language. -/
noncomputable def threeSATToThreeSATLikeReduction :
    SemanticReduction threeSATDecisionProblem threeSATLikeDecisionProblem where
  f := threeCNFToFormula
  correct := by
    intro φ
    exact (threeCNFToFormula_satisfiable_iff φ).symm

theorem constraintOfLiterals_encodedLength (l₁ l₂ l₃ : Literal) :
    (Encoding.encodeConstraint (constraintOfLiterals l₁ l₂ l₃)).length =
      l₁.var + l₂.var + l₃.var + 8 := by
  rw [Encoding.encodeConstraint_length]
  simp [constraintOfLiterals]
  omega

theorem contradictionBlock_encodedLength :
    (Encoding.encodeFormula contradictionBlock).length = 16 := by
  simp [Encoding.encodeFormula, contradictionBlock, constraintOfLiterals_encodedLength,
    Literal.positive, Literal.negative]

theorem clauseToFormula_encodedLength_le {c : Clause} (hlen : c.length ≤ 3) :
    (Encoding.encodeFormula (clauseToFormula c)).length ≤
      16 * (ThreeSATEncoding.encodeClause c).length := by
  cases c with
  | nil =>
      simp [clauseToFormula, contradictionBlock_encodedLength, ThreeSATEncoding.encodeClause]
  | cons l₁ rest =>
      cases rest with
      | nil =>
          simp [clauseToFormula, Encoding.encodeFormula, constraintOfLiterals_encodedLength,
            ThreeSATEncoding.encodeClause, ThreeSATEncoding.encodeLiteral,
            ThreeSATEncoding.encodeNat, EncodedType.nat]
          omega
      | cons l₂ rest₂ =>
          cases rest₂ with
          | nil =>
              simp [clauseToFormula, Encoding.encodeFormula, constraintOfLiterals_encodedLength,
                ThreeSATEncoding.encodeClause, ThreeSATEncoding.encodeLiteral,
                ThreeSATEncoding.encodeNat, EncodedType.nat]
              omega
          | cons l₃ rest₃ =>
              cases rest₃ with
              | nil =>
                  simp [clauseToFormula, Encoding.encodeFormula, constraintOfLiterals_encodedLength,
                    ThreeSATEncoding.encodeClause, ThreeSATEncoding.encodeLiteral,
                    ThreeSATEncoding.encodeNat, EncodedType.nat]
                  omega
              | cons _ _ =>
                  simp at hlen

theorem cnfToFormula_encodedLength_le (clauses : CNF)
    (hThree : CNF.IsThreeCNF clauses) :
    (Encoding.encodeFormula (clauses.flatMap clauseToFormula)).length ≤
      16 * (ThreeSATEncoding.encodeThreeCNF { clauses := clauses, isThree := hThree }).length := by
  induction clauses with
  | nil =>
      simp [Encoding.encodeFormula, ThreeSATEncoding.encodeThreeCNF]
  | cons c cs ih =>
      have hc : c.length ≤ 3 := hThree c (by simp)
      have hcs : CNF.IsThreeCNF cs := by
        intro d hd
        exact hThree d (by simp [hd])
      have hcBound := clauseToFormula_encodedLength_le (c := c) hc
      have hcsBound := ih hcs
      simpa [Encoding.encodeFormula, ThreeSATEncoding.encodeThreeCNF, List.length_flatMap,
        Nat.mul_add] using Nat.add_le_add hcBound hcsBound

theorem threeCNFToFormula_encodedLength_le (φ : ThreeCNF) :
    (Encoding.encodeFormula (threeCNFToFormula φ)).length ≤
      16 * (ThreeSATEncoding.encodeThreeCNF φ).length := by
  simpa [threeCNFToFormula] using cnfToFormula_encodedLength_le φ.clauses φ.isThree

theorem threeCNFToFormula_linearSizeBound :
    LinearSizeBound
      (fun φ : ThreeCNF => SAT.threeSATDecisionProblem.Instance.inputSize φ)
      (fun ψ : Formula threeSATLikeLanguage => threeSATLikeDecisionProblem.Instance.inputSize ψ)
      threeCNFToFormula :=
  LinearSizeBound.intro_with 16 0 (by
    intro φ
    simpa [EncodedType.inputSize, SAT.threeSATDecisionProblem, SAT.threeSATSatLike,
      SAT.threeCNFEncodedType, threeSATLikeDecisionProblem, boolCSPDecisionProblem,
      boolCSPSatLike, formulaEncodedType]
      using threeCNFToFormula_encodedLength_le φ)

/-- Project-local costed reverse reduction from local 3SAT to the 3SAT-like CSP language. -/
noncomputable def threeSATToThreeSATLikeCostedReduction :
    CostedReduction threeSATDecisionProblem threeSATLikeDecisionProblem :=
  CostedReduction.ofCostedMap
    threeCNFToFormula
    threeSATToThreeSATLikeReduction.correct
    (CostedMap.of_encodedLinearSizeBound threeCNFToFormula_linearSizeBound)

/-- Costed-model Karp reverse reduction from local 3SAT to the 3SAT-like CSP language. -/
noncomputable def threeSATToThreeSATLikeKarpReduction :
    KarpReductionM CostedPolyTimeModel threeSATDecisionProblem threeSATLikeDecisionProblem :=
  threeSATToThreeSATLikeCostedReduction.toKarpReductionM

end ThreeSATLike
end Hardness
end CSP
end ComplexityReduction
