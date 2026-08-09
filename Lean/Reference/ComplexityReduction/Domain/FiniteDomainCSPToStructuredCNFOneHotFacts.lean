/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNFProgram

/-!
Semantic facts for the exactly-one blocks emitted by the direct structured
finite-domain CSP to CNF program.

The at-most-one part of the program deliberately contains both orders of every
pair of distinct domain values.  The proofs below characterize that concrete
ordered-pair encoding directly.
-/

namespace ComplexityReduction
namespace Domain
namespace FiniteDomainCSPToStructuredCNFOneHotFacts

open ComplexityReduction
open FiniteDomainCSPExecutableContract
open FiniteDomainCSPToStructuredCNFProgram

/-- Exactly one in-range value code is true for one source variable. -/
def OneHotAt (domainSize sourceVar : Nat) (assignment : SAT.Assignment) : Prop :=
  ∃ value, value < domainSize ∧
    assignment (Nat.pair sourceVar value) = true ∧
      ∀ other, other < domainSize →
        assignment (Nat.pair sourceVar other) = true → other = value

private theorem fixedValueClause_eq_map (entries : List (Nat × Bool)) (sourceVar : Nat) :
    fixedValueClause entries sourceVar =
      entries.map fun entry => valueLiteral entry.1 entry.2 sourceVar := by
  induction entries with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      simp [fixedValueClause, inductionHypothesis]

private theorem variableCNFFromRows_eq_map
    (rows : List (List (Nat × Bool))) (sourceVar : Nat) :
    variableCNFFromRows rows sourceVar =
      rows.map fun row => fixedValueClause row sourceVar := by
  induction rows with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      simp [variableCNFFromRows, inductionHypothesis]

private theorem mem_distinctValuePairs_iff (domainSize left right : Nat) :
    (left, right) ∈ distinctValuePairs domainSize ↔
      left < domainSize ∧ right < domainSize ∧ left ≠ right := by
  simp [distinctValuePairs, and_assoc]

private theorem atLeastOneClause_satisfies_iff
    (domainSize sourceVar : Nat) (assignment : SAT.Assignment) :
    SAT.Clause.Satisfies
        (fixedValueClause
          ((List.range domainSize).map fun value => (value, false)) sourceVar)
        assignment ↔
      ∃ value, value < domainSize ∧
        assignment (Nat.pair sourceVar value) = true := by
  rw [fixedValueClause_eq_map]
  simp only [List.map_map]
  constructor
  · rintro ⟨literal, literalMem, literalTrue⟩
    rcases List.mem_map.mp literalMem with ⟨value, valueMem, rfl⟩
    exact ⟨value, List.mem_range.mp valueMem, by
      simpa [valueLiteral, SAT.Literal.eval] using literalTrue⟩
  · rintro ⟨value, valueBound, valueTrue⟩
    refine ⟨valueLiteral value false sourceVar, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨value, List.mem_range.mpr valueBound, rfl⟩
    · simpa [valueLiteral, SAT.Literal.eval] using valueTrue

private theorem atMostOneClauses_satisfies_iff
    (domainSize sourceVar : Nat) (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies
        ((distinctValuePairs domainSize).map fun pair =>
          fixedValueClause [(pair.1, true), (pair.2, true)] sourceVar)
        assignment ↔
      ∀ left, left < domainSize →
        ∀ right, right < domainSize → left ≠ right →
          ¬(assignment (Nat.pair sourceVar left) = true ∧
            assignment (Nat.pair sourceVar right) = true) := by
  constructor
  · intro satisfies left leftBound right rightBound distinct bothTrue
    have pairMem : (left, right) ∈ distinctValuePairs domainSize :=
      (mem_distinctValuePairs_iff domainSize left right).2
        ⟨leftBound, rightBound, distinct⟩
    have clauseMem :
        fixedValueClause [(left, true), (right, true)] sourceVar ∈
          (distinctValuePairs domainSize).map fun pair =>
            fixedValueClause [(pair.1, true), (pair.2, true)] sourceVar :=
      List.mem_map.mpr ⟨(left, right), pairMem, rfl⟩
    have clauseTrue :=
      satisfies (fixedValueClause [(left, true), (right, true)] sourceVar) clauseMem
    rcases bothTrue with ⟨leftTrue, rightTrue⟩
    simp [SAT.Clause.Satisfies, fixedValueClause, valueLiteral,
      SAT.Literal.eval, leftTrue, rightTrue] at clauseTrue
  · intro unique clause clauseMem
    rcases List.mem_map.mp clauseMem with ⟨pair, pairMem, rfl⟩
    have pairFacts :=
      (mem_distinctValuePairs_iff domainSize pair.1 pair.2).1 pairMem
    by_cases leftTrue : assignment (Nat.pair sourceVar pair.1) = true
    · have rightNotTrue : assignment (Nat.pair sourceVar pair.2) ≠ true := by
        intro rightTrue
        exact unique pair.1 pairFacts.1 pair.2 pairFacts.2.1 pairFacts.2.2
          ⟨leftTrue, rightTrue⟩
      have rightFalse : assignment (Nat.pair sourceVar pair.2) = false :=
        Bool.eq_false_of_not_eq_true rightNotTrue
      refine ⟨valueLiteral pair.2 true sourceVar, ?_, ?_⟩
      · simp [fixedValueClause]
      · simp [valueLiteral, SAT.Literal.eval, rightFalse]
    · have leftFalse : assignment (Nat.pair sourceVar pair.1) = false :=
        Bool.eq_false_of_not_eq_true leftTrue
      refine ⟨valueLiteral pair.1 true sourceVar, ?_, ?_⟩
      · simp [fixedValueClause]
      · simp [valueLiteral, SAT.Literal.eval, leftFalse]

private theorem exactlyOneCNF_eq {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (sourceVar : Nat) :
    exactlyOneCNF contract sourceVar =
      fixedValueClause
          ((List.range contract.domainSize).map fun value => (value, false)) sourceVar ::
        ((distinctValuePairs contract.domainSize).map fun pair =>
          fixedValueClause [(pair.1, true), (pair.2, true)] sourceVar) := by
  simp [exactlyOneCNF, exactlyOneRows, variableCNFFromRows_eq_map,
    List.map_map]

private theorem cnf_satisfies_singleton (clause : SAT.Clause)
    (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies [clause] assignment ↔
      SAT.Clause.Satisfies clause assignment := by
  constructor
  · intro satisfies
    exact satisfies clause (by simp)
  · intro clauseTrue candidate candidateMem
    have candidateEq : candidate = clause := by simpa using candidateMem
    subst candidate
    exact clauseTrue

/-- The program's concrete ordered-pair exactly-one block is semantically exact. -/
theorem exactlyOneCNF_satisfies_iff {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (sourceVar : Nat)
    (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies (exactlyOneCNF contract sourceVar) assignment ↔
      OneHotAt contract.domainSize sourceVar assignment := by
  rw [exactlyOneCNF_eq]
  rw [show
    fixedValueClause
          ((List.range contract.domainSize).map fun value => (value, false)) sourceVar ::
        ((distinctValuePairs contract.domainSize).map fun pair =>
          fixedValueClause [(pair.1, true), (pair.2, true)] sourceVar) =
      [fixedValueClause
          ((List.range contract.domainSize).map fun value => (value, false)) sourceVar] ++
        ((distinctValuePairs contract.domainSize).map fun pair =>
          fixedValueClause [(pair.1, true), (pair.2, true)] sourceVar) by rfl]
  rw [SAT.CNF.satisfies_append, cnf_satisfies_singleton]
  rw [atLeastOneClause_satisfies_iff, atMostOneClauses_satisfies_iff]
  constructor
  · rintro ⟨⟨value, valueBound, valueTrue⟩, atMostOne⟩
    refine ⟨value, valueBound, valueTrue, ?_⟩
    intro other otherBound otherTrue
    by_contra distinct
    exact atMostOne other otherBound value valueBound distinct
      ⟨otherTrue, valueTrue⟩
  · rintro ⟨value, valueBound, valueTrue, unique⟩
    refine ⟨⟨value, valueBound, valueTrue⟩, ?_⟩
    intro left leftBound right rightBound distinct bothTrue
    have leftEq := unique left leftBound bothTrue.1
    have rightEq := unique right rightBound bothTrue.2
    exact distinct (leftEq.trans rightEq.symm)

/-- A flattened family of exactly-one blocks is satisfied exactly when every
scope occurrence is one-hot.  Duplicate scope variables therefore only
duplicate an already identical requirement. -/
theorem scopeExactlyOneCNF_satisfies_iff {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) (scope : List Nat)
    (assignment : SAT.Assignment) :
    SAT.CNF.Satisfies (scopeExactlyOneCNF contract scope) assignment ↔
      ∀ sourceVar, sourceVar ∈ scope →
        OneHotAt contract.domainSize sourceVar assignment := by
  constructor
  · intro satisfies sourceVar sourceVarMem
    apply (exactlyOneCNF_satisfies_iff contract sourceVar assignment).1
    intro clause clauseMem
    apply satisfies clause
    rw [scopeExactlyOneCNF, List.mem_flatten]
    exact ⟨exactlyOneCNF contract sourceVar,
      List.mem_map.mpr ⟨sourceVar, sourceVarMem, rfl⟩, clauseMem⟩
  · intro oneHot clause clauseMem
    rw [scopeExactlyOneCNF, List.mem_flatten] at clauseMem
    rcases clauseMem with ⟨block, blockMem, clauseMem⟩
    rcases List.mem_map.mp blockMem with ⟨sourceVar, sourceVarMem, rfl⟩
    exact (exactlyOneCNF_satisfies_iff contract sourceVar assignment).2
      (oneHot sourceVar sourceVarMem) clause clauseMem

end FiniteDomainCSPToStructuredCNFOneHotFacts
end Domain
end ComplexityReduction
