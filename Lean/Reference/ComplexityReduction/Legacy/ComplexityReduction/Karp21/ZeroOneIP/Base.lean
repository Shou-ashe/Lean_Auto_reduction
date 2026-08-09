/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.IntegerProgramming
import Mathlib.Tactic

/-!
P15c arithmetic target: local 3SAT to 0-1 Integer Programming.

The first certificate below is the legacy constant-output-size witness
enumeration route.  The textbook route at the end of the file is the direct
clause linearization: source variables become 0-1 variables and each clause
becomes one linear inequality.
-/

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-- Bounded assignments that satisfy the source 3CNF. -/
noncomputable def satisfyingAssignments (φ : SAT.ThreeCNF) :
    List (Fin (Clique.cnfVarBound φ.clauses) → Bool) := by
  classical
  exact (Clique.assignmentList (Clique.cnfVarBound φ.clauses)).filter fun a =>
    decide (φ.Satisfies (Clique.boundedAssignment (Clique.cnfVarBound φ.clauses) a))

theorem mem_satisfyingAssignments_iff (φ : SAT.ThreeCNF)
    (a : Fin (Clique.cnfVarBound φ.clauses) → Bool) :
    a ∈ satisfyingAssignments φ ↔
      a ∈ Clique.assignmentList (Clique.cnfVarBound φ.clauses) ∧
        φ.Satisfies (Clique.boundedAssignment (Clique.cnfVarBound φ.clauses) a) := by
  classical
  simp [satisfyingAssignments]

theorem threeSAT_isYes_iff_satisfyingAssignments_pos (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ 0 < (satisfyingAssignments φ).length := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    let n := Clique.cnfVarBound φ.clauses
    let f : Fin n → Bool := fun i => a i.val
    have hSatBounded : φ.Satisfies (Clique.boundedAssignment n f) :=
      Clique.threeCNF_satisfies_bounded_of_satisfies hSat
    have hf : f ∈ satisfyingAssignments φ := by
      simp [satisfyingAssignments, n, f, Clique.mem_assignmentList n f, hSatBounded]
    exact List.length_pos_of_mem hf
  · intro hPos
    cases hList : satisfyingAssignments φ with
    | nil =>
        simp [hList] at hPos
    | cons f rest =>
        have hf : f ∈ satisfyingAssignments φ := by
          simp [hList]
        have hSat :=
          (mem_satisfyingAssignments_iff φ f).1 hf |>.2
        exact (SAT.threeSATDecisionProblem_isYes_iff φ).2
          ⟨Clique.boundedAssignment (Clique.cnfVarBound φ.clauses) f, hSat⟩

/-- Constraint row `-x₀ - ... - xₘ₋₁ ≤ -1`, forcing at least one selected variable. -/
def atLeastOneConstraint (m : Nat) : List Int × Int :=
  (List.replicate m (-1), -1)

/-- Canonical 0-1 assignment selecting only the first generated IP variable. -/
def firstSelected : BoolAssignment :=
  fun i => if i = 0 then true else false

theorem firstSelected_pos_false {i : Nat} (hi : 0 < i) :
    firstSelected i = false := by
  simp [firstSelected, Nat.ne_of_gt hi]

theorem rowValueFrom_firstSelected_pos (coeffs : List Int) {i : Nat} (hi : 0 < i) :
    rowValueFrom firstSelected i coeffs = 0 := by
  induction coeffs generalizing i with
  | nil =>
      simp [rowValueFrom]
  | cons c cs ih =>
      have hfalse : firstSelected i = false := firstSelected_pos_false hi
      have hi' : 0 < i + 1 := by omega
      simp [rowValueFrom, boolValue, hfalse, ih hi']

theorem rowValue_firstSelected_replicate_neg_one_succ (m : Nat) :
    rowValue firstSelected (List.replicate (Nat.succ m) (-1)) = -1 := by
  have htail :
      rowValueFrom firstSelected 1 (List.replicate m (-1)) = 0 :=
    rowValueFrom_firstSelected_pos (List.replicate m (-1)) (i := 1) (by omega)
  change rowValue firstSelected ((-1 : Int) :: List.replicate m (-1)) = -1
  simp [rowValue, rowValueFrom, boolValue, firstSelected, htail]

theorem firstSelected_satisfies_atLeastOneConstraint_succ (m : Nat) :
    SatisfiesConstraint firstSelected (atLeastOneConstraint (Nat.succ m)) := by
  change rowValue firstSelected (List.replicate (Nat.succ m) (-1)) ≤ (-1 : Int)
  rw [rowValue_firstSelected_replicate_neg_one_succ]

theorem atLeastOneConstraint_satisfied_length_pos {a : BoolAssignment} {m : Nat}
    (h : SatisfiesConstraint a (atLeastOneConstraint m)) :
    0 < m := by
  cases m with
  | zero =>
      simp [SatisfiesConstraint, atLeastOneConstraint, rowValue, rowValueFrom] at h
  | succ m =>
      omega

/-- P15c syntax map from local 3SAT to 0-1 integer programming. -/
noncomputable def map (φ : SAT.ThreeCNF) : IntegerProgrammingInput :=
  { numVariables := (satisfyingAssignments φ).length
    constraints := [atLeastOneConstraint (satisfyingAssignments φ).length] }

theorem map_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ ZeroOneIntegerProgramming (map φ) := by
  constructor
  · intro hYes
    have hPos := (threeSAT_isYes_iff_satisfyingAssignments_pos φ).1 hYes
    refine ⟨firstSelected, ?_⟩
    intro constraint hConstraint
    have hAtLeastOne :
        SatisfiesConstraint firstSelected
          (atLeastOneConstraint (satisfyingAssignments φ).length) := by
      cases hLen : (satisfyingAssignments φ).length with
      | zero =>
          omega
      | succ m =>
          simpa [hLen] using firstSelected_satisfies_atLeastOneConstraint_succ m
    have hEq :
        constraint = atLeastOneConstraint (satisfyingAssignments φ).length := by
      simpa [map] using hConstraint
    simpa [hEq] using hAtLeastOne
  · rintro ⟨a, hAll⟩
    have hConstraint :
        SatisfiesConstraint a
          (atLeastOneConstraint (satisfyingAssignments φ).length) := by
      exact hAll _ (by simp [map])
    have hPos := atLeastOneConstraint_satisfied_length_pos hConstraint
    exact (threeSAT_isYes_iff_satisfyingAssignments_pos φ).2 hPos

/-- Costed Karp reduction from local 3SAT to 0-1 Integer Programming. -/
noncomputable def threeSATToZeroOneIPTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem
      zeroOneIntegerProgrammingDecisionProblem := by
  simpa [zeroOneIntegerProgrammingDecisionProblem, integerProgrammingDecisionProblem,
    integerProgrammingEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.ZeroOneIntegerProgramming
      map
      map_correct

/-- Costed Karp reduction from local 3SAT to 0-1 Integer Programming. -/
noncomputable def threeSATToZeroOneIPKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      zeroOneIntegerProgrammingDecisionProblem :=
  threeSATToZeroOneIPTMBackedKarpReduction.toCostedKarpReduction

/-- 0-1 Integer Programming is locally in NP for the project-local costed model. -/
theorem zeroOneIPInNP :
    InNPEnc CostedPolyTimeModel zeroOneIntegerProgrammingDecisionProblem :=
  decidableInNP zeroOneIntegerProgrammingDecisionProblem

/-- The structured finite-alphabet 0-1 IP encoding is faithful. -/
theorem zeroOneIPStructuredEncoding_faithful :
    zeroOneIntegerProgrammingStructuredDecisionProblem.FaithfulEncoding where
  injective := integerProgrammingStructuredEncodedType_encode_injective

theorem zeroOneIPStructuredEncoding_predicateRespects :
    zeroOneIntegerProgrammingStructuredDecisionProblem.PredicateRespectsEncoding :=
  zeroOneIPStructuredEncoding_faithful.predicateRespects

theorem zeroOneIPStructuredEncoding_accepts_encode_iff (I : IntegerProgrammingInput) :
    zeroOneIntegerProgrammingStructuredDecisionProblem.toEncodedLanguage.accepts
        (integerProgrammingStructuredEncodedType.encode I) ↔
      ZeroOneIntegerProgramming I :=
  zeroOneIPStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- The binary-numeric finite-alphabet 0-1 IP encoding is faithful. -/
theorem zeroOneIPBinaryStructuredEncoding_faithful :
    zeroOneIntegerProgrammingBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := integerProgrammingBinaryStructuredEncodedType_encode_injective

theorem zeroOneIPBinaryStructuredEncoding_predicateRespects :
    zeroOneIntegerProgrammingBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  zeroOneIPBinaryStructuredEncoding_faithful.predicateRespects

theorem zeroOneIPBinaryStructuredEncoding_accepts_encode_iff (I : IntegerProgrammingInput) :
    zeroOneIntegerProgrammingBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (integerProgrammingBinaryStructuredEncodedType.encode I) ↔
      ZeroOneIntegerProgramming I :=
  zeroOneIPBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Local NP-completeness of 0-1 Integer Programming via local 3SAT. -/
theorem zeroOneIPNPComplete :
    NPCompleteEnc CostedPolyTimeModel zeroOneIntegerProgrammingDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    zeroOneIntegerProgrammingDecisionProblem
    threeSATToZeroOneIPKarpReduction
    zeroOneIPInNP

/-! ### Textbook direct clause-linearization route -/

/-- Linear coefficient contributed by one literal at variable position `i`. -/
def literalCoeffAt (l : SAT.Literal) (i : Nat) : Int :=
  if i = l.var then if l.neg then 1 else -1 else 0

/-- One literal's contribution to the left-hand side under a 0-1 assignment. -/
def literalLinearValue (a : BoolAssignment) (l : SAT.Literal) : Int :=
  if l.neg then boolValue a l.var else -boolValue a l.var

/-- The contribution of a literal to the clause bound: `1` exactly for negated literals. -/
def literalNegWeight (l : SAT.Literal) : Int :=
  if l.neg then 1 else 0

/-- Sum of literal left-hand side contributions for a clause. -/
def clauseLinearValue (a : BoolAssignment) : SAT.Clause → Int
  | [] => 0
  | l :: ls => literalLinearValue a l + clauseLinearValue a ls

/-- Number of negated literals in the clause, as an integer. -/
def clauseNegWeight : SAT.Clause → Int
  | [] => 0
  | l :: ls => literalNegWeight l + clauseNegWeight ls

/-- Bound for the inequality encoding "at least one literal in the clause is true". -/
def clauseBound (c : SAT.Clause) : Int :=
  clauseNegWeight c - 1

/-- Pointwise addition of coefficient rows, padding by the remaining suffix. -/
def addRows : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addRows xs ys

/-- The all-zero coefficient row of length `n`. -/
def zeroRow : Nat → List Int
  | 0 => []
  | n + 1 => 0 :: zeroRow n

/-- Coefficient row for one literal, starting at source variable position `start`. -/
def literalRowFrom (start : Nat) : Nat → SAT.Literal → List Int
  | 0, _ => []
  | n + 1, l => literalCoeffAt l start :: literalRowFrom (start + 1) n l

/-- Coefficient row for one literal over the first `n` source variables. -/
def literalRow (n : Nat) (l : SAT.Literal) : List Int :=
  literalRowFrom 0 n l

/-- Coefficient row for a clause, aggregating duplicate variable occurrences. -/
def clauseRow (n : Nat) : SAT.Clause → List Int
  | [] => zeroRow n
  | l :: ls => addRows (literalRow n l) (clauseRow n ls)

/-- The IP row constraint corresponding to a source clause. -/
def clauseConstraint (n : Nat) (c : SAT.Clause) : List Int × Int :=
  (clauseRow n c, clauseBound c)

theorem rowValueFrom_zeroRow (a : BoolAssignment) (i n : Nat) :
    rowValueFrom a i (zeroRow n) = 0 := by
  induction n generalizing i with
  | zero =>
      simp [zeroRow, rowValueFrom]
  | succ n ih =>
      simp [zeroRow, rowValueFrom, boolValue, ih]

theorem rowValue_zeroRow (a : BoolAssignment) (n : Nat) :
    rowValue a (zeroRow n) = 0 := by
  simpa [rowValue] using rowValueFrom_zeroRow a 0 n

theorem rowValueFrom_addRows (a : BoolAssignment) (i : Nat) (xs ys : List Int) :
    rowValueFrom a i (addRows xs ys) =
      rowValueFrom a i xs + rowValueFrom a i ys := by
  induction xs generalizing i ys with
  | nil =>
      cases ys <;> simp [addRows, rowValueFrom]
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [addRows, rowValueFrom]
      | cons y ys =>
          simp [addRows, rowValueFrom, ih]
          ring

theorem rowValue_addRows (a : BoolAssignment) (xs ys : List Int) :
    rowValue a (addRows xs ys) = rowValue a xs + rowValue a ys := by
  simpa [rowValue] using rowValueFrom_addRows a 0 xs ys

theorem literalCoeffAt_mul_boolValue_eq_linear (a : BoolAssignment) (l : SAT.Literal) :
    literalCoeffAt l l.var * boolValue a l.var = literalLinearValue a l := by
  cases l with
  | mk var neg =>
      cases neg <;> cases h : a var <;>
        simp [literalCoeffAt, literalLinearValue, boolValue, h]

theorem rowValueFrom_literalRowFrom_eq_zero_of_lt
    (a : BoolAssignment) (l : SAT.Literal) {start len : Nat}
    (hvar : l.var < start) :
    rowValueFrom a start (literalRowFrom start len l) = 0 := by
  induction len generalizing start with
  | zero =>
      simp [literalRowFrom, rowValueFrom]
  | succ len ih =>
      have hne : ¬ start = l.var := by omega
      have htail : rowValueFrom a (start + 1)
          (literalRowFrom (start + 1) len l) = 0 :=
        ih (start := start + 1) (by omega)
      simp [literalRowFrom, rowValueFrom, literalCoeffAt, hne, htail]

theorem rowValueFrom_literalRowFrom_eq_linear_of_mem
    (a : BoolAssignment) (l : SAT.Literal) {start len : Nat}
    (hlo : start ≤ l.var) (hhi : l.var < start + len) :
    rowValueFrom a start (literalRowFrom start len l) = literalLinearValue a l := by
  induction len generalizing start with
  | zero =>
      omega
  | succ len ih =>
      by_cases hEq : start = l.var
      · have htail : rowValueFrom a (start + 1)
            (literalRowFrom (start + 1) len l) = 0 :=
          rowValueFrom_literalRowFrom_eq_zero_of_lt a l (start := start + 1)
            (len := len) (by omega)
        have htail' : rowValueFrom a (l.var + 1)
            (literalRowFrom (l.var + 1) len l) = 0 := by
          simpa [hEq] using htail
        simp [literalRowFrom, rowValueFrom, literalCoeffAt, hEq, htail',
          literalLinearValue]
      · have hlt : start < l.var := by omega
        have htail : rowValueFrom a (start + 1)
            (literalRowFrom (start + 1) len l) = literalLinearValue a l :=
          ih (start := start + 1) (by omega) (by omega)
        simp [literalRowFrom, rowValueFrom, literalCoeffAt, hEq, htail]

theorem rowValue_literalRow_eq_linear
    (a : BoolAssignment) {n : Nat} {l : SAT.Literal} (hvar : l.var < n) :
    rowValue a (literalRow n l) = literalLinearValue a l := by
  simpa [rowValue, literalRow] using
    rowValueFrom_literalRowFrom_eq_linear_of_mem a l (start := 0) (len := n)
      (Nat.zero_le _) (by simpa using hvar)

theorem rowValue_clauseRow_eq_linear
    (a : BoolAssignment) {n : Nat} {c : SAT.Clause}
    (hvars : ∀ l ∈ c, l.var < n) :
    rowValue a (clauseRow n c) = clauseLinearValue a c := by
  induction c with
  | nil =>
      simp [clauseRow, clauseLinearValue, rowValue_zeroRow]
  | cons l ls ih =>
      have hl : l.var < n := hvars l (by simp)
      have hls : ∀ m ∈ ls, m.var < n := by
        intro m hm
        exact hvars m (by simp [hm])
      simp [clauseRow, clauseLinearValue, rowValue_addRows,
        rowValue_literalRow_eq_linear a hl, ih hls]

theorem literalLinearValue_le_negWeight (a : BoolAssignment) (l : SAT.Literal) :
    literalLinearValue a l ≤ literalNegWeight l := by
  cases l with
  | mk var neg =>
      cases neg <;> cases h : a var <;>
        simp [literalLinearValue, literalNegWeight, boolValue, h]

theorem literalLinearValue_eq_negWeight_of_eval_false
    {a : BoolAssignment} {l : SAT.Literal} (hEval : l.eval a = false) :
    literalLinearValue a l = literalNegWeight l := by
  cases l with
  | mk var neg =>
      cases neg <;> cases h : a var <;>
        simp [SAT.Literal.eval, literalLinearValue, literalNegWeight, boolValue, h] at hEval ⊢

theorem literalLinearValue_le_negWeight_sub_one_of_eval_true
    {a : BoolAssignment} {l : SAT.Literal} (hEval : l.eval a = true) :
    literalLinearValue a l ≤ literalNegWeight l - 1 := by
  cases l with
  | mk var neg =>
      cases neg <;> cases h : a var <;>
        simp [SAT.Literal.eval, literalLinearValue, literalNegWeight, boolValue, h] at hEval ⊢

theorem clauseLinearValue_le_negWeight (a : BoolAssignment) (c : SAT.Clause) :
    clauseLinearValue a c ≤ clauseNegWeight c := by
  induction c with
  | nil =>
      simp [clauseLinearValue, clauseNegWeight]
  | cons l ls ih =>
      have hl := literalLinearValue_le_negWeight a l
      simp [clauseLinearValue, clauseNegWeight]
      linarith

theorem clause_satisfies_iff_linearValue_le_bound
    (c : SAT.Clause) (a : BoolAssignment) :
    SAT.Clause.Satisfies c a ↔ clauseLinearValue a c ≤ clauseBound c := by
  induction c with
  | nil =>
      simp [SAT.Clause.Satisfies, clauseLinearValue, clauseBound, clauseNegWeight]
  | cons l ls ih =>
      by_cases hEval : l.eval a = true
      · constructor
        · intro _hSat
          have hl := literalLinearValue_le_negWeight_sub_one_of_eval_true
            (a := a) (l := l) hEval
          have hls := clauseLinearValue_le_negWeight a ls
          simp [clauseLinearValue, clauseBound, clauseNegWeight]
          linarith
        · intro _h
          exact ⟨l, by simp, hEval⟩
      · have hEvalFalse : l.eval a = false := by
          cases hlit : l.eval a <;> simp_all
        have hlEq := literalLinearValue_eq_negWeight_of_eval_false
          (a := a) (l := l) hEvalFalse
        have hSatTail : SAT.Clause.Satisfies (l :: ls) a ↔ SAT.Clause.Satisfies ls a := by
          constructor
          · rintro ⟨m, hm, hmEval⟩
            simp at hm
            rcases hm with rfl | hm
            · simp [hEvalFalse] at hmEval
            · exact ⟨m, hm, hmEval⟩
          · rintro ⟨m, hm, hmEval⟩
            exact ⟨m, by simp [hm], hmEval⟩
        constructor
        · intro hSat
          have hTailIneq := ih.mp (hSatTail.mp hSat)
          have hTailIneq' :
              clauseLinearValue a ls ≤ clauseNegWeight ls - 1 := by
            simpa [clauseBound] using hTailIneq
          change literalLinearValue a l + clauseLinearValue a ls ≤
            literalNegWeight l + clauseNegWeight ls - 1
          rw [hlEq]
          linarith
        · intro hIneq
          have hTailIneq : clauseLinearValue a ls ≤ clauseBound ls := by
            have hIneq' :
                literalLinearValue a l + clauseLinearValue a ls ≤
                  literalNegWeight l + clauseNegWeight ls - 1 := by
              simpa [clauseLinearValue, clauseBound, clauseNegWeight] using hIneq
            rw [hlEq] at hIneq'
            have hTailIneq' :
                clauseLinearValue a ls ≤ clauseNegWeight ls - 1 := by
              linarith
            simpa [clauseBound] using hTailIneq'
          exact hSatTail.mpr (ih.mpr hTailIneq)

/-- P15x textbook map: one 0-1 variable per source Boolean variable. -/
def textbookMap (φ : SAT.ThreeCNF) : IntegerProgrammingInput where
  numVariables := Clique.cnfVarBound φ.clauses
  constraints := φ.clauses.map (clauseConstraint (Clique.cnfVarBound φ.clauses))

theorem textbookMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ ZeroOneIntegerProgramming (textbookMap φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    refine ⟨a, ?_⟩
    intro constraint hConstraint
    rcases List.mem_map.mp hConstraint with ⟨c, hc, rfl⟩
    have hVars : ∀ l ∈ c, l.var < Clique.cnfVarBound φ.clauses := by
      intro l hl
      exact Clique.var_lt_cnfVarBound_of_mem hc hl
    have hRow := rowValue_clauseRow_eq_linear a (n := Clique.cnfVarBound φ.clauses)
      (c := c) hVars
    have hClause := (clause_satisfies_iff_linearValue_le_bound c a).1 (hSat c hc)
    change rowValue a (clauseRow (Clique.cnfVarBound φ.clauses) c) ≤ clauseBound c
    rw [hRow]
    exact hClause
  · rintro ⟨a, hAll⟩
    refine (SAT.threeSATDecisionProblem_isYes_iff φ).2 ?_
    refine ⟨a, ?_⟩
    intro c hc
    have hConstraint :
        SatisfiesConstraint a
          (clauseConstraint (Clique.cnfVarBound φ.clauses) c) := by
      have hMem :
          clauseConstraint (Clique.cnfVarBound φ.clauses) c ∈
            (textbookMap φ).constraints := by
        change clauseConstraint (Clique.cnfVarBound φ.clauses) c ∈
          φ.clauses.map (clauseConstraint (Clique.cnfVarBound φ.clauses))
        exact List.mem_map.mpr ⟨c, hc, rfl⟩
      exact hAll _ hMem
    have hVars : ∀ l ∈ c, l.var < Clique.cnfVarBound φ.clauses := by
      intro l hl
      exact Clique.var_lt_cnfVarBound_of_mem hc hl
    have hRow := rowValue_clauseRow_eq_linear a (n := Clique.cnfVarBound φ.clauses)
      (c := c) hVars
    change rowValue a (clauseRow (Clique.cnfVarBound φ.clauses) c) ≤ clauseBound c
      at hConstraint
    rw [hRow] at hConstraint
    exact (clause_satisfies_iff_linearValue_le_bound c a).2 hConstraint

def boundedTextbookMap (n : Nat) (φ : SAT.ThreeCNF) : IntegerProgrammingInput where
  numVariables := n
  constraints := φ.clauses.map (clauseConstraint n)

theorem boundedTextbookMap_correct_of_cnfVarBound_le
    (φ : SAT.ThreeCNF) {n : Nat} (hn : Clique.cnfVarBound φ.clauses ≤ n) :
    SAT.threeSATDecisionProblem.isYes φ ↔ ZeroOneIntegerProgramming (boundedTextbookMap n φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    refine ⟨a, ?_⟩
    intro constraint hConstraint
    rcases List.mem_map.mp hConstraint with ⟨c, hc, rfl⟩
    have hVars : ∀ l ∈ c, l.var < n := by
      intro l hl
      exact Nat.lt_of_lt_of_le (Clique.var_lt_cnfVarBound_of_mem hc hl) hn
    have hRow := rowValue_clauseRow_eq_linear a (n := n) (c := c) hVars
    have hClause := (clause_satisfies_iff_linearValue_le_bound c a).1 (hSat c hc)
    change rowValue a (clauseRow n c) ≤ clauseBound c
    rw [hRow]
    exact hClause
  · rintro ⟨a, hAll⟩
    refine (SAT.threeSATDecisionProblem_isYes_iff φ).2 ?_
    refine ⟨a, ?_⟩
    intro c hc
    have hConstraint :
        SatisfiesConstraint a (clauseConstraint n c) := by
      have hMem : clauseConstraint n c ∈ (boundedTextbookMap n φ).constraints := by
        change clauseConstraint n c ∈ φ.clauses.map (clauseConstraint n)
        exact List.mem_map.mpr ⟨c, hc, rfl⟩
      exact hAll _ hMem
    have hVars : ∀ l ∈ c, l.var < n := by
      intro l hl
      exact Nat.lt_of_lt_of_le (Clique.var_lt_cnfVarBound_of_mem hc hl) hn
    have hRow := rowValue_clauseRow_eq_linear a (n := n) (c := c) hVars
    change rowValue a (clauseRow n c) ≤ clauseBound c at hConstraint
    rw [hRow] at hConstraint
    exact (clause_satisfies_iff_linearValue_le_bound c a).2 hConstraint

def threeSATToZeroOneIPStructuredTMMap (φ : SAT.ThreeCNF) : IntegerProgrammingInput :=
  boundedTextbookMap (threeCNFStructuredEncodedType.inputSize φ) φ

/-- Costed textbook Karp reduction from local 3SAT to 0-1 Integer Programming. -/
noncomputable def threeSATToZeroOneIP_textbookTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem
      zeroOneIntegerProgrammingDecisionProblem := by
  simpa [zeroOneIntegerProgrammingDecisionProblem, integerProgrammingDecisionProblem,
    integerProgrammingEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.ZeroOneIntegerProgramming
      textbookMap
      textbookMap_correct

/-- Costed textbook Karp reduction from local 3SAT to 0-1 Integer Programming. -/
noncomputable def threeSATToZeroOneIP_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      zeroOneIntegerProgrammingDecisionProblem :=
  threeSATToZeroOneIP_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Local NP-completeness of 0-1 Integer Programming via the textbook 3SAT map. -/
theorem zeroOneIP_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel zeroOneIntegerProgrammingDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    zeroOneIntegerProgrammingDecisionProblem
    threeSATToZeroOneIP_textbookKarpReduction
    zeroOneIPInNP

/-! ### Structured finite-alphabet transport bounds -/

theorem integerProgrammingStructured_inputSize_eq (I : IntegerProgrammingInput) :
    integerProgrammingStructuredEncodedType.inputSize I =
      I.numVariables + constraintListStructuredEncodedType.inputSize I.constraints + 2 := by
  change integerProgrammingTupleStructuredEncodedType.inputSize (I.numVariables, I.constraints) =
    I.numVariables + constraintListStructuredEncodedType.inputSize I.constraints + 2
  simp [integerProgrammingTupleStructuredEncodedType]
  omega

theorem literalRowFrom_length (start n : Nat) (l : SAT.Literal) :
    (literalRowFrom start n l).length = n := by
  induction n generalizing start with
  | zero =>
      simp [literalRowFrom]
  | succ n ih =>
      simp [literalRowFrom, ih]

theorem literalRow_length (n : Nat) (l : SAT.Literal) :
    (literalRow n l).length = n := by
  simp [literalRow, literalRowFrom_length]

theorem zeroRow_length (n : Nat) :
    (zeroRow n).length = n := by
  induction n with
  | zero =>
      simp [zeroRow]
  | succ n ih =>
      simp [zeroRow, ih]

theorem addRows_length_of_eq {xs ys : List Int} (h : xs.length = ys.length) :
    (addRows xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [addRows] at h ⊢
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at h
      | cons y ys =>
          simp [addRows, ih (by simpa using h)]

theorem clauseRow_length (n : Nat) (c : SAT.Clause) :
    (clauseRow n c).length = n := by
  induction c with
  | nil =>
      simp [clauseRow, zeroRow_length]
  | cons l ls ih =>
      calc
        (clauseRow n (l :: ls)).length
            = (addRows (literalRow n l) (clauseRow n ls)).length := rfl
        _ = (literalRow n l).length := addRows_length_of_eq (by simp [literalRow_length, ih])
        _ = n := literalRow_length n l

theorem cliqueClauseVarBound_eq_satClauseVarBound (c : SAT.Clause) :
    Clique.clauseVarBound c = SAT.Clause.varBound c := by
  induction c with
  | nil =>
      simp [Clique.clauseVarBound, SAT.Clause.varBound]
  | cons l ls ih =>
      simp [Clique.clauseVarBound, SAT.Clause.varBound, ih]

theorem cliqueCNFVarBound_eq_satCNFVarBound (φ : SAT.CNF) :
    Clique.cnfVarBound φ = SAT.CNF.varBound φ := by
  induction φ with
  | nil =>
      simp [Clique.cnfVarBound, SAT.CNF.varBound]
  | cons c cs ih =>
      simp [Clique.cnfVarBound, SAT.CNF.varBound, ih,
        cliqueClauseVarBound_eq_satClauseVarBound c]

theorem cnfVarBound_le_threeCNFStructured_inputSize (φ : SAT.ThreeCNF) :
    Clique.cnfVarBound φ.clauses ≤ threeCNFStructuredEncodedType.inputSize φ := by
  rw [cliqueCNFVarBound_eq_satCNFVarBound]
  have h := cnfVarBound_le_cnfStructured_inputSize φ.clauses
  simpa [threeCNFStructuredEncodedType, EncodedType.inputSize] using h

theorem threeSATToZeroOneIPStructuredTMMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔
      ZeroOneIntegerProgramming (threeSATToZeroOneIPStructuredTMMap φ) := by
  exact boundedTextbookMap_correct_of_cnfVarBound_le φ
    (cnfVarBound_le_threeCNFStructured_inputSize φ)

def RowEntriesBound (B : Nat) (row : List Int) : Prop :=
  ∀ z ∈ row, -((B : Int)) ≤ z ∧ z ≤ (B : Int)

theorem rowEntriesBound_mono {B C : Nat} {row : List Int} (hBC : B ≤ C)
    (hrow : RowEntriesBound B row) :
    RowEntriesBound C row := by
  intro z hz
  have hz' := hrow z hz
  constructor <;> omega

theorem literalCoeffAt_bound (l : SAT.Literal) (i : Nat) :
    -((1 : Nat) : Int) ≤ literalCoeffAt l i ∧ literalCoeffAt l i ≤ ((1 : Nat) : Int) := by
  cases l with
  | mk var neg =>
      by_cases h : i = var <;> cases neg <;> simp [literalCoeffAt, h]

theorem literalRowFrom_entriesBound (start n : Nat) (l : SAT.Literal) :
    RowEntriesBound 1 (literalRowFrom start n l) := by
  induction n generalizing start with
  | zero =>
      intro z hz
      simp [literalRowFrom] at hz
  | succ n ih =>
      intro z hz
      simp [literalRowFrom] at hz
      rcases hz with rfl | hz
      · exact literalCoeffAt_bound l start
      · exact ih (start := start + 1) z hz

theorem literalRow_entriesBound (n : Nat) (l : SAT.Literal) :
    RowEntriesBound 1 (literalRow n l) := by
  simpa [literalRow] using literalRowFrom_entriesBound 0 n l

theorem zeroRow_entriesBound (n : Nat) :
    RowEntriesBound 0 (zeroRow n) := by
  induction n with
  | zero =>
      intro z hz
      simp [zeroRow] at hz
  | succ n ih =>
      intro z hz
      simp [zeroRow] at hz
      rcases hz with rfl | hz
      · omega
      · exact ih z hz

theorem addRows_entriesBound {xs ys : List Int} {B C : Nat}
    (hxs : RowEntriesBound B xs) (hys : RowEntriesBound C ys) :
    RowEntriesBound (B + C) (addRows xs ys) := by
  induction xs generalizing ys with
  | nil =>
      simpa [addRows] using rowEntriesBound_mono (Nat.le_add_left C B) hys
  | cons x xs ih =>
      cases ys with
      | nil =>
          simpa [addRows] using rowEntriesBound_mono (Nat.le_add_right B C) hxs
      | cons y ys =>
          intro z hz
          simp [addRows] at hz
          rcases hz with rfl | hzTail
          · have hx := hxs x (by simp)
            have hy := hys y (by simp)
            constructor <;> omega
          · have hxsTail : RowEntriesBound B xs := by
              intro w hw
              exact hxs w (by simp [hw])
            have hysTail : RowEntriesBound C ys := by
              intro w hw
              exact hys w (by simp [hw])
            exact ih hxsTail hysTail z hzTail

theorem clauseRow_entriesBound (n : Nat) (c : SAT.Clause) :
    RowEntriesBound c.length (clauseRow n c) := by
  induction c with
  | nil =>
      simpa [clauseRow] using zeroRow_entriesBound n
  | cons l ls ih =>
      have h := addRows_entriesBound (literalRow_entriesBound n l) ih
      simpa [clauseRow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem intStructured_inputSize_le_five_of_between_three {z : Int}
    (hlo : -((3 : Nat) : Int) ≤ z) (hhi : z ≤ ((3 : Nat) : Int)) :
    EncodedType.int.inputSize z ≤ 5 := by
  cases z with
  | ofNat n =>
      have hn : n ≤ 3 := by
        exact Int.le_of_ofNat_le_ofNat hhi
      rw [EncodedType.inputSize_int_ofNat]
      omega
  | negSucc n =>
      have hn : n ≤ 2 := by
        rw [Int.negSucc_eq] at hlo
        omega
      rw [EncodedType.inputSize_int_negSucc]
      omega

theorem literalNegWeight_bounds (l : SAT.Literal) :
    0 ≤ literalNegWeight l ∧ literalNegWeight l ≤ ((1 : Nat) : Int) := by
  cases l with
  | mk var neg =>
      cases neg <;> simp [literalNegWeight]

theorem clauseNegWeight_bounds (c : SAT.Clause) :
    0 ≤ clauseNegWeight c ∧ clauseNegWeight c ≤ (c.length : Int) := by
  induction c with
  | nil =>
      simp [clauseNegWeight]
  | cons l ls ih =>
      have hl := literalNegWeight_bounds l
      simp [clauseNegWeight]
      constructor <;> omega

theorem clauseBound_inputSize_le_five_of_length_le_three {c : SAT.Clause}
    (hlen : c.length ≤ 3) :
    EncodedType.int.inputSize (clauseBound c) ≤ 5 := by
  have hNeg := clauseNegWeight_bounds c
  apply intStructured_inputSize_le_five_of_between_three
  · simp [clauseBound]
    omega
  · simp [clauseBound]
    omega

theorem intRowStructured_inputSize_le_length_mul_six {row : List Int}
    (hrow : ∀ z ∈ row, EncodedType.int.inputSize z ≤ 5) :
    intRowStructuredEncodedType.inputSize row ≤ row.length * 6 := by
  have h :=
    Clique.encodedList_inputSize_le_length_mul_bound EncodedType.int row 5 hrow
  simpa [intRowStructuredEncodedType] using h

theorem clauseRow_structured_inputSize_le (n : Nat) {c : SAT.Clause}
    (hlen : c.length ≤ 3) :
    intRowStructuredEncodedType.inputSize (clauseRow n c) ≤ n * 6 := by
  have hBound := clauseRow_entriesBound n c
  have hInput : ∀ z ∈ clauseRow n c, EncodedType.int.inputSize z ≤ 5 := by
    intro z hz
    have hzBound := rowEntriesBound_mono hlen hBound z hz
    exact intStructured_inputSize_le_five_of_between_three hzBound.1 hzBound.2
  have hRow := intRowStructured_inputSize_le_length_mul_six hInput
  simpa [clauseRow_length] using hRow

theorem clauseConstraint_structured_inputSize_le (n : Nat) {c : SAT.Clause}
    (hlen : c.length ≤ 3) :
    constraintStructuredEncodedType.inputSize (clauseConstraint n c) ≤ n * 6 + 6 := by
  have hRow := clauseRow_structured_inputSize_le n hlen
  have hBound := clauseBound_inputSize_le_five_of_length_le_three hlen
  simp [constraintStructuredEncodedType, clauseConstraint]
  omega

theorem textbookConstraints_structured_inputSize_le (φ : SAT.ThreeCNF) :
    constraintListStructuredEncodedType.inputSize
        (φ.clauses.map (clauseConstraint (Clique.cnfVarBound φ.clauses))) ≤
      φ.clauses.length * (Clique.cnfVarBound φ.clauses * 6 + 7) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound constraintStructuredEncodedType
      (φ.clauses.map (clauseConstraint (Clique.cnfVarBound φ.clauses)))
      (Clique.cnfVarBound φ.clauses * 6 + 6)
      (by
        intro constraint hconstraint
        rcases List.mem_map.mp hconstraint with ⟨c, hc, rfl⟩
        exact clauseConstraint_structured_inputSize_le
          (Clique.cnfVarBound φ.clauses) (φ.isThree c hc))
  simpa [constraintListStructuredEncodedType] using hList

theorem zeroOneIPStructured_inputSize_textbookMap_le_threeSAT_poly
    (φ : SAT.ThreeCNF) :
    integerProgrammingStructuredEncodedType.inputSize (textbookMap φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  let N := Clique.cnfVarBound φ.clauses
  let C := φ.clauses.length
  have hN : N ≤ S := by
    simpa [S, N] using cnfVarBound_le_threeCNFStructured_inputSize φ
  have hC : C ≤ S := by
    simpa [S, C] using Clique.threeCNFStructured_inputSize_ge_clauses_length φ
  have hConstraints := textbookConstraints_structured_inputSize_le φ
  have hBase :
      integerProgrammingStructuredEncodedType.inputSize (textbookMap φ) ≤
        N + C * (N * 6 + 7) + 2 := by
    rw [integerProgrammingStructured_inputSize_eq]
    have hNum : (textbookMap φ).numVariables = N := by
      simp [textbookMap, N]
    have hConstraintsEq :
        (textbookMap φ).constraints =
          φ.clauses.map (clauseConstraint (Clique.cnfVarBound φ.clauses)) := by
      simp [textbookMap]
    rw [hNum, hConstraintsEq]
    simpa [N, C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hConstraints
  have hFactor : N * 6 + 7 ≤ S * 6 + 7 := by
    omega
  have hMul : C * (N * 6 + 7) ≤ S * (S * 6 + 7) :=
    Nat.mul_le_mul hC hFactor
  have hPolyBase :
      N + C * (N * 6 + 7) + 2 ≤ S + S * (S * 6 + 7) + 2 := by
    omega
  calc
    integerProgrammingStructuredEncodedType.inputSize (textbookMap φ)
        ≤ N + C * (N * 6 + 7) + 2 := hBase
    _ ≤ S + S * (S * 6 + 7) + 2 := hPolyBase
    _ ≤ 1000 * S ^ 3 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem threeSATToZeroOneIPStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : IntegerProgrammingInput => integerProgrammingStructuredEncodedType.inputSize I)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro φ
  exact zeroOneIPStructured_inputSize_textbookMap_le_threeSAT_poly φ

noncomputable def threeSATToZeroOneIPStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem zeroOneIntegerProgrammingStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            threeSATToZeroOneIPStructured_polynomialSizeBound) }
  correct := by
    intro φ
    simpa [threeSATStructuredDecisionProblem, zeroOneIntegerProgrammingStructuredDecisionProblem]
      using textbookMap_correct φ

end ZeroOneIP
end Karp21
end ComplexityReduction
