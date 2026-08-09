/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SAT
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
Finite-certificate verifier surface for bundled 3SAT.

The legacy local verifier uses a raw total assignment as certificate, whose
encoding is empty.  This file introduces the semantic finite Boolean-string
certificate layer needed before building a standard TM verifier.
-/

namespace ComplexityReduction
namespace SAT

/-- A 3SAT certificate is a finite list of Boolean values. -/
abbrev finiteAssignmentCertEncodedType : EncodedType :=
  EncodedType.list EncodedType.bool

/-- Interpret a finite Boolean certificate as a total assignment, defaulting to `false`. -/
def finiteAssignment (bits : List Bool) : Assignment :=
  fun v => bits.getD v false

/-- Restrict a total assignment to the first `bound` variables as a finite certificate. -/
def assignmentPrefix (bound : Nat) (a : Assignment) : List Bool :=
  (List.range bound).map a

@[simp] theorem assignmentPrefix_length (bound : Nat) (a : Assignment) :
    (assignmentPrefix bound a).length = bound := by
  simp [assignmentPrefix]

/-- The finite prefix certificate agrees with the original assignment below its bound. -/
theorem finiteAssignment_assignmentPrefix_of_lt {bound v : Nat} {a : Assignment}
    (hv : v < bound) :
    finiteAssignment (assignmentPrefix bound a) v = a v := by
  unfold finiteAssignment assignmentPrefix
  have hLen : v < ((List.range bound).map a).length := by
    simpa using hv
  rw [List.getD_eq_getElem _ _ hLen]
  simp [List.getElem_map]

namespace Literal

/-- Literal evaluation is preserved by a finite prefix containing the literal's variable. -/
theorem eval_finiteAssignment_assignmentPrefix {bound : Nat} {a : Assignment}
    {l : Literal} (hl : l.var < bound) :
    l.eval (finiteAssignment (assignmentPrefix bound a)) = l.eval a := by
  cases l with
  | mk var neg =>
      simp [eval, finiteAssignment_assignmentPrefix_of_lt (a := a) hl]

end Literal

namespace Clause

/-- Clause satisfaction is preserved by a finite prefix containing all variables in the clause. -/
theorem satisfies_finiteAssignment_assignmentPrefix {bound : Nat} {c : Clause}
    {a : Assignment} (hVars : ∀ l ∈ c, l.var < bound) :
    Satisfies c a → Satisfies c (finiteAssignment (assignmentPrefix bound a)) := by
  rintro ⟨l, hl, hEval⟩
  refine ⟨l, hl, ?_⟩
  simpa [hEval] using
    (Literal.eval_finiteAssignment_assignmentPrefix (a := a) (l := l) (hVars l hl))

/-- The variable bound of a clause is no larger than its local 3SAT encoding length. -/
theorem varBound_le_encodeClause_length (c : Clause) :
    Clause.varBound c ≤ (ThreeSATEncoding.encodeClause c).length := by
  induction c with
  | nil =>
      simp [Clause.varBound, ThreeSATEncoding.encodeClause]
  | cons l ls ih =>
      have hLit : l.var + 1 ≤ (ThreeSATEncoding.encodeLiteral l).length := by
        simp [ThreeSATEncoding.encodeLiteral, ThreeSATEncoding.encodeNat, EncodedType.nat]
      simp [Clause.varBound, ThreeSATEncoding.encodeClause, List.flatMap_cons] at ih ⊢
      omega

end Clause

namespace CNF

/--
CNF satisfaction is preserved by a finite prefix containing all variables in the formula.
-/
theorem satisfies_finiteAssignment_assignmentPrefix {bound : Nat} {φ : CNF}
    {a : Assignment} (hVars : ∀ c ∈ φ, ∀ l ∈ c, l.var < bound) :
    Satisfies φ a → Satisfies φ (finiteAssignment (assignmentPrefix bound a)) := by
  intro hSat c hc
  exact Clause.satisfies_finiteAssignment_assignmentPrefix (hVars c hc) (hSat c hc)

/-- Auxiliary CNF encoding length without the bundled `ThreeCNF` wrapper. -/
def encodeCNFForThreeSAT (φ : CNF) : List ThreeSATSymbol :=
  φ.flatMap ThreeSATEncoding.encodeClause

/-- The variable bound of a CNF is bounded by the local 3SAT encoding length. -/
theorem varBound_le_encodeCNFForThreeSAT_length (φ : CNF) :
    CNF.varBound φ ≤ (encodeCNFForThreeSAT φ).length := by
  induction φ with
  | nil =>
      simp [CNF.varBound, encodeCNFForThreeSAT]
  | cons c cs ih =>
      have hc := Clause.varBound_le_encodeClause_length c
      simp [CNF.varBound, encodeCNFForThreeSAT, List.flatMap_cons] at ih ⊢
      omega

end CNF

namespace ThreeCNF

/-- Bundled 3CNF satisfaction is preserved by the variable-bound finite prefix. -/
theorem satisfies_finiteAssignment_prefix (φ : ThreeCNF) (a : Assignment) :
    φ.Satisfies a →
      φ.Satisfies (finiteAssignment (assignmentPrefix (CNF.varBound φ.clauses) a)) := by
  intro hSat
  exact CNF.satisfies_finiteAssignment_assignmentPrefix
    (bound := CNF.varBound φ.clauses)
    (φ := φ.clauses)
    (a := a)
    (fun c hc => CNF.clause_vars_lt_varBound hc)
    hSat

/-- The bundled 3CNF variable bound is no larger than its encoded input size. -/
theorem varBound_le_inputSize (φ : ThreeCNF) :
    CNF.varBound φ.clauses ≤ threeSATDecisionProblem.Instance.inputSize φ := by
  change CNF.varBound φ.clauses ≤ (ThreeSATEncoding.encodeThreeCNF φ).length
  simpa [ThreeSATEncoding.encodeThreeCNF, CNF.encodeCNFForThreeSAT] using
    CNF.varBound_le_encodeCNFForThreeSAT_length φ.clauses

end ThreeCNF

/-- Finite-certificate 3SAT verifier, before adding a direct TM runner. -/
noncomputable def threeSATFiniteVerify (φ : ThreeCNF) (bits : List Bool) : Bool := by
  classical
  exact if φ.Satisfies (finiteAssignment bits) then true else false

theorem threeSATFiniteVerify_eq_true_iff (φ : ThreeCNF) (bits : List Bool) :
    threeSATFiniteVerify φ bits = true ↔ φ.Satisfies (finiteAssignment bits) := by
  classical
  by_cases h : φ.Satisfies (finiteAssignment bits)
  · simp [threeSATFiniteVerify, h]
  · simp [threeSATFiniteVerify, h]

/-- Semantic correctness of the finite-certificate 3SAT verifier. -/
theorem threeSAT_satisfiable_iff_exists_finiteVerify (φ : ThreeCNF) :
    φ.Satisfiable ↔ ∃ bits : List Bool, threeSATFiniteVerify φ bits = true := by
  constructor
  · rintro ⟨a, hSat⟩
    refine ⟨assignmentPrefix (CNF.varBound φ.clauses) a, ?_⟩
    exact (threeSATFiniteVerify_eq_true_iff φ _).2
      (ThreeCNF.satisfies_finiteAssignment_prefix φ a hSat)
  · rintro ⟨bits, hVerify⟩
    exact ⟨finiteAssignment bits, (threeSATFiniteVerify_eq_true_iff φ bits).1 hVerify⟩

/-- Encoded Boolean-list certificates have exactly two symbols per Boolean. -/
theorem boolList_inputSize_eq_two_mul_length (bits : List Bool) :
    finiteAssignmentCertEncodedType.inputSize bits = 2 * bits.length := by
  induction bits with
  | nil =>
      change (EncodedType.list EncodedType.bool).inputSize ([] : List Bool) = 0
      exact EncodedType.inputSize_list_nil EncodedType.bool
  | cons b bs ih =>
      change (EncodedType.list EncodedType.bool).inputSize (b :: bs) =
        2 * (b :: bs).length
      rw [EncodedType.inputSize_list_cons, ih, EncodedType.inputSize_bool]
      simp
      omega

theorem assignmentPrefix_inputSize (bound : Nat) (a : Assignment) :
    finiteAssignmentCertEncodedType.inputSize (assignmentPrefix bound a) = 2 * bound := by
  rw [boolList_inputSize_eq_two_mul_length, assignmentPrefix_length]

/-- The canonical satisfying finite certificate has linear size in the encoded 3CNF input. -/
theorem assignmentPrefix_inputSize_le_formula (φ : ThreeCNF) (a : Assignment) :
    finiteAssignmentCertEncodedType.inputSize
        (assignmentPrefix (CNF.varBound φ.clauses) a) ≤
      2 * threeSATDecisionProblem.Instance.inputSize φ := by
  rw [assignmentPrefix_inputSize]
  have hBound := ThreeCNF.varBound_le_inputSize φ
  omega

/--
Polynomial certificate bound for the finite-certificate 3SAT verifier.

This is the certificate-size half of a future `TMVerifier`; the verifier's
direct TM polynomial-time runner is still a separate obligation.
-/
theorem threeSATFiniteVerify_cert_bound :
    ∃ degree coeff const : Nat,
      ∀ φ : ThreeCNF, φ.Satisfiable →
        ∃ bits : List Bool,
          finiteAssignmentCertEncodedType.inputSize bits ≤
            coeff * (threeSATDecisionProblem.Instance.inputSize φ) ^ degree + const ∧
          threeSATFiniteVerify φ bits = true := by
  refine ⟨1, 2, 0, ?_⟩
  intro φ hSat
  rcases hSat with ⟨a, ha⟩
  refine ⟨assignmentPrefix (CNF.varBound φ.clauses) a, ?_, ?_⟩
  · simpa using assignmentPrefix_inputSize_le_formula φ a
  · exact (threeSATFiniteVerify_eq_true_iff φ _).2
      (ThreeCNF.satisfies_finiteAssignment_prefix φ a ha)

end SAT
end ComplexityReduction
