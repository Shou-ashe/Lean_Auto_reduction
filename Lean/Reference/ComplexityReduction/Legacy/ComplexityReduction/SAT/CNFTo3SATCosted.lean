/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.SizeBound
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT

/-!
Size facts for the arbitrary-CNF-to-3CNF splitting map.

This file is the first R1 costed layer for unrestricted arity.  It does not yet
compose the CSP truth-table expansion with splitting; it proves that the
downstream `CNF.splitToThreeCNF` phase has polynomial encoded output size under
a simple structural CNF measure.
-/

namespace ComplexityReduction
namespace SAT

namespace ListBounds

theorem sum_map_le_length_mul {α : Type} (l : List α) (f : α → Nat) (B : Nat)
    (h : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : f x ≤ B := h x (by simp)
      have hxs : (xs.map f).sum ≤ xs.length * B := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp
      rw [Nat.succ_mul]
      omega

end ListBounds

namespace ThreeSATEncoding

/-- Raw CNF encoding using the same clause alphabet as bundled local 3CNF. -/
def encodeCNF (φ : CNF) : List ThreeSATSymbol :=
  φ.flatMap encodeClause

@[simp]
theorem encodeCNF_nil :
    encodeCNF ([] : CNF) = [] :=
  rfl

@[simp]
theorem encodeCNF_cons (c : Clause) (φ : CNF) :
    encodeCNF (c :: φ) = encodeClause c ++ encodeCNF φ :=
  rfl

@[simp]
theorem encodeThreeCNF_eq_encodeCNF (φ : ThreeCNF) :
    encodeThreeCNF φ = encodeCNF φ.clauses :=
  rfl

theorem encodeLiteral_length_le_of_var_lt {l : Literal} {B : Nat}
    (h : l.var < B) :
    (encodeLiteral l).length ≤ B + 5 := by
  simp [encodeLiteral, encodeNat, EncodedType.nat]
  omega

theorem encodeClause_length_le_of_vars_lt (c : Clause) (B : Nat)
    (hLen : c.length ≤ 3) (hVars : ∀ l ∈ c, l.var < B) :
    (encodeClause c).length ≤ 1 + 3 * (B + 5) := by
  have hEach :
      ∀ l ∈ c, (encodeLiteral l).length ≤ B + 5 := by
    intro l hl
    exact encodeLiteral_length_le_of_var_lt (hVars l hl)
  have hsum :=
    ListBounds.sum_map_le_length_mul c (fun l => (encodeLiteral l).length) (B + 5)
      hEach
  simp [encodeClause, List.length_flatMap]
  calc
    (c.map fun x => (encodeLiteral x).length).sum + 1 ≤ c.length * (B + 5) + 1 := by
      omega
    _ ≤ 3 * (B + 5) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) 1
    _ = 1 + 3 * (B + 5) := by omega

theorem encodeCNF_length_le_of_vars_lt (φ : CNF) (B : Nat)
    (hThree : CNF.IsThreeCNF φ) (hVars : ∀ c ∈ φ, ∀ l ∈ c, l.var < B) :
    (encodeCNF φ).length ≤ φ.length * (1 + 3 * (B + 5)) := by
  have hEach :
      ∀ c ∈ φ, (encodeClause c).length ≤ 1 + 3 * (B + 5) := by
    intro c hc
    exact encodeClause_length_le_of_vars_lt c B (hThree c hc) (hVars c hc)
  simpa [encodeCNF, List.length_flatMap] using
    ListBounds.sum_map_le_length_mul φ (fun c => (encodeClause c).length)
      (1 + 3 * (B + 5)) hEach

end ThreeSATEncoding

namespace Clause

theorem varBound_le_of_vars_lt (c : Clause) (B : Nat)
    (h : ∀ l ∈ c, l.var < B) :
    varBound c ≤ B := by
  induction c with
  | nil =>
      simp [varBound]
  | cons l ls ih =>
      have hl : l.var + 1 ≤ B := Nat.succ_le_of_lt (h l (by simp))
      have hls : varBound ls ≤ B := ih (by
        intro m hm
        exact h m (by simp [hm]))
      simp [varBound]
      exact ⟨hl, hls⟩

theorem splitWith_length_le (next : Nat) (c : Clause) :
    (splitWith next c).length ≤ c.length + 1 := by
  fun_induction splitWith next c with
  | case1 next => simp
  | case2 next l₁ => simp
  | case3 next l₁ l₂ => simp
  | case4 next l₁ l₂ l₃ => simp
  | case5 next l₁ l₂ l₃ l₄ rest ih =>
      have ih' :
          (splitWith (next + 1) (negAux next :: l₃ :: l₄ :: rest)).length ≤
            rest.length + 4 := by
        simpa using ih
      simp
      omega

end Clause

namespace CNF

@[simp]
theorem totalClauseLength_append (φ ψ : CNF) :
    totalClauseLength (φ ++ ψ) = totalClauseLength φ + totalClauseLength ψ := by
  induction φ with
  | nil =>
      simp [totalClauseLength]
  | cons c cs ih =>
      simp [totalClauseLength, ih, Nat.add_assoc]

theorem totalClauseLength_eq_sum_length (φ : CNF) :
    totalClauseLength φ = (φ.map fun c => c.length).sum := by
  induction φ with
  | nil =>
      simp [totalClauseLength]
  | cons c cs ih =>
      simp [totalClauseLength, ih]

theorem varBound_le_of_vars_lt (φ : CNF) (B : Nat)
    (h : ∀ c ∈ φ, ∀ l ∈ c, l.var < B) :
    varBound φ ≤ B := by
  induction φ with
  | nil =>
      simp [varBound]
  | cons c cs ih =>
      have hc : Clause.varBound c ≤ B := Clause.varBound_le_of_vars_lt c B (h c (by simp))
      have hcs : varBound cs ≤ B := ih (by
        intro d hd
        exact h d (by simp [hd]))
      simp [varBound]
      exact ⟨hc, hcs⟩

theorem splitAux_length_le (next : Nat) (φ : CNF) :
    (splitAux next φ).length ≤ totalClauseLength φ + φ.length := by
  induction φ generalizing next with
  | nil =>
      simp [splitAux, totalClauseLength]
  | cons c cs ih =>
      have hc := Clause.splitWith_length_le next c
      have hcs := ih (next := next + c.length)
      simp [splitAux, totalClauseLength]
      omega

theorem splitAux_lit_bound (next : Nat) (φ : CNF)
    (hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < next) :
    ∀ d ∈ splitAux next φ, ∀ l ∈ d, l.var < next + totalClauseLength φ := by
  induction φ generalizing next with
  | nil =>
      intro d hd l hl
      cases hd
  | cons c cs ih =>
      intro d hd l hl
      rcases List.mem_append.mp (by simpa [splitAux] using hd) with hleft | hright
      · have hcBound : ∀ l ∈ c, l.var < next := hBound c (by simp)
        have hlt := Clause.splitWith_lit_bound next c hcBound d hleft l hl
        simp [totalClauseLength]
        omega
      · have hcsBound : ∀ d ∈ cs, ∀ l ∈ d, l.var < next + c.length := by
          intro d hdcs l hld
          exact Nat.lt_of_lt_of_le (hBound d (by simp [hdcs]) l hld)
            (Nat.le_add_right next c.length)
        have hlt := ih (next := next + c.length) hcsBound d hright l hl
        simp [totalClauseLength] at hlt ⊢
        omega

theorem splitTo3CNFList_lit_bound (φ : CNF) :
    ∀ d ∈ splitTo3CNFList φ, ∀ l ∈ d, l.var < varBound φ + totalClauseLength φ := by
  have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < varBound φ := by
    intro c hc
    exact clause_vars_lt_varBound hc
  exact splitAux_lit_bound (varBound φ) φ hBound

theorem splitAux_encodedLength_le (next : Nat) (φ : CNF)
    (hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < next) :
    (ThreeSATEncoding.encodeCNF (splitAux next φ)).length ≤
      (totalClauseLength φ + φ.length) * (1 + 3 * (next + totalClauseLength φ + 5)) := by
  have hEncode :=
    ThreeSATEncoding.encodeCNF_length_le_of_vars_lt
      (splitAux next φ)
      (next + totalClauseLength φ)
      (splitAux_isThreeCNF next φ)
      (splitAux_lit_bound next φ hBound)
  have hLen := splitAux_length_le next φ
  calc
    (ThreeSATEncoding.encodeCNF (splitAux next φ)).length
        ≤ (splitAux next φ).length * (1 + 3 * (next + totalClauseLength φ + 5)) :=
      hEncode
    _ ≤ (totalClauseLength φ + φ.length) *
          (1 + 3 * (next + totalClauseLength φ + 5)) := by
      exact Nat.mul_le_mul_right _ hLen

theorem splitToThreeCNF_encodedLength_le_structural (φ : CNF) :
    (ThreeSATEncoding.encodeThreeCNF (splitToThreeCNF φ)).length ≤
      (totalClauseLength φ + φ.length) *
        (1 + 3 * (varBound φ + totalClauseLength φ + 5)) := by
  have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < varBound φ := by
    intro c hc
    exact clause_vars_lt_varBound hc
  simpa [splitToThreeCNF, splitTo3CNFList, ThreeSATEncoding.encodeCNF] using
    splitAux_encodedLength_le (varBound φ) φ hBound

/-- Structural size measure used for the standalone CNF splitting certificate. -/
def structuralSize (φ : CNF) : Nat :=
  varBound φ + totalClauseLength φ + φ.length + 1

theorem splitToThreeCNF_encodedLength_le_quadraticStructural (φ : CNF) :
    (ThreeSATEncoding.encodeThreeCNF (splitToThreeCNF φ)).length ≤
      20 * (structuralSize φ) ^ 2 := by
  have hStructPos : 0 < structuralSize φ := by
    unfold structuralSize
    omega
  have hMain := splitToThreeCNF_encodedLength_le_structural φ
  have hLeft : totalClauseLength φ + φ.length ≤ structuralSize φ := by
    unfold structuralSize
    omega
  have hRight :
      1 + 3 * (varBound φ + totalClauseLength φ + 5) ≤
        20 * structuralSize φ := by
    unfold structuralSize
    omega
  have hMul :=
    Nat.mul_le_mul hLeft hRight
  exact hMain.trans (by
    calc
      (totalClauseLength φ + φ.length) *
          (1 + 3 * (varBound φ + totalClauseLength φ + 5))
          ≤ structuralSize φ * (20 * structuralSize φ) := hMul
      _ = 20 * (structuralSize φ) ^ 2 := by
        simp [pow_two, Nat.mul_left_comm])

theorem splitToThreeCNF_polynomialStructuralSizeBound :
    PolynomialSizeBound
      structuralSize
      (fun ψ : ThreeCNF => (ThreeSATEncoding.encodeThreeCNF ψ).length)
      splitToThreeCNF :=
  PolynomialSizeBound.intro_with 2 20 0 (by
    intro φ
    simpa using splitToThreeCNF_encodedLength_le_quadraticStructural φ)

end CNF
end SAT
end ComplexityReduction
