/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNF

/-!
Conversion from arbitrary CNF formulas to bundled local 3CNF formulas.

Long clauses are split by a fresh-variable OR chain.  For a clause
`[l₀, l₁, ..., lₙ]`, the construction introduces variables `next, next + 1, ...`
where each auxiliary variable stores the disjunction of the prefix seen so far.
Each Boolean gate `out ↔ left ∨ right` is encoded by the three clauses

* `¬left ∨ out`
* `¬right ∨ out`
* `left ∨ right ∨ ¬out`

and the final unit clause requires the last prefix variable to be true.  Clauses
of length at most three keep their original shape.
-/

namespace ComplexityReduction
namespace SAT

namespace Literal

@[simp]
theorem eval_mk_false (var : Nat) (a : Assignment) :
    Literal.eval ({ var := var, neg := false } : Literal) a = a var :=
  rfl

@[simp]
theorem eval_mk_true (var : Nat) (a : Assignment) :
    Literal.eval ({ var := var, neg := true } : Literal) a = !(a var) :=
  rfl

end Literal

namespace Clause

/-- Update one variable in an assignment. -/
def setVar (a : Assignment) (v : Nat) (value : Bool) : Assignment :=
  fun w => if w = v then value else a w

@[simp]
theorem setVar_self (a : Assignment) (v : Nat) (value : Bool) :
    setVar a v value v = value := by
  simp [setVar]

@[simp]
theorem setVar_ne {a : Assignment} {v w : Nat} {value : Bool} (h : w ≠ v) :
    setVar a v value w = a w := by
  simp [setVar, h]

/-- Every variable occurring in a clause is strictly below this bound. -/
def varBound : Clause → Nat
  | [] => 0
  | l :: ls => max (l.var + 1) (varBound ls)

theorem var_lt_varBound {c : Clause} {l : Literal} (hl : l ∈ c) :
    l.var < varBound c := by
  induction c with
  | nil => cases hl
  | cons h t ih =>
      rcases List.mem_cons.mp hl with rfl | ht
      · exact lt_of_lt_of_le (Nat.lt_succ_self l.var) (Nat.le_max_left _ _)
      · have hlt := ih ht
        exact lt_of_lt_of_le hlt (Nat.le_max_right _ _)

theorem eval_eq_of_eq_on_vars {a b : Assignment} {c : Clause}
    (h : ∀ v, v < varBound c → b v = a v) :
    Satisfies c b ↔ Satisfies c a := by
  constructor
  · rintro ⟨l, hl, hlEval⟩
    refine ⟨l, hl, ?_⟩
    have hv := h l.var (var_lt_varBound hl)
    cases hneg : l.neg
    · simpa [Literal.eval, hneg, hv] using hlEval
    · simpa [Literal.eval, hneg, hv] using hlEval
  · rintro ⟨l, hl, hlEval⟩
    refine ⟨l, hl, ?_⟩
    have hv := h l.var (var_lt_varBound hl)
    cases hneg : l.neg
    · simpa [Literal.eval, hneg, hv] using hlEval
    · simpa [Literal.eval, hneg, hv] using hlEval

theorem literal_eval_eq_of_var_eq {a b : Assignment} (l : Literal)
    (h : b l.var = a l.var) :
    l.eval b = l.eval a := by
  cases l.neg <;> simp [Literal.eval, h]

/-- Negate a SAT literal syntactically. -/
def negate (l : Literal) : Literal :=
  { var := l.var, neg := !l.neg }

@[simp]
theorem negate_eval_true_iff (l : Literal) (a : Assignment) :
    (negate l).eval a = true ↔ l.eval a = false := by
  cases l.neg <;> cases h : a l.var <;> simp [negate, Literal.eval, h]

/-- Positive literal for an auxiliary variable. -/
def auxLit (v : Nat) : Literal :=
  { var := v, neg := false }

/-- Three clauses encoding `out ↔ left ∨ right`. -/
def orGate (left right : Literal) (out : Nat) : CNF :=
  [[negate left, auxLit out], [negate right, auxLit out], [left, right, negate (auxLit out)]]

theorem orGate_isThreeCNF (left right : Literal) (out : Nat) :
    CNF.IsThreeCNF (orGate left right out) := by
  intro c hc
  simp [orGate] at hc
  rcases hc with rfl | rfl | rfl
  · simp
  · simp
  · simp

theorem orGate_satisfies_iff (left right : Literal) (out : Nat) (a : Assignment) :
    CNF.Satisfies (orGate left right out) a ↔ a out = (left.eval a || right.eval a) := by
  cases hleft : left.eval a <;> cases hright : right.eval a <;> cases hout : a out <;>
    simp [CNF.Satisfies, Clause.Satisfies, orGate, auxLit, negate_eval_true_iff,
      hleft, hright, hout]

/-- Split a disjunction whose first accumulated literal is `acc`. -/
def orChain (next : Nat) (acc : Literal) : List Literal → CNF
  | [] => [[acc]]
  | [l] => [[acc, l]]
  | [l₁, l₂] => [[acc, l₁, l₂]]
  | l₁ :: l₂ :: l₃ :: rest =>
      orGate acc l₁ next ++ orChain (next + 1) (auxLit next) (l₂ :: l₃ :: rest)
termination_by rest => rest.length
decreasing_by simp

theorem orChain_isThreeCNF (next : Nat) (acc : Literal) (rest : List Literal) :
    CNF.IsThreeCNF (orChain next acc rest) := by
  induction rest generalizing next acc with
  | nil =>
      intro c hc
      simp [orChain] at hc
      subst c
      simp
  | cons l₁ tail ih =>
      cases tail with
      | nil =>
          intro c hc
          simp [orChain] at hc
          subst c
          simp
      | cons l₂ tail₂ =>
          cases tail₂ with
          | nil =>
              intro c hc
              simp [orChain] at hc
              subst c
              simp
          | cons l₃ rest' =>
              intro c hc
              rcases List.mem_append.mp (by simpa [orChain] using hc) with hgate | hchain
              · exact orGate_isThreeCNF acc l₁ next c hgate
              · exact ih (next := next + 1) (acc := auxLit next) c hchain

theorem orChain_project (next : Nat) (acc : Literal) (rest : List Literal)
    (a : Assignment) :
    CNF.Satisfies (orChain next acc rest) a →
      acc.eval a = true ∨ ∃ l ∈ rest, l.eval a = true := by
  induction rest generalizing next acc with
  | nil =>
      intro h
      have hunit : Clause.Satisfies [acc] a := by
        exact h [acc] (by simp [orChain])
      rcases hunit with ⟨l, hl, hlEval⟩
      simp at hl
      subst l
      exact Or.inl hlEval
  | cons head tail ih =>
      cases tail with
      | nil =>
          intro h
          have hc : Clause.Satisfies [acc, head] a := by
            exact h [acc, head] (by simp [orChain])
          rcases hc with ⟨lit, hl, hlEval⟩
          rcases List.mem_cons.mp hl with hacc | htail
          · subst lit
            exact Or.inl hlEval
          · exact Or.inr ⟨lit, by simpa using htail, hlEval⟩
      | cons second restTail =>
          cases restTail with
          | nil =>
              intro h
              have hc : Clause.Satisfies [acc, head, second] a := by
                exact h [acc, head, second] (by simp [orChain])
              rcases hc with ⟨lit, hl, hlEval⟩
              rcases List.mem_cons.mp hl with hacc | htail
              · subst lit
                exact Or.inl hlEval
              · exact Or.inr ⟨lit, by simpa using htail, hlEval⟩
          | cons third rest' =>
              intro h
              have hgate : CNF.Satisfies (orGate acc head next) a := by
                intro c hc
                exact h c (by simp [orChain, List.mem_append, hc])
              have hchain :
                  CNF.Satisfies (orChain (next + 1) (auxLit next) (second :: third :: rest')) a := by
                intro c hc
                exact h c (by simp [orChain, List.mem_append, hc])
              have hout := (orGate_satisfies_iff acc head next a).1 hgate
              have htail := ih (next := next + 1) (acc := auxLit next) hchain
              rcases htail with haux | hrest
              · have hor : acc.eval a || head.eval a = true := by
                  simpa [auxLit, hout] using haux
                cases hacc : acc.eval a
                · have hhead : head.eval a = true := by simpa [hacc] using hor
                  exact Or.inr ⟨head, by simp, hhead⟩
                · exact Or.inl rfl
              · rcases hrest with ⟨l, hl, hlEval⟩
                exact Or.inr ⟨l, by simp [hl], hlEval⟩

/-- Positive auxiliary literal. -/
def posAux (v : Nat) : Literal :=
  { var := v, neg := false }

/-- Negative auxiliary literal. -/
def negAux (v : Nat) : Literal :=
  { var := v, neg := true }

@[simp]
theorem posAux_eval (v : Nat) (a : Assignment) :
    (posAux v).eval a = a v :=
  rfl

@[simp]
theorem negAux_eval (v : Nat) (a : Assignment) :
    (negAux v).eval a = !(a v) :=
  rfl

/--
Standard long-clause splitting. The `next` parameter is the first fresh
variable available to this clause.
-/
def splitWith (next : Nat) : Clause → CNF
  | [] => [[]]
  | [l₁] => [[l₁]]
  | [l₁, l₂] => [[l₁, l₂]]
  | [l₁, l₂, l₃] => [[l₁, l₂, l₃]]
  | l₁ :: l₂ :: l₃ :: l₄ :: rest =>
      [l₁, l₂, posAux next] :: splitWith (next + 1) (negAux next :: l₃ :: l₄ :: rest)
termination_by c => c.length
decreasing_by simp

theorem splitWith_isThreeCNF (next : Nat) (c : Clause) :
    CNF.IsThreeCNF (splitWith next c) := by
  fun_induction splitWith next c with
  | case1 next =>
      intro d hd
      simp at hd
      subst d
      simp
  | case2 next l₁ =>
      intro d hd
      simp at hd
      subst d
      simp
  | case3 next l₁ l₂ =>
      intro d hd
      simp at hd
      subst d
      simp
  | case4 next l₁ l₂ l₃ =>
      intro d hd
      simp at hd
      subst d
      simp
  | case5 next l₁ l₂ l₃ l₄ rest ih =>
      intro d hd
      rcases List.mem_cons.mp (by simpa [splitWith] using hd) with hhead | htail
      · subst d
        simp
      · exact ih d htail

theorem splitWith_project (next : Nat) (c : Clause) (a : Assignment) :
    CNF.Satisfies (splitWith next c) a → Clause.Satisfies c a := by
  fun_induction splitWith next c generalizing a with
  | case1 next =>
      intro h
      have hEmpty : Clause.Satisfies ([] : Clause) a := h [] (by simp)
      rcases hEmpty with ⟨l, hl, _⟩
      cases hl
  | case2 next l₁ =>
      intro h
      exact h [l₁] (by simp)
  | case3 next l₁ l₂ =>
      intro h
      exact h [l₁, l₂] (by simp)
  | case4 next l₁ l₂ l₃ =>
      intro h
      exact h [l₁, l₂, l₃] (by simp)
  | case5 next first second third fourth rest ih =>
      intro h
      have hhead : Clause.Satisfies [first, second, posAux next] a := by
        exact h [first, second, posAux next] (by simp)
      have htail : CNF.Satisfies (splitWith (next + 1) (negAux next :: third :: fourth :: rest)) a := by
        intro d hd
        exact h d (by simp [hd])
      rcases hhead with ⟨hit, hhit, hhitEval⟩
      rcases List.mem_cons.mp hhit with hfirst | hhit
      · exact ⟨hit, by simp [hfirst], hhitEval⟩
      · rcases List.mem_cons.mp hhit with hsecond | hhit
        · exact ⟨hit, by simp [hsecond], hhitEval⟩
        · have hy : a next = true := by
            have hEq : hit = posAux next := by simpa using hhit
            subst hit
            simpa [posAux] using hhitEval
          have htailClause := ih a htail
          rcases htailClause with ⟨lt, hlt, hltEval⟩
          rcases List.mem_cons.mp hlt with hneg | hrest
          · subst lt
            simp [negAux, hy] at hltEval
          · exact ⟨lt, by simp [hrest], hltEval⟩

theorem splitWith_extend (next : Nat) (c : Clause) (a : Assignment)
    (hBound : ∀ l ∈ c, l.var < next)
    (hSat : Clause.Satisfies c a) :
    ∃ b : Assignment, (∀ v, v < next → b v = a v) ∧
      CNF.Satisfies (splitWith next c) b := by
  fun_induction splitWith next c generalizing a with
  | case1 next =>
      rcases hSat with ⟨l, hl, _⟩
      cases hl
  | case2 next l₁ =>
      refine ⟨a, fun _ _ => rfl, ?_⟩
      intro d hd
      simp at hd
      subst d
      exact hSat
  | case3 next l₁ l₂ =>
      refine ⟨a, fun _ _ => rfl, ?_⟩
      intro d hd
      simp at hd
      subst d
      exact hSat
  | case4 next l₁ l₂ l₃ =>
      refine ⟨a, fun _ _ => rfl, ?_⟩
      intro d hd
      simp at hd
      subst d
      exact hSat
  | case5 next first second third fourth rest ih =>
      let yVal := !((first.eval a) || (second.eval a))
      let a' := setVar a next yVal
      have hTailSat : Clause.Satisfies (negAux next :: third :: fourth :: rest) a' := by
        by_cases h12 : first.eval a = true ∨ second.eval a = true
        · refine ⟨negAux next, by simp, ?_⟩
          rcases h12 with h1 | h2
          · simp [a', yVal, negAux, h1]
          · cases h1 : first.eval a <;> simp [a', yVal, negAux, h1, h2]
        · rcases hSat with ⟨l, hl, hlEval⟩
          rcases List.mem_cons.mp hl with rfl | hl
          · exact False.elim (h12 (Or.inl hlEval))
          · rcases List.mem_cons.mp hl with rfl | hl
            · exact False.elim (h12 (Or.inr hlEval))
            · refine ⟨l, by simp [hl], ?_⟩
              have hlBound : l.var < next := hBound l (by simp [hl])
              cases l.neg <;> simpa [a', setVar_ne (ne_of_lt hlBound), Literal.eval] using hlEval
      have hTailBound : ∀ l ∈ negAux next :: third :: fourth :: rest, l.var < next + 1 := by
        intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Nat.lt_succ_self next
        · exact Nat.lt_succ_of_lt (hBound l (by simp [hl]))
      rcases ih a' hTailBound hTailSat with ⟨b, hbPres, hbSat⟩
      refine ⟨b, ?_, ?_⟩
      · intro v hv
        rw [hbPres v (Nat.lt_succ_of_lt hv)]
        exact setVar_ne (ne_of_lt hv)
      · intro d hd
        rcases List.mem_cons.mp (by simpa [splitWith] using hd) with hfirst | hrest
        · subst d
          by_cases h1 : first.eval a = true
          · refine ⟨first, by simp, ?_⟩
            have hfirst : first.var < next := hBound first (by simp)
            have heq : first.eval b = first.eval a := by
              trans first.eval a'
              · exact literal_eval_eq_of_var_eq first (hbPres first.var (Nat.lt_succ_of_lt hfirst))
              · exact literal_eval_eq_of_var_eq (a := a) (b := a') first
                  (setVar_ne (ne_of_lt hfirst))
            simpa [heq] using h1
          · by_cases h2 : second.eval a = true
            · refine ⟨second, by simp, ?_⟩
              have hsecond : second.var < next := hBound second (by simp)
              have heq : second.eval b = second.eval a := by
                trans second.eval a'
                · exact literal_eval_eq_of_var_eq second
                    (hbPres second.var (Nat.lt_succ_of_lt hsecond))
                · exact literal_eval_eq_of_var_eq (a := a) (b := a') second
                    (setVar_ne (ne_of_lt hsecond))
              simpa [heq] using h2
            · refine ⟨posAux next, by simp, ?_⟩
              have heq : (posAux next).eval b = (posAux next).eval a' := by
                exact literal_eval_eq_of_var_eq (posAux next) (hbPres next (Nat.lt_succ_self next))
              have ha' : (posAux next).eval a' = true := by
                simp [a', yVal, posAux, Bool.eq_false_of_not_eq_true h1,
                  Bool.eq_false_of_not_eq_true h2]
              rw [heq]
              exact ha'
        · exact hbSat d hrest

/-- If two assignments agree on all literals of a clause, satisfaction transfers. -/
theorem satisfies_of_eval_eq {c : Clause} {a b : Assignment}
    (h : ∀ l ∈ c, l.eval b = l.eval a) :
    Clause.Satisfies c a → Clause.Satisfies c b := by
  rintro ⟨l, hl, hlEval⟩
  exact ⟨l, hl, by simpa [h l hl] using hlEval⟩

/-- All literals introduced by splitting a clause stay below `next + c.length`. -/
theorem splitWith_lit_bound (next : Nat) (c : Clause)
    (hBound : ∀ l ∈ c, l.var < next) :
    ∀ d ∈ splitWith next c, ∀ l ∈ d, l.var < next + c.length := by
  fun_induction splitWith next c with
  | case1 next =>
      intro d hd l hl
      have hd' : d = [] := by simpa [splitWith] using hd
      subst d
      cases hl
  | case2 next lit =>
      intro d hd l hl
      have hd' : d = [lit] := by simpa [splitWith] using hd
      subst d
      exact Nat.lt_of_lt_of_le (hBound l (by simpa using hl)) (Nat.le_add_right next 1)
  | case3 next lit1 lit2 =>
      intro d hd l hl
      have hd' : d = [lit1, lit2] := by simpa [splitWith] using hd
      subst d
      exact Nat.lt_of_lt_of_le (hBound l (by simpa using hl)) (Nat.le_add_right next 2)
  | case4 next lit1 lit2 lit3 =>
      intro d hd l hl
      have hd' : d = [lit1, lit2, lit3] := by simpa [splitWith] using hd
      subst d
      exact Nat.lt_of_lt_of_le (hBound l (by simpa using hl)) (Nat.le_add_right next 3)
  | case5 next lit1 lit2 lit3 lit4 rest ih =>
      intro d hd l hl
      rcases List.mem_cons.mp (by simpa [splitWith] using hd) with hhead | htail
      · subst d
        rcases List.mem_cons.mp hl with h1 | hl
        · subst l
          exact Nat.lt_of_lt_of_le (hBound lit1 (by simp)) (Nat.le_add_right next _)
        · rcases List.mem_cons.mp hl with h2 | hl
          · subst l
            exact Nat.lt_of_lt_of_le (hBound lit2 (by simp)) (Nat.le_add_right next _)
          · have hpos : l = posAux next := by simpa using hl
            subst l
            simp [posAux]
      · have hTailBound : ∀ l ∈ negAux next :: lit3 :: lit4 :: rest, l.var < next + 1 := by
          intro l hl'
          rcases List.mem_cons.mp hl' with hneg | hrest
          · subst l
            exact Nat.lt_succ_self next
          · exact Nat.lt_succ_of_lt (hBound l (by simp [hrest]))
        have hlt := ih hTailBound d htail l hl
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt

end Clause

namespace CNF

theorem splitWith_eq_singleton_of_length_le_three (next : Nat) (c : Clause)
    (h : c.length ≤ 3) :
    Clause.splitWith next c = [c] := by
  cases c with
  | nil =>
      simp [Clause.splitWith]
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp [Clause.splitWith]
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp [Clause.splitWith]
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp [Clause.splitWith]
              | cons l₄ rest =>
                  simp at h

/-- Bound all variables occurring in a CNF formula. -/
def varBound : CNF → Nat
  | [] => 0
  | c :: cs => max (Clause.varBound c) (varBound cs)

theorem clause_vars_lt_varBound {φ : CNF} {c : Clause} (hc : c ∈ φ) :
    ∀ l ∈ c, l.var < varBound φ := by
  induction φ with
  | nil => cases hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hds
      · intro l hl
        exact lt_of_lt_of_le (Clause.var_lt_varBound hl) (Nat.le_max_left _ _)
      · intro l hl
        exact lt_of_lt_of_le (ih hds l hl) (Nat.le_max_right _ _)

/-- Total literal count used to reserve disjoint auxiliary ranges. -/
def totalClauseLength : CNF → Nat
  | [] => 0
  | c :: cs => c.length + totalClauseLength cs

/-- Split every clause, using disjoint auxiliary ranges. -/
def splitAux (next : Nat) : CNF → CNF
  | [] => []
  | c :: cs => Clause.splitWith next c ++ splitAux (next + c.length) cs

/-- Convert an arbitrary CNF formula to a list-based 3CNF formula. -/
def splitTo3CNFList (φ : CNF) : CNF :=
  splitAux (varBound φ) φ

theorem splitAux_isThreeCNF (next : Nat) (φ : CNF) :
    IsThreeCNF (splitAux next φ) := by
  induction φ generalizing next with
  | nil =>
      intro c hc
      cases hc
  | cons c cs ih =>
      intro d hd
      rcases List.mem_append.mp (by simpa [splitAux] using hd) with hleft | hright
      · exact Clause.splitWith_isThreeCNF next c d hleft
      · exact ih (next := next + c.length) d hright

theorem splitTo3CNFList_isThreeCNF (φ : CNF) :
    IsThreeCNF (splitTo3CNFList φ) :=
  splitAux_isThreeCNF (varBound φ) φ

theorem splitAux_eq_self_of_isThree (next : Nat) (φ : CNF)
    (h : IsThreeCNF φ) :
    splitAux next φ = φ := by
  induction φ generalizing next with
  | nil =>
      rfl
  | cons c cs ih =>
      have hc : c.length ≤ 3 := h c (by simp)
      have hcs : IsThreeCNF cs := by
        intro d hd
        exact h d (by simp [hd])
      simp [splitAux, splitWith_eq_singleton_of_length_le_three next c hc,
        ih (next := next + c.length) hcs]

theorem splitTo3CNFList_eq_self_of_isThree (φ : CNF)
    (h : IsThreeCNF φ) :
    splitTo3CNFList φ = φ := by
  simpa [splitTo3CNFList] using splitAux_eq_self_of_isThree (varBound φ) φ h

theorem splitAux_project (next : Nat) (φ : CNF) (a : Assignment) :
    Satisfies (splitAux next φ) a → Satisfies φ a := by
  induction φ generalizing next with
  | nil =>
      intro _ c hc
      cases hc
  | cons headClause rest ih =>
      intro h d hd
      rcases List.mem_cons.mp hd with rfl | hcs
      · have hBlock : Satisfies (Clause.splitWith next d) a := by
          intro e he
          exact h e (List.mem_append.mpr (Or.inl he))
        exact Clause.splitWith_project next d a hBlock
      · have hRest : Satisfies (splitAux (next + headClause.length) rest) a := by
          intro e he
          exact h e (List.mem_append.mpr (Or.inr he))
        exact ih (next := next + headClause.length) hRest d hcs

theorem splitTo3CNFList_project (φ : CNF) (a : Assignment) :
    Satisfies (splitTo3CNFList φ) a → Satisfies φ a :=
  splitAux_project (varBound φ) φ a

/--
Extend a satisfying assignment through all split clauses. The extension keeps
all variables below `next` unchanged.
-/
theorem splitAux_extend (next : Nat) (φ : CNF) (a : Assignment)
    (hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < next)
    (hSat : Satisfies φ a) :
    ∃ b : Assignment, (∀ v, v < next → b v = a v) ∧ Satisfies (splitAux next φ) b := by
  induction φ generalizing next a with
  | nil =>
      exact ⟨a, fun _ _ => rfl, by intro c hc; cases hc⟩
  | cons c cs ih =>
      have hcSat : Clause.Satisfies c a := hSat c (by simp)
      have hcBound : ∀ l ∈ c, l.var < next := hBound c (by simp)
      rcases Clause.splitWith_extend next c a hcBound hcSat with ⟨a1, ha1Pres, ha1Sat⟩
      have hcsBound : ∀ d ∈ cs, ∀ l ∈ d, l.var < next + c.length := by
        intro d hd l hl
        exact Nat.lt_of_lt_of_le (hBound d (by simp [hd]) l hl) (Nat.le_add_right next c.length)
      have hcsSatA1 : Satisfies cs a1 := by
        intro d hd
        apply Clause.satisfies_of_eval_eq
        · intro l hl
          have hlNext : l.var < next := hBound d (by simp [hd]) l hl
          exact Clause.literal_eval_eq_of_var_eq l (ha1Pres l.var hlNext)
        · exact hSat d (by simp [hd])
      rcases ih (next := next + c.length) (a := a1) hcsBound hcsSatA1 with
        ⟨b, hbPres, hbSat⟩
      refine ⟨b, ?_, ?_⟩
      · intro v hv
        rw [hbPres v (Nat.lt_of_lt_of_le hv (Nat.le_add_right next c.length))]
        exact ha1Pres v hv
      · intro d hd
        rcases List.mem_append.mp (by simpa [splitAux] using hd) with hleft | hright
        · have hEval : ∀ l ∈ d, l.eval b = l.eval a1 := by
            intro l hl
            have hlBound :=
              Clause.splitWith_lit_bound next c hcBound d hleft l hl
            exact Clause.literal_eval_eq_of_var_eq l (hbPres l.var hlBound)
          exact Clause.satisfies_of_eval_eq hEval (ha1Sat d hleft)
        · exact hbSat d hright

theorem splitTo3CNFList_extend (φ : CNF) (a : Assignment)
    (hSat : Satisfies φ a) :
    ∃ b : Assignment, Satisfies (splitTo3CNFList φ) b := by
  have hBound : ∀ c ∈ φ, ∀ l ∈ c, l.var < varBound φ := by
    intro c hc
    exact clause_vars_lt_varBound hc
  rcases splitAux_extend (varBound φ) φ a hBound hSat with ⟨b, _hbPres, hbSat⟩
  exact ⟨b, hbSat⟩

theorem splitTo3CNFList_satisfiable_iff (φ : CNF) :
    Satisfiable (splitTo3CNFList φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, splitTo3CNFList_project φ a h⟩
  · rintro ⟨a, h⟩
    exact splitTo3CNFList_extend φ a h

/-- Convert an arbitrary CNF formula to bundled 3CNF. -/
def splitToThreeCNF (φ : CNF) : ThreeCNF where
  clauses := splitTo3CNFList φ
  isThree := splitTo3CNFList_isThreeCNF φ

theorem splitToThreeCNF_satisfiable_iff (φ : CNF) :
    (splitToThreeCNF φ).Satisfiable ↔ Satisfiable φ :=
  splitTo3CNFList_satisfiable_iff φ

/-- Package a CNF formula with an existing at-most-three-clause proof. -/
def toThreeCNF (φ : CNF) (h : IsThreeCNF φ) : ThreeCNF where
  clauses := φ
  isThree := h

@[simp]
theorem toThreeCNF_satisfies (φ : CNF) (h : IsThreeCNF φ) (a : Assignment) :
    (toThreeCNF φ h).Satisfies a ↔ Satisfies φ a :=
  Iff.rfl

end CNF

end SAT
end ComplexityReduction
