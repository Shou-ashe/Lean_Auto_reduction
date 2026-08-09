/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP
import Mathlib.Tactic

/-!
P15e graph-coloring target: local 3SAT to Chromatic Number.

The current graph-coloring schema is raw and does not require edge endpoints to
lie below the declared vertex count.  This module therefore uses the established
bounded 3SAT witness list to drive a tiny current-schema colorability family.
-/

namespace ComplexityReduction
namespace Karp21
namespace ChromaticNumber

open ComplexityReduction.Combinatorics.Graph

/-- A vacuous yes-instance for current-schema Chromatic Number. -/
def yesInput : ChromaticNumberInput where
  graph := { vertices := 0, edges := [], directed := false }
  colors := 0

/-- A one-vertex, zero-color no-instance for current-schema Chromatic Number. -/
def noInput : ChromaticNumberInput where
  graph := { vertices := 1, edges := [], directed := false }
  colors := 0

theorem yesInput_isYes :
    ChromaticNumber yesInput := by
  refine ⟨fun _ => 0, ?_⟩
  constructor
  · intro v hv
    simp [yesInput] at hv
  · intro e he
    simp [yesInput] at he

theorem noInput_isNo :
    ¬ ChromaticNumber noInput := by
  rintro ⟨colorOf, hProper⟩
  have hColor : colorOf 0 < 0 := by
    simpa [noInput] using hProper.1 0 (by simp [noInput])
  omega

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : ChromaticNumberInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    ChromaticNumber (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-- P15e syntax map from local 3SAT to Chromatic Number. -/
noncomputable def map (φ : SAT.ThreeCNF) : ChromaticNumberInput :=
  indicatorInput (ZeroOneIP.satisfyingAssignments φ).length

theorem map_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ ChromaticNumber (map φ) := by
  rw [ZeroOneIP.threeSAT_isYes_iff_satisfyingAssignments_pos]
  exact (indicatorInput_correct (ZeroOneIP.satisfyingAssignments φ).length).symm

/-! ### Textbook 3-coloring route -/

def baseVertex : Nat := 0

def trueVertex : Nat := 1

def falseVertex : Nat := 2

def posVertex (i : Nat) : Nat :=
  3 + 2 * i

def negVertex (i : Nat) : Nat :=
  3 + 2 * i + 1

def variableLimit (n : Nat) : Nat :=
  3 + 2 * n

def clauseBase (n j : Nat) : Nat :=
  variableLimit n + 4 * j

def clauseA0 (n j : Nat) : Nat :=
  clauseBase n j

def clauseA1 (n j : Nat) : Nat :=
  clauseBase n j + 1

def clauseA2 (n j : Nat) : Nat :=
  clauseBase n j + 2

def clauseA3 (n j : Nat) : Nat :=
  clauseBase n j + 3

def textbookVertexCount (n clauses : Nat) : Nat :=
  variableLimit n + 4 * clauses

def literalVertex (l : SAT.Literal) : Nat :=
  if l.neg then negVertex l.var else posVertex l.var

def paletteEdges : List (Nat × Nat) :=
  [(baseVertex, trueVertex), (baseVertex, falseVertex), (trueVertex, falseVertex)]

def variableEdgesFor (i : Nat) : List (Nat × Nat) :=
  [(posVertex i, baseVertex), (negVertex i, baseVertex), (posVertex i, negVertex i)]

def variableEdges (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap variableEdgesFor

def paddedClause : SAT.Clause → Option (SAT.Literal × SAT.Literal × SAT.Literal)
  | [] => none
  | [l] => some (l, l, l)
  | [l₁, l₂] => some (l₁, l₂, l₂)
  | l₁ :: l₂ :: l₃ :: _ => some (l₁, l₂, l₃)

def clauseGadgetEdges (n j : Nat) (l₀ l₁ l₂ : SAT.Literal) : List (Nat × Nat) :=
  let x₀ := literalVertex l₀
  let x₁ := literalVertex l₁
  let x₂ := literalVertex l₂
  let a₀ := clauseA0 n j
  let a₁ := clauseA1 n j
  let a₂ := clauseA2 n j
  let a₃ := clauseA3 n j
  [ (a₀, a₁), (a₀, a₂), (a₃, trueVertex), (a₁, trueVertex)
  , (a₂, a₃), (x₀, a₂), (x₀, a₃), (x₁, a₀), (x₂, a₁)
  ]

def clauseEdgesFor (n j : Nat) (c : SAT.Clause) : List (Nat × Nat) :=
  match paddedClause c with
  | none => [(baseVertex, baseVertex)]
  | some (l₀, l₁, l₂) => clauseGadgetEdges n j l₀ l₁ l₂

def clauseEdgesFrom (n j : Nat) : List SAT.Clause → List (Nat × Nat)
  | [] => []
  | c :: cs => clauseEdgesFor n j c ++ clauseEdgesFrom n (j + 1) cs

def textbookEdges (φ : SAT.ThreeCNF) : List (Nat × Nat) :=
  let n := Clique.cnfVarBound φ.clauses
  paletteEdges ++ variableEdges n ++ clauseEdgesFrom n 0 φ.clauses

/-- P15q syntax-only textbook map from local 3SAT to 3-colorability. -/
def textbookMap (φ : SAT.ThreeCNF) : ChromaticNumberInput where
  graph :=
    { vertices := textbookVertexCount (Clique.cnfVarBound φ.clauses) φ.clauses.length
      edges := textbookEdges φ
      directed := false }
  colors := 3

@[simp] theorem posVertex_inj {i j : Nat} : posVertex i = posVertex j ↔ i = j := by
  constructor <;> intro h
  · simp [posVertex] at h
    omega
  · simp [h]

@[simp] theorem negVertex_inj {i j : Nat} : negVertex i = negVertex j ↔ i = j := by
  constructor <;> intro h
  · simp [negVertex] at h
    omega
  · simp [h]

@[simp] theorem posVertex_ne_negVertex (i j : Nat) : posVertex i ≠ negVertex j := by
  simp [posVertex, negVertex]
  omega

@[simp] theorem negVertex_ne_posVertex (i j : Nat) : negVertex i ≠ posVertex j := by
  simp [posVertex, negVertex]
  omega

@[simp] theorem baseVertex_ne_trueVertex : baseVertex ≠ trueVertex := by
  decide

@[simp] theorem trueVertex_ne_baseVertex : trueVertex ≠ baseVertex := by
  decide

@[simp] theorem baseVertex_ne_falseVertex : baseVertex ≠ falseVertex := by
  decide

@[simp] theorem falseVertex_ne_baseVertex : falseVertex ≠ baseVertex := by
  decide

@[simp] theorem trueVertex_ne_falseVertex : trueVertex ≠ falseVertex := by
  decide

@[simp] theorem falseVertex_ne_trueVertex : falseVertex ≠ trueVertex := by
  decide

theorem posVertex_lt_variableLimit {i n : Nat} (hi : i < n) :
    posVertex i < variableLimit n := by
  simp [posVertex, variableLimit]
  omega

theorem negVertex_lt_variableLimit {i n : Nat} (hi : i < n) :
    negVertex i < variableLimit n := by
  simp [negVertex, variableLimit]
  omega

theorem clauseA0_lt_textbookVertexCount {n m j : Nat} (hj : j < m) :
    clauseA0 n j < textbookVertexCount n m := by
  simp [clauseA0, clauseBase, textbookVertexCount]
  omega

theorem clauseA1_lt_textbookVertexCount {n m j : Nat} (hj : j < m) :
    clauseA1 n j < textbookVertexCount n m := by
  simp [clauseA1, clauseBase, textbookVertexCount]
  omega

theorem clauseA2_lt_textbookVertexCount {n m j : Nat} (hj : j < m) :
    clauseA2 n j < textbookVertexCount n m := by
  simp [clauseA2, clauseBase, textbookVertexCount]
  omega

theorem clauseA3_lt_textbookVertexCount {n m j : Nat} (hj : j < m) :
    clauseA3 n j < textbookVertexCount n m := by
  simp [clauseA3, clauseBase, textbookVertexCount]
  omega

def paletteColor (v : Nat) : Nat :=
  if v = baseVertex then 0 else if v = trueVertex then 1 else if v = falseVertex then 2 else 0

def variablePaletteColorFrom (a : SAT.Assignment) : Nat → Nat → Nat
  | 0, v => paletteColor v
  | n + 1, v =>
      if v = posVertex n then
        if a n then 1 else 2
      else if v = negVertex n then
        if a n then 2 else 1
      else
        variablePaletteColorFrom a n v

theorem paletteColor_lt_three (v : Nat) :
    paletteColor v < 3 := by
  unfold paletteColor
  by_cases h0 : v = baseVertex
  · simp [h0]
  · by_cases h1 : v = trueVertex
    · simp [h1]
    · by_cases h2 : v = falseVertex
      · simp [h2]
      · simp [h0, h1, h2]

theorem variablePaletteColorFrom_lt_three (a : SAT.Assignment) (n v : Nat) :
    variablePaletteColorFrom a n v < 3 := by
  induction n with
  | zero =>
      simpa [variablePaletteColorFrom] using paletteColor_lt_three v
  | succ n ih =>
      simp [variablePaletteColorFrom]
      split
      · split <;> omega
      · split
        · split <;> omega
        · exact ih

theorem variablePaletteColorFrom_base (a : SAT.Assignment) (n : Nat) :
    variablePaletteColorFrom a n baseVertex = 0 := by
  induction n with
  | zero => simp [variablePaletteColorFrom, paletteColor, baseVertex]
  | succ n ih =>
      have hpos : baseVertex ≠ posVertex n := by
        simp [baseVertex, posVertex]
        omega
      have hneg : baseVertex ≠ negVertex n := by
        simp [baseVertex, negVertex]
      simp [variablePaletteColorFrom, hpos, hneg, ih]

theorem variablePaletteColorFrom_true (a : SAT.Assignment) (n : Nat) :
    variablePaletteColorFrom a n trueVertex = 1 := by
  induction n with
  | zero => simp [variablePaletteColorFrom, paletteColor, trueVertex, baseVertex]
  | succ n ih =>
      have hpos : trueVertex ≠ posVertex n := by
        simp [trueVertex, posVertex]
        omega
      have hneg : trueVertex ≠ negVertex n := by
        simp [trueVertex, negVertex]
      simp [variablePaletteColorFrom, hpos, hneg, ih]

theorem variablePaletteColorFrom_false (a : SAT.Assignment) (n : Nat) :
    variablePaletteColorFrom a n falseVertex = 2 := by
  induction n with
  | zero => simp [variablePaletteColorFrom, paletteColor, falseVertex, baseVertex, trueVertex]
  | succ n ih =>
      have hpos : falseVertex ≠ posVertex n := by
        simp [falseVertex, posVertex]
        omega
      have hneg : falseVertex ≠ negVertex n := by
        simp [falseVertex, negVertex]
        omega
      simp [variablePaletteColorFrom, hpos, hneg, ih]

theorem variablePaletteColorFrom_pos {a : SAT.Assignment} {n i : Nat} (hi : i < n) :
    variablePaletteColorFrom a n (posVertex i) = if a i then 1 else 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i = n
      · subst i
        simp [variablePaletteColorFrom]
      · have hi' : i < n := by omega
        have hpos : posVertex i ≠ posVertex n := by
          intro hEq
          have : i = n := (posVertex_inj.mp hEq)
          exact h this
        have hneg : posVertex i ≠ negVertex n := posVertex_ne_negVertex i n
        simp [variablePaletteColorFrom, hpos, hneg, ih hi']

theorem variablePaletteColorFrom_neg {a : SAT.Assignment} {n i : Nat} (hi : i < n) :
    variablePaletteColorFrom a n (negVertex i) = if a i then 2 else 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i = n
      · subst i
        simp [variablePaletteColorFrom]
      · have hi' : i < n := by omega
        have hpos : negVertex i ≠ posVertex n := negVertex_ne_posVertex i n
        have hneg : negVertex i ≠ negVertex n := by
          intro hEq
          have : i = n := (negVertex_inj.mp hEq)
          exact h this
        simp [variablePaletteColorFrom, hpos, hneg, ih hi']

def clauseGadgetColor (b₀ b₁ b₂ : Bool) : Nat → Nat
  | 0 =>
      match b₀, b₁, b₂ with
      | true, true, true => 2
      | true, true, false => 2
      | true, false, true => 1
      | true, false, false => 1
      | false, true, true => 2
      | false, true, false => 2
      | false, false, true => 0
      | false, false, false => 0
  | 1 =>
      match b₀, b₁, b₂ with
      | true, true, true => 0
      | true, true, false => 0
      | true, false, true => 2
      | true, false, false => 0
      | false, true, true => 0
      | false, true, false => 0
      | false, false, true => 2
      | false, false, false => 0
  | 2 =>
      match b₀, b₁, b₂ with
      | true, true, true => 0
      | true, true, false => 0
      | true, false, true => 2
      | true, false, false => 2
      | false, true, true => 1
      | false, true, false => 1
      | false, false, true => 1
      | false, false, false => 0
  | _ =>
      match b₀, b₁, b₂ with
      | true, true, true => 2
      | true, true, false => 2
      | true, false, true => 0
      | true, false, false => 0
      | false, true, true => 0
      | false, true, false => 0
      | false, false, true => 0
      | false, false, false => 0

theorem clauseGadgetColor_lt_three (b₀ b₁ b₂ : Bool) (slot : Nat) :
    clauseGadgetColor b₀ b₁ b₂ slot < 3 := by
  fin_cases b₀ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    cases slot with
    | zero => simp [clauseGadgetColor]
    | succ slot =>
        cases slot with
        | zero => simp [clauseGadgetColor]
        | succ slot =>
            cases slot with
            | zero => simp [clauseGadgetColor]
            | succ slot =>
                cases slot with
                | zero => simp [clauseGadgetColor]
                | succ slot => simp [clauseGadgetColor]

def clauseColorFor (a : SAT.Assignment) (c : SAT.Clause) (slot : Nat) : Nat :=
  match paddedClause c with
  | none => 0
  | some (l₀, l₁, l₂) =>
      clauseGadgetColor (l₀.eval a) (l₁.eval a) (l₂.eval a) slot

theorem clauseColorFor_lt_three (a : SAT.Assignment) (c : SAT.Clause) (slot : Nat) :
    clauseColorFor a c slot < 3 := by
  unfold clauseColorFor
  split
  · omega
  · apply clauseGadgetColor_lt_three

def forwardColorFrom (a : SAT.Assignment) (n : Nat) :
    List SAT.Clause → Nat → Nat → Nat
  | [], _j, v => variablePaletteColorFrom a n v
  | c :: cs, j, v =>
      if v = clauseA0 n j then clauseColorFor a c 0
      else if v = clauseA1 n j then clauseColorFor a c 1
      else if v = clauseA2 n j then clauseColorFor a c 2
      else if v = clauseA3 n j then clauseColorFor a c 3
      else forwardColorFrom a n cs (j + 1) v

def forwardColor (φ : SAT.ThreeCNF) (a : SAT.Assignment) : Nat → Nat :=
  forwardColorFrom a (Clique.cnfVarBound φ.clauses) φ.clauses 0

theorem forwardColorFrom_lt_three (a : SAT.Assignment) (n : Nat)
    (cs : List SAT.Clause) (j v : Nat) :
    forwardColorFrom a n cs j v < 3 := by
  induction cs generalizing j with
  | nil =>
      simpa [forwardColorFrom] using variablePaletteColorFrom_lt_three a n v
  | cons c cs ih =>
      simp [forwardColorFrom]
      split
      · apply clauseColorFor_lt_three
      · split
        · apply clauseColorFor_lt_three
        · split
          · apply clauseColorFor_lt_three
          · split
            · apply clauseColorFor_lt_three
            · exact ih (j + 1)

theorem forwardColor_lt_three (φ : SAT.ThreeCNF) (a : SAT.Assignment) (v : Nat) :
    forwardColor φ a v < 3 :=
  forwardColorFrom_lt_three a (Clique.cnfVarBound φ.clauses) φ.clauses 0 v

theorem baseVertex_ne_clauseA0 (n j : Nat) : baseVertex ≠ clauseA0 n j := by
  simp [baseVertex, clauseA0, clauseBase, variableLimit]
  omega

theorem baseVertex_ne_clauseA1 (n j : Nat) : baseVertex ≠ clauseA1 n j := by
  simp [baseVertex, clauseA1, clauseBase, variableLimit]

theorem baseVertex_ne_clauseA2 (n j : Nat) : baseVertex ≠ clauseA2 n j := by
  simp [baseVertex, clauseA2, clauseBase, variableLimit]

theorem baseVertex_ne_clauseA3 (n j : Nat) : baseVertex ≠ clauseA3 n j := by
  simp [baseVertex, clauseA3, clauseBase, variableLimit]

theorem trueVertex_ne_clauseA0 (n j : Nat) : trueVertex ≠ clauseA0 n j := by
  simp [trueVertex, clauseA0, clauseBase, variableLimit]
  omega

theorem trueVertex_ne_clauseA1 (n j : Nat) : trueVertex ≠ clauseA1 n j := by
  simp [trueVertex, clauseA1, clauseBase, variableLimit]

theorem trueVertex_ne_clauseA2 (n j : Nat) : trueVertex ≠ clauseA2 n j := by
  simp [trueVertex, clauseA2, clauseBase, variableLimit]

theorem trueVertex_ne_clauseA3 (n j : Nat) : trueVertex ≠ clauseA3 n j := by
  simp [trueVertex, clauseA3, clauseBase, variableLimit]

theorem falseVertex_ne_clauseA0 (n j : Nat) : falseVertex ≠ clauseA0 n j := by
  simp [falseVertex, clauseA0, clauseBase, variableLimit]
  omega

theorem falseVertex_ne_clauseA1 (n j : Nat) : falseVertex ≠ clauseA1 n j := by
  simp [falseVertex, clauseA1, clauseBase, variableLimit]
  omega

theorem falseVertex_ne_clauseA2 (n j : Nat) : falseVertex ≠ clauseA2 n j := by
  simp [falseVertex, clauseA2, clauseBase, variableLimit]

theorem falseVertex_ne_clauseA3 (n j : Nat) : falseVertex ≠ clauseA3 n j := by
  simp [falseVertex, clauseA3, clauseBase, variableLimit]

theorem posVertex_ne_clauseA0 {i n j : Nat} (hi : i < n) :
    posVertex i ≠ clauseA0 n j := by
  simp [posVertex, clauseA0, clauseBase, variableLimit]
  omega

theorem posVertex_ne_clauseA1 {i n j : Nat} (_hi : i < n) :
    posVertex i ≠ clauseA1 n j := by
  simp [posVertex, clauseA1, clauseBase, variableLimit]
  omega

theorem posVertex_ne_clauseA2 {i n j : Nat} (hi : i < n) :
    posVertex i ≠ clauseA2 n j := by
  simp [posVertex, clauseA2, clauseBase, variableLimit]
  omega

theorem posVertex_ne_clauseA3 {i n j : Nat} (_hi : i < n) :
    posVertex i ≠ clauseA3 n j := by
  simp [posVertex, clauseA3, clauseBase, variableLimit]
  omega

theorem negVertex_ne_clauseA0 {i n j : Nat} (_hi : i < n) :
    negVertex i ≠ clauseA0 n j := by
  simp [negVertex, clauseA0, clauseBase, variableLimit]
  omega

theorem negVertex_ne_clauseA1 {i n j : Nat} (hi : i < n) :
    negVertex i ≠ clauseA1 n j := by
  simp [negVertex, clauseA1, clauseBase, variableLimit]
  omega

theorem negVertex_ne_clauseA2 {i n j : Nat} (_hi : i < n) :
    negVertex i ≠ clauseA2 n j := by
  simp [negVertex, clauseA2, clauseBase, variableLimit]
  omega

theorem negVertex_ne_clauseA3 {i n j : Nat} (hi : i < n) :
    negVertex i ≠ clauseA3 n j := by
  simp [negVertex, clauseA3, clauseBase, variableLimit]
  omega

theorem clauseA0_ne_clauseA1 (n j : Nat) : clauseA0 n j ≠ clauseA1 n j := by
  simp [clauseA0, clauseA1]

theorem clauseA0_ne_clauseA2 (n j : Nat) : clauseA0 n j ≠ clauseA2 n j := by
  simp [clauseA0, clauseA2]

theorem clauseA0_ne_clauseA3 (n j : Nat) : clauseA0 n j ≠ clauseA3 n j := by
  simp [clauseA0, clauseA3]

theorem clauseA1_ne_clauseA0 (n j : Nat) : clauseA1 n j ≠ clauseA0 n j := by
  exact Ne.symm (clauseA0_ne_clauseA1 n j)

theorem clauseA1_ne_clauseA2 (n j : Nat) : clauseA1 n j ≠ clauseA2 n j := by
  simp [clauseA1, clauseA2]

theorem clauseA1_ne_clauseA3 (n j : Nat) : clauseA1 n j ≠ clauseA3 n j := by
  simp [clauseA1, clauseA3]

theorem clauseA2_ne_clauseA0 (n j : Nat) : clauseA2 n j ≠ clauseA0 n j := by
  exact Ne.symm (clauseA0_ne_clauseA2 n j)

theorem clauseA2_ne_clauseA1 (n j : Nat) : clauseA2 n j ≠ clauseA1 n j := by
  exact Ne.symm (clauseA1_ne_clauseA2 n j)

theorem clauseA2_ne_clauseA3 (n j : Nat) : clauseA2 n j ≠ clauseA3 n j := by
  simp [clauseA2, clauseA3]

theorem clauseA3_ne_clauseA0 (n j : Nat) : clauseA3 n j ≠ clauseA0 n j := by
  exact Ne.symm (clauseA0_ne_clauseA3 n j)

theorem clauseA3_ne_clauseA1 (n j : Nat) : clauseA3 n j ≠ clauseA1 n j := by
  exact Ne.symm (clauseA1_ne_clauseA3 n j)

theorem clauseA3_ne_clauseA2 (n j : Nat) : clauseA3 n j ≠ clauseA2 n j := by
  exact Ne.symm (clauseA2_ne_clauseA3 n j)

theorem forwardColorFrom_base (a : SAT.Assignment) (n : Nat)
    (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j baseVertex = 0 := by
  induction cs generalizing j with
  | nil =>
      simp [forwardColorFrom, variablePaletteColorFrom_base]
  | cons c cs ih =>
      simp [forwardColorFrom, baseVertex_ne_clauseA0, baseVertex_ne_clauseA1,
        baseVertex_ne_clauseA2, baseVertex_ne_clauseA3, ih]

theorem forwardColorFrom_true (a : SAT.Assignment) (n : Nat)
    (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j trueVertex = 1 := by
  induction cs generalizing j with
  | nil =>
      simp [forwardColorFrom, variablePaletteColorFrom_true]
  | cons c cs ih =>
      simp [forwardColorFrom, trueVertex_ne_clauseA0, trueVertex_ne_clauseA1,
        trueVertex_ne_clauseA2, trueVertex_ne_clauseA3, ih]

theorem forwardColorFrom_false (a : SAT.Assignment) (n : Nat)
    (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j falseVertex = 2 := by
  induction cs generalizing j with
  | nil =>
      simp [forwardColorFrom, variablePaletteColorFrom_false]
  | cons c cs ih =>
      simp [forwardColorFrom, falseVertex_ne_clauseA0, falseVertex_ne_clauseA1,
        falseVertex_ne_clauseA2, falseVertex_ne_clauseA3, ih]

theorem forwardColorFrom_pos {a : SAT.Assignment} {n i : Nat}
    (hi : i < n) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j (posVertex i) = if a i then 1 else 2 := by
  induction cs generalizing j with
  | nil =>
      simpa [forwardColorFrom] using variablePaletteColorFrom_pos (a := a) (n := n) hi
  | cons c cs ih =>
      simp [forwardColorFrom, posVertex_ne_clauseA0 hi, posVertex_ne_clauseA1 hi,
        posVertex_ne_clauseA2 hi, posVertex_ne_clauseA3 hi, ih]

theorem forwardColorFrom_neg {a : SAT.Assignment} {n i : Nat}
    (hi : i < n) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j (negVertex i) = if a i then 2 else 1 := by
  induction cs generalizing j with
  | nil =>
      simpa [forwardColorFrom] using variablePaletteColorFrom_neg (a := a) (n := n) hi
  | cons c cs ih =>
      simp [forwardColorFrom, negVertex_ne_clauseA0 hi, negVertex_ne_clauseA1 hi,
        negVertex_ne_clauseA2 hi, negVertex_ne_clauseA3 hi, ih]

theorem forwardColorFrom_literalVertex {a : SAT.Assignment} {n : Nat}
    {l : SAT.Literal} (hvar : l.var < n) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n cs j (literalVertex l) =
      if l.eval a then 1 else 2 := by
  cases l with
  | mk var neg =>
      cases neg
      · simp [literalVertex, SAT.Literal.eval, forwardColorFrom_pos hvar cs j]
      · by_cases hav : a var
        · simp [literalVertex, SAT.Literal.eval, forwardColorFrom_neg hvar cs j, hav]
        · simp [literalVertex, SAT.Literal.eval, forwardColorFrom_neg hvar cs j, hav]

theorem forwardColorFrom_clauseA0_head (a : SAT.Assignment) (n : Nat)
    (c : SAT.Clause) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n (c :: cs) j (clauseA0 n j) = clauseColorFor a c 0 := by
  simp [forwardColorFrom]

theorem forwardColorFrom_clauseA1_head (a : SAT.Assignment) (n : Nat)
    (c : SAT.Clause) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n (c :: cs) j (clauseA1 n j) = clauseColorFor a c 1 := by
  simp [forwardColorFrom, clauseA1_ne_clauseA0]

theorem forwardColorFrom_clauseA2_head (a : SAT.Assignment) (n : Nat)
    (c : SAT.Clause) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n (c :: cs) j (clauseA2 n j) = clauseColorFor a c 2 := by
  simp [forwardColorFrom, clauseA2_ne_clauseA0, clauseA2_ne_clauseA1]

theorem forwardColorFrom_clauseA3_head (a : SAT.Assignment) (n : Nat)
    (c : SAT.Clause) (cs : List SAT.Clause) (j : Nat) :
    forwardColorFrom a n (c :: cs) j (clauseA3 n j) = clauseColorFor a c 3 := by
  simp [forwardColorFrom, clauseA3_ne_clauseA0, clauseA3_ne_clauseA1, clauseA3_ne_clauseA2]

theorem paddedClause_or_true_of_satisfies {a : SAT.Assignment} {c : SAT.Clause}
    {l₀ l₁ l₂ : SAT.Literal}
    (hLen : c.length ≤ 3)
    (hp : paddedClause c = some (l₀, l₁, l₂))
    (hSat : SAT.Clause.Satisfies c a) :
    l₀.eval a || l₁.eval a || l₂.eval a = true := by
  rcases hSat with ⟨l, hl, hlEval⟩
  cases c with
  | nil =>
      simp [paddedClause] at hp
  | cons c₀ cs =>
      cases cs with
      | nil =>
          simp [paddedClause] at hp
          rcases hp with ⟨rfl, rfl, rfl⟩
          simp at hl
          subst l
          simpa using hlEval
      | cons c₁ cs =>
          cases cs with
          | nil =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp at hl
              rcases hl with rfl | rfl
              · simp [hlEval]
              · simp [hlEval]
          | cons c₂ cs =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp at hl
              rcases hl with rfl | rfl | rfl | hrest
              · simp [hlEval]
              · simp [hlEval]
              · simp [hlEval]
              · have hcs : cs = [] := by
                  cases cs with
                  | nil => rfl
                  | cons head tail =>
                      simp at hLen
                      omega
                simp [hcs] at hrest

theorem clauseGadgetColor_edges_ne (b₀ b₁ b₂ : Bool)
    (hOr : b₀ || b₁ || b₂ = true) :
    clauseGadgetColor b₀ b₁ b₂ 0 ≠ clauseGadgetColor b₀ b₁ b₂ 1 ∧
      clauseGadgetColor b₀ b₁ b₂ 0 ≠ clauseGadgetColor b₀ b₁ b₂ 2 ∧
      clauseGadgetColor b₀ b₁ b₂ 3 ≠ 1 ∧
      clauseGadgetColor b₀ b₁ b₂ 1 ≠ 1 ∧
      clauseGadgetColor b₀ b₁ b₂ 2 ≠ clauseGadgetColor b₀ b₁ b₂ 3 ∧
      (if b₀ then 1 else 2) ≠ clauseGadgetColor b₀ b₁ b₂ 2 ∧
      (if b₀ then 1 else 2) ≠ clauseGadgetColor b₀ b₁ b₂ 3 ∧
      (if b₁ then 1 else 2) ≠ clauseGadgetColor b₀ b₁ b₂ 0 ∧
      (if b₂ then 1 else 2) ≠ clauseGadgetColor b₀ b₁ b₂ 1 := by
  fin_cases b₀ <;> fin_cases b₁ <;> fin_cases b₂ <;>
    simp [clauseGadgetColor] at hOr ⊢

theorem paddedClause_left_mem {c : SAT.Clause} {l₀ l₁ l₂ : SAT.Literal}
    (hp : paddedClause c = some (l₀, l₁, l₂)) :
    l₀ ∈ c := by
  cases c with
  | nil =>
      simp [paddedClause] at hp
  | cons c₀ cs =>
      cases cs with
      | nil =>
          simp [paddedClause] at hp
          rcases hp with ⟨rfl, rfl, rfl⟩
          simp
      | cons c₁ cs =>
          cases cs with
          | nil =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp
          | cons c₂ cs =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp

theorem paddedClause_middle_mem {c : SAT.Clause} {l₀ l₁ l₂ : SAT.Literal}
    (hp : paddedClause c = some (l₀, l₁, l₂)) :
    l₁ ∈ c := by
  cases c with
  | nil =>
      simp [paddedClause] at hp
  | cons c₀ cs =>
      cases cs with
      | nil =>
          simp [paddedClause] at hp
          rcases hp with ⟨rfl, rfl, rfl⟩
          simp
      | cons c₁ cs =>
          cases cs with
          | nil =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp
          | cons c₂ cs =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp

theorem paddedClause_right_mem {c : SAT.Clause} {l₀ l₁ l₂ : SAT.Literal}
    (hp : paddedClause c = some (l₀, l₁, l₂)) :
    l₂ ∈ c := by
  cases c with
  | nil =>
      simp [paddedClause] at hp
  | cons c₀ cs =>
      cases cs with
      | nil =>
          simp [paddedClause] at hp
          rcases hp with ⟨rfl, rfl, rfl⟩
          simp
      | cons c₁ cs =>
          cases cs with
          | nil =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp
          | cons c₂ cs =>
              simp [paddedClause] at hp
              rcases hp with ⟨rfl, rfl, rfl⟩
              simp

def NeHeadSlots (n j v : Nat) : Prop :=
  v ≠ clauseA0 n j ∧ v ≠ clauseA1 n j ∧ v ≠ clauseA2 n j ∧ v ≠ clauseA3 n j

theorem baseVertex_neHeadSlots (n j : Nat) :
    NeHeadSlots n j baseVertex :=
  ⟨baseVertex_ne_clauseA0 n j, baseVertex_ne_clauseA1 n j,
    baseVertex_ne_clauseA2 n j, baseVertex_ne_clauseA3 n j⟩

theorem literalVertex_neHeadSlots {n j : Nat} {l : SAT.Literal}
    (hvar : l.var < n) :
    NeHeadSlots n j (literalVertex l) := by
  cases l with
  | mk var neg =>
      cases neg
      · simp [literalVertex]
        exact ⟨posVertex_ne_clauseA0 hvar, posVertex_ne_clauseA1 hvar,
          posVertex_ne_clauseA2 hvar, posVertex_ne_clauseA3 hvar⟩
      · simp [literalVertex]
        exact ⟨negVertex_ne_clauseA0 hvar, negVertex_ne_clauseA1 hvar,
          negVertex_ne_clauseA2 hvar, negVertex_ne_clauseA3 hvar⟩

theorem clauseA0_neHeadSlots_of_lt {n prev start : Nat} (h : prev < start) :
    NeHeadSlots n prev (clauseA0 n start) := by
  simp [NeHeadSlots, clauseA0, clauseA1, clauseA2, clauseA3, clauseBase]
  omega

theorem clauseA1_neHeadSlots_of_lt {n prev start : Nat} (h : prev < start) :
    NeHeadSlots n prev (clauseA1 n start) := by
  simp [NeHeadSlots, clauseA0, clauseA1, clauseA2, clauseA3, clauseBase]
  omega

theorem clauseA2_neHeadSlots_of_lt {n prev start : Nat} (h : prev < start) :
    NeHeadSlots n prev (clauseA2 n start) := by
  simp [NeHeadSlots, clauseA0, clauseA1, clauseA2, clauseA3, clauseBase]
  omega

theorem clauseA3_neHeadSlots_of_lt {n prev start : Nat} (h : prev < start) :
    NeHeadSlots n prev (clauseA3 n start) := by
  simp [NeHeadSlots, clauseA0, clauseA1, clauseA2, clauseA3, clauseBase]
  omega

theorem endpoints_neHeadSlots_of_mem_clauseEdgesFor {n prev start : Nat}
    {c : SAT.Clause} {e : Nat × Nat}
    (hprev : prev < start)
    (hBound : ∀ l ∈ c, l.var < n)
    (he : e ∈ clauseEdgesFor n start c) :
    NeHeadSlots n prev e.1 ∧ NeHeadSlots n prev e.2 := by
  unfold clauseEdgesFor at he
  cases hp : paddedClause c with
  | none =>
      simp [hp] at he
      subst e
      exact ⟨baseVertex_neHeadSlots n prev, baseVertex_neHeadSlots n prev⟩
  | some triple =>
      rcases triple with ⟨l₀, l₁, l₂⟩
      have h₀ : l₀.var < n := hBound l₀ (paddedClause_left_mem hp)
      have h₁ : l₁.var < n := hBound l₁ (paddedClause_middle_mem hp)
      have h₂ : l₂.var < n := hBound l₂ (paddedClause_right_mem hp)
      simp [hp, clauseGadgetEdges] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨clauseA0_neHeadSlots_of_lt hprev, clauseA1_neHeadSlots_of_lt hprev⟩
      · exact ⟨clauseA0_neHeadSlots_of_lt hprev, clauseA2_neHeadSlots_of_lt hprev⟩
      · exact ⟨clauseA3_neHeadSlots_of_lt hprev, ⟨trueVertex_ne_clauseA0 n prev,
          trueVertex_ne_clauseA1 n prev, trueVertex_ne_clauseA2 n prev,
          trueVertex_ne_clauseA3 n prev⟩⟩
      · exact ⟨clauseA1_neHeadSlots_of_lt hprev, ⟨trueVertex_ne_clauseA0 n prev,
          trueVertex_ne_clauseA1 n prev, trueVertex_ne_clauseA2 n prev,
          trueVertex_ne_clauseA3 n prev⟩⟩
      · exact ⟨clauseA2_neHeadSlots_of_lt hprev, clauseA3_neHeadSlots_of_lt hprev⟩
      · exact ⟨literalVertex_neHeadSlots h₀, clauseA2_neHeadSlots_of_lt hprev⟩
      · exact ⟨literalVertex_neHeadSlots h₀, clauseA3_neHeadSlots_of_lt hprev⟩
      · exact ⟨literalVertex_neHeadSlots h₁, clauseA0_neHeadSlots_of_lt hprev⟩
      · exact ⟨literalVertex_neHeadSlots h₂, clauseA1_neHeadSlots_of_lt hprev⟩

theorem endpoints_neHeadSlots_of_mem_clauseEdgesFrom {n prev start : Nat}
    {cs : List SAT.Clause} {e : Nat × Nat}
    (hprev : prev < start)
    (hBound : ∀ c ∈ cs, ∀ l ∈ c, l.var < n)
    (he : e ∈ clauseEdgesFrom n start cs) :
    NeHeadSlots n prev e.1 ∧ NeHeadSlots n prev e.2 := by
  induction cs generalizing start with
  | nil =>
      simp [clauseEdgesFrom] at he
  | cons c cs ih =>
      simp [clauseEdgesFrom] at he
      rcases he with he | he
      · exact endpoints_neHeadSlots_of_mem_clauseEdgesFor hprev
          (fun l hl => hBound c (by simp) l hl) he
      · exact ih (start := start + 1) (by omega)
          (fun d hd l hl => hBound d (by simp [hd]) l hl) he

theorem forwardColorFrom_cons_eq_of_neHeadSlots {a : SAT.Assignment} {n j v : Nat}
    {c : SAT.Clause} {cs : List SAT.Clause}
    (h : NeHeadSlots n j v) :
    forwardColorFrom a n (c :: cs) j v = forwardColorFrom a n cs (j + 1) v := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [forwardColorFrom, h0, h1, h2, h3]

end ChromaticNumber
end Karp21
end ComplexityReduction
