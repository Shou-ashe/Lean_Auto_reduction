/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Basic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic

/-!
First P15b target: local 3SAT to Clique.
-/

namespace ComplexityReduction
namespace Karp21
namespace Clique

open ComplexityReduction.Combinatorics.Graph

/-- A structural upper bound for all variables occurring in a clause. -/
def clauseVarBound : SAT.Clause → Nat
  | [] => 0
  | l :: ls => max (l.var + 1) (clauseVarBound ls)

theorem var_lt_clauseVarBound_of_mem {c : SAT.Clause} {l : SAT.Literal}
    (hl : l ∈ c) :
    l.var < clauseVarBound c := by
  induction c with
  | nil => simp at hl
  | cons head tail ih =>
      simp at hl
      rcases hl with rfl | hl
      · exact lt_of_lt_of_le (Nat.lt_succ_self l.var) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ih hl) (Nat.le_max_right _ _)

/-- A structural upper bound for all variables occurring in a CNF. -/
def cnfVarBound : SAT.CNF → Nat
  | [] => 0
  | c :: cs => max (clauseVarBound c) (cnfVarBound cs)

theorem var_lt_cnfVarBound_of_mem {φ : SAT.CNF} {c : SAT.Clause} {l : SAT.Literal}
    (hc : c ∈ φ) (hl : l ∈ c) :
    l.var < cnfVarBound φ := by
  induction φ with
  | nil => simp at hc
  | cons head tail ih =>
      simp at hc
      rcases hc with rfl | hc
      · exact lt_of_lt_of_le (var_lt_clauseVarBound_of_mem hl) (Nat.le_max_left _ _)
      · exact lt_of_lt_of_le (ih hc) (Nat.le_max_right _ _)

/-- Assignment induced by a Boolean function over the bounded variable range. -/
def boundedAssignment (n : Nat) (a : Fin n → Bool) : SAT.Assignment :=
  fun x => if h : x < n then a ⟨x, h⟩ else false

theorem literal_eval_bounded_eq {n : Nat} {a : SAT.Assignment} {f : Fin n → Bool}
    {l : SAT.Literal} (hvar : l.var < n)
    (hf : ∀ i : Fin n, f i = a i.val) :
    l.eval (boundedAssignment n f) = l.eval a := by
  cases l with
  | mk var neg =>
      by_cases hneg : neg
      · simp [SAT.Literal.eval, boundedAssignment, hvar, hneg, hf ⟨var, hvar⟩]
      · simp [SAT.Literal.eval, boundedAssignment, hvar, hneg, hf ⟨var, hvar⟩]

theorem threeCNF_satisfies_bounded_of_satisfies {φ : SAT.ThreeCNF}
    {a : SAT.Assignment} (hSat : φ.Satisfies a) :
    φ.Satisfies
      (boundedAssignment (cnfVarBound φ.clauses) fun i : Fin (cnfVarBound φ.clauses) =>
        a i.val) := by
  intro c hc
  rcases hSat c hc with ⟨l, hl, hlEval⟩
  refine ⟨l, hl, ?_⟩
  have hvar := var_lt_cnfVarBound_of_mem hc hl
  simpa [literal_eval_bounded_eq hvar (by intro i; rfl)] using hlEval

/-- All bounded assignments used as clique vertices. -/
noncomputable def assignmentList (n : Nat) : List (Fin n → Bool) := by
  classical
  exact (Finset.univ : Finset (Fin n → Bool)).toList

theorem mem_assignmentList (n : Nat) (a : Fin n → Bool) :
    a ∈ assignmentList n := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ a)

/-- Decode a non-anchor vertex to the bounded assignment it names. -/
noncomputable def assignmentAt? (n v : Nat) : Option (Fin n → Bool) :=
  (assignmentList n)[v - 1]?

/-- Edge predicate for the assignment-vertex clique instance. -/
noncomputable def edgeOK (φ : SAT.ThreeCNF) (u v : Nat) : Prop := by
  classical
  let n := cnfVarBound φ.clauses
  exact
    (u = 0 ∧ ∃ a ∈ assignmentAt? n v, φ.Satisfies (boundedAssignment n a)) ∨
      (v = 0 ∧ ∃ a ∈ assignmentAt? n u, φ.Satisfies (boundedAssignment n a))

/-- Edge list for the assignment-vertex clique instance. -/
noncomputable def edgeList (φ : SAT.ThreeCNF) : List (Nat × Nat) := by
  classical
  let n := cnfVarBound φ.clauses
  let vertexCount := 1 + (assignmentList n).length
  exact ((List.range vertexCount).product (List.range vertexCount)).filter fun e =>
    decide (edgeOK φ e.1 e.2)

theorem mem_edgeList_iff (φ : SAT.ThreeCNF) (e : Nat × Nat) :
    e ∈ edgeList φ ↔
      e.1 < 1 + (assignmentList (cnfVarBound φ.clauses)).length ∧
        e.2 < 1 + (assignmentList (cnfVarBound φ.clauses)).length ∧
        edgeOK φ e.1 e.2 := by
  cases e with
  | mk u v =>
      simp [edgeList, and_assoc]

/-- P15b syntax map from local 3SAT to an assignment-vertex Clique instance. -/
noncomputable def map (φ : SAT.ThreeCNF) : CliqueInput where
  graph :=
    { vertices := 1 + (assignmentList (cnfVarBound φ.clauses)).length
      edges := edgeList φ
      directed := false }
  k := 2

theorem edge_mem_of_satisfying_assignment (φ : SAT.ThreeCNF)
    (a : Fin (cnfVarBound φ.clauses) → Bool)
    (hSat : φ.Satisfies (boundedAssignment (cnfVarBound φ.clauses) a)) :
    (0, 1 + (assignmentList (cnfVarBound φ.clauses)).idxOf a) ∈ edgeList φ := by
  classical
  let n := cnfVarBound φ.clauses
  have haMem : a ∈ assignmentList n := mem_assignmentList n a
  have hIdx : (assignmentList n).idxOf a < (assignmentList n).length :=
    List.idxOf_lt_length_iff.mpr haMem
  rw [mem_edgeList_iff]
  refine ⟨by simp, ?_, ?_⟩
  · simpa [n] using Nat.succ_lt_succ hIdx
  left
  refine ⟨rfl, ?_⟩
  refine ⟨a, ?_, hSat⟩
  simp [assignmentAt?, n, List.getElem?_idxOf haMem]

theorem satisfiable_of_edge_mem {φ : SAT.ThreeCNF} {u v : Nat}
    (h : (u, v) ∈ edgeList φ) :
    SAT.ThreeCNF.Satisfiable φ := by
  classical
  have hOK := (mem_edgeList_iff φ (u, v)).1 h |>.2.2
  rcases hOK with ⟨_hu, a, _ha, hSat⟩ | ⟨_hv, a, _ha, hSat⟩
  · exact ⟨boundedAssignment (cnfVarBound φ.clauses) a, hSat⟩
  · exact ⟨boundedAssignment (cnfVarBound φ.clauses) a, hSat⟩

theorem map_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ Clique (map φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    let n := cnfVarBound φ.clauses
    let f : Fin n → Bool := fun i => a i.val
    let v := 1 + (assignmentList n).idxOf f
    have hSatBounded : φ.Satisfies (boundedAssignment n f) :=
      threeCNF_satisfies_bounded_of_satisfies hSat
    have hEdge : (0, v) ∈ edgeList φ := by
      simpa [n, f, v] using edge_mem_of_satisfying_assignment φ f hSatBounded
    have hvBound : v < (map φ).graph.vertices := by
      have hfMem : f ∈ assignmentList n := mem_assignmentList n f
      have hIdx : (assignmentList n).idxOf f < (assignmentList n).length :=
        List.idxOf_lt_length_iff.mpr hfMem
      simp [map, n, v]
      omega
    refine ⟨[0, v], rfl, ?_, ?_, ?_⟩
    · simp [v]
      omega
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · simp [map]
      · exact hvBound
    · intro u hu w hw huw
      simp at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact (huw rfl).elim
      · exact Or.inl hEdge
      · exact Or.inr hEdge
      · exact (huw rfl).elim
  · intro hClique
    rcases hClique with ⟨vs, hLen, hNodup, _hBounds, hAdj⟩
    cases vs with
    | nil => simp [map] at hLen
    | cons u rest =>
        cases rest with
        | nil => simp [map] at hLen
        | cons v rest' =>
            cases rest' with
            | cons w rest'' => simp [map] at hLen
            | nil =>
                have huv : u ≠ v := by
                  simpa using hNodup
                have hEdge := hAdj u (by simp) v (by simp) huv
                rcases hEdge with h | h
                · exact satisfiable_of_edge_mem h
                · exact satisfiable_of_edge_mem h

/-! ### Textbook clause-literal compatibility graph -/

/-- One concrete literal occurrence in a source 3CNF formula. -/
structure LiteralOccurrence where
  clause : Nat
  slot : Nat
  lit : SAT.Literal
  deriving DecidableEq, Repr

def defaultOccurrence : LiteralOccurrence :=
  { clause := 0, slot := 0, lit := SAT.Literal.positive 0 }

/-- Two literal occurrences are compatible when they come from different clauses and
are not complementary literals. -/
def occurrenceCompatible (a b : LiteralOccurrence) : Prop :=
  a.clause ≠ b.clause ∧ (a.lit.var ≠ b.lit.var ∨ a.lit.neg = b.lit.neg)

/-- Literal occurrences for a single clause, with explicit slot numbers. -/
def clauseOccurrencesFrom (j start : Nat) : SAT.Clause → List LiteralOccurrence
  | [] => []
  | l :: ls =>
      { clause := j, slot := start, lit := l } :: clauseOccurrencesFrom j (start + 1) ls

def clauseOccurrences (j : Nat) (c : SAT.Clause) : List LiteralOccurrence :=
  clauseOccurrencesFrom j 0 c

/-- Literal occurrences for a list of clauses, starting at clause index `j`. -/
def formulaOccurrencesFrom (j : Nat) : SAT.CNF → List LiteralOccurrence
  | [] => []
  | c :: cs => clauseOccurrences j c ++ formulaOccurrencesFrom (j + 1) cs

def literalOccurrences (φ : SAT.ThreeCNF) : List LiteralOccurrence :=
  formulaOccurrencesFrom 0 φ.clauses

/-! #### TM-facing delimiter counters for the structured 3CNF syntax -/

def outerDelimiterKeep {α : Type} : Option α → Option Bool
  | none => some true
  | some _ => none

def innerDelimiterKeep {α : Type} : Option (Option α) → Option Bool
  | some none => some true
  | _ => none

def threeCNFClauseDelimiterKeep : threeCNFStructuredEncodedType.Symbol → Option Bool
  := outerDelimiterKeep

def threeCNFLiteralDelimiterKeep : threeCNFStructuredEncodedType.Symbol → Option Bool
  := innerDelimiterKeep

@[simp] theorem outerDelimiterKeep_none {α : Type} :
    (outerDelimiterKeep : Option α → Option Bool) none = some true := rfl

@[simp] theorem outerDelimiterKeep_some {α : Type} (a : α) :
    (outerDelimiterKeep : Option α → Option Bool) (some a) = none := rfl

@[simp] theorem innerDelimiterKeep_none {α : Type} :
    (innerDelimiterKeep : Option (Option α) → Option Bool) none = none := rfl

@[simp] theorem innerDelimiterKeep_some_none {α : Type} :
    (innerDelimiterKeep : Option (Option α) → Option Bool) (some none) = some true := rfl

@[simp] theorem innerDelimiterKeep_some_some {α : Type} (a : α) :
    (innerDelimiterKeep : Option (Option α) → Option Bool) (some (some a)) = none := rfl

@[simp] theorem threeCNFClauseDelimiterKeep_none :
    threeCNFClauseDelimiterKeep none = some true := rfl

@[simp] theorem threeCNFClauseDelimiterKeep_some
    (s : clauseStructuredEncodedType.Symbol) :
    threeCNFClauseDelimiterKeep (some s) = none := rfl

@[simp] theorem threeCNFLiteralDelimiterKeep_none :
    threeCNFLiteralDelimiterKeep none = none := rfl

@[simp] theorem threeCNFLiteralDelimiterKeep_some_none :
    threeCNFLiteralDelimiterKeep (some none) = some true := rfl

@[simp] theorem threeCNFLiteralDelimiterKeep_some_some
    (s : literalStructuredEncodedType.Symbol) :
    threeCNFLiteralDelimiterKeep (some (some s)) = none := rfl

theorem list_encode_outerDelimiter_filterMap (X : EncodedType)
    (xs : List X.Carrier) :
    ((EncodedType.list X).encode xs).filterMap
        (outerDelimiterKeep : (EncodedType.list X).Symbol → Option Bool) =
      List.replicate xs.length true := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      dsimp [EncodedType.list]
      have hPayload :
          ((X.encode x).map some).filterMap
              (outerDelimiterKeep : Option X.Symbol → Option Bool) = [] := by
        induction X.encode x with
        | nil =>
            rfl
        | cons a rest ihRest =>
            change
              List.filterMap
                  (outerDelimiterKeep : Option X.Symbol → Option Bool)
                  (some a :: List.map some rest) = []
            simp only [List.filterMap_cons, outerDelimiterKeep]
            exact ihRest
      have hTail :
          (List.flatMap (fun x => List.map some (X.encode x) ++ [none]) xs).filterMap
              (outerDelimiterKeep : Option X.Symbol → Option Bool) =
            List.replicate xs.length true := by
        simpa [EncodedType.list] using ih
      calc
        List.filterMap (outerDelimiterKeep : Option X.Symbol → Option Bool)
            ((List.map some (X.encode x) ++ [none]) ++
              List.flatMap (fun x => List.map some (X.encode x) ++ [none]) xs)
            =
              [] ++ [true] ++ List.replicate xs.length true := by
              rw [List.filterMap_append, List.filterMap_append, hPayload, hTail]
              simp [outerDelimiterKeep]
        _ = List.replicate (x :: xs).length true := by
              simpa [Nat.succ_eq_add_one] using
                (show true :: List.replicate xs.length true =
                  List.replicate (Nat.succ xs.length) true from rfl)

theorem list_encode_innerDelimiter_filterMap (X : EncodedType)
    (xs : List X.Carrier) :
    (((EncodedType.list X).encode xs).map
        (some : (EncodedType.list X).Symbol → Option (EncodedType.list X).Symbol)).filterMap
        (innerDelimiterKeep : Option (EncodedType.list X).Symbol → Option Bool) =
      List.replicate xs.length true := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      dsimp [EncodedType.list]
      have hPayload :
          List.filterMap
              (innerDelimiterKeep : Option (Option X.Symbol) → Option Bool)
              (List.map (some : Option X.Symbol → Option (Option X.Symbol))
                (List.map some (X.encode x))) = [] := by
        induction X.encode x with
        | nil =>
            rfl
        | cons a rest ihRest =>
            change
              List.filterMap
                  (innerDelimiterKeep : Option (Option X.Symbol) → Option Bool)
                  (some (some a) :: List.map some (List.map some rest)) = []
            simp only [List.filterMap_cons, innerDelimiterKeep]
            exact ihRest
      have hTail :
          (List.map some
              (List.flatMap (fun x => List.map some (X.encode x) ++ [none]) xs)).filterMap
              (innerDelimiterKeep : Option (Option X.Symbol) → Option Bool) =
            List.replicate xs.length true := by
        simpa [EncodedType.list] using ih
      calc
        List.filterMap (innerDelimiterKeep : Option (Option X.Symbol) → Option Bool)
            (List.map (some : Option X.Symbol → Option (Option X.Symbol))
              ((List.map some (X.encode x) ++ [none]) ++
                List.flatMap (fun x => List.map some (X.encode x) ++ [none]) xs))
            =
              [] ++ [true] ++ List.replicate xs.length true := by
              rw [List.map_append, List.map_append, List.filterMap_append,
                List.filterMap_append, hPayload, hTail]
              simp [innerDelimiterKeep]
        _ = List.replicate (x :: xs).length true := by
              simpa [Nat.succ_eq_add_one] using
                (show true :: List.replicate xs.length true =
                  List.replicate (Nat.succ xs.length) true from rfl)

theorem threeCNFClauseDelimiter_filterMap_eq (φ : SAT.ThreeCNF) :
    (threeCNFStructuredEncodedType.encode φ).filterMap threeCNFClauseDelimiterKeep =
      List.replicate φ.clauses.length true := by
  simpa [threeCNFStructuredEncodedType, cnfStructuredEncodedType,
    threeCNFClauseDelimiterKeep, outerDelimiterKeep] using
    list_encode_outerDelimiter_filterMap clauseStructuredEncodedType φ.clauses

theorem cnfLiteralDelimiter_filterMap_eq (cs : SAT.CNF) :
    (cnfStructuredEncodedType.encode cs).filterMap threeCNFLiteralDelimiterKeep =
      List.replicate (SAT.CNF.totalClauseLength cs) true := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      dsimp [cnfStructuredEncodedType, EncodedType.list] at ih ⊢
      have hClause :
          ((clauseStructuredEncodedType.encode c).map
              (some : clauseStructuredEncodedType.Symbol →
                Option clauseStructuredEncodedType.Symbol)).filterMap
              (threeCNFLiteralDelimiterKeep :
                Option clauseStructuredEncodedType.Symbol → Option Bool) =
            List.replicate c.length true :=
        by simpa [threeCNFLiteralDelimiterKeep, clauseStructuredEncodedType] using
          list_encode_innerDelimiter_filterMap literalStructuredEncodedType c
      let f : Option clauseStructuredEncodedType.Symbol → Option Bool := threeCNFLiteralDelimiterKeep
      let tail :=
        List.flatMap
          (fun x => List.map some (clauseStructuredEncodedType.encode x) ++ [none])
          cs
      have hMap :
          List.filterMap (fun x => f (some x)) (clauseStructuredEncodedType.encode c) =
            List.filterMap f (List.map some (clauseStructuredEncodedType.encode c)) := by
        have hMap :
            List.filterMap (fun x => f (some x)) (clauseStructuredEncodedType.encode c) =
              List.filterMap f (List.map some (clauseStructuredEncodedType.encode c)) := by
          induction clauseStructuredEncodedType.encode c with
          | nil =>
              rfl
          | cons a rest ihRest =>
              cases hfa : f (some a) <;>
                simp only [List.map_cons, List.filterMap_cons, hfa, ihRest]
        exact hMap
      have hClauseF :
          List.filterMap (fun x => f (some x)) (clauseStructuredEncodedType.encode c) =
            List.replicate c.length true := by
        rw [hMap]
        simpa only [f] using hClause
      have ihF :
          List.filterMap f tail =
            List.replicate (SAT.CNF.totalClauseLength cs) true := by
        simpa [f, tail] using ih
      have hBlock :
          List.filterMap f (List.map some (clauseStructuredEncodedType.encode c) ++ [none]) =
            List.filterMap (fun x => f (some x)) (clauseStructuredEncodedType.encode c) := by
        calc
          List.filterMap f (List.map some (clauseStructuredEncodedType.encode c) ++ [none])
              =
                List.filterMap f (List.map some (clauseStructuredEncodedType.encode c)) ++
                  List.filterMap f [none] := by
                rw [List.filterMap_append]
          _ = List.filterMap (fun x => f (some x)) (clauseStructuredEncodedType.encode c) := by
                rw [← hMap]
                simp [f]
      have hBlock' :
          List.filterMap threeCNFLiteralDelimiterKeep
              (List.map some (clauseStructuredEncodedType.encode c) ++ [none]) =
            List.filterMap (fun x => threeCNFLiteralDelimiterKeep (some x))
              (clauseStructuredEncodedType.encode c) := by
        simpa only [f] using hBlock
      have hEq :
          List.filterMap f ((List.map some (clauseStructuredEncodedType.encode c) ++ [none]) ++
              tail) =
            List.replicate (c.length + SAT.CNF.totalClauseLength cs) true := by
        calc
          List.filterMap f
              ((List.map some (clauseStructuredEncodedType.encode c) ++ [none]) ++ tail)
              =
                List.filterMap f (List.map some (clauseStructuredEncodedType.encode c) ++ [none]) ++
                  List.filterMap f tail := by
                rw [List.filterMap_append]
          _ =
                (List.filterMap f (List.map some (clauseStructuredEncodedType.encode c)) ++
                  List.filterMap f [none]) ++
                  List.filterMap f tail := by
                rw [List.filterMap_append]
          _ = (List.replicate c.length true ++ []) ++
                List.replicate (SAT.CNF.totalClauseLength cs) true := by
                simp [f, hClauseF, ihF]
          _ = List.replicate (c.length + SAT.CNF.totalClauseLength cs) true := by
                rw [List.append_nil]
                rw [List.replicate_append_replicate]
      calc
        List.filterMap threeCNFLiteralDelimiterKeep
            (List.flatMap
              (fun x => List.map some (clauseStructuredEncodedType.encode x) ++ [none])
              (c :: cs))
            =
              List.filterMap (fun x => threeCNFLiteralDelimiterKeep (some x))
                (clauseStructuredEncodedType.encode c) ++
              List.filterMap (fun x => threeCNFLiteralDelimiterKeep x) tail := by
              dsimp [tail]
              rw [List.flatMap_cons, List.filterMap_append]
              rw [hBlock']
              rfl
        _ = List.replicate (c.length + SAT.CNF.totalClauseLength cs) true := by
              simpa [f] using hEq
        _ = List.replicate (SAT.CNF.totalClauseLength (c :: cs)) true := by
              simp [SAT.CNF.totalClauseLength]

theorem threeCNFLiteralDelimiter_filterMap_eq (φ : SAT.ThreeCNF) :
    (threeCNFStructuredEncodedType.encode φ).filterMap threeCNFLiteralDelimiterKeep =
      List.replicate (SAT.CNF.totalClauseLength φ.clauses) true := by
  simpa [threeCNFStructuredEncodedType] using cnfLiteralDelimiter_filterMap_eq φ.clauses

def threeCNFClauseCount (φ : SAT.ThreeCNF) : Nat :=
  φ.clauses.length

def threeCNFLiteralOccurrenceCount (φ : SAT.ThreeCNF) : Nat :=
  SAT.CNF.totalClauseLength φ.clauses

theorem threeCNFClauseCount_le_inputSize (φ : SAT.ThreeCNF) :
    threeCNFClauseCount φ ≤ threeCNFStructuredEncodedType.inputSize φ := by
  have hLen := congrArg List.length (threeCNFClauseDelimiter_filterMap_eq φ)
  have hFilter :=
    TM2Programs.filterMap_length_le threeCNFClauseDelimiterKeep
      (threeCNFStructuredEncodedType.encode φ)
  rw [hLen] at hFilter
  simpa [threeCNFClauseCount, EncodedType.inputSize] using hFilter

theorem threeCNFLiteralOccurrenceCount_le_inputSize (φ : SAT.ThreeCNF) :
    threeCNFLiteralOccurrenceCount φ ≤ threeCNFStructuredEncodedType.inputSize φ := by
  have hLen := congrArg List.length (threeCNFLiteralDelimiter_filterMap_eq φ)
  have hFilter :=
    TM2Programs.filterMap_length_le threeCNFLiteralDelimiterKeep
      (threeCNFStructuredEncodedType.encode φ)
  rw [hLen] at hFilter
  simpa [threeCNFLiteralOccurrenceCount, EncodedType.inputSize] using hFilter

noncomputable def threeCNFClauseCountTMBackedMap :
    TMBackedCostedMap threeCNFStructuredEncodedType EncodedType.nat threeCNFClauseCount where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := threeCNFStructuredEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro φ
        simp [threeCNFClauseCount, EncodedType.inputSize, EncodedType.nat]
        exact threeCNFClauseCount_le_inputSize φ))
  tm_polytime := by
    have hPayload :
        TMPolyTimeMap threeCNFStructuredEncodedType unaryPayloadEncodedType
          threeCNFClauseCount :=
      (TMBackedCostedMap.symbolFilterMap
        threeCNFStructuredEncodedType unaryPayloadEncodedType threeCNFClauseCount
        threeCNFClauseDelimiterKeep
        (by
          intro φ
          simpa [unaryPayloadEncodedType, threeCNFClauseCount]
            using (threeCNFClauseDelimiter_filterMap_eq φ).symm)).tm_polytime
    have hNat := unaryPayloadToNatTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hNat hPayload
    simpa [Function.comp] using hComp

noncomputable def threeCNFLiteralOccurrenceCountTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType EncodedType.nat threeCNFLiteralOccurrenceCount where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := threeCNFStructuredEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro φ
        simp [threeCNFLiteralOccurrenceCount, EncodedType.inputSize, EncodedType.nat]
        exact threeCNFLiteralOccurrenceCount_le_inputSize φ))
  tm_polytime := by
    have hPayload :
        TMPolyTimeMap threeCNFStructuredEncodedType unaryPayloadEncodedType
          threeCNFLiteralOccurrenceCount :=
      (TMBackedCostedMap.symbolFilterMap
        threeCNFStructuredEncodedType unaryPayloadEncodedType threeCNFLiteralOccurrenceCount
        threeCNFLiteralDelimiterKeep
        (by
          intro φ
          simpa [unaryPayloadEncodedType, threeCNFLiteralOccurrenceCount]
            using (threeCNFLiteralDelimiter_filterMap_eq φ).symm)).tm_polytime
    have hNat := unaryPayloadToNatTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hNat hPayload
    simpa [Function.comp] using hComp

/-! #### Shared-payload branch helper for the Clique edge generator -/

/--
Encoding for a Boolean branch tag followed by a payload over a shared alphabet.
This is the input shape consumed by the checked tagged branch dispatcher from
the SAT splitter route.
-/
def boolPayloadEncodedType (X : EncodedType) : EncodedType where
  Carrier := Bool × X.Carrier
  Symbol := Bool ⊕ X.Symbol
  finite_symbol := inferInstance
  encode := fun p => Sum.inl p.1 :: (X.encode p.2).map Sum.inr

def boolPayloadAsSum (X : EncodedType) (p : (boolPayloadEncodedType X).Carrier) :
    X.Carrier ⊕ X.Carrier :=
  if p.1 then Sum.inr p.2 else Sum.inl p.2

theorem boolPayloadEncodedType_encode_eq_sum (X : EncodedType)
    (p : (boolPayloadEncodedType X).Carrier) :
    (boolPayloadEncodedType X).encode p =
      match boolPayloadAsSum X p with
      | Sum.inl x => Sum.inl false :: (X.encode x).map Sum.inr
      | Sum.inr x => Sum.inl true :: (X.encode x).map Sum.inr := by
  rcases p with ⟨b, x⟩
  cases b <;> rfl

def boolPayloadFromProductKeep (X : EncodedType) :
    (EncodedType.prod EncodedType.bool X).Symbol → Option (boolPayloadEncodedType X).Symbol
  | some (Sum.inl b) => some (Sum.inl b)
  | some (Sum.inr s) => some (Sum.inr s)
  | none => none

theorem boolPayloadFromProduct_encode_filterMap (X : EncodedType)
    (p : (EncodedType.prod EncodedType.bool X).Carrier) :
    (boolPayloadEncodedType X).encode p =
      ((EncodedType.prod EncodedType.bool X).encode p).filterMap
        (boolPayloadFromProductKeep X) := by
  rcases p with ⟨b, x⟩
  simp [boolPayloadEncodedType, EncodedType.prod, EncodedType.bool,
    boolPayloadFromProductKeep]

/-- Product-encoded `(Bool, payload)` values can be re-encoded for branch dispatch. -/
noncomputable def boolPayloadFromProductTMBackedMap (X : EncodedType) :
    TMBackedCostedMap
      (EncodedType.prod EncodedType.bool X)
      (boolPayloadEncodedType X)
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p) :=
  TMBackedCostedMap.symbolFilterMap
    (EncodedType.prod EncodedType.bool X)
    (boolPayloadEncodedType X)
    (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p)
    (boolPayloadFromProductKeep X)
    (by
      intro p
      exact boolPayloadFromProduct_encode_filterMap X p)

/--
Direct TM2 branch dispatch for a Boolean tag with a shared payload encoding.
The false branch runs `fFalse`; the true branch runs `fTrue`.
-/
theorem boolPayload_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (boolPayloadEncodedType X)
      Y
      (fun p : (boolPayloadEncodedType X).Carrier =>
        if p.1 then fTrue p.2 else fFalse p.2) := by
  rcases hFalse with ⟨hFalse⟩
  rcases hTrue with ⟨hTrue⟩
  let hSum := taggedBranchDispatchComputableInPolyTime hFalse hTrue
  refine ⟨?_⟩
  exact
    { tm := hSum.tm
      inputAlphabet := hSum.inputAlphabet
      outputAlphabet := hSum.outputAlphabet
      time := hSum.time
      outputsFun := by
        intro p
        rcases p with ⟨b, x⟩
        cases b
        · simpa [boolPayloadEncodedType, boolPayloadAsSum] using hSum.outputsFun (Sum.inl x)
        · simpa [boolPayloadEncodedType, boolPayloadAsSum] using hSum.outputsFun (Sum.inr x) }

/--
Direct TM2 branch dispatch from the standard product encoding `(Bool, payload)`.
This is the form used after computing a Boolean condition such as unary natural
equality.
-/
theorem boolProduct_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool X)
      Y
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier =>
        match p.1 with
        | true => fTrue p.2
        | false => fFalse p.2) := by
  have hBranch :=
    boolPayload_dispatch_tm_polytime X Y (fFalse := fFalse) (fTrue := fTrue) hFalse hTrue
  have hTagged := boolPayloadFromProductTMBackedMap X |>.tm_polytime
  have hComp := TMPolyTimeMap.comp hBranch hTagged
  convert hComp using 1
  ext p
  rcases p with ⟨b, x⟩
  cases b <;> rfl

/-- Boolean conjunction as the branch primitive `if left then right else false`. -/
def boolAndPair (p : Bool × Bool) : Bool :=
  match p.1 with
  | true => p.2
  | false => false

theorem boolAndPair_eq_and (p : Bool × Bool) :
    boolAndPair p = (p.1 && p.2) := by
  cases p with
  | mk a b =>
      cases a <;> cases b <;> rfl

theorem boolAndPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool
      boolAndPair := by
  have hFalse : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun _ : Bool => false) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.bool false
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun b : Bool => b) :=
    TMPolyTimeMap.id EncodedType.bool
  simpa [boolAndPair] using
    boolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.bool
      (fFalse := fun _ : Bool => false) (fTrue := fun b : Bool => b) hFalse hTrue

/-- Boolean disjunction as the branch primitive `if left then true else right`. -/
def boolOrPair (p : Bool × Bool) : Bool :=
  match p.1 with
  | true => true
  | false => p.2

theorem boolOrPair_eq_or (p : Bool × Bool) :
    boolOrPair p = (p.1 || p.2) := by
  cases p with
  | mk a b =>
      cases a <;> cases b <;> rfl

theorem boolOrPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool
      boolOrPair := by
  have hFalse : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun b : Bool => b) :=
    TMPolyTimeMap.id EncodedType.bool
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun _ : Bool => true) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.bool true
  simpa [boolOrPair] using
    boolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.bool
      (fFalse := fun b : Bool => b) (fTrue := fun _ : Bool => true) hFalse hTrue

/-- Boolean equality as the branch primitive `if left then right else not right`. -/
def boolEqPair (p : Bool × Bool) : Bool :=
  match p.1 with
  | true => p.2
  | false => Bool.not p.2

theorem boolEqPair_eq_decide (p : Bool × Bool) :
    boolEqPair p = decide (p.1 = p.2) := by
  cases p with
  | mk a b =>
      cases a <;> cases b <;> rfl

theorem boolEqPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      EncodedType.bool
      boolEqPair := by
  have hFalse : TMPolyTimeMap EncodedType.bool EncodedType.bool Bool.not :=
    TMPolyTimeMap.bool_not
  have hTrue : TMPolyTimeMap EncodedType.bool EncodedType.bool (fun b : Bool => b) :=
    TMPolyTimeMap.id EncodedType.bool
  simpa [boolEqPair] using
    boolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.bool
      (fFalse := Bool.not) (fTrue := fun b : Bool => b) hFalse hTrue

/-- Tuple view of the faithful SAT literal encoding. -/
def literalToTuple (l : SAT.Literal) : literalTupleStructuredEncodedType.Carrier :=
  (l.var, l.neg)

noncomputable def literalToTupleTMBackedMap :
    TMBackedCostedMap
      literalStructuredEncodedType
      literalTupleStructuredEncodedType
      literalToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    literalStructuredEncodedType literalTupleStructuredEncodedType literalToTuple
    (Equiv.refl _) (by
      intro l
      change literalTupleStructuredEncodedType.encode (l.var, l.neg) =
        List.map id (literalTupleStructuredEncodedType.encode (l.var, l.neg))
      simp)

theorem literal_var_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType EncodedType.nat SAT.Literal.var := by
  have hTuple := literalToTupleTMBackedMap.tm_polytime
  have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFst hTuple
  simpa [Function.comp, literalToTuple] using hComp

theorem literal_neg_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType EncodedType.bool SAT.Literal.neg := by
  have hTuple := literalToTupleTMBackedMap.tm_polytime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hTuple
  simpa [Function.comp, literalToTuple] using hComp

/-- Tuple encoding for a literal occurrence `(clause, slot, literal)`. -/
def literalOccurrenceTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat literalStructuredEncodedType)

def literalOccurrenceToTuple
    (o : LiteralOccurrence) : literalOccurrenceTupleStructuredEncodedType.Carrier :=
  (o.clause, (o.slot, o.lit))

/-- Faithful structured encoding for literal occurrences used by the edge generator. -/
def literalOccurrenceStructuredEncodedType : EncodedType where
  Carrier := LiteralOccurrence
  Symbol := literalOccurrenceTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun o => literalOccurrenceTupleStructuredEncodedType.encode (literalOccurrenceToTuple o)

noncomputable def literalOccurrenceToTupleTMBackedMap :
    TMBackedCostedMap
      literalOccurrenceStructuredEncodedType
      literalOccurrenceTupleStructuredEncodedType
      literalOccurrenceToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    literalOccurrenceStructuredEncodedType literalOccurrenceTupleStructuredEncodedType
    literalOccurrenceToTuple (Equiv.refl _) (by
      intro o
      change literalOccurrenceTupleStructuredEncodedType.encode (literalOccurrenceToTuple o) =
        List.map id (literalOccurrenceTupleStructuredEncodedType.encode (literalOccurrenceToTuple o))
      simp)

theorem literalOccurrence_clause_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      EncodedType.nat
      LiteralOccurrence.clause := by
  have hTuple := literalOccurrenceToTupleTMBackedMap.tm_polytime
  have hClause :=
    TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat literalStructuredEncodedType)
  have hComp := TMPolyTimeMap.comp hClause hTuple
  simpa [Function.comp, literalOccurrenceToTuple] using hComp

theorem literalOccurrence_payload_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      (EncodedType.prod EncodedType.nat literalStructuredEncodedType)
      (fun o : LiteralOccurrence => (o.slot, o.lit)) := by
  have hTuple := literalOccurrenceToTupleTMBackedMap.tm_polytime
  have hPayload :=
    TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat literalStructuredEncodedType)
  have hComp := TMPolyTimeMap.comp hPayload hTuple
  simpa [Function.comp, literalOccurrenceToTuple] using hComp

theorem literalOccurrence_slot_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      EncodedType.nat
      LiteralOccurrence.slot := by
  have hPayload := literalOccurrence_payload_tm_polytime
  have hSlot := TMPolyTimeMap.fst EncodedType.nat literalStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hSlot hPayload
  simpa [Function.comp] using hComp

theorem literalOccurrence_lit_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      literalStructuredEncodedType
      LiteralOccurrence.lit := by
  have hPayload := literalOccurrence_payload_tm_polytime
  have hLit := TMPolyTimeMap.snd EncodedType.nat literalStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hLit hPayload
  simpa [Function.comp] using hComp

theorem literalOccurrence_lit_var_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      EncodedType.nat
      (fun o : LiteralOccurrence => o.lit.var) := by
  have hComp := TMPolyTimeMap.comp literal_var_tm_polytime literalOccurrence_lit_tm_polytime
  simpa [Function.comp] using hComp

theorem literalOccurrence_lit_neg_tm_polytime :
    TMPolyTimeMap
      literalOccurrenceStructuredEncodedType
      EncodedType.bool
      (fun o : LiteralOccurrence => o.lit.neg) := by
  have hComp := TMPolyTimeMap.comp literal_neg_tm_polytime literalOccurrence_lit_tm_polytime
  simpa [Function.comp] using hComp

def literalOccurrencePairStructuredEncodedType : EncodedType :=
  EncodedType.prod literalOccurrenceStructuredEncodedType literalOccurrenceStructuredEncodedType

def occurrenceClausePair (p : LiteralOccurrence × LiteralOccurrence) : Nat × Nat :=
  (p.1.clause, p.2.clause)

theorem occurrenceClausePair_tm_polytime :
    TMPolyTimeMap
      literalOccurrencePairStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      occurrenceClausePair := by
  have hLeftOcc :=
    TMPolyTimeMap.fst literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hRightOcc :=
    TMPolyTimeMap.snd literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hLeft :=
    TMPolyTimeMap.comp literalOccurrence_clause_tm_polytime hLeftOcc
  have hRight :=
    TMPolyTimeMap.comp literalOccurrence_clause_tm_polytime hRightOcc
  have hPair := TMPolyTimeMap.prod_mk hLeft hRight
  simpa [literalOccurrencePairStructuredEncodedType, occurrenceClausePair, Function.comp]
    using hPair

def occurrenceVarPair (p : LiteralOccurrence × LiteralOccurrence) : Nat × Nat :=
  (p.1.lit.var, p.2.lit.var)

end Clique
end Karp21
end ComplexityReduction
