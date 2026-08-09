/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

theorem literalStructured_inputSize_eq (l : SAT.Literal) :
    literalStructuredEncodedType.inputSize l = l.var + 3 := by
  cases l
  simp [literalStructuredEncodedType, literalTupleStructuredEncodedType, EncodedType.inputSize,
    EncodedType.prod, EncodedType.nat, EncodedType.bool]

@[simp] theorem literalStructured_list_inputSize_cons
    (l : SAT.Literal) (rest : SAT.Clause) :
    (EncodedType.list literalStructuredEncodedType).inputSize (l :: rest) =
      l.var + 4 + (EncodedType.list literalStructuredEncodedType).inputSize rest := by
  simp [EncodedType.inputSize_list_cons, literalStructured_inputSize_eq]

/-- Structured input `(next, clause)` for the clause-level splitter. -/
def splitWithInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clauseStructuredEncodedType

def splitWithNextAfterClause (p : splitWithInputEncodedType.Carrier) : Nat := by
  rcases p with ⟨next, c⟩
  change Nat at next
  exact next + c.length

/-- Keep the unary payload for `next + clause.length` from a splitter input. -/
def splitWithNextAfterClausePayloadKeep :
    splitWithInputEncodedType.Symbol → Option Bool
  | some (Sum.inl true) => some true
  | some (Sum.inl false) => none
  | some (Sum.inr none) => some true
  | _ => none

theorem splitWithNextAfterClausePayloadKeep_literalPayload (l : SAT.Literal) :
    ((literalStructuredEncodedType.encode l).map
        (fun s => (some (Sum.inr (some s)) : splitWithInputEncodedType.Symbol))).filterMap
        splitWithNextAfterClausePayloadKeep = [] := by
  induction literalStructuredEncodedType.encode l with
  | nil =>
      rfl
  | cons head rest ih =>
      simpa only [List.map_cons, List.filterMap_cons,
        splitWithNextAfterClausePayloadKeep] using ih

theorem splitWithNextAfterClausePayloadKeep_clausePayload (c : SAT.Clause) :
    ((clauseStructuredEncodedType.encode c).map
        (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))).filterMap
        splitWithNextAfterClausePayloadKeep =
      List.replicate c.length true := by
  induction c with
  | nil =>
      rfl
  | cons l rest ih =>
      let wrap : clauseStructuredEncodedType.Symbol → splitWithInputEncodedType.Symbol :=
        fun s => some (Sum.inr s)
      change
        List.filterMap splitWithNextAfterClausePayloadKeep
            (List.map wrap
              (((literalStructuredEncodedType.encode l).map some ++ [none]) ++
                List.flatMap
                  (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                  rest)) =
          true :: List.replicate rest.length true
      have hRest' :
          List.filterMap (fun s => splitWithNextAfterClausePayloadKeep (wrap s))
                (List.flatMap
                  (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                  rest) =
            List.replicate rest.length true := by
        have hRestMap :
            List.filterMap splitWithNextAfterClausePayloadKeep
                (List.map wrap
                  (List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest)) =
              List.replicate rest.length true := by
          simpa only [wrap, clauseStructuredEncodedType, EncodedType.list] using ih
        exact
          (List.filterMap_map
            (f := wrap)
            (g := splitWithNextAfterClausePayloadKeep)
            (l := List.flatMap
              (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
              rest)).symm.trans hRestMap
      rw [List.filterMap_map (f := wrap) (g := splitWithNextAfterClausePayloadKeep)]
      change
        List.filterMap (splitWithNextAfterClausePayloadKeep ∘ wrap)
            ((literalStructuredEncodedType.encode l).map some ++ [none] ++
              List.flatMap
                (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                rest) =
          true :: List.replicate rest.length true
      have hRestComp :
          List.filterMap (splitWithNextAfterClausePayloadKeep ∘ wrap)
              (List.flatMap
                (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                rest) =
            List.replicate rest.length true := by
        simpa [Function.comp_def] using hRest'
      induction literalStructuredEncodedType.encode l with
      | nil =>
          change
            true ::
                List.filterMap (splitWithNextAfterClausePayloadKeep ∘ wrap)
                  (List.flatMap
                    (fun x => (literalStructuredEncodedType.encode x).map some ++ [none])
                    rest) =
              true :: List.replicate rest.length true
          exact congrArg (fun xs => true :: xs) hRestComp
      | cons head tail ih =>
          simpa [wrap, splitWithNextAfterClausePayloadKeep, Function.comp_def] using ih

theorem splitWithNextAfterClausePayload_encode_filterMap
    (p : splitWithInputEncodedType.Carrier) :
    (splitWithInputEncodedType.encode p).filterMap splitWithNextAfterClausePayloadKeep =
      unaryPayloadEncodedType.encode (splitWithNextAfterClause p) := by
  rcases p with ⟨next, c⟩
  change Nat at next
  have hNat :
      ((EncodedType.nat.encode next).map
          (fun s => (some (Sum.inl s) : splitWithInputEncodedType.Symbol))).filterMap
          splitWithNextAfterClausePayloadKeep =
        List.replicate next true := by
    induction next with
    | zero =>
        change ([] : List Bool) = []
        rfl
    | succ next ih =>
        change
          true ::
              (((EncodedType.nat.encode next).map
                (fun s => (some (Sum.inl s) : splitWithInputEncodedType.Symbol))).filterMap
                splitWithNextAfterClausePayloadKeep) =
            true :: List.replicate next true
        exact congrArg (fun xs => true :: xs) ih
  have hClause := splitWithNextAfterClausePayloadKeep_clausePayload c
  have hNat' :
      (EncodedType.nat.encode next).filterMap
          (fun s => splitWithNextAfterClausePayloadKeep
            (some (Sum.inl s) : splitWithInputEncodedType.Symbol)) =
        List.replicate next true := by
    exact
      (List.filterMap_map
        (f := fun s => (some (Sum.inl s) : splitWithInputEncodedType.Symbol))
        (g := splitWithNextAfterClausePayloadKeep)
        (l := EncodedType.nat.encode next)).symm.trans hNat
  have hClause' :
      (clauseStructuredEncodedType.encode c).filterMap
          (fun s => splitWithNextAfterClausePayloadKeep
            (some (Sum.inr s) : splitWithInputEncodedType.Symbol)) =
        List.replicate c.length true := by
    exact
      (List.filterMap_map
        (f := fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))
        (g := splitWithNextAfterClausePayloadKeep)
        (l := clauseStructuredEncodedType.encode c)).symm.trans hClause
  simp only [splitWithInputEncodedType, EncodedType.prod, List.filterMap_append,
    List.filterMap_map, Function.comp, splitWithNextAfterClause, unaryPayloadEncodedType]
  rw [hNat', hClause']
  simp [splitWithNextAfterClausePayloadKeep]

/-- Direct TM-backed writer for the unterminated unary payload `next + clause.length`. -/
noncomputable def splitWithNextAfterClausePayloadTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      unaryPayloadEncodedType
      splitWithNextAfterClause where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := splitWithInputEncodedType)
      (Y := unaryPayloadEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        rw [EncodedType.inputSize, EncodedType.inputSize]
        rw [← splitWithNextAfterClausePayload_encode_filterMap p]
        simpa using
          List.length_filterMap_le splitWithNextAfterClausePayloadKeep
            (splitWithInputEncodedType.encode p)))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithInputEncodedType.Symbol
            Bool
            splitWithNextAfterClausePayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro p
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithInputEncodedType.Symbol
            Bool
            splitWithNextAfterClausePayloadKeep)
          (List.map id (splitWithInputEncodedType.encode p))
          (some (List.map id
            (unaryPayloadEncodedType.encode (splitWithNextAfterClause p))))
          ((4 * Polynomial.X + 2).eval
            (splitWithInputEncodedType.encode p).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithInputEncodedType.Symbol
            Bool
            splitWithNextAfterClausePayloadKeep
            (splitWithInputEncodedType.encode p)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithNextAfterClausePayload_encode_filterMap p).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

/-- Direct TM-backed writer for the exact next fresh index after one source clause. -/
noncomputable def splitWithNextAfterClauseTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      EncodedType.nat
      splitWithNextAfterClause where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := splitWithInputEncodedType)
      (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro p
        have hPayloadLen :=
          List.length_filterMap_le splitWithNextAfterClausePayloadKeep
            (splitWithInputEncodedType.encode p)
        rw [splitWithNextAfterClausePayload_encode_filterMap p] at hPayloadLen
        simp [unaryPayloadEncodedType, EncodedType.inputSize, EncodedType.nat] at hPayloadLen ⊢
        omega))
  tm_polytime := by
    have hComp :=
      TMPolyTimeMap.comp
        unaryPayloadToNatTMBackedMap.tm_polytime
        splitWithNextAfterClausePayloadTMBackedMap.tm_polytime
    simpa [Function.comp] using hComp

inductive SplitWithShortCount where
  | zero
  | one
  | two
  | three
  | fourOrMore
  deriving DecidableEq, Fintype

namespace SplitWithShortCount

def succ : SplitWithShortCount → SplitWithShortCount
  | zero => one
  | one => two
  | two => three
  | three => fourOrMore
  | fourOrMore => fourOrMore

def addNat : SplitWithShortCount → Nat → SplitWithShortCount
  | count, 0 => count
  | count, n + 1 => addNat count.succ n

def isShort : SplitWithShortCount → Bool
  | zero => true
  | one => true
  | two => true
  | three => true
  | fourOrMore => false

def stepSymbol (count : SplitWithShortCount) :
    splitWithInputEncodedType.Symbol → SplitWithShortCount
  | some (Sum.inr none) => count.succ
  | _ => count

def foldSymbols : SplitWithShortCount →
    List splitWithInputEncodedType.Symbol → SplitWithShortCount
  | count, [] => count
  | count, sym :: rest => foldSymbols (stepSymbol count sym) rest

theorem foldSymbols_append (count : SplitWithShortCount)
    (xs ys : List splitWithInputEncodedType.Symbol) :
    foldSymbols count (xs ++ ys) = foldSymbols (foldSymbols count xs) ys := by
  induction xs generalizing count with
  | nil =>
      rfl
  | cons sym xs ih =>
      simp [foldSymbols, ih]

theorem foldSymbols_ignore_natPrefix (count : SplitWithShortCount) (next : Nat) :
    foldSymbols count
        ((EncodedType.nat.encode next).map
          (fun s => (some (Sum.inl s) : splitWithInputEncodedType.Symbol))) =
      count := by
  induction EncodedType.nat.encode next generalizing count with
  | nil =>
      rfl
  | cons sym rest ih =>
      simp [foldSymbols, stepSymbol, ih]

theorem foldSymbols_ignore_literalPayload (count : SplitWithShortCount)
    (payload : List literalStructuredEncodedType.Symbol) :
    foldSymbols count
        (payload.map (fun s => (some (Sum.inr (some s)) : splitWithInputEncodedType.Symbol))) =
      count := by
  induction payload generalizing count with
  | nil =>
      rfl
  | cons sym rest ih =>
      simp [foldSymbols, stepSymbol, ih]

theorem foldSymbols_literalBlock (count : SplitWithShortCount) (lit : SAT.Literal) :
    foldSymbols count
        (((literalStructuredEncodedType.encode lit).map some ++ [none]).map
          (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))) =
      count.succ := by
  induction literalStructuredEncodedType.encode lit generalizing count with
  | nil =>
      rfl
  | cons sym rest ih =>
      change
        foldSymbols count
            (some (Sum.inr (some sym)) ::
              List.map (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))
                (List.map some rest ++ [none])) =
          count.succ
      simpa [foldSymbols, stepSymbol] using ih count

theorem foldSymbols_clauseBlockAppend (count : SplitWithShortCount)
    (payload : List literalStructuredEncodedType.Symbol)
    (restSymbols : List (Option literalStructuredEncodedType.Symbol)) :
    foldSymbols count
        ((((payload.map some ++ [none]) ++ restSymbols).map
          (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol)))) =
      foldSymbols count.succ
        (restSymbols.map (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))) := by
  induction payload generalizing count with
  | nil =>
      change
        foldSymbols count
            (some (Sum.inr (none : Option literalStructuredEncodedType.Symbol)) ::
              restSymbols.map
                (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))) =
          foldSymbols count.succ
            (restSymbols.map
              (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol)))
      rfl
  | cons sym payload ih =>
      change
        foldSymbols count
            (some (Sum.inr (some sym)) ::
              (((payload.map some ++ [none]) ++ restSymbols).map
                (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol)))) =
          foldSymbols count.succ
            (restSymbols.map
              (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol)))
      simpa [foldSymbols, stepSymbol] using ih count

theorem foldSymbols_clauseEncode (count : SplitWithShortCount) (c : SAT.Clause) :
    foldSymbols count
        ((clauseStructuredEncodedType.encode c).map
          (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))) =
      addNat count c.length := by
  change
    foldSymbols count
        ((List.flatMap
            (fun x : SAT.Literal => (literalStructuredEncodedType.encode x).map some ++ [none])
            c).map
          (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))) =
      addNat count c.length
  induction c generalizing count with
  | nil =>
      rfl
  | cons lit rest ih =>
      rw [List.flatMap_cons]
      change
        foldSymbols count
            ((((literalStructuredEncodedType.encode lit).map some ++ [none] ++
                List.flatMap
                  (fun x : SAT.Literal =>
                    (literalStructuredEncodedType.encode x).map some ++ [none])
                  rest).map
              (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol)))) =
          addNat count (lit :: rest).length
      rw [show (literalStructuredEncodedType.encode lit).map some ++ [none] ++
              List.flatMap
                (fun x : SAT.Literal =>
                  (literalStructuredEncodedType.encode x).map some ++ [none])
                rest =
            (((literalStructuredEncodedType.encode lit).map some ++ [none]) ++
              List.flatMap
                (fun x : SAT.Literal =>
                  (literalStructuredEncodedType.encode x).map some ++ [none])
                rest) by
        rw [List.append_assoc]]
      rw [foldSymbols_clauseBlockAppend]
      simpa [addNat] using ih count.succ

@[simp] theorem fourOrMore_addNat (n : Nat) :
    addNat fourOrMore n = fourOrMore := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [addNat, succ] using ih

theorem zero_addNat_isShort (n : Nat) :
    (addNat zero n).isShort = decide (n ≤ 3) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          cases n with
          | zero =>
              rfl
          | succ n =>
              cases n with
              | zero =>
                  rfl
              | succ n =>
                  have h : ¬ Nat.succ (Nat.succ (Nat.succ (Nat.succ n))) ≤ 3 := by
                    omega
                  simp [addNat, succ, isShort, h]

theorem foldSymbols_encodedInput_isShort
    (p : splitWithInputEncodedType.Carrier) :
    (foldSymbols zero (splitWithInputEncodedType.encode p)).isShort =
      decide (p.2.length ≤ 3) := by
  rcases p with ⟨next, c⟩
  let natPart : List splitWithInputEncodedType.Symbol :=
    (EncodedType.nat.encode next).map
      (fun s => (some (Sum.inl s) : splitWithInputEncodedType.Symbol))
  let clausePart : List splitWithInputEncodedType.Symbol :=
    (clauseStructuredEncodedType.encode c).map
      (fun s => (some (Sum.inr s) : splitWithInputEncodedType.Symbol))
  let productDelimiter : List splitWithInputEncodedType.Symbol :=
    [(none : splitWithInputEncodedType.Symbol)]
  change (foldSymbols zero ((natPart ++ productDelimiter) ++ clausePart)).isShort =
    decide (c.length ≤ 3)
  have hNat : foldSymbols zero natPart = zero := by
    simpa [natPart] using foldSymbols_ignore_natPrefix zero next
  have hPrefix : foldSymbols zero (natPart ++ productDelimiter) = zero := by
    calc
      foldSymbols zero (natPart ++ productDelimiter)
          = foldSymbols (foldSymbols zero natPart) productDelimiter :=
            foldSymbols_append zero natPart productDelimiter
      _ = foldSymbols zero productDelimiter := by rw [hNat]
      _ = zero := by simp [productDelimiter, foldSymbols, stepSymbol]
  have hInput : foldSymbols zero ((natPart ++ productDelimiter) ++ clausePart) =
      foldSymbols zero clausePart := by
    calc
      foldSymbols zero ((natPart ++ productDelimiter) ++ clausePart)
          = foldSymbols (foldSymbols zero (natPart ++ productDelimiter)) clausePart :=
            foldSymbols_append zero (natPart ++ productDelimiter) clausePart
      _ = foldSymbols zero clausePart := by rw [hPrefix]
  rw [hInput]
  have hClause : foldSymbols zero clausePart = addNat zero c.length := by
    simpa [clausePart] using foldSymbols_clauseEncode zero c
  calc
    (foldSymbols zero clausePart).isShort = (addNat zero c.length).isShort := by
      exact congrArg isShort hClause
    _ = decide (c.length ≤ 3) := zero_addNat_isShort c.length

end SplitWithShortCount

def splitWithIsShort (p : splitWithInputEncodedType.Carrier) : Bool :=
  decide (p.2.length ≤ 3)

inductive SplitWithShortBranchStack where
  | input
  | output
  deriving DecidableEq, Fintype

inductive SplitWithShortBranchLabel where
  | scan
  | write
  deriving DecidableEq, Fintype

inductive SplitWithShortBranchState where
  | scan (count : SplitWithShortCount)
  | write (isShort : Bool)
  deriving DecidableEq, Fintype

def splitWithShortBranchAlphabet : SplitWithShortBranchStack → Type
  | SplitWithShortBranchStack.input => splitWithInputEncodedType.Symbol
  | SplitWithShortBranchStack.output => Bool

instance (k : SplitWithShortBranchStack) : Fintype (splitWithShortBranchAlphabet k) := by
  cases k
  · exact inferInstanceAs (Fintype splitWithInputEncodedType.Symbol)
  · exact inferInstanceAs (Fintype Bool)

def splitWithShortBranchStateAfterPop :
    SplitWithShortBranchState →
      Option splitWithInputEncodedType.Symbol → SplitWithShortBranchState
  | SplitWithShortBranchState.scan count, none =>
      SplitWithShortBranchState.write count.isShort
  | SplitWithShortBranchState.scan count, some sym =>
      SplitWithShortBranchState.scan (count.stepSymbol sym)
  | state@(.write _), _ => state

def splitWithShortBranchNextLabel :
    SplitWithShortBranchState → SplitWithShortBranchLabel
  | .scan _ => .scan
  | .write _ => .write

def splitWithShortBranchOutput : SplitWithShortBranchState → Bool
  | .scan count => count.isShort
  | .write isShort => isShort

open Turing.TM2.Stmt in
def splitWithShortBranchMachine : Turing.FinTM2 where
  K := SplitWithShortBranchStack
  k₀ := .input
  k₁ := .output
  Γ := splitWithShortBranchAlphabet
  Λ := SplitWithShortBranchLabel
  main := .scan
  σ := SplitWithShortBranchState
  initialState := .scan .zero
  m
    | .scan =>
        pop .input splitWithShortBranchStateAfterPop
          (goto splitWithShortBranchNextLabel)
    | .write =>
        push .output splitWithShortBranchOutput
          (load (fun _ => SplitWithShortBranchState.scan .zero) halt)

def splitWithShortBranchCfg
    (label : Option SplitWithShortBranchLabel) (state : SplitWithShortBranchState)
    (input : List splitWithInputEncodedType.Symbol) (output : List Bool) :
    splitWithShortBranchMachine.Cfg where
  l := label
  var := state
  stk
    | .input => input
    | .output => output

lemma splitWithShortBranch_initList (input : List splitWithInputEncodedType.Symbol) :
    Turing.initList splitWithShortBranchMachine input =
      splitWithShortBranchCfg (some .scan) (.scan .zero) input [] := by
  simp [Turing.initList, splitWithShortBranchMachine, splitWithShortBranchCfg]
  congr
  funext k
  cases k <;> rfl

lemma splitWithShortBranch_haltList (output : List Bool) :
    Turing.haltList splitWithShortBranchMachine output =
      splitWithShortBranchCfg none (.scan .zero) [] output := by
  simp [Turing.haltList, splitWithShortBranchMachine, splitWithShortBranchCfg]
  congr
  funext k
  cases k <;> rfl

lemma splitWithShortBranch_scan_step_cons (count : SplitWithShortCount)
    (sym : splitWithInputEncodedType.Symbol) (input : List splitWithInputEncodedType.Symbol)
    (output : List Bool) :
    splitWithShortBranchMachine.step
        (splitWithShortBranchCfg (some .scan) (.scan count) (sym :: input) output) =
      some
        (splitWithShortBranchCfg (some .scan) (.scan (count.stepSymbol sym)) input output) := by
  simp [splitWithShortBranchMachine, splitWithShortBranchCfg,
    splitWithShortBranchStateAfterPop, splitWithShortBranchNextLabel]
  congr
  funext k
  cases k <;> rfl

lemma splitWithShortBranch_scan_step_nil (count : SplitWithShortCount) (output : List Bool) :
    splitWithShortBranchMachine.step
        (splitWithShortBranchCfg (some .scan) (.scan count) [] output) =
      some (splitWithShortBranchCfg (some .write) (.write count.isShort) [] output) := by
  simp [splitWithShortBranchMachine, splitWithShortBranchCfg,
    splitWithShortBranchStateAfterPop, splitWithShortBranchNextLabel]
  congr
  funext k
  cases k <;> rfl

lemma splitWithShortBranch_write_step (isShort : Bool) (output : List Bool) :
    splitWithShortBranchMachine.step
        (splitWithShortBranchCfg (some .write) (.write isShort) [] output) =
      some (splitWithShortBranchCfg none (.scan .zero) [] (isShort :: output)) := by
  simp [splitWithShortBranchMachine, splitWithShortBranchCfg, splitWithShortBranchOutput]
  congr
  funext k
  cases k <;> rfl

def splitWithShortBranch_scan_run (count : SplitWithShortCount)
    (input : List splitWithInputEncodedType.Symbol) :
    StateTransition.EvalsToInTime splitWithShortBranchMachine.step
      (splitWithShortBranchCfg (some .scan) (.scan count) input [])
      (some
        (splitWithShortBranchCfg (some .write)
          (.write (SplitWithShortCount.foldSymbols count input).isShort) [] []))
      (input.length + 1) := by
  induction input generalizing count with
  | nil =>
      simpa [SplitWithShortCount.foldSymbols] using
        TM2Programs.evalsToInTimeOne
          (splitWithShortBranch_scan_step_nil count [])
  | cons sym input ih =>
      let nextCount := count.stepSymbol sym
      let c₀ := splitWithShortBranchCfg (some .scan) (.scan count) (sym :: input) []
      let c₁ := splitWithShortBranchCfg (some .scan) (.scan nextCount) input []
      let done :=
        splitWithShortBranchCfg (some .write)
          (.write (SplitWithShortCount.foldSymbols nextCount input).isShort) [] []
      have h₁ : StateTransition.EvalsToInTime splitWithShortBranchMachine.step c₀ (some c₁) 1 :=
        TM2Programs.evalsToInTimeOne
          (splitWithShortBranch_scan_step_cons count sym input [])
      have hTail :
          StateTransition.EvalsToInTime splitWithShortBranchMachine.step c₁ (some done)
            (input.length + 1) := by
        simpa [c₁, done, nextCount] using ih nextCount
      have hAll :
          StateTransition.EvalsToInTime splitWithShortBranchMachine.step c₀ (some done)
            (input.length + 1 + 1) :=
        StateTransition.EvalsToInTime.trans splitWithShortBranchMachine.step
          1 (input.length + 1) c₀ c₁ (some done) h₁ hTail
      simpa [c₀, done, nextCount, SplitWithShortCount.foldSymbols, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def splitWithShortBranch_outputs (input : List splitWithInputEncodedType.Symbol) :
    Turing.TM2OutputsInTime splitWithShortBranchMachine input
      (some [(SplitWithShortCount.foldSymbols .zero input).isShort])
      (input.length + 2) := by
  let mid :=
    splitWithShortBranchCfg (some .write)
      (.write (SplitWithShortCount.foldSymbols .zero input).isShort) [] []
  let done :=
    splitWithShortBranchCfg none (.scan .zero) []
      [(SplitWithShortCount.foldSymbols .zero input).isShort]
  have hScan : StateTransition.EvalsToInTime splitWithShortBranchMachine.step
      (Turing.initList splitWithShortBranchMachine input) (some mid) (input.length + 1) := by
    simpa [mid, splitWithShortBranch_initList] using
      splitWithShortBranch_scan_run .zero input
  have hWrite :
      StateTransition.EvalsToInTime splitWithShortBranchMachine.step mid (some done) 1 := by
    simpa [mid, done] using
      TM2Programs.evalsToInTimeOne
        (splitWithShortBranch_write_step
          (SplitWithShortCount.foldSymbols .zero input).isShort [])
  have hAll :
      StateTransition.EvalsToInTime splitWithShortBranchMachine.step
        (Turing.initList splitWithShortBranchMachine input) (some done)
        (1 + (input.length + 1)) :=
    StateTransition.EvalsToInTime.trans splitWithShortBranchMachine.step
      (input.length + 1) 1 (Turing.initList splitWithShortBranchMachine input)
      mid (some done) hScan hWrite
  change StateTransition.EvalsToInTime splitWithShortBranchMachine.step
    (Turing.initList splitWithShortBranchMachine input)
    (some
      (Turing.haltList splitWithShortBranchMachine
        [(SplitWithShortCount.foldSymbols .zero input).isShort]))
    (input.length + 2)
  rw [splitWithShortBranch_haltList]
  convert hAll using 1
  omega

noncomputable def splitWithIsShortTMBackedMap :
    TMBackedCostedMap splitWithInputEncodedType EncodedType.bool splitWithIsShort where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithInputEncodedType)
      (Y := EncodedType.bool)
      (LinearSizeBound.intro_with 0 1 (by
        intro p
        simp [EncodedType.inputSize, EncodedType.bool]))
  tm_polytime :=
    ⟨{ tm := splitWithShortBranchMachine
       inputAlphabet := Equiv.refl splitWithInputEncodedType.Symbol
       outputAlphabet := Equiv.refl Bool
       time := Polynomial.X + 2
       outputsFun := by
        intro p
        change Turing.TM2OutputsInTime splitWithShortBranchMachine
          (List.map id (splitWithInputEncodedType.encode p))
          (some (List.map id (EncodedType.bool.encode (splitWithIsShort p))))
          ((Polynomial.X + 2).eval (splitWithInputEncodedType.encode p).length)
        simpa [splitWithIsShort, EncodedType.bool, Polynomial.eval_add, Polynomial.eval_X,
          SplitWithShortCount.foldSymbols_encodedInput_isShort, List.map_id] using
          splitWithShortBranch_outputs (splitWithInputEncodedType.encode p) }⟩

/-- Branch-decision package preserving the original splitter input. -/
def splitWithBranchDecisionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool splitWithInputEncodedType

/--
Compute the short/long branch bit while preserving the original splitter input
for the eventual branch runner.
-/
def splitWithBranchDecision
    (p : splitWithInputEncodedType.Carrier) :
    splitWithBranchDecisionEncodedType.Carrier :=
  (splitWithIsShort p, p)

theorem splitWithBranchDecision_inputSize_le
    (p : splitWithInputEncodedType.Carrier) :
    splitWithBranchDecisionEncodedType.inputSize (splitWithBranchDecision p) ≤
      splitWithInputEncodedType.inputSize p + 2 := by
  change
    splitWithBranchDecisionEncodedType.inputSize (splitWithIsShort p, p) ≤
      splitWithInputEncodedType.inputSize p + 2
  simp [splitWithBranchDecisionEncodedType, EncodedType.inputSize, EncodedType.bool,
    EncodedType.prod]

/--
The branch-decision package is direct TM-backed: it uses the checked
delimiter-scanning predicate and copies the source input for the later runner.
-/
noncomputable def splitWithBranchDecisionTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      splitWithBranchDecisionEncodedType
      splitWithBranchDecision where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithInputEncodedType)
      (Y := splitWithBranchDecisionEncodedType)
      (LinearSizeBound.intro_with 1 2 (by
        intro p
        have h := splitWithBranchDecision_inputSize_le p
        omega))
  tm_polytime := by
    have hPred :
        TMPolyTimeMap splitWithInputEncodedType EncodedType.bool splitWithIsShort :=
      splitWithIsShortTMBackedMap.tm_polytime
    have hInput :
        TMPolyTimeMap splitWithInputEncodedType splitWithInputEncodedType id :=
      TMPolyTimeMap.id splitWithInputEncodedType
    have hPair :
        TMPolyTimeMap
          splitWithInputEncodedType
          splitWithBranchDecisionEncodedType
          splitWithBranchDecision :=
      TMPolyTimeMap.prod_mk hPred hInput
    simpa [splitWithBranchDecision, splitWithBranchDecisionEncodedType] using hPair


end Karp21
end ComplexityReduction
