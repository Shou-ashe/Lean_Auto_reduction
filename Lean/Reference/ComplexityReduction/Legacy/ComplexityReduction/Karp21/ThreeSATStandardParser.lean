/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability

/-!
Parser surface for the historical bundled 3SAT encoding.

The standard bundled encoding writes each literal as `(neg, var)`, with field
tags and delimiter runs.  The faithful structured CNF verifier consumes nested
list/product encodings where each literal is `(var, neg)`.  This file fixes the
finite-state parser's pure string semantics before the direct TM2 witness is
attached.
-/

namespace ComplexityReduction
namespace SAT

open ComplexityReduction.Karp21

namespace StandardThreeSATParser

abbrev StdSym : Type := ThreeSATSymbol
abbrev OutSym : Type := Option Karp21.clauseStructuredEncodedType.Symbol

def clauseDelimiter : OutSym :=
  none

def literalDelimiter : OutSym :=
  some none

def literalFieldDelimiter : OutSym :=
  some (some none)

def literalNatBit (b : Bool) : OutSym :=
  some (some (some (Sum.inl b)))

def literalNegBit (b : Bool) : OutSym :=
  some (some (some (Sum.inr b)))

def isNegTag : StdSym → Bool
  | some (Sum.inl false) => true
  | _ => false

def isVarTag : StdSym → Bool
  | some (Sum.inl true) => true
  | _ => false

def bit? : StdSym → Option Bool
  | some (Sum.inr b) => some b
  | _ => none

def literalStructuredSymbols (l : Literal) : List OutSym :=
  (EncodedType.nat.encode l.var).map literalNatBit ++
    [literalFieldDelimiter, literalNegBit l.neg, literalDelimiter]

def clauseStructuredSymbols (c : Clause) : List OutSym :=
  c.flatMap literalStructuredSymbols ++ [clauseDelimiter]

def cnfStructuredSymbols (cnf : CNF) : List OutSym :=
  cnf.flatMap clauseStructuredSymbols

inductive State where
  | leading0
  | leading1
  | leading2Plus
  | needNegBit
  | needVarDelimiter (neg : Bool)
  | needVarTag (neg : Bool)
  | inVar (neg : Bool)
  | afterLiteralOne
  | afterLiteralMany
  deriving DecidableEq, Fintype

def closeLiteral (neg : Bool) : List OutSym :=
  [literalFieldDelimiter, literalNegBit neg, literalDelimiter]

def startLiteralState : State :=
  State.needNegBit

def leadingStep (st : State) (a : StdSym) : State × List OutSym :=
  match a with
  | none =>
      match st with
      | State.leading0 => (State.leading1, [])
      | State.leading1 => (State.leading2Plus, [])
      | _ => (State.leading2Plus, [clauseDelimiter])
  | some (Sum.inl false) => (startLiteralState, [])
  | _ => (st, [])

def afterLiteralStep (st : State) (a : StdSym) : State × List OutSym :=
  match a with
  | none =>
      match st with
      | State.afterLiteralOne => (State.afterLiteralMany, [clauseDelimiter])
      | _ => (State.afterLiteralMany, [clauseDelimiter])
  | some (Sum.inl false) => (startLiteralState, [])
  | _ => (st, [])

def step : State → StdSym → State × List OutSym
  | State.leading0, a => leadingStep State.leading0 a
  | State.leading1, a => leadingStep State.leading1 a
  | State.leading2Plus, a => leadingStep State.leading2Plus a
  | State.needNegBit, a =>
      match bit? a with
      | some neg => (State.needVarDelimiter neg, [])
      | none => (State.needNegBit, [])
  | State.needVarDelimiter neg, a =>
      match a with
      | none => (State.needVarTag neg, [])
      | _ => (State.needVarDelimiter neg, [])
  | State.needVarTag neg, a =>
      if isVarTag a then (State.inVar neg, []) else (State.needVarTag neg, [])
  | State.inVar neg, a =>
      match bit? a with
      | some b => (State.inVar neg, [literalNatBit b])
      | none => (State.afterLiteralOne, closeLiteral neg)
  | State.afterLiteralOne, a => afterLiteralStep State.afterLiteralOne a
  | State.afterLiteralMany, a => afterLiteralStep State.afterLiteralMany a

def finish : State → List OutSym
  | State.leading0 => []
  | State.leading1 => [clauseDelimiter]
  | State.leading2Plus => [clauseDelimiter, clauseDelimiter]
  | State.needNegBit => []
  | State.needVarDelimiter _ => []
  | State.needVarTag _ => []
  | State.inVar neg => closeLiteral neg ++ [clauseDelimiter]
  | State.afterLiteralOne => [clauseDelimiter, clauseDelimiter]
  | State.afterLiteralMany => [clauseDelimiter, clauseDelimiter]

def runAux : State → List StdSym → List OutSym
  | st, [] => finish st
  | st, a :: rest =>
      let next := step st a
      next.2 ++ runAux next.1 rest

def run (input : List StdSym) : List OutSym :=
  runAux State.leading0 input

def parseThreeCNFEncoding (φ : ThreeCNF) : List OutSym :=
  run (ThreeSATEncoding.encodeThreeCNF φ)

theorem closeLiteral_length (neg : Bool) :
    (closeLiteral neg).length = 3 := by
  simp [closeLiteral]

theorem leadingStep_emit_length_le (st : State) (a : StdSym) :
    (leadingStep st a).2.length ≤ 1 := by
  unfold leadingStep
  repeat split <;> simp [clauseDelimiter]

theorem afterLiteralStep_emit_length_le (st : State) (a : StdSym) :
    (afterLiteralStep st a).2.length ≤ 1 := by
  unfold afterLiteralStep
  repeat split <;> simp [clauseDelimiter]

theorem step_emit_length_le (st : State) (a : StdSym) :
    (step st a).2.length ≤ 3 := by
  cases st with
  | leading0 =>
      exact Nat.le_trans (leadingStep_emit_length_le State.leading0 a) (by decide)
  | leading1 =>
      exact Nat.le_trans (leadingStep_emit_length_le State.leading1 a) (by decide)
  | leading2Plus =>
      exact Nat.le_trans (leadingStep_emit_length_le State.leading2Plus a) (by decide)
  | needNegBit =>
      cases a with
      | none => simp [step, bit?]
      | some side =>
          cases side with
          | inl b => cases b <;> simp [step, bit?]
          | inr b => cases b <;> simp [step, bit?]
  | needVarDelimiter neg =>
      cases a <;> simp [step]
  | needVarTag neg =>
      cases a with
      | none => simp [step, isVarTag]
      | some side =>
          cases side with
          | inl b => cases b <;> simp [step, isVarTag]
          | inr b => cases b <;> simp [step, isVarTag]
  | inVar neg =>
      cases a with
      | none => simp [step, bit?, closeLiteral]
      | some side =>
          cases side with
          | inl b => cases b <;> simp [step, bit?, closeLiteral]
          | inr b => cases b <;> simp [step, bit?]
  | afterLiteralOne =>
      exact Nat.le_trans (afterLiteralStep_emit_length_le State.afterLiteralOne a) (by decide)
  | afterLiteralMany =>
      exact Nat.le_trans (afterLiteralStep_emit_length_le State.afterLiteralMany a) (by decide)

theorem finish_length_le (st : State) :
    (finish st).length ≤ 4 := by
  cases st <;> simp [finish, closeLiteral, clauseDelimiter]

theorem runAux_length_le (st : State) (input : List StdSym) :
    (runAux st input).length ≤ 3 * input.length + 4 := by
  induction input generalizing st with
  | nil =>
      simpa [runAux] using finish_length_le st
  | cons a rest ih =>
      have hStep := step_emit_length_le st a
      have hTail := ih (step st a).1
      simp [runAux]
      omega

theorem run_length_le (input : List StdSym) :
    (run input).length ≤ 3 * input.length + 4 := by
  simpa [run] using runAux_length_le State.leading0 input

theorem literalStructuredSymbols_eq_literal_encode (l : Literal) :
    literalStructuredSymbols l =
      (EncodedType.nat.encode l.var).map literalNatBit ++
        [literalFieldDelimiter, literalNegBit l.neg, literalDelimiter] :=
  rfl

theorem clauseStructuredSymbols_eq_flatMap (c : Clause) :
    clauseStructuredSymbols c = c.flatMap literalStructuredSymbols ++ [clauseDelimiter] :=
  rfl

theorem cnfStructuredSymbols_eq_flatMap (cnf : CNF) :
    cnfStructuredSymbols cnf = cnf.flatMap clauseStructuredSymbols :=
  rfl

theorem append_singleton_middle {α : Type} (xs ys : List α) (a : α) :
    xs ++ [a] ++ ys = xs ++ a :: ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp [ih]

theorem append_singleton_middle_append {α : Type} (xs ys zs : List α) (a : α) :
    xs ++ [a] ++ (ys ++ zs) = xs ++ (a :: ys) ++ zs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp [ih]

theorem literalStructuredSymbols_eq_encode (l : Literal) :
    literalStructuredSymbols l =
      (Karp21.literalStructuredEncodedType.encode l).map
          (fun s => (some (some s) : OutSym)) ++
        [literalDelimiter] := by
  cases l with
  | mk var neg =>
      cases neg <;>
        simp [literalStructuredSymbols, Karp21.literalStructuredEncodedType,
          Karp21.literalTupleStructuredEncodedType, EncodedType.prod, EncodedType.nat,
          EncodedType.bool, literalNatBit, literalFieldDelimiter, literalNegBit,
          literalDelimiter, List.map_append]

theorem clauseStructuredSymbols_eq_encode (c : Clause) :
    clauseStructuredSymbols c =
      (Karp21.clauseStructuredEncodedType.encode c).map (fun s => (some s : OutSym)) ++
        [clauseDelimiter] := by
  induction c with
  | nil =>
      rfl
  | cons l rest ih =>
      calc
        clauseStructuredSymbols (l :: rest) =
            literalStructuredSymbols l ++
              (rest.flatMap literalStructuredSymbols ++ [clauseDelimiter]) := by
          simp [clauseStructuredSymbols, List.append_assoc]
        _ =
            literalStructuredSymbols l ++
              ((Karp21.clauseStructuredEncodedType.encode rest).map
                  (fun s => (some s : OutSym)) ++ [clauseDelimiter]) := by
          simpa [clauseStructuredSymbols] using
            congrArg (fun xs => literalStructuredSymbols l ++ xs) ih
        _ =
            (Karp21.clauseStructuredEncodedType.encode (l :: rest)).map
                (fun s => (some s : OutSym)) ++ [clauseDelimiter] := by
          simpa [Karp21.clauseStructuredEncodedType, EncodedType.list,
            literalStructuredSymbols_eq_encode, Function.comp_def, literalDelimiter,
            List.map_append, List.append_assoc] using
            append_singleton_middle_append
              ((Karp21.literalStructuredEncodedType.encode l).map
                (fun s => (some (some s) : OutSym)))
              ((Karp21.clauseStructuredEncodedType.encode rest).map
                (fun s => (some s : OutSym)))
              [clauseDelimiter]
              literalDelimiter

theorem cnfStructuredSymbols_eq_encode (cnf : CNF) :
    cnfStructuredSymbols cnf = Karp21.cnfStructuredEncodedType.encode cnf := by
  induction cnf with
  | nil =>
      rfl
  | cons c rest ih =>
      calc
        cnfStructuredSymbols (c :: rest) =
            clauseStructuredSymbols c ++ cnfStructuredSymbols rest := by
          rfl
        _ =
            List.append
              (((Karp21.clauseStructuredEncodedType.encode c).map
                (fun s => (some s : OutSym)) ++ [clauseDelimiter]) : List OutSym)
              (Karp21.cnfStructuredEncodedType.encode rest : List OutSym) := by
          rw [clauseStructuredSymbols_eq_encode c, ih]
          simp [List.append_assoc]
        _ = Karp21.cnfStructuredEncodedType.encode (c :: rest) := by
          simp [Karp21.cnfStructuredEncodedType, EncodedType.list, clauseDelimiter,
            List.append_assoc]

theorem runAux_inVar_bitTokens_append (neg : Bool) (bits : List Bool)
    (tail : List StdSym) :
    runAux (State.inVar neg) (bits.map ThreeSATEncoding.bitToken ++ tail) =
      bits.map literalNatBit ++ runAux (State.inVar neg) tail := by
  induction bits with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;> simp [runAux, step, bit?, ThreeSATEncoding.bitToken, ih]

theorem runAux_needNegBit_literal_body_nil (l : Literal) :
    runAux State.needNegBit
        (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
          ThreeSATEncoding.tagToken true :: ThreeSATEncoding.encodeNat l.var) =
      literalStructuredSymbols l ++ [clauseDelimiter] := by
  cases l with
  | mk var neg =>
      simpa [runAux, step, finish, bit?, isVarTag, ThreeSATEncoding.bitToken,
        ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken, ThreeSATEncoding.encodeNat,
        literalStructuredSymbols, closeLiteral, clauseDelimiter, List.append_assoc] using
        runAux_inVar_bitTokens_append neg (EncodedType.nat.encode var) ([] : List StdSym)

theorem runAux_needNegBit_literal_body_delim (l : Literal) (tail : List StdSym) :
    runAux State.needNegBit
        (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
          ThreeSATEncoding.tagToken true ::
          (ThreeSATEncoding.encodeNat l.var ++ ThreeSATEncoding.delimiter :: tail)) =
      literalStructuredSymbols l ++ runAux State.afterLiteralOne tail := by
  cases l with
  | mk var neg =>
      simpa [runAux, step, bit?, isVarTag, ThreeSATEncoding.bitToken,
        ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken, ThreeSATEncoding.encodeNat,
        literalStructuredSymbols, closeLiteral, literalDelimiter, List.append_assoc] using
        runAux_inVar_bitTokens_append neg (EncodedType.nat.encode var)
          (ThreeSATEncoding.delimiter :: tail)

theorem runAux_afterLiteralMany_eq_leading2Plus (input : List StdSym) :
    runAux State.afterLiteralMany input = runAux State.leading2Plus input := by
  induction input with
  | nil =>
      rfl
  | cons a rest ih =>
      cases a with
      | none =>
          simp [runAux, step, leadingStep, afterLiteralStep, ih]
      | some side =>
          cases side with
          | inl b =>
              cases b <;> simp [runAux, step, leadingStep, afterLiteralStep, ih]
          | inr b =>
              cases b <;> simp [runAux, step, leadingStep, afterLiteralStep, ih]

theorem runAux_leading2Plus_clauseStream_eq_clause_cons_leading1
    (c : Clause) (rest : CNF) :
    runAux State.leading2Plus
        (c.flatMap ThreeSATEncoding.encodeLiteral ++ rest.flatMap ThreeSATEncoding.encodeClause) =
      clauseDelimiter ::
        runAux State.leading1
          (c.flatMap ThreeSATEncoding.encodeLiteral ++
            rest.flatMap ThreeSATEncoding.encodeClause) := by
  cases c with
  | nil =>
      cases rest with
      | nil =>
          simp [runAux, finish, clauseDelimiter]
      | cons c rest =>
          simp [runAux, step, leadingStep, ThreeSATEncoding.encodeClause,
            ThreeSATEncoding.delimiter, clauseDelimiter]
  | cons l ls =>
      simp [runAux, step, leadingStep, ThreeSATEncoding.encodeLiteral,
        ThreeSATEncoding.delimiter, clauseDelimiter, List.append_assoc]

theorem runAux_afterLiteralOne_clauseStream_eq_clause_cons_leading1
    (c : Clause) (rest : CNF) :
    runAux State.afterLiteralOne
        (c.flatMap ThreeSATEncoding.encodeLiteral ++ rest.flatMap ThreeSATEncoding.encodeClause) =
      clauseDelimiter ::
        runAux State.leading1
          (c.flatMap ThreeSATEncoding.encodeLiteral ++
            rest.flatMap ThreeSATEncoding.encodeClause) := by
  cases c with
  | nil =>
      cases rest with
      | nil =>
          simp [runAux, finish, clauseDelimiter]
      | cons c rest =>
          calc
            runAux State.afterLiteralOne
                (ThreeSATEncoding.encodeClause c ++ rest.flatMap ThreeSATEncoding.encodeClause) =
              clauseDelimiter ::
                runAux State.afterLiteralMany
                  (c.flatMap ThreeSATEncoding.encodeLiteral ++
                    rest.flatMap ThreeSATEncoding.encodeClause) := by
              simp [runAux, step, afterLiteralStep, ThreeSATEncoding.encodeClause,
                ThreeSATEncoding.delimiter, clauseDelimiter]
            _ =
              clauseDelimiter ::
                runAux State.leading2Plus
                  (c.flatMap ThreeSATEncoding.encodeLiteral ++
                    rest.flatMap ThreeSATEncoding.encodeClause) := by
              rw [runAux_afterLiteralMany_eq_leading2Plus]
            _ =
              clauseDelimiter ::
                runAux State.leading1
                  (ThreeSATEncoding.encodeClause c ++
                    rest.flatMap ThreeSATEncoding.encodeClause) := by
              simp [runAux, step, leadingStep, ThreeSATEncoding.encodeClause,
                ThreeSATEncoding.delimiter, clauseDelimiter]
  | cons l ls =>
      calc
        runAux State.afterLiteralOne
            ((l :: ls).flatMap ThreeSATEncoding.encodeLiteral ++
              rest.flatMap ThreeSATEncoding.encodeClause) =
          clauseDelimiter ::
            runAux State.afterLiteralMany
              (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l.neg ::
                ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                (ThreeSATEncoding.encodeNat l.var ++
                  (ls.flatMap ThreeSATEncoding.encodeLiteral ++
                    rest.flatMap ThreeSATEncoding.encodeClause))) := by
          simp [runAux, step, afterLiteralStep, ThreeSATEncoding.encodeLiteral,
            ThreeSATEncoding.delimiter, clauseDelimiter, List.append_assoc]
        _ =
          clauseDelimiter ::
            runAux State.leading2Plus
              (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l.neg ::
                ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                (ThreeSATEncoding.encodeNat l.var ++
                  (ls.flatMap ThreeSATEncoding.encodeLiteral ++
                    rest.flatMap ThreeSATEncoding.encodeClause))) := by
          rw [runAux_afterLiteralMany_eq_leading2Plus]
        _ =
          clauseDelimiter ::
            runAux State.leading1
              ((l :: ls).flatMap ThreeSATEncoding.encodeLiteral ++
                rest.flatMap ThreeSATEncoding.encodeClause) := by
          simp [runAux, step, leadingStep, ThreeSATEncoding.encodeLiteral,
            ThreeSATEncoding.delimiter, clauseDelimiter, List.append_assoc]

theorem runAux_needNegBit_literalList_noRest (l : Literal) (ls : List Literal) :
    runAux State.needNegBit
        (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
          ThreeSATEncoding.tagToken true ::
          (ThreeSATEncoding.encodeNat l.var ++ ls.flatMap ThreeSATEncoding.encodeLiteral)) =
      literalStructuredSymbols l ++ ls.flatMap literalStructuredSymbols ++ [clauseDelimiter] := by
  induction ls generalizing l with
  | nil =>
      simpa [List.append_assoc] using runAux_needNegBit_literal_body_nil l
  | cons l₂ rest ih =>
      calc
        runAux State.needNegBit
            (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
              ThreeSATEncoding.tagToken true ::
              (ThreeSATEncoding.encodeNat l.var ++
                (l₂ :: rest).flatMap ThreeSATEncoding.encodeLiteral)) =
          literalStructuredSymbols l ++
            runAux State.afterLiteralOne
              (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l₂.neg ::
                ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                (ThreeSATEncoding.encodeNat l₂.var ++
                  rest.flatMap ThreeSATEncoding.encodeLiteral)) := by
          simpa [ThreeSATEncoding.encodeLiteral, ThreeSATEncoding.delimiter,
            List.append_assoc] using
            runAux_needNegBit_literal_body_delim l
              (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l₂.neg ::
                ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                (ThreeSATEncoding.encodeNat l₂.var ++
                  rest.flatMap ThreeSATEncoding.encodeLiteral))
        _ =
          literalStructuredSymbols l ++
            runAux State.needNegBit
              (ThreeSATEncoding.bitToken l₂.neg :: ThreeSATEncoding.delimiter ::
                ThreeSATEncoding.tagToken true ::
                (ThreeSATEncoding.encodeNat l₂.var ++
                  rest.flatMap ThreeSATEncoding.encodeLiteral)) := by
          simp [runAux, step, afterLiteralStep, ThreeSATEncoding.tagToken,
            startLiteralState]
        _ =
          literalStructuredSymbols l ++
            (literalStructuredSymbols l₂ ++
              rest.flatMap literalStructuredSymbols ++ [clauseDelimiter]) := by
          rw [ih l₂]
        _ =
          literalStructuredSymbols l ++
            (l₂ :: rest).flatMap literalStructuredSymbols ++ [clauseDelimiter] := by
          simp [List.append_assoc]

theorem runAux_leading1_clauseStream (c : Clause) (rest : CNF) :
    runAux State.leading1
        (c.flatMap ThreeSATEncoding.encodeLiteral ++ rest.flatMap ThreeSATEncoding.encodeClause) =
      clauseStructuredSymbols c ++ cnfStructuredSymbols rest := by
  induction rest generalizing c with
  | nil =>
      cases c with
      | nil =>
          simp [runAux, finish, clauseStructuredSymbols, cnfStructuredSymbols, clauseDelimiter]
      | cons l ls =>
          simpa [runAux, step, leadingStep, ThreeSATEncoding.encodeLiteral,
            ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken, startLiteralState,
            clauseStructuredSymbols, cnfStructuredSymbols, List.append_assoc] using
            runAux_needNegBit_literalList_noRest l ls
  | cons cNext restTail ih =>
      have parseWithRest :
          ∀ (l : Literal) (ls : List Literal),
            runAux State.needNegBit
                (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
                  ThreeSATEncoding.tagToken true ::
                  (ThreeSATEncoding.encodeNat l.var ++
                    (ls.flatMap ThreeSATEncoding.encodeLiteral ++
                      (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause))) =
              literalStructuredSymbols l ++ ls.flatMap literalStructuredSymbols ++
                [clauseDelimiter] ++ cnfStructuredSymbols (cNext :: restTail) := by
        intro l ls
        induction ls generalizing l with
        | nil =>
            calc
              runAux State.needNegBit
                  (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
                    ThreeSATEncoding.tagToken true ::
                    (ThreeSATEncoding.encodeNat l.var ++
                      ([] ++ (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause))) =
                literalStructuredSymbols l ++
                  runAux State.afterLiteralOne
                    (cNext.flatMap ThreeSATEncoding.encodeLiteral ++
                      restTail.flatMap ThreeSATEncoding.encodeClause) := by
                simpa [ThreeSATEncoding.encodeClause, ThreeSATEncoding.delimiter,
                  List.append_assoc] using
                  runAux_needNegBit_literal_body_delim l
                    (cNext.flatMap ThreeSATEncoding.encodeLiteral ++
                      restTail.flatMap ThreeSATEncoding.encodeClause)
              _ =
                literalStructuredSymbols l ++
                  (clauseDelimiter ::
                    runAux State.leading1
                      (cNext.flatMap ThreeSATEncoding.encodeLiteral ++
                        restTail.flatMap ThreeSATEncoding.encodeClause)) := by
                rw [runAux_afterLiteralOne_clauseStream_eq_clause_cons_leading1]
              _ =
                literalStructuredSymbols l ++
                  (clauseDelimiter ::
                    (clauseStructuredSymbols cNext ++ cnfStructuredSymbols restTail)) := by
                rw [ih cNext]
              _ =
                literalStructuredSymbols l ++ [] ++ [clauseDelimiter] ++
                  cnfStructuredSymbols (cNext :: restTail) := by
                simp [cnfStructuredSymbols, List.append_assoc]
        | cons l₂ rest ihLits =>
            calc
              runAux State.needNegBit
                  (ThreeSATEncoding.bitToken l.neg :: ThreeSATEncoding.delimiter ::
                    ThreeSATEncoding.tagToken true ::
                    (ThreeSATEncoding.encodeNat l.var ++
                      ((l₂ :: rest).flatMap ThreeSATEncoding.encodeLiteral ++
                        (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause))) =
                literalStructuredSymbols l ++
                  runAux State.afterLiteralOne
                    (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l₂.neg ::
                      ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                      (ThreeSATEncoding.encodeNat l₂.var ++
                        (rest.flatMap ThreeSATEncoding.encodeLiteral ++
                          (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause))) := by
                simpa [ThreeSATEncoding.encodeLiteral, ThreeSATEncoding.delimiter,
                  List.append_assoc] using
                  runAux_needNegBit_literal_body_delim l
                    (ThreeSATEncoding.tagToken false :: ThreeSATEncoding.bitToken l₂.neg ::
                      ThreeSATEncoding.delimiter :: ThreeSATEncoding.tagToken true ::
                      (ThreeSATEncoding.encodeNat l₂.var ++
                        (rest.flatMap ThreeSATEncoding.encodeLiteral ++
                          (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause)))
              _ =
                literalStructuredSymbols l ++
                  runAux State.needNegBit
                    (ThreeSATEncoding.bitToken l₂.neg :: ThreeSATEncoding.delimiter ::
                      ThreeSATEncoding.tagToken true ::
                      (ThreeSATEncoding.encodeNat l₂.var ++
                        (rest.flatMap ThreeSATEncoding.encodeLiteral ++
                          (cNext :: restTail).flatMap ThreeSATEncoding.encodeClause))) := by
                simp [runAux, step, afterLiteralStep, ThreeSATEncoding.tagToken,
                  startLiteralState]
              _ =
                literalStructuredSymbols l ++
                  (literalStructuredSymbols l₂ ++ rest.flatMap literalStructuredSymbols ++
                    [clauseDelimiter] ++ cnfStructuredSymbols (cNext :: restTail)) := by
                rw [ihLits l₂]
              _ =
                literalStructuredSymbols l ++
                  (l₂ :: rest).flatMap literalStructuredSymbols ++ [clauseDelimiter] ++
                    cnfStructuredSymbols (cNext :: restTail) := by
                simp [List.append_assoc]
      cases c with
      | nil =>
          calc
            runAux State.leading1
                ((cNext :: restTail).flatMap ThreeSATEncoding.encodeClause) =
              runAux State.leading2Plus
                (cNext.flatMap ThreeSATEncoding.encodeLiteral ++
                  restTail.flatMap ThreeSATEncoding.encodeClause) := by
              simp [runAux, step, leadingStep, ThreeSATEncoding.encodeClause,
                ThreeSATEncoding.delimiter]
            _ =
              clauseDelimiter ::
                runAux State.leading1
                  (cNext.flatMap ThreeSATEncoding.encodeLiteral ++
                    restTail.flatMap ThreeSATEncoding.encodeClause) := by
              rw [runAux_leading2Plus_clauseStream_eq_clause_cons_leading1]
            _ =
              clauseDelimiter ::
                (clauseStructuredSymbols cNext ++ cnfStructuredSymbols restTail) := by
              rw [ih cNext]
            _ = clauseStructuredSymbols [] ++ cnfStructuredSymbols (cNext :: restTail) := by
              simp [clauseStructuredSymbols, cnfStructuredSymbols, clauseDelimiter,
                List.append_assoc]
      | cons l ls =>
          simpa [runAux, step, leadingStep, ThreeSATEncoding.encodeLiteral,
            ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken, startLiteralState,
            clauseStructuredSymbols, cnfStructuredSymbols, List.append_assoc] using
            parseWithRest l ls

theorem runAux_leading0_formula (cnf : CNF) :
    runAux State.leading0 (cnf.flatMap ThreeSATEncoding.encodeClause) =
      cnfStructuredSymbols cnf := by
  induction cnf with
  | nil =>
      simp [runAux, finish, cnfStructuredSymbols]
  | cons c rest =>
      simpa [runAux, step, leadingStep, ThreeSATEncoding.encodeClause,
        ThreeSATEncoding.delimiter, cnfStructuredSymbols, List.append_assoc] using
        runAux_leading1_clauseStream c rest

theorem run_encodeThreeCNF_eq_cnfStructuredSymbols (φ : ThreeCNF) :
    parseThreeCNFEncoding φ = cnfStructuredSymbols φ.clauses := by
  simpa [parseThreeCNFEncoding, run, ThreeSATEncoding.encodeThreeCNF] using
    runAux_leading0_formula φ.clauses

theorem run_encodeThreeCNF_eq_cnfStructured_encode (φ : ThreeCNF) :
    parseThreeCNFEncoding φ = Karp21.cnfStructuredEncodedType.encode φ.clauses := by
  rw [run_encodeThreeCNF_eq_cnfStructuredSymbols, cnfStructuredSymbols_eq_encode]

end StandardThreeSATParser

end SAT
end ComplexityReduction
