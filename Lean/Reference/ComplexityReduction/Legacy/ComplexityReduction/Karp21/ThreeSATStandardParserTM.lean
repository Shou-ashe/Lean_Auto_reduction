/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATStandardParser

/-!
Direct TM2 witness for the historical bundled 3SAT parser.

`ThreeSATStandardParser.lean` proves the parser's pure string semantics.  This
file attaches a concrete finite-state TM2 transducer to that parser and exposes
the standard bundled-3SAT clauses projection as a direct `TMPolyTimeMap`.
-/

namespace ComplexityReduction
namespace SAT
namespace StandardThreeSATParser

open Turing.TM2.Stmt

/-! ### Bounded output blocks for one parser transition -/

instance outSymDecidableEq : DecidableEq OutSym := by
  dsimp [OutSym, Karp21.clauseStructuredEncodedType, Karp21.literalStructuredEncodedType,
    Karp21.literalTupleStructuredEncodedType, EncodedType.list, EncodedType.prod,
    EncodedType.nat, EncodedType.bool]
  infer_instance

inductive Block where
  | nil
  | one (a : OutSym)
  | two (a b : OutSym)
  | three (a b c : OutSym)
  | four (a b c d : OutSym)
  deriving DecidableEq, Fintype

namespace Block

def symbols : Block → List OutSym
  | nil => []
  | one a => [a]
  | two a b => [a, b]
  | three a b c => [a, b, c]
  | four a b c d => [a, b, c, d]

def head? : Block → Option OutSym
  | nil => none
  | one a => some a
  | two a _ => some a
  | three a _ _ => some a
  | four a _ _ _ => some a

def headD : Block → OutSym
  | nil => clauseDelimiter
  | one a => a
  | two a _ => a
  | three a _ _ => a
  | four a _ _ _ => a

def tail : Block → Block
  | nil => nil
  | one _ => nil
  | two _ b => one b
  | three _ b c => two b c
  | four _ b c d => three b c d

theorem symbols_eq_nil_of_head?_none {b : Block} (h : b.head? = none) :
    b.symbols = [] := by
  cases b <;> simp [head?, symbols] at h ⊢

theorem symbols_eq_cons_of_head? {b : Block} {a : OutSym} (h : b.head? = some a) :
    b.symbols = a :: b.tail.symbols := by
  cases b <;> simp [head?, tail, symbols] at h ⊢ <;> exact h

theorem length_le_four (b : Block) :
    b.symbols.length ≤ 4 := by
  cases b <;> simp [symbols]

end Block

def closeBlock (neg : Bool) : Block :=
  Block.three literalFieldDelimiter (literalNegBit neg) literalDelimiter

def closeClauseBlock (neg : Bool) : Block :=
  Block.four literalFieldDelimiter (literalNegBit neg) literalDelimiter clauseDelimiter

def finishBlock : State → Block
  | State.leading0 => Block.nil
  | State.leading1 => Block.one clauseDelimiter
  | State.leading2Plus => Block.two clauseDelimiter clauseDelimiter
  | State.needNegBit => Block.nil
  | State.needVarDelimiter _ => Block.nil
  | State.needVarTag _ => Block.nil
  | State.inVar neg => closeClauseBlock neg
  | State.afterLiteralOne => Block.two clauseDelimiter clauseDelimiter
  | State.afterLiteralMany => Block.two clauseDelimiter clauseDelimiter

def stepBlock : State → StdSym → State × Block
  | State.leading0, a =>
      match a with
      | none => (State.leading1, Block.nil)
      | some (Sum.inl false) => (startLiteralState, Block.nil)
      | _ => (State.leading0, Block.nil)
  | State.leading1, a =>
      match a with
      | none => (State.leading2Plus, Block.nil)
      | some (Sum.inl false) => (startLiteralState, Block.nil)
      | _ => (State.leading1, Block.nil)
  | State.leading2Plus, a =>
      match a with
      | none => (State.leading2Plus, Block.one clauseDelimiter)
      | some (Sum.inl false) => (startLiteralState, Block.nil)
      | _ => (State.leading2Plus, Block.nil)
  | State.needNegBit, a =>
      match bit? a with
      | some neg => (State.needVarDelimiter neg, Block.nil)
      | none => (State.needNegBit, Block.nil)
  | State.needVarDelimiter neg, a =>
      match a with
      | none => (State.needVarTag neg, Block.nil)
      | _ => (State.needVarDelimiter neg, Block.nil)
  | State.needVarTag neg, a =>
      if isVarTag a then (State.inVar neg, Block.nil) else (State.needVarTag neg, Block.nil)
  | State.inVar neg, a =>
      match bit? a with
      | some b => (State.inVar neg, Block.one (literalNatBit b))
      | none => (State.afterLiteralOne, closeBlock neg)
  | State.afterLiteralOne, a =>
      match a with
      | none => (State.afterLiteralMany, Block.one clauseDelimiter)
      | some (Sum.inl false) => (startLiteralState, Block.nil)
      | _ => (State.afterLiteralOne, Block.nil)
  | State.afterLiteralMany, a =>
      match a with
      | none => (State.afterLiteralMany, Block.one clauseDelimiter)
      | some (Sum.inl false) => (startLiteralState, Block.nil)
      | _ => (State.afterLiteralMany, Block.nil)

theorem finishBlock_symbols_eq (st : State) :
    (finishBlock st).symbols = finish st := by
  cases st <;> simp [finishBlock, Block.symbols, finish, closeClauseBlock, closeLiteral,
    clauseDelimiter]

theorem stepBlock_fst_eq (st : State) (a : StdSym) :
    (stepBlock st a).1 = (step st a).1 := by
  cases st <;> cases a with
  | none =>
      simp [stepBlock, step, leadingStep, afterLiteralStep, bit?, isVarTag]
  | some side =>
      cases side <;> rename_i b <;> cases b <;>
        simp [stepBlock, step, leadingStep, afterLiteralStep, bit?, isVarTag,
          startLiteralState]

theorem stepBlock_symbols_eq (st : State) (a : StdSym) :
    (stepBlock st a).2.symbols = (step st a).2 := by
  cases st <;> cases a with
  | none =>
      simp [stepBlock, step, leadingStep, afterLiteralStep, bit?, isVarTag,
        closeBlock, Block.symbols, closeLiteral]
  | some side =>
    cases side <;> rename_i b <;> cases b <;>
      simp [stepBlock, step, leadingStep, afterLiteralStep, bit?, isVarTag,
        closeBlock, Block.symbols, closeLiteral]

theorem stepBlock_symbols_length_le_three (st : State) (a : StdSym) :
    (stepBlock st a).2.symbols.length ≤ 3 := by
  rw [stepBlock_symbols_eq]
  exact step_emit_length_le st a

theorem runAux_eq_stepBlock (st : State) (input : List StdSym) :
    runAux st input =
      match input with
      | [] => (finishBlock st).symbols
      | a :: rest =>
          let next := stepBlock st a
          next.2.symbols ++ runAux next.1 rest := by
  cases input with
  | nil =>
      exact (finishBlock_symbols_eq st).symm
  | cons a rest =>
      simp [runAux, stepBlock_fst_eq st a, stepBlock_symbols_eq st a]

/-! ### Concrete finite-state transducer -/

inductive ParserStack where
  | input
  | output
  | temp
  deriving DecidableEq, Fintype

abbrev parserAlphabet : ParserStack → Type
  | ParserStack.input => StdSym
  | ParserStack.output => OutSym
  | ParserStack.temp => OutSym

inductive ParserLabel where
  | readInput
  | emitTemp
  | moveTemp
  | pushOutput
  deriving DecidableEq, Fintype

inductive EmitCont where
  | scan
  | drain
  deriving DecidableEq, Fintype

inductive MachineState where
  | scan (st : State)
  | emit (cont : EmitCont) (st : State) (block : Block)
  | drain
  | output (a : OutSym)
  deriving DecidableEq, Fintype

namespace MachineState

def label : MachineState → ParserLabel
  | scan _ => ParserLabel.readInput
  | emit _ _ _ => ParserLabel.emitTemp
  | drain => ParserLabel.moveTemp
  | output _ => ParserLabel.pushOutput

def afterEmit : MachineState → MachineState
  | emit EmitCont.scan st _ => scan st
  | emit EmitCont.drain _ _ => drain
  | s => s

def hasHead : MachineState → Bool
  | emit _ _ block => block.head?.isSome
  | _ => false

def emitHead : MachineState → OutSym
  | emit _ _ block => block.headD
  | _ => clauseDelimiter

def emitTail : MachineState → MachineState
  | emit cont st block => emit cont st block.tail
  | s => s

def readAfterPop : MachineState → Option StdSym → MachineState
  | scan st, some a =>
      let next := stepBlock st a
      emit EmitCont.scan next.1 next.2
  | scan st, none =>
      emit EmitCont.drain st (finishBlock st)
  | s, _ => s

def moveAfterPop : MachineState → Option OutSym → MachineState
  | _, some a => output a
  | _, none => scan State.leading0

def isOutput : MachineState → Bool
  | output _ => true
  | _ => false

def outputHead : MachineState → OutSym
  | output a => a
  | _ => clauseDelimiter

end MachineState

def parserMachine : Turing.FinTM2 where
  K := ParserStack
  k₀ := ParserStack.input
  k₁ := ParserStack.output
  Γ := parserAlphabet
  Λ := ParserLabel
  main := ParserLabel.readInput
  σ := MachineState
  initialState := MachineState.scan State.leading0
  Γk₀Fin := by
    dsimp [parserAlphabet]
    infer_instance
  m
    | ParserLabel.readInput =>
        pop ParserStack.input MachineState.readAfterPop
          (goto MachineState.label)
    | ParserLabel.emitTemp =>
        branch MachineState.hasHead
          (push ParserStack.temp MachineState.emitHead
            (load MachineState.emitTail (goto MachineState.label)))
          (load MachineState.afterEmit (goto MachineState.label))
    | ParserLabel.moveTemp =>
        pop ParserStack.temp MachineState.moveAfterPop
          (branch MachineState.isOutput
            (goto MachineState.label)
            (load (fun _ => MachineState.scan State.leading0) halt))
    | ParserLabel.pushOutput =>
        push ParserStack.output MachineState.outputHead
          (load (fun _ => MachineState.drain) (goto MachineState.label))

def parserCfg (label : ParserLabel) (state : MachineState)
    (input : List StdSym) (output temp : List OutSym) : parserMachine.Cfg where
  l := some label
  var := state
  stk
    | ParserStack.input => input
    | ParserStack.output => output
    | ParserStack.temp => temp

def parserHalt (output : List OutSym) : parserMachine.Cfg where
  l := none
  var := MachineState.scan State.leading0
  stk
    | ParserStack.input => []
    | ParserStack.output => output
    | ParserStack.temp => []

lemma initList_parserMachine (input : List StdSym) :
    Turing.initList parserMachine input =
      parserCfg ParserLabel.readInput (MachineState.scan State.leading0) input [] [] := by
  simp [parserMachine, parserCfg, Turing.initList]
  congr
  funext k
  cases k <;> rfl

lemma haltList_parserMachine (output : List OutSym) :
    Turing.haltList parserMachine output = parserHalt output := by
  simp [parserMachine, parserHalt, Turing.haltList]
  congr
  funext k
  cases k <;> rfl

lemma readInput_step_cons (st : State) (a : StdSym) (input : List StdSym)
    (output temp : List OutSym) :
    parserMachine.step
        (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: input) output temp) =
      some
        (parserCfg ParserLabel.emitTemp
          (MachineState.emit EmitCont.scan (stepBlock st a).1 (stepBlock st a).2)
          input output temp) := by
  simp [parserMachine, parserCfg, MachineState.readAfterPop, MachineState.label]
  congr
  funext k
  cases k <;> rfl

lemma readInput_step_nil (st : State) (output temp : List OutSym) :
    parserMachine.step
        (parserCfg ParserLabel.readInput (MachineState.scan st) [] output temp) =
      some
        (parserCfg ParserLabel.emitTemp
          (MachineState.emit EmitCont.drain st (finishBlock st)) [] output temp) := by
  simp [parserMachine, parserCfg, MachineState.readAfterPop, MachineState.label]
  rfl

def afterEmitState (cont : EmitCont) (st : State) : MachineState :=
  match cont with
  | EmitCont.scan => MachineState.scan st
  | EmitCont.drain => MachineState.drain

lemma afterEmitState_label (cont : EmitCont) (st : State) :
    (afterEmitState cont st).label =
      match cont with
      | EmitCont.scan => ParserLabel.readInput
      | EmitCont.drain => ParserLabel.moveTemp := by
  cases cont <;> rfl

def emitTemp_run (cont : EmitCont) (st : State) (block : Block)
    (input : List StdSym) (output temp : List OutSym) :
    StateTransition.EvalsToInTime parserMachine.step
      (parserCfg ParserLabel.emitTemp (MachineState.emit cont st block) input output temp)
      (some
        (parserCfg (afterEmitState cont st).label (afterEmitState cont st) input output
          (block.symbols.reverse ++ temp)))
      (block.symbols.length + 1) := by
  cases hHead : block.head? with
  | none =>
      have hStep : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.emitTemp (MachineState.emit cont st block) input output temp)
          (some
            (parserCfg (afterEmitState cont st).label (afterEmitState cont st) input output
              temp)) 1 := by
        refine TM2Programs.evalsToInTimeOne ?_
        cases cont <;> cases block <;>
          simp [parserMachine, parserCfg, MachineState.hasHead, MachineState.afterEmit,
            MachineState.label, afterEmitState, Block.head?] at hHead ⊢ <;>
          rfl
      have hNil := Block.symbols_eq_nil_of_head?_none hHead
      simpa [hNil]
        using hStep
  | some a =>
      have hStep : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.emitTemp (MachineState.emit cont st block) input output temp)
          (some
            (parserCfg ParserLabel.emitTemp
              (MachineState.emit cont st block.tail) input output (a :: temp))) 1 := by
        refine TM2Programs.evalsToInTimeOne ?_
        cases block <;> simp [Block.head?] at hHead
        all_goals
          cases hHead
          simp [parserMachine, parserCfg, MachineState.hasHead, MachineState.emitHead,
            MachineState.emitTail, MachineState.label, Block.head?, Block.headD, Block.tail]
          congr
          funext k
          cases k <;> rfl
      have hTail :=
        emitTemp_run cont st block.tail input output (a :: temp)
      have hAll : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.emitTemp (MachineState.emit cont st block) input output temp)
          (some
            (parserCfg (afterEmitState cont st).label (afterEmitState cont st) input output
              (block.tail.symbols.reverse ++ (a :: temp))))
          ((block.tail.symbols.length + 1) + 1) :=
        StateTransition.EvalsToInTime.trans parserMachine.step 1
          (block.tail.symbols.length + 1)
          (parserCfg ParserLabel.emitTemp (MachineState.emit cont st block) input output temp)
          (parserCfg ParserLabel.emitTemp
            (MachineState.emit cont st block.tail) input output (a :: temp))
          (some
            (parserCfg (afterEmitState cont st).label (afterEmitState cont st) input output
              (block.tail.symbols.reverse ++ (a :: temp))))
          hStep hTail
      have hSymbols := Block.symbols_eq_cons_of_head? hHead
      simpa [hSymbols, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hAll
termination_by block.symbols.length
decreasing_by
  cases block <;> simp [Block.head?, Block.tail, Block.symbols] at hHead ⊢

def scan_run (st : State) (input : List StdSym) (output temp : List OutSym) :
    StateTransition.EvalsToInTime parserMachine.step
      (parserCfg ParserLabel.readInput (MachineState.scan st) input output temp)
      (some (parserCfg ParserLabel.moveTemp MachineState.drain [] output
        ((runAux st input).reverse ++ temp)))
      (5 * input.length + 6) := by
  induction input generalizing st temp with
  | nil =>
      have hRead : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.readInput (MachineState.scan st) [] output temp)
          (some
            (parserCfg ParserLabel.emitTemp
              (MachineState.emit EmitCont.drain st (finishBlock st)) [] output temp)) 1 :=
        TM2Programs.evalsToInTimeOne (readInput_step_nil st output temp)
      have hEmit := emitTemp_run EmitCont.drain st (finishBlock st) [] output temp
      have hAll : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.readInput (MachineState.scan st) [] output temp)
          (some
            (parserCfg ParserLabel.moveTemp MachineState.drain [] output
              ((finishBlock st).symbols.reverse ++ temp)))
          (((finishBlock st).symbols.length + 1) + 1) :=
        StateTransition.EvalsToInTime.trans parserMachine.step 1
          ((finishBlock st).symbols.length + 1)
          (parserCfg ParserLabel.readInput (MachineState.scan st) [] output temp)
          (parserCfg ParserLabel.emitTemp
            (MachineState.emit EmitCont.drain st (finishBlock st)) [] output temp)
          (some
            (parserCfg ParserLabel.moveTemp MachineState.drain [] output
              ((finishBlock st).symbols.reverse ++ temp)))
          hRead hEmit
      have hBound : ((finishBlock st).symbols.length + 1) + 1 ≤ 5 * 0 + 6 := by
        have hLen := Block.length_le_four (finishBlock st)
        omega
      have hRun : runAux st [] = (finishBlock st).symbols :=
        runAux_eq_stepBlock st []
      exact
        TM2Programs.evalsToInTime_mono
          (by simpa [hRun] using hAll) hBound
  | cons a rest ih =>
      let next := stepBlock st a
      have hRead : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: rest) output temp)
          (some
            (parserCfg ParserLabel.emitTemp
              (MachineState.emit EmitCont.scan next.1 next.2) rest output temp)) 1 := by
        simpa [next] using
          TM2Programs.evalsToInTimeOne (readInput_step_cons st a rest output temp)
      have hEmit := emitTemp_run EmitCont.scan next.1 next.2 rest output temp
      have hTail := ih next.1 (next.2.symbols.reverse ++ temp)
      have hReadEmit : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: rest) output temp)
          (some
            (parserCfg ParserLabel.readInput (MachineState.scan next.1) rest output
              (next.2.symbols.reverse ++ temp)))
          ((next.2.symbols.length + 1) + 1) :=
        StateTransition.EvalsToInTime.trans parserMachine.step 1
          (next.2.symbols.length + 1)
          (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: rest) output temp)
          (parserCfg ParserLabel.emitTemp
            (MachineState.emit EmitCont.scan next.1 next.2) rest output temp)
          (some
            (parserCfg ParserLabel.readInput (MachineState.scan next.1) rest output
              (next.2.symbols.reverse ++ temp)))
          hRead hEmit
      have hAll : StateTransition.EvalsToInTime parserMachine.step
          (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: rest) output temp)
          (some
            (parserCfg ParserLabel.moveTemp MachineState.drain [] output
              ((runAux next.1 rest).reverse ++ (next.2.symbols.reverse ++ temp))))
          ((5 * rest.length + 6) + ((next.2.symbols.length + 1) + 1)) :=
        StateTransition.EvalsToInTime.trans parserMachine.step
          ((next.2.symbols.length + 1) + 1) (5 * rest.length + 6)
          (parserCfg ParserLabel.readInput (MachineState.scan st) (a :: rest) output temp)
          (parserCfg ParserLabel.readInput (MachineState.scan next.1) rest output
            (next.2.symbols.reverse ++ temp))
          (some
            (parserCfg ParserLabel.moveTemp MachineState.drain [] output
              ((runAux next.1 rest).reverse ++ (next.2.symbols.reverse ++ temp))))
          hReadEmit hTail
      have hStepLen : next.2.symbols.length ≤ 3 := by
        simpa [next] using stepBlock_symbols_length_le_three st a
      have hBound :
          (5 * rest.length + 6) + ((next.2.symbols.length + 1) + 1) ≤
            5 * (a :: rest).length + 6 := by
        simp
        omega
      have hRun :
          runAux st (a :: rest) = next.2.symbols ++ runAux next.1 rest := by
        simpa [next] using runAux_eq_stepBlock st (a :: rest)
      exact
        TM2Programs.evalsToInTime_mono
          (by
            simpa [hRun, List.reverse_append, List.append_assoc] using hAll)
          hBound

def moveTemp_run (state : MachineState) (output temp : List OutSym) :
    StateTransition.EvalsToInTime parserMachine.step
      (parserCfg ParserLabel.moveTemp state [] output temp)
      (some (parserHalt (temp.reverse ++ output)))
      (2 * temp.length + 1) := by
  induction temp generalizing state output with
  | nil =>
      have hStep : parserMachine.step
          (parserCfg ParserLabel.moveTemp state [] output []) =
        some (parserHalt output) := by
        simp [parserMachine, parserCfg, parserHalt, MachineState.moveAfterPop,
          MachineState.isOutput]
        rfl
      simpa using TM2Programs.evalsToInTimeOne hStep
  | cons a rest ih =>
      let c₀ := parserCfg ParserLabel.moveTemp state [] output (a :: rest)
      let c₁ := parserCfg ParserLabel.pushOutput (MachineState.output a) [] output rest
      let c₂ := parserCfg ParserLabel.moveTemp MachineState.drain [] (a :: output) rest
      have h₁ : StateTransition.EvalsToInTime parserMachine.step c₀ (some c₁) 1 := by
        refine TM2Programs.evalsToInTimeOne ?_
        simp [c₀, c₁, parserMachine, parserCfg, MachineState.moveAfterPop,
          MachineState.isOutput, MachineState.label]
        congr
        funext k
        cases k <;> rfl
      have h₂ : StateTransition.EvalsToInTime parserMachine.step c₁ (some c₂) 1 := by
        refine TM2Programs.evalsToInTimeOne ?_
        simp [c₁, c₂, parserMachine, parserCfg, MachineState.outputHead,
          MachineState.label]
        congr
        funext k
        cases k <;> rfl
      have h₁₂ : StateTransition.EvalsToInTime parserMachine.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans parserMachine.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail := ih MachineState.drain (a :: output)
      have hAll : StateTransition.EvalsToInTime parserMachine.step c₀
          (some (parserHalt (rest.reverse ++ (a :: output))))
          ((2 * rest.length + 1) + (1 + 1)) :=
        StateTransition.EvalsToInTime.trans parserMachine.step (1 + 1)
          (2 * rest.length + 1) c₀ c₂
          (some (parserHalt (rest.reverse ++ (a :: output)))) h₁₂ hTail
      simpa [c₀, List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

def parserMachine_outputs (input : List StdSym) :
    Turing.TM2OutputsInTime parserMachine input (some (run input))
      (11 * input.length + 15) := by
  let parsed := run input
  have hScan := scan_run State.leading0 input [] []
  have hScan' : StateTransition.EvalsToInTime parserMachine.step
      (Turing.initList parserMachine input)
      (some (parserCfg ParserLabel.moveTemp MachineState.drain [] [] parsed.reverse))
      (5 * input.length + 6) := by
    simpa [parsed, run, initList_parserMachine] using hScan
  have hMove := moveTemp_run MachineState.drain [] parsed.reverse
  have hAll : StateTransition.EvalsToInTime parserMachine.step
      (Turing.initList parserMachine input)
      (some (parserHalt (parsed.reverse.reverse ++ [])))
      ((2 * parsed.reverse.length + 1) + (5 * input.length + 6)) := by
    simpa [parsed, run, initList_parserMachine] using
      StateTransition.EvalsToInTime.trans parserMachine.step (5 * input.length + 6)
        (2 * parsed.reverse.length + 1)
        (Turing.initList parserMachine input)
        (parserCfg ParserLabel.moveTemp MachineState.drain [] [] parsed.reverse)
        (some (parserHalt (parsed.reverse.reverse ++ []))) hScan' hMove
  change StateTransition.EvalsToInTime parserMachine.step
    (Turing.initList parserMachine input)
    (some (Turing.haltList parserMachine parsed))
    (11 * input.length + 15)
  rw [haltList_parserMachine]
  have hLen : parsed.length ≤ 3 * input.length + 4 := by
    simpa [parsed] using run_length_le input
  have hBound :
      (2 * parsed.reverse.length + 1) + (5 * input.length + 6) ≤
        11 * input.length + 15 := by
    simp [List.length_reverse]
    omega
  exact
    TM2Programs.evalsToInTime_mono
      (by simpa [parsed] using hAll) hBound

theorem standardThreeSATClauses_tm_polytime :
    TMPolyTimeMap
      threeSATDecisionProblem.Instance
      Karp21.cnfStructuredEncodedType
      (fun φ : ThreeCNF => φ.clauses) :=
  ⟨{ tm := parserMachine
     inputAlphabet := Equiv.refl StdSym
     outputAlphabet := Equiv.refl OutSym
     time := 11 * Polynomial.X + 15
     outputsFun := by
      intro φ
      have hRun := parserMachine_outputs (ThreeSATEncoding.encodeThreeCNF φ)
      have hEncode :
          run (ThreeSATEncoding.encodeThreeCNF φ) =
            Karp21.cnfStructuredEncodedType.encode φ.clauses := by
        simpa [parseThreeCNFEncoding] using run_encodeThreeCNF_eq_cnfStructured_encode φ
      have hEncode' :
          run (ThreeSATEncoding.encodeCNF φ.clauses) =
            Karp21.cnfStructuredEncodedType.encode φ.clauses := by
        simpa [ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF] using hEncode
      convert hRun using 1
      · simp only [threeSATDecisionProblem, threeSATSatLike, threeCNFEncodedType,
          SatLikeProblem.toDecisionProblem, ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF]
        change List.map (Equiv.refl StdSym).invFun (ThreeSATEncoding.encodeCNF φ.clauses) =
          ThreeSATEncoding.encodeCNF φ.clauses
        induction ThreeSATEncoding.encodeCNF φ.clauses with
        | nil => rfl
        | cons a rest ih =>
            change (Equiv.refl StdSym).invFun a ::
                List.map (Equiv.refl StdSym).invFun rest = a :: rest
            rw [ih]
            rfl
      · rw [hEncode]
        congr
        change List.map (Equiv.refl OutSym).invFun
            (Karp21.cnfStructuredEncodedType.encode φ.clauses) =
          Karp21.cnfStructuredEncodedType.encode φ.clauses
        induction Karp21.cnfStructuredEncodedType.encode φ.clauses with
        | nil => rfl
        | cons a rest ih =>
            change (Equiv.refl OutSym).invFun a ::
                List.map (Equiv.refl OutSym).invFun rest = a :: rest
            rw [ih]
            rfl
      · simp [threeSATDecisionProblem, threeSATSatLike, threeCNFEncodedType,
          SatLikeProblem.toDecisionProblem, ThreeSATEncoding.encodeThreeCNF_eq_encodeCNF,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

end StandardThreeSATParser

/-- Direct parser/projection witness from bundled 3SAT syntax to faithful CNF syntax. -/
theorem standardThreeSATClauses_tm_polytime :
    TMPolyTimeMap
      threeSATDecisionProblem.Instance
      Karp21.cnfStructuredEncodedType
      (fun φ : ThreeCNF => φ.clauses) :=
  StandardThreeSATParser.standardThreeSATClauses_tm_polytime

end SAT
end ComplexityReduction
