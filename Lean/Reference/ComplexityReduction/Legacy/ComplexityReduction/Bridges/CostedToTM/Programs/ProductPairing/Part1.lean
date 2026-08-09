/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.ProductSupport

namespace ComplexityReduction
namespace TM2Programs

open Turing.TM2.Stmt

/-- Stack layout for the arbitrary product-pairing runner. -/
inductive ProdMkStack (K₁ K₂ : Type) where
  | input
  | left (k : K₁)
  | right (k : K₂)
  | output
  | copyLeftTemp
  | copyRightTemp
  | outputTemp
  deriving DecidableEq, Fintype

/-- Stack alphabets for the arbitrary product-pairing runner. -/
abbrev prodMkAlphabet (α δ : Type) (tm₁ tm₂ : Turing.FinTM2) :
    ProdMkStack tm₁.K tm₂.K → Type
  | ProdMkStack.input => α
  | ProdMkStack.left k => tm₁.Γ k
  | ProdMkStack.right k => tm₂.Γ k
  | ProdMkStack.output => δ
  | ProdMkStack.copyLeftTemp => tm₁.Γ tm₁.k₀
  | ProdMkStack.copyRightTemp => tm₂.Γ tm₂.k₀
  | ProdMkStack.outputTemp => δ

/-- Control labels for the arbitrary product-pairing runner. -/
inductive ProdMkLabel (Λ₁ Λ₂ β γ δ : Type) where
  | copy (label : PairStackCopyMapLabel β γ)
  | left (label : Λ₁)
  | right (label : Λ₂)
  | write (label : PairOutputWriteLabel δ)
  deriving DecidableEq, Fintype

/-- Phase-indexed state for the arbitrary product-pairing runner. -/
inductive ProdMkState (σ₁ σ₂ β γ δ : Type) where
  | copy (state : PairStackCopyMapState β γ)
  | left (state : σ₁)
  | right (state : σ₂)
  | write (state : Option δ)
  deriving Fintype

def prodMkInitialState (tm₁ tm₂ : Turing.FinTM2) (δ : Type) :
    ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ :=
  ProdMkState.copy PairStackCopyMapState.none

def prodMkCopyState (tm₁ tm₂ : Turing.FinTM2) (δ : Type) :
    ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ →
      PairStackCopyMapState (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
  | ProdMkState.copy state => state
  | _ => PairStackCopyMapState.none

def prodMkLeftState (tm₁ tm₂ : Turing.FinTM2) (δ : Type) :
    ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ → tm₁.σ
  | ProdMkState.left state => state
  | _ => tm₁.initialState

def prodMkRightState (tm₁ tm₂ : Turing.FinTM2) (δ : Type) :
    ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ → tm₂.σ
  | ProdMkState.right state => state
  | _ => tm₂.initialState

def prodMkWriteState (tm₁ tm₂ : Turing.FinTM2) (δ : Type) :
    ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ → Option δ
  | ProdMkState.write state => state
  | _ => none

def prodMkCopyStack (tm₁ tm₂ : Turing.FinTM2) :
    PairStackCopyMapStack → ProdMkStack tm₁.K tm₂.K
  | PairStackCopyMapStack.source => ProdMkStack.input
  | PairStackCopyMapStack.leftTarget => ProdMkStack.left tm₁.k₀
  | PairStackCopyMapStack.rightTarget => ProdMkStack.right tm₂.k₀
  | PairStackCopyMapStack.leftTemp => ProdMkStack.copyLeftTemp
  | PairStackCopyMapStack.rightTemp => ProdMkStack.copyRightTemp

def prodMkWriteStack (tm₁ tm₂ : Turing.FinTM2) :
    PairOutputWriteStack → ProdMkStack tm₁.K tm₂.K
  | PairOutputWriteStack.leftSource => ProdMkStack.left tm₁.k₁
  | PairOutputWriteStack.rightSource => ProdMkStack.right tm₂.k₁
  | PairOutputWriteStack.output => ProdMkStack.output
  | PairOutputWriteStack.temp => ProdMkStack.outputTemp

/-- Relabel the left supplied machine into the product runner. -/
def prodMkLeftStmt (α δ : Type) (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ →
    Turing.TM2.Stmt (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
  | push k f q =>
      push (ProdMkStack.left k) (fun state => f (prodMkLeftState tm₁ tm₂ δ state))
        (prodMkLeftStmt α δ tm₁ tm₂ q)
  | peek k f q =>
      peek (ProdMkStack.left k)
        (fun state head => ProdMkState.left (f (prodMkLeftState tm₁ tm₂ δ state) head))
        (prodMkLeftStmt α δ tm₁ tm₂ q)
  | pop k f q =>
      pop (ProdMkStack.left k)
        (fun state head => ProdMkState.left (f (prodMkLeftState tm₁ tm₂ δ state) head))
        (prodMkLeftStmt α δ tm₁ tm₂ q)
  | load f q =>
      load (fun state => ProdMkState.left (f (prodMkLeftState tm₁ tm₂ δ state)))
        (prodMkLeftStmt α δ tm₁ tm₂ q)
  | branch f qTrue qFalse =>
      branch (fun state => f (prodMkLeftState tm₁ tm₂ δ state))
        (prodMkLeftStmt α δ tm₁ tm₂ qTrue) (prodMkLeftStmt α δ tm₁ tm₂ qFalse)
  | goto f =>
      goto fun state => ProdMkLabel.left (f (prodMkLeftState tm₁ tm₂ δ state))
  | halt =>
      load (fun _ => ProdMkState.right tm₂.initialState)
        (goto fun _ => ProdMkLabel.right tm₂.main)

/-- Relabel the right supplied machine into the product runner. -/
def prodMkRightStmt (α δ : Type) (tm₁ tm₂ : Turing.FinTM2) :
    Turing.TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ →
    Turing.TM2.Stmt (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
  | push k f q =>
      push (ProdMkStack.right k) (fun state => f (prodMkRightState tm₁ tm₂ δ state))
        (prodMkRightStmt α δ tm₁ tm₂ q)
  | peek k f q =>
      peek (ProdMkStack.right k)
        (fun state head => ProdMkState.right (f (prodMkRightState tm₁ tm₂ δ state) head))
        (prodMkRightStmt α δ tm₁ tm₂ q)
  | pop k f q =>
      pop (ProdMkStack.right k)
        (fun state head => ProdMkState.right (f (prodMkRightState tm₁ tm₂ δ state) head))
        (prodMkRightStmt α δ tm₁ tm₂ q)
  | load f q =>
      load (fun state => ProdMkState.right (f (prodMkRightState tm₁ tm₂ δ state)))
        (prodMkRightStmt α δ tm₁ tm₂ q)
  | branch f qTrue qFalse =>
      branch (fun state => f (prodMkRightState tm₁ tm₂ δ state))
        (prodMkRightStmt α δ tm₁ tm₂ qTrue) (prodMkRightStmt α δ tm₁ tm₂ qFalse)
  | goto f =>
      goto fun state => ProdMkLabel.right (f (prodMkRightState tm₁ tm₂ δ state))
  | halt =>
      load (fun _ => ProdMkState.write (none : Option δ))
        (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.readRight)

/-- The arbitrary product-pairing orchestration machine. -/
def prodMkMachine (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ) : Turing.FinTM2 := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  letI := tm₁.kFin
  letI := tm₂.kFin
  letI := tm₁.ΛFin
  letI := tm₂.ΛFin
  letI := tm₁.σFin
  letI := tm₂.σFin
  exact
    { K := ProdMkStack tm₁.K tm₂.K
      k₀ := ProdMkStack.input
      k₁ := ProdMkStack.output
      Γ := prodMkAlphabet α δ tm₁ tm₂
      Λ := ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ
      main := ProdMkLabel.copy PairStackCopyMapLabel.readSource
      σ := ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ
      initialState := prodMkInitialState tm₁ tm₂ δ
      Γk₀Fin := by
        dsimp [prodMkAlphabet]
        infer_instance
      m := fun
        | ProdMkLabel.copy PairStackCopyMapLabel.readSource =>
            pop ProdMkStack.input
              (fun _ head =>
                match head with
                | some a =>
                    ProdMkState.copy (PairStackCopyMapState.pair (copyLeft a) (copyRight a))
                | none => ProdMkState.copy PairStackCopyMapState.none)
              (branch (fun state => (prodMkCopyState tm₁ tm₂ δ state).isPair)
                (goto fun state =>
                  match prodMkCopyState tm₁ tm₂ δ state with
                  | PairStackCopyMapState.pair b c =>
                      ProdMkLabel.copy (PairStackCopyMapLabel.pushLeftTemp b c)
                  | _ => ProdMkLabel.copy PairStackCopyMapLabel.drainLeft)
                (goto fun _ => ProdMkLabel.copy PairStackCopyMapLabel.drainLeft))
        | ProdMkLabel.copy (PairStackCopyMapLabel.pushLeftTemp b c) =>
            push ProdMkStack.copyLeftTemp (fun _ => b)
              (goto fun _ => ProdMkLabel.copy (PairStackCopyMapLabel.pushRightTemp c))
        | ProdMkLabel.copy (PairStackCopyMapLabel.pushRightTemp c) =>
            push ProdMkStack.copyRightTemp (fun _ => c)
              (goto fun _ => ProdMkLabel.copy PairStackCopyMapLabel.readSource)
        | ProdMkLabel.copy PairStackCopyMapLabel.drainLeft =>
            pop ProdMkStack.copyLeftTemp
              (fun _ head =>
                match head with
                | some b => ProdMkState.copy (PairStackCopyMapState.left b)
                | none => ProdMkState.copy PairStackCopyMapState.none)
              (branch (fun state => (prodMkCopyState tm₁ tm₂ δ state).isLeft)
                (goto fun state =>
                  match prodMkCopyState tm₁ tm₂ δ state with
                  | PairStackCopyMapState.left b =>
                      ProdMkLabel.copy (PairStackCopyMapLabel.pushLeftTarget b)
                  | _ => ProdMkLabel.copy PairStackCopyMapLabel.drainRight)
                (goto fun _ => ProdMkLabel.copy PairStackCopyMapLabel.drainRight))
        | ProdMkLabel.copy (PairStackCopyMapLabel.pushLeftTarget b) =>
            push (ProdMkStack.left tm₁.k₀) (fun _ => b)
              (goto fun _ => ProdMkLabel.copy PairStackCopyMapLabel.drainLeft)
        | ProdMkLabel.copy PairStackCopyMapLabel.drainRight =>
            pop ProdMkStack.copyRightTemp
              (fun _ head =>
                match head with
                | some c => ProdMkState.copy (PairStackCopyMapState.right c)
                | none => ProdMkState.copy PairStackCopyMapState.none)
              (branch (fun state => (prodMkCopyState tm₁ tm₂ δ state).isRight)
                (goto fun state =>
                  match prodMkCopyState tm₁ tm₂ δ state with
                  | PairStackCopyMapState.right c =>
                      ProdMkLabel.copy (PairStackCopyMapLabel.pushRightTarget c)
                  | _ => ProdMkLabel.left tm₁.main)
                (load (fun _ => ProdMkState.left tm₁.initialState)
                  (goto fun _ => ProdMkLabel.left tm₁.main)))
        | ProdMkLabel.copy (PairStackCopyMapLabel.pushRightTarget c) =>
            push (ProdMkStack.right tm₂.k₀) (fun _ => c)
              (goto fun _ => ProdMkLabel.copy PairStackCopyMapLabel.drainRight)
        | ProdMkLabel.left label => prodMkLeftStmt α δ tm₁ tm₂ (tm₁.m label)
        | ProdMkLabel.right label => prodMkRightStmt α δ tm₁ tm₂ (tm₂.m label)
        | ProdMkLabel.write PairOutputWriteLabel.readRight =>
            pop (ProdMkStack.right tm₂.k₁)
              (fun _ head => ProdMkState.write (head.map writeRight))
              (branch (fun state => (prodMkWriteState tm₁ tm₂ δ state).isSome)
                (goto fun state =>
                  match prodMkWriteState tm₁ tm₂ δ state with
                  | some d => ProdMkLabel.write (PairOutputWriteLabel.pushRightTemp d)
                  | none => ProdMkLabel.write PairOutputWriteLabel.drainRight)
                (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.drainRight))
        | ProdMkLabel.write (PairOutputWriteLabel.pushRightTemp d) =>
            push ProdMkStack.outputTemp (fun _ => d)
              (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.readRight)
        | ProdMkLabel.write PairOutputWriteLabel.drainRight =>
            pop ProdMkStack.outputTemp (fun _ head => ProdMkState.write head)
              (branch (fun state => (prodMkWriteState tm₁ tm₂ δ state).isSome)
                (goto fun state =>
                  match prodMkWriteState tm₁ tm₂ δ state with
                  | some d => ProdMkLabel.write (PairOutputWriteLabel.pushRightOutput d)
                  | none => ProdMkLabel.write PairOutputWriteLabel.writeDelimiter)
                (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.writeDelimiter))
        | ProdMkLabel.write (PairOutputWriteLabel.pushRightOutput d) =>
            push ProdMkStack.output (fun _ => d)
              (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.drainRight)
        | ProdMkLabel.write PairOutputWriteLabel.writeDelimiter =>
            push ProdMkStack.output (fun _ => delimiter)
              (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.readLeft)
        | ProdMkLabel.write PairOutputWriteLabel.readLeft =>
            pop (ProdMkStack.left tm₁.k₁)
              (fun _ head => ProdMkState.write (head.map writeLeft))
              (branch (fun state => (prodMkWriteState tm₁ tm₂ δ state).isSome)
                (goto fun state =>
                  match prodMkWriteState tm₁ tm₂ δ state with
                  | some d => ProdMkLabel.write (PairOutputWriteLabel.pushLeftTemp d)
                  | none => ProdMkLabel.write PairOutputWriteLabel.drainLeft)
                (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.drainLeft))
        | ProdMkLabel.write (PairOutputWriteLabel.pushLeftTemp d) =>
            push ProdMkStack.outputTemp (fun _ => d)
              (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.readLeft)
        | ProdMkLabel.write PairOutputWriteLabel.drainLeft =>
            pop ProdMkStack.outputTemp (fun _ head => ProdMkState.write head)
              (branch (fun state => (prodMkWriteState tm₁ tm₂ δ state).isSome)
                (goto fun state =>
                  match prodMkWriteState tm₁ tm₂ δ state with
                  | some d => ProdMkLabel.write (PairOutputWriteLabel.pushLeftOutput d)
                  | none => ProdMkLabel.write PairOutputWriteLabel.drainLeft)
                (load (fun _ => prodMkInitialState tm₁ tm₂ δ) halt))
        | ProdMkLabel.write (PairOutputWriteLabel.pushLeftOutput d) =>
            push ProdMkStack.output (fun _ => d)
              (goto fun _ => ProdMkLabel.write PairOutputWriteLabel.drainLeft) }

def prodMkCfg (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (label : Option (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ))
    (state : ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
    (input : List α) (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (copyLeftTemp : List (tm₁.Γ tm₁.k₀))
    (copyRightTemp : List (tm₂.Γ tm₂.k₀)) (outputTemp : List δ) :
    Turing.TM2.Cfg (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ) where
  l := label
  var := state
  stk
    | ProdMkStack.input => input
    | ProdMkStack.left k => left k
    | ProdMkStack.right k => right k
    | ProdMkStack.output => output
    | ProdMkStack.copyLeftTemp => copyLeftTemp
    | ProdMkStack.copyRightTemp => copyRightTemp
    | ProdMkStack.outputTemp => outputTemp

def prodMkCopyCfg (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (cfg :
      (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
        copyLeft copyRight).Cfg)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) :
    Turing.TM2.Cfg (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  let left' := Function.update left tm₁.k₀ (cfg.stk PairStackCopyMapStack.leftTarget)
  let right' := Function.update right tm₂.k₀ (cfg.stk PairStackCopyMapStack.rightTarget)
  exact
    match cfg.l with
    | some label =>
        prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.copy label))
          (ProdMkState.copy cfg.var) (cfg.stk PairStackCopyMapStack.source)
          left' right' output (cfg.stk PairStackCopyMapStack.leftTemp)
          (cfg.stk PairStackCopyMapStack.rightTemp) outputTemp
    | none =>
        prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.left tm₁.main))
          (ProdMkState.left tm₁.initialState) (cfg.stk PairStackCopyMapStack.source)
          left' right' output (cfg.stk PairStackCopyMapStack.leftTemp)
          (cfg.stk PairStackCopyMapStack.rightTemp) outputTemp

def prodMkLeftCfg (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (cfg : tm₁.Cfg) (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) :
    Turing.TM2.Cfg (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ) :=
  match cfg.l with
  | some label =>
      prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.left label))
        (ProdMkState.left cfg.var) [] cfg.stk right output [] [] outputTemp
  | none =>
      prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.right tm₂.main))
        (ProdMkState.right tm₂.initialState) [] cfg.stk right output [] [] outputTemp

def prodMkRightCfg (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (cfg : tm₂.Cfg) (left : (k : tm₁.K) → List (tm₁.Γ k))
    (output : List δ) (outputTemp : List δ) :
    Turing.TM2.Cfg (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ) :=
  match cfg.l with
  | some label =>
      prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.right label))
        (ProdMkState.right cfg.var) [] left cfg.stk output [] [] outputTemp
  | none =>
      prodMkCfg α δ tm₁ tm₂
        (some (ProdMkLabel.write PairOutputWriteLabel.readRight))
        (ProdMkState.write none) [] left cfg.stk output [] [] outputTemp

def prodMkWriteCfg (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype (tm₁.Γ tm₁.k₁)] [Fintype (tm₂.Γ tm₂.k₁)] [Fintype δ]
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (cfg :
      (pairOutputWriteMachine (tm₁.Γ tm₁.k₁) (tm₂.Γ tm₂.k₁) δ
        writeLeft writeRight delimiter).Cfg)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k)) :
    Turing.TM2.Cfg (prodMkAlphabet α δ tm₁ tm₂)
      (ProdMkLabel tm₁.Λ tm₂.Λ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ)
      (ProdMkState tm₁.σ tm₂.σ (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀) δ) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  let left' := Function.update left tm₁.k₁ (cfg.stk PairOutputWriteStack.leftSource)
  let right' := Function.update right tm₂.k₁ (cfg.stk PairOutputWriteStack.rightSource)
  exact
    match cfg.l with
    | some label =>
        prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.write label))
          (ProdMkState.write cfg.var) [] left' right' (cfg.stk PairOutputWriteStack.output)
          [] [] (cfg.stk PairOutputWriteStack.temp)
    | none =>
        prodMkCfg α δ tm₁ tm₂ none (prodMkInitialState tm₁ tm₂ δ) []
          left' right' (cfg.stk PairOutputWriteStack.output) [] []
          (cfg.stk PairOutputWriteStack.temp)

lemma prodMkMachine_copy_step (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (cfg next :
      (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
        copyLeft copyRight).Cfg)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ)
    (hStep :
      (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
        copyLeft copyRight).step cfg = some next) :
    (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
        (prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight cfg left right output outputTemp) =
      some (prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight next left right output outputTemp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          cases label with
          | readSource =>
              cases hSrc : stk PairStackCopyMapStack.source with
              | nil =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isPair,
                    prodMkCopyState, hSrc, Function.update] at hStep ⊢
                  cases hStep
                  congr
              | cons a source =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isPair,
                    prodMkCopyState, hSrc, Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => rfl
                  | outputTemp => rfl
          | pushLeftTemp b c =>
              simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => simp [Function.update]
              | copyRightTemp => rfl
              | outputTemp => rfl
          | pushRightTemp c =>
              simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => rfl
              | copyRightTemp => simp [Function.update]
              | outputTemp => rfl
          | drainLeft =>
              cases hTemp : stk PairStackCopyMapStack.leftTemp with
              | nil =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isLeft,
                    prodMkCopyState, hTemp, Function.update] at hStep ⊢
                  cases hStep
                  congr
              | cons b leftTemp =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isLeft,
                    prodMkCopyState, hTemp, Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => simp [Function.update]
                  | copyRightTemp => rfl
                  | outputTemp => rfl
          | pushLeftTarget b =>
              simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => rfl
          | drainRight =>
              cases hTemp : stk PairStackCopyMapStack.rightTemp with
              | nil =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isRight,
                    prodMkCopyState, hTemp, Function.update] at hStep ⊢
                  cases hStep
                  congr
              | cons c rightTemp =>
                  simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                    Turing.FinTM2.step, Turing.TM2.step, PairStackCopyMapState.isRight,
                    prodMkCopyState, hTemp, Function.update] at hStep ⊢
                  cases hStep
                  congr
                  funext s
                  cases s with
                  | input => rfl
                  | left k =>
                      by_cases hk : k = tm₁.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | right k =>
                      by_cases hk : k = tm₂.k₀
                      · subst k
                        simp [Function.update]
                      · simp [Function.update, hk]
                  | output => rfl
                  | copyLeftTemp => rfl
                  | copyRightTemp => simp [Function.update]
                  | outputTemp => rfl
          | pushRightTarget c =>
              simp [prodMkMachine, prodMkCopyCfg, prodMkCfg, pairStackCopyMapMachine,
                Turing.FinTM2.step, Turing.TM2.step, Function.update] at hStep ⊢
              cases hStep
              simp
              congr
              funext s
              cases s with
              | input => rfl
              | left k =>
                  by_cases hk : k = tm₁.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | right k =>
                  by_cases hk : k = tm₂.k₀
                  · subst k
                    simp [Function.update]
                  · simp [Function.update, hk]
              | output => rfl
              | copyLeftTemp => rfl
              | copyRightTemp => rfl
              | outputTemp => rfl

def prodMkCopy_evalsToInTime (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    {cfg next :
      (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
        copyLeft copyRight).Cfg}
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) {time : Nat}
    (h :
      StateTransition.EvalsToInTime
        (pairStackCopyMapMachine α (tm₁.Γ tm₁.k₀) (tm₂.Γ tm₂.k₀)
          copyLeft copyRight).step cfg (some next) time) :
    StateTransition.EvalsToInTime
      (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
      (prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight cfg left right output outputTemp)
      (some
        (prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight next left right output outputTemp))
      time := by
  simpa using
    evalsToInTime_map_some
      (fun cfg =>
        prodMkCopyCfg α δ tm₁ tm₂ copyLeft copyRight cfg left right output outputTemp)
      (fun s s' hStep =>
        prodMkMachine_copy_step α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight
          delimiter s s' left right output outputTemp hStep)
      h

lemma prodMkLeftStmt_stepAux (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (q : Turing.TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v : tm₁.σ)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) :
    Turing.TM2.stepAux (prodMkLeftStmt α δ tm₁ tm₂ q) (ProdMkState.left v)
        (fun
          | ProdMkStack.input => ([] : List α)
          | ProdMkStack.left k => left k
          | ProdMkStack.right k => right k
          | ProdMkStack.output => output
          | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
          | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
          | ProdMkStack.outputTemp => outputTemp) =
      prodMkLeftCfg α δ tm₁ tm₂ (Turing.TM2.stepAux q v left) right output outputTemp := by
  letI := tm₁.kDecidableEq
  induction q generalizing v left with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | ProdMkStack.input => ([] : List α)
                | ProdMkStack.left k' => left k'
                | ProdMkStack.right k' => right k'
                | ProdMkStack.output => output
                | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
                | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
                | ProdMkStack.outputTemp => outputTemp) :
                (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s))
              (ProdMkStack.left k) (f v :: left k) =
            ((fun
              | ProdMkStack.input => ([] : List α)
              | ProdMkStack.left k' => Function.update left k (f v :: left k) k'
              | ProdMkStack.right k' => right k'
              | ProdMkStack.output => output
              | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
              | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
              | ProdMkStack.outputTemp => outputTemp) :
              (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s)) := by
        funext s
        cases s with
        | input => simp [Function.update]
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' => simp [Function.update]
        | output => simp [Function.update]
        | copyLeftTemp => simp [Function.update]
        | copyRightTemp => simp [Function.update]
        | outputTemp => simp [Function.update]
      simpa [prodMkLeftStmt, prodMkLeftState, hstk] using
        ih v (Function.update left k (f v :: left k))
  | peek k f q ih =>
      simpa [prodMkLeftStmt, prodMkLeftState] using ih (f v (left k).head?) left
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | ProdMkStack.input => ([] : List α)
                | ProdMkStack.left k' => left k'
                | ProdMkStack.right k' => right k'
                | ProdMkStack.output => output
                | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
                | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
                | ProdMkStack.outputTemp => outputTemp) :
                (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s))
              (ProdMkStack.left k) (left k).tail =
            ((fun
              | ProdMkStack.input => ([] : List α)
              | ProdMkStack.left k' => Function.update left k (left k).tail k'
              | ProdMkStack.right k' => right k'
              | ProdMkStack.output => output
              | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
              | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
              | ProdMkStack.outputTemp => outputTemp) :
              (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s)) := by
        funext s
        cases s with
        | input => simp [Function.update]
        | left k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | right k' => simp [Function.update]
        | output => simp [Function.update]
        | copyLeftTemp => simp [Function.update]
        | copyRightTemp => simp [Function.update]
        | outputTemp => simp [Function.update]
      simpa [prodMkLeftStmt, prodMkLeftState, hstk] using
        ih (f v (left k).head?) (Function.update left k (left k).tail)
  | load f q ih =>
      simpa [prodMkLeftStmt, prodMkLeftState] using ih (f v) left
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [prodMkLeftStmt, prodMkLeftState, hf] using ihTrue v left
      · simpa [prodMkLeftStmt, prodMkLeftState, hf] using ihFalse v left
  | goto f =>
      simp [prodMkLeftStmt, prodMkLeftCfg, prodMkCfg, prodMkLeftState]
  | halt =>
      simp [prodMkLeftStmt, prodMkLeftCfg, prodMkCfg]

lemma prodMkRightStmt_stepAux (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    (q : Turing.TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v : tm₂.σ)
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) :
    Turing.TM2.stepAux (prodMkRightStmt α δ tm₁ tm₂ q) (ProdMkState.right v)
        (fun
          | ProdMkStack.input => ([] : List α)
          | ProdMkStack.left k => left k
          | ProdMkStack.right k => right k
          | ProdMkStack.output => output
          | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
          | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
          | ProdMkStack.outputTemp => outputTemp) =
      prodMkRightCfg α δ tm₁ tm₂ (Turing.TM2.stepAux q v right) left output outputTemp := by
  letI := tm₂.kDecidableEq
  induction q generalizing v right with
  | push k f q ih =>
      have hstk :
          Function.update
              ((fun
                | ProdMkStack.input => ([] : List α)
                | ProdMkStack.left k' => left k'
                | ProdMkStack.right k' => right k'
                | ProdMkStack.output => output
                | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
                | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
                | ProdMkStack.outputTemp => outputTemp) :
                (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s))
              (ProdMkStack.right k) (f v :: right k) =
            ((fun
              | ProdMkStack.input => ([] : List α)
              | ProdMkStack.left k' => left k'
              | ProdMkStack.right k' => Function.update right k (f v :: right k) k'
              | ProdMkStack.output => output
              | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
              | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
              | ProdMkStack.outputTemp => outputTemp) :
              (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s)) := by
        funext s
        cases s with
        | input => simp [Function.update]
        | left k' => simp [Function.update]
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | output => simp [Function.update]
        | copyLeftTemp => simp [Function.update]
        | copyRightTemp => simp [Function.update]
        | outputTemp => simp [Function.update]
      simpa [prodMkRightStmt, prodMkRightState, hstk] using
        ih v (Function.update right k (f v :: right k))
  | peek k f q ih =>
      simpa [prodMkRightStmt, prodMkRightState] using ih (f v (right k).head?) right
  | pop k f q ih =>
      have hstk :
          Function.update
              ((fun
                | ProdMkStack.input => ([] : List α)
                | ProdMkStack.left k' => left k'
                | ProdMkStack.right k' => right k'
                | ProdMkStack.output => output
                | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
                | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
                | ProdMkStack.outputTemp => outputTemp) :
                (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s))
              (ProdMkStack.right k) (right k).tail =
            ((fun
              | ProdMkStack.input => ([] : List α)
              | ProdMkStack.left k' => left k'
              | ProdMkStack.right k' => Function.update right k (right k).tail k'
              | ProdMkStack.output => output
              | ProdMkStack.copyLeftTemp => ([] : List (tm₁.Γ tm₁.k₀))
              | ProdMkStack.copyRightTemp => ([] : List (tm₂.Γ tm₂.k₀))
              | ProdMkStack.outputTemp => outputTemp) :
              (s : ProdMkStack tm₁.K tm₂.K) → List (prodMkAlphabet α δ tm₁ tm₂ s)) := by
        funext s
        cases s with
        | input => simp [Function.update]
        | left k' => simp [Function.update]
        | right k' =>
            by_cases hk : k' = k
            · subst k'
              simp [Function.update]
            · simp [Function.update, hk]
        | output => simp [Function.update]
        | copyLeftTemp => simp [Function.update]
        | copyRightTemp => simp [Function.update]
        | outputTemp => simp [Function.update]
      simpa [prodMkRightStmt, prodMkRightState, hstk] using
        ih (f v (right k).head?) (Function.update right k (right k).tail)
  | load f q ih =>
      simpa [prodMkRightStmt, prodMkRightState] using ih (f v) right
  | branch f qTrue qFalse ihTrue ihFalse =>
      by_cases hf : f v
      · simpa [prodMkRightStmt, prodMkRightState, hf] using ihTrue v right
      · simpa [prodMkRightStmt, prodMkRightState, hf] using ihFalse v right
  | goto f =>
      simp [prodMkRightStmt, prodMkRightCfg, prodMkCfg, prodMkRightState]
  | halt =>
      simp [prodMkRightStmt, prodMkRightCfg, prodMkCfg]

lemma prodMkMachine_left_step (α δ : Type) (tm₁ tm₂ : Turing.FinTM2)
    [Fintype α] [Fintype (tm₁.Γ tm₁.k₀)] [Fintype (tm₂.Γ tm₂.k₀)] [Fintype δ]
    (copyLeft : α → tm₁.Γ tm₁.k₀) (copyRight : α → tm₂.Γ tm₂.k₀)
    (writeLeft : tm₁.Γ tm₁.k₁ → δ) (writeRight : tm₂.Γ tm₂.k₁ → δ)
    (delimiter : δ)
    (cfg next : tm₁.Cfg) (right : (k : tm₂.K) → List (tm₂.Γ k))
    (output : List δ) (outputTemp : List δ) (hStep : tm₁.step cfg = some next) :
    (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
        (prodMkLeftCfg α δ tm₁ tm₂ cfg right output outputTemp) =
      some (prodMkLeftCfg α δ tm₁ tm₂ next right output outputTemp) := by
  cases cfg with
  | mk label var stk =>
      cases label with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at hStep
      | some label =>
          have hNext : next = Turing.TM2.stepAux (tm₁.m label) var stk := by
            have hSome :
                some (Turing.TM2.stepAux (tm₁.m label) var stk) = some next := by
              simpa [Turing.FinTM2.step, Turing.TM2.step] using hStep
            exact (Option.some.inj hSome).symm
          subst next
          change
            (prodMkMachine α δ tm₁ tm₂ copyLeft copyRight writeLeft writeRight delimiter).step
                (prodMkCfg α δ tm₁ tm₂ (some (ProdMkLabel.left label))
                  (ProdMkState.left var) [] stk right output [] [] outputTemp) =
              some
                (prodMkLeftCfg α δ tm₁ tm₂
                  (Turing.TM2.stepAux (tm₁.m label) var stk) right output outputTemp)
          simp [prodMkMachine, prodMkCfg, Turing.FinTM2.step, Turing.TM2.step]
          exact congrArg some
            (prodMkLeftStmt_stepAux α δ tm₁ tm₂ (tm₁.m label) var stk right output outputTemp)

end TM2Programs
end ComplexityReduction
