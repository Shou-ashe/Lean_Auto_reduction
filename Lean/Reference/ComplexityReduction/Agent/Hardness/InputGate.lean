/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Export
import Lean.Meta.Basic

/-! Exact declaration-name input checks for the hardness agent. -/

namespace ComplexityReduction.Agent.Hardness.InputGate

open Lean Meta Encoding Certificate Registry

inductive Failure where
  | unknownDeclaration (declaration : Name)
  | universePolymorphicDeclaration (declaration : Name)
  | notPresentedProblem (declaration : Name) (actualType : Expr)
  | notUnaryPredicate (declaration : Name) (actualType : Expr)
  | notValidatedPresentedProblem (declaration : Name)
  | invalidNativeMembership (declaration : Name) (source actualType : Expr)
  deriving Repr

structure PresentedHandle where
  declaration : Name
  term : Expr

/-- A closed declaration whose type is exactly one predicate argument followed by `Prop`. -/
structure PredicateHandle where
  declaration : Name
  term : Expr
  domain : Expr

/-- The two independent definitional-equality checks needed to ground a predicate. -/
structure PredicateCompatibility where
  domainDefEq : Bool
  acceptsDefEq : Bool
  deriving Repr

private def declarationInfo (environment : Environment) (declaration : Name) :
    Except Failure ConstantInfo :=
  match environment.find? declaration with
  | none => .error (.unknownDeclaration declaration)
  | some info =>
      if info.levelParams.isEmpty then .ok info
      else .error (.universePolymorphicDeclaration declaration)

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def unaryPredicateDomain? (actualType : Expr) : MetaM (Option Expr) := do
  match ← whnf actualType with
  | .forallE _ domain body _ =>
      if (← whnf body) == .sort .zero then
        return some domain
      else
        return none
  | _ => return none

/-- Resolve a closed declaration whose exact type is `PresentedProblem`. -/
def presented (environment : Environment) (declaration : Name) :
    MetaM (Except Failure PresentedHandle) := do
  match declarationInfo environment declaration with
  | .error failure => return .error failure
  | .ok _ =>
      let term := mkConst declaration
      let actualType ← inferType term
      unless ← controlledDefEq actualType (mkConst ``PresentedProblem) do
        return .error (.notPresentedProblem declaration actualType)
      return .ok { declaration, term }

/--
Resolve a monomorphic, closed declaration whose type is strictly `α → Prop`.

In particular, a curried relation such as `α → β → Prop` is rejected rather
than being mistaken for a unary decision predicate.
-/
def predicate (environment : Environment) (declaration : Name) :
    MetaM (Except Failure PredicateHandle) := do
  match declarationInfo environment declaration with
  | .error failure => return .error failure
  | .ok _ =>
      let term := mkConst declaration
      let actualType ← inferType term
      if actualType.hasMVar || actualType.hasFVar then
        return .error (.notUnaryPredicate declaration actualType)
      match ← unaryPredicateDomain? actualType with
      | some domain => return .ok { declaration, term, domain }
      | none => return .error (.notUnaryPredicate declaration actualType)

/--
Check the predicate domain and the selected problem's exact `accepts` projection
independently.  Both results come from Lean definitional equality; node hashes
remain observational search keys only.
-/
def predicateCompatibility (predicate : PredicateHandle) (problem : PresentedHandle) :
    MetaM PredicateCompatibility := do
  let problemDomain ← mkAppM ``PresentedProblem.Instance #[problem.term]
  let problemAccepts ← mkAppM ``PresentedProblem.accepts #[problem.term]
  return {
    domainDefEq := ← controlledDefEq predicate.domain problemDomain
    acceptsDefEq := ← controlledDefEq predicate.term problemAccepts
  }

/-- A predicate is an exact existing endpoint predicate only when both checks pass. -/
def predicateAcceptsDefEq (predicate : PredicateHandle) (problem : PresentedHandle) :
    MetaM Bool := do
  let compatibility ← predicateCompatibility predicate problem
  return compatibility.domainDefEq && compatibility.acceptsDefEq

/-- Resolve a presented-problem declaration which also passed registry type validation. -/
def validatedPresented (environment : Environment) (declaration : Name) :
    MetaM (Except Failure PresentedHandle) := do
  match ← presented environment declaration with
  | .error failure => return .error failure
  | .ok handle =>
      match validateAttributedDeclaration environment declaration with
      | some entry =>
          match entry.capability with
          | .presentedProblem => return .ok handle
          | _ => return .error (.notValidatedPresentedProblem declaration)
      | none => return .error (.notValidatedPresentedProblem declaration)

/-- Check a declaration against the exact native-membership type of the supplied source. -/
def nativeMembership (environment : Environment) (declaration : Name) (source : Expr) :
    MetaM (Except Failure Expr) := do
  match declarationInfo environment declaration with
  | .error failure => return .error failure
  | .ok _ =>
      let membership := mkConst declaration
      let actualType ← inferType membership
      let expectedType ← mkAppM ``NativeTMInNP #[source]
      unless ← controlledDefEq actualType expectedType do
        return .error (.invalidNativeMembership declaration source actualType)
      return .ok membership

/-- Find the first validated problem declaration definitionally equal to an endpoint. -/
def canonicalPresentedHandle? {environment : Environment}
    (entries : List (ValidatedEntry environment)) (endpoint : Expr) :
    MetaM (Option PresentedHandle) := do
  for entry in entries do
    match entry.capability with
    | .presentedProblem =>
        match ← presented environment entry.candidate with
        | .ok handle =>
            if ← controlledDefEq handle.term endpoint then
              return some handle
        | .error _ => pure ()
    | _ => pure ()
  return none

end ComplexityReduction.Agent.Hardness.InputGate
