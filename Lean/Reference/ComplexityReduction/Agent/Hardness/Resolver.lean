/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.ClosedResolver
import Lean.Elab.Term

/-! Exact final elaborator for hardness-agent artifacts. -/

namespace ComplexityReduction.Agent.Hardness.Resolver

open Lean Elab Term Meta

syntax (name := byHardnessResolver) "by_hardness_resolver" : term

@[term_elab byHardnessResolver]
def elabByHardnessResolver : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType?
    | throwErrorAt stx "by_hardness_resolver requires an expected TypedAutoReductionResult type"
  let expectedType ← instantiateMVars expectedType
  let normalized := (← whnf expectedType).consumeMData
  unless normalized.getAppFn.consumeMData.isConstOf
      ``Protocol.TypedAutoReductionResult do
    throwErrorAt stx "expected type is not Protocol.TypedAutoReductionResult"
  let #[request] := normalized.getAppArgs
    | throwErrorAt stx "malformed TypedAutoReductionResult expected type"
  match ← Protocol.ClosedResolver.resolveExactRequest (← getEnv) request with
  | .ok result => ensureHasType expectedType? result
  | .error failure =>
      throwErrorAt stx m!"hardness request could not be closed: {repr failure}"

end ComplexityReduction.Agent.Hardness.Resolver
