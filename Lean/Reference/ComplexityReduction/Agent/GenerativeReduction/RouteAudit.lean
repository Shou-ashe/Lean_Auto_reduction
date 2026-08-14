/- Copyright (c) 2026. -/

import Lean.Elab.Command

/-!
Kernel-environment audit for benchmark route exclusions.

The command below checks the elaborated declaration dependency closure.  It is
stronger than scanning generated source text: aliases and wrapper lemmas cannot
hide a forbidden theorem from the audit.
-/

namespace ComplexityReduction.Agent.GenerativeReduction.RouteAudit

open Lean Elab Command

private def transitiveDependencies (root : Name) : CoreM NameSet := do
  let mut visited : NameSet := {}
  let mut pending : NameSet := {root}
  while !pending.isEmpty do
    let current := pending.min!
    pending := pending.erase current
    if !visited.contains current then
      visited := visited.insert current
      let information ← getConstInfo current
      for dependency in information.getUsedConstantsAsSet do
        if !visited.contains dependency then
          pending := pending.insert dependency
  return visited

syntax (name := generativeReductionAssertNotTransitiveDependency)
  "#generative_reduction_assert_not_transitive_dependency " ident str : command

elab_rules : command
  | `(#generative_reduction_assert_not_transitive_dependency $root:ident $forbidden:str) => do
      let rootName ← resolveGlobalConstNoOverload root
      let forbiddenName := forbidden.getString.toName
      let dependencies ← liftCoreM <| transitiveDependencies rootName
      if dependencies.contains forbiddenName then
        throwError "route audit rejected {rootName}: forbidden dependency {forbiddenName}"

end ComplexityReduction.Agent.GenerativeReduction.RouteAudit
