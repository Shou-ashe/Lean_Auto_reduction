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

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def componentsPrefix : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && componentsPrefix expectedRest actualRest

private def nameInNamespace (name prefix : Name) : Bool :=
  componentsPrefix (nameComponents prefix) (nameComponents name)

private def theoremLike : ConstantInfo → Bool
  | .thmInfo .. => true
  | .axiomInfo .. => true
  | _ => false

private def parseNamespaceList (value : String) : List Name :=
  (value.splitOn ",").filterMap fun raw =>
    let normalized := raw.trimAscii.toString
    if normalized.isEmpty then none else some normalized.toName

syntax (name := generativeReductionAssertNotTransitiveDependency)
  "#generative_reduction_assert_not_transitive_dependency " ident str : command

syntax (name := generativeReductionAssertTransitiveDependency)
  "#generative_reduction_assert_transitive_dependency " ident str : command

syntax (name := generativeReductionAssertNoTransitiveTheoremsInNamespace)
  "#generative_reduction_assert_no_transitive_theorems_in_namespace " ident str str : command

elab_rules : command
  | `(#generative_reduction_assert_not_transitive_dependency $root:ident $forbidden:str) => do
      let rootName ← resolveGlobalConstNoOverload root
      let forbiddenName := forbidden.getString.toName
      let dependencies ← liftCoreM <| transitiveDependencies rootName
      if dependencies.contains forbiddenName then
        throwError "route audit rejected {rootName}: forbidden dependency {forbiddenName}"

  | `(#generative_reduction_assert_transitive_dependency $root:ident $required:str) => do
      let rootName ← resolveGlobalConstNoOverload root
      let requiredName := required.getString.toName
      let dependencies ← liftCoreM <| transitiveDependencies rootName
      if !dependencies.contains requiredName then
        throwError "final-use audit rejected {rootName}: missing dependency {requiredName}"

  | `(#generative_reduction_assert_no_transitive_theorems_in_namespace
        $root:ident $forbidden:str $allowed:str) => do
      let rootName ← resolveGlobalConstNoOverload root
      let forbiddenPrefix := forbidden.getString.toName
      let allowedPrefixes := parseNamespaceList allowed.getString
      let dependencies ← liftCoreM <| transitiveDependencies rootName
      let mut violations : NameSet := {}
      for dependency in dependencies do
        let isAllowed := allowedPrefixes.any fun prefix =>
          nameInNamespace dependency prefix
        if nameInNamespace dependency forbiddenPrefix && !isAllowed then
          let information ← getConstInfo dependency
          if theoremLike information then
            violations := violations.insert dependency
      if !violations.isEmpty then
        throwError
          "route audit rejected {rootName}: forbidden theorem dependency {violations.min!} under namespace {forbiddenPrefix}"

end ComplexityReduction.Agent.GenerativeReduction.RouteAudit
