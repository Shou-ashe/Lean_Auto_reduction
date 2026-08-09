/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Elab.Command

/-!
Compile-time standard-axiom gates for trusted regression leaves.

This module inspects only elaborated declaration names selected by Lean source;
it has no route, registry, or manifest input and cannot create a capability.
-/

namespace ComplexityReduction
namespace AxiomGate

open Lean Elab Command

/-- The sole foundational proof axioms accepted by trusted-boundary regressions. -/
def standardAxiomAllowlist : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Fail when an audited declaration's transitive proof basis escapes the standard allowlist. -/
def assertStandardAxiomBasis (declaration : Name) : CommandElabM Unit := do
  for axiomName in ← Lean.collectAxioms declaration do
    unless standardAxiomAllowlist.contains axiomName do
      throwError "axiom gate rejected {declaration}: forbidden axiom {axiomName}"

/-- Check source-resolved declarations against the standard axiom allowlist. -/
syntax "assert_standard_axioms " ident,* : command

elab_rules : command
  | `(assert_standard_axioms $declarations:ident,*) => do
      for declarationSyntax in declarations.getElems do
        let declaration ← resolveGlobalConstNoOverload declarationSyntax
        assertStandardAxiomBasis declaration

/-- Compatibility spelling retained for existing library leaves. -/
syntax "assert_v2_standard_axioms " ident,* : command

elab_rules : command
  | `(assert_v2_standard_axioms $declarations:ident,*) => do
      for declarationSyntax in declarations.getElems do
        let declaration ← resolveGlobalConstNoOverload declarationSyntax
        assertStandardAxiomBasis declaration

end AxiomGate
end ComplexityReduction
