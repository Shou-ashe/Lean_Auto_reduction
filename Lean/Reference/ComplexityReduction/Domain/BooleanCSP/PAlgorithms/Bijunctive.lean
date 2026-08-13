/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Certificate.DeterministicP

/-!
Exact admission contract for a bijunctive (2-SAT) implementation.

The classical bijunctive decision procedure decides the satisfiability of a
conjunction of binary clauses (2-SAT): it builds the implication graph, finds
its strongly connected components, and rejects the formula exactly when a
variable and its negation lie in the same component.  Unlike a metadata flag,
a `BijunctiveAlgorithm` contains the exact `PolyProg` and a semantic
equivalence theorem; a later Lean authoring stage can instantiate this
contract only after its program and proof elaborate.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.Certificate
open ComplexityReduction.Program

/-- A bijunctive-specific certified executable, indexed by the finite Γ and class proof. -/
structure BijunctiveAlgorithm (Γ : Gamma) (bijunctive : Γ.IsBijunctive) where
  program : PolyProg (cspOf Γ).representation Encoding.StandardInstances.bool
  correct : ∀ formula, program.run formula = true ↔ (cspOf Γ).accepts formula

namespace BijunctiveAlgorithm

/-- Forget the bijunctive construction detail only after retaining its exact program and proof. -/
def toCertifiedPAlgorithm {Γ : Gamma} {bijunctive : Γ.IsBijunctive}
    (algorithm : BijunctiveAlgorithm Γ bijunctive) : CertifiedPAlgorithm (cspOf Γ) where
  program := algorithm.program
  correct := algorithm.correct

/-- A complete bijunctive executable closes the exact native P objective. -/
theorem inP {Γ : Gamma} {bijunctive : Γ.IsBijunctive}
    (algorithm : BijunctiveAlgorithm Γ bijunctive) :
    NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm algorithm.toCertifiedPAlgorithm

/-- The polynomial-time theorem is derived from the stored exact program. -/
theorem polytime {Γ : Gamma} {bijunctive : Γ.IsBijunctive}
    (algorithm : BijunctiveAlgorithm Γ bijunctive) :
    ComplexityReduction.TMPolyTimeMap (cspOf Γ).representation.encodedType
      ComplexityReduction.EncodedType.bool algorithm.program.run := by
  simpa [Encoding.StandardInstances.bool_encodedType] using algorithm.program.compileTM

end BijunctiveAlgorithm

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
