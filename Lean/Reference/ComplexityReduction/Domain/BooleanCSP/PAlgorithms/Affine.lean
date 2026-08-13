/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Certificate.DeterministicP

/-!
Exact admission contract for an affine implementation.

The classical affine decision procedure solves the linear system over `𝔽₂`
formed by the affine constraints: each constraint is a linear equation
`x₁ ⊕ ⋯ ⊕ xₖ = c`, and the system is satisfiable exactly when Gaussian
elimination over `𝔽₂` reaches no contradictory row `0 = 1`.  Unlike a metadata
flag, an `AffineAlgorithm` contains the exact `PolyProg` and a semantic
equivalence theorem; a later Lean authoring stage can instantiate this
contract only after its program and proof elaborate.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.Certificate
open ComplexityReduction.Program

/-- An affine-specific certified executable, indexed by the finite Γ and class proof. -/
structure AffineAlgorithm (Γ : Gamma) (affine : Γ.IsAffine) where
  program : PolyProg (cspOf Γ).representation Encoding.StandardInstances.bool
  correct : ∀ formula, program.run formula = true ↔ (cspOf Γ).accepts formula

namespace AffineAlgorithm

/-- Forget the affine construction detail only after retaining its exact program and proof. -/
def toCertifiedPAlgorithm {Γ : Gamma} {affine : Γ.IsAffine}
    (algorithm : AffineAlgorithm Γ affine) : CertifiedPAlgorithm (cspOf Γ) where
  program := algorithm.program
  correct := algorithm.correct

/-- A complete affine executable closes the exact native P objective. -/
theorem inP {Γ : Gamma} {affine : Γ.IsAffine}
    (algorithm : AffineAlgorithm Γ affine) :
    NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm algorithm.toCertifiedPAlgorithm

/-- The polynomial-time theorem is derived from the stored exact program. -/
theorem polytime {Γ : Gamma} {affine : Γ.IsAffine}
    (algorithm : AffineAlgorithm Γ affine) :
    ComplexityReduction.TMPolyTimeMap (cspOf Γ).representation.encodedType
      ComplexityReduction.EncodedType.bool algorithm.program.run := by
  simpa [Encoding.StandardInstances.bool_encodedType] using algorithm.program.compileTM

end AffineAlgorithm

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
