/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Certificate.DeterministicP

/-!
Exact admission contract for a dual-Horn implementation.

The classical dual-Horn decision procedure is the dual of Horn unit
propagation: it computes the greatest model of the dual-Horn formula by
backward chaining, and the formula is satisfiable exactly when no contradiction
is reached.  Unlike a metadata flag, a `DualHornAlgorithm` contains the exact
`PolyProg` and a semantic equivalence theorem; a later Lean authoring stage can
instantiate this contract only after its program and proof elaborate.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.Certificate
open ComplexityReduction.Program

/-- A dual-Horn-specific certified executable, indexed by the finite Γ and class proof. -/
structure DualHornAlgorithm (Γ : Gamma) (dualHorn : Γ.IsDualHorn) where
  program : PolyProg (cspOf Γ).representation Encoding.StandardInstances.bool
  correct : ∀ formula, program.run formula = true ↔ (cspOf Γ).accepts formula

namespace DualHornAlgorithm

/-- Forget the dual-Horn construction detail only after retaining its exact program and proof. -/
def toCertifiedPAlgorithm {Γ : Gamma} {dualHorn : Γ.IsDualHorn}
    (algorithm : DualHornAlgorithm Γ dualHorn) : CertifiedPAlgorithm (cspOf Γ) where
  program := algorithm.program
  correct := algorithm.correct

/-- A complete dual-Horn executable closes the exact native P objective. -/
theorem inP {Γ : Gamma} {dualHorn : Γ.IsDualHorn}
    (algorithm : DualHornAlgorithm Γ dualHorn) :
    NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm algorithm.toCertifiedPAlgorithm

/-- The polynomial-time theorem is derived from the stored exact program. -/
theorem polytime {Γ : Gamma} {dualHorn : Γ.IsDualHorn}
    (algorithm : DualHornAlgorithm Γ dualHorn) :
    ComplexityReduction.TMPolyTimeMap (cspOf Γ).representation.encodedType
      ComplexityReduction.EncodedType.bool algorithm.program.run := by
  simpa [Encoding.StandardInstances.bool_encodedType] using algorithm.program.compileTM

end DualHornAlgorithm

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
