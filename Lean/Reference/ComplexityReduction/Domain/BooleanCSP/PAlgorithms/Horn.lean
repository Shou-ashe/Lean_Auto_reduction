/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Certificate.DeterministicP

/-!
Exact admission contract for a Horn unit-propagation implementation.

Unlike a metadata flag, a `HornAlgorithm` contains the exact `PolyProg` and a
semantic equivalence theorem.  The Python Stage-Q runtime supplies the concrete
least-model forward-chaining implementation; a later Lean authoring stage can
instantiate this contract only after its program and proof elaborate.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.Certificate
open ComplexityReduction.Program

/-- A Horn-specific certified executable, indexed by the finite Γ and class proof. -/
structure HornAlgorithm (Γ : Gamma) (horn : Γ.IsHorn) where
  program : PolyProg (cspOf Γ).representation Encoding.StandardInstances.bool
  correct : ∀ formula, program.run formula = true ↔ (cspOf Γ).accepts formula

namespace HornAlgorithm

/-- Forget the Horn construction detail only after retaining its exact program and proof. -/
def toCertifiedPAlgorithm {Γ : Gamma} {horn : Γ.IsHorn}
    (algorithm : HornAlgorithm Γ horn) : CertifiedPAlgorithm (cspOf Γ) where
  program := algorithm.program
  correct := algorithm.correct

/-- A complete Horn executable closes the exact native P objective. -/
theorem inP {Γ : Gamma} {horn : Γ.IsHorn} (algorithm : HornAlgorithm Γ horn) :
    NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm algorithm.toCertifiedPAlgorithm

/-- The polynomial-time theorem is derived from the stored exact program. -/
theorem polytime {Γ : Gamma} {horn : Γ.IsHorn} (algorithm : HornAlgorithm Γ horn) :
    ComplexityReduction.TMPolyTimeMap (cspOf Γ).representation.encodedType
      ComplexityReduction.EncodedType.bool algorithm.program.run := by
  simpa [Encoding.StandardInstances.bool_encodedType] using algorithm.program.compileTM

end HornAlgorithm

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
