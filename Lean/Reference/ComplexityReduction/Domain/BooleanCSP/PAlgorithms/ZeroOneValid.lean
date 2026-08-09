/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.CSPInstance
import ComplexityReduction.Domain.BooleanCSP.Classes
import ComplexityReduction.Certificate.DeterministicP

/-! Constant-assignment P witnesses for zero-valid and one-valid Γ. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.CSP
open ComplexityReduction.Certificate
open ComplexityReduction.Program

theorem satisfiable_of_zeroValid {Γ : Gamma} (valid : Γ.IsZeroValid)
    (formula : CSPInstance Γ) : Satisfiable formula := by
  refine ⟨fun _ => false, ?_⟩
  intro constraint _membership
  exact valid constraint.symbol

theorem satisfiable_of_oneValid {Γ : Gamma} (valid : Γ.IsOneValid)
    (formula : CSPInstance Γ) : Satisfiable formula := by
  refine ⟨fun _ => true, ?_⟩
  intro constraint _membership
  exact valid constraint.symbol

/-- Exact constant-true algorithm for every zero-valid finite Γ. -/
noncomputable def zeroValidAlgorithm (Γ : Gamma) (valid : Γ.IsZeroValid) :
    CertifiedPAlgorithm (cspOf Γ) where
  program := PolyProg.const (cspOf Γ).representation Encoding.StandardInstances.bool true
  correct := by
    intro formula
    constructor
    · intro _
      exact (cspOf_accepts Γ formula).2 (satisfiable_of_zeroValid valid formula)
    · intro _
      rfl

/-- Exact constant-true algorithm for every one-valid finite Γ. -/
noncomputable def oneValidAlgorithm (Γ : Gamma) (valid : Γ.IsOneValid) :
    CertifiedPAlgorithm (cspOf Γ) where
  program := PolyProg.const (cspOf Γ).representation Encoding.StandardInstances.bool true
  correct := by
    intro formula
    constructor
    · intro _
      exact (cspOf_accepts Γ formula).2 (satisfiable_of_oneValid valid formula)
    · intro _
      rfl

theorem zeroValid_inP (Γ : Gamma) (valid : Γ.IsZeroValid) : NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm (zeroValidAlgorithm Γ valid)

theorem oneValid_inP (Γ : Gamma) (valid : Γ.IsOneValid) : NativeTMInP (cspOf Γ) :=
  NativeTMInP.ofAlgorithm (oneValidAlgorithm Γ valid)

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
