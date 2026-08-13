/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.PAlgorithms.ZeroOneValid
import ComplexityReduction.Domain.BooleanCSP.PAlgorithms.Horn
import ComplexityReduction.Domain.BooleanCSP.PAlgorithms.DualHorn
import ComplexityReduction.Domain.BooleanCSP.PAlgorithms.Bijunctive
import ComplexityReduction.Domain.BooleanCSP.PAlgorithms.Affine

/-!
The tractability side of Schaefer's dichotomy.

The six tractable classes (0-valid, 1-valid, Horn, dual-Horn, bijunctive,
affine) each admit a certified polynomial-time decision procedure.  The
0-valid and 1-valid cases are decided by the constant assignments; the other
four cases are packaged as exact algorithm contracts (unit propagation,
dual unit propagation, 2-SAT via implication components, and Gaussian
elimination over `𝔽₂`), each carrying its `PolyProg` and semantic
equivalence theorem.

`inP_of_schaefer_tractable` assembles these six witnesses into the full
tractability statement: every `Γ` in one of the six classes has
`NativeTMInP (cspOf Γ)`.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP
namespace PAlgorithms

open ComplexityReduction.Certificate

/-- The tractability direction of Schaefer's dichotomy.

A language `Γ` lying in one of the six tractable classes has a polynomial-time
`CSP(Γ)`: the 0-valid and 1-valid cases are decided by the constant
assignments, and the Horn, dual-Horn, bijunctive and affine cases by the
caller-supplied algorithm contracts.
-/
theorem inP_of_schaefer_tractable (Γ : Gamma)
    (hornAlgorithm : ∀ h : Γ.IsHorn, HornAlgorithm Γ h)
    (dualHornAlgorithm : ∀ h : Γ.IsDualHorn, DualHornAlgorithm Γ h)
    (bijunctiveAlgorithm : ∀ h : Γ.IsBijunctive, BijunctiveAlgorithm Γ h)
    (affineAlgorithm : ∀ h : Γ.IsAffine, AffineAlgorithm Γ h) :
    Γ.IsSchaeferTractable → NativeTMInP (cspOf Γ) := by
  intro h
  rcases h with h0 | h1 | hh | hd | hb | ha
  · exact zeroValid_inP Γ h0
  · exact oneValid_inP Γ h1
  · exact (hornAlgorithm hh).inP
  · exact (dualHornAlgorithm hd).inP
  · exact (bijunctiveAlgorithm hb).inP
  · exact (affineAlgorithm ha).inP

end PAlgorithms
end BooleanCSP
end Domain
end ComplexityReduction
