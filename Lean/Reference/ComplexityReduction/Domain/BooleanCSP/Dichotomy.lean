/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP
import ComplexityReduction.Domain.BooleanCSP.Hardness.SchaeferHardness

/-!
Schaefer's dichotomy: the complete statement.

The dichotomy assembles the two directions proved across the Boolean CSP
development:

* *Tractability*: a language `Γ` in one of the six tractable classes
  (0-valid, 1-valid, Horn, dual-Horn, bijunctive, affine) has a polynomial-time
  `CSP(Γ)`, witnessed by the constant-assignment algorithms and the four
  algorithm contracts (`PAlgorithms.inP_of_schaefer_tractable`).
* *Hardness*: a language `Γ` with only nonempty relations outside the six
  classes has an NP-hard `CSP(Γ)`, witnessed by a primitive-positive
  interpretation of one certified hard core
  (`Hardness.nPHard_of_not_schaefer_tractable`).

`schaefer_dichotomy` states the dichotomy as an exact disjunction: every such
`Γ` is either in P or NP-hard.
-/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

open ComplexityReduction.Certificate

/-- Schaefer's dichotomy.

A finite Boolean constraint language `Γ` whose relations are all nonempty is
either polynomially decidable (when it lies in one of the six tractable
classes) or NP-hard (otherwise).  The P-side witnesses are supplied by the
caller through the four algorithm contracts; the NP-side witness is the
primitive-positive interpretation of a certified hard core.
-/
theorem schaefer_dichotomy (Γ : Gamma)
    (nonempty : ∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty)
    (witness : Hardness.HardCoreWitness Γ)
    (hornAlgorithm : ∀ h : Γ.IsHorn, PAlgorithms.HornAlgorithm Γ h)
    (dualHornAlgorithm : ∀ h : Γ.IsDualHorn, PAlgorithms.DualHornAlgorithm Γ h)
    (bijunctiveAlgorithm : ∀ h : Γ.IsBijunctive, PAlgorithms.BijunctiveAlgorithm Γ h)
    (affineAlgorithm : ∀ h : Γ.IsAffine, PAlgorithms.AffineAlgorithm Γ h) :
    NativeTMInP (cspOf Γ) ∨ NativeTMNPHard (cspOf Γ) := by
  by_cases h : Γ.IsSchaeferTractable
  · exact Or.inl (PAlgorithms.inP_of_schaefer_tractable Γ hornAlgorithm
      dualHornAlgorithm bijunctiveAlgorithm affineAlgorithm h)
  · exact Or.inr (Hardness.nPHard_of_not_schaefer_tractable Γ witness nonempty h)

end BooleanCSP
end Domain
end ComplexityReduction
