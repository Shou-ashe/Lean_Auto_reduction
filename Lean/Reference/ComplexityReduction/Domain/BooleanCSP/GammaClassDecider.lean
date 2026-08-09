/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Classes

/-! Executable finite Γ class decisions and their reflection theorems. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

/-- All six class checks are retained; Γ may belong to more than one class. -/
structure GammaClassResult where
  zeroValid : Bool
  oneValid : Bool
  horn : Bool
  dualHorn : Bool
  bijunctive : Bool
  affine : Bool
  deriving DecidableEq, Repr

/-- Exhaustive finite-table class decider. -/
noncomputable def gammaClassDecider (Γ : Gamma) : GammaClassResult where
  zeroValid := decide Γ.IsZeroValid
  oneValid := decide Γ.IsOneValid
  horn := decide Γ.IsHorn
  dualHorn := decide Γ.IsDualHorn
  bijunctive := decide Γ.IsBijunctive
  affine := decide Γ.IsAffine

@[simp] theorem gammaClassDecider_zeroValid_iff (Γ : Gamma) :
    (gammaClassDecider Γ).zeroValid = true ↔ Γ.IsZeroValid := by
  simp [gammaClassDecider]

@[simp] theorem gammaClassDecider_oneValid_iff (Γ : Gamma) :
    (gammaClassDecider Γ).oneValid = true ↔ Γ.IsOneValid := by
  simp [gammaClassDecider]

@[simp] theorem gammaClassDecider_horn_iff (Γ : Gamma) :
    (gammaClassDecider Γ).horn = true ↔ Γ.IsHorn := by
  simp [gammaClassDecider]

@[simp] theorem gammaClassDecider_dualHorn_iff (Γ : Gamma) :
    (gammaClassDecider Γ).dualHorn = true ↔ Γ.IsDualHorn := by
  simp [gammaClassDecider]

@[simp] theorem gammaClassDecider_bijunctive_iff (Γ : Gamma) :
    (gammaClassDecider Γ).bijunctive = true ↔ Γ.IsBijunctive := by
  simp [gammaClassDecider]

@[simp] theorem gammaClassDecider_affine_iff (Γ : Gamma) :
    (gammaClassDecider Γ).affine = true ↔ Γ.IsAffine := by
  simp [gammaClassDecider]

/-- A positive decider bit is sound for the corresponding tractable disjunction. -/
theorem gammaClassDecider_sound (Γ : Gamma) :
    (gammaClassDecider Γ).zeroValid = true ∨
      (gammaClassDecider Γ).oneValid = true ∨
      (gammaClassDecider Γ).horn = true ∨
      (gammaClassDecider Γ).dualHorn = true ∨
      (gammaClassDecider Γ).bijunctive = true ∨
      (gammaClassDecider Γ).affine = true ↔ Γ.IsSchaeferTractable := by
  simp [Gamma.IsSchaeferTractable]

end BooleanCSP
end Domain
end ComplexityReduction
