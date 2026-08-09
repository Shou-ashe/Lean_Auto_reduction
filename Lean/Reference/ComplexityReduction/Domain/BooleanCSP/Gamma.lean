/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Relation
import ComplexityReduction.Legacy.ComplexityReduction.CSP.Language

/-! Finite relation languages Γ and canonical set fingerprints. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

open ComplexityReduction.CSP

/-- A Γ is finite by construction: its relation symbols carry a `Fintype`. -/
abbrev Gamma : Type 1 := BoolLanguage

/-- Canonical order-free Γ identity; symbol enumeration and duplicate names are erased. -/
noncomputable def Gamma.fingerprint (Γ : Gamma) : Finset RelationFingerprint :=
  (Finset.univ : Finset Γ.Symbol).image fun symbol =>
    relationFingerprint (Γ.relationOf symbol)

/-- Every concrete relation symbol occurs in the exact Γ fingerprint. -/
theorem Gamma.relationFingerprint_mem (Γ : Gamma) (symbol : Γ.Symbol) :
    relationFingerprint (Γ.relationOf symbol) ∈ Γ.fingerprint := by
  classical
  exact Finset.mem_image.mpr ⟨symbol, Finset.mem_univ symbol, rfl⟩

/-- Class-level identity includes Γ and canonical structural restriction parameters. -/
structure ClassFingerprint where
  gamma : Finset RelationFingerprint
  structuralParameters : Finset (String × String)
  deriving DecidableEq

/-- Construct a class fingerprint only from the exact finite Γ. -/
noncomputable def Gamma.classFingerprint (Γ : Gamma)
    (structuralParameters : Finset (String × String) := ∅) : ClassFingerprint where
  gamma := Γ.fingerprint
  structuralParameters := structuralParameters

end BooleanCSP
end Domain
end ComplexityReduction
