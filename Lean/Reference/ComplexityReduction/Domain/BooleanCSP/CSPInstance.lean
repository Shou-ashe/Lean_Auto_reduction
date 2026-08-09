/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.BooleanCSP.Gamma
import ComplexityReduction.Presentation.FiniteDomainCSPTable

/-! Class-level Boolean CSP instances and exact V2 presented problems. -/

namespace ComplexityReduction
namespace Domain
namespace BooleanCSP

open ComplexityReduction.CSP
open ComplexityReduction.Encoding

/-- Instances of `CSP(Γ)` are finite conjunctions of Γ constraints. -/
abbrev CSPInstance (Γ : Gamma) : Type := Formula Γ

/-- Assignment semantics for one exact Γ instance. -/
abbrev Satisfies {Γ : Gamma} (formula : CSPInstance Γ) (assignment : SAT.Assignment) : Prop :=
  Formula.Satisfies formula assignment

/-- Existential satisfiability of one exact Γ instance. -/
abbrev Satisfiable {Γ : Gamma} (formula : CSPInstance Γ) : Prop :=
  Formula.Satisfiable formula

/-- The problem class `CSP(Γ)`, not a single CSP instance. -/
noncomputable def cspOf (Γ : Gamma) : PresentedProblem :=
  Presentation.FiniteDomainCSPTable.presentedProblem Γ

@[simp]
theorem cspOf_accepts (Γ : Gamma) (formula : (cspOf Γ).Instance) :
    (cspOf Γ).accepts formula ↔ Satisfiable formula :=
  Iff.rfl

/-- `cspOf` retains the exact faithful class-level formula presentation. -/
@[simp]
theorem cspOf_representation (Γ : Gamma) :
    (cspOf Γ).representation =
      Presentation.FiniteDomainCSPTable.lawfulRepresentation Γ :=
  rfl

end BooleanCSP
end Domain
end ComplexityReduction
