/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
The one V2 role vocabulary for reduction components.

Roles classify provenance, resolution requests, and read-only registry queries;
they never grant a computational capability.  Keeping this type below both
certificate and protocol layers lets an atomic certified path retain its role
without making generic certificates import the request protocol or Lean
environment annotations.
-/

namespace ComplexityReduction

/-- The architectural role of one exact reduction component. -/
inductive ReductionComponentRole where
  | ingress
  | sharedGadget
  | egress
  | finalComposition
  deriving DecidableEq, Repr

instance : ToString ReductionComponentRole where
  toString
    | .ingress => "ingress"
    | .sharedGadget => "sharedGadget"
    | .egress => "egress"
    | .finalComposition => "finalComposition"

end ComplexityReduction
