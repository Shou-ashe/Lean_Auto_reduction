/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.GraphTM
import ComplexityReduction.AxiomGate

/-!
Minimal trusted runtime for direct-new exact-edge benchmark authoring.

This module deliberately exposes only the typed program/certificate layer, the
generic direct-TM closure library imported by that layer, and the axiom gate.
It must not import a route, registry, resolver, problem catalog, benchmark
artifact, or generated reduction.  Endpoint declarations are imported by the
case-specific public wrapper instead.
-/

namespace ComplexityReduction
namespace Agent
namespace Hardness
namespace ExactEdgeRuntime

/-- A compile-time marker used by isolation probes to bind this minimal surface. -/
def routeFree : Bool := true

end ExactEdgeRuntime
end Hardness
end Agent
end ComplexityReduction
