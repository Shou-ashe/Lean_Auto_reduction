/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.HardnessAggregate
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.InputInspection
import ComplexityReduction.Agent.Hardness.ProblemCatalog
import ComplexityReduction.Agent.Hardness.Probe
import ComplexityReduction.Agent.Hardness.Resolver
import ComplexityReduction.Agent.Hardness.NPHardResolver
import ComplexityReduction.Agent.Hardness.NPHardProbe
import ComplexityReduction.Agent.Hardness.TargetCatalog
import ComplexityReduction.AxiomGate

/-!
Trusted Lean runtime for deterministic hardness-agent probing and final certificate resolution.

The external runner may rank observational route IDs, but it supplies no theorem names to the
final elaborator. `by_hardness_resolver` reconstructs the exact result from the current environment.
-/
