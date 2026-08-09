/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Aggregate
import ComplexityReduction.Certificate.NativeCookLevin
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier
import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier

/-!
Hardness-agent registry environment.

The core production aggregate deliberately remains free of the trusted
Cook--Levin compatibility leaf.  Hardness discovery needs that native
completeness root together with the production problem, membership, and route
registry, so agent-facing exporters import this aggregate instead.
-/

namespace ComplexityReduction
namespace Registry

/--
Stable fingerprint of the exact elaborated declarations retained by one
validated hardness registry environment.

The candidate name and elaborated-type hash are the only inputs.  This is the
same algorithm historically used by the probe, problem catalog, and input
inspection exporters, now shared so their snapshots cannot drift.
-/
def registryFingerprint {environment : Lean.Environment}
    (entries : List (ValidatedEntry environment)) : String :=
  let payload := String.intercalate "|" <| entries.map fun entry =>
    s!"{entry.candidate}:{entry.elaboratedType.hash}"
  s!"lean:{payload.hash}"

/-- Fingerprint the complete validated registry visible in one environment. -/
def currentRegistryFingerprint (environment : Lean.Environment) : String :=
  registryFingerprint (exportValidated environment)

end Registry
end ComplexityReduction
