/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Export
import ComplexityReduction.Registry.ParameterizedFamily
import ComplexityReduction.Routes.Production
import ComplexityReduction.Problems.Karp21.CNFMembership
import ComplexityReduction.Problems.Karp21.ChromaticMembership
import ComplexityReduction.Problems.Karp21.CliqueCoverThreeDimensionalMatchingMembership
import ComplexityReduction.Problems.Karp21.GraphMembership
import ComplexityReduction.Problems.Karp21.GraphMembershipVertexCover
import ComplexityReduction.Problems.Karp21.HamiltonianFeedbackMembership
import ComplexityReduction.Problems.Karp21.NumericMembership
import ComplexityReduction.Problems.Karp21.MaxCutMembership
import ComplexityReduction.Problems.Karp21.JobSequencingMembership
import ComplexityReduction.Problems.Karp21.KnapsackMaxCutBinaryMembership
import ComplexityReduction.Problems.Karp21.PartitionMembership
import ComplexityReduction.Problems.Karp21.ZeroOneIPSetPackingMembership
import ComplexityReduction.Problems.Karp21.SATMembership
import ComplexityReduction.Problems.Karp21.SetSystemMembership
import ComplexityReduction.Problems.Karp21.SetSystemHittingSetMembership
import ComplexityReduction.Problems.Karp21.SteinerTreeMembership

/-!
Production candidate manifest and registry exporter aggregate for `ComplexityReduction`.

This module is the designated scan endpoint.  It imports only concrete V2
candidate leaves whose transitive imports are free of legacy adapter,
descriptor, packet, provider, slot, boundary, and test surfaces.  Routes that
still rely on a legacy direct-TM compatibility adapter or an old source-tuple
assembly remain explicit diagnostic leaves and cannot be planner candidates.
Ordinary proof leaves must not import this aggregate.
-/

namespace ComplexityReduction
namespace Registry

/-- Scan the supplied environment and return only declarations accepted by V2 type validation. -/
def scan (environment : Lean.Environment) : List (ValidatedEntry environment) :=
  exportValidated environment

/--
Scan the same production environment for non-authoritative parameterized
reduction-family observations.  These observations are not validated entries
and cannot enter the trusted graph until a closed application is validated.
-/
def scanParameterizedReductionFamilies (environment : Lean.Environment) :
    List (ParameterizedReductionFamilyObservation environment) :=
  attributedParameterizedReductionFamilies environment

@[simp]
theorem scan_eq_exportValidated (environment : Lean.Environment) :
    scan environment = exportValidated environment :=
  rfl

@[simp]
theorem scanParameterizedReductionFamilies_eq_observations
    (environment : Lean.Environment) :
    scanParameterizedReductionFamilies environment =
      attributedParameterizedReductionFamilies environment :=
  rfl

end Registry
end ComplexityReduction
