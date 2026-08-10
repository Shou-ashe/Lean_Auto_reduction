/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.ExactCoverToThreeDimensionalMatchingTM.TripleAssembly
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Presentation.ThreeDimensionalMatching

/-!
Exact direct-TM completion of the compact Exact-Cover-to-3DM reduction.

The legacy construction is guarded by two finite checks: source set-system
well-formedness and occurrence of every universe element in at least one source
set.  This module realizes both checks with standard direct-TM combinators,
dispatches to the executable compact core or the fixed no-instance, and exposes
an endpoint-exact `TMKarpReduction`.  It deliberately exports no hardness or
certified-reduction object.
-/

namespace ComplexityReduction
namespace Domain
namespace ExactCoverToThreeDimensionalMatchingTM
namespace Unified

open ComplexityReduction.Combinatorics
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ThreeDimensionalMatching
open Foundations TripleAssembly

/-- The canonical exact structured source endpoint. -/
abbrev sourceProblem : Encoding.PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

/-- The canonical exact structured target endpoint. -/
abbrev targetProblem : Encoding.PresentedProblem :=
  Presentation.ThreeDimensionalMatching.structuredProblem

/-- Enumerate precisely the source universe indices checked by the guard. -/
def universeIndicesExecutable (I : ExactCoverInput) : List Nat :=
  List.range I.system.universeSize

theorem universeIndicesExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType
      (EncodedType.list EncodedType.nat) universeIndicesExecutable := by
  have composed := TMPolyTimeMap.comp natRange_tm_polytime
    universeSizeExecutable_tmPolyTime
  simpa [universeIndicesExecutable, Function.comp] using composed

/-- Boolean realization of `compactEveryElementOccurs`. -/
def everyElementOccursBool (I : ExactCoverInput) : Bool :=
  Program.ContextListAll.executable
    (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
    elementOccursBool
    (I, universeIndicesExecutable I)

theorem everyElementOccursBool_eq_true_iff (I : ExactCoverInput) :
    everyElementOccursBool I = true ↔ compactEveryElementOccurs I := by
  rw [everyElementOccursBool,
    Program.ContextListAll.executable_eq_true_iff]
  constructor
  · intro all x xBound
    exact (elementOccursBool_eq_true_iff I x).1
      (all x (by
        change x ∈ List.range I.system.universeSize
        exact List.mem_range.mpr xBound))
  · intro every x xMember
    change Nat at x
    have xBound : x < I.system.universeSize := by
      exact List.mem_range.mp xMember
    exact (elementOccursBool_eq_true_iff I x).2 (every x xBound)

theorem everyElementOccursBool_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.bool
      everyElementOccursBool := by
  let X := exactCoverStructuredEncodedType
  let N := EncodedType.list EncodedType.nat
  have indices : TMPolyTimeMap X N universeIndicesExecutable := by
    simpa [X, N] using universeIndicesExecutable_tmPolyTime
  have packed : TMPolyTimeMap X (EncodedType.prod X N)
      (fun I : X.Carrier => (I, universeIndicesExecutable I)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) indices
  have all := Program.ContextListAll.executable_tmPolyTime
    (C := exactCoverStructuredEncodedType) (X := EncodedType.nat)
    elementOccursBool elementOccursBool_tmPolyTime
  have composed := TMPolyTimeMap.comp all packed
  simpa [everyElementOccursBool, Function.comp, X, N] using composed

/-- Executable conjunction matching the legacy compact-map guard exactly. -/
def compactMapGuardBool (I : ExactCoverInput) : Bool :=
  Karp21.SteinerTree.exactCoverWellFormedBool I && everyElementOccursBool I

theorem compactMapGuardBool_eq_true_iff (I : ExactCoverInput) :
    compactMapGuardBool I = true ↔
      SetSystemWellFormed I.system ∧ compactEveryElementOccurs I := by
  simp [compactMapGuardBool, Bool.and_eq_true,
    Karp21.SteinerTree.exactCoverWellFormedBool_eq_true_iff,
    everyElementOccursBool_eq_true_iff]

theorem compactMapGuardBool_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType EncodedType.bool
      compactMapGuardBool := by
  let X := exactCoverStructuredEncodedType
  have wellFormed : TMPolyTimeMap X EncodedType.bool
      Karp21.SteinerTree.exactCoverWellFormedBool := by
    simpa [X] using Karp21.SteinerTree.exactCoverWellFormedBool_tm_polytime
  have every : TMPolyTimeMap X EncodedType.bool everyElementOccursBool := by
    simpa [X] using everyElementOccursBool_tmPolyTime
  have checks : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun I : X.Carrier =>
        (Karp21.SteinerTree.exactCoverWellFormedBool I,
          everyElementOccursBool I)) :=
    TMPolyTimeMap.prod_mk wellFormed every
  have composed := TMPolyTimeMap.comp Program.ContextListAll.boolAnd_tmPolyTime checks
  simpa [compactMapGuardBool, Program.ContextListAll.boolAnd, Function.comp, X]
    using composed

/-- Total executable, endpoint-exact replacement for the legacy `compactMap`. -/
def compactMapExecutable (I : ExactCoverInput) : ThreeDimensionalMatchingInput :=
  match compactMapGuardBool I with
  | true => compactMapCoreExecutable I
  | false => noInput

theorem compactMapExecutable_eq_legacy (I : ExactCoverInput) :
    compactMapExecutable I = compactMap I := by
  classical
  by_cases guard : SetSystemWellFormed I.system ∧ compactEveryElementOccurs I
  · have guardBool : compactMapGuardBool I = true :=
      (compactMapGuardBool_eq_true_iff I).2 guard
    simp [compactMapExecutable, guardBool, compactMap, guard,
      compactMapCoreExecutable_eq_legacy]
  · have guardBool : compactMapGuardBool I = false := by
      cases value : compactMapGuardBool I with
      | false => rfl
      | true =>
          exact False.elim (guard ((compactMapGuardBool_eq_true_iff I).1 value))
    simp [compactMapExecutable, guardBool, compactMap, guard]

theorem compactMapExecutable_tmPolyTime :
    TMPolyTimeMap exactCoverStructuredEncodedType
      threeDimensionalMatchingStructuredEncodedType compactMapExecutable := by
  let X := exactCoverStructuredEncodedType
  let Y := threeDimensionalMatchingStructuredEncodedType
  have guard : TMPolyTimeMap X EncodedType.bool compactMapGuardBool := by
    simpa [X] using compactMapGuardBool_tmPolyTime
  have core : TMPolyTimeMap X Y compactMapCoreExecutable := by
    simpa [X, Y] using compactMapCoreExecutable_tmPolyTime
  have no : TMPolyTimeMap X Y (fun _ : X.Carrier => noInput) :=
    TMPolyTimeMap.const X Y noInput
  have tagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun I : X.Carrier => (compactMapGuardBool I, I)) :=
    TMPolyTimeMap.prod_mk guard (TMPolyTimeMap.id X)
  have branch := boolProduct_dispatch_tm_polytime X Y
    (fFalse := fun _ : X.Carrier => noInput)
    (fTrue := compactMapCoreExecutable) no core
  have composed := TMPolyTimeMap.comp branch tagged
  simpa [compactMapExecutable, Function.comp, X, Y] using composed

/-- Exact-endpoint direct-TM reduction for public authoring admission. -/
noncomputable def exactCoverToThreeDimensionalMatchingStructuredTMKarpReduction :
    TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem where
  f := compactMapExecutable
  polytime := by
    simpa [sourceProblem, targetProblem,
      Presentation.SetSystem.exactCoverStructuredProblem,
      Presentation.SetSystem.exactCoverStructuredPresentation,
      Presentation.ThreeDimensionalMatching.structuredProblem,
      Presentation.ThreeDimensionalMatching.structuredPresentation] using
      compactMapExecutable_tmPolyTime
  correct := by
    intro I
    change ExactCover I ↔ ThreeDimensionalMatching (compactMapExecutable I)
    rw [compactMapExecutable_eq_legacy]
    exact compactMap_correct I

assert_standard_axioms
  universeIndicesExecutable_tmPolyTime,
  everyElementOccursBool_eq_true_iff,
  everyElementOccursBool_tmPolyTime,
  compactMapGuardBool_eq_true_iff,
  compactMapGuardBool_tmPolyTime,
  compactMapExecutable_eq_legacy,
  compactMapExecutable_tmPolyTime,
  exactCoverToThreeDimensionalMatchingStructuredTMKarpReduction

end Unified
end ExactCoverToThreeDimensionalMatchingTM
end Domain
end ComplexityReduction
