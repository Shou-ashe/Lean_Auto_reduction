/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Regression.AggregateMissing
import ComplexityReduction.Agent.Hardness.Regression.Authoring
import ComplexityReduction.Agent.Hardness.Regression.GapClassifier
import ComplexityReduction.Agent.Hardness.Regression.NativeCookLevinAxiomGate
import ComplexityReduction.Agent.Hardness.Regression.Phase6
import ComplexityReduction.Agent.Hardness.Regression.ProgramIndexedAuthoring
import ComplexityReduction.Agent.Hardness.Regression.TargetCatalog
import ComplexityReduction.Agent.Hardness.Regression.TransportedHardness
import ComplexityReduction.Registry.Aggregate
import ComplexityReduction.Protocol.ClosedResolver
import Lean.Elab.Command

/-! Closed-resolver regressions for aggregate detection, reflexivity, and edge fallback. -/

namespace ComplexityReduction.Agent.Hardness.Regression

open Lean Elab Command Meta
open Encoding Certificate

private def alwaysSemantic : DecisionProblem where
  Instance := Bool
  isYes := fun _ => True

private def reflexiveSemantic : DecisionProblem where
  Instance := Bool
  isYes := fun value => value = value

private def finalOnlySource : PresentedProblem where
  semantic := alwaysSemantic
  representation := Encoding.StandardInstances.bool
  carrier_eq := rfl

private def finalOnlyTarget : PresentedProblem where
  semantic := reflexiveSemantic
  representation := Encoding.StandardInstances.bool
  carrier_eq := rfl

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
private def finalOnlyEdge : CertifiedReduction finalOnlySource finalOnlyTarget where
  program := .id Encoding.StandardInstances.bool
  correct := by
    intro value
    simp [finalOnlySource, finalOnlyTarget, alwaysSemantic, reflexiveSemantic,
      PresentedProblem.accepts, PresentedProblem.toSemanticInstance]

run_cmd do
  let environment ← getEnv
  unless Protocol.ClosedResolver.hasProductionAggregate environment do
    throwError "production aggregate was not detected in the regression environment"
  Command.liftTermElabM do
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``finalOnlySource) (mkConst ``finalOnlySource) with
    | .error failure =>
        throwError "reflexive path regression failed: {repr failure}"
    | .ok path =>
        unless path.atoms.isEmpty do
          throwError "reflexive path regression produced {path.atoms.length} atoms"
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``Routes.GraphToRoleGraph.originalSourceProblem)
        (mkConst ``Routes.GraphToRoleGraph.roleGraphTargetProblem) with
    | .error failure =>
        throwError "atomic-route regression failed: {repr failure}"
    | .ok path =>
        if path.atomicProvenance.any fun provenance =>
            provenance.role? == some .finalComposition then
          throwError "atomic-route regression selected a final-composition edge"
    match ← Protocol.ClosedResolver.resolvePathWithCatalog environment
        (mkConst ``Routes.GraphToRoleGraph.originalSourceProblem)
        (mkConst ``Routes.GraphToRoleGraph.roleGraphTargetProblem) .irComponents with
    | .error failure =>
        throwError "IR-component catalog regression failed: {repr failure}"
    | .ok path =>
        if path.atomicProvenance.any fun provenance =>
            provenance.role? == some .finalComposition then
          throwError "IR-component catalog selected a final-composition facade"
        unless path.atomicProvenance.any fun provenance =>
            provenance.role? == some .ingress do
          throwError "IR-component catalog did not retain the graph ingress"
        unless path.atomicProvenance.any fun provenance =>
            provenance.role? == some .sharedGadget do
          throwError "IR-component catalog did not retain the shared graph gadget"
    match ← Protocol.ClosedResolver.resolvePathWithCatalog environment
        (mkConst ``Routes.GraphToRoleGraph.originalSourceProblem)
        (mkConst ``Routes.GraphToRoleGraph.roleGraphTargetProblem) .flatAPI with
    | .error failure =>
        throwError "flat catalog regression failed: {repr failure}"
    | .ok path =>
        unless path.atomicProvenance.any fun provenance =>
            provenance.role? == some .finalComposition do
          throwError "flat catalog did not select the exact final facade"
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``finalOnlySource) (mkConst ``finalOnlyTarget) with
    | .error failure =>
        throwError "final-composition fallback regression failed: {repr failure}"
    | .ok path =>
        unless path.atomicProvenance.any fun provenance =>
            provenance.role? == some .finalComposition do
          throwError "final-composition fallback regression did not use its only edge"
    match ← Protocol.ClosedResolver.resolvePathWithCatalog environment
        (mkConst ``finalOnlySource) (mkConst ``finalOnlyTarget) .irComponents with
    | .ok _ =>
        throwError "IR-component catalog accepted a route available only as a final facade"
    | .error (.noRegistryPath _ _) => pure ()
    | .error failure =>
        throwError "IR-component final-only regression returned the wrong failure: {repr failure}"

end ComplexityReduction.Agent.Hardness.Regression
