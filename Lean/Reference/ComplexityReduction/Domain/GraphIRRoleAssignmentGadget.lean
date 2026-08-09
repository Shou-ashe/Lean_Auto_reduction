/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Domain.Core.RoleGraphIR
import ComplexityReduction.Protocol.ComponentResolver

/-!
Reusable canonical GraphIR-to-RoleGraphIR role-assignment gadget.

The executable is a closed structural `PolyProg`: it pairs the fixed
two-role cardinality with the exact incoming graph hub.  Consequently its
semantic law and direct-TM witness are indexed by that same program; no
route-local executable, TM, cost map, packet, or erased backend is used.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphIRRoleAssignmentGadget

open Certificate Encoding Program

abbrev sourceProblem : PresentedProblem :=
  GraphIR.wellFormedProblem

abbrev targetProblem : PresentedProblem :=
  RoleGraphIR.roleAssignedGraphProblem

abbrev SharedGadgetRequest (source target : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget source target

/-- The exact graph-hub-to-role-graph-hub shared-gadget request. -/
def request : SharedGadgetRequest sourceProblem targetProblem :=
  .exact

/-- The shared role-assignment program is entirely structural. -/
def roleAssignmentProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .pair
    (.const GraphIR.lawfulRepresentation StandardInstances.unaryNat (show Nat from 2))
    (.id GraphIR.lawfulRepresentation)

@[simp] theorem roleAssignmentProgram_run (input : sourceProblem.Instance) :
    roleAssignmentProgram.run input =
      RoleGraphIR.roleAssignment (show GraphIR from input) :=
  rfl

/-- The target role-graph contract is equivalent to graph-hub well-formedness on this output. -/
theorem roleAssignmentProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (roleAssignmentProgram.run input) := by
  change GraphIR.WellFormed (show GraphIR from input) ↔
    RoleGraphIR.IsRoleAssignedGraph
      (RoleGraphIR.roleAssignment (show GraphIR from input))
  constructor
  · exact RoleGraphIR.roleAssignment_isRoleAssignedGraph
  · intro assigned
    exact RoleGraphIR.graph_wellFormed_of_isRoleAssignedGraph assigned

/-- The one canonical shared role-assignment certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := roleAssignmentProgram
  correct := roleAssignmentProgram_correct

/-- Direct-TM evidence is compiled from precisely the stored shared-gadget program. -/
theorem sharedGadget_directTM :
    sharedGadget.directTM = roleAssignmentProgram.compileTM :=
  rfl

abbrev Resolution : Type 2 :=
  Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem

/-- The exact graph-hub shared-gadget request accepts only this certificate. -/
noncomputable def resolve : Resolution :=
  Protocol.ComponentResolver.accept request sharedGadget

@[simp] theorem resolve_exact : resolve = .accepted sharedGadget :=
  rfl

end GraphIRRoleAssignmentGadget
end Domain
end ComplexityReduction
