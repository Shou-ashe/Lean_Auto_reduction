/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Routes.ThreeSATToClique.Unified
import ComplexityReduction.Protocol.ComponentResolver

/-!
Boolean-tagged structured-3SAT ingress for the existing 3SAT-to-Clique hub
gadget.

The tag is intentionally ignored by the source predicate.  This module owns
one structural `snd` ingress into the canonical structured-3SAT hub and the
thin final composition with the pre-existing shared gadget.  It introduces no
primitive, route-local TM, cost witness, or replacement 3SAT-to-Clique map.
-/

namespace ComplexityReduction
namespace Routes
namespace ThreeSATToClique
namespace IngressAdapters

open Annotations Certificate Encoding Program

/-- The exact canonical structured-3SAT hub reused by the tagged source. -/
abbrev threeSATHubProblem : PresentedProblem :=
  ThreeSATToClique.threeSATHubProblem

/-- The exact canonical structured-Clique target reused by the tagged source. -/
abbrev cliqueHubProblem : PresentedProblem :=
  ThreeSATToClique.cliqueHubProblem

/-- The tagged source keeps the Boolean codec and the complete original 3SAT codec identity. -/
abbrev taggedThreeSATPresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.bool threeSATHubProblem.representation

/-- The tagged carrier is definitionally a Boolean together with one structured 3SAT instance. -/
theorem taggedThreeSATPresentation_carrier :
    taggedThreeSATPresentation.Carrier = (Bool × threeSATHubProblem.Instance) :=
  rfl

/-- The tagged predicate deliberately ignores only the Boolean metadata field. -/
def taggedThreeSATProblemAt : ProblemAt taggedThreeSATPresentation where
  isYes := fun input => threeSATHubProblem.accepts input.2

/-- The concrete tagged source presentation is discoverable from its declaration type. -/
@[complexity_reduction_ir_typed_problem]
def taggedThreeSATProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt taggedThreeSATPresentation taggedThreeSATProblemAt

/-- The tagged source is indexed by exactly the product representation above. -/
@[simp] theorem taggedThreeSATProblem_representation :
    taggedThreeSATProblem.representation = taggedThreeSATPresentation :=
  rfl

/-- The source predicate is exactly the original hub predicate after erasing the tag. -/
@[simp] theorem taggedThreeSATProblem_accepts (input : taggedThreeSATProblem.Instance) :
    taggedThreeSATProblem.accepts input ↔ threeSATHubProblem.accepts input.2 :=
  Iff.rfl

/-- The sole executable introduced for the tagged source is the structural second projection. -/
def eraseTagProgram : PolyProg taggedThreeSATPresentation threeSATHubProblem.representation :=
  PolyProg.snd StandardInstances.bool threeSATHubProblem.representation

/-- The ingress program is definitionally the shared structural product projection. -/
@[simp] theorem eraseTagProgram_eq_snd :
    eraseTagProgram = PolyProg.snd StandardInstances.bool threeSATHubProblem.representation :=
  rfl

/-- The projection executable discards exactly the Boolean metadata field. -/
@[simp] theorem eraseTagProgram_run (input : taggedThreeSATPresentation.Carrier) :
    eraseTagProgram.run input = input.2 :=
  rfl

/-- Direct-TM evidence is compilation of the same structural projection program. -/
@[simp] theorem eraseTagProgram_directTM :
    eraseTagProgram.compileTM =
      ComplexityReduction.TMPolyTimeMap.snd StandardInstances.bool.encodedType
        threeSATHubProblem.representation.encodedType :=
  rfl

/-- The structural projection preserves satisfiability because the tag has no semantic role. -/
theorem eraseTagProgram_correct (input : taggedThreeSATProblem.Instance) :
    taggedThreeSATProblem.accepts input ↔
      threeSATHubProblem.accepts (eraseTagProgram.run input) :=
  Iff.rfl

/-- The exact ingress request fixes the tagged source and canonical 3SAT hub. -/
abbrev TaggedThreeSATIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress taggedThreeSATProblem threeSATHubProblem

/-- The tagged source asks only for its structural ingress adapter. -/
def taggedThreeSATIngressRequest : TaggedThreeSATIngressRequest :=
  .exact

/-- The exact shared-gadget request is independent of the tagged source representation. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget threeSATHubProblem cliqueHubProblem

/-- The reused hub gadget is requested only at its canonical endpoints. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The sole tagged-source ingress certificate is indexed by its one projection program. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
def taggedIngress : CertifiedReduction taggedThreeSATProblem threeSATHubProblem where
  program := eraseTagProgram
  correct := eraseTagProgram_correct

/-- The ingress certificate stores exactly the structural projection program. -/
@[simp] theorem taggedIngress_program :
    taggedIngress.program = eraseTagProgram :=
  rfl

/-- The ingress direct-TM projection is compiled from that same program. -/
@[simp] theorem taggedIngress_directTM :
    taggedIngress.directTM = taggedIngress.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM taggedIngress

/-- The tagged ingress is accepted only at its exact component endpoint. -/
def taggedIngressResolution :
    Protocol.ComponentResolution .ingress taggedThreeSATProblem threeSATHubProblem :=
  Protocol.ComponentResolver.accept taggedThreeSATIngressRequest taggedIngress

/-- The existing 3SAT-to-Clique certificate is reused solely as the canonical shared gadget. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget threeSATHubProblem cliqueHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest ThreeSATToClique.sharedGadget

/-- The public tagged route is only the ingress/shared-gadget certificate composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def taggedFinalRoute :
    CertifiedReduction taggedThreeSATProblem ThreeSATToClique.originalCliqueProblem :=
  CertifiedReduction.comp ThreeSATToClique.sharedGadget taggedIngress

/-- Typed provenance fixes both components and the identity egress in the declaration type. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def taggedFinalRouteProvenance :
    CertifiedRouteProvenance taggedIngress ThreeSATToClique.sharedGadget .identity taggedFinalRoute :=
  CertifiedRouteProvenance.identityEgress taggedIngress ThreeSATToClique.sharedGadget

/-- The final executable is definitionally the required two-component program composition. -/
@[simp] theorem taggedFinalRoute_program :
    taggedFinalRoute.program =
      PolyProg.comp ThreeSATToClique.sharedGadget.program taggedIngress.program :=
  rfl

/-- The final direct-TM evidence is compiled only from that composite program. -/
@[simp] theorem taggedFinalRoute_directTM :
    taggedFinalRoute.directTM = taggedFinalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM taggedFinalRoute

/-- The resolver composes the tagged ingress with the same existing shared gadget. -/
noncomputable def resolveTaggedComponentPath :
    Protocol.ResolverOutcome taggedThreeSATProblem ThreeSATToClique.originalCliqueProblem :=
  Protocol.ComponentResolver.composeTwoStage sharedGadgetResolution taggedIngressResolution

/-- Both component resolutions are accepted without manufacturing a new gadget capability. -/
@[simp] theorem taggedIngressResolution_exact :
    taggedIngressResolution = .accepted taggedIngress :=
  rfl

/-- The shared-gadget resolution exposes exactly the pre-existing hub certificate. -/
@[simp] theorem sharedGadgetResolution_exact :
    sharedGadgetResolution = .accepted ThreeSATToClique.sharedGadget :=
  rfl

/-- The accepted final result is definitionally the thin tagged route. -/
@[simp] theorem resolveTaggedComponentPath_exact :
    resolveTaggedComponentPath = .accepted taggedFinalRoute :=
  rfl

end IngressAdapters
end ThreeSATToClique
end Routes
end ComplexityReduction
