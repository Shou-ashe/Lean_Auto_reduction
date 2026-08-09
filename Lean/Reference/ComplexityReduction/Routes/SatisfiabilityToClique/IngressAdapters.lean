/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Routes.SatisfiabilityToClique.Unified
import ComplexityReduction.Routes.ThreeSATToCNF.Unified
import ComplexityReduction.Routes.TwoCNFToCNF.Unified

/-!
Clause-family ingress compositions for the canonical CNF-SAT-to-Clique shared
gadget.

Direct 2CNF and bundled 3SAT already have exact typed normalizations into the
canonical CNF-SAT hub.  This module merely composes each existing ingress with
the one existing CNF-SAT-to-Clique shared certificate.  It owns no primitive,
new executable, TM, cost witness, or whole-route construction.
-/

namespace ComplexityReduction
namespace Routes
namespace SatisfiabilityToClique
namespace IngressAdapters

open Certificate Encoding Program

/-- The stable Clause/CNF hub shared by both concrete source adapters. -/
abbrev clauseCNFHubProblem : PresentedProblem :=
  SatisfiabilityToClique.cnfSATHubProblem

/-- The exact canonical Clique target reached by the shared gadget. -/
abbrev cliqueTargetProblem : PresentedProblem :=
  SatisfiabilityToClique.originalCliqueProblem

/-- Direct 2CNF is a concrete ingress source, never a CNF-to-Clique gadget endpoint. -/
abbrev twoCNFSourceProblem : PresentedProblem :=
  TwoCNFToCNF.originalTwoCNFProblem

/-- Bundled 3SAT is a distinct concrete ingress source, never a CNF-to-Clique gadget endpoint. -/
abbrev threeSATSourceProblem : PresentedProblem :=
  ThreeSATToCNF.originalThreeSATProblem

/-- The 2CNF normalization target is definitionally the canonical Clause/CNF hub. -/
theorem twoCNF_target_eq_clauseCNFHub :
    TwoCNFToCNF.clauseCNFHubProblem = clauseCNFHubProblem :=
  rfl

/-- The bundled-3SAT normalization target is definitionally the same Clause/CNF hub. -/
theorem threeSAT_target_eq_clauseCNFHub :
    ThreeSATToCNF.cnfSATHubProblem = clauseCNFHubProblem :=
  rfl

/-- Exact ingress request for the already-certified direct-2CNF normalization. -/
abbrev TwoCNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress twoCNFSourceProblem clauseCNFHubProblem

/-- Exact ingress request for the already-certified bundled-3SAT normalization. -/
abbrev ThreeSATIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress threeSATSourceProblem clauseCNFHubProblem

/-- The 2CNF source asks only for its existing normalization component. -/
def twoCNFIngressRequest : TwoCNFIngressRequest :=
  .exact

/-- The bundled-3SAT source asks only for its existing normalization component. -/
def threeSATIngressRequest : ThreeSATIngressRequest :=
  .exact

/-- Reuse the exact direct-2CNF normalization declaration as the first ingress ID. -/
noncomputable abbrev twoCNFIngress : CertifiedReduction twoCNFSourceProblem clauseCNFHubProblem :=
  TwoCNFToCNF.certifiedReduction

/-- Reuse the exact bundled-3SAT normalization declaration as the second ingress ID. -/
noncomputable abbrev threeSATIngress : CertifiedReduction threeSATSourceProblem clauseCNFHubProblem :=
  ThreeSATToCNF.certifiedReduction

/-- The 2CNF ingress is accepted only at its exact source/hub endpoint. -/
noncomputable def twoCNFIngressResolution :
    Protocol.ComponentResolution .ingress twoCNFSourceProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept twoCNFIngressRequest twoCNFIngress

/-- The bundled-3SAT ingress is accepted only at its distinct exact source/hub endpoint. -/
noncomputable def threeSATIngressResolution :
    Protocol.ComponentResolution .ingress threeSATSourceProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept threeSATIngressRequest threeSATIngress

/-- The downstream shared resolution is the one already owned by CNF-SAT-to-Clique. -/
noncomputable abbrev sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget clauseCNFHubProblem cliqueTargetProblem :=
  SatisfiabilityToClique.satisfiabilityToCliqueSharedGadgetResolution

/-- The direct-2CNF public route is only ingress followed by the existing shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def twoCNFToCliqueFinalRoute :
    CertifiedReduction twoCNFSourceProblem cliqueTargetProblem :=
  CertifiedReduction.comp SatisfiabilityToClique.sharedGadget twoCNFIngress

/-- The bundled-3SAT public route is only its ingress followed by that same shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def threeSATToCliqueFinalRoute :
    CertifiedReduction threeSATSourceProblem cliqueTargetProblem :=
  CertifiedReduction.comp SatisfiabilityToClique.sharedGadget threeSATIngress

/-- Provenance fixes the first concrete ingress and the common downstream gadget. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def twoCNFToCliqueFinalRouteProvenance :
    CertifiedRouteProvenance TwoCNFToCNF.certifiedReduction
      SatisfiabilityToClique.sharedGadget .identity twoCNFToCliqueFinalRoute :=
  CertifiedRouteProvenance.identityEgress TwoCNFToCNF.certifiedReduction
    SatisfiabilityToClique.sharedGadget

/-- Provenance fixes the second concrete ingress and the same downstream gadget. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def threeSATToCliqueFinalRouteProvenance :
    CertifiedRouteProvenance ThreeSATToCNF.certifiedReduction
      SatisfiabilityToClique.sharedGadget .identity threeSATToCliqueFinalRoute :=
  CertifiedRouteProvenance.identityEgress ThreeSATToCNF.certifiedReduction
    SatisfiabilityToClique.sharedGadget

/-- Both final programs are definitionally the required component compositions. -/
@[simp] theorem twoCNFToCliqueFinalRoute_program :
    twoCNFToCliqueFinalRoute.program =
      PolyProg.comp SatisfiabilityToClique.sharedGadget.program twoCNFIngress.program :=
  rfl

@[simp] theorem threeSATToCliqueFinalRoute_program :
    threeSATToCliqueFinalRoute.program =
      PolyProg.comp SatisfiabilityToClique.sharedGadget.program threeSATIngress.program :=
  rfl

/-- Direct-TM evidence for each final route is compiled from its composite program. -/
@[simp] theorem twoCNFToCliqueFinalRoute_directTM :
    twoCNFToCliqueFinalRoute.directTM = twoCNFToCliqueFinalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM twoCNFToCliqueFinalRoute

@[simp] theorem threeSATToCliqueFinalRoute_directTM :
    threeSATToCliqueFinalRoute.directTM = threeSATToCliqueFinalRoute.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM threeSATToCliqueFinalRoute

/-- The two concrete paths resolve through their exact ingress and one common shared component. -/
noncomputable def resolveTwoCNFToClique :
    Protocol.ResolverOutcome twoCNFSourceProblem cliqueTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage sharedGadgetResolution twoCNFIngressResolution

noncomputable def resolveThreeSATToClique :
    Protocol.ResolverOutcome threeSATSourceProblem cliqueTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage sharedGadgetResolution threeSATIngressResolution

@[simp] theorem twoCNFIngressResolution_exact :
    twoCNFIngressResolution = .accepted twoCNFIngress :=
  rfl

@[simp] theorem threeSATIngressResolution_exact :
    threeSATIngressResolution = .accepted threeSATIngress :=
  rfl

@[simp] theorem resolveTwoCNFToClique_exact :
    resolveTwoCNFToClique = .accepted twoCNFToCliqueFinalRoute :=
  rfl

@[simp] theorem resolveThreeSATToClique_exact :
    resolveThreeSATToClique = .accepted threeSATToCliqueFinalRoute :=
  rfl

end IngressAdapters
end SatisfiabilityToClique
end Routes
end ComplexityReduction
