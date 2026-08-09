/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Routes.ClauseToCSP.Unified
import ComplexityReduction.Routes.TwoCNFToCNF.Unified

/-!
Concrete Clause-family ingress adapters for the canonical bundled-3SAT hub.

Only ingress computation lives here.  Direct 2CNF first reuses its existing
normalization to structured CNF and then the shared CNF splitter; bundled 3SAT
is already the hub and therefore uses only a certified identity.  Both final
routes reuse `ClauseToCSP.sharedGadget` and `ClauseToCSP.egress` verbatim.
-/

namespace ComplexityReduction
namespace Routes
namespace ClauseToCSP
namespace IngressAdapters

open Certificate Encoding Program

/-- The stable bundled-3SAT hub shared by every adapter below. -/
abbrev clauseCNFHubProblem : PresentedProblem :=
  ClauseToCSP.clauseCNFHubProblem

/-- Structured CNF enters the shared bundled-3SAT hub. -/
abbrev cnfSourceProblem : PresentedProblem :=
  ClauseToCSP.originalClauseCNFProblem

/-- Direct 2CNF remains a source-only presentation. -/
abbrev twoCNFSourceProblem : PresentedProblem :=
  TwoCNFToCNF.originalTwoCNFProblem

/-- Bundled 3SAT is already the canonical shared hub. -/
abbrev threeSATSourceProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- All concrete adapters reuse the exact fixed-language CSP target. -/
noncomputable abbrev cspTargetProblem : PresentedProblem :=
  ClauseToCSP.originalCSPProblem

/-- Exact 2CNF ingress request to the bundled-3SAT hub. -/
abbrev TwoCNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress twoCNFSourceProblem clauseCNFHubProblem

/-- Exact structured-CNF ingress request to the bundled-3SAT hub. -/
abbrev CNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress cnfSourceProblem clauseCNFHubProblem

/-- Exact bundled-3SAT identity ingress request. -/
abbrev ThreeSATIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress threeSATSourceProblem clauseCNFHubProblem

/-- Final direct-2CNF composition request. -/
noncomputable abbrev TwoCNFToCSPFinalRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition twoCNFSourceProblem cspTargetProblem

/-- Final bundled-3SAT composition request. -/
noncomputable abbrev ThreeSATToCSPFinalRequest : Type 2 :=
  Protocol.ComponentRequest .finalComposition threeSATSourceProblem cspTargetProblem

def twoCNFIngressRequest : TwoCNFIngressRequest := .exact
def cnfIngressRequest : CNFIngressRequest := .exact
def threeSATIngressRequest : ThreeSATIngressRequest := .exact
noncomputable def twoCNFToCSPFinalRequest : TwoCNFToCSPFinalRequest := .exact
noncomputable def threeSATToCSPFinalRequest : ThreeSATToCSPFinalRequest := .exact

/-- Direct 2CNF reaches the hub only by composing the two existing ingress components. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def twoCNFIngress : CertifiedReduction twoCNFSourceProblem clauseCNFHubProblem :=
  CertifiedReduction.comp ClauseToCSP.ingress TwoCNFToCNF.certifiedReduction

/-- Structured CNF reuses the one Clause-family CNF splitter ingress. -/
noncomputable abbrev cnfIngress : CertifiedReduction cnfSourceProblem clauseCNFHubProblem :=
  ClauseToCSP.ingress

/-- Bundled 3SAT is the hub, so its only adapter is the typed identity. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def threeSATIngress :
    CertifiedReduction threeSATSourceProblem clauseCNFHubProblem :=
  .refl clauseCNFHubProblem

noncomputable def twoCNFIngressResolution :
    Protocol.ComponentResolution .ingress twoCNFSourceProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept twoCNFIngressRequest twoCNFIngress

noncomputable def cnfIngressResolution :
    Protocol.ComponentResolution .ingress cnfSourceProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept cnfIngressRequest cnfIngress

noncomputable def threeSATIngressResolution :
    Protocol.ComponentResolution .ingress threeSATSourceProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept threeSATIngressRequest threeSATIngress

/-- Direct 2CNF final route reuses the exact canonical shared CSP gadget and egress. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def twoCNFToCSPRoute : CertifiedReduction twoCNFSourceProblem cspTargetProblem :=
  CertifiedReduction.comp ClauseToCSP.egress
    (CertifiedReduction.comp ClauseToCSP.sharedGadget twoCNFIngress)

/-- Bundled 3SAT final route reuses the exact canonical shared CSP gadget and egress. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def threeSATToCSPRoute : CertifiedReduction threeSATSourceProblem cspTargetProblem :=
  CertifiedReduction.comp ClauseToCSP.egress
    (CertifiedReduction.comp ClauseToCSP.sharedGadget threeSATIngress)

/-- Typed provenance fixes the direct-2CNF ingress and shared CSP path in the declaration type. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def twoCNFToCSPRouteProvenance :
    CertifiedRouteProvenance twoCNFIngress Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget
      (.explicit ClauseToCSP.egress) twoCNFToCSPRoute :=
  CertifiedRouteProvenance.explicitEgress twoCNFIngress
    Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget ClauseToCSP.egress

/-- Typed provenance fixes the bundled-3SAT ingress and the same shared CSP path. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def threeSATToCSPRouteProvenance :
    CertifiedRouteProvenance threeSATIngress Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget
      (.explicit ClauseToCSP.egress) threeSATToCSPRoute :=
  CertifiedRouteProvenance.explicitEgress threeSATIngress
    Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget ClauseToCSP.egress

/-- Each public adapter resolver composes its ingress with the shared accepted components. -/
noncomputable def twoCNFToCSPResolution :
    Protocol.ResolverOutcome twoCNFSourceProblem cspTargetProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress twoCNFToCSPFinalRequest
    twoCNFIngressResolution ClauseToCSP.sharedGadgetResolution ClauseToCSP.cspEgressResolution

noncomputable def threeSATToCSPResolution :
    Protocol.ResolverOutcome threeSATSourceProblem cspTargetProblem :=
  Protocol.ComponentResolver.composeIngressSharedEgress threeSATToCSPFinalRequest
    threeSATIngressResolution ClauseToCSP.sharedGadgetResolution ClauseToCSP.cspEgressResolution

@[simp] theorem twoCNFIngressResolution_exact :
    twoCNFIngressResolution = .accepted twoCNFIngress := rfl
@[simp] theorem cnfIngressResolution_exact :
    cnfIngressResolution = .accepted cnfIngress := rfl
@[simp] theorem threeSATIngressResolution_exact :
    threeSATIngressResolution = .accepted threeSATIngress := rfl
@[simp] theorem twoCNFToCSPResolution_exact :
    twoCNFToCSPResolution = .accepted twoCNFToCSPRoute := rfl
@[simp] theorem threeSATToCSPResolution_exact :
    threeSATToCSPResolution = .accepted threeSATToCSPRoute := rfl

@[simp] theorem twoCNFToCSPRoute_program :
    twoCNFToCSPRoute.program =
      PolyProg.comp ClauseToCSP.egress.program
        (PolyProg.comp ClauseToCSP.sharedGadget.program twoCNFIngress.program) := rfl
@[simp] theorem threeSATToCSPRoute_program :
    threeSATToCSPRoute.program =
      PolyProg.comp ClauseToCSP.egress.program
        (PolyProg.comp ClauseToCSP.sharedGadget.program threeSATIngress.program) := rfl

end IngressAdapters
end ClauseToCSP
end Routes
end ComplexityReduction
