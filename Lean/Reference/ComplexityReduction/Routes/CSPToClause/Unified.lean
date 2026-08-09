/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Domain.BoolFiniteDomainCSPToStructuredCNF
import ComplexityReduction.Domain.BoolTableCSPToFiniteDomainAdapter
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first table-CSP to structured Clause/CNF route.

For each exact table language, the concrete table presentation first enters
the canonical generic finite-domain CSP hub through the reusable typed ingress
adapter.  The domain-owned Boolean finite-domain CSP gadget then performs the
faithful truth-table expansion into structured CNF, and the public target is
reached through an exact identity egress.  The final route is only the typed
composition of those three independently indexed components; it introduces no
source-to-target atom, legacy strict-logspace premise, or route-local machine.
-/

namespace ComplexityReduction
namespace Routes
namespace CSPToClause

open Certificate Encoding Program

noncomputable section

/-- The original table-CSP source endpoint for one exact table language. -/
abbrev originalCSPProblem (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : PresentedProblem :=
  Presentation.FiniteDomainCSPTable.presentedProblem Γ

/-- The canonical CSP hub is the generic finite-domain view of this table language. -/
abbrev cspHubProblem (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : PresentedProblem :=
  Domain.BoolTableCSPToFiniteDomainAdapter.hubProblem Γ

/-- The canonical structured Clause/CNF target endpoint. -/
abbrev clauseCNFTargetProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The public Clause/CNF target is the same canonical clause hub. -/
abbrev originalClauseCNFProblem : PresentedProblem :=
  clauseCNFTargetProblem

/-- Exact ingress request from a concrete table-CSP source to its canonical CSP hub. -/
abbrev CSPIngressRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ComponentRequest .ingress (originalCSPProblem Γ) (cspHubProblem Γ)

/-- Exact shared-gadget request from a table-CSP hub to the Clause/CNF hub. -/
abbrev SharedGadgetRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem

/-- Exact egress request from the canonical Clause/CNF hub to the public Clause/CNF endpoint. -/
abbrev ClauseCNFEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress clauseCNFTargetProblem originalClauseCNFProblem

/-- Exact request that fixes one final table-CSP-to-Clause/CNF endpoint pair only. -/
abbrev FinalCompositionRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ComponentRequest .finalComposition (originalCSPProblem Γ) originalClauseCNFProblem

/-- The unique ingress request for one exact table language. -/
def cspIngressRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CSPIngressRequest Γ :=
  .exact

/-- The unique shared-gadget request for the selected table language. -/
def sharedGadgetRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    SharedGadgetRequest Γ :=
  .exact

/-- The unique Clause/CNF egress request. -/
def clauseCNFEgressRequest : ClauseCNFEgressRequest :=
  .exact

/-- The final request fixes endpoints but creates no executable authority. -/
def finalCompositionRequest (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    FinalCompositionRequest Γ :=
  .exact

/-- Egress identity is available only because both complete Clause/CNF endpoints coincide. -/
theorem clauseCNFEgress_endpoints_eq :
    clauseCNFTargetProblem = originalClauseCNFProblem :=
  rfl

/-- The ingress request retains its exact language-indexed table-CSP endpoints. -/
theorem cspIngressRequest_endpoint_exact (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (cspIngressRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .ingress (originalCSPProblem Γ) (cspHubProblem Γ) from .exact) :=
  rfl

/-- The shared request retains its exact table-CSP and Clause/CNF hub endpoints. -/
theorem sharedGadgetRequest_endpoint_exact (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (sharedGadgetRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem from .exact) :=
  rfl

/-- The egress request retains its exact complete Clause/CNF endpoints. -/
theorem clauseCNFEgressRequest_endpoint_exact :
    clauseCNFEgressRequest.endpoint =
      (show Protocol.ComponentEndpoint .egress clauseCNFTargetProblem originalClauseCNFProblem from .exact) :=
  rfl

/-- The final request retains its exact concrete table-CSP and Clause/CNF endpoints. -/
theorem finalCompositionRequest_endpoint_exact (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (finalCompositionRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .finalComposition (originalCSPProblem Γ) originalClauseCNFProblem from .exact) :=
  rfl

/-- A concrete table-CSP source enters the canonical generic CSP hub only through this adapter. -/
noncomputable def ingress (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CertifiedReduction (originalCSPProblem Γ) (cspHubProblem Γ) :=
  Domain.BoolTableCSPToFiniteDomainAdapter.sourceAdapter Γ

/-- The public Clause/CNF target is reached from its hub through this identity egress. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_egress]
noncomputable def egress :
    CertifiedReduction clauseCNFTargetProblem originalClauseCNFProblem :=
  .refl clauseCNFTargetProblem

/-- The one reusable Boolean finite-domain CSP hub to structured-CNF gadget. -/
noncomputable abbrev sharedGadget
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem :=
  Domain.BoolFiniteDomainCSPToStructuredCNF.sharedGadget Γ

/-- The language-indexed source normalization adapter is accepted at its exact ingress request. -/
noncomputable def cspIngressResolution (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    Protocol.ComponentResolution .ingress (originalCSPProblem Γ) (cspHubProblem Γ) :=
  Protocol.ComponentResolver.accept (cspIngressRequest Γ) (ingress Γ)

/-- The Clause/CNF identity egress is accepted at its exact egress request. -/
noncomputable def clauseCNFEgressResolution :
    Protocol.ComponentResolution .egress clauseCNFTargetProblem originalClauseCNFProblem :=
  Protocol.ComponentResolver.accept clauseCNFEgressRequest egress

/-- The shared gadget has a canonical typed component outcome. -/
abbrev SharedGadgetResolution (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ComponentResolution .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem

/-- Accept the exact direct-TM-backed CSP-to-Clause/CNF shared gadget. -/
noncomputable def sharedGadgetResolution (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    SharedGadgetResolution Γ :=
  Protocol.ComponentResolver.accept (sharedGadgetRequest Γ) (sharedGadget Γ)

/-- The public route is exactly ingress, shared truth-table gadget, and identity egress. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CertifiedReduction (originalCSPProblem Γ) originalClauseCNFProblem :=
  CertifiedReduction.comp egress
    (CertifiedReduction.comp (sharedGadget Γ) (ingress Γ))

/-- Typed provenance records the independently owned ingress, gadget, egress, and composite. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CertifiedRouteProvenance (ingress Γ) (sharedGadget Γ) (.explicit egress) (finalRoute Γ) :=
  CertifiedRouteProvenance.explicitEgress (ingress Γ) (sharedGadget Γ) egress

/-- The final route has a generic resolver outcome indexed by its concrete table language. -/
abbrev RouteResolution (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ResolverOutcome (originalCSPProblem Γ) originalClauseCNFProblem

/-- The resolver composes the three accepted exact components. -/
noncomputable def resolveComponentRoute (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    RouteResolution Γ :=
  Protocol.ComponentResolver.composeIngressSharedEgress (finalCompositionRequest Γ)
    (cspIngressResolution Γ) (sharedGadgetResolution Γ) clauseCNFEgressResolution

/-- The ingress resolution stores exactly the language-indexed normalization certificate. -/
@[simp] theorem cspIngressResolution_exact (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    cspIngressResolution Γ = .accepted (ingress Γ) :=
  rfl

/-- The egress resolution stores exactly the Clause/CNF structural identity certificate. -/
@[simp] theorem clauseCNFEgressResolution_exact :
    clauseCNFEgressResolution = .accepted egress :=
  rfl

/-- The shared-gadget resolution stores exactly the domain-owned certificate. -/
@[simp] theorem sharedGadgetResolution_exact
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    sharedGadgetResolution Γ = .accepted (sharedGadget Γ) :=
  rfl

/-- The final certificate stores exactly the nested component program composition. -/
@[simp] theorem finalRoute_program
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (finalRoute Γ).program =
      PolyProg.comp egress.program
        (PolyProg.comp (sharedGadget Γ).program (ingress Γ).program) :=
  rfl

/-- Direct-TM evidence is definitionally compiled from the same final program. -/
@[simp] theorem finalRoute_directTM
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (finalRoute Γ).directTM = (finalRoute Γ).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (finalRoute Γ)

/-- All accepted component resolutions elaborate to precisely the final route. -/
@[simp] theorem resolveComponentRoute_exact
    (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    resolveComponentRoute Γ = .accepted (finalRoute Γ) :=
  rfl

end
end CSPToClause
end Routes
end ComplexityReduction
