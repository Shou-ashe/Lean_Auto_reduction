/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.FiniteDomainCSP
import ComplexityReduction.Presentation.ExactlyOneNeighbor
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Domain.CNFToThreeSATStandardTM
import ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNF
import ComplexityReduction.Domain.GraphColoringToIncidenceGadget
import ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget
import ComplexityReduction.Domain.ThreeSATToGraphColoringStandardTM
import ComplexityReduction.Protocol.ComponentResolver

/-!
Component-first boundaries for finite-domain CSP routes.

For a fixed finite-domain language, the lawful formula presentation is the
canonical CSP hub itself.  Its ingress is therefore an exact endpoint identity.
The generic CSP-to-Clause component still needs an executable finite-domain
and relation-table contract: `CSPAtoms.formulaCode` serializes only relation
selectors and scopes, and cannot evaluate an extensional `Rel.holds`.

An explicit `ExecutableLanguageContract` closes a separate contract-bearing
CSP-to-Clause component and its composed EON route.  The caller-free APIs that
accept only a bare `Γ` remain blocked, preserving the constructive boundary
rather than silently tabulating `Rel.holds`.

The RoleGraph-family target is frozen here at the existential
Exactly-One-Neighbor endpoint actually reached by the accepted incidence
gadget.  The reusable structured-CNF-to-EON suffix is already a composition of
accepted V2 components.  Thus a future generic CSP-to-Clause certificate can
be extended to EON without a second CSP construction or an
existential-to-fixed-role identity fiction.

This leaf exposes the accepted contract-bearing paths, the accepted downstream
suffix, and the exact bare-language blockers.  It deliberately declares no
source-to-final primitive, route-local TM/cost proof, or route-local request
enum.
-/

namespace ComplexityReduction
namespace Routes
namespace FiniteDomainCSP

open ComplexityReduction.CSP.FiniteDomain
open Certificate Encoding
open Domain.FiniteDomainCSPExecutableContract

noncomputable section

/-- The original finite-domain CSP source at one exact language. -/
abbrev originalCSPProblem {D : Type} (Γ : Language D) : PresentedProblem :=
  Presentation.FiniteDomainCSP.presentedProblem Γ

/-- The canonical CSP hub currently has the exact same presented endpoint. -/
abbrev cspHubProblem {D : Type} (Γ : Language D) : PresentedProblem :=
  Presentation.FiniteDomainCSP.presentedProblem Γ

/-- The canonical structured Clause/CNF target endpoint. -/
abbrev clauseCNFTargetProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- The canonical existential Exactly-One-Neighbor target for this family. -/
abbrev existentialEONTargetProblem : PresentedProblem :=
  Presentation.ExactlyOneNeighbor.presentedProblem

/-- Compatibility spelling for the family target, now frozen at existential EON. -/
abbrev roleGraphTargetProblem : PresentedProblem :=
  existentialEONTargetProblem

/-- The family target is definitionally the existential EON endpoint. -/
theorem roleGraphTargetProblem_eq_existentialEON :
    roleGraphTargetProblem = Presentation.ExactlyOneNeighbor.presentedProblem :=
  rfl

/-- Exact ingress request from a source CSP presentation to its canonical hub. -/
abbrev CSPIngressRequest {D : Type} (Γ : Language D) : Type 2 :=
  Protocol.ComponentRequest .ingress (originalCSPProblem Γ) (cspHubProblem Γ)

/-- Ingress identity is available only because both language-indexed endpoints coincide. -/
theorem cspIngress_endpoints_eq {D : Type} (Γ : Language D) :
    originalCSPProblem Γ = cspHubProblem Γ :=
  rfl

/-- Exact request for the CSP-hub-to-Clause/CNF shared gadget. -/
abbrev ClauseSharedGadgetRequest {D : Type} (Γ : Language D) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem

/-- Exact request for the CSP-hub-to-RoleGraph shared gadget. -/
abbrev RoleGraphSharedGadgetRequest {D : Type} (Γ : Language D) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget (cspHubProblem Γ) roleGraphTargetProblem

/-- The unique language-indexed ingress request. -/
def cspIngressRequest {D : Type} (Γ : Language D) : CSPIngressRequest Γ := .exact

/-- The unique CSP-hub-to-Clause/CNF shared-gadget request. -/
def clauseSharedGadgetRequest {D : Type} (Γ : Language D) : ClauseSharedGadgetRequest Γ :=
  .exact

/-- The unique CSP-hub-to-RoleGraph shared-gadget request. -/
def roleGraphSharedGadgetRequest {D : Type} (Γ : Language D) :
    RoleGraphSharedGadgetRequest Γ :=
  .exact

/-- The ingress request retains its full language-indexed endpoint. -/
theorem cspIngressRequest_endpoint_exact {D : Type} (Γ : Language D) :
    (cspIngressRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .ingress (originalCSPProblem Γ) (cspHubProblem Γ) from
        .exact) :=
  rfl

/-- The Clause/CNF gadget request retains its exact CSP hub and target endpoints. -/
theorem clauseSharedGadgetRequest_endpoint_exact {D : Type} (Γ : Language D) :
    (clauseSharedGadgetRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem from
        .exact) :=
  rfl

/-- The RoleGraph gadget request retains its exact CSP hub and target endpoints. -/
theorem roleGraphSharedGadgetRequest_endpoint_exact {D : Type} (Γ : Language D) :
    (roleGraphSharedGadgetRequest Γ).endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget (cspHubProblem Γ) roleGraphTargetProblem from
        .exact) :=
  rfl

/-- The structural source adapter is identity only at the exact same CSP presentation. -/
noncomputable def ingress {D : Type} (Γ : Language D) :
    CertifiedReduction (originalCSPProblem Γ) (cspHubProblem Γ) :=
  .refl (cspHubProblem Γ)

/-! ### Accepted Clause/CNF-to-existential-EON suffix -/

/--
The canonical structured-CNF-to-EON suffix reuses the accepted CNF-to-3SAT,
3SAT-to-graph-colouring, graph-colouring-to-incidence, and incidence-to-EON
domain gadgets.  It introduces no new primitive or legacy adapter.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def clauseToExistentialEON :
  CertifiedReduction clauseCNFTargetProblem existentialEONTargetProblem :=
  CertifiedReduction.comp Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget
    (CertifiedReduction.comp Domain.GraphColoringToIncidenceGadget.sharedGadget
      (CertifiedReduction.comp Domain.ThreeSATToGraphColoringStandardTM.sharedGadget
        Domain.CNFToThreeSATStandardTM.sharedGadget))

/-- The accepted suffix stores exactly the three reused component programs. -/
@[simp] theorem clauseToExistentialEON_program :
    clauseToExistentialEON.program =
      Program.PolyProg.comp Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget.program
        (Program.PolyProg.comp Domain.GraphColoringToIncidenceGadget.sharedGadget.program
          (Program.PolyProg.comp Domain.ThreeSATToGraphColoringStandardTM.sharedGadget.program
            Domain.CNFToThreeSATStandardTM.sharedGadget.program)) :=
  rfl

/-- Its direct-TM witness is compiled from that same composite program. -/
@[simp] theorem clauseToExistentialEON_directTM :
    clauseToExistentialEON.directTM = clauseToExistentialEON.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM clauseToExistentialEON

/-- The reused suffix preserves the exact structured-CNF and existential-EON predicates. -/
theorem clauseToExistentialEON_correct (formula : clauseCNFTargetProblem.Instance) :
    clauseCNFTargetProblem.accepts formula ↔
      existentialEONTargetProblem.accepts (clauseToExistentialEON.program.run formula) :=
  clauseToExistentialEON.correct formula

/-- Exact shared-component request for the already closed Clause-to-EON suffix. -/
abbrev ClauseToEONSharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget clauseCNFTargetProblem existentialEONTargetProblem

/-- The unique Clause-to-EON suffix request. -/
def clauseToEONSharedGadgetRequest : ClauseToEONSharedGadgetRequest :=
  .exact

/-- The downstream suffix is accepted independently of any generic CSP contract. -/
noncomputable def clauseToEONSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget clauseCNFTargetProblem existentialEONTargetProblem :=
  Protocol.ComponentResolver.accept clauseToEONSharedGadgetRequest clauseToExistentialEON

@[simp] theorem clauseToEONSharedGadgetResolution_exact :
    clauseToEONSharedGadgetResolution = .accepted clauseToExistentialEON :=
  rfl

/--
Any lawful generic CSP-to-Clause shared gadget extends canonically to the
selected EON target by composition; no second generic relation lookup is
required.
-/
noncomputable def roleGraphSharedGadgetOfClause {D : Type} (Γ : Language D)
    (clauseGadget : CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem) :
    CertifiedReduction (cspHubProblem Γ) roleGraphTargetProblem :=
  CertifiedReduction.comp clauseToExistentialEON clauseGadget

@[simp] theorem roleGraphSharedGadgetOfClause_program {D : Type} (Γ : Language D)
    (clauseGadget : CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem) :
    (roleGraphSharedGadgetOfClause Γ clauseGadget).program =
      Program.PolyProg.comp clauseToExistentialEON.program clauseGadget.program :=
  rfl

@[simp] theorem roleGraphSharedGadgetOfClause_directTM {D : Type} (Γ : Language D)
    (clauseGadget : CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem) :
    (roleGraphSharedGadgetOfClause Γ clauseGadget).directTM =
      (roleGraphSharedGadgetOfClause Γ clauseGadget).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (roleGraphSharedGadgetOfClause Γ clauseGadget)

/-- The identity ingress is accepted only at its exact component request. -/
noncomputable def cspIngressResolution {D : Type} (Γ : Language D) :
    Protocol.ComponentResolution .ingress (originalCSPProblem Γ) (cspHubProblem Γ) :=
  Protocol.ComponentResolver.accept (cspIngressRequest Γ) (ingress Γ)

/-! ### Accepted paths indexed by an explicit executable language contract -/

/--
An explicit executable domain/relation-table contract closes the exact generic
CSP-hub-to-structured-CNF component without changing the bare language-indexed
endpoint.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def clauseSharedGadgetWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem :=
  Domain.FiniteDomainCSPToStructuredCNF.sharedGadget contract

/-- The contract-bearing Clause gadget stores exactly the checked one-hot program. -/
@[simp] theorem clauseSharedGadgetWithContract_program {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (clauseSharedGadgetWithContract contract).program =
      Domain.FiniteDomainCSPToStructuredCNFProgram.formulaToCNFProgram contract :=
  rfl

/-- Its semantic law is the domain-owned program theorem at the exact endpoints. -/
theorem clauseSharedGadgetWithContract_correct {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (formula : (cspHubProblem Γ).Instance) :
    (cspHubProblem Γ).accepts formula ↔
      clauseCNFTargetProblem.accepts
        ((clauseSharedGadgetWithContract contract).program.run formula) :=
  (clauseSharedGadgetWithContract contract).correct formula

/-- Direct-TM evidence is compiled from the same stored one-hot program. -/
@[simp] theorem clauseSharedGadgetWithContract_directTM {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (clauseSharedGadgetWithContract contract).directTM =
      (clauseSharedGadgetWithContract contract).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (clauseSharedGadgetWithContract contract)

/-- The exact Clause component is accepted when its executable contract is supplied. -/
noncomputable def clauseSharedGadgetResolutionWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    Protocol.ComponentResolution .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem :=
  Protocol.ComponentResolver.accept (clauseSharedGadgetRequest Γ)
    (clauseSharedGadgetWithContract contract)

@[simp] theorem clauseSharedGadgetResolutionWithContract_exact
    {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ) :
    clauseSharedGadgetResolutionWithContract contract =
      .accepted (clauseSharedGadgetWithContract contract) :=
  rfl

/-- The final contract-bearing Clause route is only identity ingress plus the shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalClauseRouteWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedReduction (originalCSPProblem Γ) clauseCNFTargetProblem :=
  CertifiedReduction.comp (clauseSharedGadgetWithContract contract) (ingress Γ)

/-- Typed provenance records that the Clause target needs no separate egress. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalClauseRouteWithContractProvenance {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedRouteProvenance (ingress Γ) (clauseSharedGadgetWithContract contract)
      .identity (finalClauseRouteWithContract contract) :=
  CertifiedRouteProvenance.identityEgress (ingress Γ)
    (clauseSharedGadgetWithContract contract)

@[simp] theorem finalClauseRouteWithContract_program {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (finalClauseRouteWithContract contract).program =
      Program.PolyProg.comp (clauseSharedGadgetWithContract contract).program
        (ingress Γ).program :=
  rfl

theorem finalClauseRouteWithContract_correct {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (originalCSPProblem Γ).Instance) :
    (originalCSPProblem Γ).accepts formula ↔
      clauseCNFTargetProblem.accepts
        ((finalClauseRouteWithContract contract).program.run formula) :=
  (finalClauseRouteWithContract contract).correct formula

@[simp] theorem finalClauseRouteWithContract_directTM {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (finalClauseRouteWithContract contract).directTM =
      (finalClauseRouteWithContract contract).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (finalClauseRouteWithContract contract)

/-- The contract-bearing Clause resolver composes the two accepted exact components. -/
noncomputable def resolveClauseComponentPathWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    Protocol.ResolverOutcome (originalCSPProblem Γ) clauseCNFTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage
    (clauseSharedGadgetResolutionWithContract contract) (cspIngressResolution Γ)

@[simp] theorem resolveClauseComponentPathWithContract_exact
    {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ) :
    resolveClauseComponentPathWithContract contract =
      .accepted (finalClauseRouteWithContract contract) :=
  rfl

/--
The accepted CSP-hub-to-EON component is obtained solely by composing the
contract-bearing Clause gadget with the already accepted Clause-to-EON suffix.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def roleGraphSharedGadgetWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedReduction (cspHubProblem Γ) roleGraphTargetProblem :=
  roleGraphSharedGadgetOfClause Γ (clauseSharedGadgetWithContract contract)

@[simp] theorem roleGraphSharedGadgetWithContract_program {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (roleGraphSharedGadgetWithContract contract).program =
      Program.PolyProg.comp clauseToExistentialEON.program
        (clauseSharedGadgetWithContract contract).program :=
  rfl

theorem roleGraphSharedGadgetWithContract_correct {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) (formula : (cspHubProblem Γ).Instance) :
    (cspHubProblem Γ).accepts formula ↔
      roleGraphTargetProblem.accepts
        ((roleGraphSharedGadgetWithContract contract).program.run formula) :=
  (roleGraphSharedGadgetWithContract contract).correct formula

@[simp] theorem roleGraphSharedGadgetWithContract_directTM {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (roleGraphSharedGadgetWithContract contract).directTM =
      (roleGraphSharedGadgetWithContract contract).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (roleGraphSharedGadgetWithContract contract)

/-- The exact CSP-hub-to-EON component is accepted under the same explicit contract. -/
noncomputable def roleGraphSharedGadgetResolutionWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    Protocol.ComponentResolution .sharedGadget (cspHubProblem Γ) roleGraphTargetProblem :=
  Protocol.ComponentResolver.accept (roleGraphSharedGadgetRequest Γ)
    (roleGraphSharedGadgetWithContract contract)

@[simp] theorem roleGraphSharedGadgetResolutionWithContract_exact
    {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ) :
    roleGraphSharedGadgetResolutionWithContract contract =
      .accepted (roleGraphSharedGadgetWithContract contract) :=
  rfl

/-- The final contract-bearing EON route remains a thin ingress/shared composition. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoleGraphRouteWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedReduction (originalCSPProblem Γ) roleGraphTargetProblem :=
  CertifiedReduction.comp (roleGraphSharedGadgetWithContract contract) (ingress Γ)

/-- Typed provenance exposes the exact ingress and CSP-to-EON shared component. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRoleGraphRouteWithContractProvenance
    {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ) :
    CertifiedRouteProvenance (ingress Γ) (roleGraphSharedGadgetWithContract contract)
      .identity (finalRoleGraphRouteWithContract contract) :=
  CertifiedRouteProvenance.identityEgress (ingress Γ)
    (roleGraphSharedGadgetWithContract contract)

@[simp] theorem finalRoleGraphRouteWithContract_program {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (finalRoleGraphRouteWithContract contract).program =
      Program.PolyProg.comp (roleGraphSharedGadgetWithContract contract).program
        (ingress Γ).program :=
  rfl

theorem finalRoleGraphRouteWithContract_correct {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (originalCSPProblem Γ).Instance) :
    (originalCSPProblem Γ).accepts formula ↔
      roleGraphTargetProblem.accepts
        ((finalRoleGraphRouteWithContract contract).program.run formula) :=
  (finalRoleGraphRouteWithContract contract).correct formula

@[simp] theorem finalRoleGraphRouteWithContract_directTM {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    (finalRoleGraphRouteWithContract contract).directTM =
      (finalRoleGraphRouteWithContract contract).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (finalRoleGraphRouteWithContract contract)

/-- The contract-bearing EON resolver composes the accepted ingress and shared component. -/
noncomputable def resolveRoleGraphComponentPathWithContract {D : Type} {Γ : Language D}
    (contract : ExecutableLanguageContract Γ) :
    Protocol.ResolverOutcome (originalCSPProblem Γ) roleGraphTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage
    (roleGraphSharedGadgetResolutionWithContract contract) (cspIngressResolution Γ)

@[simp] theorem resolveRoleGraphComponentPathWithContract_exact
    {D : Type} {Γ : Language D} (contract : ExecutableLanguageContract Γ) :
    resolveRoleGraphComponentPathWithContract contract =
      .accepted (finalRoleGraphRouteWithContract contract) :=
  rfl

/-- The missing reusable CSP-to-Clause/CNF construction at its exact hub endpoint. -/
abbrev MissingClauseSharedGadget {D : Type} (Γ : Language D) : Type 2 :=
  Protocol.ComponentRequest.MissingOutcome
    (role := .sharedGadget) (source := cspHubProblem Γ) (target := clauseCNFTargetProblem)

/-- The missing generic CSP-to-EON construction at its exact hub endpoint. -/
abbrev MissingRoleGraphSharedGadget {D : Type} (Γ : Language D) : Type 2 :=
  Protocol.ComponentRequest.MissingOutcome
    (role := .sharedGadget) (source := cspHubProblem Γ) (target := roleGraphTargetProblem)

/--
The bare-language Clause/CNF request lacks executable relation rows.

The contract-bearing shared gadget above already supplies the program, semantic
proof, and compiled TM; the missing capability here is therefore the explicit
`ExecutableLanguageContract Γ`, not direct-TM evidence.
-/
def missingClauseSharedGadget {D : Type} (Γ : Language D) : MissingClauseSharedGadget Γ :=
  (clauseSharedGadgetRequest Γ).missingExecutableRelationContract

/-- The bare-language EON request has the same executable-relation prerequisite. -/
def missingRoleGraphSharedGadget {D : Type} (Γ : Language D) :
    MissingRoleGraphSharedGadget Γ :=
  (roleGraphSharedGadgetRequest Γ).missingExecutableRelationContract

/-- Resolve the absent CSP-hub-to-Clause/CNF shared gadget at its exact endpoint. -/
def clauseSharedGadgetResolution {D : Type} (Γ : Language D) :
    Protocol.ComponentResolution .sharedGadget (cspHubProblem Γ) clauseCNFTargetProblem :=
  .blocked (missingClauseSharedGadget Γ)

/-- Resolve the absent generic CSP-hub-to-EON shared gadget at its exact endpoint. -/
def roleGraphSharedGadgetResolution {D : Type} (Γ : Language D) :
    Protocol.ComponentResolution .sharedGadget (cspHubProblem Γ) roleGraphTargetProblem :=
  .blocked (missingRoleGraphSharedGadget Γ)

/-- The Clause/CNF path has a request-indexed final outcome, not a whole-route blocker. -/
noncomputable def resolveClauseComponentPath {D : Type} (Γ : Language D) :
    Protocol.ResolverOutcome (originalCSPProblem Γ) clauseCNFTargetProblem :=
  Protocol.ComponentResolver.composeTwoStage (clauseSharedGadgetResolution Γ)
    (cspIngressResolution Γ)

/--
The EON path reuses the accepted Clause suffix and retains the generic Clause
component as its first failed dependency.  The identity ingress is included
explicitly in the future success branch.
-/
noncomputable def resolveRoleGraphComponentPath {D : Type} (Γ : Language D) :
    Protocol.ResolverOutcome (originalCSPProblem Γ) roleGraphTargetProblem :=
  match cspIngressResolution Γ with
  | .blocked missing => .blocked missing
  | .accepted ingressCertificate =>
      match clauseSharedGadgetResolution Γ with
      | .blocked missing => .blocked missing
      | .accepted clauseCertificate =>
          .accepted (CertifiedReduction.comp clauseToExistentialEON
            (CertifiedReduction.comp clauseCertificate ingressCertificate))

/-- The Clause blocker retains its exact hub-level component endpoint. -/
@[simp] theorem missingClauseSharedGadget_endpoint {D : Type} (Γ : Language D) :
    (missingClauseSharedGadget Γ).endpoint = (clauseSharedGadgetRequest Γ).endpoint :=
  rfl

/-- The RoleGraph blocker retains its exact hub-level component endpoint. -/
@[simp] theorem missingRoleGraphSharedGadget_endpoint {D : Type} (Γ : Language D) :
    (missingRoleGraphSharedGadget Γ).endpoint = (roleGraphSharedGadgetRequest Γ).endpoint :=
  rfl

/-- The bare language does not contain the executable rows required by the Clause gadget. -/
@[simp] theorem missingClauseSharedGadget_reason {D : Type} (Γ : Language D) :
    (missingClauseSharedGadget Γ).reason = .executableRelationContract :=
  rfl

/-- The compatibility EON request reports the same exact contract prerequisite. -/
@[simp] theorem missingRoleGraphSharedGadget_reason {D : Type} (Γ : Language D) :
    (missingRoleGraphSharedGadget Γ).reason = .executableRelationContract :=
  rfl

/-- The Clause shared-gadget resolution is definitionally its exact missing outcome. -/
@[simp] theorem clauseSharedGadgetResolution_eq_missing {D : Type} (Γ : Language D) :
    clauseSharedGadgetResolution Γ = .blocked (missingClauseSharedGadget Γ) :=
  rfl

/-- The RoleGraph shared-gadget resolution is definitionally its exact missing outcome. -/
@[simp] theorem roleGraphSharedGadgetResolution_eq_missing {D : Type} (Γ : Language D) :
    roleGraphSharedGadgetResolution Γ = .blocked (missingRoleGraphSharedGadget Γ) :=
  rfl

/-- The Clause path stops at the exact first shared-gadget blocker. -/
@[simp] theorem resolveClauseComponentPath_eq_sharedGadget {D : Type} (Γ : Language D) :
    resolveClauseComponentPath Γ = .blocked (missingClauseSharedGadget Γ) :=
  rfl

/-- The EON path now stops at the actual generic Clause dependency. -/
@[simp] theorem resolveRoleGraphComponentPath_eq_clauseSharedGadget {D : Type} (Γ : Language D) :
    resolveRoleGraphComponentPath Γ = .blocked (missingClauseSharedGadget Γ) :=
  rfl

/-- A blocked Clause/CNF shared gadget cannot be promoted to a certificate. -/
theorem clauseSharedGadgetResolution_not_accepted {D : Type} (Γ : Language D)
    (certificate : CertifiedReduction (cspHubProblem Γ) clauseCNFTargetProblem) :
    clauseSharedGadgetResolution Γ ≠ .accepted certificate := by
  intro equality
  cases equality

/-- A blocked RoleGraph shared gadget cannot be promoted to a certificate. -/
theorem roleGraphSharedGadgetResolution_not_accepted {D : Type} (Γ : Language D)
    (certificate : CertifiedReduction (cspHubProblem Γ) roleGraphTargetProblem) :
    roleGraphSharedGadgetResolution Γ ≠ .accepted certificate := by
  intro equality
  cases equality

/-- The blocked Clause/CNF path cannot be promoted to a final certificate. -/
theorem resolveClauseComponentPath_not_accepted {D : Type} (Γ : Language D)
    (certificate : CertifiedReduction (originalCSPProblem Γ) clauseCNFTargetProblem) :
    resolveClauseComponentPath Γ ≠ .accepted certificate := by
  intro equality
  cases equality

/-- The blocked RoleGraph path cannot be promoted to a final certificate. -/
theorem resolveRoleGraphComponentPath_not_accepted {D : Type} (Γ : Language D)
    (certificate : CertifiedReduction (originalCSPProblem Γ) roleGraphTargetProblem) :
    resolveRoleGraphComponentPath Γ ≠ .accepted certificate := by
  intro equality
  cases equality

end
end FiniteDomainCSP
end Routes
end ComplexityReduction
