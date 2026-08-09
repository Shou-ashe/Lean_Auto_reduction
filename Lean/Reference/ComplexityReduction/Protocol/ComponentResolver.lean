/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Protocol.ComponentRequest

/-!
Fail-closed resolver combinators for exact typed reduction components.

Success contains only a `CertifiedReduction` at the requested lawful
presentations.  Failure contains only the first exact role-indexed
`ComponentRequest.MissingOutcome`; no primitive, route descriptor, string,
legacy packet, executable map, cost, or TM evidence participates in resolution.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding Certificate

/-- The result of resolving one exact role-indexed component request. -/
inductive ComponentResolution (role : ReductionComponentRole)
    (source target : PresentedProblem) : Type 2 where
  | accepted (certificate : CertifiedReduction source target) :
      ComponentResolution role source target
  | blocked (missing : ComponentRequest.MissingOutcome
      (role := role) (source := source) (target := target)) :
      ComponentResolution role source target

/--
The result of resolving a composed request.

An accepted result has exactly the requested source and target certificate.  A
blocked result existentially retains the role and exact lawful endpoints of
the first failed input component rather than retagging it as a whole route.
-/
inductive ResolverOutcome (source target : PresentedProblem) : Type 2 where
  | accepted (certificate : CertifiedReduction source target) : ResolverOutcome source target
  | blocked {role : ReductionComponentRole} {failedSource failedTarget : PresentedProblem}
      (missing : ComponentRequest.MissingOutcome
        (role := role) (source := failedSource) (target := failedTarget)) :
      ResolverOutcome source target

namespace ComponentResolver

/-- Accept only an exact typed certificate for one requested component. -/
def accept {role : ReductionComponentRole} {source target : PresentedProblem}
    (_request : ComponentRequest role source target)
    (certificate : CertifiedReduction source target) : ComponentResolution role source target :=
  .accepted certificate

/-- Fail closed at the exact component endpoint carried by the request. -/
def block {role : ReductionComponentRole} {source target : PresentedProblem}
    (request : ComponentRequest role source target) (reason : MissingCapabilityReason) :
    ComponentResolution role source target :=
  .blocked (request.missing reason)

/-- Reify one exact component result as the corresponding final resolver result. -/
def resolveSingle {role : ReductionComponentRole} {source target : PresentedProblem}
    (result : ComponentResolution role source target) : ResolverOutcome source target :=
  match result with
  | .accepted certificate => .accepted certificate
  | .blocked missing => .blocked missing

/--
Resolve two sequential components in construction order.

`before` is inspected first, so a source-side blocker is retained even when
`after` is also blocked.  On success, the stored program is exactly the
`CertifiedReduction.comp after before` composition.
-/
def composeTwoStage {beforeRole afterRole : ReductionComponentRole}
    {source middle target : PresentedProblem}
    (after : ComponentResolution afterRole middle target)
    (before : ComponentResolution beforeRole source middle) : ResolverOutcome source target :=
  match before with
  | .blocked missing => .blocked missing
  | .accepted beforeCertificate =>
      match after with
      | .blocked missing => .blocked missing
      | .accepted afterCertificate => .accepted (CertifiedReduction.comp afterCertificate beforeCertificate)

/--
Compose the ingress, shared-gadget, and egress components of one exact final
request.  The `finalRequest` only fixes the final lawful endpoints and cannot
override a component blocker; success is the thin certificate composition
`egress ∘ sharedGadget ∘ ingress`.
-/
def composeIngressSharedEgress {source hub egressSource target : PresentedProblem}
    (_finalRequest : ComponentRequest .finalComposition source target)
    (ingress : ComponentResolution .ingress source hub)
    (sharedGadget : ComponentResolution .sharedGadget hub egressSource)
    (egress : ComponentResolution .egress egressSource target) : ResolverOutcome source target :=
  match ingress with
  | .blocked missing => .blocked missing
  | .accepted ingressCertificate =>
      match sharedGadget with
      | .blocked missing => .blocked missing
      | .accepted sharedCertificate =>
          match egress with
          | .blocked missing => .blocked missing
          | .accepted egressCertificate =>
              .accepted (CertifiedReduction.comp egressCertificate
                (CertifiedReduction.comp sharedCertificate ingressCertificate))

@[simp] theorem resolveSingle_accepted {role : ReductionComponentRole}
    {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
    resolveSingle (.accepted (role := role) certificate) = .accepted certificate :=
  rfl

@[simp] theorem resolveSingle_blocked {role : ReductionComponentRole}
    {source target : PresentedProblem}
    (missing : ComponentRequest.MissingOutcome (role := role) (source := source) (target := target)) :
    resolveSingle (.blocked missing) = .blocked missing :=
  rfl

end ComponentResolver

end Protocol
end ComplexityReduction
