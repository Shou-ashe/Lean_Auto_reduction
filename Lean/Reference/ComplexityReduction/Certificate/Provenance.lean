/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.Reduction

/-!
Typed provenance for thin composed certified routes.

The ingress, shared-gadget, optional egress, and final
`CertifiedReduction` are all indices of the provenance type.  The final index
is definitionally the corresponding `CertifiedReduction.comp`, whose stored
program is definitionally the matching `PolyProg.comp`.  Consumers classify
this typed head; they do not inspect a definition body, declaration name,
string, or route-local primitive.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding Program

/--
The optional egress component of a composed route.

The identity case is indexed only when the shared-gadget endpoint is already
the final endpoint.  The explicit case contains its exact egress certificate
as part of the enclosing provenance type application.
-/
inductive OptionalEgress : PresentedProblem → PresentedProblem → Type 2 where
  | identity {target : PresentedProblem} : OptionalEgress target target
  | explicit {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
      OptionalEgress source target

/--
Provenance for a final certified route assembled from typed components.

Every component certificate and the final certificate occur in the type's
application, so their elaborated terms are available without unfolding a
provenance value.  The `identity` constructor records a route whose
shared-gadget target is already the final target.  The `explicit` constructor
records a separate typed egress realization.  Their result indices fix the
final certificate and its stored program to the corresponding closed
compositions.
-/
inductive CertifiedRouteProvenance :
    {source hub sharedTarget target : PresentedProblem} →
    (ingress : CertifiedReduction source hub) →
    (sharedGadget : CertifiedReduction hub sharedTarget) →
    (egress : OptionalEgress sharedTarget target) →
    (finalCertificate : CertifiedReduction source target) → Type 2 where
  | identity {source hub target : PresentedProblem}
      (ingress : CertifiedReduction source hub)
      (sharedGadget : CertifiedReduction hub target) :
      CertifiedRouteProvenance ingress sharedGadget .identity
        (CertifiedReduction.comp sharedGadget ingress)
  | explicit {source hub egressSource target : PresentedProblem}
      (ingress : CertifiedReduction source hub)
      (sharedGadget : CertifiedReduction hub egressSource)
      (egress : CertifiedReduction egressSource target) :
      CertifiedRouteProvenance ingress sharedGadget (.explicit egress)
        (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress))

namespace CertifiedRouteProvenance

/-- Closed provenance constructor when the shared gadget already reaches the final target. -/
def identityEgress {source hub target : PresentedProblem}
    (ingress : CertifiedReduction source hub)
    (sharedGadget : CertifiedReduction hub target) :
    CertifiedRouteProvenance ingress sharedGadget .identity
      (CertifiedReduction.comp sharedGadget ingress) :=
  .identity ingress sharedGadget

/-- Closed provenance constructor when a separate typed egress realization is required. -/
def explicitEgress {source hub egressSource target : PresentedProblem}
    (ingress : CertifiedReduction source hub)
    (sharedGadget : CertifiedReduction hub egressSource)
    (egress : CertifiedReduction egressSource target) :
    CertifiedRouteProvenance ingress sharedGadget (.explicit egress)
      (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)) :=
  .explicit ingress sharedGadget egress

/-- The identity-egress final index stores the exact two-component program composition. -/
@[simp] theorem identityEgress_program {source hub target : PresentedProblem}
    (ingress : CertifiedReduction source hub)
    (sharedGadget : CertifiedReduction hub target) :
    (CertifiedReduction.comp sharedGadget ingress).program =
      PolyProg.comp sharedGadget.program ingress.program :=
  rfl

/-- The explicit-egress final index stores the exact three-component program composition. -/
@[simp] theorem explicitEgress_program {source hub egressSource target : PresentedProblem}
    (ingress : CertifiedReduction source hub)
    (sharedGadget : CertifiedReduction hub egressSource)
    (egress : CertifiedReduction egressSource target) :
    (CertifiedReduction.comp egress (CertifiedReduction.comp sharedGadget ingress)).program =
      PolyProg.comp egress.program (PolyProg.comp sharedGadget.program ingress.program) :=
  rfl

end CertifiedRouteProvenance

end Certificate
end ComplexityReduction
