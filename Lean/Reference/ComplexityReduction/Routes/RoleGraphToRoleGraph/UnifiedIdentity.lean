/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Equiv
import ComplexityReduction.Certificate.ReductionAdapter
import ComplexityReduction.Presentation.RoleGraph

/-!
The single V2 identity smoke route for the erased RoleGraph carrier.

The route is explicit rather than automatically selected: its presentation is
faithful, but does not have a closed structural representation certificate.
Its executable, semantic iff, and direct-TM evidence are all tied to the same
`PolyProg.id` value.
-/

namespace ComplexityReduction
namespace Routes
namespace RoleGraphToRoleGraph

open Certificate Encoding Presentation Program

/-- The exact executable construction of the RoleGraph identity smoke route. -/
def identityProgram : PolyProg
    Presentation.RoleGraph.lawfulRepresentation Presentation.RoleGraph.lawfulRepresentation :=
  .id Presentation.RoleGraph.lawfulRepresentation

@[simp]
theorem identityProgram_run (input : Presentation.RoleGraph.lawfulRepresentation.Carrier) :
    identityProgram.run input = input :=
  rfl

/-- Direct-TM evidence derived by compiling the exact identity program above. -/
theorem identityProgram_directTM : ComplexityReduction.TMPolyTimeMap
    Presentation.RoleGraph.universalRelIREncodedType
    Presentation.RoleGraph.universalRelIREncodedType identityProgram.run :=
  identityProgram.compileTM

/--
The sole certified RoleGraph-to-RoleGraph V2 smoke route.  The candidate tag
does not itself grant capability; a registry exporter must inspect this exact
`CertifiedReduction` declaration type.
-/
@[complexity_reduction_ir_typed_edge]
def unifiedIdentityRoute : CertifiedReduction
    Presentation.RoleGraph.wellFormedPresentedProblem
    Presentation.RoleGraph.wellFormedPresentedProblem :=
  CertifiedIRRoute.ofProgram identityProgram (fun _ => Iff.rfl)

@[simp]
theorem unifiedIdentityRoute_program : unifiedIdentityRoute.program = identityProgram :=
  rfl

@[simp]
theorem unifiedIdentityRoute_correct
    (input : Presentation.RoleGraph.wellFormedPresentedProblem.Instance) :
    Presentation.RoleGraph.wellFormedPresentedProblem.accepts input ↔
      Presentation.RoleGraph.wellFormedPresentedProblem.accepts
        (unifiedIdentityRoute.program.run input) :=
  Iff.rfl

/--
The route's stored program, semantic executable and iff, direct-TM witness,
and compatibility cost are all projections of the one exact `identityProgram`.
-/
theorem unifiedIdentityRoute_exactProgramRunCertificateAlignment
    (input : Presentation.RoleGraph.wellFormedPresentedProblem.Instance) :
    unifiedIdentityRoute.program = identityProgram ∧
      unifiedIdentityRoute.toEncodedSemanticReduction.f input = identityProgram.run input ∧
      (Presentation.RoleGraph.wellFormedPresentedProblem.accepts input ↔
        Presentation.RoleGraph.wellFormedPresentedProblem.accepts
          (identityProgram.run input)) ∧
      unifiedIdentityRoute.directTM = identityProgram.compileTM ∧
      unifiedIdentityRoute.compatibilityCost = identityProgram.compatibilityCost :=
  ⟨rfl, rfl, Iff.rfl, rfl, rfl⟩

/--
Every public compatibility projection of the smoke route is derived from its
one stored identity program.  This is the route-local form of the V2
single-program invariant: the semantic function and iff, direct-TM witness,
TM-backed facades, and both Karp facades cannot select a second executable,
machine, or cost witness.
-/
theorem unifiedIdentityRoute_completeProjectionChain :
    unifiedIdentityRoute.toEncodedSemanticReduction.f = identityProgram.run ∧
    (∀ input,
      Presentation.RoleGraph.wellFormedPresentedProblem.accepts input ↔
        Presentation.RoleGraph.wellFormedPresentedProblem.accepts
          (identityProgram.run input)) ∧
    unifiedIdentityRoute.directTM = identityProgram.compileTM ∧
    unifiedIdentityRoute.compatibilityCost = identityProgram.compatibilityCost ∧
    unifiedIdentityRoute.toTMBackedCostedMap.tm_polytime = identityProgram.compileTM ∧
    unifiedIdentityRoute.toTMBackedCostedMap.costed = identityProgram.compatibilityCost ∧
    unifiedIdentityRoute.toTMBackedCostedReduction.f = identityProgram.run ∧
    unifiedIdentityRoute.toTMBackedCostedReduction.tm_polytime = identityProgram.compileTM ∧
    unifiedIdentityRoute.toTMBackedCostedReduction.costed =
      .of_costed identityProgram.compatibilityCost ∧
    unifiedIdentityRoute.toTMKarpReduction.f = identityProgram.run ∧
    unifiedIdentityRoute.toTMKarpReduction.polytime = identityProgram.compileTM ∧
    unifiedIdentityRoute.toCostedKarpReduction.f.toFun = identityProgram.run ∧
    unifiedIdentityRoute.toCostedKarpReduction.f.polytime =
      identityProgram.toCostedPolyTimeMap :=
  ⟨rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
The identity certificate is locked to the one canonical erased RoleGraph
representation at both endpoint indices.  This is stronger than sharing the
same carrier: the complete codec identity is part of the endpoint type from
which the stored program, semantic law, compiler witness, and cost projection
are all obtained.
-/
theorem unifiedIdentityRoute_exactEndpointRepresentationIdentity :
    Presentation.RoleGraph.wellFormedPresentedProblem.representationIdentity =
      Presentation.RoleGraph.representationShape.identity ∧
      unifiedIdentityRoute.program =
        PolyProg.id Presentation.RoleGraph.lawfulRepresentation ∧
      ComplexityReduction.TMPolyTimeMap
        Presentation.RoleGraph.lawfulRepresentation.encodedType
        Presentation.RoleGraph.lawfulRepresentation.encodedType
        unifiedIdentityRoute.program.run := by
  refine ⟨rfl, rfl, ?_⟩
  exact unifiedIdentityRoute.program.compileTM

/-- The same unified identity certificate supplies both directions of the local equivalence. -/
@[complexity_reduction_ir_typed_equiv]
def unifiedIdentityEquiv : CertifiedEquiv
    Presentation.RoleGraph.wellFormedPresentedProblem
    Presentation.RoleGraph.wellFormedPresentedProblem :=
  CertifiedEquiv.ofReductions unifiedIdentityRoute unifiedIdentityRoute

/-- The forward equivalence direction is exactly the single certified identity route. -/
@[simp]
theorem unifiedIdentityEquiv_forward : unifiedIdentityEquiv.forward = unifiedIdentityRoute :=
  rfl

/-- The backward equivalence direction reuses exactly the same certified identity route. -/
@[simp]
theorem unifiedIdentityEquiv_backward : unifiedIdentityEquiv.backward = unifiedIdentityRoute :=
  rfl

/--
Both directions of the identity equivalence meet at the exact canonical
RoleGraph presentation.  The endpoint equality is carried by the two
certificate indices, rather than inferred merely from the common carrier.
-/
theorem unifiedIdentityEquiv_exactCertificateBoundary :
    (∀ input : Presentation.RoleGraph.wellFormedPresentedProblem.Instance,
      Presentation.RoleGraph.wellFormedPresentedProblem.accepts input ↔
        Presentation.RoleGraph.wellFormedPresentedProblem.accepts
          (unifiedIdentityEquiv.forward.program.run input)) ∧
    (∀ input : Presentation.RoleGraph.wellFormedPresentedProblem.Instance,
      Presentation.RoleGraph.wellFormedPresentedProblem.accepts input ↔
        Presentation.RoleGraph.wellFormedPresentedProblem.accepts
          (unifiedIdentityEquiv.backward.program.run input)) ∧
    unifiedIdentityEquiv.forward.program.endpointIdentities =
      ⟨Presentation.RoleGraph.wellFormedPresentedProblem.representationIdentity,
        Presentation.RoleGraph.wellFormedPresentedProblem.representationIdentity⟩ ∧
    unifiedIdentityEquiv.backward.program.endpointIdentities =
      ⟨Presentation.RoleGraph.wellFormedPresentedProblem.representationIdentity,
        Presentation.RoleGraph.wellFormedPresentedProblem.representationIdentity⟩ :=
  CertifiedEquiv.forward_backward_certificate_boundary unifiedIdentityEquiv

/--
All public two-way facades of the smoke equivalence are projections of the
same exact `identityProgram` in both directions.  This rules out a second
executable, TM witness, or cost witness at the equivalence boundary.
-/
theorem unifiedIdentityEquiv_completeCertificateChain :
    unifiedIdentityEquiv.forward.program = identityProgram ∧
    unifiedIdentityEquiv.backward.program = identityProgram ∧
    unifiedIdentityEquiv.toForwardEncodedSemanticReduction.f = identityProgram.run ∧
    unifiedIdentityEquiv.toBackwardEncodedSemanticReduction.f = identityProgram.run ∧
    unifiedIdentityEquiv.toForwardTMBackedCostedMap.tm_polytime =
      identityProgram.compileTM ∧
    unifiedIdentityEquiv.toBackwardTMBackedCostedMap.tm_polytime =
      identityProgram.compileTM ∧
    unifiedIdentityEquiv.toForwardTMBackedCostedMap.costed =
      identityProgram.compatibilityCost ∧
    unifiedIdentityEquiv.toBackwardTMBackedCostedMap.costed =
      identityProgram.compatibilityCost ∧
    unifiedIdentityEquiv.toForwardTMKarpReduction.f = identityProgram.run ∧
    unifiedIdentityEquiv.toBackwardTMKarpReduction.f = identityProgram.run ∧
    unifiedIdentityEquiv.toForwardTMKarpReduction.polytime = identityProgram.compileTM ∧
    unifiedIdentityEquiv.toBackwardTMKarpReduction.polytime = identityProgram.compileTM ∧
    unifiedIdentityEquiv.toCostedProblemEquiv.toMap.toFun = identityProgram.run ∧
    unifiedIdentityEquiv.toCostedProblemEquiv.invMap.toFun = identityProgram.run ∧
    unifiedIdentityEquiv.toCostedProblemEquiv.toMap.polytime =
      identityProgram.toCostedPolyTimeMap ∧
    unifiedIdentityEquiv.toCostedProblemEquiv.invMap.polytime =
      identityProgram.toCostedPolyTimeMap :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

end RoleGraphToRoleGraph
end Routes
end ComplexityReduction
