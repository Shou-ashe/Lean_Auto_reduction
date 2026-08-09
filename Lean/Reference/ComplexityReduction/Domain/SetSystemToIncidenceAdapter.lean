/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.IncidenceIRSetSystemBridge
import ComplexityReduction.Domain.SetSystemMembershipPairs
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Protocol.ComponentResolver
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Projections

/-!
The structured Exact-Cover-to-IncidenceIR ingress adapter.

The adapter assembles the exact canonical incidence carrier from existing
direct-TM projections for the source universe size, set count, and indexed
membership pairs.  Its only domain atom is indexed by that assembled
executable and its direct-TM proof; semantic correctness is separately
established at the source/hub boundary.  No erased `UniversalRelIR` carrier,
bare cost map, or fused final-route primitive is admitted here.
-/

namespace ComplexityReduction
namespace Domain
namespace SetSystemToIncidenceAdapter

open Encoding
open Program
open Certificate
open ComplexityReduction
open ComplexityReduction.Combinatorics

/-- The exact structured source endpoint for the proposed ingress component. -/
abbrev sourceProblem : PresentedProblem := Presentation.SetSystem.exactCoverStructuredProblem

/-- The exact canonical typed IncidenceIR target endpoint for the proposed ingress component. -/
abbrev hubProblem : PresentedProblem := IncidenceIR.exactCoverProblem

/-- The canonical role-indexed endpoint of one Exact-Cover ingress component. -/
abbrev IngressEndpoint (source hub : PresentedProblem) : Type 2 :=
  Protocol.ComponentEndpoint .ingress source hub

/-- The canonical request for one exact Exact-Cover ingress component. -/
abbrev IngressRequest (source hub : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .ingress source hub

/-- The unique exact structured-Exact-Cover to canonical-IncidenceIR request. -/
def request : IngressRequest sourceProblem hubProblem := .exact

/- The exact source-to-hub executable; it does not mention a final route target. -/
def ingressExecutable (input : sourceProblem.Instance) : hubProblem.Instance :=
  IncidenceIRSetSystemBridge.toIncidenceIR input.system

private theorem membershipPairsFrom_eq_legacy :
    ∀ (index : Nat) (sets : List (List Nat)),
      SetSystemMembershipPairs.membershipPairsFrom index sets =
        ComplexityReduction.SetSystem.membershipPairsFrom index sets
  | _, [] => rfl
  | index, set :: sets => by
      simp [SetSystemMembershipPairs.membershipPairsFrom,
        ComplexityReduction.SetSystem.membershipPairsFrom,
        membershipPairsFrom_eq_legacy (index + 1) sets]

private theorem fromSetSystem_eq_legacy_membershipPairs
    (input : ComplexityReduction.Combinatorics.SetSystemInput) :
    SetSystemMembershipPairs.fromSetSystem input =
      ComplexityReduction.SetSystem.membershipPairs input := by
  rw [SetSystemMembershipPairs.fromSetSystem_eq_membershipPairsFrom]
  simpa [ComplexityReduction.SetSystem.membershipPairs] using
    membershipPairsFrom_eq_legacy 0 input.sets

/-- Direct-TM evidence for the exact source-to-hub executable. -/
theorem ingressExecutable_tmPolyTime :
    ComplexityReduction.TMPolyTimeMap sourceProblem.representation.encodedType
      hubProblem.representation.encodedType ingressExecutable := by
  have hPairs : ComplexityReduction.TMPolyTimeMap sourceProblem.representation.encodedType
      IncidenceIR.membershipPairsPresentation.encodedType
      (fun input : ExactCoverInput =>
        IncidenceIR.membershipPairs (IncidenceIRSetSystemBridge.toIncidenceIR input.system)) := by
    have hComp := ComplexityReduction.TMPolyTimeMap.comp
      SetSystemMembershipPairs.fromSetSystem_tmPolyTime
      ComplexityReduction.Karp21.SteinerTree.exactCoverSystemTMBackedMap.tm_polytime
    convert hComp using 1
    funext input
    simpa [Function.comp, IncidenceIRSetSystemBridge.toIncidenceIR,
      IncidenceIR.membershipPairs] using
      (show SetSystemMembershipPairs.fromSetSystem input.system =
          ComplexityReduction.SetSystem.membershipPairs input.system by
        exact fromSetSystem_eq_legacy_membershipPairs input.system).symm
  have hPayload : ComplexityReduction.TMPolyTimeMap sourceProblem.representation.encodedType
      IncidenceIR.rightPayloadPresentation.encodedType
      (fun input : ExactCoverInput =>
        (input.system.sets.length,
          IncidenceIR.membershipPairs (IncidenceIRSetSystemBridge.toIncidenceIR input.system))) :=
    ComplexityReduction.TMPolyTimeMap.prod_mk
      ComplexityReduction.Karp21.SteinerTree.exactCoverSetsLength_tm_polytime hPairs
  have hProduct := ComplexityReduction.TMPolyTimeMap.prod_mk
    ComplexityReduction.Karp21.SteinerTree.exactCoverUniverseSize_tm_polytime hPayload
  simpa [ingressExecutable, sourceProblem, Presentation.SetSystem.exactCoverStructuredProblem,
    Presentation.SetSystem.exactCoverStructuredPresentation,
    IncidenceIR.lawfulRepresentation, IncidenceIR.rightPayloadPresentation,
    IncidenceIRSetSystemBridge.toIncidenceIR, IncidenceIR.mk,
    IncidenceIR.membershipPairs] using hProduct

/-- The one minimal direct-TM-backed atom required by this concrete ingress adapter. -/
noncomputable def ingressPrimitive :
    Primitive sourceProblem.representation hubProblem.representation :=
  Primitive.ofTMPolyTime ingressExecutable ingressExecutable_tmPolyTime

/-- The adapter program contains exactly its source-to-hub atom. -/
noncomputable def ingressProgram :
    PolyProg sourceProblem.representation hubProblem.representation :=
  .atom ingressPrimitive

@[simp] theorem ingressProgram_run (input : sourceProblem.Instance) :
    ingressProgram.run input = ingressExecutable input :=
  rfl

/-- The source and hub predicates agree on the exact ingress program output. -/
theorem ingressProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ hubProblem.accepts (ingressProgram.run input) := by
  constructor
  · intro sourceAccepts
    exact (IncidenceIRSetSystemBridge.structuredExactCover_accepts_iff_incidenceIR
      sourceAccepts.1).mp sourceAccepts
  · intro hubAccepts
    apply (IncidenceIRSetSystemBridge.structuredExactCover_accepts_iff_incidenceIR
      ((IncidenceIRSetSystemBridge.toIncidenceIR_wellFormed_iff input.system).mp
        hubAccepts.1)).mpr
    simpa [ingressProgram_run, ingressExecutable] using hubAccepts

/-- The authoritative structured Exact-Cover ingress certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def sourceAdapter : CertifiedReduction sourceProblem hubProblem where
  program := ingressProgram
  correct := ingressProgram_correct

@[simp] theorem sourceAdapter_program : sourceAdapter.program = ingressProgram :=
  rfl

@[simp] theorem sourceAdapter_directTM : sourceAdapter.directTM = ingressProgram.compileTM :=
  rfl

/-- The shared resolver result for this exact ingress component. -/
abbrev Resolution : Type 2 :=
  Protocol.ComponentResolution .ingress sourceProblem hubProblem

/- The shared resolver accepts only the exact program-indexed ingress certificate. -/
noncomputable def resolve : Resolution :=
  Protocol.ComponentResolver.accept request sourceAdapter

@[simp] theorem resolve_exact :
    resolve = .accepted sourceAdapter :=
  rfl

theorem resolve_accepted_endpoint :
    match resolve with
    | .accepted certificate => certificate.program = ingressProgram
    | .blocked _ => False :=
  rfl

/-- The bridge theorem remains semantic-only and is not a program or TM witness. -/
theorem source_semantics_to_hub {input : ComplexityReduction.Combinatorics.SetSystemInput}
    (wellFormed : ComplexityReduction.Combinatorics.SetSystemWellFormed input) :
    sourceProblem.accepts { system := input } ↔
      hubProblem.accepts (IncidenceIRSetSystemBridge.toIncidenceIR input) :=
  IncidenceIRSetSystemBridge.structuredExactCover_accepts_iff_incidenceIR wellFormed

end SetSystemToIncidenceAdapter
end Domain
end ComplexityReduction
