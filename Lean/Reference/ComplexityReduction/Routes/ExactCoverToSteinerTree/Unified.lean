/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Presentation.SteinerTree
import ComplexityReduction.Protocol.ComponentResolver
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.Assembly

/-!
The canonical structured Exact-Cover-to-Steiner-Tree V2 route.

CR supplies a standard-audited direct-TM theorem for the exact compact
structured map. Its legacy `TMBackedCostedMap` and `TMKarpReduction` facades
also carry a `native_decide` dependency through their cost boundary, so this
route deliberately does not promote either facade. Instead, it builds one V2
`Primitive` directly from the exact executable and direct-TM theorem, then
derives semantic, cost, and compatibility evidence by compiling its one
stored `PolyProg`.
-/

namespace ComplexityReduction
namespace Routes
namespace ExactCoverToSteinerTree

open Certificate Encoding Program

/-- The exact structured Exact Cover presentation of the canonical source hub. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.SetSystem.exactCoverStructuredPresentation

/-- The exact structured Steiner Tree presentation of the canonical target hub. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.SteinerTree.structuredPresentation

/-- The exact V2 structured Exact Cover source endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.SetSystem.exactCoverStructuredProblem

/-- The exact V2 structured Steiner Tree target endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.SteinerTree.structuredProblem

/-- The original structured Exact Cover endpoint is the canonical source hub. -/
abbrev originalExactCoverProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Exact Cover hub retains the complete source representation. -/
abbrev exactCoverHubProblem : PresentedProblem :=
  sourceProblem

/-- The canonical Steiner Tree hub is the target of the shared gadget. -/
abbrev steinerTreeHubProblem : PresentedProblem :=
  targetProblem

/-- The final structured Steiner Tree endpoint is already the target hub. -/
abbrev finalSteinerTreeProblem : PresentedProblem :=
  targetProblem

/-- The exact identity-eligible ingress endpoint into the Exact Cover hub. -/
abbrev ExactCoverIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalExactCoverProblem exactCoverHubProblem

/-- The canonical request for the Exact Cover ingress component. -/
abbrev ExactCoverIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalExactCoverProblem exactCoverHubProblem

/-- The unique Exact Cover ingress request. -/
def exactCoverIngressRequest : ExactCoverIngressRequest :=
  .exact

/-- Ingress identity is eligible only because the complete endpoints coincide. -/
theorem exactCoverIngress_endpoints_eq :
    originalExactCoverProblem = exactCoverHubProblem :=
  rfl

/-- The exact reusable canonical shared-gadget endpoint. -/
abbrev SharedGadgetEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .sharedGadget exactCoverHubProblem steinerTreeHubProblem

/-- The canonical request for the Exact-Cover-to-Steiner-Tree shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget exactCoverHubProblem steinerTreeHubProblem

/-- The unique request for the compact direct-TM shared gadget. -/
def sharedGadgetRequest : SharedGadgetRequest :=
  .exact

/-- The exact identity-eligible egress endpoint from the Steiner Tree hub. -/
abbrev SteinerTreeEgressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .egress steinerTreeHubProblem finalSteinerTreeProblem

/-- The canonical request for the exact Steiner Tree egress component. -/
abbrev SteinerTreeEgressRequest : Type 2 :=
  Protocol.ComponentRequest .egress steinerTreeHubProblem finalSteinerTreeProblem

/-- The unique Steiner Tree egress request. -/
def steinerTreeEgressRequest : SteinerTreeEgressRequest :=
  .exact

/-- Egress identity is eligible only because the complete endpoints coincide. -/
theorem steinerTreeEgress_endpoints_eq :
    steinerTreeHubProblem = finalSteinerTreeProblem :=
  rfl

/--
The one exact direct-TM primitive for the structured route. Its sole machine
evidence is CR's standard-audited theorem for the same compact map; neither a
legacy cost map nor a legacy TM-Karp facade contributes evidence here.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def exactCoverToSteinerTreePrimitive :
    Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime
    ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap
    ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime

/-- The V2 primitive executes exactly CR's compact structured map. -/
@[simp]
theorem exactCoverToSteinerTreePrimitive_run
    (input : sourceProblem.Instance) :
    exactCoverToSteinerTreePrimitive.run input =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input :=
  rfl

/--
The primitive's sole direct-TM witness is exactly CR's theorem for the compact
structured map that it executes.  This equality names the proof object as
well as its indexed executable, so it cannot be confused with a TM theorem
for a separately packaged legacy reduction.
-/
@[simp]
theorem exactCoverToSteinerTreePrimitive_directTM_eq_legacy :
    exactCoverToSteinerTreePrimitive.tmPolyTime =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime :=
  rfl

/-- The route has exactly one primitive atom and no parallel executable. -/
noncomputable def exactCoverToSteinerTreeProgram :
    PolyProg sourcePresentation targetPresentation :=
  .atom exactCoverToSteinerTreePrimitive

/-- The route program is definitionally the direct-TM primitive atom. -/
@[simp]
theorem exactCoverToSteinerTreeProgram_eq_atom :
    exactCoverToSteinerTreeProgram = PolyProg.atom exactCoverToSteinerTreePrimitive :=
  rfl

/-- The one program runs exactly the compact structured executable. -/
@[simp]
theorem exactCoverToSteinerTreeProgram_run
    (input : sourceProblem.Instance) :
    exactCoverToSteinerTreeProgram.run input =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input :=
  rfl

/--
Compiling the route's sole stored program recovers precisely the CR direct-TM
theorem of the compact structured executable.  No legacy TM-backed cost map
is involved in this compiler projection.
-/
@[simp]
theorem exactCoverToSteinerTreeProgram_compileTM_eq_legacy :
    exactCoverToSteinerTreeProgram.compileTM =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime :=
  exactCoverToSteinerTreePrimitive_directTM_eq_legacy

/-- The CR semantic theorem is tied to the shared gadget's exact program. -/
theorem exactCoverToSteinerTreeProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (exactCoverToSteinerTreeProgram.run input) := by
  change ComplexityReduction.Combinatorics.exactCoverStructuredDecisionProblem.isYes input ↔
    ComplexityReduction.Combinatorics.Graph.steinerTreeStructuredDecisionProblem.isYes
      (ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input)
  exact ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap_correct input

/--
The sole canonical V2 Exact-Cover-to-Steiner-Tree certificate. Its semantic,
direct-TM, and compatibility-cost evidence are projections of the same stored
primitive program.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def exactCoverToSteinerTreeCertifiedReduction :
    CertifiedReduction sourceProblem targetProblem where
  program := exactCoverToSteinerTreeProgram
  correct := exactCoverToSteinerTreeProgram_correct

/-- The certificate stores exactly the route's one primitive program. -/
@[simp]
theorem exactCoverToSteinerTreeCertifiedReduction_program :
    exactCoverToSteinerTreeCertifiedReduction.program = exactCoverToSteinerTreeProgram :=
  rfl

/-- The certificate's stored program executes exactly the CR compact map. -/
@[simp]
theorem exactCoverToSteinerTreeCertifiedReduction_run
    (input : sourceProblem.Instance) :
    exactCoverToSteinerTreeCertifiedReduction.program.run input =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input :=
  rfl

/-- The certificate's direct-TM projection compiles its stored primitive program. -/
@[simp]
theorem exactCoverToSteinerTreeCertifiedReduction_directTM_eq_compileTM :
    exactCoverToSteinerTreeCertifiedReduction.directTM =
      exactCoverToSteinerTreeCertifiedReduction.program.compileTM :=
  Certificate.CertifiedReduction.directTM_eq_compileTM _

/--
The certificate's direct-TM field is CR's exact theorem for the same compact
structured map run by its stored program.
-/
@[simp]
theorem exactCoverToSteinerTreeCertifiedReduction_directTM_eq_legacy :
    exactCoverToSteinerTreeCertifiedReduction.directTM =
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime := by
  change exactCoverToSteinerTreePrimitive.tmPolyTime =
    ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime
  exact exactCoverToSteinerTreeProgram_compileTM_eq_legacy

/-- The exact CR direct-TM statement follows from the certificate's stored program. -/
theorem exactCoverToSteinerTreeCertifiedReduction_directTM_has_legacyStatement :
    ComplexityReduction.TMPolyTimeMap
      sourcePresentation.encodedType
      targetPresentation.encodedType
      ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap := by
  simpa only [exactCoverToSteinerTreeCertifiedReduction_run] using
    exactCoverToSteinerTreeCertifiedReduction.directTM

/-- The compatibility cost is derived only from compilation of the stored program. -/
@[simp]
theorem exactCoverToSteinerTreeCertifiedReduction_compatibilityCost :
    exactCoverToSteinerTreeCertifiedReduction.compatibilityCost =
      exactCoverToSteinerTreeCertifiedReduction.program.compatibilityCost :=
  Certificate.CertifiedReduction.compatibilityCost_eq_program_compatibilityCost _

/--
Endpoint-exact coherence for the compact structured CR evidence.

The primitive executable, the named program executable, the certificate
executable, and all three direct-TM projections are pinned to CR's one compact
map and its one `TMPolyTimeMap` theorem.  This is deliberately stated without
mentioning CR's legacy `TMBackedCostedMap` or `TMKarpReduction` facades: those
cost-bearing wrappers are not inputs to this V2 certificate chain.
-/
theorem exactCoverToSteinerTreeCertifiedReduction_endpointProgramDirectTMCoherence :
    sourceProblem.backendEndpoint =
        ComplexityReduction.Combinatorics.exactCoverStructuredDecisionProblem ∧
      targetProblem.backendEndpoint =
        ComplexityReduction.Combinatorics.Graph.steinerTreeStructuredDecisionProblem ∧
      (∀ input,
        exactCoverToSteinerTreePrimitive.run input =
          ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input) ∧
      (∀ input,
        exactCoverToSteinerTreeProgram.run input =
          ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input) ∧
      (∀ input,
        exactCoverToSteinerTreeCertifiedReduction.program.run input =
          ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap input) ∧
      exactCoverToSteinerTreePrimitive.tmPolyTime =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeProgram.compileTM =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        exactCoverToSteinerTreeCertifiedReduction.program.compileTM := by
  exact ⟨rfl, rfl,
    exactCoverToSteinerTreePrimitive_run,
    exactCoverToSteinerTreeProgram_run,
    exactCoverToSteinerTreeCertifiedReduction_run,
    exactCoverToSteinerTreePrimitive_directTM_eq_legacy,
    exactCoverToSteinerTreeProgram_compileTM_eq_legacy,
    exactCoverToSteinerTreeCertifiedReduction_directTM_eq_legacy,
    exactCoverToSteinerTreeCertifiedReduction_directTM_eq_compileTM⟩

/--
The compact direct-TM edge is admitted only as the exact hub-level shared
gadget.  The route-local request/resolver layer is absent: identity ingress
and egress are endpoint facts, not alternative capability authority.
-/
noncomputable def exactCoverToSteinerTreeSharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget exactCoverHubProblem steinerTreeHubProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest exactCoverToSteinerTreeCertifiedReduction

/-- The identity ingress is a typed component certificate, not a bare endpoint equality. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def ingress : CertifiedReduction originalExactCoverProblem exactCoverHubProblem :=
  .refl exactCoverHubProblem

/-- The public exact route is the thin composition of ingress and the shared gadget. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_final_composition]
noncomputable def finalRoute :
    CertifiedReduction originalExactCoverProblem finalSteinerTreeProblem :=
  CertifiedReduction.comp exactCoverToSteinerTreeCertifiedReduction ingress

/-- The identity egress and the composed final program are carried by typed provenance. -/
@[complexity_reduction_ir_typed_edge]
noncomputable def finalRouteProvenance :
    CertifiedRouteProvenance ingress exactCoverToSteinerTreeCertifiedReduction .identity finalRoute :=
  CertifiedRouteProvenance.identityEgress ingress exactCoverToSteinerTreeCertifiedReduction

/-- The final program is definitionally the required component composition. -/
@[simp] theorem finalRoute_program :
    finalRoute.program = PolyProg.comp exactCoverToSteinerTreeCertifiedReduction.program ingress.program :=
  rfl

/-- The resolver outcome reifies the exact shared-gadget component path. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalExactCoverProblem finalSteinerTreeProblem :=
  Protocol.ComponentResolver.resolveSingle exactCoverToSteinerTreeSharedGadgetResolution

/-- The shared-gadget resolution retains exactly the canonical certificate. -/
@[simp] theorem exactCoverToSteinerTreeSharedGadgetResolution_exact :
    exactCoverToSteinerTreeSharedGadgetResolution =
      .accepted exactCoverToSteinerTreeCertifiedReduction :=
  rfl

/-- The component path yields precisely the accepted shared-gadget certificate. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted exactCoverToSteinerTreeCertifiedReduction :=
  rfl

/-- The concrete route exposes all trusted evidence through its exact one primitive atom. -/
theorem exactCoverToSteinerTreeCertifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔
        targetProblem.accepts
          (exactCoverToSteinerTreeCertifiedReduction.program.run input)) ∧
      exactCoverToSteinerTreeCertifiedReduction.program =
        PolyProg.atom exactCoverToSteinerTreePrimitive ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        exactCoverToSteinerTreeCertifiedReduction.program.compileTM ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        exactCoverToSteinerTreePrimitive.tmPolyTime ∧
      exactCoverToSteinerTreeCertifiedReduction.compatibilityCost =
        exactCoverToSteinerTreeCertifiedReduction.program.compatibilityCost :=
  ⟨exactCoverToSteinerTreeCertifiedReduction.correct,
    exactCoverToSteinerTreeCertifiedReduction_program,
    exactCoverToSteinerTreeCertifiedReduction_directTM_eq_compileTM,
    exactCoverToSteinerTreeProgram_compileTM_eq_legacy,
    exactCoverToSteinerTreeCertifiedReduction_compatibilityCost⟩

/--
The accepted shared gadget, primitive atom, certificate, compiler, and cost have one
standard direct-TM provenance at the exact structured endpoints.  The legacy
cost-bearing facades are deliberately absent from this chain.
-/
theorem exactCoverToSteinerTreeCertifiedReduction_completeStandardDirectTMProvenance :
    exactCoverToSteinerTreeSharedGadgetResolution =
        .accepted exactCoverToSteinerTreeCertifiedReduction ∧
      resolveComponentPath = .accepted exactCoverToSteinerTreeCertifiedReduction ∧
      exactCoverToSteinerTreeCertifiedReduction.program =
        PolyProg.atom exactCoverToSteinerTreePrimitive ∧
      exactCoverToSteinerTreeCertifiedReduction.program.run =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructuredTMMap ∧
      exactCoverToSteinerTreePrimitive.tmPolyTime =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeCertifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        exactCoverToSteinerTreeCertifiedReduction.program.compileTM ∧
      exactCoverToSteinerTreeCertifiedReduction.directTM =
        ComplexityReduction.Karp21.SteinerTree.exactCoverToSteinerTreeCompactStructured_tm_polytime ∧
      exactCoverToSteinerTreeCertifiedReduction.compatibilityCost =
        exactCoverToSteinerTreeCertifiedReduction.program.compatibilityCost := by
  exact ⟨exactCoverToSteinerTreeSharedGadgetResolution_exact,
    resolveComponentPath_exact,
    rfl,
    rfl,
    exactCoverToSteinerTreePrimitive_directTM_eq_legacy,
    exactCoverToSteinerTreeProgram_compileTM_eq_legacy,
    exactCoverToSteinerTreeCertifiedReduction_directTM_eq_compileTM,
    exactCoverToSteinerTreeCertifiedReduction_directTM_eq_legacy,
    exactCoverToSteinerTreeCertifiedReduction_compatibilityCost⟩

end ExactCoverToSteinerTree
end Routes
end ComplexityReduction
