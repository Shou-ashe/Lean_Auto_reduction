/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Partition
import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical structured Partition-to-binary-Partition V2 route.

`ComplexityReduction` already supplies the representation-changing conversion
as an identity executable, its semantic law, and a direct-TM theorem. This
leaf admits that exact executable as one V2 primitive, so its certificate,
compiler, and compatibility-cost projections retain one program identity.
-/

namespace ComplexityReduction
namespace Routes
namespace PartitionToPartitionBinary

open Certificate Encoding Program

/-- The exact unary structured Partition presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Presentation.Partition.structuredPresentation

/-- The exact binary structured Partition presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Presentation.PartitionBinary.structuredPresentation

/-- The exact V2 unary structured Partition endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.Partition.structuredProblem

/-- The exact V2 binary structured Partition endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.PartitionBinary.structuredProblem

/--
The existing direct-TM Karp reduction at exactly the two V2 endpoints.

The simplification unfolds only the two lawful presentation aliases; it does
not re-encode inputs, rebuild a machine, or promote a bare compatibility cost.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.Partition.partitionStructuredToBinaryStructuredTMKarpReduction

/--
The reused structured conversion has exactly the pre-existing CR direct-TM
witness.  Proof irrelevance applies only after the executable and both exact
presentations have been fixed by `legacyStructuredReduction`.
-/
theorem legacyStructuredReduction_compileTM_eq_partitionStructuredToBinary :
    legacyStructuredReduction.polytime =
      ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime := by
  apply Subsingleton.elim

/-- The original unary structured Partition endpoint. -/
abbrev originalPartitionProblem : PresentedProblem :=
  sourceProblem

/-- The canonical binary Partition hub reached by the representation adapter. -/
abbrev partitionBinaryHubProblem : PresentedProblem :=
  targetProblem

/-- The final binary Partition endpoint is already the canonical hub. -/
abbrev finalPartitionBinaryProblem : PresentedProblem :=
  targetProblem

/-- The exact typed ingress endpoint of the unary-to-binary representation adapter. -/
abbrev PartitionBinaryIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalPartitionProblem partitionBinaryHubProblem

/-- The canonical request for the unary-to-binary normalization adapter. -/
abbrev PartitionBinaryIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalPartitionProblem partitionBinaryHubProblem

/-- The unique request for the direct-TM representation-changing ingress adapter. -/
def partitionBinaryIngressRequest : PartitionBinaryIngressRequest :=
  .exact

/-- The ingress request fixes the exact unary source and binary-hub endpoint. -/
theorem partitionBinaryIngressRequest_endpoint_exact :
    partitionBinaryIngressRequest.endpoint =
      (show PartitionBinaryIngressEndpoint from .exact) :=
  rfl

/-- The adapter lands directly at the final endpoint because the binary hub is final. -/
theorem partitionBinaryHub_is_finalEndpoint :
    partitionBinaryHubProblem = finalPartitionBinaryProblem :=
  rfl

/--
The exact standard-audited direct-TM primitive for CR's representation change.
Its executable is CR's identity conversion and its direct-TM theorem is the
existing `partitionStructuredToBinary_tm_polytime`; a legacy Karp facade is
not an input to this trusted primitive.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def partitionStructuredToBinaryPrimitive :
    Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime id
    ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime

/-- The direct primitive executes CR's exact representation conversion. -/
@[simp]
theorem partitionStructuredToBinaryPrimitive_run (input : sourceProblem.Instance) :
    partitionStructuredToBinaryPrimitive.run input = input :=
  rfl

/-- The sole route program is precisely the direct primitive atom. -/
noncomputable def partitionStructuredToBinaryProgram :
    PolyProg sourcePresentation targetPresentation :=
  .atom partitionStructuredToBinaryPrimitive

/-- The route stores exactly one direct-TM primitive atom. -/
@[simp]
theorem partitionStructuredToBinaryProgram_eq_atom :
    partitionStructuredToBinaryProgram =
      PolyProg.atom partitionStructuredToBinaryPrimitive :=
  rfl

/-- The one stored program executes CR's exact identity conversion. -/
@[simp]
theorem partitionStructuredToBinaryProgram_run (input : sourceProblem.Instance) :
    partitionStructuredToBinaryProgram.run input = input :=
  rfl

/-- The representation change preserves the one shared Partition predicate. -/
theorem partitionStructuredToBinaryProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔
      targetProblem.accepts (partitionStructuredToBinaryProgram.run input) := by
  change ComplexityReduction.Combinatorics.Partition input ↔
    ComplexityReduction.Combinatorics.Partition input
  rfl

/--
The sole canonical V2 Partition-to-binary-Partition certificate. Every
executable, semantic, direct-TM, compiler, and compatibility-cost projection
below comes from `partitionStructuredToBinaryProgram`; the legacy reduction is
only a read-only endpoint/evidence comparison.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := partitionStructuredToBinaryProgram
  correct := partitionStructuredToBinaryProgram_correct

/-- The certificate stores the sole direct primitive atom. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom
        partitionStructuredToBinaryPrimitive :=
  rfl

/-- The stored V2 program runs exactly CR's structured representation conversion. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = legacyStructuredReduction.f input :=
  rfl

/--
The exact reused structured conversion is the representation-changing identity
on `PartitionInput`; no route-local executable is introduced in V2.
-/
@[simp]
theorem certifiedReduction_run_eq_identity (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = input := by
  change id input = input
  rfl

/-- The route's semantic iff is indexed by the certified program's exact executable. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input) :=
  certifiedReduction.correct input

/-- Direct-TM evidence is derived by compiling the certified route's one program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The program compiler retains exactly the direct-TM witness from the legacy reduction. -/
@[simp]
theorem certifiedReduction_compileTM_eq_legacy :
    certifiedReduction.program.compileTM = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The compiler is exactly the direct-TM witness stored by the primitive atom. -/
@[simp]
theorem certifiedReduction_compileTM_eq_primitive :
    certifiedReduction.program.compileTM =
      partitionStructuredToBinaryPrimitive.tmPolyTime :=
  rfl

/--
The program compiler reaches the named CR unary-to-binary direct-TM theorem
at the route's exact endpoints.  It cannot derive this evidence from a
compatibility cost map.
-/
theorem certifiedReduction_compileTM_eq_partitionStructuredToBinary :
    certifiedReduction.program.compileTM =
      ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime :=
  certifiedReduction_compileTM_eq_legacy.trans
    legacyStructuredReduction_compileTM_eq_partitionStructuredToBinary

/--
The certificate's sole direct-TM projection is the same named existing direct
TM witness reached by compilation of its stored program.
-/
theorem certifiedReduction_directTM_eq_partitionStructuredToBinary :
    certifiedReduction.directTM =
      ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime :=
  CertifiedReduction.directTM_eq_compileTM certifiedReduction |>.trans
    certifiedReduction_compileTM_eq_partitionStructuredToBinary

/--
At the V2 presentations, compilation yields the existing direct-TM statement
for the identity conversion itself.  This statement is derived from the
certificate program; it is not an independently supplied route machine.
-/
theorem certifiedReduction_directTM_has_partitionStructuredToBinary :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      (fun input => input) := by
  have hRun : certifiedReduction.program.run = fun input => input := by
    funext input
    exact certifiedReduction_run_eq_identity input
  simpa only [hRun] using certifiedReduction.directTM

/--
The stored program retains the two *different* structured codec identities.

Both CR endpoints use the same `PartitionInput` carrier, so this is the
route-local guard against accidentally treating the unary-to-binary conversion
as a representation-preserving identity.  The executable is extensionally
`id`, but its typed program is still indexed by the selected unary source and
binary target presentations.
-/
theorem certifiedReduction_program_endpointIdentities :
    certifiedReduction.program.endpointIdentities =
      ⟨sourcePresentation.representation, targetPresentation.representation⟩ :=
  rfl

/--
The identity executable crosses distinct representation identities: its unary
source codec and binary target codec cannot be interchanged merely because
their carriers coincide.
-/
theorem certifiedReduction_program_endpointIdentities_ne :
    certifiedReduction.program.endpointIdentities.source ≠
      certifiedReduction.program.endpointIdentities.target := by
  simpa only [certifiedReduction_program_endpointIdentities,
    Presentation.Partition.structuredPresentation_representation,
    Presentation.PartitionBinary.structuredPresentation_representation] using
    Presentation.PartitionBinary.structuredPresentation_representation_ne_unary.symm

/-- The direct-TM Karp facade preserves the certified program executable. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The direct-TM Karp facade preserves compilation of that same program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/--
Two direct-TM Karp reductions at fixed endpoints are equal once their
executables agree.  Their remaining fields are propositions, so this does
not identify arbitrary machines or manufacture any TM evidence.
-/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/--
The certificate's legacy TM-Karp facade is exactly CR's already-proved
structured edge.  This packages executable, semantic, and direct-TM
coherence into one endpoint-fixed equality; the V2 certificate still derives
its witness by compiling `partitionStructuredToBinaryProgram`.
-/
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run input

/--
The V2 certificate projects back to CR's actual named structured direct-TM
Karp record, rather than merely to a route-local alias of that record.  The
proof compares the already-fixed executable at the already-fixed endpoints;
it neither supplies a new TM nor obtains cost evidence from a bare map.
-/
theorem certifiedReduction_tmKarpReduction_eq_partitionStructuredToBinaryStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.Partition.partitionStructuredToBinaryStructuredTMKarpReduction := by
  apply tmKarpReduction_eq_of_f_eq
  rw [certifiedReduction_tmKarpReduction_run_is_program]
  funext input
  exact certifiedReduction_run_eq_identity input

/--
The legacy TM-Karp facade reaches the same named CR direct-TM theorem only
through the compiler of the certificate's stored program.
-/
theorem certifiedReduction_tmKarpReduction_directTM_eq_partitionStructuredToBinary :
    certifiedReduction.toTMKarpReduction.polytime =
      ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime :=
  certifiedReduction_tmKarpReduction_directTM_is_program_compileTM.trans
    certifiedReduction_compileTM_eq_partitionStructuredToBinary

/--
Endpoint-exact coherence with CR's named structured Partition conversion.

Both endpoints, the direct-TM Karp facade, the certificate direct-TM field,
and the compiler of its one stored program are tied to the same existing CR
record.  This is an observation of the canonical typed certificate chain,
not a second route implementation.
-/
theorem certifiedReduction_endpointExact_partitionStructuredToBinaryStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.partitionStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Combinatorics.partitionBinaryStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.Partition.partitionStructuredToBinaryStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_partitionStructuredToBinaryStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_partitionStructuredToBinary,
    certifiedReduction_compileTM_eq_partitionStructuredToBinary⟩

/--
The exact structured direct-TM provenance of this canonical certificate.

This refines the general certificate compiler coherence theorem with CR's
named unary-to-binary evidence and the route's distinct codec identities.  In
particular, the apparent identity executable cannot hide an untyped
same-carrier conversion: its semantic facade, compiled direct-TM field,
TM-Karp facade, and compatibility cost are all projections of the one atom
at the two exact structured presentations.
-/
theorem certifiedReduction_structuredDirectTMProvenance :
    certifiedReduction.program = PolyProg.atom partitionStructuredToBinaryPrimitive ∧
      certifiedReduction.program.endpointIdentities =
        ⟨sourcePresentation.representation, targetPresentation.representation⟩ ∧
      certifiedReduction.program.endpointIdentities.source ≠
        certifiedReduction.program.endpointIdentities.target ∧
      certifiedReduction.toEncodedSemanticReduction.f = certifiedReduction.program.run ∧
      (∀ input,
        sourceProblem.accepts input ↔
          targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.directTM = certifiedReduction.program.compile.tm_polytime ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime =
        ComplexityReduction.Karp21.Partition.partitionStructuredToBinary_tm_polytime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compile.costed := by
  rcases CertifiedReduction.endpoint_exact_compile_coherence certifiedReduction with
    ⟨endpointIdentities, semanticRun, semanticCorrect, _compiledMap,
      directTMCompile, compatibilityCostCompile, tmKarpRun, tmKarpCompile⟩
  exact ⟨certifiedReduction_program, endpointIdentities,
    certifiedReduction_program_endpointIdentities_ne, semanticRun, semanticCorrect,
    directTMCompile, certifiedReduction_directTM_eq_partitionStructuredToBinary,
    tmKarpRun,
    tmKarpCompile.trans certifiedReduction_compileTM_eq_partitionStructuredToBinary,
    compatibilityCostCompile⟩

/-- The compatible TM-backed map is derived from program compilation, never from a bare cost. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  rfl

/-- The route compatibility cost is only the compiler projection of the stored program. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  rfl

/-- The compatibility cost follows only from the compiled direct-TM output-size theorem. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/--
The direct-TM conversion is an ingress normalization adapter, not a
whole-route primitive.  Its source/target codec identities remain indices even
though the executable is extensionally `id` on the common carrier.
-/
noncomputable def partitionToPartitionBinaryIngressResolution :
    Protocol.ComponentResolution .ingress originalPartitionProblem partitionBinaryHubProblem :=
  Protocol.ComponentResolver.accept partitionBinaryIngressRequest certifiedReduction

/-- The final path is the exact ingress adapter because the binary hub is the final endpoint. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalPartitionProblem finalPartitionBinaryProblem :=
  Protocol.ComponentResolver.resolveSingle partitionToPartitionBinaryIngressResolution

/-- The ingress resolution retains exactly the canonical adapter certificate. -/
@[simp] theorem partitionToPartitionBinaryIngressResolution_exact :
    partitionToPartitionBinaryIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the canonical ingress adapter. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- All semantic, executable, TM, and cost evidence has one primitive-program identity. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom partitionStructuredToBinaryPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = partitionStructuredToBinaryPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact certifiedReduction_compileTM_eq_primitive
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

end PartitionToPartitionBinary
end Routes
end ComplexityReduction
