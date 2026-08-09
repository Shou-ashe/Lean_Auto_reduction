/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Reductions
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical structured 3SAT-to-CNF-SAT ingress normalization.

`ComplexityReduction` already packages the proof-erasing bundled-3CNF wrapper
as one direct-TM Karp reduction at the faithful structured endpoints.  This
leaf projects exactly that evidence into the one V2 ingress component:
executable semantics, direct-TM compilation, and compatibility cost all remain
indexed by the component certificate's one stored `PolyProg`.  It declares no
route request enum or second whole-route resolver.
-/

namespace ComplexityReduction
namespace Routes
namespace ThreeSATToCNF

open Certificate Encoding Program

/-- The exact faithful structured bundled-3SAT presentation used by this route. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.threeSATStructuredPresentation

/-- The exact faithful structured CNF-SAT presentation used by this route. -/
abbrev targetPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.cnfSATStructuredPresentation

/-- The exact V2 structured bundled-3SAT endpoint. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The exact V2 structured CNF-SAT endpoint. -/
abbrev targetProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

/-- The original bundled-3SAT endpoint is the source of this ingress adapter. -/
abbrev originalThreeSATProblem : PresentedProblem :=
  sourceProblem

/-- The canonical CNF-SAT hub is the ingress adapter's target. -/
abbrev cnfSATHubProblem : PresentedProblem :=
  targetProblem

/-- The public target is already the canonical CNF-SAT hub. -/
abbrev finalCNFSATProblem : PresentedProblem :=
  targetProblem

/--
The existing direct-TM 3SAT-to-CNF-SAT wrapper at exactly the two V2 endpoints.
The proof unfolds only endpoint aliases; it introduces no route-local machine,
encoding transport, or legacy compatibility cost witness.
-/
noncomputable def legacyStructuredReduction :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem := by
  simpa [sourceProblem, sourcePresentation, targetProblem, targetPresentation] using
    ComplexityReduction.Karp21.threeSATToCNFSATStructuredTMKarpReduction

/-- The exact canonical ingress component endpoint for 3SAT normalization into the CNF hub. -/
abbrev ThreeSATToCNFIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalThreeSATProblem cnfSATHubProblem

/-- The exact canonical ingress request; it is not a route-local request language. -/
abbrev ThreeSATToCNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalThreeSATProblem cnfSATHubProblem

/-- The unique exact ingress request for the structured normalization adapter. -/
def threeSATToCNFIngressRequest : ThreeSATToCNFIngressRequest :=
  .exact

/-- The request fixes the bundled-3SAT source and CNF hub endpoint exactly. -/
theorem threeSATToCNFIngressRequest_endpoint_exact :
    threeSATToCNFIngressRequest.endpoint =
      (show ThreeSATToCNFIngressEndpoint from .exact) :=
  rfl

/--
The sole typed primitive for this ingress. Its executable and direct-TM witness
are CR's direct structured normalization theorem; the Karp record above remains
a read-only compatibility projection rather than an input to this constructor.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def directTMPrimitive : Primitive sourcePresentation targetPresentation :=
  Primitive.ofTMPolyTime ComplexityReduction.Karp21.threeCNFToCNF
    ComplexityReduction.Karp21.threeSATToCNFSATStructured_tm_polytime

/-- The primitive runs exactly the CR structured wrapper executable. -/
@[simp]
theorem directTMPrimitive_run (input : sourceProblem.Instance) :
    directTMPrimitive.run input = legacyStructuredReduction.f input :=
  rfl

/-- The primitive retains CR's named structured direct-TM theorem. -/
@[simp]
theorem directTMPrimitive_directTM_eq_standardDirectTM :
    directTMPrimitive.tmPolyTime =
      ComplexityReduction.Karp21.threeSATToCNFSATStructured_tm_polytime :=
  rfl

/-- The primitive's direct-TM witness agrees with the read-only CR Karp projection. -/
@[simp]
theorem directTMPrimitive_directTM :
    directTMPrimitive.tmPolyTime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The named route program is the exact direct-TM primitive atom. -/
noncomputable def program : PolyProg sourcePresentation targetPresentation :=
  .atom directTMPrimitive

/-- The named route program is exactly its direct-TM primitive atom. -/
@[simp]
theorem program_eq_atom : program = PolyProg.atom directTMPrimitive :=
  rfl

/-- The named one program executes precisely CR's structured wrapper. -/
@[simp]
theorem program_run (input : sourceProblem.Instance) :
    program.run input = legacyStructuredReduction.f input :=
  rfl

/-- Compiling the named program preserves the direct-TM witness of its primitive atom. -/
@[simp]
theorem program_compileTM_eq_directTMPrimitive_directTM :
    program.compileTM = directTMPrimitive.tmPolyTime :=
  rfl

/--
The sole canonical V2 3SAT-to-CNF-SAT ingress certificate. Its executable,
semantic iff, direct-TM evidence, and compatibility projections all derive
from `program`, whose one atom is the reused CR direct-TM primitive.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := legacyStructuredReduction.correct

/-- The ingress certificate is accepted only at its exact canonical endpoint. -/
noncomputable def threeSATToCNFIngressResolution :
    Protocol.ComponentResolution .ingress originalThreeSATProblem cnfSATHubProblem :=
  Protocol.ComponentResolver.accept threeSATToCNFIngressRequest certifiedReduction

/-- The final component path is the ingress adapter because the CNF hub is final. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalThreeSATProblem finalCNFSATProblem :=
  Protocol.ComponentResolver.resolveSingle threeSATToCNFIngressResolution

/-- The resolver stores exactly the canonical ingress certificate. -/
@[simp] theorem threeSATToCNFIngressResolution_exact :
    threeSATToCNFIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted ingress adapter. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certificate stores the one program atom projected from the legacy executable. -/
@[simp]
theorem certifiedReduction_program :
    certifiedReduction.program =
      PolyProg.atom directTMPrimitive :=
  rfl

/-- The certificate stores the route's one named direct-TM primitive program. -/
@[simp]
theorem certifiedReduction_program_eq_program :
    certifiedReduction.program = program :=
  rfl

/-- The stored V2 program runs exactly CR's structured bundled-3SAT wrapper. -/
@[simp]
theorem certifiedReduction_run (input : sourceProblem.Instance) :
    certifiedReduction.program.run input = legacyStructuredReduction.f input :=
  rfl

/-- The semantic facade exposes exactly the stored program executable. -/
@[simp]
theorem certifiedReduction_semanticReduction_run :
    certifiedReduction.toEncodedSemanticReduction.f = certifiedReduction.program.run :=
  rfl

/-- Consequently, the semantic facade is the reused direct-TM executable, not a second map. -/
@[simp]
theorem certifiedReduction_semanticReduction_eq_legacy :
    certifiedReduction.toEncodedSemanticReduction.f = legacyStructuredReduction.f :=
  rfl

/-- The route's semantic iff is indexed by the certified program's exact executable. -/
theorem certifiedReduction_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input) :=
  certifiedReduction.correct input

/-- Direct-TM evidence is derived by compiling the certificate's one stored program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The certificate's direct-TM projection is compilation of its one stored program. -/
@[simp]
theorem certifiedReduction_directTM_eq_program_compileTM :
    certifiedReduction.directTM = certifiedReduction.program.compileTM :=
  rfl

/-- The program compiler retains exactly the direct-TM witness from the legacy route. -/
@[simp]
theorem certifiedReduction_compileTM_eq_legacy :
    certifiedReduction.program.compileTM = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The direct-TM certificate projection is the exact witness used by the program atom. -/
@[simp]
theorem certifiedReduction_directTM_eq_legacy :
    certifiedReduction.directTM = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The compatible TM-backed map is derived from program compilation, never from a bare cost. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  rfl

/-- Its direct-TM field is the same witness supplied to the stored program atom. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap_directTM :
    certifiedReduction.toTMBackedCostedMap.tm_polytime = legacyStructuredReduction.polytime :=
  rfl

/-- The route compatibility cost is only the compiler projection of the stored program. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  rfl

/-- The compatibility cost follows only from the output-size theorem of the compiled direct TM. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/-- The legacy TM-Karp projection is a projection of the same program, with no route-local TM. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run :
    certifiedReduction.toTMKarpReduction.f = legacyStructuredReduction.f :=
  rfl

/-- The TM-Karp projection retains that program atom's direct-TM witness exactly. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM :
    certifiedReduction.toTMKarpReduction.polytime = legacyStructuredReduction.polytime :=
  Subsingleton.elim _ _

/-- The TM-Karp facade executes exactly the certificate's stored program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_run_is_program :
    certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The TM-Karp facade derives direct-TM evidence only by compiling that program. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_directTM_is_program_compileTM :
    certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM := by
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/-- Two fixed-endpoint TM-Karp reductions are equal when their executables agree. -/
private theorem tmKarpReduction_eq_of_f_eq
    {A B : ComplexityReduction.EncodedDecisionProblem}
    (first second : ComplexityReduction.TMKarpReduction A B)
    (h : first.f = second.f) : first = second := by
  cases first
  cases second
  cases h
  rfl

/-- Projecting the certificate back to CR recovers the exact endpoint-local direct-TM record. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction :
    certifiedReduction.toTMKarpReduction = legacyStructuredReduction :=
  tmKarpReduction_eq_of_f_eq _ _ (by
    rw [CertifiedReduction.toTMKarpReduction_f]
    funext input
    exact certifiedReduction_run input)

/-- The certificate facade recovers CR's one named structured 3SAT-to-CNF edge. -/
@[simp]
theorem certifiedReduction_tmKarpReduction_eq_threeSATToCNFSATStructuredTMKarpReduction :
    certifiedReduction.toTMKarpReduction =
      ComplexityReduction.Karp21.threeSATToCNFSATStructuredTMKarpReduction := by
  rw [certifiedReduction_tmKarpReduction_eq_legacyStructuredReduction]
  rfl

/-- The exact endpoints and every direct-TM facade refer to the same named CR structured edge. -/
theorem certifiedReduction_endpointExact_namedCRStructuredTMKarpCoherence :
    sourceProblem.toEncodedDecisionProblem =
        ComplexityReduction.Karp21.threeSATStructuredDecisionProblem ∧
      targetProblem.toEncodedDecisionProblem =
        ComplexityReduction.Karp21.satisfiabilityStructuredDecisionProblem ∧
      certifiedReduction.toTMKarpReduction =
        ComplexityReduction.Karp21.threeSATToCNFSATStructuredTMKarpReduction ∧
      certifiedReduction.toTMKarpReduction.f = certifiedReduction.program.run ∧
      certifiedReduction.toTMKarpReduction.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM =
        ComplexityReduction.Karp21.threeSATToCNFSATStructuredTMKarpReduction.polytime ∧
      certifiedReduction.program.compileTM =
        ComplexityReduction.Karp21.threeSATToCNFSATStructuredTMKarpReduction.polytime := by
  exact ⟨rfl, rfl,
    certifiedReduction_tmKarpReduction_eq_threeSATToCNFSATStructuredTMKarpReduction,
    certifiedReduction_tmKarpReduction_run_is_program,
    certifiedReduction_tmKarpReduction_directTM_is_program_compileTM,
    certifiedReduction_directTM_eq_legacy.trans (by rfl),
    certifiedReduction_compileTM_eq_legacy.trans (by rfl)⟩

/-- The concrete ingress keeps semantic, executable, TM, and cost evidence on one primitive atom. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom directTMPrimitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = directTMPrimitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · rfl
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

end ThreeSATToCNF
end Routes
end ComplexityReduction
