/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Problems.Karp21.SATTractable
import ComplexityReduction.Protocol.ComponentResolver

/-!
Canonical direct-2CNF-to-structured-CNF ingress normalization.

The source and target codecs use the same finite alphabet, and encoding a
direct 2CNF formula is definitionally the target CNF encoding of its faithful
syntax embedding.  Thus the primitive reuses the established generic
identity-machine `TMPolyTimeMap.of_encodingEquiv`; it introduces neither a
route-local TM nor a cost-map admission path.  The sole ingress certificate
binds that primitive's program to the local satisfiability equivalence; no
route request enum or second whole-route certificate is declared.
-/

namespace ComplexityReduction
namespace Routes
namespace TwoCNFToCNF

open Encoding Program Certificate
open ComplexityReduction.SAT

/-- The exact V2 source presentation for the direct 2CNF syntax embedding. -/
abbrev sourcePresentation : LawfulEncodedType :=
  Problems.Karp21.SATTractable.twoCNFStructuredPresentation

/-- The exact V2 target presentation for the faithful list-based CNF syntax. -/
abbrev targetPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.cnfSATStructuredPresentation

/-- The exact direct-2CNF SAT endpoint of this route. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.SATTractable.twoCNFStructuredProblem

/-- The exact structured-CNF SAT endpoint of this route. -/
abbrev targetProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

/-- The original direct-2CNF endpoint is the source of this ingress adapter. -/
abbrev originalTwoCNFProblem : PresentedProblem :=
  sourceProblem

/-- The canonical clause-CNF hub is the ingress adapter's target. -/
abbrev clauseCNFHubProblem : PresentedProblem :=
  targetProblem

/-- The public target is already the canonical clause-CNF hub. -/
abbrev finalCNFSATProblem : PresentedProblem :=
  targetProblem

/-- The exact canonical ingress component endpoint for direct-2CNF normalization. -/
abbrev TwoCNFToCNFIngressEndpoint : Type 2 :=
  Protocol.ComponentEndpoint .ingress originalTwoCNFProblem clauseCNFHubProblem

/-- The exact canonical ingress request; it is not a route-local request language. -/
abbrev TwoCNFToCNFIngressRequest : Type 2 :=
  Protocol.ComponentRequest .ingress originalTwoCNFProblem clauseCNFHubProblem

/-- The unique exact ingress request for direct-2CNF normalization. -/
def twoCNFToCNFIngressRequest : TwoCNFToCNFIngressRequest :=
  .exact

/-- The request fixes the direct-2CNF source and clause-CNF hub endpoint exactly. -/
theorem twoCNFToCNFIngressRequest_endpoint_exact :
    twoCNFToCNFIngressRequest.endpoint =
      (show TwoCNFToCNFIngressEndpoint from .exact) :=
  rfl

/-- The literal embedding preserves evaluation under every assignment. -/
theorem literalToCNF_eval (literal : TwoCNF.Literal) (assignment : Assignment) :
    (Problems.Karp21.SATTractable.twoCNFLiteralToCNFLiteral literal).eval assignment =
      literal.eval assignment := by
  cases literal with
  | mk variableIndex positive =>
      cases positive <;> rfl

/-- The faithful direct-clause embedding preserves and reflects satisfaction. -/
theorem clauseToCNF_satisfies_iff (clause : TwoCNF.Clause) (assignment : Assignment) :
    Clause.Satisfies (Problems.Karp21.SATTractable.twoCNFClauseToCNFClause clause) assignment ↔
      TwoCNF.Clause.Satisfies clause assignment := by
  cases clause with
  | empty =>
      simp [Problems.Karp21.SATTractable.twoCNFClauseToCNFClause, Clause.Satisfies,
        TwoCNF.Clause.Satisfies]
  | unit literal =>
      simp [Problems.Karp21.SATTractable.twoCNFClauseToCNFClause, Clause.Satisfies,
        TwoCNF.Clause.Satisfies, literalToCNF_eval]
  | binary left right =>
      simp [Problems.Karp21.SATTractable.twoCNFClauseToCNFClause, Clause.Satisfies,
        TwoCNF.Clause.Satisfies, literalToCNF_eval]

/-- The faithful direct-2CNF syntax embedding preserves and reflects satisfaction. -/
theorem twoCNFToCNF_satisfies_iff (formula : TwoCNF.CNF) (assignment : Assignment) :
    CNF.Satisfies (Problems.Karp21.SATTractable.twoCNFToCNF formula) assignment ↔
      TwoCNF.CNF.Satisfies formula assignment := by
  constructor
  · intro satisfied clause clauseMem
    exact (clauseToCNF_satisfies_iff clause assignment).mp
      (satisfied (Problems.Karp21.SATTractable.twoCNFClauseToCNFClause clause)
        (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩))
  · intro satisfied encodedClause encodedClauseMem
    rcases List.mem_map.mp encodedClauseMem with ⟨clause, clauseMem, rfl⟩
    exact (clauseToCNF_satisfies_iff clause assignment).mpr (satisfied clause clauseMem)

/-- The syntax embedding preserves and reflects direct 2CNF satisfiability. -/
theorem twoCNFToCNF_satisfiable_iff (formula : TwoCNF.CNF) :
    CNF.Satisfiable (Problems.Karp21.SATTractable.twoCNFToCNF formula) ↔
      TwoCNF.CNF.Satisfiable formula := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignment, (twoCNFToCNF_satisfies_iff formula assignment).mp satisfied⟩
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignment, (twoCNFToCNF_satisfies_iff formula assignment).mpr satisfied⟩

/--
The existing generic identity-machine theorem certifies the exact 2CNF syntax
embedding: source and target word encodings are definitionally identical.
-/
theorem twoCNFToCNF_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      Problems.Karp21.SATTractable.twoCNFToCNF := by
  apply ComplexityReduction.TMPolyTimeMap.of_encodingEquiv
    sourcePresentation.encodedType targetPresentation.encodedType
    Problems.Karp21.SATTractable.twoCNFToCNF (Equiv.refl _)
  intro formula
  change ComplexityReduction.Karp21.cnfStructuredEncodedType.encode
      (Problems.Karp21.SATTractable.twoCNFToCNF formula) =
    List.map id (ComplexityReduction.Karp21.cnfStructuredEncodedType.encode
      (Problems.Karp21.SATTractable.twoCNFToCNF formula))
  rw [List.map_id]

/--
The one admitted V2 primitive for the faithful direct-2CNF syntax embedding.

Its declared indices are the route's two concrete `PresentedProblem`
representations, rather than auxiliary carrier aliases.  This is the sole
primitive admission boundary for the edge: the executable and direct-TM
witness below therefore cannot be reused at a same-carrier/different-codec
endpoint.
-/
@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime Problems.Karp21.SATTractable.twoCNFToCNF twoCNFToCNF_directTM

/-- The primitive source index is exactly the declared direct-2CNF endpoint representation. -/
@[simp]
theorem primitive_sourceEndpoint :
    sourceProblem.representation = sourcePresentation :=
  rfl

/-- The primitive target index is exactly the declared structured-CNF endpoint representation. -/
@[simp]
theorem primitive_targetEndpoint :
    targetProblem.representation = targetPresentation :=
  rfl

/-- The primitive executes exactly the source-to-target syntax embedding. -/
@[simp]
theorem primitive_run (formula : sourcePresentation.Carrier) :
    primitive.run formula = Problems.Karp21.SATTractable.twoCNFToCNF formula :=
  rfl

/-- Its stored direct-TM evidence is indexed by that same source-to-target executable. -/
theorem primitive_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      primitive.run :=
  primitive.tmPolyTime

/-- The primitive retains the exact generic direct-TM witness for its syntax executable. -/
theorem primitive_tmPolyTime_eq_twoCNFToCNF_directTM :
    primitive.tmPolyTime = twoCNFToCNF_directTM :=
  rfl

/--
The sole V2 program for this route is the one direct-TM-backed primitive atom.
Like `primitive`, its type exposes the concrete presented endpoints directly;
the source/target aliases remain only convenient theorem notation.
-/
noncomputable def program :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom primitive

/-- The route program is not a second computation: it is precisely the endpoint-indexed atom. -/
@[simp]
theorem program_eq_primitive_atom :
    program = PolyProg.atom primitive :=
  rfl

/-- The program has exactly the faithful direct-2CNF-to-CNF executable. -/
@[simp]
theorem program_run (formula : sourcePresentation.Carrier) :
    program.run formula = Problems.Karp21.SATTractable.twoCNFToCNF formula :=
  rfl

/-- Program compilation preserves the primitive's same-executable direct-TM evidence. -/
theorem program_compileTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      program.run :=
  program.compileTM

/-- Compiling the one-atom program retains the primitive's same-executable direct-TM witness. -/
@[simp]
theorem program_compileTM_eq_primitive_tmPolyTime :
    program.compileTM = primitive.tmPolyTime :=
  rfl

/--
The canonical typed 2CNF-to-CNF certificate.  Its semantic law, direct-TM
evidence, and derived compatibility cost all refer to `program`.
-/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def certifiedReduction : CertifiedReduction sourceProblem targetProblem where
  program := program
  correct := by
    intro formula
    simpa only [Problems.Karp21.SATTractable.twoCNFStructuredProblem_accepts,
      Problems.Karp21.Satisfiability.cnfSATStructuredProblem_accepts, program_run] using
      (twoCNFToCNF_satisfiable_iff formula).symm

/-- The certificate is accepted only at its exact direct-2CNF ingress endpoint. -/
noncomputable def twoCNFToCNFIngressResolution :
    Protocol.ComponentResolution .ingress originalTwoCNFProblem clauseCNFHubProblem :=
  Protocol.ComponentResolver.accept twoCNFToCNFIngressRequest certifiedReduction

/-- The final component path is this ingress adapter because the clause-CNF hub is final. -/
noncomputable def resolveComponentPath :
    Protocol.ResolverOutcome originalTwoCNFProblem finalCNFSATProblem :=
  Protocol.ComponentResolver.resolveSingle twoCNFToCNFIngressResolution

/-- The component resolver stores exactly the canonical ingress certificate. -/
@[simp] theorem twoCNFToCNFIngressResolution_exact :
    twoCNFToCNFIngressResolution = .accepted certifiedReduction :=
  rfl

/-- The component path yields precisely the accepted ingress adapter. -/
@[simp] theorem resolveComponentPath_exact :
    resolveComponentPath = .accepted certifiedReduction :=
  rfl

/-- The certified route stores the exact admitted program. -/
@[simp]
theorem certifiedReduction_program : certifiedReduction.program = program :=
  rfl

/-- The certificate stores exactly the endpoint-indexed primitive atom, with no route-local map. -/
@[simp]
theorem certifiedReduction_program_eq_primitive_atom :
    certifiedReduction.program = PolyProg.atom primitive :=
  rfl

/-- The semantic route law is indexed by the very executable in the stored program. -/
theorem certifiedReduction_correct (formula : sourceProblem.Instance) :
    sourceProblem.accepts formula ↔
      targetProblem.accepts (certifiedReduction.program.run formula) :=
  certifiedReduction.correct formula

/-- The certified route's direct-TM witness is derived by compiling its stored program. -/
theorem certifiedReduction_directTM :
    ComplexityReduction.TMPolyTimeMap sourcePresentation.encodedType targetPresentation.encodedType
      certifiedReduction.program.run :=
  certifiedReduction.directTM

/-- The certificate direct-TM projection is compilation of its one stored program. -/
@[simp]
theorem certifiedReduction_directTM_eq_program_compileTM :
    certifiedReduction.directTM = certifiedReduction.program.compileTM :=
  rfl

/-- The certificate compiler projection retains the endpoint primitive's direct-TM witness. -/
@[simp]
theorem certifiedReduction_directTM_eq_primitive_tmPolyTime :
    certifiedReduction.directTM = primitive.tmPolyTime :=
  rfl

/--
The sole legacy TM-Karp compatibility facade for this edge.  CR has no
separately bundled `TwoCNF -> CNF` TM-Karp record to admit here: this record
is deliberately the one-way projection of the canonical typed certificate.
Consequently it cannot supply a primitive, program, TM, or cost independently
of `certifiedReduction`.
-/
noncomputable def legacyTMKarpFacade :
    ComplexityReduction.TMKarpReduction sourceProblem.toEncodedDecisionProblem
      targetProblem.toEncodedDecisionProblem :=
  certifiedReduction.toTMKarpReduction

/-- The compatibility record is definitionally the certificate's one-way TM-Karp projection. -/
@[simp]
theorem legacyTMKarpFacade_eq_certifiedReduction_projection :
    legacyTMKarpFacade = certifiedReduction.toTMKarpReduction :=
  rfl

/-- The projected legacy executable is exactly the certificate's stored program executable. -/
@[simp]
theorem legacyTMKarpFacade_run :
    legacyTMKarpFacade.f = certifiedReduction.program.run :=
  CertifiedReduction.toTMKarpReduction_f certifiedReduction

/-- The projected legacy direct-TM evidence is compiled from that same program. -/
@[simp]
theorem legacyTMKarpFacade_directTM :
    legacyTMKarpFacade.polytime = certifiedReduction.program.compileTM := by
  change certifiedReduction.toTMKarpReduction.polytime =
    certifiedReduction.program.compileTM
  rw [CertifiedReduction.toTMKarpReduction_polytime,
    CertifiedReduction.directTM_eq_compileTM]

/--
Exact one-way coherence between the canonical typed certificate and its
legacy TM-Karp facade.  In particular, the facade neither introduces nor
upgrades an independently supplied direct TM or compatibility cost.
-/
theorem certifiedReduction_legacyTMKarpCoherence :
    legacyTMKarpFacade = certifiedReduction.toTMKarpReduction ∧
      legacyTMKarpFacade.f = certifiedReduction.program.run ∧
      legacyTMKarpFacade.polytime = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = primitive.tmPolyTime :=
  ⟨legacyTMKarpFacade_eq_certifiedReduction_projection, legacyTMKarpFacade_run,
    legacyTMKarpFacade_directTM, certifiedReduction_directTM_eq_primitive_tmPolyTime⟩

/--
Complete endpoint-exact provenance of the canonical 2CNF-to-CNF certificate.

The concrete representation identities, one primitive atom, syntax
executable, generic direct-TM witness, compiler result, compatibility cost,
and one-way TM-Karp facade all come from one stored `PolyProg`.  The generic
CR identity-machine theorem supplies the direct-TM evidence; no route-local
machine, cost-map lift, or independently assembled legacy route is present.
-/
theorem certifiedReduction_exactProgramCertificateProvenance :
    certifiedReduction.program.endpointIdentities =
        ⟨sourceProblem.representationIdentity, targetProblem.representationIdentity⟩ ∧
      certifiedReduction.program = PolyProg.atom primitive ∧
      certifiedReduction.program.run = Problems.Karp21.SATTractable.twoCNFToCNF ∧
      primitive.tmPolyTime = twoCNFToCNF_directTM ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = primitive.tmPolyTime ∧
      certifiedReduction.directTM = twoCNFToCNF_directTM ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost ∧
      legacyTMKarpFacade = certifiedReduction.toTMKarpReduction := by
  exact ⟨rfl, certifiedReduction_program_eq_primitive_atom, rfl,
    primitive_tmPolyTime_eq_twoCNFToCNF_directTM,
    certifiedReduction_directTM_eq_program_compileTM,
    certifiedReduction_directTM_eq_primitive_tmPolyTime,
    certifiedReduction_directTM_eq_primitive_tmPolyTime.trans
      primitive_tmPolyTime_eq_twoCNFToCNF_directTM,
    rfl,
    legacyTMKarpFacade_eq_certifiedReduction_projection⟩

/-- The compatibility facade is compiled from the same stored program, never separately authored. -/
@[simp]
theorem certifiedReduction_tmBackedCostedMap :
    certifiedReduction.toTMBackedCostedMap = certifiedReduction.program.compile :=
  rfl

/-- The route cost is only the compiler-derived projection of the certified program. -/
@[simp]
theorem certifiedReduction_compatibilityCost :
    certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost :=
  rfl

/-- The route cost comes from the output-size bound of that same compiled direct TM. -/
@[simp]
theorem certifiedReduction_compatibilityCost_eq_outputSizeBound :
    certifiedReduction.compatibilityCost =
      ComplexityReduction.CostedMap.of_encodedPolynomialSizeBound
        (ComplexityReduction.TMPolyTimeMap.outputSizeBound certifiedReduction.program.compileTM) :=
  certifiedReduction.program.compatibilityCost_eq_outputSizeBound

/--
The compatibility facade remains endpoint-exact all the way back to the one
canonical program.  In particular, its executable and TM witness are the
compiler projections at the concrete direct-2CNF/structured-CNF
representations, and the certificate cost is the corresponding compiler cost.
This deliberately records no independent CR TM-Karp witness or bare cost-map
admission path.
-/
theorem legacyTMKarpFacade_endpointExact_programRunDirectTMCostCoherence :
    sourceProblem.representation = sourcePresentation ∧
      targetProblem.representation = targetPresentation ∧
      certifiedReduction.program = program ∧
      legacyTMKarpFacade.f = program.run ∧
      legacyTMKarpFacade.polytime = program.compileTM ∧
      certifiedReduction.directTM = program.compileTM ∧
      certifiedReduction.compatibilityCost = program.compatibilityCost := by
  refine ⟨primitive_sourceEndpoint, primitive_targetEndpoint,
    certifiedReduction_program, ?_, ?_, ?_, ?_⟩
  · simpa only [certifiedReduction_program] using legacyTMKarpFacade_run
  · simpa only [certifiedReduction_program] using legacyTMKarpFacade_directTM
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · simpa only [certifiedReduction_program] using
      (CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction)

/-- All semantic, executable, TM, and cost evidence has one primitive-program identity. -/
theorem certifiedReduction_oneProgramChain :
    (∀ input,
      sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom primitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = primitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  refine ⟨certifiedReduction.correct, certifiedReduction_program_eq_primitive_atom, ?_, ?_, ?_⟩
  · exact CertifiedReduction.directTM_eq_compileTM certifiedReduction
  · exact certifiedReduction_directTM_eq_primitive_tmPolyTime
  · exact CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction

/-- The accepted ingress and its final path retain the sole program/certificate evidence chain. -/
theorem canonicalIngressAdapter_oneProgramChain :
    twoCNFToCNFIngressResolution = .accepted certifiedReduction ∧
      resolveComponentPath = .accepted certifiedReduction ∧
      (∀ input,
        sourceProblem.accepts input ↔ targetProblem.accepts (certifiedReduction.program.run input)) ∧
      certifiedReduction.program = PolyProg.atom primitive ∧
      certifiedReduction.directTM = certifiedReduction.program.compileTM ∧
      certifiedReduction.directTM = primitive.tmPolyTime ∧
      certifiedReduction.compatibilityCost = certifiedReduction.program.compatibilityCost := by
  exact ⟨twoCNFToCNFIngressResolution_exact, resolveComponentPath_exact,
    certifiedReduction.correct, certifiedReduction_program_eq_primitive_atom,
    CertifiedReduction.directTM_eq_compileTM certifiedReduction,
    certifiedReduction_directTM_eq_primitive_tmPolyTime,
    CertifiedReduction.compatibilityCost_eq_program_compatibilityCost certifiedReduction⟩

end TwoCNFToCNF
end Routes
end ComplexityReduction
