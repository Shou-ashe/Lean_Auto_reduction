import Benchmark.Hardness.Inputs.Authoring.ClosedFamily
import Benchmark.Hardness.Inputs.Authoring.LawfulPresentation
import Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission
import ComplexityReduction.Agent.Hardness.Runtime
import Lean.Elab.Command

/-!
Phase 4 regression coverage for closed-family instantiation, exact lawful
presentation skeletons, existing-executable primitive admission, and bundle
endpoint validation.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.Authoring

open Lean Elab Command Meta
open Encoding Certificate

private noncomputable abbrev source : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.ClosedFamily.source

private noncomputable abbrev target : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``source) (mkConst ``target) with
    | .ok _ => throwError "closed-family baseline unexpectedly resolved without a wrapper"
    | .error (.noRegistryPath ..) => pure ()
    | .error failure => throwError "unexpected closed-family baseline failure: {repr failure}"
    let candidates ← Agent.Hardness.Authoring.closedReductionFamilyInstantiations
      environment (mkConst ``source) (mkConst ``target)
    unless candidates.any fun candidate =>
        candidate.familyDeclaration ==
            ``Domain.BoolFiniteDomainCSPToStructuredCNF.sharedGadget &&
          candidate.argumentDeclarations == [``Presentation.ThreeSATLike.language] do
      throwError "closed family matcher did not recover the exact global-handle application"

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
private noncomputable def closedCandidate : CertifiedReduction source target :=
  Domain.BoolFiniteDomainCSPToStructuredCNF.sharedGadget Presentation.ThreeSATLike.language

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← Agent.Hardness.Authoring.validateCandidateReduction environment
        ``closedCandidate (mkConst ``source) (mkConst ``target) with
    | .ok () => pure ()
    | .error failure => throwError "exact closed-family candidate was rejected: {repr failure}"
    match ← Agent.Hardness.Authoring.validateCandidateReduction environment
        ``closedCandidate (mkConst ``source)
          (mkConst ``Problems.Karp21.Satisfiability.threeSATStructuredProblem) with
    | .error (.targetMismatch _) => pure ()
    | .error failure => throwError "wrong endpoint returned the wrong failure: {repr failure}"
    | .ok () => throwError "wrong endpoint candidate passed canonical validation"
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``source) (mkConst ``target) with
    | .error failure => throwError "closed-family candidate was not re-discovered: {repr failure}"
    | .ok path =>
        unless path.atomicProvenance.any fun provenance =>
            provenance.declaration == ``closedCandidate do
          throwError "closed-family route did not consume the validated local wrapper"

private noncomputable abbrev lawfulSource : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.LawfulPresentation.source

private noncomputable abbrev lawfulTarget : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.LawfulPresentation.target

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    let templates ← Agent.Hardness.Authoring.lawfulPresentationTemplates environment
      .ingress (mkConst ``lawfulSource) (mkConst ``lawfulTarget)
    unless templates.any fun observation =>
        observation.templateDeclaration ==
          ``Benchmark.Hardness.Inputs.Authoring.LawfulPresentation.template do
      throwError "exact lawful-presentation template was not discovered"
    let wrongRole ← Agent.Hardness.Authoring.lawfulPresentationTemplates environment
      .egress (mkConst ``lawfulSource) (mkConst ``lawfulTarget)
    unless wrongRole.isEmpty do
      throwError "lawful-presentation template was accepted at the wrong component role"

@[complexity_reduction_ir_typed_presentation]
def lawfulCapability : StructuralRepresentationCertificate
    lawfulSource.representation.encodedType lawfulSource.representation.representation :=
  Benchmark.Hardness.Inputs.Authoring.LawfulPresentation.template.toStructuralCertificate

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def lawfulRoute : CertifiedReduction lawfulSource lawfulTarget :=
  Benchmark.Hardness.Inputs.Authoring.LawfulPresentation.template.toReduction lawfulCapability

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← Agent.Hardness.Authoring.validateLawfulPresentationBundle environment
        ``lawfulCapability ``lawfulRoute (mkConst ``lawfulSource) (mkConst ``lawfulTarget) with
    | .ok () => pure ()
    | .error failure =>
        throwError "exact lawful-presentation bundle was rejected: {repr failure}"
    match ← Agent.Hardness.Authoring.validateLawfulPresentationBundle environment
        ``lawfulCapability ``lawfulRoute (mkConst ``source) (mkConst ``lawfulTarget) with
    | .error (.structuralEncodedTypeMismatch _) => pure ()
    | .error (.structuralIdentityMismatch _) => pure ()
    | .error failure =>
        throwError "wrong structural endpoint returned the wrong failure: {repr failure}"
    | .ok () => throwError "wrong structural endpoint passed bundle validation"
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``lawfulSource) (mkConst ``lawfulTarget) with
    | .error failure => throwError "lawful-presentation route was not re-discovered: {repr failure}"
    | .ok path =>
        unless path.atomicProvenance.any fun provenance =>
            provenance.declaration == ``lawfulRoute do
          throwError "lawful-presentation route did not consume the generated bundle"

private noncomputable abbrev primitiveSource : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission.source

private noncomputable abbrev primitiveTarget : PresentedProblem :=
  Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission.target

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    let templates ← Agent.Hardness.Authoring.primitiveAdmissionTemplates environment
      .sharedGadget (mkConst ``primitiveSource) (mkConst ``primitiveTarget)
    unless templates.any fun observation =>
        observation.templateDeclaration ==
          ``Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission.template do
      throwError "exact primitive-admission template was not discovered"
    let wrongEndpoint ← Agent.Hardness.Authoring.primitiveAdmissionTemplates environment
      .sharedGadget (mkConst ``primitiveSource) (mkConst ``target)
    unless wrongEndpoint.isEmpty do
      throwError "primitive-admission template was accepted at a wrong exact target"

@[complexity_reduction_ir_typed_primitive]
noncomputable def primitiveCapability :
    Program.Primitive primitiveSource.representation primitiveTarget.representation :=
  Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission.template.toPrimitive

@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def primitiveRoute : CertifiedReduction primitiveSource primitiveTarget :=
  Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission.template.toReduction
    primitiveCapability rfl

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← Agent.Hardness.Authoring.validatePrimitiveAdmissionBundle environment
        ``primitiveCapability ``primitiveRoute
          (mkConst ``primitiveSource) (mkConst ``primitiveTarget) with
    | .ok () => pure ()
    | .error failure => throwError "exact primitive-admission bundle was rejected: {repr failure}"
    match ← Agent.Hardness.Authoring.validatePrimitiveAdmissionBundle environment
        ``primitiveCapability ``primitiveRoute (mkConst ``primitiveSource) (mkConst ``target) with
    | .error (.primitiveTargetMismatch _) => pure ()
    | .error failure =>
        throwError "wrong primitive endpoint returned the wrong failure: {repr failure}"
    | .ok () => throwError "wrong primitive endpoint passed bundle validation"
    match ← Protocol.ClosedResolver.resolvePath environment
        (mkConst ``primitiveSource) (mkConst ``primitiveTarget) with
    | .error failure => throwError "primitive-admission route was not re-discovered: {repr failure}"
    | .ok path =>
        unless path.atomicProvenance.any fun provenance =>
            provenance.declaration == ``primitiveRoute do
          throwError "primitive-admission route did not consume the generated primitive"

end ComplexityReduction.Agent.Hardness.Regression.Authoring
