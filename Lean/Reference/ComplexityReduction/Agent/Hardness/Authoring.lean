/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Agent.Hardness.ModelAuthoring
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Registry.ParameterizedFamily
import Lean.Attributes
import Lean.Elab.Command

/-!
Lean-owned discovery and validation primitives for job-local hardness authoring.

Parameterized-family and fixed-template matches are observations only.  They
expose closed applications made solely from global declaration handles, but do
not add those applications to the registry.  A generated wrapper must still
compile, carry candidate attributes, pass canonical declaration validation,
and be re-discovered by the final closed resolver.
-/

namespace ComplexityReduction.Agent.Hardness.Authoring

open Lean Elab Command Meta
open Encoding Certificate Program Registry

/--
The fixed Phase-4 presentation skeleton.

The source structural origin is indexed by the exact concrete encoder and
complete representation identity.  The executable adapter separately carries
alphabet-level encoding coherence and semantic correctness at the exact
presented endpoints.  There is no carrier-equivalence or metadata field from
which structural admission could be manufactured.
-/
structure LawfulPresentationTemplate
    (role : ReductionComponentRole) (source target : PresentedProblem) where
  origin : StructuralRepresentationOrigin
    source.representation.encodedType source.representation.representation
  run : source.Instance → target.Instance
  alphabetEquiv : source.representation.encodedType.Symbol ≃
    target.representation.encodedType.Symbol
  encodeCoherence : ∀ input,
    target.representation.encodedType.encode (run input) =
      (source.representation.encodedType.encode input).map alphabetEquiv
  correct : ∀ input, source.accepts input ↔ target.accepts (run input)

namespace LawfulPresentationTemplate

/-- Close the exact structural certificate exposed by a lawful-presentation template. -/
def toStructuralCertificate {role : ReductionComponentRole} {source target : PresentedProblem}
    (template : LawfulPresentationTemplate role source target) :
    source.representation.StructuralCertificate :=
  source.representation.structuralCertificateOfOrigin template.origin

/--
Derive the exact route wrapper only after the generated bundle supplies the
source structural certificate.  The certificate argument is an admission
gate at the same exact representation index; the executable, coherence, and
semantic theorem remain those of this one template.
-/
def toReduction {role : ReductionComponentRole} {source target : PresentedProblem}
    (template : LawfulPresentationTemplate role source target)
    (_certificate : source.representation.StructuralCertificate) :
    CertifiedReduction source target :=
  CertifiedReduction.ofEncodingEquiv template.run template.alphabetEquiv
    template.encodeCoherence template.correct

end LawfulPresentationTemplate

/--
The fixed Phase-4 admission skeleton for an executable which already has a
direct-TM witness.  The witness is dependent on this exact `run`; a cost-only
map or evidence for a second executable cannot inhabit the template.
-/
structure PrimitiveAdmissionTemplate
    (role : ReductionComponentRole) (source target : PresentedProblem) where
  run : source.Instance → target.Instance
  tmPolyTime : ComplexityReduction.TMPolyTimeMap
    source.representation.encodedType target.representation.encodedType run
  correct : ∀ input, source.accepts input ↔ target.accepts (run input)

namespace PrimitiveAdmissionTemplate

/-- Admit exactly the template executable and its dependent direct-TM witness. -/
def toPrimitive {role : ReductionComponentRole} {source target : PresentedProblem}
    (template : PrimitiveAdmissionTemplate role source target) :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime template.run template.tmPolyTime

/--
Package the named generated primitive into a route.  The equality premise
forces the semantic theorem to be reindexed to that same primitive executable,
rather than silently introducing a second map.
-/
def toReduction {role : ReductionComponentRole} {source target : PresentedProblem}
    (template : PrimitiveAdmissionTemplate role source target)
    (primitive : Primitive source.representation target.representation)
    (run_eq : primitive.run = template.run) : CertifiedReduction source target where
  program := .atom primitive
  correct := by
    intro input
    change source.accepts input ↔ target.accepts (primitive.run input)
    rw [run_eq]
    exact template.correct input

end PrimitiveAdmissionTemplate

/--
The fixed Phase-5 observation marker for a complete new atomic reduction.

The three components are explicit type parameters and must be closed global
declarations.  The marker itself is never referenced by generated code.  This
is important for dependency isolation: a non-standard semantic proof must not
taint the independently audited executable or direct-TM checkpoint merely
because all three were fields of one structure value.
-/
structure ProgramIndexedReductionTemplate
    (role : ReductionComponentRole) (source target : PresentedProblem)
    (run : source.Instance → target.Instance)
    (directTM : ExecutableDirectTMEvidence source target run)
    (correct : ExecutableSemanticProof source target run) : Prop where
  witness : True

namespace ProgramIndexedReductionTemplate

/-- Reindex one independent dependent-TM declaration to the generated executable. -/
def toExecutableDirectTM {source target : PresentedProblem}
    {templateRun : source.Instance → target.Instance}
    (templateDirectTM : ExecutableDirectTMEvidence source target templateRun)
    (run : source.Instance → target.Instance) (run_eq : run = templateRun) :
    ExecutableDirectTMEvidence source target run := by
  simpa [ExecutableDirectTMEvidence, run_eq] using templateDirectTM

/-- Construct the exact primitive only from the generated executable and its dependent witness. -/
def toPrimitive {source target : PresentedProblem}
    (run : source.Instance → target.Instance)
    (directTM : ExecutableDirectTMEvidence source target run) :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime run directTM

/-- The Phase-5 atomic program embeds exactly the generated primitive. -/
def toProgram {source target : PresentedProblem}
    (primitive : Primitive source.representation target.representation) :
    PolyProg source.representation target.representation :=
  .atom primitive

/--
Reindex mathematical correctness to one exact generated program.  The
equality premise prevents a semantic theorem for a second map from being
silently installed at this checkpoint.
-/
def toSemanticProof {source target : PresentedProblem}
    {templateRun : source.Instance → target.Instance}
    (templateCorrect : ExecutableSemanticProof source target templateRun)
    (program : PolyProg source.representation target.representation)
    (run_eq : program.run = templateRun) :
    ProgramSemanticProof source target program := by
  intro input
  change source.accepts input ↔ target.accepts (program.run input)
  rw [run_eq]
  exact templateCorrect input

/-- Obtain real program-indexed direct-TM evidence from the exact program compiler. -/
def toProgramDirectTM {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation) :
    ProgramDirectTMEvidence source target program :=
  program.compileTM

/-- Package exactly the program to which the semantic checkpoint is indexed. -/
def toReduction {source target : PresentedProblem}
    (program : PolyProg source.representation target.representation)
    (semantic : ProgramSemanticProof source target program) :
    CertifiedReduction source target where
  program := program
  correct := semantic

end ProgramIndexedReductionTemplate

/--
The fixed Phase-6 observation marker for exact native membership authoring.

The verifier, the structural certificate for that verifier's exact witness
presentation, and the discipline indexed by that same verifier are separate
closed global declarations.  Generated code never references this marker
value; it imports the three component handles independently so axiom and
dependency isolation remains stage-local.
-/
structure NativeMembershipTemplate
    (problem : PresentedProblem)
    (verifier : CertifiedVerifier problem)
    (witnessPresentation : verifier.witness.StructuralCertificate)
    (discipline : CertifiedVerifierEncodingDiscipline verifier) : Prop where
  witness : True

namespace NativeMembershipTemplate

/-- Re-export exactly the observed verifier at the generated verifier checkpoint. -/
def toVerifier {problem : PresentedProblem}
    (templateVerifier : CertifiedVerifier problem) : CertifiedVerifier problem :=
  templateVerifier

/--
Reindex the observed structural witness certificate to the generated verifier.
The equality premise prevents a certificate for a second witness presentation
or verifier from entering the bundle.
-/
def toWitnessPresentation {problem : PresentedProblem}
    {templateVerifier : CertifiedVerifier problem}
    (templatePresentation : templateVerifier.witness.StructuralCertificate)
    (verifier : CertifiedVerifier problem) (verifier_eq : verifier = templateVerifier) :
    verifier.witness.StructuralCertificate := by
  cases verifier_eq
  exact templatePresentation

/-- Reindex the observed discipline to the exact generated verifier. -/
def toDiscipline {problem : PresentedProblem}
    {templateVerifier : CertifiedVerifier problem}
    (templateDiscipline : CertifiedVerifierEncodingDiscipline templateVerifier)
    (verifier : CertifiedVerifier problem) (verifier_eq : verifier = templateVerifier) :
    CertifiedVerifierEncodingDiscipline verifier := by
  cases verifier_eq
  exact templateDiscipline

/--
Close exact native membership only from one verifier, its exact witness
presentation admission, and the discipline indexed by that verifier.
-/
def toNativeMembership {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem)
    (_witnessPresentation : verifier.witness.StructuralCertificate)
    (discipline : CertifiedVerifierEncodingDiscipline verifier) : NativeTMInNP problem :=
  NativeTMInNP.ofCapability (NativeVerifierCapability.mk verifier discipline)

end NativeMembershipTemplate

/-- Discovery-only marker for one exact lawful-presentation authoring template. -/
initialize lawfulPresentationTemplateAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_hardness_lawful_presentation_template
    "marks a fixed lawful-presentation authoring template; grants no trusted capability"

/-- Discovery-only marker for one exact direct-TM primitive-admission template. -/
initialize primitiveAdmissionTemplateAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_hardness_primitive_admission_template
    "marks a fixed primitive-admission authoring template; grants no trusted capability"

/-- Discovery-only marker for one complete program-indexed reduction authoring template. -/
initialize programIndexedReductionTemplateAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_hardness_program_reduction_template
    "marks a fixed program-indexed reduction template; grants no trusted capability"

/-- Discovery-only marker for one exact staged native-membership template. -/
initialize nativeMembershipTemplateAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_hardness_native_membership_template
    "marks a fixed native-membership authoring template; grants no trusted capability"

/-- Stable kinds of exact deterministic template observations. -/
inductive ExactTemplateKind where
  | lawfulPresentation
  | primitiveAdmission
  | programIndexedReduction
  | programIndexedModel
  | nativeMembership
  deriving BEq, Repr

namespace ExactTemplateKind

def label : ExactTemplateKind → String
  | .lawfulPresentation => "lawful_presentation"
  | .primitiveAdmission => "primitive_admission"
  | .programIndexedReduction => "program_indexed_reduction"
  | .programIndexedModel => "program_indexed_model"
  | .nativeMembership => "native_membership"

end ExactTemplateKind

/-- One exact, closed, attributed fixed-template observation. -/
structure ExactTemplateObservation where
  templateDeclaration : Name
  kind : ExactTemplateKind
  role : ReductionComponentRole
  componentDeclarations : List Name := []
  deriving Repr

/-- One closed, exact-endpoint application of an observed parameterized family. -/
structure ClosedFamilyInstantiation where
  familyDeclaration : Name
  argumentDeclarations : List Name
  role : ReductionComponentRole
  deriving Repr

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def candidatesOfAttribute (tag : Lean.TagAttribute) (environment : Environment) :
    Lean.NameSet :=
  let discovered :=
    (Array.range environment.allImportedModuleNames.size).foldl
      (fun candidates moduleIndex =>
        (tag.ext.getModuleEntries environment moduleIndex).foldl
          (fun candidates candidate => candidates.insert candidate) candidates)
      (tag.ext.getState environment)
  discovered.foldl
    (fun candidates candidate =>
      if tag.hasTag environment candidate then candidates.insert candidate else candidates)
    {}

private def roleOfExpr? (expression : Expr) : Option ReductionComponentRole :=
  let expression := expression.consumeMData
  if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.ingress then
    some .ingress
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.sharedGadget then
    some .sharedGadget
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.egress then
    some .egress
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.finalComposition then
    some .finalComposition
  else
    none

private def closedConstantName? (argument : Expr) : Option Name :=
  let argument := argument.consumeMData
  if argument.hasFVar || argument.hasMVar || argument.hasLooseBVars then
    none
  else
    match argument with
    | .const name _ => some name
    | _ => none

private def exactTemplateType? (type : Expr) (head : Name) :
    Option (ReductionComponentRole × Expr × Expr) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    none
  else
    let normalized := type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf head do
      none
    match normalized.getAppArgs with
    | #[roleExpression, source, target] =>
        let role ← roleOfExpr? roleExpression
        some (role, source, target)
    | _ => none

private def exactTemplateObservations (environment : Environment)
    (tag : Lean.TagAttribute) (head : Name) (kind : ExactTemplateKind)
    (role : ReductionComponentRole) (source target : Expr) :
    MetaM (List ExactTemplateObservation) := do
  let mut observations := []
  for candidate in Std.TreeSet.toList (candidatesOfAttribute tag environment) do
    let some declaration := environment.find? candidate
      | continue
    unless declaration.levelParams.isEmpty do
      continue
    let some (checkedRole, checkedSource, checkedTarget) :=
        exactTemplateType? declaration.type head
      | continue
    unless checkedRole == role do
      continue
    unless ← controlledDefEq checkedSource source do
      continue
    unless ← controlledDefEq checkedTarget target do
      continue
    observations := observations ++ [{
      templateDeclaration := candidate
      kind
      role := checkedRole
      componentDeclarations := []
    }]
  return observations

/--
Discover only closed, exact-endpoint lawful-presentation templates for one
typed gap.  The tag contributes a name; the declaration's elaborated type is
the sole source of its role and endpoints.
-/
def lawfulPresentationTemplates (environment : Environment)
    (role : ReductionComponentRole) (source target : Expr) :
    MetaM (List ExactTemplateObservation) :=
  exactTemplateObservations environment lawfulPresentationTemplateAttr
    ``LawfulPresentationTemplate .lawfulPresentation role source target

/-- Discover only closed, exact-endpoint existing-executable admission templates. -/
def primitiveAdmissionTemplates (environment : Environment)
    (role : ReductionComponentRole) (source target : Expr) :
    MetaM (List ExactTemplateObservation) :=
  exactTemplateObservations environment primitiveAdmissionTemplateAttr
    ``PrimitiveAdmissionTemplate .primitiveAdmission role source target

/--
Discover only closed, exact-endpoint Phase-5 markers whose executable,
dependent direct-TM witness, and semantic theorem are three distinct global
declaration handles encoded in the marker's elaborated type.
-/
def programIndexedReductionTemplates (environment : Environment)
    (role : ReductionComponentRole) (source target : Expr) :
    MetaM (List ExactTemplateObservation) := do
  let mut observations := []
  for candidate in Std.TreeSet.toList
      (candidatesOfAttribute programIndexedReductionTemplateAttr environment) do
    let some declaration := environment.find? candidate
      | continue
    unless declaration.levelParams.isEmpty do
      continue
    let normalized := declaration.type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf ``ProgramIndexedReductionTemplate do
      continue
    let #[roleExpression, checkedSource, checkedTarget, run, directTM, correct] :=
        normalized.getAppArgs
      | continue
    let some checkedRole := roleOfExpr? roleExpression
      | continue
    unless checkedRole == role do
      continue
    unless ← controlledDefEq checkedSource source do
      continue
    unless ← controlledDefEq checkedTarget target do
      continue
    let some runDeclaration := closedConstantName? run
      | continue
    let some directTMDeclaration := closedConstantName? directTM
      | continue
    let some correctDeclaration := closedConstantName? correct
      | continue
    unless (environment.find? runDeclaration).isSome &&
        (environment.find? directTMDeclaration).isSome &&
        (environment.find? correctDeclaration).isSome do
      continue
    observations := observations ++ [{
      templateDeclaration := candidate
      kind := .programIndexedReduction
      role := checkedRole
      componentDeclarations := [runDeclaration, directTMDeclaration, correctDeclaration]
    }]
  return observations

/--
Discover only exact-endpoint Phase-7 markers whose executable and dependent
direct-TM witness are closed global declarations.  No semantic proof handle is
present in this observation, so the public prompt cannot obtain the gold proof
through template metadata.
-/
def programIndexedModelTemplates (environment : Environment)
    (role : ReductionComponentRole) (source target : Expr) :
    MetaM (List ExactTemplateObservation) := do
  let mut observations := []
  for candidate in Std.TreeSet.toList
      (candidatesOfAttribute programIndexedModelTemplateAttr environment) do
    let some declaration := environment.find? candidate
      | continue
    unless declaration.levelParams.isEmpty do
      continue
    let normalized := declaration.type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf ``ProgramIndexedModelTemplate do
      continue
    let #[roleExpression, checkedSource, checkedTarget, run, directTM] :=
        normalized.getAppArgs
      | continue
    let some checkedRole := roleOfExpr? roleExpression
      | continue
    unless checkedRole == role do
      continue
    unless ← controlledDefEq checkedSource source do
      continue
    unless ← controlledDefEq checkedTarget target do
      continue
    let some runDeclaration := closedConstantName? run
      | continue
    let some directTMDeclaration := closedConstantName? directTM
      | continue
    unless (environment.find? runDeclaration).isSome &&
        (environment.find? directTMDeclaration).isSome do
      continue
    observations := observations ++ [{
      templateDeclaration := candidate
      kind := .programIndexedModel
      role := checkedRole
      componentDeclarations := [runDeclaration, directTMDeclaration]
    }]
  return observations

/--
Discover only closed Phase-6 membership markers whose verifier, witness
presentation certificate, and verifier-indexed discipline are three distinct
global declaration handles encoded in the marker's elaborated type.
-/
def nativeMembershipTemplates (environment : Environment) (problem : Expr) :
    MetaM (List ExactTemplateObservation) := do
  let mut observations := []
  for candidate in Std.TreeSet.toList
      (candidatesOfAttribute nativeMembershipTemplateAttr environment) do
    let some declaration := environment.find? candidate
      | continue
    unless declaration.levelParams.isEmpty do
      continue
    let normalized := declaration.type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf ``NativeMembershipTemplate do
      continue
    let #[checkedProblem, verifier, witnessPresentation, discipline] := normalized.getAppArgs
      | continue
    unless ← controlledDefEq checkedProblem problem do
      continue
    let some verifierDeclaration := closedConstantName? verifier
      | continue
    let some witnessPresentationDeclaration := closedConstantName? witnessPresentation
      | continue
    let some disciplineDeclaration := closedConstantName? discipline
      | continue
    unless (environment.find? verifierDeclaration).isSome &&
        (environment.find? witnessPresentationDeclaration).isSome &&
        (environment.find? disciplineDeclaration).isSome do
      continue
    observations := observations ++ [{
      templateDeclaration := candidate
      kind := .nativeMembership
      role := .finalComposition
      componentDeclarations := [verifierDeclaration, witnessPresentationDeclaration,
        disciplineDeclaration]
    }]
  return observations

private def certifiedReductionEndpoints? (type : Expr) : Option (Expr × Expr) :=
  let type := type.consumeMData
  if type.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Certificate.CertifiedReduction then
    match type.getAppArgs with
    | #[source, target] => some (source, target)
    | _ => none
  else
    none

private def closeReductionFamily?
    {environment : Environment}
    (observation : ParameterizedCapabilityFamilyObservation environment)
    (source target : Expr) : MetaM (Option ClosedFamilyInstantiation) := do
  let some declaration := environment.find? observation.candidate
    | return none
  unless declaration.levelParams.isEmpty do
    return none
  let some provenance := observation.componentRoleProvenance?
    | return none
  match observation.capabilityTemplate with
  | .certifiedReduction .. => pure ()
  | _ => return none
  let (arguments, _, resultType) ← forallMetaTelescope observation.elaboratedType
  let some (familySource, familyTarget) := certifiedReductionEndpoints? resultType
    | return none
  unless ← controlledDefEq familySource source do
    return none
  unless ← controlledDefEq familyTarget target do
    return none
  let mut argumentDeclarations := []
  for argument in arguments do
    let argument ← instantiateMVars argument
    let some declarationName := closedConstantName? argument
      | return none
    argumentDeclarations := argumentDeclarations ++ [declarationName]
  return some {
    familyDeclaration := observation.candidate
    argumentDeclarations
    role := provenance.role
  }

/--
Find deterministic, closed global-handle applications of attributed reduction
families at one exact pair of presented endpoints.

The returned records remain non-authoritative scheduling data.  In particular,
this function does not create a declaration, registry entry, graph edge, or
certificate term accepted by the resolver.
-/
def closedReductionFamilyInstantiations (environment : Environment)
    (source target : Expr) : MetaM (List ClosedFamilyInstantiation) := do
  let mut candidates := []
  for observation in attributedParameterizedCapabilityFamilies environment do
    match ← closeReductionFamily? observation source target with
    | some candidate => candidates := candidates ++ [candidate]
    | none => pure ()
  return candidates

/-- Stable rejection classes for canonical candidate-head validation. -/
inductive CandidateValidationFailure where
  | unknownCandidate (candidate : Name)
  | notAttributedCanonicalCapability (candidate : Name)
  | wrongCapabilityHead (candidate : Name)
  | sourceMismatch (candidate : Name)
  | targetMismatch (candidate : Name)
  deriving Repr

/--
Re-run attribute discovery and canonical type classification for one generated
candidate, then require definitionally exact requested endpoints.
-/
def validateCandidateReduction (environment : Environment) (candidate : Name)
    (source target : Expr) : MetaM (Except CandidateValidationFailure Unit) := do
  if (environment.find? candidate).isNone then
    return .error (.unknownCandidate candidate)
  let some entry := validateAttributedDeclaration environment candidate
    | return .error (.notAttributedCanonicalCapability candidate)
  match entry.capability with
  | .certifiedReduction checkedSource checkedTarget =>
      unless ← controlledDefEq checkedSource source do
        return .error (.sourceMismatch candidate)
      unless ← controlledDefEq checkedTarget target do
        return .error (.targetMismatch candidate)
      let term := mkConst candidate
      match classifyElaboratedType (← inferType term) with
      | some (.certifiedReduction canonicalSource canonicalTarget) =>
          unless ← controlledDefEq canonicalSource source do
            return .error (.sourceMismatch candidate)
          unless ← controlledDefEq canonicalTarget target do
            return .error (.targetMismatch candidate)
          return .ok ()
      | _ => return .error (.wrongCapabilityHead candidate)
  | _ => return .error (.wrongCapabilityHead candidate)

/-- Stable rejection classes for a fixed-template primary capability plus route bundle. -/
inductive CandidateBundleValidationFailure where
  | unknownPrimary (candidate : Name)
  | primaryNotAttributedCanonicalCapability (candidate : Name)
  | wrongPrimaryCapabilityHead (candidate : Name)
  | structuralEncodedTypeMismatch (candidate : Name)
  | structuralIdentityMismatch (candidate : Name)
  | primitiveSourceMismatch (candidate : Name)
  | primitiveTargetMismatch (candidate : Name)
  | routeFailure (failure : CandidateValidationFailure)
  deriving Repr

private def representationTerms (problem : Expr) : MetaM (Expr × Expr × Expr) := do
  let representation ← mkAppM ``PresentedProblem.representation #[problem]
  let encodedType ← mkAppM ``LawfulEncodedType.encodedType #[representation]
  let identity ← mkAppM ``LawfulEncodedType.representation #[representation]
  return (representation, encodedType, identity)

private def validateStructuralPrimary (environment : Environment) (candidate : Name)
    (source : Expr) : MetaM (Except CandidateBundleValidationFailure Unit) := do
  if (environment.find? candidate).isNone then
    return .error (.unknownPrimary candidate)
  let some entry := validateAttributedDeclaration environment candidate
    | return .error (.primaryNotAttributedCanonicalCapability candidate)
  let (_, expectedEncodedType, expectedIdentity) ← representationTerms source
  match entry.capability with
  | .structuralPresentation checkedEncodedType checkedIdentity =>
      unless ← controlledDefEq checkedEncodedType expectedEncodedType do
        return .error (.structuralEncodedTypeMismatch candidate)
      unless ← controlledDefEq checkedIdentity expectedIdentity do
        return .error (.structuralIdentityMismatch candidate)
      match classifyElaboratedType (← inferType (mkConst candidate)) with
      | some (.structuralPresentation canonicalEncodedType canonicalIdentity) =>
          unless ← controlledDefEq canonicalEncodedType expectedEncodedType do
            return .error (.structuralEncodedTypeMismatch candidate)
          unless ← controlledDefEq canonicalIdentity expectedIdentity do
            return .error (.structuralIdentityMismatch candidate)
          return .ok ()
      | _ => return .error (.wrongPrimaryCapabilityHead candidate)
  | _ => return .error (.wrongPrimaryCapabilityHead candidate)

private def validatePrimitivePrimary (environment : Environment) (candidate : Name)
    (source target : Expr) : MetaM (Except CandidateBundleValidationFailure Unit) := do
  if (environment.find? candidate).isNone then
    return .error (.unknownPrimary candidate)
  let some entry := validateAttributedDeclaration environment candidate
    | return .error (.primaryNotAttributedCanonicalCapability candidate)
  let (expectedSource, _, _) ← representationTerms source
  let (expectedTarget, _, _) ← representationTerms target
  match entry.capability with
  | .primitive checkedSource checkedTarget =>
      unless ← controlledDefEq checkedSource expectedSource do
        return .error (.primitiveSourceMismatch candidate)
      unless ← controlledDefEq checkedTarget expectedTarget do
        return .error (.primitiveTargetMismatch candidate)
      match classifyElaboratedType (← inferType (mkConst candidate)) with
      | some (.primitive canonicalSource canonicalTarget) =>
          unless ← controlledDefEq canonicalSource expectedSource do
            return .error (.primitiveSourceMismatch candidate)
          unless ← controlledDefEq canonicalTarget expectedTarget do
            return .error (.primitiveTargetMismatch candidate)
          return .ok ()
      | _ => return .error (.wrongPrimaryCapabilityHead candidate)
  | _ => return .error (.wrongPrimaryCapabilityHead candidate)

/-- Validate an exact structural-certificate primary and its exact derived reduction route. -/
def validateLawfulPresentationBundle (environment : Environment)
    (primary route : Name) (source target : Expr) :
    MetaM (Except CandidateBundleValidationFailure Unit) := do
  match ← validateStructuralPrimary environment primary source with
  | .error failure => return .error failure
  | .ok () => pure ()
  match ← validateCandidateReduction environment route source target with
  | .error failure => return .error (.routeFailure failure)
  | .ok () => return .ok ()

/-- Validate an exact primitive primary and the route which embeds it at exact problem endpoints. -/
def validatePrimitiveAdmissionBundle (environment : Environment)
    (primary route : Name) (source target : Expr) :
    MetaM (Except CandidateBundleValidationFailure Unit) := do
  match ← validatePrimitivePrimary environment primary source target with
  | .error failure => return .error failure
  | .ok () => pure ()
  match ← validateCandidateReduction environment route source target with
  | .error failure => return .error (.routeFailure failure)
  | .ok () => return .ok ()

/-- Stable rejection classes for a complete Phase-5 program-indexed bundle. -/
inductive ProgramIndexedReductionValidationFailure where
  | unknownStage (candidate : Name)
  | executableDirectTMHeadMismatch (candidate : Name)
  | executableDirectTMSourceMismatch (candidate : Name)
  | executableDirectTMTargetMismatch (candidate : Name)
  | executableDirectTMRunMismatch (candidate : Name)
  | primitiveFailure (failure : CandidateBundleValidationFailure)
  | primitiveExecutableMismatch (candidate : Name)
  | programHeadMismatch (candidate : Name)
  | programSourceMismatch (candidate : Name)
  | programTargetMismatch (candidate : Name)
  | programPrimitiveMismatch (candidate : Name)
  | semanticProofHeadMismatch (candidate : Name)
  | semanticSourceMismatch (candidate : Name)
  | semanticTargetMismatch (candidate : Name)
  | semanticProgramMismatch (candidate : Name)
  | directTMHeadMismatch (candidate : Name)
  | directTMSourceMismatch (candidate : Name)
  | directTMTargetMismatch (candidate : Name)
  | directTMProgramMismatch (candidate : Name)
  | routeFailure (failure : CandidateValidationFailure)
  | routeProgramMismatch (candidate : Name)
  deriving Repr

private def exactThreeArgumentType? (type : Expr) (head : Name) : Option (Expr × Expr × Expr) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    none
  else
    let normalized := type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf head do
      none
    match normalized.getAppArgs with
    | #[first, second, third] => some (first, second, third)
    | _ => none

private def exactPolyProgType? (type : Expr) : Option (Expr × Expr) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    none
  else
    let normalized := type.consumeMData
    unless normalized.getAppFn.consumeMData.isConstOf ``PolyProg do
      none
    match normalized.getAppArgs with
    | #[source, target] => some (source, target)
    | _ => none

/--
Validate every declaration in a staged Phase-5 bundle and require that all
dependent checkpoints refer to the same executable, primitive, and program.
Only the final route and primitive are registry-attributed; the intermediate
declarations are checked directly from their elaborated environment types.
-/
def validateProgramIndexedReductionBundle (environment : Environment)
    (executable executableDirectTM primitive program semantic directTM route : Name)
    (source target : Expr) :
    MetaM (Except ProgramIndexedReductionValidationFailure Unit) := do
  for candidate in [executable, executableDirectTM, primitive, program, semantic, directTM, route] do
    if (environment.find? candidate).isNone then
      return .error (.unknownStage candidate)

  let some executableTMDeclaration := environment.find? executableDirectTM
    | return .error (.unknownStage executableDirectTM)
  let some (tmSource, tmTarget, tmRun) :=
      exactThreeArgumentType? executableTMDeclaration.type ``ExecutableDirectTMEvidence
    | return .error (.executableDirectTMHeadMismatch executableDirectTM)
  unless ← controlledDefEq tmSource source do
    return .error (.executableDirectTMSourceMismatch executableDirectTM)
  unless ← controlledDefEq tmTarget target do
    return .error (.executableDirectTMTargetMismatch executableDirectTM)
  unless ← controlledDefEq tmRun (mkConst executable) do
    return .error (.executableDirectTMRunMismatch executableDirectTM)

  match ← validatePrimitivePrimary environment primitive source target with
  | .error failure => return .error (.primitiveFailure failure)
  | .ok () => pure ()
  let primitiveRun ← mkAppM ``Primitive.run #[mkConst primitive]
  unless ← controlledDefEq primitiveRun (mkConst executable) do
    return .error (.primitiveExecutableMismatch primitive)

  let some programDeclaration := environment.find? program
    | return .error (.unknownStage program)
  let some (programSource, programTarget) := exactPolyProgType? programDeclaration.type
    | return .error (.programHeadMismatch program)
  let (expectedSource, _, _) ← representationTerms source
  let (expectedTarget, _, _) ← representationTerms target
  unless ← controlledDefEq programSource expectedSource do
    return .error (.programSourceMismatch program)
  unless ← controlledDefEq programTarget expectedTarget do
    return .error (.programTargetMismatch program)
  let expectedProgram ← mkAppM ``PolyProg.atom #[mkConst primitive]
  unless ← controlledDefEq (mkConst program) expectedProgram do
    return .error (.programPrimitiveMismatch program)

  let some semanticDeclaration := environment.find? semantic
    | return .error (.unknownStage semantic)
  let some (semanticSource, semanticTarget, semanticProgram) :=
      exactThreeArgumentType? semanticDeclaration.type ``ProgramSemanticProof
    | return .error (.semanticProofHeadMismatch semantic)
  unless ← controlledDefEq semanticSource source do
    return .error (.semanticSourceMismatch semantic)
  unless ← controlledDefEq semanticTarget target do
    return .error (.semanticTargetMismatch semantic)
  unless ← controlledDefEq semanticProgram (mkConst program) do
    return .error (.semanticProgramMismatch semantic)

  let some directTMDeclaration := environment.find? directTM
    | return .error (.unknownStage directTM)
  let some (directTMSource, directTMTarget, directTMProgram) :=
      exactThreeArgumentType? directTMDeclaration.type ``ProgramDirectTMEvidence
    | return .error (.directTMHeadMismatch directTM)
  unless ← controlledDefEq directTMSource source do
    return .error (.directTMSourceMismatch directTM)
  unless ← controlledDefEq directTMTarget target do
    return .error (.directTMTargetMismatch directTM)
  unless ← controlledDefEq directTMProgram (mkConst program) do
    return .error (.directTMProgramMismatch directTM)

  match ← validateCandidateReduction environment route source target with
  | .error failure => return .error (.routeFailure failure)
  | .ok () => pure ()
  let routeProgram ← mkAppM ``CertifiedReduction.program #[mkConst route]
  unless ← controlledDefEq routeProgram (mkConst program) do
    return .error (.routeProgramMismatch route)
  return .ok ()

/-- Stable rejection classes for a complete Phase-6 native-membership bundle. -/
inductive NativeMembershipValidationFailure where
  | unknownStage (candidate : Name)
  | verifierNotAttributedCanonicalCapability (candidate : Name)
  | verifierHeadMismatch (candidate : Name)
  | verifierProblemMismatch (candidate : Name)
  | witnessPresentationNotAttributedCanonicalCapability (candidate : Name)
  | witnessPresentationHeadMismatch (candidate : Name)
  | witnessEncodedTypeMismatch (candidate : Name)
  | witnessIdentityMismatch (candidate : Name)
  | disciplineNotAttributedCanonicalCapability (candidate : Name)
  | disciplineHeadMismatch (candidate : Name)
  | disciplineProblemMismatch (candidate : Name)
  | disciplineVerifierMismatch (candidate : Name)
  | membershipNotAttributedCanonicalCapability (candidate : Name)
  | membershipHeadMismatch (candidate : Name)
  | membershipProblemMismatch (candidate : Name)
  deriving Repr

/--
Validate the four staged membership declarations and require the witness
presentation and discipline to remain indexed by the same generated verifier.
-/
def validateNativeMembershipBundle (environment : Environment)
    (verifier witnessPresentation discipline membership : Name) (problem : Expr) :
    MetaM (Except NativeMembershipValidationFailure Unit) := do
  for candidate in [verifier, witnessPresentation, discipline, membership] do
    if (environment.find? candidate).isNone then
      return .error (.unknownStage candidate)

  let some verifierEntry := validateAttributedDeclaration environment verifier
    | return .error (.verifierNotAttributedCanonicalCapability verifier)
  match verifierEntry.capability with
  | .backendVerifier checkedProblem =>
      unless ← controlledDefEq checkedProblem problem do
        return .error (.verifierProblemMismatch verifier)
  | _ => return .error (.verifierHeadMismatch verifier)
  match classifyElaboratedType (← inferType (mkConst verifier)) with
  | some (.backendVerifier canonicalProblem) =>
      unless ← controlledDefEq canonicalProblem problem do
        return .error (.verifierProblemMismatch verifier)
  | _ => return .error (.verifierHeadMismatch verifier)

  let verifierTerm := mkConst verifier
  let verifierWitness ← mkAppM ``CertifiedVerifier.witness #[verifierTerm]
  let expectedWitnessEncodedType ← mkAppM ``LawfulEncodedType.encodedType #[verifierWitness]
  let expectedWitnessIdentity ← mkAppM ``LawfulEncodedType.representation #[verifierWitness]
  let some witnessEntry := validateAttributedDeclaration environment witnessPresentation
    | return .error (.witnessPresentationNotAttributedCanonicalCapability witnessPresentation)
  match witnessEntry.capability with
  | .structuralPresentation checkedEncodedType checkedIdentity =>
      unless ← controlledDefEq checkedEncodedType expectedWitnessEncodedType do
        return .error (.witnessEncodedTypeMismatch witnessPresentation)
      unless ← controlledDefEq checkedIdentity expectedWitnessIdentity do
        return .error (.witnessIdentityMismatch witnessPresentation)
  | _ => return .error (.witnessPresentationHeadMismatch witnessPresentation)

  let some disciplineEntry := validateAttributedDeclaration environment discipline
    | return .error (.disciplineNotAttributedCanonicalCapability discipline)
  match disciplineEntry.capability with
  | .verifierEncodingDiscipline checkedProblem checkedVerifier =>
      unless ← controlledDefEq checkedProblem problem do
        return .error (.disciplineProblemMismatch discipline)
      unless ← controlledDefEq checkedVerifier verifierTerm do
        return .error (.disciplineVerifierMismatch discipline)
  | _ => return .error (.disciplineHeadMismatch discipline)

  let some membershipEntry := validateAttributedDeclaration environment membership
    | return .error (.membershipNotAttributedCanonicalCapability membership)
  match membershipEntry.capability with
  | .nativeTMInNP checkedProblem =>
      unless ← controlledDefEq checkedProblem problem do
        return .error (.membershipProblemMismatch membership)
  | _ => return .error (.membershipHeadMismatch membership)
  match classifyElaboratedType (← inferType (mkConst membership)) with
  | some (.nativeTMInNP canonicalProblem) =>
      unless ← controlledDefEq canonicalProblem problem do
        return .error (.membershipProblemMismatch membership)
  | _ => return .error (.membershipHeadMismatch membership)
  return .ok ()

private def validationMarker := "HARDNESS_CANDIDATE"
private def validationSchema := "hardness_candidate_validation_v1"

syntax (name := hardnessValidateCandidate)
  "#hardness_validate_candidate " str ident ident ident : command
syntax (name := hardnessValidateLawfulCandidate)
  "#hardness_validate_lawful_candidate " str ident ident ident ident : command
syntax (name := hardnessValidatePrimitiveCandidate)
  "#hardness_validate_primitive_candidate " str ident ident ident ident : command
syntax (name := hardnessValidateProgramReductionCandidate)
  "#hardness_validate_program_reduction_candidate " str ident ident ident ident ident ident ident
    ident ident : command
syntax (name := hardnessValidateNativeMembershipCandidate)
  "#hardness_validate_native_membership_candidate " str ident ident ident ident ident : command

elab_rules : command
  | `(#hardness_validate_candidate $nonce:str $candidate:ident $source:ident $target:ident) => do
      let candidateName ← resolveGlobalConstNoOverload candidate
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM do
        let sourceHandle ←
          match ← InputGate.presented environment sourceName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate source rejected: {repr failure}"
        let targetHandle ←
          match ← InputGate.presented environment targetName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate target rejected: {repr failure}"
        match ← validateCandidateReduction environment candidateName
            sourceHandle.term targetHandle.term with
        | .error failure => throwError "hardness candidate rejected: {repr failure}"
        | .ok () =>
            logInfo m!"{validationMarker}\t{validationSchema}\t{nonce.getString}\taccepted\t{candidateName}"
  | `(#hardness_validate_lawful_candidate $nonce:str $primary:ident $route:ident
        $source:ident $target:ident) => do
      let primaryName ← resolveGlobalConstNoOverload primary
      let routeName ← resolveGlobalConstNoOverload route
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM do
        let sourceHandle ←
          match ← InputGate.presented environment sourceName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate source rejected: {repr failure}"
        let targetHandle ←
          match ← InputGate.presented environment targetName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate target rejected: {repr failure}"
        match ← validateLawfulPresentationBundle environment primaryName routeName
            sourceHandle.term targetHandle.term with
        | .error failure => throwError "hardness lawful-presentation bundle rejected: {repr failure}"
        | .ok () =>
            logInfo m!"{validationMarker}\t{validationSchema}\t{nonce.getString}\taccepted\t\
              {primaryName}\t{routeName}"
  | `(#hardness_validate_primitive_candidate $nonce:str $primary:ident $route:ident
        $source:ident $target:ident) => do
      let primaryName ← resolveGlobalConstNoOverload primary
      let routeName ← resolveGlobalConstNoOverload route
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM do
        let sourceHandle ←
          match ← InputGate.presented environment sourceName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate source rejected: {repr failure}"
        let targetHandle ←
          match ← InputGate.presented environment targetName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate target rejected: {repr failure}"
        match ← validatePrimitiveAdmissionBundle environment primaryName routeName
            sourceHandle.term targetHandle.term with
        | .error failure => throwError "hardness primitive-admission bundle rejected: {repr failure}"
        | .ok () =>
            logInfo m!"{validationMarker}\t{validationSchema}\t{nonce.getString}\taccepted\t\
              {primaryName}\t{routeName}"
  | `(#hardness_validate_program_reduction_candidate $nonce:str
        $executable:ident $executableDirectTM:ident $primitive:ident $program:ident
        $semantic:ident $directTM:ident $route:ident $source:ident $target:ident) => do
      let executableName ← resolveGlobalConstNoOverload executable
      let executableDirectTMName ← resolveGlobalConstNoOverload executableDirectTM
      let primitiveName ← resolveGlobalConstNoOverload primitive
      let programName ← resolveGlobalConstNoOverload program
      let semanticName ← resolveGlobalConstNoOverload semantic
      let directTMName ← resolveGlobalConstNoOverload directTM
      let routeName ← resolveGlobalConstNoOverload route
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM do
        let sourceHandle ←
          match ← InputGate.presented environment sourceName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate source rejected: {repr failure}"
        let targetHandle ←
          match ← InputGate.presented environment targetName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness candidate target rejected: {repr failure}"
        match ← validateProgramIndexedReductionBundle environment
            executableName executableDirectTMName primitiveName programName semanticName
            directTMName routeName sourceHandle.term targetHandle.term with
        | .error failure =>
            throwError "hardness program-indexed reduction bundle rejected: {repr failure}"
        | .ok () =>
            logInfo m!"{validationMarker}\t{validationSchema}\t{nonce.getString}\taccepted\t\
              {executableName}\t{primitiveName}\t{programName}\t{semanticName}\t\
              {directTMName}\t{routeName}"
  | `(#hardness_validate_native_membership_candidate $nonce:str
        $verifier:ident $witnessPresentation:ident $discipline:ident $membership:ident
        $problem:ident) => do
      let verifierName ← resolveGlobalConstNoOverload verifier
      let witnessPresentationName ← resolveGlobalConstNoOverload witnessPresentation
      let disciplineName ← resolveGlobalConstNoOverload discipline
      let membershipName ← resolveGlobalConstNoOverload membership
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM do
        let problemHandle ←
          match ← InputGate.presented environment problemName with
          | .ok handle => pure handle
          | .error failure => throwError "hardness membership problem rejected: {repr failure}"
        match ← validateNativeMembershipBundle environment verifierName
            witnessPresentationName disciplineName membershipName problemHandle.term with
        | .error failure =>
            throwError "hardness native-membership bundle rejected: {repr failure}"
        | .ok () =>
            logInfo m!"{validationMarker}\t{validationSchema}\t{nonce.getString}\taccepted\t\
              {verifierName}\t{witnessPresentationName}\t{disciplineName}\t{membershipName}"

end ComplexityReduction.Agent.Hardness.Authoring
