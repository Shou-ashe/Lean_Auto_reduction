/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Registry.InstanceId
import ComplexityReduction.Registry.Validation

/-!
Environment export of validated V2 registry candidates.

Declaration-local V2 attributes provide only a bounded discovery set.  The
Annotations layer owns that non-authoritative scan scope.  Every discovered
name is passed to `validateDeclaration`, whose result is the sole source of
exported capability.  Thus an attribute on a declaration with an ineligible
elaborated type produces no entry.
-/

namespace ComplexityReduction
namespace Registry

/-- Recover active local and imported candidates from one declaration-local V2 tag. -/
private def candidatesOfAttribute (tag : Lean.TagAttribute) (environment : Lean.Environment) :
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

/--
Test whether a declaration still carries one of the Annotations-owned local
candidate tags.  This is a discovery Boolean only; it is intentionally not a
registry admission function.
-/
def isCandidateName (environment : Lean.Environment) (candidate : Lean.Name) : Bool :=
  Annotations.isCapabilityCandidate environment candidate

/-- The exporter has no independent candidate-tag list. -/
@[simp]
theorem isCandidateName_eq_annotationDiscovery (environment : Lean.Environment)
    (candidate : Lean.Name) :
    isCandidateName environment candidate =
      Annotations.isCapabilityCandidate environment candidate :=
  rfl

/--
The complete V2 declaration-local candidate set.

This union is only a scan scope: no tag kind is preserved in the result and no tag is inspected by
the validator.  Candidate names therefore carry no capability on their own.
-/
def candidateNames (environment : Lean.Environment) : List Lean.Name :=
  Std.TreeSet.toList <|
    Annotations.capabilityCandidateAttributes.foldl
      (fun candidates tag => candidates.union (candidatesOfAttribute tag environment))
      ({} : Lean.NameSet)

/--
Validate a declaration only after declaration-local candidate discovery.

The positive branch is the sole call to `validateDeclaration`; therefore the
result can contain capability only through its environment-indexed
`ValidatedEntry`, never through an attribute payload, name, or metadata.
-/
def validateAttributedDeclaration (environment : Lean.Environment) (candidate : Lean.Name) :
    Option (ValidatedEntry environment) :=
  if isCandidateName environment candidate then validateDeclaration environment candidate else none

/-- Unknown or untagged declarations are rejected before type validation can export them. -/
@[simp]
theorem validateAttributedDeclaration_eq_none_of_notCandidate {environment : Lean.Environment}
    {candidate : Lean.Name} (notCandidate : isCandidateName environment candidate = false) :
    validateAttributedDeclaration environment candidate = none := by
  unfold validateAttributedDeclaration
  have candidateFalse : isCandidateName environment candidate ≠ true := by
    intro candidateTrue
    rw [candidateTrue] at notCandidate
    simp at notCandidate
  rw [if_neg candidateFalse]

/-- An active declaration-local candidate is validated only through its elaborated type. -/
@[simp]
theorem validateAttributedDeclaration_eq_validateDeclaration_of_candidate
    {environment : Lean.Environment} {candidate : Lean.Name}
    (candidateTag : isCandidateName environment candidate = true) :
    validateAttributedDeclaration environment candidate =
      validateDeclaration environment candidate := by
  unfold validateAttributedDeclaration
  rw [if_pos candidateTag]

/--
An attribute-discovered entry has two separate provenance facts: the tag only
discovered its declaration name, while the capability itself came from that
declaration's elaborated type.  No string payload, Boolean flag, or tag kind
appears in the second conjunct.
-/
theorem validateAttributedDeclaration_type_directed {environment : Lean.Environment}
    {candidate : Lean.Name} {entry : ValidatedEntry environment}
    (validated : validateAttributedDeclaration environment candidate = some entry) :
    isCandidateName environment candidate = true ∧
      ∃ declaration,
        environment.find? candidate = some declaration ∧
          classifyElaboratedType declaration.type = some entry.classified.capability := by
  cases candidateTag : isCandidateName environment candidate with
  | false =>
      rw [validateAttributedDeclaration_eq_none_of_notCandidate candidateTag] at validated
      contradiction
  | true =>
      refine ⟨by simp, ?_⟩
      rw [validateAttributedDeclaration_eq_validateDeclaration_of_candidate candidateTag] at validated
      exact validateDeclaration_type_directed validated

/--
Extract the two exact elaborated endpoints carried by capability classes whose
canonical head has two arguments.

This is deliberately a projection of `ValidatedCapability`, rather than a
parser for declaration names or descriptor fields.  Classes with no pair of
canonical type arguments return `none`; in particular, a theorem-name string
or readiness Boolean never reaches this function without first passing
environment-indexed elaborated-type validation.
-/
def ValidatedCapability.endpointPair? : ValidatedCapability → Option (Lean.Expr × Lean.Expr)
  | .structuralPresentation encodedType representation => some (encodedType, representation)
  | .certifiedReduction source target => some (source, target)
  | .certifiedEquiv source target => some (source, target)
  | .certifiedPresentationChange source target => some (source, target)
  | .certifiedRouteProvenance _ _ _ _ _ _ _ _ => none
  | .primitive source target => some (source, target)
  | .verifierEncodingDiscipline problem verifier => some (problem, verifier)
  | .presentedProblem
  | .backendVerifier _
  | .nativeVerifierCapability _
  | .nativeTMInNP _
  | .nativeTMNPHard _
  | .nativeTMNPComplete _
  | .backendTMInNP _
  | .backendTMNPComplete _ => none

/--
Extract the exact presented-problem endpoints of an edge-like capability.

Unlike `endpointPair?`, this deliberately excludes primitives and structural
presentation certificates, whose endpoint arguments are lawful presentations
rather than `PresentedProblem`s.  It includes route provenance because the
provenance head retains the exact final route source and target in its
elaborated type.  This is a classifier projection only: it does not inspect a
declaration value or recover an endpoint from a role tag.
-/
def ValidatedCapability.problemEndpointPair? : ValidatedCapability → Option (Lean.Expr × Lean.Expr)
  | .certifiedReduction source target => some (source, target)
  | .certifiedEquiv source target => some (source, target)
  | .certifiedPresentationChange source target => some (source, target)
  | .certifiedRouteProvenance source _ _ target _ _ _ _ => some (source, target)
  | .presentedProblem
  | .structuralPresentation _ _
  | .primitive _ _
  | .backendVerifier _
  | .verifierEncodingDiscipline _ _
  | .nativeVerifierCapability _
  | .nativeTMInNP _
  | .nativeTMNPHard _
  | .nativeTMNPComplete _
  | .backendTMInNP _
  | .backendTMNPComplete _ => none

/--
The identity terms exported for an exact pair of presented-problem endpoints.

Every field is a Lean expression formed from the source or target expression
extracted from a validated canonical certificate head.  The exporter neither
serializes identities nor computes them from carriers: the terms are direct
applications of the typed `ProblemInstanceId` constructors/projections, and
therefore retain the full encoder-bound lawful presentation at each endpoint.
-/
structure ValidatedEndpointIdentityTerms where
  source : Lean.Expr
  target : Lean.Expr
  sourceProblemId : Lean.Expr
  targetProblemId : Lean.Expr
  sourceRepresentationId : Lean.Expr
  targetRepresentationId : Lean.Expr
  sourceEncoderBoundRepresentationIdentity : Lean.Expr
  targetEncoderBoundRepresentationIdentity : Lean.Expr

private def problemIdTerm (endpoint : Lean.Expr) : Lean.Expr :=
  Lean.mkApp
    (Lean.mkConst ``ComplexityReduction.Registry.ProblemInstanceId.ofPresentedProblem)
    endpoint

private def representationIdTerm (endpoint : Lean.Expr) : Lean.Expr :=
  Lean.mkApp
    (Lean.mkConst ``ComplexityReduction.Registry.ProblemInstanceId.representationId)
    endpoint

private def encoderBoundRepresentationIdentityTerm (endpoint : Lean.Expr) : Lean.Expr :=
  Lean.mkApp
    (Lean.mkConst
      ``ComplexityReduction.Registry.ProblemInstanceId.representationEncoderBoundIdentity)
    endpoint

/--
Build identity expressions only for a source/target pair already obtained from
an elaborated certificate/provenance type.  In particular this constructor has
no name, string, role, metadata, or carrier argument.
-/
def ValidatedEndpointIdentityTerms.ofExactEndpoints (source target : Lean.Expr) :
    ValidatedEndpointIdentityTerms where
  source
  target
  sourceProblemId := problemIdTerm source
  targetProblemId := problemIdTerm target
  sourceRepresentationId := representationIdTerm source
  targetRepresentationId := representationIdTerm target
  sourceEncoderBoundRepresentationIdentity := encoderBoundRepresentationIdentityTerm source
  targetEncoderBoundRepresentationIdentity := encoderBoundRepresentationIdentityTerm target

/--
Project exact problem and encoder-bound representation identities from one
already validated registry entry.  This is intentionally unavailable for
metadata, primitive-only, and non-edge capability heads.
-/
def ValidatedEntry.endpointIdentityTerms? {environment : Lean.Environment}
    (entry : ValidatedEntry environment) : Option ValidatedEndpointIdentityTerms :=
  entry.capability.problemEndpointPair?.map fun (source, target) =>
    .ofExactEndpoints source target

@[simp]
theorem ValidatedEndpointIdentityTerms.ofExactEndpoints_source (source target : Lean.Expr) :
    (ValidatedEndpointIdentityTerms.ofExactEndpoints source target).source = source :=
  rfl

@[simp]
theorem ValidatedEndpointIdentityTerms.ofExactEndpoints_target (source target : Lean.Expr) :
    (ValidatedEndpointIdentityTerms.ofExactEndpoints source target).target = target :=
  rfl

/--
Recover a capability only through declaration-local discovery followed by the
canonical environment-indexed validator.  A candidate name selects where to
look; its capability is still the classification of that declaration's
elaborated type.
-/
def exportedCapability? (environment : Lean.Environment) (candidate : Lean.Name) :
    Option ValidatedCapability :=
  (validateAttributedDeclaration environment candidate).map ValidatedEntry.capability

/--
Recover the exact two elaborated endpoints of an exported capability when its
canonical type head has two endpoint arguments.  This function is fail-closed
for non-capability candidates and for canonical capabilities with another
arity.
-/
def exportedEndpointPair? (environment : Lean.Environment) (candidate : Lean.Name) :
    Option (Lean.Expr × Lean.Expr) :=
  (exportedCapability? environment candidate).bind ValidatedCapability.endpointPair?

/--
Export exact problem and encoder-bound representation identity terms for an
edge-like V2 capability.  Candidate discovery is still only a scan boundary:
the identity terms are available solely after `validateAttributedDeclaration`
has classified the declaration's elaborated type.
-/
def exportedEndpointIdentityTerms? (environment : Lean.Environment) (candidate : Lean.Name) :
    Option ValidatedEndpointIdentityTerms :=
  (validateAttributedDeclaration environment candidate).bind
    ValidatedEntry.endpointIdentityTerms?

/--
The capability returned by the exporter is exactly the classifier output for
the retained declaration type in the scanned environment.  Attribute data and
candidate names establish discovery only, not this result.
-/
theorem exportedCapability_type_directed {environment : Lean.Environment}
    {candidate : Lean.Name} {capability : ValidatedCapability}
    (exported : exportedCapability? environment candidate = some capability) :
    isCandidateName environment candidate = true ∧
      ∃ declaration,
        environment.find? candidate = some declaration ∧
          classifyElaboratedType declaration.type = some capability := by
  unfold exportedCapability? at exported
  cases validated : validateAttributedDeclaration environment candidate with
  | none =>
      simp [validated] at exported
  | some entry =>
      have capabilityEquality : entry.capability = capability := by
        simpa [validated] using exported
      obtain ⟨candidateTag, declaration, found, classified⟩ :=
        validateAttributedDeclaration_type_directed validated
      refine ⟨candidateTag, declaration, found, ?_⟩
      rw [← capabilityEquality]
      exact classified

/--
Successful endpoint extraction is a second projection of one capability
classified from the exact declaration type.  The returned expressions are
therefore not inferred from carrier equality, theorem-name strings, or
descriptor metadata.
-/
theorem exportedEndpointPair_type_directed {environment : Lean.Environment}
    {candidate : Lean.Name} {endpoints : Lean.Expr × Lean.Expr}
    (exported : exportedEndpointPair? environment candidate = some endpoints) :
    isCandidateName environment candidate = true ∧
      ∃ declaration capability,
        environment.find? candidate = some declaration ∧
          classifyElaboratedType declaration.type = some capability ∧
            capability.endpointPair? = some endpoints := by
  unfold exportedEndpointPair? exportedCapability? at exported
  cases validated : validateAttributedDeclaration environment candidate with
  | none =>
      simp [validated] at exported
  | some entry =>
      cases extracted : entry.capability.endpointPair? with
      | none =>
          simp [validated, extracted] at exported
      | some extractedEndpoints =>
          have endpointEquality : extractedEndpoints = endpoints := by
            simpa [validated, extracted] using exported
          obtain ⟨candidateTag, declaration, found, classified⟩ :=
            validateAttributedDeclaration_type_directed validated
          refine ⟨candidateTag, declaration, entry.capability, found, classified, ?_⟩
          simpa [endpointEquality] using extracted

/--
Export exactly the candidates whose elaborated declarations satisfy canonical V2 type validation.

The result contains `ValidatedEntry` values only.  In particular, a candidate tag that names a
missing declaration, a parameterized declaration, or a declaration of an unsupported type is
dropped by `validateDeclaration`.
-/
def exportValidated (environment : Lean.Environment) : List (ValidatedEntry environment) :=
  (candidateNames environment).filterMap (validateAttributedDeclaration environment)

/--
One read-only observation of an already validated registry entry.

The `entry` is the sole capability-bearing field.  The optional component role
is copied only from declaration-local annotation provenance after validation;
it neither changes `entry` nor participates in classifying its elaborated
type.
-/
structure ValidatedExportObservation (environment : Lean.Environment) where
  entry : ValidatedEntry environment
  componentRoleProvenance? : Option Annotations.ComponentRoleCandidateProvenance

/--
Attach optional non-authoritative role provenance to an entry which has
already passed canonical elaborated-type validation.
-/
def observeValidatedEntry (environment : Lean.Environment) (entry : ValidatedEntry environment) :
    ValidatedExportObservation environment where
  entry := entry
  componentRoleProvenance? :=
    Annotations.componentRoleCandidateProvenance? environment entry.candidate

/-- The observation retains exactly the validated entry from which it was derived. -/
@[simp]
theorem observeValidatedEntry_entry (environment : Lean.Environment)
    (entry : ValidatedEntry environment) :
    (observeValidatedEntry environment entry).entry = entry :=
  rfl

/-- Role provenance in an observation is exactly the annotation-layer lookup at its entry name. -/
@[simp]
theorem observeValidatedEntry_componentRoleProvenance (environment : Lean.Environment)
    (entry : ValidatedEntry environment) :
    (observeValidatedEntry environment entry).componentRoleProvenance? =
      Annotations.componentRoleCandidateProvenance? environment entry.candidate :=
  rfl

/--
Validate a normal candidate first, then attach its optional role observation.

A component-role tag alone cannot enter this function's successful branch:
the only source of `some` is `validateAttributedDeclaration`, which remains
the canonical elaborated-type validator.
-/
def validateAttributedComponentRoleObservation? (environment : Lean.Environment)
    (candidate : Lean.Name) : Option (ValidatedExportObservation environment) :=
  (validateAttributedDeclaration environment candidate).map (observeValidatedEntry environment)

/-- A successful role observation contains an entry accepted by the canonical validator. -/
theorem validateAttributedComponentRoleObservation?_validated {environment : Lean.Environment}
    {candidate : Lean.Name} {observation : ValidatedExportObservation environment}
    (validated : validateAttributedComponentRoleObservation? environment candidate = some observation) :
    validateAttributedDeclaration environment candidate = some observation.entry := by
  unfold validateAttributedComponentRoleObservation? at validated
  cases checked : validateAttributedDeclaration environment candidate with
  | none => simp [checked] at validated
  | some entry =>
      have observationEquality : observeValidatedEntry environment entry = observation := by
        simpa [checked] using validated
      exact congrArg (fun observed : ValidatedExportObservation environment =>
        some observed.entry) observationEquality

/--
Export all canonical validated entries together with optional component-role
provenance.  This is observational only; `exportValidated` remains the
compatible authoritative export surface.
-/
def exportValidatedObservations (environment : Lean.Environment) :
    List (ValidatedExportObservation environment) :=
  (exportValidated environment).map (observeValidatedEntry environment)

/-- Every observed export entry comes from the unchanged authoritative export. -/
theorem mem_exportValidatedObservations_iff {environment : Lean.Environment}
    {observation : ValidatedExportObservation environment} :
    observation ∈ exportValidatedObservations environment ↔
      ∃ entry ∈ exportValidated environment,
        observeValidatedEntry environment entry = observation := by
  simp [exportValidatedObservations]

/-- A registry candidate enters the export exactly when canonical validation accepts it. -/
theorem mem_exportValidated_iff {environment : Lean.Environment}
    {entry : ValidatedEntry environment} :
    entry ∈ exportValidated environment ↔
      ∃ candidate ∈ candidateNames environment,
        validateAttributedDeclaration environment candidate = some entry := by
  simp [exportValidated]

/--
Every exported capability is jointly witnessed by candidate discovery and by
the exact declaration type in the scanned environment.  Attributes determine
only the first fact; the classifier applied to the elaborated type determines
the capability.  This is the public fail-closed export invariant used by
registry consumers instead of descriptor strings or `theoremUsable` flags.
-/
theorem mem_exportValidated_type_directed {environment : Lean.Environment}
    {entry : ValidatedEntry environment} (exported : entry ∈ exportValidated environment) :
    isCandidateName environment entry.candidate = true ∧
      ∃ declaration,
        environment.find? entry.candidate = some declaration ∧
          classifyElaboratedType declaration.type = some entry.classified.capability := by
  obtain ⟨candidate, _, validated⟩ := mem_exportValidated_iff.mp exported
  obtain ⟨candidateTag, declaration, found, classified⟩ :=
    validateAttributedDeclaration_type_directed validated
  have directValidation : validateDeclaration environment candidate = some entry := by
    rw [← validateAttributedDeclaration_eq_validateDeclaration_of_candidate candidateTag]
    exact validated
  have sameCandidate : entry.candidate = candidate :=
    validateDeclaration_candidate_eq directValidation
  constructor
  · simpa [sameCandidate] using candidateTag
  · refine ⟨declaration, ?_, classified⟩
    simpa [sameCandidate] using found

/--
The role in an observed export is a non-authoritative annotation lookup at
the already validated declaration, never a classifier output or body scan.
-/
theorem mem_exportValidatedObservations_type_directed {environment : Lean.Environment}
    {observation : ValidatedExportObservation environment}
    (exported : observation ∈ exportValidatedObservations environment) :
    ∃ declaration,
      environment.find? observation.entry.candidate = some declaration ∧
        classifyElaboratedType declaration.type = some observation.entry.classified.capability ∧
          observation.componentRoleProvenance? =
            Annotations.componentRoleCandidateProvenance? environment observation.entry.candidate := by
  obtain ⟨entry, entryExported, observationEquality⟩ :=
    mem_exportValidatedObservations_iff.mp exported
  cases observationEquality
  obtain ⟨_, declaration, found, classified⟩ :=
    mem_exportValidated_type_directed entryExported
  exact ⟨declaration, found, classified, rfl⟩

end Registry
end ComplexityReduction
