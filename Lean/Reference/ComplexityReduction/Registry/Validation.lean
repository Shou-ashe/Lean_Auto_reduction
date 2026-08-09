/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Environment
import ComplexityReduction.Certificate.Equiv
import ComplexityReduction.Certificate.PresentationChange
import ComplexityReduction.Certificate.Provenance
import ComplexityReduction.Certificate.NativeCompleteness
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Program.Primitive

/-!
Elaborated-type validation for V2 registry candidates.

This module recognizes only closed, exact applications of the canonical V2 certificate and
primitive heads in the Lean environment.  Attributes and all other metadata remain outside this
module and may supply only a declaration name to `validateDeclaration`; they cannot manufacture a
`ValidatedEntry` without the matching elaborated declaration type.
-/

namespace ComplexityReduction
namespace Registry

open Lean

/-- The closed capability classes that the V2 registry validator may recognize. -/
inductive ValidatedCapability where
  /-- An exact V2 `PresentedProblem` declaration; its identity remains the declaration term. -/
  | presentedProblem
  /-- Closed structural presentation evidence indexed by its encoder and representation identity. -/
  | structuralPresentation (encodedType representation : Expr)
  | certifiedReduction (source target : Expr)
  | certifiedEquiv (source target : Expr)
  | certifiedPresentationChange (source target : Expr)
  /-- A route provenance head whose components and composed final certificate are exact type indices. -/
  | certifiedRouteProvenance (source hub sharedTarget target ingress sharedGadget optionalEgress
      finalCertificate : Expr)
  | primitive (source target : Expr)
  /-- A direct-TM verifier with backend membership only. -/
  | backendVerifier (problem : Expr)
  /-- An exact verifier encoding discipline, distinct from backend verifier evidence. -/
  | verifierEncodingDiscipline (problem verifier : Expr)
  /-- A packaged verifier plus exact discipline, eligible for native capability. -/
  | nativeVerifierCapability (problem : Expr)
  /-- Native membership derived from a V2 verifier plus an exact V2 encoding discipline. -/
  | nativeTMInNP (problem : Expr)
  /-- Native NP-hardness at one exact presented problem. -/
  | nativeTMNPHard (problem : Expr)
  /-- Native completeness requires the exact V2-native completeness head, never backend completeness. -/
  | nativeTMNPComplete (problem : Expr)
  /-- Backend direct-TM membership, deliberately distinct from native verifier membership. -/
  | backendTMInNP (problem : Expr)
  /-- Backend direct-TM NP-completeness, which does not itself imply native verifier discipline. -/
  | backendTMNPComplete (problem : Expr)
  deriving Repr

/-- An elaborated declaration type together with its capability classification. -/
structure ClassifiedDeclaration where
  elaboratedType : Expr
  capability : ValidatedCapability

/-- The canonical declaration head for a concrete V2 presented problem value. -/
private def presentedProblemHead : Name :=
  ``ComplexityReduction.Encoding.PresentedProblem

/-- The canonical declaration head for closed structural presentation admission evidence. -/
private def structuralPresentationHead : Name :=
  ``ComplexityReduction.Encoding.StructuralRepresentationCertificate

/-- The canonical declaration head for typed one-way reduction certificates. -/
private def certifiedReductionHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedReduction

/-- The canonical declaration head for typed two-way equivalence certificates. -/
private def certifiedEquivHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedEquiv

/-- The canonical declaration head for certified changes between exact presentations. -/
private def certifiedPresentationChangeHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedPresentationChange

/-- The canonical head for type-indexed composed route provenance. -/
private def certifiedRouteProvenanceHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedRouteProvenance

/-- The canonical declaration head for direct-TM-backed typed primitives. -/
private def primitiveHead : Name :=
  ``ComplexityReduction.Program.Primitive

/-- The canonical declaration head for backend direct-TM verifier certificates. -/
private def certifiedVerifierHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedVerifier

/-- The canonical declaration head for exact verifier encoding disciplines. -/
private def verifierEncodingDisciplineHead : Name :=
  ``ComplexityReduction.Certificate.CertifiedVerifierEncodingDiscipline

/-- The canonical declaration head for packaged native verifier capability. -/
private def nativeVerifierCapabilityHead : Name :=
  ``ComplexityReduction.Certificate.NativeVerifierCapability

/-- The canonical V2-native membership head, distinct from the backend TM proposition. -/
private def nativeTMInNPHead : Name :=
  ``ComplexityReduction.Certificate.NativeTMInNP

/-- The canonical V2-native NP-hardness head. -/
private def nativeTMNPHardHead : Name :=
  ``ComplexityReduction.Certificate.NativeTMNPHard

/-- The canonical V2-native completeness head, distinct from `TMNPCompleteEnc`. -/
private def nativeTMNPCompleteHead : Name :=
  ``ComplexityReduction.Certificate.NativeTMNPComplete

/-- The existing direct-TM backend membership head. -/
private def backendTMInNPHead : Name :=
  ``ComplexityReduction.TMInNP

/-- The existing direct-TM backend completeness head. -/
private def backendTMNPCompleteHead : Name :=
  ``ComplexityReduction.TMNPCompleteEnc

/-- Reject declarations that still expose a binder or local type-level computation at the top level. -/
private def hasTopLevelBinder (type : Expr) : Bool :=
  match type.consumeMData with
  | .forallE .. | .letE .. | .lam .. => true
  | _ => false

/--
Reject expressions which cannot be an entirely elaborated, closed declaration
type.  This keeps the public classifier fail-closed even when it is called on
an `Expr` assembled by a metaprogram rather than immediately by
`validateRaw`.  In normal environment use these checks are all false; they
rule out using an unresolved metavariable, free variable, loose de Bruijn
variable, or universe parameter to manufacture apparent endpoints.
-/
private def hasOpenElaboratedSyntax (type : Expr) : Bool :=
  type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam

private def classifyNullaryHead (type : Expr) (head : Name)
    (capability : ValidatedCapability) : Option ValidatedCapability :=
  if type.consumeMData.isConstOf head then some capability else none

private def classifyHead (type : Expr) (head : Name)
    (mkCapability : Expr → Expr → ValidatedCapability) : Option ValidatedCapability :=
  let normalized := type.consumeMData
  if normalized.getAppFn.consumeMData.isConstOf head then
    match normalized.getAppArgs with
    | #[source, target] => some (mkCapability source target)
    | _ => none
  else
    none

private def classifyUnaryHead (type : Expr) (head : Name)
    (mkCapability : Expr → ValidatedCapability) : Option ValidatedCapability :=
  let normalized := type.consumeMData
  if normalized.getAppFn.consumeMData.isConstOf head then
    match normalized.getAppArgs with
    | #[argument] => some (mkCapability argument)
    | _ => none
  else
    none

/-- Classify the exact eight elaborated arguments of `CertifiedRouteProvenance`. -/
private def classifyRouteProvenanceHead (type : Expr) : Option ValidatedCapability :=
  let normalized := type.consumeMData
  if normalized.getAppFn.consumeMData.isConstOf certifiedRouteProvenanceHead then
    match normalized.getAppArgs with
    | #[source, hub, sharedTarget, target, ingress, sharedGadget, optionalEgress,
        finalCertificate] =>
        some (.certifiedRouteProvenance source hub sharedTarget target ingress sharedGadget
          optionalEgress finalCertificate)
    | _ => none
  else
    none

/--
Classify one elaborated declaration type by its exact closed V2 capability head.

The classifier deliberately does not unfold arbitrary aliases, inspect declaration names, parse
strings, or infer endpoints from carriers.  A declaration with binders is likewise rejected rather
than guessed: parameterized declarations require an explicit elaborated instantiation first.  In
particular, `CertifiedVerifier` is backend-only; native capability requires an exact discipline or
`NativeVerifierCapability` declaration type.
-/
def classifyElaboratedType (type : Expr) : Option ValidatedCapability :=
  if hasTopLevelBinder type || hasOpenElaboratedSyntax type then none else
    match classifyNullaryHead type presentedProblemHead .presentedProblem with
    | some capability => some capability
    | none =>
        match classifyHead type structuralPresentationHead .structuralPresentation with
        | some capability => some capability
        | none =>
            match classifyHead type certifiedReductionHead .certifiedReduction with
            | some capability => some capability
            | none =>
                match classifyHead type certifiedEquivHead .certifiedEquiv with
                | some capability => some capability
                | none =>
                    match classifyHead type certifiedPresentationChangeHead .certifiedPresentationChange with
                    | some capability => some capability
                    | none =>
                        match classifyRouteProvenanceHead type with
                        | some capability => some capability
                        | none =>
                            match classifyHead type primitiveHead .primitive with
                            | some capability => some capability
                            | none =>
                                match classifyUnaryHead type certifiedVerifierHead .backendVerifier with
                                | some capability => some capability
                                | none =>
                                    match classifyHead type verifierEncodingDisciplineHead
                                        .verifierEncodingDiscipline with
                                    | some capability => some capability
                                    | none =>
                                        match classifyUnaryHead type nativeVerifierCapabilityHead
                                            .nativeVerifierCapability with
                                        | some capability => some capability
                                        | none =>
                                            match classifyUnaryHead type nativeTMInNPHead .nativeTMInNP with
                                            | some capability => some capability
                                            | none =>
                                                match classifyUnaryHead type nativeTMNPHardHead
                                                    .nativeTMNPHard with
                                                | some capability => some capability
                                                | none =>
                                                    match classifyUnaryHead type nativeTMNPCompleteHead
                                                        .nativeTMNPComplete with
                                                    | some capability => some capability
                                                    | none =>
                                                        match classifyUnaryHead type backendTMInNPHead
                                                            .backendTMInNP with
                                                        | some capability => some capability
                                                        | none =>
                                                            classifyUnaryHead type backendTMNPCompleteHead
                                                              .backendTMNPComplete

/--
Read and classify a candidate declaration only from its elaborated environment type.

This is intentionally independent of V2 attributes: callers may pass an attribute-discovered
candidate name, but the attribute has no branch in this implementation and grants no capability.
-/
def validateRaw (environment : Environment) (candidate : Name) : Option ClassifiedDeclaration := do
  let info ← environment.find? candidate
  let elaboratedType := info.type
  let capability ← classifyElaboratedType elaboratedType
  pure { elaboratedType, capability }

/--
A registry entry validated against one exact Lean environment.

The `checked` field makes this type unavailable from an arbitrary name, Boolean, string, metadata
record, or proposition: it is inhabited by `validateDeclaration` only after classification of the
actual elaborated declaration type in the indexed environment.
-/
structure ValidatedEntry (environment : Environment) where
  candidate : Name
  classified : ClassifiedDeclaration
  /--
  The retained declaration witness ties this entry to the exact type stored in
  the environment.  It rules out constructing an export capability from a
  candidate name, descriptor payload, or separately supplied type expression.
  -/
  sourceDeclaration : ∃ declaration,
    environment.find? candidate = some declaration ∧
      classified.elaboratedType = declaration.type
  checked : validateRaw environment candidate = some classified
  classification : classifyElaboratedType classified.elaboratedType = some classified.capability

/--
Validate a declaration candidate against an exact Lean environment.

The result carries a proof that its stored classification is the direct result of `validateRaw` for
that environment and declaration.  Export code must consume this result rather than classifying
attribute payloads itself.
-/
def validateDeclaration (environment : Environment) (candidate : Name) :
    Option (ValidatedEntry environment) :=
  match info : environment.find? candidate with
  | none => none
  | some declaration =>
      match hCapability : classifyElaboratedType declaration.type with
      | none => none
      | some foundCapability =>
          let classified : ClassifiedDeclaration := ⟨declaration.type, foundCapability⟩
          some {
            candidate
            classified
            sourceDeclaration := ⟨declaration, info, rfl⟩
            checked := by
              dsimp [classified]
              simp [validateRaw, info, hCapability]
            classification := hCapability }

/--
Successful direct validation retains the exact declaration name that was
looked up.  This prevents an exporter from validating one environment entry
and relabelling the resulting capability with a descriptor, theorem-name
string, or a different candidate declaration.
-/
theorem validateDeclaration_candidate_eq {environment : Environment} {candidate : Name}
    {entry : ValidatedEntry environment}
    (validated : validateDeclaration environment candidate = some entry) :
    entry.candidate = candidate := by
  unfold validateDeclaration at validated
  split at validated <;> try contradiction
  split at validated <;> try contradiction
  exact (congrArg (fun value : ValidatedEntry environment => value.candidate)
    (Option.some.inj validated)).symm

/--
Direct validation has exactly the retained declaration type as its capability
source.  The theorem is deliberately stated without any attribute or
descriptor premise: such metadata is outside the trusted validation boundary.
-/
theorem validateDeclaration_type_directed {environment : Environment} {candidate : Name}
    {entry : ValidatedEntry environment}
    (validated : validateDeclaration environment candidate = some entry) :
    ∃ declaration,
      environment.find? candidate = some declaration ∧
        classifyElaboratedType declaration.type = some entry.classified.capability := by
  refine ⟨?_, ?_, ?_⟩
  · exact Classical.choose entry.sourceDeclaration
  · have retained := (Classical.choose_spec entry.sourceDeclaration).1
    simpa [validateDeclaration_candidate_eq validated] using retained
  · have retained := (Classical.choose_spec entry.sourceDeclaration).2
    rw [← retained]
    exact entry.classification

/-- Recover the capability class only from an environment-indexed validated entry. -/
def ValidatedEntry.capability {environment : Environment}
    (entry : ValidatedEntry environment) : ValidatedCapability :=
  entry.classified.capability

/-- Recover the actual elaborated declaration type retained by one validated entry. -/
def ValidatedEntry.elaboratedType {environment : Environment}
    (entry : ValidatedEntry environment) : Expr :=
  entry.classified.elaboratedType

/-- A validated entry's capability is exactly the result of classifying its retained type. -/
theorem ValidatedEntry.classification_eq {environment : Environment}
    (entry : ValidatedEntry environment) :
    classifyElaboratedType entry.elaboratedType = some entry.capability := by
  unfold ValidatedEntry.elaboratedType ValidatedEntry.capability
  exact entry.classification

/--
The retained elaborated type is exactly the type of the entry's declaration in
the indexed Lean environment.  In particular, registry consumers cannot swap
in a same-carrier endpoint, a theorem-name string, or descriptor metadata
after validation.
-/
theorem ValidatedEntry.elaboratedType_eq_environmentType {environment : Environment}
    (entry : ValidatedEntry environment) {declaration}
    (found : environment.find? entry.candidate = some declaration) :
    entry.elaboratedType = declaration.type := by
  obtain ⟨storedDeclaration, storedFound, retainedType⟩ := entry.sourceDeclaration
  have declarationEquality : storedDeclaration = declaration :=
    Option.some.inj (storedFound.symm.trans found)
  calc
    entry.elaboratedType = entry.classified.elaboratedType := rfl
    _ = storedDeclaration.type := retainedType
    _ = declaration.type := congrArg (fun info : ConstantInfo => info.type) declarationEquality

/--
The exported capability is the classifier result for the exact declaration
type in the indexed environment.  This is the registry's type-level
provenance theorem: tags may discover a name, but neither tags nor metadata
can determine the capability or its extracted endpoints.
-/
theorem ValidatedEntry.classification_eq_environmentType {environment : Environment}
    (entry : ValidatedEntry environment) {declaration}
    (found : environment.find? entry.candidate = some declaration) :
    classifyElaboratedType declaration.type = some entry.capability := by
  rw [← entry.elaboratedType_eq_environmentType found]
  exact entry.classification_eq

/-- Two equal reduction capability classifications have the same exact endpoints. -/
theorem ValidatedCapability.certifiedReduction_endpoints_injective
    {source target source' target' : Expr}
    (equal : ValidatedCapability.certifiedReduction source target =
      .certifiedReduction source' target') :
    source = source' ∧ target = target' := by
  cases equal
  exact ⟨rfl, rfl⟩

/-- Two equal primitive capability classifications have the same exact endpoints. -/
theorem ValidatedCapability.primitive_endpoints_injective
    {source target source' target' : Expr}
    (equal : ValidatedCapability.primitive source target = .primitive source' target') :
    source = source' ∧ target = target' := by
  cases equal
  exact ⟨rfl, rfl⟩

/--
One environment-validated entry cannot be relabelled as two different
reduction endpoints.  The endpoint expressions are those extracted from the
entry's retained elaborated declaration type, not caller-supplied strings or
same-carrier approximations.
-/
theorem ValidatedEntry.certifiedReduction_endpoints_unique {environment : Environment}
    {entry : ValidatedEntry environment} {source target source' target' : Expr}
    (first : entry.capability = .certifiedReduction source target)
    (second : entry.capability = .certifiedReduction source' target') :
    source = source' ∧ target = target' :=
  ValidatedCapability.certifiedReduction_endpoints_injective (first.symm.trans second)

/--
One environment-validated primitive entry cannot be relabelled at a different
source or target representation endpoint.
-/
theorem ValidatedEntry.primitive_endpoints_unique {environment : Environment}
    {entry : ValidatedEntry environment} {source target source' target' : Expr}
    (first : entry.capability = .primitive source target)
    (second : entry.capability = .primitive source' target') :
    source = source' ∧ target = target' :=
  ValidatedCapability.primitive_endpoints_injective (first.symm.trans second)

end Registry
end ComplexityReduction
