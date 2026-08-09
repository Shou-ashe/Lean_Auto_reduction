/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Export

/-!
Non-authoritative observation of attributed parameterized reduction families.

The canonical validator intentionally rejects declarations with top-level
binders.  This module does not relax that boundary.  It only records the
syntactic telescope and direct `CertifiedReduction` result shape of an
attributed declaration so a later Lean-side instantiator can decide which
families are worth attempting.

Endpoint templates may contain loose bound variables and universe parameters.
They are observations only: this module provides no conversion to
`ValidatedCapability`, `ValidatedEntry`, `Query.SessionAtom`, or a graph edge.
A fully elaborated closed application must still pass the existing query and
closed-capability validator before it can be used.
-/

namespace ComplexityReduction
namespace Registry

open Lean

/--
One attributed declaration whose nonempty `forall` telescope ends directly in
a two-endpoint `CertifiedReduction` head.

The environment index documents where the observation was made.  It grants no
capability: `sourceTemplate` and `targetTemplate` are deliberately named as
open templates rather than exact endpoints.
-/
structure ParameterizedReductionFamilyObservation (environment : Environment) where
  candidate : Name
  elaboratedType : Expr
  binderCount : Nat
  resultType : Expr
  sourceTemplate : Expr
  targetTemplate : Expr
  componentRoleProvenance? : Option Annotations.ComponentRoleCandidateProvenance

/-- The binder classification retained for a non-authoritative family observation. -/
inductive ParameterizedFamilyBinderKind where
  | explicit
  | implicit
  | strictImplicit
  | instanceImplicit
  deriving DecidableEq, Repr

/-- One telescope binder retained verbatim enough for a later Lean-side instantiator. -/
structure ParameterizedFamilyBinder where
  name : Name
  domain : Expr
  kind : ParameterizedFamilyBinderKind
  deriving Repr

/-- The supported canonical result heads of an open attributed family. -/
inductive ParameterizedFamilyCapabilityTemplate where
  | presentedProblem
  | structuralPresentation (encodedType representation : Expr)
  | certifiedReduction (source target : Expr)
  | certifiedEquiv (source target : Expr)
  | certifiedPresentationChange (source target : Expr)
  | certifiedRouteProvenance (source hub sharedTarget target ingress sharedGadget optionalEgress
      finalCertificate : Expr)
  | primitive (source target : Expr)
  | backendVerifier (problem : Expr)
  | verifierEncodingDiscipline (problem verifier : Expr)
  | nativeVerifierCapability (problem : Expr)
  | nativeTMInNP (problem : Expr)
  | nativeTMNPComplete (problem : Expr)
  | backendTMInNP (problem : Expr)
  | backendTMNPComplete (problem : Expr)
  deriving Repr

/--
An open capability family observed from a tagged declaration type.

This remains diagnostic only: its endpoint templates can contain loose bound
variables, so it cannot be turned into a `ValidatedEntry` or graph edge.  A
later instantiator must elaborate a closed application and re-run the existing
closed validator.
-/
structure ParameterizedCapabilityFamilyObservation (environment : Environment) where
  candidate : Name
  elaboratedType : Expr
  telescope : List ParameterizedFamilyBinder
  resultType : Expr
  capabilityTemplate : ParameterizedFamilyCapabilityTemplate
  componentRoleProvenance? : Option Annotations.ComponentRoleCandidateProvenance

/-- Peel only metadata and a nonempty direct `forall` telescope, without normalization. -/
private partial def consumeForallTelescope (type : Expr) (binderCount : Nat := 0) :
    Nat × Expr :=
  match type.consumeMData with
  | .forallE _ _ body _ => consumeForallTelescope body (binderCount + 1)
  | resultType => (binderCount, resultType)

private def binderKind (info : BinderInfo) : ParameterizedFamilyBinderKind :=
  match info with
  | .default => .explicit
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instanceImplicit

/-- Preserve the full open telescope instead of only its arity. -/
private partial def consumeObservedTelescope (type : Expr)
    (reversed : List ParameterizedFamilyBinder := []) :
    List ParameterizedFamilyBinder × Expr :=
  match type.consumeMData with
  | .forallE name domain body info =>
      consumeObservedTelescope body
        ({ name, domain, kind := binderKind info } :: reversed)
  | resultType => (reversed.reverse, resultType)

private def binaryTemplate? (resultType : Expr) (head : Name)
    (mkTemplate : Expr → Expr → ParameterizedFamilyCapabilityTemplate) :
    Option ParameterizedFamilyCapabilityTemplate :=
  let resultType := resultType.consumeMData
  if resultType.getAppFn.consumeMData.isConstOf head then
    match resultType.getAppArgs with
    | #[source, target] => some (mkTemplate source target)
    | _ => none
  else none

private def unaryTemplate? (resultType : Expr) (head : Name)
    (mkTemplate : Expr → ParameterizedFamilyCapabilityTemplate) :
    Option ParameterizedFamilyCapabilityTemplate :=
  let resultType := resultType.consumeMData
  if resultType.getAppFn.consumeMData.isConstOf head then
    match resultType.getAppArgs with
    | #[problem] => some (mkTemplate problem)
    | _ => none
  else none

private def nullaryTemplate? (resultType : Expr) (head : Name)
    (template : ParameterizedFamilyCapabilityTemplate) : Option ParameterizedFamilyCapabilityTemplate :=
  if resultType.consumeMData.isConstOf head then some template else none

private def routeProvenanceTemplate? (resultType : Expr) :
    Option ParameterizedFamilyCapabilityTemplate :=
  let resultType := resultType.consumeMData
  if resultType.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Certificate.CertifiedRouteProvenance then
    match resultType.getAppArgs with
    | #[source, hub, sharedTarget, target, ingress, sharedGadget, optionalEgress, finalCertificate] =>
        some (.certifiedRouteProvenance source hub sharedTarget target ingress sharedGadget optionalEgress
          finalCertificate)
    | _ => none
  else none

/-- Recognize only canonical open family result heads; aliases and arbitrary propositions fail closed. -/
private def capabilityTemplate? (resultType : Expr) : Option ParameterizedFamilyCapabilityTemplate :=
  nullaryTemplate? resultType ``ComplexityReduction.Encoding.PresentedProblem .presentedProblem <|>
  binaryTemplate? resultType
    ``ComplexityReduction.Encoding.StructuralRepresentationCertificate
    .structuralPresentation <|>
  binaryTemplate? resultType ``ComplexityReduction.Certificate.CertifiedReduction
    .certifiedReduction <|>
  binaryTemplate? resultType ``ComplexityReduction.Certificate.CertifiedEquiv
    .certifiedEquiv <|>
  binaryTemplate? resultType ``ComplexityReduction.Certificate.CertifiedPresentationChange
    .certifiedPresentationChange <|>
  routeProvenanceTemplate? resultType <|>
  binaryTemplate? resultType ``ComplexityReduction.Program.Primitive .primitive <|>
  unaryTemplate? resultType ``ComplexityReduction.Certificate.CertifiedVerifier
    .backendVerifier <|>
  binaryTemplate? resultType
    ``ComplexityReduction.Certificate.CertifiedVerifierEncodingDiscipline
    .verifierEncodingDiscipline <|>
  unaryTemplate? resultType ``ComplexityReduction.Certificate.NativeVerifierCapability
    .nativeVerifierCapability <|>
  unaryTemplate? resultType ``ComplexityReduction.Certificate.NativeTMInNP .nativeTMInNP <|>
  unaryTemplate? resultType ``ComplexityReduction.Certificate.NativeTMNPComplete
    .nativeTMNPComplete <|>
  unaryTemplate? resultType ``ComplexityReduction.TMInNP .backendTMInNP <|>
  unaryTemplate? resultType ``ComplexityReduction.TMNPCompleteEnc .backendTMNPComplete

/-- Recognize only the direct canonical two-endpoint reduction head. -/
private def certifiedReductionTemplates? (resultType : Expr) : Option (Expr × Expr) :=
  let resultType := resultType.consumeMData
  if resultType.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Certificate.CertifiedReduction then
    match resultType.getAppArgs with
    | #[sourceTemplate, targetTemplate] => some (sourceTemplate, targetTemplate)
    | _ => none
  else
    none

/--
Observe an attributed open family for any canonical capability head supported
by the closed validator.  The result is intentionally not validated capability
evidence: its telescope remains open and must be instantiated in Lean first.
-/
def observeAttributedParameterizedCapabilityFamily? (environment : Environment)
    (candidate : Name) : Option (ParameterizedCapabilityFamilyObservation environment) := do
  if isCandidateName environment candidate then
    let declaration ← environment.find? candidate
    let (telescope, resultType) := consumeObservedTelescope declaration.type
    if telescope.isEmpty then
      none
    else
      let capabilityTemplate ← capabilityTemplate? resultType
      some
        { candidate
          elaboratedType := declaration.type
          telescope
          resultType
          capabilityTemplate
          componentRoleProvenance? :=
            Annotations.componentRoleCandidateProvenance? environment candidate }
  else
    none

/-- All supported open capability families in the annotation-owned candidate scan scope. -/
def attributedParameterizedCapabilityFamilies (environment : Environment) :
    List (ParameterizedCapabilityFamilyObservation environment) :=
  (candidateNames environment).filterMap
    (observeAttributedParameterizedCapabilityFamily? environment)

/--
Observe one attributed parameterized reduction family from its environment
declaration type.

The declaration must already be in the annotations-owned candidate set, must
have at least one direct top-level binder, and must end directly in the
canonical `CertifiedReduction` head.  Aliases, top-level lets, metadata
families, and closed reductions fail closed.
-/
def observeAttributedParameterizedReductionFamily? (environment : Environment)
    (candidate : Name) : Option (ParameterizedReductionFamilyObservation environment) := do
  if isCandidateName environment candidate then
    let declaration ← environment.find? candidate
    let (binderCount, resultType) := consumeForallTelescope declaration.type
    if binderCount == 0 then
      none
    else
      let (sourceTemplate, targetTemplate) ← certifiedReductionTemplates? resultType
      some
        { candidate
          elaboratedType := declaration.type
          binderCount
          resultType
          sourceTemplate
          targetTemplate
          componentRoleProvenance? :=
            Annotations.componentRoleCandidateProvenance? environment candidate }
  else
    none

/--
Scan the annotations-owned candidate set for parameterized reduction-family
observations.  The result is intentionally separate from `exportValidated`.
-/
def attributedParameterizedReductionFamilies (environment : Environment) :
    List (ParameterizedReductionFamilyObservation environment) :=
  (candidateNames environment).filterMap
    (observeAttributedParameterizedReductionFamily? environment)

/-- An untagged name cannot become a parameterized-family observation. -/
@[simp]
theorem observeAttributedParameterizedReductionFamily?_eq_none_of_notCandidate
    {environment : Environment} {candidate : Name}
    (notCandidate : isCandidateName environment candidate = false) :
    observeAttributedParameterizedReductionFamily? environment candidate = none := by
  unfold observeAttributedParameterizedReductionFamily?
  rw [notCandidate]
  rfl

end Registry
end ComplexityReduction
