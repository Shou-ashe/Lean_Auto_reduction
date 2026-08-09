/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Export
import Lean.Meta.Basic

/-!
Read-only role-aware graph queries over validated V2 certificates.

This module consumes only `ValidatedExportObservation`s. Its edges preserve
the exact elaborated `Lean.Expr` endpoints already classified from declaration
types; component-role provenance remains optional, non-authoritative
annotation data.
-/

namespace ComplexityReduction
namespace Registry

open Lean
open Meta

/-- A graph edge extracted from one elaborated-type-validated certificate observation. -/
inductive ValidatedCertificateEdge (environment : Lean.Environment) where
  | reduction (observation : ValidatedExportObservation environment)
      (source target : Lean.Expr)
      (validated : observation.entry.capability = .certifiedReduction source target) :
      ValidatedCertificateEdge environment
  | equiv (observation : ValidatedExportObservation environment)
      (source target : Lean.Expr)
      (validated : observation.entry.capability = .certifiedEquiv source target) :
      ValidatedCertificateEdge environment
  | presentationChange (observation : ValidatedExportObservation environment)
      (source target : Lean.Expr)
      (validated : observation.entry.capability = .certifiedPresentationChange source target) :
      ValidatedCertificateEdge environment

namespace ValidatedCertificateEdge

variable {environment : Lean.Environment}

/-- Recover the validated observation from which an edge was extracted. -/
def observation : ValidatedCertificateEdge environment → ValidatedExportObservation environment
  | .reduction observation _ _ _ => observation
  | .equiv observation _ _ _ => observation
  | .presentationChange observation _ _ _ => observation

/-- Recover the exact source endpoint retained by the validated capability classification. -/
def source : ValidatedCertificateEdge environment → Lean.Expr
  | .reduction _ source _ _ => source
  | .equiv _ source _ _ => source
  | .presentationChange _ source _ _ => source

/-- Recover the exact target endpoint retained by the validated capability classification. -/
def target : ValidatedCertificateEdge environment → Lean.Expr
  | .reduction _ _ target _ => target
  | .equiv _ _ target _ => target
  | .presentationChange _ _ target _ => target

/-- Recover the non-authoritative role provenance attached after validation, if any. -/
def componentRoleProvenance? :
    ValidatedCertificateEdge environment → Option Annotations.ComponentRoleCandidateProvenance
  | .reduction observation _ _ _ => observation.componentRoleProvenance?
  | .equiv observation _ _ _ => observation.componentRoleProvenance?
  | .presentationChange observation _ _ _ => observation.componentRoleProvenance?

/-- Recover only the optional role value from one edge's annotation provenance. -/
def componentRole? (edge : ValidatedCertificateEdge environment) :
    Option ReductionComponentRole :=
  edge.componentRoleProvenance?.map Annotations.ComponentRoleCandidateProvenance.role

/-- The capability head of a reduction edge is exactly its certified-reduction classification. -/
theorem reduction_validatedCapability {environment : Lean.Environment}
    (observation : ValidatedExportObservation environment) (source target : Lean.Expr)
    (validated : observation.entry.capability = .certifiedReduction source target) :
    (.reduction observation source target validated : ValidatedCertificateEdge environment).observation.entry.capability =
      ValidatedCapability.certifiedReduction source target :=
  validated

/-- The capability head of an equivalence edge is exactly its certified-equivalence classification. -/
theorem equiv_validatedCapability {environment : Lean.Environment}
    (observation : ValidatedExportObservation environment) (source target : Lean.Expr)
    (validated : observation.entry.capability = .certifiedEquiv source target) :
    (.equiv observation source target validated : ValidatedCertificateEdge environment).observation.entry.capability =
      ValidatedCapability.certifiedEquiv source target :=
  validated

/-- The capability head of a presentation-change edge is its validated canonical type. -/
theorem presentationChange_validatedCapability {environment : Lean.Environment}
    (observation : ValidatedExportObservation environment) (source target : Lean.Expr)
    (validated : observation.entry.capability = .certifiedPresentationChange source target) :
    (ValidatedCertificateEdge.observation
      (.presentationChange observation source target validated : ValidatedCertificateEdge environment)).entry.capability =
      ValidatedCapability.certifiedPresentationChange source target :=
  validated

/-- Extract a graph edge only from a validated reduction or equivalence capability. -/
def ofValidatedObservation? (observation : ValidatedExportObservation environment) :
    Option (ValidatedCertificateEdge environment) :=
  match capability : observation.entry.capability with
  | .certifiedReduction source target => some (.reduction observation source target capability)
  | .certifiedEquiv source target => some (.equiv observation source target capability)
  | .certifiedPresentationChange source target =>
      some (.presentationChange observation source target capability)
  | _ => none

/-- Test a role filter without giving the role any capability-producing effect. -/
def hasComponentRole (edge : ValidatedCertificateEdge environment)
    (role : ReductionComponentRole) : Bool :=
  match edge.componentRole? with
  | some observedRole => if observedRole = role then true else false
  | none => false

/-- Match exact elaborated endpoints and, optionally, a non-authoritative component role. -/
def matchesQuery (edge : ValidatedCertificateEdge environment) (source target : Lean.Expr)
    (role? : Option ReductionComponentRole) : Bool :=
  edge.source == source && edge.target == target &&
    match role? with
    | none => true
    | some role => edge.hasComponentRole role

/-- Controlled Lean-side normalization used only for endpoint equality, never identity serialization. -/
private def controlledDefEq (first second : Lean.Expr) : MetaM Bool := do
  let first ← whnf first
  let second ← whnf second
  isDefEq first second

/--
Match graph endpoints through Lean's controlled `whnf` and definitional
equality.  The optional component role remains a read-only filter and cannot
create an edge or capability.
-/
def matchesQueryDefEq (edge : ValidatedCertificateEdge environment) (source target : Lean.Expr)
    (role? : Option ReductionComponentRole) : MetaM Bool := do
  let roleMatches :=
    match role? with
    | none => true
    | some role => edge.hasComponentRole role
  if !roleMatches then
    return false
  unless ← controlledDefEq edge.source source do
    return false
  controlledDefEq edge.target target

end ValidatedCertificateEdge

/--
All validated reduction/equivalence edges in the environment.

No declaration name, definition body, string payload, or component tag is
used to manufacture an edge: only `exportValidatedObservations` and its
validated capability classification are consumed.
-/
def validatedCertificateEdges (environment : Lean.Environment) :
    List (ValidatedCertificateEdge environment) :=
  (exportValidatedObservations environment).filterMap ValidatedCertificateEdge.ofValidatedObservation?

/--
Query adjacency by exact elaborated source and target expressions, with an
optional component-role filter. Passing `none` retains final-composition and
all other component edges together; a final convenience edge never replaces
the component-level graph.
-/
def queryValidatedCertificateEdges (environment : Lean.Environment)
    (source target : Lean.Expr) (role? : Option ReductionComponentRole) :
    List (ValidatedCertificateEdge environment) :=
  (validatedCertificateEdges environment).filter fun edge => edge.matchesQuery source target role?

/--
Defeq-aware adjacency query for Lean-side planning.

Unlike the compatibility exact-expression query, this is deliberately in
`MetaM`: expression hashes and pretty strings remain diagnostics only, while
the actual transition decision is Lean's `isDefEq` after controlled `whnf`.
Non-defeq representations must still be connected by an explicit certified
adapter edge.
-/
def queryValidatedCertificateEdgesDefEq (environment : Lean.Environment)
    (source target : Lean.Expr) (role? : Option ReductionComponentRole) :
    MetaM (List (ValidatedCertificateEdge environment)) := do
  (validatedCertificateEdges environment).filterM fun edge =>
    edge.matchesQueryDefEq source target role?

/--
The optional final-composition view is only a filtered convenience view over
the complete validated graph. It has no independent validation or authority.
-/
def finalCompositionCertificateEdges (environment : Lean.Environment) :
    List (ValidatedCertificateEdge environment) :=
  (validatedCertificateEdges environment).filter fun edge =>
    edge.hasComponentRole .finalComposition

end Registry
end ComplexityReduction
