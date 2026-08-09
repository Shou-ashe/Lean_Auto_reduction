/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Core.ComponentRole
import ComplexityReduction.Protocol.MissingCapability

/-!
Typed requests and fail-closed blockers for one reduction component.

This is the Protocol owner for exact component endpoints and requests.  The
shared role vocabulary lives in `V2.Core.ComponentRole`, so provenance and
registry queries use precisely the same role type without making generic
certificates depend on this protocol module.  This module names no routes,
primitives, declarations, or string identifiers, and it constructs neither
programs nor certificates.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding

/--
The exact endpoint of one requested component.

The role and both already-lawful presentations are indices rather than
metadata fields, so a value for one role or source/target pair cannot be used
at another component endpoint.
-/
inductive ComponentEndpoint (role : ReductionComponentRole)
    (source target : PresentedProblem) : Type 2 where
  | exact : ComponentEndpoint role source target

/--
A request to resolve one exact component endpoint.

This request contains no executable, route-local primitive, certificate, TM
evidence, cost bound, declaration name, or string metadata.  It only fixes the
typed endpoint at which a later resolver must either find a component
capability or return a typed blocker.
-/
structure ComponentRequest (role : ReductionComponentRole)
    (source target : PresentedProblem) where
  endpoint : ComponentEndpoint role source target

namespace ComponentRequest

/-- Construct the unique request for one exact role-indexed endpoint. -/
def exact {role : ReductionComponentRole} {source target : PresentedProblem} :
    ComponentRequest role source target :=
  ⟨.exact⟩

/-- A fail-closed missing outcome for the requested exact component endpoint. -/
abbrev MissingOutcome {role : ReductionComponentRole} {source target : PresentedProblem} : Type 2 :=
  MissingCapability (ComponentEndpoint role source target)

/--
Report the closed missing reason at this request's exact component endpoint.
This function has no success branch and cannot manufacture a program,
primitive, certificate, complexity bound, or TM evidence.
-/
def missing {role : ReductionComponentRole} {source target : PresentedProblem}
    (request : ComponentRequest role source target) (reason : MissingCapabilityReason) :
    MissingOutcome (role := role) (source := source) (target := target) :=
  ⟨request.endpoint, reason⟩

/-- Block one exact component because automatic presentation evidence is missing. -/
def missingLawfulPresentation {role : ReductionComponentRole} {source target : PresentedProblem}
    (request : ComponentRequest role source target) :
    MissingOutcome (role := role) (source := source) (target := target) :=
  request.missing .lawfulPresentation

/-- Block one exact component because its direct typed primitive is missing. -/
def missingPrimitive {role : ReductionComponentRole} {source target : PresentedProblem}
    (request : ComponentRequest role source target) :
    MissingOutcome (role := role) (source := source) (target := target) :=
  request.missing .primitive

/-- Block one exact component because its relation semantics lack executable rows. -/
def missingExecutableRelationContract {role : ReductionComponentRole}
    {source target : PresentedProblem} (request : ComponentRequest role source target) :
    MissingOutcome (role := role) (source := source) (target := target) :=
  request.missing .executableRelationContract

@[simp] theorem missing_endpoint {role : ReductionComponentRole}
    {source target : PresentedProblem} (request : ComponentRequest role source target)
    (reason : MissingCapabilityReason) :
    (request.missing reason).endpoint = request.endpoint :=
  rfl

@[simp] theorem missing_reason {role : ReductionComponentRole}
    {source target : PresentedProblem} (request : ComponentRequest role source target)
    (reason : MissingCapabilityReason) :
    (request.missing reason).reason = reason :=
  rfl

@[simp] theorem missingPrimitive_reason {role : ReductionComponentRole}
    {source target : PresentedProblem} (request : ComponentRequest role source target) :
    (request.missingPrimitive).reason = .primitive :=
  rfl

@[simp] theorem missingExecutableRelationContract_reason {role : ReductionComponentRole}
    {source target : PresentedProblem} (request : ComponentRequest role source target) :
    (request.missingExecutableRelationContract).reason = .executableRelationContract :=
  rfl

end ComponentRequest

/--
The exact endpoint of a request whose source is still a semantic raw problem,
before any lawful presentation has been supplied.  This is deliberately a
different type from `ComponentEndpoint`, whose source index is already a
`PresentedProblem`.
-/
inductive PresentationBeforeEndpoint (rawSource : ComplexityReduction.DecisionProblem)
    (target : PresentedProblem) : Type 2 where
  | exact : PresentationBeforeEndpoint rawSource target

/-- A request made before the raw source has a lawful presentation. -/
structure PresentationBeforeRequest (rawSource : ComplexityReduction.DecisionProblem)
    (target : PresentedProblem) where
  endpoint : PresentationBeforeEndpoint rawSource target

namespace PresentationBeforeRequest

/-- Construct the exact pre-presentation request for a raw semantic source. -/
def exact {rawSource : ComplexityReduction.DecisionProblem} {target : PresentedProblem} :
    PresentationBeforeRequest rawSource target :=
  ⟨.exact⟩

/--
The only Protocol outcome before source presentation is supplied: a typed
lawful-presentation blocker at the raw-source endpoint.  It is intentionally
not a `ComponentRequest.MissingOutcome`.
-/
abbrev MissingOutcome {rawSource : ComplexityReduction.DecisionProblem}
    {target : PresentedProblem} : Type 2 :=
  MissingCapability (PresentationBeforeEndpoint rawSource target)

/-- Report that the raw source must first receive lawful presentation evidence. -/
def missingLawfulPresentation {rawSource : ComplexityReduction.DecisionProblem}
    {target : PresentedProblem} (request : PresentationBeforeRequest rawSource target) :
    MissingOutcome (rawSource := rawSource) (target := target) :=
  MissingCapability.lawfulPresentation request.endpoint

@[simp] theorem missingLawfulPresentation_endpoint
    {rawSource : ComplexityReduction.DecisionProblem} {target : PresentedProblem}
    (request : PresentationBeforeRequest rawSource target) :
    (request.missingLawfulPresentation).endpoint = request.endpoint :=
  rfl

@[simp] theorem missingLawfulPresentation_reason
    {rawSource : ComplexityReduction.DecisionProblem} {target : PresentedProblem}
    (request : PresentationBeforeRequest rawSource target) :
    (request.missingLawfulPresentation).reason = .lawfulPresentation :=
  rfl

end PresentationBeforeRequest

end Protocol
end ComplexityReduction
