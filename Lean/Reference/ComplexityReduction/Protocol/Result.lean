/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.Request
import ComplexityReduction.Certificate.Path
import ComplexityReduction.Certificate.CompletenessTransport

/-!
Request-indexed V2 automatic-reduction results.

The result constructors accept only the exact native capability or exact
`CertifiedReduction` prescribed by their original request objective.  There is
no manifest, registry path, string, or backend-completeness admission path.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding Certificate

/-- Exact typed evidence for an objective at the presentation accepted for its request source. -/
inductive TypedObjectiveEvidence : AutoReductionRequest → PresentedProblem → Type 2 where
  | reduction {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
      TypedObjectiveEvidence (.reduceTo source target) source
  | reductionToKnownNP {source target : PresentedProblem}
      (certificate : CertifiedReduction source target) (targetMembership : NativeTMInNP target) :
      TypedObjectiveEvidence (.reduceToKnownNP source target) source
  | nativeMembership {problem : PresentedProblem} (membership : NativeTMInNP problem) :
      TypedObjectiveEvidence (.proveInNP problem) problem
  | nativeCompleteness {problem : PresentedProblem} (complete : NativeTMNPComplete problem) :
      TypedObjectiveEvidence (.proveNPComplete problem) problem

/-- A source/policy/objective request result with all three inputs fixed in its type. -/
structure TypedAutoReductionResult (request : TypedAutoReductionRequest) where
  presented : PresentedProblem
  sourceMatches : request.source.Accepts request.policy.presentation presented
  evidence : TypedObjectiveEvidence request.objective presented

namespace TypedAutoReductionResult

/--
Close an exact reduction request from an arbitrary-length atomic certificate
path.  The stored objective evidence is definitionally the path's canonical
composition; no second map, cost, or TM witness is accepted.
-/
def reduceToPath {source target : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented source).Accepts policy.presentation source)
    (path : CertifiedPath source target) :
    TypedAutoReductionResult
      { source := .fromPresented source
        policy
        objective := .reduceTo source target } where
  presented := source
  sourceMatches := sourceMatches
  evidence := .reduction path.toCertifiedReduction

@[simp]
theorem reduceToPath_evidence {source target : PresentedProblem}
    (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented source).Accepts policy.presentation source)
    (path : CertifiedPath source target) :
    (reduceToPath policy sourceMatches path).evidence =
      TypedObjectiveEvidence.reduction path.toCertifiedReduction :=
  rfl

/-- Close an exact known-NP request from the same canonical path and native target membership. -/
def reduceToKnownNPPath {source target : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented source).Accepts policy.presentation source)
    (path : CertifiedPath source target) (targetMembership : NativeTMInNP target) :
    TypedAutoReductionResult
      { source := .fromPresented source
        policy
        objective := .reduceToKnownNP source target } where
  presented := source
  sourceMatches := sourceMatches
  evidence := .reductionToKnownNP path.toCertifiedReduction targetMembership

@[simp]
theorem reduceToKnownNPPath_evidence {source target : PresentedProblem}
    (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented source).Accepts policy.presentation source)
    (path : CertifiedPath source target) (targetMembership : NativeTMInNP target) :
    (reduceToKnownNPPath policy sourceMatches path targetMembership).evidence =
      TypedObjectiveEvidence.reductionToKnownNP path.toCertifiedReduction targetMembership :=
  rfl

/-- Close an exact native-membership request from exact registered native evidence. -/
def proveInNP {problem : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented problem).Accepts
      policy.presentation problem)
    (membership : NativeTMInNP problem) :
    TypedAutoReductionResult
      { source := .fromPresented problem
        policy
        objective := .proveInNP problem } where
  presented := problem
  sourceMatches := sourceMatches
  evidence := .nativeMembership membership

@[simp]
theorem proveInNP_evidence {problem : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented problem).Accepts
      policy.presentation problem)
    (membership : NativeTMInNP problem) :
    (proveInNP policy sourceMatches membership).evidence =
      TypedObjectiveEvidence.nativeMembership membership :=
  rfl

/-- Close an exact native-completeness request from exact native completeness evidence. -/
def proveNPComplete {problem : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented problem).Accepts
      policy.presentation problem)
    (complete : NativeTMNPComplete problem) :
    TypedAutoReductionResult
      { source := .fromPresented problem
        policy
        objective := .proveNPComplete problem } where
  presented := problem
  sourceMatches := sourceMatches
  evidence := .nativeCompleteness complete

@[simp]
theorem proveNPComplete_evidence {problem : PresentedProblem}
    (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented problem).Accepts
      policy.presentation problem)
    (complete : NativeTMNPComplete problem) :
    (proveNPComplete policy sourceMatches complete).evidence =
      TypedObjectiveEvidence.nativeCompleteness complete :=
  rfl

/-- Project exact native membership from a result already indexed by a membership request. -/
def extractNativeMembership {problem : PresentedProblem} {policy : AutoReductionTrustPolicy}
    (result : TypedAutoReductionResult
      { source := .fromPresented problem
        policy
        objective := .proveInNP problem }) : NativeTMInNP problem :=
  match result.evidence with
  | .nativeMembership membership => membership

/-- Project exact native completeness for its independent final artifact axiom audit. -/
def extractNativeCompleteness {problem : PresentedProblem} {policy : AutoReductionTrustPolicy}
    (result : TypedAutoReductionResult
      { source := .fromPresented problem
        policy
        objective := .proveNPComplete problem }) : NativeTMNPComplete problem :=
  match result.evidence with
  | .nativeCompleteness complete => complete

end TypedAutoReductionResult

/-- A final result whose accepted evidence is fixed by its original request. -/
inductive AutoReductionResult : AutoReductionRequest → Type 2 where
  | reduction {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
      AutoReductionResult (.reduceTo source target)
  | reductionToKnownNP {source target : PresentedProblem}
      (certificate : CertifiedReduction source target) (targetMembership : NativeTMInNP target) :
      AutoReductionResult (.reduceToKnownNP source target)
  | nativeMembership {problem : PresentedProblem} (membership : NativeTMInNP problem) :
      AutoReductionResult (.proveInNP problem)
  | nativeCompleteness {problem : PresentedProblem} (complete : NativeTMNPComplete problem) :
      AutoReductionResult (.proveNPComplete problem)

namespace AutoReductionResult

/-- Every request-indexed result proves the exact objective interpretation of its own request. -/
theorem holds : {request : AutoReductionRequest} →
    AutoReductionResult request → request.Holds
  | .reduceTo source target, .reduction certificate => ⟨certificate⟩
  | .reduceToKnownNP source target, .reductionToKnownNP certificate targetMembership =>
      ⟨⟨certificate⟩, targetMembership⟩
  | .proveInNP problem, .nativeMembership membership => membership
  | .proveNPComplete problem, .nativeCompleteness complete => complete

/-- Build a reduction result only from an exact source-to-target certificate. -/
def reduceTo {source target : PresentedProblem} (certificate : CertifiedReduction source target) :
    AutoReductionResult (.reduceTo source target) :=
  .reduction certificate

/-- A known-NP reduction result binds both its exact route and the selected target's native membership. -/
def reduceToKnownNP {source target : PresentedProblem}
    (certificate : CertifiedReduction source target) (targetMembership : NativeTMInNP target) :
    AutoReductionResult (.reduceToKnownNP source target) :=
  .reductionToKnownNP certificate targetMembership

/-- Build a membership result only from exact V2-native membership. -/
def proveInNP {problem : PresentedProblem} (membership : NativeTMInNP problem) :
    AutoReductionResult (.proveInNP problem) :=
  .nativeMembership membership

/-- Build a completeness result only from exact V2-native completeness. -/
def proveNPComplete {problem : PresentedProblem} (complete : NativeTMNPComplete problem) :
    AutoReductionResult (.proveNPComplete problem) :=
  .nativeCompleteness complete

end AutoReductionResult

end Protocol
end ComplexityReduction
