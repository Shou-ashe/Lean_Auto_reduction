/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.Request
import ComplexityReduction.Certificate.DeterministicP

/-!
Versioned `prove_in_p` protocol.

This is deliberately separate from the frozen `AutoReductionRequest` inductive.
Adding a constructor to that historical ABI would change the meaning of its
closed request set and of existing finish payloads.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding Certificate

/-- Stage-Q v1 deterministic-P objective. -/
inductive InPRequestV1 : Type 2 where
  | proveInP (problem : PresentedProblem) : InPRequestV1

namespace InPRequestV1

/-- Exact interpretation of the versioned request. -/
def Holds : InPRequestV1 → Prop
  | .proveInP problem => NativeTMInP problem

end InPRequestV1

/-- Exact source, frozen trust policy, and P objective. -/
structure TypedInPRequestV1 where
  source : AutoReductionSource
  policy : AutoReductionTrustPolicy
  objective : InPRequestV1

/-- Evidence is indexed by both its objective and admitted presentation. -/
inductive TypedInPEvidenceV1 : InPRequestV1 → PresentedProblem → Type 2 where
  | deterministicMembership {problem : PresentedProblem}
      (membership : NativeTMInP problem) :
      TypedInPEvidenceV1 (.proveInP problem) problem

/-- A versioned P result with exact source admission and exact evidence. -/
structure TypedInPResultV1 (request : TypedInPRequestV1) where
  presented : PresentedProblem
  sourceMatches : request.source.Accepts request.policy.presentation presented
  evidence : TypedInPEvidenceV1 request.objective presented

namespace TypedInPResultV1

/-- Close `prove_in_p` only with exact native deterministic-P evidence. -/
def proveInP {problem : PresentedProblem} (policy : AutoReductionTrustPolicy)
    (sourceMatches : (AutoReductionSource.fromPresented problem).Accepts
      policy.presentation problem)
    (membership : NativeTMInP problem) :
    TypedInPResultV1
      { source := .fromPresented problem
        policy
        objective := .proveInP problem } where
  presented := problem
  sourceMatches := sourceMatches
  evidence := .deterministicMembership membership

/-- Recover the exact membership carried by a request-indexed result. -/
def extractMembership {problem : PresentedProblem} {policy : AutoReductionTrustPolicy}
    (result : TypedInPResultV1
      { source := .fromPresented problem
        policy
        objective := .proveInP problem }) : NativeTMInP problem :=
  match result.evidence with
  | .deterministicMembership membership => membership

end TypedInPResultV1

/-- Non-typed facade whose index still fixes the exact objective. -/
inductive InPResultV1 : InPRequestV1 → Type 2 where
  | deterministicMembership {problem : PresentedProblem}
      (membership : NativeTMInP problem) : InPResultV1 (.proveInP problem)

namespace InPResultV1

/-- Every result proves its own exact versioned objective. -/
theorem holds : {request : InPRequestV1} → InPResultV1 request → request.Holds
  | .proveInP _, .deterministicMembership membership => membership

end InPResultV1

end Protocol
end ComplexityReduction
