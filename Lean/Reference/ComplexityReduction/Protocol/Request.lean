/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.NativeCompleteness

/-!
Canonical request objectives for V2 automatic reductions.

Every source and target named here is an exact `PresentedProblem`; no manifest,
path, string identifier, or registry lookup is an objective endpoint.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding Certificate

/-- The two distinct origins accepted by the library-level request protocol. -/
inductive AutoReductionSource : Type 2 where
  | fromSemantic (problem : ComplexityReduction.DecisionProblem) : AutoReductionSource
  | fromPresented (problem : PresentedProblem) : AutoReductionSource

/-- Presentation authority is explicit and defaults to failure for unknown policies. -/
inductive PresentationPolicy where
  | exactUser
  | structuralOnly
  deriving DecidableEq, Repr

/-- The minimal V2 trust policy; computation remains native/program-certified throughout this API. -/
structure AutoReductionTrustPolicy where
  presentation : PresentationPolicy
  requireNativeNP : Bool
  deriving Repr

namespace AutoReductionSource

/--
The kernel-visible source-to-presentation admission relation.

An explicitly supplied presentation is accepted only by exact equality.  A
semantic source can be automatically selected only with closed structural
evidence or an audited encoder-coherent wrapper to such evidence; no carrier
equality, codec shape, role, or metadata branch can satisfy this relation.
-/
def Accepts : AutoReductionSource → PresentationPolicy → PresentedProblem → Prop
  | .fromSemantic semanticProblem, .structuralOnly, presented =>
      presented.semantic = semanticProblem ∧ PresentedProblem.AutomaticallySelectablePresentation presented
  | .fromPresented requested, .exactUser, presented => presented = requested
  | _, _, _ => False

end AutoReductionSource

/-- The closed set of V2 automatic-reduction objectives. -/
inductive AutoReductionRequest : Type 2 where
  | reduceTo (source target : PresentedProblem) : AutoReductionRequest
  | reduceToKnownNP (source target : PresentedProblem) : AutoReductionRequest
  | proveInNP (problem : PresentedProblem) : AutoReductionRequest
  | proveNPComplete (problem : PresentedProblem) : AutoReductionRequest

/-- The canonical typed request combines its source, trust policy, and objective. -/
structure TypedAutoReductionRequest where
  source : AutoReductionSource
  policy : AutoReductionTrustPolicy
  objective : AutoReductionRequest

namespace AutoReductionRequest

/--
The exact proposition required by one request objective.

This interpretation is intentionally indexed by the source and target values
stored in the request.  It uses only native membership and program-indexed
V2 reductions; backend membership/completeness cannot satisfy any branch.
-/
def Holds : AutoReductionRequest → Prop
  | .reduceTo source target => Nonempty (CertifiedReduction source target)
  | .reduceToKnownNP source target =>
      Nonempty (CertifiedReduction source target) ∧ NativeTMInNP target
  | .proveInNP problem => NativeTMInNP problem
  | .proveNPComplete problem => NativeTMNPComplete problem

end AutoReductionRequest

end Protocol
end ComplexityReduction
