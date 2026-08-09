/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.CompletenessTransport

/-!
Versioned, exact request and result types for proving native NP-hardness.

This is deliberately separate from the frozen `AutoReductionRequest` ABI.  A
request binds one exact `PresentedProblem`; the problem is always the target
of a hardness-preserving forward path.  No target name, direction flag,
membership premise, or observational registry metadata occurs in the trusted
result type.
-/

namespace ComplexityReduction
namespace Protocol

open Encoding Certificate

/-- V1 NP-hardness request for one exact, already presented problem. -/
structure TypedNPHardRequestV1 where
  problem : PresentedProblem

namespace TypedNPHardRequestV1

/-- The sole proposition requested by the V1 protocol. -/
def Holds (request : TypedNPHardRequestV1) : Prop :=
  NativeTMNPHard request.problem

end TypedNPHardRequestV1

/--
Exact evidence accepted by a V1 NP-hardness result.

The transported constructor fixes the selected path's direction in its type:
the hard hub is the path source and the requested problem is the path target.
-/
inductive TypedNPHardEvidenceV1 (request : TypedNPHardRequestV1) : Type 2 where
  | registered (hardness : NativeTMNPHard request.problem) :
      TypedNPHardEvidenceV1 request
  | transported {hub : PresentedProblem}
      (hubHardness : NativeTMNPHard hub)
      (path : CertifiedPath hub request.problem) :
      TypedNPHardEvidenceV1 request

namespace TypedNPHardEvidenceV1

/-- Project exact native hardness from either admitted evidence form. -/
noncomputable def toNativeHardness {request : TypedNPHardRequestV1}
    (evidence : TypedNPHardEvidenceV1 request) : NativeTMNPHard request.problem :=
  match evidence with
  | .registered hardness => hardness
  | .transported hubHardness path => NativeTMNPHard.alongPath hubHardness path

end TypedNPHardEvidenceV1

/-- A result indexed by the exact V1 request it closes. -/
structure TypedNPHardResultV1 (request : TypedNPHardRequestV1) where
  evidence : TypedNPHardEvidenceV1 request

namespace TypedNPHardResultV1

/-- Close a request from native hardness already registered at its exact problem. -/
noncomputable def fromRegistered (request : TypedNPHardRequestV1)
    (hardness : NativeTMNPHard request.problem) : TypedNPHardResultV1 request :=
  ⟨.registered hardness⟩

/-- Close a request from a hard hub and a certified forward path to the request problem. -/
noncomputable def fromPath (request : TypedNPHardRequestV1) {hub : PresentedProblem}
    (hubHardness : NativeTMNPHard hub) (path : CertifiedPath hub request.problem) :
    TypedNPHardResultV1 request :=
  ⟨.transported hubHardness path⟩

/-- Extract the exact caller-facing NP-hardness theorem from a V1 result. -/
noncomputable def extractNativeHardness {request : TypedNPHardRequestV1}
    (result : TypedNPHardResultV1 request) : NativeTMNPHard request.problem :=
  result.evidence.toNativeHardness

end TypedNPHardResultV1

end Protocol
end ComplexityReduction
