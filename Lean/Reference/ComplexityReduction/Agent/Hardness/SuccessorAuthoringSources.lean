/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Domain.NAEThreeSATToMaxCut
import ComplexityReduction.Domain.ThreeSATToNAEThreeSAT

/-!
Successor-only public sources for dependent authoring.

Declarations in this module are not direct authoring admissions.  The observer
may expose one only when a separately registered, endpoint-exact certified
successor continues its target to the requested endpoint.  Keeping this module
separate from `GadgetAuthoringSources` prevents a structured MaxCut request from
seeing the composed 3SAT-to-MaxCut shortcut used by the MaxCutBinary task.
-/

namespace ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources

open ComplexityReduction

/--
The exact raw 3SAT-to-structured-MaxCut program used only as the predecessor of
an independently certified successor.  It composes the two public mathematical
components without publishing a `CertifiedReduction` or a hardness theorem.
-/
@[complexity_reduction_ir_component_shared_gadget]
noncomputable def threeSATToMaxCutSuccessorOnlyTMKarpReduction :
    TMKarpReduction
      Domain.ThreeSATToNAEThreeSAT.sourceProblem.toEncodedDecisionProblem
      Domain.NAEThreeSATToMaxCut.targetProblem.toEncodedDecisionProblem :=
  TMKarpReduction.comp
    Domain.NAEThreeSATToMaxCut.naeThreeSATToMaxCutStructuredTMKarpReduction
    Domain.ThreeSATToNAEThreeSAT.threeSATToNAEThreeSATStructuredTMKarpReduction

assert_standard_axioms threeSATToMaxCutSuccessorOnlyTMKarpReduction

end ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources
