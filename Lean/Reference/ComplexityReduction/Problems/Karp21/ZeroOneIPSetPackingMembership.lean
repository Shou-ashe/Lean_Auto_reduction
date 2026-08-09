/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetPacking
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Presentation.ZeroOneIP
import ComplexityReduction.Presentation.ZeroOneIPBinary

/-!
Backend-membership annotations for the exact unary/binary structured 0-1 IP
and structured Set Packing presentations.

The imported CR theorems establish only compatibility `TMInNP`. They do not
provide V2 program-indexed checkers with V2 encoding discipline, so this leaf
exports no native verifier, native membership, or completeness capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace ZeroOneIPSetPackingMembership

open Certificate

/-- CR's direct-TM membership theorem at the exact unary structured 0-1 IP endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem zeroOneIPStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.ZeroOneIP.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingStructuredDecisionProblem
  exact ComplexityReduction.Karp21.zeroOneIPStructured_TMInNP

/-- The V2 alias retains the exact unary 0-1 IP presentation in its type. -/
theorem zeroOneIPStructured_backendTMInNP :
    BackendTMInNP Presentation.ZeroOneIP.structuredProblem :=
  zeroOneIPStructured_backendTMInNP_export

/-- CR's direct-TM membership theorem at the exact binary structured 0-1 IP endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem zeroOneIPBinaryStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.ZeroOneIPBinary.binaryStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
  exact ComplexityReduction.Karp21.zeroOneIPBinaryStructured_TMInNP

/-- The V2 alias retains the distinct binary 0-1 IP presentation in its type. -/
theorem zeroOneIPBinaryStructured_backendTMInNP :
    BackendTMInNP Presentation.ZeroOneIPBinary.binaryStructuredProblem :=
  zeroOneIPBinaryStructured_backendTMInNP_export

/-- CR's direct-TM membership theorem at the exact structured Set Packing endpoint. -/
@[complexity_reduction_ir_typed_verifier]
theorem setPackingStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.SetSystem.setPackingStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.setPackingStructuredDecisionProblem
  exact ComplexityReduction.Karp21.setPackingStructured_TMInNP

/-- The V2 alias retains the exact bounded Set Packing presentation in its type. -/
theorem setPackingStructured_backendTMInNP :
    BackendTMInNP Presentation.SetSystem.setPackingStructuredProblem :=
  setPackingStructured_backendTMInNP_export

end ZeroOneIPSetPackingMembership
end Karp21
end Problems
end ComplexityReduction
