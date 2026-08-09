/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SATCosted
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.StrictLogSpaceMachine

/-!
Strict streaming certificates for the CNF-to-3CNF splitting phase.

The verified semantic map remains `CNF.splitToThreeCNF`; this file records the
project-local streaming certificate separately from the semantic proof.
-/

namespace ComplexityReduction
namespace SAT

/-- Project-local structural CNF encoded type used as the splitting input. -/
def cnfStructuralEncodedType : EncodedType where
  Carrier := CNF
  Symbol := Unit
  finite_symbol := inferInstance
  encode := fun φ => List.replicate (CNF.structuralSize φ) ()

/-- Strict streaming primitive for the standard long-clause splitting pass. -/
noncomputable def CNF.splitToThreeCNFStrictPrimitive :
    StrictStreamPrimitive
      cnfStructuralEncodedType
      threeSATDecisionProblem.Instance
      CNF.splitToThreeCNF :=
  { name := "SAT.CNF.splitToThreeCNF"
    pass_bound := "One left-to-right pass over clauses, with a bounded scan inside each clause."
    workspace_bound := "O(log |input|) fresh-variable counter and clause-position counters."
    output_order :=
      "Emit each short clause directly; emit split long-clause blocks in source order."
    oracle_free :=
      "The splitter reads only CNF syntax and a fresh-variable counter; it never branches on \
       satisfiability."
    costed := CostedPolyTimeMap.of_costed
      (CostedMap.of_encodedPolynomialSizeBound
        (by
          simpa [cnfStructuralEncodedType, EncodedType.inputSize, SAT.threeSATDecisionProblem,
            SAT.threeSATSatLike, SAT.threeCNFEncodedType]
            using CNF.splitToThreeCNF_polynomialStructuralSizeBound)) }

/-- Strict streaming map for `CNF.splitToThreeCNF`. -/
noncomputable def CNF.splitToThreeCNFStrictMap :
    StrictStreamMap
      (X := cnfStructuralEncodedType)
      (Y := threeSATDecisionProblem.Instance)
      CNF.splitToThreeCNF :=
  StrictStreamMap.registeredPrimitive CNF.splitToThreeCNFStrictPrimitive

/-- Strict log-space map obtained from the streaming certificate for splitting. -/
noncomputable def CNF.splitToThreeCNFStrictLogSpaceMap :
    StrictLogSpaceMap
      (X := cnfStructuralEncodedType)
      (Y := threeSATDecisionProblem.Instance)
      CNF.splitToThreeCNF :=
  CNF.splitToThreeCNFStrictMap.toStrictLogSpaceMap

/-- Project-local machine/log-space certificate for `CNF.splitToThreeCNF`. -/
noncomputable def CNF.splitToThreeCNFMachineMap :
    StrictLogSpaceMachineMap
      (X := cnfStructuralEncodedType)
      (Y := threeSATDecisionProblem.Instance)
      CNF.splitToThreeCNF :=
  CNF.splitToThreeCNFStrictMap.toMachineMap

end SAT
end ComplexityReduction
