/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMRoot
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyCheckedSuffixValidityTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyRawSoundTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlySuffixValidityCNFTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyThreeCNF

/-!
Root packaging for the x-only Cook-Levin 3CNF surface.

The semantic Cook-Levin bridge is already checked for
`tmVerifierXOnlyEmittedThreeCNF`.  This file isolates the remaining root-level
obligation: a direct standard-TM `TMPolyTimeMap` for that generator.  The
checked suffix-validity package in `XOnlyCheckedSuffixValidityTM` records the
honest route to such a witness without treating the semantic invalid-prefix
filter as executable.
-/

namespace ComplexityReduction
namespace SAT

/--
Package the checked x-only 3CNF semantics as a direct verifier reduction once
the generator has a direct standard-TM polynomial-time witness.
-/
noncomputable def tmVerifierXOnlyEmittedThreeCNFReduction
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (hPoly :
      TMPolyTimeMap L.Instance threeSATDecisionProblem.Instance
        (tmVerifierXOnlyEmittedThreeCNF V)) :
    TMCookLevinVerifierReduction V where
  cookTableauThreeCNF := tmVerifierXOnlyEmittedThreeCNF V
  cookTableauThreeCNF_polytime := hPoly
  cookTableauThreeCNF_correct := by
    intro x
    exact (tmVerifierXOnlyEmittedThreeCNF_satisfiable_iff_isYes V x).symm

/--
The final root proof object follows from a uniform direct standard-TM witness
for the x-only 3CNF generator.
-/
noncomputable def tmCookLevinTheoremOfXOnlyGeneratorPolytime
    (hPoly :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) →
          TMPolyTimeMap L.Instance threeSATDecisionProblem.Instance
            (tmVerifierXOnlyEmittedThreeCNF V)) :
    TMCookLevinTheorem where
  reduceVerifier := fun V =>
    tmVerifierXOnlyEmittedThreeCNFReduction V (hPoly V)

end SAT
end ComplexityReduction
