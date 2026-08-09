/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetCovering
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking

/-!
Faithful structured Karp21 chains assembled only from direct TM-backed witnesses.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace VertexCover

/--
Faithful structured SAT-to-Vertex-Cover chain obtained by composing the checked
CNF-to-3SAT/Clique route with the checked Clique-to-Vertex-Cover route.
-/
noncomputable def satisfiabilityToVertexCoverStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem
      vertexCoverStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    cliqueToVertexCoverStructuredTMBackedKarpReduction
    Clique.satisfiabilityToCliqueStructuredTMBackedKarpReduction

noncomputable def satisfiabilityToVertexCoverStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem
      vertexCoverStructuredDecisionProblem :=
  satisfiabilityToVertexCoverStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def satisfiabilityToVertexCoverStructuredTMKarpReduction :
    TMKarpReduction
      satisfiabilityStructuredDecisionProblem
      vertexCoverStructuredDecisionProblem :=
  satisfiabilityToVertexCoverStructuredTMBackedKarpReduction.toTMKarpReduction

end VertexCover

namespace SetCovering

/-- Faithful structured Clique-to-Set-Covering chain through Vertex Cover. -/
noncomputable def cliqueToSetCoveringViaVertexCoverStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      cliqueStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    vertexCoverToSetCoveringStructuredTMBackedKarpReduction
    VertexCover.cliqueToVertexCoverStructuredTMBackedKarpReduction

noncomputable def cliqueToSetCoveringViaVertexCoverStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      cliqueStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  cliqueToSetCoveringViaVertexCoverStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def cliqueToSetCoveringViaVertexCoverStructuredTMKarpReduction :
    TMKarpReduction
      cliqueStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  cliqueToSetCoveringViaVertexCoverStructuredTMBackedKarpReduction.toTMKarpReduction

/-- Faithful structured SAT-to-Set-Covering chain through Clique and Vertex Cover. -/
noncomputable def satisfiabilityToSetCoveringStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    vertexCoverToSetCoveringStructuredTMBackedKarpReduction
    VertexCover.satisfiabilityToVertexCoverStructuredTMBackedKarpReduction

noncomputable def satisfiabilityToSetCoveringStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  satisfiabilityToSetCoveringStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def satisfiabilityToSetCoveringStructuredTMKarpReduction :
    TMKarpReduction
      satisfiabilityStructuredDecisionProblem
      setCoveringStructuredDecisionProblem :=
  satisfiabilityToSetCoveringStructuredTMBackedKarpReduction.toTMKarpReduction

end SetCovering

namespace HittingSet

/-- Faithful structured Clique-to-Hitting-Set chain through Vertex/Set Covering. -/
noncomputable def cliqueToHittingSetViaSetCoveringStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      cliqueStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    setCoveringToHittingSetStructuredTMBackedKarpReduction
    SetCovering.cliqueToSetCoveringViaVertexCoverStructuredTMBackedKarpReduction

noncomputable def cliqueToHittingSetViaSetCoveringStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      cliqueStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  cliqueToHittingSetViaSetCoveringStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def cliqueToHittingSetViaSetCoveringStructuredTMKarpReduction :
    TMKarpReduction
      cliqueStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  cliqueToHittingSetViaSetCoveringStructuredTMBackedKarpReduction.toTMKarpReduction

/-- Faithful structured SAT-to-Hitting-Set chain through Clique, Vertex Cover, and Set Covering. -/
noncomputable def satisfiabilityToHittingSetStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    setCoveringToHittingSetStructuredTMBackedKarpReduction
    SetCovering.satisfiabilityToSetCoveringStructuredTMBackedKarpReduction

noncomputable def satisfiabilityToHittingSetStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  satisfiabilityToHittingSetStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def satisfiabilityToHittingSetStructuredTMKarpReduction :
    TMKarpReduction
      satisfiabilityStructuredDecisionProblem
      hittingSetStructuredDecisionProblem :=
  satisfiabilityToHittingSetStructuredTMBackedKarpReduction.toTMKarpReduction

end HittingSet

namespace SetPacking

/-- Faithful structured SAT-to-Set-Packing chain through the direct Clique route. -/
noncomputable def satisfiabilityToSetPackingStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  TMBackedCostedReduction.comp
    cliqueToSetPackingStructuredTMBackedKarpReduction
    Clique.satisfiabilityToCliqueStructuredTMBackedKarpReduction

noncomputable def satisfiabilityToSetPackingStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      satisfiabilityStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  satisfiabilityToSetPackingStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def satisfiabilityToSetPackingStructuredTMKarpReduction :
    TMKarpReduction
      satisfiabilityStructuredDecisionProblem
      setPackingStructuredDecisionProblem :=
  satisfiabilityToSetPackingStructuredTMBackedKarpReduction.toTMKarpReduction

end SetPacking

end Karp21
end ComplexityReduction
