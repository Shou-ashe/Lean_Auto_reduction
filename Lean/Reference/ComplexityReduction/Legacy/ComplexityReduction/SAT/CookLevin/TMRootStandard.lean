/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDiscipline
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATTMRoot

/-!
Standard-TM Cook-Levin root through checked suffix discipline.

The current low-level `TMVerifier` API does not itself provide a certificate
suffix decoder for arbitrary certificate encodings.  This module therefore
uses the theorem-bearing root surface that Phase 1 exposed: verifiers carry
`TMVerifierEncodingDiscipline`.  A separate adapter still shows how a future
uniform discipline theorem would recover the old arbitrary-verifier
`TMCookLevinTheorem` surface.
-/

namespace ComplexityReduction
namespace SAT

/--
Checked suffix discipline gives one direct standard-TM Cook-Levin verifier
reduction to bundled 3SAT.
-/
noncomputable def tmVerifierEncodingDisciplineReduction
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (D : TMVerifierEncodingDiscipline V) :
    TMCookLevinVerifierReduction V where
  cookTableauThreeCNF :=
    (checkedXOnlyCookLevinBundledTMKarpReduction D.toCheckedSuffixValidity).f
  cookTableauThreeCNF_polytime :=
    (checkedXOnlyCookLevinBundledTMKarpReduction D.toCheckedSuffixValidity).polytime
  cookTableauThreeCNF_correct :=
    (checkedXOnlyCookLevinBundledTMKarpReduction D.toCheckedSuffixValidity).correct

/--
Proof object for the disciplined standard-TM Cook-Levin theorem.

This is the completed theorem surface supported by the current APIs: every
verifier with checked certificate-suffix discipline reduces to bundled 3SAT by
a direct `TMPolyTimeMap`.
-/
structure DisciplinedTMCookLevinTheorem where
  reduceVerifier :
    {L : EncodedDecisionProblem} ->
      (V : TMVerifier L) ->
        TMVerifierEncodingDiscipline V -> TMCookLevinVerifierReduction V

namespace DisciplinedTMCookLevinTheorem

/-- A disciplined root reduces one explicit disciplined verifier to bundled 3SAT. -/
theorem reduction_of_TMVerifier
    (H : DisciplinedTMCookLevinTheorem)
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (D : TMVerifierEncodingDiscipline V) :
    TMPolyReducible L threeSATDecisionProblem :=
  ⟨(H.reduceVerifier V D).toTMKarpReduction⟩

end DisciplinedTMCookLevinTheorem

/-- The checked suffix discipline proves the disciplined standard-TM root. -/
noncomputable def disciplinedStandardTMCookLevinTheorem :
    DisciplinedTMCookLevinTheorem where
  reduceVerifier := fun V D => tmVerifierEncodingDisciplineReduction V D

/--
The completed standard-TM Cook-Levin theorem for the supported verifier surface.

The verifier argument is explicit and carries `TMVerifierEncodingDiscipline`,
which is the missing certificate-suffix image recognizer for arbitrary
certificate encodings.
-/
noncomputable def standardTMCookLevinTheorem :
    DisciplinedTMCookLevinTheorem :=
  disciplinedStandardTMCookLevinTheorem

/-- The standard disciplined root reduces one disciplined verifier to bundled 3SAT. -/
theorem standardTM_reduction_of_TMVerifier
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (D : TMVerifierEncodingDiscipline V) :
    TMPolyReducible L threeSATDecisionProblem :=
  standardTMCookLevinTheorem.reduction_of_TMVerifier V D

/--
A uniform encoding-discipline theorem upgrades the disciplined root to the
current arbitrary-`TMVerifier` `TMCookLevinTheorem` surface.
-/
noncomputable def standardTMCookLevinTheoremOfUniformEncodingDiscipline
    (hDiscipline : UniformTMVerifierEncodingDiscipline) :
    TMCookLevinTheorem where
  reduceVerifier := fun V =>
    tmVerifierEncodingDisciplineReduction V (Classical.choice (hDiscipline V))

/--
A direct-TM NP witness whose verifier carries the certificate-suffix discipline
needed by the standard Cook-Levin theorem.
-/
def TMInNPWithEncodingDiscipline (L : EncodedDecisionProblem) : Prop :=
  Nonempty (Σ V : TMVerifier L, TMVerifierEncodingDiscipline V)

namespace TMInNPWithEncodingDiscipline

/-- Forgetting the encoding discipline recovers ordinary direct-TM NP. -/
theorem toTMInNP {L : EncodedDecisionProblem}
    (h : TMInNPWithEncodingDiscipline L) : TMInNP L := by
  rcases h with ⟨⟨V, _D⟩⟩
  exact ⟨V⟩

end TMInNPWithEncodingDiscipline

/--
NP-completeness for the direct-TM NP class whose verifiers carry checked
certificate-suffix encoding discipline.
-/
def TMNPCompleteEncWithEncodingDiscipline (K : EncodedDecisionProblem) : Prop :=
  TMInNP K ∧ ∀ L, TMInNPWithEncodingDiscipline L -> TMPolyReducible L K

namespace TMNPCompleteEncWithEncodingDiscipline

theorem mem_np {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithEncodingDiscipline K) : TMInNP K :=
  h.1

theorem hard {K : EncodedDecisionProblem}
    (h : TMNPCompleteEncWithEncodingDiscipline K)
    (L : EncodedDecisionProblem) (hL : TMInNPWithEncodingDiscipline L) :
    TMPolyReducible L K :=
  h.2 L hL

/--
Lift discipline-aware direct-TM NP-completeness along a reduction from the
complete problem to the target problem.
-/
theorem transfer {A B : EncodedDecisionProblem}
    (hA : TMNPCompleteEncWithEncodingDiscipline A)
    (hAB : TMPolyReducible A B)
    (hB : TMInNP B) :
    TMNPCompleteEncWithEncodingDiscipline B := by
  constructor
  · exact hB
  · intro L hL
    exact TMPolyReducible.trans (hA.hard L hL) hAB

end TMNPCompleteEncWithEncodingDiscipline

/--
High-level API alias for transferring discipline-aware NP-completeness along a
direct-TM reduction.
-/
theorem liftNPCompleteAlongReductionWithEncodingDiscipline
    {K L : EncodedDecisionProblem}
    (hK : TMNPCompleteEncWithEncodingDiscipline K)
    (rKL : TMPolyReducible K L)
    (hL : TMInNP L) :
    TMNPCompleteEncWithEncodingDiscipline L :=
  TMNPCompleteEncWithEncodingDiscipline.transfer hK rKL hL

/--
Transfer discipline-aware NP-completeness across an explicitly supplied
two-way route.  The reverse direction is retained for callers passing an
equivalence package; hardness uses the complete-to-target direction.
-/
theorem transferTMNPCompleteWithEncodingDiscipline {A B : EncodedDecisionProblem}
    (rAB : TMPolyReducible A B)
    (_rBA : TMPolyReducible B A)
    (hA : TMNPCompleteEncWithEncodingDiscipline A)
    (hBmem : TMInNP B) :
    TMNPCompleteEncWithEncodingDiscipline B :=
  liftNPCompleteAlongReductionWithEncodingDiscipline hA rAB hBmem

/--
Bundled 3SAT is standard-TM NP-complete for the discipline-carrying verifier
surface.
-/
theorem threeSAT_TMNPComplete_with_encodingDiscipline :
    TMNPCompleteEncWithEncodingDiscipline threeSATDecisionProblem := by
  constructor
  · exact threeSAT_TMInNP
  · intro L hL
    rcases hL with ⟨⟨V, D⟩⟩
    exact standardTM_reduction_of_TMVerifier V D

#check tmVerifierEncodingDisciplineReduction
#check DisciplinedTMCookLevinTheorem
#check DisciplinedTMCookLevinTheorem.reduction_of_TMVerifier
#check disciplinedStandardTMCookLevinTheorem
#check standardTMCookLevinTheorem
#check standardTM_reduction_of_TMVerifier
#check standardTMCookLevinTheoremOfUniformEncodingDiscipline
#check TMInNPWithEncodingDiscipline
#check TMInNPWithEncodingDiscipline.toTMInNP
#check TMNPCompleteEncWithEncodingDiscipline
#check TMNPCompleteEncWithEncodingDiscipline.mem_np
#check TMNPCompleteEncWithEncodingDiscipline.hard
#check TMNPCompleteEncWithEncodingDiscipline.transfer
#check liftNPCompleteAlongReductionWithEncodingDiscipline
#check transferTMNPCompleteWithEncodingDiscipline
#check threeSAT_TMNPComplete_with_encodingDiscipline

end SAT
end ComplexityReduction
