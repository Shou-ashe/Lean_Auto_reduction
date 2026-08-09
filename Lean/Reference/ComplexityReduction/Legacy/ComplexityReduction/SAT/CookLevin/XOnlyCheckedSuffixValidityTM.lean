/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMRoot
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SATStrict
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlySuffixValidityCNFTM

/-!
Checked suffix-validity interface for the x-only Cook-Levin surface.

The semantic `tmVerifierXOnlySuffixValidityCNF` layer excludes invalid
certificate suffixes by filtering all bounded read-choice prefixes.  That layer
is useful for correctness, but it is not itself a direct polynomial generator.

This file states the exact replacement interface needed by the standard-TM
root: a suffix-validity CNF generator with a direct `TMPolyTimeMap` witness and
the two semantic bridge directions consumed by the x-only tableau proof.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Structured CNF to structural CNF for the splitter -/

theorem satClauseStructured_inputSize_ge_length (c : Clause) :
    c.length ≤ clauseStructuredEncodedType.inputSize c := by
  induction c with
  | nil =>
      simp [clauseStructuredEncodedType, EncodedType.inputSize, EncodedType.list]
  | cons l ls ih =>
      have ih' : ls.length ≤ (EncodedType.list literalStructuredEncodedType).inputSize ls := by
        simpa [clauseStructuredEncodedType] using ih
      change (l :: ls).length ≤
        (EncodedType.list literalStructuredEncodedType).inputSize (l :: ls)
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

theorem satClauseVarBound_le_clauseStructured_inputSize (c : Clause) :
    Clause.varBound c ≤ clauseStructuredEncodedType.inputSize c := by
  induction c with
  | nil =>
      simp [Clause.varBound, clauseStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons l ls ih =>
      have ih' :
          Clause.varBound ls ≤ (EncodedType.list literalStructuredEncodedType).inputSize ls := by
        simpa [clauseStructuredEncodedType] using ih
      have hl : l.var + 1 ≤ literalStructuredEncodedType.inputSize l := by
        cases l with
        | mk var neg =>
            change var + 1 ≤ literalTupleStructuredEncodedType.inputSize (var, neg)
            simp [literalTupleStructuredEncodedType]
      change
        max (l.var + 1) (Clause.varBound ls) ≤
          (EncodedType.list literalStructuredEncodedType).inputSize (l :: ls)
      rw [EncodedType.inputSize_list_cons]
      exact max_le (by omega) (by omega)

theorem satCNFStructured_inputSize_ge_totalClauseLength_add_length (φ : CNF) :
    CNF.totalClauseLength φ + φ.length ≤ cnfStructuredEncodedType.inputSize φ := by
  induction φ with
  | nil =>
      simp [CNF.totalClauseLength, cnfStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons c cs ih =>
      have ih' :
          CNF.totalClauseLength cs + cs.length ≤
            (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
        simpa [cnfStructuredEncodedType] using ih
      have hc := satClauseStructured_inputSize_ge_length c
      change
        CNF.totalClauseLength (c :: cs) + (c :: cs).length ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs)
      rw [EncodedType.inputSize_list_cons]
      simp [CNF.totalClauseLength]
      omega

theorem satCNFVarBound_le_cnfStructured_inputSize (φ : CNF) :
    CNF.varBound φ ≤ cnfStructuredEncodedType.inputSize φ := by
  induction φ with
  | nil =>
      simp [CNF.varBound, cnfStructuredEncodedType, EncodedType.inputSize,
        EncodedType.list]
  | cons c cs ih =>
      have ih' :
          CNF.varBound cs ≤ (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
        simpa [cnfStructuredEncodedType] using ih
      have hc := satClauseVarBound_le_clauseStructured_inputSize c
      change
        max (Clause.varBound c) (CNF.varBound cs) ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs)
      rw [EncodedType.inputSize_list_cons]
      exact max_le (by omega) (by omega)

theorem satCNFStructuralSize_le_structured_inputSize_poly_base (φ : CNF) :
    CNF.structuralSize φ ≤ 2 * cnfStructuredEncodedType.inputSize φ + 1 := by
  have hVar := satCNFVarBound_le_cnfStructured_inputSize φ
  have hTotal := satCNFStructured_inputSize_ge_totalClauseLength_add_length φ
  unfold CNF.structuralSize
  omega

theorem cnfStructuredToStructural_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : CNF => cnfStructuredEncodedType.inputSize φ)
      (fun ψ : CNF => cnfStructuralEncodedType.inputSize ψ)
      id := by
  refine PolynomialSizeBound.intro_with 1 2 1 ?_
  intro φ
  simpa [cnfStructuralEncodedType, EncodedType.inputSize] using
    satCNFStructuralSize_le_structured_inputSize_poly_base φ

/--
Strict primitive that re-encodes a faithful structured CNF as the structural
unary-size encoding consumed by the reviewed CNF splitter.
-/
noncomputable def cnfStructuredToStructuralStrictPrimitive :
    StrictStreamPrimitive cnfStructuredEncodedType cnfStructuralEncodedType id :=
  { name := "SAT.CNF.structuredToStructural"
    pass_bound := "One streaming pass over the structured CNF syntax."
    workspace_bound := "O(log |input|) counters for variable, literal, and clause totals."
    output_order := "Emit unary structural-size tokens after the single syntax scan."
    oracle_free := "The map only counts syntax; it never branches on satisfiability."
    costed := CostedPolyTimeMap.of_costed
      (CostedMap.of_encodedPolynomialSizeBound
        cnfStructuredToStructural_polynomialSizeBound) }

/-- Strict streaming certificate for structured-CNF to structural-CNF re-encoding. -/
noncomputable def cnfStructuredToStructuralStrictMap :
    StrictStreamMap (X := cnfStructuredEncodedType) (Y := cnfStructuralEncodedType) id :=
  StrictStreamMap.registeredPrimitive cnfStructuredToStructuralStrictPrimitive

/-- Machine-level strict certificate for structured-CNF to structural-CNF re-encoding. -/
noncomputable def cnfStructuredToStructuralMachineMap :
    StrictLogSpaceMachineMap (X := cnfStructuredEncodedType) (Y := cnfStructuralEncodedType) id :=
  cnfStructuredToStructuralStrictMap.toMachineMap

/--
The standard CNF splitter is direct-TM polynomial-time from faithful structured
CNF once the explicit strict-logspace-to-TM soundness boundary is supplied.
-/
theorem splitToThreeCNF_tm_polytime_of_strictSound
    (hSound : StrictLogSpaceTMSound) :
    TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
      CNF.splitToThreeCNF := by
  have hToStructural := cnfStructuredToStructuralMachineMap.to_TMPolyTimeMap hSound
  have hSplit := CNF.splitToThreeCNFMachineMap.to_TMPolyTimeMap hSound
  have hComp := TMPolyTimeMap.comp hSplit hToStructural
  simpa [Function.comp] using hComp

/--
A checked, direct-TM suffix-validity generator for one verifier.

The `validSuffixSeed_satisfies` field is completeness for the suffix layer; the
`decodedSuffix_valid_of_satisfies` field is soundness against a satisfying
global tableau assignment.
-/
structure TMVerifierXOnlyCheckedSuffixValidity
    {L : EncodedDecisionProblem} (V : TMVerifier L) where
  suffixValidityCNF : L.Instance.Carrier → CNF
  suffixValidityCNF_tm_polytime :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType suffixValidityCNF
  validSuffixSeed_satisfies :
    {B : TMVerifierPushPayloadBoundary V} →
      {x : L.Instance.Carrier} →
        {a : Assignment} →
          TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a →
            CNF.Satisfies (suffixValidityCNF x) a
  decodedSuffix_valid_of_satisfies :
    {B : TMVerifierPushPayloadBoundary V} →
      {x : L.Instance.Carrier} →
        {a : Assignment} →
          (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) →
            CNF.Satisfies (suffixValidityCNF x) a →
              TMVerifierCertificateWordSuffix V x E.decodedInitialCertificateSuffixWord

namespace TMVerifierXOnlyCheckedSuffixValidity

/--
The current semantic suffix-validity CNF becomes a checked package if an honest
direct generator witness is supplied separately.
-/
noncomputable def ofSemanticSuffixValidityCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (hPoly :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier => tmVerifierXOnlySuffixValidityCNF V x)) :
    TMVerifierXOnlyCheckedSuffixValidity V where
  suffixValidityCNF := tmVerifierXOnlySuffixValidityCNF V
  suffixValidityCNF_tm_polytime := hPoly
  validSuffixSeed_satisfies := by
    intro B x a w
    exact tmVerifierXOnlySuffixValidityCNF_satisfies_of_validSuffixSeed w
  decodedSuffix_valid_of_satisfies := by
    intro B x a E hSuffix
    exact E.decodedInitialCertificateSuffixWord_valid_of_suffixValidityCNF hSuffix

/-- The emitted x-only CNF assembled from the global tableau and a checked suffix layer. -/
noncomputable def emittedCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) : CNF :=
  tmVerifierXOnlyGlobalTableauCNF V B x ++ G.suffixValidityCNF x

theorem emittedCNF_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => G.emittedCNF B x) := by
  have hGlobal := tmVerifierXOnlyGlobalTableauCNF_tm_polytime V B
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyGlobalTableauCNF V B x, G.suffixValidityCNF x)) :=
    TMPolyTimeMap.prod_mk hGlobal G.suffixValidityCNF_tm_polytime
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, emittedCNF, cnfStructuredEncodedType] using hAppend

theorem emittedCNF_satisfies_of_validSuffixSeed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {G : TMVerifierXOnlyCheckedSuffixValidity V}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (w : TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) :
    CNF.Satisfies (G.emittedCNF B x) a := by
  rw [emittedCNF, CNF.satisfies_append]
  exact ⟨w.global_tableau, G.validSuffixSeed_satisfies w⟩

noncomputable def validSuffixSeed_of_emittedCNF_satisfies
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {G : TMVerifierXOnlyCheckedSuffixValidity V}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (h : CNF.Satisfies (G.emittedCNF B x) a) :
    TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a := by
  have hPair :
      CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V B x) a ∧
        CNF.Satisfies (G.suffixValidityCNF x) a := by
    exact (CNF.satisfies_append
      (tmVerifierXOnlyGlobalTableauCNF V B x) (G.suffixValidityCNF x) a).1
        (by simpa [emittedCNF] using h)
  let hGlobal := hPair.1
  let E := tmVerifierXOnlyGlobalTableauCNF_evidence V B x a hGlobal
  exact
    { global_tableau := hGlobal
      valid_suffix := G.decodedSuffix_valid_of_satisfies E hPair.2 }

theorem emittedCNF_satisfiable_iff_validSuffixSeed_satisfiable
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    CNF.Satisfiable (G.emittedCNF B x) ↔
      ∃ a, Nonempty (TMVerifierXOnlyGlobalTableauValidSuffixSeed V B x a) := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, ⟨validSuffixSeed_of_emittedCNF_satisfies h⟩⟩
  · rintro ⟨a, ⟨w⟩⟩
    exact ⟨a, emittedCNF_satisfies_of_validSuffixSeed w⟩

theorem emittedCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (x : L.Instance.Carrier) :
    CNF.Satisfiable (G.emittedCNF (tmVerifierActivePushPayloadBoundary V) x) ↔
      L.isYes x := by
  rw [G.emittedCNF_satisfiable_iff_validSuffixSeed_satisfiable,
    tmVerifierXOnlyGlobalTableauValidSuffixSeed_satisfiable_iff_isYes]

/-- The checked emitted CNF converted to bundled 3CNF. -/
noncomputable def emittedThreeCNF
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (x : L.Instance.Carrier) : ThreeCNF :=
  CNF.splitToThreeCNF (G.emittedCNF (tmVerifierActivePushPayloadBoundary V) x)

theorem emittedThreeCNF_satisfiable_iff_isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (x : L.Instance.Carrier) :
    ThreeCNF.Satisfiable (G.emittedThreeCNF x) ↔ L.isYes x := by
  rw [emittedThreeCNF, CNF.splitToThreeCNF_satisfiable_iff,
    G.emittedCNF_satisfiable_iff_isYes]

theorem emittedThreeCNF_tm_polytime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF) :
    TMPolyTimeMap L.Instance threeSATDecisionProblem.Instance
      (fun x : L.Instance.Carrier => G.emittedThreeCNF x) := by
  have hCNF := G.emittedCNF_tm_polytime (tmVerifierActivePushPayloadBoundary V)
  have hComp := TMPolyTimeMap.comp hSplit hCNF
  simpa [Function.comp, emittedThreeCNF] using hComp

/-- Package a checked suffix generator as one direct Cook-Levin verifier reduction. -/
noncomputable def toVerifierReduction
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (G : TMVerifierXOnlyCheckedSuffixValidity V)
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF) :
    TMCookLevinVerifierReduction V where
  cookTableauThreeCNF := G.emittedThreeCNF
  cookTableauThreeCNF_polytime := G.emittedThreeCNF_tm_polytime hSplit
  cookTableauThreeCNF_correct := by
    intro x
    exact (G.emittedThreeCNF_satisfiable_iff_isYes x).symm

/--
The x-only route yields the standard Cook-Levin theorem from a uniform checked
suffix generator and a direct TM witness for CNF splitting.
-/
noncomputable def toCookLevinTheorem
    (hSplit :
      TMPolyTimeMap cnfStructuredEncodedType threeSATDecisionProblem.Instance
        CNF.splitToThreeCNF)
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMCookLevinTheorem where
  reduceVerifier := fun V =>
    (hSuffix V).toVerifierReduction hSplit

/--
Strict-logspace soundness plus a uniform checked suffix generator gives the
standard Cook-Levin theorem through the checked x-only route.
-/
noncomputable def toCookLevinTheoremOfStrictSound
    (hSound : StrictLogSpaceTMSound)
    (hSuffix :
      {L : EncodedDecisionProblem} →
        (V : TMVerifier L) → TMVerifierXOnlyCheckedSuffixValidity V) :
    TMCookLevinTheorem :=
  toCookLevinTheorem (splitToThreeCNF_tm_polytime_of_strictSound hSound) hSuffix

end TMVerifierXOnlyCheckedSuffixValidity

end SAT
end ComplexityReduction
