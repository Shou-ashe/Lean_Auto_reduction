import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part1

namespace ComplexityReduction
namespace Karp21
namespace Clique
open ComplexityReduction.Combinatorics.Graph

theorem occurrenceVarPair_tm_polytime :
    TMPolyTimeMap
      literalOccurrencePairStructuredEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      occurrenceVarPair := by
  have hLeftOcc :=
    TMPolyTimeMap.fst literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hRightOcc :=
    TMPolyTimeMap.snd literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hLeft :=
    TMPolyTimeMap.comp literalOccurrence_lit_var_tm_polytime hLeftOcc
  have hRight :=
    TMPolyTimeMap.comp literalOccurrence_lit_var_tm_polytime hRightOcc
  have hPair := TMPolyTimeMap.prod_mk hLeft hRight
  simpa [literalOccurrencePairStructuredEncodedType, occurrenceVarPair, Function.comp]
    using hPair

def occurrenceNegPair (p : LiteralOccurrence × LiteralOccurrence) : Bool × Bool :=
  (p.1.lit.neg, p.2.lit.neg)

theorem occurrenceNegPair_tm_polytime :
    TMPolyTimeMap
      literalOccurrencePairStructuredEncodedType
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      occurrenceNegPair := by
  have hLeftOcc :=
    TMPolyTimeMap.fst literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hRightOcc :=
    TMPolyTimeMap.snd literalOccurrenceStructuredEncodedType
      literalOccurrenceStructuredEncodedType
  have hLeft :=
    TMPolyTimeMap.comp literalOccurrence_lit_neg_tm_polytime hLeftOcc
  have hRight :=
    TMPolyTimeMap.comp literalOccurrence_lit_neg_tm_polytime hRightOcc
  have hPair := TMPolyTimeMap.prod_mk hLeft hRight
  simpa [literalOccurrencePairStructuredEncodedType, occurrenceNegPair, Function.comp]
    using hPair

def literalCompatibleBool (p : LiteralOccurrence × LiteralOccurrence) : Bool :=
  Bool.or (Bool.not (decide (p.1.lit.var = p.2.lit.var)))
    (decide (p.1.lit.neg = p.2.lit.neg))

def occurrenceCompatibleBool (p : LiteralOccurrence × LiteralOccurrence) : Bool :=
  Bool.and (Bool.not (decide (p.1.clause = p.2.clause))) (literalCompatibleBool p)

theorem literalCompatibleBool_eq_true_iff (p : LiteralOccurrence × LiteralOccurrence) :
    literalCompatibleBool p = true ↔ p.1.lit.var ≠ p.2.lit.var ∨
      p.1.lit.neg = p.2.lit.neg := by
  by_cases hVar : p.1.lit.var = p.2.lit.var <;>
    by_cases hNeg : p.1.lit.neg = p.2.lit.neg <;>
      simp [literalCompatibleBool, hVar, hNeg]

theorem occurrenceCompatibleBool_eq_true_iff (p : LiteralOccurrence × LiteralOccurrence) :
    occurrenceCompatibleBool p = true ↔ occurrenceCompatible p.1 p.2 := by
  by_cases hClause : p.1.clause = p.2.clause
  · simp [occurrenceCompatibleBool, occurrenceCompatible, hClause]
  · simp [occurrenceCompatibleBool, occurrenceCompatible, hClause,
      literalCompatibleBool_eq_true_iff p]

theorem occurrenceCompatibleBool_tm_polytime :
    TMPolyTimeMap
      literalOccurrencePairStructuredEncodedType
      EncodedType.bool
      occurrenceCompatibleBool := by
  have hClauseEq :=
    TMPolyTimeMap.comp TMPolyTimeMap.nat_eq occurrenceClausePair_tm_polytime
  have hClauseNe :=
    TMPolyTimeMap.comp TMPolyTimeMap.bool_not hClauseEq
  have hVarEq :=
    TMPolyTimeMap.comp TMPolyTimeMap.nat_eq occurrenceVarPair_tm_polytime
  have hVarNe :=
    TMPolyTimeMap.comp TMPolyTimeMap.bool_not hVarEq
  have hNegEq :=
    TMPolyTimeMap.comp boolEqPair_tm_polytime occurrenceNegPair_tm_polytime
  have hLitPair :=
    TMPolyTimeMap.prod_mk hVarNe hNegEq
  have hLitCompat :=
    TMPolyTimeMap.comp boolOrPair_tm_polytime hLitPair
  have hBoth :=
    TMPolyTimeMap.prod_mk hClauseNe hLitCompat
  have hCompat :=
    TMPolyTimeMap.comp boolAndPair_tm_polytime hBoth
  convert hCompat using 1
  ext p
  rcases p with ⟨a, b⟩
  by_cases hClause : a.clause = b.clause
  all_goals
    by_cases hVar : a.lit.var = b.lit.var
    all_goals
      have hNeg := boolEqPair_eq_decide (a.lit.neg, b.lit.neg)
      simp [Function.comp, occurrenceCompatibleBool, literalCompatibleBool,
        occurrenceClausePair, occurrenceVarPair, occurrenceNegPair, boolAndPair, boolOrPair,
        hClause, hVar, hNeg]

/-- Candidate edge together with the two literal occurrences it connects. -/
def cliqueEdgeCandidateEncodedType : EncodedType :=
  EncodedType.prod edgeStructuredEncodedType literalOccurrencePairStructuredEncodedType

def cliqueEdgeCandidateCompatible (c : cliqueEdgeCandidateEncodedType.Carrier) : Bool :=
  occurrenceCompatibleBool c.2

theorem cliqueEdgeCandidateCompatible_tm_polytime :
    TMPolyTimeMap
      cliqueEdgeCandidateEncodedType
      EncodedType.bool
      cliqueEdgeCandidateCompatible := by
  have hOccPair :=
    TMPolyTimeMap.snd edgeStructuredEncodedType literalOccurrencePairStructuredEncodedType
  have hComp := TMPolyTimeMap.comp occurrenceCompatibleBool_tm_polytime hOccPair
  simpa [cliqueEdgeCandidateEncodedType, cliqueEdgeCandidateCompatible, Function.comp] using hComp

/-- Input shape for one compatibility-filtering edge-list fold step. -/
def cliqueEdgeFilterStepInputEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list edgeStructuredEncodedType) cliqueEdgeCandidateEncodedType

def appendCompatibleEdgeStep
    (p : List edgeStructuredEncodedType.Carrier × cliqueEdgeCandidateEncodedType.Carrier) :
    List edgeStructuredEncodedType.Carrier :=
  match cliqueEdgeCandidateCompatible p.2 with
  | true => List.append (p.1 : List edgeStructuredEncodedType.Carrier) [p.2.1]
  | false => p.1

theorem appendCompatibleEdgeStep_tm_polytime :
    TMPolyTimeMap
      cliqueEdgeFilterStepInputEncodedType
      (EncodedType.list edgeStructuredEncodedType)
      appendCompatibleEdgeStep := by
  let X := cliqueEdgeFilterStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X (EncodedType.list edgeStructuredEncodedType)
        (fun p : X.Carrier => (p.1 : List edgeStructuredEncodedType.Carrier)) := by
    simpa [X, cliqueEdgeFilterStepInputEncodedType] using
      TMPolyTimeMap.fst (EncodedType.list edgeStructuredEncodedType) cliqueEdgeCandidateEncodedType
  have hCandidate :
      TMPolyTimeMap X cliqueEdgeCandidateEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueEdgeFilterStepInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType cliqueEdgeCandidateEncodedType
  have hEdge :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : X.Carrier => p.2.1) := by
    have hCandidateEdge :=
      TMPolyTimeMap.fst edgeStructuredEncodedType literalOccurrencePairStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hCandidateEdge hCandidate
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X (EncodedType.list edgeStructuredEncodedType)
        (fun p : X.Carrier => [p.2.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hEdge
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hAppendPair :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list edgeStructuredEncodedType)
          (EncodedType.list edgeStructuredEncodedType))
        (fun p : X.Carrier => ((p.1 : List edgeStructuredEncodedType.Carrier), [p.2.1])) :=
    TMPolyTimeMap.prod_mk hAcc hSingleton
  have hAppend :
      TMPolyTimeMap X (EncodedType.list edgeStructuredEncodedType)
        (fun p : X.Carrier =>
          List.append (p.1 : List edgeStructuredEncodedType.Carrier) [p.2.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendPair
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hCond :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => cliqueEdgeCandidateCompatible p.2) := by
    have hComp := TMPolyTimeMap.comp cliqueEdgeCandidateCompatible_tm_polytime hCandidate
    simpa [Function.comp, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (cliqueEdgeCandidateCompatible p.2, p)) :=
    TMPolyTimeMap.prod_mk hCond (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        (EncodedType.list edgeStructuredEncodedType)
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => List.append (p.2.1 : List edgeStructuredEncodedType.Carrier) [p.2.2.1]
          | false => (p.2.1 : List edgeStructuredEncodedType.Carrier)) :=
    boolProduct_dispatch_tm_polytime X (EncodedType.list edgeStructuredEncodedType)
      (fFalse := fun p : X.Carrier => (p.1 : List edgeStructuredEncodedType.Carrier))
      (fTrue := fun p : X.Carrier =>
        List.append (p.1 : List edgeStructuredEncodedType.Carrier) [p.2.1])
      (hFalse := hAcc) (hTrue := hAppend)
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1

/-- An occurrence paired with its graph vertex number. -/
def indexedLiteralOccurrenceEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat literalOccurrenceStructuredEncodedType

def indexedLiteralOccurrencesFrom
    (next : Nat) : List LiteralOccurrence → List indexedLiteralOccurrenceEncodedType.Carrier
  | [] => []
  | o :: os => (next, o) :: indexedLiteralOccurrencesFrom (next + 1) os

def indexedLiteralOccurrences (φ : SAT.ThreeCNF) :
    List indexedLiteralOccurrenceEncodedType.Carrier :=
  indexedLiteralOccurrencesFrom 0 (literalOccurrences φ)

def compatibleEdgesFromHead
    (head : indexedLiteralOccurrenceEncodedType.Carrier) :
    List indexedLiteralOccurrenceEncodedType.Carrier → List edgeStructuredEncodedType.Carrier
  | [] => []
  | current :: rest =>
      let tail := compatibleEdgesFromHead head rest
      if occurrenceCompatibleBool (head.2, current.2) then
        (head.1, current.1) :: tail
      else
        tail

def compatibleEdgesFromIndexedOccurrences :
    List indexedLiteralOccurrenceEncodedType.Carrier → List edgeStructuredEncodedType.Carrier
  | [] => []
  | head :: rest =>
      compatibleEdgesFromHead head rest ++ compatibleEdgesFromIndexedOccurrences rest

def occurrenceFoldEdgeList (φ : SAT.ThreeCNF) : List edgeStructuredEncodedType.Carrier :=
  compatibleEdgesFromIndexedOccurrences (indexedLiteralOccurrences φ)

/-- Accumulator used while connecting a fresh occurrence to previously seen occurrences. -/
def cliquePriorEdgeFoldAccEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list edgeStructuredEncodedType) indexedLiteralOccurrenceEncodedType

/-- Input shape for one "current occurrence against one prior occurrence" edge step. -/
def cliquePriorEdgeFoldStepInputEncodedType : EncodedType :=
  EncodedType.prod cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType

def cliquePriorEdgeCandidate
    (p : cliquePriorEdgeFoldStepInputEncodedType.Carrier) :
    cliqueEdgeCandidateEncodedType.Carrier :=
  let current := p.1.2
  let prior := p.2
  ((prior.1, current.1), (prior.2, current.2))

def appendPriorCompatibleEdgeStep
    (p : cliquePriorEdgeFoldStepInputEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.Carrier :=
  (appendCompatibleEdgeStep (p.1.1, cliquePriorEdgeCandidate p), p.1.2)

theorem cliquePriorEdgeCandidate_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeFoldStepInputEncodedType
      cliqueEdgeCandidateEncodedType
      cliquePriorEdgeCandidate := by
  let X := cliquePriorEdgeFoldStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliquePriorEdgeFoldStepInputEncodedType] using
      TMPolyTimeMap.fst cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType
  have hPrior :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliquePriorEdgeFoldStepInputEncodedType] using
      TMPolyTimeMap.snd cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType
  have hCurrent :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd (EncodedType.list edgeStructuredEncodedType)
        indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, cliquePriorEdgeFoldAccEncodedType] using hComp
  have hPriorVertex :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat literalOccurrenceStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPrior
    simpa [Function.comp, indexedLiteralOccurrenceEncodedType, X] using hComp
  have hCurrentVertex :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat literalOccurrenceStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCurrent
    simpa [Function.comp, indexedLiteralOccurrenceEncodedType, X] using hComp
  have hPriorOccurrence :
      TMPolyTimeMap X literalOccurrenceStructuredEncodedType
        (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat literalOccurrenceStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPrior
    simpa [Function.comp, indexedLiteralOccurrenceEncodedType, X] using hComp
  have hCurrentOccurrence :
      TMPolyTimeMap X literalOccurrenceStructuredEncodedType
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat literalOccurrenceStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCurrent
    simpa [Function.comp, indexedLiteralOccurrenceEncodedType, X] using hComp
  have hEdge :
      TMPolyTimeMap X edgeStructuredEncodedType
        (fun p : X.Carrier => (p.2.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hPriorVertex hCurrentVertex
  have hOccurrences :
      TMPolyTimeMap X literalOccurrencePairStructuredEncodedType
        (fun p : X.Carrier => (p.2.2, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hPriorOccurrence hCurrentOccurrence
  have hCandidate :
      TMPolyTimeMap X cliqueEdgeCandidateEncodedType
        (fun p : X.Carrier => ((p.2.1, p.1.2.1), (p.2.2, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hEdge hOccurrences
  simpa [X, cliquePriorEdgeCandidate, cliqueEdgeCandidateEncodedType] using hCandidate

theorem appendPriorCompatibleEdgeStep_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeFoldStepInputEncodedType
      cliquePriorEdgeFoldAccEncodedType
      appendPriorCompatibleEdgeStep := by
  let X := cliquePriorEdgeFoldStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliquePriorEdgeFoldStepInputEncodedType] using
      TMPolyTimeMap.fst cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType
  have hEdges :
      TMPolyTimeMap X (EncodedType.list edgeStructuredEncodedType)
        (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst (EncodedType.list edgeStructuredEncodedType)
        indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, cliquePriorEdgeFoldAccEncodedType, X] using hComp
  have hCurrent :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd (EncodedType.list edgeStructuredEncodedType)
        indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, cliquePriorEdgeFoldAccEncodedType, X] using hComp
  have hCandidate :
      TMPolyTimeMap X cliqueEdgeCandidateEncodedType
        cliquePriorEdgeCandidate :=
    cliquePriorEdgeCandidate_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X cliqueEdgeFilterStepInputEncodedType
        (fun p : X.Carrier => (p.1.1, cliquePriorEdgeCandidate p)) :=
    TMPolyTimeMap.prod_mk hEdges hCandidate
  have hNewEdges :
      TMPolyTimeMap X (EncodedType.list edgeStructuredEncodedType)
        (fun p : X.Carrier => appendCompatibleEdgeStep (p.1.1, cliquePriorEdgeCandidate p)) := by
    have hComp := TMPolyTimeMap.comp appendCompatibleEdgeStep_tm_polytime hAppendInput
    simpa [Function.comp, cliqueEdgeFilterStepInputEncodedType, X] using hComp
  have hPair :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier =>
          (appendCompatibleEdgeStep (p.1.1, cliquePriorEdgeCandidate p), p.1.2)) :=
    TMPolyTimeMap.prod_mk hNewEdges hCurrent
  simpa [appendPriorCompatibleEdgeStep, X, cliquePriorEdgeFoldAccEncodedType] using hPair

def defaultIndexedLiteralOccurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
  ((0 : Nat), defaultOccurrence)

def cliquePriorEdgeFoldInit : cliquePriorEdgeFoldAccEncodedType.Carrier :=
  (([] : List edgeStructuredEncodedType.Carrier), defaultIndexedLiteralOccurrence)

/--
Common instruction payload for the dynamic-init prior-occurrence edge runner.
For an init instruction, the left component is the loaded accumulator; for a
prior instruction, the right component is the historical indexed occurrence.
-/
def cliquePriorEdgeRunnerInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType

def cliquePriorEdgeRunnerInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool cliquePriorEdgeRunnerInstructionPayloadEncodedType

def cliquePriorEdgeRunnerStepInputEncodedType : EncodedType :=
  EncodedType.prod cliquePriorEdgeFoldAccEncodedType cliquePriorEdgeRunnerInstructionEncodedType

def cliquePriorEdgeRunnerInitInstruction
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    cliquePriorEdgeRunnerInstructionEncodedType.Carrier :=
  (false, (init, defaultIndexedLiteralOccurrence))

def cliquePriorEdgeRunnerPriorInstruction
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeRunnerInstructionEncodedType.Carrier :=
  (true, (cliquePriorEdgeFoldInit, prior))

def cliquePriorEdgeRunnerInstructions
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    List cliquePriorEdgeRunnerInstructionEncodedType.Carrier :=
  [cliquePriorEdgeRunnerInitInstruction init] ++
    prior.map cliquePriorEdgeRunnerPriorInstruction

def cliquePriorEdgeRunnerStep
    (p : cliquePriorEdgeRunnerStepInputEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.Carrier :=
  match p.2.1 with
  | true => appendPriorCompatibleEdgeStep (p.1, p.2.2.2)
  | false => p.2.2.1

theorem cliquePriorEdgeRunnerInitInstruction_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeFoldAccEncodedType
      cliquePriorEdgeRunnerInstructionEncodedType
      cliquePriorEdgeRunnerInitInstruction := by
  have hPayload :
      TMPolyTimeMap
        cliquePriorEdgeFoldAccEncodedType
        cliquePriorEdgeRunnerInstructionPayloadEncodedType
        (fun init : cliquePriorEdgeFoldAccEncodedType.Carrier =>
          (init, defaultIndexedLiteralOccurrence)) :=
    TMPolyTimeMap.prod_id_const cliquePriorEdgeFoldAccEncodedType
      indexedLiteralOccurrenceEncodedType defaultIndexedLiteralOccurrence
  have hTag :
      TMPolyTimeMap
        cliquePriorEdgeFoldAccEncodedType
        EncodedType.bool
        (fun _ : cliquePriorEdgeFoldAccEncodedType.Carrier => false) :=
    TMPolyTimeMap.const cliquePriorEdgeFoldAccEncodedType EncodedType.bool false
  have hInstr :
      TMPolyTimeMap
        cliquePriorEdgeFoldAccEncodedType
        cliquePriorEdgeRunnerInstructionEncodedType
        (fun init : cliquePriorEdgeFoldAccEncodedType.Carrier =>
          (false, (init, defaultIndexedLiteralOccurrence))) :=
    TMPolyTimeMap.prod_mk hTag hPayload
  simpa [cliquePriorEdgeRunnerInitInstruction,
    cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType] using hInstr

theorem cliquePriorEdgeRunnerPriorInstruction_tm_polytime :
    TMPolyTimeMap
      indexedLiteralOccurrenceEncodedType
      cliquePriorEdgeRunnerInstructionEncodedType
      cliquePriorEdgeRunnerPriorInstruction := by
  have hPayload :
      TMPolyTimeMap
        indexedLiteralOccurrenceEncodedType
        cliquePriorEdgeRunnerInstructionPayloadEncodedType
        (fun prior : indexedLiteralOccurrenceEncodedType.Carrier =>
          (cliquePriorEdgeFoldInit, prior)) :=
    TMPolyTimeMap.prod_left_const_id indexedLiteralOccurrenceEncodedType
      cliquePriorEdgeFoldAccEncodedType cliquePriorEdgeFoldInit
  have hTag :
      TMPolyTimeMap
        indexedLiteralOccurrenceEncodedType
        EncodedType.bool
        (fun _ : indexedLiteralOccurrenceEncodedType.Carrier => true) :=
    TMPolyTimeMap.const indexedLiteralOccurrenceEncodedType EncodedType.bool true
  have hInstr :
      TMPolyTimeMap
        indexedLiteralOccurrenceEncodedType
        cliquePriorEdgeRunnerInstructionEncodedType
        (fun prior : indexedLiteralOccurrenceEncodedType.Carrier =>
          (true, (cliquePriorEdgeFoldInit, prior))) :=
    TMPolyTimeMap.prod_mk hTag hPayload
  simpa [cliquePriorEdgeRunnerPriorInstruction,
    cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType] using hInstr

def cliquePriorEdgeRunnerInputEncodedType : EncodedType :=
  EncodedType.prod cliquePriorEdgeFoldAccEncodedType
    (EncodedType.list indexedLiteralOccurrenceEncodedType)

theorem cliquePriorEdgeRunnerInstructions_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerInputEncodedType
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType)
      (fun p : cliquePriorEdgeRunnerInputEncodedType.Carrier =>
        cliquePriorEdgeRunnerInstructions p.1 p.2) := by
  let X := cliquePriorEdgeRunnerInputEncodedType
  let Instr := cliquePriorEdgeRunnerInstructionEncodedType
  have hInit :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliquePriorEdgeRunnerInputEncodedType] using
      TMPolyTimeMap.fst cliquePriorEdgeFoldAccEncodedType
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
  have hPrior :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliquePriorEdgeRunnerInputEncodedType] using
      TMPolyTimeMap.snd cliquePriorEdgeFoldAccEncodedType
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
  have hInitInstr :
      TMPolyTimeMap X Instr
        (fun p : X.Carrier => cliquePriorEdgeRunnerInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp cliquePriorEdgeRunnerInitInstruction_tm_polytime hInit
    simpa [Function.comp, Instr, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier => [cliquePriorEdgeRunnerInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Instr) hInitInstr
    simpa [Function.comp, Instr, X] using hComp
  have hPriorInstrs :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier => p.2.map cliquePriorEdgeRunnerPriorInstruction) := by
    have hMap :=
      TMPolyTimeMap.list_map cliquePriorEdgeRunnerPriorInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hPrior
    simpa [Function.comp, Instr, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list Instr) (EncodedType.list Instr))
        (fun p : X.Carrier =>
          ([cliquePriorEdgeRunnerInitInstruction p.1],
            p.2.map cliquePriorEdgeRunnerPriorInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hPriorInstrs
  have hAppend :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier =>
          [cliquePriorEdgeRunnerInitInstruction p.1] ++
            p.2.map cliquePriorEdgeRunnerPriorInstruction) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Instr) hPair
    simpa [Function.comp, Instr, X] using hComp
  simpa [cliquePriorEdgeRunnerInstructions, X, Instr] using hAppend

theorem cliquePriorEdgeRunnerStep_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerStepInputEncodedType
      cliquePriorEdgeFoldAccEncodedType
      cliquePriorEdgeRunnerStep := by
  let X := cliquePriorEdgeRunnerStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliquePriorEdgeRunnerStepInputEncodedType] using
      TMPolyTimeMap.fst cliquePriorEdgeFoldAccEncodedType
        cliquePriorEdgeRunnerInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X cliquePriorEdgeRunnerInstructionEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliquePriorEdgeRunnerStepInputEncodedType] using
      TMPolyTimeMap.snd cliquePriorEdgeFoldAccEncodedType
        cliquePriorEdgeRunnerInstructionEncodedType
  have hTag :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => p.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.bool
        cliquePriorEdgeRunnerInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, cliquePriorEdgeRunnerInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X cliquePriorEdgeRunnerInstructionPayloadEncodedType
        (fun p : X.Carrier => p.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.bool
        cliquePriorEdgeRunnerInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, cliquePriorEdgeRunnerInstructionEncodedType, X] using hComp
  have hInitAcc :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => p.2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, cliquePriorEdgeRunnerInstructionPayloadEncodedType, X] using hComp
  have hPrior :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd cliquePriorEdgeFoldAccEncodedType indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, cliquePriorEdgeRunnerInstructionPayloadEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X cliquePriorEdgeFoldStepInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPrior
  have hAppend :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => appendPriorCompatibleEdgeStep (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp appendPriorCompatibleEdgeStep_tm_polytime hAppendInput
    simpa [Function.comp, cliquePriorEdgeFoldStepInputEncodedType, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        cliquePriorEdgeFoldAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => appendPriorCompatibleEdgeStep (p.2.1, p.2.2.2.2)
          | false => p.2.2.2.1) :=
    boolProduct_dispatch_tm_polytime X cliquePriorEdgeFoldAccEncodedType
      (fFalse := fun p : X.Carrier => p.2.2.1)
      (fTrue := fun p : X.Carrier => appendPriorCompatibleEdgeStep (p.1, p.2.2.2))
      (hFalse := hInitAcc) (hTrue := hAppend)
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1

def cliquePriorEdgeRunnerFold
    (p : cliquePriorEdgeRunnerInputEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.Carrier :=
  (cliquePriorEdgeRunnerInstructions p.1 p.2).foldl
    (fun acc instr => cliquePriorEdgeRunnerStep (acc, instr))
    cliquePriorEdgeFoldInit

@[simp] theorem cliquePriorEdgeRunnerStep_init
    (acc init : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    cliquePriorEdgeRunnerStep (acc, cliquePriorEdgeRunnerInitInstruction init) = init := by
  rfl

@[simp] theorem cliquePriorEdgeRunnerStep_prior
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeRunnerStep (acc, cliquePriorEdgeRunnerPriorInstruction prior) =
      appendPriorCompatibleEdgeStep (acc, prior) := by
  rfl

theorem cliquePriorEdgeRunnerPriorInstructions_fold_eq
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (prior.map cliquePriorEdgeRunnerPriorInstruction).foldl
        (fun acc instr => cliquePriorEdgeRunnerStep (acc, instr))
        acc =
      prior.foldl
        (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ))
        acc := by
  induction prior generalizing acc with
  | nil =>
      rfl
  | cons occ rest ih =>
      simp [ih]

theorem cliquePriorEdgeRunnerInstructions_fold_eq
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (cliquePriorEdgeRunnerInstructions init prior).foldl
        (fun acc instr => cliquePriorEdgeRunnerStep (acc, instr))
        cliquePriorEdgeFoldInit =
      prior.foldl
        (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ))
        init := by
  simp [cliquePriorEdgeRunnerInstructions,
    cliquePriorEdgeRunnerPriorInstructions_fold_eq]

theorem cliquePriorEdgeRunnerFold_eq
    (p : cliquePriorEdgeRunnerInputEncodedType.Carrier) :
    cliquePriorEdgeRunnerFold p =
      p.2.foldl
        (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ))
        p.1 := by
  simpa [cliquePriorEdgeRunnerFold] using
    cliquePriorEdgeRunnerInstructions_fold_eq p.1 p.2

def cliquePriorEdgeRunnerInstructionsImageEncodedType : EncodedType where
  Carrier := cliquePriorEdgeRunnerInputEncodedType.Carrier
  Symbol := (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).Symbol
  finite_symbol := inferInstance
  encode := fun p =>
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).encode
      (cliquePriorEdgeRunnerInstructions p.1 p.2)

theorem encodedList_length_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [EncodedType.inputSize_list_cons]
      simp
      omega

theorem encodedList_inputSize_append (X : EncodedType) (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, ih]
      omega

theorem appendCompatibleEdgeStep_inputSize_le
    (p : cliqueEdgeFilterStepInputEncodedType.Carrier) :
    (EncodedType.list edgeStructuredEncodedType).inputSize (appendCompatibleEdgeStep p) ≤
      (EncodedType.list edgeStructuredEncodedType).inputSize p.1 +
        edgeStructuredEncodedType.inputSize p.2.1 + 1 := by
  cases h : cliqueEdgeCandidateCompatible p.2 <;>
    simp [appendCompatibleEdgeStep, h, encodedList_inputSize_append] <;>
    omega

theorem cliquePriorEdgeCandidate_edge_inputSize_le
    (p : cliquePriorEdgeFoldStepInputEncodedType.Carrier) :
    edgeStructuredEncodedType.inputSize (cliquePriorEdgeCandidate p).1 ≤
      indexedLiteralOccurrenceEncodedType.inputSize p.1.2 +
        indexedLiteralOccurrenceEncodedType.inputSize p.2 := by
  rcases p with ⟨acc, prior⟩
  rcases acc with ⟨edges, current⟩
  rcases current with ⟨currentVertex, currentOcc⟩
  rcases prior with ⟨priorVertex, priorOcc⟩
  simp [cliquePriorEdgeCandidate, indexedLiteralOccurrenceEncodedType, edgeStructuredEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem appendPriorCompatibleEdgeStep_inputSize_growth
    (p : cliquePriorEdgeFoldStepInputEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize (appendPriorCompatibleEdgeStep p) ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize p.1 +
        indexedLiteralOccurrenceEncodedType.inputSize p.1.2 +
        indexedLiteralOccurrenceEncodedType.inputSize p.2 + 4 := by
  rcases p with ⟨acc, prior⟩
  rcases acc with ⟨edges, current⟩
  let candidate := cliquePriorEdgeCandidate ((edges, current), prior)
  let edgeSize := edgeStructuredEncodedType.inputSize candidate.1
  have hEdges :
      (EncodedType.list edgeStructuredEncodedType).inputSize
          (appendCompatibleEdgeStep (edges, candidate)) ≤
        (EncodedType.list edgeStructuredEncodedType).inputSize edges + edgeSize + 1 := by
    simpa [candidate, edgeSize] using
      appendCompatibleEdgeStep_inputSize_le
        ((edges, candidate) : cliqueEdgeFilterStepInputEncodedType.Carrier)
  have hEdge :
      edgeSize ≤ indexedLiteralOccurrenceEncodedType.inputSize current +
        indexedLiteralOccurrenceEncodedType.inputSize prior := by
    simpa [candidate, edgeSize] using
      cliquePriorEdgeCandidate_edge_inputSize_le
        (((edges, current), prior) : cliquePriorEdgeFoldStepInputEncodedType.Carrier)
  simp [appendPriorCompatibleEdgeStep, cliquePriorEdgeFoldAccEncodedType,
    EncodedType.inputSize_prod, candidate] at hEdges ⊢
  omega

theorem cliquePriorEdgeRunnerStep_priorInstruction_inputSize_growth
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier)
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeFoldAccEncodedType.inputSize
        (cliquePriorEdgeRunnerStep (acc, cliquePriorEdgeRunnerPriorInstruction prior)) ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize acc +
        indexedLiteralOccurrenceEncodedType.inputSize acc.2 +
        indexedLiteralOccurrenceEncodedType.inputSize prior + 4 := by
  simpa [cliquePriorEdgeRunnerStep, cliquePriorEdgeRunnerPriorInstruction] using
    appendPriorCompatibleEdgeStep_inputSize_growth
      ((acc, prior) : cliquePriorEdgeFoldStepInputEncodedType.Carrier)

theorem cliquePriorEdgeRunnerInitInstruction_inputSize_le
    (init : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    cliquePriorEdgeRunnerInstructionEncodedType.inputSize
        (cliquePriorEdgeRunnerInitInstruction init) ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize init +
        indexedLiteralOccurrenceEncodedType.inputSize defaultIndexedLiteralOccurrence + 4 := by
  simp [cliquePriorEdgeRunnerInitInstruction, cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliquePriorEdgeRunnerPriorInstruction_inputSize_le
    (prior : indexedLiteralOccurrenceEncodedType.Carrier) :
    cliquePriorEdgeRunnerInstructionEncodedType.inputSize
        (cliquePriorEdgeRunnerPriorInstruction prior) ≤
      indexedLiteralOccurrenceEncodedType.inputSize prior +
        cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit + 4 := by
  simp [cliquePriorEdgeRunnerPriorInstruction, cliquePriorEdgeRunnerInstructionEncodedType,
    cliquePriorEdgeRunnerInstructionPayloadEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliquePriorEdgeRunnerPriorInstructions_inputSize_le
    (prior : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (prior.map cliquePriorEdgeRunnerPriorInstruction) ≤
      (cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit + 5) *
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior := by
  induction prior with
  | nil =>
      simp
  | cons prior rest ih =>
      rw [List.map_cons, EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have hPrior := cliquePriorEdgeRunnerPriorInstruction_inputSize_le prior
      nlinarith

theorem cliquePriorEdgeRunnerInstructionsImage_linearSizeBound :
    LinearSizeBound
      (fun p : cliquePriorEdgeRunnerInputEncodedType.Carrier =>
        cliquePriorEdgeRunnerInputEncodedType.inputSize p)
      (fun p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier =>
        cliquePriorEdgeRunnerInstructionsImageEncodedType.inputSize p)
      id := by
  let K :=
    cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit +
      indexedLiteralOccurrenceEncodedType.inputSize defaultIndexedLiteralOccurrence + 10
  refine LinearSizeBound.intro_with K K ?_
  intro p
  rcases p with ⟨init, prior⟩
  have hInit := cliquePriorEdgeRunnerInitInstruction_inputSize_le init
  have hPrior := cliquePriorEdgeRunnerPriorInstructions_inputSize_le prior
  have hK_prior :
      cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit + 5 ≤ K := by
    dsimp [K]
    omega
  have hK_default :
      indexedLiteralOccurrenceEncodedType.inputSize defaultIndexedLiteralOccurrence + 5 ≤ K := by
    dsimp [K]
    omega
  have hK_pos : 1 ≤ K := by
    dsimp [K]
    omega
  have hInitSize :
      cliquePriorEdgeFoldAccEncodedType.inputSize init ≤
        K * cliquePriorEdgeFoldAccEncodedType.inputSize init := by
    simpa using Nat.mul_le_mul_right (cliquePriorEdgeFoldAccEncodedType.inputSize init) hK_pos
  have hPriorSize :
      (cliquePriorEdgeFoldAccEncodedType.inputSize cliquePriorEdgeFoldInit + 5) *
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior ≤
        K * (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior := by
    exact Nat.mul_le_mul_right _ hK_prior
  change
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).inputSize
        (cliquePriorEdgeRunnerInstructions init prior) ≤
      K *
          (cliquePriorEdgeRunnerInputEncodedType.inputSize
            ((init, prior) : cliquePriorEdgeRunnerInputEncodedType.Carrier)) + K
  simp [cliquePriorEdgeRunnerInstructions, cliquePriorEdgeRunnerInputEncodedType,
    EncodedType.inputSize_prod]
  nlinarith

theorem cliquePriorEdgeRunnerInstructionsImage_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerInputEncodedType
      cliquePriorEdgeRunnerInstructionsImageEncodedType
      id := by
  rcases cliquePriorEdgeRunnerInstructions_tm_polytime with ⟨hInstr⟩
  refine ⟨?_⟩
  exact
    { tm := hInstr.tm
      inputAlphabet := hInstr.inputAlphabet
      outputAlphabet := hInstr.outputAlphabet
      time := hInstr.time
      outputsFun := by
        intro p
        simpa [cliquePriorEdgeRunnerInstructionsImageEncodedType] using hInstr.outputsFun p }

theorem cliquePriorEdgeRunnerInstructionsFromImage_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerInstructionsImageEncodedType
      (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType)
      (fun p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier =>
        cliquePriorEdgeRunnerInstructions p.1 p.2) :=
  TMPolyTimeMap.of_encodingEquiv
    cliquePriorEdgeRunnerInstructionsImageEncodedType
    (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType)
    (fun p : cliquePriorEdgeRunnerInstructionsImageEncodedType.Carrier =>
      cliquePriorEdgeRunnerInstructions p.1 p.2)
    (Equiv.refl _)
    (by
      intro p
      change
        (EncodedType.list cliquePriorEdgeRunnerInstructionEncodedType).encode
            (cliquePriorEdgeRunnerInstructions p.1 p.2) =
          (cliquePriorEdgeRunnerInstructionsImageEncodedType.encode p).map id
      simp [cliquePriorEdgeRunnerInstructionsImageEncodedType])

noncomputable def cliquePriorEdgeRunnerInstructionsImageTMBackedMap :
    TMBackedCostedMap
      cliquePriorEdgeRunnerInputEncodedType
      cliquePriorEdgeRunnerInstructionsImageEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      cliquePriorEdgeRunnerInstructionsImage_linearSizeBound
  tm_polytime := cliquePriorEdgeRunnerInstructionsImage_tm_polytime

theorem mem_clauseOccurrencesFrom_clause_and_lit {j start : Nat} {c : SAT.Clause}
    {o : LiteralOccurrence} (h : o ∈ clauseOccurrencesFrom j start c) :
    o.clause = j ∧ o.lit ∈ c := by
  induction c generalizing start with
  | nil => simp [clauseOccurrencesFrom] at h
  | cons l ls ih =>
      simp [clauseOccurrencesFrom] at h
      rcases h with h | h
      · subst o
        simp
      · exact ⟨(ih h).1, by simp [(ih h).2]⟩

theorem exists_clauseOccurrenceFrom_of_lit_mem {j start : Nat} {c : SAT.Clause}
    {l : SAT.Literal} (hl : l ∈ c) :
    ∃ o ∈ clauseOccurrencesFrom j start c, o.clause = j ∧ o.lit = l := by
  induction c generalizing start with
  | nil => simp at hl
  | cons head tail ih =>
      simp at hl
      rcases hl with rfl | hl
      · refine ⟨{ clause := j, slot := start, lit := l }, ?_, rfl, rfl⟩
        simp [clauseOccurrencesFrom]
      · rcases ih (start := start + 1) hl with ⟨o, ho, hClause, hLit⟩
        exact ⟨o, by simp [clauseOccurrencesFrom, ho], hClause, hLit⟩

theorem exists_occurrence_of_getElem {cs : SAT.CNF} {idx : Nat} (hidx : idx < cs.length)
    {l : SAT.Literal} (hl : l ∈ cs[idx]) (start : Nat) :
    ∃ o ∈ formulaOccurrencesFrom start cs, o.clause = start + idx ∧ o.lit = l := by
  induction cs generalizing start idx with
  | nil => simp at hidx
  | cons c cs ih =>
      cases idx with
      | zero =>
          have hlHead : l ∈ c := by simpa using hl
          rcases exists_clauseOccurrenceFrom_of_lit_mem (j := start) (start := 0) hlHead with
            ⟨o, ho, hClause, hLit⟩
          refine ⟨o, ?_, by simpa using hClause, hLit⟩
          simp [formulaOccurrencesFrom, clauseOccurrences, ho]
      | succ idx =>
          have hidxTail : idx < cs.length := by simpa using hidx
          have hlTail : l ∈ cs[idx] := by simpa using hl
          rcases ih (start := start + 1) hidxTail hlTail with ⟨o, ho, hClause, hLit⟩
          refine ⟨o, ?_, ?_, hLit⟩
          · simp [formulaOccurrencesFrom, ho]
          · omega

theorem mem_formulaOccurrencesFrom_clause_ge {cs : SAT.CNF} {start : Nat}
    {o : LiteralOccurrence} (h : o ∈ formulaOccurrencesFrom start cs) :
    start ≤ o.clause := by
  induction cs generalizing start with
  | nil => simp [formulaOccurrencesFrom] at h
  | cons c cs ih =>
      simp [formulaOccurrencesFrom] at h
      rcases h with h | h
      · have hClause := (mem_clauseOccurrencesFrom_clause_and_lit h).1
        omega
      · have hGe := ih h
        omega

theorem mem_formulaOccurrencesFrom_clause_lt {cs : SAT.CNF} {start : Nat}
    {o : LiteralOccurrence} (h : o ∈ formulaOccurrencesFrom start cs) :
    o.clause < start + cs.length := by
  induction cs generalizing start with
  | nil => simp [formulaOccurrencesFrom] at h
  | cons c cs ih =>
      simp [formulaOccurrencesFrom] at h
      rcases h with h | h
      · have hClause := (mem_clauseOccurrencesFrom_clause_and_lit h).1
        simp [hClause]
      · have hLt := ih h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLt

theorem lit_mem_getElem_of_mem_formulaOccurrencesFrom {cs : SAT.CNF} {start idx : Nat}
    {o : LiteralOccurrence} (h : o ∈ formulaOccurrencesFrom start cs)
    (hClause : o.clause = start + idx) (hidx : idx < cs.length) :
    o.lit ∈ cs[idx] := by
  induction cs generalizing start idx with
  | nil => simp at hidx
  | cons c cs ih =>
      simp [formulaOccurrencesFrom] at h
      rcases h with h | h
      · have hInfo := mem_clauseOccurrencesFrom_clause_and_lit h
        cases idx with
        | zero =>
            simpa using hInfo.2
        | succ idx =>
            omega
      · cases idx with
        | zero =>
            have hGe := mem_formulaOccurrencesFrom_clause_ge h
            omega
        | succ idx =>
            have hidxTail : idx < cs.length := by simpa using hidx
            have hClauseTail : o.clause = start + 1 + idx := by omega
            simpa using ih h hClauseTail hidxTail

end Clique
end Karp21
end ComplexityReduction
