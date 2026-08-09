import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerStepChoice.Part1

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

noncomputable def splitWithTraceRunnerStepChoiceTMBackedMap :
    TMBackedCostedMap
      (EncodedType.prod
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerInstructionEncodedType)
      splitWithTraceRunnerStepChoiceEncodedType
      splitWithTraceRunnerStepChoice where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.prod
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerInstructionEncodedType)
      (Y := splitWithTraceRunnerStepChoiceEncodedType)
      (LinearSizeBound.of_le (by
        intro p
        exact splitWithTraceRunnerStepChoice_inputSize_le p))
  tm_polytime :=
    ⟨{ tm := splitWithTraceRunnerStepChoiceMachine
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 8
       outputsFun := by
        intro p
        rcases p with ⟨acc, instr⟩
        cases instr with
        | inl input =>
            change Turing.TM2OutputsInTime
              splitWithTraceRunnerStepChoiceMachine
              (List.map id
                ((EncodedType.prod
                  splitWithTraceLoopAccEncodedType
                  splitWithTraceRunnerInstructionEncodedType).encode (acc, Sum.inl input)))
              (some (List.map id
                (splitWithTraceRunnerStepChoiceEncodedType.encode
                  (splitWithTraceRunnerStepChoice (acc, Sum.inl input)))))
              ((4 * Polynomial.X + 8).eval
                ((EncodedType.prod
                  splitWithTraceLoopAccEncodedType
                  splitWithTraceRunnerInstructionEncodedType).encode
                    (acc, Sum.inl input)).length)
            have hOut :=
              splitWithTraceRunnerStepChoice_outputs_left
                (splitWithTraceLoopAccEncodedType.encode acc)
                (splitWithInputEncodedType.encode input)
            exact
              TM2Programs.evalsToInTime_mono
                (by
                  simpa [List.map_id, splitWithTraceRunnerStepChoiceLeftInputStack,
                    splitWithTraceRunnerStepChoiceAccInputSymbol,
                    splitWithTraceRunnerStepChoiceInstructionTagInputSymbol,
                    splitWithTraceRunnerStepChoiceInputPayloadInputSymbol,
                    splitWithTraceRunnerStepChoiceInputPayloadSymbol,
                    splitWithTraceRunnerStepChoiceEncodedType,
                    splitWithTraceRunnerStepChoice,
                    splitWithTraceRunnerInstructionEncodedType,
                    splitWithTraceRunnerFuelEncodedType,
                    EncodedType.prod, EncodedType.sum] using hOut)
                (by
                  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
                    splitWithTraceRunnerInstructionEncodedType,
                    splitWithTraceRunnerFuelEncodedType,
                    EncodedType.prod, EncodedType.sum])
        | inr fuel =>
            cases fuel
            change Turing.TM2OutputsInTime
              splitWithTraceRunnerStepChoiceMachine
              (List.map id
                ((EncodedType.prod
                  splitWithTraceLoopAccEncodedType
                  splitWithTraceRunnerInstructionEncodedType).encode (acc, Sum.inr ())))
              (some (List.map id
                (splitWithTraceRunnerStepChoiceEncodedType.encode
                  (splitWithTraceRunnerStepChoice (acc, Sum.inr ())))))
              ((4 * Polynomial.X + 8).eval
                ((EncodedType.prod
                  splitWithTraceLoopAccEncodedType
                  splitWithTraceRunnerInstructionEncodedType).encode
                    (acc, Sum.inr ())).length)
            have hOut :=
              splitWithTraceRunnerStepChoice_outputs_right
                (splitWithTraceLoopAccEncodedType.encode acc)
            exact
              TM2Programs.evalsToInTime_mono
                (by
                  simpa [List.map_id, splitWithTraceRunnerStepChoiceRightInputStack,
                    splitWithTraceRunnerStepChoiceAccInputSymbol,
                    splitWithTraceRunnerStepChoiceInstructionTagInputSymbol,
                    splitWithTraceRunnerStepChoiceAccSymbol,
                    splitWithTraceRunnerStepChoiceEncodedType,
                    splitWithTraceRunnerStepChoice,
                    splitWithTraceRunnerInstructionEncodedType,
                    splitWithTraceRunnerFuelEncodedType,
                    EncodedType.prod, EncodedType.sum, EncodedType.raw] using hOut)
                (by
                  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
                    splitWithTraceRunnerInstructionEncodedType,
                    splitWithTraceRunnerFuelEncodedType,
                    EncodedType.prod, EncodedType.sum, EncodedType.raw]) }⟩

def splitWithTraceRunnerStepChoiceDispatch
    (q : splitWithTraceRunnerStepChoiceEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  match q with
  | Sum.inl input => ([], input)
  | Sum.inr acc => splitWithTraceLoopAccStep acc

noncomputable def splitWithTraceRunnerStepInitBranchTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      splitWithTraceLoopAccEncodedType
      (fun input => (([] : List splitWithLongHeadCoreEncodedType.Carrier), input)) := by
  simpa [splitWithTraceLoopAccEncodedType] using
    (TMBackedCostedMap.prodEmptyLeftConstId
      splitWithInputEncodedType
      (EncodedType.list splitWithLongHeadCoreEncodedType)
      ([] : List splitWithLongHeadCoreEncodedType.Carrier)
      (by simp [EncodedType.list]))

theorem splitWithTraceRunnerStepChoiceDispatch_inputSize_le
    (q : splitWithTraceRunnerStepChoiceEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize
        (splitWithTraceRunnerStepChoiceDispatch q) ≤
      3 * splitWithTraceRunnerStepChoiceEncodedType.inputSize q + 34 := by
  cases q with
  | inl input =>
      change
        splitWithTraceLoopAccEncodedType.inputSize
            (([] : List splitWithLongHeadCoreEncodedType.Carrier), input) ≤
          3 * ([Sum.inl false] ++ (splitWithInputEncodedType.encode input).map
            (fun s => Sum.inr (Sum.inl s))).length + 34
      rw [List.length_append, List.length_map]
      simp [splitWithTraceLoopAccEncodedType, EncodedType.inputSize,
        EncodedType.prod, EncodedType.list]
      omega
  | inr acc =>
      have h := splitWithTraceLoopAccStep_inputSize_le acc
      simp [splitWithTraceRunnerStepChoiceDispatch,
        splitWithTraceRunnerStepChoiceEncodedType, EncodedType.inputSize] at h ⊢
      omega

def splitWithTraceRunnerStepChoiceLeftPayloadEncodedType : EncodedType where
  Carrier := splitWithInputEncodedType.Carrier
  Symbol := splitWithInputEncodedType.Symbol ⊕ splitWithTraceLoopAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun input => (splitWithInputEncodedType.encode input).map Sum.inl

def splitWithTraceRunnerStepChoiceRightPayloadEncodedType : EncodedType where
  Carrier := splitWithTraceLoopAccEncodedType.Carrier
  Symbol := splitWithInputEncodedType.Symbol ⊕ splitWithTraceLoopAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun acc => (splitWithTraceLoopAccEncodedType.encode acc).map Sum.inr

def splitWithTraceRunnerStepChoiceLeftPayloadKeep :
    splitWithInputEncodedType.Symbol ⊕ splitWithTraceLoopAccEncodedType.Symbol →
      Option splitWithInputEncodedType.Symbol
  | Sum.inl s => some s
  | Sum.inr _ => none

def splitWithTraceRunnerStepChoiceRightPayloadKeep :
    splitWithInputEncodedType.Symbol ⊕ splitWithTraceLoopAccEncodedType.Symbol →
      Option splitWithTraceLoopAccEncodedType.Symbol
  | Sum.inl _ => none
  | Sum.inr s => some s

theorem splitWithTraceRunnerStepChoiceLeftPayload_encode_filterMap
    (input : splitWithInputEncodedType.Carrier) :
    (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input).filterMap
        splitWithTraceRunnerStepChoiceLeftPayloadKeep =
      splitWithInputEncodedType.encode input := by
  simp [splitWithTraceRunnerStepChoiceLeftPayloadEncodedType,
    splitWithTraceRunnerStepChoiceLeftPayloadKeep]

theorem splitWithTraceRunnerStepChoiceRightPayload_encode_filterMap
    (acc : splitWithTraceLoopAccEncodedType.Carrier) :
    (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc).filterMap
        splitWithTraceRunnerStepChoiceRightPayloadKeep =
      splitWithTraceLoopAccEncodedType.encode acc := by
  simp [splitWithTraceRunnerStepChoiceRightPayloadEncodedType,
    splitWithTraceRunnerStepChoiceRightPayloadKeep]

noncomputable def splitWithTraceRunnerStepChoiceLeftPayloadForgetTMBackedMap :
    TMBackedCostedMap
      splitWithTraceRunnerStepChoiceLeftPayloadEncodedType
      splitWithInputEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceRunnerStepChoiceLeftPayloadEncodedType)
      (Y := splitWithInputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro input
        rw [EncodedType.inputSize, EncodedType.inputSize]
        change (splitWithInputEncodedType.encode input).length ≤
          1 * (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input).length + 0
        rw [← splitWithTraceRunnerStepChoiceLeftPayload_encode_filterMap input]
        have h := List.length_filterMap_le splitWithTraceRunnerStepChoiceLeftPayloadKeep
          (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithTraceRunnerStepChoiceLeftPayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro input
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithTraceRunnerStepChoiceLeftPayloadKeep)
          (List.map id (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input))
          (some (List.map id (splitWithInputEncodedType.encode input)))
          ((4 * Polynomial.X + 2).eval
            (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithTraceRunnerStepChoiceLeftPayloadKeep
            (splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.encode input)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithTraceRunnerStepChoiceLeftPayload_encode_filterMap input).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

noncomputable def splitWithTraceRunnerStepChoiceRightPayloadForgetTMBackedMap :
    TMBackedCostedMap
      splitWithTraceRunnerStepChoiceRightPayloadEncodedType
      splitWithTraceLoopAccEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceRunnerStepChoiceRightPayloadEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro acc
        rw [EncodedType.inputSize, EncodedType.inputSize]
        change (splitWithTraceLoopAccEncodedType.encode acc).length ≤
          1 * (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc).length + 0
        rw [← splitWithTraceRunnerStepChoiceRightPayload_encode_filterMap acc]
        have h := List.length_filterMap_le splitWithTraceRunnerStepChoiceRightPayloadKeep
          (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithTraceRunnerStepChoiceRightPayloadEncodedType.Symbol
            splitWithTraceLoopAccEncodedType.Symbol
            splitWithTraceRunnerStepChoiceRightPayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro acc
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithTraceRunnerStepChoiceRightPayloadEncodedType.Symbol
            splitWithTraceLoopAccEncodedType.Symbol
            splitWithTraceRunnerStepChoiceRightPayloadKeep)
          (List.map id (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc))
          (some (List.map id (splitWithTraceLoopAccEncodedType.encode acc)))
          ((4 * Polynomial.X + 2).eval
            (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithTraceRunnerStepChoiceRightPayloadEncodedType.Symbol
            splitWithTraceLoopAccEncodedType.Symbol
            splitWithTraceRunnerStepChoiceRightPayloadKeep
            (splitWithTraceRunnerStepChoiceRightPayloadEncodedType.encode acc)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithTraceRunnerStepChoiceRightPayload_encode_filterMap acc).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

noncomputable def splitWithTraceRunnerStepChoiceDispatchTMBackedMap :
    TMBackedCostedMap
      splitWithTraceRunnerStepChoiceEncodedType
      splitWithTraceLoopAccEncodedType
      splitWithTraceRunnerStepChoiceDispatch where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceRunnerStepChoiceEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 3 34 (by
        intro q
        exact splitWithTraceRunnerStepChoiceDispatch_inputSize_le q))
  tm_polytime := by
    have hLeftInit :
        TMPolyTimeMap
          splitWithInputEncodedType
          splitWithTraceLoopAccEncodedType
          (fun input : splitWithInputEncodedType.Carrier =>
            (([] : List splitWithLongHeadCoreEncodedType.Carrier), input)) :=
      splitWithTraceRunnerStepInitBranchTMBackedMap.tm_polytime
    have hLeftForget :
        TMPolyTimeMap
          splitWithTraceRunnerStepChoiceLeftPayloadEncodedType
          splitWithInputEncodedType
          (fun input : splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.Carrier => input) :=
      splitWithTraceRunnerStepChoiceLeftPayloadForgetTMBackedMap.tm_polytime
    have hLeftMap :
        TMPolyTimeMap
          splitWithTraceRunnerStepChoiceLeftPayloadEncodedType
          splitWithTraceLoopAccEncodedType
          (fun input : splitWithTraceRunnerStepChoiceLeftPayloadEncodedType.Carrier =>
            (([] : List splitWithLongHeadCoreEncodedType.Carrier), input)) :=
      by
        have hComp := TMPolyTimeMap.comp hLeftInit hLeftForget
        simpa [Function.comp] using hComp
    have hRightStep :
        TMPolyTimeMap
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccStep :=
      splitWithTraceLoopAccStepTMBackedMap.tm_polytime
    have hRightForget :
        TMPolyTimeMap
          splitWithTraceRunnerStepChoiceRightPayloadEncodedType
          splitWithTraceLoopAccEncodedType
          (fun acc : splitWithTraceRunnerStepChoiceRightPayloadEncodedType.Carrier => acc) :=
      splitWithTraceRunnerStepChoiceRightPayloadForgetTMBackedMap.tm_polytime
    have hRightMap :
        TMPolyTimeMap
          splitWithTraceRunnerStepChoiceRightPayloadEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccStep :=
      by
        have hComp := TMPolyTimeMap.comp hRightStep hRightForget
        simpa [Function.comp] using hComp
    rcases hLeftMap with ⟨hLeft⟩
    rcases hRightMap with ⟨hRight⟩
    refine ⟨?_⟩
    change Turing.TM2ComputableInPolyTime
      (fun q : splitWithInputEncodedType.Carrier ⊕ splitWithTraceLoopAccEncodedType.Carrier =>
        match q with
        | Sum.inl input =>
            Sum.inl false :: (splitWithInputEncodedType.encode input).map
              (fun s => Sum.inr (Sum.inl s))
        | Sum.inr acc =>
            Sum.inl true :: (splitWithTraceLoopAccEncodedType.encode acc).map
              (fun s => Sum.inr (Sum.inr s)))
      splitWithTraceLoopAccEncodedType.encode
      (fun q =>
        match q with
        | Sum.inl input => (([] : List splitWithLongHeadCoreEncodedType.Carrier), input)
        | Sum.inr acc => splitWithTraceLoopAccStep acc)
    convert taggedBranchDispatchComputableInPolyTime hLeft hRight using 1
    · funext q
      cases q <;>
        simp [splitWithTraceRunnerStepChoiceLeftPayloadEncodedType,
          splitWithTraceRunnerStepChoiceRightPayloadEncodedType]
    · funext q
      cases q <;> rfl

end Karp21
end ComplexityReduction
