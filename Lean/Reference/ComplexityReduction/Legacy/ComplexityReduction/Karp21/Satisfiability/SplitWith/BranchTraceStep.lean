/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TaggedDispatch

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/--
Choose the short or long splitter-input subtype from a checked branch decision.
This is the first branch-dispatch layer; it does not run either branch body.
-/
def splitWithBranchInputChoice
    (q : splitWithCheckedBranchDecisionEncodedType.Carrier) :
    splitWithBranchInputChoiceEncodedType.Carrier :=
  if h : q.1.2.2.length ≤ 3 then
    Sum.inl ⟨q.1.2, h⟩
  else
    Sum.inr ⟨q.1.2, by omega⟩

def splitWithBranchInputChoiceKeep :
    splitWithCheckedBranchDecisionEncodedType.Symbol →
      Option splitWithBranchInputChoiceEncodedType.Symbol
  | some (Sum.inl b) => some (Sum.inl (!b))
  | none => none
  | some (Sum.inr s) => some (Sum.inr s)

theorem splitWithBranchInputChoice_encode_filterMap
    (q : splitWithCheckedBranchDecisionEncodedType.Carrier) :
    (splitWithCheckedBranchDecisionEncodedType.encode q).filterMap
        splitWithBranchInputChoiceKeep =
      splitWithBranchInputChoiceEncodedType.encode (splitWithBranchInputChoice q) := by
  rcases q with ⟨q, hq⟩
  rcases q with ⟨isShort, p⟩
  rcases p with ⟨next, c⟩
  by_cases hLen : c.length ≤ 3
  · have hb : isShort = true := by
      simpa [splitWithIsShort, hLen] using hq
    subst isShort
    simp [splitWithCheckedBranchDecisionEncodedType, splitWithBranchInputChoiceEncodedType,
      splitWithBranchInputChoice, splitWithBranchInputChoiceKeep, splitWithBranchDecisionEncodedType,
      EncodedType.prod, EncodedType.bool, hLen]
  · have hb : isShort = false := by
      simpa [splitWithIsShort, hLen] using hq
    subst isShort
    simp [splitWithCheckedBranchDecisionEncodedType, splitWithBranchInputChoiceEncodedType,
      splitWithBranchInputChoice, splitWithBranchInputChoiceKeep, splitWithBranchDecisionEncodedType,
      EncodedType.prod, EncodedType.bool, hLen]

theorem splitWithBranchInputChoice_inputSize_le
    (q : splitWithCheckedBranchDecisionEncodedType.Carrier) :
    splitWithBranchInputChoiceEncodedType.inputSize (splitWithBranchInputChoice q) ≤
      splitWithCheckedBranchDecisionEncodedType.inputSize q := by
  rw [EncodedType.inputSize, EncodedType.inputSize]
  rw [← splitWithBranchInputChoice_encode_filterMap q]
  exact List.length_filterMap_le _ _

/--
TM-backed branch-choice layer.  It consumes the checked `(isShort, input)` package
and emits a typed short/long input choice by a direct filter-map over the product
encoding.  It is still not the recursive trace runner.
-/
noncomputable def splitWithBranchInputChoiceTMBackedMap :
    TMBackedCostedMap
      splitWithCheckedBranchDecisionEncodedType
      splitWithBranchInputChoiceEncodedType
      splitWithBranchInputChoice where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithCheckedBranchDecisionEncodedType)
      (Y := splitWithBranchInputChoiceEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro q
        have h := splitWithBranchInputChoice_inputSize_le q
        omega))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithCheckedBranchDecisionEncodedType.Symbol
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithBranchInputChoiceKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro q
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithCheckedBranchDecisionEncodedType.Symbol
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithBranchInputChoiceKeep)
          (List.map id (splitWithCheckedBranchDecisionEncodedType.encode q))
          (some (List.map id
            (splitWithBranchInputChoiceEncodedType.encode (splitWithBranchInputChoice q))))
          ((4 * Polynomial.X + 2).eval
            (splitWithCheckedBranchDecisionEncodedType.encode q).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithCheckedBranchDecisionEncodedType.Symbol
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithBranchInputChoiceKeep
            (splitWithCheckedBranchDecisionEncodedType.encode q)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithBranchInputChoice_encode_filterMap q).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

/-- Read the leading short/long tag from a typed branch input choice. -/
def splitWithBranchInputChoiceTag
    (q : splitWithBranchInputChoiceEncodedType.Carrier) : Bool :=
  match q with
  | Sum.inl _ => false
  | Sum.inr _ => true

def splitWithBranchInputChoiceTagKeep :
    splitWithBranchInputChoiceEncodedType.Symbol → Option Bool
  | Sum.inl b => some b
  | Sum.inr _ => none

theorem splitWithBranchInputChoiceTag_encode_filterMap
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    (splitWithBranchInputChoiceEncodedType.encode q).filterMap
        splitWithBranchInputChoiceTagKeep =
      EncodedType.bool.encode (splitWithBranchInputChoiceTag q) := by
  cases q with
  | inl p =>
      simp [splitWithBranchInputChoiceEncodedType, splitWithBranchInputChoiceTag,
        splitWithBranchInputChoiceTagKeep, EncodedType.bool]
  | inr p =>
      simp [splitWithBranchInputChoiceEncodedType, splitWithBranchInputChoiceTag,
        splitWithBranchInputChoiceTagKeep, EncodedType.bool]

/--
Direct TM-backed reader for the branch-choice leading tag.  This is a parser
component for the future dispatcher; it does not run either branch body.
-/
noncomputable def splitWithBranchInputChoiceTagTMBackedMap :
    TMBackedCostedMap
      splitWithBranchInputChoiceEncodedType
      EncodedType.bool
      splitWithBranchInputChoiceTag where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithBranchInputChoiceEncodedType)
      (Y := EncodedType.bool)
      (LinearSizeBound.intro_with 1 0 (by
        intro q
        rw [EncodedType.inputSize, EncodedType.inputSize]
        rw [← splitWithBranchInputChoiceTag_encode_filterMap q]
        have h := List.length_filterMap_le splitWithBranchInputChoiceTagKeep
          (splitWithBranchInputChoiceEncodedType.encode q)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithBranchInputChoiceEncodedType.Symbol
            EncodedType.bool.Symbol
            splitWithBranchInputChoiceTagKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro q
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithBranchInputChoiceEncodedType.Symbol
            EncodedType.bool.Symbol
            splitWithBranchInputChoiceTagKeep)
          (List.map id (splitWithBranchInputChoiceEncodedType.encode q))
          (some (List.map id (EncodedType.bool.encode (splitWithBranchInputChoiceTag q))))
          ((4 * Polynomial.X + 2).eval
            (splitWithBranchInputChoiceEncodedType.encode q).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithBranchInputChoiceEncodedType.Symbol
            EncodedType.bool.Symbol
            splitWithBranchInputChoiceTagKeep
            (splitWithBranchInputChoiceEncodedType.encode q)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithBranchInputChoiceTag_encode_filterMap q).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

/-- Forget the branch proof and return the shared splitter input payload. -/
def splitWithBranchInputChoicePayload
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithInputEncodedType.Carrier :=
  match q with
  | Sum.inl p => p.1
  | Sum.inr p => p.1

def splitWithBranchInputChoicePayloadKeep :
    splitWithBranchInputChoiceEncodedType.Symbol → Option splitWithInputEncodedType.Symbol
  | Sum.inl _ => none
  | Sum.inr s => some s

theorem splitWithBranchInputChoicePayload_encode_filterMap
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    (splitWithBranchInputChoiceEncodedType.encode q).filterMap
        splitWithBranchInputChoicePayloadKeep =
      splitWithInputEncodedType.encode (splitWithBranchInputChoicePayload q) := by
  cases q with
  | inl p =>
      simp [splitWithBranchInputChoiceEncodedType, splitWithBranchInputChoicePayload,
        splitWithBranchInputChoicePayloadKeep]
  | inr p =>
      simp [splitWithBranchInputChoiceEncodedType, splitWithBranchInputChoicePayload,
        splitWithBranchInputChoicePayloadKeep]

/--
Direct TM-backed payload extractor for branch-choice inputs.  The dispatcher can
reuse this parser to prepare the chosen short/long branch input, but this map
does not by itself preserve the subtype proof or run a branch body.
-/
noncomputable def splitWithBranchInputChoicePayloadTMBackedMap :
    TMBackedCostedMap
      splitWithBranchInputChoiceEncodedType
      splitWithInputEncodedType
      splitWithBranchInputChoicePayload where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithBranchInputChoiceEncodedType)
      (Y := splitWithInputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro q
        rw [EncodedType.inputSize, EncodedType.inputSize]
        rw [← splitWithBranchInputChoicePayload_encode_filterMap q]
        have h := List.length_filterMap_le splitWithBranchInputChoicePayloadKeep
          (splitWithBranchInputChoiceEncodedType.encode q)
        simpa using h))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithBranchInputChoicePayloadKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro q
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithBranchInputChoicePayloadKeep)
          (List.map id (splitWithBranchInputChoiceEncodedType.encode q))
          (some
            (List.map id
              (splitWithInputEncodedType.encode (splitWithBranchInputChoicePayload q))))
          ((4 * Polynomial.X + 2).eval
            (splitWithBranchInputChoiceEncodedType.encode q).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithBranchInputChoiceEncodedType.Symbol
            splitWithInputEncodedType.Symbol
            splitWithBranchInputChoicePayloadKeep
            (splitWithBranchInputChoiceEncodedType.encode q)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithBranchInputChoicePayload_encode_filterMap q).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

/-- Parsed branch choice as the pair `(tag, splitter payload)`. -/
def splitWithBranchInputChoiceTagPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool splitWithInputEncodedType

def splitWithBranchInputChoiceTagPayload
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchInputChoiceTagPayloadEncodedType.Carrier :=
  (splitWithBranchInputChoiceTag q, splitWithBranchInputChoicePayload q)

theorem splitWithBranchInputChoiceTagPayload_inputSize_le
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchInputChoiceTagPayloadEncodedType.inputSize
        (splitWithBranchInputChoiceTagPayload q) ≤
      splitWithBranchInputChoiceEncodedType.inputSize q + 1 := by
  cases q with
  | inl p =>
      simp [splitWithBranchInputChoiceTagPayloadEncodedType,
        splitWithBranchInputChoiceTagPayload, splitWithBranchInputChoiceTag,
        splitWithBranchInputChoicePayload, splitWithBranchInputChoiceEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
  | inr p =>
      simp [splitWithBranchInputChoiceTagPayloadEncodedType,
        splitWithBranchInputChoiceTagPayload, splitWithBranchInputChoiceTag,
        splitWithBranchInputChoicePayload, splitWithBranchInputChoiceEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.bool]

/--
Direct TM-backed combined tag/payload parser for branch choices.  This packages
the two checked filter-map parsers; it still does not run the chosen branch.
-/
noncomputable def splitWithBranchInputChoiceTagPayloadTMBackedMap :
    TMBackedCostedMap
      splitWithBranchInputChoiceEncodedType
      splitWithBranchInputChoiceTagPayloadEncodedType
      splitWithBranchInputChoiceTagPayload where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithBranchInputChoiceEncodedType)
      (Y := splitWithBranchInputChoiceTagPayloadEncodedType)
      (LinearSizeBound.intro_with 1 1 (by
        intro q
        have h := splitWithBranchInputChoiceTagPayload_inputSize_le q
        omega))
  tm_polytime := by
    have hTag :
        TMPolyTimeMap splitWithBranchInputChoiceEncodedType EncodedType.bool
          splitWithBranchInputChoiceTag :=
      splitWithBranchInputChoiceTagTMBackedMap.tm_polytime
    have hPayload :
        TMPolyTimeMap splitWithBranchInputChoiceEncodedType splitWithInputEncodedType
          splitWithBranchInputChoicePayload :=
      splitWithBranchInputChoicePayloadTMBackedMap.tm_polytime
    have hPair :
        TMPolyTimeMap
          splitWithBranchInputChoiceEncodedType
          splitWithBranchInputChoiceTagPayloadEncodedType
          splitWithBranchInputChoiceTagPayload :=
      TMPolyTimeMap.prod_mk hTag hPayload
    simpa [splitWithBranchInputChoiceTagPayload,
      splitWithBranchInputChoiceTagPayloadEncodedType] using hPair

theorem splitWithBranchInputChoicePayload_short_of_tag_false
    (q : splitWithBranchInputChoiceEncodedType.Carrier)
    (hTag : splitWithBranchInputChoiceTag q = false) :
    (splitWithBranchInputChoicePayload q).2.length ≤ 3 := by
  cases q with
  | inl p =>
      exact p.2
  | inr p =>
      cases hTag

theorem splitWithBranchInputChoicePayload_long_of_tag_true
    (q : splitWithBranchInputChoiceEncodedType.Carrier)
    (hTag : splitWithBranchInputChoiceTag q = true) :
    4 ≤ (splitWithBranchInputChoicePayload q).2.length := by
  cases q with
  | inl p =>
      cases hTag
  | inr p =>
      exact p.2

/-- Project the short/base clause from a checked short splitter input. -/
noncomputable def splitWithShortInputClauseTMBackedMap :
    TMBackedCostedMap splitWithShortInputEncodedType clauseStructuredEncodedType
      (fun p => p.1.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithShortInputEncodedType)
      (Y := clauseStructuredEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        rcases p with ⟨p, hp⟩
        rcases p with ⟨next, c⟩
        change
          clauseStructuredEncodedType.inputSize c ≤
            1 * splitWithInputEncodedType.inputSize (next, c) + 0
        simp [splitWithInputEncodedType]))
  tm_polytime := by
    let X := splitWithShortInputEncodedType
    have hForget :
        TMPolyTimeMap X splitWithInputEncodedType (fun p : X.Carrier => p.1) :=
      splitWithShortInputForgetTMBackedMap.tm_polytime
    exact
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType)
        hForget

/-- Trace output for a checked short/base splitter input. -/
def splitWithShortTraceOutput
    (p : splitWithShortInputEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.Carrier :=
  ([], p.1.2)

theorem splitWithShortTraceOutput_inputSize_le
    (p : splitWithShortInputEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.inputSize (splitWithShortTraceOutput p) ≤
      splitWithShortInputEncodedType.inputSize p + 5 := by
  rcases p with ⟨p, hp⟩
  rcases p with ⟨next, c⟩
  change
    splitWithTraceOutputEncodedType.inputSize (([] : List splitWithLongHeadCoreEncodedType.Carrier), c) ≤
      splitWithInputEncodedType.inputSize (next, c) + 5
  simp [splitWithTraceOutputEncodedType, splitWithInputEncodedType]
  omega

/--
The short/base trace-output transition is direct TM-backed.  This is still only
the checked short branch, not the branch-choice machine.
-/
noncomputable def splitWithShortTraceOutputTMBackedMap :
    TMBackedCostedMap
      splitWithShortInputEncodedType
      splitWithTraceOutputEncodedType
      splitWithShortTraceOutput where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithShortInputEncodedType)
      (Y := splitWithTraceOutputEncodedType)
      (LinearSizeBound.intro_with 1 5 (by
        intro p
        have h := splitWithShortTraceOutput_inputSize_le p
        omega))
  tm_polytime := by
    let X := splitWithShortInputEncodedType
    have hHeads :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun _ : X.Carrier => ([] : List splitWithLongHeadCoreEncodedType.Carrier)) :=
      TMPolyTimeMap.const X (EncodedType.list splitWithLongHeadCoreEncodedType) []
    have hBase :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.1.2) :=
      splitWithShortInputClauseTMBackedMap.tm_polytime
    have hPair :
        TMPolyTimeMap X splitWithTraceOutputEncodedType splitWithShortTraceOutput :=
      TMPolyTimeMap.prod_mk hHeads hBase
    simpa [X, splitWithShortTraceOutput, splitWithTraceOutputEncodedType] using hPair

theorem splitWithTrace_eq_shortTraceOutput
    (p : splitWithShortInputEncodedType.Carrier) :
    splitWithTrace p.1.1 p.1.2 = splitWithShortTraceOutput p := by
  rcases p with ⟨p, hp⟩
  rcases p with ⟨next, c⟩
  fun_induction SAT.Clause.splitWith next c with
  | case1 next =>
      change splitWithTrace next [] =
        (([] : List splitWithLongHeadCoreEncodedType.Carrier), ([] : SAT.Clause))
      unfold splitWithTrace
      simp
  | case2 next l₁ =>
      change splitWithTrace next [l₁] =
        (([] : List splitWithLongHeadCoreEncodedType.Carrier), [l₁])
      unfold splitWithTrace
      simp
  | case3 next l₁ l₂ =>
      change splitWithTrace next [l₁, l₂] =
        (([] : List splitWithLongHeadCoreEncodedType.Carrier), [l₁, l₂])
      unfold splitWithTrace
      simp
  | case4 next l₁ l₂ l₃ =>
      change splitWithTrace next [l₁, l₂, l₃] =
        (([] : List splitWithLongHeadCoreEncodedType.Carrier), [l₁, l₂, l₃])
      unfold splitWithTrace
      simp
  | case5 next l₁ l₂ l₃ l₄ rest ih =>
      have hLong : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length := by simp
      change (l₁ :: l₂ :: l₃ :: l₄ :: rest).length ≤ 3 at hp
      omega

/--
Input for the recursive long-trace combiner: one checked long transition and the
already-computed trace output for its recursive input.
-/
def splitWithLongTraceConsInputEncodedType : EncodedType :=
  EncodedType.prod splitWithLongTraceStepOutputEncodedType splitWithTraceOutputEncodedType

/-- Cons the current long-step trace head onto the recursive trace output. -/
def splitWithLongTraceConsOutput
    (p : splitWithLongTraceConsInputEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.Carrier :=
  (p.1.1 :: p.2.1, p.2.2)

theorem splitWithLongTraceConsOutput_inputSize_le
    (p : splitWithLongTraceConsInputEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.inputSize (splitWithLongTraceConsOutput p) ≤
      splitWithLongTraceConsInputEncodedType.inputSize p := by
  rcases p with ⟨step, trace⟩
  rcases step with ⟨head, recursiveInput⟩
  rcases trace with ⟨heads, base⟩
  change
    splitWithTraceOutputEncodedType.inputSize (head :: heads, base) ≤
      splitWithLongTraceConsInputEncodedType.inputSize ((head, recursiveInput), (heads, base))
  simp [splitWithLongTraceConsInputEncodedType, splitWithTraceOutputEncodedType,
    splitWithLongTraceStepOutputEncodedType]
  omega

/--
After a recursive long branch has produced its trace output, consing the current
head trace entry onto it is direct TM-backed.  This is not the branch-choice or
loop runner; it is the long-recursive return combinator needed by that runner.
-/
noncomputable def splitWithLongTraceConsOutputTMBackedMap :
    TMBackedCostedMap
      splitWithLongTraceConsInputEncodedType
      splitWithTraceOutputEncodedType
      splitWithLongTraceConsOutput where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongTraceConsInputEncodedType)
      (Y := splitWithTraceOutputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        have h := splitWithLongTraceConsOutput_inputSize_le p
        omega))
  tm_polytime := by
    let X := splitWithLongTraceConsInputEncodedType
    have hStep :
        TMPolyTimeMap X splitWithLongTraceStepOutputEncodedType
          (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst splitWithLongTraceStepOutputEncodedType splitWithTraceOutputEncodedType
    have hTrace :
        TMPolyTimeMap X splitWithTraceOutputEncodedType
          (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd splitWithLongTraceStepOutputEncodedType splitWithTraceOutputEncodedType
    have hHead :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType
          (fun p : X.Carrier => p.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst splitWithLongHeadCoreEncodedType splitWithInputEncodedType)
        hStep
    have hRecursiveHeads :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun p : X.Carrier => p.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst
          (EncodedType.list splitWithLongHeadCoreEncodedType) clauseStructuredEncodedType)
        hTrace
    have hHeadPair :
        TMPolyTimeMap X
          (EncodedType.prod
            splitWithLongHeadCoreEncodedType
            (EncodedType.list splitWithLongHeadCoreEncodedType))
          (fun p : X.Carrier => (p.1.1, p.2.1)) :=
      TMPolyTimeMap.prod_mk hHead hRecursiveHeads
    have hHeads :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun p : X.Carrier => p.1.1 :: p.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_cons splitWithLongHeadCoreEncodedType)
        hHeadPair
    have hBase :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.2.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd
          (EncodedType.list splitWithLongHeadCoreEncodedType) clauseStructuredEncodedType)
        hTrace
    have hOut :
        TMPolyTimeMap X splitWithTraceOutputEncodedType splitWithLongTraceConsOutput :=
      TMPolyTimeMap.prod_mk hHeads hBase
    simpa [X, splitWithLongTraceConsOutput, splitWithLongTraceConsInputEncodedType,
      splitWithTraceOutputEncodedType] using hOut

theorem splitWithTrace_eq_longTraceConsOutput
    (p : splitWithLongInputEncodedType.Carrier) :
    let step := splitWithLongTraceStepOutput p
    splitWithTrace p.1.1 p.1.2 =
      splitWithLongTraceConsOutput (step, splitWithTrace step.2.1 step.2.2) := by
  rcases p with ⟨p, hp⟩
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp at hp
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp at hp
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp at hp
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp at hp
              | cons l₄ rest =>
                  have h :=
                    splitWithTrace_eq_longTraceStepOutput_cons next l₁ l₂ l₃ l₄ rest hp
                  simpa [splitWithLongTraceConsOutput] using h

/--
One branch-body result: either the complete short/base trace output, or one
long-step transition that still requires a recursive trace for its tail.
-/
def splitWithBranchTraceStepOutputEncodedType : EncodedType :=
  EncodedType.sum splitWithTraceOutputEncodedType splitWithLongTraceStepOutputEncodedType

def splitWithBranchTraceStepOutput
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchTraceStepOutputEncodedType.Carrier :=
  match q with
  | Sum.inl p => Sum.inl (splitWithShortTraceOutput p)
  | Sum.inr p => Sum.inr (splitWithLongTraceStepOutput p)

theorem splitWithBranchTraceStepOutput_inputSize_le
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    splitWithBranchTraceStepOutputEncodedType.inputSize
        (splitWithBranchTraceStepOutput q) ≤
      3 * splitWithBranchInputChoiceEncodedType.inputSize q + 40 := by
  cases q with
  | inl p =>
      have h := splitWithShortTraceOutput_inputSize_le p
      simp [splitWithBranchTraceStepOutputEncodedType, splitWithBranchTraceStepOutput,
        splitWithBranchInputChoiceEncodedType, splitWithShortInputEncodedType,
        EncodedType.inputSize, EncodedType.sum] at h ⊢
      omega
  | inr p =>
      have h := splitWithLongTraceStepOutput_inputSize_le p
      simp [splitWithBranchTraceStepOutputEncodedType, splitWithBranchTraceStepOutput,
        splitWithBranchInputChoiceEncodedType, splitWithLongInputEncodedType,
        EncodedType.inputSize, EncodedType.sum] at h ⊢
      omega

theorem splitWithBranchTraceStepOutput_eq_short_of_tag_false
    (q : splitWithBranchInputChoiceEncodedType.Carrier)
    (hTag : splitWithBranchInputChoiceTag q = false) :
    splitWithBranchTraceStepOutput q =
      Sum.inl
        (splitWithShortTraceOutput
          ⟨splitWithBranchInputChoicePayload q,
            splitWithBranchInputChoicePayload_short_of_tag_false q hTag⟩) := by
  cases q with
  | inl p =>
      simp [splitWithBranchTraceStepOutput, splitWithBranchInputChoicePayload,
        splitWithShortTraceOutput]
  | inr p =>
      cases hTag

theorem splitWithBranchTraceStepOutput_eq_long_of_tag_true
    (q : splitWithBranchInputChoiceEncodedType.Carrier)
    (hTag : splitWithBranchInputChoiceTag q = true) :
    splitWithBranchTraceStepOutput q =
      Sum.inr
        (splitWithLongTraceStepOutput
          ⟨splitWithBranchInputChoicePayload q,
            splitWithBranchInputChoicePayload_long_of_tag_true q hTag⟩) := by
  cases q with
  | inl p =>
      cases hTag
  | inr p =>
      simp [splitWithBranchTraceStepOutput, splitWithBranchInputChoicePayload]

/-- Size bound for injecting the checked short branch body into the common branch codomain. -/
theorem splitWithShortBranchTraceStepOutput_inputSize_le
    (p : splitWithShortInputEncodedType.Carrier) :
    splitWithBranchTraceStepOutputEncodedType.inputSize
        (Sum.inl (splitWithShortTraceOutput p)) ≤
      splitWithShortInputEncodedType.inputSize p + 6 := by
  have h := splitWithShortTraceOutput_inputSize_le p
  simp [splitWithBranchTraceStepOutputEncodedType, EncodedType.inputSize,
    EncodedType.sum] at h ⊢
  omega

/--
The short branch body, already injected into the common branch-result codomain,
is direct TM-backed.  This is still one side of the future dispatcher, not the
tag-dispatch machine over `splitWithBranchInputChoiceEncodedType`.
-/
noncomputable def splitWithShortBranchTraceStepOutputTMBackedMap :
    TMBackedCostedMap
      splitWithShortInputEncodedType
      splitWithBranchTraceStepOutputEncodedType
      (fun p => Sum.inl (splitWithShortTraceOutput p)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithShortInputEncodedType)
      (Y := splitWithBranchTraceStepOutputEncodedType)
      (LinearSizeBound.intro_with 1 6 (by
        intro p
        have h := splitWithShortBranchTraceStepOutput_inputSize_le p
        omega))
  tm_polytime := by
    have hShort :
        TMPolyTimeMap
          splitWithShortInputEncodedType
          splitWithTraceOutputEncodedType
          splitWithShortTraceOutput :=
      splitWithShortTraceOutputTMBackedMap.tm_polytime
    have hInject :
        TMPolyTimeMap
          splitWithTraceOutputEncodedType
          splitWithBranchTraceStepOutputEncodedType
          (@Sum.inl
            splitWithTraceOutputEncodedType.Carrier
            splitWithLongTraceStepOutputEncodedType.Carrier) :=
      TMPolyTimeMap.inl splitWithTraceOutputEncodedType splitWithLongTraceStepOutputEncodedType
    have hComp := TMPolyTimeMap.comp hInject hShort
    simpa [Function.comp, splitWithBranchTraceStepOutputEncodedType] using hComp

/-- Size bound for injecting the checked long branch body into the common branch codomain. -/
theorem splitWithLongBranchTraceStepOutput_inputSize_le
    (p : splitWithLongInputEncodedType.Carrier) :
    splitWithBranchTraceStepOutputEncodedType.inputSize
        (Sum.inr (splitWithLongTraceStepOutput p)) ≤
      3 * splitWithLongInputEncodedType.inputSize p + 31 := by
  have h := splitWithLongTraceStepOutput_inputSize_le p
  simp [splitWithBranchTraceStepOutputEncodedType, EncodedType.inputSize,
    EncodedType.sum] at h ⊢
  omega

/--
The long branch body, already injected into the common branch-result codomain,
is direct TM-backed.  This is still one side of the future dispatcher, not the
tag-dispatch machine over `splitWithBranchInputChoiceEncodedType`.
-/
noncomputable def splitWithLongBranchTraceStepOutputTMBackedMap :
    TMBackedCostedMap
      splitWithLongInputEncodedType
      splitWithBranchTraceStepOutputEncodedType
      (fun p => Sum.inr (splitWithLongTraceStepOutput p)) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongInputEncodedType)
      (Y := splitWithBranchTraceStepOutputEncodedType)
      (LinearSizeBound.intro_with 3 31 (by
        intro p
        exact splitWithLongBranchTraceStepOutput_inputSize_le p))
  tm_polytime := by
    have hLong :
        TMPolyTimeMap
          splitWithLongInputEncodedType
          splitWithLongTraceStepOutputEncodedType
          splitWithLongTraceStepOutput :=
      splitWithLongTraceStepOutputTMBackedMap.tm_polytime
    have hInject :
        TMPolyTimeMap
          splitWithLongTraceStepOutputEncodedType
          splitWithBranchTraceStepOutputEncodedType
          (@Sum.inr
            splitWithTraceOutputEncodedType.Carrier
            splitWithLongTraceStepOutputEncodedType.Carrier) :=
      TMPolyTimeMap.inr splitWithTraceOutputEncodedType splitWithLongTraceStepOutputEncodedType
    have hComp := TMPolyTimeMap.comp hInject hLong
    simpa [Function.comp, splitWithBranchTraceStepOutputEncodedType] using hComp

/--
Costed branch-body specification.  This is intentionally not a TM-backed map:
the remaining P16c work is to replace this branch specification with an actual
dispatch/iteration TM2 runner.
-/
noncomputable def splitWithBranchTraceStepOutputCostedMap :
    CostedMap
      splitWithBranchInputChoiceEncodedType
      splitWithBranchTraceStepOutputEncodedType
      splitWithBranchTraceStepOutput :=
  CostedMap.of_encodedLinearSizeBound
    (LinearSizeBound.intro_with 3 40 (by
      intro q
      exact splitWithBranchTraceStepOutput_inputSize_le q))

/--
Direct TM-backed tagged dispatcher for one clause-splitting branch step.  It
reads the public short/long tag, copies the shared splitter payload into only
the selected branch body, and retags that branch output into the common
trace-step codomain.
-/
noncomputable def splitWithBranchTraceStepOutputTMBackedMap :
    TMBackedCostedMap
      splitWithBranchInputChoiceEncodedType
      splitWithBranchTraceStepOutputEncodedType
      splitWithBranchTraceStepOutput where
  costed := splitWithBranchTraceStepOutputCostedMap
  tm_polytime := by
    rcases splitWithShortBranchTraceStepOutputTMBackedMap.tm_polytime with ⟨hShort⟩
    rcases splitWithLongBranchTraceStepOutputTMBackedMap.tm_polytime with ⟨hLong⟩
    refine ⟨?_⟩
    change Turing.TM2ComputableInPolyTime
      (fun q : splitWithShortInputEncodedType.Carrier ⊕
          splitWithLongInputEncodedType.Carrier =>
        match q with
        | Sum.inl p => Sum.inl false :: (splitWithShortInputEncodedType.encode p).map Sum.inr
        | Sum.inr p => Sum.inl true :: (splitWithLongInputEncodedType.encode p).map Sum.inr)
      splitWithBranchTraceStepOutputEncodedType.encode
      (fun q : splitWithShortInputEncodedType.Carrier ⊕
          splitWithLongInputEncodedType.Carrier =>
        match q with
        | Sum.inl p => Sum.inl (splitWithShortTraceOutput p)
        | Sum.inr p => Sum.inr (splitWithLongTraceStepOutput p))
    convert taggedBranchDispatchComputableInPolyTime hShort hLong using 1
    · funext q
      cases q <;> rfl
    · funext q
      cases q <;> rfl

theorem splitWithBranchTraceStepOutput_semantic
    (q : splitWithBranchInputChoiceEncodedType.Carrier) :
    match q, splitWithBranchTraceStepOutput q with
    | Sum.inl p, Sum.inl out => splitWithTrace p.1.1 p.1.2 = out
    | Sum.inr p, Sum.inr step =>
        splitWithTrace p.1.1 p.1.2 =
          splitWithLongTraceConsOutput (step, splitWithTrace step.2.1 step.2.2)
    | _, _ => False := by
  cases q with
  | inl p =>
      simp [splitWithBranchTraceStepOutput, splitWithTrace_eq_shortTraceOutput p]
  | inr p =>
      simp [splitWithBranchTraceStepOutput, splitWithTrace_eq_longTraceConsOutput p]


end Karp21
end ComplexityReduction
