/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.BranchTraceStep

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/-- Accumulator for the bounded clause trace loop: emitted heads and current recursive input. -/
def splitWithTraceLoopAccEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.list splitWithLongHeadCoreEncodedType)
    splitWithInputEncodedType

def splitWithTraceLoopAccValue
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.Carrier :=
  (List.append (α := splitWithLongHeadCoreEncodedType.Carrier) a.1
    (splitWithTrace a.2.1 a.2.2).1, (splitWithTrace a.2.1 a.2.2).2)

/-- Accumulator states whose current recursive input is already in the short/base branch. -/
def splitWithTraceLoopShortAccEncodedType : EncodedType where
  Carrier := { a : splitWithTraceLoopAccEncodedType.Carrier // a.2.2.length ≤ 3 }
  Symbol := splitWithTraceLoopAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun a => splitWithTraceLoopAccEncodedType.encode a.1

/-- Accumulator states whose current recursive input is in the long branch. -/
def splitWithTraceLoopLongAccEncodedType : EncodedType where
  Carrier := { a : splitWithTraceLoopAccEncodedType.Carrier // 4 ≤ a.2.2.length }
  Symbol := splitWithTraceLoopAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun a => splitWithTraceLoopAccEncodedType.encode a.1

noncomputable def splitWithTraceLoopShortAccForgetTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopShortAccEncodedType
      splitWithTraceLoopAccEncodedType
      (fun a => a.1) :=
  TMBackedCostedMap.ofEncodingEquiv
    splitWithTraceLoopShortAccEncodedType splitWithTraceLoopAccEncodedType
    (fun a => a.1) (Equiv.refl _) (by
      intro a
      change splitWithTraceLoopAccEncodedType.encode a.1 =
        (splitWithTraceLoopAccEncodedType.encode a.1).map id
      simp)

noncomputable def splitWithTraceLoopLongAccForgetTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopLongAccEncodedType
      splitWithTraceLoopAccEncodedType
      (fun a => a.1) :=
  TMBackedCostedMap.ofEncodingEquiv
    splitWithTraceLoopLongAccEncodedType splitWithTraceLoopAccEncodedType
    (fun a => a.1) (Equiv.refl _) (by
      intro a
      change splitWithTraceLoopAccEncodedType.encode a.1 =
        (splitWithTraceLoopAccEncodedType.encode a.1).map id
      simp)

noncomputable def splitWithTraceLoopLongAccCurrentTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopLongAccEncodedType
      splitWithLongInputEncodedType
      (fun a => ⟨a.1.2, a.2⟩) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopLongAccEncodedType)
      (Y := splitWithLongInputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro a
        rcases a with ⟨a, ha⟩
        rcases a with ⟨heads, p⟩
        change splitWithInputEncodedType.inputSize p ≤
          1 * splitWithTraceLoopAccEncodedType.inputSize (heads, p) + 0
        simp [splitWithTraceLoopAccEncodedType]))
  tm_polytime := by
    let X := splitWithTraceLoopLongAccEncodedType
    have hForget :
        TMPolyTimeMap X splitWithTraceLoopAccEncodedType (fun a : X.Carrier => a.1) :=
      splitWithTraceLoopLongAccForgetTMBackedMap.tm_polytime
    have hCurrentPlain :
        TMPolyTimeMap X splitWithInputEncodedType (fun a : X.Carrier => a.1.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd
          (EncodedType.list splitWithLongHeadCoreEncodedType)
          splitWithInputEncodedType)
        hForget
    rcases hCurrentPlain with ⟨hCurrentPlain⟩
    exact ⟨{ hCurrentPlain with
      outputsFun := by
        intro a
        simpa [splitWithLongInputEncodedType] using hCurrentPlain.outputsFun a }⟩

theorem encodedList_inputSize_append (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  induction xs with
  | nil =>
      simp [EncodedType.inputSize_list_nil]
  | cons x xs ih =>
      rw [List.cons_append, EncodedType.inputSize_list_cons,
        EncodedType.inputSize_list_cons, ih]
      omega

def splitWithTraceLoopLongUpdate
    (a : splitWithTraceLoopLongAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  let step := splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩
  (List.append (α := splitWithLongHeadCoreEncodedType.Carrier) a.1.1 [step.1], step.2)

theorem splitWithTraceLoopLongUpdate_cons
    (heads : List splitWithLongHeadCoreEncodedType.Carrier)
    (next : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause)
    (h : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length) :
    splitWithTraceLoopLongUpdate ⟨(heads, (next, l₁ :: l₂ :: l₃ :: l₄ :: rest)), h⟩ =
      (List.append (α := splitWithLongHeadCoreEncodedType.Carrier)
        heads [(next, (l₁, l₂))],
        (Nat.succ next, SAT.Clause.negAux next :: l₃ :: l₄ :: rest)) := by
  unfold splitWithTraceLoopLongUpdate
  rw [splitWithLongTraceStepOutput_cons]
  rfl

theorem splitWithTraceLoopLongUpdate_inputSize_le
    (a : splitWithTraceLoopLongAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopLongUpdate a) ≤
      3 * splitWithTraceLoopLongAccEncodedType.inputSize a + 31 := by
  rcases a with ⟨a, ha⟩
  rcases a with ⟨heads, p⟩
  let step := splitWithLongTraceStepOutput ⟨p, ha⟩
  have hStep := splitWithLongTraceStepOutput_inputSize_le ⟨p, ha⟩
  change
    splitWithTraceLoopAccEncodedType.inputSize
        (List.append (α := splitWithLongHeadCoreEncodedType.Carrier) heads [step.1],
          step.2) ≤
      3 * splitWithTraceLoopAccEncodedType.inputSize (heads, p) + 31
  simp [splitWithTraceLoopAccEncodedType, encodedList_inputSize_append]
  have hStep' :
      splitWithLongHeadCoreEncodedType.inputSize step.1 + 1 +
          splitWithInputEncodedType.inputSize step.2 ≤
        3 * splitWithInputEncodedType.inputSize p + 30 := by
    simpa [splitWithLongTraceStepOutputEncodedType, step] using hStep
  omega

noncomputable def splitWithTraceLoopLongUpdateTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopLongAccEncodedType
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopLongUpdate where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopLongAccEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 3 31 (by
        intro a
        exact splitWithTraceLoopLongUpdate_inputSize_le a))
  tm_polytime := by
    let X := splitWithTraceLoopLongAccEncodedType
    have hForget :
        TMPolyTimeMap X splitWithTraceLoopAccEncodedType (fun a : X.Carrier => a.1) :=
      splitWithTraceLoopLongAccForgetTMBackedMap.tm_polytime
    have hHeads :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun a : X.Carrier => a.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst
          (EncodedType.list splitWithLongHeadCoreEncodedType)
          splitWithInputEncodedType)
        hForget
    have hCurrent :
        TMPolyTimeMap X splitWithLongInputEncodedType
          (fun a : X.Carrier => ⟨a.1.2, a.2⟩) :=
      splitWithTraceLoopLongAccCurrentTMBackedMap.tm_polytime
    have hStep :
        TMPolyTimeMap X splitWithLongTraceStepOutputEncodedType
          (fun a : X.Carrier => splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩) :=
      TMPolyTimeMap.comp splitWithLongTraceStepOutputTMBackedMap.tm_polytime hCurrent
    have hNewHead :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType
          (fun a : X.Carrier => (splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst splitWithLongHeadCoreEncodedType splitWithInputEncodedType)
        hStep
    have hRecursiveInput :
        TMPolyTimeMap X splitWithInputEncodedType
          (fun a : X.Carrier => (splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd splitWithLongHeadCoreEncodedType splitWithInputEncodedType)
        hStep
    have hNewHeadSingleton :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun a : X.Carrier => [(splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩).1]) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton splitWithLongHeadCoreEncodedType)
        hNewHead
    have hAppendInput :
        TMPolyTimeMap X
          (EncodedType.prod
            (EncodedType.list splitWithLongHeadCoreEncodedType)
            (EncodedType.list splitWithLongHeadCoreEncodedType))
          (fun a : X.Carrier =>
            (a.1.1, [(splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩).1])) :=
      TMPolyTimeMap.prod_mk hHeads hNewHeadSingleton
    have hHeadsOut :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun a : X.Carrier =>
            List.append (α := splitWithLongHeadCoreEncodedType.Carrier) a.1.1
              [(splitWithLongTraceStepOutput ⟨a.1.2, a.2⟩).1]) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append splitWithLongHeadCoreEncodedType)
        hAppendInput
    have hOut :
        TMPolyTimeMap X splitWithTraceLoopAccEncodedType
          splitWithTraceLoopLongUpdate :=
      TMPolyTimeMap.prod_mk hHeadsOut hRecursiveInput
    simpa [X, splitWithTraceLoopLongUpdate, splitWithTraceLoopAccEncodedType,
      splitWithLongTraceStepOutputEncodedType] using hOut

/-- Short/long accumulator branch choice with a shared accumulator payload. -/
def splitWithTraceLoopAccChoiceEncodedType : EncodedType where
  Carrier :=
    splitWithTraceLoopShortAccEncodedType.Carrier ⊕
      splitWithTraceLoopLongAccEncodedType.Carrier
  Symbol := Bool ⊕ splitWithTraceLoopAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode
    | Sum.inl a => [Sum.inl false] ++ (splitWithTraceLoopAccEncodedType.encode a.1).map Sum.inr
    | Sum.inr a => [Sum.inl true] ++ (splitWithTraceLoopAccEncodedType.encode a.1).map Sum.inr

def splitWithTraceLoopAccChoice
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccChoiceEncodedType.Carrier :=
  if h : a.2.2.length ≤ 3 then
    Sum.inl ⟨a, h⟩
  else
    Sum.inr ⟨a, by omega⟩

def splitWithTraceLoopAccBranchDecisionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool splitWithTraceLoopAccEncodedType

def splitWithTraceLoopAccBranchDecision
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccBranchDecisionEncodedType.Carrier :=
  (splitWithIsShort a.2, a)

theorem splitWithTraceLoopAccBranchDecision_inputSize_le
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccBranchDecisionEncodedType.inputSize
        (splitWithTraceLoopAccBranchDecision a) ≤
      splitWithTraceLoopAccEncodedType.inputSize a + 2 := by
  simp [splitWithTraceLoopAccBranchDecisionEncodedType,
    splitWithTraceLoopAccBranchDecision, EncodedType.inputSize, EncodedType.bool,
    EncodedType.prod]

noncomputable def splitWithTraceLoopAccBranchDecisionTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopAccBranchDecisionEncodedType
      splitWithTraceLoopAccBranchDecision where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccEncodedType)
      (Y := splitWithTraceLoopAccBranchDecisionEncodedType)
      (LinearSizeBound.intro_with 1 2 (by
        intro a
        have h := splitWithTraceLoopAccBranchDecision_inputSize_le a
        omega))
  tm_polytime := by
    let X := splitWithTraceLoopAccEncodedType
    have hCurrent :
        TMPolyTimeMap X splitWithInputEncodedType (fun a : X.Carrier => a.2) :=
      TMPolyTimeMap.snd
        (EncodedType.list splitWithLongHeadCoreEncodedType)
        splitWithInputEncodedType
    have hPred :
        TMPolyTimeMap X EncodedType.bool (fun a : X.Carrier => splitWithIsShort a.2) :=
      TMPolyTimeMap.comp splitWithIsShortTMBackedMap.tm_polytime hCurrent
    have hId : TMPolyTimeMap X X id := TMPolyTimeMap.id X
    have hPair :
        TMPolyTimeMap X splitWithTraceLoopAccBranchDecisionEncodedType
          splitWithTraceLoopAccBranchDecision :=
      TMPolyTimeMap.prod_mk hPred hId
    simpa [X, splitWithTraceLoopAccBranchDecision,
      splitWithTraceLoopAccBranchDecisionEncodedType] using hPair

def splitWithTraceLoopAccCheckedBranchDecisionEncodedType : EncodedType where
  Carrier :=
    { q : splitWithTraceLoopAccBranchDecisionEncodedType.Carrier //
      q.1 = splitWithIsShort q.2.2 }
  Symbol := splitWithTraceLoopAccBranchDecisionEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun q => splitWithTraceLoopAccBranchDecisionEncodedType.encode q.1

def splitWithTraceLoopAccCheckedBranchDecision
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Carrier :=
  ⟨splitWithTraceLoopAccBranchDecision a, rfl⟩

theorem splitWithTraceLoopAccCheckedBranchDecision_inputSize_le
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccCheckedBranchDecisionEncodedType.inputSize
        (splitWithTraceLoopAccCheckedBranchDecision a) ≤
      splitWithTraceLoopAccEncodedType.inputSize a + 2 := by
  simpa [splitWithTraceLoopAccCheckedBranchDecisionEncodedType,
    splitWithTraceLoopAccCheckedBranchDecision] using
    splitWithTraceLoopAccBranchDecision_inputSize_le a

noncomputable def splitWithTraceLoopAccCheckedBranchDecisionTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopAccCheckedBranchDecisionEncodedType
      splitWithTraceLoopAccCheckedBranchDecision where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccEncodedType)
      (Y := splitWithTraceLoopAccCheckedBranchDecisionEncodedType)
      (LinearSizeBound.intro_with 1 2 (by
        intro a
        have h := splitWithTraceLoopAccCheckedBranchDecision_inputSize_le a
        omega))
  tm_polytime := by
    rcases splitWithTraceLoopAccBranchDecisionTMBackedMap.tm_polytime with ⟨h⟩
    exact ⟨{ h with
      outputsFun := by
        intro a
        simpa [splitWithTraceLoopAccCheckedBranchDecisionEncodedType,
          splitWithTraceLoopAccCheckedBranchDecision] using h.outputsFun a }⟩

def splitWithTraceLoopAccChoiceKeep :
    splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Symbol →
      Option splitWithTraceLoopAccChoiceEncodedType.Symbol
  | some (Sum.inl b) => some (Sum.inl (!b))
  | none => none
  | some (Sum.inr s) => some (Sum.inr s)

theorem splitWithTraceLoopAccChoice_encode_filterMap
    (q : splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Carrier) :
    (splitWithTraceLoopAccCheckedBranchDecisionEncodedType.encode q).filterMap
        splitWithTraceLoopAccChoiceKeep =
      splitWithTraceLoopAccChoiceEncodedType.encode
        (splitWithTraceLoopAccChoice q.1.2) := by
  rcases q with ⟨q, hq⟩
  rcases q with ⟨isShort, a⟩
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  by_cases hLen : c.length ≤ 3
  · have hb : isShort = true := by
      simpa [splitWithIsShort, hLen] using hq
    subst isShort
    simp [splitWithTraceLoopAccCheckedBranchDecisionEncodedType,
      splitWithTraceLoopAccChoiceEncodedType, splitWithTraceLoopAccChoice,
      splitWithTraceLoopAccChoiceKeep, splitWithTraceLoopAccBranchDecisionEncodedType,
      splitWithTraceLoopAccEncodedType, EncodedType.prod, EncodedType.bool, Function.comp,
      hLen]
    rfl
  · have hb : isShort = false := by
      simpa [splitWithIsShort, hLen] using hq
    subst isShort
    simp [splitWithTraceLoopAccCheckedBranchDecisionEncodedType,
      splitWithTraceLoopAccChoiceEncodedType, splitWithTraceLoopAccChoice,
      splitWithTraceLoopAccChoiceKeep, splitWithTraceLoopAccBranchDecisionEncodedType,
      splitWithTraceLoopAccEncodedType, EncodedType.prod, EncodedType.bool, Function.comp,
      hLen]
    rfl

theorem splitWithTraceLoopAccChoice_inputSize_le
    (q : splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Carrier) :
    splitWithTraceLoopAccChoiceEncodedType.inputSize (splitWithTraceLoopAccChoice q.1.2) ≤
      splitWithTraceLoopAccCheckedBranchDecisionEncodedType.inputSize q := by
  rw [EncodedType.inputSize, EncodedType.inputSize]
  rw [← splitWithTraceLoopAccChoice_encode_filterMap q]
  exact List.length_filterMap_le _ _

noncomputable def splitWithTraceLoopAccChoiceTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccCheckedBranchDecisionEncodedType
      splitWithTraceLoopAccChoiceEncodedType
      (fun q => splitWithTraceLoopAccChoice q.1.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccCheckedBranchDecisionEncodedType)
      (Y := splitWithTraceLoopAccChoiceEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro q
        have h := splitWithTraceLoopAccChoice_inputSize_le q
        omega))
  tm_polytime :=
    ⟨{ tm :=
          TM2Programs.filterMapMachine
            splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Symbol
            splitWithTraceLoopAccChoiceEncodedType.Symbol
            splitWithTraceLoopAccChoiceKeep
       inputAlphabet := Equiv.refl _
       outputAlphabet := Equiv.refl _
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro q
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine
            splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Symbol
            splitWithTraceLoopAccChoiceEncodedType.Symbol
            splitWithTraceLoopAccChoiceKeep)
          (List.map id (splitWithTraceLoopAccCheckedBranchDecisionEncodedType.encode q))
          (some (List.map id
            (splitWithTraceLoopAccChoiceEncodedType.encode
              (splitWithTraceLoopAccChoice q.1.2))))
          ((4 * Polynomial.X + 2).eval
            (splitWithTraceLoopAccCheckedBranchDecisionEncodedType.encode q).length)
        have hOut :=
          TM2Programs.filterMap_outputs
            splitWithTraceLoopAccCheckedBranchDecisionEncodedType.Symbol
            splitWithTraceLoopAccChoiceEncodedType.Symbol
            splitWithTraceLoopAccChoiceKeep
            (splitWithTraceLoopAccCheckedBranchDecisionEncodedType.encode q)
        convert hOut using 1
        · simp
        · simp [List.map_id]
          exact (splitWithTraceLoopAccChoice_encode_filterMap q).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

def splitWithTraceLoopAccChoiceStep
    (q : splitWithTraceLoopAccChoiceEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  match q with
  | Sum.inl a => a.1
  | Sum.inr a => splitWithTraceLoopLongUpdate a

theorem splitWithTraceLoopAccChoiceStep_inputSize_le
    (q : splitWithTraceLoopAccChoiceEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccChoiceStep q) ≤
      3 * splitWithTraceLoopAccChoiceEncodedType.inputSize q + 31 := by
  cases q with
  | inl a =>
      simp [splitWithTraceLoopAccChoiceStep, splitWithTraceLoopAccChoiceEncodedType,
        splitWithTraceLoopShortAccEncodedType, EncodedType.inputSize]
      omega
  | inr a =>
      have h := splitWithTraceLoopLongUpdate_inputSize_le a
      simp [splitWithTraceLoopAccChoiceStep, splitWithTraceLoopAccChoiceEncodedType,
        splitWithTraceLoopLongAccEncodedType, EncodedType.inputSize] at h ⊢
      omega

noncomputable def splitWithTraceLoopAccChoiceStepTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccChoiceEncodedType
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopAccChoiceStep where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccChoiceEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 3 31 (by
        intro q
        exact splitWithTraceLoopAccChoiceStep_inputSize_le q))
  tm_polytime := by
    rcases splitWithTraceLoopShortAccForgetTMBackedMap.tm_polytime with ⟨hShort⟩
    rcases splitWithTraceLoopLongUpdateTMBackedMap.tm_polytime with ⟨hLong⟩
    refine ⟨?_⟩
    change Turing.TM2ComputableInPolyTime
      (fun q : splitWithTraceLoopShortAccEncodedType.Carrier ⊕
          splitWithTraceLoopLongAccEncodedType.Carrier =>
        match q with
        | Sum.inl a => Sum.inl false :: (splitWithTraceLoopShortAccEncodedType.encode a).map Sum.inr
        | Sum.inr a => Sum.inl true :: (splitWithTraceLoopLongAccEncodedType.encode a).map Sum.inr)
      splitWithTraceLoopAccEncodedType.encode
      (fun q =>
        match q with
        | Sum.inl a => a.1
        | Sum.inr a => splitWithTraceLoopLongUpdate a)
    convert taggedBranchDispatchComputableInPolyTime hShort hLong using 1
    · funext q
      cases q <;> rfl
    · funext q
      cases q <;> rfl

def splitWithTraceLoopAccStep
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  splitWithTraceLoopAccChoiceStep (splitWithTraceLoopAccChoice a)

theorem splitWithTraceLoopAccStep_inputSize_le
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccStep a) ≤
      3 * splitWithTraceLoopAccEncodedType.inputSize a + 34 := by
  have hChoice :
      splitWithTraceLoopAccChoiceEncodedType.inputSize (splitWithTraceLoopAccChoice a) ≤
        splitWithTraceLoopAccEncodedType.inputSize a + 1 := by
    by_cases hLen : a.2.2.length ≤ 3
    · simp [splitWithTraceLoopAccChoice, splitWithTraceLoopAccChoiceEncodedType,
        splitWithTraceLoopShortAccEncodedType, EncodedType.inputSize, hLen]
    · simp [splitWithTraceLoopAccChoice, splitWithTraceLoopAccChoiceEncodedType,
        splitWithTraceLoopLongAccEncodedType, EncodedType.inputSize, hLen]
  have hStep :=
    splitWithTraceLoopAccChoiceStep_inputSize_le (splitWithTraceLoopAccChoice a)
  unfold splitWithTraceLoopAccStep
  omega

noncomputable def splitWithTraceLoopAccStepTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopAccEncodedType
      splitWithTraceLoopAccStep where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 3 34 (by
        intro a
        exact splitWithTraceLoopAccStep_inputSize_le a))
  tm_polytime := by
    have hChecked :
        TMPolyTimeMap
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccCheckedBranchDecisionEncodedType
          splitWithTraceLoopAccCheckedBranchDecision :=
      splitWithTraceLoopAccCheckedBranchDecisionTMBackedMap.tm_polytime
    have hChoice :
        TMPolyTimeMap
          splitWithTraceLoopAccCheckedBranchDecisionEncodedType
          splitWithTraceLoopAccChoiceEncodedType
          (fun q => splitWithTraceLoopAccChoice q.1.2) :=
      splitWithTraceLoopAccChoiceTMBackedMap.tm_polytime
    have hChoiceFromAcc :
        TMPolyTimeMap
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccChoiceEncodedType
          splitWithTraceLoopAccChoice :=
      TMPolyTimeMap.comp hChoice hChecked
    have hStepChoice :
        TMPolyTimeMap
          splitWithTraceLoopAccChoiceEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccChoiceStep :=
      splitWithTraceLoopAccChoiceStepTMBackedMap.tm_polytime
    have hStep :
        TMPolyTimeMap
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceLoopAccStep :=
      TMPolyTimeMap.comp hStepChoice hChoiceFromAcc
    simpa [splitWithTraceLoopAccStep, Function.comp] using hStep

theorem splitWithTraceLoopLongUpdate_value
    (a : splitWithTraceLoopLongAccEncodedType.Carrier) :
    splitWithTraceLoopAccValue (splitWithTraceLoopLongUpdate a) =
      splitWithTraceLoopAccValue a.1 := by
  rcases a with ⟨a, ha⟩
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp at ha
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp at ha
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp at ha
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp at ha
              | cons l₄ rest =>
                  have hTrace :
                      splitWithTrace next (l₁ :: l₂ :: l₃ :: l₄ :: rest) =
                        ((next, (l₁, l₂)) ::
                          (splitWithTrace (Nat.succ next)
                            (SAT.Clause.negAux next :: l₃ :: l₄ :: rest)).1,
                          (splitWithTrace (Nat.succ next)
                            (SAT.Clause.negAux next :: l₃ :: l₄ :: rest)).2) := by
                    simpa [splitWithLongTraceStepOutput_cons] using
                      splitWithTrace_eq_longTraceStepOutput_cons next l₁ l₂ l₃ l₄ rest ha
                  simp [splitWithTraceLoopAccValue, splitWithTraceLoopLongUpdate,
                    splitWithLongTraceStepOutput_cons, List.append_assoc]
                  have hTraceHeads := congrArg Prod.fst hTrace
                  have hTraceBase := congrArg Prod.snd hTrace
                  simp at hTraceHeads hTraceBase
                  apply Prod.ext
                  · exact
                      (congrArg
                        (fun xs : List splitWithLongHeadCoreEncodedType.Carrier =>
                          List.append (α := splitWithLongHeadCoreEncodedType.Carrier) heads xs)
                        hTraceHeads).symm
                  · exact hTraceBase.symm

theorem splitWithTraceLoopAccStep_value
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccValue (splitWithTraceLoopAccStep a) =
      splitWithTraceLoopAccValue a := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  by_cases hLen : c.length ≤ 3
  · simp [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
      splitWithTraceLoopAccChoiceStep, splitWithTraceLoopAccValue, hLen]
  · have hLong : 4 ≤ c.length := by omega
    simpa [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
      splitWithTraceLoopAccChoiceStep, hLen] using
      splitWithTraceLoopLongUpdate_value ⟨(heads, (next, c)), hLong⟩

def splitWithTraceLoopAccIterate :
    Nat → splitWithTraceLoopAccEncodedType.Carrier →
      splitWithTraceLoopAccEncodedType.Carrier
  | 0, a => a
  | n + 1, a => splitWithTraceLoopAccIterate n (splitWithTraceLoopAccStep a)

def splitWithTraceLoopAccNext
    (a : splitWithTraceLoopAccEncodedType.Carrier) : Nat :=
  a.2.1

theorem splitWithTraceLoopAccIterate_succ_eq_step_iterate
    (n : Nat) (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccIterate (n + 1) a =
      splitWithTraceLoopAccStep (splitWithTraceLoopAccIterate n a) := by
  induction n generalizing a with
  | zero =>
      rfl
  | succ n ih =>
      change
        splitWithTraceLoopAccIterate (n + 1) (splitWithTraceLoopAccStep a) =
          splitWithTraceLoopAccStep
            (splitWithTraceLoopAccIterate n (splitWithTraceLoopAccStep a))
      exact ih (splitWithTraceLoopAccStep a)

theorem splitWithTraceLoopAccStep_next_le_succ
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccNext (splitWithTraceLoopAccStep a) ≤
      splitWithTraceLoopAccNext a + 1 := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  change Nat at next
  cases c with
  | nil =>
      simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
        splitWithTraceLoopAccChoiceStep]
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
            splitWithTraceLoopAccChoiceStep]
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
                splitWithTraceLoopAccChoiceStep]
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep,
                    splitWithTraceLoopAccChoice,
                    splitWithTraceLoopAccChoiceStep]
              | cons l₄ rest =>
                  have hNotShort :
                      ¬ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length ≤ 3 := by
                    simp
                  have hStep :
                      splitWithTraceLoopAccStep
                          (heads, (next, l₁ :: l₂ :: l₃ :: l₄ :: rest)) =
                        (List.append (α := splitWithLongHeadCoreEncodedType.Carrier)
                          heads [(next, (l₁, l₂))],
                          (Nat.succ next,
                            SAT.Clause.negAux next :: l₃ :: l₄ :: rest)) := by
                    simpa [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice, hNotShort,
                      splitWithTraceLoopAccChoiceStep] using
                      splitWithTraceLoopLongUpdate_cons heads next l₁ l₂ l₃ l₄ rest (by simp)
                  rw [hStep]
                  simp [splitWithTraceLoopAccNext]

theorem splitWithTraceLoopAccStep_inputSize_le_add_next
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccStep a) ≤
      splitWithTraceLoopAccEncodedType.inputSize a + 2 * splitWithTraceLoopAccNext a + 10 := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  change Nat at next
  cases c with
  | nil =>
      simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
        splitWithTraceLoopAccChoiceStep]
      omega
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
            splitWithTraceLoopAccChoiceStep]
          omega
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
                splitWithTraceLoopAccChoiceStep]
              omega
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccStep,
                    splitWithTraceLoopAccChoice,
                    splitWithTraceLoopAccChoiceStep]
                  omega
              | cons l₄ rest =>
                  have hNotShort :
                      ¬ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length ≤ 3 := by
                    simp
                  have hStep :
                      splitWithTraceLoopAccStep
                          (heads, (next, l₁ :: l₂ :: l₃ :: l₄ :: rest)) =
                        (List.append (α := splitWithLongHeadCoreEncodedType.Carrier)
                          heads [(next, (l₁, l₂))],
                          (Nat.succ next,
                            SAT.Clause.negAux next :: l₃ :: l₄ :: rest)) := by
                    simpa [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice, hNotShort,
                      splitWithTraceLoopAccChoiceStep] using
                      splitWithTraceLoopLongUpdate_cons heads next l₁ l₂ l₃ l₄ rest (by simp)
                  rw [hStep]
                  simp [splitWithTraceLoopAccNext, splitWithTraceLoopAccEncodedType,
                    splitWithInputEncodedType, splitWithLongHeadCoreEncodedType,
                    clauseStructuredEncodedType, literalStructured_inputSize_eq,
                    SAT.Clause.negAux, encodedList_inputSize_append]
                  simp [EncodedType.inputSize, EncodedType.list, literalStructuredEncodedType,
                    literalTupleStructuredEncodedType, EncodedType.prod, EncodedType.nat,
                    EncodedType.bool]
                  omega

theorem splitWithTraceLoopAccIterate_next_le
    (n : Nat) (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccNext (splitWithTraceLoopAccIterate n a) ≤
      splitWithTraceLoopAccNext a + n := by
  induction n generalizing a with
  | zero =>
      simp [splitWithTraceLoopAccIterate]
  | succ n ih =>
      have hTail := ih (splitWithTraceLoopAccStep a)
      have hStep := splitWithTraceLoopAccStep_next_le_succ a
      simp [splitWithTraceLoopAccIterate] at hTail ⊢
      omega

theorem splitWithTraceLoopAccIterate_inputSize_le
    (n : Nat) (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccIterate n a) ≤
      splitWithTraceLoopAccEncodedType.inputSize a +
        n * (2 * (splitWithTraceLoopAccNext a + n) + 10) := by
  induction n generalizing a with
  | zero =>
      simp [splitWithTraceLoopAccIterate]
  | succ n ih =>
      have hTail := ih (splitWithTraceLoopAccStep a)
      have hStepSize := splitWithTraceLoopAccStep_inputSize_le_add_next a
      have hStepNext := splitWithTraceLoopAccStep_next_le_succ a
      have hTerm :
          2 * (splitWithTraceLoopAccNext (splitWithTraceLoopAccStep a) + n) + 10 ≤
            2 * (splitWithTraceLoopAccNext a + (n + 1)) + 10 := by
        omega
      have hMul :
          n * (2 * (splitWithTraceLoopAccNext (splitWithTraceLoopAccStep a) + n) + 10) ≤
            n * (2 * (splitWithTraceLoopAccNext a + (n + 1)) + 10) :=
        Nat.mul_le_mul_left n hTerm
      simp [splitWithTraceLoopAccIterate] at hTail ⊢
      calc
        splitWithTraceLoopAccEncodedType.inputSize
            (splitWithTraceLoopAccIterate n (splitWithTraceLoopAccStep a))
            ≤ splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccStep a) +
                n * (2 * (splitWithTraceLoopAccNext (splitWithTraceLoopAccStep a) + n) +
                  10) := hTail
        _ ≤ splitWithTraceLoopAccEncodedType.inputSize a + 2 * splitWithTraceLoopAccNext a +
                10 + n * (2 * (splitWithTraceLoopAccNext a + (n + 1)) + 10) := by
              omega
        _ ≤ splitWithTraceLoopAccEncodedType.inputSize a +
                (n + 1) * (2 * (splitWithTraceLoopAccNext a + (n + 1)) + 10) := by
              nlinarith

theorem splitWithTraceLoopAccIterate_value
    (n : Nat) (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceLoopAccValue (splitWithTraceLoopAccIterate n a) =
      splitWithTraceLoopAccValue a := by
  induction n generalizing a with
  | zero =>
      rfl
  | succ n ih =>
      calc
        splitWithTraceLoopAccValue (splitWithTraceLoopAccIterate (n + 1) a)
            = splitWithTraceLoopAccValue
                (splitWithTraceLoopAccStep a) := ih (splitWithTraceLoopAccStep a)
        _ = splitWithTraceLoopAccValue a := splitWithTraceLoopAccStep_value a

theorem splitWithTraceLoopAccStep_eq_self_of_short
    (a : splitWithTraceLoopAccEncodedType.Carrier) (h : a.2.2.length ≤ 3) :
    splitWithTraceLoopAccStep a = a := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  simp [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice,
    splitWithTraceLoopAccChoiceStep, h]

theorem splitWithTraceLoopAccIterate_eq_self_of_short
    (n : Nat) (a : splitWithTraceLoopAccEncodedType.Carrier)
    (h : a.2.2.length ≤ 3) :
    splitWithTraceLoopAccIterate n a = a := by
  induction n generalizing a with
  | zero =>
      rfl
  | succ n ih =>
      simp [splitWithTraceLoopAccIterate, splitWithTraceLoopAccStep_eq_self_of_short a h,
        ih a h]

theorem splitWithTraceLoopAccIterate_base_length_le_three
    (heads : List splitWithLongHeadCoreEncodedType.Carrier)
    (next : Nat) (c : SAT.Clause) :
    (splitWithTraceLoopAccIterate c.length (heads, (next, c))).2.2.length ≤ 3 := by
  fun_induction SAT.Clause.splitWith next c generalizing heads with
  | case1 next =>
      exact (by decide : ([] : SAT.Clause).length ≤ 3)
  | case2 next l₁ =>
      have hShort : [l₁].length ≤ 3 := by simp
      have hEq :=
        splitWithTraceLoopAccIterate_eq_self_of_short [l₁].length
          (heads, (next, [l₁])) hShort
      simpa [hEq]
  | case3 next l₁ l₂ =>
      have hShort : [l₁, l₂].length ≤ 3 := by simp
      have hEq :=
        splitWithTraceLoopAccIterate_eq_self_of_short [l₁, l₂].length
          (heads, (next, [l₁, l₂])) hShort
      simpa [hEq]
  | case4 next l₁ l₂ l₃ =>
      have hShort : [l₁, l₂, l₃].length ≤ 3 := by simp
      have hEq :=
        splitWithTraceLoopAccIterate_eq_self_of_short [l₁, l₂, l₃].length
          (heads, (next, [l₁, l₂, l₃])) hShort
      simpa [hEq]
  | case5 next l₁ l₂ l₃ l₄ rest ih =>
      let head : splitWithLongHeadCoreEncodedType.Carrier := (next, (l₁, l₂))
      let tail : SAT.Clause := SAT.Clause.negAux next :: l₃ :: l₄ :: rest
      have hStep :
          splitWithTraceLoopAccStep (heads, (next, l₁ :: l₂ :: l₃ :: l₄ :: rest)) =
            (heads ++ [head], (next + 1, tail)) := by
        simp only [splitWithTraceLoopAccStep, splitWithTraceLoopAccChoice]
        split
        · rename_i hShort
          simp at hShort
          omega
        ·
          simp only [splitWithTraceLoopAccChoiceStep, splitWithTraceLoopLongUpdate,
            splitWithLongTraceStepOutput, splitWithLongInputDecomposition]
          simp [splitWithLongClausePayload, clauseMinLengthUncons,
            splitWithLongRecursiveInput, splitWithLongTailClause, head, tail]
          rfl
      change
        (splitWithTraceLoopAccIterate
            (tail.length + 1) (heads, (next, l₁ :: l₂ :: l₃ :: l₄ :: rest))).2.2.length ≤ 3
      simp [splitWithTraceLoopAccIterate, hStep, tail]
      simpa [tail, head] using ih (heads ++ [head])


end Karp21
end ComplexityReduction
