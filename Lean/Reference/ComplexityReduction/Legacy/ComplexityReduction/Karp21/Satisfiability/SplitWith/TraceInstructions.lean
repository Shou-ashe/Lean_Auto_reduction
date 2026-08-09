/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.TraceLoop

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

def splitWithTraceRunnerFuelEncodedType : EncodedType :=
  EncodedType.raw Unit

def splitWithTraceRunnerInstructionEncodedType : EncodedType :=
  EncodedType.sum splitWithInputEncodedType splitWithTraceRunnerFuelEncodedType

def splitWithTraceRunnerInstructions
    (p : splitWithInputEncodedType.Carrier) :
    List splitWithTraceRunnerInstructionEncodedType.Carrier :=
  Sum.inl p :: p.2.map (fun _ => Sum.inr ())

theorem splitWithTraceRunnerFuelInstructions_inputSize
    (c : SAT.Clause) :
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
        (c.map (fun _ => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier))) =
      2 * c.length := by
  induction c with
  | nil =>
      simp [splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType]
  | cons l rest ih =>
      have hUnit :
          splitWithTraceRunnerInstructionEncodedType.inputSize
              (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier) = 1 := by
        simp [splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.raw]
      rw [List.map_cons, EncodedType.inputSize_list_cons, ih, hUnit]
      simp
      omega

theorem splitWithTraceRunnerInstructions_inputSize_le
    (p : splitWithInputEncodedType.Carrier) :
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
        (splitWithTraceRunnerInstructions p) ≤
      3 * splitWithInputEncodedType.inputSize p + 6 := by
  rcases p with ⟨next, c⟩
  have hLen : c.length ≤ clauseStructuredEncodedType.inputSize c := by
    clear next
    induction c with
    | nil =>
        simp [clauseStructuredEncodedType]
    | cons l rest ih =>
        change rest.length ≤ (EncodedType.list literalStructuredEncodedType).inputSize rest at ih
        change (l :: rest).length ≤
          (EncodedType.list literalStructuredEncodedType).inputSize (l :: rest)
        rw [EncodedType.inputSize_list_cons]
        simp
        omega
  have hFuel := splitWithTraceRunnerFuelInstructions_inputSize c
  have hInit :
      splitWithTraceRunnerInstructionEncodedType.inputSize
          (Sum.inl (next, c) : splitWithTraceRunnerInstructionEncodedType.Carrier) =
        splitWithInputEncodedType.inputSize (next, c) + 1 := by
    simp [splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
      EncodedType.inputSize, EncodedType.sum]
  rw [splitWithTraceRunnerInstructions, EncodedType.inputSize_list_cons, hInit]
  let fuel : List splitWithTraceRunnerInstructionEncodedType.Carrier :=
    c.map (fun _ => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier))
  change
    splitWithInputEncodedType.inputSize (next, c) + 1 + 1 +
        (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
          fuel ≤
      3 * splitWithInputEncodedType.inputSize (next, c) + 6
  have hFuelLocal :
      (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize fuel =
        2 * c.length := by
    simpa [fuel] using hFuel
  rw [hFuelLocal]
  simp [splitWithInputEncodedType]
  omega

noncomputable def splitWithTraceRunnerInstructionsTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      (EncodedType.list splitWithTraceRunnerInstructionEncodedType)
      splitWithTraceRunnerInstructions where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithInputEncodedType)
      (Y := EncodedType.list splitWithTraceRunnerInstructionEncodedType)
      (LinearSizeBound.intro_with 3 6 (by
        intro p
        exact splitWithTraceRunnerInstructions_inputSize_le p))
  tm_polytime := by
    let X := splitWithInputEncodedType
    let Instr := splitWithTraceRunnerInstructionEncodedType
    have hInitInstr :
        TMPolyTimeMap X Instr (fun p : X.Carrier => Sum.inl p) :=
      TMPolyTimeMap.inl splitWithInputEncodedType splitWithTraceRunnerFuelEncodedType
    have hInitSingleton :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun p : X.Carrier => [Sum.inl p]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Instr) hInitInstr
    have hClause :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hFuelFromClause :
        TMPolyTimeMap clauseStructuredEncodedType (EncodedType.list Instr)
          (fun c : SAT.Clause => c.map (fun _ => Sum.inr ())) :=
      TMPolyTimeMap.list_const literalStructuredEncodedType Instr (Sum.inr ())
    have hFuel :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun p : X.Carrier => p.2.map (fun _ => Sum.inr ())) :=
      TMPolyTimeMap.comp hFuelFromClause hClause
    have hPair :
        TMPolyTimeMap X
          (EncodedType.prod (EncodedType.list Instr) (EncodedType.list Instr))
          (fun p : X.Carrier => ([Sum.inl p], p.2.map (fun _ => Sum.inr ()))) :=
      TMPolyTimeMap.prod_mk hInitSingleton (by
        simpa using hFuel)
    have hAppend :
        TMPolyTimeMap X (EncodedType.list Instr)
          ((fun p : List Instr.Carrier × List Instr.Carrier => p.1 ++ p.2) ∘
            fun p : X.Carrier => ([Sum.inl p], p.2.map (fun _ => Sum.inr ()))) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_append Instr) hPair
    have hAppend' :
        TMPolyTimeMap X (EncodedType.list Instr)
          (fun p : X.Carrier => [Sum.inl p] ++ p.2.map (fun _ => Sum.inr ())) := by
      simpa [Function.comp] using hAppend
    convert hAppend' using 1

def splitWithTraceRunnerInstructionsImageEncodedType : EncodedType where
  Carrier := splitWithInputEncodedType.Carrier
  Symbol := (EncodedType.list splitWithTraceRunnerInstructionEncodedType).Symbol
  finite_symbol := inferInstance
  encode := fun p =>
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).encode
      (splitWithTraceRunnerInstructions p)

noncomputable def splitWithTraceRunnerInstructionsImageTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      splitWithTraceRunnerInstructionsImageEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithInputEncodedType)
      (Y := splitWithTraceRunnerInstructionsImageEncodedType)
      (LinearSizeBound.intro_with 3 6 (by
        intro p
        change
          (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
              (splitWithTraceRunnerInstructions p) ≤
            3 * splitWithInputEncodedType.inputSize p + 6
        exact splitWithTraceRunnerInstructions_inputSize_le p))
  tm_polytime := by
    rcases splitWithTraceRunnerInstructionsTMBackedMap.tm_polytime with ⟨hInstr⟩
    refine ⟨?_⟩
    exact
      { tm := hInstr.tm
        inputAlphabet := hInstr.inputAlphabet
        outputAlphabet := hInstr.outputAlphabet
        time := hInstr.time
        outputsFun := by
          intro p
          simpa [splitWithTraceRunnerInstructionsImageEncodedType] using hInstr.outputsFun p }


end Karp21
end ComplexityReduction
