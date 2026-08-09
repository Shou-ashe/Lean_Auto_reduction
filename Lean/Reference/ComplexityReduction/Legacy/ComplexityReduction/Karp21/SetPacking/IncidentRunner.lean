/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.TMRoute

/-!
TM-backed incident-code runner for the compact Clique-to-Set-Packing route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SetPacking

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Instruction layer -/

def incidentCodePayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat codedComplementEdgeEncodedType

def incidentCodeInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool incidentCodePayloadEncodedType

def incidentCodeInstructionListEncodedType : EncodedType :=
  EncodedType.list incidentCodeInstructionEncodedType

def incidentCodeInstructionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat codedComplementEdgeListEncodedType

def incidentCodeAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def incidentCodeScanInputEncodedType : EncodedType :=
  EncodedType.prod incidentCodeAccEncodedType incidentCodeInstructionEncodedType

def incidentCodeDefaultCodedEdge : CodedComplementEdge :=
  (0, edgeScanDefaultPair)

def incidentCodeInitInstruction (v : Nat) : Bool × (Nat × CodedComplementEdge) :=
  (false, (v, incidentCodeDefaultCodedEdge))

def incidentCodeEdgeInstruction (ce : CodedComplementEdge) :
    Bool × (Nat × CodedComplementEdge) :=
  (true, (0, ce))

def incidentCodeInstructions (p : Nat × List CodedComplementEdge) :
    List (Bool × (Nat × CodedComplementEdge)) :=
  incidentCodeInitInstruction p.1 :: p.2.map incidentCodeEdgeInstruction

def incidentCodeScanInit : Nat × List Nat :=
  (0, [])

def incidentCodeScanStep
    (p : (Nat × List Nat) × (Bool × (Nat × CodedComplementEdge))) :
    Nat × List Nat :=
  if p.2.1 then
    let v := p.1.1
    let out := p.1.2
    let ce := p.2.2.2
    if codedEdgeIncidentBool (v, ce) then
      (v, out ++ [ce.1])
    else
      (v, out)
  else
    (p.2.2.1, [])

def incidentCodesFromInstructions
    (xs : List (Bool × (Nat × CodedComplementEdge))) : List Nat :=
  (xs.foldl (fun acc instr => incidentCodeScanStep (acc, instr)) incidentCodeScanInit).2

def incidentCodesFromInput (p : Nat × List CodedComplementEdge) : List Nat :=
  incidentCodesFromInstructions (incidentCodeInstructions p)

/-! ### Semantics -/

theorem incidentCodeEdgeInstructions_fold_eq
    (codedEdges : List CodedComplementEdge) (v : Nat) (out : List Nat) :
    (codedEdges.map incidentCodeEdgeInstruction).foldl
        (fun acc instr => incidentCodeScanStep (acc, instr)) (v, out) =
      (v,
        codedEdges.foldl
          (fun out ce => if codedEdgeIncidentBool (v, ce) then out ++ [ce.1] else out)
          out) := by
  induction codedEdges generalizing out with
  | nil =>
      simp
  | cons ce rest ih =>
      by_cases hIncident : codedEdgeIncidentBool (v, ce) = true
      · simp [incidentCodeEdgeInstruction, incidentCodeScanStep, hIncident]
        exact ih (out ++ [ce.1])
      · have hFalse : codedEdgeIncidentBool (v, ce) = false := by
          cases h : codedEdgeIncidentBool (v, ce)
          · rfl
          · exact False.elim (hIncident h)
        simp [incidentCodeEdgeInstruction, incidentCodeScanStep, hFalse]
        exact ih out

theorem incidentCodesFromInput_eq
    (v : Nat) (codedEdges : List CodedComplementEdge) :
    incidentCodesFromInput (v, codedEdges) = compactIncidentCodes v codedEdges := by
  change
    ((incidentCodeInitInstruction v :: codedEdges.map incidentCodeEdgeInstruction).foldl
      (fun acc instr => incidentCodeScanStep (acc, instr)) incidentCodeScanInit).2 =
      compactIncidentCodes v codedEdges
  rw [List.foldl_cons]
  simp [incidentCodeInitInstruction, incidentCodeScanStep, compactIncidentCodes]
  exact congrArg Prod.snd
    (incidentCodeEdgeInstructions_fold_eq codedEdges v ([] : List Nat))

/-! ### TM evidence -/

theorem codedEdgeIncidentBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat codedComplementEdgeEncodedType)
      EncodedType.bool
      codedEdgeIncidentBool := by
  classical
  let X := EncodedType.prod EncodedType.nat codedComplementEdgeEncodedType
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeEncodedType
  have hCE : TMPolyTimeMap X codedComplementEdgeEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeEncodedType
  have hEdge :
      TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat vertexPairEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCE
    simpa [Function.comp, codedComplementEdgeEncodedType, X] using hComp
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hEdge
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hEdge
    simpa [Function.comp, vertexPairEncodedType, X] using hComp
  have hLeftInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.1, p.1)) :=
    TMPolyTimeMap.prod_mk hLeft hV
  have hRightInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hV
  have hLeftEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => decide (p.2.2.1 = p.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hLeftInput
    convert hComp using 1
    funext p
    dsimp [Function.comp]
    exact Bool.decide_congr Iff.rfl
  have hRightEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => decide (p.2.2.2 = p.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRightInput
    convert hComp using 1
    funext p
    dsimp [Function.comp]
    exact Bool.decide_congr Iff.rfl
  have hBoth :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (decide (p.2.2.1 = p.1), decide (p.2.2.2 = p.1))) :=
    TMPolyTimeMap.prod_mk hLeftEq hRightEq
  have hOut := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hBoth
  convert hOut using 1
  funext p
  dsimp [Function.comp, codedEdgeIncidentBool]
  apply congrArg graphBoolOrPair
  apply Prod.ext
  · exact Bool.decide_congr Iff.rfl
  · exact Bool.decide_congr Iff.rfl

theorem incidentCodeEdgeInstruction_tm_polytime :
    TMPolyTimeMap
      codedComplementEdgeEncodedType
      incidentCodeInstructionEncodedType
      incidentCodeEdgeInstruction := by
  let X := codedComplementEdgeEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X incidentCodePayloadEncodedType
        (fun ce : X.Carrier => ((0 : Nat), ce)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [incidentCodeEdgeInstruction, incidentCodeInstructionEncodedType,
    incidentCodePayloadEncodedType, X] using hOut

theorem incidentCodeInstructions_tm_polytime :
    TMPolyTimeMap
      incidentCodeInstructionInputEncodedType
      incidentCodeInstructionListEncodedType
      incidentCodeInstructions := by
  let X := incidentCodeInstructionInputEncodedType
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, incidentCodeInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeListEncodedType
  have hCodedEdges :
      TMPolyTimeMap X codedComplementEdgeListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, incidentCodeInstructionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeListEncodedType
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hDefault :
      TMPolyTimeMap X codedComplementEdgeEncodedType
        (fun _ : X.Carrier => incidentCodeDefaultCodedEdge) :=
    TMPolyTimeMap.const X codedComplementEdgeEncodedType incidentCodeDefaultCodedEdge
  have hInitPayload :
      TMPolyTimeMap X incidentCodePayloadEncodedType
        (fun p : X.Carrier => (p.1, incidentCodeDefaultCodedEdge)) :=
    TMPolyTimeMap.prod_mk hVertex hDefault
  have hInitInstruction :
      TMPolyTimeMap X incidentCodeInstructionEncodedType
        (fun p : X.Carrier => incidentCodeInitInstruction p.1) := by
    have hPair := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [incidentCodeInitInstruction, incidentCodeInstructionEncodedType,
      incidentCodePayloadEncodedType] using hPair
  have hInitSingleton :
      TMPolyTimeMap X incidentCodeInstructionListEncodedType
        (fun p : X.Carrier => [incidentCodeInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton incidentCodeInstructionEncodedType) hInitInstruction
    simpa [Function.comp, incidentCodeInstructionListEncodedType] using hComp
  have hEdgeInstructions :
      TMPolyTimeMap X incidentCodeInstructionListEncodedType
        (fun p : X.Carrier => p.2.map incidentCodeEdgeInstruction) := by
    have hMap := TMPolyTimeMap.list_map incidentCodeEdgeInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCodedEdges
    simpa [Function.comp, incidentCodeInstructionListEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod incidentCodeInstructionListEncodedType
          incidentCodeInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([incidentCodeInitInstruction p.1], p.2.map incidentCodeEdgeInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hEdgeInstructions
  have hOut :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append incidentCodeInstructionEncodedType) hAppendInput
  simpa [Function.comp, incidentCodeInstructions, incidentCodeInstructionListEncodedType]
    using hOut

theorem incidentCodeScanStep_tm_polytime :
    TMPolyTimeMap
      incidentCodeScanInputEncodedType
      incidentCodeAccEncodedType
      incidentCodeScanStep := by
  let X := incidentCodeScanInputEncodedType
  let A := incidentCodeAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, incidentCodeScanInputEncodedType] using
      TMPolyTimeMap.fst incidentCodeAccEncodedType incidentCodeInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X incidentCodeInstructionEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, incidentCodeScanInputEncodedType] using
      TMPolyTimeMap.snd incidentCodeAccEncodedType incidentCodeInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool incidentCodePayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, incidentCodeInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X incidentCodePayloadEncodedType (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool incidentCodePayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, incidentCodeInstructionEncodedType, X] using hComp
  have hPayloadVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, incidentCodePayloadEncodedType, X] using hComp
  have hPayloadCodedEdge :
      TMPolyTimeMap X codedComplementEdgeEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat codedComplementEdgeEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, incidentCodePayloadEncodedType, X] using hComp
  have hEmpty : TMPolyTimeMap X setStructuredEncodedType (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X setStructuredEncodedType []
  have hInitOut : TMPolyTimeMap X A (fun p : X.Carrier => (p.2.2.1, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hPayloadVertex hEmpty
  have hAccVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, incidentCodeAccEncodedType, X] using hComp
  have hAccOut : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, incidentCodeAccEncodedType, X] using hComp
  have hCode : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat vertexPairEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayloadCodedEdge
    simpa [Function.comp, codedComplementEdgeEncodedType, X] using hComp
  have hSingleton :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => [p.2.2.2.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hCode
    simpa [Function.comp, setStructuredEncodedType] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : X.Carrier => (p.1.2, [p.2.2.2.1])) :=
    TMPolyTimeMap.prod_mk hAccOut hSingleton
  have hAppend :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier =>
          List.append (p.1.2 : List Nat) ([p.2.2.2.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, setStructuredEncodedType] using hComp
  have hHit : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1, List.append (p.1.2 : List Nat) ([p.2.2.2.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hAccVertex hAppend
  have hMiss : TMPolyTimeMap X A (fun p : X.Carrier => (p.1.1, p.1.2)) :=
    TMPolyTimeMap.prod_mk hAccVertex hAccOut
  have hIncidentInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat codedComplementEdgeEncodedType)
        (fun p : X.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccVertex hPayloadCodedEdge
  have hIncident :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => codedEdgeIncidentBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp codedEdgeIncidentBool_tm_polytime hIncidentInput
    simpa [Function.comp, X] using hComp
  have hIncidentBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (codedEdgeIncidentBool (p.1.1, p.2.2.2), p)) :=
    TMPolyTimeMap.prod_mk hIncident (TMPolyTimeMap.id X)
  have hIncidentBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              (p.2.1.1,
                List.append (p.2.1.2 : List Nat) ([p.2.2.2.2.1] : List Nat))
          | false => (p.2.1.1, p.2.1.2)) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.1.1, p.1.2))
      (fTrue := fun p : X.Carrier =>
        (p.1.1, List.append (p.1.2 : List Nat) ([p.2.2.2.1] : List Nat)))
      hMiss hHit
  have hScanOut : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        if codedEdgeIncidentBool (p.1.1, p.2.2.2) then
          (p.1.1, List.append (p.1.2 : List Nat) ([p.2.2.2.1] : List Nat))
        else (p.1.1, p.1.2)) := by
    have hComp := TMPolyTimeMap.comp hIncidentBranch hIncidentBranchInput
    convert hComp using 1
    funext p
    cases h : codedEdgeIncidentBool (p.1.1, p.2.2.2) <;> simp [Function.comp, h]
  have hTagBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hTagBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true =>
              if codedEdgeIncidentBool (p.2.1.1, p.2.2.2.2) then
                (p.2.1.1,
                  List.append (p.2.1.2 : List Nat) ([p.2.2.2.2.1] : List Nat))
              else (p.2.1.1, p.2.1.2)
          | false => (p.2.2.2.1, ([] : List Nat))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([] : List Nat)))
      (fTrue := fun p : X.Carrier =>
        if codedEdgeIncidentBool (p.1.1, p.2.2.2) then
          (p.1.1, List.append (p.1.2 : List Nat) ([p.2.2.2.1] : List Nat))
        else (p.1.1, p.1.2))
      hInitOut hScanOut
  have hOut := TMPolyTimeMap.comp hTagBranch hTagBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases acc with ⟨v, out⟩
  change Nat at v
  change List Nat at out
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadV, ce⟩
  cases tag <;> rfl

theorem incidentCodeScanStep_growth
    (source : incidentCodeInstructionListEncodedType.Carrier)
    (acc : incidentCodeAccEncodedType.Carrier)
    (instr : incidentCodeInstructionEncodedType.Carrier)
    (hInstr :
      incidentCodeInstructionEncodedType.inputSize instr ≤
        incidentCodeInstructionListEncodedType.inputSize source) :
    incidentCodeAccEncodedType.inputSize (incidentCodeScanStep (acc, instr)) ≤
      incidentCodeAccEncodedType.inputSize acc +
        (incidentCodeInstructionListEncodedType.inputSize source + 30) := by
  rcases acc with ⟨v, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadV, ce⟩
  rcases ce with ⟨code, edge⟩
  rcases edge with ⟨u, w⟩
  change Nat at v
  change List Nat at out
  change Nat at payloadV
  change Nat at code
  change Nat at u
  change Nat at w
  have hNilNat : EncodedType.nat.list.inputSize ([] : List Nat) = 0 := by
    exact EncodedType.inputSize_list_nil EncodedType.nat
  cases tag
  · have hPayloadV : payloadV ≤ incidentCodeInstructionListEncodedType.inputSize source := by
      simp [incidentCodeInstructionEncodedType, incidentCodePayloadEncodedType,
        codedComplementEdgeEncodedType, vertexPairEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr
      omega
    calc
      incidentCodeAccEncodedType.inputSize
          (incidentCodeScanStep ((v, out), (false, (payloadV, (code, (u, w)))))) =
        incidentCodeAccEncodedType.inputSize (payloadV, ([] : List Nat)) := by
          rfl
      _ ≤ incidentCodeAccEncodedType.inputSize (v, out) +
          (incidentCodeInstructionListEncodedType.inputSize source + 30) := by
          simp [incidentCodeAccEncodedType, setStructuredEncodedType,
            EncodedType.inputSize_prod, EncodedType.inputSize_nat]
          rw [hNilNat]
          omega
  · by_cases hIncident : codedEdgeIncidentBool (v, (code, (u, w))) = true
    · have hCode : code ≤ incidentCodeInstructionListEncodedType.inputSize source := by
        simp [incidentCodeInstructionEncodedType, incidentCodePayloadEncodedType,
          codedComplementEdgeEncodedType, vertexPairEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr
        omega
      have hSingletonSize :
          setStructuredEncodedType.inputSize ([code] : List Nat) = code + 2 := by
        change (EncodedType.list EncodedType.nat).inputSize (code :: ([] : List Nat)) =
          code + 2
        rw [EncodedType.inputSize_list_cons, hNilNat, EncodedType.inputSize_nat]
      calc
        incidentCodeAccEncodedType.inputSize
            (incidentCodeScanStep ((v, out), (true, (payloadV, (code, (u, w)))))) =
          incidentCodeAccEncodedType.inputSize (v, (out : List Nat) ++ [code]) := by
            simp [incidentCodeScanStep, hIncident]
            rfl
        _ ≤ incidentCodeAccEncodedType.inputSize (v, out) +
            (incidentCodeInstructionListEncodedType.inputSize source + 30) := by
            simp only [incidentCodeAccEncodedType, EncodedType.inputSize_prod]
            rw [show
              setStructuredEncodedType.inputSize ((out : List Nat) ++ [code]) =
                setStructuredEncodedType.inputSize out +
                  setStructuredEncodedType.inputSize ([code] : List Nat) by
                exact encodedList_inputSize_append_local EncodedType.nat out [code]]
            rw [hSingletonSize]
            omega
    · have hFalse : codedEdgeIncidentBool (v, (code, (u, w))) = false := by
        cases h : codedEdgeIncidentBool (v, (code, (u, w)))
        · rfl
        · exact False.elim (hIncident h)
      calc
        incidentCodeAccEncodedType.inputSize
            (incidentCodeScanStep ((v, out), (true, (payloadV, (code, (u, w)))))) =
          incidentCodeAccEncodedType.inputSize (v, out) := by
            simp [incidentCodeScanStep, hFalse]
            rfl
        _ ≤ incidentCodeAccEncodedType.inputSize (v, out) +
            (incidentCodeInstructionListEncodedType.inputSize source + 30) := by
            omega

theorem incidentCodeScanFold_tm_polytime :
    TMPolyTimeMap
      incidentCodeInstructionListEncodedType
      incidentCodeAccEncodedType
      (fun xs : List incidentCodeInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => incidentCodeScanStep (acc, instr))
          incidentCodeScanInit) := by
  rcases incidentCodeScanStep_tm_polytime with ⟨hStep⟩
  let base : Polynomial Nat := Polynomial.C 10
  let grow : Polynomial Nat := Polynomial.X + Polynomial.C 30
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      incidentCodeInstructionEncodedType incidentCodeAccEncodedType
      incidentCodeScanStep incidentCodeScanInit hStep base grow ?_ ?_
  · intro xs
    simp [base, incidentCodeScanInit, incidentCodeAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat]
    rw [show setStructuredEncodedType.inputSize ([] : List Nat) = 0 by
      change (EncodedType.list EncodedType.nat).inputSize ([] : List Nat) = 0
      exact EncodedType.inputSize_list_nil EncodedType.nat]
    norm_num
  · intro source acc instr hInstr
    have hInstr' :
        incidentCodeInstructionEncodedType.inputSize instr ≤
          incidentCodeInstructionListEncodedType.inputSize source := by
      simpa [incidentCodeInstructionListEncodedType] using hInstr
    have h := incidentCodeScanStep_growth source acc instr hInstr'
    simpa [incidentCodeInstructionListEncodedType, grow, Polynomial.eval_add] using h

theorem incidentCodesFromInstructions_tm_polytime :
    TMPolyTimeMap
      incidentCodeInstructionListEncodedType
      setStructuredEncodedType
      incidentCodesFromInstructions := by
  have hFold := incidentCodeScanFold_tm_polytime
  have hOut := TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, incidentCodesFromInstructions, incidentCodeAccEncodedType] using hComp

theorem incidentCodesFromInput_tm_polytime :
    TMPolyTimeMap
      incidentCodeInstructionInputEncodedType
      setStructuredEncodedType
      incidentCodesFromInput := by
  have hComp :=
    TMPolyTimeMap.comp incidentCodesFromInstructions_tm_polytime
      incidentCodeInstructions_tm_polytime
  simpa [Function.comp, incidentCodesFromInput] using hComp

theorem compactPackingSetFromCodes_tm_polytime :
    TMPolyTimeMap
      incidentCodeInstructionInputEncodedType
      setStructuredEncodedType
      (fun p : Nat × List CodedComplementEdge => compactPackingSetFromCodes p.1 p.2) := by
  let X := incidentCodeInstructionInputEncodedType
  have hVertex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, incidentCodeInstructionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat codedComplementEdgeListEncodedType
  have hVertexSingleton :
      TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => [p.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hVertex
    simpa [Function.comp, setStructuredEncodedType] using hComp
  have hIncident : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => incidentCodesFromInput p) :=
    incidentCodesFromInput_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : X.Carrier => ([p.1], incidentCodesFromInput p)) :=
    TMPolyTimeMap.prod_mk hVertexSingleton hIncident
  have hAppend :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => List.append ([p.1] : List Nat) (incidentCodesFromInput p)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp, setStructuredEncodedType] using hComp
  convert hAppend using 1
  funext p
  rcases p with ⟨v, codedEdges⟩
  rw [incidentCodesFromInput_eq]
  rfl

end SetPacking
end Karp21
end ComplexityReduction
