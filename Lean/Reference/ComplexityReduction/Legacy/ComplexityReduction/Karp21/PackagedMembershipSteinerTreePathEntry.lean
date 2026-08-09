/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreePath

/-!
Path-entry scans for faithful structured Steiner Tree certificates.

A path entry stores a terminal together with a vertex path.  For a fixed
Steiner path context `((selected, directed), (root, target))`, an entry is
accepted exactly when it names `target` and its path checker accepts.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

def steinerPathEntryEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)

abbrev SteinerPathEntry :=
  Nat × List Nat

def steinerPathEntryListEncodedType : EncodedType :=
  EncodedType.list steinerPathEntryEncodedType

def steinerPathEntryCheckInputEncodedType : EncodedType :=
  EncodedType.prod steinerPathContextEncodedType steinerPathEntryEncodedType

def steinerPathEntryCheckBool (p : SteinerPathContext × SteinerPathEntry) : Bool :=
  graphBoolAndPair
    (natEqBool (p.2.1, p.1.2.2), steinerPathBool (p.1, p.2.2))

theorem steinerPathEntryCheckBool_eq_true_iff
    (p : SteinerPathContext × SteinerPathEntry) :
    steinerPathEntryCheckBool p = true ↔
      p.2.1 = p.1.2.2 ∧ steinerPathBool (p.1, p.2.2) = true := by
  simp [steinerPathEntryCheckBool, graphBoolAndPair_eq_true_iff,
    natEqBool_eq_true_iff]

theorem steinerPathEntryCheckBool_tm_polytime :
    TMPolyTimeMap steinerPathEntryCheckInputEncodedType EncodedType.bool
      steinerPathEntryCheckBool := by
  let X := steinerPathEntryCheckInputEncodedType
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, steinerPathEntryCheckInputEncodedType] using
      TMPolyTimeMap.fst steinerPathContextEncodedType steinerPathEntryEncodedType
  have hEntry : TMPolyTimeMap X steinerPathEntryEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, steinerPathEntryCheckInputEncodedType] using
      TMPolyTimeMap.snd steinerPathContextEncodedType steinerPathEntryEncodedType
  have hRootTarget : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => p.1.2) := by
    let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
    have hSnd := TMPolyTimeMap.snd GraphCtx (EncodedType.prod EncodedType.nat EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, steinerPathContextEncodedType, GraphCtx, X] using hComp
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hRootTarget
    simpa [Function.comp, X] using hComp
  have hEntryTerminal : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hEntry
    simpa [Function.comp, steinerPathEntryEncodedType, X] using hComp
  have hEntryPath : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hEntry
    simpa [Function.comp, steinerPathEntryEncodedType, X] using hComp
  have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.2.1, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hEntryTerminal hTarget
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.2.1, p.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  have hPathInput : TMPolyTimeMap X steinerPathInputEncodedType
      (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCtx hEntryPath
  have hPath : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => steinerPathBool (p.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp steinerPathBool_tm_polytime hPathInput
    simpa [Function.comp, steinerPathInputEncodedType, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (natEqBool (p.2.1, p.1.2.2), steinerPathBool (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hEq hPath
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, steinerPathEntryCheckBool, X] using hAnd

/-! ### Generic existential scan over path entries -/

def pathEntryExistsInstructionEncodedType : EncodedType :=
  EncodedType.sum steinerPathContextEncodedType steinerPathEntryEncodedType

def pathEntryExistsInstructionListEncodedType : EncodedType :=
  EncodedType.list pathEntryExistsInstructionEncodedType

def pathEntryExistsInputEncodedType : EncodedType :=
  EncodedType.prod steinerPathContextEncodedType steinerPathEntryListEncodedType

def pathEntryExistsAccEncodedType : EncodedType :=
  EncodedType.prod steinerPathContextEncodedType EncodedType.bool

def pathEntryExistsInitInstruction
    (ctx : SteinerPathContext) : pathEntryExistsInstructionEncodedType.Carrier :=
  Sum.inl ctx

def pathEntryExistsElementInstruction
    (entry : SteinerPathEntry) : pathEntryExistsInstructionEncodedType.Carrier :=
  Sum.inr entry

def pathEntryExistsInstructions
    (p : SteinerPathContext × List SteinerPathEntry) :
    List pathEntryExistsInstructionEncodedType.Carrier :=
  pathEntryExistsInitInstruction p.1 :: p.2.map pathEntryExistsElementInstruction

def pathEntryExistsRunnerInit : pathEntryExistsAccEncodedType.Carrier :=
  ((((([] : List (Nat × Nat × Nat)), false), ((0 : Nat), (0 : Nat))) :
    SteinerPathContext), false)

def pathEntryExistsStep
    (p : pathEntryExistsAccEncodedType.Carrier × pathEntryExistsInstructionEncodedType.Carrier) :
    pathEntryExistsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl ctx => (ctx, false)
  | Sum.inr entry =>
      (p.1.1, graphBoolOrPair (p.1.2, steinerPathEntryCheckBool (p.1.1, entry)))

def pathEntryExistsFromInstructions
    (xs : List pathEntryExistsInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => pathEntryExistsStep (acc, instr)) pathEntryExistsRunnerInit).2

def pathEntryExistsBool (p : SteinerPathContext × List SteinerPathEntry) : Bool :=
  pathEntryExistsFromInstructions (pathEntryExistsInstructions p)

theorem pathEntryExistsElementInstructions_fold_eq_true_iff
    (ctx : SteinerPathContext) (found : Bool) (entries : List SteinerPathEntry) :
    ((entries.map pathEntryExistsElementInstruction).foldl
        (fun acc instr => pathEntryExistsStep (acc, instr)) (ctx, found)).2 = true ↔
      found = true ∨ ∃ entry ∈ entries, steinerPathEntryCheckBool (ctx, entry) = true := by
  induction entries generalizing found with
  | nil =>
      cases found <;> simp
  | cons entry rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        ((rest.map pathEntryExistsElementInstruction).foldl
            (fun acc instr => pathEntryExistsStep (acc, instr))
            (ctx, graphBoolOrPair (found, steinerPathEntryCheckBool (ctx, entry)))).2 = true ↔
          found = true ∨ ∃ x ∈ entry :: rest, steinerPathEntryCheckBool (ctx, x) = true
      rw [ih]
      constructor
      · intro h
        rcases h with hHead | hTail
        · rcases (graphBoolOrPair_eq_true_iff
              (found, steinerPathEntryCheckBool (ctx, entry))).1 hHead with hFound | hPred
          · exact Or.inl hFound
          · exact Or.inr ⟨entry, by simp, hPred⟩
        · rcases hTail with ⟨x, hx, hxPred⟩
          exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxPred⟩
      · intro h
        rcases h with hFound | h
        · left
          exact (graphBoolOrPair_eq_true_iff
            (found, steinerPathEntryCheckBool (ctx, entry))).2 (Or.inl hFound)
        · rcases h with ⟨x, hx, hxPred⟩
          rcases List.mem_cons.mp hx with hxHead | hxRest
          · left
            subst x
            exact (graphBoolOrPair_eq_true_iff
              (found, steinerPathEntryCheckBool (ctx, entry))).2 (Or.inr hxPred)
          · right
            exact ⟨x, hxRest, hxPred⟩

theorem pathEntryExistsBool_eq_true_iff
    (p : SteinerPathContext × List SteinerPathEntry) :
    pathEntryExistsBool p = true ↔
      ∃ entry ∈ p.2, steinerPathEntryCheckBool (p.1, entry) = true := by
  rcases p with ⟨ctx, entries⟩
  change
    (((pathEntryExistsInitInstruction ctx ::
          entries.map pathEntryExistsElementInstruction).foldl
        (fun acc instr => pathEntryExistsStep (acc, instr))
        pathEntryExistsRunnerInit).2 = true) ↔
      ∃ entry ∈ entries, steinerPathEntryCheckBool (ctx, entry) = true
  rw [List.foldl_cons]
  simpa [pathEntryExistsRunnerInit, pathEntryExistsInitInstruction,
    pathEntryExistsStep] using
    pathEntryExistsElementInstructions_fold_eq_true_iff ctx false entries

theorem pathEntryExistsInitInstruction_tm_polytime :
    TMPolyTimeMap steinerPathContextEncodedType pathEntryExistsInstructionEncodedType
      pathEntryExistsInitInstruction := by
  simpa [pathEntryExistsInitInstruction, pathEntryExistsInstructionEncodedType] using
    TMPolyTimeMap.inl steinerPathContextEncodedType steinerPathEntryEncodedType

theorem pathEntryExistsElementInstruction_tm_polytime :
    TMPolyTimeMap steinerPathEntryEncodedType pathEntryExistsInstructionEncodedType
      pathEntryExistsElementInstruction := by
  simpa [pathEntryExistsElementInstruction, pathEntryExistsInstructionEncodedType] using
    TMPolyTimeMap.inr steinerPathContextEncodedType steinerPathEntryEncodedType

theorem pathEntryExistsInstructions_tm_polytime :
    TMPolyTimeMap pathEntryExistsInputEncodedType
      pathEntryExistsInstructionListEncodedType pathEntryExistsInstructions := by
  let X := pathEntryExistsInputEncodedType
  have hCtx : TMPolyTimeMap X steinerPathContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, pathEntryExistsInputEncodedType] using
      TMPolyTimeMap.fst steinerPathContextEncodedType steinerPathEntryListEncodedType
  have hEntries :
      TMPolyTimeMap X steinerPathEntryListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, pathEntryExistsInputEncodedType] using
      TMPolyTimeMap.snd steinerPathContextEncodedType steinerPathEntryListEncodedType
  have hInit :
      TMPolyTimeMap X pathEntryExistsInstructionEncodedType
        (fun p : X.Carrier => pathEntryExistsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp pathEntryExistsInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X pathEntryExistsInstructionListEncodedType
        (fun p : X.Carrier => [pathEntryExistsInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton pathEntryExistsInstructionEncodedType)
        hInit
    simpa [Function.comp, pathEntryExistsInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X pathEntryExistsInstructionListEncodedType
        (fun p : X.Carrier => p.2.map pathEntryExistsElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map pathEntryExistsElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEntries
    simpa [Function.comp, pathEntryExistsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod pathEntryExistsInstructionListEncodedType
          pathEntryExistsInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([pathEntryExistsInitInstruction p.1], p.2.map pathEntryExistsElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append pathEntryExistsInstructionEncodedType) hAppendInput
  simpa [Function.comp, pathEntryExistsInstructions, pathEntryExistsInstructionListEncodedType,
    X] using hOut

theorem pathEntryExistsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod pathEntryExistsAccEncodedType pathEntryExistsInstructionEncodedType)
      pathEntryExistsAccEncodedType
      pathEntryExistsStep := by
  let Instr := pathEntryExistsInstructionEncodedType
  let A := pathEntryExistsAccEncodedType
  let C := steinerPathContextEncodedType
  let E := steinerPathEntryEncodedType
  let X := EncodedType.prod A Instr
  have hFalse : TMPolyTimeMap C A (fun ctx : C.Carrier => (ctx, false)) := by
    have hId := TMPolyTimeMap.id C
    have hConst : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => false) :=
      TMPolyTimeMap.const C EncodedType.bool false
    have hOut := TMPolyTimeMap.prod_mk hId hConst
    simpa [A, C, pathEntryExistsAccEncodedType] using hOut
  have hTrue : TMPolyTimeMap
      (EncodedType.prod A E) A
      (fun p : A.Carrier × E.Carrier =>
        (p.1.1, graphBoolOrPair (p.1.2, steinerPathEntryCheckBool (p.1.1, p.2)))) := by
    let Y := EncodedType.prod A E
    have hA : TMPolyTimeMap Y A (fun p : Y.Carrier => p.1) := by
      simpa [Y] using TMPolyTimeMap.fst A E
    have hC : TMPolyTimeMap Y C (fun p : Y.Carrier => p.1.1) := by
      have hFst := TMPolyTimeMap.fst C EncodedType.bool
      have hComp := TMPolyTimeMap.comp hFst hA
      simpa [Function.comp, A, C, pathEntryExistsAccEncodedType, Y] using hComp
    have hB : TMPolyTimeMap Y EncodedType.bool (fun p : Y.Carrier => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd C EncodedType.bool
      have hComp := TMPolyTimeMap.comp hSnd hA
      simpa [Function.comp, A, C, pathEntryExistsAccEncodedType, Y] using hComp
    have hE : TMPolyTimeMap Y E (fun p : Y.Carrier => p.2) := by
      simpa [Y] using TMPolyTimeMap.snd A E
    have hPInput :
        TMPolyTimeMap Y steinerPathEntryCheckInputEncodedType
          (fun p : Y.Carrier => (p.1.1, p.2)) :=
      TMPolyTimeMap.prod_mk hC hE
    have hP : TMPolyTimeMap Y EncodedType.bool
        (fun p : Y.Carrier => steinerPathEntryCheckBool (p.1.1, p.2)) := by
      have hComp := TMPolyTimeMap.comp steinerPathEntryCheckBool_tm_polytime hPInput
      simpa [Function.comp, steinerPathEntryCheckInputEncodedType, Y] using hComp
    have hOI : TMPolyTimeMap Y (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Y.Carrier => (p.1.2, steinerPathEntryCheckBool (p.1.1, p.2))) :=
      TMPolyTimeMap.prod_mk hB hP
    have hO : TMPolyTimeMap Y EncodedType.bool
        (fun p : Y.Carrier =>
          graphBoolOrPair (p.1.2, steinerPathEntryCheckBool (p.1.1, p.2))) := by
      have hComp := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOI
      simpa [Function.comp, Y] using hComp
    have hOut := TMPolyTimeMap.prod_mk hC hO
    simpa [Y, A, C, E, pathEntryExistsAccEncodedType] using hOut
  have hStepSum :
      TMPolyTimeMap
        (EncodedType.prod A Instr)
        A
        (fun p : A.Carrier × Instr.Carrier =>
          match p.2 with
          | Sum.inl ctx => (ctx, false)
          | Sum.inr entry =>
              (p.1.1,
                graphBoolOrPair
                  (p.1.2, steinerPathEntryCheckBool (p.1.1, entry)))) := by
    have hChoice := Partition.prodSumChoice_tm_polytime A C E
    have hBranches := Partition.TMPolyTimeMap.sum_elim hFalse hTrue
    have hComp := TMPolyTimeMap.comp hBranches hChoice
    convert hComp using 1
    funext p
    rcases p with ⟨acc, instr⟩
    cases instr <;> rfl
  simpa [pathEntryExistsStep, A, C, E, Instr, X] using hStepSum

theorem pathEntryExistsStep_inputSize_le
    (K : Nat) (hK : 10 ≤ K)
    (source : pathEntryExistsInstructionListEncodedType.Carrier)
    (acc : pathEntryExistsAccEncodedType.Carrier)
    (instr : pathEntryExistsInstructionEncodedType.Carrier)
    (hAcc :
      pathEntryExistsAccEncodedType.inputSize acc ≤
        pathEntryExistsInstructionListEncodedType.inputSize source + K)
    (hInstr :
      pathEntryExistsInstructionEncodedType.inputSize instr ≤
        pathEntryExistsInstructionListEncodedType.inputSize source) :
    pathEntryExistsAccEncodedType.inputSize (pathEntryExistsStep (acc, instr)) ≤
      pathEntryExistsInstructionListEncodedType.inputSize source + K := by
  rcases acc with ⟨ctx, found⟩
  cases instr with
  | inl newCtx =>
      have hLocal :
          pathEntryExistsAccEncodedType.inputSize (newCtx, false) ≤
            pathEntryExistsInstructionEncodedType.inputSize (Sum.inl newCtx) + 10 := by
        simp [pathEntryExistsAccEncodedType, pathEntryExistsInstructionEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.sum, EncodedType.bool]
      have hSource : pathEntryExistsInstructionEncodedType.inputSize (Sum.inl newCtx) + 10 ≤
          pathEntryExistsInstructionListEncodedType.inputSize source + K := by
        omega
      exact hLocal.trans hSource
  | inr entry =>
      have hLocal :
          pathEntryExistsAccEncodedType.inputSize
              (ctx, graphBoolOrPair (found, steinerPathEntryCheckBool (ctx, entry))) ≤
            pathEntryExistsAccEncodedType.inputSize (ctx, found) := by
        cases found <;> cases steinerPathEntryCheckBool (ctx, entry) <;>
          simp [pathEntryExistsAccEncodedType, EncodedType.inputSize,
            EncodedType.prod, EncodedType.bool, graphBoolOrPair]
      exact hLocal.trans hAcc

theorem pathEntryExistsFold_tm_polytime :
    TMPolyTimeMap
      pathEntryExistsInstructionListEncodedType
      pathEntryExistsAccEncodedType
      (fun xs : pathEntryExistsInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => pathEntryExistsStep (acc, instr))
          pathEntryExistsRunnerInit) := by
  rcases pathEntryExistsStep_tm_polytime with ⟨hStep⟩
  let K : Nat := pathEntryExistsAccEncodedType.inputSize pathEntryExistsRunnerInit + 10
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C K
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      pathEntryExistsInstructionEncodedType
      pathEntryExistsAccEncodedType
      pathEntryExistsStep pathEntryExistsRunnerInit hStep bound ?_ ?_
  · intro xs
    change pathEntryExistsAccEncodedType.inputSize pathEntryExistsRunnerInit ≤
      (Polynomial.X + Polynomial.C K).eval
        (pathEntryExistsInstructionEncodedType.list.inputSize xs)
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        pathEntryExistsAccEncodedType.inputSize acc ≤
          pathEntryExistsInstructionListEncodedType.inputSize source + K := by
      simpa [pathEntryExistsInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        pathEntryExistsInstructionEncodedType.inputSize instr ≤
          pathEntryExistsInstructionListEncodedType.inputSize source := by
      simpa [pathEntryExistsInstructionListEncodedType] using hInstr
    simpa [pathEntryExistsInstructionListEncodedType, bound, Polynomial.eval_add] using
      pathEntryExistsStep_inputSize_le K (by omega) source acc instr hAcc' hInstr'

theorem pathEntryExistsFromInstructions_tm_polytime :
    TMPolyTimeMap
      pathEntryExistsInstructionListEncodedType
      EncodedType.bool
      pathEntryExistsFromInstructions := by
  have hFold := pathEntryExistsFold_tm_polytime
  have hOut := TMPolyTimeMap.snd steinerPathContextEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, pathEntryExistsFromInstructions, pathEntryExistsAccEncodedType]
    using hComp

theorem pathEntryExistsBool_tm_polytime :
    TMPolyTimeMap pathEntryExistsInputEncodedType EncodedType.bool
      pathEntryExistsBool := by
  have hComp := TMPolyTimeMap.comp
    pathEntryExistsFromInstructions_tm_polytime
    pathEntryExistsInstructions_tm_polytime
  simpa [Function.comp, pathEntryExistsBool] using hComp

end SteinerTreeMembership

end Karp21
end ComplexityReduction
