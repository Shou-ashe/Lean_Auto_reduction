/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.TextbookMap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Domain.Core.GraphColoringIR
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Standard-axiom direct-TM reconstruction for the reusable structured
3SAT-to-GraphColoring clause gadget.  The CR clause-prefix runner's only
nonstandard dependency is a closed initial-size calculation; this leaf
rebuilds that theorem with kernel reduction and threads it into the exact
per-clause edge executable.
-/

namespace ComplexityReduction
namespace Domain
namespace ThreeSATToGraphColoringStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ChromaticNumber
open ComplexityReduction.Combinatorics.Graph
open Certificate Encoding Program

/-- Kernel-audited direct-TM realization of the clause-prefix fold. -/
theorem clausePrefixFromClause_tmPolyTime :
    TMPolyTimeMap
      clauseStructuredEncodedType
      clausePrefixStateEncodedType
      clausePrefixFromClause := by
  rcases clausePrefixStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      literalStructuredEncodedType clausePrefixStateEncodedType
      clausePrefixStep clausePrefixInit hStep
      (Polynomial.C 100) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro source
    simpa using
      (show clausePrefixStateEncodedType.inputSize clausePrefixInit ≤ (100 : Nat) by
        decide)
  · intro source acc lit hlit
    exact clausePrefixStep_growth source acc lit hlit

/-- Standard direct-TM realization of the prefix-carrying per-clause input. -/
theorem clauseEdgesForPrefixInputOfInput_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesForInputEncodedType
      clauseEdgesForPrefixInputEncodedType
      clauseEdgesForPrefixInputOfInput := by
  let X := clauseEdgesForInputEncodedType
  let Tail := EncodedType.prod EncodedType.nat clauseStructuredEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForInput => p.1) := by
    simpa [X, clauseEdgesForInputEncodedType, Tail, ClauseEdgesForInput] using
      TMPolyTimeMap.fst EncodedType.nat Tail
  have hTail : TMPolyTimeMap X Tail
      (fun p : ClauseEdgesForInput => p.2) := by
    simpa [X, clauseEdgesForInputEncodedType, Tail, ClauseEdgesForInput] using
      TMPolyTimeMap.snd EncodedType.nat Tail
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesForInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForInput] using hComp
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ClauseEdgesForInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X, Tail, ClauseEdgesForInput] using hComp
  have hPrefix : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseEdgesForInput => clausePrefixFromClause p.2.2) := by
    have hComp := TMPolyTimeMap.comp clausePrefixFromClause_tmPolyTime hClause
    simpa [Function.comp, X] using hComp
  have hJPrefix :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat clausePrefixStateEncodedType)
        (fun p : ClauseEdgesForInput => (p.2.1, clausePrefixFromClause p.2.2)) :=
    TMPolyTimeMap.prod_mk hJ hPrefix
  have hOut :
      TMPolyTimeMap X clauseEdgesForPrefixInputEncodedType
        (fun p : ClauseEdgesForInput =>
          (p.1, (p.2.1, clausePrefixFromClause p.2.2))) :=
    TMPolyTimeMap.prod_mk hN hJPrefix
  simpa [clauseEdgesForPrefixInputOfInput, X, clauseEdgesForPrefixInputEncodedType,
    clauseEdgesForInputEncodedType, ClauseEdgesForInput, ClauseEdgesForPrefixInput] using hOut

/-- Standard direct-TM realization of the exact per-clause textbook edge list. -/
theorem clauseEdgesFor_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesForInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesForFromInput := by
  have hComp :=
    TMPolyTimeMap.comp clauseEdgesForFromPrefix_tm_polytime
      clauseEdgesForPrefixInputOfInput_tmPolyTime
  convert hComp using 1
  funext p
  simp [Function.comp, clauseEdgesForFromInput, clauseEdgesForPrefixInputOfInput,
    clauseEdgesForFromPrefix_eq_clauseEdgesFor]

/-- Standard direct-TM realization of one bounded clause-list fold step. -/
theorem clauseEdgesFromStep_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromStepInputEncodedType
      clauseEdgesFromAccEncodedType
      clauseEdgesFromStep := by
  let X := clauseEdgesFromStepInputEncodedType
  let AccTail := EncodedType.prod EncodedType.nat edgeListStructuredEncodedType
  have hAcc : TMPolyTimeMap X clauseEdgesFromAccEncodedType
      (fun p : ClauseEdgesFromStepInput => p.1) := by
    simpa [X, clauseEdgesFromStepInputEncodedType] using
      TMPolyTimeMap.fst clauseEdgesFromAccEncodedType clauseEdgesFromInstructionEncodedType
  have hInstr : TMPolyTimeMap X clauseEdgesFromInstructionEncodedType
      (fun p : ClauseEdgesFromStepInput => p.2) := by
    simpa [X, clauseEdgesFromStepInputEncodedType] using
      TMPolyTimeMap.snd clauseEdgesFromAccEncodedType clauseEdgesFromInstructionEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesFromStepInput => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat AccTail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, clauseEdgesFromAccEncodedType, AccTail, X,
      ClauseEdgesFromStepInput] using hComp
  have hAccTail : TMPolyTimeMap X AccTail
      (fun p : ClauseEdgesFromStepInput => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat AccTail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, clauseEdgesFromAccEncodedType, AccTail, X,
      ClauseEdgesFromStepInput] using hComp
  have hJ : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesFromStepInput => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, AccTail, X, ClauseEdgesFromStepInput] using hComp
  have hOut : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : ClauseEdgesFromStepInput => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, AccTail, X, ClauseEdgesFromStepInput] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : ClauseEdgesFromStepInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool clauseEdgesFromInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, clauseEdgesFromInstructionEncodedType, X,
      ClauseEdgesFromStepInput] using hComp
  have hPayload : TMPolyTimeMap X clauseEdgesFromInstructionPayloadEncodedType
      (fun p : ClauseEdgesFromStepInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool clauseEdgesFromInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, clauseEdgesFromInstructionEncodedType, X,
      ClauseEdgesFromStepInput] using hComp
  have hInitN : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesFromStepInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, clauseEdgesFromInstructionPayloadEncodedType, X,
      ClauseEdgesFromStepInput] using hComp
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ClauseEdgesFromStepInput => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, clauseEdgesFromInstructionPayloadEncodedType, X,
      ClauseEdgesFromStepInput] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : ClauseEdgesFromStepInput => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEmpty : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun _ : ClauseEdgesFromStepInput => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hFalseBranch :
      TMPolyTimeMap X clauseEdgesFromAccEncodedType
        (fun p : ClauseEdgesFromStepInput =>
          (p.2.2.1, ((0 : Nat), ([] : List (Nat × Nat))))) :=
    clauseEdgesFromAcc_mk_tm_polytime hInitN hZero hEmpty
  have hSuccJ : TMPolyTimeMap X EncodedType.nat
      (fun p : ClauseEdgesFromStepInput => p.1.2.1 + 1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hJ
    simpa [Function.comp, Nat.succ_eq_add_one] using hComp
  have hClauseEdgesInput :
      TMPolyTimeMap X clauseEdgesForInputEncodedType
        (fun p : ClauseEdgesFromStepInput => (p.1.1, (p.1.2.1, p.2.2.2))) := by
    have hJClause :
        TMPolyTimeMap X
          (EncodedType.prod EncodedType.nat clauseStructuredEncodedType)
          (fun p : ClauseEdgesFromStepInput => (p.1.2.1, p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hJ hClause
    simpa [clauseEdgesForInputEncodedType] using TMPolyTimeMap.prod_mk hN hJClause
  have hClauseEdges : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : ClauseEdgesFromStepInput =>
        clauseEdgesForFromInput (p.1.1, (p.1.2.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp clauseEdgesFor_tmPolyTime hClauseEdgesInput
    simpa [Function.comp, X, ClauseEdgesFromStepInput] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : ClauseEdgesFromStepInput =>
          (p.1.2.2, clauseEdgesForFromInput (p.1.1, (p.1.2.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hOut hClauseEdges
  have hAppend : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun p : ClauseEdgesFromStepInput =>
        p.1.2.2 ++ clauseEdgesForFromInput (p.1.1, (p.1.2.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append edgeStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X, ClauseEdgesFromStepInput] using hComp
  have hTrueBranch :
      TMPolyTimeMap X clauseEdgesFromAccEncodedType
        (fun p : ClauseEdgesFromStepInput =>
          (p.1.1,
            (p.1.2.1 + 1,
              p.1.2.2 ++ clauseEdgesForFromInput (p.1.1, (p.1.2.1, p.2.2.2))))) :=
    clauseEdgesFromAcc_mk_tm_polytime hN hSuccJ hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ClauseEdgesFromStepInput => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) clauseEdgesFromAccEncodedType
        (fun p : Bool × ClauseEdgesFromStepInput =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (p.2.1.2.1 + 1,
                  p.2.1.2.2 ++
                    clauseEdgesForFromInput (p.2.1.1, (p.2.1.2.1, p.2.2.2.2))))
          | false => (p.2.2.2.1, ((0 : Nat), ([] : List (Nat × Nat))))) :=
    Clique.boolProduct_dispatch_tm_polytime X clauseEdgesFromAccEncodedType
      (fFalse := fun p : ClauseEdgesFromStepInput =>
        (p.2.2.1, ((0 : Nat), ([] : List (Nat × Nat)))))
      (fTrue := fun p : ClauseEdgesFromStepInput =>
        (p.1.1,
          (p.1.2.1 + 1,
            p.1.2.2 ++ clauseEdgesForFromInput (p.1.1, (p.1.2.1, p.2.2.2)))))
      hFalseBranch hTrueBranch
  have hOutMap := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOutMap using 1
  funext p
  rcases p with ⟨⟨n, j, out⟩, ⟨tag, initN, c⟩⟩
  cases tag <;> rfl

/-- Standard direct-TM realization of the bounded clause-list fold. -/
theorem clauseEdgesFromInstructionsFold_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromInstructionListEncodedType
      clauseEdgesFromAccEncodedType
      clauseEdgesFromInstructionsFold := by
  rcases clauseEdgesFromStep_tmPolyTime with ⟨hStep⟩
  let time := clauseEdgesFromFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
      clauseEdgesFromStep clauseEdgesFromInitAcc hStep time ?_
  intro source
  let N := clauseEdgesFromInstructionListEncodedType.inputSize source
  let B := clauseEdgesFromFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      Clique.encodedList_length_le_inputSize clauseEdgesFromInstructionEncodedType source
    simpa [N, clauseEdgesFromInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List ClauseEdgesFromInstruction),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
              clauseEdgesFromStep hStep
              (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                clauseEdgesFromInitAcc)
              rest ≤
            C * (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          exact List.mem_append_right pref (by simp)
        have hxN : clauseEdgesFromInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            Clique.encodedList_element_inputSize_le
              (X := clauseEdgesFromInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, clauseEdgesFromInstructionListEncodedType] using hElem
        have hPrefixSize : clauseEdgesFromInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              clauseEdgesFromInstructionListEncodedType.inputSize source =
                clauseEdgesFromInstructionListEncodedType.inputSize pref +
                  clauseEdgesFromInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            simpa [clauseEdgesFromInstructionListEncodedType] using
              Clique.encodedList_inputSize_append clauseEdgesFromInstructionEncodedType
                pref (x :: xs)
          omega
        have hPrefixBound :=
          clauseEdgesFromFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            Clique.encodedList_length_le_inputSize clauseEdgesFromInstructionEncodedType pref
          have hLen' :
              pref.length ≤ clauseEdgesFromInstructionListEncodedType.inputSize pref := by
            simpa [clauseEdgesFromInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            clauseEdgesFromAccEncodedType.inputSize
                (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                  clauseEdgesFromInitAcc) ≤ B := by
          simpa [B] using
            clauseEdgesFromAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hTailNonempty : pref.length + 1 ≤ (pref ++ (x :: xs)).length := by
            induction pref with
            | nil => simp
            | cons y ys ih => simp
          have hSourceEq : source.length = (pref ++ (x :: xs)).length :=
            congrArg List.length hEq
          omega
        have hStepBound :=
          clauseEdgesFromStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            clauseEdgesFromAccEncodedType.inputSize
                (clauseEdgesFromStep
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x)) ≤ B := by
          simpa [B] using
            clauseEdgesFromAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod clauseEdgesFromAccEncodedType
                  clauseEdgesFromInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod clauseEdgesFromAccEncodedType
                clauseEdgesFromInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              clauseEdgesFromAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                      clauseEdgesFromInitAcc) +
                  1 + clauseEdgesFromInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (clauseEdgesFromInstructionEncodedType.encode x).length
                (clauseEdgesFromAccEncodedType.encode
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc)).length
                (clauseEdgesFromAccEncodedType.encode
                  (clauseEdgesFromStep
                    (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                      clauseEdgesFromInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod clauseEdgesFromAccEncodedType
                    clauseEdgesFromInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                      clauseEdgesFromInitAcc, x))) ≤
              C * (clauseEdgesFromInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [x]) ++ xs := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [x]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
                clauseEdgesFromStep hStep
                (clauseEdgesFromStep
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x)) xs ≤
              C * (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => clauseEdgesFromStep (acc, instr))
                  clauseEdgesFromInitAcc =
                clauseEdgesFromStep
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc instr => clauseEdgesFromStep (acc, instr))
                clauseEdgesFromInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
                clauseEdgesFromStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
              clauseEdgesFromStep hStep
              (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                clauseEdgesFromInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
                clauseEdgesFromStep hStep
                (clauseEdgesFromStep
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (clauseEdgesFromInstructionEncodedType.encode x).length
                (clauseEdgesFromAccEncodedType.encode
                  (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                    clauseEdgesFromInitAcc)).length
                (clauseEdgesFromAccEncodedType.encode
                  (clauseEdgesFromStep
                    (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                      clauseEdgesFromInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod clauseEdgesFromAccEncodedType
                    clauseEdgesFromInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
                      clauseEdgesFromInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize xs +
                C * (clauseEdgesFromInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤
              C * (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
                (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
          clauseEdgesFromStep hStep clauseEdgesFromInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, clauseEdgesFromInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, clauseEdgesFromFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        clauseEdgesFromInstructionEncodedType clauseEdgesFromAccEncodedType
        clauseEdgesFromStep hStep clauseEdgesFromInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

/-- Standard direct-TM realization of clause-list output projection. -/
theorem clauseEdgesFromFromInstructions_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromInstructionListEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromFromInstructions := by
  have hFold := clauseEdgesFromInstructionsFold_tmPolyTime
  let AccTail := EncodedType.prod EncodedType.nat edgeListStructuredEncodedType
  have hTail :
      TMPolyTimeMap clauseEdgesFromAccEncodedType AccTail
        (fun acc : ClauseEdgesFromAcc => acc.2) := by
    simpa [clauseEdgesFromAccEncodedType, AccTail, ClauseEdgesFromAcc] using
      TMPolyTimeMap.snd EncodedType.nat AccTail
  have hOut :
      TMPolyTimeMap AccTail edgeListStructuredEncodedType
        (fun tail : Nat × List (Nat × Nat) => tail.2) := by
    simpa [AccTail] using TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hProj := TMPolyTimeMap.comp hOut (TMPolyTimeMap.comp hTail hFold)
  simpa [Function.comp, clauseEdgesFromFromInstructions, clauseEdgesFromInstructionsFold,
    AccTail] using hProj

/-- Standard direct-TM realization of the complete clause edge runner. -/
theorem clauseEdgesFromRunner_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromRunner := by
  have hComp :=
    TMPolyTimeMap.comp clauseEdgesFromFromInstructions_tmPolyTime
      clauseEdgesFromInstructions_tm_polytime
  simpa [Function.comp, clauseEdgesFromRunner] using hComp

/-- Standard direct-TM realization of the semantic clause-edge computation. -/
theorem clauseEdgesFrom_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromFromInput := by
  convert clauseEdgesFromRunner_tmPolyTime using 1
  funext p
  exact (clauseEdgesFromRunner_eq_clauseEdgesFrom p).symm

/-- Standard direct-TM realization of the full textbook edge assembly. -/
theorem textbookEdgesForInput_tmPolyTime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      textbookEdgesForInput := by
  let X := clauseEdgesFromInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ClauseEdgesFromInput => p.1) := by
    simpa [X, clauseEdgesFromInputEncodedType, ClauseEdgesFromInput] using
      TMPolyTimeMap.fst EncodedType.nat cnfStructuredEncodedType
  have hPalette :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : ClauseEdgesFromInput => paletteEdges) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType paletteEdges
  have hVariable :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : ClauseEdgesFromInput => variableEdges p.1) := by
    have hComp := TMPolyTimeMap.comp variableEdges_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hPVInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : ClauseEdgesFromInput => (paletteEdges, variableEdges p.1)) :=
    TMPolyTimeMap.prod_mk hPalette hVariable
  have hPV :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : ClauseEdgesFromInput => paletteEdges ++ variableEdges p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hPVInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hClause : TMPolyTimeMap X edgeListStructuredEncodedType clauseEdgesFromFromInput := by
    simpa [X] using clauseEdgesFrom_tmPolyTime
  have hAllInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : ClauseEdgesFromInput =>
          (paletteEdges ++ variableEdges p.1, clauseEdgesFromFromInput p)) :=
    TMPolyTimeMap.prod_mk hPV hClause
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAllInput
  simpa [Function.comp, textbookEdgesForInput, edgeListStructuredEncodedType, X] using hAll

/-- The bounded source clauses presented to the standard textbook edge assembly. -/
def threeSATBoundedClauseInput (φ : SAT.ThreeCNF) : ClauseEdgesFromInput :=
  (threeCNFStructuredEncodedType.inputSize φ, φ.clauses)

/-- Direct-TM evidence for the bounded source-clause pairing. -/
theorem threeSATBoundedClauseInput_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      clauseEdgesFromInputEncodedType
      threeSATBoundedClauseInput := by
  have hBound :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hPair := TMPolyTimeMap.prod_mk hBound threeCNFClauses_tm_polytime
  simpa [threeSATBoundedClauseInput, clauseEdgesFromInputEncodedType] using hPair

/-- The standard textbook edge list for a complete structured 3SAT input. -/
def threeSATTextbookEdgesTM (φ : SAT.ThreeCNF) : List (Nat × Nat) :=
  textbookEdgesForInput (threeSATBoundedClauseInput φ)

/-- Direct-TM evidence for the standard textbook edge list. -/
theorem threeSATTextbookEdgesTM_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      edgeListStructuredEncodedType
      threeSATTextbookEdgesTM := by
  have hComp :=
    TMPolyTimeMap.comp textbookEdgesForInput_tmPolyTime threeSATBoundedClauseInput_tmPolyTime
  simpa [Function.comp, threeSATTextbookEdgesTM] using hComp

/-- The standard graph payload before pairing it with its three-colour bound. -/
def threeSATBoundedGraph (φ : SAT.ThreeCNF) : GraphInput where
  vertices := ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount φ
  edges := threeSATTextbookEdgesTM φ
  directed := false

/-- Direct-TM evidence for the exact bounded graph payload. -/
theorem threeSATBoundedGraph_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      graphStructuredEncodedType
      threeSATBoundedGraph := by
  have hVertices := threeSATBoundedVertexCount_tm_polytime
  have hEdges := threeSATTextbookEdgesTM_tmPolyTime
  have hDirected :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.bool
        (fun _ : SAT.ThreeCNF => false) :=
    TMPolyTimeMap.const threeCNFStructuredEncodedType EncodedType.bool false
  have hPayload :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        graphPayloadStructuredEncodedType
        (fun φ : SAT.ThreeCNF => (threeSATTextbookEdgesTM φ, false)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        graphTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (ComplexityReduction.Karp21.ChromaticNumber.threeSATBoundedVertexCount φ,
            (threeSATTextbookEdgesTM φ, false))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph := TMPolyTimeMap.comp Clique.graphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, Clique.graphTupleToGraph, threeSATBoundedGraph] using hGraph

/-- The reusable canonical GraphColoring hub executable. -/
def executable (φ : SAT.ThreeCNF) : GraphColoringIR :=
  (threeSATBoundedGraph φ, 3)

/-- Direct-TM evidence for the one canonical Clause-to-GraphColoring executable. -/
theorem executable_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      GraphColoringIR.lawfulRepresentation.encodedType
      executable := by
  have hGraph := threeSATBoundedGraph_tmPolyTime
  have hColors :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun _ : SAT.ThreeCNF => (3 : Nat)) :=
    TMPolyTimeMap.const threeCNFStructuredEncodedType EncodedType.nat (3 : Nat)
  simpa [executable, GraphColoringIR.lawfulRepresentation] using TMPolyTimeMap.prod_mk hGraph hColors

/-- The hub executable is extensionally CR's selected structured textbook map. -/
theorem executable_eq_legacy (φ : SAT.ThreeCNF) :
    executable φ =
      ((ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumberStructuredTMMap φ).graph,
        (ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumberStructuredTMMap φ).colors) := by
  rfl

/-- The executable preserves structured 3SAT satisfiability at the graph-colouring hub. -/
theorem executable_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ GraphColoringIR.IsColorable (executable φ) := by
  rw [executable_eq_legacy]
  exact ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumberStructuredTMMap_correct φ

/-- The canonical V2 structured 3SAT source hub. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The canonical GraphColoring hub, distinct from its concrete wrapper egress. -/
abbrev targetProblem : PresentedProblem :=
  GraphColoringIR.chromaticNumberProblem

/-- The exact request for this reusable shared hub gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The standard-audited direct-TM primitive at the exact hub representations. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime executable executable_tmPolyTime

/-- The reusable hub computation is one direct-TM primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = executable input := rfl

/-- The typed semantic iff is indexed by the atom program's exact executable. -/
theorem sharedGadgetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) := by
  change SAT.threeSATDecisionProblem.isYes input ↔ GraphColoringIR.IsColorable (sharedGadgetProgram.run input)
  rw [sharedGadgetProgram_run]
  exact executable_correct input

/-- The authoritative standard-audited Clause-to-GraphColoring shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- Only the exact typed shared-gadget request receives this certificate. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

@[simp] theorem sharedGadgetResolution_exact :
    sharedGadgetResolution = .accepted sharedGadget := rfl

end ThreeSATToGraphColoringStandardTM
end Domain
end ComplexityReduction
