/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Assembly
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.ZeroOneIP
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.ComponentResolver

/-!
Standard-axiom direct-TM reconstruction for the structured 3SAT-to-0-1-IP
gadget.

The read-only CR assembly uses `native_decide` only to discharge closed initial
accumulator size bounds for three folds.  This leaf rebuilds the same machines
with kernel-reduced `decide` proofs, keeping the executable and semantic map
unchanged while removing the nonstandard proof dependency.
-/

namespace ComplexityReduction
namespace Domain
namespace ThreeSATToZeroOneIPStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ZeroOneIP
open ComplexityReduction.Combinatorics
open Certificate Encoding Program

/-- Kernel-audited direct-TM realization of the bounded clause-prefix fold. -/
theorem clausePrefixFromClause_tmPolyTime :
    TMPolyTimeMap clauseStructuredEncodedType clausePrefixStateEncodedType
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

/-- Kernel-audited direct-TM realization of the prefix-row fold. -/
theorem prefixRowFromInstructions_tmPolyTime :
    TMPolyTimeMap prefixRowInstructionListEncodedType intRowStructuredEncodedType
      prefixRowFromInstructions := by
  rcases prefixRowStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap prefixRowInstructionListEncodedType prefixRowAccEncodedType
        prefixRowInstructionsFold := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        prefixRowInstructionEncodedType prefixRowAccEncodedType
        prefixRowStep prefixRowInitAcc hStep
        (Polynomial.C 100) (Polynomial.C 10 * Polynomial.X + Polynomial.C 30) ?_ ?_
    · intro source
      simpa using
        (show prefixRowAccEncodedType.inputSize prefixRowInitAcc ≤ (100 : Nat) by
          decide)
    · intro source acc instr hinstr
      exact prefixRowStep_growth source acc instr hinstr
  have hRow :
      TMPolyTimeMap prefixRowAccEncodedType intRowStructuredEncodedType
        (fun acc : PrefixRowAcc => acc.2) := by
    simpa [prefixRowAccEncodedType, PrefixRowAcc] using
      TMPolyTimeMap.snd clausePrefixStateEncodedType intRowStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hRow hFold
  simpa [Function.comp, prefixRowFromInstructions, prefixRowInstructionsFold]
    using hComp

/-- Kernel-audited direct-TM realization of the complete prefix-row runner. -/
theorem prefixRowRunner_tmPolyTime :
    TMPolyTimeMap prefixRowInputEncodedType intRowStructuredEncodedType prefixRowRunner := by
  have hComp :=
    TMPolyTimeMap.comp prefixRowFromInstructions_tmPolyTime prefixRowInstructions_tm_polytime
  simpa [Function.comp, prefixRowRunner] using hComp

/-- Kernel-audited direct-TM realization of one source-clause constraint row. -/
theorem clauseConstraintFromInput_tmPolyTime :
    TMPolyTimeMap clauseConstraintInputEncodedType constraintStructuredEncodedType
      clauseConstraintFromInput := by
  let X := clauseConstraintInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ClauseConstraintInput => p.1) := by
    simpa [X, clauseConstraintInputEncodedType, ClauseConstraintInput] using
      TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ClauseConstraintInput => p.2) := by
    simpa [X, clauseConstraintInputEncodedType, ClauseConstraintInput] using
      TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
  have hPrefix : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseConstraintInput => clausePrefixFromClause p.2) := by
    have hComp := TMPolyTimeMap.comp clausePrefixFromClause_tmPolyTime hClause
    simpa [Function.comp, X] using hComp
  have hRowInput :
      TMPolyTimeMap X prefixRowInputEncodedType
        (fun p : ClauseConstraintInput => (p.1, clausePrefixFromClause p.2)) :=
    TMPolyTimeMap.prod_mk hN hPrefix
  have hRow : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : ClauseConstraintInput => prefixRowRunner (p.1, clausePrefixFromClause p.2)) := by
    have hComp := TMPolyTimeMap.comp prefixRowRunner_tmPolyTime hRowInput
    simpa [Function.comp, prefixRowInputEncodedType, X] using hComp
  have hBound : TMPolyTimeMap X EncodedType.int
      (fun p : ClauseConstraintInput => prefixBound (clausePrefixFromClause p.2)) := by
    have hComp := TMPolyTimeMap.comp prefixBound_tm_polytime hPrefix
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hRow hBound
  simpa [clauseConstraintFromInput, constraintStructuredEncodedType, X] using hOut

/-- Kernel-audited direct-TM realization of the constraint-list fold step. -/
theorem constraintsFromStep_tmPolyTime :
    TMPolyTimeMap constraintsFromStepInputEncodedType constraintsFromAccEncodedType
      constraintsFromStep := by
  let X := constraintsFromStepInputEncodedType
  have hAcc : TMPolyTimeMap X constraintsFromAccEncodedType
      (fun p : ConstraintsFromStepInput => p.1) := by
    simpa [X, constraintsFromStepInputEncodedType] using
      TMPolyTimeMap.fst constraintsFromAccEncodedType constraintsFromInstructionEncodedType
  have hInstr : TMPolyTimeMap X constraintsFromInstructionEncodedType
      (fun p : ConstraintsFromStepInput => p.2) := by
    simpa [X, constraintsFromStepInputEncodedType] using
      TMPolyTimeMap.snd constraintsFromAccEncodedType constraintsFromInstructionEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat
      (fun p : ConstraintsFromStepInput => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat constraintListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, constraintsFromAccEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hOut : TMPolyTimeMap X constraintListStructuredEncodedType
      (fun p : ConstraintsFromStepInput => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat constraintListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, constraintsFromAccEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : ConstraintsFromStepInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool constraintsFromInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, constraintsFromInstructionEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hPayload : TMPolyTimeMap X constraintsFromInstructionPayloadEncodedType
      (fun p : ConstraintsFromStepInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool constraintsFromInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, constraintsFromInstructionEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hInitN : TMPolyTimeMap X EncodedType.nat
      (fun p : ConstraintsFromStepInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, constraintsFromInstructionPayloadEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ConstraintsFromStepInput => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, constraintsFromInstructionPayloadEncodedType, X,
      ConstraintsFromStepInput] using hComp
  have hEmpty : TMPolyTimeMap X constraintListStructuredEncodedType
      (fun _ : ConstraintsFromStepInput => ([] : List (List Int × Int))) :=
    TMPolyTimeMap.const X constraintListStructuredEncodedType []
  have hFalseBranch :
      TMPolyTimeMap X constraintsFromAccEncodedType
        (fun p : ConstraintsFromStepInput =>
          (p.2.2.1, ([] : List (List Int × Int)))) :=
    constraintsFromAcc_mk_tm_polytime hInitN hEmpty
  have hConstraintInput :
      TMPolyTimeMap X clauseConstraintInputEncodedType
        (fun p : ConstraintsFromStepInput => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hN hClause
  have hConstraint : TMPolyTimeMap X constraintStructuredEncodedType
      (fun p : ConstraintsFromStepInput => clauseConstraintFromInput (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp clauseConstraintFromInput_tmPolyTime hConstraintInput
    simpa [Function.comp, clauseConstraintInputEncodedType, X, ConstraintsFromStepInput]
      using hComp
  have hSingleton :
      TMPolyTimeMap X constraintListStructuredEncodedType
        (fun p : ConstraintsFromStepInput => [clauseConstraintFromInput (p.1.1, p.2.2.2)]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton constraintStructuredEncodedType)
        hConstraint
    simpa [Function.comp, constraintListStructuredEncodedType, X, ConstraintsFromStepInput]
      using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod constraintListStructuredEncodedType constraintListStructuredEncodedType)
        (fun p : ConstraintsFromStepInput =>
          (p.1.2, [clauseConstraintFromInput (p.1.1, p.2.2.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend : TMPolyTimeMap X constraintListStructuredEncodedType
      (fun p : ConstraintsFromStepInput =>
        p.1.2 ++ [clauseConstraintFromInput (p.1.1, p.2.2.2)]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_append constraintStructuredEncodedType)
        hAppendInput
    simpa [Function.comp, constraintListStructuredEncodedType, X, ConstraintsFromStepInput]
      using hComp
  have hTrueBranch :
      TMPolyTimeMap X constraintsFromAccEncodedType
        (fun p : ConstraintsFromStepInput =>
          (p.1.1, p.1.2 ++ [clauseConstraintFromInput (p.1.1, p.2.2.2)])) :=
    constraintsFromAcc_mk_tm_polytime hN hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : ConstraintsFromStepInput => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) constraintsFromAccEncodedType
        (fun p : Bool × ConstraintsFromStepInput =>
          match p.1 with
          | true =>
              (p.2.1.1,
                p.2.1.2 ++ [clauseConstraintFromInput (p.2.1.1, p.2.2.2.2)])
          | false => (p.2.2.2.1, ([] : List (List Int × Int)))) :=
    Clique.boolProduct_dispatch_tm_polytime X constraintsFromAccEncodedType
      (fFalse := fun p : ConstraintsFromStepInput =>
        (p.2.2.1, ([] : List (List Int × Int))))
      (fTrue := fun p : ConstraintsFromStepInput =>
        (p.1.1, p.1.2 ++ [clauseConstraintFromInput (p.1.1, p.2.2.2)]))
      hFalseBranch hTrueBranch
  have hOutMap := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOutMap using 1
  funext p
  rcases p with ⟨⟨n, out⟩, ⟨tag, initN, c⟩⟩
  cases tag <;> rfl

/-- Kernel-audited direct-TM realization of the bounded constraint-list fold. -/
theorem constraintsFromInstructionsFold_tmPolyTime :
    TMPolyTimeMap
      constraintsFromInstructionListEncodedType
      constraintsFromAccEncodedType
      constraintsFromInstructionsFold := by
  rcases constraintsFromStep_tmPolyTime with ⟨hStep⟩
  let time := constraintsFromFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      constraintsFromInstructionEncodedType constraintsFromAccEncodedType
      constraintsFromStep constraintsFromInitAcc hStep time ?_
  intro source
  let N := constraintsFromInstructionListEncodedType.inputSize source
  let B := constraintsFromFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      Clique.encodedList_length_le_inputSize constraintsFromInstructionEncodedType source
    simpa [N, constraintsFromInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List ConstraintsFromInstruction),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              constraintsFromInstructionEncodedType constraintsFromAccEncodedType
              constraintsFromStep hStep
              (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                constraintsFromInitAcc)
              rest ≤
            C * (EncodedType.list constraintsFromInstructionEncodedType).inputSize rest := by
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
        have hxN : constraintsFromInstructionEncodedType.inputSize x ≤ N := by
          have hElem :=
            Clique.encodedList_element_inputSize_le
              (X := constraintsFromInstructionEncodedType) (x := x) (xs := source)
              hxMemSource
          simpa [N, constraintsFromInstructionListEncodedType] using hElem
        have hPrefixSize : constraintsFromInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              constraintsFromInstructionListEncodedType.inputSize source =
                constraintsFromInstructionListEncodedType.inputSize pref +
                  constraintsFromInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            simpa [constraintsFromInstructionListEncodedType] using
              Clique.encodedList_inputSize_append constraintsFromInstructionEncodedType
                pref (x :: xs)
          omega
        have hPrefixBound :=
          constraintsFromFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            Clique.encodedList_length_le_inputSize constraintsFromInstructionEncodedType pref
          have hLen' :
              pref.length ≤ constraintsFromInstructionListEncodedType.inputSize pref := by
            simpa [constraintsFromInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            constraintsFromAccEncodedType.inputSize
                (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                  constraintsFromInitAcc) ≤ B := by
          simpa [B] using
            constraintsFromAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hTailNonempty : pref.length + 1 ≤ (pref ++ (x :: xs)).length := by
            induction pref with
            | nil => simp
            | cons y ys ih => simp
          have hSourceEq : source.length = (pref ++ (x :: xs)).length :=
            congrArg List.length hEq
          omega
        have hStepBound :=
          constraintsFromStep_bound hPrefixBound hStepProcessed hxN
        have hStepSize :
            constraintsFromAccEncodedType.inputSize
                (constraintsFromStep
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x)) ≤ B := by
          simpa [B] using
            constraintsFromAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod constraintsFromAccEncodedType
                  constraintsFromInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod constraintsFromAccEncodedType
                constraintsFromInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              constraintsFromAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                      constraintsFromInitAcc) +
                  1 + constraintsFromInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (constraintsFromInstructionEncodedType.encode x).length
                (constraintsFromAccEncodedType.encode
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc)).length
                (constraintsFromAccEncodedType.encode
                  (constraintsFromStep
                    (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                      constraintsFromInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod constraintsFromAccEncodedType
                    constraintsFromInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                      constraintsFromInitAcc, x))) ≤
              C * (constraintsFromInstructionEncodedType.inputSize x + 1) := by
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
                constraintsFromInstructionEncodedType constraintsFromAccEncodedType
                constraintsFromStep hStep
                (constraintsFromStep
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x)) xs ≤
              C * (EncodedType.list constraintsFromInstructionEncodedType).inputSize xs := by
          have hFoldPref :
              (pref ++ [x]).foldl
                  (fun acc instr => constraintsFromStep (acc, instr))
                  constraintsFromInitAcc =
                constraintsFromStep
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x) := by
            exact
              List.foldl_concat
                (fun acc instr => constraintsFromStep (acc, instr))
                constraintsFromInitAcc x pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                constraintsFromInstructionEncodedType constraintsFromAccEncodedType
                constraintsFromStep hStep acc xs)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              constraintsFromInstructionEncodedType constraintsFromAccEncodedType
              constraintsFromStep hStep
              (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                constraintsFromInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
                constraintsFromInstructionEncodedType constraintsFromAccEncodedType
                constraintsFromStep hStep
                (constraintsFromStep
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc, x)) xs +
              TM2Programs.listFoldBlockTime hStep.tm
                (constraintsFromInstructionEncodedType.encode x).length
                (constraintsFromAccEncodedType.encode
                  (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                    constraintsFromInitAcc)).length
                (constraintsFromAccEncodedType.encode
                  (constraintsFromStep
                    (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                      constraintsFromInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod constraintsFromAccEncodedType
                    constraintsFromInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => constraintsFromStep (acc, instr))
                      constraintsFromInitAcc, x))) := by
                rfl
          _ ≤
              C * (EncodedType.list constraintsFromInstructionEncodedType).inputSize xs +
                C * (constraintsFromInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤
              C * (EncodedType.list constraintsFromInstructionEncodedType).inputSize
                (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          constraintsFromInstructionEncodedType constraintsFromAccEncodedType
          constraintsFromStep hStep constraintsFromInitAcc source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, constraintsFromInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, constraintsFromFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        constraintsFromInstructionEncodedType constraintsFromAccEncodedType
        constraintsFromStep hStep constraintsFromInitAcc source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

/-- Kernel-audited direct-TM realization of constraint-list projection. -/
theorem constraintsFromFromInstructions_tmPolyTime :
    TMPolyTimeMap
      constraintsFromInstructionListEncodedType
      constraintListStructuredEncodedType
      constraintsFromFromInstructions := by
  have hFold := constraintsFromInstructionsFold_tmPolyTime
  have hOut :
      TMPolyTimeMap constraintsFromAccEncodedType constraintListStructuredEncodedType
        (fun acc : ConstraintsFromAcc => acc.2) := by
    simpa [constraintsFromAccEncodedType, ConstraintsFromAcc] using
      TMPolyTimeMap.snd EncodedType.nat constraintListStructuredEncodedType
  have hProj := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, constraintsFromFromInstructions, constraintsFromInstructionsFold]
    using hProj

/-- Kernel-audited direct-TM realization of the constraint runner. -/
theorem constraintsFromRunner_tmPolyTime :
    TMPolyTimeMap
      constraintsFromInputEncodedType
      constraintListStructuredEncodedType
      constraintsFromRunner := by
  have hComp :=
    TMPolyTimeMap.comp constraintsFromFromInstructions_tmPolyTime
      constraintsFromInstructions_tm_polytime
  simpa [Function.comp, constraintsFromRunner] using hComp

/-- Kernel-audited direct-TM realization of the semantic constraint computation. -/
theorem constraintsFromComputedInput_tmPolyTime :
    TMPolyTimeMap
      constraintsFromInputEncodedType
      constraintListStructuredEncodedType
      constraintsFromComputedInput := by
  convert constraintsFromRunner_tmPolyTime using 1
  funext p
  exact (constraintsFromRunner_eq_computed p).symm

/-- The standard-audited constraint computation at the complete 3SAT source. -/
def threeSATConstraintsTM (φ : SAT.ThreeCNF) : List (List Int × Int) :=
  constraintsFromComputedInput (threeSATBoundedConstraintsInput φ)

/-- Direct-TM evidence for the standard-audited 3SAT constraint computation. -/
theorem threeSATConstraintsTM_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      constraintListStructuredEncodedType
      threeSATConstraintsTM := by
  have hComp :=
    TMPolyTimeMap.comp constraintsFromComputedInput_tmPolyTime
      threeSATBoundedConstraintsInput_tm_polytime
  simpa [Function.comp, threeSATConstraintsTM] using hComp

/-- Reify the standard-audited constraint list as the structured 0-1-IP payload. -/
def threeSATToZeroOneIPStructuredTMMapComputed
    (φ : SAT.ThreeCNF) : IntegerProgrammingInput where
  numVariables := threeCNFStructuredEncodedType.inputSize φ
  constraints := threeSATConstraintsTM φ

/-- The reconstructed executable is extensionally CR's textbook 3SAT-to-0-1-IP map. -/
theorem threeSATToZeroOneIPStructuredTMMapComputed_eq_textbook
    (φ : SAT.ThreeCNF) :
    threeSATToZeroOneIPStructuredTMMapComputed φ =
      ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap φ := by
  have hConstraints :=
    constraintsFromComputedInput_eq_textbook
      (threeSATBoundedConstraintsInput φ)
      (by
        intro c hc
        exact φ.isThree c hc)
  unfold threeSATToZeroOneIPStructuredTMMapComputed
    ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap
    boundedTextbookMap threeSATConstraintsTM
  simp [threeSATBoundedConstraintsInput, constraintsFromTextbookInput] at hConstraints ⊢
  exact hConstraints

/-- Direct-TM evidence for the reconstructed record-valued 3SAT-to-0-1-IP map. -/
theorem threeSATToZeroOneIPStructuredTMMapComputed_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      threeSATToZeroOneIPStructuredTMMapComputed := by
  have hVariables :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        EncodedType.nat
        (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ) :=
    (encodedInputSizeNatTMBackedMap threeCNFStructuredEncodedType).tm_polytime
  have hConstraints := threeSATConstraintsTM_tmPolyTime
  have hTuple :
      TMPolyTimeMap
        threeCNFStructuredEncodedType
        integerProgrammingTupleStructuredEncodedType
        (fun φ : SAT.ThreeCNF =>
          (threeCNFStructuredEncodedType.inputSize φ, threeSATConstraintsTM φ)) :=
    TMPolyTimeMap.prod_mk hVariables hConstraints
  have hOut :=
    TMPolyTimeMap.comp integerProgrammingTupleToInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, integerProgrammingTupleToInput,
    threeSATToZeroOneIPStructuredTMMapComputed] using hOut

/-- Standard-axiom direct-TM evidence for CR's selected textbook executable. -/
theorem threeSATToZeroOneIPStructuredTMMap_tmPolyTime :
    TMPolyTimeMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap := by
  convert threeSATToZeroOneIPStructuredTMMapComputed_tmPolyTime using 1
  funext φ
  exact (threeSATToZeroOneIPStructuredTMMapComputed_eq_textbook φ).symm

/-- The existing polynomial output-size proof applies to the reconstructed textbook executable. -/
theorem threeSATToZeroOneIPStructuredTMMap_polynomialSizeBound :
    ComplexityReduction.PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : IntegerProgrammingInput => integerProgrammingStructuredEncodedType.inputSize I)
      ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap :=
  ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap_polynomialSizeBound

/-- Compatibility evidence is paired with the reconstructed direct-TM witness for one executable. -/
noncomputable def threeSATToZeroOneIPStructuredTMBackedMap :
    TMBackedCostedMap
      threeCNFStructuredEncodedType
      integerProgrammingStructuredEncodedType
      ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      threeSATToZeroOneIPStructuredTMMap_polynomialSizeBound
  tm_polytime := threeSATToZeroOneIPStructuredTMMap_tmPolyTime

/-- The textbook map preserves the exact structured 3SAT/0-1-IP semantics. -/
theorem threeSATToZeroOneIPStructuredTMMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔
      ZeroOneIntegerProgramming
        (ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap φ) :=
  ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap_correct φ

/-- The canonical V2 structured 3SAT source hub. -/
abbrev sourceProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The canonical V2 structured 0-1-IP target hub. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.ZeroOneIP.structuredProblem

/-- The exact reusable shared-gadget endpoint. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

/-- The one request fixes the two complete encoder-bound hub presentations. -/
def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The standard-audited primitive for the reusable structured 3SAT-to-0-1-IP gadget. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime
    ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap
    threeSATToZeroOneIPStructuredTMMap_tmPolyTime

/-- The shared computation is one direct-TM primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input =
      ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIPStructuredTMMap input :=
  rfl

/-- The semantic iff is indexed by the same typed atom executable. -/
theorem sharedGadgetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) := by
  change SAT.threeSATDecisionProblem.isYes input ↔
    ZeroOneIntegerProgramming (sharedGadgetProgram.run input)
  rw [sharedGadgetProgram_run]
  exact threeSATToZeroOneIPStructuredTMMap_correct input

/-- The authoritative reusable V2 shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The exact shared-gadget capability is accepted only from its typed certificate. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

@[simp] theorem sharedGadgetProgram_eq_atom :
    sharedGadgetProgram = PolyProg.atom sharedGadgetPrimitive :=
  rfl

@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

@[simp] theorem sharedGadget_compileTM_eq_standardTM :
    sharedGadget.program.compileTM = threeSATToZeroOneIPStructuredTMMap_tmPolyTime :=
  rfl

@[simp] theorem sharedGadgetResolution_eq_accepted :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

end ThreeSATToZeroOneIPStandardTM
end Domain
end ComplexityReduction
