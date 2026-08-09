import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlySuffixValidityCNF

/-!
Direct standard-TM assembly boundary for the x-only suffix-validity CNF.

The suffix-validity predicate itself still needs an executable generator.  This
file records the checked composition point: once that generator is available,
the full emitted x-only CNF follows by direct TM composition.

The witnesses below deliberately stop at local prefix-match clauses.  The
semantic invalid-prefix filter in `XOnlySuffixValidityCNF` enumerates all
bounded prefixes and uses a classical certificate-image predicate, so it is not
a direct polynomial generator in its current form.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Executable input-choice prefix clauses -/

noncomputable def tmVerifierInputReadChoiceSumEncodedType
    {L : EncodedDecisionProblem} (V : TMVerifier L) : EncodedType :=
  EncodedType.sum (EncodedType.raw Unit)
    (EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V))

noncomputable def tmVerifierInputReadChoiceAsSum
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMVerifierStackReadChoice V (tmVerifierTM V).k₀ →
      (tmVerifierInputReadChoiceSumEncodedType V).Carrier
  | TMVerifierStackReadChoice.empty => Sum.inl ()
  | TMVerifierStackReadChoice.symbol payload symbol => Sum.inr (payload, symbol)

noncomputable def tmVerifierInputReadChoiceEncodedType
    {L : EncodedDecisionProblem} (V : TMVerifier L) : EncodedType where
  Carrier := TMVerifierStackReadChoice V (tmVerifierTM V).k₀
  Symbol := (tmVerifierInputReadChoiceSumEncodedType V).Symbol
  finite_symbol := inferInstance
  encode := fun choice =>
    (tmVerifierInputReadChoiceSumEncodedType V).encode
      (tmVerifierInputReadChoiceAsSum V choice)

theorem tmVerifierInputReadChoice_asSum_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (tmVerifierInputReadChoiceEncodedType V)
      (tmVerifierInputReadChoiceSumEncodedType V)
      (tmVerifierInputReadChoiceAsSum V) :=
  TMPolyTimeMap.of_encodingEquiv
      (tmVerifierInputReadChoiceEncodedType V)
      (tmVerifierInputReadChoiceSumEncodedType V)
      (tmVerifierInputReadChoiceAsSum V)
      (Equiv.refl _)
      (by
        intro choice
        change
          (tmVerifierInputReadChoiceSumEncodedType V).encode
              (tmVerifierInputReadChoiceAsSum V choice) =
            ((tmVerifierInputReadChoiceSumEncodedType V).encode
              (tmVerifierInputReadChoiceAsSum V choice)).map id
        rw [List.map_id])

def tmVerifierInputReadChoiceIsSymbol
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) : Bool :=
  match choice with
  | TMVerifierStackReadChoice.empty => false
  | TMVerifierStackReadChoice.symbol _ _ => true

noncomputable def tmVerifierInputReadChoicePayload
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) : Nat :=
  match choice with
  | TMVerifierStackReadChoice.empty => 0
  | TMVerifierStackReadChoice.symbol payload _ => payload

theorem tmVerifierInputReadChoiceIsSymbol_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (tmVerifierInputReadChoiceEncodedType V) EncodedType.bool
      (tmVerifierInputReadChoiceIsSymbol (V := V)) := by
  have hAsSum := tmVerifierInputReadChoice_asSum_tm_polytime V
  have hLeft :
      TMPolyTimeMap (EncodedType.raw Unit) EncodedType.bool
        (fun _ : Unit => false) :=
    TMPolyTimeMap.const (EncodedType.raw Unit) EncodedType.bool false
  have hRight :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V))
        EncodedType.bool
        (fun _ : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ => true) :=
    TMPolyTimeMap.const
      (EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V))
      EncodedType.bool true
  have hSum := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hSum hAsSum
  convert hComp using 1
  funext choice
  cases choice <;> rfl

theorem tmVerifierInputReadChoicePayload_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap (tmVerifierInputReadChoiceEncodedType V) EncodedType.nat
      (tmVerifierInputReadChoicePayload (V := V)) := by
  have hAsSum := tmVerifierInputReadChoice_asSum_tm_polytime V
  have hLeft :
      TMPolyTimeMap (EncodedType.raw Unit) EncodedType.nat
          (fun _ : Unit => (0 : Nat)) :=
      TMPolyTimeMap.const (EncodedType.raw Unit) EncodedType.nat (0 : Nat)
  have hRight :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat (tmVerifierInputSymbolEncodedType V))
        EncodedType.nat
        (fun p : Nat × (tmVerifierTM V).Γ (tmVerifierTM V).k₀ => p.1) := by
    simpa using
      TMPolyTimeMap.fst EncodedType.nat (tmVerifierInputSymbolEncodedType V)
  have hSum := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hSum hAsSum
  convert hComp using 1
  funext choice
  cases choice <;> rfl

theorem tmVerifierInputReadChoice_atomAt_indexed_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat (tmVerifierInputReadChoiceEncodedType V))
      literalStructuredEncodedType
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0 p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)
  let Pair := EncodedType.prod EncodedType.nat EncodedType.nat
  have hCell : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)
  have hChoice : TMPolyTimeMap X (tmVerifierInputReadChoiceEncodedType V)
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
        tmVerifierInputReadChoiceIsSymbol p.2) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierInputReadChoiceIsSymbol_tm_polytime V) hChoice
    simpa [Function.comp, X] using hComp
  have hPayload : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
        tmVerifierInputReadChoicePayload p.2) := by
    have hComp := TMPolyTimeMap.comp (tmVerifierInputReadChoicePayload_tm_polytime V) hChoice
    simpa [Function.comp, X] using hComp
  have hCellPayload : TMPolyTimeMap X Pair
      (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
        (p.1, tmVerifierInputReadChoicePayload p.2)) :=
    TMPolyTimeMap.prod_mk hCell hPayload
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool Pair)
        (fun p : Nat × TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
          (tmVerifierInputReadChoiceIsSymbol p.2,
            (p.1, tmVerifierInputReadChoicePayload p.2))) :=
    TMPolyTimeMap.prod_mk hTag hCellPayload
  have hFalse : TMPolyTimeMap Pair literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ p.1) := by
    have hFst : TMPolyTimeMap Pair EncodedType.nat (fun p : Nat × Nat => p.1) := by
      simpa [Pair] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hEmpty := tmVerifierStackEmptyAtom_cell_tm_polytime V 0 (tmVerifierTM V).k₀
    have hComp := TMPolyTimeMap.comp hEmpty hFst
    simpa [Function.comp, Pair] using hComp
  have hTrue : TMPolyTimeMap Pair literalStructuredEncodedType
      (fun p : Nat × Nat => tmVerifierStackSymbolAtom V 0 (tmVerifierTM V).k₀ p.1 p.2) :=
    tmVerifierStackSymbolAtom_cellPayload_tm_polytime V 0 (tmVerifierTM V).k₀
  have hDispatch :=
    boolProduct_dispatch_tm_polytime Pair literalStructuredEncodedType hFalse hTrue
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨cell, choice⟩
  cases choice <;> rfl

def tmVerifierInputChoicePrefixMatchAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType)

abbrev TMVerifierInputChoicePrefixMatchAcc := Nat × List Literal

noncomputable def tmVerifierInputChoicePrefixMatchInstructionEncodedType
      {L : EncodedDecisionProblem} (V : TMVerifier L) : EncodedType :=
    EncodedType.sum EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)

def tmVerifierInputChoicePrefixMatchInit :
    TMVerifierInputChoicePrefixMatchAcc :=
  ((0 : Nat), ([] : List Literal))

noncomputable def tmVerifierInputChoicePrefixMatchStep
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : TMVerifierInputChoicePrefixMatchAcc ×
      (tmVerifierInputChoicePrefixMatchInstructionEncodedType V).Carrier) :
    TMVerifierInputChoicePrefixMatchAcc :=
  match p.2 with
  | Sum.inl start => (start, [])
  | Sum.inr choice =>
      let idx := p.1.1
      let out := p.1.2
      (idx + 1,
        out ++
          [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀) 0 idx choice])

noncomputable def tmVerifierInputChoicePrefixMatchFold
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (instrs : List (tmVerifierInputChoicePrefixMatchInstructionEncodedType V).Carrier) :
    TMVerifierInputChoicePrefixMatchAcc :=
  instrs.foldl (fun acc instr => tmVerifierInputChoicePrefixMatchStep V (acc, instr))
    tmVerifierInputChoicePrefixMatchInit

noncomputable def tmVerifierInputChoicePrefixMatchInstructions
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (start : Nat)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    List (tmVerifierInputChoicePrefixMatchInstructionEncodedType V).Carrier :=
  Sum.inl start :: choices.map Sum.inr

noncomputable def tmVerifierInputChoicePrefixMatchOutput
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (acc : TMVerifierInputChoicePrefixMatchAcc) : List Literal :=
  acc.2 ++ [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ acc.1]

theorem tmVerifierInputChoicePrefixMatchStep_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod tmVerifierInputChoicePrefixMatchAccEncodedType
        (tmVerifierInputChoicePrefixMatchInstructionEncodedType V))
      tmVerifierInputChoicePrefixMatchAccEncodedType
      (tmVerifierInputChoicePrefixMatchStep V) := by
  let Acc := tmVerifierInputChoicePrefixMatchAccEncodedType
  let Choice := tmVerifierInputReadChoiceEncodedType V
  let Instr := tmVerifierInputChoicePrefixMatchInstructionEncodedType V
  let X := EncodedType.prod Acc Instr
  let Right := EncodedType.prod Acc Choice
  have hChoice :
      TMPolyTimeMap X (prodSumChoiceEncodedType Acc EncodedType.nat Choice)
        (prodSumChoice Acc EncodedType.nat Choice) := by
    simpa [X, Instr, tmVerifierInputChoicePrefixMatchInstructionEncodedType, Choice] using
      prodSumChoice_tm_polytime Acc EncodedType.nat Choice
  have hLeft :
      TMPolyTimeMap EncodedType.nat Acc
        (fun start : Nat => (start, ([] : List Literal))) := by
    have hNil :
        TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
          (fun _ : Nat => ([] : List Literal)) :=
      TMPolyTimeMap.const EncodedType.nat (EncodedType.list literalStructuredEncodedType) []
    exact TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hNil
  have hAccRight : TMPolyTimeMap Right Acc
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.1) := by
    simpa [Right, Acc, Choice] using TMPolyTimeMap.fst Acc Choice
  have hChoiceRight : TMPolyTimeMap Right Choice
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.2) := by
    simpa [Right, Acc, Choice] using TMPolyTimeMap.snd Acc Choice
  have hIdx : TMPolyTimeMap Right EncodedType.nat
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAccRight
    simpa [Function.comp, Right, Acc, tmVerifierInputChoicePrefixMatchAccEncodedType]
      using hComp
  have hOut : TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAccRight
    simpa [Function.comp, Right, Acc, tmVerifierInputChoicePrefixMatchAccEncodedType]
      using hComp
  have hNext : TMPolyTimeMap Right EncodedType.nat
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => p.1.1 + 1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hIdx
    simpa [Function.comp, Nat.succ_eq_add_one, Right] using hComp
  have hAtomInput :
      TMPolyTimeMap Right
        (EncodedType.prod EncodedType.nat (tmVerifierInputReadChoiceEncodedType V))
        (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hIdx hChoiceRight
  have hAtom : TMPolyTimeMap Right literalStructuredEncodedType
      (fun p : TMVerifierInputChoicePrefixMatchAcc ×
          TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierInputReadChoice_atomAt_indexed_tm_polytime V) hAtomInput
    simpa [Function.comp, Right] using hComp
  have hAtomSingleton :
      TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
        (fun p : TMVerifierInputChoicePrefixMatchAcc ×
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
          [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hAtom
    simpa [Function.comp, Right] using hComp
  have hAppendInput :
      TMPolyTimeMap Right
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : TMVerifierInputChoicePrefixMatchAcc ×
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
          (p.1.2,
            [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hAtomSingleton
  have hAppend :
      TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
        (fun p : TMVerifierInputChoicePrefixMatchAcc ×
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
          p.1.2 ++
            [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 p.1.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
    simpa [Function.comp, Right] using hComp
  have hRight :
      TMPolyTimeMap Right Acc
        (fun p : TMVerifierInputChoicePrefixMatchAcc ×
            TMVerifierStackReadChoice V (tmVerifierTM V).k₀ =>
          (p.1.1 + 1,
            p.1.2 ++
              [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 p.1.1 p.2])) :=
    TMPolyTimeMap.prod_mk hNext hAppend
  have hSum := TMPolyTimeMap.sum_elim hLeft hRight
  have hComp := TMPolyTimeMap.comp hSum hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem tmVerifierInputChoicePrefixMatchAcc_inputSize_step_le
    (idx : Nat) (out : List Literal) (lit : Literal) :
    tmVerifierInputChoicePrefixMatchAccEncodedType.inputSize
        (idx + 1, out ++ [lit]) ≤
      tmVerifierInputChoicePrefixMatchAccEncodedType.inputSize (idx, out) +
        literalStructuredEncodedType.inputSize lit + 3 := by
  change
    (EncodedType.prod EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)).inputSize
        (idx + 1, out ++ [lit]) ≤
      (EncodedType.prod EncodedType.nat
        (EncodedType.list literalStructuredEncodedType)).inputSize (idx, out) +
        literalStructuredEncodedType.inputSize lit + 3
  rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod]
  rw [show (EncodedType.list literalStructuredEncodedType).inputSize (out ++ [lit]) =
      (EncodedType.list literalStructuredEncodedType).inputSize out +
        literalStructuredEncodedType.inputSize lit + 1 by
    simpa using list_inputSize_append literalStructuredEncodedType out [lit]]
  simp [EncodedType.inputSize_nat]
  omega

theorem tmVerifierInputChoicePrefixMatchInstruction_inputSize_inl
    {L : EncodedDecisionProblem} (V : TMVerifier L) (start : Nat) :
    (tmVerifierInputChoicePrefixMatchInstructionEncodedType V).inputSize (Sum.inl start) =
      start + 2 := by
  change
    (EncodedType.sum EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)).inputSize
        (Sum.inl start) =
      start + 2
  simp [EncodedType.inputSize, EncodedType.sum, EncodedType.nat]

theorem tmVerifierInputChoicePrefixMatchInstruction_inputSize_inr
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀) :
    (tmVerifierInputChoicePrefixMatchInstructionEncodedType V).inputSize (Sum.inr choice) =
      (tmVerifierInputReadChoiceEncodedType V).inputSize choice + 1 := by
  change
    (EncodedType.sum EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)).inputSize
        (Sum.inr choice) =
      (tmVerifierInputReadChoiceEncodedType V).inputSize choice + 1
  simp [EncodedType.inputSize, EncodedType.sum]

theorem tmVerifierInputChoicePrefixMatchAcc_inputSize_init :
    tmVerifierInputChoicePrefixMatchAccEncodedType.inputSize
        tmVerifierInputChoicePrefixMatchInit ≤ 3 := by
  change
    (EncodedType.prod EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)).inputSize ((0 : Nat), []) ≤ 3
  simp [EncodedType.inputSize_prod, EncodedType.inputSize_nat]

theorem tmVerifierInputChoicePrefixMatchAcc_inputSize_reset (start : Nat) :
    tmVerifierInputChoicePrefixMatchAccEncodedType.inputSize
        (start, ([] : List Literal)) =
      start + 2 := by
  change
    (EncodedType.prod EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)).inputSize (start, ([] : List Literal)) =
      start + 2
  rw [EncodedType.inputSize_prod]
  rw [show (EncodedType.list literalStructuredEncodedType).inputSize ([] : List Literal) = 0 by
    exact EncodedType.inputSize_list_nil literalStructuredEncodedType]
  simp [EncodedType.inputSize_nat]

theorem tmVerifierInputChoicePrefixMatchFold_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.list (tmVerifierInputChoicePrefixMatchInstructionEncodedType V))
      tmVerifierInputChoicePrefixMatchAccEncodedType
      (tmVerifierInputChoicePrefixMatchFold V) := by
  rcases tmVerifierInputChoicePrefixMatchStep_tm_polytime V with ⟨hStep⟩
  rcases tmVerifierInputReadChoice_atomAt_indexed_tm_polytime V with ⟨hAtom⟩
  let Instr := tmVerifierInputChoicePrefixMatchInstructionEncodedType V
  let Acc := tmVerifierInputChoicePrefixMatchAccEncodedType
  let Choice := tmVerifierInputReadChoiceEncodedType V
  let B := TM2Programs.finTM2StepPushBound hAtom.tm
  let grow : Polynomial Nat :=
    Polynomial.X + Polynomial.C 12 +
      hAtom.time.comp (Polynomial.X + Polynomial.C 3) * Polynomial.C B
  let bound : Polynomial Nat := Polynomial.C 3 + Polynomial.X * grow
  let time : Polynomial Nat :=
    TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
      (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))
  refine
    TMPolyTimeMap.list_foldl_typed Instr Acc (tmVerifierInputChoicePrefixMatchStep V)
      tmVerifierInputChoicePrefixMatchInit hStep time ?_
  intro source
  let N := (EncodedType.list Instr).inputSize source
  let G := grow.eval N
  let Bound := 3 + N * G
  let T := hStep.time.eval (Bound + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm Bound T
  have hGrowEval :
      G = N + 12 + hAtom.time.eval (N + 3) * B := by
    simp [G, grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_X, B]
  have hGpos : 1 ≤ G := by
    rw [hGrowEval]
    omega
  have hBoundEval : bound.eval N = Bound := by
    simp [bound, Bound, G, Polynomial.eval_add, Polynomial.eval_mul]
  have hLoopAux :
      ∀ (rest : List Instr.Carrier) (acc : TMVerifierInputChoicePrefixMatchAcc),
        (EncodedType.list Instr).inputSize rest ≤ N →
          acc.1 + (EncodedType.list Instr).inputSize rest ≤ N →
            Acc.inputSize acc ≤ 3 + (N - (EncodedType.list Instr).inputSize rest) * G →
              TM2Programs.listFoldTypedLoopTime Instr Acc (tmVerifierInputChoicePrefixMatchStep V)
                  hStep acc rest ≤
                C * (EncodedType.list Instr).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hRest _hIdx _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons instr tail ih =>
        intro acc hRest hIdx hAcc
        have hTailN : (EncodedType.list Instr).inputSize tail ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hInstrN : Instr.inputSize instr ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hAccFull : Acc.inputSize acc ≤ Bound := by
          have hSub : N - (EncodedType.list Instr).inputSize (instr :: tail) ≤ N :=
            Nat.sub_le N ((EncodedType.list Instr).inputSize (instr :: tail))
          have hMul := Nat.mul_le_mul_right G hSub
          exact hAcc.trans (by simpa [Bound] using Nat.add_le_add_left hMul 3)
        have hNextIdx :
            (tmVerifierInputChoicePrefixMatchStep V (acc, instr)).1 +
                (EncodedType.list Instr).inputSize tail ≤ N := by
          cases instr with
          | inl start =>
              change Nat at start
              rw [EncodedType.inputSize_list_cons] at hIdx
              rw [tmVerifierInputChoicePrefixMatchInstruction_inputSize_inl V start] at hIdx
              simp [tmVerifierInputChoicePrefixMatchStep]
              omega
          | inr choice =>
              rw [EncodedType.inputSize_list_cons] at hIdx
              simp [tmVerifierInputChoicePrefixMatchStep]
              omega
        have hNextSize :
            Acc.inputSize (tmVerifierInputChoicePrefixMatchStep V (acc, instr)) ≤
              3 + (N - (EncodedType.list Instr).inputSize tail) * G := by
          cases instr with
          | inl start =>
              change Nat at start
              have hStartTail : start + (EncodedType.list Instr).inputSize tail ≤ N := by
                rw [EncodedType.inputSize_list_cons] at hIdx
                rw [tmVerifierInputChoicePrefixMatchInstruction_inputSize_inl V start] at hIdx
                omega
              have hSize :
                  Acc.inputSize
                      (tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inl start)) =
                    start + 2 := by
                simpa [Acc, tmVerifierInputChoicePrefixMatchStep] using
                  tmVerifierInputChoicePrefixMatchAcc_inputSize_reset start
              rw [hSize]
              have hStartLe : start ≤ N - (EncodedType.list Instr).inputSize tail := by
                omega
              have hMul : N - (EncodedType.list Instr).inputSize tail ≤
                  (N - (EncodedType.list Instr).inputSize tail) * G := by
                exact Nat.le_mul_of_pos_right (N - (EncodedType.list Instr).inputSize tail) hGpos
              omega
          | inr choice =>
              let lit :=
                TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                  0 acc.1 choice
              have hAtomInput :
                  (EncodedType.prod EncodedType.nat Choice).inputSize (acc.1, choice) ≤
                    N + 3 := by
                rw [EncodedType.inputSize_prod]
                change EncodedType.nat.inputSize acc.1 + 1 + Choice.inputSize choice ≤
                  N + 3
                rw [EncodedType.inputSize_list_cons] at hIdx
                have hInstrEq :
                    Instr.inputSize (Sum.inr choice) = Choice.inputSize choice + 1 := by
                  simpa [Instr, Choice] using
                    tmVerifierInputChoicePrefixMatchInstruction_inputSize_inr V choice
                rw [hInstrEq] at hIdx
                simp [EncodedType.inputSize_nat]
                omega
              have hAtomOut :=
                TM2Programs.tm2ComputableInPolyTime_output_length_le hAtom (acc.1, choice)
              have hAtomSize :
                  literalStructuredEncodedType.inputSize lit ≤
                    N + 3 + hAtom.time.eval (N + 3) * B := by
                have hTimeMono :
                    hAtom.time.eval
                        ((EncodedType.prod EncodedType.nat Choice).inputSize (acc.1, choice)) ≤
                      hAtom.time.eval (N + 3) :=
                  TM2Programs.polynomialNat_eval_mono hAtom.time hAtomInput
                have hOut' :
                    literalStructuredEncodedType.inputSize lit ≤
                      (EncodedType.prod EncodedType.nat Choice).inputSize (acc.1, choice) +
                        hAtom.time.eval
                            ((EncodedType.prod EncodedType.nat Choice).inputSize (acc.1, choice)) *
                          B := by
                  simpa [EncodedType.inputSize, lit, B, Choice] using hAtomOut
                nlinarith [hOut', hAtomInput, hTimeMono, Nat.zero_le B]
              have hStepSize :
                  Acc.inputSize (tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inr choice)) ≤
                    Acc.inputSize acc + literalStructuredEncodedType.inputSize lit + 3 := by
                simpa [Acc, lit, tmVerifierInputChoicePrefixMatchStep] using
                  tmVerifierInputChoicePrefixMatchAcc_inputSize_step_le acc.1 acc.2 lit
              have hGrowth :
                  Acc.inputSize (tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inr choice)) ≤
                    Acc.inputSize acc + G := by
                rw [hGrowEval]
                nlinarith [hStepSize, hAtomSize]
              have hConsSize :
                  (EncodedType.list Instr).inputSize (Sum.inr choice :: tail) =
                    Instr.inputSize (Sum.inr choice) + 1 +
                      (EncodedType.list Instr).inputSize tail :=
                EncodedType.inputSize_list_cons Instr (Sum.inr choice) tail
              have hSub :
                  N - (EncodedType.list Instr).inputSize (Sum.inr choice :: tail) + 1 ≤
                    N - (EncodedType.list Instr).inputSize tail := by
                rw [hConsSize] at hRest ⊢
                omega
              calc
                Acc.inputSize (tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inr choice))
                    ≤ Acc.inputSize acc + G := hGrowth
                _ ≤ 3 + (N - (EncodedType.list Instr).inputSize (Sum.inr choice :: tail)) *
                      G + G := by
                    omega
                _ = 3 + (N - (EncodedType.list Instr).inputSize (Sum.inr choice :: tail) + 1) *
                      G := by
                    ring
                _ ≤ 3 + (N - (EncodedType.list Instr).inputSize tail) * G :=
                    Nat.add_le_add_left (Nat.mul_le_mul_right G hSub) 3
        have hNextFull :
            Acc.inputSize (tmVerifierInputChoicePrefixMatchStep V (acc, instr)) ≤ Bound := by
          have hSub : N - (EncodedType.list Instr).inputSize tail ≤ N :=
            Nat.sub_le N ((EncodedType.list Instr).inputSize tail)
          have hMul := Nat.mul_le_mul_right G hSub
          exact hNextSize.trans (by simpa [Bound] using Nat.add_le_add_left hMul 3)
        have hStepTime :
            hStep.time.eval ((EncodedType.prod Acc Instr).inputSize (acc, instr)) ≤ T := by
          have hArg :
              (EncodedType.prod Acc Instr).inputSize (acc, instr) ≤ Bound + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Acc.inputSize acc + 1 + Instr.inputSize instr ≤ Bound + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (Instr.encode instr).length
                (Acc.encode acc).length
                (Acc.encode (tmVerifierInputChoicePrefixMatchStep V (acc, instr))).length
                (hStep.time.eval ((EncodedType.prod Acc Instr).inputSize (acc, instr))) ≤
              C * (Instr.inputSize instr + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm Bound T
              (by simpa [EncodedType.inputSize] using hAccFull)
              (by simpa [EncodedType.inputSize] using hNextFull)
              hStepTime
        have hTail :=
          ih (tmVerifierInputChoicePrefixMatchStep V (acc, instr)) hTailN hNextIdx hNextSize
        calc
          TM2Programs.listFoldTypedLoopTime Instr Acc (tmVerifierInputChoicePrefixMatchStep V)
              hStep acc (instr :: tail)
              =
            TM2Programs.listFoldTypedLoopTime Instr Acc (tmVerifierInputChoicePrefixMatchStep V)
                hStep (tmVerifierInputChoicePrefixMatchStep V (acc, instr)) tail +
              TM2Programs.listFoldBlockTime hStep.tm (Instr.encode instr).length
                (Acc.encode acc).length
                (Acc.encode (tmVerifierInputChoicePrefixMatchStep V (acc, instr))).length
                (hStep.time.eval ((EncodedType.prod Acc Instr).inputSize (acc, instr))) := by
              rfl
          _ ≤ C * (EncodedType.list Instr).inputSize tail + C * (Instr.inputSize instr + 1) :=
              Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list Instr).inputSize (instr :: tail) := by
              rw [EncodedType.inputSize_list_cons]
              nlinarith
  have hInitSize :
      Acc.inputSize tmVerifierInputChoicePrefixMatchInit ≤ 3 := by
    simpa [Acc] using tmVerifierInputChoicePrefixMatchAcc_inputSize_init
  have hLoop :
      TM2Programs.listFoldTypedLoopTime Instr Acc (tmVerifierInputChoicePrefixMatchStep V)
          hStep tmVerifierInputChoicePrefixMatchInit source ≤ C * N := by
    simpa [N, tmVerifierInputChoicePrefixMatchInit] using
      hLoopAux source tmVerifierInputChoicePrefixMatchInit (by simp [N])
        (by simp [N, tmVerifierInputChoicePrefixMatchInit])
        (by simpa [N] using hInitSize)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, bound, Bound, T, C, G,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [show (EncodedType.list Instr).inputSize source = N from rfl, hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem tmVerifierInputChoicePrefixMatchOutput_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap tmVerifierInputChoicePrefixMatchAccEncodedType
      (EncodedType.list literalStructuredEncodedType)
      (tmVerifierInputChoicePrefixMatchOutput V) := by
  let Acc := tmVerifierInputChoicePrefixMatchAccEncodedType
  have hIdx : TMPolyTimeMap Acc EncodedType.nat
      (fun acc : TMVerifierInputChoicePrefixMatchAcc => acc.1) := by
    simpa [Acc, tmVerifierInputChoicePrefixMatchAccEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat (EncodedType.list literalStructuredEncodedType)
  have hOut : TMPolyTimeMap Acc (EncodedType.list literalStructuredEncodedType)
      (fun acc : TMVerifierInputChoicePrefixMatchAcc => acc.2) := by
    simpa [Acc, tmVerifierInputChoicePrefixMatchAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat (EncodedType.list literalStructuredEncodedType)
  have hEmpty : TMPolyTimeMap Acc literalStructuredEncodedType
      (fun acc : TMVerifierInputChoicePrefixMatchAcc =>
        tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ acc.1) := by
    have hCell := tmVerifierStackEmptyAtom_cell_tm_polytime V 0 (tmVerifierTM V).k₀
    have hComp := TMPolyTimeMap.comp hCell hIdx
    simpa [Function.comp, Acc] using hComp
  have hSingleton :
      TMPolyTimeMap Acc (EncodedType.list literalStructuredEncodedType)
        (fun acc : TMVerifierInputChoicePrefixMatchAcc =>
          [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ acc.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hEmpty
    simpa [Function.comp, Acc] using hComp
  have hAppendInput :
      TMPolyTimeMap Acc
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun acc : TMVerifierInputChoicePrefixMatchAcc =>
          (acc.2, [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ acc.1])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierInputChoicePrefixMatchOutput,
    Acc, tmVerifierInputChoicePrefixMatchAccEncodedType] using hAppend

theorem tmVerifierInputChoicePrefixMatchFoldWith_symbols
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (idx : Nat) (out : List Literal)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    choices.foldl
        (fun acc choice => tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inr choice))
        (idx, out) =
      (idx + choices.length,
        out ++
          (choices.zipIdx idx).map fun entry =>
            TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 entry.2 entry.1) := by
    induction choices generalizing idx out with
    | nil =>
        change (idx, out) =
          (idx + ([] : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).length,
            out ++
              List.map
                (fun entry =>
                  TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                    0 entry.2 entry.1)
                (([] : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)).zipIdx idx))
        simp
    | cons choice rest ih =>
        change
          rest.foldl
              (fun acc choice => tmVerifierInputChoicePrefixMatchStep V (acc, Sum.inr choice))
              (tmVerifierInputChoicePrefixMatchStep V ((idx, out), Sum.inr choice)) =
            (idx + (choice :: rest).length,
              out ++
                List.map
                  (fun entry =>
                    TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                      0 entry.2 entry.1)
                  ((choice :: rest).zipIdx idx))
        have hih := ih (idx + 1)
          (out ++
            [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
              0 idx choice])
        simpa [tmVerifierInputChoicePrefixMatchStep, List.zipIdx_cons, List.map_map,
          List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hih

theorem tmVerifierInputChoicePrefixMatchFold_instructions_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (start : Nat)
    (choices : List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀)) :
    tmVerifierInputChoicePrefixMatchOutput V
        (tmVerifierInputChoicePrefixMatchFold V
          (tmVerifierInputChoicePrefixMatchInstructions V start choices)) =
      (choices.zipIdx start).map (fun entry =>
        TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
          0 entry.2 entry.1) ++
        [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ (start + choices.length)] := by
    rw [tmVerifierInputChoicePrefixMatchFold, tmVerifierInputChoicePrefixMatchInstructions]
    simp [tmVerifierInputChoicePrefixMatchInit, tmVerifierInputChoicePrefixMatchStep]
    rw [List.foldl_map]
    have hFold :=
      tmVerifierInputChoicePrefixMatchFoldWith_symbols V start ([] : List Literal) choices
    have hFold' :
        List.foldl
            (fun x y => (x.1 + 1,
              x.2 ++ [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 x.1 y]))
            (start, ([] : List Literal)) choices =
          (start + choices.length,
            List.map
              (fun entry =>
                TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                  0 entry.2 entry.1)
              (choices.zipIdx start)) := by
      simpa [tmVerifierInputChoicePrefixMatchStep] using hFold
    have hOut := congrArg Prod.snd hFold'
    have hIdx := congrArg Prod.fst hFold'
    have hOut' :
        (List.foldl
            (fun x y => (x.1 + 1,
              x.2 ++ [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 x.1 y]))
            (start, ([] : List Literal)) choices).2 =
          List.map
            (fun entry =>
              TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 entry.2 entry.1)
            (choices.zipIdx start) := by
      simpa using hOut
    have hIdx' :
        (List.foldl
            (fun x y => (x.1 + 1,
              x.2 ++ [TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
                0 x.1 y]))
            (start, ([] : List Literal)) choices).1 =
          start + choices.length := by
      simpa using hIdx
    simp [tmVerifierInputChoicePrefixMatchOutput]
    constructor
    · exact hOut'
    · simpa using congrArg (fun n => tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ n) hIdx'

theorem tmVerifierInputChoicePrefixMatchInstructions_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V)))
      (EncodedType.list (tmVerifierInputChoicePrefixMatchInstructionEncodedType V))
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        tmVerifierInputChoicePrefixMatchInstructions V p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat
    (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  let Instr := tmVerifierInputChoicePrefixMatchInstructionEncodedType V
  have hStart : TMPolyTimeMap X EncodedType.nat
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  have hChoices : TMPolyTimeMap X (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  have hInit : TMPolyTimeMap X Instr
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        Sum.inl p.1) := by
    have hInl := TMPolyTimeMap.inl EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)
    have hComp := TMPolyTimeMap.comp hInl hStart
    simpa [Function.comp, Instr, tmVerifierInputChoicePrefixMatchInstructionEncodedType]
      using hComp
  have hInitSingleton : TMPolyTimeMap X (EncodedType.list Instr)
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        [Sum.inl p.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Instr) hInit
    simpa [Function.comp] using hComp
  have hChoiceInstr :
      TMPolyTimeMap (tmVerifierInputReadChoiceEncodedType V) Instr
        (fun choice : TMVerifierStackReadChoice V (tmVerifierTM V).k₀ => Sum.inr choice) := by
    simpa [Instr, tmVerifierInputChoicePrefixMatchInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat (tmVerifierInputReadChoiceEncodedType V)
  have hMapped : TMPolyTimeMap X (EncodedType.list Instr)
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        p.2.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hChoiceInstr
    have hComp := TMPolyTimeMap.comp hMap hChoices
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod (EncodedType.list Instr) (EncodedType.list Instr))
        (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
          ([Sum.inl p.1], p.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hMapped
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Instr) hAppendInput
  simpa [Function.comp, tmVerifierInputChoicePrefixMatchInstructions] using hAppend

theorem tmVerifierInputChoicePrefixMatchFromStart_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V)))
      (EncodedType.list literalStructuredEncodedType)
      (fun p : Nat × List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        (p.2.zipIdx p.1).map (fun entry =>
          TMVerifierStackReadChoice.atomAt (V := V) (k := (tmVerifierTM V).k₀)
            0 entry.2 entry.1) ++
          [tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ (p.1 + p.2.length)]) := by
    have hInstrs := tmVerifierInputChoicePrefixMatchInstructions_tm_polytime V
    have hFold := tmVerifierInputChoicePrefixMatchFold_tm_polytime V
    have hOut := tmVerifierInputChoicePrefixMatchOutput_tm_polytime V
    have hFoldComp := TMPolyTimeMap.comp hFold hInstrs
    have hComp := TMPolyTimeMap.comp hOut hFoldComp
    convert hComp using 1
    funext p
    rw [Function.comp, Function.comp]
    exact (tmVerifierInputChoicePrefixMatchFold_instructions_eq V p.1 p.2).symm

theorem tmVerifierXOnlyInputChoicePrefixMatchLiterals_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod L.Instance
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V)))
      (EncodedType.list literalStructuredEncodedType)
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        tmVerifierXOnlyInputChoicePrefixMatchLiterals V p.1 p.2) := by
  let X := EncodedType.prod L.Instance
    (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  have hX : TMPolyTimeMap X L.Instance
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst L.Instance (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  have hChoices : TMPolyTimeMap X
      (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd L.Instance (EncodedType.list (tmVerifierInputReadChoiceEncodedType V))
  have hSize : TMPolyTimeMap X EncodedType.nat
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        L.Instance.inputSize p.1) := by
    have hComp := TMPolyTimeMap.comp (encodedInputSizeNatTMBackedMap L.Instance).tm_polytime hX
    simpa [Function.comp, X] using hComp
  have hStart : TMPolyTimeMap X EncodedType.nat
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        L.Instance.inputSize p.1 + 1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hSize
    simpa [Function.comp, Nat.succ_eq_add_one, X] using hComp
  have hInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list (tmVerifierInputReadChoiceEncodedType V)))
        (fun p : L.Instance.Carrier ×
            List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
          (L.Instance.inputSize p.1 + 1, p.2)) :=
    TMPolyTimeMap.prod_mk hStart hChoices
  have hFromStart := tmVerifierInputChoicePrefixMatchFromStart_tm_polytime V
  have hComp := TMPolyTimeMap.comp hFromStart hInput
  convert hComp using 1
  funext p
  rw [Function.comp, tmVerifierXOnlyInputChoicePrefixMatchLiterals]
  simp

theorem tmVerifierXOnlyInvalidInputChoicePrefixClause_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod L.Instance
        (EncodedType.list (tmVerifierInputReadChoiceEncodedType V)))
      clauseStructuredEncodedType
      (fun p : L.Instance.Carrier ×
          List (TMVerifierStackReadChoice V (tmVerifierTM V).k₀) =>
        tmVerifierXOnlyInvalidInputChoicePrefixClause V p.1 p.2) := by
  have hLits := tmVerifierXOnlyInputChoicePrefixMatchLiterals_tm_polytime V
  have hNeg := TMPolyTimeMap.list_map literalNegateTMBackedMap.tm_polytime
  have hComp := TMPolyTimeMap.comp hNeg hLits
  simpa [Function.comp, tmVerifierXOnlyInvalidInputChoicePrefixClause,
    clauseStructuredEncodedType] using hComp

theorem tmVerifierXOnlyEmittedCNF_tm_polytime_of_suffixValidityCNF
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V)
    (hSuffix :
      TMPolyTimeMap L.Instance cnfStructuredEncodedType
        (fun x : L.Instance.Carrier => tmVerifierXOnlySuffixValidityCNF V x)) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyEmittedCNF V B x) := by
  have hGlobal := tmVerifierXOnlyGlobalTableauCNF_tm_polytime V B
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyGlobalTableauCNF V B x,
            tmVerifierXOnlySuffixValidityCNF V x)) :=
    TMPolyTimeMap.prod_mk hGlobal hSuffix
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyEmittedCNF, cnfStructuredEncodedType] using hAppend

end SAT
end ComplexityReduction
