import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.BoolDispatch
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyInputPrefixTM

/-!
Direct standard-TM fold for x-only input-prefix literals.

The fold scans a typed list of verifier-input-stack symbols.  Its accumulator
stores the original symbol-list encoding size, the next cell index, and the
generated unit literals.  The size field makes the reachable-growth invariant
local to the source list while the semantic theorem identifies the output with
the existing `zipIdx` definition in `TMXOnlyCertificate`.
-/

namespace ComplexityReduction
namespace SAT

def tmVerifierInputPrefixLiteralAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))

abbrev TMVerifierInputPrefixLiteralAcc :=
  Nat × (Nat × List Literal)

def tmVerifierInputPrefixLiteralInit :
    TMVerifierInputPrefixLiteralAcc :=
  ((0 : Nat), ((0 : Nat), ([] : List Literal)))

noncomputable def tmVerifierInputPrefixLiteralStep {L : EncodedDecisionProblem}
    (V : TMVerifier L)
    (p : TMVerifierInputPrefixLiteralAcc ×
      (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier) :
    TMVerifierInputPrefixLiteralAcc :=
  match p.2 with
  | Sum.inl limit => (limit, (0, []))
  | Sum.inr s =>
      let limit := p.1.1
      let idx := p.1.2.1
      let out := p.1.2.2
      if idx < limit then
        (limit, (idx + 1, out ++ [tmVerifierInputStackSymbolAtom V 0 idx s]))
      else
        p.1

noncomputable def tmVerifierInputPrefixLiteralFold {L : EncodedDecisionProblem}
    (V : TMVerifier L)
    (instrs : List (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier) :
    TMVerifierInputPrefixLiteralAcc :=
  instrs.foldl (fun acc instr => tmVerifierInputPrefixLiteralStep V (acc, instr))
    tmVerifierInputPrefixLiteralInit

/-! ### Step witness -/

theorem tmVerifierInputPrefixLiteralStep_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.prod tmVerifierInputPrefixLiteralAccEncodedType
        (tmVerifierInputPrefixLiteralInstructionEncodedType V))
      tmVerifierInputPrefixLiteralAccEncodedType
      (tmVerifierInputPrefixLiteralStep V) := by
  let Acc := tmVerifierInputPrefixLiteralAccEncodedType
  let Sym := tmVerifierInputSymbolEncodedType V
  let Instr := tmVerifierInputPrefixLiteralInstructionEncodedType V
  let X := EncodedType.prod Acc Instr
  let Right := EncodedType.prod Acc Sym
  let RightCarrier := TMVerifierInputPrefixLiteralAcc ×
    (tmVerifierTM V).Γ (tmVerifierTM V).k₀
  have hChoice :
      TMPolyTimeMap X (prodSumChoiceEncodedType Acc EncodedType.nat Sym)
        (prodSumChoice Acc EncodedType.nat Sym) := by
    simpa [X, Instr, tmVerifierInputPrefixLiteralInstructionEncodedType, Sym] using
      prodSumChoice_tm_polytime Acc EncodedType.nat Sym
  have hLeft :
      TMPolyTimeMap EncodedType.nat Acc
        (fun limit : Nat => (limit, ((0 : Nat), ([] : List Literal)))) := by
    have hZero : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => (0 : Nat)) :=
      TMPolyTimeMap.const EncodedType.nat EncodedType.nat (0 : Nat)
    have hNil :
        TMPolyTimeMap EncodedType.nat (EncodedType.list literalStructuredEncodedType)
          (fun _ : Nat => ([] : List Literal)) :=
      TMPolyTimeMap.const EncodedType.nat (EncodedType.list literalStructuredEncodedType)
        ([] : List Literal)
    have hTail :
        TMPolyTimeMap EncodedType.nat
          (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
          (fun _ : Nat => ((0 : Nat), ([] : List Literal))) :=
      TMPolyTimeMap.prod_mk hZero hNil
    have hPair :
        TMPolyTimeMap EncodedType.nat Acc
          (fun limit : Nat => (limit, ((0 : Nat), ([] : List Literal)))) :=
      TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hTail
    simpa [Acc, tmVerifierInputPrefixLiteralAccEncodedType] using hPair
  have hAccRight : TMPolyTimeMap Right Acc (fun p : RightCarrier => p.1) := by
    simpa [Right, Acc, Sym] using TMPolyTimeMap.fst Acc Sym
  have hSymRight : TMPolyTimeMap Right Sym (fun p : RightCarrier => p.2) := by
    simpa [Right, Acc, Sym] using TMPolyTimeMap.snd Acc Sym
  have hLimit : TMPolyTimeMap Right EncodedType.nat (fun p : RightCarrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hAccRight
    simpa [Function.comp, Right, Acc, tmVerifierInputPrefixLiteralAccEncodedType] using hComp
  have hTailRight :
      TMPolyTimeMap Right
        (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
        (fun p : RightCarrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hAccRight
    simpa [Function.comp, Right, Acc, tmVerifierInputPrefixLiteralAccEncodedType] using hComp
  have hIdx : TMPolyTimeMap Right EncodedType.nat (fun p : RightCarrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTailRight
    simpa [Function.comp, Right] using hComp
  have hOut : TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
      (fun p : RightCarrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTailRight
    simpa [Function.comp, Right] using hComp
  have hNext : TMPolyTimeMap Right EncodedType.nat (fun p : RightCarrier => p.1.2.1 + 1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hIdx
    simpa [Function.comp, Nat.succ_eq_add_one, Right] using hComp
  have hAtomInput :
      TMPolyTimeMap Right (EncodedType.prod EncodedType.nat Sym)
        (fun p : RightCarrier => (p.1.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hIdx hSymRight
  have hAtom : TMPolyTimeMap Right literalStructuredEncodedType
      (fun p : RightCarrier => tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2) := by
    have hComp := TMPolyTimeMap.comp
      (tmVerifierInputStackSymbolAtom_indexed_tm_polytime V) hAtomInput
    simpa [Function.comp, Right, Sym] using hComp
  have hAtomSingleton :
      TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
        (fun p : RightCarrier => [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hAtom
    simpa [Function.comp, Right] using hComp
  have hAppendInput :
      TMPolyTimeMap Right
        (EncodedType.prod (EncodedType.list literalStructuredEncodedType)
          (EncodedType.list literalStructuredEncodedType))
        (fun p : RightCarrier =>
          (p.1.2.2, [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2])) :=
    TMPolyTimeMap.prod_mk hOut hAtomSingleton
  have hAppend :
      TMPolyTimeMap Right (EncodedType.list literalStructuredEncodedType)
        (fun p : RightCarrier =>
          p.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
    simpa [Function.comp, Right] using hComp
  have hTrueTail :
      TMPolyTimeMap Right
        (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
        (fun p : RightCarrier =>
          (p.1.2.1 + 1,
            p.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2])) :=
    TMPolyTimeMap.prod_mk hNext hAppend
  have hTrue :
      TMPolyTimeMap Right Acc
        (fun p : RightCarrier =>
          (p.1.1,
            (p.1.2.1 + 1,
              p.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2]))) :=
    TMPolyTimeMap.prod_mk hLimit hTrueTail
  have hCompareInput :
      TMPolyTimeMap Right (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : RightCarrier => (p.1.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hIdx hLimit
  have hTag : TMPolyTimeMap Right EncodedType.bool
      (fun p : RightCarrier => decide (p.1.2.1 < p.1.1)) := by
    have hComp := TMPolyTimeMap.comp natLtBool_tm_polytime hCompareInput
    simpa [Function.comp, natLtBool, Right] using hComp
  have hBranchInput :
      TMPolyTimeMap Right (EncodedType.prod EncodedType.bool Right)
        (fun p : RightCarrier => (decide (p.1.2.1 < p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id Right)
  have hRight :
      TMPolyTimeMap Right Acc
        (fun p : RightCarrier =>
          if p.1.2.1 < p.1.1 then
            (p.1.1,
              (p.1.2.1 + 1,
                p.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2]))
          else p.1) := by
    have hBranch :
        TMPolyTimeMap (EncodedType.prod EncodedType.bool Right) Acc
          (fun q : Bool × RightCarrier =>
            match q.1 with
            | true =>
                (q.2.1.1,
                  (q.2.1.2.1 + 1,
                    q.2.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 q.2.1.2.1 q.2.2]))
            | false => q.2.1) :=
      boolProduct_dispatch_tm_polytime Right Acc
        (fFalse := fun p : RightCarrier => p.1)
        (fTrue := fun p : RightCarrier =>
          (p.1.1,
            (p.1.2.1 + 1,
              p.1.2.2 ++ [tmVerifierInputStackSymbolAtom V 0 p.1.2.1 p.2])))
        hAccRight hTrue
    have hComp := TMPolyTimeMap.comp hBranch hBranchInput
    convert hComp using 1
    ext p
    by_cases hlt : p.1.2.1 < p.1.1 <;> simp [hlt]
  have hSum :=
    TMPolyTimeMap.sum_elim
      (X := EncodedType.nat) (Y := Right) (Z := Acc) hLeft hRight
  have hComp := TMPolyTimeMap.comp hSum hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> simp [tmVerifierInputPrefixLiteralStep, prodSumChoice, Instr,
    tmVerifierInputPrefixLiteralInstructionEncodedType, Sym] <;> rfl

/-! ### Fold witness and semantics -/

theorem tmVerifierInputPrefixLiteralStep_inv
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {N : Nat} {acc : TMVerifierInputPrefixLiteralAcc}
    (hLimit : acc.1 ≤ N) (hIdx : acc.2.1 ≤ acc.1)
    (instr : (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier)
    (hInstr : (tmVerifierInputPrefixLiteralInstructionEncodedType V).inputSize instr ≤ N) :
    let next := tmVerifierInputPrefixLiteralStep V (acc, instr)
    next.1 ≤ N ∧ next.2.1 ≤ next.1 := by
  cases instr with
  | inl limit =>
      change Nat at limit
      have hLimitN : limit ≤ N := by
        have h : limit + 2 ≤ N := by
          simpa [tmVerifierInputPrefixLiteralInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, EncodedType.nat] using hInstr
        omega
      simp [tmVerifierInputPrefixLiteralStep, hLimitN]
  | inr s =>
      by_cases hlt : acc.2.1 < acc.1
      · have hNextIdx : acc.2.1 + 1 ≤ acc.1 := Nat.succ_le_of_lt hlt
        simp [tmVerifierInputPrefixLiteralStep, hlt, hLimit, hNextIdx]
      · simp [tmVerifierInputPrefixLiteralStep, hlt, hLimit, hIdx]

theorem tmVerifierInputPrefixLiteralAcc_inputSize_reset (limit : Nat) :
    tmVerifierInputPrefixLiteralAccEncodedType.inputSize
        (limit, ((0 : Nat), ([] : List Literal))) =
      limit + 4 := by
  change
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))).inputSize
        (limit, ((0 : Nat), ([] : List Literal))) =
      limit + 4
  rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod]
  rw [show (EncodedType.list literalStructuredEncodedType).inputSize ([] : List Literal) = 0 by
    exact EncodedType.inputSize_list_nil literalStructuredEncodedType]
  simp [EncodedType.inputSize_nat]

theorem tmVerifierInputPrefixLiteralAcc_inputSize_append_atom
    (limit idx : Nat) (out : List Literal) (lit : Literal) :
    tmVerifierInputPrefixLiteralAccEncodedType.inputSize
        (limit, (idx + 1, out ++ [lit])) =
      tmVerifierInputPrefixLiteralAccEncodedType.inputSize (limit, (idx, out)) +
        literalStructuredEncodedType.inputSize lit + 2 := by
  change
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))).inputSize
        (limit, (idx + 1, out ++ [lit])) =
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))).inputSize
          (limit, (idx, out)) +
        literalStructuredEncodedType.inputSize lit + 2
  rw [EncodedType.inputSize_prod, EncodedType.inputSize_prod,
    EncodedType.inputSize_prod, EncodedType.inputSize_prod]
  rw [show (EncodedType.list literalStructuredEncodedType).inputSize (out ++ [lit]) =
      (EncodedType.list literalStructuredEncodedType).inputSize out +
        literalStructuredEncodedType.inputSize lit + 1 by
    simpa using
      list_inputSize_append literalStructuredEncodedType out [lit]]
  simp [EncodedType.inputSize_nat]
  omega

theorem tmVerifierInputPrefixLiteralFold_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
      tmVerifierInputPrefixLiteralAccEncodedType
      (tmVerifierInputPrefixLiteralFold V) := by
  rcases tmVerifierInputPrefixLiteralStep_tm_polytime V with ⟨hStep⟩
  rcases tmVerifierInputStackSymbolAtom_indexed_tm_polytime V with ⟨hAtom⟩
  let Instr := tmVerifierInputPrefixLiteralInstructionEncodedType V
  let Acc := tmVerifierInputPrefixLiteralAccEncodedType
  let Sym := tmVerifierInputSymbolEncodedType V
  let B := TM2Programs.finTM2StepPushBound hAtom.tm
  let grow : Polynomial Nat :=
    Polynomial.X + Polynomial.C 8 +
      hAtom.time.comp (Polynomial.X + Polynomial.C 3) * Polynomial.C B
  let Inv : Nat → Acc.Carrier → Prop :=
    fun N (acc : TMVerifierInputPrefixLiteralAcc) => acc.1 ≤ N ∧ acc.2.1 ≤ acc.1
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      Instr Acc (tmVerifierInputPrefixLiteralStep V) tmVerifierInputPrefixLiteralInit
      hStep (Polynomial.C 4) grow Inv ?_ ?_
  · intro source
    constructor
    · simp [Inv, tmVerifierInputPrefixLiteralInit]
    · have hSize := tmVerifierInputPrefixLiteralAcc_inputSize_reset 0
      simpa [Acc, tmVerifierInputPrefixLiteralInit] using hSize.le
  · intro source acc instr hInv hInstrSize
    change TMVerifierInputPrefixLiteralAcc at acc
    let N := (EncodedType.list Instr).inputSize source
    have hInvNext :
        Inv N (tmVerifierInputPrefixLiteralStep V (acc, instr)) := by
      exact tmVerifierInputPrefixLiteralStep_inv V hInv.1 hInv.2 instr (by simpa [N] using hInstrSize)
    constructor
    · exact hInvNext
    · cases instr with
      | inl limit =>
          change Nat at limit
          have hLimitN : limit ≤ N := by
            have h : limit + 2 ≤ N := by
              simpa [Instr, tmVerifierInputPrefixLiteralInstructionEncodedType,
                EncodedType.inputSize, EncodedType.sum, EncodedType.nat, N] using hInstrSize
            omega
          have hGrowEval :
              grow.eval N = N + 8 + hAtom.time.eval (N + 3) * B := by
            simp [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
              Polynomial.eval_X, B]
          calc
            Acc.inputSize (tmVerifierInputPrefixLiteralStep V (acc, Sum.inl limit))
                = limit + 4 := by
                  simpa [Acc, tmVerifierInputPrefixLiteralStep] using
                    tmVerifierInputPrefixLiteralAcc_inputSize_reset limit
            _ ≤ Acc.inputSize acc + grow.eval N := by
                  rw [hGrowEval]
                  nlinarith [hLimitN, Nat.zero_le (Acc.inputSize acc),
                    Nat.zero_le (hAtom.time.eval (N + 3) * B)]
      | inr s =>
          by_cases hlt : acc.2.1 < acc.1
          · let atom := tmVerifierInputStackSymbolAtom V 0 acc.2.1 s
            have hAtomInput :
                (EncodedType.prod EncodedType.nat Sym).inputSize (acc.2.1, s) ≤ N + 3 := by
              rw [EncodedType.inputSize_prod]
              change EncodedType.nat.inputSize acc.2.1 + 1 + Sym.inputSize s ≤ N + 3
              have hs : Sym.inputSize s = 1 := by
                simp [Sym, tmVerifierInputSymbolEncodedType]
              simp [EncodedType.inputSize_nat, hs]
              have hIdxN : acc.2.1 ≤ N := hInv.2.trans hInv.1
              omega
            have hAtomOut :=
              TM2Programs.tm2ComputableInPolyTime_output_length_le hAtom (acc.2.1, s)
            have hAtomSize :
                literalStructuredEncodedType.inputSize atom ≤
                  N + 3 + hAtom.time.eval (N + 3) * B := by
              have hTimeMono :
                  hAtom.time.eval
                      ((EncodedType.prod EncodedType.nat Sym).inputSize (acc.2.1, s)) ≤
                    hAtom.time.eval (N + 3) :=
                TM2Programs.polynomialNat_eval_mono hAtom.time hAtomInput
              have hOut' :
                  literalStructuredEncodedType.inputSize atom ≤
                    (EncodedType.prod EncodedType.nat Sym).inputSize (acc.2.1, s) +
                      hAtom.time.eval
                          ((EncodedType.prod EncodedType.nat Sym).inputSize (acc.2.1, s)) * B := by
                simpa [EncodedType.inputSize, atom, B, Sym] using hAtomOut
              nlinarith [hOut', hAtomInput, hTimeMono, Nat.zero_le B]
            have hStepSize :
                Acc.inputSize (tmVerifierInputPrefixLiteralStep V (acc, Sum.inr s)) =
                  Acc.inputSize acc + literalStructuredEncodedType.inputSize atom + 2 := by
              simp [tmVerifierInputPrefixLiteralStep, hlt]
              simpa [Acc, atom] using
                tmVerifierInputPrefixLiteralAcc_inputSize_append_atom acc.1 acc.2.1 acc.2.2 atom
            have hGrowEval :
                grow.eval N = N + 8 + hAtom.time.eval (N + 3) * B := by
              simp [grow, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
                Polynomial.eval_X, B]
            calc
              Acc.inputSize (tmVerifierInputPrefixLiteralStep V (acc, Sum.inr s))
                  = Acc.inputSize acc + literalStructuredEncodedType.inputSize atom + 2 :=
                    hStepSize
              _ ≤ Acc.inputSize acc + grow.eval N := by
                    rw [hGrowEval]
                    nlinarith [hAtomSize]
          · simp [tmVerifierInputPrefixLiteralStep, hlt]

theorem tmVerifierInputPrefixLiteralFoldWith_symbols
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (limit idx : Nat) (out : List Literal)
    (xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀))
    (h : idx + xs.length ≤ limit) :
    xs.foldl
        (fun acc s => tmVerifierInputPrefixLiteralStep V
          (acc, tmVerifierInputPrefixLiteralSymbolInstruction V s))
        (limit, (idx, out)) =
      (limit,
        (idx + xs.length,
          out ++
            (xs.zipIdx idx).map fun entry =>
              tmVerifierInputStackSymbolAtom V 0 entry.2 entry.1)) := by
  induction xs generalizing idx out with
  | nil =>
      simp
  | cons s rest ih =>
      have hlt : idx < limit := by
        have hOne : 1 ≤ (s :: rest).length := by simp
        have : idx + 1 ≤ limit := by
          calc
            idx + 1 ≤ idx + (s :: rest).length := Nat.add_le_add_left hOne idx
            _ ≤ limit := h
        omega
      have hrest : idx + 1 + rest.length ≤ limit := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      rw [List.foldl_cons]
      simp [tmVerifierInputPrefixLiteralStep, tmVerifierInputPrefixLiteralSymbolInstruction,
        hlt]
      have hih := ih (idx + 1)
        (out ++ [tmVerifierInputStackSymbolAtom V 0 idx s]) hrest
      simpa [List.zipIdx_cons, List.map_map, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hih

theorem tmVerifierInputPrefixLiteralFold_instructions_eq_zipIdx
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)) :
    (tmVerifierInputPrefixLiteralFold V
      (tmVerifierInputPrefixLiteralInstructions V xs)).2.2 =
      (xs.zipIdx.map fun entry =>
        tmVerifierInputStackSymbolAtom V 0 entry.2 entry.1) := by
  have hFold :=
    tmVerifierInputPrefixLiteralFoldWith_symbols V
      ((EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize xs)
      0 ([] : List Literal) xs
      (by
        have hLen :
            xs.length ≤ (EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize xs := by
          induction xs with
          | nil => simp
          | cons s rest ih =>
              have hs : (tmVerifierInputSymbolEncodedType V).inputSize s = 1 := by
                simp [tmVerifierInputSymbolEncodedType]
              change
                (s :: rest).length ≤
                  (EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize (s :: rest)
              rw [EncodedType.inputSize_list_cons (tmVerifierInputSymbolEncodedType V) s rest]
              rw [hs]
              change rest.length + 1 ≤ 1 + 1 +
                (EncodedType.list (tmVerifierInputSymbolEncodedType V)).inputSize rest
              omega
        simpa using hLen)
  rw [tmVerifierInputPrefixLiteralFold, tmVerifierInputPrefixLiteralInstructions]
  simp [tmVerifierInputPrefixLiteralInitInstruction, tmVerifierInputPrefixLiteralInit,
    tmVerifierInputPrefixLiteralStep]
  rw [List.foldl_map]
  exact congrArg (fun acc => acc.2.2) hFold

theorem tmVerifierInputPrefixLiteralFold_output_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap
      (EncodedType.list (tmVerifierInputPrefixLiteralInstructionEncodedType V))
      (EncodedType.list literalStructuredEncodedType)
      (fun instrs : List (tmVerifierInputPrefixLiteralInstructionEncodedType V).Carrier =>
        (tmVerifierInputPrefixLiteralFold V instrs).2.2) := by
  let Acc := tmVerifierInputPrefixLiteralAccEncodedType
  have hFold := tmVerifierInputPrefixLiteralFold_tm_polytime V
  have hTail :
      TMPolyTimeMap Acc
        (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
        (fun acc : TMVerifierInputPrefixLiteralAcc => acc.2) := by
    simpa [Acc, tmVerifierInputPrefixLiteralAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat (EncodedType.list literalStructuredEncodedType))
  have hOut :
      TMPolyTimeMap Acc (EncodedType.list literalStructuredEncodedType)
        (fun acc : TMVerifierInputPrefixLiteralAcc => acc.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.list literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Acc] using hComp
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp] using hComp

theorem tmVerifierInstanceInputPrefixLiterals_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance (EncodedType.list literalStructuredEncodedType)
      (fun x : L.Instance.Carrier => tmVerifierInstanceInputPrefixLiterals V x) := by
  have hWord := tmVerifierInstanceInputPrefixWord_tm_polytime V
  have hWordList :
      TMPolyTimeMap L.Instance (EncodedType.list (tmVerifierInputSymbolEncodedType V))
        (fun x : L.Instance.Carrier => tmVerifierInstanceInputPrefixWord V x) := by
    letI : Fintype ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) := (tmVerifierTM V).Γk₀Fin
    have hRawToList :
        TMPolyTimeMap
          (symbolListEncodedType ((tmVerifierTM V).Γ (tmVerifierTM V).k₀))
          (EncodedType.list (tmVerifierInputSymbolEncodedType V))
          (fun xs : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) => xs) := by
      simpa [tmVerifierInputSymbolEncodedType] using
        @rawSymbols_to_finiteSymbolList_tm_polytime
          ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)
          (tmVerifierTM V).Γk₀Fin
    have hComp := TMPolyTimeMap.comp hRawToList hWord
    simpa [Function.comp] using hComp
  have hInstrs := tmVerifierInputPrefixLiteralInstructions_tm_polytime V
  have hInstrsX := TMPolyTimeMap.comp hInstrs hWordList
  have hFoldOut := tmVerifierInputPrefixLiteralFold_output_tm_polytime V
  have hComp := TMPolyTimeMap.comp hFoldOut hInstrsX
  convert hComp using 1
  funext x
  rw [Function.comp, Function.comp]
  rw [tmVerifierInputPrefixLiteralFold_instructions_eq_zipIdx]
  rfl

theorem tmVerifierInstanceInputPrefixCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierInstanceInputPrefixCNF V x) := by
  have hLits := tmVerifierInstanceInputPrefixLiterals_tm_polytime V
  have hComp := TMPolyTimeMap.comp tmVerifierUnitClauses_tm_polytime hLits
  simpa [Function.comp, tmVerifierInstanceInputPrefixCNF] using hComp

theorem tmVerifierXOnlyInputStackEmptyTailUnitCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier =>
        tmVerifierUnitClauses (tmVerifierXOnlyInputStackEmptyTailLiterals V x)) := by
  have hZero :
      TMPolyTimeMap L.Instance EncodedType.nat (fun _ : L.Instance.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const L.Instance EncodedType.nat (0 : Nat)
  have hBound := tmVerifierXOnlyInputLengthBound_tm_polytime V
  have hCtx :
      TMPolyTimeMap L.Instance (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun x : L.Instance.Carrier => ((0 : Nat), tmVerifierXOnlyInputLengthBound V x)) :=
    TMPolyTimeMap.prod_mk hZero hBound
  have hCells := tmVerifierXOnlyCellRange_tm_polytime V
  have hInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod (EncodedType.prod EncodedType.nat EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun x : L.Instance.Carrier =>
          (((0 : Nat), tmVerifierXOnlyInputLengthBound V x),
            tmVerifierXOnlyCellRange V x)) :=
    TMPolyTimeMap.prod_mk hCtx hCells
  have hFold := cnfContextFlatMap_tm_polytime
    (C := EncodedType.prod EncodedType.nat EncodedType.nat) (X := EncodedType.nat)
    (fun (ctx : Nat × Nat) (cell : Nat) =>
      if ctx.2 ≤ cell then
        tmVerifierUnitCNF (tmVerifierStackEmptyAtom V ctx.1 (tmVerifierTM V).k₀ cell)
      else
        ([] : CNF))
    (tmVerifierLowerBoundStackEmptyUnitCNF_block_tm_polytime V (tmVerifierTM V).k₀)
  have hComp := TMPolyTimeMap.comp hFold hInput
  convert hComp using 1
  funext x
  rw [Function.comp]
  rw [tmVerifierXOnlyInputStackEmptyTailLiterals]
  exact tmVerifierUnitClauses_filter_map_eq_flatMap_unitCNF_le
    (tmVerifierXOnlyInputLengthBound V x)
    (fun cell => tmVerifierStackEmptyAtom V 0 (tmVerifierTM V).k₀ cell)
    (tmVerifierXOnlyCellRange V x)

theorem tmVerifierXOnlyInputStackInitialCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyInputStackInitialCNF V x) := by
  have hPrefix := tmVerifierInstanceInputPrefixCNF_tm_polytime V
  have hTail := tmVerifierXOnlyInputStackEmptyTailUnitCNF_tm_polytime V
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierInstanceInputPrefixCNF V x,
            tmVerifierUnitClauses (tmVerifierXOnlyInputStackEmptyTailLiterals V x))) :=
    TMPolyTimeMap.prod_mk hPrefix hTail
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyInputStackInitialCNF,
    tmVerifierInstanceInputPrefixCNF, tmVerifierUnitClauses_append,
    cnfStructuredEncodedType] using hAppend

theorem tmVerifierXOnlyInitialStackCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyInitialStackCNF V x) := by
  have hInput := tmVerifierXOnlyInputStackInitialCNF_tm_polytime V
  have hNonInput := tmVerifierXOnlyInitialNonInputEmptyStackCNF_tm_polytime V
  have hAppendInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (tmVerifierXOnlyInputStackInitialCNF V x,
            tmVerifierXOnlyInitialNonInputEmptyStackCNF V x)) :=
    TMPolyTimeMap.prod_mk hInput hNonInput
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, tmVerifierXOnlyInitialStackCNF, cnfStructuredEncodedType]
    using hAppend

end SAT
end ComplexityReduction
