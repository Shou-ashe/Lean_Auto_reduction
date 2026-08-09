import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Prefix
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

def literalRowInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod literalStructuredEncodedType EncodedType.nat

def literalRowInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool literalRowInstructionPayloadEncodedType

def literalRowInstructionListEncodedType : EncodedType :=
  EncodedType.list literalRowInstructionEncodedType

def literalRowInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat literalStructuredEncodedType

def literalRowAccEncodedType : EncodedType :=
  EncodedType.prod literalStructuredEncodedType intRowStructuredEncodedType

def literalRowStepInputEncodedType : EncodedType :=
  EncodedType.prod literalRowAccEncodedType literalRowInstructionEncodedType

abbrev LiteralRowInstruction := Bool × (SAT.Literal × Nat)
abbrev LiteralRowInput := Nat × SAT.Literal
abbrev LiteralRowAcc := SAT.Literal × List Int
abbrev LiteralRowStepInput := LiteralRowAcc × LiteralRowInstruction

def literalRowInitAcc : LiteralRowAcc :=
  (defaultLiteralForIPRows, [])

def literalRowInitInstruction (l : SAT.Literal) : LiteralRowInstruction :=
  (false, (l, 0))

def literalRowIndexInstruction (i : Nat) : LiteralRowInstruction :=
  (true, (defaultLiteralForIPRows, i))

def literalRowInstructions (p : LiteralRowInput) : List LiteralRowInstruction :=
  literalRowInitInstruction p.2 :: (List.range p.1).map literalRowIndexInstruction

def literalRowStep (p : LiteralRowStepInput) : LiteralRowAcc :=
  if p.2.1 then
    (p.1.1, p.1.2 ++ [literalCoeffAt p.1.1 p.2.2.2])
  else
    (p.2.2.1, [])

def literalRowInstructionsFold (xs : List LiteralRowInstruction) : LiteralRowAcc :=
  xs.foldl (fun acc instr => literalRowStep (acc, instr)) literalRowInitAcc

def literalRowFromInstructions (xs : List LiteralRowInstruction) : List Int :=
  (literalRowInstructionsFold xs).2

def literalRowRunner (p : LiteralRowInput) : List Int :=
  literalRowFromInstructions (literalRowInstructions p)

theorem literalRowFrom_succ_append (start n : Nat) (l : SAT.Literal) :
    literalRowFrom start (n + 1) l =
      literalRowFrom start n l ++ [literalCoeffAt l (start + n)] := by
  induction n generalizing start with
  | zero =>
      simp [literalRowFrom]
  | succ n ih =>
      change
        literalCoeffAt l start :: literalRowFrom (start + 1) (n + 1) l =
          literalCoeffAt l start ::
            (literalRowFrom (start + 1) n l ++ [literalCoeffAt l (start + (n + 1))])
      rw [ih (start + 1)]
      have hIndex : (start + 1) + n = start + (n + 1) := by
        omega
      simp [hIndex]

theorem literalRow_succ_append (n : Nat) (l : SAT.Literal) :
    literalRow (n + 1) l = literalRow n l ++ [literalCoeffAt l n] := by
  simpa [literalRow] using literalRowFrom_succ_append 0 n l

theorem literalRowIndexInstructions_fold_eq
    (n : Nat) (l : SAT.Literal) (row : List Int) :
    ((List.range n).map literalRowIndexInstruction).foldl
        (fun acc instr => literalRowStep (acc, instr)) (l, row) =
      (l, row ++ literalRow n l) := by
  induction n generalizing row with
  | zero =>
      simp [literalRow, literalRowFrom]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      rw [ih row]
      simp [literalRowIndexInstruction, literalRowStep, literalRow_succ_append,
        List.append_assoc]

theorem literalRowInstructionsFold_eq (p : LiteralRowInput) :
    literalRowInstructionsFold (literalRowInstructions p) =
      (p.2, literalRow p.1 p.2) := by
  rcases p with ⟨n, l⟩
  simpa [literalRowInstructionsFold, literalRowInstructions, literalRowInitInstruction,
    literalRowStep] using literalRowIndexInstructions_fold_eq n l ([] : List Int)

theorem literalRowRunner_eq_literalRow (p : LiteralRowInput) :
    literalRowRunner p = literalRow p.1 p.2 := by
  have h := congrArg Prod.snd (literalRowInstructionsFold_eq p)
  simpa [literalRowRunner, literalRowFromInstructions] using h

theorem literalRowInitInstruction_tm_polytime :
    TMPolyTimeMap
      literalStructuredEncodedType
      literalRowInstructionEncodedType
      literalRowInitInstruction := by
  have hFalse :
      TMPolyTimeMap literalStructuredEncodedType EncodedType.bool
        (fun _ : SAT.Literal => false) :=
    TMPolyTimeMap.const literalStructuredEncodedType EncodedType.bool false
  have hLit :
      TMPolyTimeMap literalStructuredEncodedType literalStructuredEncodedType
        (fun l : SAT.Literal => l) :=
    TMPolyTimeMap.id literalStructuredEncodedType
  have hZero :
      TMPolyTimeMap literalStructuredEncodedType EncodedType.nat
        (fun _ : SAT.Literal => (0 : Nat)) :=
    TMPolyTimeMap.const literalStructuredEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap literalStructuredEncodedType literalRowInstructionPayloadEncodedType
        (fun l : SAT.Literal => (l, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hLit hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [literalRowInitInstruction, literalRowInstructionEncodedType,
    literalRowInstructionPayloadEncodedType] using hOut

theorem literalRowIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      literalRowInstructionEncodedType
      literalRowIndexInstruction := by
  have hTrue :
      TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hLit :
      TMPolyTimeMap EncodedType.nat literalStructuredEncodedType
        (fun _ : Nat => defaultLiteralForIPRows) :=
    TMPolyTimeMap.const EncodedType.nat literalStructuredEncodedType defaultLiteralForIPRows
  have hIndex : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun i : Nat => i) :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat literalRowInstructionPayloadEncodedType
        (fun i : Nat => (defaultLiteralForIPRows, i)) :=
    TMPolyTimeMap.prod_mk hLit hIndex
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [literalRowIndexInstruction, literalRowInstructionEncodedType,
    literalRowInstructionPayloadEncodedType] using hOut

theorem literalRowInstructions_tm_polytime :
    TMPolyTimeMap
      literalRowInputEncodedType
      literalRowInstructionListEncodedType
      literalRowInstructions := by
  let X := literalRowInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : LiteralRowInput => p.1) := by
    simpa [X, literalRowInputEncodedType, LiteralRowInput] using
      TMPolyTimeMap.fst EncodedType.nat literalStructuredEncodedType
  have hLit : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : LiteralRowInput => p.2) := by
    simpa [X, literalRowInputEncodedType, LiteralRowInput] using
      TMPolyTimeMap.snd EncodedType.nat literalStructuredEncodedType
  have hInit :
      TMPolyTimeMap X literalRowInstructionEncodedType
        (fun p : LiteralRowInput => literalRowInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp literalRowInitInstruction_tm_polytime hLit
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : LiteralRowInput => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hIndexInstrs :
      TMPolyTimeMap X literalRowInstructionListEncodedType
        (fun p : LiteralRowInput => (List.range p.1).map literalRowIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map literalRowIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, literalRowInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod literalRowInstructionEncodedType literalRowInstructionListEncodedType)
        (fun p : LiteralRowInput =>
          (literalRowInitInstruction p.2,
            (List.range p.1).map literalRowIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalRowInstructionEncodedType) hConsInput
  simpa [Function.comp, literalRowInstructions, literalRowInstructionListEncodedType, X]
    using hOut

theorem literalRowAcc_mk_tm_polytime
    {X : EncodedType} {lit : X.Carrier → SAT.Literal} {row : X.Carrier → List Int}
    (hLit : TMPolyTimeMap X literalStructuredEncodedType lit)
    (hRow : TMPolyTimeMap X intRowStructuredEncodedType row) :
    TMPolyTimeMap X literalRowAccEncodedType (fun x => (lit x, row x)) := by
  simpa [literalRowAccEncodedType] using TMPolyTimeMap.prod_mk hLit hRow

theorem literalRowStep_tm_polytime :
    TMPolyTimeMap
      literalRowStepInputEncodedType
      literalRowAccEncodedType
      literalRowStep := by
  let X := literalRowStepInputEncodedType
  have hAcc : TMPolyTimeMap X literalRowAccEncodedType
      (fun p : LiteralRowStepInput => p.1) := by
    simpa [X, literalRowStepInputEncodedType, LiteralRowStepInput] using
      TMPolyTimeMap.fst literalRowAccEncodedType literalRowInstructionEncodedType
  have hInstr : TMPolyTimeMap X literalRowInstructionEncodedType
      (fun p : LiteralRowStepInput => p.2) := by
    simpa [X, literalRowStepInputEncodedType, LiteralRowStepInput] using
      TMPolyTimeMap.snd literalRowAccEncodedType literalRowInstructionEncodedType
  have hAccLit : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : LiteralRowStepInput => p.1.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType intRowStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, literalRowAccEncodedType, X, LiteralRowStepInput] using hComp
  have hAccRow : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : LiteralRowStepInput => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType intRowStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, literalRowAccEncodedType, X, LiteralRowStepInput] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : LiteralRowStepInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool literalRowInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, literalRowInstructionEncodedType, X, LiteralRowStepInput] using hComp
  have hPayload : TMPolyTimeMap X literalRowInstructionPayloadEncodedType
      (fun p : LiteralRowStepInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool literalRowInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, literalRowInstructionEncodedType, X, LiteralRowStepInput] using hComp
  have hInstrLit : TMPolyTimeMap X literalStructuredEncodedType
      (fun p : LiteralRowStepInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, literalRowInstructionPayloadEncodedType, X, LiteralRowStepInput]
      using hComp
  have hIndex : TMPolyTimeMap X EncodedType.nat
      (fun p : LiteralRowStepInput => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, literalRowInstructionPayloadEncodedType, X, LiteralRowStepInput]
      using hComp
  have hEmpty : TMPolyTimeMap X intRowStructuredEncodedType
      (fun _ : LiteralRowStepInput => ([] : List Int)) :=
    TMPolyTimeMap.const X intRowStructuredEncodedType []
  have hFalseBranch :
      TMPolyTimeMap X literalRowAccEncodedType
        (fun p : LiteralRowStepInput => (p.2.2.1, ([] : List Int))) :=
    literalRowAcc_mk_tm_polytime hInstrLit hEmpty
  have hCoeffInput :
      TMPolyTimeMap X literalCoeffAtInputEncodedType
        (fun p : LiteralRowStepInput => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccLit hIndex
  have hCoeff : TMPolyTimeMap X EncodedType.int
      (fun p : LiteralRowStepInput => literalCoeffAt p.1.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp literalCoeffAt_tm_polytime hCoeffInput
    simpa [Function.comp, literalCoeffAtInputEncodedType, X, LiteralRowStepInput] using hComp
  have hSingleton :
      TMPolyTimeMap X intRowStructuredEncodedType
        (fun p : LiteralRowStepInput => [literalCoeffAt p.1.1 p.2.2.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.int) hCoeff
    simpa [Function.comp, intRowStructuredEncodedType, X, LiteralRowStepInput] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod intRowStructuredEncodedType intRowStructuredEncodedType)
        (fun p : LiteralRowStepInput =>
          (p.1.2, [literalCoeffAt p.1.1 p.2.2.2])) :=
    TMPolyTimeMap.prod_mk hAccRow hSingleton
  have hAppend : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : LiteralRowStepInput =>
        p.1.2 ++ [literalCoeffAt p.1.1 p.2.2.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.int) hAppendInput
    simpa [Function.comp, intRowStructuredEncodedType, X, LiteralRowStepInput] using hComp
  have hTrueBranch :
      TMPolyTimeMap X literalRowAccEncodedType
        (fun p : LiteralRowStepInput =>
          (p.1.1, p.1.2 ++ [literalCoeffAt p.1.1 p.2.2.2])) :=
    literalRowAcc_mk_tm_polytime hAccLit hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : LiteralRowStepInput => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) literalRowAccEncodedType
        (fun p : Bool × LiteralRowStepInput =>
          match p.1 with
          | true => (p.2.1.1, p.2.1.2 ++ [literalCoeffAt p.2.1.1 p.2.2.2.2])
          | false => (p.2.2.2.1, ([] : List Int))) :=
    Clique.boolProduct_dispatch_tm_polytime X literalRowAccEncodedType
      (fFalse := fun p : LiteralRowStepInput => (p.2.2.1, ([] : List Int)))
      (fTrue := fun p : LiteralRowStepInput =>
        (p.1.1, p.1.2 ++ [literalCoeffAt p.1.1 p.2.2.2]))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨lit, row⟩, ⟨tag, instrLit, i⟩⟩
  cases tag <;> simp [literalRowStep, Function.comp] <;> rfl

theorem literalRowStep_growth
    (source : List LiteralRowInstruction) (acc : LiteralRowAcc)
    (instr : LiteralRowInstruction)
    (hinstr : literalRowInstructionEncodedType.inputSize instr ≤
      literalRowInstructionListEncodedType.inputSize source) :
    literalRowAccEncodedType.inputSize (literalRowStep (acc, instr)) ≤
      literalRowAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 30).eval
          (literalRowInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨lit, row⟩
  rcases instr with ⟨tag, instrLit, i⟩
  cases tag
  · have hEmptyRaw :
        (EncodedType.list EncodedType.int).inputSize ([] : List Int) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.int
    simp [literalRowStep, literalRowAccEncodedType, intRowStructuredEncodedType,
      literalRowInstructionEncodedType, literalRowInstructionPayloadEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat,
      hEmptyRaw, Polynomial.eval_add, Polynomial.eval_mul] at hinstr ⊢
    omega
  · have hCoeff := literalCoeffAt_bound lit i
    have hCoeff3 :
        -((3 : Nat) : Int) ≤ literalCoeffAt lit i ∧
          literalCoeffAt lit i ≤ ((3 : Nat) : Int) := by
      constructor <;> omega
    have hCoeffSize :
        EncodedType.int.inputSize (literalCoeffAt lit i) ≤ 5 :=
      intStructured_inputSize_le_five_of_between_three hCoeff3.1 hCoeff3.2
    have hAppend :
        (EncodedType.list EncodedType.int).inputSize (row ++ [literalCoeffAt lit i]) =
          (EncodedType.list EncodedType.int).inputSize row +
            (EncodedType.list EncodedType.int).inputSize [literalCoeffAt lit i] := by
      simpa using
        list_inputSize_append EncodedType.int row [literalCoeffAt lit i]
    have hSingleton :
        (EncodedType.list EncodedType.int).inputSize [literalCoeffAt lit i] ≤ 6 := by
      simp at hCoeffSize ⊢
      omega
    simp [literalRowStep, literalRowAccEncodedType, intRowStructuredEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul]
    rw [hAppend]
    omega

theorem literalRowFromInstructions_tm_polytime :
    TMPolyTimeMap
      literalRowInstructionListEncodedType
      intRowStructuredEncodedType
      literalRowFromInstructions := by
  rcases literalRowStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        literalRowInstructionListEncodedType
        literalRowAccEncodedType
        literalRowInstructionsFold := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        literalRowInstructionEncodedType literalRowAccEncodedType
        literalRowStep literalRowInitAcc hStep
        (Polynomial.C 100) (Polynomial.C 10 * Polynomial.X + Polynomial.C 30) ?_ ?_
    · intro source
      simpa using
        (show literalRowAccEncodedType.inputSize literalRowInitAcc ≤ (100 : Nat) by
          native_decide)
    · intro source acc instr hinstr
      exact literalRowStep_growth source acc instr hinstr
  have hRow :
      TMPolyTimeMap literalRowAccEncodedType intRowStructuredEncodedType
        (fun acc : LiteralRowAcc => acc.2) := by
    simpa [literalRowAccEncodedType, LiteralRowAcc] using
      TMPolyTimeMap.snd literalStructuredEncodedType intRowStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hRow hFold
  simpa [Function.comp, literalRowFromInstructions, literalRowInstructionsFold]
    using hComp

theorem literalRowRunner_tm_polytime :
    TMPolyTimeMap
      literalRowInputEncodedType
      intRowStructuredEncodedType
      literalRowRunner := by
  have hComp :=
    TMPolyTimeMap.comp literalRowFromInstructions_tm_polytime literalRowInstructions_tm_polytime
  simpa [Function.comp, literalRowRunner] using hComp

end ZeroOneIP
end Karp21
end ComplexityReduction
