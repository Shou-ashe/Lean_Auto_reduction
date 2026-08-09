import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Coeff
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

def prefixRowInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod clausePrefixStateEncodedType EncodedType.nat

def prefixRowInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool prefixRowInstructionPayloadEncodedType

def prefixRowInstructionListEncodedType : EncodedType :=
  EncodedType.list prefixRowInstructionEncodedType

def prefixRowInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clausePrefixStateEncodedType

def prefixRowAccEncodedType : EncodedType :=
  EncodedType.prod clausePrefixStateEncodedType intRowStructuredEncodedType

def prefixRowStepInputEncodedType : EncodedType :=
  EncodedType.prod prefixRowAccEncodedType prefixRowInstructionEncodedType

abbrev PrefixRowInstruction := Bool × (ClausePrefixState × Nat)
abbrev PrefixRowInput := Nat × ClausePrefixState
abbrev PrefixRowAcc := ClausePrefixState × List Int
abbrev PrefixRowStepInput := PrefixRowAcc × PrefixRowInstruction

def prefixRowInitAcc : PrefixRowAcc :=
  (clausePrefixInit, [])

def prefixRowInitInstruction (q : ClausePrefixState) : PrefixRowInstruction :=
  (false, (q, 0))

def prefixRowIndexInstruction (i : Nat) : PrefixRowInstruction :=
  (true, (clausePrefixInit, i))

def prefixRowInstructions (p : PrefixRowInput) : List PrefixRowInstruction :=
  prefixRowInitInstruction p.2 :: (List.range p.1).map prefixRowIndexInstruction

def prefixRowStep (p : PrefixRowStepInput) : PrefixRowAcc :=
  if p.2.1 then
    (p.1.1, p.1.2 ++ [prefixCoeffAtComputed (p.1.1, p.2.2.2)])
  else
    (p.2.2.1, [])

def prefixRowInstructionsFold (xs : List PrefixRowInstruction) : PrefixRowAcc :=
  xs.foldl (fun acc instr => prefixRowStep (acc, instr)) prefixRowInitAcc

def prefixRowFromInstructions (xs : List PrefixRowInstruction) : List Int :=
  (prefixRowInstructionsFold xs).2

def prefixRowRunner (p : PrefixRowInput) : List Int :=
  prefixRowFromInstructions (prefixRowInstructions p)

theorem prefixRowFrom_succ_append (start n : Nat) (q : ClausePrefixState) :
    prefixRowFrom start (n + 1) q =
      prefixRowFrom start n q ++ [prefixCoeffAt q (start + n)] := by
  induction n generalizing start with
  | zero =>
      simp [prefixRowFrom]
  | succ n ih =>
      change
        prefixCoeffAt q start :: prefixRowFrom (start + 1) (n + 1) q =
          prefixCoeffAt q start ::
            (prefixRowFrom (start + 1) n q ++ [prefixCoeffAt q (start + (n + 1))])
      rw [ih (start + 1)]
      have hIndex : (start + 1) + n = start + (n + 1) := by
        omega
      simp [hIndex]

theorem prefixRow_succ_append (n : Nat) (q : ClausePrefixState) :
    prefixRow (n + 1) q = prefixRow n q ++ [prefixCoeffAt q n] := by
  simpa [prefixRow] using prefixRowFrom_succ_append 0 n q

theorem prefixRowIndexInstructions_fold_eq
    (n : Nat) (q : ClausePrefixState) (row : List Int) :
    ((List.range n).map prefixRowIndexInstruction).foldl
        (fun acc instr => prefixRowStep (acc, instr)) (q, row) =
      (q, row ++ prefixRow n q) := by
  induction n generalizing row with
  | zero =>
      simp [prefixRow, prefixRowFrom]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.foldl_append]
      rw [ih row]
      simp [prefixRowIndexInstruction, prefixRowStep, prefixRow_succ_append,
        prefixCoeffAtComputed_eq_prefixCoeffAt, List.append_assoc]

theorem prefixRowInstructionsFold_eq (p : PrefixRowInput) :
    prefixRowInstructionsFold (prefixRowInstructions p) =
      (p.2, prefixRow p.1 p.2) := by
  rcases p with ⟨n, q⟩
  simpa [prefixRowInstructionsFold, prefixRowInstructions, prefixRowInitInstruction,
    prefixRowStep] using prefixRowIndexInstructions_fold_eq n q ([] : List Int)

theorem prefixRowRunner_eq_prefixRow (p : PrefixRowInput) :
    prefixRowRunner p = prefixRow p.1 p.2 := by
  have h := congrArg Prod.snd (prefixRowInstructionsFold_eq p)
  simpa [prefixRowRunner, prefixRowFromInstructions] using h

theorem prefixCoeffAt_bound (q : ClausePrefixState) (i : Nat) :
    -((3 : Nat) : Int) ≤ prefixCoeffAt q i ∧
      prefixCoeffAt q i ≤ ((3 : Nat) : Int) := by
  rcases q with ⟨count, l0, l1, l2⟩
  have h0 := literalCoeffAt_bound l0 i
  have h1 := literalCoeffAt_bound l1 i
  have h2 := literalCoeffAt_bound l2 i
  cases count with
  | zero =>
      simp [prefixCoeffAt]
  | succ count =>
      cases count with
      | zero =>
          simp [prefixCoeffAt]
          omega
      | succ count =>
          cases count with
          | zero =>
              simp [prefixCoeffAt]
              omega
          | succ count =>
              simp [prefixCoeffAt]
              omega

theorem prefixCoeffAtComputed_bound (q : ClausePrefixState) (i : Nat) :
    -((3 : Nat) : Int) ≤ prefixCoeffAtComputed (q, i) ∧
      prefixCoeffAtComputed (q, i) ≤ ((3 : Nat) : Int) := by
  simpa [prefixCoeffAtComputed_eq_prefixCoeffAt] using prefixCoeffAt_bound q i

theorem prefixRowInitInstruction_tm_polytime :
    TMPolyTimeMap
      clausePrefixStateEncodedType
      prefixRowInstructionEncodedType
      prefixRowInitInstruction := by
  have hFalse :
      TMPolyTimeMap clausePrefixStateEncodedType EncodedType.bool
        (fun _ : ClausePrefixState => false) :=
    TMPolyTimeMap.const clausePrefixStateEncodedType EncodedType.bool false
  have hState :
      TMPolyTimeMap clausePrefixStateEncodedType clausePrefixStateEncodedType
        (fun q : ClausePrefixState => q) :=
    TMPolyTimeMap.id clausePrefixStateEncodedType
  have hZero :
      TMPolyTimeMap clausePrefixStateEncodedType EncodedType.nat
        (fun _ : ClausePrefixState => (0 : Nat)) :=
    TMPolyTimeMap.const clausePrefixStateEncodedType EncodedType.nat (0 : Nat)
  have hPayload :
      TMPolyTimeMap clausePrefixStateEncodedType prefixRowInstructionPayloadEncodedType
        (fun q : ClausePrefixState => (q, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hState hZero
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [prefixRowInitInstruction, prefixRowInstructionEncodedType,
    prefixRowInstructionPayloadEncodedType] using hOut

theorem prefixRowIndexInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      prefixRowInstructionEncodedType
      prefixRowIndexInstruction := by
  have hTrue :
      TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool true
  have hState :
      TMPolyTimeMap EncodedType.nat clausePrefixStateEncodedType
        (fun _ : Nat => clausePrefixInit) :=
    TMPolyTimeMap.const EncodedType.nat clausePrefixStateEncodedType clausePrefixInit
  have hIndex : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun i : Nat => i) :=
    TMPolyTimeMap.id EncodedType.nat
  have hPayload :
      TMPolyTimeMap EncodedType.nat prefixRowInstructionPayloadEncodedType
        (fun i : Nat => (clausePrefixInit, i)) :=
    TMPolyTimeMap.prod_mk hState hIndex
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [prefixRowIndexInstruction, prefixRowInstructionEncodedType,
    prefixRowInstructionPayloadEncodedType] using hOut

theorem prefixRowInstructions_tm_polytime :
    TMPolyTimeMap
      prefixRowInputEncodedType
      prefixRowInstructionListEncodedType
      prefixRowInstructions := by
  let X := prefixRowInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : PrefixRowInput => p.1) := by
    simpa [X, prefixRowInputEncodedType, PrefixRowInput] using
      TMPolyTimeMap.fst EncodedType.nat clausePrefixStateEncodedType
  have hState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : PrefixRowInput => p.2) := by
    simpa [X, prefixRowInputEncodedType, PrefixRowInput] using
      TMPolyTimeMap.snd EncodedType.nat clausePrefixStateEncodedType
  have hInit :
      TMPolyTimeMap X prefixRowInstructionEncodedType
        (fun p : PrefixRowInput => prefixRowInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp prefixRowInitInstruction_tm_polytime hState
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : PrefixRowInput => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hIndexInstrs :
      TMPolyTimeMap X prefixRowInstructionListEncodedType
        (fun p : PrefixRowInput => (List.range p.1).map prefixRowIndexInstruction) := by
    have hMap := TMPolyTimeMap.list_map prefixRowIndexInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, prefixRowInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod prefixRowInstructionEncodedType prefixRowInstructionListEncodedType)
        (fun p : PrefixRowInput =>
          (prefixRowInitInstruction p.2,
            (List.range p.1).map prefixRowIndexInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hIndexInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons prefixRowInstructionEncodedType) hConsInput
  simpa [Function.comp, prefixRowInstructions, prefixRowInstructionListEncodedType, X]
    using hOut

theorem prefixRowAcc_mk_tm_polytime
    {X : EncodedType} {state : X.Carrier → ClausePrefixState} {row : X.Carrier → List Int}
    (hState : TMPolyTimeMap X clausePrefixStateEncodedType state)
    (hRow : TMPolyTimeMap X intRowStructuredEncodedType row) :
    TMPolyTimeMap X prefixRowAccEncodedType (fun x => (state x, row x)) := by
  simpa [prefixRowAccEncodedType] using TMPolyTimeMap.prod_mk hState hRow

theorem prefixRowStep_tm_polytime :
    TMPolyTimeMap
      prefixRowStepInputEncodedType
      prefixRowAccEncodedType
      prefixRowStep := by
  let X := prefixRowStepInputEncodedType
  have hAcc : TMPolyTimeMap X prefixRowAccEncodedType
      (fun p : PrefixRowStepInput => p.1) := by
    simpa [X, prefixRowStepInputEncodedType, PrefixRowStepInput] using
      TMPolyTimeMap.fst prefixRowAccEncodedType prefixRowInstructionEncodedType
  have hInstr : TMPolyTimeMap X prefixRowInstructionEncodedType
      (fun p : PrefixRowStepInput => p.2) := by
    simpa [X, prefixRowStepInputEncodedType, PrefixRowStepInput] using
      TMPolyTimeMap.snd prefixRowAccEncodedType prefixRowInstructionEncodedType
  have hAccState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : PrefixRowStepInput => p.1.1) := by
    have hFst := TMPolyTimeMap.fst clausePrefixStateEncodedType intRowStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, prefixRowAccEncodedType, X, PrefixRowStepInput] using hComp
  have hAccRow : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : PrefixRowStepInput => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd clausePrefixStateEncodedType intRowStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, prefixRowAccEncodedType, X, PrefixRowStepInput] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : PrefixRowStepInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool prefixRowInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, prefixRowInstructionEncodedType, X, PrefixRowStepInput] using hComp
  have hPayload : TMPolyTimeMap X prefixRowInstructionPayloadEncodedType
      (fun p : PrefixRowStepInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool prefixRowInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, prefixRowInstructionEncodedType, X, PrefixRowStepInput] using hComp
  have hInstrState : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : PrefixRowStepInput => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst clausePrefixStateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, prefixRowInstructionPayloadEncodedType, X, PrefixRowStepInput]
      using hComp
  have hIndex : TMPolyTimeMap X EncodedType.nat
      (fun p : PrefixRowStepInput => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd clausePrefixStateEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, prefixRowInstructionPayloadEncodedType, X, PrefixRowStepInput]
      using hComp
  have hEmpty : TMPolyTimeMap X intRowStructuredEncodedType
      (fun _ : PrefixRowStepInput => ([] : List Int)) :=
    TMPolyTimeMap.const X intRowStructuredEncodedType []
  have hFalseBranch :
      TMPolyTimeMap X prefixRowAccEncodedType
        (fun p : PrefixRowStepInput => (p.2.2.1, ([] : List Int))) :=
    prefixRowAcc_mk_tm_polytime hInstrState hEmpty
  have hCoeffInput :
      TMPolyTimeMap X prefixCoeffInputEncodedType
        (fun p : PrefixRowStepInput => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccState hIndex
  have hCoeff : TMPolyTimeMap X EncodedType.int
      (fun p : PrefixRowStepInput => prefixCoeffAtComputed (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp prefixCoeffAtComputed_tm_polytime hCoeffInput
    simpa [Function.comp, prefixCoeffInputEncodedType, X, PrefixRowStepInput] using hComp
  have hSingleton :
      TMPolyTimeMap X intRowStructuredEncodedType
        (fun p : PrefixRowStepInput => [prefixCoeffAtComputed (p.1.1, p.2.2.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.int) hCoeff
    simpa [Function.comp, intRowStructuredEncodedType, X, PrefixRowStepInput] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod intRowStructuredEncodedType intRowStructuredEncodedType)
        (fun p : PrefixRowStepInput =>
          (p.1.2, [prefixCoeffAtComputed (p.1.1, p.2.2.2)])) :=
    TMPolyTimeMap.prod_mk hAccRow hSingleton
  have hAppend : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : PrefixRowStepInput =>
        p.1.2 ++ [prefixCoeffAtComputed (p.1.1, p.2.2.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.int) hAppendInput
    simpa [Function.comp, intRowStructuredEncodedType, X, PrefixRowStepInput] using hComp
  have hTrueBranch :
      TMPolyTimeMap X prefixRowAccEncodedType
        (fun p : PrefixRowStepInput =>
          (p.1.1, p.1.2 ++ [prefixCoeffAtComputed (p.1.1, p.2.2.2)])) :=
    prefixRowAcc_mk_tm_polytime hAccState hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : PrefixRowStepInput => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) prefixRowAccEncodedType
        (fun p : Bool × PrefixRowStepInput =>
          match p.1 with
          | true => (p.2.1.1, p.2.1.2 ++ [prefixCoeffAtComputed (p.2.1.1, p.2.2.2.2)])
          | false => (p.2.2.2.1, ([] : List Int))) :=
    Clique.boolProduct_dispatch_tm_polytime X prefixRowAccEncodedType
      (fFalse := fun p : PrefixRowStepInput => (p.2.2.1, ([] : List Int)))
      (fTrue := fun p : PrefixRowStepInput =>
        (p.1.1, p.1.2 ++ [prefixCoeffAtComputed (p.1.1, p.2.2.2)]))
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨state, row⟩, ⟨tag, instrState, i⟩⟩
  cases tag <;> simp [prefixRowStep, Function.comp] <;> rfl

theorem prefixRowStep_growth
    (source : List PrefixRowInstruction) (acc : PrefixRowAcc)
    (instr : PrefixRowInstruction)
    (hinstr : prefixRowInstructionEncodedType.inputSize instr ≤
      prefixRowInstructionListEncodedType.inputSize source) :
    prefixRowAccEncodedType.inputSize (prefixRowStep (acc, instr)) ≤
      prefixRowAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 30).eval
          (prefixRowInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨state, row⟩
  rcases instr with ⟨tag, instrState, i⟩
  cases tag
  · have hEmptyRaw :
        (EncodedType.list EncodedType.int).inputSize ([] : List Int) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.int
    simp [prefixRowStep, prefixRowAccEncodedType, intRowStructuredEncodedType,
      prefixRowInstructionEncodedType, prefixRowInstructionPayloadEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat,
      hEmptyRaw, Polynomial.eval_add, Polynomial.eval_mul] at hinstr ⊢
    omega
  · have hCoeff := prefixCoeffAtComputed_bound state i
    have hCoeffSize :
        EncodedType.int.inputSize (prefixCoeffAtComputed (state, i)) ≤ 5 :=
      intStructured_inputSize_le_five_of_between_three hCoeff.1 hCoeff.2
    have hAppend :
        (EncodedType.list EncodedType.int).inputSize
            (row ++ [prefixCoeffAtComputed (state, i)]) =
          (EncodedType.list EncodedType.int).inputSize row +
            (EncodedType.list EncodedType.int).inputSize
              [prefixCoeffAtComputed (state, i)] := by
      simpa using
        list_inputSize_append EncodedType.int row [prefixCoeffAtComputed (state, i)]
    have hSingleton :
        (EncodedType.list EncodedType.int).inputSize [prefixCoeffAtComputed (state, i)] ≤ 6 := by
      simp at hCoeffSize ⊢
      omega
    simp [prefixRowStep, prefixRowAccEncodedType, intRowStructuredEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul]
    rw [hAppend]
    omega

theorem prefixRowFromInstructions_tm_polytime :
    TMPolyTimeMap
      prefixRowInstructionListEncodedType
      intRowStructuredEncodedType
      prefixRowFromInstructions := by
  rcases prefixRowStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        prefixRowInstructionListEncodedType
        prefixRowAccEncodedType
        prefixRowInstructionsFold := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        prefixRowInstructionEncodedType prefixRowAccEncodedType
        prefixRowStep prefixRowInitAcc hStep
        (Polynomial.C 100) (Polynomial.C 10 * Polynomial.X + Polynomial.C 30) ?_ ?_
    · intro source
      simpa using
        (show prefixRowAccEncodedType.inputSize prefixRowInitAcc ≤ (100 : Nat) by
          native_decide)
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

theorem prefixRowRunner_tm_polytime :
    TMPolyTimeMap
      prefixRowInputEncodedType
      intRowStructuredEncodedType
      prefixRowRunner := by
  have hComp :=
    TMPolyTimeMap.comp prefixRowFromInstructions_tm_polytime prefixRowInstructions_tm_polytime
  simpa [Function.comp, prefixRowRunner] using hComp

end ZeroOneIP
end Karp21
end ComplexityReduction
