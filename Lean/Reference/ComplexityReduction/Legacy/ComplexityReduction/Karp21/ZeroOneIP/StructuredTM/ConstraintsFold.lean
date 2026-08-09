import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.ClauseConstraint

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-!
Checked clause-list runner for the structured 3SAT-to-0-1-IP route.

The first instruction records the source variable bound `n`; each later
instruction carries one source clause.  The fold accumulator stores `n` and the
emitted constraint list.
-/

def constraintsFromInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clauseStructuredEncodedType

def constraintsFromInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool constraintsFromInstructionPayloadEncodedType

def constraintsFromInstructionListEncodedType : EncodedType :=
  EncodedType.list constraintsFromInstructionEncodedType

def constraintsFromInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat cnfStructuredEncodedType

def constraintsFromAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat constraintListStructuredEncodedType

def constraintsFromStepInputEncodedType : EncodedType :=
  EncodedType.prod constraintsFromAccEncodedType constraintsFromInstructionEncodedType

abbrev ConstraintsFromInstruction := Bool × (Nat × SAT.Clause)
abbrev ConstraintsFromInput := Nat × SAT.CNF
abbrev ConstraintsFromAcc := Nat × List (List Int × Int)
abbrev ConstraintsFromStepInput := ConstraintsFromAcc × ConstraintsFromInstruction

def constraintsFromInitAcc : ConstraintsFromAcc :=
  ((0 : Nat), ([] : List (List Int × Int)))

def constraintsFromInitInstruction (n : Nat) : ConstraintsFromInstruction :=
  (false, (n, ([] : SAT.Clause)))

def constraintsFromClauseInstruction (c : SAT.Clause) : ConstraintsFromInstruction :=
  (true, ((0 : Nat), c))

def constraintsFromInstructions (p : ConstraintsFromInput) :
    List ConstraintsFromInstruction :=
  constraintsFromInitInstruction p.1 :: p.2.map constraintsFromClauseInstruction

def constraintsFromStep
    (p : ConstraintsFromAcc × ConstraintsFromInstruction) :
    ConstraintsFromAcc :=
  if p.2.1 then
    let n := p.1.1
    let out := p.1.2
    let c := p.2.2.2
    (n, out ++ [clauseConstraintFromInput (n, c)])
  else
    (p.2.2.1, ([] : List (List Int × Int)))

def constraintsFromInstructionsFold
    (xs : List ConstraintsFromInstruction) : ConstraintsFromAcc :=
  xs.foldl (fun acc instr => constraintsFromStep (acc, instr)) constraintsFromInitAcc

def constraintsFromFromInstructions
    (xs : List ConstraintsFromInstruction) : List (List Int × Int) :=
  (constraintsFromInstructionsFold xs).2

def constraintsFromComputedInput (p : ConstraintsFromInput) : List (List Int × Int) :=
  p.2.map fun c => clauseConstraintFromInput (p.1, c)

def constraintsFromRunner (p : ConstraintsFromInput) : List (List Int × Int) :=
  constraintsFromFromInstructions (constraintsFromInstructions p)

def constraintsFromTextbookInput (p : ConstraintsFromInput) : List (List Int × Int) :=
  p.2.map (clauseConstraint p.1)

theorem constraintsFromClauseInstructions_fold
    (n : Nat) (out : List (List Int × Int)) (cs : SAT.CNF) :
    ((cs.map constraintsFromClauseInstruction).foldl
        (fun acc instr => constraintsFromStep (acc, instr)) (n, out)) =
      (n, out ++ constraintsFromComputedInput (n, cs)) := by
  induction cs generalizing out with
  | nil =>
      simp [constraintsFromComputedInput]
  | cons c rest ih =>
      change
        ((rest.map constraintsFromClauseInstruction).foldl
            (fun acc instr => constraintsFromStep (acc, instr))
            (n, out ++ [clauseConstraintFromInput (n, c)])) =
          (n, out ++ constraintsFromComputedInput (n, c :: rest))
      rw [ih (out ++ [clauseConstraintFromInput (n, c)])]
      simp [constraintsFromComputedInput, List.append_assoc]

theorem constraintsFromRunner_eq_computed (p : ConstraintsFromInput) :
    constraintsFromRunner p = constraintsFromComputedInput p := by
  rcases p with ⟨n, cs⟩
  change
    ((constraintsFromInitInstruction n :: cs.map constraintsFromClauseInstruction).foldl
      (fun acc instr => constraintsFromStep (acc, instr)) constraintsFromInitAcc).2 =
      constraintsFromComputedInput (n, cs)
  rw [List.foldl_cons]
  simp [constraintsFromInitInstruction, constraintsFromStep]
  have h := constraintsFromClauseInstructions_fold n ([] : List (List Int × Int)) cs
  simpa using congrArg Prod.snd h

theorem constraintsFromComputedInput_eq_textbook
    (p : ConstraintsFromInput) (hthree : ∀ c ∈ p.2, c.length ≤ 3) :
    constraintsFromComputedInput p = constraintsFromTextbookInput p := by
  rcases p with ⟨n, cs⟩
  induction cs with
  | nil =>
      simp [constraintsFromComputedInput, constraintsFromTextbookInput]
  | cons c rest ih =>
      have hc : c.length ≤ 3 := hthree c (by simp)
      have hrest : ∀ d ∈ rest, d.length ≤ 3 := by
        intro d hd
        exact hthree d (by simp [hd])
      change
        clauseConstraintFromInput (n, c) :: constraintsFromComputedInput (n, rest) =
          clauseConstraint n c :: constraintsFromTextbookInput (n, rest)
      rw [clauseConstraintFromInput_eq_clauseConstraint (n, c) hc, ih hrest]

theorem constraintsFromInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      constraintsFromInstructionEncodedType
      constraintsFromInitInstruction := by
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hN : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hEmpty :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun _ : Nat => ([] : SAT.Clause)) :=
    TMPolyTimeMap.const EncodedType.nat clauseStructuredEncodedType []
  have hPayload :
      TMPolyTimeMap EncodedType.nat constraintsFromInstructionPayloadEncodedType
        (fun n : Nat => (n, ([] : SAT.Clause))) :=
    TMPolyTimeMap.prod_mk hN hEmpty
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [constraintsFromInitInstruction, constraintsFromInstructionEncodedType,
    constraintsFromInstructionPayloadEncodedType] using hOut

theorem constraintsFromClauseInstruction_tm_polytime :
    TMPolyTimeMap
      clauseStructuredEncodedType
      constraintsFromInstructionEncodedType
      constraintsFromClauseInstruction := by
  have hTrue : TMPolyTimeMap clauseStructuredEncodedType EncodedType.bool
      (fun _ : SAT.Clause => true) :=
    TMPolyTimeMap.const clauseStructuredEncodedType EncodedType.bool true
  have hZero : TMPolyTimeMap clauseStructuredEncodedType EncodedType.nat
      (fun _ : SAT.Clause => (0 : Nat)) :=
    TMPolyTimeMap.const clauseStructuredEncodedType EncodedType.nat (0 : Nat)
  have hClause : TMPolyTimeMap clauseStructuredEncodedType clauseStructuredEncodedType id :=
    TMPolyTimeMap.id clauseStructuredEncodedType
  have hPayload :
      TMPolyTimeMap clauseStructuredEncodedType constraintsFromInstructionPayloadEncodedType
        (fun c : SAT.Clause => ((0 : Nat), c)) :=
    TMPolyTimeMap.prod_mk hZero hClause
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [constraintsFromClauseInstruction, constraintsFromInstructionEncodedType,
    constraintsFromInstructionPayloadEncodedType] using hOut

theorem constraintsFromInstructions_tm_polytime :
    TMPolyTimeMap
      constraintsFromInputEncodedType
      constraintsFromInstructionListEncodedType
      constraintsFromInstructions := by
  let X := constraintsFromInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ConstraintsFromInput => p.1) := by
    simpa [X, constraintsFromInputEncodedType, ConstraintsFromInput] using
      TMPolyTimeMap.fst EncodedType.nat cnfStructuredEncodedType
  have hClauses :
      TMPolyTimeMap X cnfStructuredEncodedType (fun p : ConstraintsFromInput => p.2) := by
    simpa [X, constraintsFromInputEncodedType, ConstraintsFromInput] using
      TMPolyTimeMap.snd EncodedType.nat cnfStructuredEncodedType
  have hInit :
      TMPolyTimeMap X constraintsFromInstructionEncodedType
        (fun p : ConstraintsFromInput => constraintsFromInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp constraintsFromInitInstruction_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hClauseInstrs :
      TMPolyTimeMap X constraintsFromInstructionListEncodedType
        (fun p : ConstraintsFromInput => p.2.map constraintsFromClauseInstruction) := by
    have hMap := TMPolyTimeMap.list_map constraintsFromClauseInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hClauses
    simpa [Function.comp, constraintsFromInstructionListEncodedType, cnfStructuredEncodedType,
      X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod constraintsFromInstructionEncodedType
          constraintsFromInstructionListEncodedType)
        (fun p : ConstraintsFromInput =>
          (constraintsFromInitInstruction p.1,
            p.2.map constraintsFromClauseInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hClauseInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons constraintsFromInstructionEncodedType)
      hConsInput
  simpa [Function.comp, constraintsFromInstructions,
    constraintsFromInstructionListEncodedType, X] using hOut

theorem constraintsFromAcc_mk_tm_polytime
    {X : EncodedType} {n : X.Carrier → Nat}
    {out : X.Carrier → List (List Int × Int)}
    (hN : TMPolyTimeMap X EncodedType.nat n)
    (hOut : TMPolyTimeMap X constraintListStructuredEncodedType out) :
    TMPolyTimeMap X constraintsFromAccEncodedType
      (fun x => (n x, out x)) := by
  simpa [constraintsFromAccEncodedType] using TMPolyTimeMap.prod_mk hN hOut

theorem constraintsFromStep_tm_polytime :
    TMPolyTimeMap
      constraintsFromStepInputEncodedType
      constraintsFromAccEncodedType
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
    have hComp := TMPolyTimeMap.comp clauseConstraintFromInput_tm_polytime hConstraintInput
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

/-! ### Reachable fold bounds and full constraint-list runner -/

noncomputable def constraintsFromPerClauseBoundPolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X + Polynomial.C 100

@[simp] theorem constraintsFromPerClauseBoundPolynomial_eval (N : Nat) :
    constraintsFromPerClauseBoundPolynomial.eval N = 100 * N + 100 := by
  simp [constraintsFromPerClauseBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def constraintsFromFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 200 * (Polynomial.X * Polynomial.X) + Polynomial.C 200

@[simp] theorem constraintsFromFoldAccBoundPolynomial_eval (N : Nat) :
    constraintsFromFoldAccBoundPolynomial.eval N = 200 * (N * N) + 200 := by
  simp [constraintsFromFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def constraintsFromAccBound
    (N processed : Nat) (acc : ConstraintsFromAcc) : Prop :=
  acc.1 ≤ N ∧
    constraintListStructuredEncodedType.inputSize acc.2 ≤
      processed * constraintsFromPerClauseBoundPolynomial.eval N

theorem constraintsFromInstruction_nat_inputSize_le
    {N : Nat} {instr : ConstraintsFromInstruction}
    (hInstr : constraintsFromInstructionEncodedType.inputSize instr ≤ N) :
    instr.2.1 ≤ N := by
  rcases instr with ⟨tag, n, c⟩
  change n ≤ N
  simp [constraintsFromInstructionEncodedType, constraintsFromInstructionPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat]
    at hInstr
  omega

theorem constraintsFromInitInstruction_inputSize_le (n : Nat) :
    constraintsFromInstructionEncodedType.inputSize (constraintsFromInitInstruction n) ≤
      n + 4 := by
  have hEmpty : clauseStructuredEncodedType.inputSize ([] : SAT.Clause) = 0 := by
    change (EncodedType.list literalStructuredEncodedType).inputSize
      ([] : List SAT.Literal) = 0
    exact EncodedType.inputSize_list_nil literalStructuredEncodedType
  simp [constraintsFromInitInstruction, constraintsFromInstructionEncodedType,
    constraintsFromInstructionPayloadEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, EncodedType.inputSize_nat, hEmpty]
  omega

theorem constraintsFromClauseInstruction_inputSize_le (c : SAT.Clause) :
    constraintsFromInstructionEncodedType.inputSize (constraintsFromClauseInstruction c) ≤
      clauseStructuredEncodedType.inputSize c + 4 := by
  simp [constraintsFromClauseInstruction, constraintsFromInstructionEncodedType,
    constraintsFromInstructionPayloadEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, EncodedType.inputSize_nat]
  omega

theorem constraintsFromClauseInstructions_inputSize_le (cs : SAT.CNF) :
    constraintsFromInstructionListEncodedType.inputSize
        (cs.map constraintsFromClauseInstruction) ≤
      cnfStructuredEncodedType.inputSize cs + 4 * cs.length := by
  induction cs with
  | nil =>
      simp [constraintsFromInstructionListEncodedType, cnfStructuredEncodedType]
  | cons c cs ih =>
      have hc := constraintsFromClauseInstruction_inputSize_le c
      simp only [List.map_cons]
      change
        (EncodedType.list constraintsFromInstructionEncodedType).inputSize
            (constraintsFromClauseInstruction c :: cs.map constraintsFromClauseInstruction) ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs) +
            4 * (c :: cs).length
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have ih' :
          (EncodedType.list constraintsFromInstructionEncodedType).inputSize
              (cs.map constraintsFromClauseInstruction) ≤
            (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * cs.length := by
        simpa [constraintsFromInstructionListEncodedType, cnfStructuredEncodedType] using ih
      change
        constraintsFromInstructionEncodedType.inputSize
            (constraintsFromClauseInstruction c) + 1 +
              (EncodedType.list constraintsFromInstructionEncodedType).inputSize
                (cs.map constraintsFromClauseInstruction) ≤
          clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * (cs.length + 1)
      omega

theorem constraintsFromInstructions_inputSize_le (p : ConstraintsFromInput) :
    constraintsFromInstructionListEncodedType.inputSize (constraintsFromInstructions p) ≤
      6 * constraintsFromInputEncodedType.inputSize p + 10 := by
  rcases p with ⟨n, cs⟩
  have hInit := constraintsFromInitInstruction_inputSize_le n
  have hMap := constraintsFromClauseInstructions_inputSize_le cs
  have hLen :=
    Clique.encodedList_length_le_inputSize clauseStructuredEncodedType cs
  have hLen' : cs.length ≤ cnfStructuredEncodedType.inputSize cs := by
    simpa [cnfStructuredEncodedType] using hLen
  simp only [constraintsFromInstructions]
  change
    (EncodedType.list constraintsFromInstructionEncodedType).inputSize
        (constraintsFromInitInstruction n :: cs.map constraintsFromClauseInstruction) ≤
      6 * constraintsFromInputEncodedType.inputSize (n, cs) + 10
  rw [EncodedType.inputSize_list_cons]
  have hMap' :
      (EncodedType.list constraintsFromInstructionEncodedType).inputSize
          (cs.map constraintsFromClauseInstruction) ≤
        (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * cs.length := by
    simpa [constraintsFromInstructionListEncodedType, cnfStructuredEncodedType] using hMap
  change
    constraintsFromInstructionEncodedType.inputSize (constraintsFromInitInstruction n) + 1 +
        (EncodedType.list constraintsFromInstructionEncodedType).inputSize
          (cs.map constraintsFromClauseInstruction) ≤
      6 * constraintsFromInputEncodedType.inputSize (n, cs) + 10
  have hLenBound :
      cs.length ≤ (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
    simpa [cnfStructuredEncodedType] using hLen'
  calc
    constraintsFromInstructionEncodedType.inputSize (constraintsFromInitInstruction n) + 1 +
        (EncodedType.list constraintsFromInstructionEncodedType).inputSize
          (cs.map constraintsFromClauseInstruction)
        ≤ (n + 4) + 1 +
            ((EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * cs.length) := by
          omega
    _ ≤ (n + 4) + 1 +
          ((EncodedType.list clauseStructuredEncodedType).inputSize cs +
            4 * (EncodedType.list clauseStructuredEncodedType).inputSize cs) := by
          nlinarith
    _ ≤ 6 * constraintsFromInputEncodedType.inputSize (n, cs) + 10 := by
          simp [constraintsFromInputEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, cnfStructuredEncodedType]
          nlinarith

theorem clauseConstraintFromInput_singleton_size_le_of_bound
    {N n : Nat} {c : SAT.Clause} (hn : n ≤ N) :
    constraintListStructuredEncodedType.inputSize [clauseConstraintFromInput (n, c)] ≤
      constraintsFromPerClauseBoundPolynomial.eval N := by
  have hConstraint := clauseConstraintFromInput_inputSize_le (n, c)
  change
    (EncodedType.list constraintStructuredEncodedType).inputSize
        [clauseConstraintFromInput (n, c)] ≤
      constraintsFromPerClauseBoundPolynomial.eval N
  rw [EncodedType.inputSize_list_cons]
  simp [constraintsFromPerClauseBoundPolynomial_eval]
  omega

theorem constraintsFromStep_bound {N processed : Nat}
    {acc : ConstraintsFromAcc} {instr : ConstraintsFromInstruction}
    (hAcc : constraintsFromAccBound N processed acc)
    (_hProcessed : processed + 1 ≤ N)
    (hInstr : constraintsFromInstructionEncodedType.inputSize instr ≤ N) :
    constraintsFromAccBound N (processed + 1) (constraintsFromStep (acc, instr)) := by
  rcases acc with ⟨n, out⟩
  rcases instr with ⟨tag, initN, c⟩
  rcases hAcc with ⟨hn, hout⟩
  change n ≤ N at hn
  change constraintListStructuredEncodedType.inputSize out ≤
    processed * constraintsFromPerClauseBoundPolynomial.eval N at hout
  cases tag
  · have hInitN : initN ≤ N :=
      constraintsFromInstruction_nat_inputSize_le
        (N := N) (instr := (false, (initN, c))) hInstr
    simp [constraintsFromStep, constraintsFromAccBound]
    rw [show constraintListStructuredEncodedType.inputSize
        ([] : List (List Int × Int)) = 0 by
      exact EncodedType.inputSize_list_nil constraintStructuredEncodedType]
    exact ⟨hInitN, Nat.zero_le _⟩
  · have hNew :=
      clauseConstraintFromInput_singleton_size_le_of_bound (N := N) (n := n) (c := c) hn
    have hAppend :
        constraintListStructuredEncodedType.inputSize
            (out ++ [clauseConstraintFromInput (n, c)]) =
          constraintListStructuredEncodedType.inputSize out +
            constraintListStructuredEncodedType.inputSize
              [clauseConstraintFromInput (n, c)] := by
      simpa [constraintListStructuredEncodedType] using
        Clique.encodedList_inputSize_append constraintStructuredEncodedType out
          [clauseConstraintFromInput (n, c)]
    simp [constraintsFromStep, constraintsFromAccBound, hAppend]
    refine ⟨hn, ?_⟩
    calc
      constraintListStructuredEncodedType.inputSize out +
          constraintListStructuredEncodedType.inputSize [clauseConstraintFromInput (n, c)]
          ≤
        processed * constraintsFromPerClauseBoundPolynomial.eval N +
          constraintsFromPerClauseBoundPolynomial.eval N := by
          exact Nat.add_le_add hout hNew
      _ = (processed + 1) * constraintsFromPerClauseBoundPolynomial.eval N := by
          ring
      _ = (processed + 1) * (100 * N + 100) := by
          simp [constraintsFromPerClauseBoundPolynomial_eval]

theorem constraintsFromFold_bound_aux
    {N processed : Nat}
    (xs : List ConstraintsFromInstruction) (acc : ConstraintsFromAcc)
    (hAcc : constraintsFromAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, constraintsFromInstructionEncodedType.inputSize instr ≤ N) :
    constraintsFromAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => constraintsFromStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : constraintsFromInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := constraintsFromStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, constraintsFromInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1) (acc := constraintsFromStep (acc, x))
          hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem constraintsFromFold_bound_of_inputSize_le
    {N : Nat} (xs : List ConstraintsFromInstruction)
    (hSize : constraintsFromInstructionListEncodedType.inputSize xs ≤ N) :
    constraintsFromAccBound N xs.length
      (xs.foldl (fun acc instr => constraintsFromStep (acc, instr))
        constraintsFromInitAcc) := by
  have hInit : constraintsFromAccBound N 0 constraintsFromInitAcc := by
    have hEmpty :
        constraintListStructuredEncodedType.inputSize ([] : List (List Int × Int)) = 0 :=
      EncodedType.inputSize_list_nil constraintStructuredEncodedType
    simp [constraintsFromAccBound, constraintsFromInitAcc, hEmpty]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      Clique.encodedList_length_le_inputSize constraintsFromInstructionEncodedType xs
    have hLenInput' :
        xs.length ≤ constraintsFromInstructionListEncodedType.inputSize xs := by
      simpa [constraintsFromInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, constraintsFromInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      Clique.encodedList_element_inputSize_le
        (X := constraintsFromInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : constraintsFromInstructionEncodedType.inputSize instr ≤
        constraintsFromInstructionListEncodedType.inputSize xs := by
      simpa [constraintsFromInstructionListEncodedType] using hElem
    omega
  have h :=
    constraintsFromFold_bound_aux (N := N) (processed := 0) xs constraintsFromInitAcc
      hInit hLen hInstr
  simpa using h

theorem constraintsFromAccBound_inputSize_le {N processed : Nat}
    {acc : ConstraintsFromAcc}
    (hAcc : constraintsFromAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    constraintsFromAccEncodedType.inputSize acc ≤
      constraintsFromFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨n, out⟩
  rcases hAcc with ⟨hn, hout⟩
  let Bc := constraintsFromPerClauseBoundPolynomial.eval N
  have houtN :
      constraintListStructuredEncodedType.inputSize out ≤ N * Bc :=
    hout.trans (Nat.mul_le_mul_right Bc hProcessed)
  have hBc : Bc = 100 * N + 100 := by
    simp [Bc]
  simp [constraintsFromAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  simp [hBc] at houtN ⊢
  nlinarith

theorem constraintsFromAcc_constraints_inputSize_le (acc : ConstraintsFromAcc) :
    constraintListStructuredEncodedType.inputSize acc.2 ≤
      constraintsFromAccEncodedType.inputSize acc := by
  rcases acc with ⟨n, out⟩
  simp [constraintsFromAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]

theorem constraintsFromFromInstructions_inputSize_le
    (xs : List ConstraintsFromInstruction) :
    constraintListStructuredEncodedType.inputSize (constraintsFromFromInstructions xs) ≤
      constraintsFromFoldAccBoundPolynomial.eval
        (constraintsFromInstructionListEncodedType.inputSize xs) := by
  let N := constraintsFromInstructionListEncodedType.inputSize xs
  let acc := constraintsFromInstructionsFold xs
  have hFold :
      constraintsFromAccBound N xs.length acc := by
    simpa [N, acc, constraintsFromInstructionsFold] using
      constraintsFromFold_bound_of_inputSize_le (N := N) xs (Nat.le_refl N)
  have hLen : xs.length ≤ N := by
    have h :=
      Clique.encodedList_length_le_inputSize constraintsFromInstructionEncodedType xs
    simpa [N, constraintsFromInstructionListEncodedType] using h
  have hAccSize :
      constraintsFromAccEncodedType.inputSize acc ≤
        constraintsFromFoldAccBoundPolynomial.eval N :=
    constraintsFromAccBound_inputSize_le hFold hLen
  have hOut := constraintsFromAcc_constraints_inputSize_le acc
  simpa [constraintsFromFromInstructions, acc, N] using hOut.trans hAccSize

theorem constraintsFromComputedInput_structured_inputSize_le (p : ConstraintsFromInput) :
    constraintListStructuredEncodedType.inputSize (constraintsFromComputedInput p) ≤
      1000000 * constraintsFromInputEncodedType.inputSize p ^ 2 + 1000000 := by
  let N := constraintsFromInputEncodedType.inputSize p
  let xs := constraintsFromInstructions p
  let M := constraintsFromInstructionListEncodedType.inputSize xs
  have hRunner := constraintsFromFromInstructions_inputSize_le xs
  have hM : M ≤ 6 * N + 10 := by
    simpa [M, N, xs] using constraintsFromInstructions_inputSize_le p
  have hPow : M ^ 2 ≤ (6 * N + 10) ^ 2 :=
    Nat.pow_le_pow_left hM 2
  have hEval :
      constraintsFromFoldAccBoundPolynomial.eval M ≤
        1000000 * N ^ 2 + 1000000 := by
    have hRaw :
        200 * M ^ 2 + 200 ≤ 1000000 * N ^ 2 + 1000000 := by
      nlinarith [hPow]
    simpa [constraintsFromFoldAccBoundPolynomial_eval, pow_two, Nat.mul_assoc] using hRaw
  calc
    constraintListStructuredEncodedType.inputSize (constraintsFromComputedInput p)
        =
      constraintListStructuredEncodedType.inputSize (constraintsFromRunner p) := by
        rw [constraintsFromRunner_eq_computed]
    _ ≤ constraintsFromFoldAccBoundPolynomial.eval M := by
        simpa [constraintsFromRunner, xs, M] using hRunner
    _ ≤ 1000000 * N ^ 2 + 1000000 := hEval

noncomputable def constraintsFromFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod constraintsFromAccEncodedType
          constraintsFromInstructionEncodedType).encode
        constraintsFromAccEncodedType.encode
        constraintsFromStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm constraintsFromFoldAccBoundPolynomial
    (hStep.time.comp
      (constraintsFromFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem constraintsFromInstructionsFold_tm_polytime :
    TMPolyTimeMap
      constraintsFromInstructionListEncodedType
      constraintsFromAccEncodedType
      constraintsFromInstructionsFold := by
  rcases constraintsFromStep_tm_polytime with ⟨hStep⟩
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
            | nil =>
                simp
            | cons y ys ih =>
                simp
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

theorem constraintsFromFromInstructions_tm_polytime :
    TMPolyTimeMap
      constraintsFromInstructionListEncodedType
      constraintListStructuredEncodedType
      constraintsFromFromInstructions := by
  have hFold := constraintsFromInstructionsFold_tm_polytime
  have hOut :
      TMPolyTimeMap constraintsFromAccEncodedType constraintListStructuredEncodedType
        (fun acc : ConstraintsFromAcc => acc.2) := by
    simpa [constraintsFromAccEncodedType, ConstraintsFromAcc] using
      TMPolyTimeMap.snd EncodedType.nat constraintListStructuredEncodedType
  have hProj := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, constraintsFromFromInstructions, constraintsFromInstructionsFold]
    using hProj

theorem constraintsFromRunner_tm_polytime :
    TMPolyTimeMap
      constraintsFromInputEncodedType
      constraintListStructuredEncodedType
      constraintsFromRunner := by
  have hComp :=
    TMPolyTimeMap.comp constraintsFromFromInstructions_tm_polytime
      constraintsFromInstructions_tm_polytime
  simpa [Function.comp, constraintsFromRunner] using hComp

theorem constraintsFromComputedInput_tm_polytime :
    TMPolyTimeMap
      constraintsFromInputEncodedType
      constraintListStructuredEncodedType
      constraintsFromComputedInput := by
  convert constraintsFromRunner_tm_polytime using 1
  funext p
  exact (constraintsFromRunner_eq_computed p).symm

end ZeroOneIP
end Karp21
end ComplexityReduction
