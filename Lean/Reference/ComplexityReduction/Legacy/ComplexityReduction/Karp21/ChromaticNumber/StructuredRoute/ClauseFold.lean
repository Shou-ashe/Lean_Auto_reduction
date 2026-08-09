import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute.ClauseEdges

namespace ComplexityReduction
namespace Karp21
namespace ChromaticNumber

open ComplexityReduction.Combinatorics.Graph

/-!
Checked indexed clause-list runner for the P16c Chromatic Number route.

The first instruction records the source variable bound `n`; each later
instruction carries one source clause.  The fold accumulator stores the current
`n`, the next clause index, and the emitted edge list.
-/

def clauseEdgesFromInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clauseStructuredEncodedType

def clauseEdgesFromInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool clauseEdgesFromInstructionPayloadEncodedType

def clauseEdgesFromInstructionListEncodedType : EncodedType :=
  EncodedType.list clauseEdgesFromInstructionEncodedType

def clauseEdgesFromInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat cnfStructuredEncodedType

def clauseEdgesFromAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)

def clauseEdgesFromStepInputEncodedType : EncodedType :=
  EncodedType.prod clauseEdgesFromAccEncodedType clauseEdgesFromInstructionEncodedType

abbrev ClauseEdgesFromInstruction := Bool × (Nat × SAT.Clause)

abbrev ClauseEdgesFromInput := Nat × SAT.CNF

abbrev ClauseEdgesFromAcc := Nat × (Nat × List (Nat × Nat))

abbrev ClauseEdgesFromStepInput := ClauseEdgesFromAcc × ClauseEdgesFromInstruction

def clauseEdgesFromInitAcc : ClauseEdgesFromAcc :=
  ((0 : Nat), ((0 : Nat), ([] : List (Nat × Nat))))

def clauseEdgesFromInitInstruction (n : Nat) : ClauseEdgesFromInstruction :=
  (false, (n, ([] : SAT.Clause)))

def clauseEdgesFromClauseInstruction (c : SAT.Clause) : ClauseEdgesFromInstruction :=
  (true, ((0 : Nat), c))

def clauseEdgesFromInstructions (p : ClauseEdgesFromInput) :
    List ClauseEdgesFromInstruction :=
  clauseEdgesFromInitInstruction p.1 :: p.2.map clauseEdgesFromClauseInstruction

def clauseEdgesFromStep
    (p : ClauseEdgesFromAcc × ClauseEdgesFromInstruction) :
    ClauseEdgesFromAcc :=
  if p.2.1 then
    let n := p.1.1
    let j := p.1.2.1
    let out := p.1.2.2
    let c := p.2.2.2
    (n, (j + 1, out ++ clauseEdgesForFromInput (n, (j, c))))
  else
    (p.2.2.1, ((0 : Nat), ([] : List (Nat × Nat))))

def clauseEdgesFromInstructionsFold
    (xs : List ClauseEdgesFromInstruction) : ClauseEdgesFromAcc :=
  xs.foldl (fun acc instr => clauseEdgesFromStep (acc, instr)) clauseEdgesFromInitAcc

def clauseEdgesFromFromInstructions
    (xs : List ClauseEdgesFromInstruction) : List (Nat × Nat) :=
  (clauseEdgesFromInstructionsFold xs).2.2

def clauseEdgesFromFromInput (p : ClauseEdgesFromInput) : List (Nat × Nat) :=
  clauseEdgesFrom p.1 0 p.2

def clauseEdgesFromRunner (p : ClauseEdgesFromInput) : List (Nat × Nat) :=
  clauseEdgesFromFromInstructions (clauseEdgesFromInstructions p)

/-! ### Semantics -/

theorem clauseEdgesFromClauseInstructions_fold
    (n j : Nat) (out : List (Nat × Nat)) (cs : SAT.CNF) :
    ((cs.map clauseEdgesFromClauseInstruction).foldl
        (fun acc instr => clauseEdgesFromStep (acc, instr)) (n, (j, out))) =
      (n, (j + cs.length, out ++ clauseEdgesFrom n j cs)) := by
  induction cs generalizing j out with
  | nil =>
      simp [clauseEdgesFrom]
  | cons c rest ih =>
      change
        ((rest.map clauseEdgesFromClauseInstruction).foldl
            (fun acc instr => clauseEdgesFromStep (acc, instr))
            (n, (j + 1, out ++ clauseEdgesForFromInput (n, (j, c))))) =
          (n, (j + (c :: rest).length, out ++ clauseEdgesFrom n j (c :: rest)))
      rw [ih (j + 1) (out ++ clauseEdgesForFromInput (n, (j, c)))]
      simp [clauseEdgesFrom, clauseEdgesForFromInput, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem clauseEdgesFromRunner_eq_clauseEdgesFrom (p : ClauseEdgesFromInput) :
    clauseEdgesFromRunner p = clauseEdgesFromFromInput p := by
  rcases p with ⟨n, cs⟩
  change
    ((clauseEdgesFromInitInstruction n :: cs.map clauseEdgesFromClauseInstruction).foldl
      (fun acc instr => clauseEdgesFromStep (acc, instr)) clauseEdgesFromInitAcc).2.2 =
      clauseEdgesFrom n 0 cs
  rw [List.foldl_cons]
  simp [clauseEdgesFromInitInstruction, clauseEdgesFromStep]
  have h := clauseEdgesFromClauseInstructions_fold n 0 ([] : List (Nat × Nat)) cs
  simpa [clauseEdgesFromFromInput] using congrArg (fun acc => acc.2.2) h

/-! ### TM witnesses for instructions and one fold step -/

theorem clauseEdgesFromInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      clauseEdgesFromInstructionEncodedType
      clauseEdgesFromInitInstruction := by
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hN : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hEmpty :
      TMPolyTimeMap EncodedType.nat clauseStructuredEncodedType
        (fun _ : Nat => ([] : SAT.Clause)) :=
    TMPolyTimeMap.const EncodedType.nat clauseStructuredEncodedType []
  have hPayload :
      TMPolyTimeMap EncodedType.nat clauseEdgesFromInstructionPayloadEncodedType
        (fun n : Nat => (n, ([] : SAT.Clause))) :=
    TMPolyTimeMap.prod_mk hN hEmpty
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [clauseEdgesFromInitInstruction, clauseEdgesFromInstructionEncodedType,
    clauseEdgesFromInstructionPayloadEncodedType] using hOut

theorem clauseEdgesFromClauseInstruction_tm_polytime :
    TMPolyTimeMap
      clauseStructuredEncodedType
      clauseEdgesFromInstructionEncodedType
      clauseEdgesFromClauseInstruction := by
  have hTrue : TMPolyTimeMap clauseStructuredEncodedType EncodedType.bool
      (fun _ : SAT.Clause => true) :=
    TMPolyTimeMap.const clauseStructuredEncodedType EncodedType.bool true
  have hZero : TMPolyTimeMap clauseStructuredEncodedType EncodedType.nat
      (fun _ : SAT.Clause => (0 : Nat)) :=
    TMPolyTimeMap.const clauseStructuredEncodedType EncodedType.nat (0 : Nat)
  have hClause : TMPolyTimeMap clauseStructuredEncodedType clauseStructuredEncodedType id :=
    TMPolyTimeMap.id clauseStructuredEncodedType
  have hPayload :
      TMPolyTimeMap clauseStructuredEncodedType clauseEdgesFromInstructionPayloadEncodedType
        (fun c : SAT.Clause => ((0 : Nat), c)) :=
    TMPolyTimeMap.prod_mk hZero hClause
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [clauseEdgesFromClauseInstruction, clauseEdgesFromInstructionEncodedType,
    clauseEdgesFromInstructionPayloadEncodedType] using hOut

theorem clauseEdgesFromInstructions_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      clauseEdgesFromInstructionListEncodedType
      clauseEdgesFromInstructions := by
  let X := clauseEdgesFromInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ClauseEdgesFromInput => p.1) := by
    simpa [X, clauseEdgesFromInputEncodedType, ClauseEdgesFromInput] using
      TMPolyTimeMap.fst EncodedType.nat cnfStructuredEncodedType
  have hClauses :
      TMPolyTimeMap X cnfStructuredEncodedType (fun p : ClauseEdgesFromInput => p.2) := by
    simpa [X, clauseEdgesFromInputEncodedType, ClauseEdgesFromInput] using
      TMPolyTimeMap.snd EncodedType.nat cnfStructuredEncodedType
  have hInit :
      TMPolyTimeMap X clauseEdgesFromInstructionEncodedType
        (fun p : ClauseEdgesFromInput => clauseEdgesFromInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp clauseEdgesFromInitInstruction_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hClauseInstrs :
      TMPolyTimeMap X clauseEdgesFromInstructionListEncodedType
        (fun p : ClauseEdgesFromInput => p.2.map clauseEdgesFromClauseInstruction) := by
    have hMap := TMPolyTimeMap.list_map clauseEdgesFromClauseInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hClauses
    simpa [Function.comp, clauseEdgesFromInstructionListEncodedType, cnfStructuredEncodedType,
      X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod clauseEdgesFromInstructionEncodedType
          clauseEdgesFromInstructionListEncodedType)
        (fun p : ClauseEdgesFromInput =>
          (clauseEdgesFromInitInstruction p.1,
            p.2.map clauseEdgesFromClauseInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hClauseInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseEdgesFromInstructionEncodedType)
      hConsInput
  simpa [Function.comp, clauseEdgesFromInstructions,
    clauseEdgesFromInstructionListEncodedType, X] using hOut

theorem clauseEdgesFromAcc_mk_tm_polytime
    {X : EncodedType} {n j : X.Carrier → Nat}
    {out : X.Carrier → List (Nat × Nat)}
    (hN : TMPolyTimeMap X EncodedType.nat n)
    (hJ : TMPolyTimeMap X EncodedType.nat j)
    (hOut : TMPolyTimeMap X edgeListStructuredEncodedType out) :
    TMPolyTimeMap X clauseEdgesFromAccEncodedType
      (fun x => (n x, (j x, out x))) := by
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat edgeListStructuredEncodedType)
        (fun x => (j x, out x)) :=
    TMPolyTimeMap.prod_mk hJ hOut
  simpa [clauseEdgesFromAccEncodedType] using TMPolyTimeMap.prod_mk hN hTail

theorem clauseEdgesFromStep_tm_polytime :
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
    have hComp := TMPolyTimeMap.comp clauseEdgesFor_tm_polytime hClauseEdgesInput
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

/-! ### Reachable fold bounds and full clause-list runner -/

noncomputable def clauseEdgesFromPerClauseBoundPolynomial : Polynomial Nat :=
  Polynomial.C 10000 * (Polynomial.X * Polynomial.X) + Polynomial.C 10000

@[simp] theorem clauseEdgesFromPerClauseBoundPolynomial_eval (N : Nat) :
    clauseEdgesFromPerClauseBoundPolynomial.eval N = 10000 * (N * N) + 10000 := by
  simp [clauseEdgesFromPerClauseBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

noncomputable def clauseEdgesFromFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 30000 * (Polynomial.X * Polynomial.X * Polynomial.X) + Polynomial.C 30000

@[simp] theorem clauseEdgesFromFoldAccBoundPolynomial_eval (N : Nat) :
    clauseEdgesFromFoldAccBoundPolynomial.eval N = 30000 * (N * N * N) + 30000 := by
  simp [clauseEdgesFromFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

def clauseEdgesFromAccBound
    (N processed : Nat) (acc : ClauseEdgesFromAcc) : Prop :=
  acc.1 ≤ N ∧
    acc.2.1 ≤ processed ∧
      edgeListStructuredEncodedType.inputSize acc.2.2 ≤
        processed * clauseEdgesFromPerClauseBoundPolynomial.eval N

theorem clauseEdgesFromInstruction_nat_inputSize_le
    {N : Nat} {instr : ClauseEdgesFromInstruction}
    (hInstr : clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N) :
    instr.2.1 ≤ N := by
  rcases instr with ⟨tag, n, c⟩
  change n ≤ N
  simp [clauseEdgesFromInstructionEncodedType, clauseEdgesFromInstructionPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat] at hInstr
  omega

theorem clauseEdgesFromInstruction_clause_inputSize_le
    {N : Nat} {instr : ClauseEdgesFromInstruction}
    (hInstr : clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N) :
    clauseStructuredEncodedType.inputSize instr.2.2 ≤ N := by
  rcases instr with ⟨tag, n, c⟩
  change clauseStructuredEncodedType.inputSize c ≤ N
  simp [clauseEdgesFromInstructionEncodedType, clauseEdgesFromInstructionPayloadEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool] at hInstr
  omega

theorem clauseEdgesFromInitInstruction_inputSize_le (n : Nat) :
    clauseEdgesFromInstructionEncodedType.inputSize (clauseEdgesFromInitInstruction n) ≤
      n + 4 := by
  have hEmpty : clauseStructuredEncodedType.inputSize ([] : SAT.Clause) = 0 := by
    change (EncodedType.list literalStructuredEncodedType).inputSize
      ([] : List SAT.Literal) = 0
    exact EncodedType.inputSize_list_nil literalStructuredEncodedType
  simp [clauseEdgesFromInitInstruction, clauseEdgesFromInstructionEncodedType,
    clauseEdgesFromInstructionPayloadEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, EncodedType.inputSize_nat, hEmpty]
  omega

theorem clauseEdgesFromClauseInstruction_inputSize_le (c : SAT.Clause) :
    clauseEdgesFromInstructionEncodedType.inputSize (clauseEdgesFromClauseInstruction c) ≤
      clauseStructuredEncodedType.inputSize c + 4 := by
  simp [clauseEdgesFromClauseInstruction, clauseEdgesFromInstructionEncodedType,
    clauseEdgesFromInstructionPayloadEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, EncodedType.inputSize_nat]
  omega

theorem clauseEdgesFromClauseInstructions_inputSize_le (cs : SAT.CNF) :
    clauseEdgesFromInstructionListEncodedType.inputSize
        (cs.map clauseEdgesFromClauseInstruction) ≤
      cnfStructuredEncodedType.inputSize cs + 4 * cs.length := by
  induction cs with
  | nil =>
      simp [clauseEdgesFromInstructionListEncodedType, cnfStructuredEncodedType]
  | cons c cs ih =>
      have hc := clauseEdgesFromClauseInstruction_inputSize_le c
      simp only [List.map_cons]
      change
        (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
            (clauseEdgesFromClauseInstruction c :: cs.map clauseEdgesFromClauseInstruction) ≤
          (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs) +
            4 * (c :: cs).length
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have ih' :
          (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
              (cs.map clauseEdgesFromClauseInstruction) ≤
            (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * cs.length := by
        simpa [clauseEdgesFromInstructionListEncodedType, cnfStructuredEncodedType] using ih
      change
        clauseEdgesFromInstructionEncodedType.inputSize
            (clauseEdgesFromClauseInstruction c) + 1 +
              (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
                (cs.map clauseEdgesFromClauseInstruction) ≤
          clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * (cs.length + 1)
      omega

theorem clauseEdgesFromInstructions_inputSize_le (p : ClauseEdgesFromInput) :
    clauseEdgesFromInstructionListEncodedType.inputSize (clauseEdgesFromInstructions p) ≤
      6 * clauseEdgesFromInputEncodedType.inputSize p + 10 := by
  rcases p with ⟨n, cs⟩
  have hInit := clauseEdgesFromInitInstruction_inputSize_le n
  have hMap := clauseEdgesFromClauseInstructions_inputSize_le cs
  have hLen :=
    Clique.encodedList_length_le_inputSize clauseStructuredEncodedType cs
  have hLen' : cs.length ≤ cnfStructuredEncodedType.inputSize cs := by
    simpa [cnfStructuredEncodedType] using hLen
  have hLenBound :
      cs.length ≤ (EncodedType.list clauseStructuredEncodedType).inputSize cs := by
    simpa [cnfStructuredEncodedType] using hLen'
  simp only [clauseEdgesFromInstructions]
  change
    (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
        (clauseEdgesFromInitInstruction n :: cs.map clauseEdgesFromClauseInstruction) ≤
      6 * clauseEdgesFromInputEncodedType.inputSize (n, cs) + 10
  rw [EncodedType.inputSize_list_cons]
  have hMap' :
      (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
          (cs.map clauseEdgesFromClauseInstruction) ≤
        (EncodedType.list clauseStructuredEncodedType).inputSize cs + 4 * cs.length := by
    simpa [clauseEdgesFromInstructionListEncodedType, cnfStructuredEncodedType] using hMap
  change
    clauseEdgesFromInstructionEncodedType.inputSize (clauseEdgesFromInitInstruction n) + 1 +
        (EncodedType.list clauseEdgesFromInstructionEncodedType).inputSize
          (cs.map clauseEdgesFromClauseInstruction) ≤
      6 * clauseEdgesFromInputEncodedType.inputSize (n, cs) + 10
  simp [clauseEdgesFromInputEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, cnfStructuredEncodedType]
  omega

theorem clauseEdgesForFromInput_size_le_of_bounds
    {N n j : Nat} {c : SAT.Clause}
    (hn : n ≤ N) (hj : j ≤ N) (hc : clauseStructuredEncodedType.inputSize c ≤ N) :
    edgeListStructuredEncodedType.inputSize (clauseEdgesForFromInput (n, (j, c))) ≤
      clauseEdgesFromPerClauseBoundPolynomial.eval N := by
  have hInput :
      clauseEdgesForInputEncodedType.inputSize (n, (j, c)) ≤ 3 * N + 4 := by
    simp [clauseEdgesForInputEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat]
    omega
  have hRaw := clauseEdgesForFromInput_structured_inputSize_le (n, (j, c))
  have hPow :
      clauseEdgesForInputEncodedType.inputSize (n, (j, c)) ^ 2 ≤ (3 * N + 4) ^ 2 :=
    Nat.pow_le_pow_left hInput 2
  calc
    edgeListStructuredEncodedType.inputSize (clauseEdgesForFromInput (n, (j, c)))
        ≤ 200 * clauseEdgesForInputEncodedType.inputSize (n, (j, c)) ^ 2 + 200 := hRaw
    _ ≤ 200 * (3 * N + 4) ^ 2 + 200 := by nlinarith
    _ ≤ clauseEdgesFromPerClauseBoundPolynomial.eval N := by
          simp [clauseEdgesFromPerClauseBoundPolynomial_eval, pow_two]
          nlinarith [sq_nonneg (N : Int)]

theorem clauseEdgesFromStep_bound {N processed : Nat}
    {acc : ClauseEdgesFromAcc} {instr : ClauseEdgesFromInstruction}
    (hAcc : clauseEdgesFromAccBound N processed acc)
    (hProcessed : processed + 1 ≤ N)
    (hInstr : clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N) :
    clauseEdgesFromAccBound N (processed + 1) (clauseEdgesFromStep (acc, instr)) := by
  rcases acc with ⟨n, j, out⟩
  rcases instr with ⟨tag, initN, c⟩
  rcases hAcc with ⟨hn, hj, hout⟩
  change n ≤ N at hn
  change j ≤ processed at hj
  change edgeListStructuredEncodedType.inputSize out ≤
    processed * clauseEdgesFromPerClauseBoundPolynomial.eval N at hout
  cases tag
  · have hInitN : initN ≤ N :=
      clauseEdgesFromInstruction_nat_inputSize_le
        (N := N) (instr := (false, (initN, c))) hInstr
    simp [clauseEdgesFromStep, clauseEdgesFromAccBound]
    refine ⟨hInitN, ?_⟩
    rw [show edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType]
    exact Nat.zero_le _
  · have hc : clauseStructuredEncodedType.inputSize c ≤ N :=
      clauseEdgesFromInstruction_clause_inputSize_le
        (N := N) (instr := (true, (initN, c))) hInstr
    have hjN : j ≤ N := by omega
    have hNew :=
      clauseEdgesForFromInput_size_le_of_bounds (N := N) (n := n) (j := j) (c := c)
        hn hjN hc
    have hAppend :
        edgeListStructuredEncodedType.inputSize
            (out ++ clauseEdgesForFromInput (n, (j, c))) =
          edgeListStructuredEncodedType.inputSize out +
            edgeListStructuredEncodedType.inputSize (clauseEdgesForFromInput (n, (j, c))) := by
      simpa [edgeListStructuredEncodedType] using
        Clique.encodedList_inputSize_append edgeStructuredEncodedType out
          (clauseEdgesForFromInput (n, (j, c)))
    simp [clauseEdgesFromStep, clauseEdgesFromAccBound, hAppend]
    refine ⟨hn, by omega, ?_⟩
    calc
      edgeListStructuredEncodedType.inputSize out +
          edgeListStructuredEncodedType.inputSize (clauseEdgesForFromInput (n, (j, c)))
          ≤
        processed * clauseEdgesFromPerClauseBoundPolynomial.eval N +
          clauseEdgesFromPerClauseBoundPolynomial.eval N := by
          exact Nat.add_le_add hout hNew
      _ = (processed + 1) * clauseEdgesFromPerClauseBoundPolynomial.eval N := by
          ring
      _ = (processed + 1) * (10000 * (N * N) + 10000) := by
          simp [clauseEdgesFromPerClauseBoundPolynomial_eval]

theorem clauseEdgesFromFold_bound_aux
    {N processed : Nat}
    (xs : List ClauseEdgesFromInstruction) (acc : ClauseEdgesFromAcc)
    (hAcc : clauseEdgesFromAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N) :
    clauseEdgesFromAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => clauseEdgesFromStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons x xs ih =>
      have hx : clauseEdgesFromInstructionEncodedType.inputSize x ≤ N := hInstr x (by simp)
      have hStepProcessed : processed + 1 ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hStep := clauseEdgesFromStep_bound hAcc hStepProcessed hx
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1) (acc := clauseEdgesFromStep (acc, x))
          hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem clauseEdgesFromFold_bound_of_inputSize_le
    {N : Nat} (xs : List ClauseEdgesFromInstruction)
    (hSize : clauseEdgesFromInstructionListEncodedType.inputSize xs ≤ N) :
    clauseEdgesFromAccBound N xs.length
      (xs.foldl (fun acc instr => clauseEdgesFromStep (acc, instr))
        clauseEdgesFromInitAcc) := by
  have hInit : clauseEdgesFromAccBound N 0 clauseEdgesFromInitAcc := by
    have hEmpty :
        edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 :=
      EncodedType.inputSize_list_nil edgeStructuredEncodedType
    simp [clauseEdgesFromAccBound, clauseEdgesFromInitAcc, hEmpty]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      Clique.encodedList_length_le_inputSize clauseEdgesFromInstructionEncodedType xs
    have hLenInput' : xs.length ≤ clauseEdgesFromInstructionListEncodedType.inputSize xs := by
      simpa [clauseEdgesFromInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, clauseEdgesFromInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      Clique.encodedList_element_inputSize_le
        (X := clauseEdgesFromInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : clauseEdgesFromInstructionEncodedType.inputSize instr ≤
        clauseEdgesFromInstructionListEncodedType.inputSize xs := by
      simpa [clauseEdgesFromInstructionListEncodedType] using hElem
    omega
  have h :=
    clauseEdgesFromFold_bound_aux (N := N) (processed := 0) xs clauseEdgesFromInitAcc
      hInit hLen hInstr
  simpa using h

theorem clauseEdgesFromAccBound_inputSize_le {N processed : Nat}
    {acc : ClauseEdgesFromAcc}
    (hAcc : clauseEdgesFromAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    clauseEdgesFromAccEncodedType.inputSize acc ≤
      clauseEdgesFromFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨n, j, out⟩
  rcases hAcc with ⟨hn, hj, hout⟩
  let Bedge := clauseEdgesFromPerClauseBoundPolynomial.eval N
  have houtN :
      edgeListStructuredEncodedType.inputSize out ≤ N * Bedge :=
    hout.trans (Nat.mul_le_mul_right Bedge hProcessed)
  have hBedge : Bedge = 10000 * (N * N) + 10000 := by
    simp [Bedge]
  simp [clauseEdgesFromAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  simp [hBedge] at houtN ⊢
  nlinarith [sq_nonneg (N : Int), hn, hj, houtN]

theorem clauseEdgesFromAcc_edges_inputSize_le (acc : ClauseEdgesFromAcc) :
    edgeListStructuredEncodedType.inputSize acc.2.2 ≤
      clauseEdgesFromAccEncodedType.inputSize acc := by
  rcases acc with ⟨n, j, out⟩
  simp [clauseEdgesFromAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  omega

theorem clauseEdgesFromFromInstructions_inputSize_le
    (xs : List ClauseEdgesFromInstruction) :
    edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInstructions xs) ≤
      clauseEdgesFromFoldAccBoundPolynomial.eval
        (clauseEdgesFromInstructionListEncodedType.inputSize xs) := by
  let N := clauseEdgesFromInstructionListEncodedType.inputSize xs
  let acc := clauseEdgesFromInstructionsFold xs
  have hFold :
      clauseEdgesFromAccBound N xs.length acc := by
    simpa [N, acc, clauseEdgesFromInstructionsFold] using
      clauseEdgesFromFold_bound_of_inputSize_le (N := N) xs (Nat.le_refl N)
  have hLen : xs.length ≤ N := by
    have h :=
      Clique.encodedList_length_le_inputSize clauseEdgesFromInstructionEncodedType xs
    simpa [N, clauseEdgesFromInstructionListEncodedType] using h
  have hAccSize :
      clauseEdgesFromAccEncodedType.inputSize acc ≤
        clauseEdgesFromFoldAccBoundPolynomial.eval N :=
    clauseEdgesFromAccBound_inputSize_le hFold hLen
  have hOut := clauseEdgesFromAcc_edges_inputSize_le acc
  simpa [clauseEdgesFromFromInstructions, acc, N] using hOut.trans hAccSize

theorem clauseEdgesFromFromInput_structured_inputSize_le (p : ClauseEdgesFromInput) :
    edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p) ≤
      1000000000 * clauseEdgesFromInputEncodedType.inputSize p ^ 3 + 1000000000 := by
  let N := clauseEdgesFromInputEncodedType.inputSize p
  let xs := clauseEdgesFromInstructions p
  let M := clauseEdgesFromInstructionListEncodedType.inputSize xs
  have hRunner := clauseEdgesFromFromInstructions_inputSize_le xs
  have hM : M ≤ 6 * N + 10 := by
    simpa [M, N, xs] using clauseEdgesFromInstructions_inputSize_le p
  have hPow : M ^ 3 ≤ (6 * N + 10) ^ 3 :=
    Nat.pow_le_pow_left hM 3
  have hEval :
      clauseEdgesFromFoldAccBoundPolynomial.eval M ≤
        1000000000 * N ^ 3 + 1000000000 := by
    have hCube :
        (6 * N + 10) ^ 3 ≤ 5000 * N ^ 3 + 5000 := by
      by_cases hZero : N = 0
      · simp [hZero]
      · have hPos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hZero)
        have hLin : 6 * N + 10 ≤ 16 * N := by
          nlinarith
        have hPow16 : (6 * N + 10) ^ 3 ≤ (16 * N) ^ 3 :=
          Nat.pow_le_pow_left hLin 3
        calc
          (6 * N + 10) ^ 3 ≤ (16 * N) ^ 3 := hPow16
          _ = 4096 * N ^ 3 := by ring
          _ ≤ 5000 * N ^ 3 + 5000 := by nlinarith
    have hRaw :
        30000 * M ^ 3 + 30000 ≤
          1000000000 * N ^ 3 + 1000000000 := by
      nlinarith [hPow, hCube]
    simpa [clauseEdgesFromFoldAccBoundPolynomial_eval, pow_succ, pow_two,
      Nat.mul_assoc] using hRaw
  calc
    edgeListStructuredEncodedType.inputSize (clauseEdgesFromFromInput p)
        =
      edgeListStructuredEncodedType.inputSize (clauseEdgesFromRunner p) := by
        rw [clauseEdgesFromRunner_eq_clauseEdgesFrom]
    _ ≤ clauseEdgesFromFoldAccBoundPolynomial.eval M := by
        simpa [clauseEdgesFromRunner, xs, M] using hRunner
    _ ≤ 1000000000 * N ^ 3 + 1000000000 := hEval

noncomputable def clauseEdgesFromFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod clauseEdgesFromAccEncodedType
          clauseEdgesFromInstructionEncodedType).encode
        clauseEdgesFromAccEncodedType.encode
        clauseEdgesFromStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm clauseEdgesFromFoldAccBoundPolynomial
    (hStep.time.comp
      (clauseEdgesFromFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem clauseEdgesFromInstructionsFold_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInstructionListEncodedType
      clauseEdgesFromAccEncodedType
      clauseEdgesFromInstructionsFold := by
  rcases clauseEdgesFromStep_tm_polytime with ⟨hStep⟩
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
            | nil =>
                simp
            | cons y ys ih =>
                simp
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

theorem clauseEdgesFromFromInstructions_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInstructionListEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromFromInstructions := by
  have hFold := clauseEdgesFromInstructionsFold_tm_polytime
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

theorem clauseEdgesFromRunner_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromRunner := by
  have hComp :=
    TMPolyTimeMap.comp clauseEdgesFromFromInstructions_tm_polytime
      clauseEdgesFromInstructions_tm_polytime
  simpa [Function.comp, clauseEdgesFromRunner] using hComp

theorem clauseEdgesFrom_tm_polytime :
    TMPolyTimeMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromFromInput := by
  convert clauseEdgesFromRunner_tm_polytime using 1
  funext p
  exact (clauseEdgesFromRunner_eq_clauseEdgesFrom p).symm

theorem clauseEdgesFrom_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : ClauseEdgesFromInput => clauseEdgesFromInputEncodedType.inputSize p)
      (fun edges : edgeListStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      clauseEdgesFromFromInput := by
  refine PolynomialSizeBound.intro_with 3 1000000000 1000000000 ?_
  intro p
  exact clauseEdgesFromFromInput_structured_inputSize_le p

noncomputable def clauseEdgesFromTMBackedMap :
    TMBackedCostedMap
      clauseEdgesFromInputEncodedType
      edgeListStructuredEncodedType
      clauseEdgesFromFromInput where
  costed := CostedMap.of_encodedPolynomialSizeBound clauseEdgesFrom_polynomialSizeBound
  tm_polytime := clauseEdgesFrom_tm_polytime

end ChromaticNumber
end Karp21
end ComplexityReduction
