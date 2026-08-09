/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM

/-!
Formula-level direct-TM runner components for the finite-certificate 3SAT
verifier.

This file builds on the lookup/literal layer and adds executable clause folds.
-/

namespace ComplexityReduction
namespace SAT

open ComplexityReduction.Karp21

/-! ### Clause evaluation runner -/

/-- Input for executable clause evaluation: certificate bits and one clause. -/
abbrev clauseFiniteEvalInputEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType

/-- Clause-fold accumulator: certificate bits carried with the current OR value. -/
abbrev clauseFiniteEvalAcc : Type :=
  List Bool × Bool

/-- Encoding for the clause-fold accumulator. -/
abbrev clauseFiniteEvalAccEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType EncodedType.bool

/-- A harmless literal payload for initializer instructions. -/
def defaultFiniteVerifierLiteral : Literal :=
  { var := (0 : Nat), neg := false }

/--
Clause instructions.  A `false` tag initializes the carried certificate bits;
a `true` tag evaluates the literal payload and ORs it into the accumulator.
-/
abbrev clauseFiniteEvalInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)

/-- Encoded lists of clause-evaluation instructions. -/
abbrev clauseFiniteEvalInstructionListEncodedType : EncodedType :=
  EncodedType.list clauseFiniteEvalInstructionEncodedType

/-- Fixed initial accumulator used before the initializer instruction is read. -/
def clauseFiniteEvalInitAcc : clauseFiniteEvalAcc :=
  (([] : List Bool), false)

/-- Initializer instruction carrying the certificate bits. -/
def clauseFiniteEvalInitInstruction (bits : List Bool) :
    clauseFiniteEvalInstructionEncodedType.Carrier :=
  (false, (bits, defaultFiniteVerifierLiteral))

/-- Literal instruction carrying one clause literal. -/
def clauseFiniteEvalLiteralInstruction (l : Literal) :
    clauseFiniteEvalInstructionEncodedType.Carrier :=
  (true, (([] : List Bool), l))

/-- Instruction list for executable clause evaluation. -/
def clauseFiniteEvalInstructions (p : List Bool × Clause) :
    List clauseFiniteEvalInstructionEncodedType.Carrier :=
  clauseFiniteEvalInitInstruction p.1 :: p.2.map clauseFiniteEvalLiteralInstruction

/-- One instruction-fold step for executable clause evaluation. -/
def clauseFiniteEvalStep
    (p : clauseFiniteEvalAcc × clauseFiniteEvalInstructionEncodedType.Carrier) :
    clauseFiniteEvalAcc :=
  match p.2.1 with
  | false => (p.2.2.1, false)
  | true =>
      (p.1.1,
        Karp21.Clique.boolOrPair
          (p.1.2, literalFiniteEvalBool (p.1.1, p.2.2.2)))

/-- Execute a clause-evaluation instruction list and return the OR value. -/
def clauseFiniteEvalFromInstructions
    (xs : List clauseFiniteEvalInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => clauseFiniteEvalStep (acc, instr))
    clauseFiniteEvalInitAcc).2

/-- Executable finite-certificate clause evaluation. -/
def clauseFiniteEvalBool (p : List Bool × Clause) : Bool :=
  clauseFiniteEvalFromInstructions (clauseFiniteEvalInstructions p)

theorem clauseFiniteEvalLiteralInstructions_fold_eq
    (bits : List Bool) (c : Clause) (acc : Bool) :
    (c.map clauseFiniteEvalLiteralInstruction).foldl
        (fun acc instr => clauseFiniteEvalStep (acc, instr)) (bits, acc) =
      (bits,
        c.foldl
          (fun acc lit => Karp21.Clique.boolOrPair
            (acc, literalFiniteEvalBool (bits, lit)))
          acc) := by
  induction c generalizing acc with
  | nil =>
      simp
  | cons lit rest ih =>
      simpa [clauseFiniteEvalLiteralInstruction, clauseFiniteEvalStep] using
        ih (Karp21.Clique.boolOrPair (acc, literalFiniteEvalBool (bits, lit)))

theorem clauseFiniteEvalBool_eq_fold (bits : List Bool) (c : Clause) :
    clauseFiniteEvalBool (bits, c) =
      c.foldl
        (fun acc lit => Karp21.Clique.boolOrPair
          (acc, literalFiniteEvalBool (bits, lit)))
        false := by
  change
    ((clauseFiniteEvalInitInstruction bits :: c.map clauseFiniteEvalLiteralInstruction).foldl
      (fun acc instr => clauseFiniteEvalStep (acc, instr)) clauseFiniteEvalInitAcc).2 =
      c.foldl
        (fun acc lit => Karp21.Clique.boolOrPair
          (acc, literalFiniteEvalBool (bits, lit)))
        false
  simp [clauseFiniteEvalInitInstruction, clauseFiniteEvalInitAcc, clauseFiniteEvalStep]
  exact congrArg Prod.snd (clauseFiniteEvalLiteralInstructions_fold_eq bits c false)

theorem boolOrPair_eq_true_iff (a b : Bool) :
    Karp21.Clique.boolOrPair (a, b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [Karp21.Clique.boolOrPair]

theorem clauseFiniteEvalFold_eq_true_iff
    (bits : List Bool) (c : Clause) (acc : Bool) :
    c.foldl
        (fun acc lit => Karp21.Clique.boolOrPair
          (acc, literalFiniteEvalBool (bits, lit)))
        acc = true ↔
      acc = true ∨ Clause.Satisfies c (finiteAssignment bits) := by
  induction c generalizing acc with
  | nil =>
      simp [Clause.Satisfies]
  | cons lit rest ih =>
      change
        rest.foldl
            (fun acc lit => Karp21.Clique.boolOrPair
              (acc, literalFiniteEvalBool (bits, lit)))
            (Karp21.Clique.boolOrPair (acc, literalFiniteEvalBool (bits, lit))) = true ↔
          acc = true ∨ Clause.Satisfies (lit :: rest) (finiteAssignment bits)
      rw [ih]
      simp [Clause.Satisfies, boolOrPair_eq_true_iff, literalFiniteEvalBool_eq_eval,
        or_assoc]

theorem clauseFiniteEvalBool_eq_true_iff (bits : List Bool) (c : Clause) :
    clauseFiniteEvalBool (bits, c) = true ↔
      Clause.Satisfies c (finiteAssignment bits) := by
  rw [clauseFiniteEvalBool_eq_fold, clauseFiniteEvalFold_eq_true_iff]
  simp

/-! #### Direct TM witnesses for clause evaluation -/

theorem clauseFiniteEvalInitInstruction_tm_polytime :
    TMPolyTimeMap
      finiteAssignmentCertEncodedType
      clauseFiniteEvalInstructionEncodedType
      clauseFiniteEvalInitInstruction := by
  have hFalse : TMPolyTimeMap finiteAssignmentCertEncodedType EncodedType.bool
      (fun _ : List Bool => false) :=
    TMPolyTimeMap.const finiteAssignmentCertEncodedType EncodedType.bool false
  have hBits : TMPolyTimeMap finiteAssignmentCertEncodedType finiteAssignmentCertEncodedType
      (fun bits : List Bool => bits) :=
    TMPolyTimeMap.id finiteAssignmentCertEncodedType
  have hLit : TMPolyTimeMap finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType
      (fun _ : List Bool => defaultFiniteVerifierLiteral) :=
    TMPolyTimeMap.const finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType
      defaultFiniteVerifierLiteral
  have hPayload : TMPolyTimeMap finiteAssignmentCertEncodedType
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)
      (fun bits : List Bool => (bits, defaultFiniteVerifierLiteral)) :=
    TMPolyTimeMap.prod_mk hBits hLit
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [clauseFiniteEvalInitInstruction, clauseFiniteEvalInstructionEncodedType] using hOut

theorem clauseFiniteEvalLiteralInstruction_tm_polytime :
    TMPolyTimeMap
      Karp21.literalStructuredEncodedType
      clauseFiniteEvalInstructionEncodedType
      clauseFiniteEvalLiteralInstruction := by
  have hTrue : TMPolyTimeMap Karp21.literalStructuredEncodedType EncodedType.bool
      (fun _ : Literal => true) :=
    TMPolyTimeMap.const Karp21.literalStructuredEncodedType EncodedType.bool true
  have hBits : TMPolyTimeMap Karp21.literalStructuredEncodedType finiteAssignmentCertEncodedType
      (fun _ : Literal => ([] : List Bool)) :=
    TMPolyTimeMap.const Karp21.literalStructuredEncodedType finiteAssignmentCertEncodedType []
  have hLit : TMPolyTimeMap Karp21.literalStructuredEncodedType Karp21.literalStructuredEncodedType
      (fun l : Literal => l) :=
    TMPolyTimeMap.id Karp21.literalStructuredEncodedType
  have hPayload : TMPolyTimeMap Karp21.literalStructuredEncodedType
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)
      (fun l : Literal => (([] : List Bool), l)) :=
    TMPolyTimeMap.prod_mk hBits hLit
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [clauseFiniteEvalLiteralInstruction, clauseFiniteEvalInstructionEncodedType] using hOut

theorem clauseFiniteEvalInstructions_tm_polytime :
    TMPolyTimeMap
      clauseFiniteEvalInputEncodedType
      clauseFiniteEvalInstructionListEncodedType
      clauseFiniteEvalInstructions := by
  let X := clauseFiniteEvalInputEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, clauseFiniteEvalInputEncodedType] using
      TMPolyTimeMap.fst finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType
  have hClause : TMPolyTimeMap X Karp21.clauseStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, clauseFiniteEvalInputEncodedType] using
      TMPolyTimeMap.snd finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType
  have hInit : TMPolyTimeMap X clauseFiniteEvalInstructionEncodedType
      (fun p : X.Carrier => clauseFiniteEvalInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp clauseFiniteEvalInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hMappedClause : TMPolyTimeMap X clauseFiniteEvalInstructionListEncodedType
      (fun p : X.Carrier => p.2.map clauseFiniteEvalLiteralInstruction) := by
    have hMap := TMPolyTimeMap.list_map clauseFiniteEvalLiteralInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hClause
    simpa [Function.comp, clauseFiniteEvalInstructionListEncodedType,
      Karp21.clauseStructuredEncodedType, X] using hComp
  have hConsInput : TMPolyTimeMap X
      (EncodedType.prod clauseFiniteEvalInstructionEncodedType
        clauseFiniteEvalInstructionListEncodedType)
      (fun p : X.Carrier =>
        (clauseFiniteEvalInitInstruction p.1,
          p.2.map clauseFiniteEvalLiteralInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedClause
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons clauseFiniteEvalInstructionEncodedType) hConsInput
  simpa [Function.comp, clauseFiniteEvalInstructions,
    clauseFiniteEvalInstructionListEncodedType, X] using hCons

theorem clauseFiniteEvalStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod clauseFiniteEvalAccEncodedType clauseFiniteEvalInstructionEncodedType)
      clauseFiniteEvalAccEncodedType
      clauseFiniteEvalStep := by
  let X := EncodedType.prod clauseFiniteEvalAccEncodedType clauseFiniteEvalInstructionEncodedType
  let A := clauseFiniteEvalAccEncodedType
  let I := clauseFiniteEvalInstructionEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : clauseFiniteEvalAcc × I.Carrier => p.1) := by
    simpa [X, A, I] using
      TMPolyTimeMap.fst clauseFiniteEvalAccEncodedType clauseFiniteEvalInstructionEncodedType
  have hInstr : TMPolyTimeMap X I (fun p : clauseFiniteEvalAcc × I.Carrier => p.2) := by
    simpa [X, I] using
      TMPolyTimeMap.snd clauseFiniteEvalAccEncodedType clauseFiniteEvalInstructionEncodedType
  have hAccBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst finiteAssignmentCertEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, X, A, clauseFiniteEvalAccEncodedType] using hComp
  have hAccValue : TMPolyTimeMap X EncodedType.bool
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd finiteAssignmentCertEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, A, clauseFiniteEvalAccEncodedType] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, X, I, clauseFiniteEvalInstructionEncodedType] using hComp
  have hPayload : TMPolyTimeMap X
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.literalStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, X, I, clauseFiniteEvalInstructionEncodedType] using hComp
  have hInstrBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst finiteAssignmentCertEncodedType
      Karp21.literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hLiteral : TMPolyTimeMap X Karp21.literalStructuredEncodedType
      (fun p : clauseFiniteEvalAcc × I.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd finiteAssignmentCertEncodedType
      Karp21.literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hFalse : TMPolyTimeMap X EncodedType.bool
      (fun _ : clauseFiniteEvalAcc × I.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInitBranch : TMPolyTimeMap X A
      (fun p : clauseFiniteEvalAcc × I.Carrier => (p.2.2.1, false)) :=
    TMPolyTimeMap.prod_mk hInstrBits hFalse
  have hLiteralInput : TMPolyTimeMap X literalFiniteEvalInputEncodedType
      (fun p : clauseFiniteEvalAcc × I.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccBits hLiteral
  have hLiteralValue : TMPolyTimeMap X EncodedType.bool
      (fun p : clauseFiniteEvalAcc × I.Carrier =>
        literalFiniteEvalBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp literalFiniteEvalBool_tm_polytime hLiteralInput
    simpa [Function.comp, literalFiniteEvalInputEncodedType, X] using hComp
  have hOrInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : clauseFiniteEvalAcc × I.Carrier =>
        (p.1.2, literalFiniteEvalBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hAccValue hLiteralValue
  have hOrValue : TMPolyTimeMap X EncodedType.bool
      (fun p : clauseFiniteEvalAcc × I.Carrier =>
        Karp21.Clique.boolOrPair
          (p.1.2, literalFiniteEvalBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp Karp21.Clique.boolOrPair_tm_polytime hOrInput
    simpa [Function.comp, X] using hComp
  have hLiteralBranch : TMPolyTimeMap X A
      (fun p : clauseFiniteEvalAcc × I.Carrier =>
        (p.1.1,
          Karp21.Clique.boolOrPair
            (p.1.2, literalFiniteEvalBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccBits hOrValue
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : clauseFiniteEvalAcc × I.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :=
    Karp21.Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : clauseFiniteEvalAcc × I.Carrier => (p.2.2.1, false))
      (fTrue := fun p : clauseFiniteEvalAcc × I.Carrier =>
        (p.1.1,
          Karp21.Clique.boolOrPair
            (p.1.2, literalFiniteEvalBool (p.1.1, p.2.2.2))))
      hInitBranch hLiteralBranch
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext p
  rcases p with ⟨⟨bits, value⟩, ⟨tag, instrBits, lit⟩⟩
  cases tag <;> rfl

theorem clauseFiniteEvalInitAcc_bound
    (xs : List clauseFiniteEvalInstructionEncodedType.Carrier) :
    clauseFiniteEvalAccEncodedType.inputSize clauseFiniteEvalInitAcc ≤
      (Polynomial.C 10).eval (clauseFiniteEvalInstructionListEncodedType.inputSize xs) := by
  have hNil :
      (EncodedType.list EncodedType.bool).inputSize ([] : List Bool) = 0 :=
    EncodedType.inputSize_list_nil EncodedType.bool
  simp [clauseFiniteEvalInitAcc, clauseFiniteEvalAccEncodedType,
    finiteAssignmentCertEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_bool, hNil]

theorem clauseFiniteEvalStep_growth
    (source : List clauseFiniteEvalInstructionEncodedType.Carrier)
    (acc : clauseFiniteEvalAccEncodedType.Carrier)
    (instr : clauseFiniteEvalInstructionEncodedType.Carrier)
    (hInstr :
      clauseFiniteEvalInstructionEncodedType.inputSize instr ≤
        clauseFiniteEvalInstructionListEncodedType.inputSize source) :
    clauseFiniteEvalAccEncodedType.inputSize (clauseFiniteEvalStep (acc, instr)) ≤
      clauseFiniteEvalAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (clauseFiniteEvalInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨accBits, accValue⟩
  rcases instr with ⟨tag, instrBits, lit⟩
  change Bool at tag accValue
  cases tag
  · have hRaw := hInstr
    simp [clauseFiniteEvalStep, clauseFiniteEvalInstructionEncodedType,
      clauseFiniteEvalAccEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] at hRaw ⊢
    omega
  · simp [clauseFiniteEvalStep, clauseFiniteEvalAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem clauseFiniteEvalFold_tm_polytime :
    TMPolyTimeMap
      clauseFiniteEvalInstructionListEncodedType
      clauseFiniteEvalAccEncodedType
      (fun xs : List clauseFiniteEvalInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => clauseFiniteEvalStep (acc, instr))
          clauseFiniteEvalInitAcc) := by
  rcases clauseFiniteEvalStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      clauseFiniteEvalInstructionEncodedType clauseFiniteEvalAccEncodedType
      clauseFiniteEvalStep clauseFiniteEvalInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact clauseFiniteEvalInitAcc_bound xs
  · intro source acc instr hInstr
    exact clauseFiniteEvalStep_growth source acc instr hInstr

theorem clauseFiniteEvalFromInstructions_tm_polytime :
    TMPolyTimeMap
      clauseFiniteEvalInstructionListEncodedType
      EncodedType.bool
      clauseFiniteEvalFromInstructions := by
  have hFold := clauseFiniteEvalFold_tm_polytime
  have hValue := TMPolyTimeMap.snd finiteAssignmentCertEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hValue hFold
  simpa [Function.comp, clauseFiniteEvalFromInstructions, clauseFiniteEvalAccEncodedType]
    using hComp

theorem clauseFiniteEvalBool_tm_polytime :
    TMPolyTimeMap
      clauseFiniteEvalInputEncodedType
      EncodedType.bool
      clauseFiniteEvalBool := by
  have hComp :=
    TMPolyTimeMap.comp clauseFiniteEvalFromInstructions_tm_polytime
      clauseFiniteEvalInstructions_tm_polytime
  simpa [Function.comp, clauseFiniteEvalBool] using hComp

/-! ### CNF evaluation runner -/

/-- Input for executable CNF evaluation: certificate bits and one CNF formula. -/
abbrev cnfFiniteEvalInputEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType Karp21.cnfStructuredEncodedType

/-- CNF-fold accumulator: certificate bits carried with the current AND value. -/
abbrev cnfFiniteEvalAcc : Type :=
  List Bool × Bool

/-- Encoding for the CNF-fold accumulator. -/
abbrev cnfFiniteEvalAccEncodedType : EncodedType :=
  EncodedType.prod finiteAssignmentCertEncodedType EncodedType.bool

/--
CNF instructions.  A `false` tag initializes the carried certificate bits;
a `true` tag evaluates the clause payload and ANDs it into the accumulator.
-/
abbrev cnfFiniteEvalInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)

/-- Encoded lists of CNF-evaluation instructions. -/
abbrev cnfFiniteEvalInstructionListEncodedType : EncodedType :=
  EncodedType.list cnfFiniteEvalInstructionEncodedType

/-- Fixed initial accumulator used before the initializer instruction is read. -/
def cnfFiniteEvalInitAcc : cnfFiniteEvalAcc :=
  (([] : List Bool), true)

/-- Initializer instruction carrying the certificate bits. -/
def cnfFiniteEvalInitInstruction (bits : List Bool) :
    cnfFiniteEvalInstructionEncodedType.Carrier :=
  (false, (bits, ([] : Clause)))

/-- Clause instruction carrying one formula clause. -/
def cnfFiniteEvalClauseInstruction (c : Clause) :
    cnfFiniteEvalInstructionEncodedType.Carrier :=
  (true, (([] : List Bool), c))

/-- Instruction list for executable CNF evaluation. -/
def cnfFiniteEvalInstructions (p : List Bool × CNF) :
    List cnfFiniteEvalInstructionEncodedType.Carrier :=
  cnfFiniteEvalInitInstruction p.1 :: p.2.map cnfFiniteEvalClauseInstruction

/-- One instruction-fold step for executable CNF evaluation. -/
def cnfFiniteEvalStep
    (p : cnfFiniteEvalAcc × cnfFiniteEvalInstructionEncodedType.Carrier) :
    cnfFiniteEvalAcc :=
  match p.2.1 with
  | false => (p.2.2.1, true)
  | true =>
      (p.1.1,
        Karp21.Clique.boolAndPair
          (p.1.2, clauseFiniteEvalBool (p.1.1, p.2.2.2)))

/-- Execute a CNF-evaluation instruction list and return the AND value. -/
def cnfFiniteEvalFromInstructions
    (xs : List cnfFiniteEvalInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => cnfFiniteEvalStep (acc, instr))
    cnfFiniteEvalInitAcc).2

/-- Executable finite-certificate CNF evaluation. -/
def cnfFiniteEvalBool (p : List Bool × CNF) : Bool :=
  cnfFiniteEvalFromInstructions (cnfFiniteEvalInstructions p)

theorem cnfFiniteEvalClauseInstructions_fold_eq
    (bits : List Bool) (φ : CNF) (acc : Bool) :
    (φ.map cnfFiniteEvalClauseInstruction).foldl
        (fun acc instr => cnfFiniteEvalStep (acc, instr)) (bits, acc) =
      (bits,
        φ.foldl
          (fun acc c => Karp21.Clique.boolAndPair
            (acc, clauseFiniteEvalBool (bits, c)))
          acc) := by
  induction φ generalizing acc with
  | nil =>
      simp
  | cons c rest ih =>
      simpa [cnfFiniteEvalClauseInstruction, cnfFiniteEvalStep] using
        ih (Karp21.Clique.boolAndPair (acc, clauseFiniteEvalBool (bits, c)))

theorem cnfFiniteEvalBool_eq_fold (bits : List Bool) (φ : CNF) :
    cnfFiniteEvalBool (bits, φ) =
      φ.foldl
        (fun acc c => Karp21.Clique.boolAndPair
          (acc, clauseFiniteEvalBool (bits, c)))
        true := by
  change
    ((cnfFiniteEvalInitInstruction bits :: φ.map cnfFiniteEvalClauseInstruction).foldl
      (fun acc instr => cnfFiniteEvalStep (acc, instr)) cnfFiniteEvalInitAcc).2 =
      φ.foldl
        (fun acc c => Karp21.Clique.boolAndPair
          (acc, clauseFiniteEvalBool (bits, c)))
        true
  simp [cnfFiniteEvalInitInstruction, cnfFiniteEvalInitAcc, cnfFiniteEvalStep]
  exact congrArg Prod.snd (cnfFiniteEvalClauseInstructions_fold_eq bits φ true)

theorem boolAndPair_eq_true_iff (a b : Bool) :
    Karp21.Clique.boolAndPair (a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [Karp21.Clique.boolAndPair]

theorem cnfFiniteEvalFold_eq_true_iff
    (bits : List Bool) (φ : CNF) (acc : Bool) :
    φ.foldl
        (fun acc c => Karp21.Clique.boolAndPair
          (acc, clauseFiniteEvalBool (bits, c)))
        acc = true ↔
      acc = true ∧ CNF.Satisfies φ (finiteAssignment bits) := by
  induction φ generalizing acc with
  | nil =>
      simp [CNF.Satisfies]
  | cons c rest ih =>
      change
        rest.foldl
            (fun acc c => Karp21.Clique.boolAndPair
              (acc, clauseFiniteEvalBool (bits, c)))
            (Karp21.Clique.boolAndPair (acc, clauseFiniteEvalBool (bits, c))) = true ↔
          acc = true ∧ CNF.Satisfies (c :: rest) (finiteAssignment bits)
      rw [ih]
      simp [CNF.Satisfies, boolAndPair_eq_true_iff, clauseFiniteEvalBool_eq_true_iff,
        and_assoc]

theorem cnfFiniteEvalBool_eq_true_iff (bits : List Bool) (φ : CNF) :
    cnfFiniteEvalBool (bits, φ) = true ↔
      CNF.Satisfies φ (finiteAssignment bits) := by
  rw [cnfFiniteEvalBool_eq_fold, cnfFiniteEvalFold_eq_true_iff]
  simp

/-! #### Direct TM witnesses for CNF evaluation -/

theorem cnfFiniteEvalInitInstruction_tm_polytime :
    TMPolyTimeMap
      finiteAssignmentCertEncodedType
      cnfFiniteEvalInstructionEncodedType
      cnfFiniteEvalInitInstruction := by
  have hFalse : TMPolyTimeMap finiteAssignmentCertEncodedType EncodedType.bool
      (fun _ : List Bool => false) :=
    TMPolyTimeMap.const finiteAssignmentCertEncodedType EncodedType.bool false
  have hBits : TMPolyTimeMap finiteAssignmentCertEncodedType finiteAssignmentCertEncodedType
      (fun bits : List Bool => bits) :=
    TMPolyTimeMap.id finiteAssignmentCertEncodedType
  have hClause : TMPolyTimeMap finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType
      (fun _ : List Bool => ([] : Clause)) :=
    TMPolyTimeMap.const finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType []
  have hPayload : TMPolyTimeMap finiteAssignmentCertEncodedType
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)
      (fun bits : List Bool => (bits, ([] : Clause))) :=
    TMPolyTimeMap.prod_mk hBits hClause
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [cnfFiniteEvalInitInstruction, cnfFiniteEvalInstructionEncodedType] using hOut

theorem cnfFiniteEvalClauseInstruction_tm_polytime :
    TMPolyTimeMap
      Karp21.clauseStructuredEncodedType
      cnfFiniteEvalInstructionEncodedType
      cnfFiniteEvalClauseInstruction := by
  have hTrue : TMPolyTimeMap Karp21.clauseStructuredEncodedType EncodedType.bool
      (fun _ : Clause => true) :=
    TMPolyTimeMap.const Karp21.clauseStructuredEncodedType EncodedType.bool true
  have hBits : TMPolyTimeMap Karp21.clauseStructuredEncodedType finiteAssignmentCertEncodedType
      (fun _ : Clause => ([] : List Bool)) :=
    TMPolyTimeMap.const Karp21.clauseStructuredEncodedType finiteAssignmentCertEncodedType []
  have hClause : TMPolyTimeMap Karp21.clauseStructuredEncodedType
      Karp21.clauseStructuredEncodedType (fun c : Clause => c) :=
    TMPolyTimeMap.id Karp21.clauseStructuredEncodedType
  have hPayload : TMPolyTimeMap Karp21.clauseStructuredEncodedType
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)
      (fun c : Clause => (([] : List Bool), c)) :=
    TMPolyTimeMap.prod_mk hBits hClause
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [cnfFiniteEvalClauseInstruction, cnfFiniteEvalInstructionEncodedType] using hOut

theorem cnfFiniteEvalInstructions_tm_polytime :
    TMPolyTimeMap
      cnfFiniteEvalInputEncodedType
      cnfFiniteEvalInstructionListEncodedType
      cnfFiniteEvalInstructions := by
  let X := cnfFiniteEvalInputEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X, cnfFiniteEvalInputEncodedType] using
      TMPolyTimeMap.fst finiteAssignmentCertEncodedType Karp21.cnfStructuredEncodedType
  have hCNF : TMPolyTimeMap X Karp21.cnfStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, cnfFiniteEvalInputEncodedType] using
      TMPolyTimeMap.snd finiteAssignmentCertEncodedType Karp21.cnfStructuredEncodedType
  have hInit : TMPolyTimeMap X cnfFiniteEvalInstructionEncodedType
      (fun p : X.Carrier => cnfFiniteEvalInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp cnfFiniteEvalInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hMappedCNF : TMPolyTimeMap X cnfFiniteEvalInstructionListEncodedType
      (fun p : X.Carrier => p.2.map cnfFiniteEvalClauseInstruction) := by
    have hMap := TMPolyTimeMap.list_map cnfFiniteEvalClauseInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCNF
    simpa [Function.comp, cnfFiniteEvalInstructionListEncodedType,
      Karp21.cnfStructuredEncodedType, X] using hComp
  have hConsInput : TMPolyTimeMap X
      (EncodedType.prod cnfFiniteEvalInstructionEncodedType
        cnfFiniteEvalInstructionListEncodedType)
      (fun p : X.Carrier =>
        (cnfFiniteEvalInitInstruction p.1,
          p.2.map cnfFiniteEvalClauseInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedCNF
  have hCons :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons cnfFiniteEvalInstructionEncodedType) hConsInput
  simpa [Function.comp, cnfFiniteEvalInstructions, cnfFiniteEvalInstructionListEncodedType, X]
    using hCons

theorem cnfFiniteEvalStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod cnfFiniteEvalAccEncodedType cnfFiniteEvalInstructionEncodedType)
      cnfFiniteEvalAccEncodedType
      cnfFiniteEvalStep := by
  let X := EncodedType.prod cnfFiniteEvalAccEncodedType cnfFiniteEvalInstructionEncodedType
  let A := cnfFiniteEvalAccEncodedType
  let I := cnfFiniteEvalInstructionEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : cnfFiniteEvalAcc × I.Carrier => p.1) := by
    simpa [X, A, I] using
      TMPolyTimeMap.fst cnfFiniteEvalAccEncodedType cnfFiniteEvalInstructionEncodedType
  have hInstr : TMPolyTimeMap X I (fun p : cnfFiniteEvalAcc × I.Carrier => p.2) := by
    simpa [X, I] using
      TMPolyTimeMap.snd cnfFiniteEvalAccEncodedType cnfFiniteEvalInstructionEncodedType
  have hAccBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst finiteAssignmentCertEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, X, A, cnfFiniteEvalAccEncodedType] using hComp
  have hAccValue : TMPolyTimeMap X EncodedType.bool
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd finiteAssignmentCertEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, A, cnfFiniteEvalAccEncodedType] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, X, I, cnfFiniteEvalInstructionEncodedType] using hComp
  have hPayload : TMPolyTimeMap X
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      (EncodedType.prod finiteAssignmentCertEncodedType Karp21.clauseStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, X, I, cnfFiniteEvalInstructionEncodedType] using hComp
  have hInstrBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst finiteAssignmentCertEncodedType
      Karp21.clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hClause : TMPolyTimeMap X Karp21.clauseStructuredEncodedType
      (fun p : cnfFiniteEvalAcc × I.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd finiteAssignmentCertEncodedType
      Karp21.clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool
      (fun _ : cnfFiniteEvalAcc × I.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hInitBranch : TMPolyTimeMap X A
      (fun p : cnfFiniteEvalAcc × I.Carrier => (p.2.2.1, true)) :=
    TMPolyTimeMap.prod_mk hInstrBits hTrue
  have hClauseInput : TMPolyTimeMap X clauseFiniteEvalInputEncodedType
      (fun p : cnfFiniteEvalAcc × I.Carrier => (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccBits hClause
  have hClauseValue : TMPolyTimeMap X EncodedType.bool
      (fun p : cnfFiniteEvalAcc × I.Carrier =>
        clauseFiniteEvalBool (p.1.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp clauseFiniteEvalBool_tm_polytime hClauseInput
    simpa [Function.comp, clauseFiniteEvalInputEncodedType, X] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : cnfFiniteEvalAcc × I.Carrier =>
        (p.1.2, clauseFiniteEvalBool (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hAccValue hClauseValue
  have hAndValue : TMPolyTimeMap X EncodedType.bool
      (fun p : cnfFiniteEvalAcc × I.Carrier =>
        Karp21.Clique.boolAndPair
          (p.1.2, clauseFiniteEvalBool (p.1.1, p.2.2.2))) := by
    have hComp := TMPolyTimeMap.comp Karp21.Clique.boolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hClauseBranch : TMPolyTimeMap X A
      (fun p : cnfFiniteEvalAcc × I.Carrier =>
        (p.1.1,
          Karp21.Clique.boolAndPair
            (p.1.2, clauseFiniteEvalBool (p.1.1, p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hAccBits hAndValue
  have hTagged : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : cnfFiniteEvalAcc × I.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :=
    Karp21.Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : cnfFiniteEvalAcc × I.Carrier => (p.2.2.1, true))
      (fTrue := fun p : cnfFiniteEvalAcc × I.Carrier =>
        (p.1.1,
          Karp21.Clique.boolAndPair
            (p.1.2, clauseFiniteEvalBool (p.1.1, p.2.2.2))))
      hInitBranch hClauseBranch
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext p
  rcases p with ⟨⟨bits, value⟩, ⟨tag, instrBits, clause⟩⟩
  cases tag <;> rfl

theorem cnfFiniteEvalInitAcc_bound
    (xs : List cnfFiniteEvalInstructionEncodedType.Carrier) :
    cnfFiniteEvalAccEncodedType.inputSize cnfFiniteEvalInitAcc ≤
      (Polynomial.C 10).eval (cnfFiniteEvalInstructionListEncodedType.inputSize xs) := by
  have hNil :
      (EncodedType.list EncodedType.bool).inputSize ([] : List Bool) = 0 :=
    EncodedType.inputSize_list_nil EncodedType.bool
  simp [cnfFiniteEvalInitAcc, cnfFiniteEvalAccEncodedType, finiteAssignmentCertEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_bool, hNil]

theorem cnfFiniteEvalStep_growth
    (source : List cnfFiniteEvalInstructionEncodedType.Carrier)
    (acc : cnfFiniteEvalAccEncodedType.Carrier)
    (instr : cnfFiniteEvalInstructionEncodedType.Carrier)
    (hInstr :
      cnfFiniteEvalInstructionEncodedType.inputSize instr ≤
        cnfFiniteEvalInstructionListEncodedType.inputSize source) :
    cnfFiniteEvalAccEncodedType.inputSize (cnfFiniteEvalStep (acc, instr)) ≤
      cnfFiniteEvalAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (cnfFiniteEvalInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨accBits, accValue⟩
  rcases instr with ⟨tag, instrBits, clause⟩
  change Bool at tag accValue
  cases tag
  · have hRaw := hInstr
    simp [cnfFiniteEvalStep, cnfFiniteEvalInstructionEncodedType,
      cnfFiniteEvalAccEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_bool,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hRaw ⊢
    omega
  · simp [cnfFiniteEvalStep, cnfFiniteEvalAccEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem cnfFiniteEvalFold_tm_polytime :
    TMPolyTimeMap
      cnfFiniteEvalInstructionListEncodedType
      cnfFiniteEvalAccEncodedType
      (fun xs : List cnfFiniteEvalInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => cnfFiniteEvalStep (acc, instr))
          cnfFiniteEvalInitAcc) := by
  rcases cnfFiniteEvalStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      cnfFiniteEvalInstructionEncodedType cnfFiniteEvalAccEncodedType
      cnfFiniteEvalStep cnfFiniteEvalInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact cnfFiniteEvalInitAcc_bound xs
  · intro source acc instr hInstr
    exact cnfFiniteEvalStep_growth source acc instr hInstr

theorem cnfFiniteEvalFromInstructions_tm_polytime :
    TMPolyTimeMap
      cnfFiniteEvalInstructionListEncodedType
      EncodedType.bool
      cnfFiniteEvalFromInstructions := by
  have hFold := cnfFiniteEvalFold_tm_polytime
  have hValue := TMPolyTimeMap.snd finiteAssignmentCertEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hValue hFold
  simpa [Function.comp, cnfFiniteEvalFromInstructions, cnfFiniteEvalAccEncodedType]
    using hComp

theorem cnfFiniteEvalBool_tm_polytime :
    TMPolyTimeMap
      cnfFiniteEvalInputEncodedType
      EncodedType.bool
      cnfFiniteEvalBool := by
  have hComp :=
    TMPolyTimeMap.comp cnfFiniteEvalFromInstructions_tm_polytime
      cnfFiniteEvalInstructions_tm_polytime
  simpa [Function.comp, cnfFiniteEvalBool] using hComp

/-! ### Structured bundled 3SAT verifier surface -/

/-- Executable finite-certificate verifier over the faithful structured 3SAT syntax. -/
def threeSATStructuredFiniteVerify (φ : ThreeCNF) (bits : List Bool) : Bool :=
  cnfFiniteEvalBool (bits, φ.clauses)

theorem threeSATStructuredFiniteVerify_eq_true_iff (φ : ThreeCNF) (bits : List Bool) :
    threeSATStructuredFiniteVerify φ bits = true ↔
      φ.Satisfies (finiteAssignment bits) := by
  simpa [threeSATStructuredFiniteVerify, ThreeCNF.Satisfies] using
    cnfFiniteEvalBool_eq_true_iff bits φ.clauses

theorem threeCNFStructuredClauses_tm_polytime :
    TMPolyTimeMap
      Karp21.threeCNFStructuredEncodedType
      Karp21.cnfStructuredEncodedType
      (fun φ : ThreeCNF => φ.clauses) :=
  TMPolyTimeMap.of_encodingEquiv
    Karp21.threeCNFStructuredEncodedType Karp21.cnfStructuredEncodedType
    (fun φ : ThreeCNF => φ.clauses)
    (Equiv.refl Karp21.cnfStructuredEncodedType.Symbol)
    (by
      intro φ
      change
        Karp21.cnfStructuredEncodedType.encode φ.clauses =
          (Karp21.cnfStructuredEncodedType.encode φ.clauses).map id
      simp)

theorem threeSATStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod Karp21.threeCNFStructuredEncodedType finiteAssignmentCertEncodedType)
      EncodedType.bool
      (fun p : ThreeCNF × List Bool => threeSATStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod Karp21.threeCNFStructuredEncodedType finiteAssignmentCertEncodedType
  have hFormula : TMPolyTimeMap X Karp21.threeCNFStructuredEncodedType
      (fun p : ThreeCNF × List Bool => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst Karp21.threeCNFStructuredEncodedType finiteAssignmentCertEncodedType
  have hBits : TMPolyTimeMap X finiteAssignmentCertEncodedType
      (fun p : ThreeCNF × List Bool => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd Karp21.threeCNFStructuredEncodedType finiteAssignmentCertEncodedType
  have hClauses : TMPolyTimeMap X Karp21.cnfStructuredEncodedType
      (fun p : ThreeCNF × List Bool => p.1.clauses) := by
    have hComp := TMPolyTimeMap.comp threeCNFStructuredClauses_tm_polytime hFormula
    simpa [Function.comp, X] using hComp
  have hInput : TMPolyTimeMap X cnfFiniteEvalInputEncodedType
      (fun p : ThreeCNF × List Bool => (p.2, p.1.clauses)) :=
    TMPolyTimeMap.prod_mk hBits hClauses
  have hComp := TMPolyTimeMap.comp cnfFiniteEvalBool_tm_polytime hInput
  simpa [Function.comp, threeSATStructuredFiniteVerify, cnfFiniteEvalInputEncodedType, X]
    using hComp

theorem assignmentPrefix_inputSize_le_threeCNFStructured (φ : ThreeCNF) (a : Assignment) :
    finiteAssignmentCertEncodedType.inputSize
        (assignmentPrefix (CNF.varBound φ.clauses) a) ≤
      2 * Karp21.threeCNFStructuredEncodedType.inputSize φ := by
  rw [assignmentPrefix_inputSize]
  have hBound : CNF.varBound φ.clauses ≤ Karp21.threeCNFStructuredEncodedType.inputSize φ := by
    simpa [Karp21.threeCNFStructuredEncodedType, EncodedType.inputSize] using
      Karp21.cnfVarBound_le_cnfStructured_inputSize φ.clauses
  omega

/-- Direct finite-certificate TM verifier for faithful structured 3SAT. -/
noncomputable def threeSATStructuredFiniteTMVerifier :
    TMVerifier Karp21.threeSATStructuredDecisionProblem where
  Cert := finiteAssignmentCertEncodedType
  verify := threeSATStructuredFiniteVerify
  verifier_polytime := threeSATStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 2, 0, ?_⟩
    intro φ hSat
    rcases hSat with ⟨a, ha⟩
    refine ⟨assignmentPrefix (CNF.varBound φ.clauses) a, ?_, ?_⟩
    · simpa using assignmentPrefix_inputSize_le_threeCNFStructured φ a
    · exact (threeSATStructuredFiniteVerify_eq_true_iff φ _).2
        (ThreeCNF.satisfies_finiteAssignment_prefix φ a ha)
  sound := by
    intro φ bits hVerify
    exact ⟨finiteAssignment bits,
      (threeSATStructuredFiniteVerify_eq_true_iff φ bits).1 hVerify⟩

theorem threeSATStructuredFinite_TMInNP :
    TMInNP Karp21.threeSATStructuredDecisionProblem :=
  TMInNP.intro threeSATStructuredFiniteTMVerifier

end SAT
end ComplexityReduction
