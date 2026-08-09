import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part6

namespace ComplexityReduction
namespace Karp21
namespace Clique

/-! #### Structured 3CNF to indexed literal occurrences -/

def literalOccurrenceTupleToOccurrence
    (p : literalOccurrenceTupleStructuredEncodedType.Carrier) :
    LiteralOccurrence :=
  { clause := p.1, slot := p.2.1, lit := p.2.2 }

noncomputable def literalOccurrenceTupleToOccurrenceTMBackedMap :
    TMBackedCostedMap
      literalOccurrenceTupleStructuredEncodedType
      literalOccurrenceStructuredEncodedType
      literalOccurrenceTupleToOccurrence :=
  TMBackedCostedMap.ofEncodingEquiv
    literalOccurrenceTupleStructuredEncodedType
    literalOccurrenceStructuredEncodedType
    literalOccurrenceTupleToOccurrence
    (Equiv.refl _)
    (by
      intro p
      rcases p with ⟨clause, slot, lit⟩
      change
        literalOccurrenceTupleStructuredEncodedType.encode (clause, (slot, lit)) =
          (literalOccurrenceTupleStructuredEncodedType.encode (clause, (slot, lit))).map id
      rw [List.map_id])

def cliqueIndexedClauseOccurrenceAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)))

def cliqueIndexedClauseOccurrenceStepInputEncodedType : EncodedType :=
  EncodedType.prod cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType

def cliqueIndexedClauseOccurrenceStep
    (p : cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.Carrier :=
  let clauseIdx : Nat := p.1.1
  let slot : Nat := p.1.2.1
  let next : Nat := p.1.2.2.1
  let out : List indexedLiteralOccurrenceEncodedType.Carrier := p.1.2.2.2
  let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
    (next, { clause := clauseIdx, slot := slot, lit := p.2 })
  (clauseIdx, (Nat.succ slot, (Nat.succ next, List.append out [occurrence])))

def cliqueIndexedClauseOccurrenceFold
    (clauseIdx slot next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (c : SAT.Clause) :
    cliqueIndexedClauseOccurrenceAccEncodedType.Carrier :=
  c.foldl
    (fun acc lit => cliqueIndexedClauseOccurrenceStep (acc, lit))
    (clauseIdx, (slot, (next, out)))

theorem indexedLiteralOccurrencesFrom_append
    (next : Nat) (xs ys : List LiteralOccurrence) :
    indexedLiteralOccurrencesFrom next (xs ++ ys) =
      indexedLiteralOccurrencesFrom next xs ++
        indexedLiteralOccurrencesFrom (next + xs.length) ys := by
  induction xs generalizing next with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [indexedLiteralOccurrencesFrom, ih, Nat.add_comm,
        Nat.add_left_comm]

theorem cliqueIndexedClauseOccurrenceFold_clause
    (clauseIdx slot next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (c : SAT.Clause) :
    (cliqueIndexedClauseOccurrenceFold clauseIdx slot next out c).1 = clauseIdx := by
  induction c generalizing slot next out with
  | nil =>
      change clauseIdx = clauseIdx
      rfl
  | cons lit rest ih =>
      let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
        (next, { clause := clauseIdx, slot := slot, lit := lit })
      simpa [cliqueIndexedClauseOccurrenceFold, cliqueIndexedClauseOccurrenceStep,
        occurrence] using
        ih (slot + 1) (next + 1) (out ++ [occurrence])

theorem cliqueIndexedClauseOccurrenceFold_slot
    (clauseIdx slot next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (c : SAT.Clause) :
    (cliqueIndexedClauseOccurrenceFold clauseIdx slot next out c).2.1 =
      slot + c.length := by
  induction c generalizing slot next out with
  | nil =>
      rfl
  | cons lit rest ih =>
      let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
        (next, { clause := clauseIdx, slot := slot, lit := lit })
      simpa [cliqueIndexedClauseOccurrenceFold, cliqueIndexedClauseOccurrenceStep,
        occurrence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (slot + 1) (next + 1) (out ++ [occurrence])

theorem cliqueIndexedClauseOccurrenceFold_next
    (clauseIdx slot next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (c : SAT.Clause) :
    (cliqueIndexedClauseOccurrenceFold clauseIdx slot next out c).2.2.1 =
      next + c.length := by
  induction c generalizing slot next out with
  | nil =>
      rfl
  | cons lit rest ih =>
      let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
        (next, { clause := clauseIdx, slot := slot, lit := lit })
      simpa [cliqueIndexedClauseOccurrenceFold, cliqueIndexedClauseOccurrenceStep,
        occurrence, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (slot + 1) (next + 1) (out ++ [occurrence])

theorem cliqueIndexedClauseOccurrenceFold_out
    (clauseIdx slot next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (c : SAT.Clause) :
    (cliqueIndexedClauseOccurrenceFold clauseIdx slot next out c).2.2.2 =
      out ++ indexedLiteralOccurrencesFrom next
        (clauseOccurrencesFrom clauseIdx slot c) := by
  induction c generalizing slot next out with
  | nil =>
      change out = out ++ indexedLiteralOccurrencesFrom next
        (clauseOccurrencesFrom clauseIdx slot [])
      simp [indexedLiteralOccurrencesFrom, clauseOccurrencesFrom]
  | cons lit rest ih =>
      let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
        (next, { clause := clauseIdx, slot := slot, lit := lit })
      simpa [cliqueIndexedClauseOccurrenceFold, cliqueIndexedClauseOccurrenceStep,
        indexedLiteralOccurrencesFrom, clauseOccurrencesFrom, occurrence,
        List.append_assoc] using
        ih (slot + 1) (next + 1) (out ++ [occurrence])

theorem cliqueIndexedClauseOccurrenceStep_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceStepInputEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceStep := by
  let X := cliqueIndexedClauseOccurrenceStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueIndexedClauseOccurrenceStepInputEncodedType] using
      TMPolyTimeMap.fst cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType
  have hLit :
      TMPolyTimeMap X literalStructuredEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueIndexedClauseOccurrenceStepInputEncodedType] using
      TMPolyTimeMap.snd cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType
  have hClause :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, cliqueIndexedClauseOccurrenceAccEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, cliqueIndexedClauseOccurrenceAccEncodedType, X] using hComp
  have hSlot :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hNext :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hSlotSucc :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => Nat.succ (p.1.2.1 : Nat)) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hSlot
    simpa [Function.comp] using hComp
  have hNextSucc :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => Nat.succ (p.1.2.2.1 : Nat)) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    simpa [Function.comp] using hComp
  have hOccurrenceTuple :
      TMPolyTimeMap X literalOccurrenceTupleStructuredEncodedType
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2))) := by
    have hSlotLit :
        TMPolyTimeMap X
          (EncodedType.prod EncodedType.nat literalStructuredEncodedType)
          (fun p : X.Carrier => (p.1.2.1, p.2)) :=
      TMPolyTimeMap.prod_mk hSlot hLit
    exact TMPolyTimeMap.prod_mk hClause hSlotLit
  have hOccurrence :
      TMPolyTimeMap X literalOccurrenceStructuredEncodedType
        (fun p : X.Carrier =>
          { clause := p.1.1, slot := p.1.2.1, lit := p.2 }) := by
    have hComp :=
      TMPolyTimeMap.comp literalOccurrenceTupleToOccurrenceTMBackedMap.tm_polytime
        hOccurrenceTuple
    simpa [Function.comp, literalOccurrenceTupleToOccurrence] using hComp
  have hIndexed :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier =>
          (p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })) :=
    TMPolyTimeMap.prod_mk hNext hOccurrence
  have hSingleton :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier =>
          [(p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton indexedLiteralOccurrenceEncodedType) hIndexed
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod
          (EncodedType.list indexedLiteralOccurrenceEncodedType)
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier =>
          (p.1.2.2.2,
            [(p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hOutAppend :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier =>
          List.append
            (p.1.2.2.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
            [(p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })]) := by
    have hComp :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_append indexedLiteralOccurrenceEncodedType)
        hAppendInput
    simpa [Function.comp, X] using hComp
  have hNextOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier =>
          (Nat.succ (p.1.2.2.1 : Nat),
            List.append
              (p.1.2.2.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
              [(p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })])) :=
    TMPolyTimeMap.prod_mk hNextSucc hOutAppend
  have hSlotNextOut :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.list indexedLiteralOccurrenceEncodedType)))
        (fun p : X.Carrier =>
          (Nat.succ (p.1.2.1 : Nat),
            (Nat.succ (p.1.2.2.1 : Nat),
              List.append
                (p.1.2.2.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
                [(p.1.2.2.1, { clause := p.1.1, slot := p.1.2.1, lit := p.2 })]))) :=
    TMPolyTimeMap.prod_mk hSlotSucc hNextOut
  have hOutAcc :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier =>
          (p.1.1,
            (Nat.succ (p.1.2.1 : Nat),
              (Nat.succ (p.1.2.2.1 : Nat),
                List.append
                  (p.1.2.2.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
                  [(p.1.2.2.1,
                    { clause := p.1.1, slot := p.1.2.1, lit := p.2 })])))) :=
    TMPolyTimeMap.prod_mk hClause hSlotNextOut
  simpa [cliqueIndexedClauseOccurrenceStep, X,
    cliqueIndexedClauseOccurrenceAccEncodedType] using hOutAcc

theorem cliqueIndexedClauseOccurrenceStep_inputSize_le
    (p : cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceStep p) ≤
      20 * cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize p ^ 2 + 100 := by
  rcases p with ⟨⟨clauseIdx, slot, next, out⟩, lit⟩
  change Nat at clauseIdx
  change Nat at slot
  change Nat at next
  let occurrence : indexedLiteralOccurrenceEncodedType.Carrier :=
    (next, { clause := clauseIdx, slot := slot, lit := lit })
  have hAppend :=
    encodedList_inputSize_append indexedLiteralOccurrenceEncodedType out [occurrence]
  have hAppend' :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (List.append out
            [(next, { clause := clauseIdx, slot := slot, lit := lit })]) =
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
            [(next, { clause := clauseIdx, slot := slot, lit := lit })] := by
    simpa [occurrence] using hAppend
  have hOccLe :
      indexedLiteralOccurrenceEncodedType.inputSize occurrence ≤
        cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize
          (((clauseIdx, (slot, (next, out))), lit) :
            cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier) := by
    simp [occurrence, cliqueIndexedClauseOccurrenceStepInputEncodedType,
      cliqueIndexedClauseOccurrenceAccEncodedType, indexedLiteralOccurrenceEncodedType,
      literalOccurrenceStructuredEncodedType, literalOccurrenceToTuple,
      literalOccurrenceTupleStructuredEncodedType, literalStructuredEncodedType,
      EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
    omega
  let N :=
    cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize
      (((clauseIdx, (slot, (next, out))), lit) :
        cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier)
  have hOutLe :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out ≤ N := by
    simp [N, cliqueIndexedClauseOccurrenceStepInputEncodedType,
      cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod]
    omega
  have hVarsLe :
      clauseIdx + 1 + (slot + 1 + 1 + (next + 1 + 1)) ≤ N + 6 := by
    simp [N, cliqueIndexedClauseOccurrenceStepInputEncodedType,
      cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat]
    omega
  simp only [cliqueIndexedClauseOccurrenceStep, cliqueIndexedClauseOccurrenceAccEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  rw [hAppend']
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
  have hOccLe' :
      indexedLiteralOccurrenceEncodedType.inputSize
          (next, { clause := clauseIdx, slot := slot, lit := lit }) ≤ N := by
    simpa [occurrence, N] using hOccLe
  have hLinear :
      clauseIdx + 1 + 1 +
          (slot.succ + 1 + 1 +
            (next.succ + 1 + 1 +
              ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out +
                (indexedLiteralOccurrenceEncodedType.inputSize
                    (next, { clause := clauseIdx, slot := slot, lit := lit }) +
                  1 + 0)))) ≤
        N + 10 + (N + (N + 1)) := by
    omega
  have hPoly : N + 10 + (N + (N + 1)) ≤ 20 * N ^ 2 + 100 := by
    nlinarith [sq_nonneg (N : Int)]
  exact hLinear.trans hPoly

theorem cliqueIndexedClauseOccurrenceStep_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize p)
      (fun acc : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize acc)
      cliqueIndexedClauseOccurrenceStep := by
  refine PolynomialSizeBound.intro_with 2 20 100 ?_
  intro p
  exact cliqueIndexedClauseOccurrenceStep_inputSize_le p

noncomputable def cliqueIndexedClauseOccurrenceStepTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedClauseOccurrenceStepInputEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceStep where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueIndexedClauseOccurrenceStep_polynomialSizeBound
  tm_polytime := cliqueIndexedClauseOccurrenceStep_tm_polytime

def defaultCliqueLiteral : SAT.Literal :=
  SAT.Literal.positive 0

def cliqueIndexedClauseOccurrenceFoldInit :
    cliqueIndexedClauseOccurrenceAccEncodedType.Carrier :=
  ((0 : Nat), ((0 : Nat), ((0 : Nat), [])))

def cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType

def cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType

def cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType : EncodedType :=
  EncodedType.prod cliqueIndexedClauseOccurrenceAccEncodedType
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType

def cliqueIndexedClauseOccurrenceRunnerInputEncodedType : EncodedType :=
  EncodedType.prod cliqueIndexedClauseOccurrenceAccEncodedType clauseStructuredEncodedType

def cliqueIndexedClauseOccurrenceRunnerInitInstruction
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier :=
  (false, (init, defaultCliqueLiteral))

def cliqueIndexedClauseOccurrenceRunnerLiteralInstruction
    (lit : literalStructuredEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier :=
  (true, (cliqueIndexedClauseOccurrenceFoldInit, lit))

def cliqueIndexedClauseOccurrenceRunnerInstructions
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    List cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier :=
  [cliqueIndexedClauseOccurrenceRunnerInitInstruction init] ++
    c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction

def cliqueIndexedClauseOccurrenceRunnerStep
    (p : cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.Carrier :=
  match p.2.1 with
  | true => cliqueIndexedClauseOccurrenceStep (p.1, p.2.2.2)
  | false => p.2.2.1

theorem cliqueIndexedClauseOccurrenceRunnerInitInstruction_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
      cliqueIndexedClauseOccurrenceRunnerInitInstruction := by
  have hPayload :
      TMPolyTimeMap
        cliqueIndexedClauseOccurrenceAccEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType
        (fun init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier =>
          (init, defaultCliqueLiteral)) :=
    TMPolyTimeMap.prod_id_const cliqueIndexedClauseOccurrenceAccEncodedType
      literalStructuredEncodedType defaultCliqueLiteral
  have hTag :
      TMPolyTimeMap
        cliqueIndexedClauseOccurrenceAccEncodedType
        EncodedType.bool
        (fun _ : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier => false) :=
    TMPolyTimeMap.const cliqueIndexedClauseOccurrenceAccEncodedType EncodedType.bool false
  have hInstr :
      TMPolyTimeMap
        cliqueIndexedClauseOccurrenceAccEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
        (fun init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier =>
          (false, (init, defaultCliqueLiteral))) :=
    TMPolyTimeMap.prod_mk hTag hPayload
  simpa [cliqueIndexedClauseOccurrenceRunnerInitInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType] using hInstr

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_tm_polytime :
    TMPolyTimeMap
      literalStructuredEncodedType
      cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
      cliqueIndexedClauseOccurrenceRunnerLiteralInstruction := by
  have hPayload :
      TMPolyTimeMap
        literalStructuredEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType
        (fun lit : literalStructuredEncodedType.Carrier =>
          (cliqueIndexedClauseOccurrenceFoldInit, lit)) :=
    TMPolyTimeMap.prod_left_const_id literalStructuredEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType cliqueIndexedClauseOccurrenceFoldInit
  have hTag :
      TMPolyTimeMap
        literalStructuredEncodedType
        EncodedType.bool
        (fun _ : literalStructuredEncodedType.Carrier => true) :=
    TMPolyTimeMap.const literalStructuredEncodedType EncodedType.bool true
  have hInstr :
      TMPolyTimeMap
        literalStructuredEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
        (fun lit : literalStructuredEncodedType.Carrier =>
          (true, (cliqueIndexedClauseOccurrenceFoldInit, lit))) :=
    TMPolyTimeMap.prod_mk hTag hPayload
  simpa [cliqueIndexedClauseOccurrenceRunnerLiteralInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType] using hInstr

theorem cliqueIndexedClauseOccurrenceRunnerInstructions_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerInputEncodedType
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType)
      (fun p : cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2) := by
  let X := cliqueIndexedClauseOccurrenceRunnerInputEncodedType
  let Instr := cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
  have hInit :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueIndexedClauseOccurrenceRunnerInputEncodedType] using
      TMPolyTimeMap.fst cliqueIndexedClauseOccurrenceAccEncodedType clauseStructuredEncodedType
  have hClause :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueIndexedClauseOccurrenceRunnerInputEncodedType] using
      TMPolyTimeMap.snd cliqueIndexedClauseOccurrenceAccEncodedType clauseStructuredEncodedType
  have hInitInstr :
      TMPolyTimeMap X Instr
        (fun p : X.Carrier => cliqueIndexedClauseOccurrenceRunnerInitInstruction p.1) := by
    have hComp :=
      TMPolyTimeMap.comp cliqueIndexedClauseOccurrenceRunnerInitInstruction_tm_polytime hInit
    simpa [Function.comp, Instr, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier => [cliqueIndexedClauseOccurrenceRunnerInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Instr) hInitInstr
    simpa [Function.comp, Instr, X] using hComp
  have hLiteralInstrs :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier =>
          p.2.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
    have hMap :=
      TMPolyTimeMap.list_map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hClause
    simpa [Function.comp, Instr, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list Instr) (EncodedType.list Instr))
        (fun p : X.Carrier =>
          ([cliqueIndexedClauseOccurrenceRunnerInitInstruction p.1],
            p.2.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hLiteralInstrs
  have hAppend :
      TMPolyTimeMap X (EncodedType.list Instr)
        (fun p : X.Carrier =>
          [cliqueIndexedClauseOccurrenceRunnerInitInstruction p.1] ++
            p.2.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Instr) hPair
    simpa [Function.comp, Instr, X] using hComp
  simpa [cliqueIndexedClauseOccurrenceRunnerInstructions, X, Instr] using hAppend

theorem cliqueIndexedClauseOccurrenceRunnerStep_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceRunnerStep := by
  let X := cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType] using
      TMPolyTimeMap.fst cliqueIndexedClauseOccurrenceAccEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType] using
      TMPolyTimeMap.snd cliqueIndexedClauseOccurrenceAccEncodedType
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
  have hTag :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => p.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.bool
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType, X]
      using hComp
  have hPayload :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType
        (fun p : X.Carrier => p.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.bool
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType, X]
      using hComp
  have hInitAcc :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => p.2.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType, X]
      using hComp
  have hLit :
      TMPolyTimeMap X literalStructuredEncodedType
        (fun p : X.Carrier => p.2.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd cliqueIndexedClauseOccurrenceAccEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType, X]
      using hComp
  have hStepInput :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceStepInputEncodedType
        (fun p : X.Carrier => (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hLit
  have hStep :
      TMPolyTimeMap X cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : X.Carrier => cliqueIndexedClauseOccurrenceStep (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp cliqueIndexedClauseOccurrenceStep_tm_polytime hStepInput
    simpa [Function.comp, cliqueIndexedClauseOccurrenceStepInputEncodedType, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        cliqueIndexedClauseOccurrenceAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => cliqueIndexedClauseOccurrenceStep (p.2.1, p.2.2.2.2)
          | false => p.2.2.2.1) :=
    boolProduct_dispatch_tm_polytime X cliqueIndexedClauseOccurrenceAccEncodedType
      (fFalse := fun p : X.Carrier => p.2.2.1)
      (fTrue := fun p : X.Carrier => cliqueIndexedClauseOccurrenceStep (p.1, p.2.2.2))
      (hFalse := hInitAcc) (hTrue := hStep)
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1

theorem cliqueIndexedClauseOccurrenceRunnerStep_inputSize_le
    (p : cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerStep p) ≤
      20 * cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.inputSize p ^ 2 + 100 := by
  let N := cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.inputSize p
  have hPoly : N ≤ 20 * N ^ 2 + 100 := by
    nlinarith [sq_nonneg (N : Int)]
  cases hTag : p.2.1
  · have hInit :
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize p.2.2.1 ≤ N := by
      simp [N, cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType,
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
        EncodedType.inputSize_prod]
      omega
    simpa [cliqueIndexedClauseOccurrenceRunnerStep, hTag, N] using hInit.trans hPoly
  · have hArg :
        cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize (p.1, p.2.2.2) ≤ N := by
      simp [N, cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType,
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
        cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
        cliqueIndexedClauseOccurrenceStepInputEncodedType, EncodedType.inputSize_prod]
      omega
    have hStep :=
      cliqueIndexedClauseOccurrenceStep_inputSize_le
        ((p.1, p.2.2.2) : cliqueIndexedClauseOccurrenceStepInputEncodedType.Carrier)
    have hMono :
        20 * cliqueIndexedClauseOccurrenceStepInputEncodedType.inputSize (p.1, p.2.2.2) ^ 2 +
            100 ≤
          20 * N ^ 2 + 100 := by
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hArg 2)) 100
    simpa [cliqueIndexedClauseOccurrenceRunnerStep, hTag, N] using hStep.trans hMono

theorem cliqueIndexedClauseOccurrenceRunnerStep_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType.inputSize p)
      (fun acc : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize acc)
      cliqueIndexedClauseOccurrenceRunnerStep := by
  refine PolynomialSizeBound.intro_with 2 20 100 ?_
  intro p
  exact cliqueIndexedClauseOccurrenceRunnerStep_inputSize_le p

noncomputable def cliqueIndexedClauseOccurrenceRunnerStepTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedClauseOccurrenceRunnerStepInputEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceRunnerStep where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      cliqueIndexedClauseOccurrenceRunnerStep_polynomialSizeBound
  tm_polytime := cliqueIndexedClauseOccurrenceRunnerStep_tm_polytime

@[simp] theorem cliqueIndexedClauseOccurrenceRunnerStep_init
    (acc init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerStep
        (acc, cliqueIndexedClauseOccurrenceRunnerInitInstruction init) = init := by
  rfl

@[simp] theorem cliqueIndexedClauseOccurrenceRunnerStep_literal
    (acc : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (lit : literalStructuredEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerStep
        (acc, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) =
      cliqueIndexedClauseOccurrenceStep (acc, lit) := by
  rfl

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_fold_eq
    (acc : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction).foldl
        (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
        acc =
      c.foldl
        (fun acc lit => cliqueIndexedClauseOccurrenceStep (acc, lit))
        acc := by
  induction c generalizing acc with
  | nil =>
      rfl
  | cons lit rest ih =>
      change
        List.foldl (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) acc
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
              rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) =
          List.foldl (fun acc lit => cliqueIndexedClauseOccurrenceStep (acc, lit))
            (cliqueIndexedClauseOccurrenceStep (acc, lit)) rest
      rw [List.foldl_cons]
      simpa using ih (cliqueIndexedClauseOccurrenceStep (acc, lit))

theorem cliqueIndexedClauseOccurrenceRunnerInstructions_fold_eq
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    (cliqueIndexedClauseOccurrenceRunnerInstructions init c).foldl
        (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
        cliqueIndexedClauseOccurrenceFoldInit =
      c.foldl
        (fun acc lit => cliqueIndexedClauseOccurrenceStep (acc, lit))
        init := by
  simp [cliqueIndexedClauseOccurrenceRunnerInstructions,
    cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_fold_eq]

def cliqueIndexedClauseOccurrenceRunnerFold
    (p : cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.Carrier :=
  (cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2).foldl
    (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
    cliqueIndexedClauseOccurrenceFoldInit

theorem cliqueIndexedClauseOccurrenceRunnerFold_eq
    (p : cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerFold p =
      cliqueIndexedClauseOccurrenceFold p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2 := by
  simpa [cliqueIndexedClauseOccurrenceRunnerFold, cliqueIndexedClauseOccurrenceFold] using
    cliqueIndexedClauseOccurrenceRunnerInstructions_fold_eq p.1 p.2

def cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType : EncodedType where
  Carrier := cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier
  Symbol := (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).Symbol
  finite_symbol := inferInstance
  encode := fun p =>
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).encode
      (cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2)

theorem cliqueIndexedClauseOccurrenceRunnerInitInstruction_inputSize_le
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerInitInstruction init) ≤
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init +
        literalStructuredEncodedType.inputSize defaultCliqueLiteral + 4 := by
  simp [cliqueIndexedClauseOccurrenceRunnerInitInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_inputSize_le
    (lit : literalStructuredEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) ≤
      literalStructuredEncodedType.inputSize lit +
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit + 4 := by
  simp [cliqueIndexedClauseOccurrenceRunnerLiteralInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_inputSize_le
    (c : SAT.Clause) :
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) ≤
      (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit + 5) *
        clauseStructuredEncodedType.inputSize c := by
  induction c with
  | nil =>
      change
        (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            ([] : List cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier) ≤
          (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5) *
            clauseStructuredEncodedType.inputSize ([] : SAT.Clause)
      rw [EncodedType.inputSize_list_nil]
      exact Nat.zero_le _
  | cons lit rest ih =>
      change
        (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
              rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) ≤
          (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5) *
            (EncodedType.list literalStructuredEncodedType).inputSize (lit :: rest)
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have hLit := cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_inputSize_le lit
      have hKpos :
          1 ≤ cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5 := by
        omega
      have hKpos' :
          0 < cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5 := by
        omega
      have hLitScale :
          literalStructuredEncodedType.inputSize lit ≤
            (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                cliqueIndexedClauseOccurrenceFoldInit + 5) *
              literalStructuredEncodedType.inputSize lit := by
        simpa [Nat.mul_comm] using
          Nat.le_mul_of_pos_right (literalStructuredEncodedType.inputSize lit) hKpos'
      have hHead :
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
              (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) + 1 ≤
            (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                cliqueIndexedClauseOccurrenceFoldInit + 5) *
              (literalStructuredEncodedType.inputSize lit + 1) := by
        calc
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
              (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) + 1
              ≤ (literalStructuredEncodedType.inputSize lit +
                  cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                    cliqueIndexedClauseOccurrenceFoldInit + 4) + 1 :=
                Nat.add_le_add_right hLit 1
          _ = literalStructuredEncodedType.inputSize lit +
                (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                  cliqueIndexedClauseOccurrenceFoldInit + 5) := by
                omega
          _ ≤ (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                  cliqueIndexedClauseOccurrenceFoldInit + 5) *
                literalStructuredEncodedType.inputSize lit +
              (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                cliqueIndexedClauseOccurrenceFoldInit + 5) :=
                Nat.add_le_add_right hLitScale
                  (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                    cliqueIndexedClauseOccurrenceFoldInit + 5)
          _ = (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                cliqueIndexedClauseOccurrenceFoldInit + 5) *
              (literalStructuredEncodedType.inputSize lit + 1) := by
                ring
      calc
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) + 1 +
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.list.inputSize
            (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction rest)
            ≤ (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
                cliqueIndexedClauseOccurrenceFoldInit + 5) *
              (literalStructuredEncodedType.inputSize lit + 1) +
            (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5) *
              literalStructuredEncodedType.list.inputSize rest :=
              Nat.add_le_add hHead ih
        _ = (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              cliqueIndexedClauseOccurrenceFoldInit + 5) *
            (literalStructuredEncodedType.inputSize lit + 1 +
              literalStructuredEncodedType.list.inputSize rest) := by
              ring

theorem cliqueIndexedClauseOccurrenceRunnerInstructionsImage_linearSizeBound :
    LinearSizeBound
      (fun p : cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerInputEncodedType.inputSize p)
      (fun p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize p)
      id := by
  let K :=
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize cliqueIndexedClauseOccurrenceFoldInit +
      literalStructuredEncodedType.inputSize defaultCliqueLiteral + 10
  refine LinearSizeBound.intro_with K K ?_
  intro p
  rcases p with ⟨init, c⟩
  have hInit := cliqueIndexedClauseOccurrenceRunnerInitInstruction_inputSize_le init
  have hLits := cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_inputSize_le c
  have hK_lits :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit + 5 ≤ K := by
    dsimp [K]
    omega
  have hK_default :
      literalStructuredEncodedType.inputSize defaultCliqueLiteral + 5 ≤ K := by
    dsimp [K]
    omega
  have hK_pos : 1 ≤ K := by
    dsimp [K]
    omega
  have hInitSize :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤
        K * cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init := by
    simpa using
      Nat.mul_le_mul_right (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init) hK_pos
  have hLitSize :
      (cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit + 5) *
          clauseStructuredEncodedType.inputSize c ≤
        K * clauseStructuredEncodedType.inputSize c := by
    exact Nat.mul_le_mul_right _ hK_lits
  change
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (cliqueIndexedClauseOccurrenceRunnerInstructions init c) ≤
      K *
          (cliqueIndexedClauseOccurrenceRunnerInputEncodedType.inputSize
            ((init, c) : cliqueIndexedClauseOccurrenceRunnerInputEncodedType.Carrier)) + K
  simp [cliqueIndexedClauseOccurrenceRunnerInstructions,
    cliqueIndexedClauseOccurrenceRunnerInputEncodedType, EncodedType.inputSize_prod]
  nlinarith

theorem cliqueIndexedClauseOccurrenceRunnerInstructionsImage_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerInputEncodedType
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
      id := by
  rcases cliqueIndexedClauseOccurrenceRunnerInstructions_tm_polytime with ⟨hInstr⟩
  refine ⟨?_⟩
  exact
    { tm := hInstr.tm
      inputAlphabet := hInstr.inputAlphabet
      outputAlphabet := hInstr.outputAlphabet
      time := hInstr.time
      outputsFun := by
        intro p
        simpa [cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType] using
          hInstr.outputsFun p }

noncomputable def cliqueIndexedClauseOccurrenceRunnerInstructionsImageTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedClauseOccurrenceRunnerInputEncodedType
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
      id where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      cliqueIndexedClauseOccurrenceRunnerInstructionsImage_linearSizeBound
  tm_polytime := cliqueIndexedClauseOccurrenceRunnerInstructionsImage_tm_polytime

end Clique
end Karp21
end ComplexityReduction
