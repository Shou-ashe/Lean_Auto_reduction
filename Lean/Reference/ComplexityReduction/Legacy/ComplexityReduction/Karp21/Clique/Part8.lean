import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part7

namespace ComplexityReduction
namespace Karp21
namespace Clique

def cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType : EncodedType where
  Carrier := cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier
  Symbol := cliqueIndexedClauseOccurrenceAccEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun p =>
    cliqueIndexedClauseOccurrenceAccEncodedType.encode
      (cliqueIndexedClauseOccurrenceRunnerFold p)

theorem cliqueIndexedClauseOccurrenceRunnerInstructionsFromImage_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType)
      (fun p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2) :=
  TMPolyTimeMap.of_encodingEquiv
    cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType)
    (fun p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier =>
      cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2)
    (Equiv.refl _)
    (by
      intro p
      change
        (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).encode
            (cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2) =
          (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.encode p).map id
      simp [cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType])

theorem cliqueIndexedClauseOccurrenceRunnerFoldFromImage_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceRunnerFold :=
  TMPolyTimeMap.of_encodingEquiv
    cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
    cliqueIndexedClauseOccurrenceAccEncodedType
    cliqueIndexedClauseOccurrenceRunnerFold
    (Equiv.refl _)
    (by
      intro p
      change cliqueIndexedClauseOccurrenceAccEncodedType.encode
          (cliqueIndexedClauseOccurrenceRunnerFold p) =
        (cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.encode p).map id
      simp [cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType])

noncomputable def cliqueIndexedClauseOccurrenceRunnerFoldFromImageTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
      cliqueIndexedClauseOccurrenceAccEncodedType
      cliqueIndexedClauseOccurrenceRunnerFold :=
  TMBackedCostedMap.ofEncodingEquiv
    cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
    cliqueIndexedClauseOccurrenceAccEncodedType
    cliqueIndexedClauseOccurrenceRunnerFold
    (Equiv.refl _)
    (by
      intro p
      change cliqueIndexedClauseOccurrenceAccEncodedType.encode
          (cliqueIndexedClauseOccurrenceRunnerFold p) =
        (cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.encode p).map id
      simp [cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType])

theorem cliqueIndexedClauseOccurrenceRunnerInitInstruction_init_inputSize_le
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤
      cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerInitInstruction init) := by
  simp [cliqueIndexedClauseOccurrenceRunnerInitInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_lit_inputSize_le
    (lit : literalStructuredEncodedType.Carrier) :
    literalStructuredEncodedType.inputSize lit ≤
      cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) := by
  simp [cliqueIndexedClauseOccurrenceRunnerLiteralInstruction,
    cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType,
    cliqueIndexedClauseOccurrenceRunnerInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_inputSize_ge_clause
    (c : SAT.Clause) :
    clauseStructuredEncodedType.inputSize c ≤
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
  induction c with
  | nil =>
      change (EncodedType.list literalStructuredEncodedType).inputSize ([] : SAT.Clause) ≤
        (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
          ([] : List cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier)
      change 0 ≤ 0
      rfl
  | cons lit rest ih =>
      change
        (EncodedType.list literalStructuredEncodedType).inputSize (lit :: rest) ≤
          (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
              rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      have hLit := cliqueIndexedClauseOccurrenceRunnerLiteralInstruction_lit_inputSize_le lit
      have hRest :
          (EncodedType.list literalStructuredEncodedType).inputSize rest ≤
            (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
              (rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
        simpa [clauseStructuredEncodedType] using ih
      omega

theorem cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_init
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (cliqueIndexedClauseOccurrenceRunnerInstructions init c) := by
  have hInit := cliqueIndexedClauseOccurrenceRunnerInitInstruction_init_inputSize_le init
  simp [cliqueIndexedClauseOccurrenceRunnerInstructions, EncodedType.inputSize_list_cons]
    at hInit ⊢
  omega

theorem cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_clause
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    clauseStructuredEncodedType.inputSize c ≤
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (cliqueIndexedClauseOccurrenceRunnerInstructions init c) := by
  have hClause := cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_inputSize_ge_clause c
  simp [cliqueIndexedClauseOccurrenceRunnerInstructions, EncodedType.inputSize_list_cons]
  omega

theorem cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_clause_length
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) :
    c.length ≤
      (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
        (cliqueIndexedClauseOccurrenceRunnerInstructions init c) := by
  have hLen := encodedList_length_le_inputSize literalStructuredEncodedType c
  have hClause := cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_clause init c
  have hClause' :
      (EncodedType.list literalStructuredEncodedType).inputSize c ≤
        (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
          (cliqueIndexedClauseOccurrenceRunnerInstructions init c) := by
    simpa [clauseStructuredEncodedType] using hClause
  exact hLen.trans hClause'

theorem indexedClauseOccurrence_inputSize_le
    (clauseIdx slot next : Nat) (lit : SAT.Literal) :
    indexedLiteralOccurrenceEncodedType.inputSize
        (next, { clause := clauseIdx, slot := slot, lit := lit }) ≤
      clauseIdx + slot + next + literalStructuredEncodedType.inputSize lit + 10 := by
  simp [indexedLiteralOccurrenceEncodedType, literalOccurrenceStructuredEncodedType,
    literalOccurrenceToTuple, literalOccurrenceTupleStructuredEncodedType,
    literalStructuredEncodedType, literalTupleStructuredEncodedType,
    EncodedType.inputSize, EncodedType.prod, EncodedType.nat, EncodedType.bool]
  omega

theorem indexedClauseOccurrencesFrom_inputSize_le
    (clauseIdx slot next : Nat) (c : SAT.Clause) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
        (indexedLiteralOccurrencesFrom next (clauseOccurrencesFrom clauseIdx slot c)) ≤
      c.length *
        (clauseIdx + slot + next + c.length + clauseStructuredEncodedType.inputSize c + 30) := by
  induction c generalizing slot next with
  | nil =>
      simp [indexedLiteralOccurrencesFrom, clauseOccurrencesFrom]
  | cons lit rest ih =>
      let B :=
        clauseIdx + slot + next + (lit :: rest).length +
          clauseStructuredEncodedType.inputSize (lit :: rest) + 30
      let Btail :=
        clauseIdx + (slot + 1) + (next + 1) + rest.length +
          clauseStructuredEncodedType.inputSize rest + 30
      have hHead := indexedClauseOccurrence_inputSize_le clauseIdx slot next lit
      have hLitSize :
          literalStructuredEncodedType.inputSize lit ≤
            clauseStructuredEncodedType.inputSize (lit :: rest) := by
        change literalStructuredEncodedType.inputSize lit ≤
          (EncodedType.list literalStructuredEncodedType).inputSize (lit :: rest)
        rw [EncodedType.inputSize_list_cons]
        omega
      have hBtail : Btail ≤ B := by
        dsimp [Btail, B]
        change
          clauseIdx + (slot + 1) + (next + 1) + rest.length +
              (EncodedType.list literalStructuredEncodedType).inputSize rest + 30 ≤
            clauseIdx + slot + next + (lit :: rest).length +
              (EncodedType.list literalStructuredEncodedType).inputSize (lit :: rest) + 30
        rw [EncodedType.inputSize_list_cons]
        simp
        omega
      have hTail :=
        ih (slot + 1) (next + 1)
      have hTail' :
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
              (indexedLiteralOccurrencesFrom (next + 1)
                (clauseOccurrencesFrom clauseIdx (slot + 1) rest)) ≤
            rest.length * B := by
        exact hTail.trans (Nat.mul_le_mul_left rest.length hBtail)
      change
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
            ((next, { clause := clauseIdx, slot := slot, lit := lit }) ::
              indexedLiteralOccurrencesFrom (next + 1)
                (clauseOccurrencesFrom clauseIdx (slot + 1) rest)) ≤
          (lit :: rest).length * B
      rw [EncodedType.inputSize_list_cons]
      have hHeadB :
          indexedLiteralOccurrenceEncodedType.inputSize
              (next, { clause := clauseIdx, slot := slot, lit := lit }) + 1 ≤ B := by
        dsimp [B]
        change
          indexedLiteralOccurrenceEncodedType.inputSize
              (next, { clause := clauseIdx, slot := slot, lit := lit }) + 1 ≤
            clauseIdx + slot + next + (lit :: rest).length +
              (EncodedType.list literalStructuredEncodedType).inputSize (lit :: rest) + 30
        rw [EncodedType.inputSize_list_cons]
        calc
          indexedLiteralOccurrenceEncodedType.inputSize
                (next, { clause := clauseIdx, slot := slot, lit := lit }) + 1
              ≤ clauseIdx + slot + next + literalStructuredEncodedType.inputSize lit + 11 := by
                omega
          _ ≤ clauseIdx + slot + next + (lit :: rest).length +
                (literalStructuredEncodedType.inputSize lit + 1 +
                  (EncodedType.list literalStructuredEncodedType).inputSize rest) + 30 := by
                omega
      calc
        indexedLiteralOccurrenceEncodedType.inputSize
              (next, { clause := clauseIdx, slot := slot, lit := lit }) +
            1 +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
            (indexedLiteralOccurrencesFrom (next + 1)
              (clauseOccurrencesFrom clauseIdx (slot + 1) rest))
            ≤ B + rest.length * B := Nat.add_le_add hHeadB hTail'
        _ = (lit :: rest).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

noncomputable def cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial_eval (n : Nat) :
    cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval n = 20 * (n * n) + 100 := by
  simp [cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cliqueIndexedClauseOccurrenceFoldInit_inputSize_le_100 :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        cliqueIndexedClauseOccurrenceFoldInit ≤ 100 := by
  simp [cliqueIndexedClauseOccurrenceFoldInit, cliqueIndexedClauseOccurrenceAccEncodedType,
    indexedLiteralOccurrenceEncodedType, literalOccurrenceStructuredEncodedType,
    literalOccurrenceToTuple, literalOccurrenceTupleStructuredEncodedType,
    literalStructuredEncodedType, literalTupleStructuredEncodedType, EncodedType.inputSize,
    EncodedType.prod, EncodedType.list, EncodedType.nat, EncodedType.bool]

theorem cliqueIndexedClauseOccurrenceRunnerLiteralFold_prefix_inputSize_le
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier)
    (c : SAT.Clause) (k : Nat) (hk : k ≤ c.length) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (List.foldl
          (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
          ((c.take k).map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤
      cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval
        ((EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
          (cliqueIndexedClauseOccurrenceRunnerInstructions init c)) := by
  rcases init with ⟨clauseIdx, ⟨slot, ⟨next, out⟩⟩⟩
  change Nat at clauseIdx
  change Nat at slot
  change Nat at next
  change List indexedLiteralOccurrenceEncodedType.Carrier at out
  let pref : SAT.Clause := c.take k
  let occs :=
    indexedLiteralOccurrencesFrom next (clauseOccurrencesFrom clauseIdx slot pref)
  let N :=
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
      (cliqueIndexedClauseOccurrenceRunnerInstructions
        ((clauseIdx, (slot, (next, out))) :
          cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) c)
  have hInitN :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          ((clauseIdx, (slot, (next, out))) :
            cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) ≤ N := by
    simpa [N] using
      cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_init
        ((clauseIdx, (slot, (next, out))) :
          cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) c
  have hClauseN :
      clauseStructuredEncodedType.inputSize c ≤ N := by
    simpa [N] using
      cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_clause
        ((clauseIdx, (slot, (next, out))) :
          cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) c
  have hLenN : c.length ≤ N := by
    simpa [N] using
      cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_clause_length
        ((clauseIdx, (slot, (next, out))) :
          cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) c
  have hClauseIdxN : clauseIdx ≤ N := by
    have h := hInitN
    simp [cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod] at h
    omega
  have hSlotN : slot ≤ N := by
    have h := hInitN
    simp [cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod] at h
    omega
  have hNextN : next ≤ N := by
    have h := hInitN
    simp [cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod] at h
    omega
  have hOutN :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize out ≤ N := by
    have h := hInitN
    simp [cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod] at h
    omega
  have hPrefixLenN : pref.length ≤ N := by
    have hTake : pref.length ≤ k := by
      simp [pref]
    omega
  have hPrefixInputN : clauseStructuredEncodedType.inputSize pref ≤ N := by
    have hTake := encodedList_inputSize_take_le literalStructuredEncodedType k c
    have hClause' :
        (EncodedType.list literalStructuredEncodedType).inputSize c ≤ N := by
      simpa [clauseStructuredEncodedType] using hClauseN
    have hTake' :
        clauseStructuredEncodedType.inputSize pref ≤ clauseStructuredEncodedType.inputSize c := by
      simpa [pref, clauseStructuredEncodedType] using hTake
    exact hTake'.trans hClauseN
  have hOccs :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize occs ≤
        pref.length *
          (clauseIdx + slot + next + pref.length +
            clauseStructuredEncodedType.inputSize pref + 30) := by
    simpa [occs] using
      indexedClauseOccurrencesFrom_inputSize_le clauseIdx slot next pref
  have hFold :
      pref.foldl
          (fun acc lit => cliqueIndexedClauseOccurrenceStep (acc, lit))
          ((clauseIdx, (slot, (next, out))) :
            cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) =
        (clauseIdx, (slot + pref.length,
          (next + pref.length, out ++ occs))) := by
    change cliqueIndexedClauseOccurrenceFold clauseIdx slot next out pref =
      (clauseIdx, (slot + pref.length, (next + pref.length, out ++ occs)))
    apply Prod.ext
    · exact cliqueIndexedClauseOccurrenceFold_clause clauseIdx slot next out pref
    · apply Prod.ext
      · exact cliqueIndexedClauseOccurrenceFold_slot clauseIdx slot next out pref
      · apply Prod.ext
        · exact cliqueIndexedClauseOccurrenceFold_next clauseIdx slot next out pref
        · simpa [occs] using
            cliqueIndexedClauseOccurrenceFold_out clauseIdx slot next out pref
  have hSquare : N + N * (5 * N + 30) + (N + N + N + N + N + 10) ≤
      20 * (N * N) + 100 := by
    nlinarith [sq_nonneg (N : Int)]
  rw [cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_fold_eq]
  rw [hFold]
  simp [cliqueIndexedClauseOccurrenceAccEncodedType, EncodedType.inputSize_prod,
    encodedList_inputSize_append, cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial]
  have hOccsBound :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize occs ≤
        N * (5 * N + 30) := by
    have hFactor :
        clauseIdx + slot + next + pref.length +
            clauseStructuredEncodedType.inputSize pref + 30 ≤
          5 * N + 30 := by
      omega
    exact hOccs.trans (Nat.mul_le_mul hPrefixLenN hFactor)
  nlinarith [hClauseIdxN, hSlotN, hNextN, hOutN, hPrefixLenN, hOccsBound, hSquare]

theorem cliqueIndexedClauseOccurrenceRunnerFold_inputSize_le
    (p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier) :
    cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (cliqueIndexedClauseOccurrenceRunnerFold p) ≤
      cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval
        (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize p) := by
  rcases p with ⟨init, c⟩
  have hPrefix :=
    cliqueIndexedClauseOccurrenceRunnerLiteralFold_prefix_inputSize_le init c c.length
      (Nat.le_refl c.length)
  have hTakeMap :
      (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction (c.take c.length)) =
        c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction := by
    exact congrArg (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)
      (List.take_length (l := c))
  have hFoldMap :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          (List.foldl
            (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
            (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction (c.take c.length))) =
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          (List.foldl
            (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
            (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) := by
    rw [hTakeMap]
  have hPrefix' :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          (List.foldl
            (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
            (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤
        cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval
          (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize (init, c)) := by
    have hRaw :
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
            (List.foldl
              (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
              (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤
          cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval
            ((EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
              (cliqueIndexedClauseOccurrenceRunnerInstructions init c)) :=
      hFoldMap ▸ hPrefix
    simpa [cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType] using hRaw
  simpa [cliqueIndexedClauseOccurrenceRunnerFold, cliqueIndexedClauseOccurrenceRunnerInstructions_fold_eq,
    cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_fold_eq,
    cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType] using hPrefix'

theorem cliqueIndexedClauseOccurrenceRunnerFoldImage_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize p)
      (fun p : cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.Carrier =>
        cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.inputSize p)
      id := by
  refine PolynomialSizeBound.intro_with 2 20 100 ?_
  intro p
  change cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
      (cliqueIndexedClauseOccurrenceRunnerFold p) ≤
    20 * (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize p) ^ 2 + 100
  simpa [pow_two] using cliqueIndexedClauseOccurrenceRunnerFold_inputSize_le p

theorem cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).encode
        cliqueIndexedClauseOccurrenceAccEncodedType.encode
        cliqueIndexedClauseOccurrenceRunnerStep)
    (c : SAT.Clause)
    (init : cliqueIndexedClauseOccurrenceAccEncodedType.Carrier) (B T : Nat)
    (hAcc : ∀ k, k ≤ c.length →
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (List.foldl
          (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
          ((c.take k).map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤ B)
    (hStepTime : ∀ b lit,
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize b ≤ B →
        List.Mem lit c →
          hStep.time.eval
            ((EncodedType.prod
              cliqueIndexedClauseOccurrenceAccEncodedType
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (b, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)) ≤ T) :
    TM2Programs.listFoldTypedLoopTime
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
        cliqueIndexedClauseOccurrenceAccEncodedType
        cliqueIndexedClauseOccurrenceRunnerStep hStep init
        (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) ≤
      TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
        TM2Programs.listFoldSourceLength
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
          (c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
  induction c generalizing init with
  | nil =>
      change 0 ≤ TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
        TM2Programs.listFoldSourceLength cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
          (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction [])
      exact Nat.zero_le _
  | cons lit rest ih =>
      have hAcc0 : cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤ B := by
        simpa using hAcc 0 (by simp)
      have hAcc1 :
          cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              (cliqueIndexedClauseOccurrenceRunnerStep
                (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)) ≤ B := by
        simpa using hAcc 1 (by simp)
      have hTailAcc : ∀ k, k ≤ rest.length →
          cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
            (List.foldl
              (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
              (cliqueIndexedClauseOccurrenceRunnerStep
                (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))
              ((rest.take k).map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤ B := by
        intro k hk
        have hk' : k + 1 ≤ (lit :: rest).length := by
          simp
          omega
        simpa [List.take, Nat.succ_eq_add_one, List.map_take] using hAcc (k + 1) hk'
      have hTailStepTime : ∀ b lit',
          cliqueIndexedClauseOccurrenceAccEncodedType.inputSize b ≤ B →
            List.Mem lit' rest →
              hStep.time.eval
                ((EncodedType.prod
                  cliqueIndexedClauseOccurrenceAccEncodedType
                  cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                    (b, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit')) ≤ T := by
        intro b lit' hb hmem
        exact hStepTime b lit' hb (List.mem_cons_of_mem lit hmem)
      have hTail :=
        ih (cliqueIndexedClauseOccurrenceRunnerStep
          (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))
          hTailAcc hTailStepTime
      have hBlock :
          TM2Programs.listFoldBlockTime hStep.tm
              (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
                (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)).length
              (cliqueIndexedClauseOccurrenceAccEncodedType.encode init).length
              (cliqueIndexedClauseOccurrenceAccEncodedType.encode
                (cliqueIndexedClauseOccurrenceRunnerStep
                  (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))).length
              (hStep.time.eval
                ((EncodedType.prod
                  cliqueIndexedClauseOccurrenceAccEncodedType
                  cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                    (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))) ≤
            TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              ((cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
                (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)).length + 1) := by
        exact
          TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
            (by simpa [EncodedType.inputSize] using hAcc0)
            (by simpa [EncodedType.inputSize] using hAcc1)
            (hStepTime init lit hAcc0 (by exact List.mem_cons_self))
      change
        TM2Programs.listFoldTypedLoopTime
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
            cliqueIndexedClauseOccurrenceAccEncodedType
            cliqueIndexedClauseOccurrenceRunnerStep hStep init
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
              rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) ≤
          TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
            TM2Programs.listFoldSourceLength
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
              (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
                rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)
      calc
        TM2Programs.listFoldTypedLoopTime
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
            cliqueIndexedClauseOccurrenceAccEncodedType
            cliqueIndexedClauseOccurrenceRunnerStep hStep init
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
              rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)
            =
          TM2Programs.listFoldTypedLoopTime
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
            cliqueIndexedClauseOccurrenceAccEncodedType
            cliqueIndexedClauseOccurrenceRunnerStep hStep
            (cliqueIndexedClauseOccurrenceRunnerStep
              (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))
            (rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) +
          TM2Programs.listFoldBlockTime hStep.tm
            (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
              (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)).length
            (cliqueIndexedClauseOccurrenceAccEncodedType.encode init).length
            (cliqueIndexedClauseOccurrenceAccEncodedType.encode
              (cliqueIndexedClauseOccurrenceRunnerStep
                (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))).length
            (hStep.time.eval
              ((EncodedType.prod
                cliqueIndexedClauseOccurrenceAccEncodedType
                cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                  (init, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit))) := by
              rfl
        _ ≤ TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              TM2Programs.listFoldSourceLength
                cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
                (rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) +
            TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              ((cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
                (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)).length + 1) :=
              Nat.add_le_add hTail hBlock
        _ ≤ TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              TM2Programs.listFoldSourceLength
                cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode
                (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ::
                  rest.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction) := by
              simp [TM2Programs.listFoldSourceLength]
              nlinarith

noncomputable def cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).encode
        cliqueIndexedClauseOccurrenceAccEncodedType.encode
        cliqueIndexedClauseOccurrenceRunnerStep) : Polynomial Nat :=
  let B := cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial
  let T := hStep.time.comp (B + Polynomial.X + Polynomial.C 2)
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm B T

theorem cliqueIndexedClauseOccurrenceRunnerFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).encode
        cliqueIndexedClauseOccurrenceAccEncodedType.encode
        cliqueIndexedClauseOccurrenceRunnerStep)
    (p : cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.Carrier) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep cliqueIndexedClauseOccurrenceFoldInit
          (cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2) ≤
      (cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial hStep).eval
        (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize p) := by
  rcases p with ⟨init, c⟩
  let first : cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier :=
    cliqueIndexedClauseOccurrenceRunnerInitInstruction init
  let tail : List cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.Carrier :=
    c.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction
  let N :=
    (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
      (cliqueIndexedClauseOccurrenceRunnerInstructions init c)
  let B := cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 2)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hImageSize :
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.inputSize (init, c) = N := rfl
  have hInitN := cliqueIndexedClauseOccurrenceRunnerInstructions_inputSize_ge_init init c
  have hBgeN : N ≤ B := by
    simp [B]
    nlinarith [sq_nonneg (N : Int)]
  have hDefaultAcc :
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit ≤ B := by
    exact le_trans cliqueIndexedClauseOccurrenceFoldInit_inputSize_le_100 (by simp [B])
  have hAfterInit : cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤ B := by
    have h : cliqueIndexedClauseOccurrenceAccEncodedType.inputSize init ≤ N := by
      simpa [N] using hInitN
    omega
  have hTailAcc : ∀ k, k ≤ c.length →
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
        (List.foldl
          (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
          ((c.take k).map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction)) ≤ B := by
    intro k hk
    have h := cliqueIndexedClauseOccurrenceRunnerLiteralFold_prefix_inputSize_le init c k hk
    have hMapTake :
        List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction (List.take k c) =
          List.take k (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction c) :=
      List.map_take
    have hFoldMap :
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
            (List.foldl
              (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
              (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction (List.take k c))) =
          cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
            (List.foldl
              (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
              (List.take k (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction c))) := by
      rw [hMapTake]
    have h' :
        cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
            (List.foldl
              (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
              (List.take k (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction c))) ≤ B := by
      have hRaw :
          cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
              (List.foldl
                (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr)) init
                (List.take k (List.map cliqueIndexedClauseOccurrenceRunnerLiteralInstruction c))) ≤
            cliqueIndexedClauseOccurrenceRunnerFoldAccBoundPolynomial.eval
              ((EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (cliqueIndexedClauseOccurrenceRunnerInstructions init c)) :=
        hFoldMap ▸ h
      simpa [B, N] using hRaw
    simpa [List.map_take] using h'
  have hTailStepTime : ∀ b lit,
      cliqueIndexedClauseOccurrenceAccEncodedType.inputSize b ≤ B →
        List.Mem lit c →
          hStep.time.eval
            ((EncodedType.prod
              cliqueIndexedClauseOccurrenceAccEncodedType
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (b, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit)) ≤ T := by
    intro b lit hb hmem
    have hInstrMem :
        cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit ∈
          cliqueIndexedClauseOccurrenceRunnerInstructions init c := by
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨lit, hmem, rfl⟩))
    have hInstrSize :
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
            (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) ≤ N := by
      simpa [N] using
        encodedList_element_inputSize_le
          (X := cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType) hInstrMem
    have hArg :
        (EncodedType.prod
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            (b, cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) ≤ B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      change cliqueIndexedClauseOccurrenceAccEncodedType.inputSize b + 1 +
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize
          (cliqueIndexedClauseOccurrenceRunnerLiteralInstruction lit) ≤ B + N + 2
      omega
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hTailLoop :=
    cliqueIndexedClauseOccurrenceRunnerLiteralInstructions_loopTime_le hStep
      c init B T hTailAcc hTailStepTime
  have hFirstMem : first ∈ cliqueIndexedClauseOccurrenceRunnerInstructions init c := by
    simp [first, cliqueIndexedClauseOccurrenceRunnerInstructions]
  have hFirstInstrSize :
      cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize first ≤ N := by
    simpa [N] using
      encodedList_element_inputSize_le
        (X := cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType) hFirstMem
  have hFirstStepTime :
      hStep.time.eval
          ((EncodedType.prod
            cliqueIndexedClauseOccurrenceAccEncodedType
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
              (cliqueIndexedClauseOccurrenceFoldInit, first)) ≤ T := by
    have hArg :
        (EncodedType.prod
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            (cliqueIndexedClauseOccurrenceFoldInit, first) ≤ B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      change cliqueIndexedClauseOccurrenceAccEncodedType.inputSize
          cliqueIndexedClauseOccurrenceFoldInit + 1 +
        cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize first ≤ B + N + 2
      omega
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hFirstBlock :
      TM2Programs.listFoldBlockTime hStep.tm
          (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            cliqueIndexedClauseOccurrenceFoldInit).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            (cliqueIndexedClauseOccurrenceRunnerStep
              (cliqueIndexedClauseOccurrenceFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliqueIndexedClauseOccurrenceAccEncodedType
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (cliqueIndexedClauseOccurrenceFoldInit, first))) ≤
        C * ((cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length + 1) := by
    exact
      TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
        (by simpa [EncodedType.inputSize] using hDefaultAcc)
        (by simpa [first, EncodedType.inputSize] using hAfterInit)
        hFirstStepTime
  have hInstrs :
      cliqueIndexedClauseOccurrenceRunnerInstructions init c = first :: tail := by
    simp [cliqueIndexedClauseOccurrenceRunnerInstructions, first, tail]
  have hTailLoop' :
      TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep init tail ≤
        C * TM2Programs.listFoldSourceLength
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode tail := by
    simpa [tail] using hTailLoop
  have hSource :
      N =
        (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length + 1 +
          TM2Programs.listFoldSourceLength
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode tail := by
    calc
      N = (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
            (first :: tail) := by
              simp [N, hInstrs]
      _ = cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.inputSize first + 1 +
            (EncodedType.list cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
              tail := by
              rw [EncodedType.inputSize_list_cons]
      _ =
          (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length + 1 +
            TM2Programs.listFoldSourceLength
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode tail := rfl
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep cliqueIndexedClauseOccurrenceFoldInit
          (cliqueIndexedClauseOccurrenceRunnerInstructions init c) ≤
        C * N := by
    have hFirstStep :
        cliqueIndexedClauseOccurrenceRunnerStep
            (cliqueIndexedClauseOccurrenceFoldInit, first) = init := by
      simp [first]
    calc
      TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep cliqueIndexedClauseOccurrenceFoldInit
          (cliqueIndexedClauseOccurrenceRunnerInstructions init c)
          =
        TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep
          (cliqueIndexedClauseOccurrenceRunnerStep
            (cliqueIndexedClauseOccurrenceFoldInit, first))
          tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            cliqueIndexedClauseOccurrenceFoldInit).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            (cliqueIndexedClauseOccurrenceRunnerStep
              (cliqueIndexedClauseOccurrenceFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliqueIndexedClauseOccurrenceAccEncodedType
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (cliqueIndexedClauseOccurrenceFoldInit, first))) := by
            rw [hInstrs]
            rfl
      _ =
        TM2Programs.listFoldTypedLoopTime
          cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
          cliqueIndexedClauseOccurrenceAccEncodedType
          cliqueIndexedClauseOccurrenceRunnerStep hStep init tail +
        TM2Programs.listFoldBlockTime hStep.tm
          (cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            cliqueIndexedClauseOccurrenceFoldInit).length
          (cliqueIndexedClauseOccurrenceAccEncodedType.encode
            (cliqueIndexedClauseOccurrenceRunnerStep
              (cliqueIndexedClauseOccurrenceFoldInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              cliqueIndexedClauseOccurrenceAccEncodedType
              cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType).inputSize
                (cliqueIndexedClauseOccurrenceFoldInit, first))) := by
            rw [hFirstStep]
      _ ≤ C * TM2Programs.listFoldSourceLength
            cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode tail +
          C * ((cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType.encode first).length + 1) :=
            Nat.add_le_add hTailLoop' hFirstBlock
      _ ≤ C * N := by
            nlinarith [hSource, Nat.zero_le C]
  rw [hImageSize]
  have hTimeEval :
      (cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem cliqueIndexedClauseOccurrenceRunnerFoldImage_tm_polytime :
    TMPolyTimeMap
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
      cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
      id := by
  rcases cliqueIndexedClauseOccurrenceRunnerStep_tm_polytime with ⟨hStep⟩
  let X := cliqueIndexedClauseOccurrenceRunnerInstructionEncodedType
  let Y := cliqueIndexedClauseOccurrenceAccEncodedType
  refine ⟨?_⟩
  exact
    { tm :=
        TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
          hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
          (Y.encode cliqueIndexedClauseOccurrenceFoldInit)
      inputAlphabet := Equiv.refl (Option X.Symbol)
      outputAlphabet := Equiv.refl Y.Symbol
      time := cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial hStep
      outputsFun := by
        intro p
        let xs := cliqueIndexedClauseOccurrenceRunnerInstructions p.1 p.2
        let machine :=
          TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
            hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
            (Y.encode cliqueIndexedClauseOccurrenceFoldInit)
        have hRaw :=
          TM2Programs.listFoldTyped_outputsInTime X Y cliqueIndexedClauseOccurrenceRunnerStep
            cliqueIndexedClauseOccurrenceFoldInit hStep xs
        have hTime :
            2 + TM2Programs.listFoldTypedLoopTime X Y cliqueIndexedClauseOccurrenceRunnerStep
                  hStep cliqueIndexedClauseOccurrenceFoldInit xs ≤
              (cliqueIndexedClauseOccurrenceRunnerFoldTimePolynomial hStep).eval
                (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.encode p).length := by
          simpa [X, Y, xs, cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType,
            EncodedType.inputSize] using
            cliqueIndexedClauseOccurrenceRunnerFold_loopTime_le hStep p
        have hMono := TM2Programs.evalsToInTime_mono hRaw hTime
        have hInput :
            List.map (Equiv.refl (Option X.Symbol)).invFun
                (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.encode p) =
              (EncodedType.list X).encode xs := by
          change List.map id (cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType.encode p) =
            (EncodedType.list X).encode xs
          simp [X, xs, cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType]
        have hOutput :
            List.map (Equiv.refl Y.Symbol).invFun
                (cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.encode (id p)) =
              Y.encode (xs.foldl (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
                cliqueIndexedClauseOccurrenceFoldInit) := by
          change List.map id (cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType.encode p) =
            Y.encode (xs.foldl (fun acc instr => cliqueIndexedClauseOccurrenceRunnerStep (acc, instr))
              cliqueIndexedClauseOccurrenceFoldInit)
          simp [Y, xs, cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType,
            cliqueIndexedClauseOccurrenceRunnerFold]
        unfold Turing.TM2OutputsInTime
        convert hMono using 1
        · exact congrArg (Turing.initList machine) hInput
        · exact congrArg (Option.map (Turing.haltList machine)) (congrArg some hOutput) }

noncomputable def cliqueIndexedClauseOccurrenceRunnerFoldImageTMBackedMap :
    TMBackedCostedMap
      cliqueIndexedClauseOccurrenceRunnerInstructionsImageEncodedType
      cliqueIndexedClauseOccurrenceRunnerFoldImageEncodedType
      id where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cliqueIndexedClauseOccurrenceRunnerFoldImage_polynomialSizeBound
  tm_polytime := cliqueIndexedClauseOccurrenceRunnerFoldImage_tm_polytime

def cliqueIndexedFormulaOccurrenceAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.list indexedLiteralOccurrenceEncodedType))

def cliqueIndexedFormulaOccurrenceStepInputEncodedType : EncodedType :=
  EncodedType.prod cliqueIndexedFormulaOccurrenceAccEncodedType clauseStructuredEncodedType

def cliqueIndexedFormulaOccurrenceStep
    (p : cliqueIndexedFormulaOccurrenceStepInputEncodedType.Carrier) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier :=
  let clauseIdx : Nat := p.1.1
  let next : Nat := p.1.2.1
  let out : List indexedLiteralOccurrenceEncodedType.Carrier := p.1.2.2
  let folded := cliqueIndexedClauseOccurrenceFold clauseIdx 0 next out p.2
  (Nat.succ clauseIdx, (folded.2.2.1, folded.2.2.2))

def cliqueIndexedFormulaOccurrencesFrom
    (clauseIdx next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (cs : SAT.CNF) :
    cliqueIndexedFormulaOccurrenceAccEncodedType.Carrier :=
  cs.foldl
    (fun acc clause => cliqueIndexedFormulaOccurrenceStep (acc, clause))
    (clauseIdx, (next, out))

theorem cliqueIndexedFormulaOccurrencesFrom_out
    (clauseIdx next : Nat)
    (out : List indexedLiteralOccurrenceEncodedType.Carrier)
    (cs : SAT.CNF) :
    (cliqueIndexedFormulaOccurrencesFrom clauseIdx next out cs).2.2 =
      out ++ indexedLiteralOccurrencesFrom next
        (formulaOccurrencesFrom clauseIdx cs) := by
  induction cs generalizing clauseIdx next out with
  | nil =>
      change out = out ++ indexedLiteralOccurrencesFrom next
        (formulaOccurrencesFrom clauseIdx [])
      simp [indexedLiteralOccurrencesFrom, formulaOccurrencesFrom]
  | cons clause rest ih =>
      let folded := cliqueIndexedClauseOccurrenceFold clauseIdx 0 next out clause
      have hFoldOut :
          folded.2.2.2 =
            out ++ indexedLiteralOccurrencesFrom next
              (clauseOccurrencesFrom clauseIdx 0 clause) := by
        simpa [folded] using
          cliqueIndexedClauseOccurrenceFold_out clauseIdx 0 next out clause
      have hFoldNext :
          folded.2.2.1 =
            next + (clauseOccurrencesFrom clauseIdx 0 clause).length := by
        have hNext := cliqueIndexedClauseOccurrenceFold_next clauseIdx 0 next out clause
        simpa [folded, clauseOccurrencesFrom_length] using hNext
      simp only [cliqueIndexedFormulaOccurrencesFrom, cliqueIndexedFormulaOccurrenceStep]
      change
        (cliqueIndexedFormulaOccurrencesFrom (clauseIdx + 1) folded.2.2.1
            folded.2.2.2 rest).2.2 =
          out ++ indexedLiteralOccurrencesFrom next
            (clauseOccurrencesFrom clauseIdx 0 clause ++
              formulaOccurrencesFrom (clauseIdx + 1) rest)
      rw [ih, hFoldOut, hFoldNext]
      rw [indexedLiteralOccurrencesFrom_append]
      simp [List.append_assoc]

def cliqueIndexedLiteralOccurrences (φ : SAT.ThreeCNF) :
    List indexedLiteralOccurrenceEncodedType.Carrier :=
  (cliqueIndexedFormulaOccurrencesFrom 0 0 [] φ.clauses).2.2

theorem cliqueIndexedLiteralOccurrences_eq_indexedLiteralOccurrences
    (φ : SAT.ThreeCNF) :
    cliqueIndexedLiteralOccurrences φ = indexedLiteralOccurrences φ := by
  simpa [cliqueIndexedLiteralOccurrences, indexedLiteralOccurrences, literalOccurrences] using
    cliqueIndexedFormulaOccurrencesFrom_out 0 0
      ([] : List indexedLiteralOccurrenceEncodedType.Carrier) φ.clauses

end Clique
end Karp21
end ComplexityReduction
