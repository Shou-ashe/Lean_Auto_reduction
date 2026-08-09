import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.Part1

namespace ComplexityReduction
namespace Karp21
namespace ExactCover
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.FiniteWitness

theorem setCovering_of_setCoveringCNF_satisfiable (I : SetCoveringInput) :
    SAT.CNF.Satisfiable (setCoveringCNF I) → SetCovering I := by
  classical
  rintro ⟨a, hSat⟩
  have hSlotChoice :
      ∀ slot, slot < I.k →
        ∃ choice, choice < setCoveringChoiceCount I ∧
          a (setCoveringChoiceVar I slot choice) = true := by
    intro slot hslot
    have hClauseSat := hSat _ (setCoveringSlotAtLeastClause_mem_cnf (I := I) hslot)
    rcases hClauseSat with ⟨lit, hlit, hEval⟩
    rcases List.mem_map.mp hlit with ⟨choice, hchoiceMem, rfl⟩
    refine ⟨choice, by simpa using hchoiceMem, ?_⟩
    simpa [setCoveringChoiceLit, SAT.Literal.eval] using hEval
  let chosen : Nat → Nat := fun slot =>
    if h : ∃ choice, choice < setCoveringChoiceCount I ∧
      a (setCoveringChoiceVar I slot choice) = true then Classical.choose h else 0
  have chosen_spec :
      ∀ {slot}, slot < I.k →
        chosen slot < setCoveringChoiceCount I ∧
          a (setCoveringChoiceVar I slot (chosen slot)) = true := by
    intro slot hslot
    have h : ∃ choice, choice < setCoveringChoiceCount I ∧
      a (setCoveringChoiceVar I slot choice) = true := hSlotChoice slot hslot
    simpa [chosen, h] using (Classical.choose_spec h)
  let cover : List (List Nat) :=
    (List.range I.k).filterMap fun slot =>
      if h : chosen slot < I.system.sets.length then some (sourceSetAt I (chosen slot))
      else none
  refine ⟨cover, ?_, ?_, ?_⟩
  · simpa [cover] using
      (filterMap_length_le
        (fun slot =>
          if h : chosen slot < I.system.sets.length then some (sourceSetAt I (chosen slot))
          else none)
        (List.range I.k))
  · intro S hS
    rw [List.mem_filterMap] at hS
    rcases hS with ⟨slot, _hslotMem, hSome⟩
    by_cases hidx : chosen slot < I.system.sets.length
    · simp [hidx] at hSome
      subst S
      rw [sourceSetAt, List.getD_eq_getElem (l := I.system.sets) (d := []) hidx]
      exact List.getElem_mem _
    · simp [hidx] at hSome
  · intro x hx
    have hClauseSat := hSat _ (setCoveringCoverageClause_mem_cnf (I := I) hx)
    rcases hClauseSat with ⟨lit, hlit, hEval⟩
    rcases (mem_setCoveringCoverageClause_iff I x lit).1 hlit with
      ⟨slot, hslot, idx, hidx, hxSource, rfl⟩
    have hLitTrue :
        a (setCoveringChoiceVar I slot idx) = true := by
      simpa [setCoveringChoiceLit, SAT.Literal.eval] using hEval
    have hChosen := chosen_spec hslot
    have hchoiceCountIdx : idx < setCoveringChoiceCount I := by
      simpa [setCoveringChoiceCount] using Nat.lt_succ_of_lt hidx
    have hChosenEq :
        chosen slot = idx :=
      setCoveringChoice_unique_of_cnf_satisfies (I := I) hSat hslot
        hChosen.1 hchoiceCountIdx hChosen.2 hLitTrue
    refine ⟨sourceSetAt I idx, ?_, hxSource⟩
    rw [List.mem_filterMap]
    refine ⟨slot, by simpa using hslot, ?_⟩
    simp [hidx, hChosenEq]

theorem setCoveringCNF_correct (I : SetCoveringInput) :
    SetCovering I ↔ SAT.CNF.Satisfiable (setCoveringCNF I) :=
  ⟨setCoveringCNF_satisfiable_of_setCovering I,
    setCovering_of_setCoveringCNF_satisfiable I⟩

/-! ### Structured size certificate for the compact Set Covering CNF -/

theorem setCoveringFlatMap_length_le_mul {α β : Type*} (xs : List α) (f : α → List β)
    (B : Nat) (hB : ∀ x ∈ xs, (f x).length ≤ B) :
    (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : (f x).length ≤ B := hB x (by simp)
      have hTail : ∀ y ∈ xs, (f y).length ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih hTail
      calc
        ((x :: xs).flatMap f).length = (f x).length + (xs.flatMap f).length := by
          simp
        _ ≤ B + xs.length * B := by
          omega
        _ = (x :: xs).length * B := by
          simp [Nat.succ_mul, Nat.add_comm]

theorem setCoveringEncodedList_length_le_inputSize (X : EncodedType) :
    ∀ xs : List X.Carrier, xs.length ≤ (EncodedType.list X).inputSize xs
  | [] => by simp
  | x :: xs => by
      have ih := setCoveringEncodedList_length_le_inputSize X xs
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_cons]
      omega

theorem clauseStructured_inputSize_le_length_mul_of_lit_var_le
    {c : SAT.Clause} {V : Nat}
    (hVar : ∀ l ∈ c, l.var ≤ V) :
    clauseStructuredEncodedType.inputSize c ≤ c.length * (V + 4) := by
  induction c with
  | nil =>
      change (EncodedType.list literalStructuredEncodedType).inputSize ([] : List SAT.Literal) ≤
        ([] : List SAT.Literal).length * (V + 4)
      simp [EncodedType.inputSize, EncodedType.list]
      exact ⟨rfl, rfl⟩
  | cons l ls ih =>
      have hl : l.var ≤ V := hVar l (by simp)
      have hTail : ∀ m ∈ ls, m.var ≤ V := by
        intro m hm
        exact hVar m (by simp [hm])
      have ih' := ih hTail
      have ihList :
          (EncodedType.list literalStructuredEncodedType).inputSize ls ≤
            ls.length * (V + 4) := by
        simpa [clauseStructuredEncodedType] using ih'
      have hLit : literalStructuredEncodedType.inputSize l ≤ V + 3 := by
        rw [literalStructured_inputSize_eq]
        omega
      change (EncodedType.list literalStructuredEncodedType).inputSize (l :: ls) ≤
        (l :: ls).length * (V + 4)
      rw [EncodedType.inputSize_list_cons]
      change
        literalStructuredEncodedType.inputSize l + 1 +
            (EncodedType.list literalStructuredEncodedType).inputSize ls ≤
          (ls.length + 1) * (V + 4)
      calc
        literalStructuredEncodedType.inputSize l + 1 +
            (EncodedType.list literalStructuredEncodedType).inputSize ls
            ≤ (V + 3) + 1 + ls.length * (V + 4) := by
              omega
        _ = (ls.length + 1) * (V + 4) := by
              ring

theorem cnfStructured_inputSize_le_length_mul_of_clause_bounds
    {φ : SAT.CNF} {L V : Nat}
    (hLen : ∀ c ∈ φ, c.length ≤ L)
    (hVar : ∀ c ∈ φ, ∀ l ∈ c, l.var ≤ V) :
    cnfStructuredEncodedType.inputSize φ ≤ φ.length * (L * (V + 4) + 1) := by
  induction φ with
  | nil =>
      change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : List SAT.Clause) ≤
        ([] : List SAT.Clause).length * (L * (V + 4) + 1)
      simp [EncodedType.inputSize, EncodedType.list]
      exact ⟨rfl, rfl⟩
  | cons c cs ih =>
      have hcLen : c.length ≤ L := hLen c (by simp)
      have hcVar : ∀ l ∈ c, l.var ≤ V := hVar c (by simp)
      have hcsLen : ∀ d ∈ cs, d.length ≤ L := by
        intro d hd
        exact hLen d (by simp [hd])
      have hcsVar : ∀ d ∈ cs, ∀ l ∈ d, l.var ≤ V := by
        intro d hd l hl
        exact hVar d (by simp [hd]) l hl
      have ih' := ih hcsLen hcsVar
      have ihList :
          (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤
            cs.length * (L * (V + 4) + 1) := by
        simpa [cnfStructuredEncodedType] using ih'
      have hcSize :
          clauseStructuredEncodedType.inputSize c ≤ L * (V + 4) := by
        exact (clauseStructured_inputSize_le_length_mul_of_lit_var_le hcVar).trans
          (Nat.mul_le_mul_right (V + 4) hcLen)
      change (EncodedType.list clauseStructuredEncodedType).inputSize (c :: cs) ≤
        (c :: cs).length * (L * (V + 4) + 1)
      rw [EncodedType.inputSize_list_cons]
      change
        clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs ≤
          (cs.length + 1) * (L * (V + 4) + 1)
      calc
        clauseStructuredEncodedType.inputSize c + 1 +
            (EncodedType.list clauseStructuredEncodedType).inputSize cs
            ≤ L * (V + 4) + 1 + cs.length * (L * (V + 4) + 1) := by
              omega
        _ = (cs.length + 1) * (L * (V + 4) + 1) := by
              ring

def setCoveringCNFClauseLengthBound (I : SetCoveringInput) : Nat :=
  setCoveringChoiceCount I + I.k * I.system.sets.length + 2

def setCoveringCNFVarBound (I : SetCoveringInput) : Nat :=
  (I.k + setCoveringChoiceCount I + 1) ^ 2

theorem setCoveringCoverageLitsForSlot_length_le_sets_length
    (I : SetCoveringInput) (x slot : Nat) :
    (setCoveringCoverageLitsForSlot I x slot).length ≤ I.system.sets.length := by
  unfold setCoveringCoverageLitsForSlot
  simpa using
    filterMap_length_le
      (fun idx =>
        if x ∈ sourceSetAt I idx then some (setCoveringChoiceLit I slot idx) else none)
      (List.range I.system.sets.length)

theorem setCoveringCoverageClause_length_le (I : SetCoveringInput) (x : Nat) :
    (setCoveringCoverageClause I x).length ≤ I.k * I.system.sets.length := by
  unfold setCoveringCoverageClause
  simpa using
    setCoveringFlatMap_length_le_mul (List.range I.k)
      (setCoveringCoverageLitsForSlot I x) I.system.sets.length
      (by
        intro slot _hslot
        exact setCoveringCoverageLitsForSlot_length_le_sets_length I x slot)

theorem setCoveringSlotAtMostClausesFor_length_le
    (I : SetCoveringInput) (slot choice : Nat) :
    (setCoveringSlotAtMostClausesFor I slot choice).length ≤ setCoveringChoiceCount I := by
  unfold setCoveringSlotAtMostClausesFor
  simpa using
    ComplexityReduction.Karp21.VertexCover.filter_length_le
      (fun other => decide (choice < other))
      (List.range (setCoveringChoiceCount I))

theorem setCoveringSlotAtMostClauses_length_le (I : SetCoveringInput) (slot : Nat) :
    (setCoveringSlotAtMostClauses I slot).length ≤
      setCoveringChoiceCount I * setCoveringChoiceCount I := by
  unfold setCoveringSlotAtMostClauses
  simpa using
    setCoveringFlatMap_length_le_mul (List.range (setCoveringChoiceCount I))
      (setCoveringSlotAtMostClausesFor I slot) (setCoveringChoiceCount I)
      (by
        intro choice _hchoice
        exact setCoveringSlotAtMostClausesFor_length_le I slot choice)

theorem setCoveringSlotClausesFor_length_le (I : SetCoveringInput) (slot : Nat) :
    (setCoveringSlotClausesFor I slot).length ≤
      setCoveringChoiceCount I * setCoveringChoiceCount I + 1 := by
  have hAtMost := setCoveringSlotAtMostClauses_length_le I slot
  simp [setCoveringSlotClausesFor]
  omega

theorem setCoveringSlotClauses_length_le (I : SetCoveringInput) :
    (setCoveringSlotClauses I).length ≤
      I.k * (setCoveringChoiceCount I * setCoveringChoiceCount I + 1) := by
  unfold setCoveringSlotClauses
  simpa using
    setCoveringFlatMap_length_le_mul (List.range I.k)
      (setCoveringSlotClausesFor I)
      (setCoveringChoiceCount I * setCoveringChoiceCount I + 1)
      (by
        intro slot _hslot
        exact setCoveringSlotClausesFor_length_le I slot)

theorem setCoveringCNF_length_le (I : SetCoveringInput) :
    (setCoveringCNF I).length ≤
      I.k * (setCoveringChoiceCount I * setCoveringChoiceCount I + 1) +
        I.system.universeSize := by
  have hSlot := setCoveringSlotClauses_length_le I
  have hCoverage :
      (setCoveringCoverageClauses I).length = I.system.universeSize := by
    simp [setCoveringCoverageClauses]
  rw [setCoveringCNF, List.length_append, hCoverage]
  omega

theorem setCoveringCNF_clause_length_le {I : SetCoveringInput} {clause : SAT.Clause}
    (hclause : clause ∈ setCoveringCNF I) :
    clause.length ≤ setCoveringCNFClauseLengthBound I := by
  classical
  rw [setCoveringCNF, List.mem_append] at hclause
  rcases hclause with hSlot | hCoverage
  · rw [setCoveringSlotClauses] at hSlot
    rcases List.mem_flatMap.mp hSlot with ⟨slot, _hslot, hBlock⟩
    simp [setCoveringSlotClausesFor] at hBlock
    rcases hBlock with hAtLeast | hAtMost
    · subst clause
      simp [setCoveringSlotAtLeastClause, setCoveringCNFClauseLengthBound]
      omega
    · rw [setCoveringSlotAtMostClauses] at hAtMost
      rcases List.mem_flatMap.mp hAtMost with ⟨choice, _hchoice, hPair⟩
      rw [setCoveringSlotAtMostClausesFor] at hPair
      rcases List.mem_map.mp hPair with ⟨other, _hother, hEq⟩
      subst clause
      simp [setCoveringCNFClauseLengthBound]
  · rw [setCoveringCoverageClauses] at hCoverage
    rcases List.mem_map.mp hCoverage with ⟨x, _hx, rfl⟩
    exact (setCoveringCoverageClause_length_le I x).trans (by
      simp [setCoveringCNFClauseLengthBound]
      omega)

theorem setCoveringChoiceVar_le_cnfVarBound {I : SetCoveringInput}
    {slot choice : Nat} (hslot : slot < I.k)
    (hchoice : choice < setCoveringChoiceCount I) :
    setCoveringChoiceVar I slot choice ≤ setCoveringCNFVarBound I := by
  have hPair := Nat.pair_lt_max_add_one_sq slot choice
  have hMax :
      max slot choice + 1 ≤ I.k + setCoveringChoiceCount I + 1 := by
    omega
  have hPow :
      (max slot choice + 1) ^ 2 ≤
        (I.k + setCoveringChoiceCount I + 1) ^ 2 :=
    Nat.pow_le_pow_left hMax 2
  exact (Nat.le_of_lt hPair).trans hPow

theorem setCoveringChoiceLit_var_le_cnfVarBound {I : SetCoveringInput}
    {slot choice : Nat} (hslot : slot < I.k)
    (hchoice : choice < setCoveringChoiceCount I) :
    (setCoveringChoiceLit I slot choice).var ≤ setCoveringCNFVarBound I := by
  simpa [setCoveringChoiceLit, SAT.Literal.positive] using
    setCoveringChoiceVar_le_cnfVarBound (I := I) hslot hchoice

theorem setCoveringChoiceNegLit_var_le_cnfVarBound {I : SetCoveringInput}
    {slot choice : Nat} (hslot : slot < I.k)
    (hchoice : choice < setCoveringChoiceCount I) :
    (setCoveringChoiceNegLit I slot choice).var ≤ setCoveringCNFVarBound I := by
  simpa [setCoveringChoiceNegLit, SAT.Literal.negative] using
    setCoveringChoiceVar_le_cnfVarBound (I := I) hslot hchoice

theorem setCoveringCNF_lit_var_le {I : SetCoveringInput}
    {clause : SAT.Clause} (hclause : clause ∈ setCoveringCNF I)
    {lit : SAT.Literal} (hlit : lit ∈ clause) :
    lit.var ≤ setCoveringCNFVarBound I := by
  classical
  rw [setCoveringCNF, List.mem_append] at hclause
  rcases hclause with hSlot | hCoverage
  · rw [setCoveringSlotClauses] at hSlot
    rcases List.mem_flatMap.mp hSlot with ⟨slot, hslotMem, hBlock⟩
    have hslot : slot < I.k := by simpa using hslotMem
    simp [setCoveringSlotClausesFor] at hBlock
    rcases hBlock with hAtLeast | hAtMost
    · subst clause
      rcases List.mem_map.mp hlit with ⟨choice, hchoiceMem, rfl⟩
      exact setCoveringChoiceLit_var_le_cnfVarBound (I := I) hslot (by simpa using hchoiceMem)
    · rw [setCoveringSlotAtMostClauses] at hAtMost
      rcases List.mem_flatMap.mp hAtMost with ⟨choice, hchoiceMem, hPair⟩
      have hchoice : choice < setCoveringChoiceCount I := by
        simpa using hchoiceMem
      rw [setCoveringSlotAtMostClausesFor] at hPair
      rcases List.mem_map.mp hPair with ⟨other, hotherMem, hEq⟩
      subst clause
      have hother : other < setCoveringChoiceCount I := by
        exact by
          have hmem := (List.mem_filter.mp hotherMem).1
          simpa using hmem
      simp at hlit
      rcases hlit with rfl | rfl
      · exact setCoveringChoiceNegLit_var_le_cnfVarBound (I := I) hslot hchoice
      · exact setCoveringChoiceNegLit_var_le_cnfVarBound (I := I) hslot hother
  · rw [setCoveringCoverageClauses] at hCoverage
    rcases List.mem_map.mp hCoverage with ⟨x, _hxMem, rfl⟩
    rcases (mem_setCoveringCoverageClause_iff I x lit).1 hlit with
      ⟨slot, hslot, idx, hidx, _hxSource, rfl⟩
    have hchoice : idx < setCoveringChoiceCount I := by
      simpa [setCoveringChoiceCount] using Nat.lt_succ_of_lt hidx
    exact setCoveringChoiceLit_var_le_cnfVarBound (I := I) hslot hchoice

theorem setCoveringStructured_inputSize_ge_universeSize_for_cnf (I : SetCoveringInput) :
    I.system.universeSize ≤ setCoveringStructuredEncodedType.inputSize I := by
  rw [SetCovering.setCoveringStructured_inputSize_eq,
    SetCovering.setSystemStructured_inputSize_eq]
  omega

theorem setCoveringStructured_inputSize_ge_sets_length_for_cnf (I : SetCoveringInput) :
    I.system.sets.length ≤ setCoveringStructuredEncodedType.inputSize I := by
  have hSets :
      I.system.sets.length ≤ setFamilyStructuredEncodedType.inputSize I.system.sets := by
    simpa [setFamilyStructuredEncodedType] using
      setCoveringEncodedList_length_le_inputSize setStructuredEncodedType I.system.sets
  rw [SetCovering.setCoveringStructured_inputSize_eq,
    SetCovering.setSystemStructured_inputSize_eq]
  omega

theorem setCoveringStructured_inputSize_ge_budget_for_cnf (I : SetCoveringInput) :
    I.k ≤ setCoveringStructuredEncodedType.inputSize I := by
  rw [SetCovering.setCoveringStructured_inputSize_eq]
  omega

theorem setCoveringCNF_structured_inputSize_le_source_poly_succ (I : SetCoveringInput) :
    cnfStructuredEncodedType.inputSize (setCoveringCNF I) ≤
      100000 * (setCoveringStructuredEncodedType.inputSize I + 1) ^ 8 := by
  let S := setCoveringStructuredEncodedType.inputSize I
  let C := setCoveringChoiceCount I
  let L := setCoveringCNFClauseLengthBound I
  let V := setCoveringCNFVarBound I
  have hBase :=
    cnfStructured_inputSize_le_length_mul_of_clause_bounds
      (φ := setCoveringCNF I) (L := L) (V := V)
      (by
        intro clause hclause
        simpa [L] using setCoveringCNF_clause_length_le (I := I) hclause)
      (by
        intro clause hclause lit hlit
        simpa [V] using setCoveringCNF_lit_var_le (I := I) hclause hlit)
  have hK : I.k ≤ S := by
    simpa [S] using setCoveringStructured_inputSize_ge_budget_for_cnf I
  have hM : I.system.sets.length ≤ S := by
    simpa [S] using setCoveringStructured_inputSize_ge_sets_length_for_cnf I
  have hU : I.system.universeSize ≤ S := by
    simpa [S] using setCoveringStructured_inputSize_ge_universeSize_for_cnf I
  have hC : C ≤ S + 1 := by
    simp [C, setCoveringChoiceCount]
    omega
  have hC2 : C ^ 2 ≤ (S + 1) ^ 2 :=
    Nat.pow_le_pow_left hC 2
  have hCountBase := setCoveringCNF_length_le I
  have hCountPoly :
      I.k * (C * C + 1) + I.system.universeSize ≤ 10 * (S + 1) ^ 3 := by
    have hCC : C * C ≤ (S + 1) ^ 2 := by
      simpa [pow_two] using hC2
    have hTerm :
        I.k * (C * C + 1) ≤ S * ((S + 1) ^ 2 + 1) :=
      Nat.mul_le_mul hK (Nat.add_le_add_right hCC 1)
    calc
      I.k * (C * C + 1) + I.system.universeSize
          ≤ S * ((S + 1) ^ 2 + 1) + S := by
            exact Nat.add_le_add hTerm hU
      _ ≤ 10 * (S + 1) ^ 3 := by
            cases S <;> ring_nf <;> omega
  have hCount :
      (setCoveringCNF I).length ≤ 10 * (S + 1) ^ 3 := by
    exact hCountBase.trans (by simpa [C, pow_two] using hCountPoly)
  have hKM : I.k * I.system.sets.length ≤ S * S :=
    Nat.mul_le_mul hK hM
  have hLPoly : L ≤ 10 * (S + 1) ^ 2 := by
    calc
      L ≤ (S + 1) + S * S + 2 := by
            simp [L, setCoveringCNFClauseLengthBound, C] at *
            omega
      _ ≤ 10 * (S + 1) ^ 2 := by
            cases S <;> ring_nf <;> omega
  have hKC : I.k + C + 1 ≤ S + (S + 1) + 1 := by
    omega
  have hVBase : V ≤ (S + (S + 1) + 1) ^ 2 := by
    simpa [V, setCoveringCNFVarBound, C] using Nat.pow_le_pow_left hKC 2
  have hVPoly : V ≤ 10 * (S + 1) ^ 2 := by
    calc
      V ≤ (S + (S + 1) + 1) ^ 2 := hVBase
      _ ≤ 10 * (S + 1) ^ 2 := by
            cases S <;> ring_nf <;> omega
  have hFactorPoly : L * (V + 4) + 1 ≤ 200 * (S + 1) ^ 4 := by
    have hV4 : V + 4 ≤ 10 * (S + 1) ^ 2 + 4 := by
      omega
    have hMul :
        L * (V + 4) ≤ (10 * (S + 1) ^ 2) * (10 * (S + 1) ^ 2 + 4) :=
      Nat.mul_le_mul hLPoly hV4
    calc
      L * (V + 4) + 1
          ≤ (10 * (S + 1) ^ 2) * (10 * (S + 1) ^ 2 + 4) + 1 := by
            exact Nat.add_le_add_right hMul 1
      _ ≤ 200 * (S + 1) ^ 4 := by
            cases S <;> ring_nf <;> omega
  calc
    cnfStructuredEncodedType.inputSize (setCoveringCNF I)
        ≤ (setCoveringCNF I).length * (L * (V + 4) + 1) := hBase
    _ ≤ (10 * (S + 1) ^ 3) * (200 * (S + 1) ^ 4) :=
          Nat.mul_le_mul hCount hFactorPoly
    _ ≤ 100000 * (S + 1) ^ 8 := by
          cases S <;> ring_nf <;> omega

theorem setCoveringCNF_structured_inputSize_le_source_poly (I : SetCoveringInput) :
    cnfStructuredEncodedType.inputSize (setCoveringCNF I) ≤
      100000000 * (setCoveringStructuredEncodedType.inputSize I) ^ 8 + 100000000 := by
  let S := setCoveringStructuredEncodedType.inputSize I
  have hBase := setCoveringCNF_structured_inputSize_le_source_poly_succ I
  have hSucc :
      100000 * (S + 1) ^ 8 ≤ 100000000 * S ^ 8 + 100000000 := by
    cases S <;> ring_nf <;> omega
  exact hBase.trans (by simpa [S] using hSucc)

theorem setCoveringToSatisfiabilityStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : SetCoveringInput => setCoveringStructuredEncodedType.inputSize I)
      (fun φ : SAT.CNF => cnfStructuredEncodedType.inputSize φ)
      setCoveringCNF := by
  refine PolynomialSizeBound.intro_with 8 100000000 100000000 ?_
  intro I
  exact setCoveringCNF_structured_inputSize_le_source_poly I

/--
Legacy size-only compact structured Set-Covering-to-CNF-SAT transport.

The public `setCoveringToSatisfiabilityStructuredKarpReduction` name is supplied
by the direct TM-backed Set-Covering-CNF assembly.
-/
noncomputable def setCoveringToSatisfiabilityStructuredSizeOnlyKarpReduction :
    KarpReductionM CostedPolyTimeModel
      setCoveringStructuredDecisionProblem satisfiabilityStructuredDecisionProblem where
  f :=
    { toFun := setCoveringCNF
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            setCoveringToSatisfiabilityStructured_polynomialSizeBound) }
  correct := by
    intro I
    simpa [setCoveringStructuredDecisionProblem, satisfiabilityStructuredDecisionProblem]
      using setCoveringCNF_correct I

/-- Bounded exact-cover candidate subfamilies. -/
def exactCoverCandidates (I : ExactCoverInput) : List (List (List Nat)) :=
  (indexListsUpTo I.system.sets.length I.system.sets.length).map
    (setsFromIndices I.system.sets)

theorem selected_mem_exactCoverCandidates {I : ExactCoverInput}
    {selected : List (List Nat)}
    (hLen : selected.length ≤ I.system.sets.length)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S) :
    selected ∈ exactCoverCandidates I := by
  let idxs := selected.map I.system.sets.idxOf
  have hBounds : ∀ i ∈ idxs, i < I.system.sets.length := by
    intro i hi
    rcases List.mem_map.mp hi with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  have hIdxs : idxs ∈ indexListsUpTo I.system.sets.length I.system.sets.length := by
    exact mem_indexListsUpTo_of_bounds (by simpa [idxs] using hLen) hBounds
  have hDecode : setsFromIndices I.system.sets idxs = selected := by
    simpa [setsFromIndices, idxs] using
      (valuesFromIdxOf_eq (values := I.system.sets) (selected := selected)
        (fallback := ([] : List Nat)) hFamily)
  exact List.mem_map.mpr ⟨idxs, hIdxs, hDecode⟩

/-- Canonical bounded exact-cover witnesses for an input. -/
noncomputable def exactCoverWitnesses (I : ExactCoverInput) : List (List (List Nat)) := by
  classical
  exact (exactCoverCandidates I).filter fun selected =>
    decide
      (SetSystemWellFormed I.system ∧
        (∀ S ∈ selected, IsSetInFamily I.system S) ∧
        selected.Nodup ∧
        PairwiseDisjointFamily selected ∧
        CoversUniverse I.system selected)

theorem mem_exactCoverWitnesses_iff (I : ExactCoverInput) (selected : List (List Nat)) :
    selected ∈ exactCoverWitnesses I ↔
      selected ∈ exactCoverCandidates I ∧
        SetSystemWellFormed I.system ∧
        (∀ S ∈ selected, IsSetInFamily I.system S) ∧
        selected.Nodup ∧
        PairwiseDisjointFamily selected ∧
        CoversUniverse I.system selected := by
  classical
  simp [exactCoverWitnesses]

theorem exactCover_iff_witnesses_pos (I : ExactCoverInput) :
    ExactCover I ↔ 0 < (exactCoverWitnesses I).length := by
  constructor
  · rintro ⟨hWellFormed, selected, hFamily, _hNodup, hDisjoint, hCovers⟩
    let canonical := selected.dedup
    have hCanonicalNodup : canonical.Nodup := List.nodup_dedup selected
    have hCanonicalFamily : ∀ S ∈ canonical, IsSetInFamily I.system S := by
      intro S hS
      exact hFamily S (List.mem_dedup.mp hS)
    have hCanonicalDisjoint : PairwiseDisjointFamily canonical := by
      intro A hA B hB hNe x hxA hxB
      exact hDisjoint A (List.mem_dedup.mp hA) B (List.mem_dedup.mp hB) hNe x hxA hxB
    have hCanonicalCovers : CoversUniverse I.system canonical := by
      intro x hx
      rcases hCovers x hx with ⟨S, hS, hxS⟩
      exact ⟨S, List.mem_dedup.mpr hS, hxS⟩
    have hLen : canonical.length ≤ I.system.sets.length := by
      exact nodup_length_le_of_mem hCanonicalNodup hCanonicalFamily
    have hCandidate := selected_mem_exactCoverCandidates hLen hCanonicalFamily
    have hMem : canonical ∈ exactCoverWitnesses I :=
      (mem_exactCoverWitnesses_iff I canonical).2
        ⟨hCandidate, hWellFormed, hCanonicalFamily, hCanonicalNodup, hCanonicalDisjoint,
          hCanonicalCovers⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : exactCoverWitnesses I with
    | nil =>
        simp [hList] at hPos
    | cons selected rest =>
        have hMem : selected ∈ exactCoverWitnesses I := by
          simp [hList]
        rcases (mem_exactCoverWitnesses_iff I selected).1 hMem with
          ⟨_hCandidate, hWellFormed, hFamily, hNodup, hDisjoint, hCovers⟩
        exact ⟨hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩

/-- A tiny yes-instance for current-schema Exact Cover. -/
def yesInput : ExactCoverInput where
  system := { universeSize := 1, sets := [[0]] }

/-- A tiny no-instance for current-schema Exact Cover. -/
def noInput : ExactCoverInput where
  system := { universeSize := 1, sets := [] }

theorem yesInput_isYes :
    ExactCover yesInput := by
  refine ⟨?_, [[0]], ?_, ?_, ?_, ?_⟩
  · intro S hS x hx
    simp [yesInput] at hS
    subst S
    simp at hx
    subst x
    simp [yesInput]
  · intro S hS
    simp [yesInput, IsSetInFamily] at hS ⊢
    exact hS
  · simp
  · intro A hA B hB hNe x hxA hxB
    simp at hA hB
    subst A
    subst B
    exact hNe rfl
  · intro x hx
    have hx0 : x = 0 := by
      have hx' : x < 1 := by
        simpa [yesInput] using hx
      omega
    subst x
    exact ⟨[0], by simp, by simp⟩

theorem noInput_isNo :
    ¬ ExactCover noInput := by
  rintro ⟨_hWellFormed, selected, hFamily, _hNodup, _hDisjoint, hCovers⟩
  rcases hCovers 0 (by simp [noInput]) with ⟨S, hSSelected, _h0S⟩
  have hS := hFamily S hSSelected
  simp [noInput, IsSetInFamily] at hS

/-- Indicator family: yes exactly when the source witness list is nonempty. -/
def indicatorInput (m : Nat) : ExactCoverInput :=
  if 0 < m then yesInput else noInput

theorem indicatorInput_correct (m : Nat) :
    ExactCover (indicatorInput m) ↔ 0 < m := by
  by_cases hm : 0 < m
  · constructor
    · intro _; exact hm
    · intro _; simpa [indicatorInput, hm] using yesInput_isYes
  · constructor
    · intro h
      exact (noInput_isNo (by simpa [indicatorInput, hm] using h)).elim
    · intro h
      exact (hm h).elim

/-! ### Compact Chromatic Number to Exact Cover route -/

/-- Edge/color coordinates used by the compact coloring exact-cover gadget. -/
def colorEdgeColorPairs (I : ChromaticNumberInput) : List (Nat × Nat) :=
  List.range I.graph.edges.length ×ˢ List.range I.colors

theorem mem_colorEdgeColorPairs_iff (I : ChromaticNumberInput) (p : Nat × Nat) :
    p ∈ colorEdgeColorPairs I ↔ p.1 < I.graph.edges.length ∧ p.2 < I.colors := by
  cases p with
  | mk i c =>
      simp [colorEdgeColorPairs]

theorem colorEdgeColorPairs_nodup (I : ChromaticNumberInput) :
    (colorEdgeColorPairs I).Nodup := by
  simpa [colorEdgeColorPairs] using
    (List.nodup_range (n := I.graph.edges.length)).product
      (List.nodup_range (n := I.colors))

theorem colorEdgeColorPairs_length (I : ChromaticNumberInput) :
    (colorEdgeColorPairs I).length = I.graph.edges.length * I.colors := by
  simp [colorEdgeColorPairs, List.length_product]

def colorVertexCode (_I : ChromaticNumberInput) (v : Nat) : Nat :=
  v

def colorEdgeCode (I : ChromaticNumberInput) (i c : Nat) : Nat :=
  I.graph.vertices + (colorEdgeColorPairs I).idxOf (i, c)

def colorUniverseSize (I : ChromaticNumberInput) : Nat :=
  I.graph.vertices + (colorEdgeColorPairs I).length

def colorEdgeAt (I : ChromaticNumberInput) (i : Nat) : Nat × Nat :=
  I.graph.edges.getD i (0, 0)

def colorEdgeIncident (I : ChromaticNumberInput) (i v : Nat) : Prop :=
  (colorEdgeAt I i).1 = v ∨ (colorEdgeAt I i).2 = v

instance colorEdgeIncidentDecidable (I : ChromaticNumberInput) (i v : Nat) :
    Decidable (colorEdgeIncident I i v) := by
  unfold colorEdgeIncident
  infer_instance

def colorIncidentEdgeIndices (I : ChromaticNumberInput) (v : Nat) : List Nat :=
  SetCovering.incidentEdgeIndices { graph := I.graph, k := 0 } v

/--
The block that chooses color `c` for vertex `v`.  It covers the private vertex
marker and every incident edge/color marker for that color.
-/
def colorChoiceBlock (I : ChromaticNumberInput) (v c : Nat) : List Nat :=
  colorVertexCode I v :: (colorIncidentEdgeIndices I v).map fun i => colorEdgeCode I i c

/-- Filler for edge/color markers not covered by endpoint color choices. -/
def colorFillerBlock (I : ChromaticNumberInput) (i c : Nat) : List Nat :=
  [colorEdgeCode I i c]

def colorChoiceBlocksForVertex (I : ChromaticNumberInput) (v : Nat) : List (List Nat) :=
  (List.range I.colors).map fun c => colorChoiceBlock I v c

def colorChoiceBlocks (I : ChromaticNumberInput) : List (List Nat) :=
  (List.range I.graph.vertices).flatMap (colorChoiceBlocksForVertex I)

def colorFillerBlocksForEdge (I : ChromaticNumberInput) (i : Nat) : List (List Nat) :=
  (List.range I.colors).map fun c => colorFillerBlock I i c

def colorFillerBlocks (I : ChromaticNumberInput) : List (List Nat) :=
  (List.range I.graph.edges.length).flatMap (colorFillerBlocksForEdge I)

def colorExactCoverSetSystem (I : ChromaticNumberInput) : SetSystemInput where
  universeSize := colorUniverseSize I
  sets := colorChoiceBlocks I ++ colorFillerBlocks I

def colorExactCoverCore (I : ChromaticNumberInput) : ExactCoverInput where
  system := colorExactCoverSetSystem I

def colorGraphHasSelfLoop (I : ChromaticNumberInput) : Prop :=
  ∃ e ∈ I.graph.edges, e.1 = e.2

def colorSelfLoopBool (e : Nat × Nat) : Bool :=
  decide (e.1 = e.2)

theorem colorSelfLoopBool_eq_true_iff (e : Nat × Nat) :
    colorSelfLoopBool e = true ↔ e.1 = e.2 := by
  simp [colorSelfLoopBool]

def colorGraphHasSelfLoopBool (I : ChromaticNumberInput) : Bool :=
  I.graph.edges.any colorSelfLoopBool

theorem colorGraphHasSelfLoopBool_list_eq_true_iff (edges : List (Nat × Nat)) :
    edges.any colorSelfLoopBool = true ↔ ∃ e ∈ edges, e.1 = e.2 := by
  induction edges with
  | nil =>
      simp
  | cons e es ih =>
      simp [List.any, colorSelfLoopBool_eq_true_iff, ih]

theorem colorGraphHasSelfLoopBool_eq_true_iff (I : ChromaticNumberInput) :
    colorGraphHasSelfLoopBool I = true ↔ colorGraphHasSelfLoop I := by
  simpa [colorGraphHasSelfLoopBool, colorGraphHasSelfLoop]
    using colorGraphHasSelfLoopBool_list_eq_true_iff I.graph.edges

def chromaticNumberToExactCoverMap (I : ChromaticNumberInput) : ExactCoverInput :=
  if colorGraphHasSelfLoopBool I then noInput else colorExactCoverCore I

theorem colorVertexCode_lt_universe {I : ChromaticNumberInput} {v : Nat}
    (hv : v < I.graph.vertices) :
    colorVertexCode I v < colorUniverseSize I := by
  simp [colorVertexCode, colorUniverseSize]
  omega

theorem colorEdgeCode_lt_universe {I : ChromaticNumberInput} {i c : Nat}
    (hi : i < I.graph.edges.length) (hc : c < I.colors) :
    colorEdgeCode I i c < colorUniverseSize I := by
  have hp : (i, c) ∈ colorEdgeColorPairs I :=
    (mem_colorEdgeColorPairs_iff I (i, c)).2 ⟨hi, hc⟩
  have hIdx : (colorEdgeColorPairs I).idxOf (i, c) < (colorEdgeColorPairs I).length :=
    List.idxOf_lt_length_iff.mpr hp
  simp [colorEdgeCode, colorUniverseSize]
  omega

theorem colorVertexCode_ne_colorEdgeCode {I : ChromaticNumberInput} {v i c : Nat}
    (hv : v < I.graph.vertices) :
    colorVertexCode I v ≠ colorEdgeCode I i c := by
  intro h
  simp [colorVertexCode, colorEdgeCode] at h
  omega

theorem colorEdgeCode_inj {I : ChromaticNumberInput} {i c j d : Nat}
    (hi : i < I.graph.edges.length) (hc : c < I.colors)
    (hj : j < I.graph.edges.length) (hd : d < I.colors)
    (hEq : colorEdgeCode I i c = colorEdgeCode I j d) :
    i = j ∧ c = d := by
  have hp : (i, c) ∈ colorEdgeColorPairs I :=
    (mem_colorEdgeColorPairs_iff I (i, c)).2 ⟨hi, hc⟩
  have hq : (j, d) ∈ colorEdgeColorPairs I :=
    (mem_colorEdgeColorPairs_iff I (j, d)).2 ⟨hj, hd⟩
  have hIdx :
      (colorEdgeColorPairs I).idxOf (i, c) =
        (colorEdgeColorPairs I).idxOf (j, d) := by
    simp [colorEdgeCode] at hEq
    omega
  have hPair : (i, c) = (j, d) :=
    (List.idxOf_inj hp).1 hIdx
  exact Prod.ext_iff.mp hPair

theorem colorEdgeAt_eq_getElem {I : ChromaticNumberInput} {i : Nat}
    (hi : i < I.graph.edges.length) :
    colorEdgeAt I i = I.graph.edges[i] := by
  exact List.getD_eq_getElem (l := I.graph.edges) (d := (0, 0)) hi

theorem mem_colorIncidentEdgeIndices_iff (I : ChromaticNumberInput) (v i : Nat) :
    i ∈ colorIncidentEdgeIndices I v ↔
      i < I.graph.edges.length ∧ colorEdgeIncident I i v := by
  classical
  simpa [colorIncidentEdgeIndices, SetCovering.incidentEdgeIndices,
    colorEdgeIncident, colorEdgeAt] using
    SetCovering.mem_incidentEdgeIndices_iff ({ graph := I.graph, k := 0 } : VertexCoverInput)
      v i

theorem mem_colorChoiceBlock_iff (I : ChromaticNumberInput) (v c x : Nat) :
    x ∈ colorChoiceBlock I v c ↔
      x = colorVertexCode I v ∨
        ∃ i, i < I.graph.edges.length ∧ colorEdgeIncident I i v ∧
          x = colorEdgeCode I i c := by
  constructor
  · intro hx
    simp [colorChoiceBlock] at hx
    rcases hx with hxVertex | hxEdge
    · exact Or.inl hxVertex
    · rcases hxEdge with ⟨i, hi, hEq⟩
      rcases (mem_colorIncidentEdgeIndices_iff I v i).1 hi with ⟨hiLt, hIncident⟩
      exact Or.inr ⟨i, hiLt, hIncident, hEq.symm⟩
  · intro hx
    rcases hx with hxVertex | hxEdge
    · simp [colorChoiceBlock, hxVertex]
    · rcases hxEdge with ⟨i, hi, hIncident, hEq⟩
      simp [colorChoiceBlock, hEq]
      exact Or.inr ⟨i, (mem_colorIncidentEdgeIndices_iff I v i).2 ⟨hi, hIncident⟩, rfl⟩

theorem colorVertex_mem_colorChoiceBlock (I : ChromaticNumberInput) (v c : Nat) :
    colorVertexCode I v ∈ colorChoiceBlock I v c := by
  simp [colorChoiceBlock]

theorem colorEdgeCode_mem_colorChoiceBlock {I : ChromaticNumberInput} {i v c : Nat}
    (hi : i < I.graph.edges.length) (hIncident : colorEdgeIncident I i v) :
    colorEdgeCode I i c ∈ colorChoiceBlock I v c := by
  exact (mem_colorChoiceBlock_iff I v c (colorEdgeCode I i c)).2
    (Or.inr ⟨i, hi, hIncident, rfl⟩)

theorem mem_colorFillerBlock_iff (I : ChromaticNumberInput) (i c x : Nat) :
    x ∈ colorFillerBlock I i c ↔ x = colorEdgeCode I i c := by
  simp [colorFillerBlock]

theorem mem_colorChoiceBlocks_iff (I : ChromaticNumberInput) (B : List Nat) :
    B ∈ colorChoiceBlocks I ↔
      ∃ v, v < I.graph.vertices ∧ ∃ c, c < I.colors ∧ B = colorChoiceBlock I v c := by
  constructor
  · intro hB
    rcases List.mem_flatMap.mp hB with ⟨v, hv, hBlock⟩
    rcases List.mem_map.mp hBlock with ⟨c, hc, rfl⟩
    exact ⟨v, by simpa using hv, c, by simpa using hc, rfl⟩
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨v, by simpa using hv, List.mem_map.mpr ⟨c, by simpa using hc, rfl⟩⟩

theorem mem_colorFillerBlocks_iff (I : ChromaticNumberInput) (B : List Nat) :
    B ∈ colorFillerBlocks I ↔
      ∃ i, i < I.graph.edges.length ∧
        ∃ c, c < I.colors ∧ B = colorFillerBlock I i c := by
  constructor
  · intro hB
    rcases List.mem_flatMap.mp hB with ⟨i, hi, hBlock⟩
    rcases List.mem_map.mp hBlock with ⟨c, hc, rfl⟩
    exact ⟨i, by simpa using hi, c, by simpa using hc, rfl⟩
  · rintro ⟨i, hi, c, hc, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨i, by simpa using hi, List.mem_map.mpr ⟨c, by simpa using hc, rfl⟩⟩

theorem colorExactCoverSetSystem_wellFormed (I : ChromaticNumberInput) :
    SetSystemWellFormed (colorExactCoverSetSystem I) := by
  intro B hB x hxB
  rcases List.mem_append.mp hB with hChoice | hFiller
  · rcases (mem_colorChoiceBlocks_iff I B).1 hChoice with ⟨v, hv, c, hc, rfl⟩
    rcases (mem_colorChoiceBlock_iff I v c x).1 hxB with hxVertex | hxEdge
    · rw [hxVertex]
      exact colorVertexCode_lt_universe (I := I) hv
    · rcases hxEdge with ⟨i, hi, _hIncident, hxEq⟩
      rw [hxEq]
      exact colorEdgeCode_lt_universe (I := I) hi hc
  · rcases (mem_colorFillerBlocks_iff I B).1 hFiller with ⟨i, hi, c, hc, rfl⟩
    rw [(mem_colorFillerBlock_iff I i c x).1 hxB]
    exact colorEdgeCode_lt_universe (I := I) hi hc

def colorSelectedChoiceBlocks (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    List (List Nat) :=
  (List.range I.graph.vertices).map fun v => colorChoiceBlock I v (colorOf v)

def colorSelectedFillerBlocksForEdge
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (i : Nat) :
    List (List Nat) :=
  ((List.range I.colors).filter fun c =>
    decide (c ≠ colorOf (colorEdgeAt I i).1 ∧ c ≠ colorOf (colorEdgeAt I i).2)).map
      fun c => colorFillerBlock I i c

def colorSelectedFillerBlocks (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    List (List Nat) :=
  (List.range I.graph.edges.length).flatMap (colorSelectedFillerBlocksForEdge I colorOf)

def colorSelectedBlocksRaw (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    List (List Nat) :=
  colorSelectedChoiceBlocks I colorOf ++ colorSelectedFillerBlocks I colorOf

def colorSelectedBlocks (I : ChromaticNumberInput) (colorOf : Nat → Nat) :
    List (List Nat) :=
  (colorSelectedBlocksRaw I colorOf).dedup

theorem mem_colorSelectedChoiceBlocks_iff
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (B : List Nat) :
    B ∈ colorSelectedChoiceBlocks I colorOf ↔
      ∃ v, v < I.graph.vertices ∧ B = colorChoiceBlock I v (colorOf v) := by
  constructor
  · intro hB
    rcases List.mem_map.mp hB with ⟨v, hv, rfl⟩
    exact ⟨v, by simpa using hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩

theorem mem_colorSelectedFillerBlocksForEdge_iff
    (I : ChromaticNumberInput) (colorOf : Nat → Nat) (i : Nat) (B : List Nat) :
    B ∈ colorSelectedFillerBlocksForEdge I colorOf i ↔
      ∃ c, c < I.colors ∧ c ≠ colorOf (colorEdgeAt I i).1 ∧
        c ≠ colorOf (colorEdgeAt I i).2 ∧ B = colorFillerBlock I i c := by
  constructor
  · intro hB
    rcases List.mem_map.mp hB with ⟨c, hc, rfl⟩
    have hc' := (List.mem_filter.mp hc)
    rcases hc' with ⟨hcRange, hcEndpoint⟩
    have hcEndpointProp :
        c ≠ colorOf (colorEdgeAt I i).1 ∧ c ≠ colorOf (colorEdgeAt I i).2 :=
      of_decide_eq_true hcEndpoint
    exact ⟨c, by simpa using hcRange, hcEndpointProp.1, hcEndpointProp.2, rfl⟩
  · rintro ⟨c, hc, hcLeft, hcRight, rfl⟩
    exact List.mem_map.mpr
      ⟨c, List.mem_filter.mpr ⟨by simpa using hc, by simp [hcLeft, hcRight]⟩, rfl⟩

end ExactCover
end Karp21
end ComplexityReduction
