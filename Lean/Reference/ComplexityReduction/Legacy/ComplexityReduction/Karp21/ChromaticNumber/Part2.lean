import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.Part1

namespace ComplexityReduction
namespace Karp21
namespace ChromaticNumber
open ComplexityReduction.Combinatorics.Graph

theorem forwardColorFrom_clauseEdgesFor_ne {a : SAT.Assignment} {n j : Nat}
    {c : SAT.Clause} {cs : List SAT.Clause} {e : Nat × Nat}
    (hLen : c.length ≤ 3)
    (hBound : ∀ l ∈ c, l.var < n)
    (hSat : SAT.Clause.Satisfies c a)
    (he : e ∈ clauseEdgesFor n j c) :
    forwardColorFrom a n (c :: cs) j e.1 ≠ forwardColorFrom a n (c :: cs) j e.2 := by
  unfold clauseEdgesFor at he
  cases hp : paddedClause c with
  | none =>
      cases c with
      | nil =>
          rcases hSat with ⟨l, hl, _⟩
          simp at hl
      | cons c₀ cs' =>
          cases cs' with
          | nil => simp [paddedClause] at hp
          | cons c₁ cs' =>
              cases cs' with
              | nil => simp [paddedClause] at hp
              | cons c₂ cs' => simp [paddedClause] at hp
  | some triple =>
      rcases triple with ⟨l₀, l₁, l₂⟩
      have h₀ : l₀.var < n := hBound l₀ (paddedClause_left_mem hp)
      have h₁ : l₁.var < n := hBound l₁ (paddedClause_middle_mem hp)
      have h₂ : l₂.var < n := hBound l₂ (paddedClause_right_mem hp)
      have hOr := paddedClause_or_true_of_satisfies hLen hp hSat
      have hEdges := clauseGadgetColor_edges_ne (l₀.eval a) (l₁.eval a) (l₂.eval a) hOr
      simp [hp, clauseGadgetEdges] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [forwardColorFrom_clauseA0_head, forwardColorFrom_clauseA1_head,
          clauseColorFor, hp] using hEdges.1
      · simpa [forwardColorFrom_clauseA0_head, forwardColorFrom_clauseA2_head,
          clauseColorFor, hp] using hEdges.2.1
      · simpa [forwardColorFrom_clauseA3_head, forwardColorFrom_true,
          clauseColorFor, hp] using hEdges.2.2.1
      · simpa [forwardColorFrom_clauseA1_head, forwardColorFrom_true,
          clauseColorFor, hp] using hEdges.2.2.2.1
      · simpa [forwardColorFrom_clauseA2_head, forwardColorFrom_clauseA3_head,
          clauseColorFor, hp] using hEdges.2.2.2.2.1
      · simpa [forwardColorFrom_literalVertex h₀, forwardColorFrom_clauseA2_head,
          clauseColorFor, hp] using hEdges.2.2.2.2.2.1
      · simpa [forwardColorFrom_literalVertex h₀, forwardColorFrom_clauseA3_head,
          clauseColorFor, hp] using hEdges.2.2.2.2.2.2.1
      · simpa [forwardColorFrom_literalVertex h₁, forwardColorFrom_clauseA0_head,
          clauseColorFor, hp] using hEdges.2.2.2.2.2.2.2.1
      · simpa [forwardColorFrom_literalVertex h₂, forwardColorFrom_clauseA1_head,
          clauseColorFor, hp] using hEdges.2.2.2.2.2.2.2.2

theorem forwardColorFrom_clauseEdgesFrom_ne {a : SAT.Assignment} {n j : Nat}
    {cs : List SAT.Clause} {e : Nat × Nat}
    (hLen : ∀ c ∈ cs, c.length ≤ 3)
    (hBound : ∀ c ∈ cs, ∀ l ∈ c, l.var < n)
    (hSat : ∀ c ∈ cs, SAT.Clause.Satisfies c a)
    (he : e ∈ clauseEdgesFrom n j cs) :
    forwardColorFrom a n cs j e.1 ≠ forwardColorFrom a n cs j e.2 := by
  induction cs generalizing j with
  | nil =>
      simp [clauseEdgesFrom] at he
  | cons c cs ih =>
      simp [clauseEdgesFrom] at he
      rcases he with heHead | heTail
      · exact forwardColorFrom_clauseEdgesFor_ne
          (hLen c (by simp))
          (fun l hl => hBound c (by simp) l hl)
          (hSat c (by simp))
          heHead
      · have hSafe := endpoints_neHeadSlots_of_mem_clauseEdgesFrom
          (n := n) (prev := j) (start := j + 1) (cs := cs) (e := e)
          (by omega)
          (fun d hd l hl => hBound d (by simp [hd]) l hl)
          heTail
        have hTail := ih (j := j + 1)
          (fun d hd => hLen d (by simp [hd]))
          (fun d hd l hl => hBound d (by simp [hd]) l hl)
          (fun d hd => hSat d (by simp [hd]))
          heTail
        rw [forwardColorFrom_cons_eq_of_neHeadSlots hSafe.1,
          forwardColorFrom_cons_eq_of_neHeadSlots hSafe.2]
        exact hTail

theorem textbookMap_colorable_of_satisfies (φ : SAT.ThreeCNF) (a : SAT.Assignment)
    (hSat : φ.Satisfies a) :
    ChromaticNumber (textbookMap φ) := by
  let n := Clique.cnfVarBound φ.clauses
  refine ⟨forwardColor φ a, ?_⟩
  constructor
  · intro v hv
    exact forwardColor_lt_three φ a v
  · intro e he
    simp [textbookMap, textbookEdges, forwardColor] at he ⊢
    rcases he with hPalette | hVar | hClause
    · simp [paletteEdges] at hPalette
      rcases hPalette with rfl | rfl | rfl
      · simp [forwardColorFrom_base, forwardColorFrom_true]
      · simp [forwardColorFrom_base, forwardColorFrom_false]
      · simp [forwardColorFrom_true, forwardColorFrom_false]
    · rcases List.mem_flatMap.mp hVar with ⟨i, hiRange, hiEdge⟩
      have hi : i < n := by
        simpa [n] using hiRange
      have hi' : i < Clique.cnfVarBound φ.clauses := by
        simpa [n] using hi
      simp [variableEdgesFor] at hiEdge
      rcases hiEdge with rfl | rfl | rfl
      · rw [forwardColorFrom_pos (a := a) (n := Clique.cnfVarBound φ.clauses) hi',
          forwardColorFrom_base]
        by_cases hai : a i <;> simp [hai]
      · rw [forwardColorFrom_neg (a := a) (n := Clique.cnfVarBound φ.clauses) hi',
          forwardColorFrom_base]
        by_cases hai : a i <;> simp [hai]
      · rw [forwardColorFrom_pos (a := a) (n := Clique.cnfVarBound φ.clauses) hi',
          forwardColorFrom_neg (a := a) (n := Clique.cnfVarBound φ.clauses) hi']
        by_cases hai : a i <;> simp [hai]
    · exact forwardColorFrom_clauseEdgesFrom_ne
        (a := a) (n := n) (j := 0) (cs := φ.clauses) (e := e)
        (fun c hc => φ.isThree c hc)
        (fun c hc l hl => by
          simpa [n] using Clique.var_lt_cnfVarBound_of_mem hc hl)
        (fun c hc => hSat c hc)
        hClause

def decodedAssignment (colorOf : Nat → Nat) : SAT.Assignment :=
  fun i => decide (colorOf (posVertex i) = colorOf trueVertex)

theorem decoded_literal_eval_true_of_color_true {colorOf : Nat → Nat} {l : SAT.Literal}
    (hPosNeg : colorOf (posVertex l.var) ≠ colorOf (negVertex l.var))
    (hColor : colorOf (literalVertex l) = colorOf trueVertex) :
    l.eval (decodedAssignment colorOf) = true := by
  cases l with
  | mk var neg =>
      cases neg
      · have hColor' : colorOf (posVertex var) = colorOf trueVertex := by
          simpa [literalVertex] using hColor
        simp [decodedAssignment, SAT.Literal.eval, hColor']
      · have hColor' : colorOf (negVertex var) = colorOf trueVertex := by
          simpa [literalVertex] using hColor
        have hPosNeTrue : colorOf (posVertex var) ≠ colorOf trueVertex := by
          intro h
          exact hPosNeg (by simp [h, hColor'])
        simp [decodedAssignment, SAT.Literal.eval, hPosNeTrue]

theorem eq_false_of_lt_three_ne_base_ne_true {x base true false : Nat}
    (hx : x < 3) (hb : base < 3) (ht : true < 3) (hf : false < 3)
    (hbt : base ≠ true) (hbf : base ≠ false) (htf : true ≠ false)
    (hxb : x ≠ base) (hxt : x ≠ true) :
    x = false := by
  omega

theorem clauseGadget_has_true_of_proper
    {x₀ x₁ x₂ a₀ a₁ a₂ a₃ base true false : Nat}
    (hx₀ : x₀ < 3) (hx₁ : x₁ < 3) (hx₂ : x₂ < 3)
    (ha₀ : a₀ < 3) (ha₁ : a₁ < 3) (ha₂ : a₂ < 3) (ha₃ : a₃ < 3)
    (hb : base < 3) (ht : true < 3) (hf : false < 3)
    (hbt : base ≠ true) (hbf : base ≠ false) (htf : true ≠ false)
    (hx₀b : x₀ ≠ base) (hx₁b : x₁ ≠ base) (hx₂b : x₂ ≠ base)
    (ha₀a₁ : a₀ ≠ a₁) (ha₀a₂ : a₀ ≠ a₂) (ha₃t : a₃ ≠ true)
    (ha₁t : a₁ ≠ true) (ha₂a₃ : a₂ ≠ a₃)
    (hx₀a₂ : x₀ ≠ a₂) (hx₀a₃ : x₀ ≠ a₃)
    (hx₁a₀ : x₁ ≠ a₀) (hx₂a₁ : x₂ ≠ a₁) :
    x₀ = true ∨ x₁ = true ∨ x₂ = true := by
  by_contra h
  have hx₀t : x₀ ≠ true := by intro h0; exact h (Or.inl h0)
  have hx₁t : x₁ ≠ true := by intro h1; exact h (Or.inr (Or.inl h1))
  have hx₂t : x₂ ≠ true := by intro h2; exact h (Or.inr (Or.inr h2))
  have hx₀f : x₀ = false :=
    eq_false_of_lt_three_ne_base_ne_true hx₀ hb ht hf hbt hbf htf hx₀b hx₀t
  have hx₁f : x₁ = false :=
    eq_false_of_lt_three_ne_base_ne_true hx₁ hb ht hf hbt hbf htf hx₁b hx₁t
  have hx₂f : x₂ = false :=
    eq_false_of_lt_three_ne_base_ne_true hx₂ hb ht hf hbt hbf htf hx₂b hx₂t
  omega

theorem literalVertex_lt_textbookVertexCount {l : SAT.Literal} {n m : Nat}
    (hvar : l.var < n) :
    literalVertex l < textbookVertexCount n m := by
  cases l with
  | mk var neg =>
      simp at hvar
      cases neg
      · simp [literalVertex, posVertex, textbookVertexCount, variableLimit]
        omega
      · simp [literalVertex, negVertex, textbookVertexCount, variableLimit]
        omega

theorem variableEdge_pos_base_mem {i n : Nat} (hi : i < n) :
    (posVertex i, baseVertex) ∈ variableEdges n := by
  exact List.mem_flatMap.mpr ⟨i, by simpa using hi, by simp [variableEdgesFor]⟩

theorem variableEdge_neg_base_mem {i n : Nat} (hi : i < n) :
    (negVertex i, baseVertex) ∈ variableEdges n := by
  exact List.mem_flatMap.mpr ⟨i, by simpa using hi, by simp [variableEdgesFor]⟩

theorem variableEdge_pos_neg_mem {i n : Nat} (hi : i < n) :
    (posVertex i, negVertex i) ∈ variableEdges n := by
  exact List.mem_flatMap.mpr ⟨i, by simpa using hi, by simp [variableEdgesFor]⟩

theorem clause_satisfies_of_clauseEdgesFor_proper {colorOf : Nat → Nat}
    {n totalM j : Nat} {c : SAT.Clause}
    (hj : j < totalM)
    (hLen : c.length ≤ 3)
    (hBound : ∀ l ∈ c, l.var < n)
    (hRange : ∀ v, v < textbookVertexCount n totalM → colorOf v < 3)
    (hBaseTrue : colorOf baseVertex ≠ colorOf trueVertex)
    (hBaseFalse : colorOf baseVertex ≠ colorOf falseVertex)
    (hTrueFalse : colorOf trueVertex ≠ colorOf falseVertex)
    (hLiteralBase : ∀ l ∈ c, colorOf (literalVertex l) ≠ colorOf baseVertex)
    (hPosNeg : ∀ i, i < n → colorOf (posVertex i) ≠ colorOf (negVertex i))
    (hClauseEdges : ∀ e ∈ clauseEdgesFor n j c, colorOf e.1 ≠ colorOf e.2) :
    SAT.Clause.Satisfies c (decodedAssignment colorOf) := by
  unfold clauseEdgesFor at hClauseEdges
  cases hp : paddedClause c with
  | none =>
      cases c with
      | nil =>
          have hLoop := hClauseEdges (baseVertex, baseVertex) (by simp [hp])
          exact (hLoop rfl).elim
      | cons c₀ cs =>
          cases cs with
          | nil => simp [paddedClause] at hp
          | cons c₁ cs =>
              cases cs with
              | nil => simp [paddedClause] at hp
              | cons c₂ cs => simp [paddedClause] at hp
  | some triple =>
      rcases triple with ⟨l₀, l₁, l₂⟩
      have h₀mem : l₀ ∈ c := paddedClause_left_mem hp
      have h₁mem : l₁ ∈ c := paddedClause_middle_mem hp
      have h₂mem : l₂ ∈ c := paddedClause_right_mem hp
      have h₀var : l₀.var < n := hBound l₀ h₀mem
      have h₁var : l₁.var < n := hBound l₁ h₁mem
      have h₂var : l₂.var < n := hBound l₂ h₂mem
      have hBT : colorOf baseVertex ≠ colorOf trueVertex := hBaseTrue
      have hBF : colorOf baseVertex ≠ colorOf falseVertex := hBaseFalse
      have hTF : colorOf trueVertex ≠ colorOf falseVertex := hTrueFalse
      have hTrueLit :
          colorOf (literalVertex l₀) = colorOf trueVertex ∨
            colorOf (literalVertex l₁) = colorOf trueVertex ∨
            colorOf (literalVertex l₂) = colorOf trueVertex := by
        apply clauseGadget_has_true_of_proper
        · exact hRange _ (literalVertex_lt_textbookVertexCount h₀var)
        · exact hRange _ (literalVertex_lt_textbookVertexCount h₁var)
        · exact hRange _ (literalVertex_lt_textbookVertexCount h₂var)
        · exact hRange _ (clauseA0_lt_textbookVertexCount hj)
        · exact hRange _ (clauseA1_lt_textbookVertexCount hj)
        · exact hRange _ (clauseA2_lt_textbookVertexCount hj)
        · exact hRange _ (clauseA3_lt_textbookVertexCount hj)
        · exact hRange baseVertex (by
            simp [textbookVertexCount, variableLimit, baseVertex])
        · exact hRange trueVertex (by
            simp [textbookVertexCount, variableLimit, trueVertex]
            omega)
        · exact hRange falseVertex (by
            simp [textbookVertexCount, variableLimit, falseVertex]
            omega)
        · exact hBT
        · exact hBF
        · exact hTF
        · exact hLiteralBase l₀ h₀mem
        · exact hLiteralBase l₁ h₁mem
        · exact hLiteralBase l₂ h₂mem
        · exact hClauseEdges (clauseA0 n j, clauseA1 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (clauseA0 n j, clauseA2 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (clauseA3 n j, trueVertex) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (clauseA1 n j, trueVertex) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (clauseA2 n j, clauseA3 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (literalVertex l₀, clauseA2 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (literalVertex l₀, clauseA3 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (literalVertex l₁, clauseA0 n j) (by simp [hp, clauseGadgetEdges])
        · exact hClauseEdges (literalVertex l₂, clauseA1 n j) (by simp [hp, clauseGadgetEdges])
      rcases hTrueLit with hLit | hLit | hLit
      · exact ⟨l₀, h₀mem, decoded_literal_eval_true_of_color_true (hPosNeg l₀.var h₀var) hLit⟩
      · exact ⟨l₁, h₁mem, decoded_literal_eval_true_of_color_true (hPosNeg l₁.var h₁var) hLit⟩
      · exact ⟨l₂, h₂mem, decoded_literal_eval_true_of_color_true (hPosNeg l₂.var h₂var) hLit⟩

theorem clauses_satisfy_of_clauseEdgesFrom_proper {colorOf : Nat → Nat}
    {n totalM j : Nat} {cs : List SAT.Clause}
    (hIndex : j + cs.length ≤ totalM)
    (hLen : ∀ c ∈ cs, c.length ≤ 3)
    (hBound : ∀ c ∈ cs, ∀ l ∈ c, l.var < n)
    (hRange : ∀ v, v < textbookVertexCount n totalM → colorOf v < 3)
    (hBaseTrue : colorOf baseVertex ≠ colorOf trueVertex)
    (hBaseFalse : colorOf baseVertex ≠ colorOf falseVertex)
    (hTrueFalse : colorOf trueVertex ≠ colorOf falseVertex)
    (hLiteralBase : ∀ c ∈ cs, ∀ l ∈ c, colorOf (literalVertex l) ≠ colorOf baseVertex)
    (hPosNeg : ∀ i, i < n → colorOf (posVertex i) ≠ colorOf (negVertex i))
    (hClauseEdges : ∀ e ∈ clauseEdgesFrom n j cs, colorOf e.1 ≠ colorOf e.2) :
    ∀ c ∈ cs, SAT.Clause.Satisfies c (decodedAssignment colorOf) := by
  induction cs generalizing j with
  | nil =>
      intro c hc
      simp at hc
  | cons first rest ih =>
      intro target htarget
      simp at htarget
      rcases htarget with rfl | htarget
      · have hj : j < totalM := by
          have hpos : 0 < (target :: rest).length := by simp
          omega
        exact clause_satisfies_of_clauseEdgesFor_proper
          (colorOf := colorOf) (n := n) (totalM := totalM) (j := j) (c := target)
          hj
          (hLen target (by simp))
          (fun l hl => hBound target (by simp) l hl)
          hRange
          hBaseTrue
          hBaseFalse
          hTrueFalse
          (fun l hl => hLiteralBase target (by simp) l hl)
          hPosNeg
          (fun e he => hClauseEdges e (by simp [clauseEdgesFrom, he]))
      · exact ih (j := j + 1)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIndex)
          (fun x hx => hLen x (by simp [hx]))
          (fun x hx l hl => hBound x (by simp [hx]) l hl)
          (fun x hx l hl => hLiteralBase x (by simp [hx]) l hl)
          (fun e he => hClauseEdges e (by simp [clauseEdgesFrom, he]))
          target
          htarget

theorem textbookMap_correct (φ : SAT.ThreeCNF) :
    SAT.threeSATDecisionProblem.isYes φ ↔ ChromaticNumber (textbookMap φ) := by
  constructor
  · intro hYes
    rcases (SAT.threeSATDecisionProblem_isYes_iff φ).1 hYes with ⟨a, hSat⟩
    exact textbookMap_colorable_of_satisfies φ a hSat
  · rintro ⟨colorOf, hProper⟩
    refine (SAT.threeSATDecisionProblem_isYes_iff φ).2
      ⟨decodedAssignment colorOf, ?_⟩
    apply clauses_satisfy_of_clauseEdgesFrom_proper
      (colorOf := colorOf)
      (n := Clique.cnfVarBound φ.clauses)
      (totalM := φ.clauses.length)
      (j := 0)
      (cs := φ.clauses)
    · simp
    · exact fun c hc => φ.isThree c hc
    · exact fun c hc l hl => Clique.var_lt_cnfVarBound_of_mem hc hl
    · intro v hv
      exact hProper.1 v (by simpa [textbookMap] using hv)
    · exact hProper.2 (baseVertex, trueVertex) (by
        simp [textbookMap, textbookEdges, paletteEdges])
    · exact hProper.2 (baseVertex, falseVertex) (by
        simp [textbookMap, textbookEdges, paletteEdges])
    · exact hProper.2 (trueVertex, falseVertex) (by
        simp [textbookMap, textbookEdges, paletteEdges])
    · intro c hc l hl
      have hvar := Clique.var_lt_cnfVarBound_of_mem hc hl
      cases l with
      | mk var neg =>
          simp at hvar
          cases neg
          · simpa [literalVertex] using
              hProper.2 (posVertex var, baseVertex) (by
                simp [textbookMap, textbookEdges]
                exact Or.inr (Or.inl (variableEdge_pos_base_mem hvar)))
          · simpa [literalVertex] using
              hProper.2 (negVertex var, baseVertex) (by
                simp [textbookMap, textbookEdges]
                exact Or.inr (Or.inl (variableEdge_neg_base_mem hvar)))
    · intro i hi
      exact hProper.2 (posVertex i, negVertex i) (by
        simp [textbookMap, textbookEdges]
        exact Or.inr (Or.inl (variableEdge_pos_neg_mem hi)))
    · intro e he
      exact hProper.2 e (by
        simp [textbookMap, textbookEdges]
        exact Or.inr (Or.inr he))

/-- Costed Karp reduction from local 3SAT to Chromatic Number. -/
noncomputable def threeSATToChromaticNumberTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem chromaticNumberDecisionProblem := by
  simpa [chromaticNumberDecisionProblem, chromaticNumberEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.Graph.ChromaticNumber
      map
      map_correct

/-- Costed Karp reduction from local 3SAT to Chromatic Number. -/
noncomputable def threeSATToChromaticNumberKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      chromaticNumberDecisionProblem :=
  threeSATToChromaticNumberTMBackedKarpReduction.toCostedKarpReduction

/-- Costed P15q textbook Karp reduction from local 3SAT to Chromatic Number. -/
noncomputable def threeSATToChromaticNumber_textbookTMBackedKarpReduction :
    TMBackedCostedReduction SAT.threeSATDecisionProblem chromaticNumberDecisionProblem := by
  simpa [chromaticNumberDecisionProblem, chromaticNumberEncodedType] using
    rawCodomainTMBackedReduction
      SAT.threeSATDecisionProblem
      Combinatorics.Graph.ChromaticNumber
      textbookMap
      textbookMap_correct

/-- Costed P15q textbook Karp reduction from local 3SAT to Chromatic Number. -/
noncomputable def threeSATToChromaticNumber_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem
      chromaticNumberDecisionProblem :=
  threeSATToChromaticNumber_textbookTMBackedKarpReduction.toCostedKarpReduction

/-- Chromatic Number is locally in NP for the project-local costed model. -/
theorem chromaticNumberInNP :
    InNPEnc CostedPolyTimeModel chromaticNumberDecisionProblem :=
  decidableInNP chromaticNumberDecisionProblem

/-- The structured finite-alphabet Chromatic Number encoding is faithful. -/
theorem chromaticNumberStructuredEncoding_faithful :
    chromaticNumberStructuredDecisionProblem.FaithfulEncoding where
  injective := chromaticNumberStructuredEncodedType_encode_injective

theorem chromaticNumberStructuredEncoding_predicateRespects :
    chromaticNumberStructuredDecisionProblem.PredicateRespectsEncoding :=
  chromaticNumberStructuredEncoding_faithful.predicateRespects

theorem chromaticNumberStructuredEncoding_accepts_encode_iff (I : ChromaticNumberInput) :
    chromaticNumberStructuredDecisionProblem.toEncodedLanguage.accepts
        (chromaticNumberStructuredEncodedType.encode I) ↔
      ChromaticNumber I :=
  chromaticNumberStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-! ### Structured finite-alphabet transport bounds -/

theorem variableEdgesFor_length (i : Nat) :
    (variableEdgesFor i).length = 3 := by
  simp [variableEdgesFor]

theorem variableEdges_length (n : Nat) :
    (variableEdges n).length = 3 * n := by
  unfold variableEdges
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [List.range_succ, List.flatMap_append, variableEdgesFor_length, ih]
      omega

theorem clauseGadgetEdges_length (n j : Nat) (l₀ l₁ l₂ : SAT.Literal) :
    (clauseGadgetEdges n j l₀ l₁ l₂).length = 9 := by
  simp [clauseGadgetEdges]

theorem clauseEdgesFor_length_le (n j : Nat) (c : SAT.Clause) :
    (clauseEdgesFor n j c).length ≤ 9 := by
  unfold clauseEdgesFor
  cases h : paddedClause c with
  | none =>
      simp
  | some triple =>
      rcases triple with ⟨l₀, l₁, l₂⟩
      simp [clauseGadgetEdges_length]

theorem clauseEdgesFrom_length_le (n j : Nat) :
    ∀ cs : List SAT.Clause, (clauseEdgesFrom n j cs).length ≤ 9 * cs.length
  | [] => by simp [clauseEdgesFrom]
  | c :: cs => by
      have hHead := clauseEdgesFor_length_le n j c
      have hTail := clauseEdgesFrom_length_le n (j + 1) cs
      simp [clauseEdgesFrom]
      omega

theorem textbookEdges_length_le (φ : SAT.ThreeCNF) :
    (textbookEdges φ).length ≤
      3 + 3 * Clique.cnfVarBound φ.clauses + 9 * φ.clauses.length := by
  have hVar := variableEdges_length (Clique.cnfVarBound φ.clauses)
  have hClause := clauseEdgesFrom_length_le (Clique.cnfVarBound φ.clauses) 0 φ.clauses
  simp [textbookEdges, paletteEdges, hVar]
  omega

theorem edgeStructured_inputSize_le_of_lt {B : Nat} {e : Nat × Nat}
    (h₁ : e.1 < B) (h₂ : e.2 < B) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * B + 1 := by
  cases e
  simp [edgeStructuredEncodedType]
  omega

theorem edgeStructured_inputSize_le_of_textbookVertexCount {n m : Nat} {e : Nat × Nat}
    (h₁ : e.1 < textbookVertexCount n m) (h₂ : e.2 < textbookVertexCount n m) :
    edgeStructuredEncodedType.inputSize e ≤ 2 * textbookVertexCount n m + 1 :=
  edgeStructured_inputSize_le_of_lt h₁ h₂

theorem variableEdgesFor_endpoints_lt {n m i : Nat} (hi : i < n) {e : Nat × Nat}
    (he : e ∈ variableEdgesFor i) :
    e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
  simp [variableEdgesFor] at he
  rcases he with rfl | rfl | rfl
  · constructor
    · simp [posVertex, textbookVertexCount, variableLimit]
      omega
    · simp [baseVertex, textbookVertexCount, variableLimit]
  · constructor
    · simp [negVertex, textbookVertexCount, variableLimit]
      omega
    · simp [baseVertex, textbookVertexCount, variableLimit]
  · constructor
    · simp [posVertex, textbookVertexCount, variableLimit]
      omega
    · simp [negVertex, textbookVertexCount, variableLimit]
      omega

theorem paletteEdges_endpoints_lt {n m : Nat} {e : Nat × Nat}
    (he : e ∈ paletteEdges) :
    e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
  simp [paletteEdges] at he
  rcases he with rfl | rfl | rfl
  · constructor
    · simp [baseVertex, textbookVertexCount, variableLimit]
    · simp [trueVertex, textbookVertexCount, variableLimit]
      omega
  · constructor
    · simp [baseVertex, textbookVertexCount, variableLimit]
    · simp [falseVertex, textbookVertexCount, variableLimit]
      omega
  · constructor
    · simp [trueVertex, textbookVertexCount, variableLimit]
      omega
    · simp [falseVertex, textbookVertexCount, variableLimit]
      omega

theorem variableEdges_endpoints_lt {n m : Nat} {e : Nat × Nat}
    (he : e ∈ variableEdges n) :
    e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
  rcases List.mem_flatMap.mp he with ⟨i, hi, hiEdge⟩
  exact variableEdgesFor_endpoints_lt (n := n) (m := m) (i := i) (by simpa using hi) hiEdge

theorem clauseEdgesFor_endpoints_lt {n m j : Nat} {c : SAT.Clause} {e : Nat × Nat}
    (hj : j < m)
    (hBound : ∀ l ∈ c, l.var < n)
    (he : e ∈ clauseEdgesFor n j c) :
    e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
  unfold clauseEdgesFor at he
  cases hp : paddedClause c with
  | none =>
      simp [hp] at he
      subst e
      constructor <;> simp [baseVertex, textbookVertexCount, variableLimit]
  | some triple =>
      rcases triple with ⟨l₀, l₁, l₂⟩
      have h₀ : l₀.var < n := hBound l₀ (paddedClause_left_mem hp)
      have h₁ : l₁.var < n := hBound l₁ (paddedClause_middle_mem hp)
      have h₂ : l₂.var < n := hBound l₂ (paddedClause_right_mem hp)
      simp [hp, clauseGadgetEdges] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨clauseA0_lt_textbookVertexCount hj, clauseA1_lt_textbookVertexCount hj⟩
      · exact ⟨clauseA0_lt_textbookVertexCount hj, clauseA2_lt_textbookVertexCount hj⟩
      · exact ⟨clauseA3_lt_textbookVertexCount hj, by
          simp [trueVertex, textbookVertexCount, variableLimit]
          omega⟩
      · exact ⟨clauseA1_lt_textbookVertexCount hj, by
          simp [trueVertex, textbookVertexCount, variableLimit]
          omega⟩
      · exact ⟨clauseA2_lt_textbookVertexCount hj, clauseA3_lt_textbookVertexCount hj⟩
      · exact ⟨literalVertex_lt_textbookVertexCount h₀, clauseA2_lt_textbookVertexCount hj⟩
      · exact ⟨literalVertex_lt_textbookVertexCount h₀, clauseA3_lt_textbookVertexCount hj⟩
      · exact ⟨literalVertex_lt_textbookVertexCount h₁, clauseA0_lt_textbookVertexCount hj⟩
      · exact ⟨literalVertex_lt_textbookVertexCount h₂, clauseA1_lt_textbookVertexCount hj⟩

theorem clauseEdgesFrom_endpoints_lt {n m j : Nat} {cs : List SAT.Clause} {e : Nat × Nat}
    (hIndex : j + cs.length ≤ m)
    (hBound : ∀ c ∈ cs, ∀ l ∈ c, l.var < n)
    (he : e ∈ clauseEdgesFrom n j cs) :
    e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
  induction cs generalizing j with
  | nil =>
      simp [clauseEdgesFrom] at he
  | cons c cs ih =>
      simp [clauseEdgesFrom] at he
      rcases he with heHead | heTail
      · have hj : j < m := by
          have hpos : 0 < (c :: cs).length := by simp
          omega
        exact clauseEdgesFor_endpoints_lt hj (fun l hl => hBound c (by simp) l hl) heHead
      · exact ih (j := j + 1)
          (by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIndex)
          (fun d hd l hl => hBound d (by simp [hd]) l hl)
          heTail

theorem textbookEdges_endpoints_lt {φ : SAT.ThreeCNF} {e : Nat × Nat}
    (he : e ∈ textbookEdges φ) :
    e.1 < (textbookMap φ).graph.vertices ∧ e.2 < (textbookMap φ).graph.vertices := by
  let n := Clique.cnfVarBound φ.clauses
  let m := φ.clauses.length
  have hBound : ∀ c ∈ φ.clauses, ∀ l ∈ c, l.var < n := by
    intro c hc l hl
    simpa [n] using Clique.var_lt_cnfVarBound_of_mem hc hl
  simp [textbookEdges] at he
  have hEndpoints :
      e.1 < textbookVertexCount n m ∧ e.2 < textbookVertexCount n m := by
    rcases he with hePalette | heVar | heClause
    · exact paletteEdges_endpoints_lt (n := n) (m := m) hePalette
    · exact variableEdges_endpoints_lt (n := n) (m := m) heVar
    · exact clauseEdgesFrom_endpoints_lt
        (n := n) (m := m) (j := 0) (cs := φ.clauses)
        (by simp [m])
        hBound
        heClause
  simpa [textbookMap, n, m] using hEndpoints

theorem edgeStructured_inputSize_le_of_mem_textbookEdges {φ : SAT.ThreeCNF}
    {e : Nat × Nat} (he : e ∈ textbookEdges φ) :
    edgeStructuredEncodedType.inputSize e ≤
      2 * (textbookMap φ).graph.vertices + 1 := by
  have hEndpoints := textbookEdges_endpoints_lt he
  exact edgeStructured_inputSize_le_of_lt hEndpoints.1 hEndpoints.2

theorem textbookEdges_structured_inputSize_le (φ : SAT.ThreeCNF) :
    edgeListStructuredEncodedType.inputSize (textbookEdges φ) ≤
      (3 + 3 * Clique.cnfVarBound φ.clauses + 9 * φ.clauses.length) *
        (2 * (textbookMap φ).graph.vertices + 2) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (textbookEdges φ) (2 * (textbookMap φ).graph.vertices + 1)
      (by
        intro e he
        exact edgeStructured_inputSize_le_of_mem_textbookEdges he)
  have hLen := textbookEdges_length_le φ
  exact hList.trans (by
    have hMul :=
      Nat.mul_le_mul_right (2 * (textbookMap φ).graph.vertices + 2) hLen
    simpa [edgeListStructuredEncodedType, Nat.add_assoc] using hMul)

theorem chromaticNumberStructured_inputSize_eq (I : ChromaticNumberInput) :
    chromaticNumberStructuredEncodedType.inputSize I =
      graphStructuredEncodedType.inputSize I.graph + I.colors + 2 := by
  change chromaticNumberTupleStructuredEncodedType.inputSize (I.graph, I.colors) =
    graphStructuredEncodedType.inputSize I.graph + I.colors + 2
  simp [chromaticNumberTupleStructuredEncodedType]
  omega

theorem clauseVarBound_eq_satClauseVarBound (c : SAT.Clause) :
    Clique.clauseVarBound c = SAT.Clause.varBound c := by
  induction c with
  | nil =>
      simp [Clique.clauseVarBound, SAT.Clause.varBound]
  | cons l ls ih =>
      simp [Clique.clauseVarBound, SAT.Clause.varBound, ih]

theorem cnfVarBound_eq_satCNFVarBound (φ : SAT.CNF) :
    Clique.cnfVarBound φ = SAT.CNF.varBound φ := by
  induction φ with
  | nil =>
      simp [Clique.cnfVarBound, SAT.CNF.varBound]
  | cons c cs ih =>
      simp [Clique.cnfVarBound, SAT.CNF.varBound, ih, clauseVarBound_eq_satClauseVarBound c]

theorem cnfVarBound_le_threeCNFStructured_inputSize (φ : SAT.ThreeCNF) :
    Clique.cnfVarBound φ.clauses ≤ threeCNFStructuredEncodedType.inputSize φ := by
  rw [cnfVarBound_eq_satCNFVarBound]
  have h :=
    ComplexityReduction.Karp21.cnfVarBound_le_cnfStructured_inputSize φ.clauses
  simpa [threeCNFStructuredEncodedType, EncodedType.inputSize] using h

theorem chromaticNumberStructured_inputSize_textbookMap_le_threeSAT_poly
    (φ : SAT.ThreeCNF) :
    chromaticNumberStructuredEncodedType.inputSize (textbookMap φ) ≤
      1000 * (threeCNFStructuredEncodedType.inputSize φ) ^ 3 + 1000 := by
  let S := threeCNFStructuredEncodedType.inputSize φ
  let N := Clique.cnfVarBound φ.clauses
  let C := φ.clauses.length
  let V := textbookVertexCount N C
  let L := 3 + 3 * N + 9 * C
  have hN : N ≤ S := by
    simpa [S, N] using cnfVarBound_le_threeCNFStructured_inputSize φ
  have hC : C ≤ S := by
    simpa [S, C] using Clique.threeCNFStructured_inputSize_ge_clauses_length φ
  have hV : V ≤ 6 * S + 3 := by
    simp [V, textbookVertexCount, variableLimit, N, C]
    omega
  have hL : L ≤ 12 * S + 3 := by
    simp [L, N, C]
    omega
  have hEdges := textbookEdges_structured_inputSize_le φ
  have hBase :
      chromaticNumberStructuredEncodedType.inputSize (textbookMap φ) ≤
        V + L * (2 * V + 2) + 9 := by
    calc
      chromaticNumberStructuredEncodedType.inputSize (textbookMap φ)
          = graphStructuredEncodedType.inputSize (textbookMap φ).graph +
              (textbookMap φ).colors + 2 := chromaticNumberStructured_inputSize_eq (textbookMap φ)
      _ ≤ V + L * (2 * V + 2) + 9 := by
            rw [Clique.graphStructured_inputSize_eq]
            have hEdges' :
                edgeListStructuredEncodedType.inputSize (textbookEdges φ) ≤
                  L * (2 * V + 2) := by
              simpa [V, L, N, C, textbookMap, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hEdges
            have hVertices : (textbookMap φ).graph.vertices = V := by
              simp [textbookMap, V, N, C]
            have hGraphEdges :
                edgeListStructuredEncodedType.inputSize (textbookMap φ).graph.edges =
                  edgeListStructuredEncodedType.inputSize (textbookEdges φ) := by
              simp [textbookMap]
            have hColors : (textbookMap φ).colors = 3 := by
              simp [textbookMap]
            rw [hVertices, hGraphEdges, hColors]
            omega
  have hFactor : 2 * V + 2 ≤ 2 * (6 * S + 3) + 2 := by
    omega
  have hMul : L * (2 * V + 2) ≤ (12 * S + 3) * (2 * (6 * S + 3) + 2) :=
    Nat.mul_le_mul hL hFactor
  have hPolyBase :
      V + L * (2 * V + 2) + 9 ≤
        (6 * S + 3) + (12 * S + 3) * (2 * (6 * S + 3) + 2) + 9 := by
    omega
  calc
    chromaticNumberStructuredEncodedType.inputSize (textbookMap φ)
        ≤ V + L * (2 * V + 2) + 9 := hBase
    _ ≤ (6 * S + 3) + (12 * S + 3) * (2 * (6 * S + 3) + 2) + 9 := hPolyBase
    _ ≤ 1000 * S ^ 3 + 1000 := by
          cases S with
          | zero =>
              norm_num
          | succ S =>
              ring_nf
              omega

theorem threeSATToChromaticNumberStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun φ : SAT.ThreeCNF => threeCNFStructuredEncodedType.inputSize φ)
      (fun I : ChromaticNumberInput => chromaticNumberStructuredEncodedType.inputSize I)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 3 1000 1000 ?_
  intro φ
  exact chromaticNumberStructured_inputSize_textbookMap_le_threeSAT_poly φ

noncomputable def threeSATToChromaticNumberStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      threeSATStructuredDecisionProblem chromaticNumberStructuredDecisionProblem where
  f :=
    { toFun := textbookMap
      polytime :=
        CostedPolyTimeMap.of_costed
          (CostedMap.of_encodedPolynomialSizeBound
            threeSATToChromaticNumberStructured_polynomialSizeBound) }
  correct := by
    intro φ
    simpa [threeSATStructuredDecisionProblem, chromaticNumberStructuredDecisionProblem]
      using textbookMap_correct φ

/-- Local NP-completeness of Chromatic Number via local 3SAT. -/
theorem chromaticNumberNPComplete :
    NPCompleteEnc CostedPolyTimeModel chromaticNumberDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    chromaticNumberDecisionProblem
    threeSATToChromaticNumberKarpReduction
    chromaticNumberInNP

/-- Local NP-completeness of Chromatic Number via the P15q textbook coloring route. -/
theorem chromaticNumber_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel chromaticNumberDecisionProblem :=
  Targets.npComplete_of_localThreeSAT_karp
    chromaticNumberDecisionProblem
    threeSATToChromaticNumber_textbookKarpReduction
    chromaticNumberInNP

end ChromaticNumber
end Karp21
end ComplexityReduction
