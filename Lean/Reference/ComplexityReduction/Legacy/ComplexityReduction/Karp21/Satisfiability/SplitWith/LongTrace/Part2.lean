import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.LongTrace.Part1

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

/--
The trace-rebuilding fold step is direct TM-backed.  This is the step witness
needed by a future bounded fold over the already parsed long-step trace.
-/

noncomputable def splitWithTraceFoldStepTMBackedMap :
    TMBackedCostedMap
      splitWithTraceFoldStepInputEncodedType cnfStructuredEncodedType
      splitWithTraceFoldStep where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceFoldStepInputEncodedType)
      (Y := cnfStructuredEncodedType)
      (LinearSizeBound.intro_with 1 10 (by
        intro p
        rcases p with ⟨acc, core⟩
        rcases core with ⟨next, lits⟩
        rcases lits with ⟨l₁, l₂⟩
        change
          (EncodedType.list clauseStructuredEncodedType).inputSize
              ([l₁, l₂, SAT.Clause.posAux next] :: acc) ≤
            1 * EncodedType.inputSize
                (EncodedType.prod cnfStructuredEncodedType splitWithLongHeadCoreEncodedType)
                (acc, (next, (l₁, l₂))) + 10
        rw [EncodedType.inputSize_list_cons]
        change
          (EncodedType.list literalStructuredEncodedType).inputSize
              [l₁, l₂, SAT.Clause.posAux next] + 1 +
              (EncodedType.list clauseStructuredEncodedType).inputSize acc ≤
            1 * EncodedType.inputSize
                (EncodedType.prod cnfStructuredEncodedType splitWithLongHeadCoreEncodedType)
                (acc, (next, (l₁, l₂))) + 10
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        simp [splitWithLongHeadCoreEncodedType, cnfStructuredEncodedType,
          clauseStructuredEncodedType, literalStructured_inputSize_eq, SAT.Clause.posAux]
        omega))
  tm_polytime := by
    let X := splitWithTraceFoldStepInputEncodedType
    have hAcc :
        TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst cnfStructuredEncodedType splitWithLongHeadCoreEncodedType
    have hHead :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd cnfStructuredEncodedType splitWithLongHeadCoreEncodedType
    have hSwap :
        TMPolyTimeMap X splitWithLongHeadInputEncodedType
          (fun p : X.Carrier => (p.2, p.1)) :=
      TMPolyTimeMap.prod_mk hHead hAcc
    have hStep :
        TMPolyTimeMap X cnfStructuredEncodedType splitWithTraceFoldStep :=
      TMPolyTimeMap.comp splitWithLongHeadConsTMBackedMap.tm_polytime hSwap
    simpa [X, splitWithTraceFoldStep, splitWithLongHeadInputEncodedType, Function.comp]
      using hStep

/-- Definitional decomposition of one long-clause splitter step. -/
theorem splitWith_eq_longHeadCons_of_long
    (next : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause) :
    SAT.Clause.splitWith next (l₁ :: l₂ :: l₃ :: l₄ :: rest) =
      splitWithLongHeadCons
        ((next, (l₁, l₂)),
          SAT.Clause.splitWith (next + 1)
            (splitWithLongTailClause (next, (l₃, (l₄, rest))))) := by
  simp [SAT.Clause.splitWith, splitWithLongHeadCons, splitWithLongHeadClause,
    splitWithLongTailClause]

/-- Long-branch splitter equation phrased over the decomposed recursive-input builder. -/
theorem splitWith_eq_longHeadCons_of_decomposed
    (p : splitWithLongDecomposedInputEncodedType.Carrier) :
    SAT.Clause.splitWith p.1.1 (p.1.2.1 :: p.1.2.2 :: p.2.1 :: p.2.2.1 :: p.2.2.2) =
      splitWithLongHeadCons
        (p.1,
          SAT.Clause.splitWith (splitWithLongRecursiveInput p).1
            (splitWithLongRecursiveInput p).2) := by
  rcases p with ⟨head, tail⟩
  rcases head with ⟨next, headLits⟩
  rcases headLits with ⟨l₁, l₂⟩
  rcases tail with ⟨l₃, l₄Rest⟩
  rcases l₄Rest with ⟨l₄, rest⟩
  simpa [splitWithLongRecursiveInput] using
    splitWith_eq_longHeadCons_of_long next l₁ l₂ l₃ l₄ rest

/--
Semantic long-branch parser for the clause splitter.  The future delimiter TM
runner must implement this branch test over `clauseStructuredEncodedType`;
this definition records the exact Lean-side branch contract.
-/
def splitWithLongDecomposition
    (p : splitWithInputEncodedType.Carrier) :
    Option splitWithLongDecomposedInputEncodedType.Carrier :=
  match p with
  | (next, l1 :: l2 :: l3 :: l4 :: rest) =>
      some ((next, (l1, l2)), (l3, (l4, rest)))
  | _ => none

theorem splitWithLongDecomposition_longInput_eq_some
    (p : splitWithLongInputEncodedType.Carrier) :
    splitWithLongDecomposition p.1 = some (splitWithLongInputDecomposition p) := by
  rcases p with ⟨p, hp⟩
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp at hp
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp at hp
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp at hp
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp at hp
              | cons l₄ rest =>
                  rw [splitWithLongInputDecomposition_cons next l₁ l₂ l₃ l₄ rest hp]
                  simp [splitWithLongDecomposition]
                  rfl

theorem splitWithLongDecomposition_none_length_le_three
    (p : splitWithInputEncodedType.Carrier)
    (h : splitWithLongDecomposition p = none) :
    p.2.length ≤ 3 := by
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp
  | cons l1 c1 =>
      cases c1 with
      | nil =>
          simp
      | cons l2 c2 =>
          cases c2 with
          | nil =>
              simp
          | cons l3 c3 =>
              cases c3 with
              | nil =>
                  simp
              | cons l4 rest =>
                  simp [splitWithLongDecomposition] at h

theorem splitWithLongDecomposition_eq_none_of_length_le_three
    (p : splitWithInputEncodedType.Carrier)
    (h : p.2.length ≤ 3) :
    splitWithLongDecomposition p = none := by
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp [splitWithLongDecomposition]
  | cons l1 c1 =>
      cases c1 with
      | nil =>
          simp [splitWithLongDecomposition]
      | cons l2 c2 =>
          cases c2 with
          | nil =>
              simp [splitWithLongDecomposition]
          | cons l3 c3 =>
              cases c3 with
              | nil =>
                  simp [splitWithLongDecomposition]
              | cons l4 rest =>
                  simp at h
                  omega

theorem splitWithLongDecomposition_eq_none_iff_length_le_three
    (p : splitWithInputEncodedType.Carrier) :
    splitWithLongDecomposition p = none ↔ p.2.length ≤ 3 :=
  ⟨splitWithLongDecomposition_none_length_le_three p,
    splitWithLongDecomposition_eq_none_of_length_le_three p⟩

theorem splitWithIsShort_eq_true_iff_decomposition_none
    (p : splitWithInputEncodedType.Carrier) :
    splitWithIsShort p = true ↔ splitWithLongDecomposition p = none := by
  constructor
  · intro h
    have hLen : p.2.length ≤ 3 :=
      of_decide_eq_true (by simpa [splitWithIsShort] using h)
    exact splitWithLongDecomposition_eq_none_of_length_le_three p hLen
  · intro h
    have hLen := splitWithLongDecomposition_none_length_le_three p h
    simp [splitWithIsShort, hLen]

theorem splitWithBranchDecision_short_iff_decomposition_none
    (p : splitWithInputEncodedType.Carrier) :
    (splitWithBranchDecision p).1 = true ↔ splitWithLongDecomposition p = none := by
  simpa [splitWithBranchDecision] using
    splitWithIsShort_eq_true_iff_decomposition_none p

/--
Branch decisions whose Boolean agrees with the delimiter-scanned predicate.
This subtype keeps exactly the branch-decision encoding.
-/
def splitWithCheckedBranchDecisionEncodedType : EncodedType where
  Carrier := { q : splitWithBranchDecisionEncodedType.Carrier // q.1 = splitWithIsShort q.2 }
  Symbol := splitWithBranchDecisionEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun q => splitWithBranchDecisionEncodedType.encode q.1

/-- The checked branch-decision package produced from a splitter input. -/
def splitWithCheckedBranchDecision
    (p : splitWithInputEncodedType.Carrier) :
    splitWithCheckedBranchDecisionEncodedType.Carrier :=
  ⟨splitWithBranchDecision p, by rfl⟩

theorem splitWithCheckedBranchDecision_inputSize_le
    (p : splitWithInputEncodedType.Carrier) :
    splitWithCheckedBranchDecisionEncodedType.inputSize
        (splitWithCheckedBranchDecision p) ≤
      splitWithInputEncodedType.inputSize p + 2 := by
  simpa [splitWithCheckedBranchDecisionEncodedType, splitWithCheckedBranchDecision,
    EncodedType.inputSize] using splitWithBranchDecision_inputSize_le p

/--
The checked branch-decision package has the same output encoding as
`splitWithBranchDecision`, so it reuses that direct TM-backed computation.
-/
noncomputable def splitWithCheckedBranchDecisionTMBackedMap :
    TMBackedCostedMap
      splitWithInputEncodedType
      splitWithCheckedBranchDecisionEncodedType
      splitWithCheckedBranchDecision where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithInputEncodedType)
      (Y := splitWithCheckedBranchDecisionEncodedType)
      (LinearSizeBound.intro_with 1 2 (by
        intro p
        have h := splitWithCheckedBranchDecision_inputSize_le p
        omega))
  tm_polytime := by
    rcases splitWithBranchDecisionTMBackedMap.tm_polytime with ⟨h⟩
    exact
      ⟨{ tm := h.tm
         inputAlphabet := h.inputAlphabet
         outputAlphabet := h.outputAlphabet
         time := h.time
         outputsFun := by
          intro p
          simpa [splitWithCheckedBranchDecisionEncodedType,
            splitWithCheckedBranchDecision] using h.outputsFun p }⟩

theorem splitWithLongDecomposition_some_eq
    (p : splitWithInputEncodedType.Carrier)
    (d : splitWithLongDecomposedInputEncodedType.Carrier)
    (h : splitWithLongDecomposition p = some d) :
    p = (d.1.1, d.1.2.1 :: d.1.2.2 :: d.2.1 :: d.2.2.1 :: d.2.2.2) := by
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp [splitWithLongDecomposition] at h
  | cons l1 c1 =>
      cases c1 with
      | nil =>
          simp [splitWithLongDecomposition] at h
      | cons l2 c2 =>
          cases c2 with
          | nil =>
              simp [splitWithLongDecomposition] at h
          | cons l3 c3 =>
              cases c3 with
              | nil =>
                  simp [splitWithLongDecomposition] at h
              | cons l4 rest =>
                  simp [splitWithLongDecomposition] at h
                  subst d
                  rfl

theorem splitWithLongDecomposition_recursive_length_lt
    (p : splitWithInputEncodedType.Carrier)
    (d : splitWithLongDecomposedInputEncodedType.Carrier)
    (h : splitWithLongDecomposition p = some d) :
    (splitWithLongRecursiveInput d).2.length < p.2.length := by
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp [splitWithLongDecomposition] at h
  | cons l1 c1 =>
      cases c1 with
      | nil =>
          simp [splitWithLongDecomposition] at h
      | cons l2 c2 =>
          cases c2 with
          | nil =>
              simp [splitWithLongDecomposition] at h
          | cons l3 c3 =>
              cases c3 with
              | nil =>
                  simp [splitWithLongDecomposition] at h
              | cons l4 rest =>
                  simp [splitWithLongDecomposition] at h
                  subst d
                  change rest.length + 3 < rest.length + 4
                  omega

theorem splitWith_eq_singleton_of_decomposition_none
    (p : splitWithInputEncodedType.Carrier)
    (h : splitWithLongDecomposition p = none) :
    SAT.Clause.splitWith p.1 p.2 = [p.2] := by
  exact splitWith_eq_clauseSingleton_of_length_le_three p.1 p.2
    (splitWithLongDecomposition_none_length_le_three p h)

theorem splitWith_eq_longHeadCons_of_decomposition_some
    (p : splitWithInputEncodedType.Carrier)
    (d : splitWithLongDecomposedInputEncodedType.Carrier)
    (h : splitWithLongDecomposition p = some d) :
    SAT.Clause.splitWith p.1 p.2 =
      splitWithLongHeadCons
        (d.1,
          SAT.Clause.splitWith (splitWithLongRecursiveInput d).1
            (splitWithLongRecursiveInput d).2) := by
  have hp := splitWithLongDecomposition_some_eq p d h
  subst p
  exact splitWith_eq_longHeadCons_of_decomposed d

/-- Trace of long-branch head clauses plus the final short clause. -/
def splitWithTrace (next : Nat) : SAT.Clause →
    List splitWithLongHeadCoreEncodedType.Carrier × SAT.Clause
  | [] => ([], [])
  | [l1] => ([], [l1])
  | [l1, l2] => ([], [l1, l2])
  | [l1, l2, l3] => ([], [l1, l2, l3])
  | l1 :: l2 :: l3 :: l4 :: rest =>
      let tail := splitWithLongTailClause (next, (l3, (l4, rest)))
      let trace := splitWithTrace (next + 1) tail
      ((next, (l1, l2)) :: trace.1, trace.2)
termination_by c => c.length
decreasing_by simp [splitWithLongTailClause]

theorem splitWithTrace_eq_longTraceStepOutput_cons
    (next : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause)
    (h : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length) :
    let out := splitWithLongTraceStepOutput
      ⟨(next, l₁ :: l₂ :: l₃ :: l₄ :: rest), h⟩
    splitWithTrace next (l₁ :: l₂ :: l₃ :: l₄ :: rest) =
      (out.1 :: (splitWithTrace out.2.1 out.2.2).1,
        (splitWithTrace out.2.1 out.2.2).2) := by
  simp [splitWithTrace, splitWithLongTraceStepOutput_cons, splitWithLongTailClause]
  rfl

/-- Rebuild the splitter CNF from the long-step trace and final short clause. -/
def splitWithTraceCNF :
    List splitWithLongHeadCoreEncodedType.Carrier → SAT.Clause → SAT.CNF
  | [], base => [base]
  | head :: heads, base => splitWithLongHeadCons (head, splitWithTraceCNF heads base)

theorem splitWithTraceCNF_eq_foldl_reverse
    (heads : List splitWithLongHeadCoreEncodedType.Carrier) (base : SAT.Clause) :
    splitWithTraceCNF heads base =
      heads.reverse.foldl (fun acc head => splitWithTraceFoldStep (acc, head)) [base] := by
  induction heads with
  | nil =>
      simp [splitWithTraceCNF]
  | cons head heads ih =>
      simp [splitWithTraceCNF, List.foldl_append, splitWithTraceFoldStep, ih]

theorem splitWithTraceCNF_eq_map_headClauses_append
    (heads : List splitWithLongHeadCoreEncodedType.Carrier) (base : SAT.Clause) :
    splitWithTraceCNF heads base =
      heads.map splitWithLongHeadCoreClause ++ [base] := by
  induction heads with
  | nil =>
      simp [splitWithTraceCNF]
  | cons head heads ih =>
      simp [splitWithTraceCNF, splitWithLongHeadCons, splitWithLongHeadClause,
        splitWithLongHeadCoreClause, ih]

/-- Trace-output input `(long-step heads, final short clause)`. -/
def splitWithTraceOutputEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.list splitWithLongHeadCoreEncodedType)
    clauseStructuredEncodedType

/-- Rebuild the full splitter CNF from the long-step trace and final base clause. -/
def splitWithTraceOutputToCNF
    (p : splitWithTraceOutputEncodedType.Carrier) : SAT.CNF :=
  (p.1.map splitWithLongHeadCoreClause : SAT.CNF) ++ ([p.2] : SAT.CNF)

theorem splitWithTraceOutputToCNF_inputSize_le
    (p : splitWithTraceOutputEncodedType.Carrier) :
    cnfStructuredEncodedType.inputSize (splitWithTraceOutputToCNF p) ≤
      10 * splitWithTraceOutputEncodedType.inputSize p + 10 := by
  rcases p with ⟨heads, base⟩
  induction heads with
  | nil =>
      change
        (EncodedType.list clauseStructuredEncodedType).inputSize
            ([base] : List clauseStructuredEncodedType.Carrier) ≤
          10 *
              (EncodedType.prod (EncodedType.list splitWithLongHeadCoreEncodedType)
                clauseStructuredEncodedType).inputSize
                (([] : List splitWithLongHeadCoreEncodedType.Carrier), base) + 10
      have hOut :=
        EncodedType.inputSize_list_cons clauseStructuredEncodedType base
          ([] : List clauseStructuredEncodedType.Carrier)
      have hNilOut := EncodedType.inputSize_list_nil clauseStructuredEncodedType
      have hNilIn := EncodedType.inputSize_list_nil splitWithLongHeadCoreEncodedType
      have hOut' :
          (EncodedType.list clauseStructuredEncodedType).inputSize
              ([base] : List clauseStructuredEncodedType.Carrier) =
            clauseStructuredEncodedType.inputSize base + 1 := by
        calc
          (EncodedType.list clauseStructuredEncodedType).inputSize
              ([base] : List clauseStructuredEncodedType.Carrier)
              = clauseStructuredEncodedType.inputSize base + 1 +
                  (EncodedType.list clauseStructuredEncodedType).inputSize
                    ([] : List clauseStructuredEncodedType.Carrier) := hOut
          _ = clauseStructuredEncodedType.inputSize base + 1 := by
                rw [hNilOut]
      rw [hOut']
      simp only [EncodedType.inputSize_prod, hNilIn]
      omega
  | cons head heads ih =>
      have hHead := splitWithLongHeadCoreClause_inputSize_le head
      change
        (EncodedType.list clauseStructuredEncodedType).inputSize
            (splitWithLongHeadCoreClause head ::
              ((heads.map splitWithLongHeadCoreClause : SAT.CNF) ++ ([base] : SAT.CNF))) ≤
          10 *
              (EncodedType.prod (EncodedType.list splitWithLongHeadCoreEncodedType)
                clauseStructuredEncodedType).inputSize (head :: heads, base) + 10
      rw [EncodedType.inputSize_list_cons]
      have ih' :
          (EncodedType.list clauseStructuredEncodedType).inputSize
              ((heads.map splitWithLongHeadCoreClause : SAT.CNF) ++ ([base] : SAT.CNF)) ≤
            10 *
                (EncodedType.prod (EncodedType.list splitWithLongHeadCoreEncodedType)
                  clauseStructuredEncodedType).inputSize (heads, base) + 10 := by
        simpa [splitWithTraceOutputToCNF, splitWithTraceOutputEncodedType,
          cnfStructuredEncodedType] using ih
      simp only [EncodedType.inputSize_prod, EncodedType.inputSize_list_cons] at ih' ⊢
      omega

/--
Direct TM-backed trace rebuilder.  This consumes an already-computed trace; the
remaining clause-runner work is to compute that trace from the source clause.
-/
noncomputable def splitWithTraceOutputToCNFTMBackedMap :
    TMBackedCostedMap
      splitWithTraceOutputEncodedType cnfStructuredEncodedType
      splitWithTraceOutputToCNF where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceOutputEncodedType)
      (Y := cnfStructuredEncodedType)
      (LinearSizeBound.intro_with 10 10 (by
        intro p
        exact splitWithTraceOutputToCNF_inputSize_le p))
  tm_polytime := by
    let X := splitWithTraceOutputEncodedType
    have hHeads :
        TMPolyTimeMap X (EncodedType.list splitWithLongHeadCoreEncodedType)
          (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst
        (EncodedType.list splitWithLongHeadCoreEncodedType)
        clauseStructuredEncodedType
    have hBase :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd
        (EncodedType.list splitWithLongHeadCoreEncodedType)
        clauseStructuredEncodedType
    have hMapped :
        TMPolyTimeMap X cnfStructuredEncodedType
          (fun p : X.Carrier => p.1.map splitWithLongHeadCoreClause) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_map splitWithLongHeadCoreClauseTMBackedMap.tm_polytime)
        hHeads
    have hBaseSingleton :
        TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => [p.2]) :=
      TMPolyTimeMap.comp clauseSingletonTMBackedMap.tm_polytime hBase
    have hPair :
        TMPolyTimeMap X
          (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
          (fun p : X.Carrier =>
            (p.1.map splitWithLongHeadCoreClause, [p.2])) :=
      TMPolyTimeMap.prod_mk hMapped hBaseSingleton
    have hAppend :
        TMPolyTimeMap X cnfStructuredEncodedType splitWithTraceOutputToCNF :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType) hPair
    simpa [X, splitWithTraceOutputToCNF, cnfStructuredEncodedType, Function.comp] using hAppend

end Karp21
end ComplexityReduction
