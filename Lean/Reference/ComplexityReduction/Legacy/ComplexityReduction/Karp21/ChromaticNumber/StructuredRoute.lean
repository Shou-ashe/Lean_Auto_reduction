import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.Part2
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

/-!
P16c direct-TM components for the structured 3SAT-to-Chromatic-Number route.

This file collects the small finite-alphabet arithmetic and tuple reifiers used
by the checked graph-gadget runners.  The final edge-list runners are kept as a
separate step so the existing P15q semantic proof remains unchanged.
-/

/-! ### Unary arithmetic primitives used by graph-gadget vertex codes -/

def natAddInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def natAddPayloadKeep : natAddInputEncodedType.Symbol → Option Bool
  | some (Sum.inl true) => some true
  | some (Sum.inr true) => some true
  | _ => none

set_option linter.unusedSimpArgs false in
theorem natAddPayload_encode_filterMap (p : Nat × Nat) :
    (natAddInputEncodedType.encode p).filterMap natAddPayloadKeep =
      unaryPayloadEncodedType.encode (p.1 + p.2) := by
  rcases p with ⟨m, n⟩
  simp [natAddInputEncodedType, EncodedType.prod, EncodedType.nat, unaryPayloadEncodedType,
    natAddPayloadKeep, List.filterMap_append, List.replicate_append_replicate]

theorem natAdd_tm_polytime :
    TMPolyTimeMap
      natAddInputEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) := by
  have hPayload :
      TMPolyTimeMap
        natAddInputEncodedType
        unaryPayloadEncodedType
        (fun p : Nat × Nat => p.1 + p.2) :=
    (TMBackedCostedMap.symbolFilterMap
      natAddInputEncodedType unaryPayloadEncodedType
      (fun p : Nat × Nat => p.1 + p.2)
      natAddPayloadKeep
      (fun p => (natAddPayload_encode_filterMap p).symm)).tm_polytime
  have hComp :=
    TMPolyTimeMap.comp unaryPayloadToNatTMBackedMap.tm_polytime hPayload
  simpa [Function.comp] using hComp

noncomputable def natAddTMBackedMap :
    TMBackedCostedMap
      natAddInputEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := natAddInputEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro p
        have hPayloadLen :=
          List.length_filterMap_le natAddPayloadKeep (natAddInputEncodedType.encode p)
        rw [natAddPayload_encode_filterMap p] at hPayloadLen
        simp [unaryPayloadEncodedType, EncodedType.inputSize, EncodedType.nat] at hPayloadLen ⊢
        omega))
  tm_polytime := natAdd_tm_polytime

def natDouble (n : Nat) : Nat :=
  n + n

theorem natDouble_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat natDouble := by
  have hPair := TMPolyTimeMap.prod_diag EncodedType.nat
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hPair
  simpa [Function.comp, natDouble] using hComp

noncomputable def natDoubleTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.nat natDouble where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 2 1 (by
        intro n
        simp [natDouble, EncodedType.inputSize, EncodedType.nat]
        omega))
  tm_polytime := natDouble_tm_polytime

def natQuadruple (n : Nat) : Nat :=
  natDouble (natDouble n)

theorem natQuadruple_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat natQuadruple := by
  have hComp := TMPolyTimeMap.comp natDouble_tm_polytime natDouble_tm_polytime
  simpa [Function.comp, natQuadruple] using hComp

noncomputable def natQuadrupleTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.nat natQuadruple where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 4 1 (by
        intro n
        simp [natQuadruple, natDouble, EncodedType.inputSize, EncodedType.nat]
        omega))
  tm_polytime := natQuadruple_tm_polytime

theorem natPlusThree_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n + 3) := by
  have h₁ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime (TMPolyTimeMap.id EncodedType.nat)
  have h₂ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₁
  have h₃ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₂
  simpa [Function.comp] using h₃

noncomputable def natPlusThreeTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.nat (fun n : Nat => n + 3) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 3 (by
        intro n
        simp [EncodedType.inputSize, EncodedType.nat]))
  tm_polytime := natPlusThree_tm_polytime

namespace ChromaticNumber

/-! ### Tuple reifiers and vertex-code maps -/

def chromaticNumberTupleToChromaticNumberInput
    (p : chromaticNumberTupleStructuredEncodedType.Carrier) :
    ChromaticNumberInput where
  graph := p.1
  colors := p.2

theorem chromaticNumberTupleToChromaticNumberInput_encode
    (p : chromaticNumberTupleStructuredEncodedType.Carrier) :
    chromaticNumberStructuredEncodedType.encode (chromaticNumberTupleToChromaticNumberInput p) =
      chromaticNumberTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, colors⟩
  rfl

noncomputable def chromaticNumberTupleToChromaticNumberInputTMBackedMap :
    TMBackedCostedMap
      chromaticNumberTupleStructuredEncodedType
      chromaticNumberStructuredEncodedType
      chromaticNumberTupleToChromaticNumberInput :=
  TMBackedCostedMap.ofEncodingEquiv
    chromaticNumberTupleStructuredEncodedType
    chromaticNumberStructuredEncodedType
    chromaticNumberTupleToChromaticNumberInput
    (Equiv.refl chromaticNumberTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change
        chromaticNumberStructuredEncodedType.encode
            (chromaticNumberTupleToChromaticNumberInput p) =
          (chromaticNumberTupleStructuredEncodedType.encode p).map id
      simp [chromaticNumberTupleToChromaticNumberInput_encode])

theorem posVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat posVertex := by
  have h₀ := natDouble_tm_polytime
  have h₁ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₀
  have h₂ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₁
  have h₃ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₂
  convert h₃ using 1
  funext i
  simp [Function.comp, posVertex, natDouble]
  omega

theorem negVertex_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat negVertex := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime posVertex_tm_polytime
  simpa [Function.comp, negVertex, posVertex] using hComp

theorem literalVertex_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType EncodedType.nat literalVertex := by
  have hVar :
      TMPolyTimeMap literalStructuredEncodedType EncodedType.nat SAT.Literal.var :=
    Clique.literal_var_tm_polytime
  have hNeg :
      TMPolyTimeMap literalStructuredEncodedType EncodedType.bool SAT.Literal.neg :=
    Clique.literal_neg_tm_polytime
  have hBranchInput :
      TMPolyTimeMap
        literalStructuredEncodedType
        (EncodedType.prod EncodedType.bool EncodedType.nat)
        (fun l : SAT.Literal => (l.neg, l.var)) :=
    TMPolyTimeMap.prod_mk hNeg hVar
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool EncodedType.nat)
        EncodedType.nat
        (fun p : Bool × Nat =>
          match p.1 with
          | true => negVertex p.2
          | false => posVertex p.2) :=
    Clique.boolProduct_dispatch_tm_polytime
      EncodedType.nat EncodedType.nat
      (fFalse := posVertex)
      (fTrue := negVertex)
      posVertex_tm_polytime
      negVertex_tm_polytime
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext l
  cases l with
  | mk var neg =>
      cases neg <;> simp [Function.comp, literalVertex]

def textbookVertexCountComponents (p : Nat × Nat) : Nat :=
  textbookVertexCount p.1 p.2

theorem textbookVertexCountComponents_tm_polytime :
    TMPolyTimeMap
      natAddInputEncodedType
      EncodedType.nat
      textbookVertexCountComponents := by
  let X := natAddInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X, natAddInputEncodedType] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hM : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X, natAddInputEncodedType] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hN2 : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => natDouble p.1) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hM2 : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => natDouble p.2) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hM
    simpa [Function.comp, X] using hComp
  have hM4 : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => natDouble (natDouble p.2)) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hM2
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat => (natDouble p.1, natDouble (natDouble p.2))) :=
    TMPolyTimeMap.prod_mk hN2 hM4
  have hAdd :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Nat × Nat => natDouble p.1 + natDouble (natDouble p.2)) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hPair
    simpa [Function.comp, X] using hComp
  have h₁ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAdd
  have h₂ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₁
  have h₃ := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime h₂
  convert h₃ using 1
  funext p
  rcases p with ⟨n, m⟩
  simp [Function.comp, textbookVertexCountComponents, textbookVertexCount,
    variableLimit, natDouble]
  omega

noncomputable def textbookVertexCountComponentsTMBackedMap :
    TMBackedCostedMap
      natAddInputEncodedType
      EncodedType.nat
      textbookVertexCountComponents where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := natAddInputEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 6 5 (by
        intro p
        rcases p with ⟨n, m⟩
        simp [textbookVertexCountComponents, textbookVertexCount, variableLimit,
          natAddInputEncodedType, EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
        omega))
  tm_polytime := textbookVertexCountComponents_tm_polytime

theorem variableLimit_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat variableLimit := by
  have hComp := TMPolyTimeMap.comp natPlusThree_tm_polytime natDouble_tm_polytime
  convert hComp using 1
  funext n
  simp [Function.comp, variableLimit, natDouble]
  omega

noncomputable def variableLimitTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.nat variableLimit where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 2 3 (by
        intro n
        simp [variableLimit, EncodedType.inputSize, EncodedType.nat]
        omega))
  tm_polytime := variableLimit_tm_polytime

def clauseBaseComponents (p : Nat × Nat) : Nat :=
  clauseBase p.1 p.2

theorem clauseBaseComponents_tm_polytime :
    TMPolyTimeMap natAddInputEncodedType EncodedType.nat clauseBaseComponents := by
  let X := natAddInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X, natAddInputEncodedType] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X, natAddInputEncodedType] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hLimit : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => variableLimit p.1) := by
    have hComp := TMPolyTimeMap.comp variableLimit_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hQuad : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => natQuadruple p.2) := by
    have hComp := TMPolyTimeMap.comp natQuadruple_tm_polytime hJ
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat => (variableLimit p.1, natQuadruple p.2)) :=
    TMPolyTimeMap.prod_mk hLimit hQuad
  have hAdd := TMPolyTimeMap.comp natAdd_tm_polytime hPair
  convert hAdd using 1
  funext p
  rcases p with ⟨n, j⟩
  simp [Function.comp, clauseBaseComponents, clauseBase, natQuadruple, natDouble]
  omega

noncomputable def clauseBaseComponentsTMBackedMap :
    TMBackedCostedMap natAddInputEncodedType EncodedType.nat clauseBaseComponents where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := natAddInputEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 4 8 (by
        intro p
        rcases p with ⟨n, j⟩
        simp [clauseBaseComponents, clauseBase, variableLimit, natAddInputEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.nat]
        omega))
  tm_polytime := clauseBaseComponents_tm_polytime

def clauseA0Components (p : Nat × Nat) : Nat :=
  clauseA0 p.1 p.2

def clauseA1Components (p : Nat × Nat) : Nat :=
  clauseA1 p.1 p.2

def clauseA2Components (p : Nat × Nat) : Nat :=
  clauseA2 p.1 p.2

def clauseA3Components (p : Nat × Nat) : Nat :=
  clauseA3 p.1 p.2

theorem clauseA0Components_tm_polytime :
    TMPolyTimeMap natAddInputEncodedType EncodedType.nat clauseA0Components := by
  simpa [clauseA0Components, clauseA0, clauseBaseComponents] using
    clauseBaseComponents_tm_polytime

theorem clauseA1Components_tm_polytime :
    TMPolyTimeMap natAddInputEncodedType EncodedType.nat clauseA1Components := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime clauseA0Components_tm_polytime
  simpa [Function.comp, clauseA1Components, clauseA1, clauseA0Components, clauseA0] using hComp

theorem clauseA2Components_tm_polytime :
    TMPolyTimeMap natAddInputEncodedType EncodedType.nat clauseA2Components := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime clauseA1Components_tm_polytime
  simpa [Function.comp, clauseA2Components, clauseA2, clauseA1Components, clauseA1] using hComp

theorem clauseA3Components_tm_polytime :
    TMPolyTimeMap natAddInputEncodedType EncodedType.nat clauseA3Components := by
  have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime clauseA2Components_tm_polytime
  simpa [Function.comp, clauseA3Components, clauseA3, clauseA2Components, clauseA2] using hComp

theorem variableEdgesFor_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      edgeListStructuredEncodedType
      variableEdgesFor := by
  have hBase :
      TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => baseVertex) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat baseVertex
  have hPosBase :
      TMPolyTimeMap EncodedType.nat edgeStructuredEncodedType
        (fun i : Nat => (posVertex i, baseVertex)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk posVertex_tm_polytime hBase
  have hNegBase :
      TMPolyTimeMap EncodedType.nat edgeStructuredEncodedType
        (fun i : Nat => (negVertex i, baseVertex)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk negVertex_tm_polytime hBase
  have hPosNeg :
      TMPolyTimeMap EncodedType.nat edgeStructuredEncodedType
        (fun i : Nat => (posVertex i, negVertex i)) := by
    simpa [edgeStructuredEncodedType] using
      TMPolyTimeMap.prod_mk posVertex_tm_polytime negVertex_tm_polytime
  have hThird :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun i : Nat => [(posVertex i, negVertex i)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton edgeStructuredEncodedType) hPosNeg
    simpa [Function.comp, edgeListStructuredEncodedType] using hComp
  have hSecondInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun i : Nat => ((negVertex i, baseVertex), [(posVertex i, negVertex i)])) :=
    TMPolyTimeMap.prod_mk hNegBase hThird
  have hSecond :
      TMPolyTimeMap EncodedType.nat edgeListStructuredEncodedType
        (fun i : Nat => [(negVertex i, baseVertex), (posVertex i, negVertex i)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons edgeStructuredEncodedType) hSecondInput
    simpa [Function.comp, edgeListStructuredEncodedType] using hComp
  have hFirstInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun i : Nat =>
          ((posVertex i, baseVertex),
            [(negVertex i, baseVertex), (posVertex i, negVertex i)])) :=
    TMPolyTimeMap.prod_mk hPosBase hSecond
  have hOut := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeStructuredEncodedType) hFirstInput
  simpa [Function.comp, variableEdgesFor, edgeListStructuredEncodedType] using hOut

noncomputable def variableEdgesForTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      edgeListStructuredEncodedType
      variableEdgesFor where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := edgeListStructuredEncodedType)
      (LinearSizeBound.intro_with 20 50 (by
        intro i
        simp [variableEdgesFor, edgeListStructuredEncodedType, edgeStructuredEncodedType,
          EncodedType.inputSize, EncodedType.list, EncodedType.prod, EncodedType.nat,
          baseVertex, posVertex, negVertex]
        omega))
  tm_polytime := variableEdgesFor_tm_polytime

/-! ### Checked variable-edge list runner -/

def variableEdgesBuilderStep
    (p : List (Nat × Nat) × Nat) :
    List (Nat × Nat) :=
  p.1 ++ variableEdgesFor p.2

theorem variableEdgesBuilderStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod edgeListStructuredEncodedType EncodedType.nat)
      edgeListStructuredEncodedType
      variableEdgesBuilderStep := by
  let X := EncodedType.prod edgeListStructuredEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.nat
  have hIndex : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.nat
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => variableEdgesFor p.2) := by
    have hComp := TMPolyTimeMap.comp variableEdgesFor_tm_polytime hIndex
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.1, variableEdgesFor p.2)) :=
    TMPolyTimeMap.prod_mk hAcc hEdges
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
  simpa [Function.comp, variableEdgesBuilderStep, edgeListStructuredEncodedType, X] using hAppend

theorem variableEdgesBuilderStep_growth
    (source : List Nat) (acc : List (Nat × Nat)) (i : Nat)
    (hi : EncodedType.nat.inputSize i ≤
      (EncodedType.list EncodedType.nat).inputSize source) :
    edgeListStructuredEncodedType.inputSize (variableEdgesBuilderStep (acc, i)) ≤
      edgeListStructuredEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
          ((EncodedType.list EncodedType.nat).inputSize source) := by
  have hi' : i + 1 ≤ (EncodedType.list EncodedType.nat).inputSize source := by
    simpa [EncodedType.inputSize_nat] using hi
  simp [variableEdgesBuilderStep, variableEdgesFor, edgeListStructuredEncodedType,
    edgeStructuredEncodedType, EncodedType.inputSize, EncodedType.list, EncodedType.prod,
    EncodedType.nat, posVertex, negVertex, baseVertex, Polynomial.eval_add,
    Polynomial.eval_mul] at hi' ⊢
  omega

def variableEdgesFromIndices (xs : List Nat) : List (Nat × Nat) :=
  xs.foldl (fun acc i => variableEdgesBuilderStep (acc, i)) []

theorem variableEdgesFromIndices_eq_flatMap (xs : List Nat) :
    variableEdgesFromIndices xs = xs.flatMap variableEdgesFor := by
  unfold variableEdgesFromIndices
  have h :
      ∀ acc : List (Nat × Nat),
        xs.foldl (fun acc i => variableEdgesBuilderStep (acc, i)) acc =
          acc ++ xs.flatMap variableEdgesFor := by
    induction xs with
    | nil =>
        intro acc
        simp [variableEdgesBuilderStep]
    | cons i is ih =>
        intro acc
        simp [List.flatMap, variableEdgesBuilderStep, List.append_assoc]
  simpa using h []

theorem variableEdgesFromRange_eq_variableEdges (n : Nat) :
    variableEdgesFromIndices (List.range n) = variableEdges n := by
  simp [variableEdges, variableEdgesFromIndices_eq_flatMap]

theorem variableEdgesFromIndices_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.nat)
      edgeListStructuredEncodedType
      variableEdgesFromIndices := by
  rcases variableEdgesBuilderStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat edgeListStructuredEncodedType
      variableEdgesBuilderStep ([] : List (Nat × Nat))
      hStep (Polynomial.C 0) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro source
    rw [show edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 by
      rfl]
    simp
  · intro source acc i hi
    exact variableEdgesBuilderStep_growth source acc i hi

theorem variableEdges_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      edgeListStructuredEncodedType
      variableEdges := by
  have hComp := TMPolyTimeMap.comp variableEdgesFromIndices_tm_polytime natRange_tm_polytime
  convert hComp using 1
  funext n
  simp [Function.comp, variableEdgesFromRange_eq_variableEdges]

theorem variableEdges_structured_inputSize_le (n : Nat) :
    edgeListStructuredEncodedType.inputSize (variableEdges n) ≤
      100 * EncodedType.nat.inputSize n ^ 2 + 100 := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound edgeStructuredEncodedType
      (variableEdges n) (2 * variableLimit n + 1)
      (by
        intro e he
        have hEndpoints := variableEdges_endpoints_lt (n := n) (m := 0) he
        exact edgeStructured_inputSize_le_of_lt hEndpoints.1 hEndpoints.2)
  have hLen := variableEdges_length n
  calc
    edgeListStructuredEncodedType.inputSize (variableEdges n)
        ≤ (variableEdges n).length * (2 * variableLimit n + 1 + 1) := by
          simpa [edgeListStructuredEncodedType] using hList
    _ = 3 * n * (2 * variableLimit n + 2) := by
          rw [hLen]
    _ ≤ 100 * EncodedType.nat.inputSize n ^ 2 + 100 := by
          simp [EncodedType.inputSize_nat, variableLimit]
          ring_nf
          omega

theorem variableEdges_polynomialSizeBound :
    PolynomialSizeBound
      (fun n : Nat => EncodedType.nat.inputSize n)
      (fun edges : edgeListStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      variableEdges := by
  refine PolynomialSizeBound.intro_with 2 100 100 ?_
  intro n
  exact variableEdges_structured_inputSize_le n

noncomputable def variableEdgesTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      edgeListStructuredEncodedType
      variableEdges where
  costed := CostedMap.of_encodedPolynomialSizeBound variableEdges_polynomialSizeBound
  tm_polytime := variableEdges_tm_polytime

/-! ### Checked fixed-length clause-gadget edge runner -/

def clauseGadgetInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)))

def clauseGadgetEdgesFromInput (p : clauseGadgetInputEncodedType.Carrier) :
    List (Nat × Nat) :=
  clauseGadgetEdges p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

theorem edgeList_cons_tm_polytime
    {X : EncodedType} {head : X.Carrier → edgeStructuredEncodedType.Carrier}
    {tail : X.Carrier → edgeListStructuredEncodedType.Carrier}
    (hHead : TMPolyTimeMap X edgeStructuredEncodedType head)
    (hTail : TMPolyTimeMap X edgeListStructuredEncodedType tail) :
    TMPolyTimeMap X edgeListStructuredEncodedType (fun x => head x :: tail x) := by
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod edgeStructuredEncodedType edgeListStructuredEncodedType)
        (fun x => (head x, tail x)) :=
    TMPolyTimeMap.prod_mk hHead hTail
  have hCons := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons edgeStructuredEncodedType) hPair
  simpa [Function.comp, edgeListStructuredEncodedType] using hCons

theorem clauseGadgetEdgesFromInput_tm_polytime :
    TMPolyTimeMap
      clauseGadgetInputEncodedType
      edgeListStructuredEncodedType
      clauseGadgetEdgesFromInput := by
  let X := clauseGadgetInputEncodedType
  let Tail :=
    EncodedType.prod EncodedType.nat
      (EncodedType.prod literalStructuredEncodedType
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
  let LitTail :=
    EncodedType.prod literalStructuredEncodedType
      (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
  let LitPair := EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, clauseGadgetInputEncodedType, Tail] using TMPolyTimeMap.fst EncodedType.nat Tail
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.2) := by
    simpa [X, clauseGadgetInputEncodedType, Tail] using TMPolyTimeMap.snd EncodedType.nat Tail
  have hJ : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat LitTail
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X, Tail, LitTail] using hComp
  have hLitTail : TMPolyTimeMap X LitTail (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat LitTail
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X, Tail, LitTail] using hComp
  have hL0 : TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType LitPair
    have hComp := TMPolyTimeMap.comp hFst hLitTail
    simpa [Function.comp, X, LitTail, LitPair] using hComp
  have hL12 : TMPolyTimeMap X LitPair (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType LitPair
    have hComp := TMPolyTimeMap.comp hSnd hLitTail
    simpa [Function.comp, X, LitTail, LitPair] using hComp
  have hL1 : TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hL12
    simpa [Function.comp, X, LitPair] using hComp
  have hL2 : TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hL12
    simpa [Function.comp, X, LitPair] using hComp
  have hNJ : TMPolyTimeMap X natAddInputEncodedType (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hN hJ
  have hA0 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => clauseA0 p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp clauseA0Components_tm_polytime hNJ
    simpa [Function.comp, clauseA0Components, X] using hComp
  have hA1 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => clauseA1 p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp clauseA1Components_tm_polytime hNJ
    simpa [Function.comp, clauseA1Components, X] using hComp
  have hA2 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => clauseA2 p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp clauseA2Components_tm_polytime hNJ
    simpa [Function.comp, clauseA2Components, X] using hComp
  have hA3 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => clauseA3 p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp clauseA3Components_tm_polytime hNJ
    simpa [Function.comp, clauseA3Components, X] using hComp
  have hX0 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => literalVertex p.2.2.1) := by
    have hComp := TMPolyTimeMap.comp literalVertex_tm_polytime hL0
    simpa [Function.comp, X] using hComp
  have hX1 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => literalVertex p.2.2.2.1) := by
    have hComp := TMPolyTimeMap.comp literalVertex_tm_polytime hL1
    simpa [Function.comp, X] using hComp
  have hX2 : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => literalVertex p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp literalVertex_tm_polytime hL2
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => trueVertex) :=
    TMPolyTimeMap.const X EncodedType.nat trueVertex
  have hE01 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (clauseA0 p.1 p.2.1, clauseA1 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hA0 hA1
  have hE02 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (clauseA0 p.1 p.2.1, clauseA2 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hA0 hA2
  have hE3T : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (clauseA3 p.1 p.2.1, trueVertex)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hA3 hTrue
  have hE1T : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (clauseA1 p.1 p.2.1, trueVertex)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hA1 hTrue
  have hE23 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (clauseA2 p.1 p.2.1, clauseA3 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hA2 hA3
  have hX0A2 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (literalVertex p.2.2.1, clauseA2 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hX0 hA2
  have hX0A3 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (literalVertex p.2.2.1, clauseA3 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hX0 hA3
  have hX1A0 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (literalVertex p.2.2.2.1, clauseA0 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hX1 hA0
  have hX2A1 : TMPolyTimeMap X edgeStructuredEncodedType
      (fun p : X.Carrier => (literalVertex p.2.2.2.2, clauseA1 p.1 p.2.1)) := by
    simpa [edgeStructuredEncodedType] using TMPolyTimeMap.prod_mk hX2 hA1
  have hNil : TMPolyTimeMap X edgeListStructuredEncodedType (fun _ : X.Carrier => []) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have h9 := edgeList_cons_tm_polytime hX2A1 hNil
  have h8 := edgeList_cons_tm_polytime hX1A0 h9
  have h7 := edgeList_cons_tm_polytime hX0A3 h8
  have h6 := edgeList_cons_tm_polytime hX0A2 h7
  have h5 := edgeList_cons_tm_polytime hE23 h6
  have h4 := edgeList_cons_tm_polytime hE1T h5
  have h3 := edgeList_cons_tm_polytime hE3T h4
  have h2 := edgeList_cons_tm_polytime hE02 h3
  have h1 := edgeList_cons_tm_polytime hE01 h2
  simpa [clauseGadgetEdgesFromInput, clauseGadgetEdges] using h1

end ChromaticNumber
end Karp21
end ComplexityReduction
