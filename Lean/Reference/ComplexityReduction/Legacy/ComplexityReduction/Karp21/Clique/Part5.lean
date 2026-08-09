import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part4

namespace ComplexityReduction
namespace Karp21
namespace Clique

open ComplexityReduction.Combinatorics.Graph

/-! #### TM-backed compatibility edge-list fold over expanded occurrence items -/

def cliqueCompatibilityEdgeItemEncodedType : EncodedType :=
  EncodedType.prod indexedLiteralOccurrenceEncodedType
    (EncodedType.list indexedLiteralOccurrenceEncodedType)

def cliqueCompatibilityEdgeItemStepInputEncodedType : EncodedType :=
  EncodedType.prod edgeListStructuredEncodedType cliqueCompatibilityEdgeItemEncodedType

def cliqueCompatibilityEdgeItemStep
    (p : cliqueCompatibilityEdgeItemStepInputEncodedType.Carrier) :
    List edgeStructuredEncodedType.Carrier :=
  (cliquePriorEdgeRunnerFold ((p.1, p.2.1), p.2.2)).1

def cliqueCompatibilityEdgesFromItems
    (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    List edgeStructuredEncodedType.Carrier :=
  items.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item)) []

theorem cliquePriorEdgeRunner_tm_polytime :
    TMPolyTimeMap
      cliquePriorEdgeRunnerInputEncodedType
      cliquePriorEdgeFoldAccEncodedType
      cliquePriorEdgeRunnerFold := by
  have hImage :
      TMPolyTimeMap
        cliquePriorEdgeRunnerInputEncodedType
        cliquePriorEdgeRunnerFoldImageEncodedType
        id := by
    have hComp :=
      TMPolyTimeMap.comp cliquePriorEdgeRunnerFoldImage_tm_polytime
        cliquePriorEdgeRunnerInstructionsImage_tm_polytime
    simpa [Function.comp] using hComp
  have hComp :=
    TMPolyTimeMap.comp cliquePriorEdgeRunnerFoldFromImage_tm_polytime
      hImage
  simpa [Function.comp] using hComp

theorem cliquePriorEdgeFoldAcc_edges_inputSize_le
    (acc : cliquePriorEdgeFoldAccEncodedType.Carrier) :
    edgeListStructuredEncodedType.inputSize acc.1 ≤
      cliquePriorEdgeFoldAccEncodedType.inputSize acc := by
  rcases acc with ⟨edges, current⟩
  simp [cliquePriorEdgeFoldAccEncodedType, edgeListStructuredEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem cliqueCompatibilityEdgeItem_current_inputSize_le
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    indexedLiteralOccurrenceEncodedType.inputSize item.1 ≤
      cliqueCompatibilityEdgeItemEncodedType.inputSize item := by
  rcases item with ⟨current, prior⟩
  simp [cliqueCompatibilityEdgeItemEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliqueCompatibilityEdgeItem_prior_inputSize_le
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize item.2 ≤
      cliqueCompatibilityEdgeItemEncodedType.inputSize item := by
  rcases item with ⟨current, prior⟩
  simp [cliqueCompatibilityEdgeItemEncodedType, EncodedType.inputSize_prod]

theorem cliqueCompatibilityEdgeItemStep_tm_polytime :
    TMPolyTimeMap
      cliqueCompatibilityEdgeItemStepInputEncodedType
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgeItemStep := by
  let X := cliqueCompatibilityEdgeItemStepInputEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueCompatibilityEdgeItemStepInputEncodedType] using
      TMPolyTimeMap.fst edgeListStructuredEncodedType cliqueCompatibilityEdgeItemEncodedType
  have hItem :
      TMPolyTimeMap X cliqueCompatibilityEdgeItemEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueCompatibilityEdgeItemStepInputEncodedType] using
      TMPolyTimeMap.snd edgeListStructuredEncodedType cliqueCompatibilityEdgeItemEncodedType
  have hCurrent :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst indexedLiteralOccurrenceEncodedType
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hItem
    simpa [Function.comp, cliqueCompatibilityEdgeItemEncodedType, X] using hComp
  have hPrior :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => p.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd indexedLiteralOccurrenceEncodedType
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hItem
    simpa [Function.comp, cliqueCompatibilityEdgeItemEncodedType, X] using hComp
  have hInit :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hEdges hCurrent
  have hRunnerInput :
      TMPolyTimeMap X cliquePriorEdgeRunnerInputEncodedType
        (fun p : X.Carrier => ((p.1, p.2.1), p.2.2)) :=
    TMPolyTimeMap.prod_mk hInit hPrior
  have hRunner :
      TMPolyTimeMap X cliquePriorEdgeFoldAccEncodedType
        (fun p : X.Carrier => cliquePriorEdgeRunnerFold ((p.1, p.2.1), p.2.2)) := by
    have hComp := TMPolyTimeMap.comp cliquePriorEdgeRunner_tm_polytime hRunnerInput
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => (cliquePriorEdgeRunnerFold ((p.1, p.2.1), p.2.2)).1) := by
    have hFst :=
      TMPolyTimeMap.fst edgeListStructuredEncodedType indexedLiteralOccurrenceEncodedType
    have hComp := TMPolyTimeMap.comp hFst hRunner
    simpa [Function.comp, cliquePriorEdgeFoldAccEncodedType, X] using hComp
  simpa [cliqueCompatibilityEdgeItemStep, X] using hOut

theorem cliqueCompatibilityEdgeItemStep_inputSize_growth
    (edges : List edgeStructuredEncodedType.Carrier)
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgeItemStep (edges, item)) ≤
      edgeListStructuredEncodedType.inputSize edges +
        cliqueCompatibilityEdgeItemEncodedType.inputSize item *
          (cliqueCompatibilityEdgeItemEncodedType.inputSize item + 4) +
        cliqueCompatibilityEdgeItemEncodedType.inputSize item + 5 := by
  rcases item with ⟨current, prior⟩
  let init : cliquePriorEdgeFoldAccEncodedType.Carrier := (edges, current)
  have hFold := cliquePriorEdgeRunnerPriorFold_inputSize_le init prior
  have hFoldAppend :
      cliquePriorEdgeFoldAccEncodedType.inputSize
          (prior.foldl (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ)) init) ≤
        cliquePriorEdgeFoldAccEncodedType.inputSize init +
          prior.length * (indexedLiteralOccurrenceEncodedType.inputSize init.2 + 4) +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior := by
    simpa [cliquePriorEdgeRunnerStep_prior] using hFold
  have hFoldEq :
      cliquePriorEdgeRunnerFold (init, prior) =
        prior.foldl (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ)) init := by
    simpa [init] using cliquePriorEdgeRunnerFold_eq (init, prior)
  have hEdgesOut :=
    cliquePriorEdgeFoldAcc_edges_inputSize_le
      (prior.foldl (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ)) init)
  have hCurrent :
      indexedLiteralOccurrenceEncodedType.inputSize current ≤
        cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) :=
    cliqueCompatibilityEdgeItem_current_inputSize_le (current, prior)
  have hPriorInput :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior ≤
        cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) :=
    cliqueCompatibilityEdgeItem_prior_inputSize_le (current, prior)
  have hPriorLen :
      prior.length ≤ cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) := by
    have hLen := encodedList_length_le_inputSize indexedLiteralOccurrenceEncodedType prior
    omega
  calc
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgeItemStep (edges, current, prior))
        = edgeListStructuredEncodedType.inputSize
            (prior.foldl (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ)) init).1 := by
          simp [cliqueCompatibilityEdgeItemStep, hFoldEq, init]
    _ ≤ cliquePriorEdgeFoldAccEncodedType.inputSize
          (prior.foldl (fun acc occ => appendPriorCompatibleEdgeStep (acc, occ)) init) :=
          hEdgesOut
    _ ≤ cliquePriorEdgeFoldAccEncodedType.inputSize init +
          prior.length * (indexedLiteralOccurrenceEncodedType.inputSize init.2 + 4) +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize prior :=
          hFoldAppend
    _ ≤ edgeListStructuredEncodedType.inputSize edges +
          cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) *
            (cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) + 4) +
          cliqueCompatibilityEdgeItemEncodedType.inputSize (current, prior) + 5 := by
          simp [cliquePriorEdgeFoldAccEncodedType, cliqueCompatibilityEdgeItemEncodedType,
            edgeListStructuredEncodedType, EncodedType.inputSize_prod] at hCurrent hPriorInput hPriorLen ⊢
          nlinarith

noncomputable def cliqueCompatibilityEdgeItemGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * (Polynomial.X * Polynomial.X) + Polynomial.C 100

@[simp] theorem cliqueCompatibilityEdgeItemGrowPolynomial_eval (n : Nat) :
    cliqueCompatibilityEdgeItemGrowPolynomial.eval n = 10 * (n * n) + 100 := by
  simp [cliqueCompatibilityEdgeItemGrowPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cliqueCompatibilityEdgeItemStep_growth_for_source
    (source : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (edges : List edgeStructuredEncodedType.Carrier)
    (item : cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (hItem :
      cliqueCompatibilityEdgeItemEncodedType.inputSize item ≤
        (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) :
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgeItemStep (edges, item)) ≤
      edgeListStructuredEncodedType.inputSize edges +
        cliqueCompatibilityEdgeItemGrowPolynomial.eval
          ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) := by
  let N := (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source
  have hStep := cliqueCompatibilityEdgeItemStep_inputSize_growth edges item
  have hGrow :
      cliqueCompatibilityEdgeItemEncodedType.inputSize item *
          (cliqueCompatibilityEdgeItemEncodedType.inputSize item + 4) +
        cliqueCompatibilityEdgeItemEncodedType.inputSize item + 5 ≤ 10 * (N * N) + 100 := by
    let m := cliqueCompatibilityEdgeItemEncodedType.inputSize item
    have hMul : m * (m + 4) ≤ N * (N + 4) :=
      Nat.mul_le_mul hItem (Nat.add_le_add_right hItem 4)
    have hSmall : m * (m + 4) + m + 5 ≤ N * (N + 4) + N + 5 := by
      omega
    have hBig : N * (N + 4) + N + 5 ≤ 10 * (N * N) + 100 := by
      nlinarith [sq_nonneg (N : Int)]
    exact hSmall.trans hBig
  have hAdd :
      edgeListStructuredEncodedType.inputSize edges +
            cliqueCompatibilityEdgeItemEncodedType.inputSize item *
              (cliqueCompatibilityEdgeItemEncodedType.inputSize item + 4) +
          cliqueCompatibilityEdgeItemEncodedType.inputSize item + 5 ≤
        edgeListStructuredEncodedType.inputSize edges + (10 * (N * N) + 100) := by
    omega
  have hTarget :
      edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgeItemStep (edges, item)) ≤
        edgeListStructuredEncodedType.inputSize edges + (10 * (N * N) + 100) :=
    hStep.trans hAdd
  simpa [N, cliqueCompatibilityEdgeItemGrowPolynomial] using hTarget

theorem cliqueCompatibilityEdgesFromItems_inputSize_le_aux
    (source rest : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
    (edges : List edgeStructuredEncodedType.Carrier)
    (hRest :
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize rest ≤
        (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) :
    edgeListStructuredEncodedType.inputSize
        (rest.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item)) edges) ≤
      edgeListStructuredEncodedType.inputSize edges +
        rest.length *
          cliqueCompatibilityEdgeItemGrowPolynomial.eval
            ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) := by
  induction rest generalizing edges with
  | nil =>
      simp
  | cons item rest ih =>
      have hItem :
          cliqueCompatibilityEdgeItemEncodedType.inputSize item ≤
            (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source := by
        rw [EncodedType.inputSize_list_cons] at hRest
        omega
      have hRestTail :
          (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize rest ≤
            (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source := by
        rw [EncodedType.inputSize_list_cons] at hRest
        omega
      have hStep :=
        cliqueCompatibilityEdgeItemStep_growth_for_source source edges item hItem
      have hTail := ih (cliqueCompatibilityEdgeItemStep (edges, item)) hRestTail
      simp only [List.foldl_cons]
      calc
        edgeListStructuredEncodedType.inputSize
            (rest.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item))
              (cliqueCompatibilityEdgeItemStep (edges, item)))
            ≤ edgeListStructuredEncodedType.inputSize
                (cliqueCompatibilityEdgeItemStep (edges, item)) +
              rest.length *
                cliqueCompatibilityEdgeItemGrowPolynomial.eval
                  ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) :=
              hTail
        _ ≤ edgeListStructuredEncodedType.inputSize edges +
              (item :: rest).length *
                cliqueCompatibilityEdgeItemGrowPolynomial.eval
                  ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source) := by
              let G :=
                cliqueCompatibilityEdgeItemGrowPolynomial.eval
                  ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize source)
              have hStepG :
                  edgeListStructuredEncodedType.inputSize
                      (cliqueCompatibilityEdgeItemStep (edges, item)) ≤
                    edgeListStructuredEncodedType.inputSize edges + G := by
                simpa [G] using hStep
              have hBound :
                  edgeListStructuredEncodedType.inputSize
                      (cliqueCompatibilityEdgeItemStep (edges, item)) +
                    rest.length * G ≤
                    edgeListStructuredEncodedType.inputSize edges + G + rest.length * G :=
                Nat.add_le_add_right hStepG (rest.length * G)
              have hArith :
                  edgeListStructuredEncodedType.inputSize edges + G + rest.length * G =
                    edgeListStructuredEncodedType.inputSize edges + (item :: rest).length * G := by
                simp
                nlinarith
              exact hBound.trans (le_of_eq hArith)

theorem cliqueCompatibilityEdgesFromItems_inputSize_le
    (items : List cliqueCompatibilityEdgeItemEncodedType.Carrier) :
    edgeListStructuredEncodedType.inputSize (cliqueCompatibilityEdgesFromItems items) ≤
      200 * ((EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize items) ^ 3 +
        100 := by
  let N := (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize items
  have hAux :=
    cliqueCompatibilityEdgesFromItems_inputSize_le_aux items items
      ([] : List edgeStructuredEncodedType.Carrier) (by simp)
  have hLen := encodedList_length_le_inputSize cliqueCompatibilityEdgeItemEncodedType items
  have hNil : edgeListStructuredEncodedType.inputSize
      ([] : List edgeStructuredEncodedType.Carrier) = 0 := by
    change (EncodedType.list edgeStructuredEncodedType).inputSize ([] : List (Nat × Nat)) = 0
    exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
  simp [cliqueCompatibilityEdgesFromItems, hNil] at hAux ⊢
  change
    edgeListStructuredEncodedType.inputSize
        (List.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item)) [] items) ≤
      200 * N ^ 3 + 100
  have hAuxN :
      edgeListStructuredEncodedType.inputSize
          (List.foldl (fun edges item => cliqueCompatibilityEdgeItemStep (edges, item)) [] items) ≤
        items.length * (10 * (N * N) + 100) := by
    simpa [N] using hAux
  have hLenN : items.length ≤ N := by
    simpa [N] using hLen
  have hGrow : items.length * (10 * (N * N) + 100) ≤ 200 * N ^ 3 + 100 := by
    cases hN : N with
    | zero =>
        have hLenZero : items.length = 0 := by omega
        simp [hLenZero]
    | succ n =>
        have hNpos : 1 ≤ Nat.succ n := by omega
        have hLen' : items.length ≤ Nat.succ n := by omega
        nlinarith [hLen', sq_nonneg (Nat.succ n : Int), hNpos]
  exact hAuxN.trans hGrow

theorem cliqueCompatibilityEdgesFromItems_polynomialSizeBound :
    PolynomialSizeBound
      (fun items : List cliqueCompatibilityEdgeItemEncodedType.Carrier =>
        (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize items)
      (fun edges : List edgeStructuredEncodedType.Carrier =>
        edgeListStructuredEncodedType.inputSize edges)
      cliqueCompatibilityEdgesFromItems := by
  refine PolynomialSizeBound.intro_with 3 200 100 ?_
  intro items
  exact cliqueCompatibilityEdgesFromItems_inputSize_le items

theorem cliqueCompatibilityEdgesFromItems_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromItems := by
  rcases cliqueCompatibilityEdgeItemStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      cliqueCompatibilityEdgeItemEncodedType edgeListStructuredEncodedType
      cliqueCompatibilityEdgeItemStep ([] : List edgeStructuredEncodedType.Carrier)
      hStep (Polynomial.C 0) cliqueCompatibilityEdgeItemGrowPolynomial ?_ ?_
  · intro source
    simp [edgeListStructuredEncodedType]
  · intro source edges item hItem
    exact cliqueCompatibilityEdgeItemStep_growth_for_source source edges item hItem

noncomputable def cliqueCompatibilityEdgesFromItemsTMBackedMap :
    TMBackedCostedMap
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
      edgeListStructuredEncodedType
      cliqueCompatibilityEdgesFromItems where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cliqueCompatibilityEdgesFromItems_polynomialSizeBound
  tm_polytime := cliqueCompatibilityEdgesFromItems_tm_polytime

/-! #### TM-backed expansion from occurrences to `(current, prior)` items -/

def cliqueCompatibilityItemBuilderAccEncodedType : EncodedType :=
  EncodedType.prod (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
    (EncodedType.list indexedLiteralOccurrenceEncodedType)

def cliqueCompatibilityItemBuilderStepInputEncodedType : EncodedType :=
  EncodedType.prod cliqueCompatibilityItemBuilderAccEncodedType indexedLiteralOccurrenceEncodedType

def cliqueCompatibilityItemBuilderInit :
    cliqueCompatibilityItemBuilderAccEncodedType.Carrier :=
  (([] : List cliqueCompatibilityEdgeItemEncodedType.Carrier),
    ([] : List indexedLiteralOccurrenceEncodedType.Carrier))

def cliqueCompatibilityItemBuilderStep
    (p : cliqueCompatibilityItemBuilderStepInputEncodedType.Carrier) :
    cliqueCompatibilityItemBuilderAccEncodedType.Carrier :=
  let items : List cliqueCompatibilityEdgeItemEncodedType.Carrier := p.1.1
  let prior : List indexedLiteralOccurrenceEncodedType.Carrier := p.1.2
  let current := p.2
  let item : cliqueCompatibilityEdgeItemEncodedType.Carrier := (current, prior)
  (List.append items [item], List.append prior [current])

def cliqueCompatibilityItemsFromOccurrences
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    List cliqueCompatibilityEdgeItemEncodedType.Carrier :=
  (xs.foldl
    (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
    cliqueCompatibilityItemBuilderInit).1

theorem cliqueCompatibilityItemBuilderAcc_items_inputSize_le
    (acc : cliqueCompatibilityItemBuilderAccEncodedType.Carrier) :
    (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize acc.1 ≤
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc := by
  rcases acc with ⟨items, prior⟩
  simp [cliqueCompatibilityItemBuilderAccEncodedType, EncodedType.inputSize_prod]
  omega

theorem cliqueCompatibilityItemBuilderAcc_prior_inputSize_le
    (acc : cliqueCompatibilityItemBuilderAccEncodedType.Carrier) :
    (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize acc.2 ≤
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc := by
  rcases acc with ⟨items, prior⟩
  simp [cliqueCompatibilityItemBuilderAccEncodedType, EncodedType.inputSize_prod]

theorem cliqueCompatibilityItemBuilderStep_tm_polytime :
    TMPolyTimeMap
      cliqueCompatibilityItemBuilderStepInputEncodedType
      cliqueCompatibilityItemBuilderAccEncodedType
      cliqueCompatibilityItemBuilderStep := by
  let X := cliqueCompatibilityItemBuilderStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X cliqueCompatibilityItemBuilderAccEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, cliqueCompatibilityItemBuilderStepInputEncodedType] using
      TMPolyTimeMap.fst cliqueCompatibilityItemBuilderAccEncodedType
        indexedLiteralOccurrenceEncodedType
  have hCurrent :
      TMPolyTimeMap X indexedLiteralOccurrenceEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X, cliqueCompatibilityItemBuilderStepInputEncodedType] using
      TMPolyTimeMap.snd cliqueCompatibilityItemBuilderAccEncodedType
        indexedLiteralOccurrenceEncodedType
  have hItems :
      TMPolyTimeMap X (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
        (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, X, cliqueCompatibilityItemBuilderAccEncodedType] using hComp
  have hPrior :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
        (EncodedType.list indexedLiteralOccurrenceEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, cliqueCompatibilityItemBuilderAccEncodedType] using hComp
  have hItem :
      TMPolyTimeMap X cliqueCompatibilityEdgeItemEncodedType
        (fun p : X.Carrier =>
          (p.2, (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier))) :=
    TMPolyTimeMap.prod_mk hCurrent hPrior
  have hItemSingleton :
      TMPolyTimeMap X (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
        (fun p : X.Carrier =>
          [(p.2, (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier))]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton cliqueCompatibilityEdgeItemEncodedType) hItem
    simpa [Function.comp, X] using hComp
  have hItemsAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod
          (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
          (EncodedType.list cliqueCompatibilityEdgeItemEncodedType))
        (fun p : X.Carrier =>
          ((p.1.1 : List cliqueCompatibilityEdgeItemEncodedType.Carrier),
            [(p.2, (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier))])) :=
    TMPolyTimeMap.prod_mk hItems hItemSingleton
  have hNewItems :
      TMPolyTimeMap X (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
        (fun p : X.Carrier =>
          List.append (p.1.1 : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
            [((p.2, (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier)) :
              cliqueCompatibilityEdgeItemEncodedType.Carrier)]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append cliqueCompatibilityEdgeItemEncodedType)
        hItemsAppendInput
    simpa [Function.comp, X] using hComp
  have hCurrentSingleton :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier => [p.2]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton indexedLiteralOccurrenceEncodedType) hCurrent
    simpa [Function.comp, X] using hComp
  have hPriorAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod
          (EncodedType.list indexedLiteralOccurrenceEncodedType)
          (EncodedType.list indexedLiteralOccurrenceEncodedType))
        (fun p : X.Carrier =>
          ((p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier), [p.2])) :=
    TMPolyTimeMap.prod_mk hPrior hCurrentSingleton
  have hNewPrior :
      TMPolyTimeMap X (EncodedType.list indexedLiteralOccurrenceEncodedType)
        (fun p : X.Carrier =>
          List.append (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier) [p.2]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_append indexedLiteralOccurrenceEncodedType)
        hPriorAppendInput
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X cliqueCompatibilityItemBuilderAccEncodedType
        (fun p : X.Carrier =>
          (List.append (p.1.1 : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
              [((p.2, (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier)) :
                cliqueCompatibilityEdgeItemEncodedType.Carrier)],
            List.append (p.1.2 : List indexedLiteralOccurrenceEncodedType.Carrier) [p.2])) :=
    TMPolyTimeMap.prod_mk hNewItems hNewPrior
  simpa [cliqueCompatibilityItemBuilderStep, X,
    cliqueCompatibilityItemBuilderAccEncodedType] using hOut

noncomputable def cliqueCompatibilityItemBuilderGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 100

@[simp] theorem cliqueCompatibilityItemBuilderGrowPolynomial_eval (n : Nat) :
    cliqueCompatibilityItemBuilderGrowPolynomial.eval n = 10 * n + 100 := by
  simp [cliqueCompatibilityItemBuilderGrowPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem cliqueCompatibilityItemBuilderStep_growth_for_source
    (source : List indexedLiteralOccurrenceEncodedType.Carrier)
    (acc : cliqueCompatibilityItemBuilderAccEncodedType.Carrier)
    (current : indexedLiteralOccurrenceEncodedType.Carrier)
    (hPrior :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize acc.2 ≤
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source)
    (hCurrent :
      indexedLiteralOccurrenceEncodedType.inputSize current ≤
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source) :
    cliqueCompatibilityItemBuilderAccEncodedType.inputSize
        (cliqueCompatibilityItemBuilderStep (acc, current)) ≤
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
        cliqueCompatibilityItemBuilderGrowPolynomial.eval
          ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source) := by
  rcases acc with ⟨items, prior⟩
  let itemList : List cliqueCompatibilityEdgeItemEncodedType.Carrier := items
  let priorList : List indexedLiteralOccurrenceEncodedType.Carrier := prior
  let N := (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source
  have hItemsAppend :
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize
          (List.append itemList
            ([(current, priorList)] : List cliqueCompatibilityEdgeItemEncodedType.Carrier)) =
        (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize itemList +
          cliqueCompatibilityEdgeItemEncodedType.inputSize (current, priorList) + 1 := by
    simpa using
      encodedList_inputSize_append cliqueCompatibilityEdgeItemEncodedType itemList
        ([(current, priorList)] : List cliqueCompatibilityEdgeItemEncodedType.Carrier)
  have hPriorAppend :
      (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (List.append priorList
            ([current] : List indexedLiteralOccurrenceEncodedType.Carrier)) =
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize priorList +
          indexedLiteralOccurrenceEncodedType.inputSize current + 1 := by
    simpa using
      encodedList_inputSize_append indexedLiteralOccurrenceEncodedType priorList
        ([current] : List indexedLiteralOccurrenceEncodedType.Carrier)
  change
    cliqueCompatibilityItemBuilderAccEncodedType.inputSize
        (cliqueCompatibilityItemBuilderStep ((itemList, priorList), current)) ≤
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize (itemList, priorList) +
        cliqueCompatibilityItemBuilderGrowPolynomial.eval
          ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source)
  simp [cliqueCompatibilityItemBuilderStep, cliqueCompatibilityItemBuilderAccEncodedType,
    EncodedType.inputSize_prod] at hPrior hCurrent ⊢
  change
    (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize
          (List.append itemList
            ([(current, priorList)] : List cliqueCompatibilityEdgeItemEncodedType.Carrier)) +
        1 +
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
          (List.append priorList
            ([current] : List indexedLiteralOccurrenceEncodedType.Carrier)) ≤
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize itemList + 1 +
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize priorList +
        (10 * (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source + 100)
  rw [hItemsAppend, hPriorAppend]
  simp [cliqueCompatibilityEdgeItemEncodedType, EncodedType.inputSize_prod] at hPrior hCurrent ⊢
  nlinarith

theorem cliqueCompatibilityItemBuilderInit_inputSize_le :
    cliqueCompatibilityItemBuilderAccEncodedType.inputSize
        cliqueCompatibilityItemBuilderInit ≤ 10 := by
  simp [cliqueCompatibilityItemBuilderInit, cliqueCompatibilityItemBuilderAccEncodedType,
    EncodedType.inputSize_prod]

theorem cliqueCompatibilityItemBuilderFold_inputSize_le_aux
    (source rest : List indexedLiteralOccurrenceEncodedType.Carrier)
    (acc : cliqueCompatibilityItemBuilderAccEncodedType.Carrier)
    (hSplit :
      List.append (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier) rest = source) :
    cliqueCompatibilityItemBuilderAccEncodedType.inputSize
        (rest.foldl
          (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current)) acc) ≤
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
        rest.length *
          cliqueCompatibilityItemBuilderGrowPolynomial.eval
            ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source) := by
  induction rest generalizing acc with
  | nil =>
      simp
  | cons current rest ih =>
      let N := (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source
      have hPrior :
          (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize acc.2 ≤ N := by
        have hAppend :
            (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                (List.append (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
                  (current :: rest)) =
              (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                  (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier) +
                (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                  (current :: rest) := by
          simpa using encodedList_inputSize_append indexedLiteralOccurrenceEncodedType
            (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier) (current :: rest)
        rw [hSplit] at hAppend
        omega
      have hCurrent :
          indexedLiteralOccurrenceEncodedType.inputSize current ≤ N := by
        have hRestSize :
            (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize (current :: rest) ≤
              N := by
          have hAppend := encodedList_inputSize_append indexedLiteralOccurrenceEncodedType
            (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier) (current :: rest)
          have hAppend' :
              (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                  (List.append (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier)
                    (current :: rest)) =
                (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                    (acc.2 : List indexedLiteralOccurrenceEncodedType.Carrier) +
                  (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize
                    (current :: rest) := by
            simpa using hAppend
          rw [hSplit] at hAppend'
          omega
        rw [EncodedType.inputSize_list_cons] at hRestSize
        omega
      have hStep :=
        cliqueCompatibilityItemBuilderStep_growth_for_source source acc current hPrior hCurrent
      have hSplitTail :
          List.append
              ((cliqueCompatibilityItemBuilderStep (acc, current)).2 :
                List indexedLiteralOccurrenceEncodedType.Carrier) rest = source := by
        simpa [cliqueCompatibilityItemBuilderStep, List.append_assoc] using hSplit
      have hTail := ih (cliqueCompatibilityItemBuilderStep (acc, current)) hSplitTail
      simp only [List.foldl_cons]
      calc
        cliqueCompatibilityItemBuilderAccEncodedType.inputSize
            (rest.foldl
              (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
              (cliqueCompatibilityItemBuilderStep (acc, current)))
            ≤ cliqueCompatibilityItemBuilderAccEncodedType.inputSize
                (cliqueCompatibilityItemBuilderStep (acc, current)) +
              rest.length *
                cliqueCompatibilityItemBuilderGrowPolynomial.eval N := by
              simpa [N] using hTail
        _ ≤ cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
              (current :: rest).length *
                cliqueCompatibilityItemBuilderGrowPolynomial.eval N := by
              have hBound :
                  cliqueCompatibilityItemBuilderAccEncodedType.inputSize
                      (cliqueCompatibilityItemBuilderStep (acc, current)) +
                    rest.length * cliqueCompatibilityItemBuilderGrowPolynomial.eval N ≤
                    cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
                      cliqueCompatibilityItemBuilderGrowPolynomial.eval N +
                      rest.length * cliqueCompatibilityItemBuilderGrowPolynomial.eval N :=
                Nat.add_le_add_right (by simpa [N] using hStep)
                  (rest.length * cliqueCompatibilityItemBuilderGrowPolynomial.eval N)
              have hArith :
                  cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
                      cliqueCompatibilityItemBuilderGrowPolynomial.eval N +
                      rest.length * cliqueCompatibilityItemBuilderGrowPolynomial.eval N =
                    cliqueCompatibilityItemBuilderAccEncodedType.inputSize acc +
                      (current :: rest).length *
                        cliqueCompatibilityItemBuilderGrowPolynomial.eval N := by
                simp
                nlinarith
              exact hBound.trans (le_of_eq hArith)

theorem cliqueCompatibilityItemBuilderFold_inputSize_le
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    cliqueCompatibilityItemBuilderAccEncodedType.inputSize
        (xs.foldl
          (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
          cliqueCompatibilityItemBuilderInit) ≤
      200 * ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs) ^ 2 + 100 := by
  let N := (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs
  have hAux :=
    cliqueCompatibilityItemBuilderFold_inputSize_le_aux xs xs
      cliqueCompatibilityItemBuilderInit (by rfl)
  have hLen := encodedList_length_le_inputSize indexedLiteralOccurrenceEncodedType xs
  have hInit := cliqueCompatibilityItemBuilderInit_inputSize_le
  have hBound :
      cliqueCompatibilityItemBuilderAccEncodedType.inputSize
          (xs.foldl
            (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
            cliqueCompatibilityItemBuilderInit) ≤
        10 + xs.length * (10 * N + 100) := by
    have hInitPlus :
        cliqueCompatibilityItemBuilderAccEncodedType.inputSize cliqueCompatibilityItemBuilderInit +
            xs.length * (10 * N + 100) ≤
          10 + xs.length * (10 * N + 100) :=
      Nat.add_le_add_right hInit _
    have hAuxN :
        cliqueCompatibilityItemBuilderAccEncodedType.inputSize
            (xs.foldl
              (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
              cliqueCompatibilityItemBuilderInit) ≤
          cliqueCompatibilityItemBuilderAccEncodedType.inputSize cliqueCompatibilityItemBuilderInit +
            xs.length * (10 * N + 100) := by
      simpa [N] using hAux
    exact hAuxN.trans hInitPlus
  have hPoly : 10 + xs.length * (10 * N + 100) ≤ 200 * N ^ 2 + 100 := by
    have hLenN : xs.length ≤ N := by simpa [N] using hLen
    nlinarith [hLenN, sq_nonneg (N : Int)]
  exact hBound.trans hPoly

theorem cliqueCompatibilityItemsFromOccurrences_inputSize_le
    (xs : List indexedLiteralOccurrenceEncodedType.Carrier) :
    (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize
        (cliqueCompatibilityItemsFromOccurrences xs) ≤
      200 * ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs) ^ 2 + 100 := by
  have hAcc := cliqueCompatibilityItemBuilderFold_inputSize_le xs
  have hItems :=
    cliqueCompatibilityItemBuilderAcc_items_inputSize_le
      (xs.foldl
        (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
        cliqueCompatibilityItemBuilderInit)
  exact hItems.trans hAcc

theorem cliqueCompatibilityItemsFromOccurrences_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : List indexedLiteralOccurrenceEncodedType.Carrier =>
        (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize xs)
      (fun items : List cliqueCompatibilityEdgeItemEncodedType.Carrier =>
        (EncodedType.list cliqueCompatibilityEdgeItemEncodedType).inputSize items)
      cliqueCompatibilityItemsFromOccurrences := by
  refine PolynomialSizeBound.intro_with 2 200 100 ?_
  intro xs
  exact cliqueCompatibilityItemsFromOccurrences_inputSize_le xs

noncomputable def cliqueCompatibilityItemBuilderTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueCompatibilityItemBuilderAccEncodedType
          indexedLiteralOccurrenceEncodedType).encode
        cliqueCompatibilityItemBuilderAccEncodedType.encode
        cliqueCompatibilityItemBuilderStep) : Polynomial Nat :=
  TMPolyTimeMap.listFoldTypedGrowthTimePolynomial
    indexedLiteralOccurrenceEncodedType
    cliqueCompatibilityItemBuilderAccEncodedType
    cliqueCompatibilityItemBuilderStep hStep
    (Polynomial.C 10) cliqueCompatibilityItemBuilderGrowPolynomial

theorem cliqueCompatibilityItemBuilderFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          cliqueCompatibilityItemBuilderAccEncodedType
          indexedLiteralOccurrenceEncodedType).encode
        cliqueCompatibilityItemBuilderAccEncodedType.encode
        cliqueCompatibilityItemBuilderStep)
    (source : List indexedLiteralOccurrenceEncodedType.Carrier) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          indexedLiteralOccurrenceEncodedType
          cliqueCompatibilityItemBuilderAccEncodedType
          cliqueCompatibilityItemBuilderStep hStep cliqueCompatibilityItemBuilderInit source ≤
      (cliqueCompatibilityItemBuilderTimePolynomial hStep).eval
        ((EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source) := by
  let X := indexedLiteralOccurrenceEncodedType
  let Y := cliqueCompatibilityItemBuilderAccEncodedType
  let N := (EncodedType.list X).inputSize source
  let B₀ := (10 : Nat)
  let G := cliqueCompatibilityItemBuilderGrowPolynomial.eval N
  let B := B₀ + N * G
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (rest : List X.Carrier) (acc : Y.Carrier),
        List.append (acc.2 : List X.Carrier) rest = source →
          (EncodedType.list X).inputSize rest ≤ N →
            Y.inputSize acc ≤ B₀ + (N - (EncodedType.list X).inputSize rest) * G →
              TM2Programs.listFoldTypedLoopTime X Y cliqueCompatibilityItemBuilderStep
                  hStep acc rest ≤
                C * (EncodedType.list X).inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro acc _hSplit _hRest _hAcc
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons current rest ih =>
        intro acc hSplit hRest hAcc
        have hCurrentN : X.inputSize current ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hRestN : (EncodedType.list X).inputSize rest ≤ N := by
          rw [EncodedType.inputSize_list_cons] at hRest
          omega
        have hPriorN : (EncodedType.list X).inputSize acc.2 ≤ N := by
          have hAppend :
              (EncodedType.list X).inputSize
                  (List.append (acc.2 : List X.Carrier) (current :: rest)) =
                (EncodedType.list X).inputSize (acc.2 : List X.Carrier) +
                  (EncodedType.list X).inputSize (current :: rest) := by
            simpa using encodedList_inputSize_append X (acc.2 : List X.Carrier)
              (current :: rest)
          rw [hSplit] at hAppend
          omega
        have hAccFull : Y.inputSize acc ≤ B := by
          dsimp [B]
          nlinarith [hAcc, Nat.sub_le N ((EncodedType.list X).inputSize (current :: rest))]
        have hGrowth :=
          cliqueCompatibilityItemBuilderStep_growth_for_source
            source acc current (by simpa [X, N] using hPriorN) (by simpa [X, N] using hCurrentN)
        have hNext :
            Y.inputSize (cliqueCompatibilityItemBuilderStep (acc, current)) ≤
              B₀ + (N - (EncodedType.list X).inputSize rest) * G := by
          have hGrowth' :
              Y.inputSize (cliqueCompatibilityItemBuilderStep (acc, current)) ≤
                Y.inputSize acc + G := by
            simpa [X, Y, N, G] using hGrowth
          have hSub :
              N - (EncodedType.list X).inputSize (current :: rest) + 1 ≤
                N - (EncodedType.list X).inputSize rest := by
            rw [EncodedType.inputSize_list_cons]
            rw [EncodedType.inputSize_list_cons] at hRest
            omega
          have hBudget :
              (N - (EncodedType.list X).inputSize (current :: rest)) * G + G ≤
                (N - (EncodedType.list X).inputSize rest) * G := by
            calc
              (N - (EncodedType.list X).inputSize (current :: rest)) * G + G
                  = (N - (EncodedType.list X).inputSize (current :: rest) + 1) * G := by
                    ring
              _ ≤ (N - (EncodedType.list X).inputSize rest) * G :=
                    Nat.mul_le_mul_right G hSub
          nlinarith [hAcc, hGrowth', hBudget]
        have hNextFull : Y.inputSize (cliqueCompatibilityItemBuilderStep (acc, current)) ≤ B := by
          dsimp [B]
          nlinarith [hNext, Nat.sub_le N ((EncodedType.list X).inputSize rest)]
        have hSplitTail :
            List.append ((cliqueCompatibilityItemBuilderStep (acc, current)).2 :
                List X.Carrier) rest = source := by
          simpa [cliqueCompatibilityItemBuilderStep, List.append_assoc] using hSplit
        have hTail := ih (cliqueCompatibilityItemBuilderStep (acc, current))
          hSplitTail hRestN hNext
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod Y X).inputSize (acc, current)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (acc, current) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize acc + 1 + X.inputSize current ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
                (Y.encode acc).length
                (Y.encode (cliqueCompatibilityItemBuilderStep (acc, current))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, current))) ≤
              C * (X.inputSize current + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [Y, EncodedType.inputSize] using hAccFull)
              (by simpa [Y, EncodedType.inputSize] using hNextFull)
              hStepTime
        calc
          TM2Programs.listFoldTypedLoopTime X Y cliqueCompatibilityItemBuilderStep
              hStep acc (current :: rest)
              =
            TM2Programs.listFoldTypedLoopTime X Y cliqueCompatibilityItemBuilderStep
              hStep (cliqueCompatibilityItemBuilderStep (acc, current)) rest +
            TM2Programs.listFoldBlockTime hStep.tm (X.encode current).length
              (Y.encode acc).length
              (Y.encode (cliqueCompatibilityItemBuilderStep (acc, current))).length
              (hStep.time.eval ((EncodedType.prod Y X).inputSize (acc, current))) := by
                rfl
          _ ≤ C * (EncodedType.list X).inputSize rest + C * (X.inputSize current + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list X).inputSize (current :: rest) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hInitBound :
      Y.inputSize cliqueCompatibilityItemBuilderInit ≤
        B₀ + (N - (EncodedType.list X).inputSize source) * G := by
    have hInit := cliqueCompatibilityItemBuilderInit_inputSize_le
    have hSub : N - (EncodedType.list X).inputSize source = 0 := by simp [N]
    rw [hSub, Nat.zero_mul, Nat.add_zero]
    simpa [Y, B₀] using hInit
  have hLoop :
      TM2Programs.listFoldTypedLoopTime X Y cliqueCompatibilityItemBuilderStep hStep
          cliqueCompatibilityItemBuilderInit source ≤ C * N := by
    simpa [X, Y, N] using
      hLoopAux source cliqueCompatibilityItemBuilderInit
        (by rfl)
        (by simp [N])
        hInitBound
  have hTimeEval :
      (cliqueCompatibilityItemBuilderTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [cliqueCompatibilityItemBuilderTimePolynomial, X, N, B₀, G, B, T, C,
      TMPolyTimeMap.listFoldTypedGrowthTimePolynomial,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [show (EncodedType.list indexedLiteralOccurrenceEncodedType).inputSize source = N from rfl,
    hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem cliqueCompatibilityItemBuilderFold_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      cliqueCompatibilityItemBuilderAccEncodedType
      (fun xs : List indexedLiteralOccurrenceEncodedType.Carrier =>
        xs.foldl
          (fun acc current => cliqueCompatibilityItemBuilderStep (acc, current))
          cliqueCompatibilityItemBuilderInit) := by
  rcases cliqueCompatibilityItemBuilderStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed
      indexedLiteralOccurrenceEncodedType cliqueCompatibilityItemBuilderAccEncodedType
      cliqueCompatibilityItemBuilderStep cliqueCompatibilityItemBuilderInit hStep
      (cliqueCompatibilityItemBuilderTimePolynomial hStep) ?_
  intro source
  exact cliqueCompatibilityItemBuilderFold_loopTime_le hStep source

theorem cliqueCompatibilityItemsFromOccurrences_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
      cliqueCompatibilityItemsFromOccurrences := by
  have hFold := cliqueCompatibilityItemBuilderFold_tm_polytime
  have hFst :=
    TMPolyTimeMap.fst (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
  have hComp := TMPolyTimeMap.comp hFst hFold
  simpa [Function.comp, cliqueCompatibilityItemsFromOccurrences,
    cliqueCompatibilityItemBuilderAccEncodedType] using hComp

noncomputable def cliqueCompatibilityItemsFromOccurrencesTMBackedMap :
    TMBackedCostedMap
      (EncodedType.list indexedLiteralOccurrenceEncodedType)
      (EncodedType.list cliqueCompatibilityEdgeItemEncodedType)
      cliqueCompatibilityItemsFromOccurrences where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cliqueCompatibilityItemsFromOccurrences_polynomialSizeBound
  tm_polytime := cliqueCompatibilityItemsFromOccurrences_tm_polytime

end Clique
end Karp21
end ComplexityReduction
