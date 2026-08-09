import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range

/-!
TM-backed ordered vertex-pair candidate generation for faithful structured graph encodings.

This is an assembly component for the P16c graph-complement routes.  It
enumerates all ordered vertex pairs below a natural vertex bound; it does not
filter to strict unordered pairs and does not inspect the source edge list.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

/-! ### Ordered vertex-pair candidate generation -/

def vertexPairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def vertexPairListEncodedType : EncodedType :=
  EncodedType.list vertexPairEncodedType

def natPairCandidatesAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod vertexPairListEncodedType vertexPairListEncodedType)

def natPairCandidateCtx (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun u => (u, n)

def vertexPairSwap (p : Nat × Nat) : Nat × Nat :=
  (p.2, p.1)

def vertexPairRightSucc (p : Nat × Nat) : Nat × Nat :=
  (p.1, Nat.succ p.2)

def natPairCandidatesCore : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 =>
      natPairCandidatesCore n ++ natPairCandidateCtx n ++
        (natPairCandidateCtx n).map vertexPairSwap ++ [(n, n)]

def natPairCandidatesAcc (n : Nat) :
    natPairCandidatesAccEncodedType.Carrier :=
  (n, (natPairCandidateCtx n, natPairCandidatesCore n))

def natPairCandidatesBuilderInit : natPairCandidatesAccEncodedType.Carrier :=
  natPairCandidatesAcc 0

def natPairCandidatesBuilderStep
    (p : natPairCandidatesAccEncodedType.Carrier × Unit) :
    natPairCandidatesAccEncodedType.Carrier :=
  let next : Nat := p.1.1
  let ctx : List (Nat × Nat) := p.1.2.1
  let pairs : List (Nat × Nat) := p.1.2.2
  let nextSucc : Nat := Nat.succ next
  let nextCtx : List (Nat × Nat) := ctx.map vertexPairRightSucc ++ [(next, nextSucc)]
  let newRow : List (Nat × Nat) := ctx.map vertexPairSwap ++ [(next, next)]
  (nextSucc, (nextCtx, pairs ++ ctx ++ newRow))

def natPairCandidatesFromUnits (xs : List Unit) : List (Nat × Nat) :=
  (xs.foldl
      (fun acc x => natPairCandidatesBuilderStep (acc, x))
      natPairCandidatesBuilderInit).2.2

def natPairCandidates (n : Nat) : List (Nat × Nat) :=
  natPairCandidatesFromUnits (List.replicate n ())

theorem natPairCandidateCtx_succ (n : Nat) :
    natPairCandidateCtx (n + 1) =
      (natPairCandidateCtx n).map vertexPairRightSucc ++ [(n, n + 1)] := by
  simp [natPairCandidateCtx, vertexPairRightSucc, List.range_succ, Nat.succ_eq_add_one,
    List.map_map]

theorem natPairCandidatesBuilderStep_acc (n : Nat) (u : Unit) :
    natPairCandidatesBuilderStep (natPairCandidatesAcc n, u) =
      natPairCandidatesAcc (n + 1) := by
  simp [natPairCandidatesBuilderStep, natPairCandidatesAcc, natPairCandidatesCore,
    natPairCandidateCtx_succ]

theorem natPairCandidatesFold_acc_aux (N : Nat) :
    ∀ (rest : List Unit) (m : Nat),
      m + rawUnitListEncodedType.inputSize rest = N →
        rest.foldl
            (fun acc x => natPairCandidatesBuilderStep (acc, x))
            (natPairCandidatesAcc m) =
          natPairCandidatesAcc N
  | [], m, h => by
      simp [rawUnitList_inputSize_eq_length] at h
      subst N
      simp
  | u :: rest, m, h => by
      have hNext : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
        rw [rawUnitList_inputSize_eq_length] at h ⊢
        simp at h ⊢
        omega
      simp [natPairCandidatesBuilderStep_acc m u]
      exact natPairCandidatesFold_acc_aux N rest (m + 1) hNext

theorem natPairCandidatesFromUnits_eq_core (xs : List Unit) :
    natPairCandidatesFromUnits xs = natPairCandidatesCore xs.length := by
  have hFold :=
    natPairCandidatesFold_acc_aux (rawUnitListEncodedType.inputSize xs) xs 0 (by simp)
  rw [rawUnitList_inputSize_eq_length xs] at hFold
  simpa [natPairCandidatesFromUnits, natPairCandidatesBuilderInit,
    natPairCandidatesAcc] using congrArg (fun p => p.2.2) hFold

theorem natPairCandidates_replicate (n : Nat) :
    natPairCandidates n = natPairCandidatesCore n := by
  simpa [natPairCandidates] using
    natPairCandidatesFromUnits_eq_core (List.replicate n ())

theorem mem_natPairCandidateCtx_iff (n : Nat) (e : Nat × Nat) :
    e ∈ natPairCandidateCtx n ↔ e.1 < n ∧ e.2 = n := by
  cases e with
  | mk u v =>
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨a, ha, hEq⟩
        simp at hEq
        rcases hEq with ⟨rfl, rfl⟩
        exact ⟨List.mem_range.mp ha, rfl⟩
      · rintro ⟨hu, rfl⟩
        exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩

theorem mem_natPairCandidateCtx_swap_iff (n : Nat) (e : Nat × Nat) :
    e ∈ (natPairCandidateCtx n).map vertexPairSwap ↔ e.1 = n ∧ e.2 < n := by
  cases e with
  | mk u v =>
      constructor
      · intro h
        rcases List.mem_map.mp h with ⟨p, hp, hpEq⟩
        rcases p with ⟨a, b⟩
        have hp' := (mem_natPairCandidateCtx_iff n (a, b)).1 hp
        simp [vertexPairSwap] at hpEq
        omega
      · rintro ⟨hu, hv⟩
        rw [List.mem_map]
        refine ⟨(v, n), ?_, ?_⟩
        · exact (mem_natPairCandidateCtx_iff n (v, n)).2 ⟨hv, rfl⟩
        · subst hu
          simp [vertexPairSwap]

theorem mem_natPairCandidatesCore_iff (n : Nat) (e : Nat × Nat) :
    e ∈ natPairCandidatesCore n ↔ e.1 < n ∧ e.2 < n := by
  induction n with
  | zero =>
      simp [natPairCandidatesCore]
  | succ n ih =>
      cases e with
      | mk u v =>
          constructor
          · intro h
            simp [natPairCandidatesCore, mem_natPairCandidateCtx_iff,
              mem_natPairCandidateCtx_swap_iff, ih] at h
            omega
          · intro h
            have hCases :
                (u < n ∧ v < n) ∨ (u < n ∧ v = n) ∨
                  (u = n ∧ v < n) ∨ u = n ∧ v = n := by
              omega
            simpa [natPairCandidatesCore, ih, mem_natPairCandidateCtx_iff,
              mem_natPairCandidateCtx_swap_iff] using hCases

theorem natPairCandidateCtx_length (n : Nat) :
    (natPairCandidateCtx n).length = n := by
  simp [natPairCandidateCtx]

theorem natPairCandidatesCore_length (n : Nat) :
    (natPairCandidatesCore n).length = n * n := by
  induction n with
  | zero =>
      simp [natPairCandidatesCore]
  | succ n ih =>
      simp [natPairCandidatesCore, ih, natPairCandidateCtx_length]
      ring

theorem vertexPair_inputSize_le_of_lt {n : Nat} {e : Nat × Nat}
    (hu : e.1 < n) (hv : e.2 < n) :
    vertexPairEncodedType.inputSize e ≤ 2 * n + 3 := by
  cases e with
  | mk u v =>
      simp [vertexPairEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat] at *
      omega

theorem encodedList_inputSize_le_length_mul_bound (X : EncodedType)
    (xs : List X.Carrier) (B : Nat)
    (hB : ∀ x ∈ xs, X.inputSize x ≤ B) :
    (EncodedType.list X).inputSize xs ≤ xs.length * (B + 1) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : X.inputSize x ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, X.inputSize y ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have ih' := ih htail
      calc
        (EncodedType.list X).inputSize (x :: xs)
            = X.inputSize x + 1 + (EncodedType.list X).inputSize xs := by
              simp
        _ ≤ B + 1 + xs.length * (B + 1) := by
              omega
        _ = (x :: xs).length * (B + 1) := by
              simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

theorem natPairCandidatesCore_inputSize_le (n : Nat) :
    vertexPairListEncodedType.inputSize (natPairCandidatesCore n) ≤
      (n * n) * (2 * n + 4) := by
  have hList :=
    encodedList_inputSize_le_length_mul_bound vertexPairEncodedType
      (natPairCandidatesCore n) (2 * n + 3)
      (by
        intro e he
        have hmem := (mem_natPairCandidatesCore_iff n e).1 he
        exact vertexPair_inputSize_le_of_lt hmem.1 hmem.2)
  have hLen := natPairCandidatesCore_length n
  change vertexPairEncodedType.list.inputSize (natPairCandidatesCore n) ≤
    (n * n) * (2 * n + 4)
  calc
    vertexPairEncodedType.list.inputSize (natPairCandidatesCore n)
        ≤ (natPairCandidatesCore n).length * (2 * n + 3 + 1) := hList
    _ = (n * n) * (2 * n + 4) := by
          rw [hLen]

theorem natPairCandidateCtx_inputSize_le (n : Nat) :
    vertexPairListEncodedType.inputSize (natPairCandidateCtx n) ≤
      n * (2 * n + 4) := by
  have hList :=
    encodedList_inputSize_le_length_mul_bound vertexPairEncodedType
      (natPairCandidateCtx n) (2 * n + 3)
      (by
        intro e he
        have hmem := (mem_natPairCandidateCtx_iff n e).1 he
        cases e with
        | mk u v =>
            simp [vertexPairEncodedType, EncodedType.inputSize_prod,
              EncodedType.inputSize_nat] at hmem ⊢
            omega)
  have hLen := natPairCandidateCtx_length n
  change vertexPairEncodedType.list.inputSize (natPairCandidateCtx n) ≤
    n * (2 * n + 4)
  calc
    vertexPairEncodedType.list.inputSize (natPairCandidateCtx n)
        ≤ (natPairCandidateCtx n).length * (2 * n + 3 + 1) := hList
    _ = n * (2 * n + 4) := by
          rw [hLen]

theorem natPairCandidatesAcc_inputSize_le (n : Nat) :
    natPairCandidatesAccEncodedType.inputSize (natPairCandidatesAcc n) ≤
      10 * ((n + 2) * (n + 2) * (n + 2)) + 20 := by
  have hCtx := natPairCandidateCtx_inputSize_le n
  have hCore := natPairCandidatesCore_inputSize_le n
  simp [natPairCandidatesAccEncodedType, natPairCandidatesAcc,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat] at *
  nlinarith

theorem natPairCandidatesCore_inputSize_le_cubic (n : Nat) :
    vertexPairListEncodedType.inputSize (natPairCandidatesCore n) ≤
      10 * ((n + 2) * (n + 2) * (n + 2)) + 20 := by
  have hCore := natPairCandidatesCore_inputSize_le n
  nlinarith

theorem natPairCandidatesCubicBound_mono {m N : Nat} (h : m ≤ N) :
    10 * ((m + 2) * (m + 2) * (m + 2)) + 20 ≤
      10 * ((N + 2) * (N + 2) * (N + 2)) + 20 := by
  have h1 : m + 2 ≤ N + 2 := by omega
  have h2 : (m + 2) * (m + 2) ≤ (N + 2) * (N + 2) :=
    Nat.mul_le_mul h1 h1
  have h3 :
      (m + 2) * (m + 2) * (m + 2) ≤
        (N + 2) * (N + 2) * (N + 2) :=
    Nat.mul_le_mul h2 h1
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 h3) 20

theorem natPairCandidatesCubicBound_poly (N : Nat) :
    10 * ((N + 2) * (N + 2) * (N + 2)) + 20 ≤
      1000 * N ^ 3 + 1000 := by
  by_cases hZero : N = 0
  · simp [hZero]
  · have hPos : 1 ≤ N := by omega
    have h1 : N + 2 ≤ 3 * N := by omega
    have h2 : (N + 2) * (N + 2) ≤ (3 * N) * (3 * N) :=
      Nat.mul_le_mul h1 h1
    have h3 :
        (N + 2) * (N + 2) * (N + 2) ≤
          (3 * N) * (3 * N) * (3 * N) :=
      Nat.mul_le_mul h2 h1
    calc
      10 * ((N + 2) * (N + 2) * (N + 2)) + 20
          ≤ 10 * ((3 * N) * (3 * N) * (3 * N)) + 20 := by
            exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 h3) 20
      _ ≤ 1000 * N ^ 3 + 1000 := by
            nlinarith

theorem natPairCandidatesFromUnits_inputSize_le (xs : List Unit) :
    vertexPairListEncodedType.inputSize (natPairCandidatesFromUnits xs) ≤
      10 * ((rawUnitListEncodedType.inputSize xs + 2) *
        (rawUnitListEncodedType.inputSize xs + 2) *
        (rawUnitListEncodedType.inputSize xs + 2)) + 20 := by
  rw [natPairCandidatesFromUnits_eq_core, rawUnitList_inputSize_eq_length]
  exact natPairCandidatesCore_inputSize_le_cubic xs.length

theorem natPairCandidatesFromUnits_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : List Unit => rawUnitListEncodedType.inputSize xs)
      (fun ys : List (Nat × Nat) => vertexPairListEncodedType.inputSize ys)
      natPairCandidatesFromUnits :=
  PolynomialSizeBound.intro_with 3 1000 1000 (by
    intro xs
    have h := natPairCandidatesFromUnits_inputSize_le xs
    exact h.trans (natPairCandidatesCubicBound_poly (rawUnitListEncodedType.inputSize xs)))

theorem natPairCandidates_inputSize_le (n : Nat) :
    vertexPairListEncodedType.inputSize (natPairCandidates n) ≤
      10 * ((EncodedType.nat.inputSize n + 2) *
        (EncodedType.nat.inputSize n + 2) *
        (EncodedType.nat.inputSize n + 2)) + 20 := by
  rw [natPairCandidates, natPairCandidatesFromUnits_eq_core]
  have hCore := natPairCandidatesCore_inputSize_le_cubic n
  have hMono := natPairCandidatesCubicBound_mono (m := n) (N := n + 1) (by omega)
  simpa [EncodedType.inputSize_nat] using hCore.trans hMono

theorem natPairCandidates_polynomialSizeBound :
    PolynomialSizeBound
      (fun n : Nat => EncodedType.nat.inputSize n)
      (fun ys : List (Nat × Nat) => vertexPairListEncodedType.inputSize ys)
      natPairCandidates :=
  PolynomialSizeBound.intro_with 3 1000 1000 (by
    intro n
    have h := natPairCandidates_inputSize_le n
    exact h.trans (natPairCandidatesCubicBound_poly (EncodedType.nat.inputSize n)))

theorem mem_natPairCandidates_iff (n : Nat) (e : Nat × Nat) :
    e ∈ natPairCandidates n ↔ e.1 < n ∧ e.2 < n := by
  rw [natPairCandidates_replicate]
  exact mem_natPairCandidatesCore_iff n e

theorem vertexPairSwap_tm_polytime :
    TMPolyTimeMap vertexPairEncodedType vertexPairEncodedType vertexPairSwap := by
  have hFst : TMPolyTimeMap vertexPairEncodedType EncodedType.nat (fun p : Nat × Nat => p.1) :=
    by
      simpa [vertexPairEncodedType] using
        TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSnd : TMPolyTimeMap vertexPairEncodedType EncodedType.nat (fun p : Nat × Nat => p.2) :=
    by
      simpa [vertexPairEncodedType] using
        TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hPair := TMPolyTimeMap.prod_mk hSnd hFst
  simpa [vertexPairSwap, vertexPairEncodedType] using hPair

theorem vertexPairRightSucc_tm_polytime :
    TMPolyTimeMap vertexPairEncodedType vertexPairEncodedType vertexPairRightSucc := by
  have hFst : TMPolyTimeMap vertexPairEncodedType EncodedType.nat (fun p : Nat × Nat => p.1) :=
    by
      simpa [vertexPairEncodedType] using
        TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hSnd : TMPolyTimeMap vertexPairEncodedType EncodedType.nat (fun p : Nat × Nat => p.2) :=
    by
      simpa [vertexPairEncodedType] using
        TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSndSucc :
      TMPolyTimeMap vertexPairEncodedType EncodedType.nat
        (fun p : Nat × Nat => Nat.succ p.2) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hSnd
    simpa [Function.comp] using hComp
  have hPair := TMPolyTimeMap.prod_mk hFst hSndSucc
  simpa [vertexPairRightSucc, vertexPairEncodedType] using hPair

theorem natPairCandidatesBuilderStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod natPairCandidatesAccEncodedType (EncodedType.raw Unit))
      natPairCandidatesAccEncodedType
      natPairCandidatesBuilderStep := by
  let A := natPairCandidatesAccEncodedType
  let R := vertexPairListEncodedType
  let X := EncodedType.prod A (EncodedType.raw Unit)
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A (EncodedType.raw Unit)
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.prod R R)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [A, X, natPairCandidatesAccEncodedType] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod R R) (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod R R)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [A, X, natPairCandidatesAccEncodedType] using hComp
  have hCtx : TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst R R
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [X] using hComp
  have hPairs : TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd R R
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [X] using hComp
  have hNextSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    simpa [Function.comp] using hComp
  have hCtxUpdatedOld :
      TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.1.map vertexPairRightSucc) := by
    have hMap := TMPolyTimeMap.list_map vertexPairRightSucc_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCtx
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hNewCtxEntry :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => ((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))) :=
    TMPolyTimeMap.prod_mk hNext hNextSucc
  have hNewCtxSingleton :
      TMPolyTimeMap X R
        (fun p : X.Carrier => [((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton vertexPairEncodedType)
      hNewCtxEntry
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hNextCtxInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc,
            [((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))])) :=
    TMPolyTimeMap.prod_mk hCtxUpdatedOld hNewCtxSingleton
  have hNextCtx :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc)
            ([((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))] : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hNextCtxInput
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hRowOld : TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.1.map vertexPairSwap) := by
    have hMap := TMPolyTimeMap.list_map vertexPairSwap_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCtx
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hSelfEntry :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => ((p.1.1 : Nat), (p.1.1 : Nat))) :=
    TMPolyTimeMap.prod_mk hNext hNext
  have hSelfSingleton :
      TMPolyTimeMap X R
        (fun p : X.Carrier => [((p.1.1 : Nat), (p.1.1 : Nat))]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton vertexPairEncodedType)
      hSelfEntry
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hNewRowInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          ((p.1.2.1 : List (Nat × Nat)).map vertexPairSwap,
            [((p.1.1 : Nat), (p.1.1 : Nat))])) :=
    TMPolyTimeMap.prod_mk hRowOld hSelfSingleton
  have hNewRow :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairSwap)
            ([((p.1.1 : Nat), (p.1.1 : Nat))] : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hNewRowInput
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hPairsCtxInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier => (p.1.2.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hPairs hCtx
  have hPairsCtx :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append (p.1.2.2 : List (Nat × Nat))
            (p.1.2.1 : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hPairsCtxInput
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hPairsAllInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          (List.append (p.1.2.2 : List (Nat × Nat)) (p.1.2.1 : List (Nat × Nat)),
            List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairSwap)
              ([((p.1.1 : Nat), (p.1.1 : Nat))] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hPairsCtx hNewRow
  have hPairsAll :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append
            (List.append (p.1.2.2 : List (Nat × Nat))
              (p.1.2.1 : List (Nat × Nat)))
            (List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairSwap)
              ([((p.1.1 : Nat), (p.1.1 : Nat))] : List (Nat × Nat)))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hPairsAllInput
    simpa only [Function.comp] using hComp
  have hOutPayload :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          (List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc)
              ([((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))] : List (Nat × Nat)),
            List.append
              (List.append (p.1.2.2 : List (Nat × Nat))
                (p.1.2.1 : List (Nat × Nat)))
              (List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairSwap)
                ([((p.1.1 : Nat), (p.1.1 : Nat))] : List (Nat × Nat))))) :=
    TMPolyTimeMap.prod_mk hNextCtx hPairsAll
  have hOut :=
    TMPolyTimeMap.prod_mk hNextSucc hOutPayload
  convert hOut using 1

noncomputable def natPairCandidatesFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod natPairCandidatesAccEncodedType (EncodedType.raw Unit)).encode
        natPairCandidatesAccEncodedType.encode
        natPairCandidatesBuilderStep) :
    Polynomial Nat :=
  let bound :=
    Polynomial.C 10 *
      ((Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2)) +
      Polynomial.C 20
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
    (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))

theorem natPairCandidatesFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod natPairCandidatesAccEncodedType (EncodedType.raw Unit)).encode
        natPairCandidatesAccEncodedType.encode
        natPairCandidatesBuilderStep)
    (source : List Unit) :
    2 +
      TM2Programs.listFoldTypedLoopTime
        (EncodedType.raw Unit) natPairCandidatesAccEncodedType
        natPairCandidatesBuilderStep hStep natPairCandidatesBuilderInit source ≤
        (natPairCandidatesFoldTimePolynomial hStep).eval
          (rawUnitListEncodedType.inputSize source) := by
  let X := EncodedType.raw Unit
  let Y := natPairCandidatesAccEncodedType
  let N := rawUnitListEncodedType.inputSize source
  let bound : Polynomial Nat :=
    Polynomial.C 10 *
      ((Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2)) +
      Polynomial.C 20
  let B := bound.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hBoundEval :
      B = 10 * ((N + 2) * (N + 2) * (N + 2)) + 20 := by
    simp [B, bound, Polynomial.eval_add, Polynomial.eval_mul]
  have hLoopAux :
      ∀ (rest : List Unit) (m : Nat),
        m + rawUnitListEncodedType.inputSize rest = N →
          TM2Programs.listFoldTypedLoopTime
            X Y natPairCandidatesBuilderStep hStep (natPairCandidatesAcc m) rest ≤
            C * rawUnitListEncodedType.inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro m _h
        simp [TM2Programs.listFoldTypedLoopTime, rawUnitList_inputSize_eq_length]
    | cons u rest ih =>
        intro m hRest
        have hmN : m ≤ N := by
          omega
        have hmSuccN : m + 1 ≤ N := by
          rw [rawUnitList_inputSize_eq_length] at hRest
          simp at hRest
          omega
        have hRestTail : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
          rw [rawUnitList_inputSize_eq_length] at hRest ⊢
          simp at hRest ⊢
          omega
        have hAcc :
            Y.inputSize (natPairCandidatesAcc m) ≤ B := by
          have hBase := natPairCandidatesAcc_inputSize_le m
          exact hBase.trans (by
            rw [hBoundEval]
            exact natPairCandidatesCubicBound_mono hmN)
        have hNext :
            Y.inputSize (natPairCandidatesBuilderStep (natPairCandidatesAcc m, u)) ≤ B := by
          rw [natPairCandidatesBuilderStep_acc m u]
          have hBase := natPairCandidatesAcc_inputSize_le (m + 1)
          exact hBase.trans (by
            rw [hBoundEval]
            exact natPairCandidatesCubicBound_mono hmSuccN)
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod Y X).inputSize (natPairCandidatesAcc m, u)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize (natPairCandidatesAcc m, u) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize (natPairCandidatesAcc m) + 1 + X.inputSize u ≤ B + N + 5
            have hx : X.inputSize u = 0 := by rfl
            rw [hx]
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (natPairCandidatesAcc m)).length
                (Y.encode (natPairCandidatesBuilderStep (natPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize (natPairCandidatesAcc m, u))) ≤
              C * (X.inputSize u + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [Y, EncodedType.inputSize] using hAcc)
              (by simpa [Y, EncodedType.inputSize] using hNext)
              hStepTime
        have hTail :=
          ih (m + 1) hRestTail
        calc
          TM2Programs.listFoldTypedLoopTime X Y natPairCandidatesBuilderStep hStep
              (natPairCandidatesAcc m) (u :: rest)
              =
            TM2Programs.listFoldTypedLoopTime X Y natPairCandidatesBuilderStep hStep
              (natPairCandidatesBuilderStep (natPairCandidatesAcc m, u)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (natPairCandidatesAcc m)).length
                (Y.encode (natPairCandidatesBuilderStep (natPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize (natPairCandidatesAcc m, u))) := by
                rfl
          _ =
            TM2Programs.listFoldTypedLoopTime X Y natPairCandidatesBuilderStep hStep
              (natPairCandidatesAcc (m + 1)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (natPairCandidatesAcc m)).length
                (Y.encode (natPairCandidatesBuilderStep (natPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize (natPairCandidatesAcc m, u))) := by
                rw [natPairCandidatesBuilderStep_acc m u]
          _ ≤ C * rawUnitListEncodedType.inputSize rest + C * (X.inputSize u + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * rawUnitListEncodedType.inputSize (u :: rest) := by
                have hConsSize :
                    rawUnitListEncodedType.inputSize (u :: rest) =
                      rawUnitListEncodedType.inputSize rest + 1 := by
                  exact rawUnitList_inputSize_cons u rest
                rw [hConsSize]
                simp [X, EncodedType.inputSize, EncodedType.raw, Nat.mul_add]
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
        X Y natPairCandidatesBuilderStep hStep natPairCandidatesBuilderInit source ≤ C * N := by
    simpa [X, Y, natPairCandidatesBuilderInit, N] using hLoopAux source 0 (by simp [N])
  have hTimeEval :
      (natPairCandidatesFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [natPairCandidatesFoldTimePolynomial, bound, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem natPairCandidatesFold_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      natPairCandidatesAccEncodedType
      (fun xs : List Unit =>
        xs.foldl
          (fun acc x => natPairCandidatesBuilderStep (acc, x))
          natPairCandidatesBuilderInit) := by
  rcases natPairCandidatesBuilderStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed
      (EncodedType.raw Unit) natPairCandidatesAccEncodedType
      natPairCandidatesBuilderStep natPairCandidatesBuilderInit hStep
      (natPairCandidatesFoldTimePolynomial hStep) ?_
  intro source
  exact natPairCandidatesFold_loopTime_le hStep source

theorem natPairCandidatesFromUnits_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      vertexPairListEncodedType
      natPairCandidatesFromUnits := by
  have hFold := natPairCandidatesFold_tm_polytime
  have hPayload :=
    TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod vertexPairListEncodedType vertexPairListEncodedType)
  have hPairs := TMPolyTimeMap.snd vertexPairListEncodedType vertexPairListEncodedType
  have hPayloadComp := TMPolyTimeMap.comp hPayload hFold
  have hPairsComp := TMPolyTimeMap.comp hPairs hPayloadComp
  simpa [Function.comp, natPairCandidatesFromUnits, natPairCandidatesAccEncodedType] using
    hPairsComp

noncomputable def natPairCandidatesFromUnitsTMBackedMap :
    TMBackedCostedMap
      rawUnitListEncodedType
      vertexPairListEncodedType
      natPairCandidatesFromUnits where
  costed := CostedMap.of_encodedPolynomialSizeBound natPairCandidatesFromUnits_polynomialSizeBound
  tm_polytime := natPairCandidatesFromUnits_tm_polytime

theorem natPairCandidates_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      vertexPairListEncodedType
      natPairCandidates := by
  have hComp :=
    TMPolyTimeMap.comp natPairCandidatesFromUnits_tm_polytime
      natToRawUnitListTMBackedMap.tm_polytime
  convert hComp using 1

noncomputable def natPairCandidatesTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      vertexPairListEncodedType
      natPairCandidates where
  costed := CostedMap.of_encodedPolynomialSizeBound natPairCandidates_polynomialSizeBound
  tm_polytime := natPairCandidates_tm_polytime

end Karp21
end ComplexityReduction
