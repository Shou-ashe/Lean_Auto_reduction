import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Lookup

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Textbook pair order for the direct structured Partition-to-MaxCut route.

The checked strict-pair generator emits pairs in increasing right endpoint.  The
textbook edge list is row-major in the left endpoint.  Mirroring a strict pair
`(u,v)` below `n` to `(n - (v+1), n - (u+1))` turns the strict order into the
reverse of the textbook row-major order.
-/

def mirrorVertexPair (n : Nat) (p : Nat × Nat) : Nat × Nat :=
  (n - (p.2 + 1), n - (p.1 + 1))

def vertexPairShiftSucc (p : Nat × Nat) : Nat × Nat :=
  (p.1 + 1, p.2 + 1)

def maxCutTextbookPairRow (n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun j => (0, j + 1)

def maxCutTextbookPairCandidates : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 =>
      maxCutTextbookPairRow n ++
        (maxCutTextbookPairCandidates n).map vertexPairShiftSucc

theorem maxCutTextbookPairRow_succ (n : Nat) :
    maxCutTextbookPairRow (n + 1) =
      maxCutTextbookPairRow n ++ [(0, n + 1)] := by
  simp [maxCutTextbookPairRow, List.range_succ, List.map_append]

theorem maxCutTextbookPairRow_cons_shift (n : Nat) :
    maxCutTextbookPairRow (n + 1) =
      (0, 1) :: (maxCutTextbookPairRow n).map vertexPairRightSucc := by
  simp [maxCutTextbookPairRow, List.range_succ_eq_map, vertexPairRightSucc,
    List.map_map, Nat.succ_eq_add_one]

theorem mirrorVertexPair_shift_of_strict {n : Nat} {p : Nat × Nat}
    (hp : p.1 < n ∧ p.2 < n ∧ p.1 < p.2) :
    mirrorVertexPair (n + 1) p =
      vertexPairShiftSucc (mirrorVertexPair n p) := by
  rcases p with ⟨u, v⟩
  simp [mirrorVertexPair, vertexPairShiftSucc] at hp ⊢
  omega

theorem mirrorVertexPair_rightSucc_of_ctx {n : Nat} {p : Nat × Nat}
    (hp : p ∈ natPairCandidateCtx n) :
    mirrorVertexPair (n + 2) (vertexPairRightSucc p) =
      vertexPairRightSucc (mirrorVertexPair (n + 1) p) := by
  rcases p with ⟨u, v⟩
  have hp' := (mem_natPairCandidateCtx_iff n (u, v)).1 hp
  simp [mirrorVertexPair, vertexPairRightSucc] at hp' ⊢
  omega

theorem natPairCandidateCtx_mirror_reverse_eq_row (n : Nat) :
    ((natPairCandidateCtx n).map (mirrorVertexPair (n + 1))).reverse =
      maxCutTextbookPairRow n := by
  induction n with
  | zero =>
      simp [natPairCandidateCtx, maxCutTextbookPairRow]
  | succ n ih =>
      have hMap :
          (natPairCandidateCtx n).map
              (fun p => mirrorVertexPair (n + 2) (vertexPairRightSucc p)) =
            (natPairCandidateCtx n).map
              (fun p => vertexPairRightSucc (mirrorVertexPair (n + 1) p)) := by
        apply List.map_congr_left
        intro p hp
        exact mirrorVertexPair_rightSucc_of_ctx hp
      calc
        ((natPairCandidateCtx (n + 1)).map (mirrorVertexPair (n + 2))).reverse =
            (0, 1) ::
              ((natPairCandidateCtx n).map
                (fun p => mirrorVertexPair (n + 2) (vertexPairRightSucc p))).reverse := by
              rw [natPairCandidateCtx_succ]
              simp [List.map_append, List.map_map, mirrorVertexPair]
        _ =
            (0, 1) ::
              ((natPairCandidateCtx n).map
                (fun p => vertexPairRightSucc (mirrorVertexPair (n + 1) p))).reverse := by
              rw [hMap]
        _ =
            (0, 1) ::
              (((natPairCandidateCtx n).map (mirrorVertexPair (n + 1))).reverse).map
                vertexPairRightSucc := by
              simp [List.map_map]
        _ = (0, 1) :: (maxCutTextbookPairRow n).map vertexPairRightSucc := by
              rw [ih]
        _ = maxCutTextbookPairRow (n + 1) := by
              exact (maxCutTextbookPairRow_cons_shift n).symm

theorem strictNatPairCandidatesCore_mirror_reverse_eq_textbook (n : Nat) :
    ((strictNatPairCandidatesCore n).map (mirrorVertexPair n)).reverse =
      maxCutTextbookPairCandidates n := by
  induction n with
  | zero =>
      simp [strictNatPairCandidatesCore, maxCutTextbookPairCandidates]
  | succ n ih =>
      have hMap :
          (strictNatPairCandidatesCore n).map (mirrorVertexPair (n + 1)) =
            (strictNatPairCandidatesCore n).map
              (fun p => vertexPairShiftSucc (mirrorVertexPair n p)) := by
        apply List.map_congr_left
        intro p hp
        exact mirrorVertexPair_shift_of_strict
          ((mem_strictNatPairCandidatesCore_iff n p).1 hp)
      calc
        ((strictNatPairCandidatesCore (n + 1)).map (mirrorVertexPair (n + 1))).reverse =
            ((natPairCandidateCtx n).map (mirrorVertexPair (n + 1))).reverse ++
              ((strictNatPairCandidatesCore n).map (mirrorVertexPair (n + 1))).reverse := by
              rw [strictNatPairCandidatesCore, List.map_append, List.reverse_append]
        _ =
            maxCutTextbookPairRow n ++
              ((strictNatPairCandidatesCore n).map
                (fun p => vertexPairShiftSucc (mirrorVertexPair n p))).reverse := by
              rw [natPairCandidateCtx_mirror_reverse_eq_row, hMap]
        _ =
            maxCutTextbookPairRow n ++
              (((strictNatPairCandidatesCore n).map (mirrorVertexPair n)).reverse).map
                vertexPairShiftSucc := by
              simp [List.map_map]
        _ =
            maxCutTextbookPairRow n ++
              (maxCutTextbookPairCandidates n).map vertexPairShiftSucc := by
              rw [ih]
        _ = maxCutTextbookPairCandidates (n + 1) := by
              simp [maxCutTextbookPairCandidates]

theorem strictNatPairCandidates_mirror_reverse_eq_textbook (n : Nat) :
    ((strictNatPairCandidates n).map (mirrorVertexPair n)).reverse =
      maxCutTextbookPairCandidates n := by
  rw [strictNatPairCandidates_replicate]
  exact strictNatPairCandidatesCore_mirror_reverse_eq_textbook n

theorem mirrorVertexPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat vertexPairEncodedType)
      vertexPairEncodedType
      (fun p : Nat × (Nat × Nat) => mirrorVertexPair p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat vertexPairEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat vertexPairEncodedType
  have hPair : TMPolyTimeMap X vertexPairEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat vertexPairEncodedType
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hPair
    simpa [Function.comp, X, vertexPairEncodedType] using hComp
  have hV : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hPair
    simpa [Function.comp, X, vertexPairEncodedType] using hComp
  have hUSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.2.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hU
    simpa [Function.comp] using hComp
  have hVSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.2.2) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hV
    simpa [Function.comp] using hComp
  have hLeftInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, Nat.succ p.2.2)) :=
    TMPolyTimeMap.prod_mk hN hVSucc
  have hRightInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, Nat.succ p.2.1)) :=
    TMPolyTimeMap.prod_mk hN hUSucc
  have hLeft : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => Nat.sub (p.1 : Nat) (Nat.succ (p.2.2 : Nat))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hLeftInput
    simpa [Function.comp, X] using hComp
  have hRight : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => Nat.sub (p.1 : Nat) (Nat.succ (p.2.1 : Nat))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hRightInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hLeft hRight
  simpa [mirrorVertexPair, vertexPairEncodedType, X, Nat.succ_eq_add_one] using hOut

end MaxCut
end Karp21
end ComplexityReduction
