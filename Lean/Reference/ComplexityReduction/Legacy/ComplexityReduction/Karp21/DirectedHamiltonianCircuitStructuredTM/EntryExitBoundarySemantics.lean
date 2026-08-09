/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryTM

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! Semantic equivalence for the executable entry slot-boundary scan. -/

def dhcEntryBoundaryLastOr
    (prev : dhcIndexedIncidenceEncodedType.Carrier) :
    List dhcIndexedIncidenceEncodedType.Carrier → dhcIndexedIncidenceEncodedType.Carrier
  | [] => prev
  | x :: xs => dhcEntryBoundaryLastOr x xs

theorem dhcEntryBoundaryFold_active_invariant
    (budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier) (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
        (budget, (slot, (true, (prev, out)))) =
      (budget,
        (slot,
          (true,
            (dhcEntryBoundaryLastOr prev xs,
              out ++ dhcEntryArcsForSlotFromPrevIndexed budget slot prev xs)))) := by
  induction xs generalizing prev out with
  | nil =>
      simp [dhcEntryBoundaryLastOr, dhcEntryArcsForSlotFromPrevIndexed]
      rfl
  | cons x xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
            (dhcEntryBoundaryFoldStep ((budget, (slot, (true, (prev, out)))),
              Sum.inr x)) =
          (budget,
            (slot,
              (true,
                (dhcEntryBoundaryLastOr prev (x :: xs),
                  out ++ dhcEntryArcsForSlotFromPrevIndexed budget slot prev (x :: xs)))))
      rw [show
          dhcEntryBoundaryFoldStep
              ((budget, (slot, (true, (prev, out)))), Sum.inr x) =
            (budget,
              (slot,
                (true,
                  (x,
                    out ++
                      dhcEntryBoundaryBlock (budget, (slot, (true, (prev, x)))))))) by
        rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
            (budget,
              (slot,
                (true,
                  (x,
                    out ++
                      dhcEntryBoundaryBlock (budget, (slot, (true, (prev, x))))))))
            =
          (budget,
            (slot,
              (true,
                (dhcEntryBoundaryLastOr x xs,
                  (out ++ dhcEntryBoundaryBlock (budget, (slot, (true, (prev, x))))) ++
                    dhcEntryArcsForSlotFromPrevIndexed budget slot x xs)))) := by
            exact ih x
              (out ++ dhcEntryBoundaryBlock (budget, (slot, (true, (prev, x)))))
        _ =
          (budget,
            (slot,
              (true,
                (dhcEntryBoundaryLastOr prev (x :: xs),
                  out ++ dhcEntryArcsForSlotFromPrevIndexed budget slot prev (x :: xs))))) := by
            by_cases hSame :
                dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource x
            · have hSameRaw : (prev.1.1 : Nat) = (x.1.1 : Nat) := by
                simpa [dhcBoundaryIncidenceSource] using hSame
              simp [dhcEntryBoundaryLastOr, dhcEntryBoundaryBlock,
                dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
                dhcEntryArcsForSlotFromPrevIndexed, hSameRaw]
            · have hSameRaw : ¬(prev.1.1 : Nat) = (x.1.1 : Nat) := by
                simpa [dhcBoundaryIncidenceSource] using hSame
              have hBeq : Nat.beq (prev.1.1 : Nat) (x.1.1 : Nat) = false := by
                rw [← Bool.not_eq_true, Nat.beq_eq]
                exact hSameRaw
              simp [dhcEntryBoundaryLastOr, dhcEntryBoundaryBlock,
                dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
                dhcEntryArcsForSlotFromPrevIndexed, hBeq,
                List.append_assoc]
              intro hEq
              exact False.elim (hSameRaw hEq)

theorem dhcEntryBoundaryFold_inactive_invariant
    (budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
        (budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))) =
      match xs with
      | [] => (budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out))))
      | x :: xs =>
          (budget,
            (slot,
              (true,
                (dhcEntryBoundaryLastOr x xs,
                  out ++ dhcEntryArcsForSlotFromBoundaryIndexed budget slot (x :: xs))))) := by
  cases xs with
  | nil =>
      simp
      rfl
  | cons x xs =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcEntryBoundaryFoldStep (acc, instr))
            (dhcEntryBoundaryFoldStep
              ((budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))),
                Sum.inr x)) =
          (budget,
            (slot,
              (true,
                (dhcEntryBoundaryLastOr x xs,
                  out ++ dhcEntryArcsForSlotFromBoundaryIndexed budget slot (x :: xs)))))
      rw [show
          dhcEntryBoundaryFoldStep
              ((budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))),
                Sum.inr x) =
            (budget,
              (slot,
                (true,
                  (x,
                    out ++ dhcEntryArcForSlotBlockFromIndexed budget slot x)))) by
        simp [dhcEntryBoundaryFoldStep, dhcEntryBoundaryFoldRightStep,
          dhcEntryBoundaryBlock]
        rfl]
      have hFold :=
        dhcEntryBoundaryFold_active_invariant budget slot x xs
          (out ++ dhcEntryArcForSlotBlockFromIndexed budget slot x)
      simpa [dhcEntryArcsForSlotFromBoundaryIndexed, List.append_assoc] using hFold

theorem dhcEntryArcsForSlotFromBoundaryIndexedExecutable_eq
    (p : dhcSlotIndexedIncidenceListRaw) :
    dhcEntryArcsForSlotFromBoundaryIndexedExecutable p =
      dhcEntryArcsForSlotFromBoundaryIndexed p.1 p.2.1 p.2.2 := by
  rcases p with ⟨budget, slot, xs⟩
  rw [dhcEntryArcsForSlotFromBoundaryIndexedExecutable, dhcEntryBoundaryFoldResult,
    dhcEntryBoundaryInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcEntryBoundaryFoldStep (dhcEntryBoundaryFoldInit, Sum.inl (budget, slot)) =
        (budget,
          (slot,
            (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat)))))) by
    rfl]
  have hFold :=
    congrArg (fun acc : dhcEntryBoundaryAccEncodedType.Carrier => acc.2.2.2.2)
      (dhcEntryBoundaryFold_inactive_invariant budget slot xs ([] : List (Nat × Nat)))
  cases xs with
  | nil =>
      simp [dhcEntryArcsForSlotFromBoundaryIndexed] at hFold ⊢
  | cons x xs =>
      simpa [dhcEntryArcsForSlotFromBoundaryIndexed] using hFold

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
