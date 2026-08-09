/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryExitTM

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! Semantic equivalence for the executable exit slot-boundary scan. -/

def dhcExitBoundaryLastOr
    (prev : dhcIndexedIncidenceEncodedType.Carrier) :
    List dhcIndexedIncidenceEncodedType.Carrier → dhcIndexedIncidenceEncodedType.Carrier
  | [] => prev
  | x :: xs => dhcExitBoundaryLastOr x xs

def dhcExitArcsForSlotFromPrevIndexedPending
    (budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier) :
    List dhcIndexedIncidenceEncodedType.Carrier → List (Nat × Nat)
  | [] => []
  | inc :: rest =>
      (match dhcBoundarySameSourceBool prev inc with
        | true => []
        | false => dhcExitArcForSlotBlockFromIndexed budget slot prev) ++
        dhcExitArcsForSlotFromPrevIndexedPending budget slot inc rest

theorem dhcExitBoundaryFold_active_invariant
    (budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier) (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
        (budget, (slot, (true, (prev, out)))) =
      (budget,
        (slot,
          (true,
            (dhcExitBoundaryLastOr prev xs,
              out ++ dhcExitArcsForSlotFromPrevIndexedPending budget slot prev xs)))) := by
  induction xs generalizing prev out with
  | nil =>
      simp [dhcExitBoundaryLastOr, dhcExitArcsForSlotFromPrevIndexedPending]
      rfl
  | cons x xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
            (dhcExitBoundaryFoldStep ((budget, (slot, (true, (prev, out)))),
              Sum.inr x)) =
          (budget,
            (slot,
              (true,
                (dhcExitBoundaryLastOr prev (x :: xs),
                  out ++
                    dhcExitArcsForSlotFromPrevIndexedPending budget slot prev (x :: xs)))))
      rw [show
          dhcExitBoundaryFoldStep
              ((budget, (slot, (true, (prev, out)))), Sum.inr x) =
            (budget,
              (slot,
                (true,
                  (x,
                    out ++
                      dhcExitBoundaryBlock (budget, (slot, (true, (prev, x)))))))) by
        rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
            (budget,
              (slot,
                (true,
                  (x,
                    out ++
                      dhcExitBoundaryBlock (budget, (slot, (true, (prev, x))))))))
            =
          (budget,
            (slot,
              (true,
                (dhcExitBoundaryLastOr x xs,
                  (out ++ dhcExitBoundaryBlock (budget, (slot, (true, (prev, x))))) ++
                    dhcExitArcsForSlotFromPrevIndexedPending budget slot x xs)))) := by
            exact ih x
              (out ++ dhcExitBoundaryBlock (budget, (slot, (true, (prev, x)))))
        _ =
          (budget,
            (slot,
              (true,
                (dhcExitBoundaryLastOr prev (x :: xs),
                  out ++
                    dhcExitArcsForSlotFromPrevIndexedPending budget slot prev (x :: xs))))) := by
            by_cases hSame :
                dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource x
            · have hSameRaw : (prev.1.1 : Nat) = (x.1.1 : Nat) := by
                simpa [dhcBoundaryIncidenceSource] using hSame
              simp [dhcExitBoundaryLastOr, dhcExitBoundaryBlock,
                dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
                dhcExitArcsForSlotFromPrevIndexedPending, hSameRaw]
            · have hSameRaw : ¬(prev.1.1 : Nat) = (x.1.1 : Nat) := by
                simpa [dhcBoundaryIncidenceSource] using hSame
              have hBeq : Nat.beq (prev.1.1 : Nat) (x.1.1 : Nat) = false := by
                rw [← Bool.not_eq_true, Nat.beq_eq]
                exact hSameRaw
              simp [dhcExitBoundaryLastOr, dhcExitBoundaryBlock,
                dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource,
                dhcExitArcsForSlotFromPrevIndexedPending, hBeq,
                List.append_assoc]

theorem dhcExitBoundaryFold_inactive_invariant
    (budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
        (budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))) =
      match xs with
      | [] => (budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out))))
      | x :: xs =>
          (budget,
            (slot,
              (true,
                (dhcExitBoundaryLastOr x xs,
                  out ++ dhcExitArcsForSlotFromPrevIndexedPending budget slot x xs)))) := by
  cases xs with
  | nil =>
      simp
      rfl
  | cons x xs =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcExitBoundaryFoldStep (acc, instr))
            (dhcExitBoundaryFoldStep
              ((budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))),
                Sum.inr x)) =
          (budget,
            (slot,
              (true,
                (dhcExitBoundaryLastOr x xs,
                  out ++ dhcExitArcsForSlotFromPrevIndexedPending budget slot x xs))))
      rw [show
          dhcExitBoundaryFoldStep
              ((budget, (slot, (false, (dhcEntryExitBoundaryDummyIncidence, out)))),
                Sum.inr x) =
            (budget,
              (slot,
                (true,
                  (x,
                    out ++ ([] : List (Nat × Nat)))))) by
        simp [dhcExitBoundaryFoldStep, dhcExitBoundaryFoldRightStep,
          dhcExitBoundaryBlock]
        rfl]
      have hFold :=
        dhcExitBoundaryFold_active_invariant budget slot x xs out
      simpa using hFold

theorem dhcExitArcsForSlotFromPrevIndexedPending_append_final
    (budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier) :
    dhcExitArcsForSlotFromPrevIndexedPending budget slot prev xs ++
      dhcExitArcForSlotBlockFromIndexed budget slot (dhcExitBoundaryLastOr prev xs) =
        dhcExitArcsForSlotFromPrevIndexed budget slot prev xs := by
  induction xs generalizing prev with
  | nil =>
      simp [dhcExitArcsForSlotFromPrevIndexedPending, dhcExitBoundaryLastOr,
        dhcExitArcsForSlotFromPrevIndexed]
  | cons x xs ih =>
      by_cases hSame :
          dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource x
      · have hSameRaw : (prev.1.1 : Nat) = (x.1.1 : Nat) := by
          simpa [dhcBoundaryIncidenceSource] using hSame
        simp [dhcExitArcsForSlotFromPrevIndexedPending, dhcExitBoundaryLastOr,
          dhcExitArcsForSlotFromPrevIndexed, dhcBoundarySameSourceBool,
          dhcBoundaryIncidenceSource, hSameRaw, ih x]
      · have hSameRaw : ¬(prev.1.1 : Nat) = (x.1.1 : Nat) := by
          simpa [dhcBoundaryIncidenceSource] using hSame
        have hBeq : Nat.beq (prev.1.1 : Nat) (x.1.1 : Nat) = false := by
          rw [← Bool.not_eq_true, Nat.beq_eq]
          exact hSameRaw
        simp [dhcExitArcsForSlotFromPrevIndexedPending, dhcExitBoundaryLastOr,
          dhcExitArcsForSlotFromPrevIndexed, dhcBoundarySameSourceBool,
          dhcBoundaryIncidenceSource, hBeq, ih x, List.append_assoc]
        intro hEq
        exact False.elim (hSameRaw hEq)

theorem dhcExitArcsForSlotFromBoundaryIndexedExecutable_eq
    (p : dhcSlotIndexedIncidenceListRaw) :
    dhcExitArcsForSlotFromBoundaryIndexedExecutable p =
      dhcExitArcsForSlotFromBoundaryIndexed p.1 p.2.1 p.2.2 := by
  rcases p with ⟨budget, slot, xs⟩
  rw [dhcExitArcsForSlotFromBoundaryIndexedExecutable, dhcExitBoundaryFoldResult,
    dhcExitBoundaryInstructions, dhcEntryBoundaryInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcExitBoundaryFoldStep (dhcExitBoundaryFoldInit, Sum.inl (budget, slot)) =
        (budget,
          (slot,
            (false, (dhcEntryExitBoundaryDummyIncidence, ([] : List (Nat × Nat)))))) by
    rfl]
  cases xs with
  | nil =>
      simp [dhcExitBoundaryFinalBlock, dhcExitBoundaryFoldStep,
        dhcExitArcsForSlotFromBoundaryIndexed]
  | cons x xs =>
      have hFold :=
        dhcExitBoundaryFold_inactive_invariant budget slot (x :: xs) ([] : List (Nat × Nat))
      have hOut :=
        congrArg
          (fun acc : dhcExitBoundaryAccEncodedType.Carrier =>
            (show List (Nat × Nat) from acc.2.2.2.2) ++
              dhcExitBoundaryFinalBlock acc)
          hFold
      have hPending :=
        dhcExitArcsForSlotFromPrevIndexedPending_append_final budget slot x xs
      simpa [dhcExitBoundaryFinalBlock, dhcExitArcsForSlotFromBoundaryIndexed,
        List.append_assoc] using hOut.trans hPending

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
