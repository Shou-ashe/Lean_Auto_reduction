import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatMul
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Clique.Part1

namespace ComplexityReduction
namespace Karp21

/-!
Direct TM-backed unary arithmetic helpers for Karp21 routes that still use
`Nat.pair` as a semantic code.  The multiplication witness is imported from the
non-cyclic bridge-level module, so Exact Cover routes can use this file without
pulling in Partition/Knapsack and creating an import cycle.
-/

def natLtBool (p : Nat × Nat) : Bool :=
  decide (p.1 < p.2)

theorem natLtBool_eq_true_iff (p : Nat × Nat) :
    natLtBool p = true ↔ p.1 < p.2 := by
  simp [natLtBool]

theorem natLtBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool
      natLtBool := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1.succ) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hLeft
    simpa [Function.comp, X] using hComp
  have hSubInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1.succ, p.2)) :=
    TMPolyTimeMap.prod_mk hSucc hRight
  have hSub :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1.succ - p.2) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : Nat × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1.succ - p.2, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hSub hZero
  have hEq :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => decide (p.1.succ - p.2 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp, X] using hComp
  convert hEq using 1
  funext p
  by_cases hlt : p.1 < p.2
  · have hZeroSub : p.1.succ - p.2 = 0 := by omega
    simp [natLtBool, hlt, hZeroSub]
  · have hNonzero : p.1.succ - p.2 ≠ 0 := by
      intro hZeroSub
      have hLe : p.1.succ ≤ p.2 := (Nat.sub_eq_zero_iff_le).1 hZeroSub
      have : p.1 < p.2 := by omega
      exact hlt this
    simp [natLtBool, hlt, hNonzero]

def natSquare (n : Nat) : Nat :=
  n * n

theorem natSquare_tm_polytime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat natSquare := by
  have hDiag := TMPolyTimeMap.prod_diag EncodedType.nat
  have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hDiag
  simpa [Function.comp, natSquare] using hComp

theorem natPair_trueBranch_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.2 * p.2 + p.1) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hRightSq : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2 * p.2) := by
    have hComp := TMPolyTimeMap.comp natSquare_tm_polytime hRight
    simpa [Function.comp, natSquare, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat => (p.2 * p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRightSq hLeft
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natAddInputEncodedType, X] using hOut

theorem natPair_falseBranch_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.1 * p.1 + p.1 + p.2) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hLeft : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hLeftSq : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1 * p.1) := by
    have hComp := TMPolyTimeMap.comp natSquare_tm_polytime hLeft
    simpa [Function.comp, natSquare, X] using hComp
  have hFirstAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat => (p.1 * p.1, p.1)) :=
    TMPolyTimeMap.prod_mk hLeftSq hLeft
  have hFirstAdd :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1 * p.1 + p.1) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hFirstAddInput
    simpa [Function.comp, natAddInputEncodedType, X] using hComp
  have hSecondAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Nat × Nat => (p.1 * p.1 + p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hFirstAdd hRight
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hSecondAddInput
  simpa [Function.comp, natAddInputEncodedType, X] using hOut

theorem natPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : Nat × Nat => (natLtBool p, p)) :=
    TMPolyTimeMap.prod_mk natLtBool_tm_polytime (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) EncodedType.nat
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => p.2.2 * p.2.2 + p.2.1
          | false => p.2.1 * p.2.1 + p.2.1 + p.2.2) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.nat
      natPair_falseBranch_tm_polytime natPair_trueBranch_tm_polytime
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  by_cases hlt : p.1 < p.2 <;> simp [Function.comp, natLtBool, hlt, Nat.pair]

end Karp21
end ComplexityReduction
