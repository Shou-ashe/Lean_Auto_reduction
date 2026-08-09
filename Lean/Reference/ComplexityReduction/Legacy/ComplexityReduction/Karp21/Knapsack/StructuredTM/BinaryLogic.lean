import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompareTM

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Small binary-natural Boolean combinators for compact Knapsack code generation.
-/

def binaryNatEqBool (p : Nat × Nat) : Bool :=
  Clique.boolAndPair
    (!binaryNatSuccLeBool (p.1, p.2), !binaryNatSuccLeBool (p.2, p.1))

theorem binaryNatEqBool_eq_true_iff (p : Nat × Nat) :
    binaryNatEqBool p = true ↔ p.1 = p.2 := by
  rcases p with ⟨a, b⟩
  by_cases hlt : a.succ ≤ b
  · have hne : a ≠ b := by omega
    simp [binaryNatEqBool, binaryNatSuccLeBool, Clique.boolAndPair, hlt, hne]
  · by_cases hgt : b.succ ≤ a
    · have hne : a ≠ b := by omega
      simp [binaryNatEqBool, binaryNatSuccLeBool, Clique.boolAndPair, hlt, hgt, hne]
    · have heq : a = b := by omega
      simp [binaryNatEqBool, binaryNatSuccLeBool, Clique.boolAndPair, heq]

theorem binaryNatEqBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.bool
      binaryNatEqBool := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => binaryNatSuccLeBool (p.1, p.2)) := by
    simpa [X] using binaryNatSuccLeBool_tm_polytime
  have hLeft :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hRight :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hReverse :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : Nat × Nat => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hLeft
  have hGt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => binaryNatSuccLeBool (p.2, p.1)) := by
    have hComp := TMPolyTimeMap.comp binaryNatSuccLeBool_tm_polytime hReverse
    simpa [Function.comp, X] using hComp
  have hNotLt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => !binaryNatSuccLeBool (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hLt
    simpa [Function.comp] using hComp
  have hNotGt :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => !binaryNatSuccLeBool (p.2, p.1)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hGt
    simpa [Function.comp] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : Nat × Nat =>
          (!binaryNatSuccLeBool (p.1, p.2), !binaryNatSuccLeBool (p.2, p.1))) :=
    TMPolyTimeMap.prod_mk hNotLt hNotGt
  have hAnd := TMPolyTimeMap.comp Clique.boolAndPair_tm_polytime hPair
  simpa [Function.comp, binaryNatEqBool, X] using hAnd

def boolToBinaryNat (b : Bool) : Nat :=
  if b then 1 else 0

theorem boolToBinaryNat_tm_polytime :
    TMPolyTimeMap EncodedType.bool EncodedType.binaryNat boolToBinaryNat := by
  have hFalse :
      TMPolyTimeMap EncodedType.bool EncodedType.binaryNat
        (fun _ : Bool => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.binaryNat (0 : Nat)
  have hTrue :
      TMPolyTimeMap EncodedType.bool EncodedType.binaryNat
        (fun _ : Bool => (1 : Nat)) :=
    TMPolyTimeMap.const EncodedType.bool EncodedType.binaryNat (1 : Nat)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool EncodedType.bool)
        EncodedType.binaryNat
        (fun p : Bool × Bool =>
          match p.1 with
          | true => (1 : Nat)
          | false => (0 : Nat)) :=
    Clique.boolProduct_dispatch_tm_polytime EncodedType.bool EncodedType.binaryNat
      (fFalse := fun _ : Bool => (0 : Nat))
      (fTrue := fun _ : Bool => (1 : Nat))
      hFalse hTrue
  have hTagged :
      TMPolyTimeMap EncodedType.bool (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun b : Bool => (b, b)) :=
    TMPolyTimeMap.prod_diag EncodedType.bool
  have hComp := TMPolyTimeMap.comp hDispatch hTagged
  convert hComp using 1
  funext b
  cases b <;> rfl

def binaryNatEqDigit (p : Nat × Nat) : Nat :=
  boolToBinaryNat (binaryNatEqBool p)

theorem binaryNatEqDigit_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatEqDigit := by
  have hComp := TMPolyTimeMap.comp boolToBinaryNat_tm_polytime binaryNatEqBool_tm_polytime
  simpa [Function.comp, binaryNatEqDigit] using hComp

def binaryNatMax (p : Nat × Nat) : Nat :=
  max p.1 p.2

theorem binaryNatMax_eq_lt_dispatch (p : Nat × Nat) :
    binaryNatMax p =
      match binaryNatSuccLeBool (p.1, p.2) with
      | true => p.2
      | false => p.1 := by
  rcases p with ⟨a, b⟩
  by_cases hlt : a.succ ≤ b
  · have hle : a ≤ b := by omega
    simp [binaryNatMax, binaryNatSuccLeBool, hlt, max_eq_right hle]
  · have hle : b ≤ a := by omega
    simp [binaryNatMax, binaryNatSuccLeBool, hlt, max_eq_left hle]

theorem binaryNatMax_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatMax := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hFlag :
      TMPolyTimeMap X EncodedType.bool
        (fun p : Nat × Nat => binaryNatSuccLeBool (p.1, p.2)) := by
    simpa [X] using binaryNatSuccLeBool_tm_polytime
  have hLeft :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hRight :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : Nat × Nat => (binaryNatSuccLeBool (p.1, p.2), p)) :=
    TMPolyTimeMap.prod_mk hFlag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        EncodedType.binaryNat
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => p.2.2
          | false => p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.binaryNat
      (fFalse := fun p : Nat × Nat => p.1)
      (fTrue := fun p : Nat × Nat => p.2)
      hLeft hRight
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rw [binaryNatMax_eq_lt_dispatch p]
  cases h : binaryNatSuccLeBool (p.1, p.2) <;> simp [Function.comp, h]

end Knapsack
end Karp21
end ComplexityReduction
