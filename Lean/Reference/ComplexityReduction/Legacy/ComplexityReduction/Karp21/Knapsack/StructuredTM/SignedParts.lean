import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Direct binary witnesses for signed coefficient parts used by compact Knapsack
digit generation.
-/

theorem intPositivePart_eq_sign_dispatch (z : Int) :
    intPositivePart z =
      match binaryIntSignBool z with
      | false => binaryIntPayload z
      | true => 0 := by
  cases z <;> simp [intPositivePart, binaryIntSignBool, binaryIntPayload]

theorem intPositivePart_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryInt
      EncodedType.binaryNat
      intPositivePart := by
  let N := EncodedType.binaryNat
  have hBranchInput :
      TMPolyTimeMap
        EncodedType.binaryInt
        (EncodedType.prod EncodedType.bool N)
        (fun z : Int => (binaryIntSignBool z, binaryIntPayload z)) :=
    TMPolyTimeMap.prod_mk binaryIntSignBool_tm_polytime binaryIntPayload_tm_polytime
  have hZero : TMPolyTimeMap N N (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const N N (0 : Nat)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool N)
        N
        (fun p : Bool × Nat =>
          match p.1 with
          | true => (0 : Nat)
          | false => p.2) :=
    Clique.boolProduct_dispatch_tm_polytime N N
      (fFalse := fun n : Nat => n)
      (fTrue := fun _ : Nat => (0 : Nat))
      (TMPolyTimeMap.id N) hZero
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext z
  rw [intPositivePart_eq_sign_dispatch z]
  cases h : binaryIntSignBool z <;> simp [Function.comp, h]

def compactCoeffContributionInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryInt EncodedType.bool

theorem compactCoeffContribution_tm_polytime :
    TMPolyTimeMap
      compactCoeffContributionInputEncodedType
      EncodedType.binaryNat
      (fun p : Int × Bool => compactCoeffContribution p.1 p.2) := by
  let X := compactCoeffContributionInputEncodedType
  let N := EncodedType.binaryNat
  let P := EncodedType.prod N N
  have hCoeff : TMPolyTimeMap X EncodedType.binaryInt (fun p : Int × Bool => p.1) := by
    simpa [X, compactCoeffContributionInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryInt EncodedType.bool
  have hChoice : TMPolyTimeMap X EncodedType.bool (fun p : Int × Bool => p.2) := by
    simpa [X, compactCoeffContributionInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryInt EncodedType.bool
  have hPos : TMPolyTimeMap X N (fun p : Int × Bool => intPositivePart p.1) := by
    have hComp := TMPolyTimeMap.comp intPositivePart_tm_polytime hCoeff
    simpa [Function.comp, X, N] using hComp
  have hNeg : TMPolyTimeMap X N (fun p : Int × Bool => intNegativePart p.1) := by
    have hComp := TMPolyTimeMap.comp intNegativePart_tm_polytime hCoeff
    simpa [Function.comp, X, N] using hComp
  have hParts :
      TMPolyTimeMap X P
        (fun p : Int × Bool => (intPositivePart p.1, intNegativePart p.1)) :=
    TMPolyTimeMap.prod_mk hPos hNeg
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool P)
        (fun p : Int × Bool =>
          (p.2, (intPositivePart p.1, intNegativePart p.1))) :=
    TMPolyTimeMap.prod_mk hChoice hParts
  have hFalse : TMPolyTimeMap P N (fun p : Nat × Nat => p.2) := by
    simpa [P, N] using TMPolyTimeMap.snd N N
  have hTrue : TMPolyTimeMap P N (fun p : Nat × Nat => p.1) := by
    simpa [P, N] using TMPolyTimeMap.fst N N
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool P)
        N
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => p.2.1
          | false => p.2.2) :=
    Clique.boolProduct_dispatch_tm_polytime P N
      (fFalse := fun p : Nat × Nat => p.2)
      (fTrue := fun p : Nat × Nat => p.1)
      hFalse hTrue
  have hOut := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨z, b⟩
  cases b <;> simp [Function.comp, compactCoeffContribution]

end Knapsack
end Karp21
end ComplexityReduction
