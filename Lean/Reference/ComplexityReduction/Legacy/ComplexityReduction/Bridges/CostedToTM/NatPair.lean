import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import Mathlib.Tactic

/-!
Bridge-level direct-TM witnesses for unary `Nat.pair`.

The SAT/Cook-Levin tableau encodings use nested `Nat.pair` codes.  These
witnesses live outside the Karp21 namespace so Cook-Levin generators can cite
them without importing Karp21 reductions.
-/

namespace ComplexityReduction

/-! ### Boolean and comparison helpers -/

def boolToNat (b : Bool) : Nat :=
  if b then 1 else 0

theorem boolToNat_eq_zero_iff (b : Bool) :
    boolToNat b = 0 ↔ b = false := by
  cases b <;> simp [boolToNat]

theorem boolToNat_eq_one_iff (b : Bool) :
    boolToNat b = 1 ↔ b = true := by
  cases b <;> simp [boolToNat]

def boolToNatPayloadKeep : Bool → Option Bool
  | true => some true
  | false => none

theorem boolToNatPayload_encode_filterMap (b : Bool) :
    (EncodedType.bool.encode b).filterMap boolToNatPayloadKeep =
      unaryPayloadEncodedType.encode (boolToNat b) := by
  cases b <;> rfl

theorem boolToNat_tm_polytime :
    TMPolyTimeMap EncodedType.bool EncodedType.nat boolToNat := by
  have hPayload :
      TMPolyTimeMap EncodedType.bool unaryPayloadEncodedType boolToNat :=
    (TMBackedCostedMap.symbolFilterMap
      EncodedType.bool unaryPayloadEncodedType
      boolToNat
      boolToNatPayloadKeep
      (fun b => (boolToNatPayload_encode_filterMap b).symm)).tm_polytime
  have hComp := TMPolyTimeMap.comp unaryPayloadToNatTMBackedMap.tm_polytime hPayload
  simpa [Function.comp] using hComp

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

/-! ### Unary arithmetic blocks for `Nat.pair` -/

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

def natSelectFromBool (p : Bool × (Nat × Nat)) : Nat :=
  boolToNat p.1 * p.2.2 + (1 - boolToNat p.1) * p.2.1

theorem natSelectFromBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool
        (EncodedType.prod EncodedType.nat EncodedType.nat))
      EncodedType.nat
      natSelectFromBool := by
  let X :=
    EncodedType.prod EncodedType.bool
      (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hBool : TMPolyTimeMap X EncodedType.bool (fun p : Bool × (Nat × Nat) => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst EncodedType.bool
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hFlag : TMPolyTimeMap X EncodedType.nat (fun p : Bool × (Nat × Nat) => boolToNat p.1) := by
    have hComp := TMPolyTimeMap.comp boolToNat_tm_polytime hBool
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Bool × (Nat × Nat) => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.bool
        (EncodedType.prod EncodedType.nat EncodedType.nat)
  have hFalseValue :
      TMPolyTimeMap X EncodedType.nat (fun p : Bool × (Nat × Nat) => p.2.1) := by
    have hFirst :=
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFirst hPayload
    simpa [Function.comp, X] using hComp
  have hTrueValue :
      TMPolyTimeMap X EncodedType.nat (fun p : Bool × (Nat × Nat) => p.2.2) := by
    have hSecond :=
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSecond hPayload
    simpa [Function.comp, X] using hComp
  have hTrueMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Bool × (Nat × Nat) => (boolToNat p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hFlag hTrueValue
  have hTrueTerm :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Bool × (Nat × Nat) => boolToNat p.1 * p.2.2) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hTrueMulInput
    simpa [Function.comp, X] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : Bool × (Nat × Nat) => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hOneMinusInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Bool × (Nat × Nat) => ((1 : Nat), boolToNat p.1)) :=
    TMPolyTimeMap.prod_mk hOne hFlag
  have hOneMinus :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Bool × (Nat × Nat) => (1 : Nat) - boolToNat p.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hOneMinusInput
    simpa [Function.comp, X] using hComp
  have hFalseMulInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Bool × (Nat × Nat) => ((1 : Nat) - boolToNat p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hOneMinus hFalseValue
  have hFalseTerm :
      TMPolyTimeMap X EncodedType.nat
        (fun p : Bool × (Nat × Nat) => ((1 : Nat) - boolToNat p.1) * p.2.1) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hFalseMulInput
    simpa [Function.comp, X] using hComp
  have hAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : Bool × (Nat × Nat) =>
          (boolToNat p.1 * p.2.2, ((1 : Nat) - boolToNat p.1) * p.2.1)) :=
    TMPolyTimeMap.prod_mk hTrueTerm hFalseTerm
  have hOut := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natSelectFromBool, X] using hOut

theorem natSelectFromBool_false (a b : Nat) :
    natSelectFromBool (false, (a, b)) = a := by
  simp [natSelectFromBool, boolToNat]

theorem natSelectFromBool_true (a b : Nat) :
    natSelectFromBool (true, (a, b)) = b := by
  simp [natSelectFromBool, boolToNat]

theorem natPair_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => Nat.pair p.1 p.2) := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hFalseBranch := natPair_falseBranch_tm_polytime
  have hTrueBranch := natPair_trueBranch_tm_polytime
  have hPairBranches :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1 * p.1 + p.1 + p.2, p.2 * p.2 + p.1)) :=
    TMPolyTimeMap.prod_mk hFalseBranch hTrueBranch
  have hFlagBranches :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool
          (EncodedType.prod EncodedType.nat EncodedType.nat))
        (fun p : Nat × Nat =>
          (natLtBool p, (p.1 * p.1 + p.1 + p.2, p.2 * p.2 + p.1))) :=
    TMPolyTimeMap.prod_mk natLtBool_tm_polytime hPairBranches
  have hSelected := TMPolyTimeMap.comp natSelectFromBool_tm_polytime hFlagBranches
  convert hSelected using 1
  funext p
  by_cases hlt : p.1 < p.2
  · simp [Function.comp, natLtBool, hlt, Nat.pair, natSelectFromBool, boolToNat]
  · simp [Function.comp, natLtBool, hlt, Nat.pair, natSelectFromBool, boolToNat]

theorem nat_pair_const_left_tm_polytime (k : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => Nat.pair k n) := by
  have hLeft : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => k) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat k
  have hPair :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun n : Nat => (k, n)) :=
    TMPolyTimeMap.prod_mk hLeft (TMPolyTimeMap.id EncodedType.nat)
  have hComp := TMPolyTimeMap.comp natPair_tm_polytime hPair
  simpa [Function.comp] using hComp

theorem nat_pair_const_right_tm_polytime (k : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => Nat.pair n k) := by
  have hRight : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => k) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat k
  have hPair :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun n : Nat => (n, k)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hRight
  have hComp := TMPolyTimeMap.comp natPair_tm_polytime hPair
  simpa [Function.comp] using hComp

end ComplexityReduction
