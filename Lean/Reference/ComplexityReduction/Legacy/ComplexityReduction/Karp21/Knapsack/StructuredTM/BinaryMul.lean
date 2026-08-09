import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitLength

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Direct binary multiplication scaffolding for compact Knapsack code generation.

The executable multiplication path uses a typed instruction fold.  The first
instruction installs the left multiplicand in the reachable accumulator; each
following bit instruction consumes one little-endian multiplier bit, adds the
current power when the bit is set, and doubles the power.
-/

def binaryMulAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)

def binaryMulInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.bool

def binaryMulInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool binaryMulInstructionPayloadEncodedType

def binaryMulInstructionListEncodedType : EncodedType :=
  EncodedType.list binaryMulInstructionEncodedType

def binaryMulStepInputEncodedType : EncodedType :=
  EncodedType.prod binaryMulAccEncodedType binaryMulInstructionEncodedType

def binaryMulBranchInputEncodedType : EncodedType :=
  EncodedType.prod binaryMulAccEncodedType binaryMulInstructionPayloadEncodedType

def binaryMulBitsInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.bool)

abbrev BinaryMulAcc := Nat × (Nat × Nat)
abbrev BinaryMulInstructionPayload := Nat × Bool
abbrev BinaryMulInstruction := Bool × BinaryMulInstructionPayload
abbrev BinaryMulBranchInput := BinaryMulAcc × BinaryMulInstructionPayload
abbrev BinaryMulBitsInput := Nat × List Bool

def binaryMulInitAcc : BinaryMulAcc :=
  (0, (0, 0))

def binaryMulInitInstruction (m : Nat) : BinaryMulInstruction :=
  (false, (m, false))

def binaryMulBitInstruction (bit : Bool) : BinaryMulInstruction :=
  (true, ((0 : Nat), bit))

def binaryMulInstructionsFromBits (p : BinaryMulBitsInput) :
    List BinaryMulInstruction :=
  binaryMulInitInstruction p.1 :: p.2.map binaryMulBitInstruction

def binaryMulInstructions (p : Nat × Nat) :
    List BinaryMulInstruction :=
  binaryMulInstructionsFromBits (p.1, binaryNatBitsList p.2)

def binaryMulInitStep
    (p : BinaryMulBranchInput) : BinaryMulAcc :=
  let m := p.2.1
  (m, (m, 0))

def binaryMulBitStep
    (p : BinaryMulBranchInput) : BinaryMulAcc :=
  let acc := p.1
  let bit := p.2.2
  let base := acc.1
  let power := acc.2.1
  let total := acc.2.2
  let total' := if bit then total + power else total
  let power' := power + power
  (base, (power', total'))

def binaryMulStep
    (p : BinaryMulAcc × BinaryMulInstruction) : BinaryMulAcc :=
  match p.2.1 with
  | false => binaryMulInitStep (p.1, p.2.2)
  | true => binaryMulBitStep (p.1, p.2.2)

def binaryMulFold (xs : List BinaryMulInstruction) : BinaryMulAcc :=
  xs.foldl (fun acc instr => binaryMulStep (acc, instr)) binaryMulInitAcc

def binaryMulFromInstructions
    (xs : List BinaryMulInstruction) : Nat :=
  (binaryMulFold xs).2.2

def binaryNatMulExecutable (p : Nat × Nat) : Nat :=
  binaryMulFromInstructions (binaryMulInstructions p)

theorem binaryMulBitInstructions_fold_eq
    (bits : List Bool) (base power total : Nat) :
    (bits.map binaryMulBitInstruction).foldl
        (fun acc instr => binaryMulStep (acc, instr)) (base, (power, total)) =
      (base, (power * 2 ^ bits.length, total + power * boolBitsValue bits)) := by
  induction bits generalizing power total with
  | nil =>
      simp [boolBitsValue]
  | cons bit bits ih =>
      rw [List.map_cons, List.foldl_cons]
      simp only [binaryMulBitInstruction]
      change (bits.map binaryMulBitInstruction).foldl
          (fun acc instr => binaryMulStep (acc, instr))
          (base, (power + power, if bit then total + power else total)) =
        (base, (power * 2 ^ (bit :: bits).length,
          total + power * boolBitsValue (bit :: bits)))
      rw [ih (power + power) (if bit then total + power else total)]
      cases bit <;>
        simp [boolBitsValue, boolBitValue, Nat.ofDigits_cons, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, pow_succ] <;>
          ring_nf <;>
          constructor <;> trivial

theorem binaryMulInstructionsFromBits_fold_eq (m : Nat) (bits : List Bool) :
    binaryMulFold (binaryMulInstructionsFromBits (m, bits)) =
      (m, (m * 2 ^ bits.length, m * boolBitsValue bits)) := by
  simp [binaryMulFold, binaryMulInstructionsFromBits, binaryMulInitInstruction,
    binaryMulStep, binaryMulInitStep]
  simpa using binaryMulBitInstructions_fold_eq bits m m 0

theorem binaryNatMulExecutable_eq_mul (p : Nat × Nat) :
    binaryNatMulExecutable p = p.1 * p.2 := by
  rcases p with ⟨m, n⟩
  simp [binaryNatMulExecutable, binaryMulFromInstructions, binaryMulInstructions,
    binaryMulInstructionsFromBits_fold_eq, binaryNatBitsList,
    boolBitsValue_binaryNat_encode]

theorem binaryNatDouble_tm_polytime :
    TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat (fun n : Nat => n + n) := by
  have hDiag := TMPolyTimeMap.prod_diag EncodedType.binaryNat
  have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hDiag
  simpa [Function.comp] using hComp

theorem binaryMulInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      binaryMulInstructionEncodedType
      binaryMulInitInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hBit : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hPayload :
      TMPolyTimeMap X binaryMulInstructionPayloadEncodedType
        (fun m : Nat => (m, false)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) hBit
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [binaryMulInstructionEncodedType, binaryMulInstructionPayloadEncodedType,
    binaryMulInitInstruction, X] using hOut

theorem binaryMulBitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.bool
      binaryMulInstructionEncodedType
      binaryMulBitInstruction := by
  let X := EncodedType.bool
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Bool => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : Bool => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X binaryMulInstructionPayloadEncodedType
        (fun bit : Bool => ((0 : Nat), bit)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [binaryMulInstructionEncodedType, binaryMulInstructionPayloadEncodedType,
    binaryMulBitInstruction, X] using hOut

theorem binaryMulInstructionsFromBits_tm_polytime :
    TMPolyTimeMap
      binaryMulBitsInputEncodedType
      binaryMulInstructionListEncodedType
      binaryMulInstructionsFromBits := by
  let X := binaryMulBitsInputEncodedType
  have hM : TMPolyTimeMap X EncodedType.binaryNat (fun p : BinaryMulBitsInput => p.1) := by
    simpa [X, binaryMulBitsInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat (EncodedType.list EncodedType.bool)
  have hBits :
      TMPolyTimeMap X (EncodedType.list EncodedType.bool)
        (fun p : BinaryMulBitsInput => p.2) := by
    simpa [X, binaryMulBitsInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.list EncodedType.bool)
  have hInit :
      TMPolyTimeMap X binaryMulInstructionEncodedType
        (fun p : BinaryMulBitsInput => binaryMulInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp binaryMulInitInstruction_tm_polytime hM
    simpa [Function.comp, X] using hComp
  have hBitInstructions :
      TMPolyTimeMap X binaryMulInstructionListEncodedType
        (fun p : BinaryMulBitsInput => p.2.map binaryMulBitInstruction) := by
    have hMap := TMPolyTimeMap.list_map binaryMulBitInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hBits
    simpa [Function.comp, binaryMulInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod binaryMulInstructionEncodedType binaryMulInstructionListEncodedType)
        (fun p : BinaryMulBitsInput =>
          (binaryMulInitInstruction p.1, p.2.map binaryMulBitInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hBitInstructions
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons binaryMulInstructionEncodedType) hConsInput
  simpa [Function.comp, binaryMulInstructionsFromBits, binaryMulInstructionListEncodedType,
    X] using hCons

theorem binaryMulInstructions_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      binaryMulInstructionListEncodedType
      binaryMulInstructions := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hM : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hN : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hBits :
      TMPolyTimeMap X (EncodedType.list EncodedType.bool)
        (fun p : Nat × Nat => binaryNatBitsList p.2) := by
    have hComp := TMPolyTimeMap.comp binaryNatBitsList_tm_polytime hN
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X binaryMulBitsInputEncodedType
        (fun p : Nat × Nat => (p.1, binaryNatBitsList p.2)) :=
    TMPolyTimeMap.prod_mk hM hBits
  have hComp := TMPolyTimeMap.comp binaryMulInstructionsFromBits_tm_polytime hInput
  simpa [Function.comp, binaryMulInstructions, binaryMulBitsInputEncodedType, X] using hComp

theorem binaryMulInitStep_tm_polytime :
    TMPolyTimeMap
      binaryMulBranchInputEncodedType
      binaryMulAccEncodedType
      binaryMulInitStep := by
  let X := binaryMulBranchInputEncodedType
  have hPayload :
      TMPolyTimeMap X binaryMulInstructionPayloadEncodedType
        (fun p : BinaryMulBranchInput => p.2) := by
    simpa [X, binaryMulBranchInputEncodedType] using
      TMPolyTimeMap.snd binaryMulAccEncodedType binaryMulInstructionPayloadEncodedType
  have hM : TMPolyTimeMap X EncodedType.binaryNat (fun p : BinaryMulBranchInput => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, binaryMulInstructionPayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : BinaryMulBranchInput => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : BinaryMulBranchInput => (p.2.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hM hZero
  have hOut := TMPolyTimeMap.prod_mk hM hTail
  simpa [binaryMulInitStep, binaryMulAccEncodedType, binaryMulBranchInputEncodedType,
    binaryMulInstructionPayloadEncodedType, X] using hOut

theorem binaryMulAccPower_tm_polytime :
    TMPolyTimeMap
      binaryMulAccEncodedType
      EncodedType.binaryNat
      (fun acc : BinaryMulAcc => acc.2.1) := by
  have hTail := TMPolyTimeMap.snd EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hPower := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hComp := TMPolyTimeMap.comp hPower hTail
  simpa [Function.comp, binaryMulAccEncodedType] using hComp

theorem binaryMulAccTotal_tm_polytime :
    TMPolyTimeMap
      binaryMulAccEncodedType
      EncodedType.binaryNat
      (fun acc : BinaryMulAcc => acc.2.2) := by
  have hTail := TMPolyTimeMap.snd EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hTotal := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hComp := TMPolyTimeMap.comp hTotal hTail
  simpa [Function.comp, binaryMulAccEncodedType] using hComp

theorem binaryMulAccTotalAddPower_tm_polytime :
    TMPolyTimeMap
      binaryMulAccEncodedType
      EncodedType.binaryNat
      (fun acc : BinaryMulAcc => acc.2.2 + acc.2.1) := by
  have hPair :
      TMPolyTimeMap binaryMulAccEncodedType
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun acc : BinaryMulAcc => (acc.2.2, acc.2.1)) :=
    TMPolyTimeMap.prod_mk binaryMulAccTotal_tm_polytime binaryMulAccPower_tm_polytime
  have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair
  simpa [Function.comp, binaryMulAccEncodedType] using hComp

theorem binaryMulBitStep_tm_polytime :
    TMPolyTimeMap
      binaryMulBranchInputEncodedType
      binaryMulAccEncodedType
      binaryMulBitStep := by
  let X := binaryMulBranchInputEncodedType
  have hAcc :
      TMPolyTimeMap X binaryMulAccEncodedType (fun p : BinaryMulBranchInput => p.1) := by
    simpa [X, binaryMulBranchInputEncodedType] using
      TMPolyTimeMap.fst binaryMulAccEncodedType binaryMulInstructionPayloadEncodedType
  have hPayload :
      TMPolyTimeMap X binaryMulInstructionPayloadEncodedType
        (fun p : BinaryMulBranchInput => p.2) := by
    simpa [X, binaryMulBranchInputEncodedType] using
      TMPolyTimeMap.snd binaryMulAccEncodedType binaryMulInstructionPayloadEncodedType
  have hBase :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : BinaryMulBranchInput => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, binaryMulAccEncodedType, X] using hComp
  have hPower :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : BinaryMulBranchInput => p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp binaryMulAccPower_tm_polytime hAcc
    simpa [Function.comp, X] using hComp
  have hBit : TMPolyTimeMap X EncodedType.bool (fun p : BinaryMulBranchInput => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, binaryMulInstructionPayloadEncodedType, X] using hComp
  have hPower' :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryMulBranchInput => p.1.2.1 + p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp binaryNatDouble_tm_polytime hPower
    simpa [Function.comp, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool binaryMulAccEncodedType)
        (fun p : BinaryMulBranchInput => (p.2.2, p.1)) :=
    TMPolyTimeMap.prod_mk hBit hAcc
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool binaryMulAccEncodedType)
        EncodedType.binaryNat
        (fun p : Bool × BinaryMulAcc =>
          match p.1 with
          | true => p.2.2.2 + p.2.2.1
          | false => p.2.2.2) :=
    Clique.boolProduct_dispatch_tm_polytime binaryMulAccEncodedType EncodedType.binaryNat
      (fFalse := fun acc : BinaryMulAcc => acc.2.2)
      (fTrue := fun acc : BinaryMulAcc => acc.2.2 + acc.2.1)
      binaryMulAccTotal_tm_polytime binaryMulAccTotalAddPower_tm_polytime
  have hTotal' :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : BinaryMulBranchInput =>
          if p.2.2 then p.1.2.2 + p.1.2.1 else p.1.2.2) := by
    have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
    convert hComp using 1
    funext p
    rcases p with ⟨acc, payload⟩
    rcases payload with ⟨m, bit⟩
    cases bit <;> simp [Function.comp]
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : BinaryMulBranchInput =>
          (p.1.2.1 + p.1.2.1,
            if p.2.2 then p.1.2.2 + p.1.2.1 else p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hPower' hTotal'
  have hOut := TMPolyTimeMap.prod_mk hBase hTail
  simpa [binaryMulBitStep, binaryMulAccEncodedType, binaryMulBranchInputEncodedType,
    binaryMulInstructionPayloadEncodedType, X] using hOut

theorem binaryMulStep_tm_polytime :
    TMPolyTimeMap
      binaryMulStepInputEncodedType
      binaryMulAccEncodedType
      binaryMulStep := by
  let X := binaryMulStepInputEncodedType
  have hAcc : TMPolyTimeMap X binaryMulAccEncodedType
      (fun p : BinaryMulAcc × BinaryMulInstruction => p.1) := by
    simpa [X, binaryMulStepInputEncodedType] using
      TMPolyTimeMap.fst binaryMulAccEncodedType binaryMulInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X binaryMulInstructionEncodedType
        (fun p : BinaryMulAcc × BinaryMulInstruction => p.2) := by
    simpa [X, binaryMulStepInputEncodedType] using
      TMPolyTimeMap.snd binaryMulAccEncodedType binaryMulInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : BinaryMulAcc × BinaryMulInstruction => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool binaryMulInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, binaryMulInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X binaryMulInstructionPayloadEncodedType
        (fun p : BinaryMulAcc × BinaryMulInstruction => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool binaryMulInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, binaryMulInstructionEncodedType, X] using hComp
  have hBranchPayload :
      TMPolyTimeMap X binaryMulBranchInputEncodedType
        (fun p : BinaryMulAcc × BinaryMulInstruction => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPayload
  have hBranchInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.bool binaryMulBranchInputEncodedType)
        (fun p : BinaryMulAcc × BinaryMulInstruction => (p.2.1, (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hTag hBranchPayload
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool binaryMulBranchInputEncodedType)
        binaryMulAccEncodedType
        (fun p : Bool × BinaryMulBranchInput =>
          match p.1 with
          | true => binaryMulBitStep p.2
          | false => binaryMulInitStep p.2) :=
    Clique.boolProduct_dispatch_tm_polytime binaryMulBranchInputEncodedType
      binaryMulAccEncodedType
      (fFalse := binaryMulInitStep)
      (fTrue := binaryMulBitStep)
      binaryMulInitStep_tm_polytime binaryMulBitStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

/-! ### Reachable fold witness -/

theorem binaryNatAdd_inputSize_le_max (a b : Nat) :
    EncodedType.binaryNat.inputSize (a + b) ≤
      max (EncodedType.binaryNat.inputSize a) (EncodedType.binaryNat.inputSize b) + 1 := by
  let sa := EncodedType.binaryNat.inputSize a
  let sb := EncodedType.binaryNat.inputSize b
  let s := max sa sb
  have ha0 : a < 2 ^ sa := by
    simpa [sa] using binaryNat_lt_two_pow_inputSize a
  have hb0 : b < 2 ^ sb := by
    simpa [sb] using binaryNat_lt_two_pow_inputSize b
  have hsa : sa ≤ s := by simp [s]
  have hsb : sb ≤ s := by simp [s]
  have ha : a < 2 ^ s :=
    lt_of_lt_of_le ha0 (Nat.pow_le_pow_right (by decide : 0 < 2) hsa)
  have hb : b < 2 ^ s :=
    lt_of_lt_of_le hb0 (Nat.pow_le_pow_right (by decide : 0 < 2) hsb)
  have hsum : a + b < 2 ^ (s + 1) := by
    calc
      a + b < 2 ^ s + 2 ^ s := Nat.add_lt_add ha hb
      _ = 2 ^ (s + 1) := by
        rw [pow_succ]
        ring
  simpa [s] using binaryNat_inputSize_le_of_lt_two_pow hsum

theorem binaryNatDouble_inputSize_le (n : Nat) :
    EncodedType.binaryNat.inputSize (n + n) ≤ EncodedType.binaryNat.inputSize n + 1 := by
  simpa using binaryNatAdd_inputSize_le_max n n

theorem binaryMulInstruction_payloadNat_inputSize_le (instr : BinaryMulInstruction) :
    EncodedType.binaryNat.inputSize instr.2.1 ≤
      binaryMulInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨m, bit⟩
  simp [binaryMulInstructionEncodedType, binaryMulInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

def binaryMulAccBound (N processed : Nat) (acc : BinaryMulAcc) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ N + 2 ∧
    EncodedType.binaryNat.inputSize acc.2.1 ≤ N + processed + 2 ∧
      EncodedType.binaryNat.inputSize acc.2.2 ≤ N + processed + 2

theorem binaryMulInitAcc_bound (N : Nat) :
    binaryMulAccBound N 0 binaryMulInitAcc := by
  constructor
  · simp [binaryMulInitAcc, EncodedType.inputSize, EncodedType.binaryNat]
  · constructor <;> simp [binaryMulInitAcc, EncodedType.inputSize, EncodedType.binaryNat]

theorem binaryMulStep_bound {N processed : Nat}
    {acc : BinaryMulAcc} {instr : BinaryMulInstruction}
    (hAcc : binaryMulAccBound N processed acc)
    (hInstr : binaryMulInstructionEncodedType.inputSize instr ≤ N) :
    binaryMulAccBound N (processed + 1) (binaryMulStep (acc, instr)) := by
  rcases acc with ⟨base, power, total⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨m, bit⟩
  rcases hAcc with ⟨hBase, hPower, hTotal⟩
  simp at hBase hPower hTotal
  have hM : EncodedType.binaryNat.inputSize m ≤ N := by
    exact (binaryMulInstruction_payloadNat_inputSize_le (tag, (m, bit))).trans hInstr
  cases tag
  · constructor
    · simpa [binaryMulStep, binaryMulInitStep] using hM.trans (by omega)
    · constructor
      · simpa [binaryMulStep, binaryMulInitStep] using hM.trans (by omega)
      · simp [binaryMulStep, binaryMulInitStep, EncodedType.inputSize, EncodedType.binaryNat]
  · have hDouble := binaryNatDouble_inputSize_le power
    constructor
    · simpa [binaryMulStep, binaryMulBitStep] using hBase
    · constructor
      · simpa [binaryMulStep, binaryMulBitStep] using hDouble.trans (by omega)
      · cases bit
        · simpa [binaryMulStep, binaryMulBitStep] using hTotal.trans (by omega)
        · have hAdd := binaryNatAdd_inputSize_le_max total power
          have hMax : max (EncodedType.binaryNat.inputSize total)
              (EncodedType.binaryNat.inputSize power) ≤ N + processed + 2 := by
            exact max_le hTotal hPower
          simpa [binaryMulStep, binaryMulBitStep] using hAdd.trans (by omega)

theorem binaryMulList_length_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [EncodedType.inputSize_list_cons]
      omega

theorem binaryMulList_element_inputSize_le {X : EncodedType}
    {x : X.Carrier} {xs : List X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      rw [EncodedType.inputSize_list_cons]
      simp at hx
      rcases hx with hEq | hMem
      · subst x
        omega
      · have hTail := ih hMem
        omega

theorem binaryMulList_inputSize_append (X : EncodedType)
    (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [EncodedType.inputSize_list_cons, ih, Nat.add_assoc]

theorem binaryMulList_length_append_cons {α : Type} (pref : List α) (x : α) (xs : List α) :
    (pref ++ x :: xs).length = pref.length + (x :: xs).length := by
  induction pref with
  | nil =>
      simp
  | cons y pref ih =>
      simp [ih]
      omega

theorem binaryMulFold_bound_aux {N processed : Nat}
    (rest : List BinaryMulInstruction) (acc : BinaryMulAcc)
    (hAcc : binaryMulAccBound N processed acc)
    (hLen : processed + rest.length ≤ N)
    (hInstr : ∀ instr ∈ rest, binaryMulInstructionEncodedType.inputSize instr ≤ N) :
    binaryMulAccBound N (processed + rest.length)
      (rest.foldl (fun acc instr => binaryMulStep (acc, instr)) acc) := by
  induction rest generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons instr rest ih =>
      have hHead : binaryMulInstructionEncodedType.inputSize instr ≤ N :=
        hInstr instr (by simp)
      have hStep := binaryMulStep_bound (N := N) (processed := processed)
        (acc := acc) (instr := instr) hAcc hHead
      have hLenTail : processed + 1 + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLen
      have hInstrTail :
          ∀ instr' ∈ rest, binaryMulInstructionEncodedType.inputSize instr' ≤ N := by
        intro instr' hin
        exact hInstr instr' (by simp [hin])
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (processed := processed + 1) (acc := binaryMulStep (acc, instr))
          hStep hLenTail hInstrTail

theorem binaryMulFold_bound_of_inputSize_le {N : Nat}
    (xs : List BinaryMulInstruction)
    (hSize : binaryMulInstructionListEncodedType.inputSize xs ≤ N) :
    binaryMulAccBound N xs.length
      (xs.foldl (fun acc instr => binaryMulStep (acc, instr)) binaryMulInitAcc) := by
  have hLenRaw := binaryMulList_length_le_inputSize binaryMulInstructionEncodedType xs
  have hLen : xs.length ≤ N := by
    have hLenRaw' :
        xs.length ≤ binaryMulInstructionListEncodedType.inputSize xs := by
      simpa [binaryMulInstructionListEncodedType] using hLenRaw
    omega
  have hInstr :
      ∀ instr ∈ xs, binaryMulInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem := binaryMulList_element_inputSize_le
      (X := binaryMulInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' :
        binaryMulInstructionEncodedType.inputSize instr ≤
          binaryMulInstructionListEncodedType.inputSize xs := by
      simpa [binaryMulInstructionListEncodedType] using hElem
    omega
  have h := binaryMulFold_bound_aux (N := N) (processed := 0) xs binaryMulInitAcc
    (binaryMulInitAcc_bound N) (by simpa using hLen) hInstr
  simpa using h

noncomputable def binaryMulFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 5 * Polynomial.X + Polynomial.C 10

@[simp] theorem binaryMulFoldAccBoundPolynomial_eval (N : Nat) :
    binaryMulFoldAccBoundPolynomial.eval N = 5 * N + 10 := by
  simp [binaryMulFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem binaryMulAccBound_inputSize_le {N processed : Nat}
    {acc : BinaryMulAcc}
    (hAcc : binaryMulAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    binaryMulAccEncodedType.inputSize acc ≤
      binaryMulFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨base, power, total⟩
  rcases hAcc with ⟨hBase, hPower, hTotal⟩
  simp [binaryMulAccEncodedType, EncodedType.inputSize_prod] at hBase hPower hTotal ⊢
  nlinarith [hBase, hPower, hTotal, hProcessed, Nat.zero_le N]

noncomputable def binaryMulFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod binaryMulAccEncodedType binaryMulInstructionEncodedType).encode
        binaryMulAccEncodedType.encode
        binaryMulStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm binaryMulFoldAccBoundPolynomial
    (hStep.time.comp
      (binaryMulFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem binaryMulFold_tm_polytime :
    TMPolyTimeMap
      binaryMulInstructionListEncodedType
      binaryMulAccEncodedType
      binaryMulFold := by
  rcases binaryMulStep_tm_polytime with ⟨hStep⟩
  let time := binaryMulFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      binaryMulInstructionEncodedType binaryMulAccEncodedType
      binaryMulStep binaryMulInitAcc hStep time ?_
  intro source
  let N := binaryMulInstructionListEncodedType.inputSize source
  let B := binaryMulFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hLoopAux :
      ∀ (pref rest : List BinaryMulInstruction),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              binaryMulInstructionEncodedType binaryMulAccEncodedType
              binaryMulStep hStep
              (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                binaryMulInitAcc)
              rest ≤
            C * (EncodedType.list binaryMulInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons x xs ih =>
        intro hEq
        have hxMemSource : x ∈ source := by
          rw [hEq]
          exact List.mem_append_right pref (by simp)
        have hxN : binaryMulInstructionEncodedType.inputSize x ≤ N := by
          have hElem := binaryMulList_element_inputSize_le
            (X := binaryMulInstructionEncodedType) (x := x) (xs := source) hxMemSource
          simpa [N, binaryMulInstructionListEncodedType] using hElem
        have hPrefixSize : binaryMulInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              binaryMulInstructionListEncodedType.inputSize source =
                binaryMulInstructionListEncodedType.inputSize pref +
                  binaryMulInstructionListEncodedType.inputSize (x :: xs) := by
            rw [hEq]
            exact binaryMulList_inputSize_append binaryMulInstructionEncodedType pref (x :: xs)
          omega
        have hPrefixBound :=
          binaryMulFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen := binaryMulList_length_le_inputSize binaryMulInstructionEncodedType pref
          have hLen' :
              pref.length ≤ binaryMulInstructionListEncodedType.inputSize pref := by
            simpa [binaryMulInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            binaryMulAccEncodedType.inputSize
                (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                  binaryMulInitAcc) ≤ B := by
          simpa [B] using binaryMulAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepBound := binaryMulStep_bound
          (N := N) (processed := pref.length)
          (acc := pref.foldl (fun acc instr => binaryMulStep (acc, instr))
            binaryMulInitAcc)
          (instr := x) hPrefixBound hxN
        have hNextSize :
            binaryMulAccEncodedType.inputSize
                (binaryMulStep
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc, x)) ≤ B := by
          have hPrefixSucc : pref.length + 1 ≤ N := by
            have hSourceLenN : source.length ≤ N := by
              have hLen :=
                binaryMulList_length_le_inputSize binaryMulInstructionEncodedType source
              have hLen' :
                  source.length ≤ binaryMulInstructionListEncodedType.inputSize source := by
                simpa [binaryMulInstructionListEncodedType] using hLen
              omega
            have hLenEq : source.length = pref.length + (x :: xs).length := by
              rw [hEq]
              exact binaryMulList_length_append_cons pref x xs
            simp at hLenEq
            omega
          simpa [B] using binaryMulAccBound_inputSize_le hStepBound hPrefixSucc
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod binaryMulAccEncodedType
                    binaryMulInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc, x)) ≤ T := by
          have hArg :
              (EncodedType.prod binaryMulAccEncodedType
                    binaryMulInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc, x) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change binaryMulAccEncodedType.inputSize
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc) + 1 +
                binaryMulInstructionEncodedType.inputSize x ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (binaryMulInstructionEncodedType.encode x).length
                (binaryMulAccEncodedType.encode
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc)).length
                (binaryMulAccEncodedType.encode
                  (binaryMulStep
                    (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                      binaryMulInitAcc, x))).length
                (hStep.time.eval
                  ((EncodedType.prod binaryMulAccEncodedType
                    binaryMulInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                      binaryMulInitAcc, x))) ≤
              C * (binaryMulInstructionEncodedType.inputSize x + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hNextSize)
              hStepTime
        have hTail := ih (pref := pref ++ [x]) (by
          rw [hEq]
          simp [List.append_assoc])
        calc
          TM2Programs.listFoldTypedLoopTime
              binaryMulInstructionEncodedType binaryMulAccEncodedType
              binaryMulStep hStep
              (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                binaryMulInitAcc)
              (x :: xs)
              =
            TM2Programs.listFoldTypedLoopTime
              binaryMulInstructionEncodedType binaryMulAccEncodedType
              binaryMulStep hStep
              ((pref ++ [x]).foldl (fun acc instr => binaryMulStep (acc, instr))
                binaryMulInitAcc)
              xs +
            TM2Programs.listFoldBlockTime hStep.tm
              (binaryMulInstructionEncodedType.encode x).length
              (binaryMulAccEncodedType.encode
                (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                  binaryMulInitAcc)).length
              (binaryMulAccEncodedType.encode
                (binaryMulStep
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc, x))).length
              (hStep.time.eval
                ((EncodedType.prod binaryMulAccEncodedType
                  binaryMulInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => binaryMulStep (acc, instr))
                    binaryMulInitAcc, x))) := by
                simp [TM2Programs.listFoldTypedLoopTime, List.foldl_append]; rfl
          _ ≤ C * (EncodedType.list binaryMulInstructionEncodedType).inputSize xs +
              C * (binaryMulInstructionEncodedType.inputSize x + 1) :=
                Nat.add_le_add hTail hBlock
          _ = C * (EncodedType.list binaryMulInstructionEncodedType).inputSize (x :: xs) := by
                rw [EncodedType.inputSize_list_cons]
                ring
  have hLoop := hLoopAux [] source (by simp)
  have hTimeEval :
      time.eval N = (C + 2) * (N + 1) := by
    simp [time, binaryMulFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, Polynomial.eval_add,
      TM2Programs.listFoldBlockTimeCoeff]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        binaryMulInstructionEncodedType binaryMulAccEncodedType
        binaryMulStep hStep binaryMulInitAcc source ≤ time.eval N
  rw [hTimeEval]
  have hLoop' :
      TM2Programs.listFoldTypedLoopTime
        binaryMulInstructionEncodedType binaryMulAccEncodedType
        binaryMulStep hStep binaryMulInitAcc source ≤ C * N := by
    simpa [N, binaryMulInstructionListEncodedType] using hLoop
  nlinarith [hLoop', Nat.zero_le C, Nat.zero_le N]

theorem binaryMulFromInstructions_tm_polytime :
    TMPolyTimeMap
      binaryMulInstructionListEncodedType
      EncodedType.binaryNat
      binaryMulFromInstructions := by
  have hFold := binaryMulFold_tm_polytime
  have hComp := TMPolyTimeMap.comp binaryMulAccTotal_tm_polytime hFold
  simpa [Function.comp, binaryMulFromInstructions] using hComp

theorem binaryNatMulExecutable_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      binaryNatMulExecutable := by
  have hComp := TMPolyTimeMap.comp binaryMulFromInstructions_tm_polytime
    binaryMulInstructions_tm_polytime
  simpa [Function.comp, binaryNatMulExecutable] using hComp

theorem binaryNatMul_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      EncodedType.binaryNat
      (fun p : Nat × Nat => p.1 * p.2) := by
  convert binaryNatMulExecutable_tm_polytime using 1
  funext p
  exact (binaryNatMulExecutable_eq_mul p).symm

end Knapsack
end Karp21
end ComplexityReduction
