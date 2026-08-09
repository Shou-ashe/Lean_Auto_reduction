import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryLogic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinarySubTM
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.IntegerProgramming

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Binary-indexed lookup for compact IP rows.

The compact Knapsack code-generation layer needs `compactCoeffAt row i`, where
`i` is represented as a binary natural.  The runner below scans the row with a
binary countdown and returns the default coefficient `0` outside the row,
matching `List.getD`.
-/

theorem binaryNat_inputSize_mono {a b : Nat} (h : a ≤ b) :
    EncodedType.binaryNat.inputSize a ≤ EncodedType.binaryNat.inputSize b :=
  binaryNat_inputSize_le_of_lt_two_pow
    (lt_of_le_of_lt h (binaryNat_lt_two_pow_inputSize b))

@[simp] theorem rowLookup_binaryNat_inputSize_zero :
    EncodedType.binaryNat.inputSize (0 : Nat) = 0 := by
  simp [EncodedType.inputSize, EncodedType.binaryNat, Nat.digits_zero]

@[simp] theorem rowLookup_binaryInt_inputSize_zero :
    EncodedType.binaryInt.inputSize (0 : Int) = 1 := by
  simp only [EncodedType.inputSize, EncodedType.binaryInt, EncodedType.binaryNat,
    Nat.digits_zero, List.map_nil]
  rfl

def intRowGetDAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.bool EncodedType.binaryInt)

abbrev IntRowGetDAcc := Nat × (Bool × Int)

def intRowGetDInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.binaryInt

def intRowGetDInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool intRowGetDInstructionPayloadEncodedType

def intRowGetDInstructionListEncodedType : EncodedType :=
  EncodedType.list intRowGetDInstructionEncodedType

def intRowGetDInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat intRowBinaryStructuredEncodedType

def intRowGetDInitAcc : IntRowGetDAcc :=
  ((0 : Nat), (false, (0 : Int)))

def intRowGetDInitInstruction (target : Nat) :
    intRowGetDInstructionEncodedType.Carrier :=
  (false, (target, (0 : Int)))

def intRowGetDCoeffInstruction (z : Int) :
    intRowGetDInstructionEncodedType.Carrier :=
  (true, ((0 : Nat), z))

def intRowGetDInstructions (p : Nat × List Int) :
    List intRowGetDInstructionEncodedType.Carrier :=
  intRowGetDInitInstruction p.1 :: p.2.map intRowGetDCoeffInstruction

def intRowGetDCoeffStep (p : IntRowGetDAcc × Int) : IntRowGetDAcc :=
  let remaining := p.1.1
  let found := p.1.2.1
  let value := p.1.2.2
  let z := p.2
  match found with
  | true => p.1
  | false =>
      match binaryNatEqBool (remaining, 0) with
      | true => (0, (true, z))
      | false => (remaining - 1, (false, value))

def intRowGetDStep
    (p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier) :
    IntRowGetDAcc :=
  match p.2.1 with
  | true => intRowGetDCoeffStep (p.1, p.2.2.2)
  | false => (p.2.2.1, (false, 0))

def intRowGetDFromInstructions
    (xs : List intRowGetDInstructionEncodedType.Carrier) : Int :=
  (xs.foldl (fun acc instr => intRowGetDStep (acc, instr)) intRowGetDInitAcc).2.2

def intRowGetDFromInput (p : Nat × List Int) : Int :=
  intRowGetDFromInstructions (intRowGetDInstructions p)

def intRowGetD (p : List Int × Nat) : Int :=
  p.1.getD p.2 0

theorem intRowGetDCoeffStep_found (remaining : Nat) (value z : Int) :
    intRowGetDCoeffStep ((remaining, (true, value)), z) =
      (remaining, (true, value)) := by
  simp [intRowGetDCoeffStep]

theorem intRowGetDCoeffInstructions_fold_found
    (xs : List Int) (remaining : Nat) (value : Int) :
    (xs.map intRowGetDCoeffInstruction).foldl
        (fun acc instr => intRowGetDStep (acc, instr))
        (remaining, (true, value)) =
      (remaining, (true, value)) := by
  induction xs generalizing remaining value with
  | nil =>
      simp
  | cons z zs ih =>
      simpa [intRowGetDCoeffInstruction, intRowGetDStep, intRowGetDCoeffStep] using
        ih remaining value

theorem intRowGetDCoeffInstructions_value_eq_getD
    (xs : List Int) (target : Nat) :
    ((xs.map intRowGetDCoeffInstruction).foldl
        (fun acc instr => intRowGetDStep (acc, instr))
        (target, (false, 0))).2.2 =
      xs.getD target 0 := by
  induction xs generalizing target with
  | nil =>
      cases target <;> simp [intRowGetDStep, intRowGetDCoeffStep, binaryNatEqBool]
  | cons z zs ih =>
      cases target with
      | zero =>
          have h := intRowGetDCoeffInstructions_fold_found zs 0 z
          simpa [intRowGetDCoeffInstruction, intRowGetDStep, intRowGetDCoeffStep,
            binaryNatEqBool] using congrArg (fun q : IntRowGetDAcc => q.2.2) h
      | succ target =>
          have hZero : binaryNatEqBool (Nat.succ target, 0) = false := by
            have hne : Nat.succ target ≠ 0 := by omega
            exact Bool.eq_false_iff.mpr ((binaryNatEqBool_eq_true_iff _).not.mpr hne)
          simpa [intRowGetDCoeffInstruction, intRowGetDStep, intRowGetDCoeffStep,
            hZero] using ih target

theorem intRowGetDFromInput_eq_getD (p : Nat × List Int) :
    intRowGetDFromInput p = p.2.getD p.1 0 := by
  rcases p with ⟨target, row⟩
  have h := intRowGetDCoeffInstructions_value_eq_getD row target
  simp [intRowGetDFromInput, intRowGetDFromInstructions, intRowGetDInstructions,
    intRowGetDInitInstruction, intRowGetDInitAcc, intRowGetDStep] at h ⊢
  exact h

theorem intRowGetDInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      intRowGetDInstructionEncodedType
      intRowGetDInitInstruction := by
  have hTag :
      TMPolyTimeMap EncodedType.binaryNat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.binaryNat EncodedType.bool false
  have hZeroInt :
      TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryInt (fun _ : Nat => (0 : Int)) :=
    TMPolyTimeMap.const EncodedType.binaryNat EncodedType.binaryInt (0 : Int)
  have hPayload :
      TMPolyTimeMap EncodedType.binaryNat intRowGetDInstructionPayloadEncodedType
        (fun target : Nat => (target, (0 : Int))) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.binaryNat) hZeroInt
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [intRowGetDInitInstruction, intRowGetDInstructionEncodedType,
    intRowGetDInstructionPayloadEncodedType] using hOut

theorem intRowGetDCoeffInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryInt
      intRowGetDInstructionEncodedType
      intRowGetDCoeffInstruction := by
  have hTag :
      TMPolyTimeMap EncodedType.binaryInt EncodedType.bool (fun _ : Int => true) :=
    TMPolyTimeMap.const EncodedType.binaryInt EncodedType.bool true
  have hZeroNat :
      TMPolyTimeMap EncodedType.binaryInt EncodedType.binaryNat (fun _ : Int => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.binaryInt EncodedType.binaryNat (0 : Nat)
  have hPayload :
      TMPolyTimeMap EncodedType.binaryInt intRowGetDInstructionPayloadEncodedType
        (fun z : Int => ((0 : Nat), z)) :=
    TMPolyTimeMap.prod_mk hZeroNat (TMPolyTimeMap.id EncodedType.binaryInt)
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [intRowGetDCoeffInstruction, intRowGetDInstructionEncodedType,
    intRowGetDInstructionPayloadEncodedType] using hOut

theorem intRowGetDInstructions_tm_polytime :
    TMPolyTimeMap
      intRowGetDInputEncodedType
      intRowGetDInstructionListEncodedType
      intRowGetDInstructions := by
  let X := intRowGetDInputEncodedType
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × List Int => p.1) := by
    simpa [X, intRowGetDInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat intRowBinaryStructuredEncodedType
  have hRow :
      TMPolyTimeMap X intRowBinaryStructuredEncodedType (fun p : Nat × List Int => p.2) := by
    simpa [X, intRowGetDInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat intRowBinaryStructuredEncodedType
  have hInit :
      TMPolyTimeMap X intRowGetDInstructionEncodedType
        (fun p : Nat × List Int => intRowGetDInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp intRowGetDInitInstruction_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hMappedRow :
      TMPolyTimeMap X intRowGetDInstructionListEncodedType
        (fun p : Nat × List Int => p.2.map intRowGetDCoeffInstruction) := by
    have hMap := TMPolyTimeMap.list_map intRowGetDCoeffInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRow
    simpa [Function.comp, intRowGetDInstructionListEncodedType, X,
      intRowBinaryStructuredEncodedType] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod intRowGetDInstructionEncodedType
          intRowGetDInstructionListEncodedType)
        (fun p : Nat × List Int =>
          (intRowGetDInitInstruction p.1, p.2.map intRowGetDCoeffInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedRow
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons intRowGetDInstructionEncodedType)
      hConsInput
  simpa [Function.comp, intRowGetDInstructions, intRowGetDInstructionListEncodedType, X]
    using hCons

theorem intRowGetDCoeffStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod intRowGetDAccEncodedType EncodedType.binaryInt)
      intRowGetDAccEncodedType
      intRowGetDCoeffStep := by
  let X := EncodedType.prod intRowGetDAccEncodedType EncodedType.binaryInt
  let A := intRowGetDAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : IntRowGetDAcc × Int => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A EncodedType.binaryInt
  have hCoeff : TMPolyTimeMap X EncodedType.binaryInt (fun p : IntRowGetDAcc × Int => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A EncodedType.binaryInt
  have hRemaining : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : IntRowGetDAcc × Int => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, intRowGetDAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
        (fun p : IntRowGetDAcc × Int => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat
      (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, intRowGetDAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool
      (fun p : IntRowGetDAcc × Int => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.binaryInt
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hValue : TMPolyTimeMap X EncodedType.binaryInt
      (fun p : IntRowGetDAcc × Int => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.binaryInt
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hZeroNat : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : IntRowGetDAcc × Int => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hOneNat : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : IntRowGetDAcc × Int => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (1 : Nat)
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : IntRowGetDAcc × Int => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : IntRowGetDAcc × Int => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hRemainingZeroInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : IntRowGetDAcc × Int => (p.1.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hZeroNat
  have hRemainingIsZero :
      TMPolyTimeMap X EncodedType.bool
        (fun p : IntRowGetDAcc × Int => binaryNatEqBool (p.1.1, 0)) := by
    have hComp := TMPolyTimeMap.comp binaryNatEqBool_tm_polytime hRemainingZeroInput
    simpa [Function.comp, X] using hComp
  have hPredInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : IntRowGetDAcc × Int => (p.1.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hOneNat
  have hPred :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : IntRowGetDAcc × Int => p.1.1 - 1) := by
    have hComp := TMPolyTimeMap.comp binaryNatSub_tm_polytime hPredInput
    simpa [Function.comp, X] using hComp
  have hHitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
        (fun p : IntRowGetDAcc × Int => (true, p.2)) :=
    TMPolyTimeMap.prod_mk hTrue hCoeff
  have hHit :
      TMPolyTimeMap X A
        (fun p : IntRowGetDAcc × Int => (show IntRowGetDAcc from (0, (true, p.2)))) :=
    TMPolyTimeMap.prod_mk hZeroNat hHitTail
  have hMissTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
        (fun p : IntRowGetDAcc × Int => (false, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hFalse hValue
  have hMiss :
      TMPolyTimeMap X A
        (fun p : IntRowGetDAcc × Int => (p.1.1 - 1, (false, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hPred hMissTail
  have hZeroBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : IntRowGetDAcc × Int => (binaryNatEqBool (p.1.1, 0), p)) :=
    TMPolyTimeMap.prod_mk hRemainingIsZero (TMPolyTimeMap.id X)
  have hZeroBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (IntRowGetDAcc × Int) =>
          match p.1 with
          | true => (show IntRowGetDAcc from (0, (true, p.2.2)))
          | false => (show IntRowGetDAcc from (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : IntRowGetDAcc × Int =>
        (show IntRowGetDAcc from (p.1.1 - 1, (false, p.1.2.2))))
      (fTrue := fun p : IntRowGetDAcc × Int =>
        (show IntRowGetDAcc from (0, (true, p.2))))
      hMiss hHit
  have hNotFound :
      TMPolyTimeMap X A
        (fun p : IntRowGetDAcc × Int =>
          if binaryNatEqBool (p.1.1, 0) then
            (show IntRowGetDAcc from (0, (true, p.2)))
          else
            (show IntRowGetDAcc from (p.1.1 - 1, (false, p.1.2.2)))) := by
    have hComp := TMPolyTimeMap.comp hZeroBranch hZeroBranchInput
    convert hComp using 1
    funext p
    cases h : binaryNatEqBool (p.1.1, 0) <;> simp [Function.comp, h]
  have hFoundBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : IntRowGetDAcc × Int => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hFound (TMPolyTimeMap.id X)
  have hFoundBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (IntRowGetDAcc × Int) =>
          match p.1 with
          | true => p.2.1
          | false =>
              if binaryNatEqBool (p.2.1.1, 0) then
                (show IntRowGetDAcc from (0, (true, p.2.2)))
              else
                (show IntRowGetDAcc from (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : IntRowGetDAcc × Int =>
        if binaryNatEqBool (p.1.1, 0) then
          (show IntRowGetDAcc from (0, (true, p.2)))
        else
          (show IntRowGetDAcc from (p.1.1 - 1, (false, p.1.2.2)))
      )
      (fTrue := fun p : IntRowGetDAcc × Int => p.1)
      hNotFound hAcc
  have hOut := TMPolyTimeMap.comp hFoundBranch hFoundBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨remaining, found, value⟩, z⟩
  cases found <;> cases h : binaryNatEqBool (remaining, 0) <;>
    simp [Function.comp, intRowGetDCoeffStep, h]

theorem intRowGetDStepInit_tm_polytime :
    TMPolyTimeMap
      intRowGetDInstructionPayloadEncodedType
      intRowGetDAccEncodedType
      (fun payload : Nat × Int => (show IntRowGetDAcc from (payload.1, (false, 0)))) := by
  have hTarget :
      TMPolyTimeMap intRowGetDInstructionPayloadEncodedType EncodedType.binaryNat
        (fun payload : Nat × Int => payload.1) := by
    simpa [intRowGetDInstructionPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryInt
  have hFalse :
      TMPolyTimeMap intRowGetDInstructionPayloadEncodedType EncodedType.bool
        (fun _ : Nat × Int => false) :=
    TMPolyTimeMap.const intRowGetDInstructionPayloadEncodedType EncodedType.bool false
  have hZeroInt :
      TMPolyTimeMap intRowGetDInstructionPayloadEncodedType EncodedType.binaryInt
        (fun _ : Nat × Int => (0 : Int)) :=
    TMPolyTimeMap.const intRowGetDInstructionPayloadEncodedType EncodedType.binaryInt (0 : Int)
  have hTail :
      TMPolyTimeMap intRowGetDInstructionPayloadEncodedType
        (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
        (fun _ : Nat × Int => (false, (0 : Int))) :=
    TMPolyTimeMap.prod_mk hFalse hZeroInt
  have hOut := TMPolyTimeMap.prod_mk hTarget hTail
  simpa [intRowGetDAccEncodedType] using hOut

theorem intRowGetDStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod intRowGetDAccEncodedType intRowGetDInstructionEncodedType)
      intRowGetDAccEncodedType
      intRowGetDStep := by
  let X := EncodedType.prod intRowGetDAccEncodedType intRowGetDInstructionEncodedType
  let P := intRowGetDInstructionPayloadEncodedType
  have hAcc : TMPolyTimeMap X intRowGetDAccEncodedType
      (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst intRowGetDAccEncodedType intRowGetDInstructionEncodedType
  have hInstr : TMPolyTimeMap X intRowGetDInstructionEncodedType
      (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd intRowGetDAccEncodedType intRowGetDInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool P
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, intRowGetDInstructionEncodedType, X, P] using hComp
  have hPayload : TMPolyTimeMap X P
      (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool P
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, intRowGetDInstructionEncodedType, X, P] using hComp
  have hPayloadCoeff : TMPolyTimeMap X EncodedType.binaryInt
      (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryInt
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, P, intRowGetDInstructionPayloadEncodedType, X] using hComp
  have hCoeffInput :
      TMPolyTimeMap X (EncodedType.prod intRowGetDAccEncodedType EncodedType.binaryInt)
        (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier =>
          (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hPayloadCoeff
  have hCoeffBranch :
      TMPolyTimeMap X intRowGetDAccEncodedType
        (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier =>
          intRowGetDCoeffStep (p.1, p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp intRowGetDCoeffStep_tm_polytime hCoeffInput
    simpa [Function.comp, X] using hComp
  have hInitBranch :
      TMPolyTimeMap X intRowGetDAccEncodedType
        (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier =>
          (show IntRowGetDAcc from (p.2.2.1, (false, 0)))) := by
    have hComp := TMPolyTimeMap.comp intRowGetDStepInit_tm_polytime hPayload
    simpa [Function.comp, X, P] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) intRowGetDAccEncodedType
        (fun p : Bool × (IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier) =>
          match p.1 with
          | true => intRowGetDCoeffStep (p.2.1, p.2.2.2.2)
          | false => (show IntRowGetDAcc from (p.2.2.2.1, (false, 0)))) :=
    Clique.boolProduct_dispatch_tm_polytime X intRowGetDAccEncodedType
      (fFalse := fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier =>
        (show IntRowGetDAcc from (p.2.2.1, (false, 0))))
      (fTrue := fun p : IntRowGetDAcc × intRowGetDInstructionEncodedType.Carrier =>
        intRowGetDCoeffStep (p.1, p.2.2.2))
      hInitBranch hCoeffBranch
  have hOut := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hOut using 1

theorem intRowGetDInitAcc_bound
    (xs : List intRowGetDInstructionEncodedType.Carrier) :
    intRowGetDAccEncodedType.inputSize intRowGetDInitAcc ≤
      (Polynomial.C 20).eval (intRowGetDInstructionListEncodedType.inputSize xs) := by
  simp [intRowGetDInitAcc, intRowGetDAccEncodedType, EncodedType.inputSize_prod]

theorem intRowGetDInstruction_target_inputSize_le
    (instr : intRowGetDInstructionEncodedType.Carrier) :
    EncodedType.binaryNat.inputSize instr.2.1 ≤
      intRowGetDInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, target, z⟩
  simp [intRowGetDInstructionEncodedType, intRowGetDInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem intRowGetDInstruction_coeff_inputSize_le
    (instr : intRowGetDInstructionEncodedType.Carrier) :
    EncodedType.binaryInt.inputSize instr.2.2 ≤
      intRowGetDInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, target, z⟩
  simp [intRowGetDInstructionEncodedType, intRowGetDInstructionPayloadEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem intRowGetDStep_growth
    (source : List intRowGetDInstructionEncodedType.Carrier)
    (acc : intRowGetDAccEncodedType.Carrier)
    (instr : intRowGetDInstructionEncodedType.Carrier)
    (hInstr :
      intRowGetDInstructionEncodedType.inputSize instr ≤
        intRowGetDInstructionListEncodedType.inputSize source) :
    intRowGetDAccEncodedType.inputSize (intRowGetDStep (acc, instr)) ≤
      intRowGetDAccEncodedType.inputSize acc +
      (Polynomial.C 50 * Polynomial.X + Polynomial.C 100).eval
          (intRowGetDInstructionListEncodedType.inputSize source) := by
  change IntRowGetDAcc at acc
  rcases acc with ⟨remaining, found, value⟩
  rcases instr with ⟨tag, target, z⟩
  have hTargetSize :
      EncodedType.binaryNat.inputSize target ≤
        intRowGetDInstructionListEncodedType.inputSize source :=
    (intRowGetDInstruction_target_inputSize_le (tag, target, z)).trans hInstr
  have hCoeffSize :
      EncodedType.binaryInt.inputSize z ≤
        intRowGetDInstructionListEncodedType.inputSize source :=
    (intRowGetDInstruction_coeff_inputSize_le (tag, target, z)).trans hInstr
  have hPredSize :
      EncodedType.binaryNat.inputSize (remaining - 1) ≤
        EncodedType.binaryNat.inputSize remaining :=
    binaryNat_inputSize_mono (Nat.sub_le remaining 1)
  cases tag
  · simp [intRowGetDStep, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      intRowGetDAccEncodedType, EncodedType.inputSize_prod]
    omega
  · cases found
    · cases hZero : binaryNatEqBool (remaining, 0)
      · simp [intRowGetDStep, intRowGetDCoeffStep, hZero, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_X, intRowGetDAccEncodedType,
          EncodedType.inputSize_prod]
        omega
      · simp [intRowGetDStep, intRowGetDCoeffStep, hZero, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_X, intRowGetDAccEncodedType,
          EncodedType.inputSize_prod]
        omega
    · simp [intRowGetDStep, intRowGetDCoeffStep, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X]

theorem intRowGetDFold_tm_polytime :
    TMPolyTimeMap
      intRowGetDInstructionListEncodedType
      intRowGetDAccEncodedType
      (fun xs : List intRowGetDInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => intRowGetDStep (acc, instr)) intRowGetDInitAcc) := by
  rcases intRowGetDStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      intRowGetDInstructionEncodedType intRowGetDAccEncodedType
      intRowGetDStep intRowGetDInitAcc hStep
      (Polynomial.C 20) (Polynomial.C 50 * Polynomial.X + Polynomial.C 100) ?_ ?_
  · intro xs
    exact intRowGetDInitAcc_bound xs
  · intro source acc instr hInstr
    exact intRowGetDStep_growth source acc instr hInstr

theorem intRowGetDFromInstructions_tm_polytime :
    TMPolyTimeMap
      intRowGetDInstructionListEncodedType
      EncodedType.binaryInt
      intRowGetDFromInstructions := by
  have hFold := intRowGetDFold_tm_polytime
  have hTail :=
    TMPolyTimeMap.snd EncodedType.binaryNat (EncodedType.prod EncodedType.bool EncodedType.binaryInt)
  have hValue := TMPolyTimeMap.snd EncodedType.bool EncodedType.binaryInt
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hValueComp := TMPolyTimeMap.comp hValue hTailComp
  simpa [Function.comp, intRowGetDFromInstructions, intRowGetDAccEncodedType]
    using hValueComp

theorem intRowGetDFromInput_tm_polytime :
    TMPolyTimeMap
      intRowGetDInputEncodedType
      EncodedType.binaryInt
      intRowGetDFromInput := by
  have hComp :=
    TMPolyTimeMap.comp intRowGetDFromInstructions_tm_polytime
      intRowGetDInstructions_tm_polytime
  simpa [Function.comp, intRowGetDFromInput] using hComp

theorem intRowGetD_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod intRowBinaryStructuredEncodedType EncodedType.binaryNat)
      EncodedType.binaryInt
      intRowGetD := by
  let X := EncodedType.prod intRowBinaryStructuredEncodedType EncodedType.binaryNat
  have hRow :
      TMPolyTimeMap X intRowBinaryStructuredEncodedType (fun p : List Int × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst intRowBinaryStructuredEncodedType EncodedType.binaryNat
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat (fun p : List Int × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd intRowBinaryStructuredEncodedType EncodedType.binaryNat
  have hInput :
      TMPolyTimeMap X intRowGetDInputEncodedType
        (fun p : List Int × Nat => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hTarget hRow
  have hComp := TMPolyTimeMap.comp intRowGetDFromInput_tm_polytime hInput
  convert hComp using 1
  funext p
  rcases p with ⟨row, target⟩
  exact (intRowGetDFromInput_eq_getD (target, row)).symm

theorem compactCoeffAt_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod intRowBinaryStructuredEncodedType EncodedType.binaryNat)
      EncodedType.binaryInt
      (fun p : List Int × Nat => compactCoeffAt p.1 p.2) := by
  simpa [compactCoeffAt, intRowGetD] using intRowGetD_tm_polytime

end Knapsack
end Karp21
end ComplexityReduction
