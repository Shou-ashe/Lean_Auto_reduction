import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.DigitCode

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Shared-base digit-code list generation.

Given one binary base and a list of little-endian digit vectors, this layer
constructs the paired list `[(base, digits)]` and then maps the direct
`binaryNatOfDigits` witness over it.
-/

def sharedBaseDigitPairEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat (EncodedType.list EncodedType.binaryNat)

def sharedBaseDigitPairListEncodedType : EncodedType :=
  EncodedType.list sharedBaseDigitPairEncodedType

def sharedBaseDigitPairsInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.list (EncodedType.list EncodedType.binaryNat))

def sharedBaseDigitPairsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat sharedBaseDigitPairListEncodedType

def sharedBaseDigitPairsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool sharedBaseDigitPairEncodedType

def sharedBaseDigitPairsInstructionListEncodedType : EncodedType :=
  EncodedType.list sharedBaseDigitPairsInstructionEncodedType

abbrev SharedBaseDigitPairsInstruction := Bool × (Nat × List Nat)

def sharedBaseDigitPairsInitAcc : Nat × List (Nat × List Nat) :=
  (0, [])

def sharedBaseDigitPairsInitInstruction (base : Nat) :
    SharedBaseDigitPairsInstruction :=
  (false, (base, []))

def sharedBaseDigitPairsDigitInstruction (digits : List Nat) :
    SharedBaseDigitPairsInstruction :=
  (true, ((0 : Nat), digits))

def sharedBaseDigitPairsInstructions (p : Nat × List (List Nat)) :
    List SharedBaseDigitPairsInstruction :=
  sharedBaseDigitPairsInitInstruction p.1 ::
    p.2.map sharedBaseDigitPairsDigitInstruction

def sharedBaseDigitPairsStep
    (p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction) :
    Nat × List (Nat × List Nat) :=
  match p.2.1 with
  | true => (p.1.1, p.1.2 ++ [(p.1.1, (p.2.2.2 : List Nat))])
  | false => (p.2.2.1, [])

def sharedBaseDigitPairsFold
    (instructions : List SharedBaseDigitPairsInstruction) :
    Nat × List (Nat × List Nat) :=
  instructions.foldl (fun acc instr => sharedBaseDigitPairsStep (acc, instr))
    sharedBaseDigitPairsInitAcc

def sharedBaseDigitPairs (p : Nat × List (List Nat)) : List (Nat × List Nat) :=
  (sharedBaseDigitPairsFold (sharedBaseDigitPairsInstructions p)).2

def sharedBaseDigitCodes (p : Nat × List (List Nat)) : List Nat :=
  (sharedBaseDigitPairs p).map binaryNatOfDigits

theorem sharedBaseDigitPairsDigitInstructions_fold
    (base : Nat) (out : List (Nat × List Nat)) (vectors : List (List Nat)) :
    (vectors.map sharedBaseDigitPairsDigitInstruction).foldl
        (fun acc instr => sharedBaseDigitPairsStep (acc, instr))
        (base, out) =
      (base, out ++ vectors.map fun digits => (base, digits)) := by
  induction vectors generalizing out with
  | nil =>
      simp [sharedBaseDigitPairsStep]
  | cons digits vectors ih =>
      rw [List.map_cons, List.foldl_cons]
      simp only [sharedBaseDigitPairsDigitInstruction, sharedBaseDigitPairsStep]
      simpa [List.append_assoc] using ih (out ++ [(base, digits)])

theorem sharedBaseDigitPairs_eq (p : Nat × List (List Nat)) :
    sharedBaseDigitPairs p = p.2.map fun digits => (p.1, digits) := by
  rcases p with ⟨base, vectors⟩
  have h := sharedBaseDigitPairsDigitInstructions_fold base [] vectors
  simpa [sharedBaseDigitPairs, sharedBaseDigitPairsFold, sharedBaseDigitPairsInstructions,
    sharedBaseDigitPairsInitInstruction, sharedBaseDigitPairsInitAcc,
    sharedBaseDigitPairsStep] using congrArg Prod.snd h

theorem sharedBaseDigitCodes_eq (p : Nat × List (List Nat)) :
    sharedBaseDigitCodes p = p.2.map fun digits => Nat.ofDigits p.1 digits := by
  rw [sharedBaseDigitCodes, sharedBaseDigitPairs_eq]
  simp [binaryNatOfDigits]

theorem sharedBaseDigitPairListAppendSingleton_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod sharedBaseDigitPairListEncodedType sharedBaseDigitPairEncodedType)
      sharedBaseDigitPairListEncodedType
      (fun p : List (Nat × List Nat) × (Nat × List Nat) => p.1 ++ [p.2]) := by
  let X := EncodedType.prod sharedBaseDigitPairListEncodedType sharedBaseDigitPairEncodedType
  have hHead :
      TMPolyTimeMap X sharedBaseDigitPairListEncodedType
        (fun p : List (Nat × List Nat) × (Nat × List Nat) => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst sharedBaseDigitPairListEncodedType sharedBaseDigitPairEncodedType
  have hPayload :
      TMPolyTimeMap X sharedBaseDigitPairEncodedType
        (fun p : List (Nat × List Nat) × (Nat × List Nat) => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd sharedBaseDigitPairListEncodedType sharedBaseDigitPairEncodedType
  have hSingleton :
      TMPolyTimeMap X sharedBaseDigitPairListEncodedType
        (fun p : List (Nat × List Nat) × (Nat × List Nat) => [p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton sharedBaseDigitPairEncodedType) hPayload
    simpa [Function.comp, sharedBaseDigitPairListEncodedType] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod sharedBaseDigitPairListEncodedType sharedBaseDigitPairListEncodedType)
        (fun p : List (Nat × List Nat) × (Nat × List Nat) => (p.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hHead hSingleton
  have hComp := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append sharedBaseDigitPairEncodedType) hPair
  simpa [Function.comp, X, sharedBaseDigitPairListEncodedType] using hComp

theorem sharedBaseDigitPairsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod sharedBaseDigitPairsAccEncodedType
        sharedBaseDigitPairsInstructionEncodedType)
      sharedBaseDigitPairsAccEncodedType
      sharedBaseDigitPairsStep := by
  let X := EncodedType.prod sharedBaseDigitPairsAccEncodedType
    sharedBaseDigitPairsInstructionEncodedType
  let A := sharedBaseDigitPairsAccEncodedType
  have hAcc : TMPolyTimeMap X A
      (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst sharedBaseDigitPairsAccEncodedType
        sharedBaseDigitPairsInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X sharedBaseDigitPairsInstructionEncodedType
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.2) := by
    simpa [X, A] using
      TMPolyTimeMap.snd sharedBaseDigitPairsAccEncodedType
        sharedBaseDigitPairsInstructionEncodedType
  have hBase : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat sharedBaseDigitPairListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, sharedBaseDigitPairsAccEncodedType, X] using hComp
  have hOut : TMPolyTimeMap X sharedBaseDigitPairListEncodedType
      (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat sharedBaseDigitPairListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, sharedBaseDigitPairsAccEncodedType, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool sharedBaseDigitPairEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, sharedBaseDigitPairsInstructionEncodedType, X] using hComp
  have hPayload :
      TMPolyTimeMap X sharedBaseDigitPairEncodedType
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool sharedBaseDigitPairEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, sharedBaseDigitPairsInstructionEncodedType, X] using hComp
  have hPayloadBase : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, sharedBaseDigitPairEncodedType, X] using hComp
  have hPayloadDigits :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat
      (EncodedType.list EncodedType.binaryNat)
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, sharedBaseDigitPairEncodedType, X] using hComp
  have hEmpty :
      TMPolyTimeMap X sharedBaseDigitPairListEncodedType
        (fun _ : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          ([] : List (Nat × List Nat))) :=
    TMPolyTimeMap.const X sharedBaseDigitPairListEncodedType []
  have hFalseBranch :
      TMPolyTimeMap X A
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          (p.2.2.1, ([] : List (Nat × List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadBase hEmpty
  have hPairPayload :
      TMPolyTimeMap X sharedBaseDigitPairEncodedType
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          (p.1.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hBase hPayloadDigits
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod sharedBaseDigitPairListEncodedType sharedBaseDigitPairEncodedType)
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          (p.1.2, (p.1.1, p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hOut hPairPayload
  have hAppend :
      TMPolyTimeMap X sharedBaseDigitPairListEncodedType
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          p.1.2 ++ [(p.1.1, p.2.2.2)]) := by
    have hComp := TMPolyTimeMap.comp
      sharedBaseDigitPairListAppendSingleton_tm_polytime hAppendInput
    simpa [Function.comp, X] using hComp
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          (p.1.1, p.1.2 ++ [(p.1.1, p.2.2.2)])) :=
    TMPolyTimeMap.prod_mk hBase hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
          (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × ((Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction) =>
          match p.1 with
          | true => (p.2.1.1, p.2.1.2 ++ [(p.2.1.1, p.2.2.2.2)])
          | false => (p.2.2.2.1, ([] : List (Nat × List Nat)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
        (p.2.2.1, ([] : List (Nat × List Nat))))
      (fTrue := fun p : (Nat × List (Nat × List Nat)) × SharedBaseDigitPairsInstruction =>
        (p.1.1, p.1.2 ++ [(p.1.1, p.2.2.2)]))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1

def sharedBaseDigitPairsFoldInv (N : Nat)
    (acc : Nat × List (Nat × List Nat)) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ N

theorem sharedBaseDigitPairsInstruction_base_inputSize_le
    (instr : SharedBaseDigitPairsInstruction) :
    EncodedType.binaryNat.inputSize instr.2.1 ≤
      sharedBaseDigitPairsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, base, digits⟩
  simp [sharedBaseDigitPairsInstructionEncodedType, sharedBaseDigitPairEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem sharedBaseDigitPairsInstruction_digits_inputSize_le
    (instr : SharedBaseDigitPairsInstruction) :
    (EncodedType.list EncodedType.binaryNat).inputSize instr.2.2 ≤
      sharedBaseDigitPairsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, base, digits⟩
  simp [sharedBaseDigitPairsInstructionEncodedType, sharedBaseDigitPairEncodedType,
    EncodedType.inputSize_prod]
  omega

theorem sharedBaseDigitPairsStep_growth
    (source : List SharedBaseDigitPairsInstruction)
    (acc : Nat × List (Nat × List Nat))
    (instr : SharedBaseDigitPairsInstruction)
    (hInv :
      sharedBaseDigitPairsFoldInv
        (sharedBaseDigitPairsInstructionListEncodedType.inputSize source) acc)
    (hinstr :
      sharedBaseDigitPairsInstructionEncodedType.inputSize instr ≤
        sharedBaseDigitPairsInstructionListEncodedType.inputSize source) :
    sharedBaseDigitPairsFoldInv
        (sharedBaseDigitPairsInstructionListEncodedType.inputSize source)
        (sharedBaseDigitPairsStep (acc, instr)) ∧
      sharedBaseDigitPairsAccEncodedType.inputSize (sharedBaseDigitPairsStep (acc, instr)) ≤
        sharedBaseDigitPairsAccEncodedType.inputSize acc +
          ((Polynomial.C 3 * Polynomial.X + Polynomial.C 6).eval
            (sharedBaseDigitPairsInstructionListEncodedType.inputSize source)) := by
  rcases acc with ⟨base, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadBase, digits⟩
  have hPayloadBase :
      EncodedType.binaryNat.inputSize payloadBase ≤
        sharedBaseDigitPairsInstructionListEncodedType.inputSize source :=
    (sharedBaseDigitPairsInstruction_base_inputSize_le (tag, payloadBase, digits)).trans hinstr
  have hDigits :
      (EncodedType.list EncodedType.binaryNat).inputSize digits ≤
        sharedBaseDigitPairsInstructionListEncodedType.inputSize source :=
    (sharedBaseDigitPairsInstruction_digits_inputSize_le (tag, payloadBase, digits)).trans hinstr
  cases tag
  · constructor
    · exact hPayloadBase
    · simp [sharedBaseDigitPairsStep, sharedBaseDigitPairsAccEncodedType,
        sharedBaseDigitPairListEncodedType, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, EncodedType.inputSize_prod]
      have hEmpty :
          (EncodedType.list sharedBaseDigitPairEncodedType).inputSize
          ([] : List (Nat × List Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil sharedBaseDigitPairEncodedType
      rw [hEmpty]
      omega
  · constructor
    · exact hInv
    · have hAppend :
          sharedBaseDigitPairListEncodedType.inputSize (out ++ [(base, digits)]) =
            sharedBaseDigitPairListEncodedType.inputSize out +
              sharedBaseDigitPairEncodedType.inputSize (base, digits) + 1 := by
        exact encodedList_inputSize_append_singleton sharedBaseDigitPairEncodedType out
          (base, digits)
      simp [sharedBaseDigitPairsStep, sharedBaseDigitPairsAccEncodedType,
        sharedBaseDigitPairEncodedType, sharedBaseDigitPairListEncodedType,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        EncodedType.inputSize_prod] at hAppend ⊢
      have hBase : EncodedType.binaryNat.inputSize base ≤
          sharedBaseDigitPairsInstructionListEncodedType.inputSize source := by
        exact hInv
      omega

theorem sharedBaseDigitPairsFold_tm_polytime :
    TMPolyTimeMap
      sharedBaseDigitPairsInstructionListEncodedType
      sharedBaseDigitPairsAccEncodedType
      sharedBaseDigitPairsFold := by
  rcases sharedBaseDigitPairsStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        sharedBaseDigitPairsInstructionListEncodedType
        sharedBaseDigitPairsAccEncodedType
        (fun instructions : List SharedBaseDigitPairsInstruction =>
          instructions.foldl (fun acc instr => sharedBaseDigitPairsStep (acc, instr))
            sharedBaseDigitPairsInitAcc) := by
    refine
      TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
        sharedBaseDigitPairsInstructionEncodedType sharedBaseDigitPairsAccEncodedType
        sharedBaseDigitPairsStep sharedBaseDigitPairsInitAcc hStep
        (Polynomial.C 1) (Polynomial.C 3 * Polynomial.X + Polynomial.C 6)
        sharedBaseDigitPairsFoldInv ?_ ?_
    · intro instructions
      constructor
      · simp [sharedBaseDigitPairsFoldInv, sharedBaseDigitPairsInitAcc,
          EncodedType.inputSize, EncodedType.binaryNat]
      · simp [sharedBaseDigitPairsInitAcc, sharedBaseDigitPairsAccEncodedType,
          sharedBaseDigitPairListEncodedType, EncodedType.inputSize,
          EncodedType.prod, EncodedType.binaryNat, EncodedType.list]
        constructor <;> rfl
    · intro source acc instr hInv hinstr
      exact sharedBaseDigitPairsStep_growth source acc instr hInv hinstr
  simpa [sharedBaseDigitPairsFold] using hFold

theorem sharedBaseDigitPairsInitInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      sharedBaseDigitPairsInstructionEncodedType
      sharedBaseDigitPairsInitInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hEmpty :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const X (EncodedType.list EncodedType.binaryNat) []
  have hPayload :
      TMPolyTimeMap X sharedBaseDigitPairEncodedType
        (fun base : Nat => (base, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) hEmpty
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [sharedBaseDigitPairsInitInstruction, sharedBaseDigitPairsInstructionEncodedType,
    sharedBaseDigitPairEncodedType, X] using hOut

theorem sharedBaseDigitPairsDigitInstruction_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.binaryNat)
      sharedBaseDigitPairsInstructionEncodedType
      sharedBaseDigitPairsDigitInstruction := by
  let X := EncodedType.list EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : List Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : List Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X sharedBaseDigitPairEncodedType
        (fun digits : List Nat => ((0 : Nat), digits)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  convert hOut using 1

theorem sharedBaseDigitPairsInstructions_tm_polytime :
    TMPolyTimeMap
      sharedBaseDigitPairsInputEncodedType
      sharedBaseDigitPairsInstructionListEncodedType
      sharedBaseDigitPairsInstructions := by
  let X := sharedBaseDigitPairsInputEncodedType
  let V := EncodedType.list (EncodedType.list EncodedType.binaryNat)
  have hBase : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × List (List Nat) => p.1) := by
    simpa [X, sharedBaseDigitPairsInputEncodedType, V] using
      TMPolyTimeMap.fst EncodedType.binaryNat V
  have hVectors : TMPolyTimeMap X V (fun p : Nat × List (List Nat) => p.2) := by
    simpa [X, sharedBaseDigitPairsInputEncodedType, V] using
      TMPolyTimeMap.snd EncodedType.binaryNat V
  have hInit :
      TMPolyTimeMap X sharedBaseDigitPairsInstructionEncodedType
        (fun p : Nat × List (List Nat) => sharedBaseDigitPairsInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp sharedBaseDigitPairsInitInstruction_tm_polytime hBase
    simpa [Function.comp, X] using hComp
  have hDigitInstrs :
      TMPolyTimeMap X sharedBaseDigitPairsInstructionListEncodedType
        (fun p : Nat × List (List Nat) =>
          p.2.map sharedBaseDigitPairsDigitInstruction) := by
    have hMap := TMPolyTimeMap.list_map sharedBaseDigitPairsDigitInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hVectors
    simpa [Function.comp, sharedBaseDigitPairsInstructionListEncodedType, V, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod sharedBaseDigitPairsInstructionEncodedType
          sharedBaseDigitPairsInstructionListEncodedType)
        (fun p : Nat × List (List Nat) =>
          (sharedBaseDigitPairsInitInstruction p.1,
            p.2.map sharedBaseDigitPairsDigitInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hDigitInstrs
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons sharedBaseDigitPairsInstructionEncodedType) hConsInput
  simpa [Function.comp, sharedBaseDigitPairsInstructions, X,
    sharedBaseDigitPairsInstructionListEncodedType] using hCons

theorem sharedBaseDigitPairs_tm_polytime :
    TMPolyTimeMap
      sharedBaseDigitPairsInputEncodedType
      sharedBaseDigitPairListEncodedType
      sharedBaseDigitPairs := by
  have hFold := TMPolyTimeMap.comp sharedBaseDigitPairsFold_tm_polytime
    sharedBaseDigitPairsInstructions_tm_polytime
  have hSnd :
      TMPolyTimeMap sharedBaseDigitPairsAccEncodedType sharedBaseDigitPairListEncodedType
        (fun acc : Nat × List (Nat × List Nat) => acc.2) := by
    simpa [sharedBaseDigitPairsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat sharedBaseDigitPairListEncodedType
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, sharedBaseDigitPairs] using hComp

theorem sharedBaseDigitCodes_tm_polytime :
    TMPolyTimeMap
      sharedBaseDigitPairsInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      sharedBaseDigitCodes := by
  have hMap := TMPolyTimeMap.list_map binaryNatOfDigits_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap sharedBaseDigitPairs_tm_polytime
  simpa [Function.comp, sharedBaseDigitCodes, sharedBaseDigitPairListEncodedType,
    binaryNatOfDigitsInputEncodedType, sharedBaseDigitPairEncodedType] using hComp

end Knapsack
end Karp21
end ComplexityReduction
