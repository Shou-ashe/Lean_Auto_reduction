import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.Front

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-!
Direct unary-to-binary encoding bridge for faithful structured 0-1 IP.

The semantic carrier and predicate are unchanged.  The map only changes the
numeric payload encoding from unary `Nat`/`Int` blocks to binary blocks.
-/

def integerProgrammingStructuredTupleOfInput (I : IntegerProgrammingInput) :
    integerProgrammingTupleStructuredEncodedType.Carrier :=
  (I.numVariables, I.constraints)

theorem integerProgrammingStructuredTupleOfInput_encode (I : IntegerProgrammingInput) :
    integerProgrammingTupleStructuredEncodedType.encode
        (integerProgrammingStructuredTupleOfInput I) =
      integerProgrammingStructuredEncodedType.encode I := by
  rfl

noncomputable def integerProgrammingStructuredTupleOfInputTMBackedMap :
    TMBackedCostedMap
      integerProgrammingStructuredEncodedType
      integerProgrammingTupleStructuredEncodedType
      integerProgrammingStructuredTupleOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    integerProgrammingStructuredEncodedType
    integerProgrammingTupleStructuredEncodedType
    integerProgrammingStructuredTupleOfInput
    (Equiv.refl integerProgrammingTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change
        integerProgrammingTupleStructuredEncodedType.encode
            (integerProgrammingStructuredTupleOfInput I) =
          (integerProgrammingStructuredEncodedType.encode I).map id
      simp [integerProgrammingStructuredTupleOfInput_encode])

theorem intRowStructuredToBinary_tm_polytime :
    TMPolyTimeMap intRowStructuredEncodedType intRowBinaryStructuredEncodedType id := by
  have hMap := TMPolyTimeMap.list_map Knapsack.unaryIntToBinaryInt_tm_polytime
  convert hMap using 1
  funext row
  exact (List.map_id row).symm

theorem constraintStructuredToBinary_tm_polytime :
    TMPolyTimeMap constraintStructuredEncodedType constraintBinaryStructuredEncodedType id := by
  let X := constraintStructuredEncodedType
  have hRow : TMPolyTimeMap X intRowBinaryStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    have hFst :
        TMPolyTimeMap X intRowStructuredEncodedType
          (fun p : X.Carrier => p.1) := by
      simpa [X, constraintStructuredEncodedType] using
        TMPolyTimeMap.fst intRowStructuredEncodedType EncodedType.int
    have hComp := TMPolyTimeMap.comp intRowStructuredToBinary_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hBound : TMPolyTimeMap X EncodedType.binaryInt
      (fun p : X.Carrier => p.2) := by
    have hSnd : TMPolyTimeMap X EncodedType.int
        (fun p : X.Carrier => p.2) := by
      simpa [X, constraintStructuredEncodedType] using
        TMPolyTimeMap.snd intRowStructuredEncodedType EncodedType.int
    have hComp := TMPolyTimeMap.comp Knapsack.unaryIntToBinaryInt_tm_polytime hSnd
    simpa [Function.comp, X] using hComp
  have hPair : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hRow hBound
  simpa [X, constraintBinaryStructuredEncodedType, Prod.eta] using hPair

theorem constraintListStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      constraintListStructuredEncodedType
      constraintListBinaryStructuredEncodedType
      id := by
  have hMap := TMPolyTimeMap.list_map constraintStructuredToBinary_tm_polytime
  convert hMap using 1
  funext constraints
  exact (List.map_id constraints).symm

theorem integerProgrammingTupleStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      integerProgrammingTupleStructuredEncodedType
      integerProgrammingTupleBinaryStructuredEncodedType
      id := by
  let X := integerProgrammingTupleStructuredEncodedType
  have hNum : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1) := by
    have hFst : TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier => p.1) := by
      simpa [X, integerProgrammingTupleStructuredEncodedType] using
        TMPolyTimeMap.fst EncodedType.nat constraintListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp Knapsack.unaryNatToBinaryNat_tm_polytime hFst
    simpa [Function.comp, X] using hComp
  have hConstraints : TMPolyTimeMap X constraintListBinaryStructuredEncodedType
      (fun p : X.Carrier => p.2) := by
    have hSnd : TMPolyTimeMap X constraintListStructuredEncodedType
        (fun p : X.Carrier => p.2) := by
      simpa [X, integerProgrammingTupleStructuredEncodedType] using
        TMPolyTimeMap.snd EncodedType.nat constraintListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp constraintListStructuredToBinary_tm_polytime hSnd
    simpa [Function.comp, X] using hComp
  have hPair : TMPolyTimeMap X integerProgrammingTupleBinaryStructuredEncodedType
      (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hNum hConstraints
  simpa [X, integerProgrammingTupleBinaryStructuredEncodedType, Prod.eta] using hPair

theorem integerProgrammingStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      integerProgrammingStructuredEncodedType
      integerProgrammingBinaryStructuredEncodedType
      id := by
  have hTupleFrom :=
    integerProgrammingStructuredTupleOfInputTMBackedMap.tm_polytime
  have hTuple :
      TMPolyTimeMap
        integerProgrammingStructuredEncodedType
        integerProgrammingTupleBinaryStructuredEncodedType
        integerProgrammingStructuredTupleOfInput := by
    have hComp :=
      TMPolyTimeMap.comp integerProgrammingTupleStructuredToBinary_tm_polytime hTupleFrom
    simpa [Function.comp] using hComp
  have hOut :=
    TMPolyTimeMap.comp
      Knapsack.integerProgrammingBinaryTupleToInputTMBackedMap.tm_polytime
      hTuple
  convert hOut using 1

noncomputable def zeroOneIPStructuredToBinaryStructuredTMKarpReduction :
    TMKarpReduction
      zeroOneIntegerProgrammingStructuredDecisionProblem
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem where
  f := id
  polytime := integerProgrammingStructuredToBinary_tm_polytime
  correct := by
    intro I
    rfl

end ZeroOneIP
end Karp21
end ComplexityReduction
