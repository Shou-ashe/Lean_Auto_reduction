import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.Base

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

/-!
Direct TM-facing components for the structured 3SAT-to-0-1-IP textbook route.

The semantic map is defined in `ZeroOneIP.Base`; this module adds checked
finite-alphabet construction witnesses without using the legacy costed-only
closure as a TM soundness shortcut.
-/

def literalCoeffAtInputEncodedType : EncodedType :=
  EncodedType.prod literalStructuredEncodedType EncodedType.nat

def literalCoeffAtEqBool (p : SAT.Literal × Nat) : Bool :=
  decide (p.2 = p.1.var)

theorem literalCoeffAt_tm_polytime :
    TMPolyTimeMap
      literalCoeffAtInputEncodedType
      EncodedType.int
      (fun p : SAT.Literal × Nat => literalCoeffAt p.1 p.2) := by
  let X := literalCoeffAtInputEncodedType
  have hLit : TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, literalCoeffAtInputEncodedType] using
      TMPolyTimeMap.fst literalStructuredEncodedType EncodedType.nat
  have hI : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, literalCoeffAtInputEncodedType] using
      TMPolyTimeMap.snd literalStructuredEncodedType EncodedType.nat
  have hVar : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.var) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_var_tm_polytime hLit
    simpa [Function.comp, X] using hComp
  have hEqInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.2, p.1.var)) :=
    TMPolyTimeMap.prod_mk hI hVar
  have hEq : TMPolyTimeMap X EncodedType.bool
      literalCoeffAtEqBool := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hEqInput
    simpa [Function.comp, literalCoeffAtEqBool] using hComp
  have hNeg : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.neg) := by
    have hComp := TMPolyTimeMap.comp Clique.literal_neg_tm_polytime hLit
    simpa [Function.comp, X] using hComp
  have hNegTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.1.neg, p)) :=
    TMPolyTimeMap.prod_mk hNeg (TMPolyTimeMap.id X)
  have hSign :
      TMPolyTimeMap X EncodedType.int
        (fun p : X.Carrier =>
          match p.1.neg with
          | true => (1 : Int)
          | false => (-1 : Int)) := by
    have hFalse :
        TMPolyTimeMap X EncodedType.int (fun _ : X.Carrier => (-1 : Int)) :=
      TMPolyTimeMap.const X EncodedType.int (-1 : Int)
    have hTrue :
        TMPolyTimeMap X EncodedType.int (fun _ : X.Carrier => (1 : Int)) :=
      TMPolyTimeMap.const X EncodedType.int (1 : Int)
    have hDispatch :=
      Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
        (fFalse := fun _ : X.Carrier => (-1 : Int))
        (fTrue := fun _ : X.Carrier => (1 : Int))
        hFalse hTrue
    have hComp := TMPolyTimeMap.comp hDispatch hNegTagged
    simpa [Function.comp] using hComp
  have hEqTagged :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (literalCoeffAtEqBool p, p)) :=
    TMPolyTimeMap.prod_mk hEq (TMPolyTimeMap.id X)
  have hZero :
      TMPolyTimeMap X EncodedType.int (fun _ : X.Carrier => (0 : Int)) :=
    TMPolyTimeMap.const X EncodedType.int (0 : Int)
  have hDispatch :=
    Clique.boolProduct_dispatch_tm_polytime X EncodedType.int
      (fFalse := fun _ : X.Carrier => (0 : Int))
      (fTrue := fun p : X.Carrier =>
        match p.1.neg with
        | true => (1 : Int)
        | false => (-1 : Int))
      hZero hSign
  have hComp := TMPolyTimeMap.comp hDispatch hEqTagged
  convert hComp using 1
  funext p
  rcases p with ⟨l, i⟩
  cases l with
  | mk var neg =>
      by_cases h : i = var <;> cases neg <;>
        simp [Function.comp, literalCoeffAt, literalCoeffAtEqBool, h]

end ZeroOneIP
end Karp21
end ComplexityReduction
