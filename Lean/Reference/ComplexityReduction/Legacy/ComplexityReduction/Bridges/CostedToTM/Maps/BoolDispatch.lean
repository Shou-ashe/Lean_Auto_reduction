import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum

namespace ComplexityReduction

open Turing.TM2.Stmt

/-!
Shared direct-TM branch dispatch for a Boolean tag and one payload encoding.

This bridge-level copy lets Cook-Levin generator files use Boolean dispatch
without importing any Karp21 target module.
-/

def boolPayloadEncodedType (X : EncodedType) : EncodedType where
  Carrier := Bool × X.Carrier
  Symbol := Bool ⊕ X.Symbol
  finite_symbol := inferInstance
  encode := fun p => Sum.inl p.1 :: (X.encode p.2).map Sum.inr

def boolPayloadAsSum (X : EncodedType) (p : (boolPayloadEncodedType X).Carrier) :
    X.Carrier ⊕ X.Carrier :=
  if p.1 then Sum.inr p.2 else Sum.inl p.2

theorem boolPayloadEncodedType_encode_eq_sum (X : EncodedType)
    (p : (boolPayloadEncodedType X).Carrier) :
    (boolPayloadEncodedType X).encode p =
      match boolPayloadAsSum X p with
      | Sum.inl x => Sum.inl false :: (X.encode x).map Sum.inr
      | Sum.inr x => Sum.inl true :: (X.encode x).map Sum.inr := by
  rcases p with ⟨b, x⟩
  cases b <;> rfl

def boolPayloadFromProductKeep (X : EncodedType) :
    (EncodedType.prod EncodedType.bool X).Symbol → Option (boolPayloadEncodedType X).Symbol
  | some (Sum.inl b) => some (Sum.inl b)
  | some (Sum.inr s) => some (Sum.inr s)
  | none => none

theorem boolPayloadFromProduct_encode_filterMap (X : EncodedType)
    (p : (EncodedType.prod EncodedType.bool X).Carrier) :
    (boolPayloadEncodedType X).encode p =
      ((EncodedType.prod EncodedType.bool X).encode p).filterMap
        (boolPayloadFromProductKeep X) := by
  rcases p with ⟨b, x⟩
  simp [boolPayloadEncodedType, EncodedType.prod, EncodedType.bool,
    boolPayloadFromProductKeep]

theorem boolPayloadFromProduct_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool X)
      (boolPayloadEncodedType X)
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p) :=
  TMPolyTimeMap.symbol_filterMap
    (EncodedType.prod EncodedType.bool X)
    (boolPayloadEncodedType X)
    (fun p : (EncodedType.prod EncodedType.bool X).Carrier => p)
    (boolPayloadFromProductKeep X)
    (by
      intro p
      exact boolPayloadFromProduct_encode_filterMap X p)

theorem boolPayload_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (boolPayloadEncodedType X)
      Y
      (fun p : (boolPayloadEncodedType X).Carrier =>
        if p.1 then fTrue p.2 else fFalse p.2) := by
  rcases hFalse with ⟨hFalse⟩
  rcases hTrue with ⟨hTrue⟩
  let hSum := taggedBranchDispatchComputableInPolyTime hFalse hTrue
  refine ⟨?_⟩
  exact
    { tm := hSum.tm
      inputAlphabet := hSum.inputAlphabet
      outputAlphabet := hSum.outputAlphabet
      time := hSum.time
      outputsFun := by
        intro p
        rcases p with ⟨b, x⟩
        cases b
        · simpa [boolPayloadEncodedType, boolPayloadAsSum] using hSum.outputsFun (Sum.inl x)
        · simpa [boolPayloadEncodedType, boolPayloadAsSum] using hSum.outputsFun (Sum.inr x) }

theorem boolProduct_dispatch_tm_polytime
    (X Y : EncodedType) {fFalse fTrue : X.Carrier → Y.Carrier}
    (hFalse : TMPolyTimeMap X Y fFalse) (hTrue : TMPolyTimeMap X Y fTrue) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool X)
      Y
      (fun p : (EncodedType.prod EncodedType.bool X).Carrier =>
        match p.1 with
        | true => fTrue p.2
        | false => fFalse p.2) := by
  have hBranch :=
    boolPayload_dispatch_tm_polytime X Y (fFalse := fFalse) (fTrue := fTrue) hFalse hTrue
  have hTagged := boolPayloadFromProduct_tm_polytime X
  have hComp := TMPolyTimeMap.comp hBranch hTagged
  convert hComp using 1
  ext p
  rcases p with ⟨b, x⟩
  cases b <;> rfl

end ComplexityReduction
