import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.FiniteLookup
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.RawToEncodedList

namespace ComplexityReduction

/-!
Direct-TM helpers for finite symbol streams encoded as themselves.

`EncodedType.list` is delimiter-based and is the right encoding for ordinary
typed lists.  Some Cook-Levin boundary generators, however, must scan the raw
encoding stream of an input object.  `symbolListEncodedType` records such a
stream without adding delimiters.
-/

def symbolListEncodedType (α : Type) [Fintype α] : EncodedType where
  Carrier := List α
  Symbol := α
  finite_symbol := inferInstance
  encode := fun xs => xs

def finiteSymbolEncodedType (α : Type) [Fintype α] : EncodedType where
  Carrier := α
  Symbol := α
  finite_symbol := inferInstance
  encode := fun a => [a]

@[simp]
theorem symbolListEncodedType_encode {α : Type} [Fintype α] (xs : List α) :
    (symbolListEncodedType α).encode xs = xs := rfl

@[simp]
theorem symbolListEncodedType_inputSize {α : Type} [Fintype α] (xs : List α) :
    (symbolListEncodedType α).inputSize xs = xs.length := rfl

@[simp]
theorem finiteSymbolEncodedType_encode {α : Type} [Fintype α] (a : α) :
    (finiteSymbolEncodedType α).encode a = [a] := rfl

@[simp]
theorem finiteSymbolEncodedType_inputSize {α : Type} [Fintype α] (a : α) :
    (finiteSymbolEncodedType α).inputSize a = 1 := rfl

theorem finiteSymbol_map_tm_polytime (α : Type) [Fintype α]
    (Y : EncodedType) (f : α → Y.Carrier) :
    TMPolyTimeMap (finiteSymbolEncodedType α) Y f :=
  ⟨TM2Programs.finiteSymbolComputableInPolyTime α Y f⟩

theorem finiteSymbolList_encode_eq_rawToEncodedListOutput {α : Type} [Fintype α]
    (xs : List α) :
    (EncodedType.list (finiteSymbolEncodedType α)).encode xs =
      TM2Programs.rawToEncodedListOutput xs := by
  change xs.flatMap (fun x : α => [some x, none]) =
    xs.flatMap TM2Programs.rawToEncodedListBlock
  induction xs with
  | nil =>
      rfl
  | cons a xs ih =>
      simp [TM2Programs.rawToEncodedListBlock, ih]

@[simp]
theorem list_map_equivRefl_symm {α : Type} (xs : List α) :
    xs.map (Equiv.refl α).symm = xs := by
  simp

theorem rawSymbols_to_finiteSymbolList_tm_polytime (α : Type) [Fintype α] :
    TMPolyTimeMap
      (symbolListEncodedType α)
      (EncodedType.list (finiteSymbolEncodedType α))
      (fun xs : List α => xs) :=
  ⟨{ tm := TM2Programs.rawToEncodedListMachine α
     inputAlphabet := Equiv.refl α
     outputAlphabet := Equiv.refl (Option α)
     time := 7 * Polynomial.X + 2
     outputsFun := by
      intro xs
      have hRaw := TM2Programs.rawToEncodedList_outputs α xs
      convert hRaw using 1
      · change List.map id xs = xs
        exact List.map_id xs
      · apply congrArg some
        change List.map id ((EncodedType.list (finiteSymbolEncodedType α)).encode xs) =
          TM2Programs.rawToEncodedListOutput xs
        rw [List.map_id]
        exact finiteSymbolList_encode_eq_rawToEncodedListOutput xs
      · simp [symbolListEncodedType, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X] }⟩

theorem encodedSymbols_map_tm_polytime (X : EncodedType) (β : Type) [Fintype β]
    (mapSym : X.Symbol → β) :
    TMPolyTimeMap X (symbolListEncodedType β)
      (fun x : X.Carrier => (X.encode x).map mapSym) :=
  TMPolyTimeMap.symbol_filterMap X (symbolListEncodedType β)
    (fun x : X.Carrier => (X.encode x).map mapSym)
    (fun s => some (mapSym s))
    (by
      intro x
      change (X.encode x).map mapSym =
        (X.encode x).filterMap (fun s => some (mapSym s))
      induction X.encode x with
      | nil => rfl
      | cons s rest ih =>
          change mapSym s :: rest.map mapSym =
            mapSym s :: rest.filterMap (fun s => some (mapSym s))
          exact congrArg (fun ys => mapSym s :: ys) ih)

theorem encodedSymbols_suffixMap_tm_polytime (X : EncodedType) (β : Type) [Fintype β]
    (mapSym : X.Symbol → β) (suffix : β) :
    TMPolyTimeMap X (symbolListEncodedType β)
      (fun x : X.Carrier => (X.encode x).map mapSym ++ [suffix]) := by
  refine ⟨?_⟩
  exact
    { tm := TM2Programs.suffixMapMachine X.Symbol β suffix mapSym
      inputAlphabet := Equiv.refl X.Symbol
      outputAlphabet := Equiv.refl β
      time := 4 * Polynomial.X + 3
      outputsFun := by
        intro x
        convert
          TM2Programs.suffixMap_outputs X.Symbol β suffix mapSym (X.encode x) using 1
        · change List.map id (X.encode x) = X.encode x
          exact List.map_id (X.encode x)
        · apply congrArg some
          change List.map id ((X.encode x).map mapSym ++ [suffix]) =
            (X.encode x).map mapSym ++ [suffix]
          exact List.map_id ((X.encode x).map mapSym ++ [suffix])
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }

end ComplexityReduction
