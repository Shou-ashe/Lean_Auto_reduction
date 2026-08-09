/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.SymbolList
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSAT
import Mathlib.Tactic

/-!
Direct TM2 encoder from faithful structured 3SAT syntax to the historical
bundled 3SAT string encoding.

The map is semantically the identity on `SAT.ThreeCNF`; the work here is only
the finite-alphabet encoder direction.  The standard bundled encoding writes
each literal as `(neg, var)`, while the faithful structured encoding stores a
literal as `(var, neg)`.  We build the output by direct raw symbol-list
transductions and typed list folds, avoiding any size-only soundness boundary.
-/

namespace ComplexityReduction
namespace SAT

namespace ThreeSATStructuredEncoder

abbrev StdSymbols : EncodedType :=
  symbolListEncodedType ThreeSATSymbol

def symbolListAppendKeep {α : Type} : Option (α ⊕ α) → Option α
  | some (Sum.inl a) => some a
  | some (Sum.inr a) => some a
  | none => none

theorem symbolList_append_tm_polytime (α : Type) [Fintype α] :
    TMPolyTimeMap
      (EncodedType.prod (symbolListEncodedType α) (symbolListEncodedType α))
      (symbolListEncodedType α)
      (fun p : List α × List α => p.1 ++ p.2) :=
  TMPolyTimeMap.symbol_filterMap
    (EncodedType.prod (symbolListEncodedType α) (symbolListEncodedType α))
    (symbolListEncodedType α)
    (fun p : List α × List α => p.1 ++ p.2)
    symbolListAppendKeep
    (by
      intro p
      cases p with
      | mk xs ys =>
          simp [EncodedType.prod, symbolListEncodedType, symbolListAppendKeep])

theorem symbolList_append_maps {X : EncodedType} {α : Type} [Fintype α]
    {f g : X.Carrier → List α}
    (hf : TMPolyTimeMap X (symbolListEncodedType α) f)
    (hg : TMPolyTimeMap X (symbolListEncodedType α) g) :
    TMPolyTimeMap X (symbolListEncodedType α) (fun x => f x ++ g x) := by
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod (symbolListEncodedType α) (symbolListEncodedType α))
        (fun x => (f x, g x)) :=
    TMPolyTimeMap.prod_mk hf hg
  have hAppend := symbolList_append_tm_polytime α
  have hComp := TMPolyTimeMap.comp hAppend hPair
  simpa [Function.comp] using hComp

def literalVarKeep : Karp21.literalStructuredEncodedType.Symbol → Option ThreeSATSymbol
  | some (Sum.inl b) => some (ThreeSATEncoding.bitToken b)
  | _ => none

def literalNegKeep : Karp21.literalStructuredEncodedType.Symbol → Option ThreeSATSymbol
  | some (Sum.inr b) => some (ThreeSATEncoding.bitToken b)
  | _ => none

set_option linter.unusedSimpArgs false in
theorem literalVarKeep_filterMap_eq (l : Literal) :
    (Karp21.literalStructuredEncodedType.encode l).filterMap literalVarKeep =
      ThreeSATEncoding.encodeNat l.var := by
  cases l with
  | mk var neg =>
      simp [Karp21.literalStructuredEncodedType, Karp21.literalTupleStructuredEncodedType,
        EncodedType.prod, EncodedType.nat, ThreeSATEncoding.encodeNat,
        ThreeSATEncoding.bitToken, literalVarKeep]

set_option linter.unusedSimpArgs false in
theorem literalNegKeep_filterMap_eq (l : Literal) :
    (Karp21.literalStructuredEncodedType.encode l).filterMap literalNegKeep =
      [ThreeSATEncoding.bitToken l.neg] := by
  cases l with
  | mk var neg =>
      cases neg <;>
        simp [Karp21.literalStructuredEncodedType, Karp21.literalTupleStructuredEncodedType,
          EncodedType.prod, EncodedType.nat, EncodedType.bool,
          ThreeSATEncoding.bitToken, literalNegKeep]

theorem literalVarSymbols_tm_polytime :
    TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
      (fun l : Literal => ThreeSATEncoding.encodeNat l.var) :=
  TMPolyTimeMap.symbol_filterMap
    Karp21.literalStructuredEncodedType StdSymbols
    (fun l : Literal => ThreeSATEncoding.encodeNat l.var)
    literalVarKeep
    (fun l => by
      simpa [StdSymbols] using (literalVarKeep_filterMap_eq l).symm)

theorem literalNegSymbol_tm_polytime :
    TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
      (fun l : Literal => [ThreeSATEncoding.bitToken l.neg]) :=
  TMPolyTimeMap.symbol_filterMap
    Karp21.literalStructuredEncodedType StdSymbols
    (fun l : Literal => [ThreeSATEncoding.bitToken l.neg])
    literalNegKeep
    (fun l => by
      simpa [StdSymbols] using (literalNegKeep_filterMap_eq l).symm)

theorem encodeLiteral_tm_polytime :
    TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
      ThreeSATEncoding.encodeLiteral := by
  let pre : List ThreeSATSymbol :=
    [ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken false]
  let mid : List ThreeSATSymbol :=
    [ThreeSATEncoding.delimiter, ThreeSATEncoding.tagToken true]
  have hPre :
      TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols (fun _ : Literal => pre) :=
    TMPolyTimeMap.const Karp21.literalStructuredEncodedType StdSymbols pre
  have hPreNeg :
      TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
        (fun l : Literal => pre ++ [ThreeSATEncoding.bitToken l.neg]) :=
    symbolList_append_maps hPre literalNegSymbol_tm_polytime
  have hMid :
      TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols (fun _ : Literal => mid) :=
    TMPolyTimeMap.const Karp21.literalStructuredEncodedType StdSymbols mid
  have hPreNegMid :
      TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
        (fun l : Literal => pre ++ [ThreeSATEncoding.bitToken l.neg] ++ mid) :=
    symbolList_append_maps hPreNeg hMid
  have hAll :
      TMPolyTimeMap Karp21.literalStructuredEncodedType StdSymbols
        (fun l : Literal =>
          pre ++ [ThreeSATEncoding.bitToken l.neg] ++ mid ++
            ThreeSATEncoding.encodeNat l.var) :=
    symbolList_append_maps hPreNegMid literalVarSymbols_tm_polytime
  simpa [ThreeSATEncoding.encodeLiteral, pre, mid, List.append_assoc] using hAll

def clauseFoldStep (p : List ThreeSATSymbol × Literal) : List ThreeSATSymbol :=
  p.1 ++ ThreeSATEncoding.encodeLiteral p.2

theorem clauseFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod StdSymbols Karp21.literalStructuredEncodedType)
      StdSymbols
      clauseFoldStep := by
  have hAcc :
      TMPolyTimeMap
        (EncodedType.prod StdSymbols Karp21.literalStructuredEncodedType)
        StdSymbols
        (fun p : List ThreeSATSymbol × Literal => p.1) :=
    TMPolyTimeMap.fst StdSymbols Karp21.literalStructuredEncodedType
  have hLitInput :
      TMPolyTimeMap
        (EncodedType.prod StdSymbols Karp21.literalStructuredEncodedType)
        Karp21.literalStructuredEncodedType
        (fun p : List ThreeSATSymbol × Literal => p.2) :=
    TMPolyTimeMap.snd StdSymbols Karp21.literalStructuredEncodedType
  have hLit := TMPolyTimeMap.comp encodeLiteral_tm_polytime hLitInput
  have hAppend := symbolList_append_maps hAcc hLit
  simpa [clauseFoldStep, Function.comp] using hAppend

theorem foldl_clauseFoldStep_eq (pref : List ThreeSATSymbol) (c : Clause) :
    c.foldl (fun acc l => clauseFoldStep (acc, l)) pref =
      pref ++ c.flatMap ThreeSATEncoding.encodeLiteral := by
  induction c generalizing pref with
  | nil =>
      simp [clauseFoldStep]
  | cons l rest ih =>
      calc
        (l :: rest).foldl (fun acc l => clauseFoldStep (acc, l)) pref
            = rest.foldl (fun acc l => clauseFoldStep (acc, l))
                (pref ++ ThreeSATEncoding.encodeLiteral l) := by
              rfl
        _ = (pref ++ ThreeSATEncoding.encodeLiteral l) ++
              rest.flatMap ThreeSATEncoding.encodeLiteral :=
              ih _
        _ = pref ++ (l :: rest).flatMap ThreeSATEncoding.encodeLiteral := by
              simp [List.append_assoc]

theorem encodeLiteral_length_le_inputSize_add_three (l : Literal) :
    (ThreeSATEncoding.encodeLiteral l).length ≤
      Karp21.literalStructuredEncodedType.inputSize l + 3 := by
  cases l with
  | mk var neg =>
      simp [ThreeSATEncoding.encodeLiteral, ThreeSATEncoding.encodeNat,
        Karp21.literalStructuredEncodedType, Karp21.literalTupleStructuredEncodedType,
        EncodedType.inputSize, EncodedType.prod, EncodedType.nat, EncodedType.bool]

theorem encodeLiteral_length_le_four_inputSize_succ (l : Literal) :
    (ThreeSATEncoding.encodeLiteral l).length ≤
      4 * (Karp21.literalStructuredEncodedType.inputSize l + 1) := by
  have h := encodeLiteral_length_le_inputSize_add_three l
  omega

theorem encodeClause_tm_polytime :
    TMPolyTimeMap Karp21.clauseStructuredEncodedType StdSymbols
      ThreeSATEncoding.encodeClause := by
  rcases clauseFoldStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap (EncodedType.list Karp21.literalStructuredEncodedType) StdSymbols
        (fun c : Clause =>
          c.foldl (fun acc l => clauseFoldStep (acc, l)) [ThreeSATEncoding.delimiter]) :=
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      Karp21.literalStructuredEncodedType StdSymbols clauseFoldStep
      [ThreeSATEncoding.delimiter] hStep
      (Polynomial.C 1) (Polynomial.X + Polynomial.C 3)
      (by
        intro c
        simp [symbolListEncodedType, EncodedType.inputSize])
      (by
        intro source acc l hl
        have hLit := encodeLiteral_length_le_inputSize_add_three l
        simp [symbolListEncodedType, clauseFoldStep, EncodedType.inputSize,
          Polynomial.eval_add, Polynomial.eval_X] at hLit hl ⊢
        omega)
  change
    TMPolyTimeMap (EncodedType.list Karp21.literalStructuredEncodedType) StdSymbols
      (fun c : Clause => [ThreeSATEncoding.delimiter] ++
        c.flatMap ThreeSATEncoding.encodeLiteral)
  convert hFold using 1
  funext c
  exact (foldl_clauseFoldStep_eq [ThreeSATEncoding.delimiter] c).symm

def cnfFoldStep (p : List ThreeSATSymbol × Clause) : List ThreeSATSymbol :=
  p.1 ++ ThreeSATEncoding.encodeClause p.2

theorem cnfFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod StdSymbols Karp21.clauseStructuredEncodedType)
      StdSymbols
      cnfFoldStep := by
  have hAcc :
      TMPolyTimeMap
        (EncodedType.prod StdSymbols Karp21.clauseStructuredEncodedType)
        StdSymbols
        (fun p : List ThreeSATSymbol × Clause => p.1) :=
    TMPolyTimeMap.fst StdSymbols Karp21.clauseStructuredEncodedType
  have hClauseInput :
      TMPolyTimeMap
        (EncodedType.prod StdSymbols Karp21.clauseStructuredEncodedType)
        Karp21.clauseStructuredEncodedType
        (fun p : List ThreeSATSymbol × Clause => p.2) :=
    TMPolyTimeMap.snd StdSymbols Karp21.clauseStructuredEncodedType
  have hClause := TMPolyTimeMap.comp encodeClause_tm_polytime hClauseInput
  have hAppend := symbolList_append_maps hAcc hClause
  simpa [cnfFoldStep, Function.comp] using hAppend

theorem foldl_cnfFoldStep_eq (pref : List ThreeSATSymbol) (φ : CNF) :
    φ.foldl (fun acc c => cnfFoldStep (acc, c)) pref =
      pref ++ φ.flatMap ThreeSATEncoding.encodeClause := by
  induction φ generalizing pref with
  | nil =>
      simp [cnfFoldStep]
  | cons c rest ih =>
      calc
        (c :: rest).foldl (fun acc c => cnfFoldStep (acc, c)) pref
            = rest.foldl (fun acc c => cnfFoldStep (acc, c))
                (pref ++ ThreeSATEncoding.encodeClause c) := by
              rfl
        _ = (pref ++ ThreeSATEncoding.encodeClause c) ++
              rest.flatMap ThreeSATEncoding.encodeClause :=
              ih _
        _ = pref ++ (c :: rest).flatMap ThreeSATEncoding.encodeClause := by
              simp [List.append_assoc]

theorem flatMap_encodeLiteral_length_le_four_inputSize (c : Clause) :
    (c.flatMap ThreeSATEncoding.encodeLiteral).length ≤
      4 * Karp21.clauseStructuredEncodedType.inputSize c := by
  induction c with
  | nil =>
      simp [Karp21.clauseStructuredEncodedType, EncodedType.inputSize, EncodedType.list]
  | cons l rest ih =>
      have hLit := encodeLiteral_length_le_four_inputSize_succ l
      have hRest :
          (rest.flatMap ThreeSATEncoding.encodeLiteral).length ≤
            4 * (EncodedType.list Karp21.literalStructuredEncodedType).inputSize rest := by
        simpa [Karp21.clauseStructuredEncodedType] using ih
      change
        (ThreeSATEncoding.encodeLiteral l ++
            rest.flatMap ThreeSATEncoding.encodeLiteral).length ≤
          4 * (EncodedType.list Karp21.literalStructuredEncodedType).inputSize (l :: rest)
      rw [EncodedType.inputSize_list_cons]
      simp only [List.length_append]
      nlinarith

theorem encodeClause_length_le_four_inputSize_add_one (c : Clause) :
    (ThreeSATEncoding.encodeClause c).length ≤
      4 * Karp21.clauseStructuredEncodedType.inputSize c + 1 := by
  have h := flatMap_encodeLiteral_length_le_four_inputSize c
  calc
    (ThreeSATEncoding.encodeClause c).length =
        1 + (c.flatMap ThreeSATEncoding.encodeLiteral).length := by
          simp [ThreeSATEncoding.encodeClause, Nat.add_comm]
    _ ≤ 1 + 4 * Karp21.clauseStructuredEncodedType.inputSize c :=
          Nat.add_le_add_left h 1
    _ = 4 * Karp21.clauseStructuredEncodedType.inputSize c + 1 := by
          omega

theorem cnfToStandardSymbols_tm_polytime :
    TMPolyTimeMap Karp21.cnfStructuredEncodedType StdSymbols
      (fun φ : CNF => φ.flatMap ThreeSATEncoding.encodeClause) := by
  rcases cnfFoldStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap (EncodedType.list Karp21.clauseStructuredEncodedType) StdSymbols
        (fun φ : CNF => φ.foldl (fun acc c => cnfFoldStep (acc, c)) []) :=
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      Karp21.clauseStructuredEncodedType StdSymbols cnfFoldStep [] hStep
      (Polynomial.C 0) (4 * Polynomial.X + Polynomial.C 1)
      (by
        intro φ
        simp [symbolListEncodedType, EncodedType.inputSize])
      (by
        intro source acc c hc
        have hClause := encodeClause_length_le_four_inputSize_add_one c
        simp [symbolListEncodedType, cnfFoldStep, EncodedType.inputSize,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at hClause hc ⊢
        nlinarith)
  change
    TMPolyTimeMap (EncodedType.list Karp21.clauseStructuredEncodedType) StdSymbols
      (fun φ : CNF => φ.flatMap ThreeSATEncoding.encodeClause)
  convert hFold using 1
  funext φ
  simpa using (foldl_cnfFoldStep_eq [] φ).symm

theorem threeCNFStructured_clauses_tm_polytime :
    TMPolyTimeMap Karp21.threeCNFStructuredEncodedType Karp21.cnfStructuredEncodedType
      (fun φ : ThreeCNF => φ.clauses) :=
  TMPolyTimeMap.of_encodingEquiv
    Karp21.threeCNFStructuredEncodedType Karp21.cnfStructuredEncodedType
    (fun φ : ThreeCNF => φ.clauses)
    (Equiv.refl _)
    (by
      intro φ
      change Karp21.cnfStructuredEncodedType.encode φ.clauses =
        (Karp21.cnfStructuredEncodedType.encode φ.clauses).map id
      rw [List.map_id])

theorem threeCNFStructuredToStandardSymbols_tm_polytime :
    TMPolyTimeMap Karp21.threeCNFStructuredEncodedType StdSymbols
      (fun φ : ThreeCNF => ThreeSATEncoding.encodeThreeCNF φ) := by
  have hComp :=
    TMPolyTimeMap.comp cnfToStandardSymbols_tm_polytime
      threeCNFStructured_clauses_tm_polytime
  simpa [Function.comp, ThreeSATEncoding.encodeThreeCNF] using hComp

/--
The identity map from faithful structured 3CNF syntax to the historical bundled
3SAT carrier is direct TM2 polynomial-time.
-/
theorem threeCNFStructuredToStandard_tm_polytime :
    TMPolyTimeMap
      Karp21.threeSATStructuredDecisionProblem.Instance
      threeSATDecisionProblem.Instance
      (fun φ : ThreeCNF => φ) := by
  rcases threeCNFStructuredToStandardSymbols_tm_polytime with ⟨hRaw⟩
  exact
    ⟨{ tm := hRaw.tm
       inputAlphabet := hRaw.inputAlphabet
       outputAlphabet := hRaw.outputAlphabet
       time := hRaw.time
       outputsFun := by
        intro φ
        exact hRaw.outputsFun φ }⟩

end ThreeSATStructuredEncoder

export ThreeSATStructuredEncoder (threeCNFStructuredToStandard_tm_polytime)

end SAT
end ComplexityReduction
