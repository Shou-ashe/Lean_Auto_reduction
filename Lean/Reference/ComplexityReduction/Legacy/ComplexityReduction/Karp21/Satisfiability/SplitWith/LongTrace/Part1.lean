/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.ListUncons

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/-- Payload for the recursive tail-clause writer in the long-clause splitter. -/
def splitWithLongTailCoreEncodedType : EncodedType :=
  EncodedType.prod literalStructuredEncodedType
    (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)

/-- Four-literal payload parsed from a long clause, without the fresh-counter prefix. -/
def splitWithLongClausePayloadEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    splitWithLongTailCoreEncodedType

/-- Repeated typed uncons payload parser for clauses of length at least four. -/
def splitWithLongClausePayload
    (c : (clauseMinLengthEncodedType 4).Carrier) :
    splitWithLongClausePayloadEncodedType.Carrier :=
  let first := clauseMinLengthUncons 3 c
  let second := clauseMinLengthUncons 2 first.2
  let third := clauseMinLengthUncons 1 second.2
  let fourth := clauseMinLengthUncons 0 third.2
  ((first.1, second.1), (third.1, (fourth.1, fourth.2.1)))

theorem splitWithLongClausePayload_cons
    (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause)
    (h : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length) :
    splitWithLongClausePayload ⟨l₁ :: l₂ :: l₃ :: l₄ :: rest, h⟩ =
      ((l₁, l₂), (l₃, (l₄, rest))) := by
  simp [splitWithLongClausePayload, clauseMinLengthUncons]
  rfl

/--
The four-literal long-clause payload parser is direct TM-backed by four typed
delimiter-list uncons calls plus structural product/projection closures.
-/
noncomputable def splitWithLongClausePayloadTMBackedMap :
    TMBackedCostedMap
      (clauseMinLengthEncodedType 4)
      splitWithLongClausePayloadEncodedType
      splitWithLongClausePayload where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := clauseMinLengthEncodedType 4)
      (Y := splitWithLongClausePayloadEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro c
        rcases c with ⟨c, hc⟩
        cases c with
        | nil =>
            simp at hc
        | cons l₁ c₁ =>
            cases c₁ with
            | nil =>
                simp at hc
            | cons l₂ c₂ =>
                cases c₂ with
                | nil =>
                    simp at hc
                | cons l₃ c₃ =>
                    cases c₃ with
                    | nil =>
                        simp at hc
                    | cons l₄ rest =>
                        rw [splitWithLongClausePayload_cons l₁ l₂ l₃ l₄ rest hc]
                        have hInput :
                            (clauseMinLengthEncodedType 4).inputSize
                                ⟨l₁ :: l₂ :: l₃ :: l₄ :: rest, hc⟩ =
                              clauseStructuredEncodedType.inputSize
                                (l₁ :: l₂ :: l₃ :: l₄ :: rest) := rfl
                        rw [hInput, one_mul, add_zero]
                        change
                          splitWithLongClausePayloadEncodedType.inputSize
                              ((l₁, l₂), (l₃, (l₄, rest))) ≤
                            clauseStructuredEncodedType.inputSize
                              (l₁ :: l₂ :: l₃ :: l₄ :: rest)
                        simp [splitWithLongClausePayloadEncodedType,
                          splitWithLongTailCoreEncodedType, clauseStructuredEncodedType]
                        omega))
  tm_polytime := by
    let X := clauseMinLengthEncodedType 4
    have hFirst :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType 3))
          (fun c : X.Carrier => clauseMinLengthUncons 3 c) :=
      (clauseMinLengthUnconsTMBackedMap 3).tm_polytime
    have hL₁ :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun c : X.Carrier => (clauseMinLengthUncons 3 c).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType (clauseMinLengthEncodedType 3))
        hFirst
    have hTail₃ :
        TMPolyTimeMap X (clauseMinLengthEncodedType 3)
          (fun c : X.Carrier => (clauseMinLengthUncons 3 c).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType (clauseMinLengthEncodedType 3))
        hFirst
    have hSecond :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType 2))
          (fun c : X.Carrier => clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2) :=
      TMPolyTimeMap.comp (clauseMinLengthUnconsTMBackedMap 2).tm_polytime hTail₃
    have hL₂ :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun c : X.Carrier => (clauseMinLengthUncons 2
            (clauseMinLengthUncons 3 c).2).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType (clauseMinLengthEncodedType 2))
        hSecond
    have hTail₂ :
        TMPolyTimeMap X (clauseMinLengthEncodedType 2)
          (fun c : X.Carrier => (clauseMinLengthUncons 2
            (clauseMinLengthUncons 3 c).2).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType (clauseMinLengthEncodedType 2))
        hSecond
    have hThird :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType 1))
          (fun c : X.Carrier => clauseMinLengthUncons 1
            (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2) :=
      TMPolyTimeMap.comp (clauseMinLengthUnconsTMBackedMap 1).tm_polytime hTail₂
    have hL₃ :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun c : X.Carrier => (clauseMinLengthUncons 1
            (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType (clauseMinLengthEncodedType 1))
        hThird
    have hTail₁ :
        TMPolyTimeMap X (clauseMinLengthEncodedType 1)
          (fun c : X.Carrier => (clauseMinLengthUncons 1
            (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType (clauseMinLengthEncodedType 1))
        hThird
    have hFourth :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType (clauseMinLengthEncodedType 0))
          (fun c : X.Carrier => clauseMinLengthUncons 0
            (clauseMinLengthUncons 1
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2) :=
      TMPolyTimeMap.comp (clauseMinLengthUnconsTMBackedMap 0).tm_polytime hTail₁
    have hL₄ :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun c : X.Carrier => (clauseMinLengthUncons 0
            (clauseMinLengthUncons 1
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType (clauseMinLengthEncodedType 0))
        hFourth
    have hRestSubtype :
        TMPolyTimeMap X (clauseMinLengthEncodedType 0)
          (fun c : X.Carrier => (clauseMinLengthUncons 0
            (clauseMinLengthUncons 1
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType (clauseMinLengthEncodedType 0))
        hFourth
    have hRest :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun c : X.Carrier => (clauseMinLengthUncons 0
            (clauseMinLengthUncons 1
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).2.1) :=
      TMPolyTimeMap.comp (clauseMinLengthForgetTMBackedMap 0).tm_polytime hRestSubtype
    have hL₁L₂ :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          (fun c : X.Carrier =>
            ((clauseMinLengthUncons 3 c).1,
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).1)) :=
      TMPolyTimeMap.prod_mk hL₁ hL₂
    have hL₄Rest :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun c : X.Carrier =>
            ((clauseMinLengthUncons 0
              (clauseMinLengthUncons 1
                (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).1,
              (clauseMinLengthUncons 0
                (clauseMinLengthUncons 1
                  (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).2.1)) :=
      TMPolyTimeMap.prod_mk hL₄ hRest
    have hTailCore :
        TMPolyTimeMap X splitWithLongTailCoreEncodedType
          (fun c : X.Carrier =>
            ((clauseMinLengthUncons 1
              (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).1,
              ((clauseMinLengthUncons 0
                (clauseMinLengthUncons 1
                  (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).1,
                (clauseMinLengthUncons 0
                  (clauseMinLengthUncons 1
                    (clauseMinLengthUncons 2 (clauseMinLengthUncons 3 c).2).2).2).2.1))) :=
      TMPolyTimeMap.prod_mk hL₃ hL₄Rest
    have hPayload :
        TMPolyTimeMap X splitWithLongClausePayloadEncodedType splitWithLongClausePayload :=
      TMPolyTimeMap.prod_mk hL₁L₂ hTailCore
    simpa [X, splitWithLongClausePayload, splitWithLongClausePayloadEncodedType,
      splitWithLongTailCoreEncodedType] using hPayload

/-- Input `(next, l₃, l₄, rest)` for building `¬y_next :: l₃ :: l₄ :: rest`. -/
def splitWithLongTailInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat splitWithLongTailCoreEncodedType

/-- Recursive tail clause for one long-clause splitter step. -/
def splitWithLongTailClause
    (p : splitWithLongTailInputEncodedType.Carrier) : SAT.Clause :=
  SAT.Clause.negAux p.1 :: p.2.1 :: p.2.2.1 :: p.2.2.2

/-- The recursive tail-clause writer is direct TM-backed under faithful encodings. -/
noncomputable def splitWithLongTailClauseTMBackedMap :
    TMBackedCostedMap
      splitWithLongTailInputEncodedType clauseStructuredEncodedType
      splitWithLongTailClause where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongTailInputEncodedType)
      (Y := clauseStructuredEncodedType)
      (LinearSizeBound.intro_with 1 10 (by
        intro p
        rcases p with ⟨next, core⟩
        rcases core with ⟨l₃, l₄Rest⟩
        rcases l₄Rest with ⟨l₄, rest⟩
        change
          (EncodedType.list literalStructuredEncodedType).inputSize
              (SAT.Clause.negAux next :: l₃ :: l₄ :: rest) ≤
            1 * (EncodedType.prod EncodedType.nat splitWithLongTailCoreEncodedType).inputSize
                (next, (l₃, (l₄, rest))) + 10
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_cons]
        simp [splitWithLongTailCoreEncodedType, clauseStructuredEncodedType,
          literalStructured_inputSize_eq, SAT.Clause.negAux]
        omega))
  tm_polytime := by
    let X := splitWithLongTailInputEncodedType
    have hNext :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst EncodedType.nat splitWithLongTailCoreEncodedType
    have hCore :
        TMPolyTimeMap X splitWithLongTailCoreEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd EncodedType.nat splitWithLongTailCoreEncodedType
    have hL₃ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType))
        hCore
    have hL₄Rest :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => p.2.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType))
        hCore
    have hL₄ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType clauseStructuredEncodedType)
        hL₄Rest
    have hRest :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.2.2.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType clauseStructuredEncodedType)
        hL₄Rest
    have hNeg :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun p : X.Carrier => SAT.Clause.negAux p.1) :=
      TMPolyTimeMap.comp negAuxTMBackedMap.tm_polytime hNext
    have hL₄RestClause :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => (p.2.2.1, p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hL₄ hRest
    have hAfterL₄ :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => p.2.2.1 :: p.2.2.2) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₄RestClause
    have hL₃RestClause :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => (p.2.1, p.2.2.1 :: p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hL₃ hAfterL₄
    have hAfterL₃ :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => p.2.1 :: p.2.2.1 :: p.2.2.2) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₃RestClause
    have hNegRestClause :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier =>
            (SAT.Clause.negAux p.1, p.2.1 :: p.2.2.1 :: p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hNeg hAfterL₃
    have hTail :
        TMPolyTimeMap X clauseStructuredEncodedType splitWithLongTailClause :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hNegRestClause
    simpa [X, splitWithLongTailClause, Function.comp] using hTail

/-- Payload `(next, l₁, l₂)` for the head clause of a long splitter step. -/
def splitWithLongHeadCoreEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)

/-- Decomposed long-clause input `(next, l₁, l₂, l₃, l₄, rest)`. -/
def splitWithLongDecomposedInputEncodedType : EncodedType :=
  EncodedType.prod splitWithLongHeadCoreEncodedType splitWithLongTailCoreEncodedType

/-- Splitter inputs whose current clause is known to be in the long branch. -/
def splitWithLongInputEncodedType : EncodedType where
  Carrier := { p : splitWithInputEncodedType.Carrier // 4 ≤ p.2.length }
  Symbol := splitWithInputEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun p => splitWithInputEncodedType.encode p.1

/-- Forget the long-branch proof without changing the splitter input encoding. -/
noncomputable def splitWithLongInputForgetTMBackedMap :
    TMBackedCostedMap splitWithLongInputEncodedType splitWithInputEncodedType
      (fun p => p.1) :=
  TMBackedCostedMap.ofEncodingEquiv
    splitWithLongInputEncodedType splitWithInputEncodedType
    (fun p => p.1) (Equiv.refl splitWithInputEncodedType.Symbol) (by
      intro p
      change splitWithInputEncodedType.encode p.1 =
        List.map id (splitWithInputEncodedType.encode p.1)
      simp)

/-- Project the long-branch clause as a length-at-least-four typed clause. -/
noncomputable def splitWithLongInputClauseTMBackedMap :
    TMBackedCostedMap splitWithLongInputEncodedType (clauseMinLengthEncodedType 4)
      (fun p => ⟨p.1.2, p.2⟩) where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongInputEncodedType)
      (Y := clauseMinLengthEncodedType 4)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        rcases p with ⟨p, hp⟩
        rcases p with ⟨next, c⟩
        change
          (clauseMinLengthEncodedType 4).inputSize ⟨c, hp⟩ ≤
            1 * splitWithLongInputEncodedType.inputSize ⟨(next, c), hp⟩ + 0
        change clauseStructuredEncodedType.inputSize c ≤
          1 * splitWithInputEncodedType.inputSize (next, c) + 0
        simp [splitWithInputEncodedType]))
  tm_polytime := by
    let X := splitWithLongInputEncodedType
    have hForget :
        TMPolyTimeMap X splitWithInputEncodedType (fun p : X.Carrier => p.1) :=
      splitWithLongInputForgetTMBackedMap.tm_polytime
    have hClausePlain :
        TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.1.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType)
        hForget
    rcases hClausePlain with ⟨hClausePlain⟩
    exact ⟨{ hClausePlain with
      outputsFun := by
        intro p
        simpa [clauseMinLengthEncodedType] using hClausePlain.outputsFun p }⟩

/-- Parse a long splitter input into the payload expected by the long branch writers. -/
def splitWithLongInputDecomposition
    (p : splitWithLongInputEncodedType.Carrier) :
    splitWithLongDecomposedInputEncodedType.Carrier :=
  let payload := splitWithLongClausePayload ⟨p.1.2, p.2⟩
  ((p.1.1, payload.1), payload.2)

theorem splitWithLongInputDecomposition_cons
    (next : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause)
    (h : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length) :
    splitWithLongInputDecomposition ⟨(next, l₁ :: l₂ :: l₃ :: l₄ :: rest), h⟩ =
      ((next, (l₁, l₂)), (l₃, (l₄, rest))) := by
  unfold splitWithLongInputDecomposition
  change
    ((next, (splitWithLongClausePayload ⟨l₁ :: l₂ :: l₃ :: l₄ :: rest, h⟩).1),
      (splitWithLongClausePayload ⟨l₁ :: l₂ :: l₃ :: l₄ :: rest, h⟩).2) =
      ((next, (l₁, l₂)), (l₃, (l₄, rest)))
  rw [splitWithLongClausePayload_cons l₁ l₂ l₃ l₄ rest h]
  rfl

/--
The long-branch payload parser for full splitter inputs is direct TM-backed.
It projects `next`, parses the clause by repeated uncons, and rearranges the
result into `splitWithLongDecomposedInputEncodedType`.
-/
noncomputable def splitWithLongInputDecompositionTMBackedMap :
    TMBackedCostedMap
      splitWithLongInputEncodedType
      splitWithLongDecomposedInputEncodedType
      splitWithLongInputDecomposition where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongInputEncodedType)
      (Y := splitWithLongDecomposedInputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro p
        rcases p with ⟨p, hp⟩
        rcases p with ⟨next, c⟩
        cases c with
        | nil =>
            simp at hp
        | cons l₁ c₁ =>
            cases c₁ with
            | nil =>
                simp at hp
            | cons l₂ c₂ =>
                cases c₂ with
                | nil =>
                    simp at hp
                | cons l₃ c₃ =>
                    cases c₃ with
                    | nil =>
                        simp at hp
                    | cons l₄ rest =>
                        rw [splitWithLongInputDecomposition_cons next l₁ l₂ l₃ l₄ rest hp]
                        have hInput :
                            splitWithLongInputEncodedType.inputSize
                                ⟨(next, l₁ :: l₂ :: l₃ :: l₄ :: rest), hp⟩ =
                              splitWithInputEncodedType.inputSize
                                (next, l₁ :: l₂ :: l₃ :: l₄ :: rest) := rfl
                        rw [hInput, one_mul, add_zero]
                        change
                          splitWithLongDecomposedInputEncodedType.inputSize
                              ((next, (l₁, l₂)), (l₃, (l₄, rest))) ≤
                            splitWithInputEncodedType.inputSize
                              (next, l₁ :: l₂ :: l₃ :: l₄ :: rest)
                        simp [splitWithLongDecomposedInputEncodedType,
                          splitWithLongHeadCoreEncodedType, splitWithLongTailCoreEncodedType,
                          splitWithInputEncodedType, clauseStructuredEncodedType]
                        omega))
  tm_polytime := by
    let X := splitWithLongInputEncodedType
    have hForget :
        TMPolyTimeMap X splitWithInputEncodedType (fun p : X.Carrier => p.1) :=
      splitWithLongInputForgetTMBackedMap.tm_polytime
    have hNext :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType)
        hForget
    have hClause :
        TMPolyTimeMap X (clauseMinLengthEncodedType 4)
          (fun p : X.Carrier => ⟨p.1.2, p.2⟩) :=
      splitWithLongInputClauseTMBackedMap.tm_polytime
    have hPayload :
        TMPolyTimeMap X splitWithLongClausePayloadEncodedType
          (fun p : X.Carrier => splitWithLongClausePayload ⟨p.1.2, p.2⟩) :=
      TMPolyTimeMap.comp splitWithLongClausePayloadTMBackedMap.tm_polytime hClause
    have hPayloadHead :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          (fun p : X.Carrier => (splitWithLongClausePayload ⟨p.1.2, p.2⟩).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          splitWithLongTailCoreEncodedType)
        hPayload
    have hPayloadTail :
        TMPolyTimeMap X splitWithLongTailCoreEncodedType
          (fun p : X.Carrier => (splitWithLongClausePayload ⟨p.1.2, p.2⟩).2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          splitWithLongTailCoreEncodedType)
        hPayload
    have hHeadCore :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType
          (fun p : X.Carrier => (p.1.1, (splitWithLongClausePayload ⟨p.1.2, p.2⟩).1)) :=
      TMPolyTimeMap.prod_mk hNext hPayloadHead
    have hDecomposed :
        TMPolyTimeMap X splitWithLongDecomposedInputEncodedType
          (fun p : X.Carrier =>
            ((p.1.1, (splitWithLongClausePayload ⟨p.1.2, p.2⟩).1),
              (splitWithLongClausePayload ⟨p.1.2, p.2⟩).2)) :=
      TMPolyTimeMap.prod_mk hHeadCore hPayloadTail
    simpa [X, splitWithLongInputDecomposition, splitWithLongDecomposedInputEncodedType,
      splitWithLongHeadCoreEncodedType, splitWithLongClausePayloadEncodedType] using hDecomposed

/-- Input `((next, l₁, l₂), tail)` for consing the long-step head onto a tail CNF. -/
def splitWithLongHeadInputEncodedType : EncodedType :=
  EncodedType.prod splitWithLongHeadCoreEncodedType cnfStructuredEncodedType

/-- Recursive `(next + 1, tailClause)` input emitted by one long splitter step. -/
def splitWithLongRecursiveInput
    (p : splitWithLongDecomposedInputEncodedType.Carrier) : splitWithInputEncodedType.Carrier :=
  (Nat.succ p.1.1, splitWithLongTailClause (p.1.1, p.2))

/--
The long-branch recursive-input builder is direct TM-backed.  This is the
`next + 1` counter update plus the `¬y_next :: l₃ :: l₄ :: rest` tail-clause
writer needed by the full clause-level runner.
-/
noncomputable def splitWithLongRecursiveInputTMBackedMap :
    TMBackedCostedMap
      splitWithLongDecomposedInputEncodedType splitWithInputEncodedType
      splitWithLongRecursiveInput where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongDecomposedInputEncodedType)
      (Y := splitWithInputEncodedType)
      (LinearSizeBound.intro_with 2 20 (by
        intro p
        rcases p with ⟨head, tail⟩
        rcases head with ⟨next, headLits⟩
        rcases headLits with ⟨l₁, l₂⟩
        rcases tail with ⟨l₃, l₄Rest⟩
        rcases l₄Rest with ⟨l₄, rest⟩
        change
          (EncodedType.prod EncodedType.nat clauseStructuredEncodedType).inputSize
              (Nat.succ next, SAT.Clause.negAux next :: l₃ :: l₄ :: rest) ≤
            2 *
                (EncodedType.prod splitWithLongHeadCoreEncodedType
                  splitWithLongTailCoreEncodedType).inputSize
                  ((next, (l₁, l₂)), (l₃, (l₄, rest))) + 20
        simp [splitWithLongHeadCoreEncodedType, splitWithLongTailCoreEncodedType,
          clauseStructuredEncodedType, literalStructured_inputSize_eq, SAT.Clause.negAux]
        omega))
  tm_polytime := by
    let X := splitWithLongDecomposedInputEncodedType
    have hHead :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst splitWithLongHeadCoreEncodedType splitWithLongTailCoreEncodedType
    have hTailCore :
        TMPolyTimeMap X splitWithLongTailCoreEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd splitWithLongHeadCoreEncodedType splitWithLongTailCoreEncodedType
    have hNext :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        hHead
    have hSucc :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.1) :=
      TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    have hTailInput :
        TMPolyTimeMap X splitWithLongTailInputEncodedType
          (fun p : X.Carrier => (p.1.1, p.2)) :=
      TMPolyTimeMap.prod_mk hNext hTailCore
    have hTailClause :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => splitWithLongTailClause (p.1.1, p.2)) :=
      TMPolyTimeMap.comp splitWithLongTailClauseTMBackedMap.tm_polytime hTailInput
    have hPair :
        TMPolyTimeMap X splitWithInputEncodedType splitWithLongRecursiveInput :=
      TMPolyTimeMap.prod_mk hSucc hTailClause
    simpa [X, splitWithInputEncodedType, splitWithLongRecursiveInput, Function.comp] using hPair

/-- Output of one checked long splitter step: the trace head and recursive input. -/
def splitWithLongTraceStepOutputEncodedType : EncodedType :=
  EncodedType.prod splitWithLongHeadCoreEncodedType splitWithInputEncodedType

/--
One long splitter step packaged as the pair needed by the future clause runner:
the head trace entry and the recursive splitter input.
-/
def splitWithLongTraceStepOutput
    (p : splitWithLongInputEncodedType.Carrier) :
    splitWithLongTraceStepOutputEncodedType.Carrier :=
  let d := splitWithLongInputDecomposition p
  (d.1, splitWithLongRecursiveInput d)

theorem splitWithLongTraceStepOutput_cons
    (next : Nat) (l₁ l₂ l₃ l₄ : SAT.Literal) (rest : SAT.Clause)
    (h : 4 ≤ (l₁ :: l₂ :: l₃ :: l₄ :: rest).length) :
    splitWithLongTraceStepOutput ⟨(next, l₁ :: l₂ :: l₃ :: l₄ :: rest), h⟩ =
      ((next, (l₁, l₂)),
        (Nat.succ next, SAT.Clause.negAux next :: l₃ :: l₄ :: rest)) := by
  rw [splitWithLongTraceStepOutput, splitWithLongInputDecomposition_cons]
  rfl

theorem splitWithLongTraceStepOutput_inputSize_le
    (p : splitWithLongInputEncodedType.Carrier) :
    splitWithLongTraceStepOutputEncodedType.inputSize (splitWithLongTraceStepOutput p) ≤
      3 * splitWithLongInputEncodedType.inputSize p + 30 := by
  rcases p with ⟨p, hp⟩
  rcases p with ⟨next, c⟩
  cases c with
  | nil =>
      simp at hp
  | cons l₁ c₁ =>
      cases c₁ with
      | nil =>
          simp at hp
      | cons l₂ c₂ =>
          cases c₂ with
          | nil =>
              simp at hp
          | cons l₃ c₃ =>
              cases c₃ with
              | nil =>
                  simp at hp
              | cons l₄ rest =>
                  rw [splitWithLongTraceStepOutput_cons next l₁ l₂ l₃ l₄ rest hp]
                  have hInput :
                      splitWithLongInputEncodedType.inputSize
                          ⟨(next, l₁ :: l₂ :: l₃ :: l₄ :: rest), hp⟩ =
                        splitWithInputEncodedType.inputSize
                          (next, l₁ :: l₂ :: l₃ :: l₄ :: rest) := rfl
                  rw [hInput]
                  change
                    splitWithLongTraceStepOutputEncodedType.inputSize
                        ((next, (l₁, l₂)),
                          (Nat.succ next, SAT.Clause.negAux next :: l₃ :: l₄ :: rest)) ≤
                      3 *
                        splitWithInputEncodedType.inputSize
                          (next, l₁ :: l₂ :: l₃ :: l₄ :: rest) + 30
                  simp [splitWithLongTraceStepOutputEncodedType,
                    splitWithLongHeadCoreEncodedType, splitWithInputEncodedType,
                    clauseStructuredEncodedType, literalStructured_inputSize_eq,
                    SAT.Clause.negAux]
                  omega

/--
The long-step trace/recursive-input transition is direct TM-backed.  This is
still only the long branch transition; it does not choose the branch or iterate
the clause recursion.
-/
noncomputable def splitWithLongTraceStepOutputTMBackedMap :
    TMBackedCostedMap
      splitWithLongInputEncodedType
      splitWithLongTraceStepOutputEncodedType
      splitWithLongTraceStepOutput where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongInputEncodedType)
      (Y := splitWithLongTraceStepOutputEncodedType)
      (LinearSizeBound.intro_with 3 30 (by
        intro p
        exact splitWithLongTraceStepOutput_inputSize_le p))
  tm_polytime := by
    let X := splitWithLongInputEncodedType
    have hDecomposed :
        TMPolyTimeMap X splitWithLongDecomposedInputEncodedType
          splitWithLongInputDecomposition :=
      splitWithLongInputDecompositionTMBackedMap.tm_polytime
    have hHead :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType
          (fun p : X.Carrier => (splitWithLongInputDecomposition p).1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst splitWithLongHeadCoreEncodedType splitWithLongTailCoreEncodedType)
        hDecomposed
    have hRecursive :
        TMPolyTimeMap X splitWithInputEncodedType
          (fun p : X.Carrier => splitWithLongRecursiveInput (splitWithLongInputDecomposition p)) :=
      TMPolyTimeMap.comp splitWithLongRecursiveInputTMBackedMap.tm_polytime hDecomposed
    have hPair :
        TMPolyTimeMap X splitWithLongTraceStepOutputEncodedType
          splitWithLongTraceStepOutput :=
      TMPolyTimeMap.prod_mk hHead hRecursive
    simpa [X, splitWithLongTraceStepOutput, splitWithLongTraceStepOutputEncodedType,
      Function.comp] using hPair

/-- Head clause `[l₁, l₂, y_next]` emitted by one long-clause splitter step. -/
def splitWithLongHeadClause
    (p : splitWithLongHeadInputEncodedType.Carrier) : SAT.Clause :=
  [p.1.2.1, p.1.2.2, SAT.Clause.posAux p.1.1]

/-- Long-step head consing function. -/
def splitWithLongHeadCons
    (p : splitWithLongHeadInputEncodedType.Carrier) : SAT.CNF :=
  splitWithLongHeadClause p :: p.2

/-- The head clause determined by one long-step trace entry. -/
def splitWithLongHeadCoreClause
    (p : splitWithLongHeadCoreEncodedType.Carrier) : SAT.Clause :=
  [p.2.1, p.2.2, SAT.Clause.posAux p.1]

theorem splitWithLongHeadCoreClause_inputSize_le
    (p : splitWithLongHeadCoreEncodedType.Carrier) :
    clauseStructuredEncodedType.inputSize (splitWithLongHeadCoreClause p) + 1 ≤
      splitWithLongHeadCoreEncodedType.inputSize p + 10 := by
  rcases p with ⟨next, lits⟩
  rcases lits with ⟨l₁, l₂⟩
  change
    (EncodedType.list literalStructuredEncodedType).inputSize
        [l₁, l₂, SAT.Clause.posAux next] + 1 ≤
      splitWithLongHeadCoreEncodedType.inputSize (next, (l₁, l₂)) + 10
  rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
    EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
  simp [splitWithLongHeadCoreEncodedType, literalStructured_inputSize_eq,
    SAT.Clause.posAux]
  omega

/--
The head-clause writer for a single trace entry is direct TM-backed under
faithful encodings.
-/
noncomputable def splitWithLongHeadCoreClauseTMBackedMap :
    TMBackedCostedMap
      splitWithLongHeadCoreEncodedType clauseStructuredEncodedType
      splitWithLongHeadCoreClause where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongHeadCoreEncodedType)
      (Y := clauseStructuredEncodedType)
      (LinearSizeBound.intro_with 1 10 (by
        intro p
        have h := splitWithLongHeadCoreClause_inputSize_le p
        omega))
  tm_polytime := by
    let X := splitWithLongHeadCoreEncodedType
    have hNext :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hLitPair :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
    have hL₁ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType)
        hLitPair
    have hL₂ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.2.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType)
        hLitPair
    have hPos :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun p : X.Carrier => SAT.Clause.posAux p.1) :=
      TMPolyTimeMap.comp posAuxTMBackedMap.tm_polytime hNext
    have hPosSingleton :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => [SAT.Clause.posAux p.1]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hPos
    have hL₂Rest :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => (p.2.2, [SAT.Clause.posAux p.1])) :=
      TMPolyTimeMap.prod_mk hL₂ hPosSingleton
    have hAfterL₂ :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => [p.2.2, SAT.Clause.posAux p.1]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₂Rest
    have hL₁Rest :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => (p.2.1, [p.2.2, SAT.Clause.posAux p.1])) :=
      TMPolyTimeMap.prod_mk hL₁ hAfterL₂
    have hClause :
        TMPolyTimeMap X clauseStructuredEncodedType splitWithLongHeadCoreClause :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₁Rest
    simpa [X, splitWithLongHeadCoreClause, Function.comp] using hClause

/-- The long-step head-cons writer is direct TM-backed under faithful encodings. -/
noncomputable def splitWithLongHeadConsTMBackedMap :
    TMBackedCostedMap
      splitWithLongHeadInputEncodedType cnfStructuredEncodedType
      splitWithLongHeadCons where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithLongHeadInputEncodedType)
      (Y := cnfStructuredEncodedType)
      (LinearSizeBound.intro_with 1 10 (by
        intro p
        rcases p with ⟨core, tail⟩
        rcases core with ⟨next, lits⟩
        rcases lits with ⟨l₁, l₂⟩
        change
          (EncodedType.list clauseStructuredEncodedType).inputSize
              ([l₁, l₂, SAT.Clause.posAux next] :: tail) ≤
            1 * (EncodedType.prod splitWithLongHeadCoreEncodedType cnfStructuredEncodedType).inputSize
                ((next, (l₁, l₂)), tail) + 10
        rw [EncodedType.inputSize_list_cons]
        change
          (EncodedType.list literalStructuredEncodedType).inputSize
              [l₁, l₂, SAT.Clause.posAux next] + 1 +
              (EncodedType.list clauseStructuredEncodedType).inputSize tail ≤
            1 * (EncodedType.prod splitWithLongHeadCoreEncodedType cnfStructuredEncodedType).inputSize
                ((next, (l₁, l₂)), tail) + 10
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        simp [splitWithLongHeadCoreEncodedType, cnfStructuredEncodedType,
          clauseStructuredEncodedType, literalStructured_inputSize_eq, SAT.Clause.posAux]
        omega))
  tm_polytime := by
    let X := splitWithLongHeadInputEncodedType
    have hCore :
        TMPolyTimeMap X splitWithLongHeadCoreEncodedType (fun p : X.Carrier => p.1) :=
      TMPolyTimeMap.fst splitWithLongHeadCoreEncodedType cnfStructuredEncodedType
    have hTail :
        TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.2) :=
      TMPolyTimeMap.snd splitWithLongHeadCoreEncodedType cnfStructuredEncodedType
    have hNext :
        TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        hCore
    have hLitPair :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType)
          (fun p : X.Carrier => p.1.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd EncodedType.nat
          (EncodedType.prod literalStructuredEncodedType literalStructuredEncodedType))
        hCore
    have hL₁ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.1.2.1) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.fst literalStructuredEncodedType literalStructuredEncodedType)
        hLitPair
    have hL₂ :
        TMPolyTimeMap X literalStructuredEncodedType (fun p : X.Carrier => p.1.2.2) :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.snd literalStructuredEncodedType literalStructuredEncodedType)
        hLitPair
    have hPos :
        TMPolyTimeMap X literalStructuredEncodedType
          (fun p : X.Carrier => SAT.Clause.posAux p.1.1) :=
      TMPolyTimeMap.comp posAuxTMBackedMap.tm_polytime hNext
    have hPosSingleton :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => [SAT.Clause.posAux p.1.1]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton literalStructuredEncodedType) hPos
    have hL₂RestClause :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier => (p.1.2.2, [SAT.Clause.posAux p.1.1])) :=
      TMPolyTimeMap.prod_mk hL₂ hPosSingleton
    have hAfterL₂ :
        TMPolyTimeMap X clauseStructuredEncodedType
          (fun p : X.Carrier => [p.1.2.2, SAT.Clause.posAux p.1.1]) :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₂RestClause
    have hL₁RestClause :
        TMPolyTimeMap X
          (EncodedType.prod literalStructuredEncodedType clauseStructuredEncodedType)
          (fun p : X.Carrier =>
            (p.1.2.1, [p.1.2.2, SAT.Clause.posAux p.1.1])) :=
      TMPolyTimeMap.prod_mk hL₁ hAfterL₂
    have hHead :
        TMPolyTimeMap X clauseStructuredEncodedType splitWithLongHeadClause :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons literalStructuredEncodedType) hL₁RestClause
    have hHeadTail :
        TMPolyTimeMap X
          (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
          (fun p : X.Carrier => (splitWithLongHeadClause p, p.2)) :=
      TMPolyTimeMap.prod_mk hHead hTail
    have hCons :
        TMPolyTimeMap X cnfStructuredEncodedType splitWithLongHeadCons :=
      TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hHeadTail
    simpa [X, splitWithLongHeadCons, splitWithLongHeadClause, Function.comp] using hCons

/-- Fold-step input `(accumulated CNF, long-step head core)` for trace rebuilding. -/
def splitWithTraceFoldStepInputEncodedType : EncodedType :=
  EncodedType.prod cnfStructuredEncodedType splitWithLongHeadCoreEncodedType

/-- Add one long-step head clause in front of the accumulated splitter output. -/
def splitWithTraceFoldStep
    (p : splitWithTraceFoldStepInputEncodedType.Carrier) : SAT.CNF :=
  splitWithLongHeadCons (p.2, p.1)


end Karp21
end ComplexityReduction
