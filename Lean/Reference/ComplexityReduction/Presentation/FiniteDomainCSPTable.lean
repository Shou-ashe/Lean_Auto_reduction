/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.SatLike
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Program.EncodingTransport

/-!
Canonical explicit presentation of CR's concrete finite relation-table CSP fragment.

`ComplexityReduction.CSP.FiniteDomain.Language` is deliberately more general:
its `Rel.holds` field is an extensional `Prop` predicate.  Finiteness of the
domain and of the symbol type does not make that predicate executable, and this
leaf does not manufacture a Boolean lookup, a program, or TM evidence for it.

The older CR library does, separately, contain one exact table carrier:
`CSP.BoolRel`, whose `accepts` field is a finite table of Boolean tuples.  A
`CSP.BoolLanguage` is the corresponding finite family of those tables.  This
file presents precisely that carrier and its formula syntax.  It does not
claim that CR's noncomputable `BoolRel.Holds` decision instance supplies a
direct-TM table lookup.  Such an atom needs separately audited executable and
direct-TM evidence.

The formula representation is intentionally user-locked.  Relation-symbol
enumeration and the dependent formula payload are fixed per language, so no
closed `StructuralRepresentationCertificate` is exported.
-/

namespace ComplexityReduction
namespace Presentation
namespace FiniteDomainCSPTable

open Encoding
open ComplexityReduction.CSP

noncomputable section

/-- The exact CR carrier for a finite Boolean relation table language. -/
abbrev TableLanguage : Type 1 := BoolLanguage

/-- The accepting table stored by a concrete CR Boolean relation symbol. -/
def acceptedRows (Γ : TableLanguage) (symbol : Γ.Symbol) :
    Finset (BoolTuple (Γ.relationOf symbol).arity) :=
  (Γ.relationOf symbol).accepts

/-- Table membership agrees exactly with the legacy Boolean relation semantics. -/
@[simp]
theorem holds_iff_mem_acceptedRows (Γ : TableLanguage) (symbol : Γ.Symbol)
    (tuple : BoolTuple (Γ.relationOf symbol).arity) :
    (Γ.relationOf symbol).Holds tuple ↔ tuple ∈ acceptedRows Γ symbol :=
  BoolRel.holds_iff_mem _ _

/-- The exact CR compatibility encoder for table-language formulas, retained as evidence scope. -/
abbrev legacyFormulaEncodedType (Γ : TableLanguage) : ComplexityReduction.EncodedType :=
  ComplexityReduction.CSP.formulaEncodedType Γ

/-- The legacy table-language encoder has exactly the original Boolean CSP formula carrier. -/
@[simp]
theorem legacyFormulaEncodedType_carrier (Γ : TableLanguage) :
    (legacyFormulaEncodedType Γ).Carrier = Formula Γ :=
  rfl

/--
The finite index of one relation symbol in exactly the selected table language.
Unlike a bare natural number, this index retains both the language parameter
and its cardinality bound, so it cannot be reused as a symbol identity for an
unrelated table language.
-/
def relationIndex (Γ : TableLanguage) (symbol : Γ.Symbol) : Fin (Fintype.card Γ.Symbol) :=
  Fintype.equivFin Γ.Symbol symbol

/-- Recover the exact selected-language symbol from a bounded relation index. -/
def relationSymbol (Γ : TableLanguage) (index : Fin (Fintype.card Γ.Symbol)) : Γ.Symbol :=
  (Fintype.equivFin Γ.Symbol).symm index

/-- Relation-symbol indexing round-trips at the exact table-language parameter. -/
@[simp]
theorem relationSymbol_relationIndex (Γ : TableLanguage) (symbol : Γ.Symbol) :
    relationSymbol Γ (relationIndex Γ symbol) = symbol :=
  (Fintype.equivFin Γ.Symbol).symm_apply_apply symbol

/-- Decoding then re-indexing a bounded relation code is exact. -/
@[simp]
theorem relationIndex_relationSymbol (Γ : TableLanguage)
    (index : Fin (Fintype.card Γ.Symbol)) :
    relationIndex Γ (relationSymbol Γ index) = index :=
  (Fintype.equivFin Γ.Symbol).apply_symm_apply index

/-- The fixed numeric identity is the value of the exact bounded relation index. -/
def relationCode (Γ : TableLanguage) (symbol : Γ.Symbol) : Nat :=
  (relationIndex Γ symbol).val

/-- A relation code retains the cardinality bound of its selected language. -/
theorem relationCode_lt_card (Γ : TableLanguage) (symbol : Γ.Symbol) :
    relationCode Γ symbol < Fintype.card Γ.Symbol :=
  (relationIndex Γ symbol).isLt

/-- The relation-symbol code is faithful for exactly the selected table language. -/
theorem relationCode_injective (Γ : TableLanguage) :
    Function.Injective (relationCode Γ) := by
  intro left right equality
  apply (Fintype.equivFin Γ.Symbol).injective
  exact Fin.ext equality

/-- The numeric payload of one dependent table-language CSP constraint. -/
def constraintCode {Γ : TableLanguage} (constraint : Constraint Γ) : Nat × List Nat :=
  (relationCode Γ constraint.symbol, constraint.varsList)

/-- The ordered numeric payload of one exact table-language CSP formula. -/
def formulaCode (Γ : TableLanguage) (formula : Formula Γ) : List (Nat × List Nat) :=
  formula.map constraintCode

private theorem list_ofFn_injective {α : Type} {n : Nat} :
    Function.Injective (List.ofFn : (Fin n → α) → List α) := by
  intro left right equality
  funext index
  have entryEquality := congrArg (fun values : List α => values[index.val]?) equality
  simpa [List.getElem?_ofFn, index.isLt] using entryEquality

/-- The dependent constraint payload is faithful. -/
theorem constraintCode_injective (Γ : TableLanguage) :
    Function.Injective (@constraintCode Γ) := by
  rintro ⟨leftSymbol, leftVars⟩ ⟨rightSymbol, rightVars⟩ equality
  have symbolEquality : leftSymbol = rightSymbol :=
    relationCode_injective Γ (congrArg Prod.fst equality)
  cases symbolEquality
  have varsEquality : leftVars = rightVars :=
    list_ofFn_injective (congrArg Prod.snd equality)
  cases varsEquality
  rfl

/-- The exact table-language formula payload is faithful. -/
theorem formulaCode_injective (Γ : TableLanguage) :
    Function.Injective (formulaCode Γ) := by
  exact List.map_injective_iff.mpr (constraintCode_injective Γ)

/-- Standard payload layout for one finite-table CSP constraint. -/
abbrev constraintCodeEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod ComplexityReduction.EncodedType.nat
    (ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat)

/-- Standard payload layout for an ordered finite-table CSP formula. -/
abbrev formulaCodeEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list constraintCodeEncodedType

private theorem formulaCodeEncodedType_encode_injective :
    Function.Injective formulaCodeEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective
    (ComplexityReduction.EncodedType.prod_encode_injective
      ComplexityReduction.EncodedType.nat_encode_injective
      (ComplexityReduction.EncodedType.list_encode_injective
        ComplexityReduction.EncodedType.nat_encode_injective))

/--
The faithful V2 formula encoding for one exact CR Boolean table language.

The carrier is the original `CSP.Formula Γ`, and its relation semantics remain
the original finite `BoolRel.accepts` tables.  This encoder is explicit rather
than automatically selected.
-/
def encodedType (Γ : TableLanguage) : ComplexityReduction.EncodedType where
  Carrier := Formula Γ
  Symbol := formulaCodeEncodedType.Symbol
  finite_symbol := formulaCodeEncodedType.finite_symbol
  encode := fun formula => formulaCodeEncodedType.encode (formulaCode Γ formula)

/-- Faithfulness of the exact table-language V2 formula encoding. -/
theorem encodedType_encode_injective (Γ : TableLanguage) :
    Function.Injective (encodedType Γ).encode := by
  intro left right equality
  apply formulaCode_injective Γ
  exact formulaCodeEncodedType_encode_injective equality

/--
Convert a direct-TM computation of the canonical numeric formula payload into
a direct-TM computation of the corresponding table-CSP formula.  The formula
function and payload function are inferred from the two supplied proofs.
-/
theorem formula_tmPolyTime_of_code {X : ComplexityReduction.EncodedType}
    {Γ : TableLanguage}
    {formula : X.Carrier → Formula Γ}
    {code : X.Carrier → formulaCodeEncodedType.Carrier}
    (hCode : ComplexityReduction.TMPolyTimeMap X formulaCodeEncodedType code)
    (codeEq : ∀ input, code input = formulaCode Γ (formula input)) :
    ComplexityReduction.TMPolyTimeMap X (encodedType Γ) formula := by
  apply ComplexityReduction.TMPolyTimeMap.transport_output
    (Z := encodedType Γ) (targetOutput := formula) hCode (Equiv.refl _)
  intro input
  rw [codeEq input]
  change formulaCodeEncodedType.encode (formulaCode Γ (formula input)) =
    List.map (fun symbol => symbol)
      (formulaCodeEncodedType.encode (formulaCode Γ (formula input)))
  exact (List.map_id _).symm

/-- The complete identity of the custom table-language formula-code layout. -/
def representationShape : CodecShape :=
  .list (.prod .unaryNat (.list .unaryNat))

/--
The exact lawful V2 presentation of formulas over a finite Boolean table
language.  The absence of a structural certificate is intentional: the
language-specific table enumeration is explicitly user-locked.
-/
def lawfulRepresentation (Γ : TableLanguage) : LawfulEncodedType where
  encodedType := encodedType Γ
  representation := representationShape.identity
  faithful := ⟨encodedType_encode_injective Γ⟩

@[simp]
theorem lawfulRepresentation_encodedType (Γ : TableLanguage) :
    (lawfulRepresentation Γ).encodedType = encodedType Γ :=
  rfl

@[simp]
theorem lawfulRepresentation_representation (Γ : TableLanguage) :
    (lawfulRepresentation Γ).representation = representationShape.identity :=
  rfl

/-- The presentation carrier is exactly the CR Boolean table-language formula syntax. -/
theorem lawfulRepresentation_carrier_eq_formula (Γ : TableLanguage) :
    (lawfulRepresentation Γ).Carrier = Formula Γ :=
  rfl

/-- The sole encoder exposed by this presentation is its explicit V2 formula codec. -/
@[simp]
theorem lawfulRepresentation_encode (Γ : TableLanguage)
    (formula : (lawfulRepresentation Γ).Carrier) :
    (lawfulRepresentation Γ).encode formula = (encodedType Γ).encode formula :=
  rfl

/-- The legacy table-language decision problem before selecting its V2 presentation. -/
def semanticProblem (Γ : TableLanguage) : ComplexityReduction.DecisionProblem where
  Instance := Formula Γ
  isYes := Formula.Satisfiable

@[simp]
theorem semanticProblem_isYes (Γ : TableLanguage) (formula : Formula Γ) :
    (semanticProblem Γ).isYes formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

/-- The semantic predicate at the exact user-locked table-language presentation. -/
def problemAt (Γ : TableLanguage) : ProblemAt (lawfulRepresentation Γ) where
  isYes := Formula.Satisfiable

/-- The V2 endpoint for one exact CR Boolean relation-table CSP language. -/
def presentedProblem (Γ : TableLanguage) : PresentedProblem :=
  PresentedProblem.ofProblemAt (lawfulRepresentation Γ) (problemAt Γ)

/--
The semantic endpoint indexed by the one selected table-language presentation.

This is a projection of `presentedProblem Γ`, rather than a separately
assembled predicate on an equal formula carrier.  Consequently a consumer of
the endpoint is indexed by the same `lawfulRepresentation Γ` whose faithful
codec evidence and representation identity were used to construct the
presented problem.
-/
def endpoint (Γ : TableLanguage) : PresentedProblem.EndpointAt (lawfulRepresentation Γ) :=
  (presentedProblem Γ).endpoint

/--
The endpoint projection retains exactly the predicate fixed for the selected
table language; it is not reindexed through a carrier equality or a codec
equivalence.
-/
@[simp]
theorem endpoint_eq_problemAt (Γ : TableLanguage) :
    endpoint Γ = problemAt Γ :=
  rfl

/--
Rebuilding the presentation from the exported endpoint does not change its
parameter, faithful codec evidence, predicate, or representation identity.
This is the only endpoint reassembly exported by this leaf.
-/
@[simp]
theorem presentedProblem_eq_of_endpoint (Γ : TableLanguage) :
    presentedProblem Γ =
      PresentedProblem.ofProblemAt (lawfulRepresentation Γ) (endpoint Γ) :=
  rfl

/-- The fixed-presentation endpoint is exactly Boolean table-CSP satisfiability. -/
@[simp]
theorem endpoint_isYes (Γ : TableLanguage)
    (formula : (lawfulRepresentation Γ).Carrier) :
    (endpoint Γ).isYes formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

@[simp]
theorem presentedProblem_representation (Γ : TableLanguage) :
    (presentedProblem Γ).representation = lawfulRepresentation Γ :=
  rfl

/--
Any future automatic admission for this table-language endpoint must carry a
structural certificate at this exact explicit lawful presentation.  This does
not manufacture such a certificate from the faithful custom formula codec;
it only records the closed input required by automatic admission.
-/
theorem automaticAdmission_exactLawfulPresentation (Γ : TableLanguage)
    (admission : PresentedProblem.AutomaticPresentationAdmission (presentedProblem Γ)) :
    admission.certificate.toLawfulEncodedType = lawfulRepresentation Γ :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ admission.certificate

@[simp]
theorem presentedProblem_backendEndpoint_instance (Γ : TableLanguage) :
    (presentedProblem Γ).backendEndpoint.Instance = encodedType Γ :=
  rfl

@[simp]
theorem presentedProblem_representationIdentity (Γ : TableLanguage) :
    (presentedProblem Γ).representationIdentity = representationShape.identity :=
  rfl

/-- The endpoint has exactly the legacy Boolean table-CSP satisfiability semantics. -/
@[simp]
theorem presentedProblem_accepts (Γ : TableLanguage)
    (formula : (presentedProblem Γ).Instance) :
    (presentedProblem Γ).accepts formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

/-- The typed endpoint agrees with CR's exact Boolean CSP decision problem. -/
@[simp]
theorem presentedProblem_accepts_iff_boolCSPDecisionProblem (Γ : TableLanguage)
    (formula : (presentedProblem Γ).Instance) :
    (presentedProblem Γ).accepts formula ↔
      (ComplexityReduction.CSP.boolCSPDecisionProblem Γ).isYes formula :=
  Iff.rfl

namespace ExtensionalBoundary

open ComplexityReduction.CSP.FiniteDomain

/--
Explicit data needed to tabulate one generic finite-domain extensional
relation.  A `Language D` alone provides none of this data.  `rows` uses a
plain list deliberately: this proposition-level witness does not install a
decidable lookup procedure, a Boolean function, a program, or TM evidence.
-/
structure UserSuppliedRelationTable {D : Type} (Γ : Language D) (symbol : Γ.Symbol) where
  rows : List (Tuple D (Γ.relationOf symbol).arity)
  holds_iff_mem : ∀ tuple, (Γ.relationOf symbol).Holds tuple ↔ tuple ∈ rows

/-- A complete generic table view must be supplied relation-by-relation by the caller. -/
abbrev UserSuppliedLanguageTables {D : Type} (Γ : Language D) : Type :=
  ∀ symbol : Γ.Symbol, UserSuppliedRelationTable Γ symbol

/-- A supplied table records only the exact extensional predicate it validates. -/
@[simp]
theorem holds_iff_mem_rows {D : Type} {Γ : Language D} {symbol : Γ.Symbol}
    (table : UserSuppliedRelationTable Γ symbol)
    (tuple : Tuple D (Γ.relationOf symbol).arity) :
    (Γ.relationOf symbol).Holds tuple ↔ tuple ∈ table.rows :=
  table.holds_iff_mem tuple

end ExtensionalBoundary

end

end FiniteDomainCSPTable
end Presentation
end ComplexityReduction
