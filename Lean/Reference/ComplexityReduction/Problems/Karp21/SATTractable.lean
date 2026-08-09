/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding
import ComplexityReduction.Legacy.ComplexityReduction.SAT.TwoCNF
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
User-locked V2 presentation of the direct tractable 2CNF SAT endpoint.

`ComplexityReduction.SAT.TwoCNF` supplies the direct 2CNF syntax and its
semantic satisfiability predicate, but not an encoded decision problem.  This
leaf therefore embeds that exact syntax faithfully into the existing structured
CNF encoder.  The embedding and the reused CNF encoder are both injective.

The direct 2CNF syntax is a domain-specific selection rather than a closed
`StructuralRepresentationOrigin`; consequently this module intentionally
exports no structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SATTractable

open Encoding
open ComplexityReduction.SAT

/-- Translate a direct 2CNF literal to the established CNF-literal syntax. -/
def twoCNFLiteralToCNFLiteral (literal : TwoCNF.Literal) : Literal :=
  { var := literal.var, neg := !literal.positive }

/-- Translate a direct 2CNF clause to its exact list-based CNF clause. -/
def twoCNFClauseToCNFClause : TwoCNF.Clause → Clause
  | .empty => []
  | .unit literal => [twoCNFLiteralToCNFLiteral literal]
  | .binary left right => [twoCNFLiteralToCNFLiteral left, twoCNFLiteralToCNFLiteral right]

/-- The faithful syntax embedding from direct 2CNF formulas to list-based CNF formulas. -/
def twoCNFToCNF (formula : TwoCNF.CNF) : CNF :=
  formula.map twoCNFClauseToCNFClause

/-- The direct literal translation is injective. -/
theorem twoCNFLiteralToCNFLiteral_injective : Function.Injective twoCNFLiteralToCNFLiteral := by
  intro left right equality
  cases left with
  | mk leftVar leftPositive =>
      cases right with
      | mk rightVar rightPositive =>
          simp [twoCNFLiteralToCNFLiteral] at equality
          rcases equality with ⟨variableEquality, polarityEquality⟩
          cases variableEquality
          cases leftPositive <;> cases rightPositive <;> simp at polarityEquality ⊢

/-- The direct-clause embedding is injective. -/
theorem twoCNFClauseToCNFClause_injective : Function.Injective twoCNFClauseToCNFClause := by
  intro left right equality
  cases left with
  | empty =>
      cases right <;> simp [twoCNFClauseToCNFClause] at equality ⊢
  | unit leftLiteral =>
      cases right with
      | empty =>
          simp [twoCNFClauseToCNFClause] at equality
      | unit rightLiteral =>
          have literalEquality :
              twoCNFLiteralToCNFLiteral leftLiteral = twoCNFLiteralToCNFLiteral rightLiteral := by
            simpa [twoCNFClauseToCNFClause] using congrArg List.head? equality
          exact congrArg TwoCNF.Clause.unit
            (twoCNFLiteralToCNFLiteral_injective literalEquality)
      | binary rightFirst rightSecond =>
          simp [twoCNFClauseToCNFClause] at equality
  | binary leftFirst leftSecond =>
      cases right with
      | empty =>
          simp [twoCNFClauseToCNFClause] at equality
      | unit rightLiteral =>
          simp [twoCNFClauseToCNFClause] at equality
      | binary rightFirst rightSecond =>
          have firstEquality :
              twoCNFLiteralToCNFLiteral leftFirst = twoCNFLiteralToCNFLiteral rightFirst := by
            simpa [twoCNFClauseToCNFClause] using congrArg List.head? equality
          have secondEquality :
              twoCNFLiteralToCNFLiteral leftSecond = twoCNFLiteralToCNFLiteral rightSecond := by
            simpa [twoCNFClauseToCNFClause] using
              congrArg (fun clause : Clause => clause.tail.head?) equality
          have leftFirst_eq_rightFirst := twoCNFLiteralToCNFLiteral_injective firstEquality
          have leftSecond_eq_rightSecond := twoCNFLiteralToCNFLiteral_injective secondEquality
          cases leftFirst_eq_rightFirst
          cases leftSecond_eq_rightSecond
          rfl

/-- The direct 2CNF-to-CNF syntax embedding is injective. -/
theorem twoCNFToCNF_injective : Function.Injective twoCNFToCNF :=
  List.map_injective_iff.mpr twoCNFClauseToCNFClause_injective

/--
The exact direct-2CNF encoding, using the existing structured CNF finite
alphabet after the injective syntax embedding.
-/
def twoCNFStructuredEncodedType : ComplexityReduction.EncodedType where
  Carrier := TwoCNF.CNF
  Symbol := ComplexityReduction.Karp21.cnfStructuredEncodedType.Symbol
  finite_symbol := ComplexityReduction.Karp21.cnfStructuredEncodedType.finite_symbol
  encode := fun formula =>
    ComplexityReduction.Karp21.cnfStructuredEncodedType.encode (twoCNFToCNF formula)

/-- The direct-2CNF structured encoding is faithful. -/
theorem twoCNFStructuredEncodedType_encode_injective :
    Function.Injective twoCNFStructuredEncodedType.encode := by
  intro left right equality
  apply twoCNFToCNF_injective
  exact ComplexityReduction.Karp21.cnfStructuredEncodedType_encode_injective equality

/-- The complete explicit layout identity of the direct-2CNF encoding. -/
def twoCNFStructuredShape : CodecShape :=
  .list (.list (.prod .unaryNat .bool))

/--
The exact V2 lawful presentation of direct 2CNF syntax.

This is explicitly user-locked: the codec is faithful, but its syntax
embedding is not one of the closed standard structural origins.
-/
def twoCNFStructuredPresentation : LawfulEncodedType where
  encodedType := twoCNFStructuredEncodedType
  representation := twoCNFStructuredShape.identity
  faithful := ⟨twoCNFStructuredEncodedType_encode_injective⟩

@[simp]
theorem twoCNFStructuredPresentation_encodedType :
    twoCNFStructuredPresentation.encodedType = twoCNFStructuredEncodedType :=
  rfl

@[simp]
theorem twoCNFStructuredPresentation_representation :
    twoCNFStructuredPresentation.representation = twoCNFStructuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the direct `SAT.TwoCNF.CNF` syntax. -/
theorem twoCNFStructuredPresentation_carrier_eq_TwoCNF :
    twoCNFStructuredPresentation.Carrier = TwoCNF.CNF :=
  rfl

/-- The sole exposed encoder is the direct-2CNF embedding followed by the established CNF codec. -/
@[simp]
theorem twoCNFStructuredPresentation_encode (formula : twoCNFStructuredPresentation.Carrier) :
    twoCNFStructuredPresentation.encode formula =
      ComplexityReduction.Karp21.cnfStructuredEncodedType.encode (twoCNFToCNF formula) :=
  rfl

/-- The direct 2CNF satisfiability predicate at this exact presentation. -/
def twoCNFStructuredProblemAt : ProblemAt twoCNFStructuredPresentation where
  isYes := TwoCNF.CNF.Satisfiable

/-- A discoverable, user-locked V2 direct-2CNF SAT endpoint. -/
@[complexity_reduction_ir_typed_problem]
def twoCNFStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt twoCNFStructuredPresentation twoCNFStructuredProblemAt

@[simp]
theorem twoCNFStructuredProblem_representation :
    twoCNFStructuredProblem.representation = twoCNFStructuredPresentation :=
  rfl

@[simp]
theorem twoCNFStructuredProblem_backendEndpoint_instance :
    twoCNFStructuredProblem.backendEndpoint.Instance = twoCNFStructuredEncodedType :=
  rfl

@[simp]
theorem twoCNFStructuredProblem_representationIdentity :
    twoCNFStructuredProblem.representationIdentity = twoCNFStructuredShape.identity :=
  rfl

/-- The typed endpoint retains the exact direct 2CNF satisfiability semantics. -/
@[simp]
theorem twoCNFStructuredProblemAt_isYes (formula : twoCNFStructuredPresentation.Carrier) :
    twoCNFStructuredProblemAt.isYes formula ↔ TwoCNF.CNF.Satisfiable formula :=
  Iff.rfl

@[simp]
theorem twoCNFStructuredProblem_accepts (formula : twoCNFStructuredProblem.Instance) :
    twoCNFStructuredProblem.accepts formula ↔ TwoCNF.CNF.Satisfiable formula :=
  Iff.rfl

end SATTractable
end Karp21
end Problems
end ComplexityReduction
