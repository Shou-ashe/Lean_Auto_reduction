/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1
import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.BoolBridge
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.FiniteDomainCSP
import ComplexityReduction.Presentation.FiniteDomainCSPTable
import ComplexityReduction.Protocol.ComponentResolver

/-!
The canonical ingress from CR's Boolean finite-table CSP syntax to the generic
finite-domain CSP hub over `Bool`.

The table language is one concrete source presentation.  The target is the
same `FiniteDomainCSP` endpoint used by generic finite-domain CSP routes, so
future CSP hub gadgets are written once at that endpoint.  The bridge changes
only the relation-language view of formula constraints.  Its executable,
semantic law, and direct-TM proof are all indexed by this one ingress program.
-/

namespace ComplexityReduction
namespace Domain
namespace BoolTableCSPToFiniteDomainAdapter

open Certificate Encoding

noncomputable section

/-- The exact table-language source presentation for one Boolean CSP language. -/
abbrev sourceProblem (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : PresentedProblem :=
  Presentation.FiniteDomainCSPTable.presentedProblem Γ

/-- The canonical generic finite-domain CSP hub induced by the same table language. -/
abbrev hubProblem (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : PresentedProblem :=
  Presentation.FiniteDomainCSP.presentedProblem
    (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)

/-- The exact ingress request from a Boolean table CSP presentation to its generic CSP hub. -/
abbrev IngressRequest (source hub : PresentedProblem) : Type 2 :=
  Protocol.ComponentRequest .ingress source hub

/-- The only accepted ingress request is indexed by one selected table language. -/
def request (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    IngressRequest (sourceProblem Γ) (hubProblem Γ) :=
  .exact

/-- Reinterpret each table-language constraint as a finite-domain `Bool` constraint. -/
def ingressExecutable (Γ : Presentation.FiniteDomainCSPTable.TableLanguage)
    (input : (sourceProblem Γ).Instance) : (hubProblem Γ).Instance :=
  ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula input

private theorem ingressExecutable_encode (Γ : Presentation.FiniteDomainCSPTable.TableLanguage)
    (input : (sourceProblem Γ).Instance) :
    (hubProblem Γ).representation.encodedType.encode (ingressExecutable Γ input) =
      ((sourceProblem Γ).representation.encodedType.encode input).map id := by
  change Presentation.FiniteDomainCSP.formulaCodeEncodedType.encode
      (Presentation.FiniteDomainCSP.formulaCode
        (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)
        (ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula input)) =
    (Presentation.FiniteDomainCSPTable.formulaCodeEncodedType.encode
      (Presentation.FiniteDomainCSPTable.formulaCode Γ input)).map id
  rw [List.map_id]
  have hCode :
      Presentation.FiniteDomainCSP.formulaCode
          (ComplexityReduction.CSP.FiniteDomain.BoolBridge.languageOfBoolLanguage Γ)
          (ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula input) =
        Presentation.FiniteDomainCSPTable.formulaCode Γ input := by
    simp only [Presentation.FiniteDomainCSP.formulaCode,
      Presentation.FiniteDomainCSPTable.formulaCode,
      ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula, List.map_map]
    apply List.map_congr_left
    intro constraint _
    rfl
  exact congrArg Presentation.FiniteDomainCSP.formulaCodeEncodedType.encode hCode

private noncomputable def ingressTMBacked (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    ComplexityReduction.TMBackedCostedMap
      (sourceProblem Γ).representation.encodedType
      (hubProblem Γ).representation.encodedType
      (ingressExecutable Γ) :=
  ComplexityReduction.TMBackedCostedMap.ofEncodingEquiv
    (sourceProblem Γ).representation.encodedType
    (hubProblem Γ).representation.encodedType
    (ingressExecutable Γ)
    (Equiv.refl (sourceProblem Γ).representation.encodedType.Symbol)
    (by
      intro input
      change (hubProblem Γ).representation.encodedType.encode (ingressExecutable Γ input) =
        ((sourceProblem Γ).representation.encodedType.encode input).map id
      exact ingressExecutable_encode Γ input)

/-- Direct-TM evidence for the exact Boolean-table-to-finite-domain ingress executable. -/
theorem ingressExecutable_tmPolyTime (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    ComplexityReduction.TMPolyTimeMap
      (sourceProblem Γ).representation.encodedType
      (hubProblem Γ).representation.encodedType
      (ingressExecutable Γ) :=
  (ingressTMBacked Γ).tm_polytime

/-- The one direct-TM-backed atom required by this concrete source normalization. -/
noncomputable def ingressPrimitive (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    Program.Primitive (sourceProblem Γ).representation (hubProblem Γ).representation :=
  Program.Primitive.ofTMPolyTime (ingressExecutable Γ) (ingressExecutable_tmPolyTime Γ)

/-- The canonical table-CSP ingress program contains exactly its direct-TM-backed atom. -/
noncomputable def ingressProgram (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    Program.PolyProg (sourceProblem Γ).representation (hubProblem Γ).representation :=
  .atom (ingressPrimitive Γ)

@[simp] theorem ingressProgram_run (Γ : Presentation.FiniteDomainCSPTable.TableLanguage)
    (input : (sourceProblem Γ).Instance) :
    (ingressProgram Γ).run input = ingressExecutable Γ input :=
  rfl

/-- The bridge preserves Boolean table-CSP satisfiability at the canonical generic CSP hub. -/
theorem ingressProgram_correct (Γ : Presentation.FiniteDomainCSPTable.TableLanguage)
    (input : (sourceProblem Γ).Instance) :
    (sourceProblem Γ).accepts input ↔ (hubProblem Γ).accepts ((ingressProgram Γ).run input) := by
  change ComplexityReduction.CSP.Formula.Satisfiable input ↔
    ComplexityReduction.CSP.FiniteDomain.Formula.Satisfiable (ingressExecutable Γ input)
  exact (ComplexityReduction.CSP.FiniteDomain.BoolBridge.formulaOfBoolFormula_satisfiable_iff
    input).symm

/-- The authoritative program-indexed Boolean table-CSP ingress certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_ingress]
noncomputable def sourceAdapter (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    CertifiedReduction (sourceProblem Γ) (hubProblem Γ) where
  program := ingressProgram Γ
  correct := ingressProgram_correct Γ

@[simp] theorem sourceAdapter_program (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (sourceAdapter Γ).program = ingressProgram Γ :=
  rfl

@[simp] theorem sourceAdapter_directTM (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    (sourceAdapter Γ).directTM = (ingressProgram Γ).compileTM :=
  rfl

/-- Shared resolver outcome for the exact table-CSP ingress component. -/
abbrev Resolution (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Type 2 :=
  Protocol.ComponentResolution .ingress (sourceProblem Γ) (hubProblem Γ)

/-- Resolve the table source only through the same typed program-indexed ingress certificate. -/
noncomputable def resolve (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) : Resolution Γ :=
  Protocol.ComponentResolver.accept (request Γ) (sourceAdapter Γ)

@[simp] theorem resolve_exact (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    resolve Γ = .accepted (sourceAdapter Γ) :=
  rfl

theorem resolve_accepted_endpoint (Γ : Presentation.FiniteDomainCSPTable.TableLanguage) :
    match resolve Γ with
    | .accepted certificate => certificate.program = ingressProgram Γ
    | .blocked _ => False :=
  rfl

end
end BoolTableCSPToFiniteDomainAdapter
end Domain
end ComplexityReduction
