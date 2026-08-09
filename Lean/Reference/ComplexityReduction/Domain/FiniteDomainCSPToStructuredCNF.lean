/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.FiniteDomainCSPToStructuredCNFSemantics
import ComplexityReduction.Protocol.ComponentResolver

/-!
Accepted contract-bearing generic finite-domain CSP to structured CNF gadget.

The executable contract is an explicit input to every exported capability.
This leaf therefore closes only the contract-indexed endpoint; it does not
derive relation tables from a bare proposition-valued finite-domain language
and does not alter any bare-language resolver.
-/

namespace ComplexityReduction
namespace Domain
namespace FiniteDomainCSPToStructuredCNF

open Certificate Encoding
open FiniteDomainCSPExecutableContract
open FiniteDomainCSPToStructuredCNFProgram

noncomputable section

/-- Exact generic finite-domain CSP endpoint selected by the contract. -/
abbrev sourceProblem {D : Type} (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    PresentedProblem :=
  FiniteDomainCSPToStructuredCNFProgram.sourceProblem Γ

/-- Canonical structured CNF-SAT target endpoint. -/
abbrev targetProblem : PresentedProblem :=
  FiniteDomainCSPToStructuredCNFProgram.targetProblem

/-- Contract-indexed exact shared gadget backed by the one checked program. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    CertifiedReduction (sourceProblem Γ) targetProblem where
  program := formulaToCNFProgram contract
  correct := by
    intro formula
    change ComplexityReduction.CSP.FiniteDomain.Formula.Satisfiable formula ↔
      ComplexityReduction.SAT.CNF.Satisfiable (formulaToCNF contract formula)
    exact
      (FiniteDomainCSPToStructuredCNFSemantics.formulaToCNF_satisfiable_iff
        contract formula).symm

/-- The certificate stores exactly the program proved correct by the semantic leaf. -/
@[simp]
theorem sharedGadget_program {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    (sharedGadget contract).program = formulaToCNFProgram contract :=
  rfl

/-- Runtime behavior is exactly the contract-bearing one-hot transducer. -/
@[simp]
theorem sharedGadget_run {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (sourceProblem Γ).Instance) :
    (sharedGadget contract).program.run formula = formulaToCNF contract formula :=
  rfl

/-- Semantic correctness is projected from the certificate's one stored program. -/
theorem sharedGadget_correct {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ)
    (formula : (sourceProblem Γ).Instance) :
    (sourceProblem Γ).accepts formula ↔
      targetProblem.accepts ((sharedGadget contract).program.run formula) :=
  (sharedGadget contract).correct formula

/-- The direct TM is definitionally the checked program leaf's exact witness. -/
@[simp]
theorem sharedGadget_directTM {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    (sharedGadget contract).directTM = formulaToCNF_tmPolyTime contract :=
  rfl

/-- The direct TM remains the compiler output of the same stored program. -/
@[simp]
theorem sharedGadget_directTM_eq_compileTM {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    (sharedGadget contract).directTM = (sharedGadget contract).program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM (sharedGadget contract)

/-- Exact shared-component request at the contract's fixed source language. -/
abbrev SharedGadgetRequest {D : Type}
    (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) : Type 2 :=
  Protocol.ComponentRequest .sharedGadget (sourceProblem Γ) targetProblem

/-- The request fixes the exact generic CSP and structured CNF presentations. -/
def request {D : Type} (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    SharedGadgetRequest Γ :=
  .exact

/-- The request retains the exact language-indexed CSP and structured-CNF endpoints. -/
@[simp]
theorem request_endpoint_exact {D : Type}
    (Γ : ComplexityReduction.CSP.FiniteDomain.Language D) :
    (request Γ).endpoint =
      (show Protocol.ComponentEndpoint .sharedGadget (sourceProblem Γ) targetProblem from
        .exact) :=
  rfl

/-- Accepted resolution exists only after an explicit executable contract is supplied. -/
noncomputable def resolution {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    Protocol.ComponentResolution .sharedGadget (sourceProblem Γ) targetProblem :=
  Protocol.ComponentResolver.accept (request Γ) (sharedGadget contract)

@[simp]
theorem resolution_exact {D : Type}
    {Γ : ComplexityReduction.CSP.FiniteDomain.Language D}
    (contract : ExecutableLanguageContract Γ) :
    resolution contract = .accepted (sharedGadget contract) :=
  rfl

end
end FiniteDomainCSPToStructuredCNF
end Domain
end ComplexityReduction
