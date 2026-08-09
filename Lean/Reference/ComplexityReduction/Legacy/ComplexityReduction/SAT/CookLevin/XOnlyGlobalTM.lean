import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalBaseTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitionsRowsTM

/-!
Direct standard-TM witness for the full x-only global tableau CNF.

The base rows and migrated transition rows are proved in separate files to keep
each layer below the file-size budget.  This file only assembles those witnesses.
-/

namespace ComplexityReduction
namespace SAT

theorem list_append_seven_flatMap_blocks
    {α : Type} (a b c d e f g : List α) :
    (a :: b :: c :: d :: e :: f :: g :: []).flatMap id =
      ((((((a ++ b) ++ c) ++ d) ++ e) ++ f) ++ g) := by
  simp [List.append_assoc]

theorem tmVerifierXOnlyGlobalTableauCNF_tm_polytime
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) :
    TMPolyTimeMap L.Instance cnfStructuredEncodedType
      (fun x : L.Instance.Carrier => tmVerifierXOnlyGlobalTableauCNF V B x) := by
  have hControlRows := tmVerifierXOnlyControlDomainRowsCNF_tm_polytime V
  have hInitialControl := tmVerifierInitialControlCNF_tm_polytime V
  have hInitialStack := tmVerifierXOnlyInitialStackCNF_tm_polytime V
  have hStackRows := tmVerifierXOnlyStackWellFormedRowsCNF_tm_polytime V
  have hMicroRows := tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_tm_polytime V
  have hTransitionRows := tmVerifierXOnlyTransitionFixedRowsCNF_tm_polytime V B
  have hEndpoint := tmVerifierXOnlyEndpointCNF_tm_polytime V
  have h12Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t,
            tmVerifierInitialControlCNF V)) :=
    TMPolyTimeMap.prod_mk hControlRows hInitialControl
  have h12 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h12Input
  have h123Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V,
            tmVerifierXOnlyInitialStackCNF V x)) :=
    TMPolyTimeMap.prod_mk h12 hInitialStack
  have h123 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h123Input
  have h1234Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x,
            tmVerifierXOnlyStackWellFormedRowsCNF V x)) :=
    TMPolyTimeMap.prod_mk h123 hStackRows
  have h1234 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h1234Input
  have h12345Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x) ++
            tmVerifierXOnlyStackWellFormedRowsCNF V x,
            tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x)) :=
    TMPolyTimeMap.prod_mk h1234 hMicroRows
  have h12345 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h12345Input
  have h123456Input :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          ((((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x) ++
            tmVerifierXOnlyStackWellFormedRowsCNF V x) ++
            tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x,
            tmVerifierXOnlyTransitionFixedRowsCNF V B x)) :=
    TMPolyTimeMap.prod_mk h12345 hTransitionRows
  have h123456 := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) h123456Input
  have hAllInput :
      TMPolyTimeMap L.Instance
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun x : L.Instance.Carrier =>
          (((((((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t =>
              tmVerifierControlDomainCNFAt V t) ++
            tmVerifierInitialControlCNF V) ++
            tmVerifierXOnlyInitialStackCNF V x) ++
            tmVerifierXOnlyStackWellFormedRowsCNF V x) ++
            tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x) ++
            tmVerifierXOnlyTransitionFixedRowsCNF V B x,
            tmVerifierXOnlyEndpointCNF V x)) :=
    TMPolyTimeMap.prod_mk h123456 hEndpoint
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAllInput
  convert hAll using 1
  funext x
  exact list_append_seven_flatMap_blocks
    ((tmVerifierXOnlyTableauTimeRange V x).flatMap fun t => tmVerifierControlDomainCNFAt V t)
    (tmVerifierInitialControlCNF V)
    (tmVerifierXOnlyInitialStackCNF V x)
    (tmVerifierXOnlyStackWellFormedRowsCNF V x)
    (tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF V x)
    (tmVerifierXOnlyTransitionFixedRowsCNF V B x)
    (tmVerifierXOnlyEndpointCNF V x)

end SAT
end ComplexityReduction
