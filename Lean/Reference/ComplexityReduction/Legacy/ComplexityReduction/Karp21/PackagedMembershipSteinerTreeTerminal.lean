/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTreePathEntry

/-!
Terminal-list scanner for faithful structured Steiner Tree certificates.

The certificate supplies a root and a table of `(terminal, path)` entries.
Scanning the input terminal list checks that the first terminal is that root and
that every terminal is an endpoint of the selected edge set with a certified
path from the root.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

namespace SteinerTreeMembership

def steinerTerminalScanContextEncodedType : EncodedType :=
  EncodedType.prod
    (EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool)
    (EncodedType.prod EncodedType.nat steinerPathEntryListEncodedType)

abbrev SteinerTerminalScanContext :=
  (List (Nat × Nat × Nat) × Bool) × (Nat × List SteinerPathEntry)

def steinerTerminalScanAccEncodedType : EncodedType :=
  EncodedType.prod steinerTerminalScanContextEncodedType
    (EncodedType.prod EncodedType.bool EncodedType.bool)

abbrev SteinerTerminalScanAcc :=
  SteinerTerminalScanContext × (Bool × Bool)

def steinerTerminalScanInstructionEncodedType : EncodedType :=
  EncodedType.sum steinerTerminalScanContextEncodedType EncodedType.nat

def steinerTerminalScanInstructionListEncodedType : EncodedType :=
  EncodedType.list steinerTerminalScanInstructionEncodedType

def steinerTerminalScanInputEncodedType : EncodedType :=
  EncodedType.prod steinerTerminalScanContextEncodedType (EncodedType.list EncodedType.nat)

def steinerTerminalScanContext.selected (ctx : SteinerTerminalScanContext) :
    List (Nat × Nat × Nat) := ctx.1.1

def steinerTerminalScanContext.directed (ctx : SteinerTerminalScanContext) : Bool := ctx.1.2

def steinerTerminalScanContext.root (ctx : SteinerTerminalScanContext) : Nat := ctx.2.1

def steinerTerminalScanContext.entries (ctx : SteinerTerminalScanContext) :
    List SteinerPathEntry := ctx.2.2

def steinerTerminalCoverageBool (p : SteinerTerminalScanContext × Nat) : Bool :=
  let ctx := p.1
  let t := p.2
  graphBoolAndPair
    (weightedEndpointInListBool (t, steinerTerminalScanContext.selected ctx),
      pathEntryExistsBool
        ((((steinerTerminalScanContext.selected ctx, steinerTerminalScanContext.directed ctx),
            (steinerTerminalScanContext.root ctx, t))),
          steinerTerminalScanContext.entries ctx))

def steinerTerminalRootOKBool (p : SteinerTerminalScanContext × (Bool × Nat)) : Bool :=
  graphBoolOrPair (p.2.1, natEqBool (steinerTerminalScanContext.root p.1, p.2.2))

def steinerTerminalElementAcc (p : SteinerTerminalScanAcc × Nat) :
    SteinerTerminalScanAcc :=
  let ctx := p.1.1
  let seen := p.1.2.1
  let ok := p.1.2.2
  let t := p.2
  let rootOK := steinerTerminalRootOKBool (ctx, (seen, t))
  let coverage := steinerTerminalCoverageBool (ctx, t)
  (ctx, (true, graphBoolAndPair (ok, graphBoolAndPair (rootOK, coverage))))

def steinerTerminalScanRunnerInit : SteinerTerminalScanAcc :=
  ((((([] : List (Nat × Nat × Nat)), false), ((0 : Nat), ([] : List SteinerPathEntry))) :
    SteinerTerminalScanContext), (false, true))

def steinerTerminalScanInitInstruction
    (ctx : SteinerTerminalScanContext) : steinerTerminalScanInstructionEncodedType.Carrier :=
  Sum.inl ctx

def steinerTerminalScanElementInstruction
    (t : Nat) : steinerTerminalScanInstructionEncodedType.Carrier :=
  Sum.inr t

def steinerTerminalScanInstructions
    (p : SteinerTerminalScanContext × List Nat) :
    List steinerTerminalScanInstructionEncodedType.Carrier :=
  steinerTerminalScanInitInstruction p.1 :: p.2.map steinerTerminalScanElementInstruction

def steinerTerminalScanStep
    (p : SteinerTerminalScanAcc × steinerTerminalScanInstructionEncodedType.Carrier) :
    SteinerTerminalScanAcc :=
  match p.2 with
  | Sum.inl ctx => (ctx, (false, true))
  | Sum.inr t => steinerTerminalElementAcc (p.1, t)

def steinerTerminalScanFromInstructions
    (xs : List steinerTerminalScanInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => steinerTerminalScanStep (acc, instr))
    steinerTerminalScanRunnerInit).2.2

def steinerTerminalScanBool (p : SteinerTerminalScanContext × List Nat) : Bool :=
  steinerTerminalScanFromInstructions (steinerTerminalScanInstructions p)

theorem steinerTerminalCoverageBool_eq_true_iff
    (ctx : SteinerTerminalScanContext) (t : Nat) :
    steinerTerminalCoverageBool (ctx, t) = true ↔
      (∃ e ∈ steinerTerminalScanContext.selected ctx, WeightedEdgeHasEndpoint e t) ∧
        ∃ entry ∈ steinerTerminalScanContext.entries ctx,
          entry.1 = t ∧
            steinerPathBool
              ((((steinerTerminalScanContext.selected ctx,
                  steinerTerminalScanContext.directed ctx),
                (steinerTerminalScanContext.root ctx, t))), entry.2) = true := by
  rw [steinerTerminalCoverageBool, graphBoolAndPair_eq_true_iff,
    weightedEndpointInListBool_eq_true_iff, pathEntryExistsBool_eq_true_iff]
  constructor
  · rintro ⟨hEndpoint, hEntry⟩
    refine ⟨hEndpoint, ?_⟩
    rcases hEntry with ⟨entry, hEntryMem, hEntryOK⟩
    rcases (steinerPathEntryCheckBool_eq_true_iff
        (((steinerTerminalScanContext.selected ctx, steinerTerminalScanContext.directed ctx),
            (steinerTerminalScanContext.root ctx, t)), entry)).1 hEntryOK with
      ⟨hTerm, hPath⟩
    exact ⟨entry, hEntryMem, hTerm, hPath⟩
  · rintro ⟨hEndpoint, hEntry⟩
    refine ⟨hEndpoint, ?_⟩
    rcases hEntry with ⟨entry, hEntryMem, hTerm, hPath⟩
    exact ⟨entry, hEntryMem, (steinerPathEntryCheckBool_eq_true_iff
      (((steinerTerminalScanContext.selected ctx, steinerTerminalScanContext.directed ctx),
        (steinerTerminalScanContext.root ctx, t)), entry)).2 ⟨hTerm, hPath⟩⟩

theorem steinerTerminalRootOKBool_eq_true_iff
    (ctx : SteinerTerminalScanContext) (seen : Bool) (t : Nat) :
    steinerTerminalRootOKBool (ctx, (seen, t)) = true ↔
      seen = true ∨ steinerTerminalScanContext.root ctx = t := by
  cases seen <;>
    simp [steinerTerminalRootOKBool, graphBoolOrPair_eq_true_iff, natEqBool_eq_true_iff]

theorem steinerTerminalElementAcc_ok_eq_true_iff
    (ctx : SteinerTerminalScanContext) (seen ok : Bool) (t : Nat) :
    (steinerTerminalElementAcc ((ctx, (seen, ok)), t)).2.2 = true ↔
      ok = true ∧
        steinerTerminalRootOKBool (ctx, (seen, t)) = true ∧
        steinerTerminalCoverageBool (ctx, t) = true := by
  simp [steinerTerminalElementAcc, graphBoolAndPair_eq_true_iff]

theorem steinerTerminalElementInstructions_initial_ok
    (ctx : SteinerTerminalScanContext) :
    ∀ (terminals : List Nat) (seen ok : Bool),
      ((terminals.map steinerTerminalScanElementInstruction).foldl
          (fun acc instr => steinerTerminalScanStep (acc, instr))
          (ctx, (seen, ok))).2.2 = true →
        ok = true
  | [], _seen, ok, h => by simpa using h
  | t :: rest, seen, ok, h => by
      rw [List.map_cons, List.foldl_cons] at h
      have hNext :=
        steinerTerminalElementInstructions_initial_ok ctx rest true
          (steinerTerminalElementAcc ((ctx, (seen, ok)), t)).2.2 h
      rcases (steinerTerminalElementAcc_ok_eq_true_iff ctx seen ok t).1 hNext with
        ⟨hok, _hRoot, _hCoverage⟩
      exact hok

theorem steinerTerminalElementInstructions_coverage
    (ctx : SteinerTerminalScanContext) :
    ∀ (terminals : List Nat) (seen ok : Bool),
      ((terminals.map steinerTerminalScanElementInstruction).foldl
          (fun acc instr => steinerTerminalScanStep (acc, instr))
          (ctx, (seen, ok))).2.2 = true →
        ∀ t ∈ terminals, steinerTerminalCoverageBool (ctx, t) = true
  | [], _seen, _ok, _h, t, ht => by simp at ht
  | t :: rest, seen, ok, h, u, hu => by
      rw [List.map_cons, List.foldl_cons] at h
      have hNextOK :=
        steinerTerminalElementInstructions_initial_ok ctx rest true
          (steinerTerminalElementAcc ((ctx, (seen, ok)), t)).2.2 h
      have hTail :=
        steinerTerminalElementInstructions_coverage ctx rest true
          (steinerTerminalElementAcc ((ctx, (seen, ok)), t)).2.2 h
      rcases (steinerTerminalElementAcc_ok_eq_true_iff ctx seen ok t).1 hNextOK with
        ⟨_hok, _hRoot, hCoverage⟩
      rcases List.mem_cons.mp hu with hHead | hRest
      · subst u
        exact hCoverage
      · exact hTail u hRest

theorem steinerTerminalElementInstructions_first_root
    (ctx : SteinerTerminalScanContext) (first : Nat) (rest : List Nat) :
    ((first :: rest).map steinerTerminalScanElementInstruction).foldl
        (fun acc instr => steinerTerminalScanStep (acc, instr))
        (ctx, (false, true)) |>.2.2 = true →
      steinerTerminalScanContext.root ctx = first := by
  intro h
  rw [List.map_cons, List.foldl_cons] at h
  have hNextOK :=
    steinerTerminalElementInstructions_initial_ok ctx rest true
      (steinerTerminalElementAcc ((ctx, (false, true)), first)).2.2 h
  rcases (steinerTerminalElementAcc_ok_eq_true_iff ctx false true first).1 hNextOK with
    ⟨_hok, hRootOK, _hCoverage⟩
  exact (steinerTerminalRootOKBool_eq_true_iff ctx false first).1 hRootOK |>.resolve_left
    (by simp)

theorem steinerTerminalScanBool_sound
    (ctx : SteinerTerminalScanContext) (terminals : List Nat)
    (hScan : steinerTerminalScanBool (ctx, terminals) = true) :
    (terminals = [] ∨ steinerTerminalScanContext.root ctx ∈ terminals.head?) ∧
      ∀ t ∈ terminals,
        (∃ e ∈ steinerTerminalScanContext.selected ctx, WeightedEdgeHasEndpoint e t) ∧
          WeightedReachable (steinerTerminalScanContext.selected ctx)
            (steinerTerminalScanContext.directed ctx)
            (steinerTerminalScanContext.root ctx) t := by
  rcases terminals with _ | ⟨first, rest⟩
  · simp
  · have hFold :
        (((first :: rest).map steinerTerminalScanElementInstruction).foldl
          (fun acc instr => steinerTerminalScanStep (acc, instr))
          (ctx, (false, true))).2.2 = true := by
        simpa [steinerTerminalScanBool, steinerTerminalScanFromInstructions,
          steinerTerminalScanInstructions, steinerTerminalScanInitInstruction,
          steinerTerminalScanRunnerInit, steinerTerminalScanStep] using hScan
    have hRoot := steinerTerminalElementInstructions_first_root ctx first rest hFold
    refine ⟨Or.inr ?_, ?_⟩
    · simp [hRoot]
    · intro t ht
      have hCoverage :=
        steinerTerminalElementInstructions_coverage ctx (first :: rest) false true hFold t ht
      rcases (steinerTerminalCoverageBool_eq_true_iff ctx t).1 hCoverage with
        ⟨hEndpoint, entry, hEntryMem, hEntryTerm, hPath⟩
      subst t
      exact ⟨hEndpoint, weightedReachable_of_steinerPathBool hPath⟩

theorem steinerTerminalElementInstructions_complete_seen
    (ctx : SteinerTerminalScanContext) :
    ∀ terminals : List Nat,
      (∀ t ∈ terminals, steinerTerminalCoverageBool (ctx, t) = true) →
        ((terminals.map steinerTerminalScanElementInstruction).foldl
          (fun acc instr => steinerTerminalScanStep (acc, instr))
          (ctx, (true, true))).2.2 = true
  | [], _hCoverage => by
      simp
  | t :: rest, hCoverage => by
      rw [List.map_cons, List.foldl_cons]
      have hRootOK : steinerTerminalRootOKBool (ctx, (true, t)) = true :=
        (steinerTerminalRootOKBool_eq_true_iff ctx true t).2 (Or.inl rfl)
      have hCov : steinerTerminalCoverageBool (ctx, t) = true :=
        hCoverage t (by simp)
      have hStep :
          steinerTerminalElementAcc ((ctx, (true, true)), t) = (ctx, (true, true)) := by
        simp [steinerTerminalElementAcc, hRootOK, hCov, graphBoolAndPair]
      have hStepScan :
          steinerTerminalScanStep ((ctx, (true, true)), steinerTerminalScanElementInstruction t) =
            (ctx, (true, true)) := by
        simpa [steinerTerminalScanStep, steinerTerminalScanElementInstruction] using hStep
      have hRest :
          ∀ u ∈ rest, steinerTerminalCoverageBool (ctx, u) = true := by
        intro u hu
        exact hCoverage u (List.mem_cons_of_mem t hu)
      simpa [hStepScan] using
        steinerTerminalElementInstructions_complete_seen ctx rest hRest

theorem steinerTerminalElementInstructions_complete
    (ctx : SteinerTerminalScanContext) (first : Nat) (rest : List Nat)
    (hRoot : steinerTerminalScanContext.root ctx = first)
    (hCoverage : ∀ t ∈ first :: rest, steinerTerminalCoverageBool (ctx, t) = true) :
    (((first :: rest).map steinerTerminalScanElementInstruction).foldl
      (fun acc instr => steinerTerminalScanStep (acc, instr))
      (ctx, (false, true))).2.2 = true := by
  rw [List.map_cons, List.foldl_cons]
  have hRootOK : steinerTerminalRootOKBool (ctx, (false, first)) = true :=
    (steinerTerminalRootOKBool_eq_true_iff ctx false first).2 (Or.inr hRoot)
  have hCov : steinerTerminalCoverageBool (ctx, first) = true :=
    hCoverage first (by simp)
  have hStep :
      steinerTerminalElementAcc ((ctx, (false, true)), first) = (ctx, (true, true)) := by
    simp [steinerTerminalElementAcc, hRootOK, hCov, graphBoolAndPair]
  have hStepScan :
      steinerTerminalScanStep ((ctx, (false, true)), steinerTerminalScanElementInstruction first) =
        (ctx, (true, true)) := by
    simpa [steinerTerminalScanStep, steinerTerminalScanElementInstruction] using hStep
  have hRest : ∀ u ∈ rest, steinerTerminalCoverageBool (ctx, u) = true := by
    intro u hu
    exact hCoverage u (List.mem_cons_of_mem first hu)
  simpa [hStepScan] using
    steinerTerminalElementInstructions_complete_seen ctx rest hRest

theorem steinerTerminalScanBool_complete
    (ctx : SteinerTerminalScanContext) (terminals : List Nat)
    (hRoot : terminals = [] ∨ steinerTerminalScanContext.root ctx ∈ terminals.head?)
    (hCoverage : ∀ t ∈ terminals, steinerTerminalCoverageBool (ctx, t) = true) :
    steinerTerminalScanBool (ctx, terminals) = true := by
  rcases terminals with _ | ⟨first, rest⟩
  · simp [steinerTerminalScanBool, steinerTerminalScanFromInstructions,
      steinerTerminalScanInstructions, steinerTerminalScanInitInstruction,
      steinerTerminalScanRunnerInit, steinerTerminalScanStep]
  · have hRootEq : steinerTerminalScanContext.root ctx = first := by
      rcases hRoot with hNil | hHead
      · simp at hNil
      · simpa using hHead.symm
    have hFold :=
      steinerTerminalElementInstructions_complete ctx first rest hRootEq hCoverage
    simpa [steinerTerminalScanBool, steinerTerminalScanFromInstructions,
      steinerTerminalScanInstructions, steinerTerminalScanInitInstruction,
      steinerTerminalScanRunnerInit, steinerTerminalScanStep] using hFold

theorem steinerTerminalCoverageBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTerminalScanContextEncodedType EncodedType.nat)
      EncodedType.bool
      steinerTerminalCoverageBool := by
  let X := EncodedType.prod steinerTerminalScanContextEncodedType EncodedType.nat
  let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
  let CertCtx := EncodedType.prod EncodedType.nat steinerPathEntryListEncodedType
  let RootTarget := EncodedType.prod EncodedType.nat EncodedType.nat
  have hCtx :
      TMPolyTimeMap X steinerTerminalScanContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst steinerTerminalScanContextEncodedType EncodedType.nat
  have hTerminal : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd steinerTerminalScanContextEncodedType EncodedType.nat
  have hGraphCtx : TMPolyTimeMap X GraphCtx (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst GraphCtx CertCtx
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, steinerTerminalScanContextEncodedType, GraphCtx, CertCtx, X]
      using hComp
  have hSelected :
      TMPolyTimeMap X weightedEdgeListStructuredEncodedType (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hGraphCtx
    simpa [Function.comp, GraphCtx, X] using hComp
  have hDirected : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd weightedEdgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hGraphCtx
    simpa [Function.comp, GraphCtx, X] using hComp
  have hCertCtx : TMPolyTimeMap X CertCtx (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd GraphCtx CertCtx
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, steinerTerminalScanContextEncodedType, GraphCtx, CertCtx, X]
      using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat steinerPathEntryListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCertCtx
    simpa [Function.comp, CertCtx, X] using hComp
  have hEntries :
      TMPolyTimeMap X steinerPathEntryListEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat steinerPathEntryListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hCertCtx
    simpa [Function.comp, CertCtx, X] using hComp
  have hEndpointInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat weightedEdgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2, p.1.1.1)) :=
    TMPolyTimeMap.prod_mk hTerminal hSelected
  have hEndpoint : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => weightedEndpointInListBool (p.2, p.1.1.1)) := by
    have hComp := TMPolyTimeMap.comp weightedEndpointInListBool_tm_polytime hEndpointInput
    simpa [Function.comp, X] using hComp
  have hRootTarget : TMPolyTimeMap X RootTarget (fun p : X.Carrier => (p.1.2.1, p.2)) :=
    TMPolyTimeMap.prod_mk hRoot hTerminal
  have hPathContext :
      TMPolyTimeMap X steinerPathContextEncodedType
        (fun p : X.Carrier => ((p.1.1.1, p.1.1.2), (p.1.2.1, p.2))) := by
    have hGraphPair : TMPolyTimeMap X GraphCtx (fun p : X.Carrier => (p.1.1.1, p.1.1.2)) :=
      TMPolyTimeMap.prod_mk hSelected hDirected
    have hOut := TMPolyTimeMap.prod_mk hGraphPair hRootTarget
    simpa [steinerPathContextEncodedType, GraphCtx, RootTarget] using hOut
  have hEntryInput :
      TMPolyTimeMap X pathEntryExistsInputEncodedType
        (fun p : X.Carrier =>
          (((p.1.1.1, p.1.1.2), (p.1.2.1, p.2)), p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hPathContext hEntries
  have hEntriesOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        pathEntryExistsBool (((p.1.1.1, p.1.1.2), (p.1.2.1, p.2)), p.1.2.2)) := by
    have hComp := TMPolyTimeMap.comp pathEntryExistsBool_tm_polytime hEntryInput
    simpa [Function.comp, pathEntryExistsInputEncodedType, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (weightedEndpointInListBool (p.2, p.1.1.1),
            pathEntryExistsBool (((p.1.1.1, p.1.1.2), (p.1.2.1, p.2)), p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hEndpoint hEntriesOK
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, steinerTerminalCoverageBool, X] using hAnd

theorem steinerTerminalRootOKBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTerminalScanContextEncodedType
        (EncodedType.prod EncodedType.bool EncodedType.nat))
      EncodedType.bool
      steinerTerminalRootOKBool := by
  let Tail := EncodedType.prod EncodedType.bool EncodedType.nat
  let GraphCtx := EncodedType.prod weightedEdgeListStructuredEncodedType EncodedType.bool
  let CertCtx := EncodedType.prod EncodedType.nat steinerPathEntryListEncodedType
  let X := EncodedType.prod steinerTerminalScanContextEncodedType Tail
  have hCtx :
      TMPolyTimeMap X steinerTerminalScanContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, Tail] using TMPolyTimeMap.fst steinerTerminalScanContextEncodedType Tail
  have hTail : TMPolyTimeMap X Tail (fun p : X.Carrier => p.2) := by
    simpa [X, Tail] using TMPolyTimeMap.snd steinerTerminalScanContextEncodedType Tail
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, X] using hComp
  have hTerm : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, X] using hComp
  have hCertCtx : TMPolyTimeMap X CertCtx (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd GraphCtx CertCtx
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, steinerTerminalScanContextEncodedType, GraphCtx, CertCtx, X]
      using hComp
  have hRoot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat steinerPathEntryListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hCertCtx
    simpa [Function.comp, CertCtx, X] using hComp
  have hEqInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier => (p.1.2.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hRoot hTerm
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => natEqBool (p.1.2.1, p.2.2)) := by
    have hComp := TMPolyTimeMap.comp natEqBool_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  have hOrInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier => (p.2.1, natEqBool (p.1.2.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hSeen hEq
  have hOr := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime hOrInput
  simpa [Function.comp, steinerTerminalRootOKBool, X] using hOr

theorem steinerTerminalElementAcc_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTerminalScanAccEncodedType EncodedType.nat)
      steinerTerminalScanAccEncodedType
      steinerTerminalElementAcc := by
  let PairBool := EncodedType.prod EncodedType.bool EncodedType.bool
  let X := EncodedType.prod steinerTerminalScanAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X steinerTerminalScanAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst steinerTerminalScanAccEncodedType EncodedType.nat
  have hTerm : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd steinerTerminalScanAccEncodedType EncodedType.nat
  have hCtx : TMPolyTimeMap X steinerTerminalScanContextEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst steinerTerminalScanContextEncodedType PairBool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, steinerTerminalScanAccEncodedType, PairBool, X] using hComp
  have hTail : TMPolyTimeMap X PairBool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd steinerTerminalScanContextEncodedType PairBool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, steinerTerminalScanAccEncodedType, PairBool, X] using hComp
  have hSeen : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, PairBool, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, PairBool, X] using hComp
  have hRootInput :
      TMPolyTimeMap X
        (EncodedType.prod steinerTerminalScanContextEncodedType
          (EncodedType.prod EncodedType.bool EncodedType.nat))
        (fun p : X.Carrier => (p.1.1, (p.1.2.1, p.2))) := by
    have hSeenTerm :
        TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.nat)
          (fun p : X.Carrier => (p.1.2.1, p.2)) :=
      TMPolyTimeMap.prod_mk hSeen hTerm
    exact TMPolyTimeMap.prod_mk hCtx hSeenTerm
  have hRootOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp steinerTerminalRootOKBool_tm_polytime hRootInput
    simpa [Function.comp, X] using hComp
  have hCoverageInput :
      TMPolyTimeMap X
        (EncodedType.prod steinerTerminalScanContextEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hCtx hTerm
  have hCoverage : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => steinerTerminalCoverageBool (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp steinerTerminalCoverageBool_tm_polytime hCoverageInput
    simpa [Function.comp, X] using hComp
  have hInnerInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2)),
            steinerTerminalCoverageBool (p.1.1, p.2))) :=
    TMPolyTimeMap.prod_mk hRootOK hCoverage
  have hInner : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2)),
            steinerTerminalCoverageBool (p.1.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hInnerInput
    simpa [Function.comp, X] using hComp
  have hOuterInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2.2,
            graphBoolAndPair
              (steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2)),
                steinerTerminalCoverageBool (p.1.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hOk hInner
  have hNewOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2,
            graphBoolAndPair
              (steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2)),
                steinerTerminalCoverageBool (p.1.1, p.2)))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hOuterInput
    simpa [Function.comp, X] using hComp
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hTailOut :
      TMPolyTimeMap X PairBool
        (fun p : X.Carrier =>
          (true,
            graphBoolAndPair
              (p.1.2.2,
                graphBoolAndPair
                  (steinerTerminalRootOKBool (p.1.1, (p.1.2.1, p.2)),
                    steinerTerminalCoverageBool (p.1.1, p.2))))) :=
    TMPolyTimeMap.prod_mk hTrue hNewOK
  have hOut := TMPolyTimeMap.prod_mk hCtx hTailOut
  simpa [Function.comp, steinerTerminalElementAcc, PairBool, X] using hOut

theorem steinerTerminalScanInitInstruction_tm_polytime :
    TMPolyTimeMap steinerTerminalScanContextEncodedType
      steinerTerminalScanInstructionEncodedType
      steinerTerminalScanInitInstruction := by
  simpa [steinerTerminalScanInitInstruction, steinerTerminalScanInstructionEncodedType] using
    TMPolyTimeMap.inl steinerTerminalScanContextEncodedType EncodedType.nat

theorem steinerTerminalScanElementInstruction_tm_polytime :
    TMPolyTimeMap EncodedType.nat
      steinerTerminalScanInstructionEncodedType
      steinerTerminalScanElementInstruction := by
  simpa [steinerTerminalScanElementInstruction, steinerTerminalScanInstructionEncodedType] using
    TMPolyTimeMap.inr steinerTerminalScanContextEncodedType EncodedType.nat

theorem steinerTerminalScanInstructions_tm_polytime :
    TMPolyTimeMap steinerTerminalScanInputEncodedType
      steinerTerminalScanInstructionListEncodedType
      steinerTerminalScanInstructions := by
  let X := steinerTerminalScanInputEncodedType
  have hCtx : TMPolyTimeMap X steinerTerminalScanContextEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, steinerTerminalScanInputEncodedType] using
      TMPolyTimeMap.fst steinerTerminalScanContextEncodedType (EncodedType.list EncodedType.nat)
  have hTerms :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.2) := by
    simpa [X, steinerTerminalScanInputEncodedType] using
      TMPolyTimeMap.snd steinerTerminalScanContextEncodedType (EncodedType.list EncodedType.nat)
  have hInit :
      TMPolyTimeMap X steinerTerminalScanInstructionEncodedType
        (fun p : X.Carrier => steinerTerminalScanInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp steinerTerminalScanInitInstruction_tm_polytime hCtx
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X steinerTerminalScanInstructionListEncodedType
        (fun p : X.Carrier => [steinerTerminalScanInitInstruction p.1]) := by
    have hComp :=
      TMPolyTimeMap.comp
        (TMPolyTimeMap.list_singleton steinerTerminalScanInstructionEncodedType) hInit
    simpa [Function.comp, steinerTerminalScanInstructionListEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X steinerTerminalScanInstructionListEncodedType
        (fun p : X.Carrier => p.2.map steinerTerminalScanElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map steinerTerminalScanElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hTerms
    simpa [Function.comp, steinerTerminalScanInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod steinerTerminalScanInstructionListEncodedType
          steinerTerminalScanInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([steinerTerminalScanInitInstruction p.1],
            p.2.map steinerTerminalScanElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append steinerTerminalScanInstructionEncodedType) hAppendInput
  simpa [Function.comp, steinerTerminalScanInstructions,
    steinerTerminalScanInstructionListEncodedType, X] using hOut

theorem steinerTerminalScanStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod steinerTerminalScanAccEncodedType
        steinerTerminalScanInstructionEncodedType)
      steinerTerminalScanAccEncodedType
      steinerTerminalScanStep := by
  let A := steinerTerminalScanAccEncodedType
  let C := steinerTerminalScanContextEncodedType
  let Instr := steinerTerminalScanInstructionEncodedType
  have hFalse : TMPolyTimeMap C A (fun ctx : C.Carrier => (ctx, (false, true))) := by
    have hId : TMPolyTimeMap C C id := TMPolyTimeMap.id C
    have hFalse : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => false) :=
      TMPolyTimeMap.const C EncodedType.bool false
    have hTrue : TMPolyTimeMap C EncodedType.bool (fun _ : C.Carrier => true) :=
      TMPolyTimeMap.const C EncodedType.bool true
    have hTail :
        TMPolyTimeMap C (EncodedType.prod EncodedType.bool EncodedType.bool)
          (fun _ : C.Carrier => (false, true)) :=
      TMPolyTimeMap.prod_mk hFalse hTrue
    have hOut := TMPolyTimeMap.prod_mk hId hTail
    simpa [A, C, steinerTerminalScanAccEncodedType] using hOut
  have hTrue : TMPolyTimeMap (EncodedType.prod A EncodedType.nat) A
      (fun p : A.Carrier × Nat => steinerTerminalElementAcc (p.1, p.2)) := by
    simpa [A] using steinerTerminalElementAcc_tm_polytime
  have hChoice := Partition.prodSumChoice_tm_polytime A C EncodedType.nat
  have hBranches := Partition.TMPolyTimeMap.sum_elim hFalse hTrue
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem steinerTerminalScanStep_inputSize_le
    (K : Nat) (hK : 10 ≤ K)
    (source : steinerTerminalScanInstructionListEncodedType.Carrier)
    (acc : steinerTerminalScanAccEncodedType.Carrier)
    (instr : steinerTerminalScanInstructionEncodedType.Carrier)
    (hAcc :
      steinerTerminalScanAccEncodedType.inputSize acc ≤
        steinerTerminalScanInstructionListEncodedType.inputSize source + K)
    (hInstr :
      steinerTerminalScanInstructionEncodedType.inputSize instr ≤
        steinerTerminalScanInstructionListEncodedType.inputSize source) :
    steinerTerminalScanAccEncodedType.inputSize (steinerTerminalScanStep (acc, instr)) ≤
      steinerTerminalScanInstructionListEncodedType.inputSize source + K := by
  rcases acc with ⟨ctx, seen, ok⟩
  cases instr with
  | inl newCtx =>
      have hLocal :
          steinerTerminalScanAccEncodedType.inputSize (newCtx, (false, true)) ≤
            steinerTerminalScanInstructionEncodedType.inputSize (Sum.inl newCtx) + 10 := by
        simp [steinerTerminalScanAccEncodedType, steinerTerminalScanInstructionEncodedType,
          EncodedType.inputSize, EncodedType.prod, EncodedType.sum, EncodedType.bool]
      have hSource :
          steinerTerminalScanInstructionEncodedType.inputSize (Sum.inl newCtx) + 10 ≤
            steinerTerminalScanInstructionListEncodedType.inputSize source + K := by
        omega
      exact hLocal.trans hSource
  | inr t =>
      have hLocal :
          steinerTerminalScanAccEncodedType.inputSize
              (steinerTerminalElementAcc ((ctx, (seen, ok)), t)) ≤
            steinerTerminalScanAccEncodedType.inputSize (ctx, (seen, ok)) := by
        cases seen <;> cases ok <;>
          simp [steinerTerminalElementAcc, steinerTerminalScanAccEncodedType,
            EncodedType.inputSize, EncodedType.prod, EncodedType.bool]
      exact hLocal.trans hAcc

theorem steinerTerminalScanFold_tm_polytime :
    TMPolyTimeMap
      steinerTerminalScanInstructionListEncodedType
      steinerTerminalScanAccEncodedType
      (fun xs : steinerTerminalScanInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => steinerTerminalScanStep (acc, instr))
          steinerTerminalScanRunnerInit) := by
  rcases steinerTerminalScanStep_tm_polytime with ⟨hStep⟩
  let K : Nat := steinerTerminalScanAccEncodedType.inputSize steinerTerminalScanRunnerInit + 10
  let bound : Polynomial Nat := Polynomial.X + Polynomial.C K
  refine
    TMPolyTimeMap.list_foldl_typed_bounded
      steinerTerminalScanInstructionEncodedType
      steinerTerminalScanAccEncodedType
      steinerTerminalScanStep steinerTerminalScanRunnerInit hStep bound ?_ ?_
  · intro xs
    change steinerTerminalScanAccEncodedType.inputSize steinerTerminalScanRunnerInit ≤
      (Polynomial.X + Polynomial.C K).eval
        (steinerTerminalScanInstructionEncodedType.list.inputSize xs)
    simp [Polynomial.eval_add]
    omega
  · intro source acc instr hAcc hInstr
    have hAcc' :
        steinerTerminalScanAccEncodedType.inputSize acc ≤
          steinerTerminalScanInstructionListEncodedType.inputSize source + K := by
      simpa [steinerTerminalScanInstructionListEncodedType, bound, Polynomial.eval_add] using hAcc
    have hInstr' :
        steinerTerminalScanInstructionEncodedType.inputSize instr ≤
          steinerTerminalScanInstructionListEncodedType.inputSize source := by
      simpa [steinerTerminalScanInstructionListEncodedType] using hInstr
    simpa [steinerTerminalScanInstructionListEncodedType, bound, Polynomial.eval_add] using
      steinerTerminalScanStep_inputSize_le K (by omega) source acc instr hAcc' hInstr'

theorem steinerTerminalScanFromInstructions_tm_polytime :
    TMPolyTimeMap
      steinerTerminalScanInstructionListEncodedType
      EncodedType.bool
      steinerTerminalScanFromInstructions := by
  let Tail := EncodedType.prod EncodedType.bool EncodedType.bool
  have hFold := steinerTerminalScanFold_tm_polytime
  have hTail : TMPolyTimeMap steinerTerminalScanAccEncodedType Tail
      (fun acc : steinerTerminalScanAccEncodedType.Carrier => acc.2) := by
    simpa [steinerTerminalScanAccEncodedType, Tail] using
      TMPolyTimeMap.snd steinerTerminalScanContextEncodedType Tail
  have hOKTail : TMPolyTimeMap Tail EncodedType.bool (fun p : Tail.Carrier => p.2) := by
    simpa [Tail] using TMPolyTimeMap.snd EncodedType.bool EncodedType.bool
  have hOK := TMPolyTimeMap.comp hOKTail hTail
  have hComp := TMPolyTimeMap.comp hOK hFold
  simpa [Function.comp, steinerTerminalScanFromInstructions, Tail] using hComp

theorem steinerTerminalScanBool_tm_polytime :
    TMPolyTimeMap steinerTerminalScanInputEncodedType EncodedType.bool
      steinerTerminalScanBool := by
  have hComp := TMPolyTimeMap.comp
    steinerTerminalScanFromInstructions_tm_polytime
    steinerTerminalScanInstructions_tm_polytime
  simpa [Function.comp, steinerTerminalScanBool] using hComp

end SteinerTreeMembership

end Karp21
end ComplexityReduction
