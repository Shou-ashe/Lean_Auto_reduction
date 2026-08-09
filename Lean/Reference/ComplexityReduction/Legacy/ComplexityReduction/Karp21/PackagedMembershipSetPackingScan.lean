/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetPackingEq
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SetPacking.Base
import Mathlib.Tactic

/-!
Direct standard-TM certificate scan for faithful structured Set Packing.

The certificate is a raw selected subfamily (`List (List Nat)`).  The scan keeps
the source family, previously selected sets, the concatenation of their
elements, and an accumulated Boolean flag.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace SetPackingMembership

abbrev setPackingCertificateEncodedType : EncodedType :=
  setFamilyStructuredEncodedType

abbrev setPackingScanAccEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType
    (EncodedType.prod setFamilyStructuredEncodedType
      (EncodedType.prod setStructuredEncodedType EncodedType.bool))

abbrev setPackingScanPayloadEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType

abbrev setPackingScanInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool setPackingScanPayloadEncodedType

abbrev setPackingScanInstructionListEncodedType : EncodedType :=
  EncodedType.list setPackingScanInstructionEncodedType

abbrev setPackingScanInputEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setFamilyStructuredEncodedType

abbrev SetPackingScanAccCarrier :=
  List (List Nat) × (List (List Nat) × (List Nat × Bool))

abbrev SetPackingScanStepCarrier :=
  SetPackingScanAccCarrier × setPackingScanInstructionEncodedType.Carrier

def setPackingScanRunnerInit : setPackingScanAccEncodedType.Carrier :=
  (([] : List (List Nat)), (([] : List (List Nat)), (([] : List Nat), false)))

def setPackingScanInitInstruction (source : List (List Nat)) :
    setPackingScanInstructionEncodedType.Carrier :=
  (false, (source, []))

def setPackingScanSetInstruction (S : List Nat) :
    setPackingScanInstructionEncodedType.Carrier :=
  (true, ([], S))

def setPackingScanInstructions (p : List (List Nat) × List (List Nat)) :
    List setPackingScanInstructionEncodedType.Carrier :=
  setPackingScanInitInstruction p.1 :: p.2.map setPackingScanSetInstruction

def setPackingLocalDisjointBool (S seenElems : List Nat) : Bool :=
  Bool.not (HittingSet.setHitBool (S, seenElems))

def setPackingLocalOKBool
    (source seenSets : List (List Nat)) (seenElems S : List Nat) : Bool :=
  graphBoolAndPair
    (setFamilyContainsBool (S, source),
      graphBoolAndPair
        (Bool.not (setFamilyContainsBool (S, seenSets)),
          setPackingLocalDisjointBool S seenElems))

def setPackingScanElementStep
    (acc : setPackingScanAccEncodedType.Carrier) (S : List Nat) :
    setPackingScanAccEncodedType.Carrier :=
  let source : List (List Nat) := acc.1
  let seenSets : List (List Nat) := acc.2.1
  let seenElems : List Nat := acc.2.2.1
  let ok : Bool := acc.2.2.2
  (source,
    (S :: seenSets,
      (S ++ seenElems,
        graphBoolAndPair (ok, setPackingLocalOKBool source seenSets seenElems S))))

def setPackingScanStep (p : SetPackingScanStepCarrier) :
    setPackingScanAccEncodedType.Carrier :=
  match p.2.1 with
  | true => setPackingScanElementStep p.1 p.2.2.2
  | false => (p.2.2.1, ([], ([], true)))

def setPackingScanFromInstructions
    (xs : List setPackingScanInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => setPackingScanStep (acc, instr))
    setPackingScanRunnerInit).2.2.2

def setPackingScanBool (p : List (List Nat) × List (List Nat)) : Bool :=
  setPackingScanFromInstructions (setPackingScanInstructions p)

def PackingScanOK
    (source seenSets : List (List Nat)) (seenElems : List Nat) :
    List (List Nat) → Prop
  | [] => True
  | S :: rest =>
      S ∈ source ∧
        S ∉ seenSets ∧
        (∀ x, x ∈ seenElems → x ∉ S) ∧
        PackingScanOK source (S :: seenSets) (S ++ seenElems) rest

theorem setPackingLocalDisjointBool_eq_true_iff (S seenElems : List Nat) :
    setPackingLocalDisjointBool S seenElems = true ↔
      ∀ x, x ∈ seenElems → x ∉ S := by
  constructor
  · intro h x hxSeen hxS
    have hHit : HittingSet.setHitBool (S, seenElems) = true :=
      (HittingSet.setHitBool_eq_true_iff (S, seenElems)).2 ⟨x, hxSeen, hxS⟩
    simp [setPackingLocalDisjointBool, hHit] at h
  · intro h
    cases hHit : HittingSet.setHitBool (S, seenElems)
    · simp [setPackingLocalDisjointBool, hHit]
    · rcases (HittingSet.setHitBool_eq_true_iff (S, seenElems)).1 hHit with
        ⟨x, hxSeen, hxS⟩
      exact False.elim (h x hxSeen hxS)

theorem setPackingLocalOKBool_eq_true_iff
    (source seenSets : List (List Nat)) (seenElems S : List Nat) :
    setPackingLocalOKBool source seenSets seenElems S = true ↔
      S ∈ source ∧ S ∉ seenSets ∧ ∀ x, x ∈ seenElems → x ∉ S := by
  rw [setPackingLocalOKBool, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, setFamilyContainsBool_eq_true_iff,
    setPackingLocalDisjointBool_eq_true_iff]
  constructor
  · rintro ⟨hFamily, hFreshBool, hDisjoint⟩
    refine ⟨hFamily, ?_, hDisjoint⟩
    intro hSeen
    have hContains : setFamilyContainsBool (S, seenSets) = true :=
      (setFamilyContainsBool_eq_true_iff S seenSets).2 hSeen
    simp [hContains] at hFreshBool
  · rintro ⟨hFamily, hFresh, hDisjoint⟩
    refine ⟨hFamily, ?_, hDisjoint⟩
    cases hContains : setFamilyContainsBool (S, seenSets)
    · simp
    · have hSeen : S ∈ seenSets :=
        (setFamilyContainsBool_eq_true_iff S seenSets).1 hContains
      exact False.elim (hFresh hSeen)

theorem setPackingScanElementInstructions_fold_iff
    (xs source seenSets : List (List Nat)) (seenElems : List Nat) (ok : Bool) :
    (((xs.map setPackingScanSetInstruction).foldl
        (fun acc instr => setPackingScanStep (acc, instr))
        (source, (seenSets, (seenElems, ok)))).2.2.2 = true) ↔
      ok = true ∧ PackingScanOK source seenSets seenElems xs := by
  induction xs generalizing seenSets seenElems ok with
  | nil =>
      cases ok <;> simp [PackingScanOK]
  | cons S rest ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((rest.map setPackingScanSetInstruction).foldl
            (fun acc instr => setPackingScanStep (acc, instr))
            (source,
              (S :: seenSets,
                (S ++ seenElems,
                  graphBoolAndPair
                    (ok, setPackingLocalOKBool source seenSets seenElems S))))).2.2.2 =
            true) ↔
          ok = true ∧ PackingScanOK source seenSets seenElems (S :: rest)
      rw [ih]
      simp [PackingScanOK, graphBoolAndPair_eq_true_iff,
        setPackingLocalOKBool_eq_true_iff, and_assoc]
      tauto

theorem setPackingScanBool_eq_true_iff
    (source cert : List (List Nat)) :
    setPackingScanBool (source, cert) = true ↔
      PackingScanOK source [] [] cert := by
  change
    (((setPackingScanInitInstruction source ::
      cert.map setPackingScanSetInstruction).foldl
        (fun acc instr => setPackingScanStep (acc, instr))
        setPackingScanRunnerInit).2.2.2 = true) ↔ _
  rw [List.foldl_cons]
  simpa [setPackingScanRunnerInit, setPackingScanInitInstruction, setPackingScanStep] using
    setPackingScanElementInstructions_fold_iff cert source [] [] true

theorem PackingScanOK.mem_family
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (h : PackingScanOK source seenSets seenElems xs) :
    ∀ S ∈ xs, S ∈ source := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      simp
  | cons S rest ih =>
      simp [PackingScanOK] at h
      rcases h with ⟨hFamily, _hFresh, _hDisjoint, hTail⟩
      intro A hA
      simp at hA
      rcases hA with rfl | hA
      · exact hFamily
      · exact ih hTail A hA

theorem PackingScanOK.seenSets_not_mem
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (h : PackingScanOK source seenSets seenElems xs) :
    ∀ S ∈ seenSets, S ∉ xs := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      simp
  | cons S rest ih =>
      simp [PackingScanOK] at h
      rcases h with ⟨_hFamily, hFresh, _hDisjoint, hTail⟩
      have hTailNo := ih hTail
      intro A hA hAxs
      simp at hAxs
      rcases hAxs with hEq | hRest
      · subst A
        exact hFresh hA
      · exact hTailNo A (by simp [hA]) hRest

theorem PackingScanOK.seenElems_not_mem
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (h : PackingScanOK source seenSets seenElems xs) :
    ∀ x ∈ seenElems, ∀ S ∈ xs, x ∉ S := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      simp
  | cons S rest ih =>
      simp [PackingScanOK] at h
      rcases h with ⟨_hFamily, _hFresh, hDisjoint, hTail⟩
      have hTailNo := ih hTail
      intro x hxSeen A hA hxA
      simp at hA
      rcases hA with rfl | hRest
      · exact hDisjoint x hxSeen hxA
      · exact hTailNo x (List.mem_append_right S hxSeen) A hRest hxA

theorem PackingScanOK.nodup
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (h : PackingScanOK source seenSets seenElems xs) :
    xs.Nodup := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      simp
  | cons S rest ih =>
      simp [PackingScanOK] at h
      rcases h with ⟨_hFamily, _hFresh, _hDisjoint, hTail⟩
      have hNoHead : S ∉ rest :=
        PackingScanOK.seenSets_not_mem hTail S (by simp)
      exact List.nodup_cons.mpr ⟨hNoHead, ih hTail⟩

theorem PackingScanOK.pairwiseDisjoint
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (h : PackingScanOK source seenSets seenElems xs) :
    PairwiseDisjointFamily xs := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      intro A hA
      simp at hA
  | cons S rest ih =>
      simp [PackingScanOK] at h
      rcases h with ⟨_hFamily, _hFresh, _hDisjoint, hTail⟩
      have hTailPair := ih hTail
      have hSeenTail := PackingScanOK.seenElems_not_mem hTail
      intro A hA B hB hNe x hxA hxB
      simp at hA hB
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact hNe rfl
      · exact hSeenTail x (List.mem_append_left seenElems hxA) B hB hxB
      · exact hSeenTail x (List.mem_append_left seenElems hxB) A hA hxA
      · exact hTailPair A hA B hB hNe x hxA hxB

theorem PackingScanOK.of_props_with_seen
    {source seenSets xs : List (List Nat)} {seenElems : List Nat}
    (hFamily : ∀ S ∈ xs, S ∈ source)
    (hSeenSets : ∀ S ∈ seenSets, S ∉ xs)
    (hSeenElems : ∀ x ∈ seenElems, ∀ S ∈ xs, x ∉ S)
    (hNodup : xs.Nodup)
    (hPairwise : PairwiseDisjointFamily xs) :
    PackingScanOK source seenSets seenElems xs := by
  induction xs generalizing seenSets seenElems with
  | nil =>
      simp [PackingScanOK]
  | cons S rest ih =>
      have hHeadFamily : S ∈ source := hFamily S (by simp)
      have hTailFamily : ∀ A ∈ rest, A ∈ source := by
        intro A hA
        exact hFamily A (by simp [hA])
      have hConsNodup : (S :: rest).Nodup := by simpa using hNodup
      rcases List.nodup_cons.mp hConsNodup with ⟨hHeadNotTail, hTailNodup⟩
      have hFreshSeen : S ∉ seenSets := by
        intro hSSeen
        exact hSeenSets S hSSeen (by simp)
      have hDisjointSeen : ∀ x, x ∈ seenElems → x ∉ S := by
        intro x hxSeen hxS
        exact hSeenElems x hxSeen S (by simp) hxS
      have hTailPair : PairwiseDisjointFamily rest := by
        intro A hA B hB hNe x hxA hxB
        exact hPairwise A (by simp [hA]) B (by simp [hB]) hNe x hxA hxB
      have hSeenSetsTail : ∀ A ∈ S :: seenSets, A ∉ rest := by
        intro A hA hATail
        simp at hA
        rcases hA with rfl | hA
        · exact hHeadNotTail hATail
        · exact hSeenSets A hA (by simp [hATail])
      have hSeenElemsTail :
          ∀ x ∈ S ++ seenElems, ∀ A ∈ rest, x ∉ A := by
        intro x hx A hA hxA
        rcases List.mem_append.mp hx with hxS | hxSeen
        · have hNe : S ≠ A := by
            intro hEq
            subst A
            exact hHeadNotTail hA
          exact hPairwise S (by simp) A (by simp [hA]) hNe x hxS hxA
        · exact hSeenElems x hxSeen A (by simp [hA]) hxA
      exact
        ⟨hHeadFamily, hFreshSeen, hDisjointSeen,
          ih hTailFamily hSeenSetsTail hSeenElemsTail hTailNodup hTailPair⟩

theorem PackingScanOK.of_props
    {source xs : List (List Nat)}
    (hFamily : ∀ S ∈ xs, S ∈ source)
    (hNodup : xs.Nodup)
    (hPairwise : PairwiseDisjointFamily xs) :
    PackingScanOK source [] [] xs := by
  exact PackingScanOK.of_props_with_seen hFamily (by simp) (by simp) hNodup hPairwise

theorem setPackingScanInstructions_tm_polytime :
    TMPolyTimeMap
      setPackingScanInputEncodedType
      setPackingScanInstructionListEncodedType
      setPackingScanInstructions := by
  let X := setPackingScanInputEncodedType
  have hSource : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, setPackingScanInputEncodedType] using
      TMPolyTimeMap.fst setFamilyStructuredEncodedType setFamilyStructuredEncodedType
  have hCert : TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setPackingScanInputEncodedType] using
      TMPolyTimeMap.snd setFamilyStructuredEncodedType setFamilyStructuredEncodedType
  have hEmptySet : TMPolyTimeMap X setStructuredEncodedType
      (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X setStructuredEncodedType []
  have hInitPayload : TMPolyTimeMap X setPackingScanPayloadEncodedType
      (fun p : X.Carrier => (p.1, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hSource hEmptySet
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInit : TMPolyTimeMap X setPackingScanInstructionEncodedType
      (fun p : X.Carrier => setPackingScanInitInstruction p.1) := by
    have hOut := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [setPackingScanInitInstruction, setPackingScanInstructionEncodedType,
      setPackingScanPayloadEncodedType] using hOut
  have hInitSingleton : TMPolyTimeMap X setPackingScanInstructionListEncodedType
      (fun p : X.Carrier => [setPackingScanInitInstruction p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton setPackingScanInstructionEncodedType) hInit
    simpa [Function.comp, setPackingScanInstructionListEncodedType, X] using hComp
  have hElement : TMPolyTimeMap setStructuredEncodedType setPackingScanInstructionEncodedType
      setPackingScanSetInstruction := by
    have hTrue : TMPolyTimeMap setStructuredEncodedType EncodedType.bool
        (fun _ : List Nat => true) :=
      TMPolyTimeMap.const setStructuredEncodedType EncodedType.bool true
    have hEmptyFamily : TMPolyTimeMap setStructuredEncodedType setFamilyStructuredEncodedType
        (fun _ : List Nat => ([] : List (List Nat))) :=
      TMPolyTimeMap.const setStructuredEncodedType setFamilyStructuredEncodedType []
    have hSet : TMPolyTimeMap setStructuredEncodedType setStructuredEncodedType id :=
      TMPolyTimeMap.id setStructuredEncodedType
    have hPayload : TMPolyTimeMap setStructuredEncodedType setPackingScanPayloadEncodedType
        (fun S : List Nat => (([] : List (List Nat)), S)) :=
      TMPolyTimeMap.prod_mk hEmptyFamily hSet
    have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
    simpa [setPackingScanSetInstruction, setPackingScanInstructionEncodedType,
      setPackingScanPayloadEncodedType] using hOut
  have hElements : TMPolyTimeMap X setPackingScanInstructionListEncodedType
      (fun p : X.Carrier => p.2.map setPackingScanSetInstruction) := by
    have hMap := TMPolyTimeMap.list_map hElement
    have hComp := TMPolyTimeMap.comp hMap hCert
    simpa [Function.comp, setPackingScanInstructionListEncodedType, X] using hComp
  have hAppendInput : TMPolyTimeMap X
      (EncodedType.prod setPackingScanInstructionListEncodedType
        setPackingScanInstructionListEncodedType)
      (fun p : X.Carrier =>
        ([setPackingScanInitInstruction p.1],
          p.2.map setPackingScanSetInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElements
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append setPackingScanInstructionEncodedType) hAppendInput
  simpa [Function.comp, setPackingScanInstructions,
    setPackingScanInstructionListEncodedType, X] using hOut

theorem setPackingScanStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setPackingScanAccEncodedType setPackingScanInstructionEncodedType)
      setPackingScanAccEncodedType
      setPackingScanStep := by
  let X := EncodedType.prod setPackingScanAccEncodedType setPackingScanInstructionEncodedType
  let A := setPackingScanAccEncodedType
  let SeenElemsOK := EncodedType.prod setStructuredEncodedType EncodedType.bool
  let AccTail := EncodedType.prod setFamilyStructuredEncodedType SeenElemsOK
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A setPackingScanInstructionEncodedType
  have hInstr : TMPolyTimeMap X setPackingScanInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A setPackingScanInstructionEncodedType
  have hSource : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType AccTail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setPackingScanAccEncodedType, AccTail, X] using hComp
  have hAccTail : TMPolyTimeMap X AccTail (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType AccTail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setPackingScanAccEncodedType, AccTail, X] using hComp
  have hSeenSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType SeenElemsOK
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, AccTail, X] using hComp
  have hSeenElemsOK : TMPolyTimeMap X SeenElemsOK (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType SeenElemsOK
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, AccTail, X] using hComp
  have hSeenElems : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hSeenElemsOK
    simpa [Function.comp, SeenElemsOK, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hSeenElemsOK
    simpa [Function.comp, SeenElemsOK, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool setPackingScanPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, setPackingScanInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X setPackingScanPayloadEncodedType
      (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool setPackingScanPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, setPackingScanInstructionEncodedType, X] using hComp
  have hInitSource : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, setPackingScanPayloadEncodedType, X] using hComp
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, setPackingScanPayloadEncodedType, X] using hComp
  have hInFamilyInput : TMPolyTimeMap X setFamilyContainsInputEncodedType
      (fun p : X.Carrier => (p.2.2.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hSet hSource
  have hInFamily : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => setFamilyContainsBool (p.2.2.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp setFamilyContainsBool_tm_polytime hInFamilyInput
    simpa [Function.comp, setFamilyContainsInputEncodedType, X] using hComp
  have hDuplicateInput : TMPolyTimeMap X setFamilyContainsInputEncodedType
      (fun p : X.Carrier => (p.2.2.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hSet hSeenSets
  have hDuplicate : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => setFamilyContainsBool (p.2.2.2, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp setFamilyContainsBool_tm_polytime hDuplicateInput
    simpa [Function.comp, setFamilyContainsInputEncodedType, X] using hComp
  have hFresh : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => Bool.not (setFamilyContainsBool (p.2.2.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hDuplicate
    simpa [Function.comp, X] using hComp
  have hHitInput : TMPolyTimeMap X HittingSet.setHitInstructionInputEncodedType
      (fun p : X.Carrier => (p.2.2.2, p.1.2.2.1)) :=
    TMPolyTimeMap.prod_mk hSet hSeenElems
  have hHit : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setHitBool (p.2.2.2, p.1.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setHitBool_tm_polytime hHitInput
    simpa [Function.comp, HittingSet.setHitInstructionInputEncodedType, X] using hComp
  have hDisjoint : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => setPackingLocalDisjointBool p.2.2.2 p.1.2.2.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.bool_not hHit
    simpa [Function.comp, setPackingLocalDisjointBool, X] using hComp
  have hFreshDisjointInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (Bool.not (setFamilyContainsBool (p.2.2.2, p.1.2.1)),
          setPackingLocalDisjointBool p.2.2.2 p.1.2.2.1)) :=
    TMPolyTimeMap.prod_mk hFresh hDisjoint
  have hFreshDisjoint : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (Bool.not (setFamilyContainsBool (p.2.2.2, p.1.2.1)),
            setPackingLocalDisjointBool p.2.2.2 p.1.2.2.1)) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hFreshDisjointInput
    simpa [Function.comp, X] using hComp
  have hLocalInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (setFamilyContainsBool (p.2.2.2, p.1.1),
          graphBoolAndPair
            (Bool.not (setFamilyContainsBool (p.2.2.2, p.1.2.1)),
              setPackingLocalDisjointBool p.2.2.2 p.1.2.2.1))) :=
    TMPolyTimeMap.prod_mk hInFamily hFreshDisjoint
  have hLocalOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        setPackingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hLocalInput
    simpa [Function.comp, setPackingLocalOKBool, X] using hComp
  have hNewOKInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        (p.1.2.2.2, setPackingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hOk hLocalOK
  have hNewOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2.2, setPackingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hNewOKInput
    simpa [Function.comp, X] using hComp
  have hNewSeenSetsInput :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType setFamilyStructuredEncodedType)
        (fun p : X.Carrier => (p.2.2.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hSet hSeenSets
  have hNewSeenSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2 :: p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_cons setStructuredEncodedType) hNewSeenSetsInput
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hNewSeenElemsInput :
      TMPolyTimeMap X (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : X.Carrier => (p.2.2.2, p.1.2.2.1)) :=
    TMPolyTimeMap.prod_mk hSet hSeenElems
  have hNewSeenElems : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier =>
        let current : List Nat := p.2.2.2
        let seenElems : List Nat := p.1.2.2.1
        current ++ seenElems) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hNewSeenElemsInput
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hNewSeenElemsOK : TMPolyTimeMap X SeenElemsOK
      (fun p : X.Carrier =>
        ((let current : List Nat := p.2.2.2
          let seenElems : List Nat := p.1.2.2.1
          current ++ seenElems),
          graphBoolAndPair
            (p.1.2.2.2, setPackingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hNewSeenElems hNewOK
  have hTrueTail : TMPolyTimeMap X AccTail
      (fun p : X.Carrier =>
        (p.2.2.2 :: p.1.2.1,
          ((let current : List Nat := p.2.2.2
            let seenElems : List Nat := p.1.2.2.1
            current ++ seenElems),
            graphBoolAndPair
              (p.1.2.2.2,
                setPackingLocalOKBool p.1.1 p.1.2.1 p.1.2.2.1 p.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hNewSeenSets hNewSeenElemsOK
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : X.Carrier => setPackingScanElementStep p.1 p.2.2.2) := by
    have hOut := TMPolyTimeMap.prod_mk hSource hTrueTail
    simpa [setPackingScanElementStep, A, setPackingScanAccEncodedType, AccTail,
      SeenElemsOK] using hOut
  have hEmptyFamily : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun _ : X.Carrier => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X setFamilyStructuredEncodedType []
  have hEmptySet : TMPolyTimeMap X setStructuredEncodedType
      (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X setStructuredEncodedType []
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseSeenElemsOK : TMPolyTimeMap X SeenElemsOK
      (fun _ : X.Carrier => (([] : List Nat), true)) :=
    TMPolyTimeMap.prod_mk hEmptySet hTrue
  have hFalseTail : TMPolyTimeMap X AccTail
      (fun _ : X.Carrier => (([] : List (List Nat)), (([] : List Nat), true))) :=
    TMPolyTimeMap.prod_mk hEmptyFamily hFalseSeenElemsOK
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier => (p.2.2.1, (([] : List (List Nat)), (([] : List Nat), true)))) :=
    TMPolyTimeMap.prod_mk hInitSource hFalseTail
  have hBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
      (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => setPackingScanElementStep p.2.1 p.2.2.2.2
          | false => (p.2.2.2.1, ([], ([], true)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier => (p.2.2.1, ([], ([], true))))
      (fTrue := fun p : X.Carrier => setPackingScanElementStep p.1 p.2.2.2)
      hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  simpa [Function.comp, setPackingScanStep] using hOut

theorem setPackingScanFold_tm_polytime :
    TMPolyTimeMap
      setPackingScanInstructionListEncodedType
      setPackingScanAccEncodedType
      (fun xs : setPackingScanInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => setPackingScanStep (acc, x)) setPackingScanRunnerInit) := by
  rcases setPackingScanStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      setPackingScanInstructionEncodedType setPackingScanAccEncodedType
      setPackingScanStep setPackingScanRunnerInit hStep
      (Polynomial.C 1000) (Polynomial.C 3 * Polynomial.X + Polynomial.C 1000) ?_ ?_
  · intro xs
    change setPackingScanAccEncodedType.inputSize setPackingScanRunnerInit ≤
      (Polynomial.C 1000).eval
        (setPackingScanInstructionEncodedType.list.inputSize xs)
    have hInit : setPackingScanAccEncodedType.inputSize setPackingScanRunnerInit ≤
        1000 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    rcases acc with ⟨sourceFamily, accTail⟩
    rcases accTail with ⟨seenSets, seenElemsOK⟩
    rcases seenElemsOK with ⟨seenElems, ok⟩
    rcases instr with ⟨tag, payload⟩
    rcases payload with ⟨initSource, current⟩
    change List (List Nat) at sourceFamily seenSets initSource
    change List Nat at seenElems current
    cases tag
    · simp [setPackingScanStep, setPackingScanAccEncodedType,
        setPackingScanInstructionEncodedType, setPackingScanPayloadEncodedType,
        setFamilyStructuredEncodedType, setStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_list_nil, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] at hInstr ⊢
      omega
    · simp [setPackingScanStep, setPackingScanElementStep, setPackingScanAccEncodedType,
        setPackingScanInstructionEncodedType, setPackingScanPayloadEncodedType,
        setFamilyStructuredEncodedType, setStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool,
        EncodedType.inputSize_list_cons, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] at hInstr ⊢
      have hAppend :
          EncodedType.nat.list.inputSize (current ++ seenElems) =
            EncodedType.nat.list.inputSize current +
              EncodedType.nat.list.inputSize seenElems := by
        simpa using Clique.encodedList_inputSize_append EncodedType.nat current seenElems
      rw [hAppend]
      omega

theorem setPackingScanFromInstructions_tm_polytime :
    TMPolyTimeMap
      setPackingScanInstructionListEncodedType
      EncodedType.bool
      setPackingScanFromInstructions := by
  have hFold := setPackingScanFold_tm_polytime
  have hTail1 := TMPolyTimeMap.snd setFamilyStructuredEncodedType
    (EncodedType.prod setFamilyStructuredEncodedType
      (EncodedType.prod setStructuredEncodedType EncodedType.bool))
  have hComp1 := TMPolyTimeMap.comp hTail1 hFold
  have hTail2 := TMPolyTimeMap.snd setFamilyStructuredEncodedType
    (EncodedType.prod setStructuredEncodedType EncodedType.bool)
  have hComp2 := TMPolyTimeMap.comp hTail2 hComp1
  have hBool := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.bool
  have hComp3 := TMPolyTimeMap.comp hBool hComp2
  simpa [Function.comp, setPackingScanFromInstructions, setPackingScanAccEncodedType]
    using hComp3

theorem setPackingScanBool_tm_polytime :
    TMPolyTimeMap
      setPackingScanInputEncodedType
      EncodedType.bool
      setPackingScanBool := by
  have hComp := TMPolyTimeMap.comp setPackingScanFromInstructions_tm_polytime
    setPackingScanInstructions_tm_polytime
  simpa [Function.comp, setPackingScanBool] using hComp

end SetPackingMembership
end Karp21
end ComplexityReduction
