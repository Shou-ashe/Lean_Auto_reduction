import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.SeqComp.Part1

namespace ComplexityReduction
namespace TM2Programs
open Turing.TM2.Stmt

lemma seqCopy_pushTemp_step (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (b : tm₂.Γ tm₂.k₀)
    (source : List (tm₁.Γ tm₁.k₁)) (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTemp b) state
          source target left right temp) =
      some
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead state
          source target left right (b :: temp)) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]
  congr
  funext x
  cases x with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp [Function.update]

lemma seqCopy_drain_step_cons (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (source : List (tm₁.Γ tm₁.k₁))
    (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (b : tm₂.Γ tm₂.k₀) (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain state
          source target left right (b :: temp)) =
      some
        (seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTarget b) (some b)
          source target left right temp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]
  congr
  funext x
  cases x with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp [Function.update]

lemma seqCopy_drain_step_nil (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (source : List (tm₁.Γ tm₁.k₁))
    (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain state
          source target left right []) =
      some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ source)
          (Function.update right tm₂.k₀ target) []) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]

lemma seqCopy_pushTarget_step (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (source : List (tm₁.Γ tm₁.k₁))
    (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (b : tm₂.Γ tm₂.k₀) (temp : List (tm₂.Γ tm₂.k₀)) :
    (seqCompMachine tm₁ tm₂ mapSym).step
        (seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTarget b) state
          source target left right temp) =
      some
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain state
          source (b :: target) left right temp) := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqCopyCfg, seqCompCfg, Function.update, seqCompCopyState]
  congr
  funext x
  cases x with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp [Function.update]

def seqCopy_fillTemp_run (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (source : List (tm₁.Γ tm₁.k₁))
    (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    StateTransition.EvalsToInTime (seqCompMachine tm₁ tm₂ mapSym).step
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead state
        source target left right temp)
      (some
        (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain none
          [] target left right ((source.map mapSym).reverse ++ temp)))
      (2 * source.length + 1) := by
  induction source generalizing state temp with
  | nil =>
      simpa using
        evalsToInTimeOne
          (seqCopy_read_step_nil tm₁ tm₂ mapSym state target left right temp)
  | cons a source ih =>
      let tm := seqCompMachine tm₁ tm₂ mapSym
      let c₀ := seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead state
        (a :: source) target left right temp
      let c₁ := seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTemp (mapSym a))
        (some (mapSym a)) source target left right temp
      let c₂ := seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead (some (mapSym a))
        source target left right (mapSym a :: temp)
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (seqCopy_read_step_cons tm₁ tm₂ mapSym state a source target left right temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (seqCopy_pushTemp_step tm₁ tm₂ mapSym (some (mapSym a)) (mapSym a)
            source target left right temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain none
              [] target left right ((source.map mapSym).reverse ++ (mapSym a :: temp))))
          (2 * source.length + 1) :=
        ih (some (mapSym a)) (mapSym a :: temp)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * source.length + 1) c₀ c₂
          (some
            (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain none
              [] target left right ((source.map mapSym).reverse ++ (mapSym a :: temp))))
          h₁₂ hTail

def seqCopy_drainTemp_run (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (state : Option (tm₂.Γ tm₂.k₀)) (source : List (tm₁.Γ tm₁.k₁))
    (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k))
    (temp : List (tm₂.Γ tm₂.k₀)) :
    StateTransition.EvalsToInTime (seqCompMachine tm₁ tm₂ mapSym).step
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain state
        source target left right temp)
      (some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ source)
          (Function.update right tm₂.k₀ (temp.reverse ++ target)) []))
      (2 * temp.length + 1) := by
  induction temp generalizing state target with
  | nil =>
      simpa using
        evalsToInTimeOne
          (seqCopy_drain_step_nil tm₁ tm₂ mapSym state source target left right)
  | cons b temp ih =>
      let tm := seqCompMachine tm₁ tm₂ mapSym
      let c₀ := seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain state
        source target left right (b :: temp)
      let c₁ := seqCopyCfg tm₁ tm₂ mapSym (SeqCompLabel.copyPushTarget b) (some b)
        source target left right temp
      let c₂ := seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain (some b)
        source (b :: target) left right temp
      have h₁ : StateTransition.EvalsToInTime tm.step c₀ (some c₁) 1 :=
        evalsToInTimeOne
          (seqCopy_drain_step_cons tm₁ tm₂ mapSym state source target left right b temp)
      have h₂ : StateTransition.EvalsToInTime tm.step c₁ (some c₂) 1 :=
        evalsToInTimeOne
          (seqCopy_pushTarget_step tm₁ tm₂ mapSym (some b) source target left right b temp)
      have h₁₂ : StateTransition.EvalsToInTime tm.step c₀ (some c₂) (1 + 1) :=
        StateTransition.EvalsToInTime.trans tm.step 1 1 c₀ c₁ (some c₂) h₁ h₂
      have hTail : StateTransition.EvalsToInTime tm.step c₂
          (some
            (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
              (SeqCompState.second tm₂.initialState)
              (Function.update left tm₁.k₁ source)
              (Function.update right tm₂.k₀ (temp.reverse ++ (b :: target))) []))
          (2 * temp.length + 1) :=
        ih (some b) (b :: target)
      simpa [tm, c₀, c₁, c₂, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        StateTransition.EvalsToInTime.trans tm.step (1 + 1)
          (2 * temp.length + 1) c₀ c₂
          (some
            (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
              (SeqCompState.second tm₂.initialState)
              (Function.update left tm₁.k₁ source)
              (Function.update right tm₂.k₀ (temp.reverse ++ (b :: target))) []))
          h₁₂ hTail

def seqCopy_run (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (source : List (tm₁.Γ tm₁.k₁)) (target : List (tm₂.Γ tm₂.k₀))
    (left : (k : tm₁.K) → List (tm₁.Γ k))
    (right : (k : tm₂.K) → List (tm₂.Γ k)) :
    StateTransition.EvalsToInTime (seqCompMachine tm₁ tm₂ mapSym).step
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none
        source target left right [])
      (some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ [])
          (Function.update right tm₂.k₀ (source.map mapSym ++ target)) []))
      (4 * source.length + 2) := by
  let tm := seqCompMachine tm₁ tm₂ mapSym
  let mid := seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyDrain none
    [] target left right (source.map mapSym).reverse
  have hFill : StateTransition.EvalsToInTime tm.step
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none
        source target left right [])
      (some mid) (2 * source.length + 1) := by
    simpa [tm, mid] using
      seqCopy_fillTemp_run tm₁ tm₂ mapSym none source target left right []
  have hDrain : StateTransition.EvalsToInTime tm.step mid
      (some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ [])
          (Function.update right tm₂.k₀ ((source.map mapSym).reverse.reverse ++ target)) []))
      (2 * (source.map mapSym).reverse.length + 1) := by
    simpa [tm, mid] using
      seqCopy_drainTemp_run tm₁ tm₂ mapSym none [] target left right
        (source.map mapSym).reverse
  have hAll : StateTransition.EvalsToInTime tm.step
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none
        source target left right [])
      (some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ [])
          (Function.update right tm₂.k₀ ((source.map mapSym).reverse.reverse ++ target)) []))
      ((2 * (source.map mapSym).reverse.length + 1) + (2 * source.length + 1)) :=
    StateTransition.EvalsToInTime.trans tm.step
      (2 * source.length + 1)
      (2 * (source.map mapSym).reverse.length + 1)
      (seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none
        source target left right [])
      mid
      (some
        (seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
          (SeqCompState.second tm₂.initialState)
          (Function.update left tm₁.k₁ [])
          (Function.update right tm₂.k₀ ((source.map mapSym).reverse.reverse ++ target)) []))
      hFill hDrain
  refine
    { steps := hAll.steps
      evals_in_steps := by
        simpa [tm, mid] using hAll.evals_in_steps
      steps_le_m := ?_ }
  have hSteps := hAll.steps_le_m
  simp [List.length_reverse] at hSteps
  omega

lemma seqComp_initList (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (input : List (tm₁.Γ tm₁.k₀)) :
    Turing.initList (seqCompMachine tm₁ tm₂ mapSym) input =
      seqFirstCfg tm₁ tm₂ mapSym (Turing.initList tm₁ input) (fun _ => []) [] := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqFirstCfg, seqCompCfg, Turing.initList]
  congr
  funext s
  cases s with
  | left k =>
      by_cases hk : k = tm₁.k₀
      · subst k
        simp
      · simp [hk]
  | right k =>
      simp
  | copyTemp =>
      simp

lemma haltList_output_update_eq_self (tm : Turing.FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    Function.update (Turing.haltList tm output).stk tm.k₁ output =
      (Turing.haltList tm output).stk := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₁
  · subst k
    simp [Function.update, Turing.haltList]
  · simp [Function.update, Turing.haltList, hk]

lemma haltList_clear_output_eq_empty (tm : Turing.FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    Function.update (Turing.haltList tm output).stk tm.k₁ [] = fun k => ([] : List (tm.Γ k)) := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₁
  · subst k
    simp [Function.update]
  · simp [Function.update, Turing.haltList, hk]

lemma initList_eq_update_empty (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    (Turing.initList tm input).stk =
      Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ input := by
  letI := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₀
  · subst k
    simp [Function.update, Turing.initList]
  · simp [Function.update, Turing.initList, hk]

lemma seqFirst_halt_eq_seqCopy_start (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (middle : List (tm₁.Γ tm₁.k₁)) :
    seqFirstCfg tm₁ tm₂ mapSym (Turing.haltList tm₁ middle) (fun _ => []) [] =
      seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none middle []
        (Turing.haltList tm₁ middle).stk (fun _ => []) [] := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqFirstCfg, seqCopyCfg, seqCompCfg, Turing.haltList]
  funext s
  cases s with
  | left k =>
      by_cases hk : k = tm₁.k₁
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | right k =>
      simp
  | copyTemp =>
      simp

lemma seqCopy_done_eq_seqSecond_init (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (middle : List (tm₁.Γ tm₁.k₁)) :
    seqCompCfg tm₁ tm₂ mapSym (some (SeqCompLabel.second tm₂.main))
        (SeqCompState.second tm₂.initialState)
        (Function.update (Turing.haltList tm₁ middle).stk tm₁.k₁ [])
        (Function.update (fun k => ([] : List (tm₂.Γ k))) tm₂.k₀ (middle.map mapSym))
        [] =
      seqSecondCfg tm₁ tm₂ mapSym (Turing.initList tm₂ (middle.map mapSym))
        (fun _ => []) [] := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqSecondCfg, seqCompCfg, Turing.initList, haltList_clear_output_eq_empty]
  funext s
  cases s with
  | left k =>
      simp
  | right k =>
      by_cases hk : k = tm₂.k₀
      · subst k
        simp [Function.update]
      · simp [Function.update, hk]
  | copyTemp =>
      simp

lemma seqSecond_halt_eq_seqComp_haltList (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (output : List (tm₂.Γ tm₂.k₁)) :
    seqSecondCfg tm₁ tm₂ mapSym (Turing.haltList tm₂ output) (fun _ => []) [] =
      Turing.haltList (seqCompMachine tm₁ tm₂ mapSym) output := by
  letI := tm₁.kDecidableEq
  letI := tm₂.kDecidableEq
  simp [seqCompMachine, seqSecondCfg, seqCompCfg, Turing.haltList]
  funext s
  cases s with
  | left k =>
      simp
  | right k =>
      by_cases hk : k = tm₂.k₁
      · subst k
        simp
      · simp [hk]
  | copyTemp =>
      simp

/--
Sequential composition at the public `TM2OutputsInTime` boundary.

If `tm₁` maps `input` to `middle` and `tm₂` maps the copied intermediate stack
to `output`, then the orchestrating machine runs the first phase, copies the
intermediate output, and runs the second phase.
-/
def seqComp_outputsInTime (tm₁ tm₂ : Turing.FinTM2)
    (mapSym : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (input : List (tm₁.Γ tm₁.k₀)) (middle : List (tm₁.Γ tm₁.k₁))
    (output : List (tm₂.Γ tm₂.k₁)) (time₁ time₂ : Nat)
    (h₁ : Turing.TM2OutputsInTime tm₁ input (some middle) time₁)
    (h₂ : Turing.TM2OutputsInTime tm₂ (middle.map mapSym) (some output) time₂) :
    Turing.TM2OutputsInTime (seqCompMachine tm₁ tm₂ mapSym) input (some output)
      (time₂ + ((4 * middle.length + 2) + time₁)) := by
  let tm := seqCompMachine tm₁ tm₂ mapSym
  let copyStart :=
    seqCopyCfg tm₁ tm₂ mapSym SeqCompLabel.copyRead none middle []
      (Turing.haltList tm₁ middle).stk (fun _ => []) []
  let secondStart :=
    seqSecondCfg tm₁ tm₂ mapSym (Turing.initList tm₂ (middle.map mapSym))
      (fun _ => []) []
  let finalCfg := Turing.haltList tm output
  have hFirst : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some copyStart) time₁ := by
    have hMapped :=
      seqFirstFinTM2_evalsToInTime tm₁ tm₂ mapSym (fun _ => []) [] h₁
    simpa [tm, copyStart, seqComp_initList, seqFirst_halt_eq_seqCopy_start] using hMapped
  have hCopy : StateTransition.EvalsToInTime tm.step copyStart (some secondStart)
      (4 * middle.length + 2) := by
    have hRun :=
      seqCopy_run tm₁ tm₂ mapSym middle [] (Turing.haltList tm₁ middle).stk
        (fun _ => [])
    simpa [tm, copyStart, secondStart, seqCopy_done_eq_seqSecond_init] using hRun
  have hSecond : StateTransition.EvalsToInTime tm.step secondStart (some finalCfg) time₂ := by
    have hMapped :=
      seqSecondFinTM2_evalsToInTime tm₁ tm₂ mapSym (fun _ => []) [] h₂
    simpa [tm, secondStart, finalCfg, seqSecond_halt_eq_seqComp_haltList] using hMapped
  have hFirstCopy : StateTransition.EvalsToInTime tm.step
      (Turing.initList tm input) (some secondStart) ((4 * middle.length + 2) + time₁) :=
    StateTransition.EvalsToInTime.trans tm.step time₁ (4 * middle.length + 2)
      (Turing.initList tm input) copyStart (some secondStart) hFirst hCopy
  simpa [Turing.TM2OutputsInTime, tm, finalCfg] using
    StateTransition.EvalsToInTime.trans tm.step ((4 * middle.length + 2) + time₁) time₂
      (Turing.initList tm input) secondStart (some finalCfg) hFirstCopy hSecond

/-- Evaluation of a polynomial over `Nat` is monotone in the input. -/
theorem polynomialNat_eval_mono (p : Polynomial Nat) {m n : Nat} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact Nat.mul_le_mul_left (p.coeff i) (Nat.pow_le_pow_left h i)

/-- Polynomial bound used by the constructive sequential-composition TM2 witness. -/
noncomputable def seqCompTimePolynomial (tm₁ : Turing.FinTM2) (p₁ p₂ : Polynomial Nat) :
    Polynomial Nat :=
  let bound := Polynomial.X + p₁ * Polynomial.C (finTM2StepPushBound tm₁)
  p₂.comp bound + (Polynomial.C 4 * bound + Polynomial.C 2) + p₁

@[simp] lemma seqCompTimePolynomial_eval (tm₁ : Turing.FinTM2)
    (p₁ p₂ : Polynomial Nat) (n : Nat) :
    (seqCompTimePolynomial tm₁ p₁ p₂).eval n =
      p₂.eval (n + p₁.eval n * finTM2StepPushBound tm₁) +
        (4 * (n + p₁.eval n * finTM2StepPushBound tm₁) + 2) +
        p₁.eval n := by
  simp [seqCompTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_comp]

/--
Constructive replacement for mathlib's `TM2ComputableInPolyTime.comp`.

The machine is `seqCompMachine`: run the first TM2, copy its output stack into
the second TM2 input stack through the two alphabet equivalences, then run the
second TM2.  The intermediate output-size bound supplies the polynomial bound
for the second phase.
-/
noncomputable def seqCompComputableInPolyTime
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (h₂ : Turing.TM2ComputableInPolyTime eβ eγ g) :
    Turing.TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm :=
    seqCompMachine h₁.tm h₂.tm
      (fun b => h₂.inputAlphabet.invFun (h₁.outputAlphabet b))
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := h₂.outputAlphabet
  time := seqCompTimePolynomial h₁.tm h₁.time h₂.time
  outputsFun a := by
    let mapSym : h₁.tm.Γ h₁.tm.k₁ → h₂.tm.Γ h₂.tm.k₀ :=
      fun b => h₂.inputAlphabet.invFun (h₁.outputAlphabet b)
    let input : List (h₁.tm.Γ h₁.tm.k₀) :=
      List.map h₁.inputAlphabet.invFun (eα a)
    let middle : List (h₁.tm.Γ h₁.tm.k₁) :=
      List.map h₁.outputAlphabet.invFun (eβ (f a))
    let output : List (h₂.tm.Γ h₂.tm.k₁) :=
      List.map h₂.outputAlphabet.invFun (eγ (g (f a)))
    have hFirst : Turing.TM2OutputsInTime h₁.tm input (some middle)
        (h₁.time.eval (eα a).length) := by
      simpa [input, middle] using h₁.outputsFun a
    have hMiddleInput :
        middle.map mapSym = List.map h₂.inputAlphabet.invFun (eβ (f a)) := by
      simp [middle, mapSym, List.map_map]
    have hSecond : Turing.TM2OutputsInTime h₂.tm (middle.map mapSym) (some output)
        (h₂.time.eval (eβ (f a)).length) := by
      rw [hMiddleInput]
      simpa [output] using h₂.outputsFun (f a)
    have hRun :=
      seqComp_outputsInTime h₁.tm h₂.tm mapSym input middle output
        (h₁.time.eval (eα a).length) (h₂.time.eval (eβ (f a)).length)
        hFirst hSecond
    refine
      { steps := hRun.steps
        evals_in_steps := by
          simpa [input, output, mapSym, Function.comp] using hRun.evals_in_steps
        steps_le_m := ?_ }
    have hRunSteps := hRun.steps_le_m
    have hMiddleLen : middle.length = (eβ (f a)).length := by
      simp [middle]
    let n := (eα a).length
    let bound := n + h₁.time.eval n * finTM2StepPushBound h₁.tm
    have hOutputBound :
        middle.length ≤ bound := by
      have hOut := tm2ComputableInPolyTime_output_length_le h₁ a
      simp [middle, n, bound] at hOut ⊢
      omega
    have hSecondTime :
        h₂.time.eval (eβ (f a)).length ≤ h₂.time.eval bound := by
      rw [← hMiddleLen]
      exact polynomialNat_eval_mono h₂.time hOutputBound
    have hCopyTime : 4 * middle.length + 2 ≤ 4 * bound + 2 := by
      omega
    have hSecondTimeExplicit :
        h₂.time.eval (eβ (f a)).length ≤
          h₂.time.eval
            ((eα a).length +
              h₁.time.eval (eα a).length * finTM2StepPushBound h₁.tm) := by
      simpa [n, bound] using hSecondTime
    have hCopyTimeExplicit :
        4 * middle.length + 2 ≤
          4 * ((eα a).length +
            h₁.time.eval (eα a).length * finTM2StepPushBound h₁.tm) + 2 := by
      simpa [n, bound] using hCopyTime
    have hActualLe :
        h₂.time.eval (eβ (f a)).length +
            ((4 * middle.length + 2) + h₁.time.eval (eα a).length) ≤
          (seqCompTimePolynomial h₁.tm h₁.time h₂.time).eval (eα a).length := by
      simp [seqCompTimePolynomial_eval]
      omega
    exact hRunSteps.trans hActualLe

end TM2Programs
end ComplexityReduction
