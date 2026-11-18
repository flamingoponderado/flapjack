module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithClock
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyConst
public import Flapjack.Compiler.Backend.Semantics.DataProps.InitialStateLaws
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields
public import Flapjack.Misc.ClockWeightInduction
public import Flapjack.HolRef

@[expose] public section

/-!
# Clock extension under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2003`
`evaluate_add_clock` and `:2134` `evaluate_add_clock_io_events_mono`.

Raising the starting clock by `ck` raises the final clock by `ck` and leaves the
evaluation result unchanged, provided the original run does not time out. The
induction runs over the lexicographic `(clock, weight)` measure; each
constructor's step is a private lemma below.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- Raise the starting clock by `ck`. -/
abbrev addClockState {C F : Type} (state : State C F) (ck : Nat) : State C F :=
  { state with clock := state.clock + ck }

@[simp] theorem addClockState_clock {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).clock = state.clock + ck := rfl

@[simp] theorem addClockState_locals {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).locals = state.locals := rfl

@[simp] theorem addClockState_localsSize {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).localsSize = state.localsSize := rfl

@[simp] theorem addClockState_stack {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).stack = state.stack := rfl

@[simp] theorem addClockState_stackMax {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).stackMax = state.stackMax := rfl

@[simp] theorem addClockState_stackFrameSizes {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).stackFrameSizes = state.stackFrameSizes := rfl

@[simp] theorem addClockState_global {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).global = state.global := rfl

@[simp] theorem addClockState_handler {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).handler = state.handler := rfl

@[simp] theorem addClockState_refs {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).refs = state.refs := rfl

@[simp] theorem addClockState_compile {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).compile = state.compile := rfl

@[simp] theorem addClockState_code {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).code = state.code := rfl

@[simp] theorem addClockState_ffi {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).ffi = state.ffi := rfl

@[simp] theorem addClockState_space {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).space = state.space := rfl

@[simp] theorem addClockState_tstamps {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).tstamps = state.tstamps := rfl

@[simp] theorem addClockState_limits {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).limits = state.limits := rfl

@[simp] theorem addClockState_safeForSpace {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).safeForSpace = state.safeForSpace := rfl

@[simp] theorem addClockState_peakHeapLength {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).peakHeapLength = state.peakHeapLength := rfl

@[simp] theorem addClockState_compileOracle {C F : Type} (state : State C F) (ck : Nat) :
    (addClockState state ck).compileOracle = state.compileOracle := rfl

/-- A clock tick commutes with a clock extension once the clock is positive. -/
theorem decClock_addClockState {C F : Type} (state : State C F) (ck : Nat)
    (positive : state.clock ≠ 0) :
    decClock (addClockState state ck) = addClockState (decClock state) ck := by
  simp only [decClock, addClockState]
  rw [show state.clock + ck - 1 = state.clock - 1 + ck by omega]

/-- A local-environment cut commutes with a clock extension. -/
theorem cutStateOpt_addClockState {C F : Type} (names : Option NumSet) (state : State C F)
    (ck : Nat) :
    cutStateOpt names (addClockState state ck) =
      (cutStateOpt names state).map (fun next => addClockState next ck) := by
  cases names with
  | none => simp only [cutStateOpt, Option.map_some]
  | some names =>
    simp only [cutStateOpt, cutState, Option.map_map]
    congr 1

/-- Clamping a result's clock commutes with extending both clocks by the same
    amount. -/
theorem fixClock_addClockState {C F D G R : Type} (state : State C F) (value : R)
    (next : State D G) (ck : Nat) :
    fixClock (addClockState state ck) (value, addClockState next ck) =
      (value, addClockState (fixClock state (value, next)).2 ck) := by
  simp [fixClock, addClockState, Nat.add_min_add_right]

/-- Flushing locals commutes with a clock extension. -/
theorem flushState_addClockState {C F : Type} (all : Bool) (state : State C F) (ck : Nat) :
    flushState all (addClockState state ck) = addClockState (flushState all state) ck := by
  cases all <;> simp [flushState, addClockState]

/-- Installation's safety update commutes with a clock extension. -/
theorem installSfs_addClockState {C F : Type} (op : ClosLang.Op) (state : State C F) (ck : Nat) :
    installSfs op (addClockState state ck) = addClockState (installSfs op state) ck := by
  cases op <;> simp [installSfs, addClockState]

/-- Reserving space commutes with a clock extension. -/
theorem addSpace_addClockState {C F : Type} (state : State C F) (amount ck : Nat) :
    addSpace (addClockState state ck) amount = addClockState (addSpace state amount) ck := by
  simp only [addSpace, addClockState]
  rw [sizeOfHeap_with_clock]

/-- Restoring the next frame commutes with a clock extension. -/
theorem popEnv_addClockState {C F : Type} (state : State C F) (ck : Nat) :
    popEnv (addClockState state ck) =
      (popEnv state).map (fun next => addClockState next ck) := by
  cases stackEq : state.stack with
  | nil => simp [popEnv, stackEq]
  | cons frame rest =>
    cases frame with
    | env size env => simp [popEnv, stackEq, addClockState]
    | exc size env handler => simp [popEnv, stackEq, addClockState]

/-- An exception-stack jump commutes with a clock extension. -/
theorem jumpExc_addClockState {C F : Type} (state : State C F) (ck : Nat) :
    jumpExc (addClockState state ck) =
      (jumpExc state).map (fun next => addClockState next ck) := by
  simp only [jumpExc, addClockState]
  split
  · split <;> simp
  · simp

/-- Entering a call commutes with a clock extension. -/
theorem callEnv_addClockState {C F : Type} (args : List DataSem.Value) (size : Option Nat)
    (state : State C F) (ck : Nat) :
    callEnv args size (addClockState state ck) = addClockState (callEnv args size state) ck := by
  simp [callEnv, addClockState]

/-- Pushing a frame commutes with a clock extension. -/
theorem pushEnv_addClockState {C F : Type} (env : Spt DataSem.Value) (handler : Bool)
    (state : State C F) (ck : Nat) :
    pushEnv env handler (addClockState state ck) =
      addClockState (pushEnv env handler state) ck := by
  simp [pushEnv, addClockState]

/-- Writing a local commutes with a clock extension. -/
theorem setVar_addClockState {C F : Type} (name : Nat) (value : DataSem.Value) (state : State C F)
    (ck : Nat) :
    setVar name value (addClockState state ck) = addClockState (setVar name value state) ck := by
  simp [setVar, addClockState]

/-- Writing several locals commutes with a clock extension. -/
theorem setVars_addClockState {C F : Type} (names : List Nat) (values : List DataSem.Value)
    (state : State C F) (ck : Nat) :
    setVars names values (addClockState state ck) =
      addClockState (setVars names values state) ck := by
  simp [setVars, addClockState]


/-- Primitive application commutes with a clock extension; the result state is
    shifted by the same amount, using that `doApp` preserves the clock. -/
theorem doApp_addClockState {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (ck : Nat) :
    doApp op values (addClockState state ck) =
      mapResult (fun (value, next) => (value, addClockState next ck)) id
        (doApp op values state) := by
  simp only [addClockState]
  rw [doApp_with_clock op values state (state.clock + ck)]
  cases applied : doApp op values state with
  | val pair =>
    obtain ⟨value, next⟩ := pair
    have clockEq := (doApp_const op values state value next applied).2.2.2.1
    simp only [mapResult, clockEq]
  | err error => simp only [mapResult]

/-- The add-clock property for one program and starting state: a run that does
    not time out is reproduced at the clock-extended state with the final clock
    extended by the same amount. -/
private def AddClockAt {C F : Type} (program : DataLang.Prog) (state : State C F) : Prop :=
  ∀ ck res next, evaluate program state = (res, next) →
    res ≠ some (.err (.abort .timeoutError)) →
    evaluate program (addClockState state ck) = (res, addClockState next ck)

/-- A stopped program is unchanged by a clock extension. -/
private theorem addClock_skip {C F : Type} (state : State C F) : AddClockAt .skip state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  obtain ⟨rfl, rfl⟩ := run
  rfl

/-- A move is unchanged by a clock extension. -/
private theorem addClock_move {C F : Type} (dest src : Nat) (state : State C F) :
    AddClockAt (.move dest src) state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  cases read : getVar src state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some value =>
    simp only [read, setVar_addClockState] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- An assignment is unchanged by a clock extension. -/
private theorem addClock_assign {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state : State C F) : AddClockAt (.assign dest op names live) state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · rw [if_pos invalid] at run ⊢
    simp only [typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  · rw [if_neg invalid] at run ⊢
    cases read : getVars names state.locals with
    | none =>
      simp only [read, typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | some values =>
      simp only [read] at run ⊢
      cases cut : cutStateOpt live state with
      | none =>
        rw [cutStateOpt_addClockState live state ck, cut, Option.map_none] at ⊢
        simp only [cut, typeError] at run ⊢
        obtain ⟨rfl, rfl⟩ := run
        rfl
      | some prepared =>
        rw [cutStateOpt_addClockState live state ck, cut, Option.map_some] at ⊢
        simp only [cut] at run
        simp only []
        rw [doApp_addClockState] at ⊢
        cases app : doApp op values prepared with
        | err error =>
          simp only [app, mapResult, mapErrorResult_id] at run ⊢
          rw [installSfs_addClockState, flushState_addClockState] at ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app, mapResult] at run ⊢
          rw [installSfs_addClockState, setVar_addClockState] at ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl

/-- A tick either times out or decrements the clock on both sides. -/
private theorem addClock_tick {C F : Type} (state : State C F) : AddClockAt .tick state := by
  intro ck res next run notTimeout
  simp only [evaluate] at run ⊢
  by_cases zero : state.clock = 0
  · simp only [zero] at run ⊢
    simp only [timeoutError] at run
    obtain ⟨rfl, _⟩ := run
    exact absurd rfl notTimeout
  · simp only [zero] at run ⊢
    have positive : state.clock + ck ≠ 0 := by omega
    rw [if_neg positive]
    rw [decClock_addClockState state ck zero]
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- Reserving space is unchanged by a clock extension. -/
private theorem addClock_makeSpace {C F : Type} (amount : Nat) (names : NumSet)
    (state : State C F) : AddClockAt (.makeSpace amount names) state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [cut, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some env =>
    simp only [cut] at run ⊢
    have comm : { addClockState state ck with locals := env } =
        addClockState { state with locals := env } ck := rfl
    rw [comm, addSpace_addClockState]
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- Raising an exception is unchanged by a clock extension. -/
private theorem addClock_raise {C F : Type} (name : Nat) (state : State C F) :
    AddClockAt (.raise name) state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  cases read : getVar name state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some value =>
    simp only [read] at run ⊢
    cases jump : jumpExc state with
    | none =>
      rw [jumpExc_addClockState, jump, Option.map_none] at ⊢
      simp only [jump, typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | some jumped =>
      simp only [jumpExc_addClockState, jump, Option.map_some] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl

/-- Returning values is unchanged by a clock extension. -/
private theorem addClock_return {C F : Type} (names : List Nat) (state : State C F) :
    AddClockAt (.return names) state := by
  intro ck res next run _
  simp only [evaluate] at run ⊢
  cases read : getVars names state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some values =>
    simp only [read, flushState_addClockState] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl

/-- A sequence follows its two programs at the clamped intermediate state. -/
private theorem addClock_seq {C F : Type} (first second : DataLang.Prog) (state : State C F)
    (firstIH : AddClockAt first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → AddClockAt second mid) :
    AddClockAt (.seq first second) state := by
  intro ck res next run notTimeout
  simp only [evaluate] at run ⊢
  cases firstRun : evaluate first state with
  | mk firstRes firstNext =>
    rw [firstRun] at run
    simp only [fixClock] at run
    have hres1 : firstRes ≠ some (.err (.abort .timeoutError)) := by
      intro h
      rw [h] at run
      simp only [] at run
      obtain ⟨rfl, _⟩ := run
      exact absurd rfl notTimeout
    have firstSwap := firstIH ck firstRes firstNext firstRun hres1
    rw [firstSwap] at ⊢
    rw [fixClock_addClockState state firstRes firstNext ck] at ⊢
    cases firstRes with
    | none =>
      simp only [] at run ⊢
      let mid := (fixClock state
        ((none : Option (Result (List DataSem.Value) DataSem.Value)), firstNext)).2
      have midClock : mid.clock ≤ state.clock := by
        simp only [mid, fixClock]
        exact Nat.min_le_left _ _
      exact secondIH mid midClock ck res next run notTimeout
    | some result =>
      simp only [] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl

/-- A conditional follows the branch its guard selects. -/
private theorem addClock_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (state : State C F) (yesIH : AddClockAt yes state) (noIH : AddClockAt no state) :
    AddClockAt (.ifThenElse name yes no) state := by
  intro ck res next run notTimeout
  simp only [evaluate] at run ⊢
  cases read : getVar name state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some value =>
    simp only [read] at run ⊢
    by_cases trueBranch : isBool true value = true
    · rw [if_pos trueBranch] at run ⊢
      exact yesIH ck res next run notTimeout
    · rw [if_neg trueBranch] at run ⊢
      by_cases falseBranch : isBool false value = true
      · rw [if_pos falseBranch] at run ⊢
        exact noIH ck res next run notTimeout
      · rw [if_neg falseBranch] at run ⊢
        simp only [typeError] at run ⊢
        obtain ⟨rfl, rfl⟩ := run
        rfl


/-- A force follows its thunk: the evaluated, direct, and body branches are each
    unchanged by a clock extension. -/
private theorem addClock_force {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      AddClockAt body next) :
    AddClockAt (.force ret label src) state := by
  intro ck res next run notTimeout
  simp only [evaluate] at run ⊢
  cases read : getVar src state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some thunk =>
    simp only [read] at run ⊢
    generalize destEq : destThunk thunk state.refs = dest at run ⊢
    cases dest with
    | badRef =>
      simp only [] at run ⊢
      simp only [typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | notThunk =>
      simp only [] at run ⊢
      simp only [typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | isThunk mode thunkValue =>
      cases mode with
      | evaluated =>
        simp only [] at run ⊢
        cases ret with
        | none =>
          simp only [] at run ⊢
          rw [flushState_addClockState] at ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl
        | some retPair =>
          obtain ⟨dest', names⟩ := retPair
          simp only [] at run ⊢
          cases cut : cutEnv names state.locals with
          | none =>
            simp only [cut, typeError] at run ⊢
            obtain ⟨rfl, rfl⟩ := run
            rfl
          | some env =>
            simp only [cut] at run ⊢
            have comm : { addClockState state ck with locals := env } =
                addClockState { state with locals := env } ck := rfl
            rw [comm, setVar_addClockState]
            obtain ⟨rfl, rfl⟩ := run
            rfl
      | notEvaluated =>
        simp only [] at run ⊢
        generalize foundEq : findCode (some label) [thunk, thunkValue] state.code
            state.stackFrameSizes = found at run ⊢
        cases found with
        | none =>
          simp only [] at run ⊢
          simp only [typeError] at run ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl
        | some entry =>
          obtain ⟨args, body, size⟩ := entry
          simp only [] at run ⊢
          cases ret with
          | none =>
            simp only [] at run ⊢
            by_cases zero : state.clock = 0
            · rw [if_pos zero] at run
              simp only [timeoutError] at run
              obtain ⟨rfl, _⟩ := run
              exact absurd rfl notTimeout
            · rw [if_neg zero] at run
              have positive : ¬ state.clock + ck = 0 := by omega
              rw [if_neg positive]
              rw [decClock_addClockState state ck zero, callEnv_addClockState]
              cases bodyRun : evaluate body (callEnv args size (decClock state)) with
              | mk bodyRes last =>
                rw [bodyRun] at run
                simp only [] at run
                have clockLt : (callEnv args size (decClock state)).clock < state.clock := by
                  simp only [callEnv, decClock]
                  omega
                have hresBody : bodyRes ≠ some (.err (.abort .timeoutError)) := by
                  intro h
                  rw [h] at run
                  simp only [] at run
                  obtain ⟨rfl, _⟩ := run
                  exact absurd rfl notTimeout
                have bodySwap := bodyIH body (callEnv args size (decClock state)) clockLt
                  ck bodyRes last bodyRun hresBody
                rw [bodySwap] at ⊢
                cases bodyRes with
                | none =>
                  simp only [] at run ⊢
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
                | some value =>
                  simp only [] at run ⊢
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
          | some retPair =>
            obtain ⟨dest', names⟩ := retPair
            simp only [] at run ⊢
            cases cut : cutEnv names state.locals with
            | none =>
              simp only [cut, typeError] at run ⊢
              obtain ⟨rfl, rfl⟩ := run
              rfl
            | some env =>
              simp only [cut] at run ⊢
              by_cases zero : state.clock = 0
              · rw [if_pos zero] at run
                simp only [timeoutError] at run
                obtain ⟨rfl, _⟩ := run
                exact absurd rfl notTimeout
              · rw [if_neg zero] at run
                have positive : ¬ state.clock + ck = 0 := by omega
                rw [if_neg positive]
                rw [decClock_addClockState state ck zero, pushEnv_addClockState,
                  callEnv_addClockState]
                cases bodyRun : evaluate body
                    (callEnv args size (pushEnv env false (decClock state))) with
                | mk bodyRes last =>
                  rw [bodyRun] at run
                  simp only [fixClock] at run
                  have clockLt : (callEnv args size
                      (pushEnv env false (decClock state))).clock < state.clock := by
                    simp only [callEnv, pushEnv, decClock]
                    omega
                  have hresBody : bodyRes ≠ some (.err (.abort .timeoutError)) := by
                    intro h
                    rw [h] at run
                    simp only [] at run
                    obtain ⟨rfl, _⟩ := run
                    exact absurd rfl notTimeout
                  have bodySwap := bodyIH body
                    (callEnv args size (pushEnv env false (decClock state))) clockLt
                    ck bodyRes last bodyRun hresBody
                  rw [bodySwap] at ⊢
                  rw [fixClock_addClockState] at ⊢
                  simp only [fixClock] at ⊢
                  cases bodyRes with
                  | none =>
                    simp only [] at run ⊢
                    obtain ⟨rfl, rfl⟩ := run
                    rfl
                  | some result =>
                    cases result with
                    | err error =>
                      simp only [] at run ⊢
                      obtain ⟨rfl, rfl⟩ := run
                      rfl
                    | val values =>
                      cases values with
                      | nil =>
                        simp only [] at run ⊢
                        obtain ⟨rfl, rfl⟩ := run
                        rfl
                      | cons v rest =>
                        cases rest with
                        | nil =>
                          simp only [] at run ⊢
                          rw [popEnv_addClockState]
                          cases pop : popEnv
                              { last with clock := min (callEnv args size
                                (pushEnv env false (decClock state))).clock last.clock } with
                          | none =>
                            simp only [pop, Option.map_none] at run ⊢
                            simp only [typeError] at run ⊢
                            obtain ⟨rfl, rfl⟩ := run
                            rfl
                          | some poppedNext =>
                            simp only [pop, Option.map_some] at run ⊢
                            obtain ⟨rfl, rfl⟩ := run
                            rw [setVar_addClockState]
                        | cons _ _ =>
                          simp only [] at run ⊢
                          obtain ⟨rfl, rfl⟩ := run
                          rfl

/-- A call follows the callee body and, on a raised exception, the handler. -/
private theorem addClock_call {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ body : DataLang.Prog, ∀ next : State C F, next.clock < state.clock →
      AddClockAt body next) :
    AddClockAt (.call ret dest names handler) state := by
  intro ck res next run notTimeout
  simp only [evaluate] at run ⊢
  cases read : getVars names state.locals with
  | none =>
    simp only [read, typeError] at run ⊢
    obtain ⟨rfl, rfl⟩ := run
    rfl
  | some values =>
    simp only [read] at run ⊢
    generalize foundEq : findCode dest values state.code state.stackFrameSizes = found at run ⊢
    cases found with
    | none =>
      simp only [] at run ⊢
      simp only [typeError] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      rfl
    | some entry =>
      obtain ⟨args, body, size⟩ := entry
      simp only [] at run ⊢
      cases ret with
      | none =>
        simp only [] at run ⊢
        by_cases someHandler : handler.isSome = true
        · rw [if_pos someHandler] at run ⊢
          simp only [typeError] at run ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl
        · rw [if_neg someHandler] at run ⊢
          by_cases zero : state.clock = 0
          · rw [if_pos zero] at run
            simp only [timeoutError] at run
            obtain ⟨rfl, _⟩ := run
            exact absurd rfl notTimeout
          · rw [if_neg zero] at run
            have positive : ¬ state.clock + ck = 0 := by omega
            rw [if_neg positive]
            rw [decClock_addClockState state ck zero, callEnv_addClockState]
            cases bodyRun : evaluate body (callEnv args size (decClock state)) with
            | mk bodyRes last =>
              rw [bodyRun] at run
              simp only [] at run
              have clockLt : (callEnv args size (decClock state)).clock < state.clock := by
                simp only [callEnv, decClock]
                omega
              have hresBody : bodyRes ≠ some (.err (.abort .timeoutError)) := by
                intro h
                rw [h] at run
                simp only [] at run
                obtain ⟨rfl, _⟩ := run
                exact absurd rfl notTimeout
              have bodySwap := bodyIH body (callEnv args size (decClock state)) clockLt
                ck bodyRes last bodyRun hresBody
              rw [bodySwap] at ⊢
              cases bodyRes with
              | none =>
                simp only [] at run ⊢
                obtain ⟨rfl, rfl⟩ := run
                rfl
              | some value =>
                simp only [] at run ⊢
                obtain ⟨rfl, rfl⟩ := run
                rfl
      | some retPair =>
        obtain ⟨returns, live⟩ := retPair
        simp only [] at run ⊢
        by_cases nodup : (!returns.Nodup) = true
        · rw [if_pos nodup] at run ⊢
          simp only [typeError] at run ⊢
          obtain ⟨rfl, rfl⟩ := run
          rfl
        · rw [if_neg nodup] at run ⊢
          cases cut : cutEnv live state.locals with
          | none =>
            simp only [cut, typeError] at run ⊢
            obtain ⟨rfl, rfl⟩ := run
            rfl
          | some env =>
            simp only [cut] at run ⊢
            by_cases zero : state.clock = 0
            · rw [if_pos zero] at run
              simp only [timeoutError] at run
              obtain ⟨rfl, _⟩ := run
              exact absurd rfl notTimeout
            · rw [if_neg zero] at run
              have positive : ¬ state.clock + ck = 0 := by omega
              rw [if_neg positive]
              rw [decClock_addClockState state ck zero, pushEnv_addClockState,
                callEnv_addClockState]
              cases bodyRun : evaluate body
                  (callEnv args size (pushEnv env handler.isSome (decClock state))) with
              | mk bodyRes last =>
                rw [bodyRun] at run
                simp only [fixClock] at run
                have clockLt : (callEnv args size
                    (pushEnv env handler.isSome (decClock state))).clock < state.clock := by
                  simp only [callEnv, pushEnv, decClock]
                  omega
                have hresBody : bodyRes ≠ some (.err (.abort .timeoutError)) := by
                  intro h
                  rw [h] at run
                  simp only [] at run
                  obtain ⟨rfl, _⟩ := run
                  exact absurd rfl notTimeout
                have bodySwap := bodyIH body
                  (callEnv args size (pushEnv env handler.isSome (decClock state))) clockLt
                  ck bodyRes last bodyRun hresBody
                rw [bodySwap] at ⊢
                rw [fixClock_addClockState] at ⊢
                simp only [fixClock] at ⊢
                cases bodyRes with
                | none =>
                  simp only [] at run ⊢
                  obtain ⟨rfl, rfl⟩ := run
                  rfl
                | some result =>
                  cases result with
                  | err error =>
                    cases error with
                    | abort reason =>
                      simp only [] at run ⊢
                      obtain ⟨rfl, rfl⟩ := run
                      rfl
                    | raise value =>
                      simp only [] at run ⊢
                      cases handler with
                      | none =>
                        simp only [Option.isSome_none] at run ⊢
                        obtain ⟨rfl, rfl⟩ := run
                        rfl
                      | some entry =>
                        obtain ⟨handlerName, handlerBody⟩ := entry
                        simp only [Option.isSome_some] at run ⊢
                        rw [setVar_addClockState] at ⊢
                        let handlerState : State C F := setVar handlerName value
                          (fixClock (callEnv args size (pushEnv env true (decClock state)))
                            ((some (.err (.raise value)) :
                              Option (Result (List DataSem.Value) DataSem.Value)),
                              last)).2
                        have handlerClock : handlerState.clock < state.clock := by
                          simp only [handlerState, setVar, fixClock]
                          exact lt_of_le_of_lt (Nat.min_le_left _ _) clockLt
                        exact bodyIH handlerBody handlerState handlerClock ck res next
                          run notTimeout
                  | val values =>
                    simp only [] at run ⊢
                    by_cases sameLength : values.length = returns.length
                    · rw [if_pos sameLength] at run ⊢
                      rw [popEnv_addClockState]
                      cases pop : popEnv
                          { last with clock := min (callEnv args size
                            (pushEnv env handler.isSome (decClock state))).clock last.clock } with
                      | none =>
                        simp only [pop, Option.map_none] at run ⊢
                        simp only [typeError] at run ⊢
                        obtain ⟨rfl, rfl⟩ := run
                        rfl
                      | some poppedNext =>
                        simp only [pop, Option.map_some] at run ⊢
                        obtain ⟨rfl, rfl⟩ := run
                        rw [setVars_addClockState]
                    · rw [if_neg sameLength] at run ⊢
                      simp only [typeError] at run ⊢
                      obtain ⟨rfl, rfl⟩ := run
                      rfl

/-- Every program satisfies the add-clock property, by the lexicographic
    `(clock, weight)` induction over the program. -/
private theorem addClock_all {C F : Type} (program : DataLang.Prog) (state : State C F) :
    AddClockAt program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => AddClockAt program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact addClock_skip state
  | move dest src => exact addClock_move dest src state
  | assign dest op names live => exact addClock_assign dest op names live state
  | tick => exact addClock_tick state
  | makeSpace amount names => exact addClock_makeSpace amount names state
  | raise name => exact addClock_raise name state
  | «return» names => exact addClock_return names state
  | seq first second =>
    apply addClock_seq first second state
    · exact exprIH first state (by omega)
        (by
          simp only [DataLang.Prog.seq.sizeOf_spec]
          omega)
    · intro mid bound
      exact exprIH second mid bound
        (by
          simp only [DataLang.Prog.seq.sizeOf_spec]
          omega)
  | ifThenElse name yes no =>
    apply addClock_if name yes no state
    · exact exprIH yes state (by omega)
        (by
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
          omega)
    · exact exprIH no state (by omega)
        (by
          simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
          omega)
  | force ret label src =>
    apply addClock_force ret label src state
    intro body next clockLt
    exact smaller body next clockLt
  | call ret dest names handler =>
    apply addClock_call ret dest names handler state
    intro body next clockLt
    exact smaller body next clockLt

/-- Adding `ck` to the starting clock adds `ck` to the final clock and leaves the
    evaluation result unchanged, unless the original run times out. Port of HOL
    `evaluate_add_clock`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_add_clock"]
theorem evaluate_add_clock {C F : Type} (program : DataLang.Prog) (state : State C F)
    (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (premise : evaluate program state = (res, next) ∧
      res ≠ some (.err (.abort .timeoutError)))
    (ck : Nat) :
    evaluate program { state with clock := state.clock + ck } =
      (res, { next with clock := next.clock + ck }) :=
  addClock_all program state ck res next premise.1 premise.2

end Flapjack.Compiler.Backend.DataProps
