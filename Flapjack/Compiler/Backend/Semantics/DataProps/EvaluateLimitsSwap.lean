module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackLocalsSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.CutFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceSwap
public import Flapjack.Misc.ClockWeightInduction
public import Flapjack.HolRef

@[expose] public section

/-!
# Limits replacement under data evaluation

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2325`
`evaluate_swap_limits`, together with the consequences `evaluate_zero_limits_FST`
(`:2484`) and `evaluate_zero_limits_ffi` (`:2494`).

The induction runs over a state relation rather than HOL's explicit list of
replaced fields: two states are related when they agree on every field the
evaluator reads except the stack maximum and the resource observations, with the
second state's limits fixed at the swapped-in value. That relation is exactly the
shape of HOL's conclusion.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.DataSem

/-- Two states are related for the limits swap when the second is the first with
    the limits set to the swapped-in value and the stack maximum, the safety flag
    and the peak heap length replaced. -/
@[simp] private def LimitSwapState {C F : Type} (lim : Limits) (state other : State C F) : Prop :=
  other = { state with
    limits := lim
    stackMax := other.stackMax
    safeForSpace := other.safeForSpace
    peakHeapLength := other.peakHeapLength }

/-- The related state agrees on the locals. -/
private theorem limitSwapState_locals {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.locals = state.locals := by rw [h]

/-- The related state agrees on the references. -/
private theorem limitSwapState_refs {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.refs = state.refs := by rw [h]

/-- The related state agrees on the clock. -/
private theorem limitSwapState_clock {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.clock = state.clock := by rw [h]

/-- The related state agrees on the code map. -/
private theorem limitSwapState_code {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.code = state.code := by rw [h]

/-- The related state agrees on the stack. -/
private theorem limitSwapState_stack {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.stack = state.stack := by rw [h]

/-- The related state agrees on the locals size. -/
private theorem limitSwapState_localsSize {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.localsSize = state.localsSize := by rw [h]

/-- The related state agrees on the handler index. -/
private theorem limitSwapState_handler {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.handler = state.handler := by rw [h]

/-- The related state agrees on the frame-size map. -/
private theorem limitSwapState_stackFrameSizes {C F : Type} {lim : Limits}
    {state other : State C F}
    (h : LimitSwapState lim state other) : other.stackFrameSizes = state.stackFrameSizes := by
  rw [h]

/-- The related state agrees on the global pointer. -/
private theorem limitSwapState_global {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.global = state.global := by rw [h]

/-- The related state agrees on the FFI state. -/
private theorem limitSwapState_ffi {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.ffi = state.ffi := by rw [h]

/-- The related state agrees on the space counter. -/
private theorem limitSwapState_space {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.space = state.space := by rw [h]

/-- The related state agrees on the time stamps. -/
private theorem limitSwapState_tstamps {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.tstamps = state.tstamps := by rw [h]

/-- The related state agrees on the compiler configuration. -/
private theorem limitSwapState_compile {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) : other.compile = state.compile := by rw [h]

/-- The related state agrees on the compiler oracle. -/
private theorem limitSwapState_compileOracle {C F : Type} {lim : Limits}
    {state other : State C F}
    (h : LimitSwapState lim state other) : other.compileOracle = state.compileOracle := by
  rw [h]

/-- The limits swap at one program and starting state, for a fixed swapped-in
    limits value. -/
private def LimitSwapAt {C F : Type} (lim : Limits) (program : DataLang.Prog)
    (state : State C F) : Prop :=
  ∀ (res : Option (Result (List DataSem.Value) DataSem.Value)) (next : State C F)
    (other : State C F),
    evaluate program state = (res, next) →
    LimitSwapState lim state other →
    ∃ other', evaluate program other = (res, other') ∧ LimitSwapState lim next other'

/-- Clearing the locals size and the stack keeps the relation: only the locals,
    the locals size and the stack change. -/
private theorem clearState_limitSwap {C F : Type} {lim : Limits} {state other : State C F}
    (h : LimitSwapState lim state other) :
    LimitSwapState lim { state with stack := [], locals := .ln }
      { other with stack := [], locals := .ln } := by
  rw [h]
  simp

/-- Installing the safety flag keeps the relation: it only updates the safety
    observation. -/
private theorem installSfs_limitSwap {C F : Type} {lim : Limits} (op : ClosLang.Op)
    {state other : State C F} (h : LimitSwapState lim state other) :
    LimitSwapState lim (installSfs op state) (installSfs op other) := by
  unfold installSfs
  rw [h]
  simp

/-- Assigning a local keeps the relation: only the locals change, and both
    states install the same binding. -/
private theorem setVar_limitSwap {C F : Type} {lim : Limits} (dest : Nat)
    (value : DataSem.Value) {state other : State C F} (h : LimitSwapState lim state other) :
    LimitSwapState lim (setVar dest value state) (setVar dest value other) := by
  unfold setVar
  rw [h]
  simp

/-- Assigning several locals keeps the relation: only the locals change, and
    both states install the same bindings. -/
private theorem setVars_limitSwap {C F : Type} {lim : Limits} (names : List Nat)
    (values : List DataSem.Value) {state other : State C F} (h : LimitSwapState lim state other) :
    LimitSwapState lim (setVars names values state) (setVars names values other) := by
  unfold setVars
  rw [h]
  simp

/-- Flushing the state keeps the relation: it clears the locals, the locals size
    and the stack. -/
private theorem flushState_limitSwap {C F : Type} {lim : Limits} (all : Bool)
    {state other : State C F} (h : LimitSwapState lim state other) :
    LimitSwapState lim (flushState all state) (flushState all other) := by
  unfold flushState
  cases all with
  | false =>
    rw [h]
    simp
  | true =>
    rw [h]
    simp

/-- A successful primitive application at a related state succeeds with the same
    value and a related result state. -/
private theorem doApp_limitSwap {C F : Type} {lim : Limits} (op : ClosLang.Op)
    (values : List DataSem.Value) (state other : State C F) (value : DataSem.Value)
    (next : State C F) (h : LimitSwapState lim state other)
    (run : doApp op values state = .val (value, next)) :
    ∃ otherNext, doApp op values other = .val (value, otherNext) ∧
      LimitSwapState lim next otherNext := by
  obtain ⟨safe', peak', mx', step1⟩ := doApp_limSwap op values state value next lim run
  obtain ⟨safe'', peak'', mx'', step2⟩ :=
    doApp_stackSafePeakSwap op values
      { state with limits := lim }
      value
      { next with
          limits := lim
          stackMax := mx'
          safeForSpace := safe'
          peakHeapLength := peak' }
      other.stackMax other.safeForSpace other.peakHeapLength step1
  refine ⟨{ next with
      limits := lim
      stackMax := mx''
      safeForSpace := safe''
      peakHeapLength := peak'' }, ?_, ?_⟩
  · rw [h]
    exact step2
  · simp

/-- A failed primitive application at a related state fails the same way. -/
private theorem doApp_err_limitSwap {C F : Type} {lim : Limits} (op : ClosLang.Op)
    (values : List DataSem.Value) (state other : State C F)
    (error : ErrorResult DataSem.Value)
    (h : LimitSwapState lim state other) (run : doApp op values state = .err error) :
    doApp op values other = .err error := by
  have step1 := doApp_err_limSwap op values state error lim run
  have step2 := doApp_err_lssStackSafePeakSwap op values
    { state with limits := lim } error state.localsSize other.stackMax
    other.safeForSpace other.peakHeapLength step1
  rw [h]
  exact step2

/-- An exception jump at a related state jumps to a related result: the unwound
    frame is read from the same stack at the same handler index. -/
private theorem jumpExc_limitSwap {C F : Type} {lim : Limits} (state other jumped : State C F)
    (h : LimitSwapState lim state other) (run : jumpExc state = some jumped) :
    ∃ jumped', jumpExc other = some jumped' ∧ LimitSwapState lim jumped jumped' := by
  obtain ⟨hlt, n, e, ls, xs1, lastN, jumpedEq⟩ := jumpExcImp state jumped run
  have stackEq := limitSwapState_stack h
  have handlerEq := limitSwapState_handler h
  have hltX : other.handler < other.stack.length := by
    rw [handlerEq, stackEq]
    exact hlt
  have lastX : wordSemLastN (other.handler + 1) other.stack = .exc ls e n :: xs1 := by
    rw [handlerEq, stackEq]
    exact lastN
  subst jumpedEq
  have jumpSwap :
      jumpExc other =
        some { other with
                localsSize := ls
                stack := xs1
                handler := n
                locals := e } := by
    unfold jumpExc
    rw [if_pos hltX, ← wordSemLastN_eq_drop, lastX]
  refine ⟨_, jumpSwap, ?_⟩
  rw [h]
  simp

/-- Entering a call at a related state keeps the relation: the locals become the
    same argument list, and the resource observations are free. -/
private theorem callEnv_limitSwap {C F : Type} {lim : Limits} (args : List DataSem.Value)
    (size : Option Nat)
    (state other : State C F) (h : LimitSwapState lim state other) :
    LimitSwapState lim (DataSem.callEnv args size state)
      (DataSem.callEnv args size other) := by
  unfold DataSem.callEnv
  rw [h]
  simp

/-- Pushing an environment frame at a related state keeps the relation: the
    pushed frame carries the same environment. -/
private theorem pushEnv_limitSwap {C F : Type} {lim : Limits} (env : Spt DataSem.Value)
    (handler : Bool) (state other : State C F) (h : LimitSwapState lim state other) :
    LimitSwapState lim (DataSem.pushEnv env handler state)
      (DataSem.pushEnv env handler other) := by
  unfold DataSem.pushEnv
  rw [h]
  simp

/-- Restoring a saved environment at a related state keeps the relation. -/
private theorem popEnv_limitSwap {C F : Type} {lim : Limits} (state other next : State C F)
    (h : LimitSwapState lim state other) (run : DataSem.popEnv state = some next) :
    ∃ next', DataSem.popEnv other = some next' ∧ LimitSwapState lim next next' := by
  have stackEq := limitSwapState_stack h
  cases stackEq' : state.stack with
  | nil => simp [DataSem.popEnv, stackEq'] at run
  | cons frame rest =>
    simp only [DataSem.popEnv, stackEq'] at run
    cases frame with
    | env size env =>
      obtain ⟨rfl⟩ := Option.some.inj run
      refine ⟨{ other with locals := env, stack := rest, localsSize := size }, ?_, ?_⟩
      · simp only [DataSem.popEnv, stackEq, stackEq']
      · rw [h]
        simp
    | exc size env handler =>
      obtain ⟨rfl⟩ := Option.some.inj run
      refine ⟨{ other with
          locals := env
          stack := rest
          localsSize := size
          handler := handler }, ?_, ?_⟩
      · simp only [DataSem.popEnv, stackEq, stackEq']
      · rw [h]
        simp

/-- When the original stack cannot be popped, neither can a related stack. -/
private theorem popEnv_none_limitSwap {C F : Type} {lim : Limits} (state other : State C F)
    (h : LimitSwapState lim state other) (run : DataSem.popEnv state = none) :
    DataSem.popEnv other = none := by
  have stackEq := limitSwapState_stack h
  cases stackEq' : state.stack with
  | nil => simp [DataSem.popEnv, stackEq, stackEq']
  | cons frame rest =>
    cases frame with
    | env size env => simp [DataSem.popEnv, stackEq'] at run
    | exc size env handler => simp [DataSem.popEnv, stackEq'] at run

/-- The narrow cut keeps the relation: it reads only the locals and installs the
    same environment. -/
private theorem cutStateOpt_limitSwap {C F : Type} {lim : Limits} (live : Option NumSet)
    (state other next : State C F)
    (h : LimitSwapState lim state other) (cut : cutStateOpt live state = some next) :
    ∃ otherNext, cutStateOpt live other = some otherNext ∧ LimitSwapState lim next otherNext := by
  cases live with
  | none =>
    simp only [cutStateOpt, Option.some.injEq] at cut
    subst cut
    exact ⟨other, by simp [cutStateOpt], h⟩
  | some names =>
    simp only [cutStateOpt, cutState, Option.map_eq_some_iff] at cut
    obtain ⟨env, envEq, nextEq⟩ := cut
    subst nextEq
    refine ⟨{ other with locals := env }, ?_, ?_⟩
    · simp [cutStateOpt, cutState, limitSwapState_locals h, envEq]
    · rw [h]
      simp

/-- Clamping the clock keeps the relation, because both runs agree on the clocks. -/
private theorem fixClock_limitSwap {C F : Type} {lim : Limits} {state other : State C F}
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (next otherNext : State C F)
    (h : LimitSwapState lim state other) (rel : LimitSwapState lim next otherNext) :
    LimitSwapState lim (fixClock state (result, next)).2
      (fixClock other (result, otherNext)).2 := by
  have clockEq := limitSwapState_clock h
  have nextClockEq := limitSwapState_clock rel
  unfold fixClock
  rw [h, rel]
  simp

/-- The `Skip` case. -/
private theorem limitSwap_skip {C F : Type} (lim : Limits) (state : State C F) :
    LimitSwapAt lim (.skip : DataLang.Prog) state := by
  intro res next other run h
  simp only [evaluate, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨other, by simp [evaluate], h⟩

/-- The `Move` case. -/
private theorem limitSwap_move {C F : Type} (lim : Limits) (dest src : Nat)
    (state : State C F) : LimitSwapAt lim (.move dest src) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨setVar dest value other, ?_, ?_⟩
    · simp [evaluate, localsEq, read]
    · rw [h]
      simp [setVar]

/-- The `Tick` case. -/
private theorem limitSwap_tick {C F : Type} (lim : Limits) (state : State C F) :
    LimitSwapAt lim (.tick : DataLang.Prog) state := by
  intro res next other run h
  have clockEq := limitSwapState_clock h
  by_cases zero : state.clock = 0
  · simp only [evaluate, zero, timeoutError] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState true other, ?_, ?_⟩
    · simp [evaluate, timeoutError, clockEq, if_pos zero]
    · rw [h]
      simp [flushState]
  · simp only [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨decClock other, ?_, ?_⟩
    · simp [evaluate, clockEq, if_neg zero]
    · rw [h]
      simp [decClock]

/-- The `MakeSpace` case. -/
private theorem limitSwap_makeSpace {C F : Type} (lim : Limits) (amount : Nat)
    (names : NumSet) (state : State C F) : LimitSwapAt lim (.makeSpace amount names) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  cases cut : cutEnv names state.locals with
  | none =>
    simp only [evaluate, cut, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, cut]
  | some env =>
    simp only [evaluate, cut, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨addSpace { other with locals := env } amount, ?_, ?_⟩
    · simp [evaluate, localsEq, cut]
    · rw [h]
      simp [addSpace]

/-- The `Return` case. -/
private theorem limitSwap_return {C F : Type} (lim : Limits) (names : List Nat)
    (state : State C F) : LimitSwapAt lim (.return names) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  cases read : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some values =>
    simp only [evaluate, read, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState false other, ?_, ?_⟩
    · simp [evaluate, localsEq, read]
    · rw [h]
      simp [flushState]

/-- The `If` case. -/
private theorem limitSwap_if {C F : Type} (lim : Limits) (name : Nat)
    (yes no : DataLang.Prog) (state : State C F) (yesIH : LimitSwapAt lim yes state)
    (noIH : LimitSwapAt lim no state) :
    LimitSwapAt lim (.ifThenElse name yes no) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    by_cases yesValue : isBool true value
    · have branch : evaluate yes state = (res, next) := by
        simpa [evaluate, read, yesValue] using run
      simpa [evaluate, localsEq, read, yesValue] using yesIH res next other branch h
    · by_cases noValue : isBool false value
      · have branch : evaluate no state = (res, next) := by
          simpa [evaluate, read, yesValue, noValue] using run
        simpa [evaluate, localsEq, read, yesValue, noValue] using noIH res next other branch h
      · simp only [evaluate, read, yesValue, noValue, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨other, ?_, h⟩
        simp [evaluate, typeError, localsEq, read, yesValue, noValue]

/-- A sequential composition whose first half has stopped returns the first
    half's result. -/
private theorem seq_some_limit {C F : Type} (first second : DataLang.Prog)
    (state : State C F) (stopped : Result (List DataSem.Value) DataSem.Value)
    (next : State C F) (run : evaluate first state = (some stopped, next)) :
    evaluate (.seq first second) state = (some stopped, next) := by
  have bound : next.clock ≤ state.clock := by simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- A sequential composition whose first half continues evaluates the second
    half at the first half's result state. -/
private theorem seq_none_limit {C F : Type} (first second : DataLang.Prog)
    (state mid : State C F) (run : evaluate first state = (none, mid)) :
    evaluate (.seq first second) state = evaluate second mid := by
  have bound : mid.clock ≤ state.clock := by simpa only [run] using evaluate_clock_le first state
  simp only [evaluate, run, fixClock, Nat.min_eq_right bound]

/-- The `Seq` case. -/
private theorem limitSwap_seq {C F : Type} (lim : Limits) (first second : DataLang.Prog)
    (state : State C F) (firstIH : LimitSwapAt lim first state)
    (secondIH : ∀ mid : State C F, mid.clock ≤ state.clock → LimitSwapAt lim second mid) :
    LimitSwapAt lim (.seq first second) state := by
  intro res next other run h
  cases firstRun : evaluate first state with
  | mk outcome mid =>
    have midClock : mid.clock ≤ state.clock := by
      simpa only [firstRun] using evaluate_clock_le first state
    obtain ⟨midOther, firstOther, relMid⟩ := firstIH outcome mid other firstRun h
    cases outcome with
    | some stopped =>
      have clamp : fixClock state (evaluate first state) = (some stopped, mid) := by
        rw [fixClockEvaluate, firstRun]
      have hres : res = some stopped := by
        have hh := congrArg Prod.fst run
        simpa only [evaluate, clamp] using hh.symm
      have hnext : next = mid := by
        have hh := congrArg Prod.snd run
        simpa only [evaluate, clamp] using hh.symm
      rw [hres, hnext]
      refine ⟨midOther, ?_, relMid⟩
      rw [seq_some_limit first second other stopped midOther firstOther]
    | none =>
      have secondRun : evaluate second mid = (res, next) := by
        have clamp : fixClock state (evaluate first state) = (none, mid) := by
          rw [fixClockEvaluate, firstRun]
        simpa only [evaluate, clamp] using run
      obtain ⟨lastOther, secondOther, relLast⟩ :=
        secondIH mid midClock res next midOther secondRun relMid
      refine ⟨lastOther, ?_, relLast⟩
      rw [seq_none_limit first second other midOther firstOther]
      exact secondOther

/-- The `Assign` case. -/
private theorem limitSwap_assign {C F : Type} (lim : Limits) (dest : Nat)
    (op : ClosLang.Op) (names : List Nat) (live : Option NumSet) (state : State C F) :
    LimitSwapAt lim (.assign dest op names live) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  by_cases needs : (DataLang.opRequiresNames op == live.isNone) = true
  · simp only [evaluate, needs, typeError] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨other, by simp [evaluate, needs], h⟩
  · have needsFalse : (DataLang.opRequiresNames op == live.isNone) = false := by
      simpa using needs
    simp only [evaluate, needsFalse] at run
    cases vars : DataSem.getVars names state.locals with
    | none =>
      simp only [vars, typeError] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, needsFalse, localsEq, vars]
    | some values =>
      simp only [vars] at run
      have varsOther : DataSem.getVars names other.locals = some values := by
        rw [localsEq]
        exact vars
      cases cut : cutStateOpt live state with
      | none =>
        simp only [cut, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        have cutOther : cutStateOpt live other = none := by
          cases live with
          | none => simp [cutStateOpt] at cut
          | some names =>
            cases envEq : cutEnv names state.locals with
            | none =>
              simp only [cutStateOpt, cutState, envEq] at cut ⊢
              rw [limitSwapState_locals h, envEq]
              rfl
            | some env =>
              simp only [cutStateOpt, cutState, envEq] at cut
              simp at cut
        refine ⟨other, ?_, h⟩
        simp [evaluate, typeError, needsFalse, varsOther, cutOther]
      | some mid =>
        simp only [cut] at run
        obtain ⟨midOther, cutOtherRun, relMid⟩ := cutStateOpt_limitSwap live state other mid h cut
        cases app : doApp op values mid with
        | err error =>
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          have appOther := doApp_err_limitSwap op values mid midOther error relMid app
          refine ⟨flushState true (installSfs op midOther), ?_, ?_⟩
          · simp [evaluate, needsFalse, varsOther, cutOtherRun, appOther]
          · exact flushState_limitSwap true (installSfs_limitSwap op relMid)
        | val pair =>
          obtain ⟨value, last⟩ := pair
          simp only [app] at run
          obtain ⟨rfl, rfl⟩ := run
          obtain ⟨lastOther, appOther, relLast⟩ :=
            doApp_limitSwap op values mid midOther value last relMid app
          refine ⟨setVar dest value (installSfs op lastOther), ?_, ?_⟩
          · simp [evaluate, needsFalse, varsOther, cutOtherRun, appOther]
          · exact setVar_limitSwap dest value (installSfs_limitSwap op relLast)

/-- The `Raise` case. -/
private theorem limitSwap_raise {C F : Type} (lim : Limits) (name : Nat)
    (state : State C F) : LimitSwapAt lim (.raise name) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  cases read : getVar name state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some value =>
    cases jump : jumpExc state with
    | none =>
      simp only [evaluate, read, jump, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have jumpOther : jumpExc other = none := by
        cases otherJump : jumpExc other with
        | none => rfl
        | some jumped =>
          obtain ⟨hlt, n, e, ls, xs1, lastN, _⟩ := jumpExcImp other jumped otherJump
          rw [limitSwapState_handler h, limitSwapState_stack h] at hlt lastN
          have jumpSome : jumpExc state =
              some { state with localsSize := ls, stack := xs1, handler := n, locals := e } := by
            unfold jumpExc
            rw [if_pos hlt, ← wordSemLastN_eq_drop, lastN]
          rw [jumpSome] at jump
          cases jump
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, localsEq, read, jumpOther]
    | some jumped =>
      simp only [evaluate, read, jump, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨jumpedOther, jumpOther, relJumped⟩ := jumpExc_limitSwap state other jumped h jump
      refine ⟨jumpedOther, ?_, relJumped⟩
      simp [evaluate, localsEq, read, jumpOther]

/-- The `Force` case without a destination. -/
private theorem limitSwap_tailForce {C F : Type} (lim : Limits) (label src : Nat)
    (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → LimitSwapAt lim body called) :
    LimitSwapAt lim (.force none label src) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  have refsEq := limitSwapState_refs h
  have clockEq := limitSwapState_clock h
  have codeEq := limitSwapState_code h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp only [evaluate, read, th, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨flushState false other, ?_, ?_⟩
        · simp [evaluate, localsEq, read, refsEq, th]
        · rw [h]
          simp [flushState]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have foundOther :
              findCode (some label) [thunk, value] other.code other.stackFrameSizes = none := by
            rw [codeEq, limitSwapState_stackFrameSizes h]
            exact found
          refine ⟨other, ?_, h⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, foundOther]
        | some foundEntry =>
          obtain ⟨args, body, size⟩ := foundEntry
          have foundOther :
              findCode (some label) [thunk, value] other.code other.stackFrameSizes =
                some (args, body, size) := by
            rw [codeEq, limitSwapState_stackFrameSizes h]
            exact found
          by_cases zero : state.clock = 0
          · simp only [evaluate, read, th, found, if_pos zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            let callState := DataSem.callEnv args size (DataSem.decClock state)
            let callOther := DataSem.callEnv args size (DataSem.decClock other)
            refine ⟨{ other with stack := [], locals := .ln }, ?_, ?_⟩
            · simp [evaluate, timeoutError, localsEq, read, refsEq, th, foundOther,
                clockEq, if_pos zero]
            · exact clearState_limitSwap h
          · let callState := DataSem.callEnv args size (DataSem.decClock state)
            let callOther := DataSem.callEnv args size (DataSem.decClock other)
            have clockLt : callState.clock < state.clock := by
              simp only [callState, DataSem.callEnv, DataSem.decClock]
              omega
            have relCall : LimitSwapState lim callState callOther :=
              callEnv_limitSwap args size (DataSem.decClock state) (DataSem.decClock other)
                (by
                  rw [h]
                  simp [DataSem.decClock])
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              obtain ⟨lastOther, bodyOther, relBody⟩ :=
                bodyIH body callState clockLt outcome last callOther bodyRun relCall
              have bodyRun' :
                  evaluate body (DataSem.callEnv args size (DataSem.decClock state)) =
                    (outcome, last) := bodyRun
              have bodyOther' :
                  evaluate body (DataSem.callEnv args size (DataSem.decClock other)) =
                    (outcome, lastOther) := bodyOther
              have bodyOther' :
                  evaluate body (DataSem.callEnv args size (DataSem.decClock other)) =
                    (outcome, lastOther) := bodyOther
              simp only [evaluate, read, th, found, if_neg zero] at run
              rw [bodyRun'] at run
              cases outcome with
              | none =>
                simp only [typeError] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨lastOther, ?_, relBody⟩
                simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                  if_neg zero, bodyOther', typeError]
              | some stopped =>
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨lastOther, ?_, relBody⟩
                simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                  if_neg zero, bodyOther']

/-- The `Force` case with a destination. -/
private theorem limitSwap_returningForce {C F : Type} (lim : Limits) (dest : Nat)
    (live : NumSet) (label src : Nat) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → LimitSwapAt lim body called) :
    LimitSwapAt lim (.force (some (dest, live)) label src) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  have refsEq := limitSwapState_refs h
  have clockEq := limitSwapState_clock h
  have codeEq := limitSwapState_code h
  cases read : getVar src state.locals with
  | none =>
    simp only [evaluate, read, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, read]
  | some thunk =>
    cases th : destThunk thunk state.refs with
    | badRef =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | notThunk =>
      simp only [evaluate, read, th, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, localsEq, read, refsEq, th]
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        cases cut : cutEnv live state.locals with
        | none =>
          simp only [evaluate, read, th, cut, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, cut]
        | some env =>
          simp only [evaluate, read, th, cut, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨setVar dest value { other with locals := env }, ?_, ?_⟩
          · simp [evaluate, localsEq, read, refsEq, th, cut]
          · rw [h]
            simp [setVar]
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] state.code state.stackFrameSizes with
        | none =>
          simp only [evaluate, read, th, found, typeError, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl⟩ := run
          have foundOther :
              findCode (some label) [thunk, value] other.code other.stackFrameSizes = none := by
            rw [codeEq, limitSwapState_stackFrameSizes h]
            exact found
          refine ⟨other, ?_, h⟩
          simp [evaluate, typeError, localsEq, read, refsEq, th, foundOther]
        | some foundEntry =>
          obtain ⟨args, body, size⟩ := foundEntry
          have foundOther :
              findCode (some label) [thunk, value] other.code other.stackFrameSizes =
                some (args, body, size) := by
            rw [codeEq, limitSwapState_stackFrameSizes h]
            exact found
          cases cut : cutEnv live state.locals with
          | none =>
            simp only [evaluate, read, th, found, cut, typeError, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨other, ?_, h⟩
            simp [evaluate, typeError, localsEq, read, refsEq, th, foundOther, cut]
          | some env =>
            by_cases zero : state.clock = 0
            · simp only [evaluate, read, th, found, cut, if_pos zero, timeoutError] at run
              obtain ⟨rfl, rfl⟩ := run
              let callState :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
              let callOther :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock other))
              refine ⟨{ callOther with stack := [], locals := .ln }, ?_, ?_⟩
              · simp [evaluate, timeoutError, localsEq, read, refsEq, th, foundOther,
                  clockEq, cut, callOther, if_pos zero]
              · simpa [zero, callState, callOther] using
                  clearState_limitSwap
                    (callEnv_limitSwap args size
                      (DataSem.pushEnv env false (DataSem.decClock state))
                      (DataSem.pushEnv env false (DataSem.decClock other))
                      (pushEnv_limitSwap env false (DataSem.decClock state)
                        (DataSem.decClock other) (by
                          rw [h]
                          simp [DataSem.decClock])))
            · let callState :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
              let callOther :=
                DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock other))
              have clockLt : callState.clock < state.clock := by
                simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
                omega
              have relCall : LimitSwapState lim callState callOther :=
                callEnv_limitSwap args size
                  (DataSem.pushEnv env false (DataSem.decClock state))
                  (DataSem.pushEnv env false (DataSem.decClock other))
                  (pushEnv_limitSwap env false (DataSem.decClock state)
                    (DataSem.decClock other) (by
                      rw [h]
                      simp [DataSem.decClock]))
              cases bodyRun : evaluate body callState with
              | mk outcome last =>
                obtain ⟨lastOther, bodyOther, relBody⟩ :=
                  bodyIH body callState clockLt outcome last callOther bodyRun relCall
                have bodyRun' :
                    evaluate body
                        (DataSem.callEnv args size
                          (DataSem.pushEnv env false (DataSem.decClock state))) =
                      (outcome, last) := bodyRun
                have bodyOther' :
                    evaluate body
                        (DataSem.callEnv args size
                          (DataSem.pushEnv env false (DataSem.decClock other))) =
                      (outcome, lastOther) := bodyOther
                have relClamp : LimitSwapState lim
                    { last with clock := min callState.clock last.clock }
                    { lastOther with clock := min callOther.clock lastOther.clock } :=
                  fixClock_limitSwap outcome last lastOther relCall relBody
                simp only [evaluate, read, th, found, cut, if_neg zero] at run
                rw [bodyRun'] at run
                have clampEq :
                    (fixClock callState (outcome, last)).2 =
                      ({ last with clock := min callState.clock last.clock } : State C F) := rfl
                rw [clampEq] at run
                simp only [fixClock] at run
                cases outcome with
                | none =>
                  simp only [typeError] at run
                  obtain ⟨rfl, rfl⟩ := run
                  refine ⟨_, ?_, relClamp⟩
                  simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                    cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                | some stopped =>
                  cases stopped with
                  | err error =>
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                      cut, callOther, if_neg zero, bodyOther', fixClock]
                  | val values =>
                    cases values with
                    | nil =>
                      simp only [typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨_, ?_, relClamp⟩
                      simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                        cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                    | cons value rest =>
                      cases rest with
                      | cons otherValue tail =>
                        simp only [typeError] at run
                        obtain ⟨rfl, rfl⟩ := run
                        refine ⟨_, ?_, relClamp⟩
                        simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                          cut, callOther, if_neg zero, bodyOther', fixClock, typeError]
                      | nil =>
                        cases pop : DataSem.popEnv
                            ({ last with clock := min callState.clock last.clock } : State C F) with
                        | none =>
                          simp only [pop, typeError] at run
                          obtain ⟨rfl, rfl⟩ := run
                          have popOtherNone := popEnv_none_limitSwap _ _ relClamp pop
                          refine ⟨_, ?_, relClamp⟩
                          simp only [evaluate, localsEq, read, refsEq, th, foundOther, clockEq,
                            cut, callOther, if_neg zero, bodyOther', fixClock, popOtherNone,
                            typeError]
                        | some popped =>
                          obtain ⟨poppedOther, popOther, relPopped⟩ :=
                            popEnv_limitSwap _ _ popped relClamp pop
                          simp only [pop] at run
                          obtain ⟨rfl, rfl⟩ := run
                          refine ⟨setVar dest value poppedOther, ?_, ?_⟩
                          · simp only [evaluate, localsEq, read, refsEq, th, foundOther,
                              clockEq, cut, callOther, if_neg zero, bodyOther', fixClock,
                              popOther]
                          · exact setVar_limitSwap dest value relPopped

/-- The `Call` case without a destination. -/
private theorem limitSwap_tailCall {C F : Type} (lim : Limits) (dest : Option Nat)
    (names : List Nat) (handler : Option (Nat × DataLang.Prog)) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → LimitSwapAt lim body called) :
    LimitSwapAt lim (.call none dest names handler) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  have clockEq := limitSwapState_clock h
  have codeEq := limitSwapState_code h
  cases vars : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, vars, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, vars]
  | some values =>
    have varsOther : DataSem.getVars names other.locals = some values := by
      rw [localsEq]
      exact vars
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, vars, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have foundOther : findCode dest values other.code other.stackFrameSizes = none := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, varsOther, foundOther]
    | some foundEntry =>
      obtain ⟨args, body, size⟩ := foundEntry
      have foundOther :
          findCode dest values other.code other.stackFrameSizes = some (args, body, size) := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      cases handler with
      | some handled =>
        simp only [evaluate, vars, found, Option.isSome_some, if_true, typeError,
          Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨other, ?_, h⟩
        simp [evaluate, typeError, varsOther, foundOther]
      | none =>
        by_cases zero : state.clock = 0
        · simp only [evaluate, vars, found, Option.isSome_none, Bool.false_eq_true, if_false,
            zero, timeoutError] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨flushState true other, ?_, ?_⟩
          · simp [evaluate, timeoutError, varsOther, foundOther, clockEq, if_pos zero]
          · rw [h]
            simp [flushState]
        · let called := DataSem.callEnv args size (DataSem.decClock state)
          let calledOther := DataSem.callEnv args size (DataSem.decClock other)
          have clockLt : called.clock < state.clock := by
            simp only [called, DataSem.callEnv, DataSem.decClock]
            omega
          have relCall : LimitSwapState lim called calledOther :=
            callEnv_limitSwap args size (DataSem.decClock state) (DataSem.decClock other)
              (by
                rw [h]
                simp [DataSem.decClock])
          cases bodyRun : evaluate body called with
          | mk outcome last =>
            obtain ⟨lastOther, bodyOther, relBody⟩ :=
              bodyIH body called clockLt outcome last calledOther bodyRun relCall
            have bodyRun' :
                evaluate body (DataSem.callEnv args size (DataSem.decClock state)) =
                  (outcome, last) := bodyRun
            have bodyOther' :
                evaluate body (DataSem.callEnv args size (DataSem.decClock other)) =
                  (outcome, lastOther) := bodyOther
            simp only [evaluate, vars, found, Option.isSome_none, Bool.false_eq_true, if_false,
              zero] at run
            rw [bodyRun'] at run
            cases outcome with
            | none =>
              simp only [typeError] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨lastOther, ?_, relBody⟩
              simp [evaluate, varsOther, foundOther, clockEq, if_neg zero,
                Option.isSome_none, bodyOther', typeError]
            | some stopped =>
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨lastOther, ?_, relBody⟩
              simp [evaluate, varsOther, foundOther, clockEq, if_neg zero,
                Option.isSome_none, bodyOther']

/-- The `Call` case that returns into a variable list without an exception
    handler. -/
private theorem limitSwap_returningCall_noHandler {C F : Type} (lim : Limits)
    (dest : Option Nat) (names : List Nat) (returns : List Nat) (live : NumSet)
    (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → LimitSwapAt lim body called) :
    LimitSwapAt lim (.call (some (returns, live)) dest names none) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  have clockEq := limitSwapState_clock h
  have codeEq := limitSwapState_code h
  cases vars : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, vars, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, vars]
  | some values =>
    have varsOther : DataSem.getVars names other.locals = some values := by
      rw [localsEq]
      exact vars
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, vars, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have foundOther : findCode dest values other.code other.stackFrameSizes = none := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, varsOther, foundOther]
    | some foundEntry =>
      obtain ⟨args, body, size⟩ := foundEntry
      have foundOther :
          findCode dest values other.code other.stackFrameSizes = some (args, body, size) := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp [evaluate, vars, found, distinct, cut, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h⟩
          simp [evaluate, typeError, localsEq, vars, foundOther, distinct, cut]
        | some env =>
          by_cases zero : state.clock = 0
          · simp [evaluate, vars, found, distinct, cut, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            let callState : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
            let callOther : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock other))
            refine ⟨{ callOther with stack := [], locals := .ln }, ?_, ?_⟩
            · simp [evaluate, timeoutError, localsEq, vars, foundOther, clockEq, cut, callOther,
                distinct, if_pos zero]
            · simpa [zero, callState, callOther] using
                clearState_limitSwap
                  (callEnv_limitSwap args size
                    (DataSem.pushEnv env false (DataSem.decClock state))
                    (DataSem.pushEnv env false (DataSem.decClock other))
                    (pushEnv_limitSwap env false (DataSem.decClock state)
                      (DataSem.decClock other) (by
                        rw [h]
                        simp [DataSem.decClock])))
          · let callState : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock state))
            let callOther : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env false (DataSem.decClock other))
            have clockLt : callState.clock < state.clock := by
              simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
              omega
            have relCall : LimitSwapState lim callState callOther :=
              callEnv_limitSwap args size
                (DataSem.pushEnv env false (DataSem.decClock state))
                (DataSem.pushEnv env false (DataSem.decClock other))
                (pushEnv_limitSwap env false (DataSem.decClock state)
                  (DataSem.decClock other) (by
                    rw [h]
                    simp [DataSem.decClock]))
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              obtain ⟨lastOther, bodyOther, relBody⟩ :=
                bodyIH body callState clockLt outcome last callOther bodyRun relCall
              have bodyRun' :
                  evaluate body
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env false (DataSem.decClock state))) =
                    (outcome, last) := bodyRun
              have bodyOther' :
                  evaluate body
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env false (DataSem.decClock other))) =
                    (outcome, lastOther) := bodyOther
              have relClamp : LimitSwapState lim
                  { last with clock := min callState.clock last.clock }
                  { lastOther with clock := min callOther.clock lastOther.clock } :=
                fixClock_limitSwap outcome last lastOther relCall relBody
              simp only [evaluate, vars, found, distinct, decide_true, Bool.not_true,
                Bool.false_eq_true, if_false, Option.isSome_none, cut, zero] at run
              rw [bodyRun'] at run
              have clampEq :
                  (fixClock callState (outcome, last)).2 =
                    ({ last with clock := min callState.clock last.clock } : State C F) := rfl
              rw [clampEq] at run
              simp only [fixClock] at run
              cases outcome with
              | none =>
                simp only [typeError] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨_, ?_, relClamp⟩
                simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                  distinct, if_neg zero, bodyOther', fixClock, typeError]
              | some stopped =>
                cases stopped with
                | val results =>
                  dsimp only at run
                  by_cases length : results.length = returns.length
                  · rw [if_pos length] at run
                    cases pop : DataSem.popEnv
                        ({ last with clock := min callState.clock last.clock } : State C F) with
                    | none =>
                      simp only [pop, typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have popOtherNone := popEnv_none_limitSwap _ _ relClamp pop
                      refine ⟨_, ?_, relClamp⟩
                      simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                        distinct, if_neg zero, bodyOther', fixClock, popOtherNone, typeError]
                    | some popped =>
                      obtain ⟨poppedOther, popOther, relPopped⟩ :=
                        popEnv_limitSwap _ _ popped relClamp pop
                      simp only [pop] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨setVars returns results poppedOther, ?_, ?_⟩
                      · simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                          distinct, if_pos length, if_neg zero, bodyOther', fixClock, popOther]
                      · exact setVars_limitSwap returns results relPopped
                  · rw [if_neg length] at run
                    simp only [typeError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                      distinct, if_neg zero, bodyOther', fixClock, if_neg length, typeError]
                | err error =>
                  cases error with
                  | raise value =>
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                      distinct, if_neg zero, bodyOther', fixClock]
                  | abort reason =>
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                      distinct, if_neg zero, bodyOther', fixClock]
      · simp [evaluate, vars, found, distinct, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨other, ?_, h⟩
        simp [evaluate, typeError, localsEq, vars, foundOther, distinct]

/-- The `Call` case that returns into a variable list with an exception
    handler. -/
private theorem limitSwap_returningCall_handler {C F : Type} (lim : Limits)
    (dest : Option Nat) (names : List Nat) (returns : List Nat) (live : NumSet)
    (handlerName : Nat) (handlerBody : DataLang.Prog) (state : State C F)
    (bodyIH : ∀ (body : DataLang.Prog) (called : State C F),
      called.clock < state.clock → LimitSwapAt lim body called) :
    LimitSwapAt lim
      (.call (some (returns, live)) dest names (some (handlerName, handlerBody))) state := by
  intro res next other run h
  have localsEq := limitSwapState_locals h
  have clockEq := limitSwapState_clock h
  have codeEq := limitSwapState_code h
  cases vars : DataSem.getVars names state.locals with
  | none =>
    simp only [evaluate, vars, typeError, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨other, ?_, h⟩
    simp [evaluate, typeError, localsEq, vars]
  | some values =>
    have varsOther : DataSem.getVars names other.locals = some values := by
      rw [localsEq]
      exact vars
    cases found : findCode dest values state.code state.stackFrameSizes with
    | none =>
      simp only [evaluate, vars, found, typeError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have foundOther : findCode dest values other.code other.stackFrameSizes = none := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      refine ⟨other, ?_, h⟩
      simp [evaluate, typeError, varsOther, foundOther]
    | some foundEntry =>
      obtain ⟨args, body, size⟩ := foundEntry
      have foundOther :
          findCode dest values other.code other.stackFrameSizes = some (args, body, size) := by
        rw [codeEq, limitSwapState_stackFrameSizes h]
        exact found
      by_cases distinct : returns.Nodup
      · cases cut : cutEnv live state.locals with
        | none =>
          simp [evaluate, vars, found, distinct, cut, typeError] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨other, ?_, h⟩
          simp [evaluate, typeError, localsEq, vars, foundOther, distinct, cut]
        | some env =>
          by_cases zero : state.clock = 0
          · simp [evaluate, vars, found, distinct, cut, zero, timeoutError] at run
            obtain ⟨rfl, rfl⟩ := run
            let callState : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env true (DataSem.decClock state))
            let callOther : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env true (DataSem.decClock other))
            refine ⟨{ callOther with stack := [], locals := .ln }, ?_, ?_⟩
            · simp [evaluate, timeoutError, localsEq, vars, foundOther, clockEq, cut, callOther,
                distinct, if_pos zero]
            · simpa [zero, callState, callOther] using
                clearState_limitSwap
                  (callEnv_limitSwap args size
                    (DataSem.pushEnv env true (DataSem.decClock state))
                    (DataSem.pushEnv env true (DataSem.decClock other))
                    (pushEnv_limitSwap env true (DataSem.decClock state)
                      (DataSem.decClock other) (by
                        rw [h]
                        simp [DataSem.decClock])))
          · let callState : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env true (DataSem.decClock state))
            let callOther : State C F :=
              DataSem.callEnv args size (DataSem.pushEnv env true (DataSem.decClock other))
            have clockLt : callState.clock < state.clock := by
              simp only [callState, DataSem.callEnv, DataSem.pushEnv, DataSem.decClock]
              omega
            have relCall : LimitSwapState lim callState callOther :=
              callEnv_limitSwap args size
                (DataSem.pushEnv env true (DataSem.decClock state))
                (DataSem.pushEnv env true (DataSem.decClock other))
                (pushEnv_limitSwap env true (DataSem.decClock state)
                  (DataSem.decClock other) (by
                    rw [h]
                    simp [DataSem.decClock]))
            cases bodyRun : evaluate body callState with
            | mk outcome last =>
              obtain ⟨lastOther, bodyOther, relBody⟩ :=
                bodyIH body callState clockLt outcome last callOther bodyRun relCall
              have bodyRun' :
                  evaluate body
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env true (DataSem.decClock state))) =
                    (outcome, last) := bodyRun
              have bodyOther' :
                  evaluate body
                      (DataSem.callEnv args size
                        (DataSem.pushEnv env true (DataSem.decClock other))) =
                    (outcome, lastOther) := bodyOther
              have relClamp : LimitSwapState lim
                  { last with clock := min callState.clock last.clock }
                  { lastOther with clock := min callOther.clock lastOther.clock } :=
                fixClock_limitSwap outcome last lastOther relCall relBody
              simp only [evaluate, vars, found, distinct, decide_true, Bool.not_true,
                Bool.false_eq_true, if_false, Option.isSome_some, cut, zero] at run
              rw [bodyRun'] at run
              have clampEq :
                  (fixClock callState (outcome, last)).2 =
                    ({ last with clock := min callState.clock last.clock } : State C F) := rfl
              rw [clampEq] at run
              simp only [fixClock] at run
              cases outcome with
              | none =>
                simp only [typeError] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨_, ?_, relClamp⟩
                simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                  distinct, if_neg zero, bodyOther', fixClock, typeError]
              | some stopped =>
                cases stopped with
                | val results =>
                  dsimp only at run
                  by_cases length : results.length = returns.length
                  · rw [if_pos length] at run
                    cases pop : DataSem.popEnv
                        ({ last with clock := min callState.clock last.clock } : State C F) with
                    | none =>
                      simp only [pop, typeError] at run
                      obtain ⟨rfl, rfl⟩ := run
                      have popOtherNone := popEnv_none_limitSwap _ _ relClamp pop
                      refine ⟨_, ?_, relClamp⟩
                      simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                        distinct, if_neg zero, bodyOther', fixClock, popOtherNone, typeError]
                    | some popped =>
                      obtain ⟨poppedOther, popOther, relPopped⟩ :=
                        popEnv_limitSwap _ _ popped relClamp pop
                      simp only [pop] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨setVars returns results poppedOther, ?_, ?_⟩
                      · simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                          distinct, if_pos length, if_neg zero, bodyOther', fixClock, popOther]
                      · exact setVars_limitSwap returns results relPopped
                  · rw [if_neg length] at run
                    simp only [typeError] at run
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                      distinct, if_neg zero, bodyOther', fixClock, if_neg length, typeError]
                | err error =>
                  cases error with
                  | raise value =>
                    have runHandler :
                        evaluate handlerBody
                            (setVar handlerName value
                              ({ last with clock := min callState.clock last.clock } :
                                State C F)) = (res, next) := run
                    have relHandler : LimitSwapState lim
                        (setVar handlerName value
                          ({ last with clock := min callState.clock last.clock } : State C F))
                        (setVar handlerName value
                          ({ lastOther with clock := min callOther.clock lastOther.clock } :
                            State C F)) := setVar_limitSwap handlerName value relClamp
                    have clockLtHandler :
                        (setVar handlerName value
                          ({ last with clock := min callState.clock last.clock } :
                            State C F)).clock < state.clock := by
                      simp only [setVar]
                      omega
                    obtain ⟨handlerOther, handlerRun, relHandlerOut⟩ :=
                      bodyIH handlerBody
                        (setVar handlerName value
                          ({ last with clock := min callState.clock last.clock } :
                            State C F)) clockLtHandler res next
                        (setVar handlerName value
                          ({ lastOther with clock := min callOther.clock lastOther.clock } :
                            State C F)) runHandler relHandler
                    refine ⟨handlerOther, ?_, relHandlerOut⟩
                    simp only [evaluate, localsEq, vars, foundOther, clockEq, cut,
                      Option.isSome_some, distinct, if_neg zero, bodyOther', fixClock]
                    exact handlerRun
                  | abort reason =>
                    obtain ⟨rfl, rfl⟩ := run
                    refine ⟨_, ?_, relClamp⟩
                    simp [evaluate, localsEq, vars, foundOther, clockEq, cut, callOther,
                      distinct, if_neg zero, bodyOther', fixClock]
      · simp [evaluate, vars, found, distinct, typeError] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨other, ?_, h⟩
        simp [evaluate, typeError, localsEq, vars, foundOther, distinct]

/-- Every limits swap step preserves the relation, by the lexicographic
    `(clock, weight)` induction over the program. -/
private theorem limitSwap_all {C F : Type} (lim : Limits) (program : DataLang.Prog)
    (state : State C F) :
    LimitSwapAt lim program state := by
  refine clockWeightInduction (α := DataLang.Prog) (σ := State C F) (·.clock) sizeOf
    (motive := fun program state => LimitSwapAt lim program state) ?_ program state
  intro program state exprIH smaller
  cases program with
  | skip => exact limitSwap_skip lim state
  | move dest src => exact limitSwap_move lim dest src state
  | assign dest op names live => exact limitSwap_assign lim dest op names live state
  | tick => exact limitSwap_tick lim state
  | makeSpace amount names => exact limitSwap_makeSpace lim amount names state
  | raise name => exact limitSwap_raise lim name state
  | «return» names => exact limitSwap_return lim names state
  | seq first second =>
    apply limitSwap_seq lim first second state
    · apply exprIH first state (by omega)
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
    · intro mid bound
      apply exprIH second mid bound
      simp only [DataLang.Prog.seq.sizeOf_spec]
      omega
  | ifThenElse name yes no =>
    apply limitSwap_if lim name yes no state
    · apply exprIH yes state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
    · apply exprIH no state (by omega)
      simp only [DataLang.Prog.ifThenElse.sizeOf_spec]
      omega
  | force ret label src =>
    cases ret with
    | none => exact limitSwap_tailForce lim label src state smaller
    | some ret =>
      obtain ⟨dest, live⟩ := ret
      exact limitSwap_returningForce lim dest live label src state smaller
  | call ret dest names handler =>
    cases ret with
    | none => exact limitSwap_tailCall lim dest names handler state smaller
    | some ret =>
      obtain ⟨returns, live⟩ := ret
      cases handler with
      | none =>
        exact limitSwap_returningCall_noHandler lim dest names returns live state smaller
      | some entry =>
        obtain ⟨handlerName, handlerBody⟩ := entry
        exact limitSwap_returningCall_handler lim dest names returns live handlerName
          handlerBody state smaller

/-- HOL's `zero_limits`: the three size limits are zero and the architecture
    flags, which HOL's partial record literal leaves as `ARB`, are rendered by
    `false`. Flapjack rendering of HOL `zero_limits_def`; the theorems below hold
    for every limits value, so the choice of the `ARB` fields is immaterial. -/
def zeroLimits : Limits :=
  { heapLimit := 0, lengthLimit := 0, stackLimit := 0, arch64Bit := false,
    hasFpOps := false, hasFpTops := false }

/-- Replacing the configured limits of the starting state preserves the
    evaluation result, with the stack maximum, the safety flag and the peak heap
    length free in the result. Port of HOL `evaluate_swap_limits`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "evaluate_swap_limits"]
theorem evaluate_swap_limits {C F : Type} (program : DataLang.Prog)
    (state next : State C F) (res : Option (Result (List DataSem.Value) DataSem.Value))
    (limits : Limits) (run : evaluate program state = (res, next)) :
    ∃ smx safe peak,
      evaluate program { state with limits := limits } =
        (res, { next with
          limits := limits
          stackMax := smx
          safeForSpace := safe
          peakHeapLength := peak }) := by
  obtain ⟨other, otherRun, relNext⟩ :=
    limitSwap_all limits program state res next { state with limits := limits } run rfl
  refine ⟨other.stackMax, other.safeForSpace, other.peakHeapLength, ?_⟩
  rw [relNext] at otherRun
  exact otherRun

/-- The evaluation result of a program does not depend on the configured
    limits. Port of HOL `evaluate_zero_limits_FST`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml"
  "evaluate_zero_limits_FST"]
theorem evaluate_zero_limits_FST {C F : Type} (program : DataLang.Prog)
    (state : State C F) :
    (evaluate program state).1 =
      (evaluate program { state with limits := zeroLimits }).1 := by
  cases runEq : evaluate program state with
  | mk res next =>
    obtain ⟨smx, safe, peak, runSwap⟩ :=
      evaluate_swap_limits program state next res zeroLimits runEq
    rw [runSwap]

/-- The final FFI state of a program does not depend on the configured limits.
    Port of HOL `evaluate_zero_limits_ffi`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml"
  "evaluate_zero_limits_ffi"]
theorem evaluate_zero_limits_ffi {C F : Type} (program : DataLang.Prog)
    (state : State C F) :
    (evaluate program state).2.ffi =
      (evaluate program { state with limits := zeroLimits }).2.ffi := by
  cases runEq : evaluate program state with
  | mk res next =>
    obtain ⟨smx, safe, peak, runSwap⟩ :=
      evaluate_swap_limits program state next res zeroLimits runEq
    rw [runSwap]

end Flapjack.Compiler.Backend.DataProps
