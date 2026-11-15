module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Compiler.Backend.Semantics.DataProps.ApplyErrors
public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.Stack
public import Flapjack.Compiler.Backend.Semantics.DataSem.Value

@[expose] public section

/-! `dataPropsScript.sml` initial-state and locals facts for the data
evaluator's state. -/

namespace Flapjack.Compiler.Backend.DataSem

/-- Exact HOL `initial_state_simp` (`dataPropsScript.sml:113`): the eight
    projected fields of the initial state, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "initial_state_simp"]
theorem initialState_simp {C F : Type} (f : HolFfiState F) (c : Spt (Nat × DataLang.Prog))
    (co : CompileOracle C) (cc : Compiler C) (ts : Bool) (l : Limits) (ss : Spt Nat) (k : Nat) :
    (initialState f c co cc ts l ss k).clock = k ∧
    (initialState f c co cc ts l ss k).locals = .ln ∧
    (initialState f c co cc ts l ss k).code = c ∧
    (initialState f c co cc ts l ss k).ffi = f ∧
    (initialState f c co cc ts l ss k).compileOracle = co ∧
    (initialState f c co cc ts l ss k).compile = cc ∧
    (initialState f c co cc ts l ss k).stack = [] ∧
    (initialState f c co cc ts l ss k).peakHeapLength = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `initial_state_with_simp` (`dataPropsScript.sml:126`): rewriting
    the clock, stack or locals of the initial state to the value it already
    has yields the initial state. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "initial_state_with_simp"]
theorem initialState_with_simp {C F : Type} (f : HolFfiState F) (c : Spt (Nat × DataLang.Prog))
    (co : CompileOracle C) (cc : Compiler C) (ts : Bool) (l : Limits) (ss : Spt Nat)
    (k k' : Nat) :
    ({ initialState f c co cc ts l ss k with clock := k' } : State C F) =
        initialState f c co cc ts l ss k' ∧
    ({ initialState f c co cc ts l ss k with stack := [] } : State C F) =
        initialState f c co cc ts l ss k ∧
    ({ initialState f c co cc ts l ss k with locals := .ln } : State C F) =
        initialState f c co cc ts l ss k :=
  ⟨rfl, rfl, rfl⟩

/-- Exact HOL `with_same_locals` (`dataPropsScript.sml:181`): rewriting a
    state's locals to their own value is the identity. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "with_same_locals"]
theorem with_same_locals {C F : Type} (s : State C F) :
    ({ s with locals := s.locals } : State C F) = s := by
  rfl

/-- Exact HOL `do_stack_const` (`dataPropsScript.sml:154`): the stack-space
    computation leaves sixteen fields alone, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_stack_const"]
theorem doStack_const {C F : Type} (op : ClosLang.Op) (vs : List Value) (s : State C F) :
    (doStack op vs s).locals = s.locals ∧
    (doStack op vs s).localsSize = s.localsSize ∧
    (doStack op vs s).stack = s.stack ∧
    (doStack op vs s).stackFrameSizes = s.stackFrameSizes ∧
    (doStack op vs s).global = s.global ∧
    (doStack op vs s).handler = s.handler ∧
    (doStack op vs s).refs = s.refs ∧
    (doStack op vs s).compile = s.compile ∧
    (doStack op vs s).clock = s.clock ∧
    (doStack op vs s).code = s.code ∧
    (doStack op vs s).ffi = s.ffi ∧
    (doStack op vs s).space = s.space ∧
    (doStack op vs s).tstamps = s.tstamps ∧
    (doStack op vs s).limits = s.limits ∧
    (doStack op vs s).peakHeapLength = s.peakHeapLength ∧
    (doStack op vs s).compileOracle = s.compileOracle := by
  simp [doStack]

/-- Exact HOL `Boolv_11` (`dataPropsScript.sml:167`): two Boolean blocks are
    equal exactly when their Booleans are. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "Boolv_11"]
theorem boolValue_inj (b1 b2 : Bool) : boolValue b1 = boolValue b2 ↔ b1 = b2 := by
  cases b1
  all_goals cases b2
  all_goals simp [boolValue, Flapjack.Compiler.Backend.BackendCommon.boolToTag,
    Flapjack.Compiler.Backend.BackendCommon.trueTag,
    Flapjack.Compiler.Backend.BackendCommon.falseTag]


/-- Exact HOL `set_var_const` (`dataPropsScript.sml:1915`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "set_var_const"]
theorem setVar_const {C F : Type} (name : Nat) (value : Value) (state : State C F) :
    (setVar name value state).ffi = state.ffi ∧ (setVar name value state).clock = state.clock :=
  ⟨rfl, rfl⟩

/-- Exact HOL `set_var_with_const` (`dataPropsScript.sml:1922`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "set_var_with_const"]
theorem setVar_with_const {C F : Type} (name : Nat) (value : Value) (state : State C F)
    (clock : Nat) :
    setVar name value { state with clock := clock } =
      { setVar name value state with clock := clock } := by
  simp only [setVar]

/-- Exact HOL `set_vars_const` (`dataPropsScript.sml:1928`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "set_vars_const"]
theorem setVars_const {C F : Type} (names : List Nat) (values : List Value) (state : State C F) :
    (setVars names values state).ffi = state.ffi ∧
      (setVars names values state).clock = state.clock :=
  ⟨rfl, rfl⟩

/-- Exact HOL `set_vars_with_const` (`dataPropsScript.sml:1935`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "set_vars_with_const"]
theorem setVars_with_const {C F : Type} (names : List Nat) (values : List Value)
    (state : State C F) (clock : Nat) :
    setVars names values { state with clock := clock } =
      { setVars names values state with clock := clock } := by
  simp only [setVars]

/-- Exact HOL `call_env_const` (`dataPropsScript.sml:1941`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "call_env_const"]
theorem callEnv_const {C F : Type} (args : List Value) (size : Option Nat) (state : State C F) :
    (callEnv args size state).ffi = state.ffi ∧ (callEnv args size state).clock = state.clock :=
  ⟨rfl, rfl⟩

/-- Exact HOL `call_env_with_const` (`dataPropsScript.sml:1948`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "call_env_with_const"]
theorem callEnv_with_const {C F : Type} (args : List Value) (size : Option Nat)
    (state : State C F) (clock : Nat) :
    callEnv args size { state with clock := clock } =
      { callEnv args size state with clock := clock } := by
  simp only [callEnv]

/-- Exact HOL `push_env_const` (`dataPropsScript.sml:1954`): the seven fields
    that pushing a frame leaves alone, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "push_env_const"]
theorem pushEnv_const {C F : Type} (env : Spt Value) (handler : Bool) (state : State C F) :
    (pushEnv env handler state).ffi = state.ffi ∧
    (pushEnv env handler state).clock = state.clock ∧
    (pushEnv env handler state).code = state.code ∧
    (pushEnv env handler state).compileOracle = state.compileOracle ∧
    (pushEnv env handler state).compile = state.compile ∧
    (pushEnv env handler state).refs = state.refs ∧
    (pushEnv env handler state).global = state.global :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `push_env_with_const` (`dataPropsScript.sml:1966`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "push_env_with_const"]
theorem pushEnv_with_const {C F : Type} (env : Spt Value) (handler : Bool)
    (state : State C F) (clock : Nat) :
    pushEnv env handler { state with clock := clock } =
      { pushEnv env handler state with clock := clock } := by
  simp only [pushEnv]

/-- Exact HOL `dec_clock_const` (`dataPropsScript.sml:2086`): the six fields
    a clock tick leaves alone, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "dec_clock_const"]
theorem decClock_const {C F : Type} (state : State C F) :
    (decClock state).ffi = state.ffi ∧
    (decClock state).code = state.code ∧
    (decClock state).compileOracle = state.compileOracle ∧
    (decClock state).compile = state.compile ∧
    (decClock state).refs = state.refs ∧
    (decClock state).global = state.global :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `add_space_const` (`dataPropsScript.sml:2097`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "add_space_const"]
theorem addSpace_const {C F : Type} (state : State C F) (amount : Nat) :
    (addSpace state amount).ffi = state.ffi :=
  rfl

/-- Exact HOL `with_clock_ffi` (`dataPropsScript.sml:2120`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "with_clock_ffi"]
theorem withClock_ffi {C F : Type} (state : State C F) (clock : Nat) :
    ({ state with clock := clock }).ffi = state.ffi :=
  rfl

/-- Exact HOL `with_same_clock` (`dataPropsScript.sml:1997`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "with_same_clock"]
theorem withSameClock {C F : Type} (state : State C F) :
    { state with clock := state.clock } = state :=
  rfl

/-- Exact HOL `cut_state_eq_some` (`dataPropsScript.sml:1909`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_eq_some"]
theorem cutState_eq_some {C F : Type} (names : NumSet) (state : State C F)
    (next : State C F) :
    cutState names state = some next ↔
      ∃ env : Spt Value, cutEnv names state.locals = some env ∧
        next = { state with locals := env } := by
  simp only [cutState, Option.map_eq_some_iff]
  constructor
  · intro h
    obtain ⟨env, heq, hnext⟩ := h
    exact ⟨env, heq, hnext.symm⟩
  · intro h
    obtain ⟨env, heq, hnext⟩ := h
    exact ⟨env, heq, hnext.symm⟩

/-- Exact HOL `cut_state_eq_none` (`dataPropsScript.sml:1991`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_eq_none"]
theorem cutState_eq_none {C F : Type} (names : NumSet) (state : State C F) :
    cutState names state = none ↔ cutEnv names state.locals = none := by
  simp only [cutState, Option.map_eq_none_iff]


/-- Exact HOL `size_of_heap_with_clock` (`dataPropsScript.sml:1849`): the heap
    size does not depend on the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_heap_with_clock"]
theorem sizeOfHeap_with_clock {C F : Type} (state : State C F) (clock : Nat) :
    sizeOfHeap { state with clock := clock } = sizeOfHeap state :=
  rfl

/-- Exact HOL `size_of_heap_args_with_clock` (`dataPropsScript.sml:1855`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "size_of_heap_args_with_clock"]
theorem sizeOfHeapArgs_with_clock {C F : Type} (state : State C F) (clock : Nat)
    (args : List Value) :
    sizeOfHeapArgs args { state with clock := clock } = sizeOfHeapArgs args state :=
  rfl

/-- Exact HOL `do_app_Rerr` (`dataPropsScript.sml:1841`): a primitive error is
    a type error or an FFI final event. Same statement as HOL `do_app_err`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_Rerr"]
theorem doApp_Rerr {C F : Type} (op : ClosLang.Op) (values : List Value) (state : State C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : doApp op values state = .err error) :
    error = .abort .typeError ∨
      ∃ name outcome, op = .ffi name ∧ error = .abort (.ffiError outcome) :=
  DataProps.doApp_err op values state error run

/-- Exact HOL `pop_env_with_const` (`dataPropsScript.sml:1972`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "pop_env_with_const"]
theorem popEnv_with_const {C F : Type} (state : State C F) (clock : Nat) :
    popEnv { state with clock := clock } =
      (popEnv state).map (fun next => { next with clock := clock }) := by
  cases h : state.stack with
  | nil => simp [popEnv, h]
  | cons frame rest =>
    cases frame with
    | env size env => simp [popEnv, h]
    | exc size env handler => simp [popEnv, h]

/-- Exact HOL `jump_exc_with_const` (`dataPropsScript.sml:2126`). -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "jump_exc_with_const"]
theorem jumpExc_with_const {C F : Type} (state : State C F) (clock : Nat) :
    jumpExc { state with clock := clock } =
      (jumpExc state).map (fun next => { next with clock := clock }) := by
  simp only [jumpExc]
  split
  · split
    · simp
    · simp
  · simp

/-- Exact HOL `cut_state_opt_const` (`dataPropsScript.sml:2054`): a live-name
    cut leaves `ffi` and `global` alone. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "cut_state_opt_const"]
theorem cutStateOpt_const {C F : Type} (names : Option NumSet) (state next : State C F)
    (run : cutStateOpt names state = some next) :
    next.ffi = state.ffi ∧ next.global = state.global := by
  cases names with
  | none =>
    simp only [cutStateOpt, Option.some.injEq] at run
    subst run
    exact ⟨rfl, rfl⟩
  | some names =>
    simp only [cutStateOpt, cutState, Option.map_eq_some_iff] at run
    obtain ⟨env, _, hnext⟩ := run
    subst hnext
    exact ⟨rfl, rfl⟩

end Flapjack.Compiler.Backend.DataSem
