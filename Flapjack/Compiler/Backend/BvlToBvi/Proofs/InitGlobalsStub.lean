import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileSingle

/-! Initialization of the target global array. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Initial global-array capacity, including the source's lower and upper
clamps. -/
def initGlobalsCapacity (n : Nat) : Nat := min (max n 1) initGlobalsMax

theorem initGlobalsCapacity_positive (n : Nat) : 0 < initGlobalsCapacity n := by
  simp [initGlobalsCapacity, initGlobalsMax]

theorem initGlobalsCapacity_small (n : Nat) : BackendCommon.smallEnoughInt (Int.ofNat (initGlobalsCapacity n)) = true := by
  have upper : initGlobalsCapacity n ≤ 10000 := by simp [initGlobalsCapacity, initGlobalsMax]
  simp [BackendCommon.smallEnoughInt]
  omega

/-- The initialization stub creates a global array with header one, installs
its pointer, and then calls the compiled entry point. Untagged pending BVI
evaluator and dispatcher correspondence review. -/
theorem evaluate_initGlobals_prefix {C F : Type} (start n : Nat) (state : BviSem.BviState C F) :
    let size := initGlobalsCapacity n
    let ptr := BvlSem.leastUnusedRef state.refs
    let ready : BviSem.BviState C F := { state with
      global := some ptr
      refs := state.refs.updateEq (ptr, .valueArray (.number 1 :: List.replicate (size - 1) (.number 0))) }
    BviSem.evaluate [(initGlobalsCode start n).2] [] state =
      BviSem.evaluate [.call 0 (some start) [] (some (.var 0))]
        [BvlSem.unitValue, BvlSem.unitValue, .refPtr true ptr] ready := by
  let size := initGlobalsCapacity n
  let ptr := BvlSem.leastUnusedRef state.refs
  let zeros := List.replicate size (Value.number 0)
  let allocated : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .valueArray zeros) }
  let written : BviSem.BviState C F := { state with refs := state.refs.updateEq (ptr, .valueArray (.number 1 :: List.replicate (size - 1) (.number 0))) }
  let ready : BviSem.BviState C F := { written with global := some ptr }
  let zero : Bvi.Exp := .op (.intOp (.const 0)) []
  let count : Bvi.Exp := .op (.intOp (.const (Int.ofNat size))) []
  let allocate : Bvi.Exp := .op (.memOp .refArray) [zero, count]
  let write : Bvi.Exp := .op (.memOp .update) [.op (.intOp (.const 1)) [], zero, .var 0]
  let setGlobal : Bvi.Exp := .op (.globOp .setGlobalsPtr) [.var 1]
  have zeroRun : BviSem.evaluate [zero] [] state = (.val [.number 0], state) := by
    apply evaluate_smallConst
    decide
  have countRun : BviSem.evaluate [count] [] state = (.val [.number (Int.ofNat size)], state) := by
    exact evaluate_smallConst (Int.ofNat size) [] state (initGlobalsCapacity_small n)
  have allocArgs := evaluate_pair zero count [] state (.number 0) (.number (Int.ofNat size)) zeroRun countRun
  have allocRun : BviSem.evaluate [allocate] [] state = (.val [.refPtr true ptr], allocated) := by
    dsimp [allocate]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocArgs]
    have nonnegative : ¬ (size : Int) < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, nonnegative, ptr, allocated, zeros]
  have writeArgs : BviSem.evaluate [.op (.intOp (.const 1)) [], zero, .var 0] [.refPtr true ptr] allocated =
      (.val [.number 1, .number 0, .refPtr true ptr], allocated) := by
    apply evaluate_readOnly
    simp [zero, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have allocLookup : allocated.refs.lookup ptr = some (.valueArray zeros) := by
    simp [allocated, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have setZeros : zeros.set 0 (.number 1) = .number 1 :: List.replicate (size - 1) (.number 0) := by
    have positive : 0 < size := initGlobalsCapacity_positive n
    obtain ⟨tail, equal⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    simp [zeros, equal, List.replicate_succ]
  have writeRun : BviSem.evaluate [write] [.refPtr true ptr] allocated = (.val [BvlSem.unitValue], written) := by
    dsimp [write]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeArgs]
    have nonempty : zeros ≠ [] := by
      intro empty
      have len := congrArg List.length empty
      simp [zeros] at len
      have positive := initGlobalsCapacity_positive n
      omega
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
      BviSem.toBvl, BviSem.fromBvl, allocated, written, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, nonempty, setZeros, updateEq_overwrite]
  have setRun : BviSem.evaluate [setGlobal] [BvlSem.unitValue, .refPtr true ptr] written =
      (.val [BvlSem.unitValue], ready) := by
    simp [setGlobal, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, ready]
  change BviSem.evaluate [.let [allocate] (.let [write] (.let [setGlobal] _))] [] state = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, allocRun]
  change BviSem.evaluate [.let [write] (.let [setGlobal] _)] [.refPtr true ptr] allocated = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, writeRun]
  change BviSem.evaluate [.let [setGlobal] _] [BvlSem.unitValue, .refPtr true ptr] written = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, setRun]
  rfl

/-- The initialization handler turns an entry-point exception into the
returned singleton value and otherwise preserves the call result. -/
theorem evaluate_initGlobals_handler {C F : Type} (start : Nat) (env : List Value)
    (state : BviSem.BviState C F) :
    BviSem.evaluate [.call 0 (some start) [] (some (.var 0))] env state =
      let (result, last) := BviSem.evaluate [.call 0 (some start) [] none] [] state
      (match result with
        | .err (.raise (.exn value)) => .val [value]
        | other => other, last) := by
  rw [BviSem.evaluate, BviSem.evaluate]
  simp only [BviSem.fixClock_evaluate]
  simp only [BviSem.evaluate, BvlSem.findCode]
  have fixEmpty : BviSem.fixClock state ((.val [] : BviSem.BviResult), state) = ((.val [] : BviSem.BviResult), state) := by
    cases state
    simp [BviSem.fixClock]
  simp only [fixEmpty, BviSem.fixClock_evaluate]
  cases lookup : sptLookup start state.code with
  | none => simp
  | some entry =>
    rcases entry with ⟨arity, body⟩
    by_cases arityZero : arity = 0
    · subst arity
      simp only [List.length_nil, ite_true, Nat.zero_add, Nat.lt_one_iff]
      by_cases clockZero : state.clock = 0
      · simp [clockZero]
      · simp only [clockZero, if_false]
        cases evaluated : BviSem.evaluate [body] [] (BviSem.decClock 1 state) with
        | mk result last =>
          cases result with
          | val values => simp
          | err error =>
            cases error with
            | abort reason => simp
            | raise raised =>
              cases raised with
              | exn value => simp
              | ret values => simp
    · simp [Ne.symm arityZero]

/-- Initialization followed by the entry call, with uncaught exceptions
returned as singleton values. -/
theorem evaluate_initGlobals {C F : Type} (start n : Nat) (state : BviSem.BviState C F) :
    let size := initGlobalsCapacity n
    let ptr := BvlSem.leastUnusedRef state.refs
    let ready : BviSem.BviState C F := { state with
      global := some ptr
      refs := state.refs.updateEq (ptr, .valueArray (.number 1 :: List.replicate (size - 1) (.number 0))) }
    BviSem.evaluate [(initGlobalsCode start n).2] [] state =
      let (result, last) := BviSem.evaluate [.call 0 (some start) [] none] [] ready
      (match result with
        | .err (.raise (.exn value)) => .val [value]
        | other => other, last) := by
  rw [evaluate_initGlobals_prefix, evaluate_initGlobals_handler]

/-- An ordinary call converts a callee's internal return signal to a type
error, so it never exposes a return signal to its caller. -/
theorem evaluate_entry_noReturn {C F : Type} (start : Nat) (state next : BviSem.BviState C F)
    (values : List Value)
    (run : BviSem.evaluate [.call 0 (some start) [] none] [] state = (.err (.raise (.ret values)), next)) : False := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate] at run
  simp only [BviSem.evaluate, BvlSem.findCode] at run
  cases found : sptLookup start state.code with
  | none => simp [found] at run
  | some entry =>
    rcases entry with ⟨arity, body⟩
    by_cases arityZero : arity = 0
    · subst arity
      simp only [found, List.length_nil, ite_true, Nat.zero_add, Nat.lt_one_iff] at run
      by_cases clockZero : state.clock = 0
      · simp [clockZero] at run
      · simp only [clockZero, if_false, BviSem.fixClock_evaluate] at run
        cases evaluation : BviSem.evaluate [body] [] (BviSem.decClock 1 state) with
        | mk result last =>
          cases result with
          | val values => simp [evaluation] at run
          | err error => cases error with
            | abort reason => simp [evaluation] at run
            | raise raised => cases raised <;> simp_all
    · simp [found, Ne.symm arityZero] at run

/-- Calling the installed initializer sets up globals, consumes the call
tick, and runs the entry point with the initializer's exception handler.
Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_initGlobals_call {C F : Type} (start n : Nat) (state : BviSem.BviState C F)
    (code : sptLookup initGlobalsLocation state.code = some (initGlobalsCode start n))
    (clock : state.clock ≠ 0) :
    let base := BviSem.decClock 1 state
    let size := initGlobalsCapacity n
    let ptr := BvlSem.leastUnusedRef base.refs
    let ready : BviSem.BviState C F := { base with
      global := some ptr
      refs := base.refs.updateEq (ptr, .valueArray (.number 1 :: List.replicate (size - 1) (.number 0))) }
    BviSem.evaluate [.call 0 (some initGlobalsLocation) [] none] [] state =
      let (result, last) := BviSem.evaluate [.call 0 (some start) [] none] [] ready
      (match result with
        | .err (.raise (.exn value)) => .val [value]
        | other => other, last) := by
  let base := BviSem.decClock 1 state
  let ptr := BvlSem.leastUnusedRef base.refs
  let ready : BviSem.BviState C F := { base with
    global := some ptr
    refs := base.refs.updateEq (ptr, .valueArray (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }
  change BviSem.evaluate [.call 0 (some initGlobalsLocation) [] none] [] state =
    (let (result, last) := BviSem.evaluate [.call 0 (some start) [] none] [] ready
     (match result with | .err (.raise (.exn value)) => .val [value] | other => other, last))
  have code' : sptLookup initGlobalsLocation state.code = some (0, (initGlobalsCode start n).2) := by
    simpa [initGlobalsCode] using code
  rw [BviSem.evaluate, BviSem.fixClock_evaluate]
  conv_lhs =>
    simp only [BviSem.evaluate, BvlSem.findCode, code', List.length_nil, ite_true,
      Nat.zero_add, Nat.lt_one_iff, clock, if_false, BviSem.fixClock_evaluate]
  rw [evaluate_initGlobals]
  cases callRun : BviSem.evaluate [.call 0 (some start) [] none] [] ready with
  | mk result last =>
    cases result with
    | val values => rfl
    | err error =>
      cases error with
      | abort reason => rfl
      | raise raised =>
        cases raised with
        | exn value => rfl
        | ret values => exact (evaluate_entry_noReturn start ready last values callRun).elim

/-- The initialization entry is present in the source-ordered stub list. -/
theorem lookup_initGlobals_stubs (start n : Nat) (code : List (Nat × Nat × Bvi.Exp)) :
    sptLookup initGlobalsLocation (sptFromAList (stubs start n ++ code)) = some (initGlobalsCode start n) := by
  rw [sptLookup_sptFromAList]
  simp [stubs, sptAListLookup, initGlobalsLocation, copyGlobalsLocation, allocGlobalLocation]
  omega

/-- Every runtime stub required by the state relation is installed before
the compiled program entries. -/
theorem lookup_staticStubs (start n : Nat) (code : List (Nat × Nat × Bvi.Exp)) :
    let tree := sptFromAList (stubs start n ++ code)
    sptLookup allocGlobalLocation tree = some allocGlobalCode ∧
    sptLookup copyGlobalsLocation tree = some copyGlobalsCode ∧
    sptLookup listLengthLocation tree = some listLengthCode ∧
    sptLookup fromListByteLocation tree = some fromListByteCode ∧
    sptLookup toListByteLocation tree = some toListByteCode ∧
    sptLookup sumListLengthLocation tree = some sumListLengthCode ∧
    sptLookup concatByteLocation tree = some concatByteCode := by
  dsimp only
  repeat' constructor
  all_goals rw [sptLookup_sptFromAList]
  all_goals simp [stubs, sptAListLookup, allocGlobalLocation, copyGlobalsLocation, initGlobalsLocation,
    listLengthLocation, fromListByteLocation, toListByteLocation, sumListLengthLocation, concatByteLocation,
    dataNumStubs, wordNumStubs, stackNumStubs]

/-- Starting the generated stub program initializes the target global array
and then executes the entry point. Untagged pending BVI evaluator and
dispatcher correspondence review. -/
theorem evaluate_stubs_init {C F : Type} (start n clock : Nat) (ffi : HolFfiState F)
    (code : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C) (compiler : BviSem.Compiler C) :
    let tree := sptFromAList (stubs start n ++ code)
    let initial := BviSem.initialState ffi tree oracle compiler (clock + 1)
    let ready : BviSem.BviState C F := { initial with
      clock := clock
      global := some 0
      refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
        (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }
    BviSem.evaluate [.call 0 (some initGlobalsLocation) [] none] [] initial =
      let (result, last) := BviSem.evaluate [.call 0 (some start) [] none] [] ready
      (match result with
        | .err (.raise (.exn value)) => .val [value]
        | other => other, last) := by
  let tree := sptFromAList (stubs start n ++ code)
  let initial := BviSem.initialState ffi tree oracle compiler (clock + 1)
  have lookup : sptLookup initGlobalsLocation initial.code = some (initGlobalsCode start n) := by
    exact lookup_initGlobals_stubs start n code
  have nonzero : initial.clock ≠ 0 := by simp [initial, BviSem.initialState]
  have result := evaluate_initGlobals_call start n initial lookup nonzero
  have least : BvlSem.leastUnusedRef (HolFiniteMapExact.empty : HolFiniteMapExact Nat (BvlSem.Ref Value)) = 0 := by
    apply BvlSem.leastUnusedRef_eq_zero
    rfl
  simpa [initial, BviSem.initialState, BviSem.decClock, least] using result

/-- The initialization handler commutes with the simulation's result mapping. -/
theorem mapSimulationResult_handleException (relocate : Nat → Nat)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) :
    (match mapSimulationResult relocate result with
      | .err (.raise (.exn value)) => .val [value]
      | other => other) =
    mapSimulationResult relocate (match result with
      | .err (.raise value) => .val [value]
      | other => other) := by
  cases result with
  | val values => rfl
  | err error => cases error <;> rfl

/-- Initialization and the entry-point simulation compose whenever the
initialized target state is related to the source state. The remaining
whole-program obligation is to establish that initial relation from the
compiled program. Untagged pending evaluator and dispatcher review. -/
theorem compileEntryWithInit {C F : Type} (start n clock : Nat) (ffi : HolFfiState F)
    (code : List (Nat × Nat × Bvi.Exp)) (oracle : BviSem.CompileOracle C) (compiler : BviSem.Compiler C)
    (source next : BvlSem.State (Nat × C) F) (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (relocate : Nat → Nat)
    (run : BvlSem.evaluate [.call 0 (some start) []] [] source = (res, next))
    (sourceOk : stateOk source) (notTypeError : res ≠ .err (.abort .typeError))
    (related : stateRel relocate source
      { BviSem.initialState ffi (sptFromAList (stubs (bvlNumStubs + bvlToBviNamespaces * start) n ++ code)) oracle compiler clock with
        global := some 0
        refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
          (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }) :
    ∃ extra newRelocate targetNext,
      BviSem.evaluate [.call 0 (some initGlobalsLocation) [] none] []
        (BviSem.initialState ffi (sptFromAList (stubs (bvlNumStubs + bvlToBviNamespaces * start) n ++ code))
          oracle compiler (clock + extra + 1)) =
      (mapSimulationResult newRelocate (match res with
        | .err (.raise value) => .val [value]
        | other => other), targetNext) ∧
      stateRel newRelocate next targetNext := by
  let entry := bvlNumStubs + bvlToBviNamespaces * start
  let tree := sptFromAList (stubs entry n ++ code)
  let ready : BviSem.BviState C F := { BviSem.initialState ffi tree oracle compiler clock with
    global := some 0
    refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
      (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) }
  have global : ready.global.isSome = true := by simp [ready]
  obtain ⟨extra, newRelocate, targetNext, targetRun, finalRel⟩ :=
    compileSingleEvaluate start source next ready res relocate run related global sourceOk notTypeError
  have initialized := evaluate_stubs_init entry n (clock + extra) ffi code oracle compiler
  have readyShift : BviProps.incClock extra ready =
      { BviSem.initialState ffi tree oracle compiler (clock + extra) with
        global := some 0
        refs := HolFiniteMapExact.empty.updateEq (0, .valueArray
          (.number 1 :: List.replicate (initGlobalsCapacity n - 1) (.number 0))) } := by
    simp [ready, BviSem.initialState, BviProps.incClock]
  rw [readyShift] at targetRun
  refine ⟨extra, newRelocate, targetNext, ?_, finalRel⟩
  simp only [entry, tree, BviSem.initialState] at initialized targetRun
  rw [targetRun] at initialized
  simpa [mapSimulationResult_handleException, BviSem.initialState] using initialized

/-- The initial BVL state has no dangling globals or references. -/
theorem initialState_ok {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvl.Exp))
    (oracle : BvlSem.CompileOracle C) (compiler : BvlSem.Compiler C) (clock : Nat) :
    stateOk (BvlSem.initialState ffi code oracle compiler clock) := by
  simp [stateOk, BvlSem.initialState, HolFiniteMapExact.empty]

/-- An empty source reference store is related to any target reference store,
for any relocation function. -/
theorem refsRel_empty_source (relocate : Nat → Nat) (target : HolFiniteMapExact Nat (BvlSem.Ref Value)) :
    refsRel relocate HolFiniteMapExact.empty target := by
  simp [refsRel, HolFiniteMapExact.empty]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
