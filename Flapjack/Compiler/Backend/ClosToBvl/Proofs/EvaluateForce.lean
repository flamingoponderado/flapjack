import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateLet
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Thunk

/-! Forced-thunk cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- An already-evaluated source thunk and its target thunk return related
payloads without changing either state. -/
theorem evaluatePost_force_evaluated {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp)
    (thunk value : ClosSem.Value)
    (post : evaluatePost s sMiddle t targetEnv f (.val [thunk]) args)
    (found : ClosSem.destThunk [thunk] sMiddle.refs = .isThunk .evaluated value)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sMiddle t targetEnv f (.val [value])
      [.let args (.force (numStubs s.maxApp - 2) 0)] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have argsRel : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [thunk] targetValues := by simpa [resultRel, maxApp] using related
    cases argsRel with
    | cons thunkRel tail =>
      cases tail
      obtain ⟨targetValue, targetFound, valueRel⟩ :=
        destThunk_isThunk_related sMiddle tMiddle state thunkRel .evaluated value found
      refine ⟨clock, .val [targetValue], tMiddle, fMiddle, ?_, ?_, state, map, refs, annotations, clocks⟩
      · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
        simp [BvlSem.evaluate, targetFound]
      · exact .cons (by simpa [maxApp] using valueRel) .nil

/-- An unevaluated target thunk with no clock times out before entering the
installed forcing code. -/
theorem evaluate_force_unevaluated_timeout {C F : Type} (t : BvlSem.State C F)
    (env : List BvlSem.Value) (thunk function : BvlSem.Value) (location : Nat)
    (found : BvlSem.destThunk thunk t.refs = .isThunk .notEvaluated function)
    (installed : sptLookup location t.code = some (2, forceThunkCode)) (clock : t.clock = 0) :
    BvlSem.evaluate [.force location 0] (thunk :: env) t =
      (.err (.abort .timeoutError), { t with clock := 0 }) := by
  rw [BvlSem.evaluate]
  simp [found, BvlSem.findCode, installed, clock]

/-- With clock available, forcing an unevaluated target thunk enters exactly
the installed forcing code with the thunk and its function as arguments. -/
theorem evaluate_force_unevaluated_enter {C F : Type} (t : BvlSem.State C F)
    (env : List BvlSem.Value) (thunk function : BvlSem.Value) (location : Nat)
    (found : BvlSem.destThunk thunk t.refs = .isThunk .notEvaluated function)
    (installed : sptLookup location t.code = some (2, forceThunkCode)) (clock : t.clock ≠ 0) :
    BvlSem.evaluate [.force location 0] (thunk :: env) t =
      BvlSem.evaluate [forceThunkCode] [thunk, function] (BvlSem.decClock 1 t) := by
  rw [BvlSem.evaluate]
  simp [found, BvlSem.findCode, installed, clock]

/-- Errors from forcing arguments propagate through the generated target let. -/
theorem evaluatePost_force_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (args : List Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error)
      [.let args (.force (numStubs s.maxApp - 2) 0)] :=
  evaluatePost_let_error s sFinal t targetEnv f args (.force (numStubs s.maxApp - 2) 0) error post

/-- If the source force operation avoids a type error after evaluating its
arguments, those arguments identify an actual thunk cell. -/
theorem force_source_shape {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (s sMiddle sLast : ClosSem.State C F)
    (values : List ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args env s = (.val values, sMiddle))
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env s = (result, sLast))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ (ptr : Nat) (mode : AstHOL.ThunkMode) (value : ClosSem.Value),
      values = [.refPtr false ptr] ∧ sMiddle.refs.lookup ptr = some (.thunk mode value) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
  cases inspected : ClosSem.destThunk values sMiddle.refs with
  | badRef =>
    simp [inspected] at run
    exact False.elim (noType run.1.symm)
  | notThunk =>
    simp [inspected] at run
    exact False.elim (noType run.1.symm)
  | isThunk mode value =>
    obtain ⟨ptr, valuesEq, found⟩ := destThunk_isThunk_shape values sMiddle.refs mode value inspected
    exact ⟨ptr, mode, value, valuesEq, found⟩

/-- The already-evaluated branch of the source force expression follows from
the argument simulation, with the original compiler and installation premises. -/
theorem expressionSimulation_force_evaluated_case {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value) (thunk value : ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val [thunk], sMiddle))
    (found : ClosSem.destThunk [thunk] sMiddle.refs = .isThunk .evaluated value)
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] sourceEnv s = (result, sFinal))
    (compile : compileExpsHOL s.maxApp [.op trace (.thunkOp .forceThunk) args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.op trace (.thunkOp .forceThunk) args])
    (annotations : codeAnnotations s)
    (varsAnnotated : ClosProps.everyFnVarsSome [.op trace (.thunkOp .forceThunk) args])
    (installed : codeInstalled finalAux t.code) (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (states : stateRel f s t) (argsIH : expressionSimulation (C := C) (F := F) args) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.thunkOp .forceThunk) args] aux =
        ([.let targetArgs (.force (numStubs s.maxApp - 2) 0)], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    have maxApp : sMiddle.maxApp = s.maxApp := by
      have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
      rw [argsRun] at h
      exact h
    have post := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val [thunk])
      argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at run
    simp [found] at run
    rcases run with ⟨rfl, rfl⟩
    exact evaluatePost_force_evaluated s sMiddle t targetEnv f targetArgs thunk value post found maxApp

/-- Compiling the source thunk application produces a unit argument and an
indirect closure call without adding auxiliary code. -/
theorem compile_force_appUnit (maxApp : Nat) (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpsHOL maxApp [ClosSem.appUnit (.var .none 0)] aux =
      ([.let [.op (.blockOp (.cons 0)) [], .var 0]
        (mkClCall (.var 1) [.var 0])], aux) := by
  rw [compileExps_eq_list]
  simp [ClosSem.appUnit, compileExpListHOL, compileExpHOL, compileOp,
    BackendCommon.closTagShift]

/-- The argument binding generated for the thunk's unit application simply
places unit and the function into the call environment. -/
theorem evaluate_force_appUnit_binding {C F : Type} (t : BvlSem.State C F)
    (function : BvlSem.Value) :
    BvlSem.evaluate [.let [.op (.blockOp (.cons 0)) [], .var 0]
      (mkClCall (.var 1) [.var 0])] [function] t =
      BvlSem.evaluate [mkClCall (.var 1) [.var 0]] [BvlSem.unitValue, function, function] t := by
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, BvlSem.unitValue]

/-- The direct-call argument sequences in the generated forcing stub and in
the compiled unit application evaluate identically. -/
theorem evaluate_force_direct_arguments {C F : Type} (t : BvlSem.State C F)
    (thunk function : BvlSem.Value) :
    BvlSem.evaluate [.op (.blockOp (.cons 0)) [], .var 1, .op (.blockOp (.elemAt 0)) [.var 1]]
        [thunk, function] t =
      BvlSem.evaluate [.var 0, .var 1, .op (.blockOp (.elemAt 0)) [.var 1]]
        [BvlSem.unitValue, function, function] t := by
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, BvlSem.unitValue]

/-- The generic-call argument sequences in the generated forcing stub and
compiled unit application evaluate identically. -/
theorem evaluate_force_generic_arguments {C F : Type} (t : BvlSem.State C F)
    (thunk function : BvlSem.Value) :
    BvlSem.evaluate [.op (.blockOp (.cons 0)) [], .var 1] [thunk, function] t =
      BvlSem.evaluate [.var 0, .var 1] [BvlSem.unitValue, function, function] t := by
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, BvlSem.unitValue]

/-- The force stub's direct application and the compiled unit application's
direct branch take the same call step. -/
theorem evaluate_force_direct_call {C F : Type} (t : BvlSem.State C F)
    (thunk function : BvlSem.Value) :
    BvlSem.evaluate [.call 0 none [.op (.blockOp (.cons 0)) [], .var 1,
      .op (.blockOp (.elemAt 0)) [.var 1]]] [thunk, function] t =
      BvlSem.evaluate [.call 0 none [.var 0, .var 1, .op (.blockOp (.elemAt 0)) [.var 1]]]
        [BvlSem.unitValue, function, function] t := by
  conv_lhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  conv_rhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  rw [evaluate_force_direct_arguments]

/-- The force stub's generic application and the compiled unit application's
generic branch take the same call step. -/
theorem evaluate_force_generic_call {C F : Type} (t : BvlSem.State C F)
    (thunk function : BvlSem.Value) :
    BvlSem.evaluate [.call 0 (some 0) [.op (.blockOp (.cons 0)) [], .var 1]] [thunk, function] t =
      BvlSem.evaluate [.call 0 (some 0) [.var 0, .var 1]] [BvlSem.unitValue, function, function] t := by
  conv_lhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  conv_rhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  rw [evaluate_force_generic_arguments]

/-- The force stub and compiled unit application inspect the same closure
arity under their respective environments. -/
theorem evaluate_force_arity_test {C F : Type} (t : BvlSem.State C F)
    (thunk function : BvlSem.Value) :
    BvlSem.evaluate [.op (.blockOp (.equalConst (.int 0)))
      [.op (.blockOp (.elemAt 1)) [.var 1]]] [thunk, function] t =
    BvlSem.evaluate [.op (.blockOp (.equalConst (.int 0)))
      [.op (.blockOp (.elemAt 1)) [.var 1]]] [BvlSem.unitValue, function, function] t := by
  simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, BvlSem.unitValue]

/-- The target continuation writes the result of a thunk application back
into the thunk and returns it. -/
def forceMemoize : Bvl.Exp :=
  .let [.op (.thunkOp (.updateThunk .evaluated)) [.var 0, .var 1]] (.var 1)

/-- Once the thunk update primitive succeeds, the generated continuation
returns the memoized value and retains the updated state. -/
theorem evaluate_forceMemoize {C F : Type} (t next : BvlSem.State C F)
    (thunk value : BvlSem.Value) (rest : List BvlSem.Value)
    (updated : BvlSem.doApp (.thunkOp (.updateThunk .evaluated)) [thunk, value] t =
      .val (BvlSem.unitValue, next)) :
    BvlSem.evaluate [forceMemoize] (value :: thunk :: rest) t = (.val [value], next) := by
  have clock := BvlSem.doApp_clock (.thunkOp (.updateThunk .evaluated)) [thunk, value] t next BvlSem.unitValue updated
  cases next
  simp_all [forceMemoize, BvlSem.evaluate, BvlSem.fixClock]

/-- The generated memoization continuation returns a value related to the
source result and establishes the source's updated thunk state. -/
theorem evaluate_forceMemoize_related {C F : Type} {f : HolFiniteMapExact Nat Nat}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (states : stateRel f s t)
    (thunk value : ClosSem.Value) (targetThunk targetValue : BvlSem.Value) (rest : List BvlSem.Value)
    (thunkRel : vRel s.maxApp f t.refs t.code thunk targetThunk)
    (valueRel : vRel s.maxApp f t.refs t.code value targetValue)
    (nextRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (updated : ClosSem.updateThunk [thunk] s.refs [value] = some nextRefs) :
    ∃ targetNext,
      BvlSem.evaluate [forceMemoize] (targetValue :: targetThunk :: rest) t = (.val [targetValue], targetNext) ∧
      stateRel f { s with refs := nextRefs } targetNext ∧
      vRel s.maxApp f targetNext.refs targetNext.code value targetValue ∧
      unmappedRefsSubmap t.refs targetNext.refs f f ∧ targetNext.clock = t.clock := by
  obtain ⟨targetNext, targetRun, nextState, nextValue, frame, clock⟩ :=
    forceUpdate_related s t states thunk value targetThunk targetValue thunkRel valueRel nextRefs updated
  exact ⟨targetNext, evaluate_forceMemoize t targetNext targetThunk targetValue rest targetRun,
    nextState, nextValue, frame, clock⟩

end Flapjack.Compiler.Backend.ClosToBvl
