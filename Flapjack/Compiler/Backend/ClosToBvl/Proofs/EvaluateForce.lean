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

end Flapjack.Compiler.Backend.ClosToBvl
