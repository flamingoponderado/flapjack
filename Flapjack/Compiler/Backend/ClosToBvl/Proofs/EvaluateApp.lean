import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateCall
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Application cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- The application expression emitted after compiling its argument list and
function expression. This local helper makes both location cases explicit. -/
def appTarget (maxApp : Nat) (location : Option Nat) (args : List Bvl.Exp) (function : Bvl.Exp) : Bvl.Exp :=
  match location with
  | none => .let (args ++ [function])
      (mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var))
  | some loc => .call (args.length - 1) (some (loc + numStubs maxApp)) (args ++ [function])

/-- An error in the compiled argument list propagates through either form of
application before the function expression or call is executed. -/
theorem evaluate_appTarget_args_error {C F : Type} (s next : BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (location : Option Nat)
    (args : List Bvl.Exp) (function : Bvl.Exp) (error : ErrorResult BvlSem.Value)
    (run : BvlSem.evaluate args env s = (.err error, next)) :
    BvlSem.evaluate [appTarget maxApp location args function] env s = (.err error, next) := by
  have appended : BvlSem.evaluate (args ++ [function]) env s = (.err error, next) := by
    change BvlSem.evaluateTuple (args ++ [function], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, run]
  cases location <;> simp only [appTarget] <;>
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, appended]

/-- An error in the compiled function expression propagates after successful
argument evaluation through either application form. -/
theorem evaluate_appTarget_function_error {C F : Type} (s middle next : BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (location : Option Nat)
    (args : List Bvl.Exp) (function : Bvl.Exp) (values : List BvlSem.Value)
    (error : ErrorResult BvlSem.Value)
    (argsRun : BvlSem.evaluate args env s = (.val values, middle))
    (functionRun : BvlSem.evaluate [function] env middle = (.err error, next)) :
    BvlSem.evaluate [appTarget maxApp location args function] env s = (.err error, next) := by
  have appended : BvlSem.evaluate (args ++ [function]) env s = (.err error, next) := by
    change BvlSem.evaluateTuple (args ++ [function], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, functionRun]
  cases location <;> simp only [appTarget] <;>
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, appended]

/-- An argument error preserves the candidate simulation postcondition for
both direct and generic application. -/
theorem evaluatePost_app_args_error {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (env : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (location : Option Nat) (args : List Bvl.Exp)
    (function : Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t env f (.err error) args) :
    evaluatePost s sFinal t env f (.err error) [appTarget s.maxApp location args function] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, states, map, frame, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    exact ⟨clock, .err targetError, tFinal, fFinal,
      evaluate_appTarget_args_error _ _ _ _ _ _ _ _ run, related, states, map, frame, annotations, clocks⟩

/-- After successful argument evaluation, a simulated function-expression
error propagates through the target application. -/
theorem evaluatePost_app_function_error {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceArgs : List ClosLang.Exp) (targetArgs : List Bvl.Exp)
    (targetFunction : Bvl.Exp) (location : Option Nat) (values : List ClosSem.Value)
    (error : ErrorResult ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sMiddle))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sMiddle t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tMiddle : BvlSem.State C F) (fMiddle : HolFiniteMapExact Nat Nat),
      stateRel fMiddle sMiddle tMiddle →
      envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle targetEnv fMiddle (.err error) [targetFunction]) :
    evaluatePost s sFinal t targetEnv f (.err error) [appTarget s.maxApp location targetArgs targetFunction] := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceArgs sourceEnv s
    rw [argsRun] at h
    exact h
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, run1, related1, state1, map1, frame1,
    annotations1, clocks1, growth1, env1⟩ :=
      evaluatePost_environment s sMiddle t sourceEnv targetEnv f (.val values) targetArgs envRelated argsPost
  cases targetResult with
  | err targetError => simp [resultRel] at related1
  | val targetValues =>
    have middleEnv : envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv := by
      simpa [maxApp] using env1
    obtain ⟨clock2, result2, tFinal, fFinal, run2, related2, state2, map2, frame2,
      annotations2, clocks2⟩ := functionIH tMiddle fMiddle state1 middleEnv annotations1 growth1
    cases result2 with
    | val values => simp [resultRel] at related2
    | err targetError =>
      have shifted := BvlProps.evaluate_addClock targetArgs targetEnv
        { t with clock := s.clock + clock1 } tMiddle (.val targetValues) clock2 run1 (by simp)
      have runArgs : BvlSem.evaluate targetArgs targetEnv
          { t with clock := s.clock + (clock1 + clock2) } =
          (.val targetValues, { tMiddle with clock := sMiddle.clock + clock2 }) := by
        simpa [Nat.add_assoc, clocks1] using shifted
      refine ⟨clock1 + clock2, .err targetError, tFinal, fFinal, ?_, ?_, state2,
        relocationSubmap_trans map1 map2, unmappedRefsSubmap_trans frame1 frame2, annotations2, clocks2⟩
      · exact evaluate_appTarget_function_error _ _ _ _ _ _ _ _ _ _ runArgs run2
      · simpa [maxApp] using related2

/-- A generic application first evaluates arguments and the function, then
enters the generated closure-call code with those values in its environment. -/
theorem evaluate_appTarget_generic {C F : Type} (s middle next : BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (args : List Bvl.Exp) (function : Bvl.Exp)
    (values : List BvlSem.Value) (closure : BvlSem.Value)
    (argsRun : BvlSem.evaluate args env s = (.val values, middle))
    (functionRun : BvlSem.evaluate [function] env middle = (.val [closure], next)) :
    BvlSem.evaluate [appTarget maxApp none args function] env s =
      BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
        (values ++ [closure] ++ env) next := by
  have appended : BvlSem.evaluate (args ++ [function]) env s = (.val (values ++ [closure]), next) := by
    change BvlSem.evaluateTuple (args ++ [function], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, functionRun]
  simp only [appTarget]
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, appended]

/-- A resolved direct application takes the corresponding call step after
argument and function evaluation, including its timeout behavior. -/
theorem evaluate_appTarget_direct {C F : Type} (s middle next : BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp location : Nat) (args : List Bvl.Exp) (function body : Bvl.Exp)
    (values : List BvlSem.Value) (closure : BvlSem.Value)
    (argsRun : BvlSem.evaluate args env s = (.val values, middle))
    (functionRun : BvlSem.evaluate [function] env middle = (.val [closure], next))
    (found : BvlSem.findCode (some (location + numStubs maxApp)) (values ++ [closure]) next.code =
      some (values ++ [closure], body)) :
    BvlSem.evaluate [appTarget maxApp (some location) args function] env s =
      if next.clock < args.length - 1 + 1 then (.err (.abort .timeoutError), { next with clock := 0 })
      else BvlSem.evaluate [body] (values ++ [closure]) (BvlSem.decClock (args.length - 1 + 1) next) := by
  have appended : BvlSem.evaluate (args ++ [function]) env s = (.val (values ++ [closure]), next) := by
    change BvlSem.evaluateTuple (args ++ [function], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, functionRun]
  simp only [appTarget]
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, appended]
  simp [found]

/-- Compiling an application uses `appTarget` with the compiler's threaded
auxiliary-code accumulator. -/
theorem compile_appTarget (maxApp : Nat) (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (aux middle final : List (Nat × Nat × Bvl.Exp)) (targetFunction : Bvl.Exp) (targetArgs : List Bvl.Exp)
    (functionCompile : compileExpHOL maxApp function aux = (targetFunction, middle))
    (argsCompile : compileExpListHOL maxApp args middle = (targetArgs, final)) :
    compileExpsHOL maxApp [.app trace location function args] aux =
      ([appTarget maxApp location targetArgs targetFunction], final) := by
  rw [compileExps_eq_list]
  cases location <;> simp [compileExpListHOL, compileExpHOL, functionCompile, argsCompile, appTarget]

/-- When a closure's remaining arity matches the generated argument list,
`mkClCall` selects its direct call and enters the installed body. -/
theorem evaluate_mkClCall_direct {C F : Type} (s : BvlSem.State C F)
    (env : List BvlSem.Value) (cl : Bvl.Exp) (args : List Bvl.Exp)
    (values : List BvlSem.Value) (tag ptr : Nat) (fields : List BvlSem.Value) (body : Bvl.Exp)
    (clRun : BvlSem.evaluate [cl] env s =
      (.val [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields)], s))
    (argsRun : BvlSem.evaluate args env s = (.val values, s))
    (nonempty : args ≠ [])
    (lookup : sptLookup ptr s.code = some (values.length + 1, body)) :
    BvlSem.evaluate [mkClCall cl args] env s =
      if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body]
        (values ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields)])
        (BvlSem.decClock args.length s) := by
  have elemZero : BvlSem.evaluate [.op (.blockOp (.elemAt 0)) [cl]] env s = (.val [.codePtr ptr], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun]
    simp [BvlSem.doApp, BvlSem.applyBlock]
  have elemOne : BvlSem.evaluate [.op (.blockOp (.elemAt 1)) [cl]] env s =
      (.val [.number (Int.ofNat (args.length - 1))], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun]
    simp [BvlSem.doApp, BvlSem.applyBlock]
  have condRun : BvlSem.evaluate
      [.op (.blockOp (.equalConst (.int (Int.ofNat (args.length - 1)))))
        [.op (.blockOp (.elemAt 1)) [cl]]] env s = (.val [BvlSem.boolValue true], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, elemOne]
    simp [BvlSem.doApp, BvlSem.applyBlock]
  have tailRun : BvlSem.evaluate [cl, .op (.blockOp (.elemAt 0)) [cl]] env s =
      (.val [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields), .codePtr ptr], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun, elemZero]
    rfl
  have argumentsRun : BvlSem.evaluate (args ++ [cl, .op (.blockOp (.elemAt 0)) [cl]]) env s =
      (.val (values ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields), .codePtr ptr]), s) := by
    change BvlSem.evaluateTuple (args ++ [cl, .op (.blockOp (.elemAt 0)) [cl]], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, tailRun]
  change BvlSem.evaluate [.ifThenElse
    (.op (.blockOp (.equalConst (.int (Int.ofNat (args.length - 1)))))
      [.op (.blockOp (.elemAt 1)) [cl]])
    (.call (args.length - 1) none (args ++ [cl, .op (.blockOp (.elemAt 0)) [cl]]))
    (.call 0 (some (genericAppFnLocation (args.length - 1))) (args ++ [cl]))] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, condRun]
  simp only [BvlSem.boolValue, BackendCommon.boolToTag, BvlSem.asBool]
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argumentsRun]
  have count : args.length - 1 + 1 = args.length := by
    cases args <;> simp_all
  have lastPair (inst : Nonempty BvlSem.Value) (xs : List BvlSem.Value) (x y : BvlSem.Value) :
      @Flapjack.holLast BvlSem.Value inst (xs ++ [x, y]) = y := by
    induction xs with
    | nil => simp [Flapjack.holLast]
    | cons z zs ih => simp [Flapjack.holLast_cons, ih]
  simp [BvlSem.findCode, count, BackendCommon.trueTag, lastPair, lookup]

/-- The generated sequence of variables reads a prefix of the target
environment without changing the state. -/
theorem evaluate_rangeVars {C F : Type} (n : Nat) (env : List BvlSem.Value)
    (s : BvlSem.State C F) (bound : n ≤ env.length) :
    BvlSem.evaluate ((List.range n).map Bvl.Exp.var) env s = (.val (env.take n), s) := by
  induction n with
  | zero => simp [BvlSem.evaluate]
  | succ n ih =>
    have boundN : n ≤ env.length := by omega
    have indexBound : n < env.length := by omega
    rw [List.range_succ, List.map_append]
    change BvlSem.evaluateTuple (((List.range n).map Bvl.Exp.var ++ [.var n]), env, s) = _
    rw [BvlProps.evaluateAppend]
    simp only [BvlSem.evaluateTuple, ih boundN]
    have varRun : BvlSem.evaluate [.var n] env s = (.val [env[n]], s) := by
      simp [BvlSem.evaluate, indexBound]
    rw [varRun]
    simp only [List.take_append_getElem indexBound]

/-- The compiler's generated variable call enters the closure body when its
remaining arity exactly matches the nonempty argument prefix. -/
theorem evaluate_mkClCall_direct_env {C F : Type} (s : BvlSem.State C F)
    (values rest : List BvlSem.Value) (tag ptr : Nat) (fields : List BvlSem.Value) (body : Bvl.Exp)
    (nonempty : values ≠ []) (lookup : sptLookup ptr s.code = some (values.length + 1, body)) :
    BvlSem.evaluate [mkClCall (.var values.length) ((List.range values.length).map Bvl.Exp.var)]
      (values ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (values.length - 1)) :: fields)] ++ rest) s =
      if s.clock < values.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body]
        (values ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (values.length - 1)) :: fields)])
        (BvlSem.decClock values.length s) := by
  let closure := BvlSem.Value.block tag (.codePtr ptr :: .number (Int.ofNat (values.length - 1)) :: fields)
  let env := values ++ [closure] ++ rest
  have clRun : BvlSem.evaluate [.var values.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have argsRun : BvlSem.evaluate ((List.range values.length).map Bvl.Exp.var) env s = (.val values, s) := by
    have bound : values.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars values.length env s bound
  have argsNonempty : (List.range values.length).map Bvl.Exp.var ≠ [] := by
    simpa using nonempty
  have h := evaluate_mkClCall_direct s env (.var values.length) ((List.range values.length).map Bvl.Exp.var)
    values tag ptr fields body (by simpa [closure] using clRun) argsRun argsNonempty lookup
  simpa [env, closure] using h

/-- A generic application with exactly enough evaluated arguments invokes the
installed closure body with the generated argument environment. -/
theorem evaluate_appTarget_generic_exact {C F : Type} (s middle next : BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (args : List Bvl.Exp) (function body : Bvl.Exp)
    (values : List BvlSem.Value) (tag ptr : Nat) (fields : List BvlSem.Value)
    (argsRun : BvlSem.evaluate args env s = (.val values, middle))
    (functionRun : BvlSem.evaluate [function] env middle =
      (.val [.block tag (.codePtr ptr :: .number (Int.ofNat (values.length - 1)) :: fields)], next))
    (nonempty : values ≠ []) (lookup : sptLookup ptr next.code = some (values.length + 1, body)) :
    BvlSem.evaluate [appTarget maxApp none args function] env s =
      if next.clock < values.length then (.err (.abort .timeoutError), { next with clock := 0 })
      else BvlSem.evaluate [body]
        (values ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (values.length - 1)) :: fields)])
        (BvlSem.decClock values.length next) := by
  have lengths : values.length = args.length := by
    have h := BvlSem.evaluate_length args env s middle values argsRun
    exact h
  rw [evaluate_appTarget_generic s middle next env maxApp args function values _ argsRun functionRun]
  simpa [← lengths] using evaluate_mkClCall_direct_env next values env tag ptr fields body nonempty lookup

end Flapjack.Compiler.Backend.ClosToBvl
