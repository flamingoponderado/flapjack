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

/-- The generated free-variable selectors read the payload after the two
closure metadata fields, preserving both its order and the target state. -/
theorem evaluate_freeLet {C F : Type} (n : Nat) (s : BvlSem.State C F)
    (env : List BvlSem.Value) (closure : Bvl.Exp) (tag : Nat)
    (code arity : BvlSem.Value) (fields : List BvlSem.Value)
    (clRun : BvlSem.evaluate [closure] env s = (.val [.block tag (code :: arity :: fields)], s))
    (bound : n ≤ fields.length) :
    BvlSem.evaluate (freeLet closure n) env s = (.val (fields.take n), s) := by
  induction n with
  | zero => simp [freeLet, BvlSem.evaluate]
  | succ n ih =>
    have boundN : n ≤ fields.length := by omega
    have indexBound : n < fields.length := by omega
    have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt (n + 2))) [closure]] env s =
        (.val [fields[n]], s) := by
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun]
      simp [BvlSem.doApp, BvlSem.applyBlock, indexBound]
    simp only [freeLet, List.range_succ, List.map_append, List.map_singleton]
    change BvlSem.evaluateTuple (freeLet closure n ++ [.op (.blockOp (.elemAt (n + 2))) [closure]], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp only [BvlSem.evaluateTuple, ih boundN, elemRun, List.take_append_getElem indexBound]

/-- An ordinary closure's entry code exposes arguments followed by captured
values to its compiled body. -/
theorem evaluate_closure_entry {C F : Type} (s : BvlSem.State C F)
    (args fields : List BvlSem.Value) (tag : Nat) (code arity : BvlSem.Value) (body : Bvl.Exp) :
    BvlSem.evaluate [.let ((List.range args.length).map Bvl.Exp.var ++
        freeLet (.var args.length) fields.length) body]
      (args ++ [.block tag (code :: arity :: fields)]) s =
    BvlSem.evaluate [body]
      ((args ++ fields) ++ args ++ [.block tag (code :: arity :: fields)]) s := by
  let env := args ++ [.block tag (code :: arity :: fields)]
  have argsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var) env s = (.val args, s) := by
    have bound : args.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars args.length env s bound
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [.block tag (code :: arity :: fields)], s) := by
    simp [BvlSem.evaluate, env]
  have freeRun : BvlSem.evaluate (freeLet (.var args.length) fields.length) env s = (.val fields, s) := by
    simpa using evaluate_freeLet fields.length s env (.var args.length) tag code arity fields clRun (by simp)
  have bindingsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var ++
      freeLet (.var args.length) fields.length) env s = (.val (args ++ fields), s) := by
    change BvlSem.evaluateTuple (((List.range args.length).map Bvl.Exp.var ++
      freeLet (.var args.length) fields.length), env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, freeRun]
  change BvlSem.evaluate [.let _ body] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, bindingsRun]
  simp [env, List.append_assoc]

/-- An ordinary related closure at exact arity resolves to installed target
code that presents its arguments and captured values to the compiled body. -/
theorem clRel_ordinary_exact_call {C F : Type}
    (s : BvlSem.State C F) (maxApp ptr arity : Nat) (fs : Nat → Prop)
    (sourceEnv : List ClosSem.Value) (fields values rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp fs s.refs s.code (sourceEnv, fields)
      (.closure (some ptr) [] sourceEnv arity sourceBody) target)
    (length : values.length = arity) (fieldsLength : fields.length = sourceEnv.length) :
    ∃ aux targetBody finalAux,
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      sptLookup (ptr + numStubs maxApp) s.code = some (arity + 1,
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) sourceEnv.length) targetBody) ∧
      target = .block 30 (.codePtr (ptr + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) ∧
      BvlSem.evaluate [mkClCall (.var values.length) ((List.range values.length).map Bvl.Exp.var)]
          (values ++ [target] ++ rest) s =
        if s.clock < arity then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          ((values ++ fields) ++ values ++ [target]) (BvlSem.decClock arity s) := by
  cases related with
  | closure bound positive locations vars compiled installed lookup =>
    have nonempty : values ≠ [] := by
      intro empty
      simp [empty] at length
      exact positive length.symm
    refine ⟨_, _, _, compiled, installed, lookup, rfl, ?_⟩
    have run := evaluate_mkClCall_direct_env s values rest 30 (ptr + numStubs maxApp) fields _ nonempty
      (by simpa [length, fieldsLength] using lookup)
    simp only [length] at run ⊢
    rw [run]
    split
    · rfl
    · rw [← fieldsLength, ← length]
      simpa [length] using evaluate_closure_entry (BvlSem.decClock arity s) values fields 30
        (.codePtr (ptr + numStubs maxApp)) (.number (Int.ofNat (arity - 1))) _

/-- An un-applied ordinary closure given exactly its arity selects its body,
with no arguments left for a subsequent application. -/
theorem destClosure_ordinary_exact (maxApp ptr arity : Nat) (sourceEnv args : List ClosSem.Value)
    (body : ClosLang.Exp) (bound : arity ≤ maxApp) (positive : arity ≠ 0)
    (length : args.length = arity) :
    ClosSem.destClosure maxApp none (.closure (some ptr) [] sourceEnv arity body) args =
      some (.fullApp body (args ++ sourceEnv) []) := by
  have positiveArity : 0 < arity := Nat.pos_of_ne_zero positive
  have take : args.reverse.take arity = args.reverse := by
    apply List.take_of_length_le
    simp [length]
  simp [ClosSem.destClosure, ClosSem.checkLoc, length, bound, positiveArity, take]

/-- A related ordinary closure called with exactly its arity simulates its
source body, assuming the body simulation and enough source clock. The target
entry's extra environment suffix is permitted by `envRel`. -/
theorem evaluatePost_ordinary_exact_call {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (locations : ClosProps.everyFnLocationSome [sourceBody])
    (vars : ClosProps.everyFnVarsSome [sourceBody])
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have targetLength : targetArgs.length = arity := by
    rw [← arityMatch]
    exact argsRelated.length_eq.symm
  have fieldsLength : fields.length = sourceEnv.length := envRelated.length_eq.symm
  obtain ⟨aux, targetBody, finalAux, compiled, installed, sourceLookup, targetEq, _⟩ :=
    clRel_ordinary_exact_call t s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
      related targetLength fieldsLength
  have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
    exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code (sourceArgs ++ sourceEnv)
      ((targetArgs ++ fields) ++ targetArgs ++ [targetClosure]) := by
    have tail : envRel s.maxApp f t.refs t.code sourceEnv (fields ++ targetArgs ++ [targetClosure]) := by
      simpa using envRel_prepend envRelated (env := []) (targetEnv := targetArgs ++ [targetClosure]) (by simp [envRel])
    simpa [List.append_assoc] using envRel_prepend argsRelated tail
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t (sourceArgs ++ sourceEnv)
    ((targetArgs ++ fields) ++ targetArgs ++ [targetClosure]) f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + clock }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure := by
    simpa [start] using related
  obtain ⟨_, targetBody2, _, _, _, lookup2, _, callRun⟩ :=
    clRel_ordinary_exact_call start s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
      shiftedRelated targetLength fieldsLength
  have bodyEq : targetBody2 = targetBody := by
    have same := sourceLookup.symm.trans lookup2
    cases same
    rfl
  subst targetBody2
  have enoughTarget : ¬start.clock < arity := by simp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have clockEq : s.clock + clock - arity = s.clock - arity + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
      (targetArgs ++ [targetClosure] ++ rest) start = (targetResult, tFinal) := by
    rw [callRun]
    simpa [start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- Exact ordinary closure application evaluates the selected source body
and returns its result when there are no remaining arguments. -/
theorem evaluateApp_ordinary_exact {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr arity : Nat) (sourceEnv args : List ClosSem.Value) (body : ClosLang.Exp)
    (bound : arity ≤ s.maxApp) (positive : arity ≠ 0) (length : args.length = arity)
    (enough : arity ≤ s.clock) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (args ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal)) :
    ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity body) args s = (result, sFinal) := by
  have found := destClosure_ordinary_exact s.maxApp ptr arity sourceEnv args body bound positive length
  have nonempty : args ≠ [] := by
    intro empty
    simp [empty] at length
    exact positive length.symm
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp only [List.length_nil, Nat.sub_zero, length, Nat.not_lt.mpr enough, ↓reduceIte]
    rw [ClosSem.fixClock_evaluate, bodyRun]
    cases result with
    | err error => rfl
    | val values =>
      cases values with
      | nil => rfl
      | cons value tail =>
        cases tail <;> simp [ClosSem.evaluateApp]

/-- A successful-clock exact application of a related ordinary closure
simulates the source application itself. The remaining premise is the
simulation induction hypothesis for the closure body. -/
theorem evaluateApp_ordinary_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ arity ≠ 0 ∧ ClosProps.everyFnLocationSome [sourceBody] ∧
      ClosProps.everyFnVarsSome [sourceBody] := by
    cases related with
    | closure bound positive locations vars _ _ _ => exact ⟨bound, positive, locations, vars⟩
  obtain ⟨bound, positive, locations, vars⟩ := info
  cases bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ sourceEnv) (ClosSem.decClock arity s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_ordinary_exact s bodyFinal ptr arity sourceEnv sourceArgs sourceBody
      bound positive arityMatch enough bodyResult bodyRun
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_ordinary_exact_call s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough result bodyRun
      noType locations vars bodyIH

/-- An exact ordinary closure call with insufficient source clock times out on
both sides, preserving the candidate state and reference relations. -/
theorem evaluateApp_ordinary_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (timeout : s.clock < arity) :
    ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [targetClosure] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases related with
    | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  obtain ⟨bound, positive⟩ := info
  have found := destClosure_ordinary_exact s.maxApp ptr arity sourceEnv sourceArgs sourceBody bound positive arityMatch
  have nonempty : sourceArgs ≠ [] := by
    intro empty
    simp [empty] at arityMatch
    exact positive arityMatch.symm
  have sourceTimeout : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    cases sourceArgs with
    | nil => contradiction
    | cons head tail =>
      rw [ClosSem.evaluateApp, found]
      simp [arityMatch, timeout]
  have targetLength : targetArgs.length = arity := by
    rw [← arityMatch]
    exact argsRelated.length_eq.symm
  let start : BvlSem.State C F := { t with clock := s.clock }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure := by
    simpa [start] using related
  obtain ⟨_, _, _, _, _, _, _, targetRun⟩ :=
    clRel_ordinary_exact_call start s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
      shiftedRelated targetLength envRelated.length_eq.symm
  have targetTimeout : start.clock < arity := by simpa [start] using timeout
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped
    exact mapped
  · intro key value mapped fresh
    exact ⟨mapped, fresh⟩
  · exact annotations

/-- Exact ordinary closure application simulates both timeout and body
execution, using the body simulation only when the source has enough clock. -/
theorem evaluateApp_ordinary_exact_all {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · exact evaluateApp_ordinary_exact_simulation s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_exact_timeout s t f ptr arity sourceEnv sourceArgs
      fields targetArgs rest sourceBody targetClosure states annotations related envRelated argsRelated arityMatch (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- A related ordinary closure with no supplied arguments has a direct closure
layout; the partial-closure representation necessarily supplies arguments. -/
theorem vRel_ordinary_closure {maxApp ptr arity : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {sourceEnv : List ClosSem.Value} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.closure (some ptr) [] sourceEnv arity body) target) :
    ∃ fields, List.Forall₂ (vRel maxApp f refs code) sourceEnv fields ∧
      clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (sourceEnv, fields)
        (.closure (some ptr) [] sourceEnv arity body) target := by
  cases related with
  | closure envRel closure =>
    cases closure with
    | closure bound positive loc vars compiled installed lookup =>
      exact ⟨_, envRel, .closure bound positive loc vars compiled installed lookup⟩
  | @partialClosure env fvs argEnv ys numArgs cl clApp clTarget envRel argsRel nonempty bound lookup added getArgs closure =>
    cases cl <;> simp [addArgs] at added
    all_goals simp_all

/-- Exact ordinary closure application follows from the value relation itself,
without requiring the caller to expose the captured target environment. -/
theorem evaluateApp_ordinary_exact_vRel {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code
      (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRelated, closure⟩ := vRel_ordinary_closure functionRel
  exact evaluateApp_ordinary_exact_all s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
    sourceBody targetClosure states annotations closure envRelated argsRelated arityMatch result appRun noType bodyIH

/-- Compose the two successful subexpression simulations with the generic
closure-call simulation. The application continuation receives the values and
relations after evaluating the function expression. -/
theorem evaluatePost_app_generic_success {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values : List ClosSem.Value)
    (function : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs = (.val [function], sFunction))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [function]) [targetFunction])
    (appIH : ∀ (targetValues : List BvlSem.Value) (targetClosure : BvlSem.Value)
      (tFunction : BvlSem.State C F) (fFunction : HolFiniteMapExact Nat Nat),
      stateRel fFunction sFunction tFunction → codeAnnotations sFunction →
      List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code) values targetValues →
      vRel sFunction.maxApp fFunction tFunction.refs tFunction.code function targetClosure →
      evaluatePost sFunction sFinal tFunction (targetValues ++ [targetClosure] ++ targetEnv) fFunction result
        [mkClCall (.var targetValues.length) ((List.range targetValues.length).map Bvl.Exp.var)]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  have maxArgs : sArgs.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 sourceArgs sourceEnv s
    rw [argsRun] at h
    exact h
  have maxFunction : sFunction.maxApp = sArgs.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [sourceFunction] sourceEnv sArgs
    rw [functionRun] at h
    exact h
  obtain ⟨clock1, argsResult, tArgs, fArgs, targetArgsRun, argsRel, states1, map1, frame1,
    annotations1, clocks1, growth1, env1⟩ :=
      evaluatePost_environment s sArgs t sourceEnv targetEnv f (.val values) targetArgs envRelated argsPost
  cases argsResult with
  | err error => simp [resultRel] at argsRel
  | val targetValues =>
    have argsRel1 : List.Forall₂ (vRel sArgs.maxApp fArgs tArgs.refs tArgs.code) values targetValues := by
      simpa [resultRel, maxArgs] using argsRel
    have envArgs : envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv := by
      simpa [maxArgs] using env1
    obtain ⟨clock2, functionResult, tFunction, fFunction, targetFunctionRun, functionRel, states2, map2,
      frame2, annotations2, clocks2⟩ := functionIH tArgs fArgs states1 envArgs annotations1 growth1
    cases functionResult with
    | err error => simp [resultRel] at functionRel
    | val targetFunctions =>
      have singleton : List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code)
          [function] targetFunctions := by simpa [resultRel, maxFunction] using functionRel
      cases singleton with
      | @cons _ targetClosure _ _ headRel tail =>
        cases tail
        have growth2 : sptSubspt tArgs.code tFunction.code :=
          BvlProps.evaluateMono [targetFunction] targetEnv { tArgs with clock := sArgs.clock + clock2 }
            (.val [targetClosure]) tFunction targetFunctionRun
        have argsRel2 : List.Forall₂ (vRel sFunction.maxApp fFunction tFunction.refs tFunction.code)
            values targetValues := by
          apply argsRel1.imp
          intro a b head
          simpa [maxFunction] using vRel_grow head map2 frame2 growth2
        obtain ⟨clock3, targetResult, tFinal, fFinal, targetCallRun, related, states3, map3, frame3,
          annotations3, clocks3⟩ := appIH targetValues targetClosure tFunction fFunction states2 annotations2 argsRel2 headRel
        have targetLength : targetValues.length = targetArgs.length :=
          BvlSem.evaluate_length targetArgs targetEnv { t with clock := s.clock + clock1 } tArgs targetValues targetArgsRun
        have shiftArgs := BvlProps.evaluate_addClock targetArgs targetEnv { t with clock := s.clock + clock1 }
          tArgs (.val targetValues) (clock2 + clock3) targetArgsRun (by simp)
        have runArgs : BvlSem.evaluate targetArgs targetEnv { t with clock := s.clock + (clock1 + clock2 + clock3) } =
            (.val targetValues, { tArgs with clock := sArgs.clock + (clock2 + clock3) }) := by
          simpa [Nat.add_assoc, clocks1] using shiftArgs
        have shiftFunction := BvlProps.evaluate_addClock [targetFunction] targetEnv
          { tArgs with clock := sArgs.clock + clock2 } tFunction (.val [targetClosure]) clock3 targetFunctionRun (by simp)
        have runFunction : BvlSem.evaluate [targetFunction] targetEnv
            { tArgs with clock := sArgs.clock + (clock2 + clock3) } =
            (.val [targetClosure], { tFunction with clock := sFunction.clock + clock3 }) := by
          simpa [Nat.add_assoc, clocks2] using shiftFunction
        refine ⟨clock1 + clock2 + clock3, targetResult, tFinal, fFinal, ?_, ?_, states3,
          relocationSubmap_trans (relocationSubmap_trans map1 map2) map3,
          unmappedRefsSubmap_trans (unmappedRefsSubmap_trans frame1 frame2) frame3, annotations3, clocks3⟩
        · rw [evaluate_appTarget_generic _ _ _ _ _ _ _ _ _ runArgs runFunction]
          simpa [targetLength] using targetCallRun
        · simpa [maxFunction, maxArgs] using related

/-- A generic application of an ordinary closure at exact arity follows from
simulations of its arguments, function expression, and closure body. -/
theorem evaluatePost_app_ordinary_exact {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.closure (some ptr) [] captured arity body], sFunction))
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) values sFunction =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError)) (arityMatch : values.length = arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.closure (some ptr) [] captured arity body]) [targetFunction])
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.closure (some ptr) [] captured arity body) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  exact evaluateApp_ordinary_exact_vRel sFunction sFinal tFunction fFunction ptr arity captured values targetValues
    targetEnv body targetClosure states annotations functionRel argsRel arityMatch result appRun noType bodyIH

end Flapjack.Compiler.Backend.ClosToBvl
