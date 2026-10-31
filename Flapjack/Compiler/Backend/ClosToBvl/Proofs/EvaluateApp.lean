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

/-- The generic application expression case for an ordinary, unapplied
closure at exact arity, with the compiler's accumulator and installed-code
premises. The recursive body simulation is an induction hypothesis. -/
theorem expressionSimulation_app_ordinary_exact_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.closure (some ptr) [] captured arity body], sFunction))
    (arityMatch : values.length = arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_ordinary_exact s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured ptr arity body result argsRun functionRun appRun noType arityMatch
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.closure (some ptr) [] captured arity body]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs
      · exact bodyIH

/-- Argument and function-expression errors satisfy the application simulation
for both direct and generic calls, before closure application begins. -/
theorem expressionSimulation_app_preCall_error_case {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace location function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (preCall : (∃ error, ClosSem.evaluate args sourceEnv s = (.err error, sFinal)) ∨
      (∃ values sArgs error, ClosSem.evaluate args sourceEnv s = (.val values, sArgs) ∧
        ClosSem.evaluate [function] sourceEnv sArgs = (.err error, sFinal)))
    (compile : compileExpsHOL s.maxApp [.app trace location function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace location function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace location function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function]) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have notEmpty : args.isEmpty = false := by cases args <;> simp_all
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace location function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      rw [ClosSem.evaluate] at run
      simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
      rw [ClosSem.fixClock_evaluate] at run
      rcases preCall with ⟨error, argsRun⟩ | ⟨values, sArgs, error, argsRun, functionRun⟩
      · rw [argsRun] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_app_args_error s sFinal t targetEnv f location targetArgs targetFunction error
          (argsIH s sFinal t sourceEnv targetEnv f middleAux finalAux targetArgs (.err error)
            argsRun noType argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states)
      · rw [argsRun] at run
        dsimp only at run
        rw [ClosSem.fixClock_evaluate, functionRun] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
        apply evaluatePost_app_function_error s sArgs sFinal t sourceEnv targetEnv f args targetArgs
          targetFunction location values error argsRun envRelated argsPost
        intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFinal tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction] (.err error)
          functionRun noType (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

/-- A singleton recursive closure's entry passes its own target closure after
its arguments, before the captured values. -/
theorem evaluate_singletonRec_entry {C F : Type} (s : BvlSem.State C F)
    (args fields : List BvlSem.Value) (tag : Nat) (code arity : BvlSem.Value) (body : Bvl.Exp) :
    BvlSem.evaluate [.let ((List.range (args.length + 1)).map Bvl.Exp.var ++
        freeLet (.var args.length) fields.length) body]
      (args ++ [.block tag (code :: arity :: fields)]) s =
    BvlSem.evaluate [body]
      (((args ++ [.block tag (code :: arity :: fields)]) ++ fields) ++
        args ++ [.block tag (code :: arity :: fields)]) s := by
  let closure := BvlSem.Value.block tag (code :: arity :: fields)
  let env := args ++ [closure]
  have argsRun : BvlSem.evaluate ((List.range (args.length + 1)).map Bvl.Exp.var) env s =
      (.val (args ++ [closure]), s) := by
    have bound : args.length + 1 ≤ env.length := by simp [env]
    simpa [env, List.take_of_length_le] using evaluate_rangeVars (args.length + 1) env s bound
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have freeRun : BvlSem.evaluate (freeLet (.var args.length) fields.length) env s = (.val fields, s) := by
    simpa [closure] using evaluate_freeLet fields.length s env (.var args.length) tag code arity fields
      (by simpa [closure] using clRun) (by simp)
  have bindingsRun : BvlSem.evaluate ((List.range (args.length + 1)).map Bvl.Exp.var ++
      freeLet (.var args.length) fields.length) env s = (.val ((args ++ [closure]) ++ fields), s) := by
    change BvlSem.evaluateTuple (((List.range (args.length + 1)).map Bvl.Exp.var ++
      freeLet (.var args.length) fields.length), env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, freeRun]
  change BvlSem.evaluate [.let _ body] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, bindingsRun]
  simp [env, closure, List.append_assoc]

/-- Exact application of a related singleton recursive closure enters its
compiled body with the self-closure in the corresponding environment slot. -/
theorem clRel_singletonRec_exact_call {C F : Type}
    (s : BvlSem.State C F) (maxApp ptr arity : Nat) (fs : Nat → Prop)
    (sourceEnv : List ClosSem.Value) (fields values rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp fs s.refs s.code (sourceEnv, fields)
      (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) target)
    (length : values.length = arity) (fieldsLength : fields.length = sourceEnv.length) :
    ∃ aux targetBody finalAux,
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      sptLookup (ptr + numStubs maxApp) s.code = some (arity + 1,
        .let ((List.range (arity + 1)).map Bvl.Exp.var ++ freeLet (.var arity) sourceEnv.length) targetBody) ∧
      target = .block 30 (.codePtr (ptr + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) ∧
      BvlSem.evaluate [mkClCall (.var values.length) ((List.range values.length).map Bvl.Exp.var)]
          (values ++ [target] ++ rest) s =
        if s.clock < arity then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          (((values ++ [target]) ++ fields) ++ values ++ [target]) (BvlSem.decClock arity s) := by
  cases related with
  | singletonRec bound positive locations vars compiled installed lookup =>
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
      simpa [length] using evaluate_singletonRec_entry (BvlSem.decClock arity s) values fields 30
        (.codePtr (ptr + numStubs maxApp)) (.number (Int.ofNat (arity - 1))) _
  | mutualRec exps ps positions values fresh stored impossible index locations vars installed =>
    simp at impossible

/-- A singleton recursive closure given exactly its arity selects the body
with itself between the argument prefix and captured environment. -/
theorem destClosure_singletonRec_exact (maxApp ptr arity : Nat) (sourceEnv args : List ClosSem.Value)
    (body : ClosLang.Exp) (bound : arity ≤ maxApp) (positive : arity ≠ 0)
    (length : args.length = arity) :
    ClosSem.destClosure maxApp none (.recclosure (some ptr) [] sourceEnv [(arity, body)] 0) args =
      some (.fullApp body (args ++ [.recclosure (some ptr) [] sourceEnv [(arity, body)] 0] ++ sourceEnv) []) := by
  have positiveArity : 0 < arity := Nat.pos_of_ne_zero positive
  have take : args.reverse.take arity = args.reverse := by
    apply List.take_of_length_le
    simp [length]
  simp [ClosSem.destClosure, ClosSem.checkLoc, length, bound, positiveArity, take]

/-- The exact singleton recursive call preserves the simulation postcondition
when the recursive body simulation holds. -/
theorem evaluatePost_singletonRec_exact_call {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal))
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
    clRel_singletonRec_exact_call t s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
      related targetLength fieldsLength
  have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
    exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
  have selfRel : vRel s.maxApp f t.refs t.code
      (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure := by
    rw [targetEq] at related ⊢
    exact .closure envRelated related
  have bodyEnv : envRel s.maxApp f t.refs t.code
      (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv)
      (((targetArgs ++ [targetClosure]) ++ fields) ++ targetArgs ++ [targetClosure]) := by
    have tail : envRel s.maxApp f t.refs t.code
        (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0 :: sourceEnv)
        (targetClosure :: fields ++ targetArgs ++ [targetClosure]) := by
      refine ⟨selfRel, ?_⟩
      simpa using envRel_prepend envRelated (env := []) (targetEnv := targetArgs ++ [targetClosure]) (by simp [envRel])
    simpa [List.append_assoc] using envRel_prepend argsRelated tail
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv)
    (((targetArgs ++ [targetClosure]) ++ fields) ++ targetArgs ++ [targetClosure]) f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + clock }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure := by
    simpa [start] using related
  obtain ⟨_, targetBody2, _, _, _, lookup2, _, callRun⟩ :=
    clRel_singletonRec_exact_call start s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
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

/-- Singleton recursive closure simulation step. -/
theorem evaluateApp_singletonRec_exact {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr arity : Nat) (sourceEnv args : List ClosSem.Value) (body : ClosLang.Exp)
    (bound : arity ≤ s.maxApp) (positive : arity ≠ 0) (length : args.length = arity)
    (enough : arity ≤ s.clock) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (args ++ [.recclosure (some ptr) [] sourceEnv [(arity, body)] 0] ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal)) :
    ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, body)] 0) args s = (result, sFinal) := by
  have found := destClosure_singletonRec_exact s.maxApp ptr arity sourceEnv args body bound positive length
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


/-- Singleton recursive closure simulation step. -/
theorem evaluateApp_singletonRec_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ arity ≠ 0 ∧ ClosProps.everyFnLocationSome [sourceBody] ∧
      ClosProps.everyFnVarsSome [sourceBody] := by
    cases related with
    | singletonRec bound positive locations vars _ _ _ => exact ⟨bound, positive, locations, vars⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  obtain ⟨bound, positive, locations, vars⟩ := info
  cases bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv) (ClosSem.decClock arity s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_singletonRec_exact s bodyFinal ptr arity sourceEnv sourceArgs sourceBody
      bound positive arityMatch enough bodyResult bodyRun
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_singletonRec_exact_call s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough result bodyRun
      noType locations vars bodyIH


/-- Singleton recursive closure simulation step. -/
theorem evaluateApp_singletonRec_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (timeout : s.clock < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [targetClosure] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases related with
    | singletonRec bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  obtain ⟨bound, positive⟩ := info
  have found := destClosure_singletonRec_exact s.maxApp ptr arity sourceEnv sourceArgs sourceBody bound positive arityMatch
  have nonempty : sourceArgs ≠ [] := by
    intro empty
    simp [empty] at arityMatch
    exact positive arityMatch.symm
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
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
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure := by
    simpa [start] using related
  obtain ⟨_, _, _, _, _, _, _, targetRun⟩ :=
    clRel_singletonRec_exact_call start s.maxApp ptr arity _ sourceEnv fields targetArgs rest sourceBody targetClosure
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


/-- Singleton recursive closure simulation step. -/
theorem evaluateApp_singletonRec_exact_all {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · exact evaluateApp_singletonRec_exact_simulation s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_singletonRec_exact_timeout s t f ptr arity sourceEnv sourceArgs
      fields targetArgs rest sourceBody targetClosure states annotations related envRelated argsRelated arityMatch (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- A related singleton recursive closure records its actual captured source
environment in the closure relation. -/
theorem clRel_singletonRec_sourceEnv {maxApp ptr arity : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {sourceEnv env : List ClosSem.Value} {fields : List BvlSem.Value} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (env, fields)
      (.recclosure (some ptr) [] sourceEnv [(arity, body)] 0) target) : env = sourceEnv := by
  cases related with
  | singletonRec => rfl
  | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible

/-- Singleton recursive closure simulation step. -/
theorem vRel_singletonRec_closure {maxApp ptr arity : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {sourceEnv : List ClosSem.Value} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.recclosure (some ptr) [] sourceEnv [(arity, body)] 0) target) :
    ∃ fields, List.Forall₂ (vRel maxApp f refs code) sourceEnv fields ∧
      clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (sourceEnv, fields)
        (.recclosure (some ptr) [] sourceEnv [(arity, body)] 0) target := by
  cases related with
  | closure envRel closure =>
    have eq := clRel_singletonRec_sourceEnv closure
    cases eq
    exact ⟨_, envRel, closure⟩
  | @partialClosure env fvs argEnv ys numArgs cl clApp clTarget envRel argsRel nonempty bound lookup added getArgs closure =>
    cases cl <;> simp [addArgs] at added
    all_goals simp_all


/-- Singleton recursive closure simulation step. -/
theorem evaluateApp_singletonRec_exact_vRel {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code
      (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRelated, closure⟩ := vRel_singletonRec_closure functionRel
  exact evaluateApp_singletonRec_exact_all s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
    sourceBody targetClosure states annotations closure envRelated argsRelated arityMatch result appRun noType bodyIH

/-- Exact singleton recursive closure application simulation step. -/
theorem evaluatePost_app_singletonRec_exact {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.recclosure (some ptr) [] captured [(arity, body)] 0], sFunction))
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) values sFunction =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError)) (arityMatch : values.length = arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.recclosure (some ptr) [] captured [(arity, body)] 0]) [targetFunction])
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.recclosure (some ptr) [] captured [(arity, body)] 0) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  exact evaluateApp_singletonRec_exact_vRel sFunction sFinal tFunction fFunction ptr arity captured values targetValues
    targetEnv body targetClosure states annotations functionRel argsRel arityMatch result appRun noType bodyIH


/-- Exact singleton recursive closure application simulation step. -/
theorem expressionSimulation_app_singletonRec_exact_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.recclosure (some ptr) [] captured [(arity, body)] 0], sFunction))
    (arityMatch : values.length = arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_singletonRec_exact s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured ptr arity body result argsRun functionRun appRun noType arityMatch
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.recclosure (some ptr) [] captured [(arity, body)] 0]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs
      · exact bodyIH

/-- Partially applying a related ordinary closure produces the target partial
closure layout, with the correct installed entry and related saved arguments. -/
theorem vRel_ordinary_partial {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (target targetArgs : List BvlSem.Value)
    (body : ClosLang.Exp) (states : stateRel f s t)
    (functionRel : vRel s.maxApp f t.refs t.code
      (.closure (some ptr) [] captured arity body) (.block 30 target))
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (partialBound : args.length < arity) :
    vRel s.maxApp f t.refs t.code (.closure (some ptr) args captured arity body)
      (.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) ::
        .number (Int.ofNat (arity - 1 - args.length)) :: .block 30 target :: targetArgs)) := by
  obtain ⟨fields, envRel, closure⟩ := vRel_ordinary_closure functionRel
  have bounds : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with
    | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  obtain ⟨arityBound, positive⟩ := bounds
  have argsLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have argsPositive : 0 < args.length := List.length_pos_iff.mpr nonempty
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : targetArgs.length - 1 < arity - 1 := by omega
  have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (targetArgs.length - 1)
    ⟨totalBound, previousBound⟩
  have sizeEq : arity - 1 - (targetArgs.length - 1) + 1 = arity - args.length + 1 := by omega
  have installed' : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) t.code =
      some (arity - args.length + 1, generatePartialAppClosureFn (arity - 1) (targetArgs.length - 1)) := by
    simpa [sizeEq] using installed
  have added : addArgs (.closure (some ptr) [] captured arity body) args =
      some (.closure (some ptr) args captured arity body) := by simp [addArgs]
  exact .partialClosure envRel argsRel nonempty partialBound installed' added (by simp [getNumArgs]) closure

/-- Partially applying a singleton recursive closure preserves its related
closure and saved arguments. -/
theorem vRel_singletonRec_partial {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (target targetArgs : List BvlSem.Value)
    (body : ClosLang.Exp) (states : stateRel f s t)
    (functionRel : vRel s.maxApp f t.refs t.code
      (.recclosure (some ptr) [] captured [(arity, body)] 0) (.block 30 target))
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (partialBound : args.length < arity) :
    vRel s.maxApp f t.refs t.code (.recclosure (some ptr) args captured [(arity, body)] 0)
      (.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) ::
        .number (Int.ofNat (arity - 1 - args.length)) :: .block 30 target :: targetArgs)) := by
  obtain ⟨fields, envRel, closure⟩ := vRel_singletonRec_closure functionRel
  have boundsFor (v : BvlSem.Value)
      (rel : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
        (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) v) :
      arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases rel with
    | singletonRec bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have bounds := boundsFor _ closure
  obtain ⟨arityBound, positive⟩ := bounds
  have argsLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have argsPositive : 0 < args.length := List.length_pos_iff.mpr nonempty
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : targetArgs.length - 1 < arity - 1 := by omega
  have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (targetArgs.length - 1)
    ⟨totalBound, previousBound⟩
  have sizeEq : arity - 1 - (targetArgs.length - 1) + 1 = arity - args.length + 1 := by omega
  have installed' : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) t.code =
      some (arity - args.length + 1, generatePartialAppClosureFn (arity - 1) (targetArgs.length - 1)) := by
    simpa [sizeEq] using installed
  have added : addArgs (.recclosure (some ptr) [] captured [(arity, body)] 0) args =
      some (.recclosure (some ptr) args captured [(arity, body)] 0) := by simp [addArgs]
  exact .partialClosure envRel argsRel nonempty partialBound installed' added (by simp [getNumArgs, Flapjack.holEl, Flapjack.holHd]) closure

/-- The source ordinary-closure dispatcher saves an undersaturated argument
prefix for a later application. -/
theorem destClosure_ordinary_partial (maxApp ptr arity : Nat) (captured args : List ClosSem.Value)
    (body : ClosLang.Exp) (bound : args.length ≤ maxApp) (partialBound : args.length < arity) :
    ClosSem.destClosure maxApp none (.closure (some ptr) [] captured arity body) args =
      some (.partialApp (.closure (some ptr) args captured arity body)) := by
  have positive : 0 < arity := by omega
  simp [ClosSem.destClosure, ClosSem.checkLoc, bound, partialBound, positive]

/-- The source singleton recursive-closure dispatcher saves an undersaturated
argument prefix for a later application. -/
theorem destClosure_singletonRec_partial (maxApp ptr arity : Nat) (captured args : List ClosSem.Value)
    (body : ClosLang.Exp) (bound : args.length ≤ maxApp) (partialBound : args.length < arity) :
    ClosSem.destClosure maxApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) args =
      some (.partialApp (.recclosure (some ptr) args captured [(arity, body)] 0)) := by
  have positive : 0 < arity := by omega
  simp [ClosSem.destClosure, ClosSem.checkLoc, bound, partialBound, positive]

/-- The computed partial-application slot evaluates the triangular index plus
the number of previously supplied arguments. -/
theorem evaluate_partialAppFnLocationCode {C F : Type} {α : Type}
    (maxApp : α) (s : BvlSem.State C F) (env : List BvlSem.Value)
    (total previous : Bvl.Exp) (totalValue previousValue : Int)
    (totalRun : BvlSem.evaluate [total] env s = (.val [.number totalValue], s))
    (previousRun : BvlSem.evaluate [previous] (.number totalValue :: env) s = (.val [.number previousValue], s)) :
    BvlSem.evaluate [partialAppFnLocationCode maxApp total previous] env s =
      (.val [.number (previousValue + (totalValue * (totalValue - 1)).fdiv 2)], s) := by
  rw [partialAppFnLocationCode, BvlSem.evaluate, BvlSem.fixClock_evaluate, totalRun]
  simp [mkConst, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp,
    BvlSem.applyNumeric, BvlSem.doIntApp, previousRun]
  rw [Int.mul_comm (totalValue - 1) totalValue, Int.add_comm]

/-- For a positive total arity, the computed slot agrees with the natural
triangular index used to construct the partial-application table. -/
theorem evaluate_partialAppFnLocationCode_nat {C F : Type} {α : Type}
    (maxApp : α) (s : BvlSem.State C F) (env : List BvlSem.Value)
    (total previous : Bvl.Exp) (totalValue previousValue : Nat) (positive : 0 < totalValue)
    (totalRun : BvlSem.evaluate [total] env s = (.val [.number (Int.ofNat totalValue)], s))
    (previousRun : BvlSem.evaluate [previous] (.number (Int.ofNat totalValue) :: env) s =
      (.val [.number (Int.ofNat previousValue)], s)) :
    BvlSem.evaluate [partialAppFnLocationCode maxApp total previous] env s =
      (.val [.number (Int.ofNat (previousValue + totalValue * (totalValue - 1) / 2))], s) := by
  rw [evaluate_partialAppFnLocationCode maxApp s env total previous _ _ totalRun previousRun]
  have sub : (Int.ofNat totalValue - 1) = Int.ofNat (totalValue - 1) := by
    cases totalValue with
    | zero => omega
    | succ n => simp
  rw [sub, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  simp only [Int.ofNat_eq_natCast]
  push_cast
  rfl

/-- The generic stub computes the partial-application table slot from the
closure arity field and the argument count. -/
theorem evaluate_partialAppFnLocationCode_stub {C F : Type} {α : Type}
    (maxApp : α) (s : BvlSem.State C F) (args : List BvlSem.Value)
    (extra ptr : BvlSem.Value) (tag : Nat) (fields : List BvlSem.Value)
    (total previous : Nat) (bound : previous < total) :
    BvlSem.evaluate [partialAppFnLocationCode maxApp
      (.op (.blockOp (.elemAt 1)) [.var (args.length + 1)]) (mkConst previous)]
      (extra :: (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s =
      (.val [.number (Int.ofNat (previous + total * (total - 1) / 2))], s) := by
  apply evaluate_partialAppFnLocationCode_nat maxApp s _ _ _ total previous (by omega)
  · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
    simp [BvlSem.evaluate, BvlSem.doApp, BvlSem.applyBlock]
  · simp [mkConst, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]

/-- Entries in the partial-application global table, ordered first by total
arity and then by previously supplied arguments. -/
def partialAppEntries (maxApp count : Nat) : List BvlSem.Value :=
  ((List.range count).map fun total =>
    (List.range total).map fun previous =>
      BvlSem.Value.codePtr (partialAppFnLocation maxApp total previous)).flatten

/-- Extending the table by one arity appends exactly that arity's entries. -/
theorem partialAppEntries_succ (maxApp count : Nat) :
    partialAppEntries maxApp (count + 1) = partialAppEntries maxApp count ++
      (List.range count).map (fun previous => BvlSem.Value.codePtr (partialAppFnLocation maxApp count previous)) := by
  simp [partialAppEntries, List.range_succ]

/-- Table lookup by the length of the preceding arity rows. -/
theorem partialAppEntries_lookup (maxApp count total previous : Nat)
    (inTable : total < count) (inRow : previous < total) :
    (partialAppEntries maxApp count)[(partialAppEntries maxApp total).length + previous]? =
      some (.codePtr (partialAppFnLocation maxApp total previous)) := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [partialAppEntries_succ]
    by_cases equal : total = count
    · subst total
      simp [inRow]
    · have smaller : total < count := by omega
      have run := ih smaller
      have bound : (partialAppEntries maxApp total).length + previous < (partialAppEntries maxApp count).length := by
        exact (List.getElem?_eq_some_iff.mp run).1
      simp [List.getElem?_append, bound, (List.getElem?_eq_some_iff.mp run).2]

/-- The preceding table rows have the triangular length used by the generated
index calculation. -/
theorem partialAppEntries_length (maxApp count : Nat) :
    (partialAppEntries maxApp count).length = count * (count - 1) / 2 := by
  have twice : ∀ n, (partialAppEntries maxApp n).length * 2 = n * (n - 1) := by
    intro n
    induction n with
    | zero => simp [partialAppEntries]
    | succ n ih =>
      rw [partialAppEntries_succ]
      simp only [List.length_append, List.length_map, List.length_range]
      cases n with
      | zero => simp [partialAppEntries]
      | succ n =>
        simp only [Nat.add_sub_cancel] at *
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at ih ⊢
        omega
  have h := congrArg (fun n : Nat => n / 2) (twice count)
  simpa using h

/-- The triangular slot in the global partial-application table contains the
corresponding generated code pointer. -/
theorem globalTable_partialApp_lookup (maxApp total previous : Nat)
    (totalBound : total < maxApp) (previousBound : previous < total) :
    ∃ entries, globalTable maxApp = .block 0 entries ∧
      entries[previous + total * (total - 1) / 2]? =
        some (.codePtr (partialAppFnLocation maxApp total previous)) := by
  refine ⟨partialAppEntries maxApp maxApp, rfl, ?_⟩
  simpa [partialAppEntries_length, Nat.add_comm] using
    partialAppEntries_lookup maxApp maxApp total previous totalBound previousBound

/-- A successfully computed slot and the installed global table evaluate to
the corresponding partial-application code pointer. -/
theorem evaluate_partialApp_global_pointer {C F : Type} (s : BvlSem.State C F)
    (env : List BvlSem.Value) (index : Bvl.Exp) (maxApp total previous : Nat)
    (totalBound : total < maxApp) (previousBound : previous < total)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp)))
    (indexRun : BvlSem.evaluate [index] env s =
      (.val [.number (Int.ofNat (previous + total * (total - 1) / 2))], s)) :
    BvlSem.evaluate [mkEl (.op (.globOp (.global 0)) []) index] env s =
      (.val [.codePtr (partialAppFnLocation maxApp total previous)], s) := by
  obtain ⟨entries, tableEq, slot⟩ := globalTable_partialApp_lookup maxApp total previous totalBound previousBound
  have globalRun : BvlSem.evaluate [.op (.globOp (.global 0)) []] env s = (.val [.block 0 entries], s) := by
    simp [ClosSem.getGlobal] at global
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyGlobal, global, tableEq]
  rw [mkEl, BvlSem.evaluate, BvlSem.fixClock_evaluate]
  have argsRun : BvlSem.evaluate [index, .op (.globOp (.global 0)) []] env s =
      (.val [.number (Int.ofNat (previous + total * (total - 1) / 2)), .block 0 entries], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, indexRun, globalRun]
    rfl
  rw [argsRun]
  have indexEq : (Int.ofNat previous + Int.ofNat total * Int.ofNat (total - 1) / 2) =
      Int.ofNat (previous + total * (total - 1) / 2) := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    rfl
  simp only [Int.ofNat_eq_natCast] at indexEq
  simp [BvlSem.doApp, BvlSem.applyMemory]
  rw [indexEq]
  have nonnegative : ¬ ((previous + total * (total - 1) / 2 : Nat) : Int) < 0 := by
    exact Int.not_lt.mpr (Int.natCast_nonneg _)
  simp only [if_neg nonnegative, Int.toNat_natCast, slot, Option.bind]

/-- The generated stub's arity lookup and table access jointly select the
installed partial-application entry pointer. -/
theorem evaluate_partialApp_stub_pointer {C F : Type} (s : BvlSem.State C F)
    (args : List BvlSem.Value) (extra ptr : BvlSem.Value) (tag : Nat) (fields : List BvlSem.Value)
    (maxApp total previous : Nat) (totalBound : total < maxApp) (previousBound : previous < total)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [mkEl (.op (.globOp (.global 0)) [])
      (partialAppFnLocationCode maxApp
        (.op (.blockOp (.elemAt 1)) [.var (args.length + 1)]) (mkConst previous))]
      (extra :: (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s =
      (.val [.codePtr (partialAppFnLocation maxApp total previous)], s) := by
  apply evaluate_partialApp_global_pointer s _ _ maxApp total previous totalBound previousBound global
  exact evaluate_partialAppFnLocationCode_stub maxApp s args extra ptr tag fields total previous previousBound

/-- Extract the partial-application branch of the generated generic stub for
local reasoning about its control flow. -/
def genericAppPartialBranch (maxApp n : Nat) : Bvl.Exp :=
  match generateGenericApp maxApp n with
  | .let _ (.ifThenElse _ _ partialBranch) => partialBranch
  | _ => .var 0

/-- If the supplied argument count does not exceed the closure's remaining
arity, the generic stub selects its partial-application branch. -/
theorem evaluate_genericApp_partial_branch {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (bound : n + 1 ≤ total) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]) s =
    BvlSem.evaluate [genericAppPartialBranch maxApp n]
      (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s := by
  let env := args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]
  let diff : Int := Int.ofNat total - Int.ofNat (n + 1)
  have varRun : BvlSem.evaluate [.var (n + 1)] env s =
      (.val [.block tag (ptr :: .number (Int.ofNat total) :: fields)], s) := by
    simp [BvlSem.evaluate, env, ← length]
  have firstRun : BvlSem.evaluate [.op (.intOp .sub)
      [mkConst (n + 1), .op (.blockOp (.elemAt 1)) [.var (n + 1)]]] env s = (.val [.number diff], s) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.applyNumeric, BvlSem.doIntApp, mkConst, varRun, diff]
  have testRun : BvlSem.evaluate [.op (.intOp .less) [mkConst 0, .var 0]] (.number diff :: env) s =
      (.val [BvlSem.boolValue false], s) := by
    have nonnegative : ¬diff < 0 := by dsimp [diff]; omega
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, mkConst, nonnegative]
  change BvlSem.evaluate [.let [.op (.intOp .sub)
      [mkConst (n + 1), .op (.blockOp (.elemAt 1)) [.var (n + 1)]]]
      (.ifThenElse (.op (.intOp .less) [mkConst 0, .var 0]) _
        (genericAppPartialBranch maxApp n))] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, firstRun]
  dsimp only
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.singleton_append]
  rw [testRun]
  simp [BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.falseTag, BvlSem.asBool, env, diff]

/-- The repeated tick sequence consumes its requested clock or times out at
zero before entering its body. -/
theorem evaluate_genericAppTicks {C F : Type} (n : Nat) (body : Bvl.Exp)
    (env : List BvlSem.Value) (s : BvlSem.State C F) :
    BvlSem.evaluate [genericAppTicks n body] env s =
      if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] env (BvlSem.decClock n s) := by
  induction n generalizing s with
  | zero =>
    change BvlSem.evaluate [body] env s = BvlSem.evaluate [body] env (BvlSem.decClock 0 s)
    cases s
    rfl
  | succ n ih =>
    change BvlSem.evaluate [.tick (genericAppTicks n body)] env s = _
    rw [BvlSem.evaluate]
    by_cases empty : s.clock = 0
    · cases s
      simp_all
    · simp only [empty, ↓reduceIte]
      rw [ih]
      by_cases insufficient : s.clock < n + 1
      · have less : s.clock - 1 < n := by omega
        simp [insufficient, less, BvlSem.decClock]
      · have enough : ¬(BvlSem.decClock 1 s).clock < n := by simp [BvlSem.decClock]; omega
        simp only [insufficient, enough, ↓reduceIte]
        have clocks : s.clock - 1 - n = s.clock - (n + 1) := by omega
        simp [BvlSem.decClock, clocks]

/-- Strip a known number of generated tick constructors. -/
def stripGenericAppTicks : Nat → Bvl.Exp → Bvl.Exp
  | 0, body => body
  | n + 1, .tick body => stripGenericAppTicks n body
  | _ + 1, body => body

/-- The body of the partial-application branch after its tick sequence. -/
def genericAppPartialChoice (maxApp n : Nat) : Bvl.Exp :=
  stripGenericAppTicks n (genericAppPartialBranch maxApp n)

/-- Stripping a generated tick sequence recovers its body. -/
theorem stripGenericAppTicks_generated (n : Nat) (body : Bvl.Exp) :
    stripGenericAppTicks n (genericAppTicks n body) = body := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change stripGenericAppTicks n (genericAppTicks n body) = body
    exact ih

/-- The partial branch consists of its arity-dependent ticks followed by the
closure-tag choice. -/
theorem genericAppPartialBranch_ticks (maxApp n : Nat) :
    genericAppPartialBranch maxApp n = genericAppTicks n (genericAppPartialChoice maxApp n) := by
  unfold genericAppPartialChoice genericAppPartialBranch generateGenericApp
  change genericAppTicks n _ = genericAppTicks n (stripGenericAppTicks n (genericAppTicks n _))
  rw [stripGenericAppTicks_generated]

/-- Selecting the partial branch and consuming its ticks either times out or
continues with the closure-tag choice. -/
theorem evaluate_genericApp_partial_ticks {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (bound : n + 1 ≤ total) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]) s =
    if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
    else BvlSem.evaluate [genericAppPartialChoice maxApp n]
      (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) (BvlSem.decClock n s) := by
  rw [evaluate_genericApp_partial_branch s maxApp n total tag args fields ptr length bound,
    genericAppPartialBranch_ticks, evaluate_genericAppTicks]

/-- The generated branch that constructs a partial closure from a previously
unapplied closure. -/
def genericAppPartialNormal (maxApp n : Nat) : Bvl.Exp :=
  match genericAppPartialChoice maxApp n with
  | .ifThenElse _ normal _ => normal
  | _ => .var 0

/-- The remaining partial branch tests the closure tag and chooses between
new and existing partial closures. -/
theorem genericAppPartialChoice_shape (maxApp n : Nat) :
    ∃ other, genericAppPartialChoice maxApp n =
      .ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) (genericAppPartialNormal maxApp n) other := by
  have shape : ∃ normal other, genericAppPartialChoice maxApp n =
      .ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) normal other := by
    unfold genericAppPartialChoice genericAppPartialBranch generateGenericApp
    change ∃ normal other, stripGenericAppTicks n (genericAppTicks n
        (.ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) _ _)) = _
    rw [stripGenericAppTicks_generated]
    exact ⟨_, _, rfl⟩
  obtain ⟨normal, other, shape⟩ := shape
  refine ⟨other, ?_⟩
  simp [genericAppPartialNormal, shape]

/-- An ordinary closure takes the new-partial-closure branch after the generic
stub's arity test and tick sequence. -/
theorem evaluate_genericApp_partial_normal {C F : Type} (s : BvlSem.State C F)
    (maxApp n total : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (bound : n + 1 ≤ total) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)]) s =
    if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
    else BvlSem.evaluate [genericAppPartialNormal maxApp n]
      (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)])) (BvlSem.decClock n s) := by
  rw [evaluate_genericApp_partial_ticks s maxApp n total 30 args fields ptr length bound]
  split
  · rfl
  · obtain ⟨other, shape⟩ := genericAppPartialChoice_shape maxApp n
    rw [shape, BvlSem.evaluate, BvlSem.fixClock_evaluate]
    have test : BvlSem.evaluate [.op (.blockOp (.tagEq 30)) [.var (n + 2)]]
        (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
          (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)])) (BvlSem.decClock n s) =
        (.val [BvlSem.boolValue true], BvlSem.decClock n s) := by
      simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, ← length]
    rw [test]
    simp [BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.trueTag, BvlSem.asBool]

/-- The reversed generated variable sequence reads a prefix of the argument
list in reverse order without changing the state. -/
theorem evaluate_reverse_offsetVars {C F : Type} (n : Nat) (first : BvlSem.Value)
    (args rest : List BvlSem.Value) (s : BvlSem.State C F) (bound : n ≤ args.length) :
    BvlSem.evaluate (((List.range n).map (fun i => Bvl.Exp.var (i + 1))).reverse)
      (first :: (args ++ rest)) s = (.val (args.take n).reverse, s) := by
  induction n with
  | zero => simp [BvlSem.evaluate]
  | succ n ih =>
    have smaller : n ≤ args.length := by omega
    have indexBound : n < args.length := by omega
    have varRun : BvlSem.evaluate [.var (n + 1)] (first :: (args ++ rest)) s = (.val [args[n]], s) := by
      simp [BvlSem.evaluate, List.getElem?_append, indexBound]
    rw [List.range_succ, List.map_append, List.reverse_append]
    change BvlSem.evaluateTuple (.var (n + 1) :: _, first :: (args ++ rest), s) = _
    rw [BvlProps.evaluateCons]
    simp only [BvlSem.evaluateTuple, varRun]
    dsimp only [List.append]
    rw [ih smaller]
    simp only [Flapjack.holHd, Prod.mk.injEq, Result.val.injEq, and_true]
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append] using
      (congrArg List.reverse (List.take_append_getElem indexBound))

/-- The normal partial-application branch constructs a block from the table
pointer, remaining arity, original closure and saved arguments. -/
theorem genericAppPartialNormal_shape (maxApp n : Nat) :
    genericAppPartialNormal maxApp n = .op (.blockOp (.cons 31))
      ((mkEl (.op (.globOp (.global 0)) [])
          (partialAppFnLocationCode maxApp (.op (.blockOp (.elemAt 1)) [.var (n + 2)]) (mkConst n)) ::
        .var 0 :: .var (n + 2) :: (List.range (n + 1)).map (fun i => .var (i + 1))).reverse) := by
  unfold genericAppPartialNormal genericAppPartialChoice genericAppPartialBranch generateGenericApp
  change (match stripGenericAppTicks n (genericAppTicks n
      (.ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) _ _)) with
      | .ifThenElse _ normal _ => normal
      | _ => .var 0) = _
  rw [stripGenericAppTicks_generated]
  rfl

/-- The normal partial branch constructs the target closure with the selected
stub pointer, remaining arity, original closure, and saved arguments. -/
theorem evaluate_genericAppPartialNormal {C F : Type} (s : BvlSem.State C F)
    (maxApp n total : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value) (remaining : Int)
    (length : args.length = n + 1) (previousBound : n < total) (totalBound : total < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [genericAppPartialNormal maxApp n]
      (.number remaining :: (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)])) s =
    (.val [.block 31 (.codePtr (partialAppFnLocation maxApp total n) :: .number remaining ::
      .block 30 (ptr :: .number (Int.ofNat total) :: fields) :: args)], s) := by
  let closure := BvlSem.Value.block 30 (ptr :: .number (Int.ofNat total) :: fields)
  let env := .number remaining :: (args ++ [closure])
  let slot := mkEl (.op (.globOp (.global 0)) [])
    (partialAppFnLocationCode maxApp (.op (.blockOp (.elemAt 1)) [.var (n + 2)]) (mkConst n))
  have varsRun : BvlSem.evaluate (((List.range (n + 1)).map (fun i => Bvl.Exp.var (i + 1))).reverse) env s =
      (.val args.reverse, s) := by
    simpa [env, ← length] using evaluate_reverse_offsetVars (n + 1) (.number remaining) args [closure] s (by omega)
  have closureRun : BvlSem.evaluate [.var (n + 2)] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env, ← length]
  have remainingRun : BvlSem.evaluate [.var 0] env s = (.val [.number remaining], s) := by
    simp [BvlSem.evaluate, env]
  have slotRun : BvlSem.evaluate [slot] env s =
      (.val [.codePtr (partialAppFnLocation maxApp total n)], s) := by
    simpa [slot, env, closure, length, Nat.add_assoc] using
      evaluate_partialApp_stub_pointer s args (.number remaining) ptr 30 fields maxApp total n totalBound previousBound global
  have tailRun : BvlSem.evaluate [.var (n + 2), .var 0, slot] env s =
      (.val [closure, .number remaining, .codePtr (partialAppFnLocation maxApp total n)], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, closureRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, remainingRun]
    dsimp only
    rw [slotRun]
    rfl
  have allRun : BvlSem.evaluate
      (((List.range (n + 1)).map (fun i => Bvl.Exp.var (i + 1))).reverse ++ [.var (n + 2), .var 0, slot]) env s =
      (.val (args.reverse ++ [closure, .number remaining, .codePtr (partialAppFnLocation maxApp total n)]), s) := by
    change BvlSem.evaluateTuple (_, env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, varsRun, tailRun]
  rw [genericAppPartialNormal_shape, BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  rw [allRun]
  simp [BvlSem.doApp, BvlSem.applyBlock, closure]

/-- The generic application stub either times out or constructs the expected
partial closure for an ordinary closure with more arguments still needed. -/
theorem evaluate_genericApp_partial_new {C F : Type} (s : BvlSem.State C F)
    (maxApp n total : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (previousBound : n < total) (totalBound : total < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)]) s =
    if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
    else (.val [.block 31 (.codePtr (partialAppFnLocation maxApp total n) ::
      .number (Int.ofNat (total - (n + 1))) ::
      .block 30 (ptr :: .number (Int.ofNat total) :: fields) :: args)], BvlSem.decClock n s) := by
  have bound : n + 1 ≤ total := by omega
  rw [evaluate_genericApp_partial_normal s maxApp n total args fields ptr length bound]
  split
  · rfl
  · have globalDec : ClosSem.getGlobal 0 (BvlSem.decClock n s).globals = some (some (globalTable maxApp)) := by
      simpa [BvlSem.decClock] using global
    rw [evaluate_genericAppPartialNormal (BvlSem.decClock n s) maxApp n total args fields ptr _
      length previousBound totalBound globalDec]
    simp only [Int.ofNat_eq_natCast]
    rw [← Int.natCast_sub bound]

/-- An arity mismatch in `mkClCall` enters the installed generic stub after
one call tick, preserving the evaluated argument and closure values. -/
theorem evaluate_mkClCall_generic {C F : Type} (s : BvlSem.State C F)
    (env : List BvlSem.Value) (cl : Bvl.Exp) (args : List Bvl.Exp)
    (values : List BvlSem.Value) (tag total : Nat) (ptr : BvlSem.Value)
    (fields : List BvlSem.Value) (body : Bvl.Exp)
    (clRun : BvlSem.evaluate [cl] env s =
      (.val [.block tag (ptr :: .number (Int.ofNat total) :: fields)], s))
    (argsRun : BvlSem.evaluate args env s = (.val values, s))
    (different : args.length - 1 ≠ total)
    (lookup : sptLookup (genericAppFnLocation (args.length - 1)) s.code = some (values.length + 1, body)) :
    BvlSem.evaluate [mkClCall cl args] env s =
      if s.clock = 0 then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (values ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])
        (BvlSem.decClock 1 s) := by
  have elemRun : BvlSem.evaluate [.op (.blockOp (.elemAt 1)) [cl]] env s = (.val [.number (Int.ofNat total)], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, clRun]
    simp [BvlSem.doApp, BvlSem.applyBlock]
  have condRun : BvlSem.evaluate
      [.op (.blockOp (.equalConst (.int (Int.ofNat (args.length - 1)))))
        [.op (.blockOp (.elemAt 1)) [cl]]] env s = (.val [BvlSem.boolValue false], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, elemRun]
    have unequal : ((args.length - 1 : Nat) : Int) ≠ (total : Int) := by
      exact_mod_cast different
    simp [BvlSem.doApp, BvlSem.applyBlock, unequal]
  have argumentsRun : BvlSem.evaluate (args ++ [cl]) env s =
      (.val (values ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]), s) := by
    change BvlSem.evaluateTuple (args ++ [cl], env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, clRun]
  change BvlSem.evaluate [.ifThenElse
    (.op (.blockOp (.equalConst (.int (Int.ofNat (args.length - 1)))))
      [.op (.blockOp (.elemAt 1)) [cl]])
    (.call (args.length - 1) none (args ++ [cl, .op (.blockOp (.elemAt 0)) [cl]]))
    (.call 0 (some (genericAppFnLocation (args.length - 1))) (args ++ [cl]))] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, condRun]
  simp only [BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.falseTag, BvlSem.asBool]
  change BvlSem.evaluate [.call 0 (some (genericAppFnLocation (args.length - 1))) (args ++ [cl])] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argumentsRun]
  simp [BvlSem.findCode, lookup]

/-- The compiler-generated closure call and generic stub together construct
a new partial closure, charging one call tick plus the stub's ticks. -/
theorem evaluate_mkClCall_partial_new {C F : Type} (s : BvlSem.State C F)
    (maxApp n total : Nat) (args fields rest : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (previousBound : n < total) (totalBound : total < maxApp)
    (lookup : sptLookup (genericAppFnLocation n) s.code = some (n + 2, generateGenericApp maxApp n))
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
      (args ++ [.block 30 (ptr :: .number (Int.ofNat total) :: fields)] ++ rest) s =
    if s.clock < n + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
    else (.val [.block 31 (.codePtr (partialAppFnLocation maxApp total n) ::
      .number (Int.ofNat (total - (n + 1))) ::
      .block 30 (ptr :: .number (Int.ofNat total) :: fields) :: args)], BvlSem.decClock (n + 1) s) := by
  let closure := BvlSem.Value.block 30 (ptr :: .number (Int.ofNat total) :: fields)
  let env := args ++ [closure] ++ rest
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have argsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var) env s = (.val args, s) := by
    have bound : args.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars args.length env s bound
  have different : ((List.range args.length).map Bvl.Exp.var).length - 1 ≠ total := by
    simp only [List.length_map, List.length_range, length]
    omega
  have genericLookup : sptLookup (genericAppFnLocation (((List.range args.length).map Bvl.Exp.var).length - 1)) s.code =
      some (args.length + 1, generateGenericApp maxApp n) := by
    simpa [length] using lookup
  have callRun := evaluate_mkClCall_generic s env (.var args.length) ((List.range args.length).map Bvl.Exp.var)
    args 30 total ptr fields (generateGenericApp maxApp n) (by simpa [closure] using clRun) argsRun different genericLookup
  simp only [length] at callRun
  change BvlSem.evaluate [_] env s = _
  simp only [length]
  rw [callRun]
  by_cases zero : s.clock = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    have globalDec : ClosSem.getGlobal 0 (BvlSem.decClock 1 s).globals = some (some (globalTable maxApp)) := by
      simpa [BvlSem.decClock] using global
    rw [evaluate_genericApp_partial_new (BvlSem.decClock 1 s) maxApp n total args fields ptr
      length previousBound totalBound globalDec]
    have clockTest : (BvlSem.decClock 1 s).clock < n ↔ s.clock < n + 1 := by
      simp only [BvlSem.decClock]
      omega
    simp only [clockTest]
    split
    · simp [BvlSem.decClock]
    · have clocks : s.clock - 1 - n = s.clock - (n + 1) := by omega
      simp [BvlSem.decClock, clocks]

/-- Source partial application either times out or returns a closure with its
newly supplied arguments saved. -/
theorem evaluateApp_ordinary_partial {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : args ≠ []) (bound : args.length ≤ s.maxApp) (partialBound : args.length < arity) :
    ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
      if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else (.val [.closure (some ptr) args captured arity body], ClosSem.decClock args.length s) := by
  have found := destClosure_ordinary_partial s.maxApp ptr arity captured args body bound partialBound
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp

/-- The target partial closure is related to the source partial result, with
both sides charging exactly one tick per supplied argument. -/
theorem evaluateApp_ordinary_partial_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) targetClosure)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (partialBound : args.length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal) ∧
      evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
        [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel, closure⟩ := vRel_ordinary_closure functionRel
  have shape : arity ≤ s.maxApp ∧ arity ≠ 0 ∧
      targetClosure = .block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
    cases closure with
    | closure bound positive _ _ _ _ _ => exact ⟨bound, positive, rfl⟩
  obtain ⟨arityBound, positive, targetEq⟩ := shape
  have argsLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have argsPositive : 0 < args.length := List.length_pos_iff.mpr nonempty
  have argsBound : args.length ≤ s.maxApp := by omega
  let n := targetArgs.length - 1
  have targetLength : targetArgs.length = n + 1 := by dsimp [n]; omega
  have previousBound : n < arity - 1 := by dsimp [n]; omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have nBound : n < s.maxApp := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have lookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have global : ClosSem.getGlobal 0 start.globals = some (some (globalTable s.maxApp)) := states.2.2.1
  have targetRun := evaluate_mkClCall_partial_new start s.maxApp n (arity - 1) targetArgs fields rest
    (.codePtr (ptr + numStubs s.maxApp)) targetLength previousBound totalBound lookup global
  have tickEq : n + 1 = args.length := by omega
  have remainingEq : arity - 1 - (n + 1) = arity - 1 - args.length := by omega
  have sourceRun := evaluateApp_ordinary_partial s ptr arity captured args body nonempty argsBound partialBound
  by_cases timeout : s.clock < args.length
  · refine ⟨.err (.abort .timeoutError), { s with clock := 0 }, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · refine ⟨0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
      · have targetTimeout : start.clock < n + 1 := by dsimp [start]; omega
        rw [if_pos targetTimeout] at targetRun
        rw [targetEq]
        simpa only [start, Nat.add_zero] using targetRun
      · simp [resultRel, excRel]
      · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
      · intro key value mapped
        exact mapped
      · intro key value mapped fresh
        exact ⟨mapped, fresh⟩
  · refine ⟨.val [.closure (some ptr) args captured arity body], ClosSem.decClock args.length s, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · let next : BvlSem.State C F := BvlSem.decClock args.length start
      let partialClosure := BvlSem.Value.block 31
        (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) ::
          .number (Int.ofNat (arity - 1 - args.length)) :: targetClosure :: targetArgs)
      refine ⟨0, .val [partialClosure], next, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have targetEnough : ¬ start.clock < n + 1 := by dsimp [start]; omega
        rw [if_neg targetEnough] at targetRun
        rw [targetEq]
        dsimp only [partialClosure, next]
        rw [targetEq]
        simp only [tickEq] at targetRun
        simpa only [start, Nat.add_zero, n] using targetRun
      · apply List.Forall₂.cons
        · change vRel s.maxApp f t.refs t.code (.closure (some ptr) args captured arity body) partialClosure
          dsimp only [partialClosure]
          rw [targetEq]
          exact vRel_ordinary_partial s t f ptr arity captured args _ targetArgs body states
            (by simpa [targetEq] using functionRel) argsRel nonempty partialBound
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - args.length)).2.mpr
          ((stateRel_clock f s t (s.clock - args.length)).1.mpr states)
      · intro key value mapped
        exact mapped
      · intro key value mapped fresh
        exact ⟨mapped, fresh⟩
      · exact annotations
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- Source singleton recursive partial application and its clock behavior. -/
theorem evaluateApp_singletonRec_partial {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : args ≠ []) (bound : args.length ≤ s.maxApp) (partialBound : args.length < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) args s =
      if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else (.val [.recclosure (some ptr) args captured [(arity, body)] 0], ClosSem.decClock args.length s) := by
  have found := destClosure_singletonRec_partial s.maxApp ptr arity captured args body bound partialBound
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp

/-- The singleton recursive partial result is related to the target stub result. -/
theorem evaluateApp_singletonRec_partial_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured [(arity, body)] 0) targetClosure)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (partialBound : args.length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) args s = (result, sFinal) ∧
      evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
        [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel, closure⟩ := vRel_singletonRec_closure functionRel
  have shape : arity ≤ s.maxApp ∧ arity ≠ 0 ∧
      targetClosure = .block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
    cases closure with
    | singletonRec bound positive _ _ _ _ _ => exact ⟨bound, positive, rfl⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  obtain ⟨arityBound, positive, targetEq⟩ := shape
  have argsLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have argsPositive : 0 < args.length := List.length_pos_iff.mpr nonempty
  have argsBound : args.length ≤ s.maxApp := by omega
  let n := targetArgs.length - 1
  have targetLength : targetArgs.length = n + 1 := by dsimp [n]; omega
  have previousBound : n < arity - 1 := by dsimp [n]; omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have nBound : n < s.maxApp := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have lookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have global : ClosSem.getGlobal 0 start.globals = some (some (globalTable s.maxApp)) := states.2.2.1
  have targetRun := evaluate_mkClCall_partial_new start s.maxApp n (arity - 1) targetArgs fields rest
    (.codePtr (ptr + numStubs s.maxApp)) targetLength previousBound totalBound lookup global
  have tickEq : n + 1 = args.length := by omega
  have remainingEq : arity - 1 - (n + 1) = arity - 1 - args.length := by omega
  have sourceRun := evaluateApp_singletonRec_partial s ptr arity captured args body nonempty argsBound partialBound
  by_cases timeout : s.clock < args.length
  · refine ⟨.err (.abort .timeoutError), { s with clock := 0 }, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · refine ⟨0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
      · have targetTimeout : start.clock < n + 1 := by dsimp [start]; omega
        rw [if_pos targetTimeout] at targetRun
        rw [targetEq]
        simpa only [start, Nat.add_zero] using targetRun
      · simp [resultRel, excRel]
      · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
      · intro key value mapped
        exact mapped
      · intro key value mapped fresh
        exact ⟨mapped, fresh⟩
  · refine ⟨.val [.recclosure (some ptr) args captured [(arity, body)] 0], ClosSem.decClock args.length s, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · let next : BvlSem.State C F := BvlSem.decClock args.length start
      let partialClosure := BvlSem.Value.block 31
        (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) ::
          .number (Int.ofNat (arity - 1 - args.length)) :: targetClosure :: targetArgs)
      refine ⟨0, .val [partialClosure], next, f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have targetEnough : ¬ start.clock < n + 1 := by dsimp [start]; omega
        rw [if_neg targetEnough] at targetRun
        rw [targetEq]
        dsimp only [partialClosure, next]
        rw [targetEq]
        simp only [tickEq] at targetRun
        simpa only [start, Nat.add_zero, n] using targetRun
      · apply List.Forall₂.cons
        · change vRel s.maxApp f t.refs t.code (.recclosure (some ptr) args captured [(arity, body)] 0) partialClosure
          dsimp only [partialClosure]
          rw [targetEq]
          exact vRel_singletonRec_partial s t f ptr arity captured args _ targetArgs body states
            (by simpa [targetEq] using functionRel) argsRel nonempty partialBound
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - args.length)).2.mpr
          ((stateRel_clock f s t (s.clock - args.length)).1.mpr states)
      · intro key value mapped
        exact mapped
      · intro key value mapped fresh
        exact ⟨mapped, fresh⟩
      · exact annotations
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- A generic application that partially applies an ordinary closure composes
with the argument and function-expression simulations. -/
theorem evaluatePost_app_ordinary_partial {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.closure (some ptr) [] captured arity body], sFunction))
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) values sFunction =
      (result, sFinal)) (nonempty : values ≠ []) (partialBound : values.length < arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.closure (some ptr) [] captured arity body]) [targetFunction]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.closure (some ptr) [] captured arity body) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  obtain ⟨sourceResult, sourceFinal, sourceRun, targetPost⟩ :=
    evaluateApp_ordinary_partial_simulation sFunction tFunction fFunction ptr arity captured values targetValues
      targetEnv body targetClosure states annotations functionRel argsRel nonempty partialBound
  rw [appRun] at sourceRun
  cases sourceRun
  exact targetPost

/-- A generic partial application of a singleton recursive closure composes
with the argument and function-expression simulations. -/
theorem evaluatePost_app_singletonRec_partial {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.recclosure (some ptr) [] captured [(arity, body)] 0], sFunction))
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) values sFunction =
      (result, sFinal)) (nonempty : values ≠ []) (partialBound : values.length < arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.recclosure (some ptr) [] captured [(arity, body)] 0]) [targetFunction]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.recclosure (some ptr) [] captured [(arity, body)] 0) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  obtain ⟨sourceResult, sourceFinal, sourceRun, targetPost⟩ :=
    evaluateApp_singletonRec_partial_simulation sFunction tFunction fFunction ptr arity captured values targetValues
      targetEnv body targetClosure states annotations functionRel argsRel nonempty partialBound
  rw [appRun] at sourceRun
  cases sourceRun
  exact targetPost

/-- Application expression case for a newly partially applied closure. -/
theorem expressionSimulation_app_ordinary_partial_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.closure (some ptr) [] captured arity body], sFunction))
    (partialBound : values.length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have valuesNonempty : values ≠ [] := by
    intro empty
    have h := (ClosSem.evaluate_length (C := C) (F := F)).1 args sourceEnv s sArgs values argsRun
    simp [empty] at h
    apply nonempty
    cases args with
    | nil => rfl
    | cons head tail => simp at h
  have appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_ordinary_partial s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured ptr arity body result argsRun functionRun appRun valuesNonempty partialBound
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.closure (some ptr) [] captured arity body]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs


/-- Application expression case for a newly partially applied closure. -/
theorem expressionSimulation_app_singletonRec_partial_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.recclosure (some ptr) [] captured [(arity, body)] 0], sFunction))
    (partialBound : values.length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have valuesNonempty : values ≠ [] := by
    intro empty
    have h := (ClosSem.evaluate_length (C := C) (F := F)).1 args sourceEnv s sArgs values argsRun
    simp [empty] at h
    apply nonempty
    cases args with
    | nil => rfl
    | cons head tail => simp at h
  have appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured [(arity, body)] 0) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_singletonRec_partial s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured ptr arity body result argsRun functionRun appRun valuesNonempty partialBound
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.recclosure (some ptr) [] captured [(arity, body)] 0]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

/-- Extending a partial closure with another undersaturated argument prefix
preserves the value relation and selects the corresponding installed stub. -/
theorem vRel_partial_extend {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (captured oldArgs newArgs : List ClosSem.Value) (fields oldTargets newTargets : List BvlSem.Value)
    (original oldClosure newClosure : ClosSem.Value) (targetOriginal : BvlSem.Value) (arity : Nat)
    (states : stateRel f s t)
    (envRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (combinedBound : (newArgs ++ oldArgs).length < arity)
    (totalBound : arity - 1 < s.maxApp)
    (oldAdded : addArgs original oldArgs = some oldClosure)
    (newAdded : addArgs oldClosure newArgs = some newClosure)
    (getArgs : getNumArgs original = some arity)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) original targetOriginal) :
    vRel s.maxApp f t.refs t.code newClosure
      (.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1)
          ((newTargets ++ oldTargets).length - 1)) ::
        .number (Int.ofNat (arity - 1 - (newArgs ++ oldArgs).length)) ::
        targetOriginal :: (newTargets ++ oldTargets))) := by
  have combinedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (newArgs ++ oldArgs) (newTargets ++ oldTargets) := List.rel_append newRel oldRel
  have combinedNonempty : newArgs ++ oldArgs ≠ [] := by
    intro empty
    simp only [List.append_eq_nil_iff] at empty
    exact oldNonempty empty.2
  have targetLength : (newTargets ++ oldTargets).length = (newArgs ++ oldArgs).length := combinedRel.length_eq.symm
  have countPositive : 0 < (newArgs ++ oldArgs).length := List.length_pos_iff.mpr combinedNonempty
  have previousBound : (newTargets ++ oldTargets).length - 1 < arity - 1 := by omega
  have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) ((newTargets ++ oldTargets).length - 1)
    ⟨totalBound, previousBound⟩
  have sizeEq : arity - 1 - ((newTargets ++ oldTargets).length - 1) + 1 =
      arity - (newArgs ++ oldArgs).length + 1 := by omega
  have installed' : sptLookup (partialAppFnLocation s.maxApp (arity - 1) ((newTargets ++ oldTargets).length - 1)) t.code =
      some (arity - (newArgs ++ oldArgs).length + 1,
        generatePartialAppClosureFn (arity - 1) ((newTargets ++ oldTargets).length - 1)) := by
    rw [sizeEq] at installed
    exact installed
  have added : addArgs original (newArgs ++ oldArgs) = some newClosure := by
    rw [addArgs_append original oldArgs oldClosure newArgs oldAdded]
    exact newAdded
  exact .partialClosure envRel combinedRel combinedNonempty combinedBound installed' added getArgs closure

/-- The branch that extends an already partially applied closure. -/
def genericAppPartialExisting (maxApp n : Nat) : Bvl.Exp :=
  match genericAppPartialChoice maxApp n with
  | .ifThenElse _ _ existing => existing
  | _ => .var 0

/-- A partial-closure tag selects the extension branch after the generic
stub's arity test and tick sequence. -/
theorem evaluate_genericApp_partial_existing {C F : Type} (s : BvlSem.State C F)
    (maxApp n total : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (bound : n + 1 ≤ total) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block 31 (ptr :: .number (Int.ofNat total) :: fields)]) s =
    if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
    else BvlSem.evaluate [genericAppPartialExisting maxApp n]
      (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat total) :: fields)])) (BvlSem.decClock n s) := by
  rw [evaluate_genericApp_partial_ticks s maxApp n total 31 args fields ptr length bound]
  split
  · rfl
  · obtain ⟨other, shape⟩ := genericAppPartialChoice_shape maxApp n
    have otherEq : other = genericAppPartialExisting maxApp n := by
      simp [genericAppPartialExisting, shape]
    rw [shape, otherEq, BvlSem.evaluate, BvlSem.fixClock_evaluate]
    have test : BvlSem.evaluate [.op (.blockOp (.tagEq 30)) [.var (n + 2)]]
        (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
          (args ++ [.block 31 (ptr :: .number (Int.ofNat total) :: fields)])) (BvlSem.decClock n s) =
        (.val [BvlSem.boolValue false], BvlSem.decClock n s) := by
      simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, ← length]
    rw [test]
    simp [BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.falseTag, BvlSem.asBool]

/-- The existing-partial branch reconstructs the original total arity and
adds the new arguments to the saved-argument count when computing its slot. -/
theorem evaluate_existingPartial_index {C F : Type} {α : Type}
    (maxApp : α) (s : BvlSem.State C F) (rest : List BvlSem.Value)
    (n remaining saved : Nat) (bound : n < remaining) :
    BvlSem.evaluate [partialAppFnLocationCode maxApp
      (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
      (.op (.intOp .add) [.var 1, mkConst n])]
      (.number (Int.ofNat saved) :: .number (Int.ofNat (remaining - (n + 1))) :: rest) s =
    (.val [.number (Int.ofNat (saved + n + (remaining + saved) * (remaining + saved - 1) / 2))], s) := by
  let env := .number (Int.ofNat saved) :: .number (Int.ofNat (remaining - (n + 1))) :: rest
  have bound' : n + 1 ≤ remaining := by omega
  have totalRun : BvlSem.evaluate [.op (.intOp .add)
      [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]]] env s =
      (.val [.number (Int.ofNat (remaining + saved))], s) := by
    have sub := Int.ofNat_sub bound'
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, mkConst, env]
    omega
  have previousRun : BvlSem.evaluate [.op (.intOp .add) [.var 1, mkConst n]]
      (.number (Int.ofNat (remaining + saved)) :: env) s =
      (.val [.number (Int.ofNat (saved + n))], s) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, mkConst, env, Int.add_comm]
  exact evaluate_partialAppFnLocationCode_nat maxApp s env _ _ (remaining + saved) (saved + n)
    (by omega) totalRun previousRun

/-- The existing-partial branch's computed slot retrieves the stub for the
combined saved-argument count. -/
theorem evaluate_existingPartial_pointer {C F : Type}
    (s : BvlSem.State C F) (rest : List BvlSem.Value)
    (maxApp n remaining saved : Nat) (bound : n < remaining) (totalBound : remaining + saved < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [mkEl (.op (.globOp (.global 0)) [])
      (partialAppFnLocationCode maxApp
        (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
        (.op (.intOp .add) [.var 1, mkConst n]))]
      (.number (Int.ofNat saved) :: .number (Int.ofNat (remaining - (n + 1))) :: rest) s =
    (.val [.codePtr (partialAppFnLocation maxApp (remaining + saved) (saved + n))], s) := by
  apply evaluate_partialApp_global_pointer s _ _ maxApp (remaining + saved) (saved + n)
    totalBound (by omega) global
  exact evaluate_existingPartial_index maxApp s rest n remaining saved bound

/-- The body following the saved-argument count in the extension branch. -/
def genericAppPartialExistingBody (maxApp n : Nat) : Bvl.Exp :=
  match genericAppPartialExisting maxApp n with
  | .let _ body => body
  | _ => .var 0

/-- The extension branch first binds the count of previously saved arguments. -/
theorem genericAppPartialExisting_shape (maxApp n : Nat) :
    genericAppPartialExisting maxApp n = .let
      [.op (.intOp .sub) [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]]
      (genericAppPartialExistingBody maxApp n) := by
  have fullShape : ∃ normal body, genericAppPartialChoice maxApp n =
      .ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) normal
        (.let [.op (.intOp .sub) [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]] body) := by
    unfold genericAppPartialChoice genericAppPartialBranch generateGenericApp
    change ∃ normal body, stripGenericAppTicks n (genericAppTicks n
      (.ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) _ _)) = _
    rw [stripGenericAppTicks_generated]
    exact ⟨_, _, rfl⟩
  obtain ⟨normal, body, fullShape⟩ := fullShape
  have existsLet : ∃ body, genericAppPartialExisting maxApp n = .let
      [.op (.intOp .sub) [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]] body := by
    refine ⟨body, ?_⟩
    simp [genericAppPartialExisting, fullShape]
  obtain ⟨body, existsLet⟩ := existsLet
  simp [genericAppPartialExistingBody, existsLet]

/-- Entering the extension branch binds the length of the old argument suffix,
leaving the closure and new arguments available to the constructor. -/
theorem evaluate_genericAppPartialExisting_enter {C F : Type} (s : BvlSem.State C F)
    (maxApp n remaining : Nat) (args saved : List BvlSem.Value) (ptr original : BvlSem.Value)
    (length : args.length = n + 1) :
    BvlSem.evaluate [genericAppPartialExisting maxApp n]
      (.number (Int.ofNat (remaining - (n + 1))) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)])) s =
    BvlSem.evaluate [genericAppPartialExistingBody maxApp n]
      (.number (Int.ofNat saved.length) :: .number (Int.ofNat (remaining - (n + 1))) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)])) s := by
  have countRun : BvlSem.evaluate [.op (.intOp .sub)
      [mkConst 3, .op (.blockOp .lengthBlock) [.var (n + 2)]]]
      (.number (Int.ofNat (remaining - (n + 1))) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)])) s =
      (.val [.number (Int.ofNat saved.length)], s) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.applyNumeric, BvlSem.doIntApp, mkConst, ← length]
    omega
  rw [genericAppPartialExisting_shape, BvlSem.evaluate, BvlSem.fixClock_evaluate, countRun]
  rfl

/-- In the extension branch's bound environment, the generated global-table
lookup selects the stub for the old and new saved arguments. -/
theorem evaluate_genericAppPartialExisting_pointer {C F : Type} (s : BvlSem.State C F)
    (maxApp n remaining : Nat) (args saved : List BvlSem.Value) (ptr original : BvlSem.Value)
    (bound : n < remaining) (totalBound : remaining + saved.length < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [mkEl (.op (.globOp (.global 0)) [])
      (partialAppFnLocationCode maxApp
        (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
        (.op (.intOp .add) [.var 1, mkConst n]))]
      (.number (Int.ofNat saved.length) :: .number (Int.ofNat (remaining - (n + 1))) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)])) s =
      (.val [.codePtr (partialAppFnLocation maxApp (remaining + saved.length) (saved.length + n))], s) :=
  evaluate_existingPartial_pointer s _ maxApp n remaining saved.length bound totalBound global

/-- The two-slot offset version reads new arguments in reverse order. -/
theorem evaluate_reverse_offsetVars2 {C F : Type} (n : Nat) (first second : BvlSem.Value)
    (args rest : List BvlSem.Value) (s : BvlSem.State C F) (bound : n ≤ args.length) :
    BvlSem.evaluate (((List.range n).map (fun i => Bvl.Exp.var (i + 2))).reverse)
      (first :: second :: (args ++ rest)) s = (.val (args.take n).reverse, s) := by
  induction n with
  | zero => simp [BvlSem.evaluate]
  | succ n ih =>
    have smaller : n ≤ args.length := by omega
    have indexBound : n < args.length := by omega
    have varRun : BvlSem.evaluate [.var (n + 2)] (first :: second :: (args ++ rest)) s = (.val [args[n]], s) := by
      simp [BvlSem.evaluate, List.getElem?_append, indexBound]
    rw [List.range_succ, List.map_append, List.reverse_append]
    change BvlSem.evaluateTuple (.var (n + 2) :: _, first :: second :: (args ++ rest), s) = _
    rw [BvlProps.evaluateCons]
    simp only [BvlSem.evaluateTuple, varRun]
    dsimp only [List.append]
    rw [ih smaller]
    simp only [Flapjack.holHd, Prod.mk.injEq, Result.val.injEq, and_true]
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append] using
      (congrArg List.reverse (List.take_append_getElem indexBound))

/-- The extension body uses block extension to prepend the new saved fields. -/
theorem genericAppPartialExistingBody_shape (maxApp n : Nat) :
    genericAppPartialExistingBody maxApp n = .op (.blockOp (.consExtend 31))
      ((.var (n + 3) :: mkConst 3 :: .var 0 :: .op (.intOp .add) [.var 0, mkConst (n + 4)] ::
        mkEl (.op (.globOp (.global 0)) [])
          (partialAppFnLocationCode maxApp
            (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
            (.op (.intOp .add) [.var 1, mkConst n])) ::
        .var 1 :: .op (.blockOp (.elemAt 2)) [.var (n + 3)] ::
        (List.range (n + 1)).map (fun i => .var (i + 2))).reverse) := by
  unfold genericAppPartialExistingBody genericAppPartialExisting genericAppPartialChoice
    genericAppPartialBranch generateGenericApp
  change (match (match stripGenericAppTicks n (genericAppTicks n
      (.ifThenElse (.op (.blockOp (.tagEq 30)) [.var (n + 2)]) _ _)) with
      | .ifThenElse _ _ existing => existing | _ => .var 0) with
      | .let _ body => body | _ => .var 0) = _
  rw [stripGenericAppTicks_generated]
  rfl

/-- Block extension preserves the old saved suffix after the newly supplied
arguments, retaining the new stub pointer and original closure. -/
theorem doApp_extendPartial {C F : Type} (s : BvlSem.State C F)
    (n remaining savedCount : Nat) (args saved : List BvlSem.Value)
    (oldPtr newPtr original : BvlSem.Value) (length : args.length = n + 1)
    (savedLength : saved.length = savedCount) :
    BvlSem.doApp (.blockOp (.consExtend 31))
      (.block 31 (oldPtr :: .number (Int.ofNat remaining) :: original :: saved) ::
        .number 3 :: .number (Int.ofNat savedCount) :: .number (Int.ofNat (savedCount + (n + 4))) ::
        newPtr :: .number (Int.ofNat (remaining - (n + 1))) :: original :: args) s =
    .val (.block 31 (newPtr :: .number (Int.ofNat (remaining - (n + 1))) :: original :: (args ++ saved)), s) := by
  simp [BvlSem.doApp, BvlSem.applyBlock, length, savedLength]
  have valid : ¬ ((savedCount : Int) < 0 ∨
      (savedCount : Int) + 1 + 1 + 1 < 3 + (savedCount : Int) ∨
      (savedCount : Int) + ((n : Int) + 4) = 0 ∨
      ¬ (savedCount : Int) + ((n : Int) + 4) = (n : Int) + 1 + 1 + 1 + 1 + (savedCount : Int)) := by omega
  simp only [if_neg valid]
  simp [← savedLength]

/-- The existing-partial body constructs the extended closure with the new
arguments followed by the old saved arguments. -/
theorem evaluate_genericAppPartialExistingBody {C F : Type} (s : BvlSem.State C F)
    (maxApp n remaining : Nat) (args saved : List BvlSem.Value) (ptr original : BvlSem.Value)
    (length : args.length = n + 1) (bound : n < remaining) (totalBound : remaining + saved.length < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [genericAppPartialExistingBody maxApp n]
      (.number (Int.ofNat saved.length) :: .number (Int.ofNat (remaining - (n + 1))) ::
        (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)])) s =
    (.val [.block 31 (.codePtr (partialAppFnLocation maxApp (remaining + saved.length) (saved.length + n)) ::
      .number (Int.ofNat (remaining - (n + 1))) :: original :: (args ++ saved))], s) := by
  let old := BvlSem.Value.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)
  let newPtr := BvlSem.Value.codePtr (partialAppFnLocation maxApp (remaining + saved.length) (saved.length + n))
  let env := .number (Int.ofNat saved.length) :: .number (Int.ofNat (remaining - (n + 1))) :: (args ++ [old])
  let slot := mkEl (.op (.globOp (.global 0)) [])
    (partialAppFnLocationCode maxApp
      (.op (.intOp .add) [.var 0, .op (.intOp .add) [mkConst (n + 1), .var 1]])
      (.op (.intOp .add) [.var 1, mkConst n]))
  let totalExp := Bvl.Exp.op (.intOp .add) [.var 0, mkConst (n + 4)]
  let originalExp := Bvl.Exp.op (.blockOp (.elemAt 2)) [.var (n + 3)]
  have varsRun : BvlSem.evaluate (((List.range (n + 1)).map (fun i => Bvl.Exp.var (i + 2))).reverse) env s =
      (.val args.reverse, s) := by
    simpa [env, ← length] using evaluate_reverse_offsetVars2 (n + 1) (.number (Int.ofNat saved.length))
      (.number (Int.ofNat (remaining - (n + 1)))) args [old] s (by omega)
  have oldRun : BvlSem.evaluate [.var (n + 3)] env s = (.val [old], s) := by
    simp [BvlSem.evaluate, env, ← length]
  have originalRun : BvlSem.evaluate [originalExp] env s = (.val [original], s) := by
    rw [show originalExp = .op (.blockOp (.elemAt 2)) [.var (n + 3)] from rfl,
      BvlSem.evaluate, BvlSem.fixClock_evaluate, oldRun]
    simp [BvlSem.doApp, BvlSem.applyBlock, old]
  have remainingRun : BvlSem.evaluate [.var 1] env s =
      (.val [.number (Int.ofNat (remaining - (n + 1)))], s) := by simp [BvlSem.evaluate, env]
  have savedRun : BvlSem.evaluate [.var 0] env s = (.val [.number (Int.ofNat saved.length)], s) := by
    simp [BvlSem.evaluate, env]
  have slotRun : BvlSem.evaluate [slot] env s = (.val [newPtr], s) := by
    exact evaluate_genericAppPartialExisting_pointer s maxApp n remaining args saved ptr original bound totalBound global
  have totalRun : BvlSem.evaluate [totalExp] env s = (.val [.number (Int.ofNat (saved.length + (n + 4)))], s) := by
    simp [totalExp, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, mkConst, env, Int.add_comm]
  have constRun : BvlSem.evaluate [mkConst 3] env s = (.val [.number 3], s) := by
    simp [mkConst, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]
  have tailRun : BvlSem.evaluate [originalExp, .var 1, slot, totalExp, .var 0, mkConst 3, .var (n + 3)] env s =
      (.val [original, .number (Int.ofNat (remaining - (n + 1))), newPtr,
        .number (Int.ofNat (saved.length + (n + 4))), .number (Int.ofNat saved.length), .number 3, old], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, originalRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, remainingRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, slotRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, totalRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, savedRun]
    dsimp only
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, constRun]
    dsimp only
    rw [oldRun]
    rfl
  have allRun : BvlSem.evaluate
      (((List.range (n + 1)).map (fun i => Bvl.Exp.var (i + 2))).reverse ++
        [originalExp, .var 1, slot, totalExp, .var 0, mkConst 3, .var (n + 3)]) env s =
      (.val (args.reverse ++ [original, .number (Int.ofNat (remaining - (n + 1))), newPtr,
        .number (Int.ofNat (saved.length + (n + 4))), .number (Int.ofNat saved.length), .number 3, old]), s) := by
    change BvlSem.evaluateTuple (_, env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, varsRun, tailRun]
  rw [genericAppPartialExistingBody_shape, BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  rw [allRun]
  have extended := doApp_extendPartial s n remaining saved.length args saved ptr newPtr original length rfl
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_reverse,
    List.nil_append, List.singleton_append, List.append_assoc] at *
  simp only [List.cons_append, List.nil_append]
  change (match BvlSem.doApp (.blockOp (.consExtend 31))
    (.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved) ::
      .number 3 :: .number (Int.ofNat saved.length) :: .number (Int.ofNat (saved.length + (n + 4))) ::
      newPtr :: .number (Int.ofNat (remaining - (n + 1))) :: original :: args) s with
    | .err error => (Result.err error, s)
    | .val (value, last) => (Result.val [value], last)) = _
  rw [extended]

/-- The generated generic stub extends an existing partial closure, retaining
the original closure and the saved argument suffix. -/
theorem evaluate_genericApp_partial_extend {C F : Type} (s : BvlSem.State C F)
    (maxApp n remaining : Nat) (args saved : List BvlSem.Value) (ptr original : BvlSem.Value)
    (length : args.length = n + 1) (bound : n < remaining)
    (totalBound : remaining + saved.length < maxApp)
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)]) s =
    if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
    else (.val [.block 31 (.codePtr (partialAppFnLocation maxApp (remaining + saved.length) (saved.length + n)) ::
      .number (Int.ofNat (remaining - (n + 1))) :: original :: (args ++ saved))], BvlSem.decClock n s) := by
  rw [evaluate_genericApp_partial_existing s maxApp n remaining args (original :: saved) ptr length (by omega)]
  split
  · rfl
  · have sub : Int.ofNat remaining - Int.ofNat (n + 1) = Int.ofNat (remaining - (n + 1)) := by
      exact (Int.ofNat_sub (by omega)).symm
    rw [sub, evaluate_genericAppPartialExisting_enter _ maxApp n remaining args saved ptr original length]
    apply evaluate_genericAppPartialExistingBody _ maxApp n remaining args saved ptr original length bound totalBound
    simpa [BvlSem.decClock] using global

/-- A generated closure call extends an existing partial closure, charging
one tick for the call and one for each remaining stub tick. -/
theorem evaluate_mkClCall_partial_extend {C F : Type} (s : BvlSem.State C F)
    (maxApp n remaining : Nat) (args saved rest : List BvlSem.Value) (ptr original : BvlSem.Value)
    (length : args.length = n + 1) (bound : n < remaining)
    (totalBound : remaining + saved.length < maxApp)
    (lookup : sptLookup (genericAppFnLocation n) s.code = some (n + 2, generateGenericApp maxApp n))
    (global : ClosSem.getGlobal 0 s.globals = some (some (globalTable maxApp))) :
    BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
      (args ++ [.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)] ++ rest) s =
    if s.clock < n + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
    else (.val [.block 31 (.codePtr (partialAppFnLocation maxApp (remaining + saved.length) (saved.length + n)) ::
      .number (Int.ofNat (remaining - (n + 1))) :: original :: (args ++ saved))], BvlSem.decClock (n + 1) s) := by
  let closure := BvlSem.Value.block 31 (ptr :: .number (Int.ofNat remaining) :: original :: saved)
  let env := args ++ [closure] ++ rest
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have argsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var) env s = (.val args, s) := by
    have envBound : args.length ≤ env.length := by simp [env]
    simpa [env] using evaluate_rangeVars args.length env s envBound
  have different : ((List.range args.length).map Bvl.Exp.var).length - 1 ≠ remaining := by
    simp only [List.length_map, List.length_range, length]
    omega
  have genericLookup : sptLookup (genericAppFnLocation (((List.range args.length).map Bvl.Exp.var).length - 1)) s.code =
      some (args.length + 1, generateGenericApp maxApp n) := by
    simpa [length] using lookup
  have callRun := evaluate_mkClCall_generic s env (.var args.length) ((List.range args.length).map Bvl.Exp.var)
    args 31 remaining ptr (original :: saved) (generateGenericApp maxApp n)
    (by simpa [closure] using clRun) argsRun different genericLookup
  simp only [length] at callRun
  change BvlSem.evaluate [_] env s = _
  simp only [length]
  rw [callRun]
  by_cases zero : s.clock = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    have globalDec : ClosSem.getGlobal 0 (BvlSem.decClock 1 s).globals = some (some (globalTable maxApp)) := by
      simpa [BvlSem.decClock] using global
    rw [evaluate_genericApp_partial_extend (BvlSem.decClock 1 s) maxApp n remaining args saved ptr original
      length bound totalBound globalDec]
    have clockTest : (BvlSem.decClock 1 s).clock < n ↔ s.clock < n + 1 := by
      simp only [BvlSem.decClock]
      omega
    simp only [clockTest]
    split
    · simp [BvlSem.decClock]
    · have clocks : s.clock - 1 - n = s.clock - (n + 1) := by omega
      simp [BvlSem.decClock, clocks]

/-- Source evaluation saves a second, still undersaturating argument group. -/
theorem evaluateApp_ordinary_partial_again {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : newArgs ≠ []) (bound : newArgs.length ≤ s.maxApp)
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s =
      if s.clock < newArgs.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else (.val [.closure (some ptr) (newArgs ++ oldArgs) captured arity body],
        ClosSem.decClock newArgs.length s) := by
  have oldBound : oldArgs.length < arity := by simp only [List.length_append] at partialBound; omega
  have found : ClosSem.destClosure s.maxApp none (.closure (some ptr) oldArgs captured arity body) newArgs =
      some (.partialApp (.closure (some ptr) (newArgs ++ oldArgs) captured arity body)) := by
    simp [ClosSem.destClosure, ClosSem.checkLoc, bound, oldBound, ← List.length_append, partialBound]
  cases newArgs with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp

/-- Repeated partial application of an ordinary closure preserves the value and
state relations for the emitted call and its exact clock cost. -/
theorem evaluateApp_ordinary_partial_again_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (targetOriginal : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (originalRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) targetOriginal)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    let targetClosure := BvlSem.Value.block 31
      (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: targetOriginal :: oldTargets)
    ∃ result sFinal,
      ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [targetClosure] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel, closure⟩ := vRel_ordinary_closure originalRel
  have arityBound : arity ≤ s.maxApp := by cases closure with | closure bound _ _ _ _ _ _ => exact bound
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have combinedLength : newArgs.length + oldArgs.length < arity := by simpa using partialBound
  have argsBound : newArgs.length ≤ s.maxApp := by omega
  let n := newTargets.length - 1
  let remaining := arity - 1 - oldArgs.length
  have targetLength : newTargets.length = n + 1 := by dsimp [n]; omega
  have remainingBound : n < remaining := by dsimp [n, remaining]; omega
  have totalBound : remaining + oldTargets.length < s.maxApp := by dsimp [remaining]; omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have lookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have global : ClosSem.getGlobal 0 start.globals = some (some (globalTable s.maxApp)) := states.2.2.1
  have targetRun := evaluate_mkClCall_partial_extend start s.maxApp n remaining newTargets oldTargets rest
    (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1))) targetOriginal
    targetLength remainingBound totalBound lookup global
  have tickEq : n + 1 = newArgs.length := by omega
  have totalEq : remaining + oldTargets.length = arity - 1 := by dsimp [remaining]; omega
  have indexEq : oldTargets.length + n = (newTargets ++ oldTargets).length - 1 := by
    simp only [List.length_append]; dsimp [n]; omega
  have remainingEq : remaining - (n + 1) = arity - 1 - (newArgs ++ oldArgs).length := by
    simp only [List.length_append]; dsimp [remaining, n]; omega
  have sourceRun := evaluateApp_ordinary_partial_again s ptr arity captured oldArgs newArgs body nonempty argsBound partialBound
  by_cases timeout : s.clock < newArgs.length
  · refine ⟨.err (.abort .timeoutError), { s with clock := 0 }, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · refine ⟨0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
      · have targetTimeout : start.clock < n + 1 := by dsimp [start]; omega
        rw [if_pos targetTimeout] at targetRun
        simpa only [start, remaining, Nat.add_zero] using targetRun
      · simp [resultRel, excRel]
      · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
      · intro key value mapped; exact mapped
      · intro key value mapped fresh; exact ⟨mapped, fresh⟩
  · refine ⟨.val [.closure (some ptr) (newArgs ++ oldArgs) captured arity body],
      ClosSem.decClock newArgs.length s, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · let next : BvlSem.State C F := BvlSem.decClock newArgs.length start
      let combined := BvlSem.Value.block 31
        (.codePtr (partialAppFnLocation s.maxApp (arity - 1) ((newTargets ++ oldTargets).length - 1)) ::
          .number (Int.ofNat (arity - 1 - (newArgs ++ oldArgs).length)) :: targetOriginal :: (newTargets ++ oldTargets))
      refine ⟨0, .val [combined], next, f, ?_, ?_, ?_, ?_, ?_, annotations, ?_⟩
      · have targetEnough : ¬ start.clock < n + 1 := by dsimp [start]; omega
        rw [if_neg targetEnough, totalEq, indexEq, remainingEq, tickEq] at targetRun
        simpa only [start, remaining, next, combined, Nat.add_zero] using targetRun
      · apply List.Forall₂.cons
        · change vRel s.maxApp f t.refs t.code (.closure (some ptr) (newArgs ++ oldArgs) captured arity body) combined
          dsimp only [combined]
          exact vRel_partial_extend s t f captured oldArgs newArgs fields oldTargets newTargets
            (.closure (some ptr) [] captured arity body) (.closure (some ptr) oldArgs captured arity body)
            (.closure (some ptr) (newArgs ++ oldArgs) captured arity body) targetOriginal arity
            states envRel oldRel newRel oldNonempty partialBound (by omega)
            (by simp [addArgs]) (by simp [addArgs]) (by simp [getNumArgs]) closure
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr
          ((stateRel_clock f s t (s.clock - newArgs.length)).1.mpr states)
      · intro key value mapped; exact mapped
      · intro key value mapped fresh; exact ⟨mapped, fresh⟩
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- A related already-partial ordinary closure exposes its original closure
and the corresponding saved argument values. -/
theorem vRel_ordinary_partial_existing {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (target : BvlSem.Value) (nonempty : oldArgs ≠ [])
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) oldArgs captured arity body) target) :
    ∃ oldTargets targetOriginal,
      target = .block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: targetOriginal :: oldTargets) ∧
      vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) targetOriginal ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets := by
  cases related with
  | closure envRel closure => cases closure; simp_all
  | @partialClosure env fvs argEnv ys numArgs cl clApp cl' envRel argRel argsNonempty argsBound installed added arityEq closure =>
    cases cl <;> simp [addArgs] at added
    case closure loc supplied captured' arity' body' =>
      obtain ⟨rfl, argsEq, rfl, rfl, rfl⟩ := added
      cases closure with
      | closure bound positive locs vars compiled codeInstalled lookup =>
        simp only [List.append_nil] at argsEq
        subst oldArgs
        simp [getNumArgs] at arityEq
        subst numArgs
        exact ⟨ys, _, rfl, .closure envRel (.closure bound positive locs vars compiled codeInstalled lookup), argRel⟩

/-- The repeated-partial simulation follows from the ordinary value relation;
callers need not supply the target closure layout or saved values separately. -/
theorem evaluateApp_ordinary_partial_again_related {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) oldArgs captured arity body) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨oldTargets, original, rfl, originalRel, oldRel⟩ :=
    vRel_ordinary_partial_existing s t f ptr arity captured oldArgs body target oldNonempty related
  exact evaluateApp_ordinary_partial_again_simulation s t f ptr arity captured oldArgs newArgs
    oldTargets newTargets rest body original states annotations originalRel oldRel newRel oldNonempty nonempty partialBound

/-- Compose repeated ordinary partial application with the function and
argument expression simulations. -/
theorem evaluatePost_app_ordinary_partial_again {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured oldArgs : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.closure (some ptr) oldArgs captured arity body], sFunction))
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) values sFunction =
      (result, sFinal)) (oldNonempty : oldArgs ≠ []) (nonempty : values ≠ [])
    (partialBound : (values ++ oldArgs).length < arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.closure (some ptr) oldArgs captured arity body]) [targetFunction]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.closure (some ptr) oldArgs captured arity body) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  obtain ⟨sourceResult, sourceFinal, sourceRun, targetPost⟩ :=
    evaluateApp_ordinary_partial_again_related sFunction tFunction fFunction ptr arity captured oldArgs values
      targetValues targetEnv body targetClosure states annotations functionRel argsRel oldNonempty nonempty partialBound
  rw [appRun] at sourceRun
  cases sourceRun
  exact targetPost

/-- Source evaluation saves a second, still undersaturating argument group. -/
theorem evaluateApp_singletonRec_partial_again {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : newArgs ≠ []) (bound : newArgs.length ≤ s.maxApp)
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s =
      if s.clock < newArgs.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else (.val [.recclosure (some ptr) (newArgs ++ oldArgs) captured [(arity, body)] 0],
        ClosSem.decClock newArgs.length s) := by
  have oldBound : oldArgs.length < arity := by simp only [List.length_append] at partialBound; omega
  have found : ClosSem.destClosure s.maxApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs =
      some (.partialApp (.recclosure (some ptr) (newArgs ++ oldArgs) captured [(arity, body)] 0)) := by
    simp [ClosSem.destClosure, ClosSem.checkLoc, bound, oldBound, ← List.length_append, partialBound]
  cases newArgs with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp

/-- Repeated partial application of a singleton recursive closure preserves the value and
state relations for the emitted call and its exact clock cost. -/
theorem evaluateApp_singletonRec_partial_again_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (targetOriginal : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (originalRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured [(arity, body)] 0) targetOriginal)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    let targetClosure := BvlSem.Value.block 31
      (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: targetOriginal :: oldTargets)
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [targetClosure] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel, closure⟩ := vRel_singletonRec_closure originalRel
  have arityBound : arity ≤ s.maxApp := by
    cases closure with
    | singletonRec bound _ _ _ _ _ _ => exact bound
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have combinedLength : newArgs.length + oldArgs.length < arity := by simpa using partialBound
  have argsBound : newArgs.length ≤ s.maxApp := by omega
  let n := newTargets.length - 1
  let remaining := arity - 1 - oldArgs.length
  have targetLength : newTargets.length = n + 1 := by dsimp [n]; omega
  have remainingBound : n < remaining := by dsimp [n, remaining]; omega
  have totalBound : remaining + oldTargets.length < s.maxApp := by dsimp [remaining]; omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have lookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have global : ClosSem.getGlobal 0 start.globals = some (some (globalTable s.maxApp)) := states.2.2.1
  have targetRun := evaluate_mkClCall_partial_extend start s.maxApp n remaining newTargets oldTargets rest
    (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1))) targetOriginal
    targetLength remainingBound totalBound lookup global
  have tickEq : n + 1 = newArgs.length := by omega
  have totalEq : remaining + oldTargets.length = arity - 1 := by dsimp [remaining]; omega
  have indexEq : oldTargets.length + n = (newTargets ++ oldTargets).length - 1 := by
    simp only [List.length_append]; dsimp [n]; omega
  have remainingEq : remaining - (n + 1) = arity - 1 - (newArgs ++ oldArgs).length := by
    simp only [List.length_append]; dsimp [remaining, n]; omega
  have sourceRun := evaluateApp_singletonRec_partial_again s ptr arity captured oldArgs newArgs body nonempty argsBound partialBound
  by_cases timeout : s.clock < newArgs.length
  · refine ⟨.err (.abort .timeoutError), { s with clock := 0 }, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · refine ⟨0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
      · have targetTimeout : start.clock < n + 1 := by dsimp [start]; omega
        rw [if_pos targetTimeout] at targetRun
        simpa only [start, remaining, Nat.add_zero] using targetRun
      · simp [resultRel, excRel]
      · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
      · intro key value mapped; exact mapped
      · intro key value mapped fresh; exact ⟨mapped, fresh⟩
  · refine ⟨.val [.recclosure (some ptr) (newArgs ++ oldArgs) captured [(arity, body)] 0],
      ClosSem.decClock newArgs.length s, ?_, ?_⟩
    · simpa [timeout] using sourceRun
    · let next : BvlSem.State C F := BvlSem.decClock newArgs.length start
      let combined := BvlSem.Value.block 31
        (.codePtr (partialAppFnLocation s.maxApp (arity - 1) ((newTargets ++ oldTargets).length - 1)) ::
          .number (Int.ofNat (arity - 1 - (newArgs ++ oldArgs).length)) :: targetOriginal :: (newTargets ++ oldTargets))
      refine ⟨0, .val [combined], next, f, ?_, ?_, ?_, ?_, ?_, annotations, ?_⟩
      · have targetEnough : ¬ start.clock < n + 1 := by dsimp [start]; omega
        rw [if_neg targetEnough, totalEq, indexEq, remainingEq, tickEq] at targetRun
        simpa only [start, remaining, next, combined, Nat.add_zero] using targetRun
      · apply List.Forall₂.cons
        · change vRel s.maxApp f t.refs t.code (.recclosure (some ptr) (newArgs ++ oldArgs) captured [(arity, body)] 0) combined
          dsimp only [combined]
          exact vRel_partial_extend s t f captured oldArgs newArgs fields oldTargets newTargets
            (.recclosure (some ptr) [] captured [(arity, body)] 0) (.recclosure (some ptr) oldArgs captured [(arity, body)] 0)
            (.recclosure (some ptr) (newArgs ++ oldArgs) captured [(arity, body)] 0) targetOriginal arity
            states envRel oldRel newRel oldNonempty partialBound (by omega)
            (by simp [addArgs]) (by simp [addArgs]) (by simp [getNumArgs, Flapjack.holEl, Flapjack.holHd]) closure
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr
          ((stateRel_clock f s t (s.clock - newArgs.length)).1.mpr states)
      · intro key value mapped; exact mapped
      · intro key value mapped fresh; exact ⟨mapped, fresh⟩
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- A related already-partial singleton recursive closure exposes its original
closure and the corresponding saved argument values. -/
theorem vRel_singletonRec_partial_existing {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (target : BvlSem.Value) (nonempty : oldArgs ≠ [])
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) target) :
    ∃ oldTargets targetOriginal,
      target = .block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: targetOriginal :: oldTargets) ∧
      vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured [(arity, body)] 0) targetOriginal ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets := by
  have empty {env : List ClosSem.Value} {fvs : List BvlSem.Value} {v : BvlSem.Value}
      (rel : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
        (env, fvs) (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) v) : oldArgs = [] := by
    cases rel with
    | singletonRec _ _ _ _ _ _ _ => rfl
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  cases related with
  | closure envRel closure => exact (nonempty (empty closure)).elim
  | @partialClosure env fvs argEnv ys numArgs cl clApp cl' envRel argRel argsNonempty argsBound installed added arityEq closure =>
    cases cl <;> simp [addArgs] at added
    case recclosure loc supplied captured' functions index =>
      obtain ⟨rfl, argsEq, rfl, rfl, rfl⟩ := added
      cases closure with
      | singletonRec bound positive locs vars compiled codeInstalled lookup =>
        simp only [List.append_nil] at argsEq
        subst oldArgs
        simp [getNumArgs, Flapjack.holEl, Flapjack.holHd] at arityEq
        subst numArgs
        exact ⟨ys, _, rfl, .closure envRel (.singletonRec bound positive locs vars compiled codeInstalled lookup), argRel⟩
      | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible

/-- The repeated-partial simulation follows from the value relation;
callers need not supply the target closure layout or saved values separately. -/
theorem evaluateApp_singletonRec_partial_again_related {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨oldTargets, original, rfl, originalRel, oldRel⟩ :=
    vRel_singletonRec_partial_existing s t f ptr arity captured oldArgs body target oldNonempty related
  exact evaluateApp_singletonRec_partial_again_simulation s t f ptr arity captured oldArgs newArgs
    oldTargets newTargets rest body original states annotations originalRel oldRel newRel oldNonempty nonempty partialBound

/-- Compose repeated singleton recursive partial application with the function and
argument expression simulations. -/
theorem evaluatePost_app_singletonRec_partial_again {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values captured oldArgs : List ClosSem.Value)
    (ptr arity : Nat) (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs =
      (.val [.recclosure (some ptr) oldArgs captured [(arity, body)] 0], sFunction))
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) values sFunction =
      (result, sFinal)) (oldNonempty : oldArgs ≠ []) (nonempty : values ≠ [])
    (partialBound : (values ++ oldArgs).length < arity)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [.recclosure (some ptr) oldArgs captured [(arity, body)] 0]) [targetFunction]) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) result
    argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  obtain ⟨sourceResult, sourceFinal, sourceRun, targetPost⟩ :=
    evaluateApp_singletonRec_partial_again_related sFunction tFunction fFunction ptr arity captured oldArgs values
      targetValues targetEnv body targetClosure states annotations functionRel argsRel oldNonempty nonempty partialBound
  rw [appRun] at sourceRun
  cases sourceRun
  exact targetPost

/-- Application expression case for a repeatedly partially applied closure. -/
theorem expressionSimulation_app_ordinary_partial_again_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured oldArgs : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.closure (some ptr) oldArgs captured arity body], sFunction))
    (oldNonempty : oldArgs ≠ []) (partialBound : (values ++ oldArgs).length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have valuesNonempty : values ≠ [] := by
    intro empty
    have h := (ClosSem.evaluate_length (C := C) (F := F)).1 args sourceEnv s sArgs values argsRun
    simp [empty] at h
    apply nonempty
    cases args with
    | nil => rfl
    | cons head tail => simp at h
  have appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_ordinary_partial_again s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured oldArgs ptr arity body result argsRun functionRun appRun oldNonempty valuesNonempty partialBound
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.closure (some ptr) oldArgs captured arity body]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs


/-- Application expression case for a repeatedly partially applied closure. -/
theorem expressionSimulation_app_singletonRec_partial_again_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured oldArgs : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.recclosure (some ptr) oldArgs captured [(arity, body)] 0], sFunction))
    (oldNonempty : oldArgs ≠ []) (partialBound : (values ++ oldArgs).length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have valuesNonempty : values ≠ [] := by
    intro empty
    have h := (ClosSem.evaluate_length (C := C) (F := F)).1 args sourceEnv s sArgs values argsRun
    simp [empty] at h
    apply nonempty
    cases args with
    | nil => rfl
    | cons head tail => simp at h
  have appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) values sFunction =
      (result, sFinal) := by
    have notEmpty : args.isEmpty = false := by cases args <;> simp_all
    rw [ClosSem.evaluate] at run
    simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at run
    rw [ClosSem.fixClock_evaluate, argsRun] at run
    dsimp only at run
    rw [ClosSem.fixClock_evaluate, functionRun] at run
    exact run
  cases functionCompile : compileExpHOL s.maxApp function aux with
  | mk targetFunction middleAux =>
    cases argsCompile : compileExpListHOL s.maxApp args middleAux with
    | mk targetArgs lastAux =>
      have whole := compile_appTarget s.maxApp trace none function args aux middleAux lastAux
        targetFunction targetArgs functionCompile argsCompile
      have equal := compile.symm.trans whole
      cases equal
      have argsCompiled : compileExpsHOL s.maxApp args middleAux = (targetArgs, finalAux) := by
        rw [compileExps_eq_list]
        exact argsCompile
      have functionCompiled : compileExpsHOL s.maxApp [function] aux = ([targetFunction], middleAux) := by
        rw [compileExps_eq_list]
        simp [compileExpListHOL, functionCompile]
      have functionInstalled : codeInstalled middleAux t.code :=
        compileExps_codeInstalled s.maxApp args middleAux finalAux targetArgs t.code argsCompiled installed
      have locationsParts : ClosProps.fnLocationSomeExp function ∧ ClosProps.everyFnLocationSome args := by
        simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
      have varsParts : ClosProps.fnVarsSomeExp function ∧ ClosProps.everyFnVarsSome args := by
        simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using vars
      have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
        argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_singletonRec_partial_again s sArgs sFunction sFinal t sourceEnv targetEnv f args function
        targetArgs targetFunction values captured oldArgs ptr arity body result argsRun functionRun appRun oldNonempty valuesNonempty partialBound
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [.recclosure (some ptr) oldArgs captured [(arity, body)] 0]) functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

/-- Application expression simulation for any undersaturated argument prefix. -/
theorem expressionSimulation_app_ordinary_partial_all_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured oldArgs : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.closure (some ptr) oldArgs captured arity body], sFunction))
    (partialBound : (values ++ oldArgs).length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  cases oldArgs with
  | nil =>
    simp only [List.append_nil] at partialBound
    exact expressionSimulation_app_ordinary_partial_case s sArgs sFunction sFinal t sourceEnv targetEnv f
      trace args function values captured ptr arity body aux finalAux compiled result argsRun functionRun
      partialBound run noType compile locations annotations vars installed envRelated states argsIH functionIH
  | cons head tail =>
    exact expressionSimulation_app_ordinary_partial_again_case s sArgs sFunction sFinal t sourceEnv targetEnv f
      trace args function values captured (head :: tail) ptr arity body aux finalAux compiled result argsRun functionRun
      (by simp) partialBound run noType compile locations annotations vars installed envRelated states argsIH functionIH

/-- Application expression simulation for any undersaturated argument prefix. -/
theorem expressionSimulation_app_singletonRec_partial_all_case {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values captured oldArgs : List ClosSem.Value) (ptr arity : Nat) (body : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [.recclosure (some ptr) oldArgs captured [(arity, body)] 0], sFunction))
    (partialBound : (values ++ oldArgs).length < arity)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulation (C := C) (F := F) args)
    (functionIH : expressionSimulation (C := C) (F := F) [function])
    :
    evaluatePost s sFinal t targetEnv f result compiled := by
  cases oldArgs with
  | nil =>
    simp only [List.append_nil] at partialBound
    exact expressionSimulation_app_singletonRec_partial_case s sArgs sFunction sFinal t sourceEnv targetEnv f
      trace args function values captured ptr arity body aux finalAux compiled result argsRun functionRun
      partialBound run noType compile locations annotations vars installed envRelated states argsIH functionIH
  | cons head tail =>
    exact expressionSimulation_app_singletonRec_partial_again_case s sArgs sFunction sFinal t sourceEnv targetEnv f
      trace args function values captured (head :: tail) ptr arity body aux finalAux compiled result argsRun functionRun
      (by simp) partialBound run noType compile locations annotations vars installed envRelated states argsIH functionIH

/-- The completion stub reads the newly supplied arguments after binding the
original closure at the front of its environment. -/
theorem evaluate_completion_newArgs {C F : Type} (args rest : List BvlSem.Value)
    (original : BvlSem.Value) (s : BvlSem.State C F) :
    BvlSem.evaluate ((List.range args.length).map (fun i => Bvl.Exp.var (i + 1)))
      (original :: (args ++ rest)) s = (.val args, s) := by
  have shifted : ∀ n, n ≤ args.length →
      BvlSem.evaluate ((List.range n).map (fun i => Bvl.Exp.var (i + 1)))
        (original :: (args ++ rest)) s = (.val (args.take n), s) := by
    intro n bound
    induction n with
    | zero => simp [BvlSem.evaluate]
    | succ n ih =>
      have boundN : n ≤ args.length := by omega
      have indexBound : n < args.length := by omega
      rw [List.range_succ, List.map_append]
      change BvlSem.evaluateTuple (((List.range n).map (fun i => Bvl.Exp.var (i + 1)) ++
        [.var (n + 1)]), original :: (args ++ rest), s) = _
      rw [BvlProps.evaluateAppend]
      simp only [BvlSem.evaluateTuple, ih boundN]
      have varRun : BvlSem.evaluate [.var (n + 1)] (original :: (args ++ rest)) s = (.val [args[n]], s) := by
        simp [BvlSem.evaluate, List.getElem?_append_left, indexBound]
      rw [varRun]
      simp only [List.take_append_getElem indexBound]
  simpa using shifted args.length (by omega)

/-- The completion stub reads its saved arguments in their stored order. -/
theorem evaluate_completion_savedArgs {C F : Type} (args saved : List BvlSem.Value)
    (original ptr arity : BvlSem.Value) (s : BvlSem.State C F) :
    BvlSem.evaluate ((List.range saved.length).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (args.length + 1)]))
      (original :: (args ++ [.block 31 (ptr :: arity :: original :: saved)])) s = (.val saved, s) := by
  have savedPrefix : ∀ n, n ≤ saved.length →
      BvlSem.evaluate ((List.range n).map (fun i => Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (args.length + 1)]))
        (original :: (args ++ [.block 31 (ptr :: arity :: original :: saved)])) s =
        (.val (saved.take n), s) := by
    intro n bound
    induction n with
    | zero => simp [BvlSem.evaluate]
    | succ n ih =>
      have boundN : n ≤ saved.length := by omega
      have indexBound : n < saved.length := by omega
      rw [List.range_succ, List.map_append]
      change BvlSem.evaluateTuple (((List.range n).map (fun i => Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (args.length + 1)]) ++
        [Bvl.Exp.op (.blockOp (.elemAt (n + 3))) [.var (args.length + 1)]]),
        original :: (args ++ [.block 31 (ptr :: arity :: original :: saved)]), s) = _
      rw [BvlProps.evaluateAppend]
      simp only [BvlSem.evaluateTuple, ih boundN]
      have elemRun : BvlSem.evaluate [Bvl.Exp.op (.blockOp (.elemAt (n + 3))) [.var (args.length + 1)]]
          (original :: (args ++ [.block 31 (ptr :: arity :: original :: saved)])) s = (.val [saved[n]], s) := by
        simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, indexBound]
      rw [elemRun]
      simp only [List.take_append_getElem indexBound]
  simpa using savedPrefix saved.length (by omega)

/-- The generated completion stub restores new and saved arguments in order,
then calls the original closure, charging the call tick. -/
theorem evaluate_partialAppClosureFn {C F : Type} (s : BvlSem.State C F)
    (total previous : Nat) (args saved : List BvlSem.Value) (stub originalPtr : Nat)
    (remaining : BvlSem.Value) (originalFields : List BvlSem.Value) (body : Bvl.Exp)
    (newCount : total - previous = args.length) (savedCount : previous + 1 = saved.length)
    (lookup : sptLookup originalPtr s.code = some (args.length + saved.length + 1, body)) :
    let original := BvlSem.Value.block 30 (.codePtr originalPtr :: originalFields)
    let partialValue := BvlSem.Value.block 31 (.codePtr stub :: remaining :: original :: saved)
    BvlSem.evaluate [generatePartialAppClosureFn total previous] (args ++ [partialValue]) s =
      if s.clock = 0 then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (args ++ saved ++ [original]) (BvlSem.decClock 1 s) := by
  let original := BvlSem.Value.block 30 (.codePtr originalPtr :: originalFields)
  let partialValue := BvlSem.Value.block 31 (.codePtr stub :: remaining :: original :: saved)
  let env := original :: (args ++ [partialValue])
  have originalRun : BvlSem.evaluate [.op (.blockOp (.elemAt 2)) [.var (total - previous)]]
      (args ++ [partialValue]) s = (.val [original], s) := by
    simp [newCount, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, partialValue]
  have newRun : BvlSem.evaluate ((List.range (total - previous)).map (fun i => Bvl.Exp.var (i + 1))) env s =
      (.val args, s) := by
    simpa [newCount, env] using evaluate_completion_newArgs args [partialValue] original s
  have savedRun : BvlSem.evaluate ((List.range (previous + 1)).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (total - previous + 1)])) env s =
      (.val saved, s) := by
    simpa [newCount, savedCount, env, partialValue] using
      evaluate_completion_savedArgs args saved original (.codePtr stub) remaining s
  have tailRun : BvlSem.evaluate [.var 0, .op (.blockOp (.elemAt 0)) [.var 0]] env s =
      (.val [original, .codePtr originalPtr], s) := by
    simp [env, original, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock]
  have savedAndTail : BvlSem.evaluate
      (((List.range (previous + 1)).map (fun i => Bvl.Exp.op (.blockOp (.elemAt (i + 3)))
        [.var (total - previous + 1)])) ++ [.var 0, .op (.blockOp (.elemAt 0)) [.var 0]]) env s =
      (.val (saved ++ [original, .codePtr originalPtr]), s) := by
    change BvlSem.evaluateTuple (_, env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, savedRun, tailRun]
  have allRun : BvlSem.evaluate
      (((List.range (total - previous)).map (fun i => Bvl.Exp.var (i + 1))) ++
       ((List.range (previous + 1)).map (fun i => Bvl.Exp.op (.blockOp (.elemAt (i + 3)))
         [.var (total - previous + 1)]) ++ [.var 0, .op (.blockOp (.elemAt 0)) [.var 0]])) env s =
      (.val (args ++ saved ++ [original, .codePtr originalPtr]), s) := by
    change BvlSem.evaluateTuple (_, env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, newRun, savedAndTail, List.append_assoc]
  change BvlSem.evaluate [.let [.op (.blockOp (.elemAt 2)) [.var (total - previous)]]
    (.call 0 none (((List.range (total - previous)).map (fun i => .var (i + 1))) ++
      ((List.range (previous + 1)).map (fun i => .op (.blockOp (.elemAt (i + 3)))
        [.var (total - previous + 1)])) ++ [.var 0, .op (.blockOp (.elemAt 0)) [.var 0]]))]
    (args ++ [partialValue]) s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, originalRun]
  dsimp only
  simp only [List.append_assoc, env] at allRun
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.append_assoc, List.singleton_append]
  rw [allRun]
  have lastPair (inst : Nonempty BvlSem.Value) (xs : List BvlSem.Value) (x y : BvlSem.Value) :
      @Flapjack.holLast BvlSem.Value inst (xs ++ [x, y]) = y := by
    induction xs with
    | nil => simp [Flapjack.holLast]
    | cons z zs ih => simp [Flapjack.holLast_cons, ih]
  simp [BvlSem.findCode, lookup, lastPair, ← List.append_assoc, original]

/-- A saturated call through an existing partial closure enters the original
body with both argument groups and the original closure in its environment. -/
theorem evaluate_mkClCall_partial_complete {C F : Type} (s : BvlSem.State C F)
    (total previous : Nat) (args saved rest : List BvlSem.Value) (stub originalPtr : Nat)
    (originalFields : List BvlSem.Value) (body : Bvl.Exp)
    (nonempty : args ≠ []) (newCount : total - previous = args.length)
    (savedCount : previous + 1 = saved.length)
    (stubLookup : sptLookup stub s.code = some (args.length + 1, generatePartialAppClosureFn total previous))
    (originalLookup : sptLookup originalPtr s.code = some (args.length + saved.length + 1, body)) :
    let original := BvlSem.Value.block 30 (.codePtr originalPtr :: originalFields)
    let partialValue := BvlSem.Value.block 31 (.codePtr stub :: .number (Int.ofNat (args.length - 1)) :: original :: saved)
    BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
      (args ++ [partialValue] ++ rest) s =
      if s.clock < args.length + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (args ++ saved ++ [original]) (BvlSem.decClock (args.length + 1) s) := by
  let original := BvlSem.Value.block 30 (.codePtr originalPtr :: originalFields)
  let partialValue := BvlSem.Value.block 31 (.codePtr stub :: .number (Int.ofNat (args.length - 1)) :: original :: saved)
  change BvlSem.evaluate [_] (args ++ [partialValue] ++ rest) s = _
  have callRun := evaluate_mkClCall_direct_env s args rest 31 stub (original :: saved)
    (generatePartialAppClosureFn total previous) nonempty stubLookup
  rw [callRun]
  by_cases timeout : s.clock < args.length
  · simp [timeout, show s.clock < args.length + 1 by omega]
  · simp only [timeout, ↓reduceIte]
    have lookupDec : sptLookup originalPtr (BvlSem.decClock args.length s).code =
        some (args.length + saved.length + 1, body) := by simpa [BvlSem.decClock] using originalLookup
    rw [evaluate_partialAppClosureFn (BvlSem.decClock args.length s) total previous args saved stub originalPtr
      (.number (Int.ofNat (args.length - 1))) originalFields body newCount savedCount lookupDec]
    have clockTest : (BvlSem.decClock args.length s).clock = 0 ↔ s.clock < args.length + 1 := by
      simp only [BvlSem.decClock]
      omega
    simp only [clockTest]
    split
    · simp [BvlSem.decClock]
    · have clocks : s.clock - args.length - 1 = s.clock - (args.length + 1) := by omega
      simp [BvlSem.decClock, clocks]

/-- Saturating an ordinary partial closure selects its body with the new
arguments before the previously saved arguments. -/
theorem destClosure_ordinary_partial_exact (maxApp ptr arity : Nat)
    (captured oldArgs newArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (oldBound : oldArgs.length < arity) (bound : newArgs.length ≤ maxApp)
    (length : newArgs.length + oldArgs.length = arity) :
    ClosSem.destClosure maxApp none (.closure (some ptr) oldArgs captured arity body) newArgs =
      some (.fullApp body (newArgs ++ oldArgs ++ captured) []) := by
  have take : newArgs.reverse.take (arity - oldArgs.length) = newArgs.reverse := by
    apply List.take_of_length_le
    simp only [List.length_reverse]
    omega
  have drop : newArgs.reverse.drop (arity - oldArgs.length) = [] := by
    apply List.drop_eq_nil_of_le
    simp only [List.length_reverse]
    omega
  simp [ClosSem.destClosure, ClosSem.checkLoc, bound, oldBound, length, take, drop, List.append_assoc]

/-- A saturated ordinary partial closure runs its body or times out after
charging one source tick per newly supplied argument. -/
theorem evaluateApp_ordinary_partial_exact {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : newArgs ≠ []) (oldBound : oldArgs.length < arity)
    (bound : newArgs.length ≤ s.maxApp) (length : newArgs.length + oldArgs.length = arity) :
    ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s =
      if s.clock < newArgs.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else
        let next := ClosSem.fixClock (ClosSem.decClock newArgs.length s)
          (ClosSem.evaluate [body] (newArgs ++ oldArgs ++ captured) (ClosSem.decClock newArgs.length s))
        match next.1 with
        | .val [value] => (.val [value], next.2)
        | other => (other, next.2) := by
  have found := destClosure_ordinary_partial_exact s.maxApp ptr arity captured oldArgs newArgs body oldBound bound length
  cases newArgs with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, found]
    simp [ClosSem.evaluateApp]
    split <;> rfl

/-- The completion stub enters an ordinary closure's compiled body with both
argument groups and captured values, after the target's additional call tick. -/
theorem evaluate_partialComplete_ordinary_entry {C F : Type} (s : BvlSem.State C F)
    (maxApp ptr arity : Nat) (fs : Nat → Prop) (captured : List ClosSem.Value) (fields newArgs saved rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp fs s.refs s.code
      (captured, fields) (.closure (some ptr) [] captured arity sourceBody) target)
    (fieldsLength : fields.length = captured.length) (nonempty : newArgs ≠ []) (savedNonempty : saved ≠ [])
    (length : newArgs.length + saved.length = arity)
    (stubLookup : sptLookup (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) s.code =
      some (newArgs.length + 1, generatePartialAppClosureFn (arity - 1) (saved.length - 1))) :
    ∃ aux targetBody finalAux,
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      sptLookup (ptr + numStubs maxApp) s.code = some (arity + 1,
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) ∧
      BvlSem.evaluate [mkClCall (.var newArgs.length) ((List.range newArgs.length).map Bvl.Exp.var)]
        (newArgs ++ [.block 31 (.codePtr (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) ::
          .number (Int.ofNat (newArgs.length - 1)) :: target :: saved)] ++ rest) s =
        if s.clock < newArgs.length + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          (((newArgs ++ saved) ++ fields) ++ (newArgs ++ saved) ++ [target])
          (BvlSem.decClock (newArgs.length + 1) s) := by
  cases related with
  | closure bound positive locations vars compiled installed lookup =>
    have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
    have savedPositive : 0 < saved.length := List.length_pos_iff.mpr savedNonempty
    have newCount : arity - 1 - (saved.length - 1) = newArgs.length := by omega
    have savedCount : saved.length - 1 + 1 = saved.length := by omega
    refine ⟨_, _, _, compiled, installed, lookup, ?_⟩
    have callRun := evaluate_mkClCall_partial_complete s (arity - 1) (saved.length - 1) newArgs saved rest
      (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) (ptr + numStubs maxApp)
      (.number (Int.ofNat (arity - 1)) :: fields) _ nonempty newCount savedCount stubLookup
      (by simpa [length] using lookup)
    rw [callRun]
    split
    · rfl
    · rw [← fieldsLength, ← length]
      simpa [List.length_append, List.append_assoc, ← length] using
        evaluate_closure_entry (BvlSem.decClock (newArgs.length + 1) s) (newArgs ++ saved) fields 30
          (.codePtr (ptr + numStubs maxApp)) (.number (Int.ofNat (arity - 1))) _

/-- When the source has enough clock, completing an ordinary partial closure
simulates its body using the target completion stub and closure entry. -/
theorem evaluatePost_ordinary_partial_exact {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ ClosProps.everyFnLocationSome [body] ∧ ClosProps.everyFnVarsSome [body] := by
    cases related with | closure bound _ locations vars _ _ _ => exact ⟨bound, locations, vars⟩
  obtain ⟨arityBound, locations, vars⟩ := info
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have targetLength : newTargets.length + oldTargets.length = arity := by omega
  have targetNewNonempty : newTargets ≠ [] := by simp only [← List.length_pos_iff, newLength]; exact newPositive
  have targetOldNonempty : oldTargets ≠ [] := by simp only [← List.length_pos_iff, oldLength]; exact oldPositive
  have totalBound : arity - 1 < s.maxApp := by omega
  have prevBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) t.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨totalBound, prevBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = newTargets.length + 1 := by omega
    simpa [count] using installed
  obtain ⟨aux, targetBody, finalAux, compiled, installed, sourceLookup, _⟩ :=
    evaluate_partialComplete_ordinary_entry t s.maxApp ptr arity _ captured fields newTargets oldTargets rest
      body original related envRel'.length_eq.symm targetNewNonempty targetOldNonempty targetLength stubLookup
  have bodyStates : stateRel f (ClosSem.decClock newArgs.length s) t := by
    exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code (newArgs ++ oldArgs ++ captured)
      (((newTargets ++ oldTargets) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) := by
    have tail : envRel s.maxApp f t.refs t.code captured (fields ++ (newTargets ++ oldTargets) ++ [original]) := by
      simpa using envRel_prepend envRel' (env := []) (targetEnv := (newTargets ++ oldTargets) ++ [original]) (by simp [envRel])
    simpa [List.append_assoc] using envRel_prepend (List.rel_append newRel oldRel) tail
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ captured)
    (((newTargets ++ oldTargets) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + (clock + 1) }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original := by simpa [start] using related
  have shiftedLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    simpa [start] using stubLookup
  obtain ⟨aux2, targetBody2, finalAux2, compiled2, _, lookup2, callRun⟩ :=
    evaluate_partialComplete_ordinary_entry start s.maxApp ptr arity _ captured fields newTargets oldTargets rest
      body original shiftedRelated envRel'.length_eq.symm targetNewNonempty targetOldNonempty targetLength shiftedLookup
  have targetEq : targetBody2 = targetBody := by
    have same := sourceLookup.symm.trans lookup2
    cases same
    rfl
  subst targetBody2
  have enoughTarget : ¬ start.clock < newTargets.length + 1 := by dsimp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have clockEq : s.clock + (clock + 1) - (newTargets.length + 1) = s.clock - newArgs.length + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)]
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) start = (targetResult, tFinal) := by
    rw [callRun]
    simpa [start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock + 1, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- With enough source clock, saturating an ordinary partial closure produces
the result of its selected body. -/
theorem evaluateApp_ordinary_partial_exact_body {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value) (body : ClosLang.Exp)
    (nonempty : newArgs ≠ []) (oldBound : oldArgs.length < arity)
    (bound : newArgs.length ≤ s.maxApp) (length : newArgs.length + oldArgs.length = arity)
    (enough : newArgs.length ≤ s.clock) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) :
    ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal) := by
  rw [evaluateApp_ordinary_partial_exact s ptr arity captured oldArgs newArgs body nonempty oldBound bound length]
  rw [if_neg (Nat.not_lt.mpr enough), ClosSem.fixClock_evaluate, bodyRun]
  cases result with
  | err error => rfl
  | val values => cases values with
    | nil => rfl
    | cons value tail => cases tail <;> rfl

/-- The source application and generated target call agree for a saturated
ordinary partial closure when the source has enough clock. -/
theorem evaluateApp_ordinary_partial_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := by cases related with | closure bound _ _ _ _ _ _ => exact bound
  have positive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ captured) (ClosSem.decClock newArgs.length s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_ordinary_partial_exact_body s bodyFinal ptr arity captured oldArgs newArgs body
      nonempty oldBound bound length enough bodyResult bodyRun
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_ordinary_partial_exact s sFinal t f ptr arity captured oldArgs newArgs fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel oldNonempty nonempty length enough result bodyRun noType bodyIH

end Flapjack.Compiler.Backend.ClosToBvl
