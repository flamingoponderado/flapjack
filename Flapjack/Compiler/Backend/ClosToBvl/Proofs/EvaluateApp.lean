module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.DirectApplication
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureShape
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.RecursiveEntry
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreeLet
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SavedSelectors
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialCodeDomain
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureArgumentRelation
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateCall
public import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList
public import Flapjack.Compiler.Backend.BvlJump.Proofs

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.ClosToBvl.Stubs
@[expose] public section

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

namespace AppHelperCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end AppHelperCarrier

/-- A non-value argument result propagates through the compiled application. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_app_helper"
  (fmap_as_finite_support := [refs])]
theorem evaluateAppHelper {C F : Type} (s next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (location : Option Nat)
    (args : List Bvl.Exp) (function : Bvl.Exp) (result : Result (List BvlSem.Value) BvlSem.Value)
    (premises : (∀ x, result ≠ .val x) ∧ BvlSem.evaluate args env s = (result, next)) :
    BvlSem.evaluate [appTarget maxApp location args function] env s = (result, next) := by
  rcases premises with ⟨nonvalue, run⟩
  cases result with
  | val values => exact False.elim (nonvalue values rfl)
  | err error =>
    have appended : BvlSem.evaluate (args ++ [function]) env s = (.err error, next) := by
      change BvlSem.evaluateTuple (args ++ [function], env, s) = _
      rw [BvlProps.evaluateAppend]
      simp [BvlSem.evaluateTuple, run]
    cases location <;> simp only [appTarget] <;>
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, appended]

/-- A non-value function result propagates after successful argument evaluation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "evaluate_app_helper2"
  (fmap_as_finite_support := [refs])]
theorem evaluateAppHelper2 {C F : Type} (s middle next : Flapjack.Compiler.Backend.BvlSem.State C F)
    (env : List BvlSem.Value) (maxApp : Nat) (location : Option Nat)
    (args : List Bvl.Exp) (function : Bvl.Exp) (values : List BvlSem.Value)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (premises : (∀ x, result ≠ .val x) ∧ BvlSem.evaluate args env s = (.val values, middle) ∧
      BvlSem.evaluate [function] env middle = (result, next)) :
    BvlSem.evaluate [appTarget maxApp location args function] env s = (result, next) := by
  rcases premises with ⟨nonvalue, argsRun, functionRun⟩
  cases result with
  | val values => exact False.elim (nonvalue values rfl)
  | err error =>
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
      evaluateAppHelper _ _ _ _ _ _ _ _ ⟨by simp, run⟩, related, states, map, frame, annotations, clocks⟩

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
        HolFiniteMapExact.submap_trans map1 map2, unmappedRefsSubmap_trans frame1 frame2, annotations2, clocks2⟩
      · exact evaluateAppHelper2 _ _ _ _ _ _ _ _ _ _ ⟨by simp, runArgs, run2⟩
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
    simpa [env, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env values.length s bound
  have argsNonempty : (List.range values.length).map Bvl.Exp.var ≠ [] := by
    simpa using nonempty
  have h := evaluate_mkClCall_direct s env (.var values.length) ((List.range values.length).map Bvl.Exp.var)
    values tag ptr fields body (by simpa [closure] using clRun) argsRun argsNonempty lookup
  simpa [env, closure] using h

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
    simpa [env, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env args.length s bound
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [.block tag (code :: arity :: fields)], s) := by
    simp [BvlSem.evaluate, env]
  have freeRun : BvlSem.evaluate (freeLet (.var args.length) fields.length) env s = (.val fields, s) := by
    simpa using bEval_freeLet_block fields (.var args.length) env s tag code arity clRun
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
    have sourceNonempty : sourceArgs ≠ [] := by
      intro empty
      simp [empty] at arityMatch
      exact positive arityMatch.symm
    have sourceStep := evaluateApp_ordinary_partial_exact_body s bodyFinal ptr arity sourceEnv [] sourceArgs sourceBody
      sourceNonempty (by simpa using Nat.pos_of_ne_zero positive) (by simpa [arityMatch] using bound)
      (by simpa using arityMatch) (by simpa [arityMatch] using enough) bodyResult
      (by simpa [arityMatch] using bodyRun)
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
  have found := destClosure_ordinary_partial_exact s.maxApp ptr arity sourceEnv [] sourceArgs sourceBody
    (by simpa using Nat.pos_of_ne_zero positive) (by simpa [arityMatch] using bound) (by simpa using arityMatch)
  simp only [List.append_nil] at found
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
          HolFiniteMapExact.submap_trans (HolFiniteMapExact.submap_trans map1 map2) map3,
          unmappedRefsSubmap_trans (unmappedRefsSubmap_trans frame1 frame2) frame3, annotations3, clocks3⟩
        · rw [evaluate_appTarget_generic _ _ _ _ _ _ _ _ _ runArgs runFunction]
          simpa [targetLength] using targetCallRun
        · simpa [maxFunction, maxArgs] using related

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
    simpa [env, List.take_of_length_le, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env (args.length + 1) s bound
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env]
  have freeRun : BvlSem.evaluate (freeLet (.var args.length) fields.length) env s = (.val fields, s) := by
    simpa [closure] using bEval_freeLet_block fields (.var args.length) env s tag code arity
      (by simpa [closure] using clRun)
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

/-- A saturated recursive closure selects its body with all newly supplied
and saved arguments followed by the recursive group and captured environment. -/
theorem destClosure_recclosure_exact (maxApp ptr arity index : Nat)
    (captured oldArgs newArgs : List ClosSem.Value) (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) (oldBound : oldArgs.length < arity)
    (bound : newArgs.length ≤ maxApp) (length : newArgs.length + oldArgs.length = arity) :
    ClosSem.destClosure maxApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs =
      some (.fullApp body (newArgs ++ oldArgs ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured) []) := by
  have take : newArgs.reverse.take (arity - oldArgs.length) = newArgs.reverse := by
    apply List.take_of_length_le
    simp only [List.length_reverse]
    omega
  have drop : newArgs.reverse.drop (arity - oldArgs.length) = [] := by
    apply List.drop_eq_nil_of_le
    simp only [List.length_reverse]
    omega
  simp [ClosSem.destClosure, found, ClosSem.checkLoc, bound, oldBound, length, take, drop, List.append_assoc]

/-- A saturated recursive closure either times out or evaluates the selected
body with the whole recursive group in its environment. -/
theorem evaluateApp_recclosure_exact {C F : Type} (s : ClosSem.State C F)
    (ptr arity index : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) (nonempty : newArgs ≠ [])
    (oldBound : oldArgs.length < arity) (bound : newArgs.length ≤ s.maxApp)
    (length : newArgs.length + oldArgs.length = arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s =
      if s.clock < newArgs.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else
        let next := ClosSem.fixClock (ClosSem.decClock newArgs.length s)
          (ClosSem.evaluate [body] (newArgs ++ oldArgs ++
            (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
            (ClosSem.decClock newArgs.length s))
        match next.1 with
        | .val [value] => (.val [value], next.2)
        | other => (other, next.2) := by
  have selected := destClosure_recclosure_exact s.maxApp ptr arity index captured oldArgs newArgs functions body
    found oldBound bound length
  cases newArgs with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, selected]
    simp [ClosSem.evaluateApp]
    split <;> rfl

/-- A saturated recursive partial closure returns its selected body result when its clock suffices. -/
theorem evaluateApp_recclosure_partial_exact_body {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr index arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body))
    (nonempty : newArgs ≠ []) (oldBound : oldArgs.length < arity)
    (bound : newArgs.length ≤ s.maxApp) (length : newArgs.length + oldArgs.length = arity)
    (enough : newArgs.length ≤ s.clock) (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) :
    ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal) := by
  rw [evaluateApp_recclosure_exact s ptr arity index captured oldArgs newArgs functions body found nonempty oldBound bound length]
  rw [if_neg (Nat.not_lt.mpr enough), ClosSem.fixClock_evaluate, bodyRun]
  cases result with
  | err error => rfl
  | val values => cases values with
    | nil => rfl
    | cons value tail => cases tail <;> rfl

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
    have sourceNonempty : sourceArgs ≠ [] := by
      intro empty
      simp [empty] at arityMatch
      exact positive arityMatch.symm
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr 0 arity sourceEnv [] sourceArgs
      [(arity, sourceBody)] sourceBody (by simp) sourceNonempty (by simpa using Nat.pos_of_ne_zero positive)
      (by simpa [arityMatch] using bound) (by simpa using arityMatch)
      (by simpa [arityMatch] using enough) bodyResult (by simpa [arityMatch] using bodyRun)
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
  have found := destClosure_recclosure_exact s.maxApp ptr arity 0 sourceEnv [] sourceArgs [(arity, sourceBody)] sourceBody
    (by simp) (by simpa using Nat.pos_of_ne_zero positive)
    (by simpa [arityMatch] using bound) (by simpa using arityMatch)
  simp only [List.length_singleton, List.range_one, List.map_cons, List.map_nil, List.append_nil] at found
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


/-- A recursive closure relation uses the closure's captured environment. -/
theorem clRel_recclosure_env {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {env captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index : Nat}
    {functions : List (Nat × ClosLang.Exp)} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (env, fields) (.recclosure (some ptr) [] captured functions index) target) :
    env = captured := by
  cases related <;> rfl

/-- A recursive closure with no saved arguments is represented directly,
with its captured environment related to the target environment. -/
theorem vRel_recclosure_original {maxApp ptr index : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {functions : List (Nat × ClosLang.Exp)} {target : BvlSem.Value}
    (related : vRel maxApp f refs code (.recclosure (some ptr) [] captured functions index) target) :
    ∃ fields, List.Forall₂ (vRel maxApp f refs code) captured fields ∧
      clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (captured, fields)
        (.recclosure (some ptr) [] captured functions index) target := by
  cases related with
  | @closure env fvs cl p n ys envRel closure =>
    have envEq : env = captured := clRel_recclosure_env closure
    subst env
    exact ⟨fvs, envRel, closure⟩
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
  obtain ⟨fields, envRelated, closure⟩ := vRel_recclosure_original functionRel
  exact evaluateApp_singletonRec_exact_all s sFinal t f ptr arity sourceEnv sourceArgs fields targetArgs rest
    sourceBody targetClosure states annotations closure envRelated argsRelated arityMatch result appRun noType bodyIH

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
  exact triangleTableSize count (fun total previous =>
    BvlSem.Value.codePtr (partialAppFnLocation maxApp total previous))

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
theorem evaluate_mkTick {C F : Type} (n : Nat) (body : Bvl.Exp)
    (env : List BvlSem.Value) (s : BvlSem.State C F) :
    BvlSem.evaluate [Bvl.mkTick n body] env s =
      if s.clock < n then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] env (BvlSem.decClock n s) := by
  induction n generalizing s with
  | zero =>
    change BvlSem.evaluate [body] env s = BvlSem.evaluate [body] env (BvlSem.decClock 0 s)
    cases s
    rfl
  | succ n ih =>
    change BvlSem.evaluate [.tick (Bvl.mkTick n body)] env s = _
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
    stripGenericAppTicks n (Bvl.mkTick n body) = body := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change stripGenericAppTicks n (Bvl.mkTick n body) = body
    exact ih

/-- The partial branch consists of its arity-dependent ticks followed by the
closure-tag choice. -/
theorem genericAppPartialBranch_ticks (maxApp n : Nat) :
    genericAppPartialBranch maxApp n = Bvl.mkTick n (genericAppPartialChoice maxApp n) := by
  unfold genericAppPartialChoice genericAppPartialBranch generateGenericApp
  change Bvl.mkTick n _ = Bvl.mkTick n (stripGenericAppTicks n (Bvl.mkTick n _))
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
    genericAppPartialBranch_ticks, evaluate_mkTick]

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
    change ∃ normal other, stripGenericAppTicks n (Bvl.mkTick n
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

/-- The normal partial-application branch constructs a block from the table
pointer, remaining arity, original closure and saved arguments. -/
theorem genericAppPartialNormal_shape (maxApp n : Nat) :
    genericAppPartialNormal maxApp n = .op (.blockOp (.cons 31))
      ((mkEl (.op (.globOp (.global 0)) [])
          (partialAppFnLocationCode maxApp (.op (.blockOp (.elemAt 1)) [.var (n + 2)]) (mkConst n)) ::
        .var 0 :: .var (n + 2) :: (List.range (n + 1)).map (fun i => .var (i + 1))).reverse) := by
  unfold genericAppPartialNormal genericAppPartialChoice genericAppPartialBranch generateGenericApp
  change (match stripGenericAppTicks n (Bvl.mkTick n
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
    have bound : (n + 1) + 1 ≤ env.length := by simp [env, length]
    simpa [env, ← length, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVarsRev 1 env (n + 1) s bound
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
    simpa [env, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env args.length s bound
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
  have sourceRun := evaluateApp_ordinary_partial_again s ptr arity captured [] args body nonempty argsBound
    (by simpa using partialBound)
  simp only [List.append_nil] at sourceRun
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
    change ∃ normal body, stripGenericAppTicks n (Bvl.mkTick n
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
  change (match (match stripGenericAppTicks n (Bvl.mkTick n
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
    have bound : (n + 1) + 2 ≤ env.length := by simp [env, length]
    simpa [env, ← length, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVarsRev 2 env (n + 1) s bound
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
    simpa [env, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env args.length s envBound
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

/-- A related recursive partial closure exposes its original closure relation
and pointwise related saved arguments, for any recursive group. -/
theorem vRel_recclosure_partial_existing {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured oldArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (found : functions[index]? = some (arity, body)) (nonempty : oldArgs ≠ [])
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured functions index) target) :
    ∃ fields oldTargets original,
      target = .block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: original :: oldTargets) ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets ∧
      clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
        (captured, fields) (.recclosure (some ptr) [] captured functions index) original := by
  have indexBound : index < functions.length := List.getElem?_eq_some_iff.mp found |>.1
  have entryEq : functions[index] = (arity, body) := by simpa [List.getElem?_eq_getElem indexBound] using found
  cases related with
  | closure envRel closure =>
    have empty : oldArgs = [] := by
      simpa [getOldArgs] using (clRel_dest _ _ _ _ _ _ _ _ closure).1
    exact (nonempty empty).elim
  | @partialClosure env fvs argEnv ys numArgs cl clApp cl' envRel argRel argsNonempty argsBound installed added arityEq closure =>
    cases cl <;> simp [addArgs] at added
    case recclosure loc supplied captured' functions' index' =>
      obtain ⟨rfl, argsEq, rfl, rfl, rfl⟩ := added
      have suppliedEmpty : supplied = [] := by
        simpa [getOldArgs] using (clRel_dest _ _ _ _ _ _ _ _ closure).1
      subst supplied
      simp only [List.append_nil] at argsEq
      subst oldArgs
      simp [getNumArgs, Flapjack.holEl_eq_getElem index' functions' indexBound, entryEq] at arityEq
      subst numArgs
      have capturedEq : env = captured' := by cases closure <;> rfl
      subst env
      exact ⟨fvs, ys, cl', rfl, envRel, argRel, closure⟩

/-- The generated completion stub restores new and saved arguments in order,
then calls the original closure, charging the call tick. -/
theorem evaluate_partialAppClosureFn {C F : Type} (s : BvlSem.State C F)
    (total previous : Nat) (args saved : List BvlSem.Value) (stub : BvlSem.Value) (originalPtr tag originalTag : Nat)
    (remaining : BvlSem.Value) (originalFields : List BvlSem.Value) (body : Bvl.Exp)
    (newCount : total - previous = args.length) (savedCount : previous + 1 = saved.length)
    (lookup : sptLookup originalPtr s.code = some (args.length + saved.length + 1, body)) :
    let original := BvlSem.Value.block originalTag (.codePtr originalPtr :: originalFields)
    let partialValue := BvlSem.Value.block tag (stub :: remaining :: original :: saved)
    BvlSem.evaluate [generatePartialAppClosureFn total previous] (args ++ [partialValue]) s =
      if s.clock = 0 then (.err (.abort .timeoutError), { s with clock := 0 })
      else BvlSem.evaluate [body] (args ++ saved ++ [original]) (BvlSem.decClock 1 s) := by
  let original := BvlSem.Value.block originalTag (.codePtr originalPtr :: originalFields)
  let partialValue := BvlSem.Value.block tag (stub :: remaining :: original :: saved)
  let env := original :: (args ++ [partialValue])
  have originalRun : BvlSem.evaluate [.op (.blockOp (.elemAt 2)) [.var (total - previous)]]
      (args ++ [partialValue]) s = (.val [original], s) := by
    simp [newCount, BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, partialValue]
  have newRun : BvlSem.evaluate ((List.range (total - previous)).map (fun i => Bvl.Exp.var (i + 1))) env s =
      (.val args, s) := by
    have bound : args.length + 1 ≤ env.length := by simp [env]
    simpa [newCount, env, BvlSem.evaluateTuple] using
      BvlProps.evaluateGenlistVars 1 env args.length s bound
  have savedRun : BvlSem.evaluate ((List.range (previous + 1)).map (fun i =>
      Bvl.Exp.op (.blockOp (.elemAt (i + 3))) [.var (total - previous + 1)])) env s =
      (.val saved, s) := by
    simpa [newCount, savedCount, env, partialValue] using
      evaluateGenlistPrevArgs1NoRev saved original tag stub remaining original args s
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
    rw [evaluate_partialAppClosureFn (BvlSem.decClock args.length s) total previous args saved (.codePtr stub) originalPtr 31 30
      (.number (Int.ofNat (args.length - 1))) originalFields body newCount savedCount lookupDec]
    have clockTest : (BvlSem.decClock args.length s).clock = 0 ↔ s.clock < args.length + 1 := by
      simp only [BvlSem.decClock]
      omega
    simp only [clockTest]
    split
    · simp [BvlSem.decClock]
    · have clocks : s.clock - args.length - 1 = s.clock - (args.length + 1) := by omega
      simp [BvlSem.decClock, clocks]

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

/-- Length and stub bookkeeping shared by the partial-application completion
cases: the target argument groups have the source lengths and positivity, both
are nonempty, and the completion stub is installed. Flapjack infrastructure;
no separately named HOL original. -/
private theorem partialAppEntryFacts {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (arity : Nat)
    (oldArgs newArgs : List ClosSem.Value) (oldTargets newTargets : List BvlSem.Value)
    (states : stateRel f s t) (arityBound : arity ≤ s.maxApp)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) :
    oldTargets.length = oldArgs.length ∧ newTargets.length = newArgs.length ∧
      0 < oldArgs.length ∧ 0 < newArgs.length ∧
      newTargets.length + oldTargets.length = arity ∧
      newTargets ≠ [] ∧ oldTargets ≠ [] ∧
      sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) t.code =
        some (newTargets.length + 1,
          generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have targetLength : newTargets.length + oldTargets.length = arity := by omega
  have targetNewNonempty : newTargets ≠ [] := by
    simp only [← List.length_pos_iff, newLength]; exact newPositive
  have targetOldNonempty : oldTargets ≠ [] := by
    simp only [← List.length_pos_iff, oldLength]; exact oldPositive
  have totalBound : arity - 1 < s.maxApp := by omega
  have prevBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup :
      sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) t.code =
        some (newTargets.length + 1,
          generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1)
      ⟨totalBound, prevBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = newTargets.length + 1 := by omega
    simpa [count] using installed
  exact ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩

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
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
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

/-- A saturated ordinary partial closure times out on both sides when the
source clock is insufficient. -/
theorem evaluateApp_ordinary_partial_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (timeout : s.clock < newArgs.length) :
    ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := by cases related with | closure bound _ _ _ _ _ _ => exact bound
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  have sourceTimeout : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_ordinary_partial_exact s ptr arity captured oldArgs newArgs body nonempty oldBound bound length]
    simp [timeout]
  have targetNonempty : newTargets ≠ [] := by simp only [← List.length_pos_iff, newLength]; exact newPositive
  have totalBound : arity - 1 < s.maxApp := by omega
  have prevBound : oldTargets.length - 1 < arity - 1 := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1)
      ⟨totalBound, prevBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = newTargets.length + 1 := by omega
    simpa [start, count] using installed
  have targetRun := evaluate_mkClCall_direct_env start newTargets rest 31
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) (original :: oldTargets)
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) targetNonempty stubLookup
  have targetTimeout : start.clock < newTargets.length := by dsimp [start]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- Saturating a related ordinary partial closure simulates both successful
body evaluation and timeout, using the body induction hypothesis. -/
theorem evaluateApp_ordinary_partial_exact_related {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) oldArgs captured arity body) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨oldTargets, original, targetEq, originalRel, oldRel⟩ :=
    vRel_ordinary_partial_existing s t f ptr arity captured oldArgs body target oldNonempty related
  obtain ⟨fields, envRel', closure⟩ := vRel_ordinary_closure originalRel
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_ordinary_partial_exact_simulation s sFinal t f ptr arity captured oldArgs newArgs
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      oldNonempty nonempty length enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_partial_exact_timeout s t f ptr arity
      captured oldArgs newArgs fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- The completion stub enters a singleton recursive closure's compiled body with both
argument groups and captured values, after the target's additional call tick. -/
theorem evaluate_partialComplete_singletonRec_entry {C F : Type} (s : BvlSem.State C F)
    (maxApp ptr arity : Nat) (fs : Nat → Prop) (captured : List ClosSem.Value) (fields newArgs saved rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp fs s.refs s.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, sourceBody)] 0) target)
    (fieldsLength : fields.length = captured.length) (nonempty : newArgs ≠ []) (savedNonempty : saved ≠ [])
    (length : newArgs.length + saved.length = arity)
    (stubLookup : sptLookup (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) s.code =
      some (newArgs.length + 1, generatePartialAppClosureFn (arity - 1) (saved.length - 1))) :
    ∃ aux targetBody finalAux,
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      sptLookup (ptr + numStubs maxApp) s.code = some (arity + 1,
        .let ((List.range (arity + 1)).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) ∧
      BvlSem.evaluate [mkClCall (.var newArgs.length) ((List.range newArgs.length).map Bvl.Exp.var)]
        (newArgs ++ [.block 31 (.codePtr (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) ::
          .number (Int.ofNat (newArgs.length - 1)) :: target :: saved)] ++ rest) s =
        if s.clock < newArgs.length + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          (((newArgs ++ saved ++ [target]) ++ fields) ++ (newArgs ++ saved) ++ [target])
          (BvlSem.decClock (newArgs.length + 1) s) := by
  cases related with
  | singletonRec bound positive locations vars compiled installed lookup =>
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
        evaluate_singletonRec_entry (BvlSem.decClock (newArgs.length + 1) s) (newArgs ++ saved) fields 30
          (.codePtr (ptr + numStubs maxApp)) (.number (Int.ofNat (arity - 1))) _
  | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible

/-- When the source has enough clock, completing a singleton recursive partial closure
simulates its body using the target completion stub and closure entry. -/
theorem evaluatePost_singletonRec_partial_exact {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ ClosProps.everyFnLocationSome [body] ∧ ClosProps.everyFnVarsSome [body] := by
    cases related with
    | singletonRec bound _ locations vars _ _ _ => exact ⟨bound, locations, vars⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  obtain ⟨arityBound, locations, vars⟩ := info
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
  obtain ⟨aux, targetBody, finalAux, compiled, installed, sourceLookup, _⟩ :=
    evaluate_partialComplete_singletonRec_entry t s.maxApp ptr arity _ captured fields newTargets oldTargets rest
      body original related envRel'.length_eq.symm targetNewNonempty targetOldNonempty targetLength stubLookup
  have bodyStates : stateRel f (ClosSem.decClock newArgs.length s) t := by
    exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr states
  have selfRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured [(arity, body)] 0) original := by
    cases related with
    | singletonRec bound positive loc vars compiled installed lookup =>
      exact .closure envRel' (.singletonRec bound positive loc vars compiled installed lookup)
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have bodyEnv : envRel s.maxApp f t.refs t.code (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured)
      (((newTargets ++ oldTargets ++ [original]) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) := by
    have tail : envRel s.maxApp f t.refs t.code
        (.recclosure (some ptr) [] captured [(arity, body)] 0 :: captured)
        (original :: fields ++ (newTargets ++ oldTargets) ++ [original]) := by
      refine ⟨selfRel, ?_⟩
      simpa using envRel_prepend envRel' (env := []) (targetEnv := (newTargets ++ oldTargets) ++ [original]) (by simp [envRel])
    simpa [List.append_assoc] using envRel_prepend (List.rel_append newRel oldRel) tail
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured)
    (((newTargets ++ oldTargets ++ [original]) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + (clock + 1) }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original := by simpa [start] using related
  have shiftedLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    simpa [start] using stubLookup
  obtain ⟨aux2, targetBody2, finalAux2, compiled2, _, lookup2, callRun⟩ :=
    evaluate_partialComplete_singletonRec_entry start s.maxApp ptr arity _ captured fields newTargets oldTargets rest
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

/-- The source application and generated target call agree for a saturated
singleton recursive partial closure when the source has enough clock. -/
theorem evaluateApp_singletonRec_partial_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := by cases related with
    | singletonRec bound _ _ _ _ _ _ => exact bound
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have positive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured) (ClosSem.decClock newArgs.length s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr 0 arity captured oldArgs newArgs
      [(arity, body)] body (by simp) nonempty oldBound bound length enough bodyResult (by simpa using bodyRun)
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_singletonRec_partial_exact s sFinal t f ptr arity captured oldArgs newArgs fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel oldNonempty nonempty length enough result bodyRun noType bodyIH

/-- A saturated singleton recursive partial closure times out on both sides when the
source clock is insufficient. -/
theorem evaluateApp_singletonRec_partial_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (timeout : s.clock < newArgs.length) :
    ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := by cases related with
    | singletonRec bound _ _ _ _ _ _ => exact bound
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_recclosure_exact s ptr arity 0 captured oldArgs newArgs [(arity, body)] body
      (by simp) nonempty oldBound bound length]
    simp only [List.length_singleton, List.range_one, List.map_cons, List.map_nil]
    simp [timeout]
  have targetNonempty : newTargets ≠ [] := by simp only [← List.length_pos_iff, newLength]; exact newPositive
  have totalBound : arity - 1 < s.maxApp := by omega
  have prevBound : oldTargets.length - 1 < arity - 1 := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1)
      ⟨totalBound, prevBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = newTargets.length + 1 := by omega
    simpa [start, count] using installed
  have targetRun := evaluate_mkClCall_direct_env start newTargets rest 31
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) (original :: oldTargets)
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) targetNonempty stubLookup
  have targetTimeout : start.clock < newTargets.length := by dsimp [start]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- Saturating a related singleton recursive partial closure simulates both successful
body evaluation and timeout, using the body induction hypothesis. -/
theorem evaluateApp_singletonRec_partial_exact_related {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, targetEq, envRel', oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity 0 captured oldArgs [(arity, body)] body target
      (by simp) oldNonempty related
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_singletonRec_partial_exact_simulation s sFinal t f ptr arity captured oldArgs newArgs
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      oldNonempty nonempty length enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_singletonRec_partial_exact_timeout s t f ptr arity
      captured oldArgs newArgs fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Every selected function in a related recursive closure has a valid
application arity, including functions in mutually recursive groups. -/
theorem clRel_recclosure_arity {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr : Nat}
    {functions : List (Nat × ClosLang.Exp)} {index arity : Nat} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) : arity ≤ maxApp ∧ arity ≠ 0 := by
  cases related with
  | singletonRec bound positive _ _ _ _ _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨bound, positive⟩
  | mutualRec exps ps positions values fresh stored many indexBound locations vars installed =>
    have member : (arity, body) ∈ functions := List.mem_of_getElem? found
    rw [exps] at member
    obtain ⟨entry, entryMember, entryEq⟩ := List.mem_map.mp member
    cases entry with
    | mk function label =>
      change function = (arity, body) at entryEq
      subst function
      exact ⟨(installed _ entryMember).1, (installed _ entryMember).2.1⟩

/-- Undersaturated recursive closure application saves arguments or times out
after one source tick per newly supplied argument. -/
theorem evaluateApp_recclosure_partial {C F : Type} (s : ClosSem.State C F)
    (ptr arity index : Nat) (captured supplied args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ [])
    (bound : args.length ≤ s.maxApp) (partialBound : args.length + supplied.length < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) supplied captured functions index) args s =
      if s.clock < args.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else (.val [.recclosure (some ptr) (args ++ supplied) captured functions index],
        ClosSem.decClock args.length s) := by
  have oldBound : supplied.length < arity := by omega
  have selected : ClosSem.destClosure s.maxApp none
      (.recclosure (some ptr) supplied captured functions index) args =
      some (.partialApp (.recclosure (some ptr) (args ++ supplied) captured functions index)) := by
    simp [ClosSem.destClosure, found, ClosSem.checkLoc, bound, oldBound, partialBound]
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, selected]
    simp

/-- Repeated partial application of a recursive closure preserves the simulation relation. -/
theorem evaluateApp_recclosure_partial_again_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (targetOriginal : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (envRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) targetOriginal)
    (found : functions[index]? = some (arity, body))
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    let targetClosure := BvlSem.Value.block 31
      (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (arity - 1 - oldArgs.length)) :: targetOriginal :: oldTargets)
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [targetClosure] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity closure found).1
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
  have sourceRun := evaluateApp_recclosure_partial s ptr arity index captured oldArgs newArgs functions body found nonempty argsBound (by simpa using partialBound)
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
  · refine ⟨.val [.recclosure (some ptr) (newArgs ++ oldArgs) captured functions index],
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
        · change vRel s.maxApp f t.refs t.code (.recclosure (some ptr) (newArgs ++ oldArgs) captured functions index) combined
          dsimp only [combined]
          exact vRel_partial_extend s t f captured oldArgs newArgs fields oldTargets newTargets
            (.recclosure (some ptr) [] captured functions index) (.recclosure (some ptr) oldArgs captured functions index)
            (.recclosure (some ptr) (newArgs ++ oldArgs) captured functions index) targetOriginal arity
            states envRel oldRel newRel oldNonempty partialBound (by omega)
            (by simp [addArgs]) (by simp [addArgs]) (by
              have indexBound : index < functions.length := List.getElem?_eq_some_iff.mp found |>.1
              rw [getNumArgs, Flapjack.holEl_eq_getElem index functions indexBound]
              have entryEq : functions[index] = (arity, body) := by simpa [List.getElem?_eq_getElem indexBound] using found
              simp [entryEq]) closure
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr
          ((stateRel_clock f s t (s.clock - newArgs.length)).1.mpr states)
      · intro key value mapped; exact mapped
      · intro key value mapped fresh; exact ⟨mapped, fresh⟩
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- Repeated undersaturated application of a related recursive closure
simulates the generated call for arbitrary recursive groups. -/
theorem evaluateApp_recclosure_partial_again_related {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (newTargets rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured functions index) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (partialBound : (newArgs ++ oldArgs).length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal) ∧
      evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
        [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, rfl, envRel, oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity index captured oldArgs functions body target found oldNonempty related
  exact evaluateApp_recclosure_partial_again_simulation s t f ptr arity index captured oldArgs newArgs functions
    fields oldTargets newTargets rest body original states annotations envRel closure found oldRel newRel oldNonempty nonempty partialBound

/-- Partially applying a recursive closure in any group preserves the value
relation and installs the correct partial-application stub. -/
theorem vRel_recclosure_partial {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured args : List ClosSem.Value) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (target : BvlSem.Value) (targetArgs : List BvlSem.Value)
    (states : stateRel f s t)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ []) (partialBound : args.length < arity) :
    vRel s.maxApp f t.refs t.code (.recclosure (some ptr) args captured functions index)
      (.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) ::
        .number (Int.ofNat (arity - 1 - args.length)) :: target :: targetArgs)) := by
  obtain ⟨fields, envRel, closure⟩ := vRel_recclosure_original functionRel
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity closure found).1
  have argsLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have argsPositive : 0 < args.length := List.length_pos_iff.mpr nonempty
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : targetArgs.length - 1 < arity - 1 := by omega
  have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (targetArgs.length - 1) ⟨totalBound, previousBound⟩
  have sizeEq : arity - 1 - (targetArgs.length - 1) + 1 = arity - args.length + 1 := by omega
  have installed' : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (targetArgs.length - 1)) t.code =
      some (arity - args.length + 1, generatePartialAppClosureFn (arity - 1) (targetArgs.length - 1)) := by
    simpa [sizeEq] using installed
  have getArgs : getNumArgs (.recclosure (some ptr) [] captured functions index) = some arity := by
    have indexBound : index < functions.length := List.getElem?_eq_some_iff.mp found |>.1
    rw [getNumArgs, Flapjack.holEl_eq_getElem index functions indexBound]
    have entryEq : functions[index] = (arity, body) := by simpa [List.getElem?_eq_getElem indexBound] using found
    simp [entryEq]
  exact .partialClosure envRel argsRel nonempty partialBound installed' (by simp [addArgs]) getArgs closure

/-- First partial application of a recursive closure in any group is simulated by the generated stub. -/
theorem evaluateApp_recclosure_partial_simulation {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured args : List ClosSem.Value) (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) targetClosure)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ []) (partialBound : args.length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal) ∧
      evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
        [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel, closure⟩ := vRel_recclosure_original functionRel
  have bounds := clRel_recclosure_arity closure found
  obtain ⟨arityBound, positive⟩ := bounds
  obtain ⟨address, stored, payload, targetEq⟩ := (clRel_dest _ _ _ _ _ _ _ _ closure).2
  have getStored : getNumArgs (.recclosure (some ptr) [] captured functions index) = some (stored + 1) := by
    apply clRel_getNumArgs _ _ _ _ _ _ _ 30 (.codePtr address) (stored + 1) payload
    simpa [targetEq] using closure
  have indexBound : index < functions.length := List.getElem?_eq_some_iff.mp found |>.1
  have entryEq : functions[index] = (arity, body) := by
    simpa [List.getElem?_eq_getElem indexBound] using found
  have storedEq : stored = arity - 1 := by
    rw [getNumArgs, Flapjack.holEl_eq_getElem index functions indexBound, entryEq] at getStored
    simp only [Option.some.injEq] at getStored
    omega
  rw [storedEq] at targetEq
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
  have targetRun := evaluate_mkClCall_partial_new start s.maxApp n (arity - 1) targetArgs payload rest
    (.codePtr address) targetLength previousBound totalBound lookup global
  have tickEq : n + 1 = args.length := by omega
  have remainingEq : arity - 1 - (n + 1) = arity - 1 - args.length := by omega
  have sourceRun := evaluateApp_recclosure_partial s ptr arity index captured [] args functions body found nonempty argsBound (by simpa using partialBound)
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
  · refine ⟨.val [.recclosure (some ptr) args captured functions index], ClosSem.decClock args.length s, ?_, ?_⟩
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
        · change vRel s.maxApp f t.refs t.code (.recclosure (some ptr) args captured functions index) partialClosure
          dsimp only [partialClosure]
          rw [targetEq]
          exact vRel_recclosure_partial s t f ptr arity index captured args functions body _ targetArgs states
            (by simpa [targetEq] using functionRel) argsRel found nonempty partialBound
        · exact .nil
      · exact (stateRel_clock f s t (s.clock - args.length)).2.mpr
          ((stateRel_clock f s t (s.clock - args.length)).1.mpr states)
      · intro key value mapped
        exact mapped
      · intro key value mapped fresh
        exact ⟨mapped, fresh⟩
      · exact annotations
      · simp [ClosSem.decClock, next, BvlSem.decClock, start]

/-- Undersaturated application of a related recursive closure simulates the
generated target call, whether or not it already has saved arguments. -/
theorem evaluateApp_recclosure_partial_related {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured oldArgs args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ [])
    (partialBound : (args ++ oldArgs).length < arity) :
    ∃ result sFinal,
      ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) args s = (result, sFinal) ∧
      evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
        [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  cases oldArgs with
  | nil =>
    simp only [List.append_nil] at partialBound
    exact evaluateApp_recclosure_partial_simulation s t f ptr arity index captured args functions targetArgs rest
      body target states annotations related argsRel found nonempty partialBound
  | cons head tail =>
    exact evaluateApp_recclosure_partial_again_related s t f ptr arity index captured (head :: tail) args
      functions targetArgs rest body target states annotations related argsRel found (by simp) nonempty partialBound

/-- A selected member of a related mutual-recursion group has a matching
target closure, shared array, and installed compiled entry. -/
theorem clRel_mutualRec_selected {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body)) :
    ∃ address shared targets aux targetBody finalAux,
      target = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] ∧
      refs.lookup shared = some (.valueArray (targets ++ fields)) ∧ targets.length = functions.length ∧
      arity ≤ maxApp ∧ arity ≠ 0 ∧
      compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
      sptLookup address code = some (arity + 1, (codeForReccCase (captured.length + functions.length) arity targetBody).2) ∧
      codeInstalled finalAux code := by
  cases related with
  | singletonRec _ _ _ _ _ _ _ => simp at many
  | @mutualRec exps entries ps rs loc shared env ys k expsEq psEq positions values fresh stored groupSize indexBound locations vars installed =>
    have entryBound : index < entries.length := by simpa [expsEq] using indexBound
    have entryEq : (entries[index]'entryBound).1 = (arity, body) := by
      have h : functions[index]? = some (arity, body) := found
      rw [expsEq, List.getElem?_map, List.getElem?_eq_getElem entryBound] at h
      simpa using h
    have groupLength : entries.length = functions.length := by simp [expsEq]
    have member : entries[index]'entryBound ∈ entries := List.getElem_mem _
    cases entryShape : entries[index]'entryBound with
    | mk pair address =>
      have pairEq : pair = (arity, body) := by simpa [entryShape] using entryEq
      subst pair
      have member' : ((arity, body), address) ∈ entries := by simpa [entryShape] using member
      obtain ⟨bound, positive, aux, targetBody, finalAux, compiled, lookup, installedAux⟩ := installed _ member'
      have targetShape : holEl index rs = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] := by
        rw [values, Flapjack.holEl_eq_getElem index _ (by simpa using entryBound)]
        simp [entryShape]
      have targetsLength : rs.length = functions.length := by simp [values, groupLength]
      exact ⟨address, shared, rs, aux, targetBody, finalAux, targetShape, stored, targetsLength,
        bound, positive, compiled, by simpa [groupLength] using lookup, installedAux⟩

/-- An exact target call of a mutual-recursive closure enters the selected
compiled body with the complete shared environment. -/
theorem clRel_mutualRec_exact_call {C F : Type} (s : BvlSem.State C F)
    (maxApp ptr index arity : Nat) (fs : Nat → Prop) (captured : List ClosSem.Value)
    (fields args rest : List BvlSem.Value) (functions : List (Nat × ClosLang.Exp))
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp fs s.refs s.code (captured, fields)
      (.recclosure (some ptr) [] captured functions index) target)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, sourceBody))
    (fieldsLength : fields.length = captured.length) (length : args.length = arity) :
    ∃ address shared targets aux targetBody finalAux,
      target = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] ∧
      s.refs.lookup shared = some (.valueArray (targets ++ fields)) ∧ targets.length = functions.length ∧
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
        (args ++ [target] ++ rest) s =
        if s.clock < arity then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          ((args ++ (targets ++ fields)) ++ [.refPtr true shared] ++ args ++ [target]) (BvlSem.decClock arity s) := by
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength,
    arityBound, positive, compiled, lookup, installed⟩ := clRel_mutualRec_selected related many found
  have nonempty : args ≠ [] := by
    intro empty
    simp [empty] at length
    exact positive length.symm
  refine ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength, compiled, installed, ?_⟩
  rw [targetEq]
  have run := evaluate_mkClCall_direct_env s args rest 30 address [.refPtr true shared]
    ((codeForReccCase (captured.length + functions.length) arity targetBody).2) nonempty
    (by simpa [length] using lookup)
  simp only [length] at run ⊢
  rw [run]
  split
  · rfl
  · have storedDec : (BvlSem.decClock arity s).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
      simpa [BvlSem.decClock] using stored
    have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
      simp [targetsLength, fieldsLength, Nat.add_comm]
    simpa [← sharedLength, ← length] using
      evaluateCodeForReccCase (BvlSem.decClock arity s) shared (targets ++ fields) args
        targetBody address (arity - 1) [] storedDec

/-- The selected mutual-recursive entry and its related closure group refer
to the same shared array. -/
theorem clRel_mutualRec_selected_related {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel maxApp f refs code) captured fields)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body)) :
    ∃ address shared targets aux targetBody finalAux,
      target = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] ∧
      refs.lookup shared = some (.valueArray (targets ++ fields)) ∧ targets.length = functions.length ∧
      List.Forall₂ (vRel maxApp f refs code)
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) targets ∧
      arity ≤ maxApp ∧ arity ≠ 0 ∧
      compileExpsHOL maxApp [body] aux = ([targetBody], finalAux) ∧
      sptLookup address code = some (arity + 1, (codeForReccCase (captured.length + functions.length) arity targetBody).2) ∧
      codeInstalled finalAux code := by
  cases related with
  | singletonRec _ _ _ _ _ _ _ => simp at many
  | @mutualRec exps entries ps rs loc shared env ys k expsEq psEq positions values fresh stored groupSize indexBound locations vars installed =>
    have targetsLength : rs.length = functions.length := by simp [values, expsEq]
    have groupRelated : List.Forall₂ (vRel maxApp f refs code)
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) rs := by
      apply List.forall₂_of_length_eq_of_get
      · simp [targetsLength]
      · intro j sourceBound targetBound
        have bound : j < functions.length := by simpa using sourceBound
        have groupRel : clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code
            (captured, fields) (.recclosure (some ptr) [] captured functions j) (holEl j rs) :=
          .mutualRec expsEq psEq positions values fresh stored groupSize bound locations vars installed
        obtain ⟨address', storedArity, payload, shape⟩ := (clRel_dest _ _ _ _ _ _ _ _ groupRel).2
        have valueRel : vRel maxApp f refs code (.recclosure (some ptr) [] captured functions j) (holEl j rs) := by
          rw [shape] at groupRel ⊢
          exact .closure envRel' groupRel
        rw [Flapjack.holEl_eq_getElem j rs targetBound] at valueRel
        simpa using valueRel
    have entryBound : index < entries.length := by simpa [expsEq] using indexBound
    have entryEq : (entries[index]'entryBound).1 = (arity, body) := by
      have h : functions[index]? = some (arity, body) := found
      rw [expsEq, List.getElem?_map, List.getElem?_eq_getElem entryBound] at h
      simpa using h
    have groupLength : entries.length = functions.length := by simp [expsEq]
    have member : entries[index]'entryBound ∈ entries := List.getElem_mem _
    cases entryShape : entries[index]'entryBound with
    | mk pair address =>
      have pairEq : pair = (arity, body) := by simpa [entryShape] using entryEq
      subst pair
      have member' : ((arity, body), address) ∈ entries := by simpa [entryShape] using member
      obtain ⟨bound, positive, aux, targetBody, finalAux, compiled, lookup, installedAux⟩ := installed _ member'
      have targetShape : holEl index rs = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] := by
        rw [values, Flapjack.holEl_eq_getElem index _ (by simpa using entryBound)]
        simp [entryShape]
      exact ⟨address, shared, rs, aux, targetBody, finalAux, targetShape, stored, targetsLength, groupRelated,
        bound, positive, compiled, by simpa [groupLength] using lookup, installedAux⟩

/-- An exact call to a related mutually recursive closure simulates the
selected body when the source clock suffices. -/
theorem evaluatePost_mutualRec_exact_call {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (length : args.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (args ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) = (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (locations : ClosProps.everyFnLocationSome [body]) (vars : ClosProps.everyFnVarsSome [body])
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength,
    groupRel, arityBound, positive, compiled, lookup, installed⟩ :=
    clRel_mutualRec_selected_related related envRel' many found
  have targetLength : targetArgs.length = arity := by rw [← length]; exact argsRel.length_eq.symm
  have nonempty : targetArgs ≠ [] := by intro empty; simp [empty] at targetLength; exact positive targetLength.symm
  have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
    exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code
      (args ++ (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      ((targetArgs ++ (targets ++ fields)) ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
    have tail : envRel s.maxApp f t.refs t.code captured (fields ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
      simpa using envRel_prepend envRel' (env := [])
        (targetEnv := BvlSem.Value.refPtr true shared :: (targetArgs ++ [target])) (by simp [envRel])
    have group : envRel s.maxApp f t.refs t.code
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
        (targets ++ fields ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
      simpa [List.append_assoc] using envRel_prepend groupRel tail
    simpa [List.append_assoc] using envRel_prepend argsRel group
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t _ _ f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + clock }
  have lookupStart : sptLookup address start.code = some (targetArgs.length + 1,
      (codeForReccCase (captured.length + functions.length) arity targetBody).2) := by
    simpa [start, targetLength] using lookup
  have callRun := evaluate_mkClCall_direct_env start targetArgs rest 30 address [.refPtr true shared]
    ((codeForReccCase (captured.length + functions.length) arity targetBody).2) nonempty lookupStart
  have enoughTarget : ¬ start.clock < targetArgs.length := by dsimp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have storedStart : (BvlSem.decClock targetArgs.length start).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
    simpa [start, BvlSem.decClock] using stored
  have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
    simp [targetsLength, envRel'.length_eq, Nat.add_comm]
  have entryRun := evaluateCodeForReccCase (BvlSem.decClock targetArgs.length start) shared (targets ++ fields) targetArgs
    targetBody address (arity - 1) [] storedStart
  have clockEq : s.clock + clock - arity = s.clock - arity + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
      (targetArgs ++ [target] ++ rest) start = (targetResult, tFinal) := by
    rw [targetEq]
    rw [show targetArgs.length - 1 = arity - 1 by omega] at callRun
    rw [callRun]
    rw [sharedLength, targetLength] at entryRun
    rw [targetLength]
    rw [entryRun]
    simpa [targetEq, start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- The selected recursive function inherits the group's body annotations. -/
theorem clRel_recclosure_annotations {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) :
    ClosProps.everyFnLocationSome [body] ∧ ClosProps.everyFnVarsSome [body] := by
  have locationMember : ∀ es : List ClosLang.Exp, ClosProps.everyFnLocationSome es →
      ∀ e ∈ es, ClosProps.fnLocationSomeExp e := by
    intro es h e member
    induction es with
    | nil => simp at member
    | cons head tail ih =>
      simp only [ClosProps.everyFnLocationSome] at h
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact h.1
      · exact ih h.2 member
  have varsMember : ∀ es : List ClosLang.Exp, ClosProps.everyFnVarsSome es →
      ∀ e ∈ es, ClosProps.fnVarsSomeExp e := by
    intro es h e member
    induction es with
    | nil => simp at member
    | cons head tail ih =>
      simp only [ClosProps.everyFnVarsSome] at h
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact h.1
      · exact ih h.2 member
  cases related with
  | singletonRec bound positive locations vars compiled installed lookup =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨locations, vars⟩
  | mutualRec exps ps positions values fresh stored many indexBound locations vars installed =>
    have member : body ∈ functions.map Prod.snd := List.mem_map.mpr ⟨(arity, body), List.mem_of_getElem? found, rfl⟩
    exact ⟨by simpa [ClosProps.everyFnLocationSome] using locationMember _ locations body member,
      by simpa [ClosProps.everyFnVarsSome] using varsMember _ vars body member⟩

/-- Exact mutual-recursive application simulates the selected body when the
source has enough clock. -/
theorem evaluateApp_mutualRec_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (length : args.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity related found
  have ⟨locations, vars⟩ := clRel_recclosure_annotations related found
  have nonempty : args ≠ [] := by intro empty; simp [empty] at length; exact positive length.symm
  have bound : args.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (args ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr index arity captured [] args functions body
      found nonempty (by simp only [List.length_nil]; have h := List.length_pos_iff.mpr nonempty; omega)
      bound (by simpa using length) (by simpa [length] using enough) bodyResult (by simpa [length] using bodyRun)
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_mutualRec_exact_call s sFinal t f ptr index arity captured args fields targetArgs rest
      functions body target states annotations related envRel' argsRel many found length enough result bodyRun noType locations vars bodyIH

/-- Exact mutual-recursive application times out on both sides when the
source has insufficient clock. -/
theorem evaluateApp_mutualRec_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (length : args.length = arity) (timeout : s.clock < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [target] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity related found
  have nonempty : args ≠ [] := by intro empty; simp [empty] at length; exact positive length.symm
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_recclosure_exact s ptr arity index captured [] args functions body found nonempty (by simp; omega)
      (by omega) (by simpa using length)]
    simp [length, timeout]
  have targetLength : targetArgs.length = arity := by rw [← length]; exact argsRel.length_eq.symm
  let start : BvlSem.State C F := { t with clock := s.clock }
  have shifted : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target := by simpa [start] using related
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, targetRun⟩ :=
    clRel_mutualRec_exact_call start s.maxApp ptr index arity _ captured fields targetArgs rest functions body target
      shifted many found envRel'.length_eq.symm targetLength
  have targetTimeout : start.clock < arity := by simpa [start] using timeout
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- Exact application of a related mutual-recursive closure simulates both
body execution and timeout. -/
theorem evaluateApp_mutualRec_exact_related {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body)) (length : args.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original related
  by_cases enough : arity ≤ s.clock
  · exact evaluateApp_mutualRec_exact_simulation s sFinal t f ptr index arity captured args fields targetArgs rest
      functions body target states annotations closure envRel' argsRel many found length enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_mutualRec_exact_timeout s t f ptr index arity captured args
      fields targetArgs rest functions body target states annotations closure envRel' argsRel many found length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Completing a mutual-recursive partial closure enters the selected body
with its new arguments, saved arguments and shared recursive environment. -/
theorem evaluate_partialComplete_mutualRec_entry {C F : Type} (s : BvlSem.State C F)
    (maxApp ptr index arity : Nat) (f : HolFiniteMapExact Nat Nat) (captured : List ClosSem.Value)
    (fields newArgs saved rest : List BvlSem.Value) (functions : List (Nat × ClosLang.Exp))
    (sourceBody : ClosLang.Exp) (target : BvlSem.Value)
    (related : clRel maxApp (fun p => ∃ r, f.lookup r = some p) s.refs s.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel maxApp f s.refs s.code) captured fields)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, sourceBody))
    (nonempty : newArgs ≠ []) (savedNonempty : saved ≠ []) (length : newArgs.length + saved.length = arity)
    (stubLookup : sptLookup (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) s.code =
      some (newArgs.length + 1, generatePartialAppClosureFn (arity - 1) (saved.length - 1))) :
    ∃ address shared targets aux targetBody finalAux,
      target = .block 30 [.codePtr address, .number (Int.ofNat (arity - 1)), .refPtr true shared] ∧
      s.refs.lookup shared = some (.valueArray (targets ++ fields)) ∧
      List.Forall₂ (vRel maxApp f s.refs s.code)
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) targets ∧
      compileExpsHOL maxApp [sourceBody] aux = ([targetBody], finalAux) ∧
      codeInstalled finalAux s.code ∧
      sptLookup address s.code = some (arity + 1,
        (codeForReccCase (captured.length + functions.length) arity targetBody).2) ∧
      BvlSem.evaluate [mkClCall (.var newArgs.length) ((List.range newArgs.length).map Bvl.Exp.var)]
        (newArgs ++ [.block 31 (.codePtr (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) ::
          .number (Int.ofNat (newArgs.length - 1)) :: target :: saved)] ++ rest) s =
        if s.clock < newArgs.length + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
        else BvlSem.evaluate [targetBody]
          (((newArgs ++ saved) ++ (targets ++ fields)) ++ [.refPtr true shared] ++ (newArgs ++ saved) ++ [target])
          (BvlSem.decClock (newArgs.length + 1) s) := by
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength,
    groupRel, arityBound, positive, compiled, lookup, installed⟩ :=
    clRel_mutualRec_selected_related related envRel' many found
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have savedPositive : 0 < saved.length := List.length_pos_iff.mpr savedNonempty
  have newCount : arity - 1 - (saved.length - 1) = newArgs.length := by omega
  have savedCount : saved.length - 1 + 1 = saved.length := by omega
  refine ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, groupRel, compiled, installed, lookup, ?_⟩
  rw [targetEq]
  have callRun := evaluate_mkClCall_partial_complete s (arity - 1) (saved.length - 1) newArgs saved rest
    (partialAppFnLocation maxApp (arity - 1) (saved.length - 1)) address
    [.number (Int.ofNat (arity - 1)), .refPtr true shared] _ nonempty newCount savedCount stubLookup
    (by simpa [length] using lookup)
  rw [callRun]
  split
  · rfl
  · have storedDec : (BvlSem.decClock (newArgs.length + 1) s).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
      simpa [BvlSem.decClock] using stored
    have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
      simp [targetsLength, envRel'.length_eq, Nat.add_comm]
    simpa [← sharedLength, ← length, List.length_append, List.append_assoc] using
      evaluateCodeForReccCase (BvlSem.decClock (newArgs.length + 1) s) shared (targets ++ fields) (newArgs ++ saved)
        targetBody address (arity - 1) [] storedDec

/-- Saturated mutual-recursive partial application simulates the selected body. -/
theorem evaluatePost_mutualRec_partial_exact {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity related found).1
  have ⟨locations, vars⟩ := clRel_recclosure_annotations related found
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, groupRel, compiled, installed, sourceLookup, _⟩ :=
    evaluate_partialComplete_mutualRec_entry t s.maxApp ptr index arity f captured fields newTargets oldTargets rest
      functions body original related envRel' many found targetNewNonempty targetOldNonempty targetLength stubLookup
  have bodyStates : stateRel f (ClosSem.decClock newArgs.length s) t := by
    exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code
      (newArgs ++ oldArgs ++ (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (((newTargets ++ oldTargets) ++ (targets ++ fields)) ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) := by
    have tail : envRel s.maxApp f t.refs t.code captured
        (fields ++ .refPtr true shared :: ((newTargets ++ oldTargets) ++ [original])) := by
      simpa using envRel_prepend envRel' (env := [])
        (targetEnv := BvlSem.Value.refPtr true shared :: ((newTargets ++ oldTargets) ++ [original])) (by simp [envRel])
    have group : envRel s.maxApp f t.refs t.code
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
        (targets ++ fields ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) := by
      simpa [List.append_assoc] using envRel_prepend groupRel tail
    simpa [List.append_assoc] using envRel_prepend (List.rel_append newRel oldRel) group
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured)
    (((newTargets ++ oldTargets) ++ (targets ++ fields)) ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + (clock + 1) }
  have shiftedStub : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    simpa [start] using stubLookup
  have shiftedOriginal : sptLookup address start.code = some ((newTargets.length + oldTargets.length) + 1,
      (codeForReccCase (captured.length + functions.length) arity targetBody).2) := by
    simpa [start, targetLength] using sourceLookup
  have newCount : arity - 1 - (oldTargets.length - 1) = newTargets.length := by omega
  have savedCount : oldTargets.length - 1 + 1 = oldTargets.length := by omega
  have callRun := evaluate_mkClCall_partial_complete start (arity - 1) (oldTargets.length - 1) newTargets oldTargets rest
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) address
    [.number (Int.ofNat (arity - 1)), .refPtr true shared] _ targetNewNonempty newCount savedCount shiftedStub shiftedOriginal
  have enoughTarget : ¬ start.clock < newTargets.length + 1 := by dsimp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have storedStart : (BvlSem.decClock (newTargets.length + 1) start).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
    simpa [start, BvlSem.decClock] using stored
  have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
    have targetsLength := groupRel.length_eq.symm
    simp only [List.length_map, List.length_range] at targetsLength
    simp [targetsLength, envRel'.length_eq, Nat.add_comm]
  have entryRun := evaluateCodeForReccCase (BvlSem.decClock (newTargets.length + 1) start)
    shared (targets ++ fields) (newTargets ++ oldTargets) targetBody address (arity - 1) [] storedStart
  have clockEq : s.clock + (clock + 1) - (newTargets.length + 1) = s.clock - newArgs.length + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)]
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) start = (targetResult, tFinal) := by
    rw [targetEq, callRun]
    rw [sharedLength, List.length_append, targetLength] at entryRun
    rw [entryRun]
    simpa [targetEq, start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock + 1, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- Saturated mutual-recursive partial application simulates success and timeout. -/
theorem evaluateApp_mutualRec_partial_exact_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity related found).1
  have positive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured) (ClosSem.decClock newArgs.length s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr index arity captured oldArgs newArgs functions body
      found nonempty oldBound bound length enough bodyResult bodyRun
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_mutualRec_partial_exact s sFinal t f ptr index arity captured oldArgs newArgs functions fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel many found oldNonempty nonempty length enough result bodyRun noType bodyIH

/-- A saturated singleton recursive partial closure times out on both sides when the
source clock is insufficient. -/
theorem evaluateApp_mutualRec_partial_exact_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (_many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (timeout : s.clock < newArgs.length) :
    ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity related found).1
  have oldLength : oldTargets.length = oldArgs.length := oldRel.length_eq.symm
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have oldPositive : 0 < oldArgs.length := List.length_pos_iff.mpr oldNonempty
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_recclosure_exact s ptr arity index captured oldArgs newArgs functions body found nonempty oldBound bound length]
    simp [timeout]
  have targetNonempty : newTargets ≠ [] := by simp only [← List.length_pos_iff, newLength]; exact newPositive
  have totalBound : arity - 1 < s.maxApp := by omega
  have prevBound : oldTargets.length - 1 < arity - 1 := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1)
      ⟨totalBound, prevBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = newTargets.length + 1 := by omega
    simpa [start, count] using installed
  have targetRun := evaluate_mkClCall_direct_env start newTargets rest 31
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) (original :: oldTargets)
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) targetNonempty stubLookup
  have targetTimeout : start.clock < newTargets.length := by dsimp [start]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- Saturated mutual-recursive partial application composes with the expression simulations. -/
theorem evaluateApp_mutualRec_partial_exact_related {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured functions index) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, targetEq, envRel', oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity index captured oldArgs functions body target found oldNonempty related
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_mutualRec_partial_exact_simulation s sFinal t f ptr index arity captured oldArgs newArgs functions
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      many found oldNonempty nonempty length enough result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_mutualRec_partial_exact_timeout s t f ptr index arity
      captured oldArgs newArgs functions fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      many found oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Extract the overapplication branch of the generated generic stub. -/
def genericAppOverBranch (maxApp n : Nat) : Bvl.Exp :=
  match generateGenericApp maxApp n with
  | .let _ (.ifThenElse _ over _) => over
  | _ => .var 0

/-- When the supplied argument group exceeds the closure's remaining arity,
the generic stub enters its overapplication branch. -/
theorem evaluate_genericApp_over_branch {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (bound : total < n + 1) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]) s =
    BvlSem.evaluate [genericAppOverBranch maxApp n]
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
      (.val [BvlSem.boolValue true], s) := by
    have negative : diff < 0 := by dsimp [diff]; omega
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyNumeric,
      BvlSem.doIntApp, mkConst, negative]
  change BvlSem.evaluate [.let [.op (.intOp .sub)
      [mkConst (n + 1), .op (.blockOp (.elemAt 1)) [.var (n + 1)]]]
      (.ifThenElse (.op (.intOp .less) [mkConst 0, .var 0])
        (genericAppOverBranch maxApp n) _)] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, firstRun]
  dsimp only
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
  simp only [List.singleton_append]
  rw [testRun]
  simp [BvlSem.boolValue, BackendCommon.boolToTag, BackendCommon.trueTag, BvlSem.asBool, env, diff]

/-- The overapplication branch dispatches on the stored remaining arity. -/
theorem genericAppOverBranch_shape (maxApp n : Nat) :
    genericAppOverBranch maxApp n = BvlJump.jump
      (.op (.blockOp (.elemAt 1)) [.var (n + 2)])
      ((List.range maxApp).map fun numArgs =>
        .let [.call numArgs none
          ((List.range (numArgs + 1)).map (fun arg => .var (arg + 2 + n - numArgs)) ++
            [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]])]
          (mkClCall (.var 0) ((List.range (n - numArgs)).map fun i => .var (i + 3)))) := by
  rfl

/-- For an in-range stored arity, the overapplication branch selects the
corresponding generated case of the balanced dispatch tree. -/
theorem evaluate_genericAppOverBranch {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (totalBound : total < maxApp) :
    BvlSem.evaluate [genericAppOverBranch maxApp n]
      (.number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s =
    BvlSem.evaluate [.let [.call total none
        ((List.range (total + 1)).map (fun arg => .var (arg + 2 + n - total)) ++
          [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]])]
        (mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3)))]
      (.number (Int.ofNat total) :: .number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s := by
  let env := .number (Int.ofNat total - Int.ofNat (n + 1)) ::
    (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])
  have selector : BvlSem.evaluate [.op (.blockOp (.elemAt 1)) [.var (n + 2)]] env s =
      (.val [.number (Int.ofNat total)], s) := by
    simp [BvlSem.evaluate, BvlSem.fixClock, BvlSem.doApp, BvlSem.applyBlock, env, ← length]
  rw [genericAppOverBranch_shape]
  let branches := (List.range maxApp).map fun numArgs =>
    Bvl.Exp.let [.call numArgs none
      ((List.range (numArgs + 1)).map (fun arg => .var (arg + 2 + n - numArgs)) ++
        [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]])]
      (mkClCall (.var 0) ((List.range (n - numArgs)).map fun i => .var (i + 3)))
  have run := BvlJump.evaluate_jump (.op (.blockOp (.elemAt 1)) [.var (n + 2)]) branches env s s total selector
    (by simpa [branches] using totalBound)
  simpa [env, branches, List.getElem_map] using run

/-- An overapplied generic stub dispatches to the case for the closure's
stored remaining arity, without changing the state. -/
theorem evaluate_genericApp_over_dispatch {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag : Nat) (args fields : List BvlSem.Value) (ptr : BvlSem.Value)
    (length : args.length = n + 1) (over : total < n + 1) (totalBound : total < maxApp) :
    BvlSem.evaluate [generateGenericApp maxApp n]
      (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)]) s =
    BvlSem.evaluate [.let [.call total none
        ((List.range (total + 1)).map (fun arg => .var (arg + 2 + n - total)) ++
          [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]])]
        (mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3)))]
      (.number (Int.ofNat total) :: .number (Int.ofNat total - Int.ofNat (n + 1)) ::
        (args ++ [.block tag (ptr :: .number (Int.ofNat total) :: fields)])) s := by
  rw [evaluate_genericApp_over_branch s maxApp n total tag args fields ptr length over]
  exact evaluate_genericAppOverBranch s maxApp n total tag args fields ptr length totalBound

/-- The first overapplication call applies the argument suffix to the
original closure and charges its full arity in target ticks. -/
theorem evaluate_overApp_firstCall {C F : Type} (s : BvlSem.State C F)
    (n total tag address : Nat) (args fields : List BvlSem.Value) (first second : BvlSem.Value)
    (body : Bvl.Exp) (length : args.length = n + 1) (over : total < n + 1)
    (lookup : sptLookup address s.code = some (total + 2, body)) :
    let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
    BvlSem.evaluate [.call total none
      ((List.range (total + 1)).map (fun arg => .var (arg + 2 + n - total)) ++
        [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]])]
      (first :: second :: (args ++ [closure])) s =
    if s.clock < total + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
    else BvlSem.evaluate [body] (args.drop (n - total) ++ [closure]) (BvlSem.decClock (total + 1) s) := by
  let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
  let env := first :: second :: (args ++ [closure])
  have argsRun : BvlSem.evaluate ((List.range (total + 1)).map (fun arg => Bvl.Exp.var (arg + 2 + n - total))) env s =
      (.val (args.drop (n - total)), s) := by
    dsimp only [env]
    have shift (arg : Nat) : arg + 2 + n - total = arg + (n - total + 2) := by omega
    simp only [shift]
    have h := BvlProps.evaluateGenlistVars (n - total + 2)
      (first :: second :: (args ++ [closure])) (total + 1) s (by simp; omega)
    have off : n - total + 2 = Nat.succ (Nat.succ (n - total)) := by omega
    have dropEq : (first :: second :: (args ++ [closure])).drop (n - total + 2) =
        args.drop (n - total) ++ [closure] := by
      rw [off]
      simp only [List.drop_succ_cons]
      exact List.drop_append_of_le_length (by omega)
    have suffixLength : (args.drop (n - total)).length = total + 1 := by simp; omega
    change BvlSem.evaluate _ _ _ = _ at h
    rw [dropEq, List.take_append_of_le_length (by omega : total + 1 ≤ (args.drop (n - total)).length),
      ← suffixLength, List.take_length] at h
    simpa only [suffixLength] using h
  have closureRun : BvlSem.evaluate [.var (n + 3)] env s = (.val [closure], s) := by
    simp [BvlSem.evaluate, env, ← length]
  have pointerRun : BvlSem.evaluate [.op (.blockOp (.elemAt 0)) [.var (n + 3)]] env s =
      (.val [.codePtr address], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, closureRun]
    simp [BvlSem.doApp, BvlSem.applyBlock, closure]
  have tailRun : BvlSem.evaluate [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]] env s =
      (.val [closure, .codePtr address], s) := by
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, closureRun, pointerRun]
    rfl
  have allRun : BvlSem.evaluate
      (((List.range (total + 1)).map (fun arg => Bvl.Exp.var (arg + 2 + n - total))) ++
        [.var (n + 3), .op (.blockOp (.elemAt 0)) [.var (n + 3)]]) env s =
      (.val (args.drop (n - total) ++ [closure, .codePtr address]), s) := by
    change BvlSem.evaluateTuple (_, env, s) = _
    rw [BvlProps.evaluateAppend]
    simp [BvlSem.evaluateTuple, argsRun, tailRun]
  have suffixLength : (args.drop (n - total)).length = total + 1 := by
    simp [List.length_drop, length]
    omega
  have lastPair (inst : Nonempty BvlSem.Value) (xs : List BvlSem.Value) (x y : BvlSem.Value) :
      @Flapjack.holLast BvlSem.Value inst (xs ++ [x, y]) = y := by
    induction xs with
    | nil => simp [Flapjack.holLast]
    | cons z zs ih => simp [Flapjack.holLast_cons, ih]
  change BvlSem.evaluate [.call total none _] env s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, allRun]
  simp [BvlSem.findCode, lookup, lastPair, suffixLength, closure]

/-- An overapplied generic stub first runs the saturated call. Errors and
timeouts propagate; successful values are bound for the remaining call. -/
theorem evaluate_genericApp_over_step {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag address : Nat) (args fields : List BvlSem.Value) (body : Bvl.Exp)
    (length : args.length = n + 1) (over : total < n + 1) (totalBound : total < maxApp)
    (lookup : sptLookup address s.code = some (total + 2, body)) :
    let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
    BvlSem.evaluate [generateGenericApp maxApp n] (args ++ [closure]) s =
      if s.clock < total + 1 then (.err (.abort .timeoutError), { s with clock := 0 })
      else
        let next := BvlSem.evaluate [body] (args.drop (n - total) ++ [closure]) (BvlSem.decClock (total + 1) s)
        match next.1 with
        | .err error => (.err error, next.2)
        | .val values => BvlSem.evaluate
            [mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3))]
            (values ++ [.number (Int.ofNat total), .number (Int.ofNat total - Int.ofNat (n + 1))] ++
              args ++ [closure]) next.2 := by
  let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
  change BvlSem.evaluate [generateGenericApp maxApp n] (args ++ [closure]) s = _
  rw [evaluate_genericApp_over_dispatch s maxApp n total tag args fields (.codePtr address) length over totalBound]
  change BvlSem.evaluate [.let [.call total none _] _]
    (.number (Int.ofNat total) :: .number (Int.ofNat total - Int.ofNat (n + 1)) :: (args ++ [closure])) s = _
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate,
    evaluate_overApp_firstCall s n total tag address args fields (.number (Int.ofNat total))
      (.number (Int.ofNat total - Int.ofNat (n + 1))) body length over lookup]
  by_cases timeout : s.clock < total + 1
  · simp [timeout]
  · simp only [timeout, ↓reduceIte]
    cases BvlSem.evaluate [body] (args.drop (n - total) ++ [closure]) (BvlSem.decClock (total + 1) s) with
    | mk result next => cases result <;> simp [closure, List.append_assoc]

/-- Overapplication of an ordinary closure evaluates its saturated body, then
applies any remaining prefix to a singleton result. -/
theorem evaluateApp_ordinary_over {C F : Type} (s : ClosSem.State C F)
    (ptr arity : Nat) (captured saved args : List ClosSem.Value) (body : ClosLang.Exp)
    (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length + saved.length) :
    ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s =
      if s.clock < arity - saved.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else
        let next := ClosSem.fixClock (ClosSem.decClock (arity - saved.length) s)
          (ClosSem.evaluate [body] (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
            (ClosSem.decClock (arity - saved.length) s))
        match next.1 with
        | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) next.2
        | other => (other, next.2) := by
  have nonempty : args ≠ [] := by intro empty; simp [empty] at over; omega
  have neededBound : arity - saved.length ≤ args.length := by omega
  have cost : args.length - (args.take (args.length - (arity - saved.length))).length = arity - saved.length := by
    simp [List.length_take]
    omega
  have notPartial : ¬ args.length + saved.length < arity := by omega
  have selected : ClosSem.destClosure s.maxApp none (.closure (some ptr) saved captured arity body) args =
      some (.fullApp body (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
        (args.take (args.length - (arity - saved.length)))) := by
    simp [ClosSem.destClosure, ClosSem.checkLoc, bound, savedBound, notPartial,
      List.reverse_take, List.reverse_drop, List.append_assoc]
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, selected]
    simp only [cost]
    split <;> rfl

/-- Overapplication of a recursive closure evaluates the selected body with
its recursive group, then applies any remaining prefix to a singleton result. -/
theorem evaluateApp_recclosure_over {C F : Type} (s : ClosSem.State C F)
    (ptr arity index : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (found : functions[index]? = some (arity, body)) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length) :
    ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s =
      if s.clock < arity - saved.length then (.err (.abort .timeoutError), { s with clock := 0 })
      else
        let next := ClosSem.fixClock (ClosSem.decClock (arity - saved.length) s)
          (ClosSem.evaluate [body] (args.drop (args.length - (arity - saved.length)) ++ saved ++
            (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
            (ClosSem.decClock (arity - saved.length) s))
        match next.1 with
        | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) next.2
        | other => (other, next.2) := by
  have nonempty : args ≠ [] := by intro empty; simp [empty] at over; omega
  have neededBound : arity - saved.length ≤ args.length := by omega
  have cost : args.length - (args.take (args.length - (arity - saved.length))).length = arity - saved.length := by
    simp [List.length_take]
    omega
  have notPartial : ¬ args.length + saved.length < arity := by omega
  have selected : ClosSem.destClosure s.maxApp none (.recclosure (some ptr) saved captured functions index) args =
      some (.fullApp body (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
        (args.take (args.length - (arity - saved.length)))) := by
    simp [ClosSem.destClosure, found, ClosSem.checkLoc, bound, savedBound, notPartial,
      List.reverse_take, List.reverse_drop, List.append_assoc]
  cases args with
  | nil => contradiction
  | cons head tail =>
    rw [ClosSem.evaluateApp, selected]
    simp only [cost]
    split <;> rfl

/-- The source overapplication split and generated target split agree on
related argument lists and preserve the relation in each segment. -/
theorem overApp_related_split {α β : Type} (r : α → β → Prop)
    (source : List α) (target : List β) (arity saved n total : Nat)
    (related : List.Forall₂ r source target) (targetLength : target.length = n + 1)
    (savedBound : saved < arity) (storedArity : total = arity - saved - 1)
    (over : arity < source.length + saved) :
    source.length - (arity - saved) = n - total ∧
    List.Forall₂ r (source.take (source.length - (arity - saved))) (target.take (n - total)) ∧
    List.Forall₂ r (source.drop (source.length - (arity - saved))) (target.drop (n - total)) := by
  have sameLength : source.length = target.length := related.length_eq
  have splitEq : source.length - (arity - saved) = n - total := by omega
  have takeRel := List.forall₂_take (n - total) related
  have dropRel := clRelRunLemma3 r source target (arity - saved) related
  exact ⟨splitEq, by simpa [splitEq] using takeRel,
    by simpa [← sameLength, splitEq] using dropRel⟩

/-- Overapplication suffix facts shared by the partial-completion cases: the
saved group has the source length and is nonempty, the dropped suffix groups
are related, and both suffix groups have the remaining arity. Flapjack
infrastructure; no separately named HOL original. -/
private theorem overAppSuffixFacts {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (arity n total : Nat)
    (saved args : List ClosSem.Value) (oldTargets targetArgs : List BvlSem.Value)
    (sourceSuffix : List ClosSem.Value) (targetSuffix : List BvlSem.Value)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ [])
    (savedBound : saved.length < arity) (storedArity : total = arity - saved.length - 1)
    (over : arity < args.length + saved.length)
    (sourceEq : sourceSuffix = args.drop (args.length - (arity - saved.length)))
    (targetEq : targetSuffix = targetArgs.drop (n - total)) :
    oldTargets.length = saved.length ∧ 0 < saved.length ∧
      List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix ∧
      sourceSuffix.length = arity - saved.length ∧
      targetSuffix.length = arity - saved.length := by
  have savedLength : oldTargets.length = saved.length := savedRel.length_eq.symm
  have savedPositive : 0 < saved.length := List.length_pos_iff.mpr savedNonempty
  have ⟨_, _, suffixRel⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity saved.length n total argsRel length savedBound storedArity over
  have relatedSuffix : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix := by
    simpa [sourceEq, targetEq] using suffixRel
  have sourceLength : sourceSuffix.length = arity - saved.length := by
    rw [sourceEq]
    simp only [List.length_drop]
    omega
  have targetLength : targetSuffix.length = arity - saved.length := by
    rw [← sourceLength]
    exact relatedSuffix.length_eq.symm
  exact ⟨savedLength, savedPositive, relatedSuffix, sourceLength, targetLength⟩

/-- The generated closure call and generic overapplication stub execute the
first saturated call, charging the outer call tick and the closure arity. -/
theorem evaluate_mkClCall_over_step {C F : Type} (s : BvlSem.State C F)
    (maxApp n total tag address : Nat) (args fields rest : List BvlSem.Value) (body : Bvl.Exp)
    (length : args.length = n + 1) (over : total < n) (totalBound : total < maxApp)
    (genericLookup : sptLookup (genericAppFnLocation n) s.code = some (n + 2, generateGenericApp maxApp n))
    (lookup : sptLookup address s.code = some (total + 2, body)) :
    let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
    BvlSem.evaluate [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]
      (args ++ [closure] ++ rest) s =
    if s.clock < total + 2 then (.err (.abort .timeoutError), { s with clock := 0 })
    else
      let next := BvlSem.evaluate [body] (args.drop (n - total) ++ [closure]) (BvlSem.decClock (total + 2) s)
      match next.1 with
      | .err error => (.err error, next.2)
      | .val values => BvlSem.evaluate
          [mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3))]
          (values ++ [.number (Int.ofNat total), .number (Int.ofNat total - Int.ofNat (n + 1))] ++
            args ++ [closure]) next.2 := by
  let closure := BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)
  let env := args ++ [closure] ++ rest
  have clRun : BvlSem.evaluate [.var args.length] env s = (.val [closure], s) := by simp [BvlSem.evaluate, env]
  have argsRun : BvlSem.evaluate ((List.range args.length).map Bvl.Exp.var) env s = (.val args, s) := by
    have bound : args.length ≤ env.length := by simp [env]
    simpa [env, BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 env args.length s bound
  have different : ((List.range args.length).map Bvl.Exp.var).length - 1 ≠ total := by
    simp only [List.length_map, List.length_range, length]
    omega
  have lookup' : sptLookup (genericAppFnLocation (((List.range args.length).map Bvl.Exp.var).length - 1)) s.code =
      some (args.length + 1, generateGenericApp maxApp n) := by simpa [length] using genericLookup
  have callRun := evaluate_mkClCall_generic s env (.var args.length) ((List.range args.length).map Bvl.Exp.var)
    args tag total (.codePtr address) fields (generateGenericApp maxApp n)
    (by simpa [closure] using clRun) argsRun different lookup'
  simp only [length] at callRun
  change BvlSem.evaluate [_] env s = _
  simp only [length]
  rw [callRun]
  by_cases zero : s.clock = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    have lookupDec : sptLookup address (BvlSem.decClock 1 s).code = some (total + 2, body) := by
      simpa [BvlSem.decClock] using lookup
    rw [evaluate_genericApp_over_step (BvlSem.decClock 1 s) maxApp n total tag address args fields body
      length (by omega) totalBound lookupDec]
    have clockTest : (BvlSem.decClock 1 s).clock < total + 1 ↔ s.clock < total + 2 := by
      simp only [BvlSem.decClock]
      omega
    simp only [clockTest]
    split
    · simp [BvlSem.decClock]
    · have clocks : s.clock - 1 - (total + 1) = s.clock - (total + 2) := by omega
      simp [BvlSem.decClock, clocks]

/-- If an overapplied ordinary closure runs out of clock before its first
body call, both source and target time out. -/
theorem evaluateApp_ordinary_over_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length) (timeout : s.clock < arity) :
    ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [target] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_ordinary_closure related
  have shape : ∃ targetBody,
      arity ≤ s.maxApp ∧ arity ≠ 0 ∧
      target = .block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) ∧
      sptLookup (ptr + numStubs s.maxApp) t.code = some (arity + 1,
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) := by
    cases closure with
    | closure arityBound positive _ _ _ _ lookup => exact ⟨_, arityBound, positive, rfl, lookup⟩
  obtain ⟨targetBody, arityBound, positive, targetEq, bodyLookup⟩ := shape
  have sourceTimeout : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_ordinary_over s ptr arity captured [] args body (by simp; omega) bound (by simpa using over)]
    simp [timeout]
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  let n := targetArgs.length - 1
  have length : targetArgs.length = n + 1 := by dsimp [n]; omega
  have over' : arity - 1 < n := by dsimp [n]; omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have genericLookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have lookup : sptLookup (ptr + numStubs s.maxApp) start.code = some (arity - 1 + 2,
      .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) := by
    have arityEq : arity - 1 + 2 = arity + 1 := by omega
    simpa [start, arityEq] using bodyLookup
  have targetRun := evaluate_mkClCall_over_step start s.maxApp n (arity - 1) 30 (ptr + numStubs s.maxApp)
    targetArgs fields rest _ length over' totalBound genericLookup lookup
  have targetTimeout : start.clock < arity - 1 + 2 := by dsimp [start]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · rw [targetEq]
    simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- An overapplied ordinary partial closure times out on both sides when the
source clock is insufficient for its first saturated call. -/
theorem evaluateApp_ordinary_partial_over_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) saved captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (savedNonempty : saved ≠ []) (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length + saved.length) (timeout : s.clock < arity - saved.length) :
    ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [target] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨oldTargets, original, targetEq, originalRel, oldRel⟩ :=
    vRel_ordinary_partial_existing s t f ptr arity captured saved body target savedNonempty related
  obtain ⟨fields, envRel', closure⟩ := vRel_ordinary_closure originalRel
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure arityBound positive _ _ _ _ _ => exact ⟨arityBound, positive⟩
  have sourceTimeout : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_ordinary_over s ptr arity captured saved args body savedBound bound over]
    simp [timeout]
  have oldLength : oldTargets.length = saved.length := oldRel.length_eq.symm
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have savedPositive : 0 < saved.length := List.length_pos_iff.mpr savedNonempty
  let n := targetArgs.length - 1
  let total := arity - 1 - saved.length
  have length : targetArgs.length = n + 1 := by dsimp [n]; omega
  have over' : total < n := by dsimp [total, n]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  have stubPrev : oldTargets.length - 1 < arity - 1 := by omega
  have stubTotal : arity - 1 < s.maxApp := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have genericLookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨stubTotal, stubPrev⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = total + 2 := by dsimp [total]; omega
    simpa [start, count] using installed
  have targetRun := evaluate_mkClCall_over_step start s.maxApp n total 31
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) targetArgs (original :: oldTargets) rest
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) length over' totalBound genericLookup stubLookup
  have targetTimeout : start.clock < total + 2 := by dsimp [start, total]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · rw [targetEq]
    simpa [start, total] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- A directly related recursive closure has installed code at the pointer
stored in its target block, for both singleton and mutual groups. -/
theorem clRel_recclosure_target_code {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) :
    ∃ address payload entry,
      target = .block 30 (.codePtr address :: .number (Int.ofNat (arity - 1)) :: payload) ∧
      sptLookup address code = some (arity + 1, entry) := by
  by_cases many : 1 < functions.length
  · obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength,
      bound, positive, compiled, lookup, installed⟩ := clRel_mutualRec_selected related many found
    exact ⟨address, [.refPtr true shared], _, targetEq, lookup⟩
  · cases related with
    | singletonRec bound positive locations vars compiled installed lookup =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨_, _, _, rfl, lookup⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim

/-- An overapplied recursive closure times out on both sides before its first body call. -/
theorem evaluateApp_recclosure_over_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (bound : args.length ≤ s.maxApp) (over : arity < args.length) (timeout : s.clock < arity) :
    ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [target] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original related
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  obtain ⟨address, payload, targetBody, targetEq, bodyLookup⟩ := clRel_recclosure_target_code closure found
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_recclosure_over s ptr arity index captured [] args functions body found (by simp; omega) bound (by simpa using over)]
    simp [timeout]
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  let n := targetArgs.length - 1
  have length : targetArgs.length = n + 1 := by dsimp [n]; omega
  have over' : arity - 1 < n := by dsimp [n]; omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have genericLookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have lookup : sptLookup address start.code = some (arity - 1 + 2,
      targetBody) := by
    have arityEq : arity - 1 + 2 = arity + 1 := by omega
    simpa [start, arityEq] using bodyLookup
  have targetRun := evaluate_mkClCall_over_step start s.maxApp n (arity - 1) 30 address
    targetArgs payload rest _ length over' totalBound genericLookup lookup
  have targetTimeout : start.clock < arity - 1 + 2 := by dsimp [start]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · rw [targetEq]
    simpa [start] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- An overapplied recursive partial closure times out on both sides before its first body call. -/
theorem evaluateApp_recclosure_partial_over_timeout {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity index : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) saved captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length + saved.length) (timeout : s.clock < arity - saved.length) :
    ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) ∧
    evaluatePost s { s with clock := 0 } t (targetArgs ++ [target] ++ rest) f
      (.err (.abort .timeoutError))
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, targetEq, envRel', oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity index captured saved functions body target found savedNonempty related
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  have sourceTimeout : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
    rw [evaluateApp_recclosure_over s ptr arity index captured saved args functions body found savedBound bound over]
    simp [timeout]
  have oldLength : oldTargets.length = saved.length := oldRel.length_eq.symm
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have savedPositive : 0 < saved.length := List.length_pos_iff.mpr savedNonempty
  let n := targetArgs.length - 1
  let total := arity - 1 - saved.length
  have length : targetArgs.length = n + 1 := by dsimp [n]; omega
  have over' : total < n := by dsimp [total, n]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have nBound : n < s.maxApp := by dsimp [n]; omega
  have stubPrev : oldTargets.length - 1 < arity - 1 := by omega
  have stubTotal : arity - 1 < s.maxApp := by omega
  let start : BvlSem.State C F := { t with clock := s.clock }
  have genericLookup : sptLookup (genericAppFnLocation n) start.code = some (n + 2, generateGenericApp s.maxApp n) :=
    states.2.2.2.2.2.2.2.2.1 n nBound
  have stubLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨stubTotal, stubPrev⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = total + 2 := by dsimp [total]; omega
    simpa [start, count] using installed
  have targetRun := evaluate_mkClCall_over_step start s.maxApp n total 31
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) targetArgs (original :: oldTargets) rest
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) length over' totalBound genericLookup stubLookup
  have targetTimeout : start.clock < total + 2 := by dsimp [start, total]; omega
  simp only [if_pos targetTimeout] at targetRun
  refine ⟨sourceTimeout, 0, .err (.abort .timeoutError), { t with clock := 0 }, f, ?_, ?_, ?_, ?_, ?_, annotations, rfl⟩
  · rw [targetEq]
    simpa [start, total] using targetRun
  · simp [resultRel, excRel]
  · exact (stateRel_clock f s t 0).2.mpr ((stateRel_clock f s t 0).1.mpr states)
  · intro key value mapped; exact mapped
  · intro key value mapped fresh; exact ⟨mapped, fresh⟩

/-- Compose the saturated target body with the generated overapplication
continuation. The continuation hypothesis is the application simulation for
the returned value and the remaining arguments; the body and continuation
postconditions supply their own target clocks and state extensions. -/
theorem evaluatePost_mkClCall_over_compose {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (n total tag address : Nat)
    (args fields rest : List BvlSem.Value) (body : Bvl.Exp) (value : ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (length : args.length = n + 1) (over : total < n) (totalBound : total < s.maxApp)
    (genericLookup : sptLookup (genericAppFnLocation n) t.code = some (n + 2, generateGenericApp s.maxApp n))
    (lookup : sptLookup address t.code = some (total + 2, body))
    (enough : total + 1 ≤ s.clock) (maxAppEq : sMiddle.maxApp = s.maxApp)
    (bodyPost : evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (args.drop (n - total) ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
      f (.val [value]) [body])
    (continuationIH : ∀ (targetValue : BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat),
      stateRel fMiddle sMiddle tMiddle →
      vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code value targetValue →
      f.submap fMiddle → unmappedRefsSubmap t.refs tMiddle.refs f fMiddle →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle
        (targetValue :: .number (Int.ofNat total) :: .number (Int.ofNat total - Int.ofNat (n + 1)) ::
          (args ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)]))
        fMiddle result [mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3))]) :
    evaluatePost s sFinal t
      (args ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)] ++ rest) f result
      [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)] := by
  obtain ⟨clock1, targetResult, tMiddle, fMiddle, bodyRun, bodyRel, states1, map1, refs1,
    annotations1, clocks1⟩ := bodyPost
  cases targetResult with
  | err error => simp [resultRel] at bodyRel
  | val targetValues =>
    have singleton : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        [value] targetValues := by simpa [resultRel, ClosSem.decClock, maxAppEq] using bodyRel
    cases singleton with
    | @cons _ targetValue _ _ valueRel tail =>
      cases tail
      have growth : sptSubspt t.code tMiddle.code := by
        exact BvlProps.evaluateMono [body]
          (args.drop (n - total) ++ [BvlSem.Value.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
          { t with clock := (ClosSem.decClock (total + 1) s).clock + clock1 }
          (.val [targetValue]) tMiddle bodyRun
      obtain ⟨clock2, targetFinal, tFinal, fFinal, continuationRun, resultRel, states2, map2,
        refs2, annotations2, clocks2⟩ :=
          continuationIH targetValue tMiddle fMiddle states1 valueRel map1 refs1 annotations1 growth
      have shiftedBody := BvlProps.evaluate_addClock [body]
        (args.drop (n - total) ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
        { t with clock := (ClosSem.decClock (total + 1) s).clock + clock1 }
        tMiddle (.val [targetValue]) clock2 bodyRun (by simp)
      have bodyShifted : BvlSem.evaluate [body]
          (args.drop (n - total) ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
          (BvlSem.decClock (total + 2) { t with clock := s.clock + (clock1 + clock2 + 1) }) =
          (.val [targetValue], { tMiddle with clock := sMiddle.clock + clock2 }) := by
        have clockEq : s.clock + (clock1 + clock2 + 1) - (total + 2) =
            (s.clock - (total + 1) + clock1) + clock2 := by omega
        simpa [BvlSem.decClock, ClosSem.decClock, clockEq, clocks1] using shiftedBody
      refine ⟨clock1 + clock2 + 1, targetFinal, tFinal, fFinal, ?_, ?_, states2,
        HolFiniteMapExact.submap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2, annotations2, clocks2⟩
      · rw [evaluate_mkClCall_over_step _ s.maxApp n total tag address args fields rest body length over totalBound
          (by simpa using genericLookup) (by simpa using lookup)]
        have targetEnough : ¬s.clock + (clock1 + clock2 + 1) < total + 2 := by omega
        simp only [targetEnough, ↓reduceIte, bodyShifted]
        simpa using continuationRun
      · simpa [maxAppEq] using resultRel

/-- The first saturated body of an overapplied ordinary closure satisfies the
expression simulation on the related suffixes of the source and target
arguments. The target entry reads its captured values from the closure block. -/
theorem evaluatePost_ordinary_over_body {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n : Nat) (captured args : List ClosSem.Value) (fields targetArgs : List BvlSem.Value)
    (body : ClosLang.Exp) (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (over : arity < args.length)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    ∃ targetBody,
      sptLookup (ptr + numStubs s.maxApp) t.code = some (arity + 1,
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) ∧
      evaluatePost (ClosSem.decClock arity s) sMiddle t
        (targetArgs.drop (n - (arity - 1)) ++
          [.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)])
        f bodyResult
        [.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody] := by
  cases closure with
  | @closure _ _ aux targetBody aux1 _ _ _ arityBound positive locations vars compiled installed lookup =>
    let sourceSuffix := args.drop (args.length - arity)
    let targetSuffix := targetArgs.drop (n - (arity - 1))
    let targetClosure := BvlSem.Value.block 30
      (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)
    have ⟨_, _, suffixRel⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
      arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
    have relatedSuffix : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix := by
      simpa [sourceSuffix, targetSuffix] using suffixRel
    have suffixLength : targetSuffix.length = arity := by
      dsimp [targetSuffix]
      simp only [List.length_drop, length]
      omega
    have fieldsLength : fields.length = captured.length := capturedRel.length_eq.symm
    have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
      exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
    have bodyEnv : envRel s.maxApp f t.refs t.code (sourceSuffix ++ captured)
        ((targetSuffix ++ fields) ++ targetSuffix ++ [targetClosure]) := by
      have tail : envRel s.maxApp f t.refs t.code captured (fields ++ targetSuffix ++ [targetClosure]) := by
        simpa using envRel_prepend capturedRel (env := []) (targetEnv := targetSuffix ++ [targetClosure]) (by simp [envRel])
      simpa [List.append_assoc] using envRel_prepend relatedSuffix tail
    have bodyPost := bodyIH (ClosSem.decClock arity s) sMiddle t (sourceSuffix ++ captured)
      ((targetSuffix ++ fields) ++ targetSuffix ++ [targetClosure]) f aux aux1 [targetBody] bodyResult
      (by simpa [sourceSuffix] using bodyRun) noType (by simpa [ClosSem.decClock] using compiled)
      locations (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
      (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
    obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
      finalAnnotations, finalClock⟩ := bodyPost
    refine ⟨_, lookup, clock, targetResult, tFinal, fFinal, ?_, resultRel, finalStates, map, frame,
      finalAnnotations, finalClock⟩
    have entry := evaluate_closure_entry { t with clock := (ClosSem.decClock arity s).clock + clock }
      targetSuffix fields 30 (.codePtr (ptr + numStubs s.maxApp)) (.number (Int.ofNat (arity - 1))) targetBody
    simpa [targetSuffix, targetClosure, suffixLength, fieldsLength] using entry.trans targetRun

/-- An overapplied ordinary closure whose first body returns a value follows
from the body simulation and the simulation of the remaining application.
The continuation hypothesis is stated at the generated continuation's
environment, while the source execution supplies its application result. -/
theorem evaluateApp_ordinary_over_success {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (ptr arity n : Nat)
    (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (value : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length) (enough : arity ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) = (.val [value], sMiddle))
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : ∀ (targetValue : BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat),
      ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle = (result, sFinal) →
      stateRel fMiddle sMiddle tMiddle →
      vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code value targetValue →
      f.submap fMiddle → unmappedRefsSubmap t.refs tMiddle.refs f fMiddle →
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
      evaluatePost sMiddle sFinal tMiddle
        (targetValue :: .number (Int.ofNat (arity - 1)) ::
          .number (Int.ofNat (arity - 1) - Int.ofNat (n + 1)) ::
          (targetArgs ++ [.block 30 (.codePtr (ptr + numStubs s.maxApp) ::
            .number (Int.ofNat (arity - 1)) :: fields)]))
        fMiddle result [mkClCall (.var 0) ((List.range (n - (arity - 1))).map fun i => .var (i + 3))]) :
    evaluatePost s sFinal t
      (targetArgs ++ [.block 30 (.codePtr (ptr + numStubs s.maxApp) ::
        .number (Int.ofNat (arity - 1)) :: fields)] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : arity - 1 < n := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have cost : arity - 1 + 1 = arity := by omega
  have lookupSize : arity - 1 + 2 = arity + 1 := by omega
  have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle =
      (result, sFinal) := by
    rw [evaluateApp_ordinary_over s ptr arity captured [] args body (by simp; omega) bound (by simpa using over)] at appRun
    simp only [List.length_nil, Nat.sub_zero, List.append_nil,
      Nat.not_lt.mpr enough, ↓reduceIte] at appRun
    rw [ClosSem.fixClock_evaluate, bodyRun] at appRun
    exact appRun
  have maxAppEq : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
      (args.drop (args.length - arity) ++ captured) (ClosSem.decClock arity s)
    rw [bodyRun] at h
    simpa [ClosSem.decClock] using h
  obtain ⟨targetBody, lookup, bodyPost⟩ := evaluatePost_ordinary_over_body s sMiddle t f ptr arity n
    captured args fields targetArgs body (.val [value]) states annotations closure capturedRel argsRel length over bodyRun (by simp) bodyIH
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  apply evaluatePost_mkClCall_over_compose s sMiddle sFinal t f n (arity - 1) 30
    (ptr + numStubs s.maxApp) targetArgs fields rest
    (.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody)
    value result length over' totalBound genericLookup (by simpa [lookupSize] using lookup)
    (by simpa [cost] using enough) maxAppEq (by simpa [cost] using bodyPost)
  intro targetValue tMiddle fMiddle statesMiddle valueRel map refs annotationsMiddle growth
  exact continuationIH targetValue tMiddle fMiddle sourceContinue statesMiddle valueRel map refs annotationsMiddle growth

/-- A generated closure call depends on its argument expressions and closure
expression only through their values and the number of arguments, provided
those expressions evaluate without changing the state. -/
theorem evaluate_mkClCall_congr {C F : Type} (s : BvlSem.State C F)
    (env1 env2 : List BvlSem.Value) (cl1 cl2 : Bvl.Exp) (args1 args2 : List Bvl.Exp)
    (closure : BvlSem.Value) (values : List BvlSem.Value)
    (length : args1.length = args2.length)
    (clRun1 : ∀ u : BvlSem.State C F, BvlSem.evaluate [cl1] env1 u = (.val [closure], u))
    (clRun2 : ∀ u : BvlSem.State C F, BvlSem.evaluate [cl2] env2 u = (.val [closure], u))
    (argsRun1 : ∀ u : BvlSem.State C F, BvlSem.evaluate args1 env1 u = (.val values, u))
    (argsRun2 : ∀ u : BvlSem.State C F, BvlSem.evaluate args2 env2 u = (.val values, u)) :
    BvlSem.evaluate [mkClCall cl1 args1] env1 s = BvlSem.evaluate [mkClCall cl2 args2] env2 s := by
  have elemEq (u : BvlSem.State C F) (i : Nat) :
      BvlSem.evaluate [.op (.blockOp (.elemAt i)) [cl1]] env1 u =
      BvlSem.evaluate [.op (.blockOp (.elemAt i)) [cl2]] env2 u := by
    rw [BvlSem.evaluate, BvlSem.evaluate, BvlSem.fixClock_evaluate, BvlSem.fixClock_evaluate, clRun1, clRun2]
  have condEq : BvlSem.evaluate
      [.op (.blockOp (.equalConst (.int (Int.ofNat (args1.length - 1)))))
        [.op (.blockOp (.elemAt 1)) [cl1]]] env1 s =
      BvlSem.evaluate
      [.op (.blockOp (.equalConst (.int (Int.ofNat (args2.length - 1)))))
        [.op (.blockOp (.elemAt 1)) [cl2]]] env2 s := by
    rw [← length]
    conv_lhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
    conv_rhs => rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
    rw [elemEq]
  have tailEq (u : BvlSem.State C F) : BvlSem.evaluate [cl1, .op (.blockOp (.elemAt 0)) [cl1]] env1 u =
      BvlSem.evaluate [cl2, .op (.blockOp (.elemAt 0)) [cl2]] env2 u := by
    rw [BvlSem.evaluate, BvlSem.evaluate, BvlSem.fixClock_evaluate, BvlSem.fixClock_evaluate, clRun1, clRun2]
    rw [elemEq]
  have argsDirectEq (u : BvlSem.State C F) :
      BvlSem.evaluate (args1 ++ [cl1, .op (.blockOp (.elemAt 0)) [cl1]]) env1 u =
      BvlSem.evaluate (args2 ++ [cl2, .op (.blockOp (.elemAt 0)) [cl2]]) env2 u := by
    change BvlSem.evaluateTuple (_, env1, u) = BvlSem.evaluateTuple (_, env2, u)
    rw [BvlProps.evaluateAppend, BvlProps.evaluateAppend]
    simp only [BvlSem.evaluateTuple, argsRun1, argsRun2, tailEq]
  have argsGenericEq (u : BvlSem.State C F) : BvlSem.evaluate (args1 ++ [cl1]) env1 u =
      BvlSem.evaluate (args2 ++ [cl2]) env2 u := by
    change BvlSem.evaluateTuple (_, env1, u) = BvlSem.evaluateTuple (_, env2, u)
    rw [BvlProps.evaluateAppend, BvlProps.evaluateAppend]
    simp only [BvlSem.evaluateTuple, argsRun1, argsRun2, clRun1, clRun2]
  change BvlSem.evaluate [.ifThenElse
    (.op (.blockOp (.equalConst (.int (Int.ofNat (args1.length - 1))))) [.op (.blockOp (.elemAt 1)) [cl1]])
    (.call (args1.length - 1) none (args1 ++ [cl1, .op (.blockOp (.elemAt 0)) [cl1]]))
    (.call 0 (some (genericAppFnLocation (args1.length - 1))) (args1 ++ [cl1]))] env1 s =
    BvlSem.evaluate [.ifThenElse
    (.op (.blockOp (.equalConst (.int (Int.ofNat (args2.length - 1))))) [.op (.blockOp (.elemAt 1)) [cl2]])
    (.call (args2.length - 1) none (args2 ++ [cl2, .op (.blockOp (.elemAt 0)) [cl2]]))
    (.call 0 (some (genericAppFnLocation (args2.length - 1))) (args2 ++ [cl2]))] env2 s
  rw [← length] at condEq ⊢
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, BvlSem.evaluate, BvlSem.fixClock_evaluate, condEq]
  split <;> simp_all only [BvlSem.evaluate, BvlSem.fixClock_evaluate]

/-- The generated overapplication continuation and a canonical closure call
evaluate the same remaining arguments and returned value in any target state. -/
theorem evaluate_overApp_continue_canonical {C F : Type} (s : BvlSem.State C F)
    (n total : Nat) (args rest extra : List BvlSem.Value) (value first second : BvlSem.Value)
    (length : args.length = n + 1) (over : total < n) :
    BvlSem.evaluate [mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3))]
      (value :: first :: second :: (args ++ rest)) s =
    BvlSem.evaluate [mkClCall (.var (args.take (n - total)).length)
      ((List.range (args.take (n - total)).length).map Bvl.Exp.var)]
      (args.take (n - total) ++ [value] ++ extra) s := by
  let remaining := args.take (n - total)
  have remainingLength : remaining.length = n - total := by
    dsimp [remaining]
    simp [List.length_take]
    omega
  apply evaluate_mkClCall_congr s _ _ _ _ _ _ value remaining
  · simp only [List.length_map, List.length_range, List.length_take]
    omega
  · intro u
    simp [BvlSem.evaluate]
  · intro u
    simp [BvlSem.evaluate, Nat.min_eq_left (by omega : n - total ≤ args.length)]
  · intro u
    have bound : (n - total) + 3 ≤ (value :: first :: second :: (args ++ rest)).length := by
      simp only [List.length_cons, List.length_append]
      omega
    simpa [BvlSem.evaluateTuple, List.take_append_of_le_length (by omega : n - total ≤ args.length)] using
      BvlProps.evaluateGenlistVars 3 (value :: first :: second :: (args ++ rest)) (n - total) u bound
  · intro u
    have bound : remaining.length ≤ (remaining ++ [value] ++ extra).length := by simp
    change BvlSem.evaluate ((List.range remaining.length).map Bvl.Exp.var)
      (remaining ++ [value] ++ extra) u = (.val remaining, u)
    simpa [BvlSem.evaluateTuple] using BvlProps.evaluateGenlistVars 0 (remaining ++ [value] ++ extra) remaining.length u bound

/-- Lift the canonical remaining-call simulation to the environment used by
the generated overapplication continuation. -/
theorem evaluatePost_overApp_continue_canonical {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (n total : Nat) (args rest extra : List BvlSem.Value) (value first second : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (length : args.length = n + 1) (over : total < n)
    (post : evaluatePost s sFinal t (args.take (n - total) ++ [value] ++ extra) f result
      [mkClCall (.var (args.take (n - total)).length)
        ((List.range (args.take (n - total)).length).map Bvl.Exp.var)]) :
    evaluatePost s sFinal t (value :: first :: second :: (args ++ rest)) f result
      [mkClCall (.var 0) ((List.range (n - total)).map fun i => .var (i + 3))] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, states, map, frame, annotations, clocks⟩ := post
  refine ⟨clock, targetResult, tFinal, fFinal, ?_, related, states, map, frame, annotations, clocks⟩
  rw [evaluate_overApp_continue_canonical _ n total args rest extra value first second length over]
  exact run

/-- Successful ordinary overapplication follows from the closure-body
simulation and the ordinary application simulation for the remaining prefix. -/
theorem evaluateApp_ordinary_over_success_canonical {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (ptr arity n : Nat)
    (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (value : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length) (enough : arity ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) = (.val [value], sMiddle))
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : ∀ (targetValue : BvlSem.Value) (tMiddle : BvlSem.State C F)
      (fMiddle : HolFiniteMapExact Nat Nat),
      ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle = (result, sFinal) →
      stateRel fMiddle sMiddle tMiddle →
      vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code value targetValue →
      List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) →
      codeAnnotations sMiddle →
      evaluatePost sMiddle sFinal tMiddle
        (targetArgs.take (n - (arity - 1)) ++ [targetValue]) fMiddle result
        [mkClCall (.var (targetArgs.take (n - (arity - 1))).length)
          ((List.range (targetArgs.take (n - (arity - 1))).length).map Bvl.Exp.var)]) :
    evaluatePost s sFinal t
      (targetArgs ++ [.block 30 (.codePtr (ptr + numStubs s.maxApp) ::
        .number (Int.ofNat (arity - 1)) :: fields)] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have positive : arity ≠ 0 := by cases closure with | closure _ positive _ _ _ _ _ => exact positive
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have over' : arity - 1 < n := by omega
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have prefixRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by
    simpa using prefixRel
  have maxAppEq : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
      (args.drop (args.length - arity) ++ captured) (ClosSem.decClock arity s)
    rw [bodyRun] at h
    simpa [ClosSem.decClock] using h
  apply evaluateApp_ordinary_over_success s sMiddle sFinal t f ptr arity n captured args fields targetArgs rest
    body value result states annotations closure capturedRel argsRel length bound over enough bodyRun appRun bodyIH
  intro targetValue tMiddle fMiddle sourceRun statesMiddle valueRel map refs annotationsMiddle growth
  have grown : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
      (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by
    apply prefixRel'.imp
    intro x y related
    simpa [maxAppEq] using vRel_grow related map refs growth
  have post := continuationIH targetValue tMiddle fMiddle sourceRun statesMiddle valueRel grown annotationsMiddle
  have post' : evaluatePost sMiddle sFinal tMiddle
      (targetArgs.take (n - (arity - 1)) ++ [targetValue] ++ []) fMiddle result
      [mkClCall (.var (targetArgs.take (n - (arity - 1))).length)
        ((List.range (targetArgs.take (n - (arity - 1))).length).map Bvl.Exp.var)] := by simpa using post
  exact evaluatePost_overApp_continue_canonical sMiddle sFinal tMiddle fMiddle n (arity - 1) targetArgs
    [.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)] []
    targetValue (.number (Int.ofNat (arity - 1))) (.number (Int.ofNat (arity - 1) - Int.ofNat (n + 1)))
    result length over' post'

/-- Errors from the first saturated target body propagate through the
overapplication stub, without running the remaining application. -/
theorem evaluatePost_mkClCall_over_error {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (n total tag address : Nat)
    (args fields rest : List BvlSem.Value) (body : Bvl.Exp) (error : ErrorResult ClosSem.Value)
    (length : args.length = n + 1) (over : total < n) (totalBound : total < s.maxApp)
    (genericLookup : sptLookup (genericAppFnLocation n) t.code = some (n + 2, generateGenericApp s.maxApp n))
    (lookup : sptLookup address t.code = some (total + 2, body)) (enough : total + 1 ≤ s.clock)
    (bodyPost : evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (args.drop (n - total) ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
      f (.err error) [body]) :
    evaluatePost s sMiddle t
      (args ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)] ++ rest) f (.err error)
      [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, bodyRun, related, finalStates, map, frame,
    annotations, clocks⟩ := bodyPost
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock + 1, .err targetError, tFinal, fFinal, ?_, ?_, finalStates, map, frame, annotations, clocks⟩
    · rw [evaluate_mkClCall_over_step _ s.maxApp n total tag address args fields rest body length over totalBound
        (by simpa using genericLookup) (by simpa using lookup)]
      have targetEnough : ¬s.clock + (clock + 1) < total + 2 := by omega
      simp only [targetEnough, ↓reduceIte]
      have clockEq : s.clock + (clock + 1) - (total + 2) = s.clock - (total + 1) + clock := by omega
      have bodyRun' := bodyRun
      simp only [BvlSem.decClock, ClosSem.decClock, clockEq] at bodyRun' ⊢
      rw [bodyRun']
    · simpa [ClosSem.decClock] using related

/-- If an overapplied ordinary closure's first body raises an error, the
compiled call propagates the corresponding error and state. -/
theorem evaluateApp_ordinary_over_error {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (error : ErrorResult ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length) (enough : arity ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) = (.err error, sMiddle))
    (noType : error ≠ .abort .typeError) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (.err error, sMiddle) ∧
    evaluatePost s sMiddle t
      (targetArgs ++ [.block 30 (.codePtr (ptr + numStubs s.maxApp) ::
        .number (Int.ofNat (arity - 1)) :: fields)] ++ rest) f (.err error)
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : arity - 1 < n := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have cost : arity - 1 + 1 = arity := by omega
  have lookupSize : arity - 1 + 2 = arity + 1 := by omega
  have sourceError : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
      (.err error, sMiddle) := by
    rw [evaluateApp_ordinary_over s ptr arity captured [] args body (by simp; omega) bound (by simpa using over)]
    simp only [List.length_nil, Nat.sub_zero, List.append_nil, Nat.not_lt.mpr enough, ↓reduceIte]
    rw [ClosSem.fixClock_evaluate, bodyRun]
  obtain ⟨targetBody, lookup, bodyPost⟩ := evaluatePost_ordinary_over_body s sMiddle t f ptr arity n
    captured args fields targetArgs body (.err error) states annotations closure capturedRel argsRel length over bodyRun
    (by simpa using noType) bodyIH
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  refine ⟨sourceError, ?_⟩
  exact evaluatePost_mkClCall_over_error s sMiddle t f n (arity - 1) 30 (ptr + numStubs s.maxApp)
    targetArgs fields rest (.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody)
    error length over' totalBound genericLookup (by simpa [lookupSize] using lookup)
    (by simpa [cost] using enough) (by simpa [cost] using bodyPost)

/-- With enough clock for the first saturated call, ordinary overapplication
either propagates a body error or continues using the returned singleton value.
The only recursive application premise is the canonical remaining-call
simulation. -/
theorem evaluateApp_ordinary_over_enough {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (bound : args.length ≤ s.maxApp)
    (over : arity < args.length) (enough : arity ≤ s.clock)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : ∀ (value : ClosSem.Value) (sMiddle : ClosSem.State C F),
      ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
        (ClosSem.decClock arity s) = (.val [value], sMiddle) →
      ∀ (targetValue : BvlSem.Value) (tMiddle : BvlSem.State C F) (fMiddle : HolFiniteMapExact Nat Nat),
      ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle = (result, sFinal) →
      stateRel fMiddle sMiddle tMiddle →
      vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code value targetValue →
      List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
        (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) →
      codeAnnotations sMiddle →
      evaluatePost sMiddle sFinal tMiddle
        (targetArgs.take (n - (arity - 1)) ++ [targetValue]) fMiddle result
        [mkClCall (.var (targetArgs.take (n - (arity - 1))).length)
          ((List.range (targetArgs.take (n - (arity - 1))).length).map Bvl.Exp.var)]) :
    evaluatePost s sFinal t
      (targetArgs ++ [.block 30 (.codePtr (ptr + numStubs s.maxApp) ::
        .number (Int.ofNat (arity - 1)) :: fields)] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have positive : arity ≠ 0 := by cases closure with | closure _ positive _ _ _ _ _ => exact positive
  cases bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult sMiddle =>
    cases bodyResult with
    | err error =>
      have sourceError : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
          (.err error, sMiddle) := by
        rw [evaluateApp_ordinary_over s ptr arity captured [] args body (by simp; omega) bound (by simpa using over)]
        simp only [List.length_nil, Nat.sub_zero, List.append_nil, Nat.not_lt.mpr enough, ↓reduceIte]
        rw [ClosSem.fixClock_evaluate, bodyRun]
      have equal := appRun.symm.trans sourceError
      cases equal
      have errorNoType : error ≠ .abort .typeError := by simpa using noType
      exact (evaluateApp_ordinary_over_error s sFinal t f ptr arity n captured args fields targetArgs rest
        body error states annotations closure capturedRel argsRel length bound over enough bodyRun errorNoType bodyIH).2
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - arity) ++ captured) (ClosSem.decClock arity s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          exact evaluateApp_ordinary_over_success_canonical s sMiddle sFinal t f ptr arity n
            captured args fields targetArgs rest body value result states annotations closure capturedRel argsRel
            length bound over enough bodyRun appRun bodyIH (continuationIH value sMiddle bodyRun)

/-- Candidate application simulation for a fixed source argument list. This
Flapjack induction predicate is untagged while the evaluator and state
relations await their HOL correspondence review. -/
def applicationSimulation {C F : Type} (args : List ClosSem.Value) : Prop :=
  args ≠ [] → ∀ (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (value : ClosSem.Value) (targetValue : BvlSem.Value) (targetArgs rest : List BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value),
    ClosSem.evaluateApp none value args s = (result, sFinal) → result ≠ .err (.abort .typeError) →
    stateRel f s t → codeAnnotations s → vRel s.maxApp f t.refs t.code value targetValue →
    List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs →
    evaluatePost s sFinal t (targetArgs ++ [targetValue] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]

/-- All clock outcomes for an overapplied, previously unapplied ordinary
closure follow from its body simulation and application simulation for the
strictly shorter remaining argument prefix. -/
theorem evaluateApp_ordinary_over_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F) (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · obtain ⟨fields, capturedRel, closure⟩ := vRel_ordinary_closure functionRel
    have targetEq : target = .block 30
        (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
      cases closure with | closure _ _ _ _ _ _ _ => rfl
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    rw [targetEq]
    apply evaluateApp_ordinary_over_enough s sFinal t f ptr arity n captured args fields targetArgs rest
      body result states annotations (by simpa [targetEq] using closure) capturedRel argsRel length bound over enough
      appRun noType bodyIH
    intro value sMiddle bodyRun targetValue tMiddle fMiddle sourceRun statesMiddle valueRel remainingRel annotationsMiddle
    have post := continuationIH (by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega) sMiddle sFinal tMiddle fMiddle value targetValue
      (targetArgs.take (n - (arity - 1))) [] result sourceRun noType statesMiddle annotationsMiddle valueRel remainingRel
    simpa using post
  · have timeout : s.clock < arity := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_over_timeout s t f ptr arity captured args
      targetArgs rest body target states annotations functionRel argsRel bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Peel a saturated direct closure call from an evaluation postcondition.
When the source has enough clock, the postcondition applies to the installed
target entry at the corresponding decremented source clock. -/
theorem evaluatePost_mkClCall_direct_body {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (args rest fields : List BvlSem.Value) (tag ptr : Nat) (body : Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value) (nonempty : args ≠ [])
    (lookup : sptLookup ptr t.code = some (args.length + 1, body)) (enough : args.length ≤ s.clock)
    (post : evaluatePost s sFinal t
      (args ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields)] ++ rest) f result
      [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)]) :
    evaluatePost (ClosSem.decClock args.length s) sFinal t
      (args ++ [.block tag (.codePtr ptr :: .number (Int.ofNat (args.length - 1)) :: fields)]) f result [body] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, callRun, related, states, map, frame, annotations, clocks⟩ := post
  have shiftedLookup : sptLookup ptr { t with clock := s.clock + clock }.code = some (args.length + 1, body) := by
    simpa using lookup
  have targetCall := evaluate_mkClCall_direct_env { t with clock := s.clock + clock } args rest tag ptr fields body
    nonempty shiftedLookup
  have targetEnough : ¬s.clock + clock < args.length := by omega
  simp only [targetEnough, ↓reduceIte] at targetCall
  have clockEq : s.clock + clock - args.length = s.clock - args.length + clock := by omega
  refine ⟨clock, targetResult, tFinal, fFinal, ?_, ?_, states, map, frame, annotations, clocks⟩
  · rw [targetCall] at callRun
    simpa [BvlSem.decClock, ClosSem.decClock, clockEq] using callRun
  · simpa [ClosSem.decClock] using related

/-- The saturated suffix of an overapplied ordinary partial closure runs the
installed partial-closure entry with the saved arguments and original closure. -/
theorem evaluatePost_ordinary_partial_over_body {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n : Nat) (captured saved args : List ClosSem.Value)
    (fields oldTargets targetArgs : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (over : arity < args.length + saved.length) (enough : arity - saved.length ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
      (ClosSem.decClock (arity - saved.length) s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    sptLookup stub t.code = some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) ∧
    evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (targetArgs.drop (n - total) ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)])
      f bodyResult [generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  let sourceSuffix := args.drop (args.length - (arity - saved.length))
  let targetSuffix := targetArgs.drop (n - total)
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  obtain ⟨savedLength, savedPositive, relatedSuffix, sourceLength, targetLength⟩ :=
    overAppSuffixFacts s t f arity n total saved args oldTargets targetArgs sourceSuffix
      targetSuffix savedRel argsRel length savedNonempty savedBound rfl over rfl rfl
  have sourceNonempty : sourceSuffix ≠ [] := by
    intro empty
    simp [empty] at sourceLength
    omega
  have targetNonempty : targetSuffix ≠ [] := by
    intro empty
    simp [empty] at targetLength
    omega
  have arityMatch : sourceSuffix.length + saved.length = arity := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup : sptLookup stub t.code =
      some (targetSuffix.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨totalBound, previousBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = targetSuffix.length + 1 := by omega
    simpa [stub, count] using installed
  have saturatedPost := evaluatePost_ordinary_partial_exact s sMiddle t f ptr arity captured saved sourceSuffix
    fields oldTargets targetSuffix [] body original states annotations closure capturedRel savedRel relatedSuffix
    savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) bodyResult
    (by simpa [sourceSuffix, sourceLength] using bodyRun) noType bodyIH
  have entryPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] (original :: oldTargets) 31 stub
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) bodyResult targetNonempty stubLookup
    (by simpa [targetLength] using enough) (by simpa [stub] using saturatedPost)
  have count : targetSuffix.length - 1 = total := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have lookupSize : targetSuffix.length + 1 = total + 2 := by dsimp [total]; omega
  rw [count, targetLength] at entryPost
  exact ⟨by simpa [lookupSize] using stubLookup, by simpa [targetSuffix, total, stub, cost] using entryPost⟩

/-- With enough clock, overapplication of an ordinary partial closure
simulates either a first-body error or the remaining application. -/
theorem evaluateApp_ordinary_partial_over_enough {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n : Nat) (captured saved args : List ClosSem.Value)
    (fields oldTargets targetArgs rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (enough : arity - saved.length ≤ s.clock)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F)
      (args.take (args.length - (arity - saved.length)))) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    evaluatePost s sFinal t (targetArgs ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] ++ rest)
      f result [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  have arityBound : arity ≤ s.maxApp := by cases closure with | closure bound _ _ _ _ _ _ => exact bound
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : total < n := by dsimp [total]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity saved.length n total argsRel length savedBound rfl over
  cases bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
      (ClosSem.decClock (arity - saved.length) s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_ordinary_over s ptr arity captured saved args body savedBound bound over]
      simp only [Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_ordinary_partial_over_body s sFinal t f ptr arity n
        captured saved args fields oldTargets targetArgs body original (.err error) states annotations closure capturedRel
        savedRel argsRel length savedNonempty savedBound over enough bodyRun errorNoType bodyIH
      exact evaluatePost_mkClCall_over_error s sFinal t f n total 31 stub targetArgs (original :: oldTargets) rest
        (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) error length over' totalBound
        genericLookup stubLookup (by simpa [cost] using enough) bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
          (ClosSem.decClock (arity - saved.length) s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
              (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_ordinary_partial_over_body s sMiddle t f ptr arity n
            captured saved args fields oldTargets targetArgs body original (.val [value]) states annotations closure capturedRel
            savedRel argsRel length savedNonempty savedBound over enough bodyRun (by simp) bodyIH
          apply evaluatePost_mkClCall_over_compose s sMiddle sFinal t f n total 31 stub targetArgs
            (original :: oldTargets) rest (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1))
            value result length over' totalBound genericLookup stubLookup (by simpa [cost] using enough) maxAppEq bodyPost
          intro targetValue tMiddle fMiddle statesMiddle valueRel map refs annotationsMiddle growth
          have grown : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
              (args.take (args.length - (arity - saved.length))) (targetArgs.take (n - total)) := by
            apply prefixRel.imp
            intro x y related
            simpa [maxAppEq] using vRel_grow related map refs growth
          have post := continuationIH (by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega) sMiddle sFinal tMiddle fMiddle value targetValue
            (targetArgs.take (n - total)) [] result sourceContinue noType statesMiddle annotationsMiddle valueRel grown
          have post' : evaluatePost sMiddle sFinal tMiddle (targetArgs.take (n - total) ++ [targetValue] ++ [])
              fMiddle result [mkClCall (.var (targetArgs.take (n - total)).length)
                ((List.range (targetArgs.take (n - total)).length).map Bvl.Exp.var)] := by simpa using post
          exact evaluatePost_overApp_continue_canonical sMiddle sFinal tMiddle fMiddle n total targetArgs
            [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] []
            targetValue (.number (Int.ofNat total)) (.number (Int.ofNat total - Int.ofNat (n + 1)))
            result length over' post'

/-- Overapplication of a related ordinary partial closure simulates all clock
outcomes, assuming the body and the strictly shorter remaining application. -/
theorem evaluateApp_ordinary_partial_over_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) saved captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F)
      (args.take (args.length - (arity - saved.length)))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity - saved.length ≤ s.clock
  · obtain ⟨oldTargets, original, targetEq, originalRel, savedRel⟩ :=
      vRel_ordinary_partial_existing s t f ptr arity captured saved body target savedNonempty functionRel
    obtain ⟨fields, capturedRel, closure⟩ := vRel_ordinary_closure originalRel
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    have totalEq : arity - 1 - saved.length = arity - saved.length - 1 := by omega
    rw [targetEq]
    simpa [totalEq] using evaluateApp_ordinary_partial_over_enough s sFinal t f ptr arity n captured saved args
      fields oldTargets targetArgs rest body original result states annotations closure capturedRel savedRel argsRel
      length savedNonempty savedBound bound over enough appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity - saved.length := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_partial_over_timeout s t f ptr arity captured saved args
      targetArgs rest body target states annotations functionRel argsRel savedNonempty savedBound bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- The remaining argument prefix of an overapplied partial closure is
strictly shorter because at least one new argument is consumed. -/
theorem ordinary_partial_over_remaining_length (arity : Nat) (saved args : List ClosSem.Value)
    (savedBound : saved.length < arity) (over : arity < args.length + saved.length) :
    (args.take (args.length - (arity - saved.length))).length < args.length := by
  simp only [List.length_take]
  omega

/-- The saturated suffix of an overapplied recursive closure runs its
installed target entry with the same result as the selected source body. -/
theorem evaluatePost_recclosure_over_body {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n : Nat) (captured args : List ClosSem.Value) (targetArgs : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body))
    (length : targetArgs.length = n + 1) (over : arity < args.length) (enough : arity ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    ∃ address payload entry,
      target = .block 30 (.codePtr address :: .number (Int.ofNat (arity - 1)) :: payload) ∧
      sptLookup address t.code = some (arity + 1, entry) ∧
      evaluatePost (ClosSem.decClock arity s) sMiddle t (targetArgs.drop (n - (arity - 1)) ++ [target])
        f bodyResult [entry] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original functionRel
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  obtain ⟨address, payload, entry, targetEq, lookup⟩ := clRel_recclosure_target_code closure found
  let sourceSuffix := args.drop (args.length - arity)
  let targetSuffix := targetArgs.drop (n - (arity - 1))
  have ⟨_, _, suffixRel⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have relatedSuffix : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix := by
    simpa [sourceSuffix, targetSuffix] using suffixRel
  have sourceLength : sourceSuffix.length = arity := by
    dsimp [sourceSuffix]
    simp only [List.length_drop]
    omega
  have targetLength : targetSuffix.length = arity := by rw [← sourceLength]; exact relatedSuffix.length_eq.symm
  have sourceNonempty : sourceSuffix ≠ [] := by intro empty; simp [empty] at sourceLength; omega
  have targetNonempty : targetSuffix ≠ [] := by intro empty; simp [empty] at targetLength; omega
  have sourceExact := evaluateApp_recclosure_partial_exact_body s sMiddle ptr index arity captured [] sourceSuffix functions body
    found sourceNonempty (by simp only [List.length_nil]; have h := List.length_pos_iff.mpr sourceNonempty; omega)
    (by omega) (by simpa using sourceLength) (by simpa [sourceLength] using enough) bodyResult
    (by simpa [sourceSuffix, sourceLength] using bodyRun)
  have exactPost : evaluatePost s sMiddle t (targetSuffix ++ [target] ++ []) f bodyResult
      [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    by_cases many : 1 < functions.length
    · exact evaluateApp_mutualRec_exact_related s sMiddle t f ptr index arity captured sourceSuffix targetSuffix []
        functions body target states annotations functionRel relatedSuffix many found sourceLength bodyResult sourceExact noType bodyIH
    · cases closure with
      | singletonRec bound positive locations vars compiled installed lookup =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact evaluateApp_singletonRec_exact_vRel s sMiddle t f ptr _ captured sourceSuffix targetSuffix []
          _ _ states annotations functionRel relatedSuffix sourceLength bodyResult sourceExact noType bodyIH
      | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
  have directPost : evaluatePost s sMiddle t
      (targetSuffix ++ [.block 30 (.codePtr address :: .number (Int.ofNat (targetSuffix.length - 1)) :: payload)] ++ []) f
      bodyResult [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    simpa [targetEq, targetLength] using exactPost
  have directLookup : sptLookup address t.code = some (targetSuffix.length + 1, entry) := by simpa [targetLength] using lookup
  have bodyPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] payload 30 address entry bodyResult
    targetNonempty directLookup (by simpa [targetLength] using enough) directPost
  refine ⟨address, payload, entry, targetEq, lookup, ?_⟩
  simpa [targetSuffix, targetEq, targetLength] using bodyPost

/-- With enough clock, an overapplied recursive closure propagates its first
body error or continues on the remaining argument prefix. -/
theorem evaluateApp_recclosure_over_enough {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length) (enough : arity ≤ s.clock)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F) (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original functionRel
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : arity - 1 < n := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have cost : arity - 1 + 1 = arity := by omega
  have lookupSize : arity - 1 + 2 = arity + 1 := by omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have prefixRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by simpa using prefixRel
  cases bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_recclosure_over s ptr arity index captured [] args functions body found (by simp; omega) bound (by simpa using over)]
      simp only [List.length_nil, Nat.sub_zero, List.append_nil, Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨address, payload, entry, targetEq, lookup, bodyPost⟩ := evaluatePost_recclosure_over_body s sFinal t f
        ptr index arity n captured args targetArgs functions body target (.err error) states annotations functionRel argsRel
        found length over enough bodyRun errorNoType bodyIH
      rw [targetEq]
      apply evaluatePost_mkClCall_over_error s sFinal t f n (arity - 1) 30 address targetArgs payload rest entry error
        length over' totalBound genericLookup (by simpa [lookupSize] using lookup) (by simpa [cost] using enough)
      simpa [targetEq, cost] using bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - arity) ++
            (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
          (ClosSem.decClock arity s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - arity) ++
                (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
              (ClosSem.decClock arity s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨address, payload, entry, targetEq, lookup, bodyPost⟩ := evaluatePost_recclosure_over_body s sMiddle t f
            ptr index arity n captured args targetArgs functions body target (.val [value]) states annotations functionRel argsRel
            found length over enough bodyRun (by simp) bodyIH
          rw [targetEq]
          apply evaluatePost_mkClCall_over_compose s sMiddle sFinal t f n (arity - 1) 30 address targetArgs
            payload rest entry value result length over' totalBound genericLookup (by simpa [lookupSize] using lookup)
            (by simpa [cost] using enough) maxAppEq (by simpa [targetEq, cost] using bodyPost)
          intro targetValue tMiddle fMiddle statesMiddle valueRel map refs annotationsMiddle growth
          have grown : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
              (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by
            apply prefixRel'.imp
            intro x y related
            simpa [maxAppEq] using vRel_grow related map refs growth
          have post := continuationIH (by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega) sMiddle sFinal tMiddle fMiddle value targetValue
            (targetArgs.take (n - (arity - 1))) [] result sourceContinue noType statesMiddle annotationsMiddle valueRel grown
          have post' : evaluatePost sMiddle sFinal tMiddle (targetArgs.take (n - (arity - 1)) ++ [targetValue] ++ [])
              fMiddle result [mkClCall (.var (targetArgs.take (n - (arity - 1))).length)
                ((List.range (targetArgs.take (n - (arity - 1))).length).map Bvl.Exp.var)] := by simpa using post
          exact evaluatePost_overApp_continue_canonical sMiddle sFinal tMiddle fMiddle n (arity - 1) targetArgs
            [.block 30 (.codePtr address :: .number (Int.ofNat (arity - 1)) :: payload)] []
            targetValue (.number (Int.ofNat (arity - 1))) (.number (Int.ofNat (arity - 1) - Int.ofNat (n + 1)))
            result length over' post'

/-- Recursive overapplication simulates both the first-call timeout and the
enough-clock path, with induction on the remaining argument prefix. -/
theorem evaluateApp_recclosure_over_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (bound : args.length ≤ s.maxApp) (over : arity < args.length)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F) (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    exact evaluateApp_recclosure_over_enough s sFinal t f ptr index arity n captured args targetArgs rest functions body target
      result states annotations functionRel argsRel found length bound over enough appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_recclosure_over_timeout s t f ptr arity index captured args
      functions targetArgs rest body target states annotations functionRel argsRel found bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- The saturated suffix of an overapplied recursive partial closure runs the
installed partial-closure entry with the saved arguments and original closure. -/
theorem evaluatePost_recclosure_partial_over_body {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets targetArgs : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (over : arity < args.length + saved.length) (enough : arity - saved.length ≤ s.clock)
    (bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock (arity - saved.length) s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body]) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    sptLookup stub t.code = some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) ∧
    evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (targetArgs.drop (n - total) ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)])
      f bodyResult [generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  let sourceSuffix := args.drop (args.length - (arity - saved.length))
  let targetSuffix := targetArgs.drop (n - total)
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  obtain ⟨savedLength, savedPositive, relatedSuffix, sourceLength, targetLength⟩ :=
    overAppSuffixFacts s t f arity n total saved args oldTargets targetArgs sourceSuffix
      targetSuffix savedRel argsRel length savedNonempty savedBound rfl over rfl rfl
  have sourceNonempty : sourceSuffix ≠ [] := by
    intro empty
    simp [empty] at sourceLength
    omega
  have targetNonempty : targetSuffix ≠ [] := by
    intro empty
    simp [empty] at targetLength
    omega
  have arityMatch : sourceSuffix.length + saved.length = arity := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup : sptLookup stub t.code =
      some (targetSuffix.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨totalBound, previousBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = targetSuffix.length + 1 := by omega
    simpa [stub, count] using installed
  have saturatedPost : evaluatePost s sMiddle t
      (targetSuffix ++ [.block 31 (.codePtr stub :: .number (Int.ofNat (targetSuffix.length - 1)) :: original :: oldTargets)] ++ [])
      f bodyResult [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    by_cases many : 1 < functions.length
    · exact evaluatePost_mutualRec_partial_exact s sMiddle t f ptr index arity captured saved sourceSuffix functions
        fields oldTargets targetSuffix [] body original states annotations closure capturedRel savedRel relatedSuffix
        many found savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) bodyResult
        (by simpa [sourceSuffix, sourceLength] using bodyRun) noType bodyIH
    · cases closure with
      | singletonRec bound positive locations vars compiled installed lookup =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        apply evaluatePost_singletonRec_partial_exact s sMiddle t f ptr _ captured saved sourceSuffix
          fields oldTargets targetSuffix [] _ _ states annotations
          (.singletonRec bound positive locations vars compiled installed lookup) capturedRel savedRel relatedSuffix
          savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) bodyResult
        · simpa [sourceSuffix, sourceLength] using bodyRun
        · exact noType
        · exact bodyIH
      | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
  have entryPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] (original :: oldTargets) 31 stub
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) bodyResult targetNonempty stubLookup
    (by simpa [targetLength] using enough) (by simpa [stub] using saturatedPost)
  have count : targetSuffix.length - 1 = total := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have lookupSize : targetSuffix.length + 1 = total + 2 := by dsimp [total]; omega
  rw [count, targetLength] at entryPost
  exact ⟨by simpa [lookupSize] using stubLookup, by simpa [targetSuffix, total, stub, cost] using entryPost⟩


/-- With enough clock, overapplication of an recursive partial closure
simulates either a first-body error or the remaining application. -/
theorem evaluateApp_recclosure_partial_over_enough {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets targetArgs rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (enough : arity - saved.length ≤ s.clock)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F)
      (args.take (args.length - (arity - saved.length)))) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    evaluatePost s sFinal t (targetArgs ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] ++ rest)
      f result [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity closure found).1
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : total < n := by dsimp [total]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity saved.length n total argsRel length savedBound rfl over
  cases bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock (arity - saved.length) s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_recclosure_over s ptr arity index captured saved args functions body found savedBound bound over]
      simp only [Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_recclosure_partial_over_body s sFinal t f ptr index arity n
        captured saved args functions fields oldTargets targetArgs body original (.err error) states annotations closure capturedRel
        savedRel argsRel found length savedNonempty savedBound over enough bodyRun errorNoType bodyIH
      exact evaluatePost_mkClCall_over_error s sFinal t f n total 31 stub targetArgs (original :: oldTargets) rest
        (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) error length over' totalBound
        genericLookup stubLookup (by simpa [cost] using enough) bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
          (ClosSem.decClock (arity - saved.length) s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
              (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_recclosure_partial_over_body s sMiddle t f ptr index arity n
            captured saved args functions fields oldTargets targetArgs body original (.val [value]) states annotations closure capturedRel
            savedRel argsRel found length savedNonempty savedBound over enough bodyRun (by simp) bodyIH
          apply evaluatePost_mkClCall_over_compose s sMiddle sFinal t f n total 31 stub targetArgs
            (original :: oldTargets) rest (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1))
            value result length over' totalBound genericLookup stubLookup (by simpa [cost] using enough) maxAppEq bodyPost
          intro targetValue tMiddle fMiddle statesMiddle valueRel map refs annotationsMiddle growth
          have grown : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
              (args.take (args.length - (arity - saved.length))) (targetArgs.take (n - total)) := by
            apply prefixRel.imp
            intro x y related
            simpa [maxAppEq] using vRel_grow related map refs growth
          have post := continuationIH (by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega) sMiddle sFinal tMiddle fMiddle value targetValue
            (targetArgs.take (n - total)) [] result sourceContinue noType statesMiddle annotationsMiddle valueRel grown
          have post' : evaluatePost sMiddle sFinal tMiddle (targetArgs.take (n - total) ++ [targetValue] ++ [])
              fMiddle result [mkClCall (.var (targetArgs.take (n - total)).length)
                ((List.range (targetArgs.take (n - total)).length).map Bvl.Exp.var)] := by simpa using post
          exact evaluatePost_overApp_continue_canonical sMiddle sFinal tMiddle fMiddle n total targetArgs
            [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] []
            targetValue (.number (Int.ofNat total)) (.number (Int.ofNat total - Int.ofNat (n + 1)))
            result length over' post'


/-- Overapplication of a related recursive partial closure simulates all clock
outcomes, assuming the body and the strictly shorter remaining application. -/
theorem evaluateApp_recclosure_partial_over_simulation {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) saved captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (continuationIH : applicationSimulation (C := C) (F := F)
      (args.take (args.length - (arity - saved.length)))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity - saved.length ≤ s.clock
  · obtain ⟨fields, oldTargets, original, targetEq, capturedRel, savedRel, closure⟩ :=
      vRel_recclosure_partial_existing s t f ptr arity index captured saved functions body target found savedNonempty functionRel
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    have totalEq : arity - 1 - saved.length = arity - saved.length - 1 := by omega
    rw [targetEq]
    simpa [totalEq] using evaluateApp_recclosure_partial_over_enough s sFinal t f ptr index arity n captured saved args functions
      fields oldTargets targetArgs rest body original result states annotations closure capturedRel savedRel argsRel
      found length savedNonempty savedBound bound over enough appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity - saved.length := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_recclosure_partial_over_timeout s t f ptr arity index captured saved args
      functions targetArgs rest body target states annotations functionRel argsRel found savedNonempty savedBound bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- An ordinary closure application with a valid saved-argument count is
simulated in the undersaturated, exact and overapplied cases. Overapplication
uses the induction hypothesis only on the strictly shorter remaining prefix. -/
theorem evaluateApp_ordinary_induction_case {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) saved captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (smallerIH : ∀ earlier : List ClosSem.Value, earlier.length < args.length → applicationSimulation (C := C) (F := F) earlier) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  cases saved with
  | nil =>
    by_cases partialBound : args.length < arity
    · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_ordinary_partial_simulation s t f ptr arity
        captured args targetArgs rest body target states annotations functionRel argsRel nonempty partialBound
      rw [appRun] at sourceRun
      cases sourceRun
      exact post
    · by_cases exactArity : args.length = arity
      · exact evaluateApp_ordinary_exact_vRel s sFinal t f ptr arity captured args targetArgs rest body target
          states annotations functionRel argsRel exactArity result appRun noType bodyIH
      · have over : arity < args.length := by omega
        have shorter := ordinary_partial_over_remaining_length arity [] args
          (by simpa using savedBound) (by simpa using over)
        simp only [List.length_nil, Nat.sub_zero] at shorter
        exact evaluateApp_ordinary_over_simulation s sFinal t f ptr arity captured args targetArgs rest body target
          result states annotations functionRel argsRel bound over appRun noType bodyIH
          (smallerIH (args.take (args.length - arity)) shorter)
  | cons first tail =>
    by_cases partialBound : args.length + (first :: tail).length < arity
    · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_ordinary_partial_again_related s t f ptr arity
        captured (first :: tail) args targetArgs rest body target states annotations functionRel argsRel (by simp) nonempty
        (by simpa using partialBound)
      rw [appRun] at sourceRun
      cases sourceRun
      exact post
    · by_cases exactArity : args.length + (first :: tail).length = arity
      · exact evaluateApp_ordinary_partial_exact_related s sFinal t f ptr arity captured (first :: tail) args
          targetArgs rest body target states annotations functionRel argsRel (by simp) nonempty exactArity
          result appRun noType bodyIH
      · have over : arity < args.length + (first :: tail).length := by omega
        have shorter := ordinary_partial_over_remaining_length arity (first :: tail) args savedBound over
        exact evaluateApp_ordinary_partial_over_simulation s sFinal t f ptr arity captured (first :: tail) args
          targetArgs rest body target result states annotations functionRel argsRel (by simp) savedBound bound over
          appRun noType bodyIH (smallerIH (args.take (args.length - (arity - (first :: tail).length))) shorter)

/-- A recursive closure application with a valid selected function and saved
argument count is simulated in all arity cases, using the induction hypothesis
only on a strictly shorter remaining prefix. -/
theorem evaluateApp_recclosure_induction_case {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) saved captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ [])
    (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulation (C := C) (F := F) [body])
    (smallerIH : ∀ earlier : List ClosSem.Value, earlier.length < args.length → applicationSimulation (C := C) (F := F) earlier) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases partialBound : args.length + saved.length < arity
  · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_recclosure_partial_related s t f ptr arity index
      captured saved args functions targetArgs rest body target states annotations functionRel argsRel found nonempty
      (by simpa using partialBound)
    rw [appRun] at sourceRun
    cases sourceRun
    exact post
  · by_cases exactArity : args.length + saved.length = arity
    · cases saved with
      | nil =>
        have exactLength : args.length = arity := by simpa using exactArity
        by_cases many : 1 < functions.length
        · exact evaluateApp_mutualRec_exact_related s sFinal t f ptr index arity captured args targetArgs rest
            functions body target states annotations functionRel argsRel many found exactLength result appRun noType bodyIH
        · obtain ⟨fields, capturedRel, closure⟩ := vRel_recclosure_original functionRel
          cases closure with
          | singletonRec bound positive locations vars compiled installed lookup =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact evaluateApp_singletonRec_exact_vRel s sFinal t f ptr _ captured args targetArgs rest _ _
              states annotations functionRel argsRel exactLength result appRun noType bodyIH
          | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
      | cons first tail =>
        by_cases many : 1 < functions.length
        · exact evaluateApp_mutualRec_partial_exact_related s sFinal t f ptr index arity captured (first :: tail) args
            functions targetArgs rest body target states annotations functionRel argsRel many found (by simp) nonempty
            exactArity result appRun noType bodyIH
        · obtain ⟨fields, oldTargets, original, targetEq, capturedRel, savedRel, closure⟩ :=
            vRel_recclosure_partial_existing s t f ptr arity index captured (first :: tail) functions body target found (by simp) functionRel
          cases closure with
          | singletonRec bound positive locations vars compiled installed lookup =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact evaluateApp_singletonRec_partial_exact_related s sFinal t f ptr _ captured (first :: tail) args
              targetArgs rest _ target states annotations functionRel argsRel (by simp) nonempty exactArity
              result appRun noType bodyIH
          | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
    · have over : arity < args.length + saved.length := by omega
      cases saved with
      | nil =>
        have over' : arity < args.length := by simpa using over
        have shorter := ordinary_partial_over_remaining_length arity [] args
          (by simpa using savedBound) (by simpa using over')
        simp only [List.length_nil, Nat.sub_zero] at shorter
        exact evaluateApp_recclosure_over_simulation s sFinal t f ptr index arity captured args targetArgs rest
          functions body target result states annotations functionRel argsRel found bound over' appRun noType bodyIH
          (smallerIH (args.take (args.length - arity)) shorter)
      | cons first tail =>
        have shorter := ordinary_partial_over_remaining_length arity (first :: tail) args savedBound over
        exact evaluateApp_recclosure_partial_over_simulation s sFinal t f ptr index arity captured (first :: tail) args
          functions targetArgs rest body target result states annotations functionRel argsRel found (by simp) savedBound
          bound over appRun noType bodyIH
          (smallerIH (args.take (args.length - (arity - (first :: tail).length))) shorter)

/-- A nonempty application that does not produce a type error must select a
closure application case. -/
theorem evaluateApp_destClosure_some {C F : Type} (s sFinal : ClosSem.State C F)
    (value : ClosSem.Value) (args : List ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ []) (run : ClosSem.evaluateApp none value args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ application, ClosSem.destClosure s.maxApp none value args = some application := by
  cases args with
  | nil => contradiction
  | cons head tail =>
    cases selected : ClosSem.destClosure s.maxApp none value (head :: tail) with
    | none =>
      rw [ClosSem.evaluateApp, selected] at run
      change (.err (.abort .typeError), s) = (result, sFinal) at run
      cases run
      exact False.elim (noType rfl)
    | some application => exact ⟨application, rfl⟩

/-- Successful ordinary closure dispatch implies the application and saved
argument bounds required by the generated stubs. -/
theorem evaluateApp_ordinary_bounds {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr arity : Nat) (captured saved args : List ClosSem.Value) (body : ClosLang.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value) (nonempty : args ≠ [])
    (run : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) : saved.length < arity ∧ args.length ≤ s.maxApp := by
  obtain ⟨application, selected⟩ := evaluateApp_destClosure_some s sFinal
    (.closure (some ptr) saved captured arity body) args result nonempty run noType
  by_cases bound : args.length ≤ s.maxApp
  · by_cases savedBound : saved.length < arity
    · exact ⟨savedBound, bound⟩
    · simp [ClosSem.destClosure, ClosSem.checkLoc, bound, savedBound] at selected
  · simp [ClosSem.destClosure, ClosSem.checkLoc, bound] at selected

/-- Successful recursive closure dispatch selects a function and implies the
same application and saved-argument bounds. -/
theorem evaluateApp_recclosure_bounds {C F : Type} (s sFinal : ClosSem.State C F)
    (ptr index : Nat) (captured saved args : List ClosSem.Value) (functions : List (Nat × ClosLang.Exp))
    (result : Result (List ClosSem.Value) ClosSem.Value) (nonempty : args ≠ [])
    (run : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) :
    ∃ arity body, functions[index]? = some (arity, body) ∧ saved.length < arity ∧ args.length ≤ s.maxApp := by
  obtain ⟨application, selected⟩ := evaluateApp_destClosure_some s sFinal
    (.recclosure (some ptr) saved captured functions index) args result nonempty run noType
  cases found : functions[index]? with
  | none => simp [ClosSem.destClosure, found] at selected
  | some pair =>
    obtain ⟨arity, body⟩ := pair
    by_cases bound : args.length ≤ s.maxApp
    · by_cases savedBound : saved.length < arity
      · exact ⟨arity, body, rfl, savedBound, bound⟩
      · simp [ClosSem.destClosure, found, ClosSem.checkLoc, bound, savedBound] at selected
    · simp [ClosSem.destClosure, found, ClosSem.checkLoc, bound] at selected

/-- Related ordinary closures always carry the code location required by the
target representation. -/
theorem vRel_ordinary_location_some {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (location : Option Nat) (saved captured : List ClosSem.Value) (arity : Nat) (body : ClosLang.Exp)
    (target : BvlSem.Value) (related : vRel maxApp f refs code (.closure location saved captured arity body) target) :
    ∃ ptr, location = some ptr := by
  cases related with
  | closure envRel closure =>
    have h := (clRel_getLoc _ _ _ _ _ _ _ _ _ _ _ closure).2
    cases location <;> simp_all [getLoc]
  | @partialClosure env fvs argEnv ys numArgs cl clApp clTarget envRel argsRel nonempty bound lookup added getArgs closure =>
    cases cl <;> simp [addArgs] at added
    all_goals (cases closure; simp_all; aesop)

/-- Related recursive closures always carry the code location required by the
target representation. -/
theorem vRel_recclosure_location_some {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    (location : Option Nat) (saved captured : List ClosSem.Value) (functions : List (Nat × ClosLang.Exp)) (index : Nat)
    (target : BvlSem.Value) (related : vRel maxApp f refs code (.recclosure location saved captured functions index) target) :
    ∃ ptr, location = some ptr := by
  cases related with
  | closure envRel closure =>
    have h := (clRel_getLoc _ _ _ _ _ _ _ _ _ _ _ closure).2
    cases location <;> simp_all [getLoc]
  | @partialClosure env fvs argEnv ys numArgs cl clApp clTarget envRel argsRel nonempty bound lookup added getArgs closure =>
    cases cl <;> simp [addArgs] at added
    all_goals cases closure <;> simp_all <;> aesop

/-- Application simulation follows by strong induction on the argument-list
length, assuming the expression simulation for closure bodies. This is an
untagged intermediate in the mutual expression/application argument; the
universal body premise remains to be discharged by that argument. -/
theorem applicationSimulation_of_body_simulation {C F : Type}
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulation (C := C) (F := F) [body]) :
    ∀ args : List ClosSem.Value, applicationSimulation (C := C) (F := F) args := by
  have induct : ∀ n : Nat, ∀ args : List ClosSem.Value, args.length = n →
      applicationSimulation (C := C) (F := F) args := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro args argsLength nonempty s sFinal t f value target targetArgs rest result run noType
        states annotations functionRel argsRel
      obtain ⟨application, selected⟩ := evaluateApp_destClosure_some s sFinal value args result nonempty run noType
      cases value with
      | number n => simp [ClosSem.destClosure] at selected
      | word64 w => simp [ClosSem.destClosure] at selected
      | block tag values => simp [ClosSem.destClosure] at selected
      | byteVector bytes => simp [ClosSem.destClosure] at selected
      | refPtr bit ptr => simp [ClosSem.destClosure] at selected
      | closure location saved captured arity body =>
        obtain ⟨ptr, rfl⟩ := vRel_ordinary_location_some location saved captured arity body target functionRel
        obtain ⟨savedBound, bound⟩ := evaluateApp_ordinary_bounds s sFinal ptr arity captured saved args body
          result nonempty run noType
        apply evaluateApp_ordinary_induction_case s sFinal t f ptr arity captured saved args targetArgs rest
          body target result states annotations functionRel argsRel nonempty savedBound bound run noType (bodyIH body)
        intro earlier shorter
        exact ih earlier.length (by omega) earlier rfl
      | recclosure location saved captured functions index =>
        obtain ⟨ptr, rfl⟩ := vRel_recclosure_location_some location saved captured functions index target functionRel
        obtain ⟨arity, body, found, savedBound, bound⟩ := evaluateApp_recclosure_bounds s sFinal ptr index
          captured saved args functions result nonempty run noType
        apply evaluateApp_recclosure_induction_case s sFinal t f ptr index arity captured saved args targetArgs rest
          functions body target result states annotations functionRel argsRel found nonempty savedBound bound run noType (bodyIH body)
        intro earlier shorter
        exact ih earlier.length (by omega) earlier rfl
  intro args
  exact induct args.length args rfl

/-- Exact ordinary closure entry simulation using a body simulation below a
clock bound. This supports the source evaluator's smaller-clock induction. -/
theorem evaluatePost_ordinary_exact_call_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (locations : ClosProps.everyFnLocationSome [sourceBody])
    (vars : ClosProps.everyFnVarsSome [sourceBody])
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
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
  have positive : arity ≠ 0 := by cases related with | closure _ positive _ _ _ _ _ => exact positive
  have bodyClock : (ClosSem.decClock arity s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t (sourceArgs ++ sourceEnv)
    ((targetArgs ++ fields) ++ targetArgs ++ [targetClosure]) f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
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


/-- Exact ordinary closure application simulates both timeout and body
execution using only the body simulation below the caller's clock bound. -/
theorem evaluateApp_ordinary_exact_all_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · have info : arity ≤ s.maxApp ∧ arity ≠ 0 ∧ ClosProps.everyFnLocationSome [sourceBody] ∧
        ClosProps.everyFnVarsSome [sourceBody] := by
      cases related with | closure bound positive locations vars _ _ _ => exact ⟨bound, positive, locations, vars⟩
    obtain ⟨bound, positive, locations, vars⟩ := info
    cases bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ sourceEnv) (ClosSem.decClock arity s) with
    | mk bodyResult bodyFinal =>
      have sourceNonempty : sourceArgs ≠ [] := by
        intro empty
        simp [empty] at arityMatch
        exact positive arityMatch.symm
      have sourceStep := evaluateApp_ordinary_partial_exact_body s bodyFinal ptr arity sourceEnv [] sourceArgs sourceBody
        sourceNonempty (by simpa using Nat.pos_of_ne_zero positive) (by simpa [arityMatch] using bound)
        (by simpa using arityMatch) (by simpa [arityMatch] using enough) bodyResult
        (by simpa [arityMatch] using bodyRun)
      rw [appRun] at sourceStep
      cases sourceStep
      exact evaluatePost_ordinary_exact_call_below s sFinal t f ptr arity clockBound sourceEnv sourceArgs fields targetArgs rest
        sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough clockBounded result bodyRun
        noType locations vars bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_exact_timeout s t f ptr arity sourceEnv sourceArgs
      fields targetArgs rest sourceBody targetClosure states annotations related envRelated argsRelated arityMatch (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Exact ordinary partial-closure simulation with the body premise restricted
to a smaller source clock. -/
theorem evaluatePost_ordinary_partial_exact_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ ClosProps.everyFnLocationSome [body] ∧ ClosProps.everyFnVarsSome [body] := by
    cases related with | closure bound _ locations vars _ _ _ => exact ⟨bound, locations, vars⟩
  obtain ⟨arityBound, locations, vars⟩ := info
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
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
  have bodyClock : (ClosSem.decClock newArgs.length s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ captured)
    (((newTargets ++ oldTargets) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
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


/-- The saturated body of an ordinary overapplication uses only the
smaller-clock body simulation. -/
theorem evaluatePost_ordinary_over_body_below {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n clockBound : Nat) (captured args : List ClosSem.Value) (fields targetArgs : List BvlSem.Value)
    (body : ClosLang.Exp) (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body)
      (.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)))
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (over : arity < args.length)
    (enough : arity ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    ∃ targetBody,
      sptLookup (ptr + numStubs s.maxApp) t.code = some (arity + 1,
        .let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody) ∧
      evaluatePost (ClosSem.decClock arity s) sMiddle t
        (targetArgs.drop (n - (arity - 1)) ++
          [.block 30 (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)])
        f bodyResult
        [.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody] := by
  cases closure with
  | @closure _ _ aux targetBody aux1 _ _ _ arityBound positive locations vars compiled installed lookup =>
    let sourceSuffix := args.drop (args.length - arity)
    let targetSuffix := targetArgs.drop (n - (arity - 1))
    let targetClosure := BvlSem.Value.block 30
      (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields)
    have ⟨_, _, suffixRel⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
      arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
    have relatedSuffix : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix := by
      simpa [sourceSuffix, targetSuffix] using suffixRel
    have suffixLength : targetSuffix.length = arity := by
      dsimp [targetSuffix]
      simp only [List.length_drop, length]
      omega
    have fieldsLength : fields.length = captured.length := capturedRel.length_eq.symm
    have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
      exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
    have bodyEnv : envRel s.maxApp f t.refs t.code (sourceSuffix ++ captured)
        ((targetSuffix ++ fields) ++ targetSuffix ++ [targetClosure]) := by
      have tail : envRel s.maxApp f t.refs t.code captured (fields ++ targetSuffix ++ [targetClosure]) := by
        simpa using envRel_prepend capturedRel (env := []) (targetEnv := targetSuffix ++ [targetClosure]) (by simp [envRel])
      simpa [List.append_assoc] using envRel_prepend relatedSuffix tail
    have bodyClock : (ClosSem.decClock arity s).clock < clockBound := by
      simp only [ClosSem.decClock]
      omega
    have bodyPost := bodyIH (ClosSem.decClock arity s) sMiddle t (sourceSuffix ++ captured)
      ((targetSuffix ++ fields) ++ targetSuffix ++ [targetClosure]) f aux aux1 [targetBody] bodyResult
      bodyClock (by simpa [sourceSuffix] using bodyRun) noType (by simpa [ClosSem.decClock] using compiled)
      locations (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
      (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
    obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
      finalAnnotations, finalClock⟩ := bodyPost
    refine ⟨_, lookup, clock, targetResult, tFinal, fFinal, ?_, resultRel, finalStates, map, frame,
      finalAnnotations, finalClock⟩
    have entry := evaluate_closure_entry { t with clock := (ClosSem.decClock arity s).clock + clock }
      targetSuffix fields 30 (.codePtr (ptr + numStubs s.maxApp)) (.number (Int.ofNat (arity - 1))) targetBody
    simpa [targetSuffix, targetClosure, suffixLength, fieldsLength] using entry.trans targetRun


/-- The saturated body of an ordinary partial-closure overapplication uses
only the smaller-clock body simulation. -/
theorem evaluatePost_ordinary_partial_over_body_below {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n clockBound : Nat) (captured saved args : List ClosSem.Value)
    (fields oldTargets targetArgs : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (over : arity < args.length + saved.length) (enough : arity - saved.length ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
      (ClosSem.decClock (arity - saved.length) s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    sptLookup stub t.code = some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) ∧
    evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (targetArgs.drop (n - total) ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)])
      f bodyResult [generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  let sourceSuffix := args.drop (args.length - (arity - saved.length))
  let targetSuffix := targetArgs.drop (n - total)
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  obtain ⟨savedLength, savedPositive, relatedSuffix, sourceLength, targetLength⟩ :=
    overAppSuffixFacts s t f arity n total saved args oldTargets targetArgs sourceSuffix
      targetSuffix savedRel argsRel length savedNonempty savedBound rfl over rfl rfl
  have sourceNonempty : sourceSuffix ≠ [] := by
    intro empty
    simp [empty] at sourceLength
    omega
  have targetNonempty : targetSuffix ≠ [] := by
    intro empty
    simp [empty] at targetLength
    omega
  have arityMatch : sourceSuffix.length + saved.length = arity := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup : sptLookup stub t.code =
      some (targetSuffix.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨totalBound, previousBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = targetSuffix.length + 1 := by omega
    simpa [stub, count] using installed
  have saturatedPost := evaluatePost_ordinary_partial_exact_below s sMiddle t f ptr arity clockBound captured saved sourceSuffix
    fields oldTargets targetSuffix [] body original states annotations closure capturedRel savedRel relatedSuffix
    savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) clockBounded bodyResult
    (by simpa [sourceSuffix, sourceLength] using bodyRun) noType bodyIH
  have entryPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] (original :: oldTargets) 31 stub
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) bodyResult targetNonempty stubLookup
    (by simpa [targetLength] using enough) (by simpa [stub] using saturatedPost)
  have count : targetSuffix.length - 1 = total := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have lookupSize : targetSuffix.length + 1 = total + 2 := by dsimp [total]; omega
  rw [count, targetLength] at entryPost
  exact ⟨by simpa [lookupSize] using stubLookup, by simpa [targetSuffix, total, stub, cost] using entryPost⟩


/-- Application simulation restricted to a maximum source clock. This
Flapjack induction interface remains untagged while the evaluator and state
carriers await their HOL correspondence review. -/
def applicationSimulationThrough {C F : Type} (clockBound : Nat) (args : List ClosSem.Value) : Prop :=
  args ≠ [] → ∀ (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (value : ClosSem.Value) (targetValue : BvlSem.Value) (targetArgs rest : List BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value),
    s.clock ≤ clockBound → ClosSem.evaluateApp none value args s = (result, sFinal) →
    result ≠ .err (.abort .typeError) → stateRel f s t → codeAnnotations s →
    vRel s.maxApp f t.refs t.code value targetValue →
    List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs →
    evaluatePost s sFinal t (targetArgs ++ [targetValue] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]

/-- Compose an overapplication body with a clock-bounded simulation of the
remaining call, carrying the remaining argument relation across body effects. -/
theorem evaluatePost_mkClCall_over_compose_through {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (clockBound n total tag address : Nat)
    (args fields rest : List BvlSem.Value) (sourceRemaining : List ClosSem.Value)
    (body : Bvl.Exp) (value : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (length : args.length = n + 1) (over : total < n) (totalBound : total < s.maxApp)
    (genericLookup : sptLookup (genericAppFnLocation n) t.code = some (n + 2, generateGenericApp s.maxApp n))
    (lookup : sptLookup address t.code = some (total + 2, body)) (enough : total + 1 ≤ s.clock)
    (maxAppEq : sMiddle.maxApp = s.maxApp) (middleClock : sMiddle.clock ≤ clockBound)
    (remainingNonempty : sourceRemaining ≠ [])
    (remainingRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceRemaining (args.take (n - total)))
    (sourceRun : ClosSem.evaluateApp none value sourceRemaining sMiddle = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (bodyPost : evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (args.drop (n - total) ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)])
      f (.val [value]) [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound sourceRemaining) :
    evaluatePost s sFinal t
      (args ++ [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)] ++ rest) f result
      [mkClCall (.var args.length) ((List.range args.length).map Bvl.Exp.var)] := by
  apply evaluatePost_mkClCall_over_compose s sMiddle sFinal t f n total tag address args fields rest body value result
    length over totalBound genericLookup lookup enough maxAppEq bodyPost
  intro targetValue tMiddle fMiddle statesMiddle valueRel map refs annotationsMiddle growth
  have grown : List.Forall₂ (vRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code)
      sourceRemaining (args.take (n - total)) := by
    apply remainingRel.imp
    intro x y related
    simpa [maxAppEq] using vRel_grow related map refs growth
  have post := continuationIH remainingNonempty sMiddle sFinal tMiddle fMiddle value targetValue
    (args.take (n - total)) [] result middleClock sourceRun noType statesMiddle annotationsMiddle valueRel grown
  have post' : evaluatePost sMiddle sFinal tMiddle (args.take (n - total) ++ [targetValue] ++ []) fMiddle result
      [mkClCall (.var (args.take (n - total)).length)
        ((List.range (args.take (n - total)).length).map Bvl.Exp.var)] := by simpa using post
  exact evaluatePost_overApp_continue_canonical sMiddle sFinal tMiddle fMiddle n total args
    [.block tag (.codePtr address :: .number (Int.ofNat total) :: fields)] [] targetValue
    (.number (Int.ofNat total)) (.number (Int.ofNat total - Int.ofNat (n + 1))) result length over post'

/-- Ordinary partial-closure overapplication with body and continuation
simulations bounded by the caller's clock. -/
theorem evaluateApp_ordinary_partial_over_enough_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n clockBound : Nat) (captured saved args : List ClosSem.Value)
    (fields oldTargets targetArgs rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (enough : arity - saved.length ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound
      (args.take (args.length - (arity - saved.length)))) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    evaluatePost s sFinal t (targetArgs ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] ++ rest)
      f result [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  have arityBound : arity ≤ s.maxApp := by cases closure with | closure bound _ _ _ _ _ _ => exact bound
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : total < n := by dsimp [total]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity saved.length n total argsRel length savedBound rfl over
  cases bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
      (ClosSem.decClock (arity - saved.length) s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_ordinary_over s ptr arity captured saved args body savedBound bound over]
      simp only [Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_ordinary_partial_over_body_below s sFinal t f ptr arity n clockBound
        captured saved args fields oldTargets targetArgs body original (.err error) states annotations closure capturedRel
        savedRel argsRel length savedNonempty savedBound over enough clockBounded bodyRun errorNoType bodyIH
      exact evaluatePost_mkClCall_over_error s sFinal t f n total 31 stub targetArgs (original :: oldTargets) rest
        (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) error length over' totalBound
        genericLookup stubLookup (by simpa [cost] using enough) bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
          (ClosSem.decClock (arity - saved.length) s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
              (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_ordinary_partial_over_body_below s sMiddle t f ptr arity n clockBound
            captured saved args fields oldTargets targetArgs body original (.val [value]) states annotations closure capturedRel
            savedRel argsRel length savedNonempty savedBound over enough clockBounded bodyRun (by simp) bodyIH
          have middleClock : sMiddle.clock ≤ clockBound := by
            have h := ClosSem.evaluate_clock_le [body]
              (args.drop (args.length - (arity - saved.length)) ++ saved ++ captured)
              (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simp only [ClosSem.decClock] at h
            omega
          have remainingNonempty : args.take (args.length - (arity - saved.length)) ≠ [] := by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega
          exact evaluatePost_mkClCall_over_compose_through s sMiddle sFinal t f clockBound n total 31 stub targetArgs
            (original :: oldTargets) rest (args.take (args.length - (arity - saved.length)))
            (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) value result length over' totalBound
            genericLookup stubLookup (by simpa [cost] using enough) maxAppEq middleClock remainingNonempty prefixRel
            sourceContinue noType bodyPost continuationIH

/-- Ordinary partial-closure overapplication at any clock, using bounded
body and remaining-application hypotheses. -/
theorem evaluateApp_ordinary_partial_over_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) saved captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length) (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound
      (args.take (args.length - (arity - saved.length)))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity - saved.length ≤ s.clock
  · obtain ⟨oldTargets, original, targetEq, originalRel, savedRel⟩ :=
      vRel_ordinary_partial_existing s t f ptr arity captured saved body target savedNonempty functionRel
    obtain ⟨fields, capturedRel, closure⟩ := vRel_ordinary_closure originalRel
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    have totalEq : arity - 1 - saved.length = arity - saved.length - 1 := by omega
    rw [targetEq]
    simpa [totalEq] using evaluateApp_ordinary_partial_over_enough_below s sFinal t f ptr arity n clockBound captured saved args
      fields oldTargets targetArgs rest body original result states annotations closure capturedRel savedRel argsRel
      length savedNonempty savedBound bound over enough clockBounded appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity - saved.length := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_partial_over_timeout s t f ptr arity captured saved args
      targetArgs rest body target states annotations functionRel argsRel savedNonempty savedBound bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- Ordinary closure overapplication with body and continuation simulations
bounded by the caller's clock. -/
theorem evaluateApp_ordinary_over_enough_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity n clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (length : targetArgs.length = n + 1)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length) (enough : arity ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_ordinary_closure functionRel
  have ⟨arityBound, positive⟩ : arity ≤ s.maxApp ∧ arity ≠ 0 := by
    cases closure with | closure bound positive _ _ _ _ _ => exact ⟨bound, positive⟩
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : arity - 1 < n := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have cost : arity - 1 + 1 = arity := by omega
  have lookupSize : arity - 1 + 2 = arity + 1 := by omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have prefixRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by simpa using prefixRel
  cases bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_ordinary_over s ptr arity captured [] args body (by simp; omega) bound (by simpa using over)]
      simp only [List.length_nil, Nat.sub_zero, List.append_nil, Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      have targetEq : target = .block 30
          (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
        cases closure with | closure _ _ _ _ _ _ _ => rfl
      obtain ⟨targetBody, lookup, bodyPost⟩ := evaluatePost_ordinary_over_body_below s sFinal t f
        ptr arity n clockBound captured args fields targetArgs body (.err error) states annotations
        (by simpa [targetEq] using closure) envRel' argsRel length over enough clockBounded bodyRun errorNoType bodyIH
      let address := ptr + numStubs s.maxApp
      let payload := fields
      let entry := Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody
      rw [targetEq]
      apply evaluatePost_mkClCall_over_error s sFinal t f n (arity - 1) 30 address targetArgs payload rest entry error
        length over' totalBound genericLookup (by simpa [lookupSize] using lookup) (by simpa [cost] using enough)
      simpa [targetEq, cost] using bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - arity) ++ captured)
          (ClosSem.decClock arity s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - arity) ++ captured)
              (ClosSem.decClock arity s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          have targetEq : target = .block 30
              (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
            cases closure with | closure _ _ _ _ _ _ _ => rfl
          obtain ⟨targetBody, lookup, bodyPost⟩ := evaluatePost_ordinary_over_body_below s sMiddle t f
            ptr arity n clockBound captured args fields targetArgs body (.val [value]) states annotations
            (by simpa [targetEq] using closure) envRel' argsRel length over enough clockBounded bodyRun (by simp) bodyIH
          let address := ptr + numStubs s.maxApp
          let payload := fields
          let entry := Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ freeLet (.var arity) captured.length) targetBody
          rw [targetEq]
          have middleClock : sMiddle.clock ≤ clockBound := by
            have h := ClosSem.evaluate_clock_le [body] (args.drop (args.length - arity) ++ captured)
              (ClosSem.decClock arity s)
            rw [bodyRun] at h
            simp only [ClosSem.decClock] at h
            omega
          have remainingNonempty : args.take (args.length - arity) ≠ [] := by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega
          exact evaluatePost_mkClCall_over_compose_through s sMiddle sFinal t f clockBound n (arity - 1) 30 address
            targetArgs payload rest (args.take (args.length - arity)) entry value result length over' totalBound
            genericLookup (by simpa [address, entry, lookupSize] using lookup) (by simpa [cost] using enough) maxAppEq
            middleClock remainingNonempty prefixRel' sourceContinue noType (by simpa [targetEq, address, payload, entry, cost] using bodyPost) continuationIH

/-- Ordinary closure overapplication at any clock, using bounded body and
remaining-application hypotheses. -/
theorem evaluateApp_ordinary_over_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length) (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · obtain ⟨fields, capturedRel, closure⟩ := vRel_ordinary_closure functionRel
    have targetEq : target = .block 30
        (.codePtr (ptr + numStubs s.maxApp) :: .number (Int.ofNat (arity - 1)) :: fields) := by
      cases closure with | closure _ _ _ _ _ _ _ => rfl
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    exact evaluateApp_ordinary_over_enough_below s sFinal t f ptr arity n clockBound captured args targetArgs rest
      body target result states annotations functionRel argsRel length bound over enough clockBounded appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_over_timeout s t f ptr arity captured args
      targetArgs rest body target states annotations functionRel argsRel bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- Saturated ordinary partial application with a smaller-clock body hypothesis. -/
theorem evaluateApp_ordinary_partial_exact_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.closure (some ptr) [] captured arity body) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
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
    exact evaluatePost_ordinary_partial_exact_below s sFinal t f ptr arity clockBound captured oldArgs newArgs fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel oldNonempty nonempty length enough clockBounded result bodyRun noType bodyIH


/-- Related saturated ordinary partial application with a smaller-clock body hypothesis. -/
theorem evaluateApp_ordinary_partial_exact_related_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.closure (some ptr) oldArgs captured arity body) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) oldArgs captured arity body) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨oldTargets, original, targetEq, originalRel, oldRel⟩ :=
    vRel_ordinary_partial_existing s t f ptr arity captured oldArgs body target oldNonempty related
  obtain ⟨fields, envRel', closure⟩ := vRel_ordinary_closure originalRel
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_ordinary_partial_exact_simulation_below s sFinal t f ptr arity clockBound captured oldArgs newArgs
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      oldNonempty nonempty length enough clockBounded result appRun noType bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_ordinary_partial_exact_timeout s t f ptr arity
      captured oldArgs newArgs fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- A related exact ordinary closure call uses the body simulation below
the caller's clock bound. -/
theorem evaluateApp_ordinary_exact_vRel_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) [] sourceEnv arity sourceBody) targetClosure)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) [] sourceEnv arity sourceBody) sourceArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRelated, closure⟩ := vRel_ordinary_closure functionRel
  exact evaluateApp_ordinary_exact_all_below s sFinal t f ptr arity clockBound sourceEnv sourceArgs fields targetArgs rest
    sourceBody targetClosure states annotations closure envRelated argsRelated arityMatch clockBounded result appRun noType bodyIH

/-- The ordinary closure induction case with bounded body and shorter-call
hypotheses. -/
theorem evaluateApp_ordinary_induction_case_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.closure (some ptr) saved captured arity body) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (nonempty : args ≠ []) (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.closure (some ptr) saved captured arity body) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (smallerIH : ∀ earlier : List ClosSem.Value, earlier.length < args.length → applicationSimulationThrough (C := C) (F := F) clockBound earlier) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  cases saved with
  | nil =>
    by_cases partialBound : args.length < arity
    · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_ordinary_partial_simulation s t f ptr arity
        captured args targetArgs rest body target states annotations functionRel argsRel nonempty partialBound
      rw [appRun] at sourceRun
      cases sourceRun
      exact post
    · by_cases exactArity : args.length = arity
      · exact evaluateApp_ordinary_exact_vRel_below s sFinal t f ptr arity clockBound captured args targetArgs rest body target
          states annotations functionRel argsRel exactArity clockBounded result appRun noType bodyIH
      · have over : arity < args.length := by omega
        have shorter := ordinary_partial_over_remaining_length arity [] args
          (by simpa using savedBound) (by simpa using over)
        simp only [List.length_nil, Nat.sub_zero] at shorter
        exact evaluateApp_ordinary_over_simulation_below s sFinal t f ptr arity clockBound captured args targetArgs rest body target
          result states annotations functionRel argsRel bound over clockBounded appRun noType bodyIH
          (smallerIH (args.take (args.length - arity)) shorter)
  | cons first tail =>
    by_cases partialBound : args.length + (first :: tail).length < arity
    · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_ordinary_partial_again_related s t f ptr arity
        captured (first :: tail) args targetArgs rest body target states annotations functionRel argsRel (by simp) nonempty
        (by simpa using partialBound)
      rw [appRun] at sourceRun
      cases sourceRun
      exact post
    · by_cases exactArity : args.length + (first :: tail).length = arity
      · exact evaluateApp_ordinary_partial_exact_related_below s sFinal t f ptr arity clockBound captured (first :: tail) args
          targetArgs rest body target states annotations functionRel argsRel (by simp) nonempty exactArity clockBounded
          result appRun noType bodyIH
      · have over : arity < args.length + (first :: tail).length := by omega
        have shorter := ordinary_partial_over_remaining_length arity (first :: tail) args savedBound over
        exact evaluateApp_ordinary_partial_over_simulation_below s sFinal t f ptr arity clockBound captured (first :: tail) args
          targetArgs rest body target result states annotations functionRel argsRel (by simp) savedBound bound over clockBounded
          appRun noType bodyIH (smallerIH (args.take (args.length - (arity - (first :: tail).length))) shorter)


/-- Recursive closure entry simulation using a smaller-clock body hypothesis. -/
theorem evaluatePost_singletonRec_exact_call_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (sourceEnv, fields) (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (envRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceEnv fields)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) (enough : arity ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [sourceBody] (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv) (ClosSem.decClock arity s) = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError))
    (locations : ClosProps.everyFnLocationSome [sourceBody])
    (vars : ClosProps.everyFnVarsSome [sourceBody])
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
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
  have positive : arity ≠ 0 := (clRel_recclosure_arity (body := sourceBody) related (by simp)).2
  have bodyClock : (ClosSem.decClock arity s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t (sourceArgs ++ [.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0] ++ sourceEnv)
    (((targetArgs ++ [targetClosure]) ++ fields) ++ targetArgs ++ [targetClosure]) f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
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

/-- Recursive closure entry simulation using a smaller-clock body hypothesis. -/
theorem evaluatePost_singletonRec_partial_exact_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have info : arity ≤ s.maxApp ∧ ClosProps.everyFnLocationSome [body] ∧ ClosProps.everyFnVarsSome [body] := by
    cases related with
    | singletonRec bound _ locations vars _ _ _ => exact ⟨bound, locations, vars⟩
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  obtain ⟨arityBound, locations, vars⟩ := info
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
  obtain ⟨aux, targetBody, finalAux, compiled, installed, sourceLookup, _⟩ :=
    evaluate_partialComplete_singletonRec_entry t s.maxApp ptr arity _ captured fields newTargets oldTargets rest
      body original related envRel'.length_eq.symm targetNewNonempty targetOldNonempty targetLength stubLookup
  have bodyStates : stateRel f (ClosSem.decClock newArgs.length s) t := by
    exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr states
  have selfRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured [(arity, body)] 0) original := by
    cases related with
    | singletonRec bound positive loc vars compiled installed lookup =>
      exact .closure envRel' (.singletonRec bound positive loc vars compiled installed lookup)
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have bodyEnv : envRel s.maxApp f t.refs t.code (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured)
      (((newTargets ++ oldTargets ++ [original]) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) := by
    have tail : envRel s.maxApp f t.refs t.code
        (.recclosure (some ptr) [] captured [(arity, body)] 0 :: captured)
        (original :: fields ++ (newTargets ++ oldTargets) ++ [original]) := by
      refine ⟨selfRel, ?_⟩
      simpa using envRel_prepend envRel' (env := []) (targetEnv := (newTargets ++ oldTargets) ++ [original]) (by simp [envRel])
    simpa [List.append_assoc] using envRel_prepend (List.rel_append newRel oldRel) tail
  have bodyClock : (ClosSem.decClock newArgs.length s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured)
    (((newTargets ++ oldTargets ++ [original]) ++ fields) ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + (clock + 1) }
  have shiftedRelated : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) start.refs start.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original := by simpa [start] using related
  have shiftedLookup : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    simpa [start] using stubLookup
  obtain ⟨aux2, targetBody2, finalAux2, compiled2, _, lookup2, callRun⟩ :=
    evaluate_partialComplete_singletonRec_entry start s.maxApp ptr arity _ captured fields newTargets oldTargets rest
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

/-- Recursive closure entry simulation using a smaller-clock body hypothesis. -/
theorem evaluatePost_mutualRec_exact_call_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (length : args.length = arity) (enough : arity ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (args ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) = (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (locations : ClosProps.everyFnLocationSome [body]) (vars : ClosProps.everyFnVarsSome [body])
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, targetsLength,
    groupRel, arityBound, positive, compiled, lookup, installed⟩ :=
    clRel_mutualRec_selected_related related envRel' many found
  have targetLength : targetArgs.length = arity := by rw [← length]; exact argsRel.length_eq.symm
  have nonempty : targetArgs ≠ [] := by intro empty; simp [empty] at targetLength; exact positive targetLength.symm
  have bodyStates : stateRel f (ClosSem.decClock arity s) t := by
    exact (stateRel_clock f s t (s.clock - arity)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code
      (args ++ (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      ((targetArgs ++ (targets ++ fields)) ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
    have tail : envRel s.maxApp f t.refs t.code captured (fields ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
      simpa using envRel_prepend envRel' (env := [])
        (targetEnv := BvlSem.Value.refPtr true shared :: (targetArgs ++ [target])) (by simp [envRel])
    have group : envRel s.maxApp f t.refs t.code
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
        (targets ++ fields ++ [.refPtr true shared] ++ targetArgs ++ [target]) := by
      simpa [List.append_assoc] using envRel_prepend groupRel tail
    simpa [List.append_assoc] using envRel_prepend argsRel group
  have bodyClock : (ClosSem.decClock arity s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock arity s) sFinal t _ _ f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + clock }
  have lookupStart : sptLookup address start.code = some (targetArgs.length + 1,
      (codeForReccCase (captured.length + functions.length) arity targetBody).2) := by
    simpa [start, targetLength] using lookup
  have callRun := evaluate_mkClCall_direct_env start targetArgs rest 30 address [.refPtr true shared]
    ((codeForReccCase (captured.length + functions.length) arity targetBody).2) nonempty lookupStart
  have enoughTarget : ¬ start.clock < targetArgs.length := by dsimp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have storedStart : (BvlSem.decClock targetArgs.length start).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
    simpa [start, BvlSem.decClock] using stored
  have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
    simp [targetsLength, envRel'.length_eq, Nat.add_comm]
  have entryRun := evaluateCodeForReccCase (BvlSem.decClock targetArgs.length start) shared (targets ++ fields) targetArgs
    targetBody address (arity - 1) [] storedStart
  have clockEq : s.clock + clock - arity = s.clock - arity + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)]
      (targetArgs ++ [target] ++ rest) start = (targetResult, tFinal) := by
    rw [targetEq]
    rw [show targetArgs.length - 1 = arity - 1 by omega] at callRun
    rw [callRun]
    rw [sharedLength, targetLength] at entryRun
    rw [targetLength]
    rw [entryRun]
    simpa [targetEq, start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- Recursive closure entry simulation using a smaller-clock body hypothesis. -/
theorem evaluatePost_mutualRec_partial_exact_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured) (ClosSem.decClock newArgs.length s) =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity related found).1
  have ⟨locations, vars⟩ := clRel_recclosure_annotations related found
  obtain ⟨oldLength, newLength, oldPositive, newPositive, targetLength, targetNewNonempty,
    targetOldNonempty, stubLookup⟩ :=
    partialAppEntryFacts s t f arity oldArgs newArgs oldTargets newTargets states arityBound
      oldRel newRel oldNonempty nonempty length
  obtain ⟨address, shared, targets, aux, targetBody, finalAux, targetEq, stored, groupRel, compiled, installed, sourceLookup, _⟩ :=
    evaluate_partialComplete_mutualRec_entry t s.maxApp ptr index arity f captured fields newTargets oldTargets rest
      functions body original related envRel' many found targetNewNonempty targetOldNonempty targetLength stubLookup
  have bodyStates : stateRel f (ClosSem.decClock newArgs.length s) t := by
    exact (stateRel_clock f s t (s.clock - newArgs.length)).2.mpr states
  have bodyEnv : envRel s.maxApp f t.refs t.code
      (newArgs ++ oldArgs ++ (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (((newTargets ++ oldTargets) ++ (targets ++ fields)) ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) := by
    have tail : envRel s.maxApp f t.refs t.code captured
        (fields ++ .refPtr true shared :: ((newTargets ++ oldTargets) ++ [original])) := by
      simpa using envRel_prepend envRel' (env := [])
        (targetEnv := BvlSem.Value.refPtr true shared :: ((newTargets ++ oldTargets) ++ [original])) (by simp [envRel])
    have group : envRel s.maxApp f t.refs t.code
        ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
        (targets ++ fields ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) := by
      simpa [List.append_assoc] using envRel_prepend groupRel tail
    simpa [List.append_assoc] using envRel_prepend (List.rel_append newRel oldRel) group
  have bodyClock : (ClosSem.decClock newArgs.length s).clock < clockBound := by
    simp only [ClosSem.decClock]
    omega
  have bodyPost := bodyIH (ClosSem.decClock newArgs.length s) sFinal t (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured)
    (((newTargets ++ oldTargets) ++ (targets ++ fields)) ++ [.refPtr true shared] ++ (newTargets ++ oldTargets) ++ [original]) f aux finalAux [targetBody] result
    bodyClock bodyRun noType (by simpa [ClosSem.decClock] using compiled) locations
    (by simpa [ClosSem.decClock, codeAnnotations] using annotations) vars installed
    (by simpa [ClosSem.decClock] using bodyEnv) bodyStates
  obtain ⟨clock, targetResult, tFinal, fFinal, targetRun, resultRel, finalStates, map, frame,
    finalAnnotations, finalClock⟩ := bodyPost
  let start : BvlSem.State C F := { t with clock := s.clock + (clock + 1) }
  have shiftedStub : sptLookup (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) start.code =
      some (newTargets.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    simpa [start] using stubLookup
  have shiftedOriginal : sptLookup address start.code = some ((newTargets.length + oldTargets.length) + 1,
      (codeForReccCase (captured.length + functions.length) arity targetBody).2) := by
    simpa [start, targetLength] using sourceLookup
  have newCount : arity - 1 - (oldTargets.length - 1) = newTargets.length := by omega
  have savedCount : oldTargets.length - 1 + 1 = oldTargets.length := by omega
  have callRun := evaluate_mkClCall_partial_complete start (arity - 1) (oldTargets.length - 1) newTargets oldTargets rest
    (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) address
    [.number (Int.ofNat (arity - 1)), .refPtr true shared] _ targetNewNonempty newCount savedCount shiftedStub shiftedOriginal
  have enoughTarget : ¬ start.clock < newTargets.length + 1 := by dsimp [start]; omega
  simp only [if_neg enoughTarget] at callRun
  have storedStart : (BvlSem.decClock (newTargets.length + 1) start).refs.lookup shared = some (.valueArray (targets ++ fields)) := by
    simpa [start, BvlSem.decClock] using stored
  have sharedLength : (targets ++ fields).length = captured.length + functions.length := by
    have targetsLength := groupRel.length_eq.symm
    simp only [List.length_map, List.length_range] at targetsLength
    simp [targetsLength, envRel'.length_eq, Nat.add_comm]
  have entryRun := evaluateCodeForReccCase (BvlSem.decClock (newTargets.length + 1) start)
    shared (targets ++ fields) (newTargets ++ oldTargets) targetBody address (arity - 1) [] storedStart
  have clockEq : s.clock + (clock + 1) - (newTargets.length + 1) = s.clock - newArgs.length + clock := by omega
  have finalRun : BvlSem.evaluate [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)]
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) start = (targetResult, tFinal) := by
    rw [targetEq, callRun]
    rw [sharedLength, List.length_append, targetLength] at entryRun
    rw [entryRun]
    simpa [targetEq, start, BvlSem.decClock, ClosSem.decClock, clockEq] using targetRun
  exact ⟨clock + 1, targetResult, tFinal, fFinal, finalRun, by simpa [ClosSem.decClock] using resultRel,
    finalStates, map, frame, finalAnnotations, finalClock⟩

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_singletonRec_exact_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
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
    (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
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
    have sourceNonempty : sourceArgs ≠ [] := by
      intro empty
      simp [empty] at arityMatch
      exact positive arityMatch.symm
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr 0 arity sourceEnv [] sourceArgs
      [(arity, sourceBody)] sourceBody (by simp) sourceNonempty (by simpa using Nat.pos_of_ne_zero positive)
      (by simpa [arityMatch] using bound) (by simpa using arityMatch)
      (by simpa [arityMatch] using enough) bodyResult (by simpa [arityMatch] using bodyRun)
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_singletonRec_exact_call_below s sFinal t f ptr arity clockBound sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough clockBounded result bodyRun
      noType locations vars bodyIH


/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_singletonRec_exact_all_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
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
    (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · exact evaluateApp_singletonRec_exact_simulation_below s sFinal t f ptr arity clockBound sourceEnv sourceArgs fields targetArgs rest
      sourceBody targetClosure states annotations related envRelated argsRelated arityMatch enough result appRun noType clockBounded bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_singletonRec_exact_timeout s t f ptr arity sourceEnv sourceArgs
      fields targetArgs rest sourceBody targetClosure states annotations related envRelated argsRelated arityMatch (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_singletonRec_exact_vRel_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (sourceEnv sourceArgs : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (sourceBody : ClosLang.Exp) (targetClosure : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code
      (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) targetClosure)
    (argsRelated : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] sourceEnv [(arity, sourceBody)] 0) sourceArgs s =
      (result, sFinal)) (noType : result ≠ .err (.abort .typeError))
    (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [sourceBody]) :
    evaluatePost s sFinal t (targetArgs ++ [targetClosure] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRelated, closure⟩ := vRel_recclosure_original functionRel
  exact evaluateApp_singletonRec_exact_all_below s sFinal t f ptr arity clockBound sourceEnv sourceArgs fields targetArgs rest
    sourceBody targetClosure states annotations closure envRelated argsRelated arityMatch result appRun noType clockBounded bodyIH

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_singletonRec_partial_exact_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured [(arity, body)] 0) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := by cases related with
    | singletonRec bound _ _ _ _ _ _ => exact bound
    | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => simp at impossible
  have positive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ [.recclosure (some ptr) [] captured [(arity, body)] 0] ++ captured) (ClosSem.decClock newArgs.length s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr 0 arity captured oldArgs newArgs
      [(arity, body)] body (by simp) nonempty oldBound bound length enough bodyResult (by simpa using bodyRun)
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_singletonRec_partial_exact_below s sFinal t f ptr arity clockBound captured oldArgs newArgs fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel oldNonempty nonempty length enough clockBounded result bodyRun noType bodyIH

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_singletonRec_partial_exact_related_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured [(arity, body)] 0) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, targetEq, envRel', oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity 0 captured oldArgs [(arity, body)] body target
      (by simp) oldNonempty related
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_singletonRec_partial_exact_simulation_below s sFinal t f ptr arity clockBound captured oldArgs newArgs
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      oldNonempty nonempty length enough result appRun noType clockBounded bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_singletonRec_partial_exact_timeout s t f ptr arity
      captured oldArgs newArgs fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_mutualRec_exact_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured args : List ClosSem.Value) (fields targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (length : args.length = arity) (enough : arity ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity related found
  have ⟨locations, vars⟩ := clRel_recclosure_annotations related found
  have nonempty : args ≠ [] := by intro empty; simp [empty] at length; exact positive length.symm
  have bound : args.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (args ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr index arity captured [] args functions body
      found nonempty (by simp only [List.length_nil]; have h := List.length_pos_iff.mpr nonempty; omega)
      bound (by simpa using length) (by simpa [length] using enough) bodyResult (by simpa [length] using bodyRun)
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_mutualRec_exact_call_below s sFinal t f ptr index arity clockBound captured args fields targetArgs rest
      functions body target states annotations related envRel' argsRel many found length enough clockBounded result bodyRun noType locations vars bodyIH

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_mutualRec_exact_related_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body)) (length : args.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original related
  by_cases enough : arity ≤ s.clock
  · exact evaluateApp_mutualRec_exact_simulation_below s sFinal t f ptr index arity clockBound captured args fields targetArgs rest
      functions body target states annotations closure envRel' argsRel many found length enough result appRun noType clockBounded bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_mutualRec_exact_timeout s t f ptr index arity captured args
      fields targetArgs rest functions body target states annotations closure envRel' argsRel many found length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_mutualRec_partial_exact_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (envRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (oldRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) oldArgs oldTargets)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity) (enough : newArgs.length ≤ s.clock)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t
      (newTargets ++ [.block 31 (.codePtr (partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)) ::
        .number (Int.ofNat (newTargets.length - 1)) :: original :: oldTargets)] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity related found).1
  have positive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have oldBound : oldArgs.length < arity := by omega
  have bound : newArgs.length ≤ s.maxApp := by omega
  cases bodyRun : ClosSem.evaluate [body] (newArgs ++ oldArgs ++ ((List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i)) ++ captured) (ClosSem.decClock newArgs.length s) with
  | mk bodyResult bodyFinal =>
    have sourceStep := evaluateApp_recclosure_partial_exact_body s bodyFinal ptr index arity captured oldArgs newArgs functions body
      found nonempty oldBound bound length enough bodyResult bodyRun
    rw [appRun] at sourceStep
    cases sourceStep
    exact evaluatePost_mutualRec_partial_exact_below s sFinal t f ptr index arity clockBound captured oldArgs newArgs functions fields oldTargets newTargets rest
      body original states annotations related envRel' oldRel newRel many found oldNonempty nonempty length enough clockBounded result bodyRun noType bodyIH

/-- Recursive application simulation using a smaller-clock body hypothesis. -/
theorem evaluateApp_mutualRec_partial_exact_related_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured oldArgs newArgs : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (newTargets rest : List BvlSem.Value) (body : ClosLang.Exp) (target : BvlSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (related : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) oldArgs captured functions index) target)
    (newRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) newArgs newTargets)
    (many : 1 < functions.length) (found : functions[index]? = some (arity, body))
    (oldNonempty : oldArgs ≠ []) (nonempty : newArgs ≠ [])
    (length : newArgs.length + oldArgs.length = arity)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) oldArgs captured functions index) newArgs s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock ≤ clockBound)
    (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    evaluatePost s sFinal t (newTargets ++ [target] ++ rest) f result
      [mkClCall (.var newTargets.length) ((List.range newTargets.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, oldTargets, original, targetEq, envRel', oldRel, closure⟩ :=
    vRel_recclosure_partial_existing s t f ptr arity index captured oldArgs functions body target found oldNonempty related
  have newLength : newTargets.length = newArgs.length := newRel.length_eq.symm
  have newPositive : 0 < newArgs.length := List.length_pos_iff.mpr nonempty
  have remaining : arity - 1 - oldArgs.length = newTargets.length - 1 := by omega
  rw [targetEq, remaining]
  by_cases enough : newArgs.length ≤ s.clock
  · exact evaluateApp_mutualRec_partial_exact_simulation_below s sFinal t f ptr index arity clockBound captured oldArgs newArgs functions
      fields oldTargets newTargets rest body original states annotations closure envRel' oldRel newRel
      many found oldNonempty nonempty length enough result appRun noType clockBounded bodyIH
  · obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_mutualRec_partial_exact_timeout s t f ptr index arity
      captured oldArgs newArgs functions fields oldTargets newTargets rest body original states annotations closure oldRel newRel
      many found oldNonempty nonempty length (by omega)
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Saturated recursive overapplication entry with a bounded body hypothesis. -/
theorem evaluatePost_recclosure_over_body_below {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body))
    (length : targetArgs.length = n + 1) (over : arity < args.length) (enough : arity ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    ∃ address payload entry,
      target = .block 30 (.codePtr address :: .number (Int.ofNat (arity - 1)) :: payload) ∧
      sptLookup address t.code = some (arity + 1, entry) ∧
      evaluatePost (ClosSem.decClock arity s) sMiddle t (targetArgs.drop (n - (arity - 1)) ++ [target])
        f bodyResult [entry] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original functionRel
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  obtain ⟨address, payload, entry, targetEq, lookup⟩ := clRel_recclosure_target_code closure found
  let sourceSuffix := args.drop (args.length - arity)
  let targetSuffix := targetArgs.drop (n - (arity - 1))
  have ⟨_, _, suffixRel⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have relatedSuffix : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceSuffix targetSuffix := by
    simpa [sourceSuffix, targetSuffix] using suffixRel
  have sourceLength : sourceSuffix.length = arity := by
    dsimp [sourceSuffix]
    simp only [List.length_drop]
    omega
  have targetLength : targetSuffix.length = arity := by rw [← sourceLength]; exact relatedSuffix.length_eq.symm
  have sourceNonempty : sourceSuffix ≠ [] := by intro empty; simp [empty] at sourceLength; omega
  have targetNonempty : targetSuffix ≠ [] := by intro empty; simp [empty] at targetLength; omega
  have sourceExact := evaluateApp_recclosure_partial_exact_body s sMiddle ptr index arity captured [] sourceSuffix functions body
    found sourceNonempty (by simp only [List.length_nil]; have h := List.length_pos_iff.mpr sourceNonempty; omega)
    (by omega) (by simpa using sourceLength) (by simpa [sourceLength] using enough) bodyResult
    (by simpa [sourceSuffix, sourceLength] using bodyRun)
  have exactPost : evaluatePost s sMiddle t (targetSuffix ++ [target] ++ []) f bodyResult
      [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    by_cases many : 1 < functions.length
    · exact evaluateApp_mutualRec_exact_related_below s sMiddle t f ptr index arity clockBound captured sourceSuffix targetSuffix []
        functions body target states annotations functionRel relatedSuffix many found sourceLength bodyResult sourceExact noType clockBounded bodyIH
    · cases closure with
      | singletonRec bound positive locations vars compiled installed lookup =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact evaluateApp_singletonRec_exact_vRel_below s sMiddle t f ptr _ clockBound captured sourceSuffix targetSuffix []
          _ _ states annotations functionRel relatedSuffix sourceLength bodyResult sourceExact noType clockBounded bodyIH
      | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
  have directPost : evaluatePost s sMiddle t
      (targetSuffix ++ [.block 30 (.codePtr address :: .number (Int.ofNat (targetSuffix.length - 1)) :: payload)] ++ []) f
      bodyResult [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    simpa [targetEq, targetLength] using exactPost
  have directLookup : sptLookup address t.code = some (targetSuffix.length + 1, entry) := by simpa [targetLength] using lookup
  have bodyPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] payload 30 address entry bodyResult
    targetNonempty directLookup (by simpa [targetLength] using enough) directPost
  refine ⟨address, payload, entry, targetEq, lookup, ?_⟩
  simpa [targetSuffix, targetEq, targetLength] using bodyPost

/-- Saturated recursive partial-closure entry with a bounded body hypothesis. -/
theorem evaluatePost_recclosure_partial_over_body_below {C F : Type}
    (s sMiddle : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n clockBound : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets targetArgs : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (bodyResult : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (over : arity < args.length + saved.length) (enough : arity - saved.length ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock (arity - saved.length) s) = (bodyResult, sMiddle))
    (noType : bodyResult ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    sptLookup stub t.code = some (total + 2, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) ∧
    evaluatePost (ClosSem.decClock (total + 1) s) sMiddle t
      (targetArgs.drop (n - total) ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)])
      f bodyResult [generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  let sourceSuffix := args.drop (args.length - (arity - saved.length))
  let targetSuffix := targetArgs.drop (n - total)
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  obtain ⟨savedLength, savedPositive, relatedSuffix, sourceLength, targetLength⟩ :=
    overAppSuffixFacts s t f arity n total saved args oldTargets targetArgs sourceSuffix
      targetSuffix savedRel argsRel length savedNonempty savedBound rfl over rfl rfl
  have sourceNonempty : sourceSuffix ≠ [] := by
    intro empty
    simp [empty] at sourceLength
    omega
  have targetNonempty : targetSuffix ≠ [] := by
    intro empty
    simp [empty] at targetLength
    omega
  have arityMatch : sourceSuffix.length + saved.length = arity := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have previousBound : oldTargets.length - 1 < arity - 1 := by omega
  have stubLookup : sptLookup stub t.code =
      some (targetSuffix.length + 1, generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) := by
    have installed := states.2.2.2.2.2.2.2.2.2.1 (arity - 1) (oldTargets.length - 1) ⟨totalBound, previousBound⟩
    have count : arity - 1 - (oldTargets.length - 1) + 1 = targetSuffix.length + 1 := by omega
    simpa [stub, count] using installed
  have saturatedPost : evaluatePost s sMiddle t
      (targetSuffix ++ [.block 31 (.codePtr stub :: .number (Int.ofNat (targetSuffix.length - 1)) :: original :: oldTargets)] ++ [])
      f bodyResult [mkClCall (.var targetSuffix.length) ((List.range targetSuffix.length).map Bvl.Exp.var)] := by
    by_cases many : 1 < functions.length
    · exact evaluatePost_mutualRec_partial_exact_below s sMiddle t f ptr index arity clockBound captured saved sourceSuffix functions
        fields oldTargets targetSuffix [] body original states annotations closure capturedRel savedRel relatedSuffix
        many found savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) clockBounded bodyResult
        (by simpa [sourceSuffix, sourceLength] using bodyRun) noType bodyIH
    · cases closure with
      | singletonRec bound positive locations vars compiled installed lookup =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        apply evaluatePost_singletonRec_partial_exact_below s sMiddle t f ptr _ clockBound captured saved sourceSuffix
          fields oldTargets targetSuffix [] _ _ states annotations
          (.singletonRec bound positive locations vars compiled installed lookup) capturedRel savedRel relatedSuffix
          savedNonempty sourceNonempty arityMatch (by simpa [sourceLength] using enough) clockBounded bodyResult
        · simpa [sourceSuffix, sourceLength] using bodyRun
        · exact noType
        · exact bodyIH
      | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
  have entryPost := evaluatePost_mkClCall_direct_body s sMiddle t f targetSuffix [] (original :: oldTargets) 31 stub
    (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) bodyResult targetNonempty stubLookup
    (by simpa [targetLength] using enough) (by simpa [stub] using saturatedPost)
  have count : targetSuffix.length - 1 = total := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have lookupSize : targetSuffix.length + 1 = total + 2 := by dsimp [total]; omega
  rw [count, targetLength] at entryPost
  exact ⟨by simpa [lookupSize] using stubLookup, by simpa [targetSuffix, total, stub, cost] using entryPost⟩


/-- Recursive closure overapplication with bounded body and continuation simulations. -/
theorem evaluateApp_recclosure_over_enough_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length) (enough : arity ≤ s.clock)
    (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  obtain ⟨fields, envRel', closure⟩ := vRel_recclosure_original functionRel
  have ⟨arityBound, positive⟩ := clRel_recclosure_arity closure found
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : arity - 1 < n := by omega
  have totalBound : arity - 1 < s.maxApp := by omega
  have cost : arity - 1 + 1 = arity := by omega
  have lookupSize : arity - 1 + 2 = arity + 1 := by omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity 0 n (arity - 1) argsRel length (by omega) (by simp) (by simpa using over)
  have prefixRel' : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (args.take (args.length - arity)) (targetArgs.take (n - (arity - 1))) := by simpa using prefixRel
  cases bodyRun : ClosSem.evaluate [body] (args.drop (args.length - arity) ++
      (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock arity s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_recclosure_over s ptr arity index captured [] args functions body found (by simp; omega) bound (by simpa using over)]
      simp only [List.length_nil, Nat.sub_zero, List.append_nil, Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨address, payload, entry, targetEq, lookup, bodyPost⟩ := evaluatePost_recclosure_over_body_below s sFinal t f
        ptr index arity n clockBound captured args targetArgs functions body target (.err error) states annotations functionRel argsRel
        found length over enough clockBounded bodyRun errorNoType bodyIH
      rw [targetEq]
      apply evaluatePost_mkClCall_over_error s sFinal t f n (arity - 1) 30 address targetArgs payload rest entry error
        length over' totalBound genericLookup (by simpa [lookupSize] using lookup) (by simpa [cost] using enough)
      simpa [targetEq, cost] using bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - arity) ++
            (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
          (ClosSem.decClock arity s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - arity)) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - arity) ++
                (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
              (ClosSem.decClock arity s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨address, payload, entry, targetEq, lookup, bodyPost⟩ := evaluatePost_recclosure_over_body_below s sMiddle t f
            ptr index arity n clockBound captured args targetArgs functions body target (.val [value]) states annotations functionRel argsRel
            found length over enough clockBounded bodyRun (by simp) bodyIH
          rw [targetEq]
          have middleClock : sMiddle.clock ≤ clockBound := by
            have h := ClosSem.evaluate_clock_le [body] (args.drop (args.length - arity) ++
                (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured) (ClosSem.decClock (arity) s)
            rw [bodyRun] at h
            simp only [ClosSem.decClock] at h
            omega
          have remainingNonempty : args.take (args.length - arity) ≠ [] := by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega
          exact evaluatePost_mkClCall_over_compose_through s sMiddle sFinal t f clockBound n (arity - 1) 30 address
            targetArgs payload rest (args.take (args.length - arity)) entry value result length over' totalBound
            genericLookup (by simpa [lookupSize] using lookup) (by simpa [cost] using enough) maxAppEq middleClock remainingNonempty
            prefixRel' sourceContinue noType (by simpa [targetEq, cost] using bodyPost) continuationIH

/-- Recursive closure overapplication with bounded body and continuation simulations. -/
theorem evaluateApp_recclosure_partial_over_enough_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity n clockBound : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp))
    (fields oldTargets targetArgs rest : List BvlSem.Value) (body : ClosLang.Exp) (original : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (closure : clRel s.maxApp (fun p => ∃ r, f.lookup r = some p) t.refs t.code
      (captured, fields) (.recclosure (some ptr) [] captured functions index) original)
    (capturedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) captured fields)
    (savedRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) saved oldTargets)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (length : targetArgs.length = n + 1) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length)
    (enough : arity - saved.length ≤ s.clock) (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound
      (args.take (args.length - (arity - saved.length)))) :
    let total := arity - saved.length - 1
    let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
    evaluatePost s sFinal t (targetArgs ++ [.block 31 (.codePtr stub :: .number (Int.ofNat total) :: original :: oldTargets)] ++ rest)
      f result [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  let total := arity - saved.length - 1
  let stub := partialAppFnLocation s.maxApp (arity - 1) (oldTargets.length - 1)
  have arityBound : arity ≤ s.maxApp := (clRel_recclosure_arity closure found).1
  have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
  have nBound : n < s.maxApp := by omega
  have over' : total < n := by dsimp [total]; omega
  have totalBound : total < s.maxApp := by dsimp [total]; omega
  have cost : total + 1 = arity - saved.length := by dsimp [total]; omega
  have genericLookup := states.2.2.2.2.2.2.2.2.1 n nBound
  have ⟨_, prefixRel, _⟩ := overApp_related_split (vRel s.maxApp f t.refs t.code) args targetArgs
    arity saved.length n total argsRel length savedBound rfl over
  cases bodyRun : ClosSem.evaluate [body]
      (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
      (ClosSem.decClock (arity - saved.length) s) with
  | mk bodyResult sMiddle =>
    have sourceStep : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s =
        (match bodyResult with
         | .val [value] => ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle
         | other => (other, sMiddle)) := by
      rw [evaluateApp_recclosure_over s ptr arity index captured saved args functions body found savedBound bound over]
      simp only [Nat.not_lt.mpr enough, ↓reduceIte]
      conv_lhs => rw [ClosSem.fixClock_evaluate, bodyRun]
      cases bodyResult with
      | err error => rfl
      | val values => cases values with
        | nil => rfl
        | cons value tail => cases tail <;> rfl
    cases bodyResult with
    | err error =>
      have equal := appRun.symm.trans sourceStep
      cases equal
      have errorNoType : (.err error : Result (List ClosSem.Value) ClosSem.Value) ≠ .err (.abort .typeError) := noType
      obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_recclosure_partial_over_body_below s sFinal t f ptr index arity n clockBound
        captured saved args functions fields oldTargets targetArgs body original (.err error) states annotations closure capturedRel
        savedRel argsRel found length savedNonempty savedBound over enough clockBounded bodyRun errorNoType bodyIH
      exact evaluatePost_mkClCall_over_error s sFinal t f n total 31 stub targetArgs (original :: oldTargets) rest
        (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) error length over' totalBound
        genericLookup stubLookup (by simpa [cost] using enough) bodyPost
    | val values =>
      have valuesLength : values.length = 1 := by
        have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [body]
          (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
          (ClosSem.decClock (arity - saved.length) s) sMiddle values bodyRun
        simpa using h
      cases values with
      | nil => simp at valuesLength
      | cons value tail =>
        cases tail with
        | cons head tail => simp at valuesLength
        | nil =>
          have sourceContinue : ClosSem.evaluateApp none value (args.take (args.length - (arity - saved.length))) sMiddle =
              (result, sFinal) := sourceStep.symm.trans appRun
          have maxAppEq : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [body]
              (args.drop (args.length - (arity - saved.length)) ++ saved ++
        (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured)
              (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simpa [ClosSem.decClock] using h
          obtain ⟨stubLookup, bodyPost⟩ := evaluatePost_recclosure_partial_over_body_below s sMiddle t f ptr index arity n clockBound
            captured saved args functions fields oldTargets targetArgs body original (.val [value]) states annotations closure capturedRel
            savedRel argsRel found length savedNonempty savedBound over enough clockBounded bodyRun (by simp) bodyIH
          have middleClock : sMiddle.clock ≤ clockBound := by
            have h := ClosSem.evaluate_clock_le [body] (args.drop (args.length - (arity - saved.length)) ++ saved ++
                (List.range functions.length).map (fun i => .recclosure (some ptr) [] captured functions i) ++ captured) (ClosSem.decClock (arity - saved.length) s)
            rw [bodyRun] at h
            simp only [ClosSem.decClock] at h
            omega
          have remainingNonempty : args.take (args.length - (arity - saved.length)) ≠ [] := by
            intro empty
            have h := congrArg List.length empty
            simp only [List.length_take, List.length_nil] at h
            omega
          exact evaluatePost_mkClCall_over_compose_through s sMiddle sFinal t f clockBound n total 31 stub
            targetArgs (original :: oldTargets) rest (args.take (args.length - (arity - saved.length))) (generatePartialAppClosureFn (arity - 1) (oldTargets.length - 1)) value result length over' totalBound
            genericLookup stubLookup (by simpa [cost] using enough) maxAppEq middleClock remainingNonempty
            prefixRel sourceContinue noType bodyPost continuationIH

/-- Recursive closure overapplication with bounded induction hypotheses. -/
theorem evaluateApp_recclosure_over_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) [] captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (bound : args.length ≤ s.maxApp) (over : arity < args.length)
    (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) [] captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound (args.take (args.length - arity))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity ≤ s.clock
  · have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    exact evaluateApp_recclosure_over_enough_below s sFinal t f ptr index arity n clockBound captured args targetArgs rest functions body target
      result states annotations functionRel argsRel found length bound over enough clockBounded appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_recclosure_over_timeout s t f ptr arity index captured args
      functions targetArgs rest body target states annotations functionRel argsRel found bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout

/-- Recursive closure overapplication with bounded induction hypotheses. -/
theorem evaluateApp_recclosure_partial_over_simulation_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured saved args : List ClosSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (targetArgs rest : List BvlSem.Value)
    (body : ClosLang.Exp) (target : BvlSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) saved captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (savedNonempty : saved ≠ []) (savedBound : saved.length < arity)
    (bound : args.length ≤ s.maxApp) (over : arity < args.length + saved.length) (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (continuationIH : applicationSimulationThrough (C := C) (F := F) clockBound
      (args.take (args.length - (arity - saved.length)))) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases enough : arity - saved.length ≤ s.clock
  · obtain ⟨fields, oldTargets, original, targetEq, capturedRel, savedRel, closure⟩ :=
      vRel_recclosure_partial_existing s t f ptr arity index captured saved functions body target found savedNonempty functionRel
    have targetLength : targetArgs.length = args.length := argsRel.length_eq.symm
    let n := targetArgs.length - 1
    have length : targetArgs.length = n + 1 := by dsimp [n]; omega
    have totalEq : arity - 1 - saved.length = arity - saved.length - 1 := by omega
    rw [targetEq]
    simpa [totalEq] using evaluateApp_recclosure_partial_over_enough_below s sFinal t f ptr index arity n clockBound captured saved args functions
      fields oldTargets targetArgs rest body original result states annotations closure capturedRel savedRel argsRel
      found length savedNonempty savedBound bound over enough clockBounded appRun noType bodyIH continuationIH
  · have timeout : s.clock < arity - saved.length := by omega
    obtain ⟨sourceTimeout, targetTimeout⟩ := evaluateApp_recclosure_partial_over_timeout s t f ptr arity index captured saved args
      functions targetArgs rest body target states annotations functionRel argsRel found savedNonempty savedBound bound over timeout
    rw [sourceTimeout] at appRun
    cases appRun
    exact targetTimeout


/-- Recursive closure induction case with bounded body and shorter-call hypotheses. -/
theorem evaluateApp_recclosure_induction_case_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (ptr index arity clockBound : Nat) (captured saved args : List ClosSem.Value) (targetArgs rest : List BvlSem.Value)
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (target : BvlSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value) (states : stateRel f s t) (annotations : codeAnnotations s)
    (functionRel : vRel s.maxApp f t.refs t.code (.recclosure (some ptr) saved captured functions index) target)
    (argsRel : List.Forall₂ (vRel s.maxApp f t.refs t.code) args targetArgs)
    (found : functions[index]? = some (arity, body)) (nonempty : args ≠ [])
    (savedBound : saved.length < arity) (bound : args.length ≤ s.maxApp)
    (clockBounded : s.clock ≤ clockBound)
    (appRun : ClosSem.evaluateApp none (.recclosure (some ptr) saved captured functions index) args s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (bodyIH : expressionSimulationBelow (C := C) (F := F) clockBound [body])
    (smallerIH : ∀ earlier : List ClosSem.Value, earlier.length < args.length → applicationSimulationThrough (C := C) (F := F) clockBound earlier) :
    evaluatePost s sFinal t (targetArgs ++ [target] ++ rest) f result
      [mkClCall (.var targetArgs.length) ((List.range targetArgs.length).map Bvl.Exp.var)] := by
  by_cases partialBound : args.length + saved.length < arity
  · obtain ⟨actual, actualState, sourceRun, post⟩ := evaluateApp_recclosure_partial_related s t f ptr arity index
      captured saved args functions targetArgs rest body target states annotations functionRel argsRel found nonempty
      (by simpa using partialBound)
    rw [appRun] at sourceRun
    cases sourceRun
    exact post
  · by_cases exactArity : args.length + saved.length = arity
    · cases saved with
      | nil =>
        have exactLength : args.length = arity := by simpa using exactArity
        by_cases many : 1 < functions.length
        · exact evaluateApp_mutualRec_exact_related_below s sFinal t f ptr index arity clockBound captured args targetArgs rest
            functions body target states annotations functionRel argsRel many found exactLength result appRun noType clockBounded bodyIH
        · obtain ⟨fields, capturedRel, closure⟩ := vRel_recclosure_original functionRel
          cases closure with
          | singletonRec bound positive locations vars compiled installed lookup =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact evaluateApp_singletonRec_exact_vRel_below s sFinal t f ptr _ clockBound captured args targetArgs rest _ _
              states annotations functionRel argsRel exactLength result appRun noType clockBounded bodyIH
          | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
      | cons first tail =>
        by_cases many : 1 < functions.length
        · exact evaluateApp_mutualRec_partial_exact_related_below s sFinal t f ptr index arity clockBound captured (first :: tail) args
            functions targetArgs rest body target states annotations functionRel argsRel many found (by simp) nonempty
            exactArity result appRun noType clockBounded bodyIH
        · obtain ⟨fields, oldTargets, original, targetEq, capturedRel, savedRel, closure⟩ :=
            vRel_recclosure_partial_existing s t f ptr arity index captured (first :: tail) functions body target found (by simp) functionRel
          cases closure with
          | singletonRec bound positive locations vars compiled installed lookup =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl⟩ := found
            exact evaluateApp_singletonRec_partial_exact_related_below s sFinal t f ptr _ clockBound captured (first :: tail) args
              targetArgs rest _ target states annotations functionRel argsRel (by simp) nonempty exactArity
              result appRun noType clockBounded bodyIH
          | mutualRec _ _ _ _ _ _ impossible _ _ _ _ => exact (many impossible).elim
    · have over : arity < args.length + saved.length := by omega
      cases saved with
      | nil =>
        have over' : arity < args.length := by simpa using over
        have shorter := ordinary_partial_over_remaining_length arity [] args
          (by simpa using savedBound) (by simpa using over')
        simp only [List.length_nil, Nat.sub_zero] at shorter
        exact evaluateApp_recclosure_over_simulation_below s sFinal t f ptr index arity clockBound captured args targetArgs rest
          functions body target result states annotations functionRel argsRel found bound over' clockBounded appRun noType bodyIH
          (smallerIH (args.take (args.length - arity)) shorter)
      | cons first tail =>
        have shorter := ordinary_partial_over_remaining_length arity (first :: tail) args savedBound over
        exact evaluateApp_recclosure_partial_over_simulation_below s sFinal t f ptr index arity clockBound captured (first :: tail) args
          functions targetArgs rest body target result states annotations functionRel argsRel found (by simp) savedBound
          bound over clockBounded appRun noType bodyIH
          (smallerIH (args.take (args.length - (arity - (first :: tail).length))) shorter)

/-- Application simulation through a clock bound follows from body
simulations strictly below that bound, by induction on argument length. -/
theorem applicationSimulationThrough_of_body_simulationBelow {C F : Type}
    (clockBound : Nat)
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    ∀ args : List ClosSem.Value, applicationSimulationThrough (C := C) (F := F) clockBound args := by
  have induct : ∀ n : Nat, ∀ args : List ClosSem.Value, args.length = n →
      applicationSimulationThrough (C := C) (F := F) clockBound args := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro args argsLength nonempty s sFinal t f value target targetArgs rest result clockBounded run noType
        states annotations functionRel argsRel
      obtain ⟨application, selected⟩ := evaluateApp_destClosure_some s sFinal value args result nonempty run noType
      cases value with
      | number n => simp [ClosSem.destClosure] at selected
      | word64 w => simp [ClosSem.destClosure] at selected
      | block tag values => simp [ClosSem.destClosure] at selected
      | byteVector bytes => simp [ClosSem.destClosure] at selected
      | refPtr bit ptr => simp [ClosSem.destClosure] at selected
      | closure location saved captured arity body =>
        obtain ⟨ptr, rfl⟩ := vRel_ordinary_location_some location saved captured arity body target functionRel
        obtain ⟨savedBound, bound⟩ := evaluateApp_ordinary_bounds s sFinal ptr arity captured saved args body
          result nonempty run noType
        apply evaluateApp_ordinary_induction_case_below s sFinal t f ptr arity clockBound captured saved args targetArgs rest
          body target result states annotations functionRel argsRel nonempty savedBound bound clockBounded run noType (bodyIH body)
        intro earlier shorter
        exact ih earlier.length (by omega) earlier rfl
      | recclosure location saved captured functions index =>
        obtain ⟨ptr, rfl⟩ := vRel_recclosure_location_some location saved captured functions index target functionRel
        obtain ⟨arity, body, found, savedBound, bound⟩ := evaluateApp_recclosure_bounds s sFinal ptr index
          captured saved args functions result nonempty run noType
        apply evaluateApp_recclosure_induction_case_below s sFinal t f ptr index arity clockBound captured saved args targetArgs rest
          functions body target result states annotations functionRel argsRel found nonempty savedBound bound clockBounded run noType (bodyIH body)
        intro earlier shorter
        exact ih earlier.length (by omega) earlier rfl
  intro args
  exact induct args.length args rfl

/-- Compose expression evaluations with a clock-bounded application simulation. -/
theorem evaluatePost_app_applicationSimulationThrough {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (clockBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (sourceArgs : List ClosLang.Exp) (sourceFunction : ClosLang.Exp)
    (targetArgs : List Bvl.Exp) (targetFunction : Bvl.Exp) (values : List ClosSem.Value)
    (function : ClosSem.Value) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate sourceArgs sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [sourceFunction] sourceEnv sArgs = (.val [function], sFunction))
    (appRun : ClosSem.evaluateApp none function values sFunction = (result, sFinal))
    (nonempty : values ≠ []) (noType : result ≠ .err (.abort .typeError))
    (clockBounded : s.clock ≤ clockBound)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (argsPost : evaluatePost s sArgs t targetEnv f (.val values) targetArgs)
    (functionIH : ∀ (tArgs : BvlSem.State C F) (fArgs : HolFiniteMapExact Nat Nat),
      stateRel fArgs sArgs tArgs → envRel sArgs.maxApp fArgs tArgs.refs tArgs.code sourceEnv targetEnv →
      codeAnnotations sArgs → sptSubspt t.code tArgs.code →
      evaluatePost sArgs sFunction tArgs targetEnv fArgs (.val [function]) [targetFunction])
    (appIH : applicationSimulationThrough (C := C) (F := F) clockBound values) :
    evaluatePost s sFinal t targetEnv f result [appTarget s.maxApp none targetArgs targetFunction] := by
  apply evaluatePost_app_generic_success s sArgs sFunction sFinal t sourceEnv targetEnv f sourceArgs sourceFunction
    targetArgs targetFunction values function result argsRun functionRun envRelated argsPost functionIH
  intro targetValues targetClosure tFunction fFunction states annotations argsRel functionRel
  have argsClock := ClosSem.evaluate_clock_le sourceArgs sourceEnv s
  rw [argsRun] at argsClock
  have functionClock := ClosSem.evaluate_clock_le [sourceFunction] sourceEnv sArgs
  rw [functionRun] at functionClock
  dsimp only at argsClock functionClock
  have functionBound : sFunction.clock ≤ clockBound := by omega
  exact appIH nonempty sFunction sFinal tFunction fFunction function targetClosure targetValues targetEnv result
    functionBound appRun noType states annotations functionRel argsRel

/-- Pre-call error propagation with bounded subexpression hypotheses. -/
theorem expressionSimulation_app_preCall_error_case_below {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (clockBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (location : Option Nat) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace location function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock < clockBound)
    (preCall : (∃ error, ClosSem.evaluate args sourceEnv s = (.err error, sFinal)) ∨
      (∃ values sArgs error, ClosSem.evaluate args sourceEnv s = (.val values, sArgs) ∧
        ClosSem.evaluate [function] sourceEnv sArgs = (.err error, sFinal)))
    (compile : compileExpsHOL s.maxApp [.app trace location function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace location function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace location function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) clockBound [function]) :
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
            clockBounded argsRun noType argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states)
      · rw [argsRun] at run
        dsimp only at run
        rw [ClosSem.fixClock_evaluate, functionRun] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        have argsPost := argsIH s sArgs t sourceEnv targetEnv f middleAux finalAux targetArgs (.val values)
          clockBounded argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
        apply evaluatePost_app_function_error s sArgs sFinal t sourceEnv targetEnv f args targetArgs
          targetFunction location values error argsRun envRelated argsPost
        intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsClock : sArgs.clock < clockBound := by
          have h := ClosSem.evaluate_clock_le args sourceEnv s
          rw [argsRun] at h
          dsimp only at h
          omega
        exact functionIH sArgs sFinal tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction] (.err error)
          argsClock functionRun noType (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

/-- Successful generic application with independently bounded structural and call hypotheses. -/
theorem expressionSimulation_app_success_case_belowBound {C F : Type}
    (s sArgs sFunction sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (clockBound appBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (values : List ClosSem.Value) (functionValue : ClosSem.Value)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsRun : ClosSem.evaluate args sourceEnv s = (.val values, sArgs))
    (functionRun : ClosSem.evaluate [function] sourceEnv sArgs =
      (.val [functionValue], sFunction))
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock < clockBound) (callerBound : s.clock ≤ appBound)
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) clockBound [function])
    (appIH : applicationSimulationThrough (C := C) (F := F) appBound values)
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
  have appRun : ClosSem.evaluateApp none functionValue values sFunction =
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
        clockBounded argsRun (by simp) argsCompiled locationsParts.2 annotations varsParts.2 installed envRelated states
      apply evaluatePost_app_applicationSimulationThrough s sArgs sFunction sFinal t appBound sourceEnv targetEnv f args function
        targetArgs targetFunction values functionValue result argsRun functionRun appRun valuesNonempty noType callerBound
        envRelated argsPost
      · intro tArgs fArgs statesArgs envArgs annotationsArgs growth
        have maxApp : sArgs.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsClock : sArgs.clock < clockBound := by
          have h := ClosSem.evaluate_clock_le args sourceEnv s
          rw [argsRun] at h
          dsimp only at h
          omega
        exact functionIH sArgs sFunction tArgs sourceEnv targetEnv fArgs aux middleAux [targetFunction]
          (.val [functionValue]) argsClock functionRun (by simp)
          (by simpa [maxApp] using functionCompiled)
          (by simpa [ClosProps.everyFnLocationSome] using locationsParts.1) annotationsArgs
          (by simpa [ClosProps.everyFnVarsSome] using varsParts.1)
          (codeInstalled_subspt functionInstalled growth) envArgs statesArgs

      · exact appIH

/-- Generic application with independently bounded structural and call hypotheses. -/
theorem expressionSimulation_app_generic_case_bounded2 {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F) (clockBound appBound : Nat)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (aux finalAux : List (Nat × Nat × Bvl.Exp)) (compiled : List Bvl.Exp)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate [.app trace none function args] sourceEnv s = (result, sFinal))
    (noType : result ≠ .err (.abort .typeError)) (clockBounded : s.clock < clockBound) (callerBound : s.clock ≤ appBound)
    (compile : compileExpsHOL s.maxApp [.app trace none function args] aux = (compiled, finalAux))
    (locations : ClosProps.everyFnLocationSome [.app trace none function args]) (annotations : codeAnnotations s)
    (vars : ClosProps.everyFnVarsSome [.app trace none function args]) (installed : codeInstalled finalAux t.code)
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv) (states : stateRel f s t)
    (argsIH : expressionSimulationBelow (C := C) (F := F) clockBound args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) clockBound [function])
    (appIH : ∀ values : List ClosSem.Value, applicationSimulationThrough (C := C) (F := F) appBound values) :
    evaluatePost s sFinal t targetEnv f result compiled := by
  have nonempty : args ≠ [] := by
    intro empty
    subst args
    simp [ClosSem.evaluate] at run
    exact noType run.1.symm
  have notEmpty : args.isEmpty = false := by cases args <;> simp_all
  cases argsRun : ClosSem.evaluate args sourceEnv s with
  | mk argsResult sArgs =>
    cases argsResult with
    | err error =>
      have sourceRun := run
      rw [ClosSem.evaluate] at sourceRun
      simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at sourceRun
      rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
      simp only at sourceRun
      cases sourceRun
      exact expressionSimulation_app_preCall_error_case_below s sFinal t clockBound sourceEnv targetEnv f trace none args function
        aux finalAux compiled (.err error) run noType clockBounded (Or.inl ⟨error, argsRun⟩) compile locations annotations vars
        installed envRelated states argsIH functionIH
    | val values =>
      cases functionRun : ClosSem.evaluate [function] sourceEnv sArgs with
      | mk functionResult sFunction =>
        cases functionResult with
        | err error =>
          have sourceRun := run
          rw [ClosSem.evaluate] at sourceRun
          simp only [notEmpty, Bool.false_eq_true, ↓reduceIte] at sourceRun
          rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
          dsimp only at sourceRun
          rw [ClosSem.fixClock_evaluate, functionRun] at sourceRun
          simp only at sourceRun
          cases sourceRun
          exact expressionSimulation_app_preCall_error_case_below s sFinal t clockBound sourceEnv targetEnv f trace none args function
            aux finalAux compiled (.err error) run noType clockBounded (Or.inr ⟨values, sArgs, error, argsRun, functionRun⟩)
            compile locations annotations vars installed envRelated states argsIH functionIH
        | val functions =>
          have functionLength : functions.length = 1 := by
            have h := (ClosSem.evaluate_length (C := C) (F := F)).1 [function] sourceEnv sArgs sFunction functions functionRun
            simpa using h
          cases functions with
          | nil => simp at functionLength
          | cons functionValue tail =>
            cases tail with
            | cons head tail => simp at functionLength
            | nil =>
              exact expressionSimulation_app_success_case_belowBound s sArgs sFunction sFinal t clockBound appBound sourceEnv targetEnv f
                trace args function values functionValue aux finalAux compiled result argsRun functionRun run noType clockBounded callerBound
                compile locations annotations vars installed envRelated states argsIH functionIH (appIH values)

/-- A generic application is simulated below the successor clock bound when
its structural subexpressions are simulated at that bound and every closure
body is simulated below the predecessor bound. -/
theorem expressionSimulationBelow_app_succ {C F : Type} (clockBound : Nat) (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (function : ClosLang.Exp)
    (argsIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) args)
    (functionIH : expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [function])
    (bodyIH : ∀ body : ClosLang.Exp, expressionSimulationBelow (C := C) (F := F) clockBound [body]) :
    expressionSimulationBelow (C := C) (F := F) (clockBound + 1) [.app trace none function args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clockBounded run noType compile
    locations annotations vars installed envRelated states
  exact expressionSimulation_app_generic_case_bounded2 s sFinal t (clockBound + 1) clockBound
    sourceEnv targetEnv f trace args function aux finalAux compiled result run noType clockBounded (by omega)
    compile locations annotations vars installed envRelated states argsIH functionIH
    (applicationSimulationThrough_of_body_simulationBelow clockBound bodyIH)

end Flapjack.Compiler.Backend.ClosToBvl
