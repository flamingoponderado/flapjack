import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateLocalArray

/-! Clock-bounded array simulation over preliminary source-to-flat relations. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open OracleInvariant

/-- A missing optional name leaves every binding list unchanged. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "opt_bind_lem"]
theorem optBind_none {K V : Type} :
    (optBind (none : Option K) : V → List (K × V) → List (K × V)) = fun _ env => env := rfl

/-- Updating a flat environment's value bindings by the identity leaves it unchanged. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "env_updated_lem"]
theorem flatEnvironment_update_identity {α : Type} (env : FlatSem.Environment α) :
    { env with v := (fun y => y) env.v } = env := by
  cases env
  rfl

/-- Anonymous let sequencing propagates the same error as evaluating the
expression list, for any trace annotation. -/
@[hol "cakeml/compiler/backend/proofs/source_to_flatProofScript.sml" "evaluate_foldr_let_err"]
theorem flatFoldLets_error {C F : Type} (trace : BackendCommon.Tra) (env : FlatSem.Environment FlatSem.Value)
    (state last : FlatSem.State C F) (expressions : List FlatLang.Exp) (body : FlatLang.Exp)
    (error : ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state expressions = (last, .err error)) :
    FlatSem.evaluate env state [expressions.foldr (FlatLang.Exp.let_ trace none) body] =
      (last, .err error) := by
  induction expressions generalizing state with
  | nil => simp [FlatSem.evaluate] at run
  | cons first rest ih =>
    cases rest with
    | nil =>
      simp only [List.foldr_cons, List.foldr_nil]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env state [first] body []).1, run]
    | cons second tail =>
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env state [first] body []).1] at run
      generalize headRun : FlatSem.evaluate env state [first] = headResult at run
      obtain ⟨middle, headResult⟩ := headResult
      cases headResult with
      | err headError =>
        simp only [Prod.mk.injEq, Result.err.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        simp only [List.foldr_cons]
        rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env state [first] body []).1, headRun]
      | val values =>
        cases tailRun : FlatSem.evaluate env middle (second :: tail) with
        | mk next result =>
          rw [tailRun] at run
          cases result with
          | val values => cases run
          | err tailError =>
            simp only [Prod.mk.injEq, Result.err.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            simp only [List.foldr_cons]
            rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations env state [first] body []).1, headRun]
            exact ih middle tailRun

/-- Empty-array allocation evaluates its argument before allocating an empty
array in both stores. This uses the unreviewed factored relations. -/
theorem localEnvBounded_aallocEmpty {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (body : AstHOL.Exp) (bodyIH : LocalEnvBoundedIH (F := F) interp transform limit body) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aallocEmpty [body]) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have bodySafe : ∀ last, EvaluateHOL.evaluate source sourceEnv [body] ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocEmpty [body]] = _
    rw [EvaluateHOL.evaluate]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, bad]
  obtain ⟨nextGenv, bodySim, post⟩ := bodyIH genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation bodySafe
  unfold ExprSim at bodySim
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv [body] = sourceResult at bodySim post
  obtain ⟨nextSource, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat [compileExp trace compMap body] = flatResult at bodySim post
  obtain ⟨nextFlat, flatResult⟩ := flatResult
  obtain ⟨related, states⟩ := bodySim
  cases related with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldr_cons, List.foldr_nil, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      trivial
  | raise valueRel =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldr_cons, List.foldr_nil, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact ⟨.raise valueRel, states⟩
    · rw [EvaluateHOL.evaluate]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
      simp only [compileExp, compileExps, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldr_cons, List.foldr_nil, ↓reduceIte]
      rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
        (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
      exact post
  | @value sourceValues flatValues valuesRel =>
    obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull source sourceEnv body nextSource sourceValues sourceRun
    cases valuesRel with
    | cons valueRel tail =>
      cases tail with
      | nil =>
        rename_i flatValue
        obtain ⟨growth, nextInvariant, nextGeneration, forward⟩ := post
        have successful : doApp (nextSource.refs, nextSource.ffi) .aallocEmpty [value] ≠ none := by
          intro failed
          apply safe nextSource
          change EvaluateHOL.evaluate source sourceEnv [.app .aallocEmpty [body]] = _
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp [getOpClass, failed, EvaluateHOL.typeError]
        have unit : value = .conv none [] := by
          cases value <;> simp [doApp, doAppNumericCore, doAppBasic] at successful
          case conv stamp values =>
            cases stamp <;> cases values <;> simp_all
        subst value
        obtain ⟨stateRel, offset, reserved⟩ := stateRel_storeAlloc nextGenv nextSource nextFlat states
          (.varray []) (.varray []) (.varray .nil)
        have finalInvariant := factoredInvariant_changeStores interp transform gen nextGenv (start, finish, other)
          nextSource nextFlat (storeAlloc (.varray []) nextSource.refs).1
          (storeAlloc (.varray []) nextFlat.refs).1 nextInvariant stateRel reserved
        have locationRel : ValueRel nextGenv (.loc true (storeAlloc (.varray []) nextSource.refs).2)
            (.loc true (storeAlloc (.varray []) nextFlat.refs).2) := by
          rw [offset]
          exact .location nextGenv _ true
        refine ⟨nextGenv, ?_, ?_⟩
        · unfold ExprSim
          rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldr_cons, List.foldr_nil, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simp [getOpClass, doApp, doAppNumericCore, doAppBasic, FlatSem.evaluate,
            FlatSem.fixClock, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
            FlatSem.applyResult, EvaluateHOL.listResult]
          exact ⟨.value (.cons locationRel .nil), stateRel⟩
        · rw [EvaluateHOL.evaluate]
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
          rw [(EvaluateHOL.fixClockEvaluate source sourceEnv [body] []).1, sourceRun]
          simp only [compileExp, compileExps, List.reverse_cons, List.reverse_nil, List.nil_append, List.foldr_cons, List.foldr_nil, ↓reduceIte]
          rw [FlatSem.evaluate, (FlatSem.fixClock_evaluations flatEnv flat [compileExp trace compMap body]
            (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
          simpa [getOpClass, doApp, doAppNumericCore, doAppBasic, FlatSem.evaluate,
            FlatSem.fixClock, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
            FlatSem.applyResult, EvaluateHOL.listResult] using
            And.intro growth (And.intro finalInvariant (And.intro nextGeneration forward))

/-- Malformed empty-array allocation propagates operand errors through the generated lets. -/
theorem localEnvBounded_aallocEmpty_badArity {C F : Type} [Nonempty C]
    (interp : Option (Value → Option (Config × C))) (transform : List Dec → List Dec) (limit : Nat)
    (args : List AstHOL.Exp) (badArity : args.length ≠ 1)
    (each : ∀ expr, expr ∈ args → LocalEnvBoundedIH (F := F) interp transform limit expr) :
    LocalEnvBoundedIH (F := F) interp transform limit (.app .aallocEmpty args) := by
  intro genv start finish other source flat baseEnv sourceLocal flatEnv traces trace baseMap gen clockBound localRel envInv tracesLen invariant generation safe
  let sourceEnv := { baseEnv with v := nsAppend sourceLocal baseEnv.v }
  let compMap := { baseMap with v := bindLocals traces (flatEnv.v.map Prod.fst) baseMap.v }
  have compiled : compileExp trace compMap (.app .aallocEmpty args) =
      (compileExps trace compMap args).reverse.foldr (FlatLang.Exp.let_ .none none)
        (.app .none (.src .aalloc) [.lit .none (.intLit 0), .lit .none (.intLit 0)]) := rfl
  have argsSafe : ∀ last, EvaluateHOL.evaluate source sourceEnv args.reverse ≠ (last, .err (.abort .typeError)) := by
    intro last bad
    apply safe last
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocEmpty args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, bad]
  obtain ⟨nextGenv, argsSim, post⟩ := boundedEnvListStep_of_each interp transform limit args.reverse
    (fun expr member => each expr (List.mem_reverse.mp member)) genv start finish other source flat baseEnv sourceLocal flatEnv traces
    trace baseMap gen clockBound localRel envInv tracesLen invariant generation argsSafe
  unfold ExprListSim at argsSim
  rw [compileExps_reverse] at argsSim post
  generalize sourceRun : EvaluateHOL.evaluate source sourceEnv args.reverse = sourceResult at argsSim post
  obtain ⟨sourceNext, sourceResult⟩ := sourceResult
  generalize flatRun : FlatSem.evaluate flatEnv flat (compileExps trace compMap args).reverse = flatResult at argsSim post
  obtain ⟨flatNext, flatResult⟩ := flatResult
  obtain ⟨resultRel, states⟩ := argsSim
  cases resultRel with
  | abort error =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled]
      rw [flatFoldLets_error .none flatEnv flat flatNext (compileExps trace compMap args).reverse
        (.app .none (.src .aalloc) [.lit .none (.intLit 0), .lit .none (.intLit 0)]) _ flatRun]
      exact ⟨.abort error, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      trivial
  | raise related =>
    refine ⟨nextGenv, ?_, ?_⟩
    · unfold ExprSim
      rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled]
      rw [flatFoldLets_error .none flatEnv flat flatNext (compileExps trace compMap args).reverse
        (.app .none (.src .aalloc) [.lit .none (.intLit 0), .lit .none (.intLit 0)]) _ flatRun]
      exact ⟨.raise related, states⟩
    · rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
      rw [compiled]
      rw [flatFoldLets_error .none flatEnv flat flatNext (compileExps trace compMap args).reverse
        (.app .none (.src .aalloc) [.lit .none (.intLit 0), .lit .none (.intLit 0)]) _ flatRun]
      exact post
  | @value sourceValues flatValues related =>
    have length := EvaluateProps.evaluateLengthFull source sourceNext sourceEnv args.reverse sourceValues sourceRun
    have bad : sourceValues.reverse.length ≠ 1 := by simpa [length] using badArity
    have rejected : doApp (sourceNext.refs, sourceNext.ffi) .aallocEmpty sourceValues.reverse = none := by
      cases vals : sourceValues.reverse with
      | nil => simp [doApp, doAppNumericCore, doAppBasic]
      | cons first rest =>
        cases rest with
        | nil => simp [vals] at bad
        | cons second rest => simp [doApp, doAppNumericCore, doAppBasic]
    apply False.elim
    apply safe sourceNext
    change EvaluateHOL.evaluate source sourceEnv [.app .aallocEmpty args] = _
    rw [EvaluateHOL.evaluate, (EvaluateHOL.fixClockEvaluate source sourceEnv args.reverse []).1, sourceRun]
    simp [getOpClass, rejected, EvaluateHOL.typeError]


end Flapjack.Compiler.Backend.SourceToFlat
