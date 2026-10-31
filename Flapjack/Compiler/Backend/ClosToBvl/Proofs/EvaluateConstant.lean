import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ScalarConstant
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ConstantBuild

/-! Constant operation cases of the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.BackendCommon

/-- Every source constant has a related target value, including nested blocks
and any target-only string allocations. -/
theorem constant_dispatch {C F : Type} (constant : ClosLang.Const)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t) :
    ∃ target next,
      BvlSem.doApp (compileConst constant) [] t = .val (target, next) ∧
      vRel s.maxApp f next.refs next.code (ClosSem.makeConst constant) target ∧
      stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧ next.clock = t.clock := by
  cases constant with
  | constInt n =>
    obtain ⟨target, next, _, run, rel, state, frame, clock⟩ := scalarConstant_dispatch (.int n) s t f states
    exact ⟨target, next, run, rel, state, frame, clock⟩
  | constStr text =>
    obtain ⟨target, next, _, run, rel, state, frame, clock⟩ := scalarConstant_dispatch (.string text) s t f states
    exact ⟨target, next, run, rel, state, frame, clock⟩
  | constWord64 word =>
    obtain ⟨target, next, _, run, rel, state, frame, clock⟩ := scalarConstant_dispatch (.word word) s t f states
    exact ⟨target, next, run, rel, state, frame, clock⟩
  | constCons tag constants =>
    cases constants with
    | nil =>
      obtain ⟨target, next, _, run, rel, state, frame, clock⟩ := scalarConstant_dispatch (.emptyBlock tag) s t f states
      exact ⟨target, next, run, rel, state, frame, clock⟩
    | cons first rest =>
      have prereqs : (∀ n, ClosLang.Const.constCons tag (first :: rest) ≠ .constInt n) ∧
          (∀ n, ClosLang.Const.constCons tag (first :: rest) ≠ .constCons n []) := by simp
      obtain ⟨target, refs, compiled, run, rel, state, frame⟩ :=
        compileConst_build_related (.constCons tag (first :: rest)) prereqs s t f states
      refine ⟨target, { t with refs := refs }, ?_, rel, state, frame, rfl⟩
      rw [compiled]
      simp [BvlSem.doApp, BvlSem.applyBlock, run]

/-- Applying a constant after successful empty argument evaluation preserves
the simulation postcondition. -/
theorem evaluatePost_constant_success {C F : Type} (s sMiddle : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (constant : ClosLang.Const) (targetArgs : List Bvl.Exp)
    (post : evaluatePost s sMiddle t targetEnv f (.val []) targetArgs)
    (maxApp : sMiddle.maxApp = s.maxApp) :
    evaluatePost s sMiddle t targetEnv f (.val [ClosSem.makeConst constant])
      [.op (compileConst constant) targetArgs] := by
  obtain ⟨clock, targetResult, tMiddle, fMiddle, targetRun, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | err error => simp [resultRel] at related
  | val targetValues =>
    have empty : targetValues = [] := by
      simpa [resultRel] using related
    subst targetValues
    obtain ⟨target, next, app, valueRel, nextState, nextRefs, nextClock⟩ :=
      constant_dispatch constant sMiddle tMiddle fMiddle state
    refine ⟨clock, .val [target], next, fMiddle, ?_, ?_, nextState, map,
      unmappedRefsSubmap_trans refs nextRefs, annotations, ?_⟩
    · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, targetRun]
      simp [app]
    · exact .cons (by simpa [maxApp] using valueRel) .nil
    · exact clocks.trans nextClock.symm

/-- Argument errors propagate through the compiled constant operation. -/
theorem evaluatePost_constant_error {C F : Type} (s sFinal : ClosSem.State C F)
    (t : BvlSem.State C F) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (constant : ClosLang.Const) (args : List Bvl.Exp)
    (error : ErrorResult ClosSem.Value)
    (post : evaluatePost s sFinal t targetEnv f (.err error) args) :
    evaluatePost s sFinal t targetEnv f (.err error) [.op (compileConst constant) args] := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, state, map, refs, annotations, clocks⟩ := post
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, state, map, refs, annotations, clocks⟩
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- The constant expression case for arbitrary argument lists. The argument
induction hypothesis and the relations are the existing simulation candidates,
which remain subject to HOL semantic-carrier review. -/
theorem expressionSimulation_constant {C F : Type} (trace : BackendCommon.Tra)
    (constant : ClosLang.Const) (args : List ClosLang.Exp)
    (argsIH : expressionSimulation (C := C) (F := F) args) :
    expressionSimulation (C := C) (F := F) [.op trace (.blockOp (.constant constant)) args] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases argsCompile : compileExpListHOL s.maxApp args aux with
  | mk targetArgs aux1 =>
    have argsCompiled : compileExpsHOL s.maxApp args aux = (targetArgs, aux1) := by
      rw [compileExps_eq_list]
      exact argsCompile
    have wholeCompiled : compileExpsHOL s.maxApp [.op trace (.blockOp (.constant constant)) args] aux =
        ([.op (compileConst constant) targetArgs], aux1) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, compileExpHOL, argsCompile, compileOp]
    have equal := compile.symm.trans wholeCompiled
    cases equal
    have argsLoc : ClosProps.everyFnLocationSome args := by
      simpa [ClosProps.everyFnLocationSome, ClosProps.fnLocationSomeExp] using locations
    have argsVars : ClosProps.everyFnVarsSome args := by
      simpa [ClosProps.everyFnVarsSome, ClosProps.fnVarsSomeExp] using varsAnnotated
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
    cases argsRun : ClosSem.evaluate args sourceEnv s with
    | mk argsResult sMiddle =>
      rw [argsRun] at run
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact evaluatePost_constant_error s sMiddle t targetEnv f constant targetArgs error
          (argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.err error)
            argsRun noTypeError argsCompiled argsLoc annotations argsVars installed envRelated states)
      | val values =>
        have maxApp : sMiddle.maxApp = s.maxApp := by
          have h := (ClosProps.evaluate_const (C := C) (F := F)).1 args sourceEnv s
          rw [argsRun] at h
          exact h
        have argsPost := argsIH s sMiddle t sourceEnv targetEnv f aux finalAux targetArgs (.val values)
          argsRun (by simp) argsCompiled argsLoc annotations argsVars installed envRelated states
        cases values with
        | nil =>
          simp [ClosSem.doApp, ClosSem.applyBlock] at run
          rcases run with ⟨rfl, rfl⟩
          exact evaluatePost_constant_success s sMiddle t targetEnv f constant targetArgs argsPost maxApp
        | cons value rest =>
          simp [ClosSem.doApp, ClosSem.applyBlock] at run
          rcases run with ⟨rfl, rfl⟩
          exact False.elim (noTypeError rfl)

end Flapjack.Compiler.Backend.ClosToBvl
