import Flapjack.Compiler.Backend.BviTmc.Proofs.IfWorker
import Flapjack.Compiler.Backend.BviTmc.Proofs.OperationError
import Flapjack.Compiler.Backend.Semantics.BviProps.ApplyErrorCases

/-! TMC simulation for non-extracted primitive operations. -/
namespace Flapjack.Compiler.Backend.BviTmc.OperationSimulation
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation IfWorker OperationError

private theorem reverse_related (f : HolFiniteMapExact Nat Nat) (xs ys : List Value)
    (related : List.Forall₂ (valueRel f) xs ys) : List.Forall₂ (valueRel f) xs.reverse ys.reverse := by
  have appendRel : ∀ {a b c d : List Value}, List.Forall₂ (valueRel f) a b →
      List.Forall₂ (valueRel f) c d → List.Forall₂ (valueRel f) (a ++ c) (b ++ d) := by
    intro a b c d first second
    induction first with
    | nil => exact second
    | cons head tail ih => exact .cons head ih
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa using appendRel ih (.cons head .nil)

/-- Flapjack infrastructure: ordinary operation simulation from the argument
list induction hypothesis. The source measure and safety premises on the
argument expressions are omitted. -/
theorem evaluate_op_core {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [.op op args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safeOp : noMutconsOp op)
    (argsIH : ∀ r mid, evaluate args env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core args env2 f target r mid) :
    Core [.op op args] env2 f target result final := by
  cases argsRun : evaluate args env1 source with
  | mk argsResult middle =>
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argsResult
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
      exact notTypeError (congrArg Prod.fst run.symm)
    obtain ⟨middleTarget, g, targetResult, targetRun, related, middleStates, extension,
      fresh, unchanged, still⟩ := argsIH argsResult middle argsRun argsSafe
    cases argsResult with
    | err error =>
      cases targetResult with
      | val values => simp [resultRel] at related
      | err error' =>
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        refine ⟨middleTarget, g, .err error', ?_, related, middleStates, extension, fresh, unchanged, still⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
    | val values =>
      cases targetResult with
      | err error => simp [resultRel] at related
      | val values' =>
        have reversed : List.Forall₂ (valueRel g) values.reverse values'.reverse :=
          reverse_related g values values' related
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun] at run
        cases appRun : BviSem.doApp op values.reverse middle with
        | err error =>
          simp only [appRun] at run
          obtain ⟨rfl, rfl⟩ := run.symm
          have classification := BviProps.doApp_error op values.reverse final error appRun
          rcases classification with bad | ⟨name, outcome, rfl, rfl⟩
          · exact False.elim (notTypeError (congrArg _ bad))
          · have targetApp := doApp_op_err_rel name values.reverse values'.reverse final middleTarget g outcome
              appRun middleStates reversed
            refine ⟨middleTarget, g, .err (.abort (.ffiError outcome)), ?_, ?_, middleStates,
              extension, fresh, unchanged, still⟩
            · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
              simp [targetApp]
            · rfl
        | val pair =>
          obtain ⟨value, lastSource⟩ := pair
          simp only [appRun] at run
          obtain ⟨rfl, rfl⟩ := run.symm
          obtain ⟨h, value', lastTarget, targetApp, valueRel', nextStates, appExtension,
            appFresh, appUnchanged, appStill⟩ :=
            doApp_op_rel g op values.reverse values'.reverse middle final middleTarget value
              appRun safeOp reversed middleStates
          have submap : finiteSubmap f h := by
            intro k v found; exact appExtension k v (extension k v found)
          have domain := BviProps.evaluate_refs_subset args env2 target middleTarget (.val values') targetRun
          have allFresh := onlyFresh_trans f g h target.refs middleTarget.refs fresh appFresh domain
          have allUnchanged := holesUnchanged_trans f g target.refs middleTarget.refs lastTarget.refs ∅
            unchanged appUnchanged fresh extension
          have allStill := holesStill_trans f g target.refs middleTarget.refs lastTarget.refs ()
            still appStill fresh extension
          refine ⟨lastTarget, h, .val [value'], ?_, ?_, nextStates, submap, allFresh, allUnchanged, allStill⟩
          · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
            simp [targetApp]
          · exact .cons valueRel' .nil

/-- Flapjack infrastructure: ordinary, wrapper, and worker simulation for an
operation which is not extracted as a call block. The argument-list induction
hypothesis is specialized, and the original measure and argument safety
premises are omitted. -/
theorem evaluate_op_non_extracted {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate [.op op args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safeOp : noMutconsOp op)
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (notExtracted : toBlockSource env1.length loc (.op op args) = none)
    (argsIH : ∀ r mid, evaluate args env1 source = (r, mid) →
      r ≠ .err (.abort .typeError) → Core args env2 f target r mid) :
    Core [.op op args] env2 f target result final ∧
    ∀ locOpt, optimisedCode loc locOpt source.code target.code →
      (∀ wrapper, rewriteWrapperSource loc locOpt env1.length (.op op args) = some wrapper →
        Core [wrapper] env2 f target result final) ∧
      (opt = true → ∀ holePtr c, holeHasVal f env1 env2 target.refs c →
        holeNotFinalised target.refs holePtr → holEl env1.length env2 = .refPtr false holePtr →
        WorkerCore (rewriteWorkerSource loc locOpt env1.length (env1.length + 1) env1.length
          (.op op args)) env1 env2 f target holePtr result final) := by
  have core := evaluate_op_core op args source env1 result final f target env2 run notTypeError safeOp argsIH
  constructor
  · exact core
  · intro locOpt _code
    constructor
    · intro wrapper rewrite
      simp [rewriteWrapperSource, notExtracted] at rewrite
    · intro optTrue holePtr c hole notFinal pointer
      have optEnv : envRel true f env1 env2 := by simpa [optTrue] using environments
      obtain ⟨next, g, targetResult, targetRun, resultRel', nextStates, extension, fresh, unchanged, still⟩ := core
      obtain ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩ :=
        FillHole.evaluate_fill_hole (.op op args) f g env1 env2 source final target next result targetResult c holePtr
          run targetRun optEnv states extension resultRel' hole notFinal unchanged still fresh nextStates pointer
      simp only [rewriteWorkerSource, notExtracted]
      exact ⟨fillResult, fillMap, fillState, fillRun, rel, state, ext, only, unch, rest, filled⟩

end Flapjack.Compiler.Backend.BviTmc.OperationSimulation
