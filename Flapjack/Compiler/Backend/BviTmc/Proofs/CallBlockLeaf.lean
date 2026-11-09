import Flapjack.Compiler.Backend.BviTmc.Proofs.CallBlockFrame
import Flapjack.Compiler.Backend.BviTmc.Proofs.CallRelation

/-! Recursive-call leaf of ordinary TMC call-block simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc.CallBlockLeaf
open BviTmc BviSem BvlSem SemanticPrimitivesProps ResultRelation ListSimulation CallBlockEnvironment

/-- Flapjack infrastructure: ordinary recursive-call simulation using the
smaller-clock function-body induction hypothesis. The original measure and
optimized call-block conclusions are omitted. -/
theorem evaluate_rcall_core {C F : Type} (loc ticks : Nat) (indices : List Nat)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value)
    (run : evaluate [callBlockToBvi loc (.rCall ticks indices)] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (wf : wfVars env1.length indices)
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (bodyIH : ∀ body body' args args' bodyResult,
      ticks + 1 ≤ source.clock →
      findCode (some loc) (indices.map (fun n => holEl n env1)) source.code = some (args, body) →
      findCode (some loc) (indices.map (fun n => holEl n env2)) target.code = some (args', body') →
      envRel false f args args' → noMutcons body →
      (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
        rewriteWrapperSource loc workerLoc args.length body = some body') →
      evaluate [body] args (BviSem.decClock (ticks + 1) source) = (bodyResult, final) →
      bodyResult ≠ .err (.abort .typeError) →
      Core [body'] args' f (BviSem.decClock (ticks + 1) target) bodyResult final) :
    Core [callBlockToBvi loc (.rCall ticks indices)] env2 f target result final := by
  have sourceArgs := evaluate_vars_source indices env1 source wf
  have targetArgs := evaluate_vars_target indices env1.length env2 target wf (envRel_length opt f env1 env2 environments)
  have argsRelated := wfVars_list_rel indices opt f env1 env2 environments wf
  simp only [callBlockToBvi] at run ⊢
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, sourceArgs] at run
  cases found : findCode (some loc) (indices.map (fun n => holEl n env1)) source.code with
  | none =>
    simp [found] at run
    exact False.elim (notTypeError run.1.symm)
  | some pair =>
    obtain ⟨args, body⟩ := pair
    have direct : noMutcons body ∧ ∃ args' body',
        findCode (some loc) (indices.map (fun n => holEl n env2)) target.code = some (args', body') ∧
        envRel false f args args' ∧
        (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
          rewriteWrapperSource loc workerLoc args.length body = some body') := by
      cases lookup : sptLookup loc source.code with
      | none => simp [findCode, lookup] at found
      | some entry =>
        obtain ⟨arity, sourceBody⟩ := entry
        by_cases arityEq : (indices.map (fun n => holEl n env1)).length = arity
        · simp [findCode, lookup, arityEq] at found
          obtain ⟨rfl, rfl⟩ := found
          obtain ⟨safe, worker, targetBody, targetLookup, changed⟩ :=
            codeRel_cases loc arity sourceBody source.code target.code lookup (stateRel_codeRel f source target states)
          have lengths := argsRelated.length_eq
          refine ⟨safe, _, targetBody, ?_, listRel_envRel f _ _ argsRelated, ?_⟩
          · simp [findCode, targetLookup, ← lengths, arityEq]
          · intro different
            obtain ⟨optimised, wrapper⟩ := changed different
            exact ⟨worker, optimised, by simpa [arityEq] using wrapper⟩
        · simp [findCode, lookup] at found
          exact False.elim (arityEq (by simpa using found.1))
    obtain ⟨safe, args', body', targetFound, argsRel, bodyChanged⟩ := direct
    have clocks : target.clock = source.clock := states.2.1
    by_cases timeout : source.clock < ticks + 1
    · have targetTimeout : target.clock < ticks + 1 := by simpa [clocks] using timeout
      simp [found, timeout] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      refine ⟨{ target with clock := 0 }, f, .err (.abort .timeoutError), ?_, ?_,
        stateRel_with_clock 0 f source target states, ?_, ?_, ?_, ?_⟩
      · rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp [targetFound, targetTimeout]
      · rfl
      · intro k v h; exact h
      · exact onlyFresh_refl f target.refs
      · exact holesUnchanged_refl f target.refs ∅
      · exact holesStill_refl f target.refs
    · have targetEnough : ¬target.clock < ticks + 1 := by simpa [clocks] using timeout
      simp only [found, timeout, ↓reduceIte] at run
      rw [BviSem.fixClock_evaluate] at run
      cases bodyRun : evaluate [body] args (BviSem.decClock (ticks + 1) source) with
      | mk bodyResult bodyFinal =>
        simp only [bodyRun] at run
        have bodyPair : (bodyResult, bodyFinal) = (result, final) := by
          cases bodyResult with
          | val values => simpa [bodyRun] using run
          | err error =>
            cases error with
            | abort reason => simpa [bodyRun] using run
            | raise payload =>
              cases payload with
              | exn value => simpa [bodyRun] using run
              | ret values =>
                simp at run
                exact False.elim (notTypeError run.1.symm)
        have noReturn : ∀ values, bodyResult ≠ .err (.raise (.ret values)) := by
          intro values bad
          rw [bad] at run
          simp at run
          exact notTypeError run.1.symm
        cases bodyPair
        obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ :=
          bodyIH body body' args args' result (by omega) found targetFound argsRel safe bodyChanged bodyRun notTypeError
        refine ⟨next, g, targetResult, ?_, related, nextStates, extension, fresh, unchanged, still⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          targetFound, targetEnough]
        rw [BviSem.fixClock_evaluate, targetRun]
        cases targetResult with
        | val values => rfl
        | err error =>
          cases error with
          | abort reason => rfl
          | raise payload =>
            cases payload with
            | exn value => rfl
            | ret values =>
              cases result with
              | val sourceValues => simp [SemanticPrimitivesProps.resultRel] at related
              | err sourceError =>
                cases sourceError with
                | abort reason => simp [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel] at related
                | raise sourcePayload =>
                  cases sourcePayload with
                  | exn value => simp [SemanticPrimitivesProps.resultRel, SemanticPrimitivesProps.excRel, eorRel] at related
                  | ret sourceValues => exact False.elim (noReturn sourceValues rfl)

/-- Flapjack infrastructure: ordinary simulation of a well-formed call block
from the smaller-clock body hypothesis. Optimized worker and wrapper
conclusions remain separate. -/
theorem evaluate_cb_ordinary {C F : Type} (loc : Nat) (cb : CallBlock)
    (source : BviState (Nat × C) F) (env1 : List Value) (opt : Bool)
    (f : HolFiniteMapExact Nat Nat) (target : BviState C F) (env2 : List Value)
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (bodyIH : ∀ ticks indices body body' args args' bodyResult bodyFinal,
      wfVars env1.length indices →
      ticks + 1 ≤ source.clock →
      findCode (some loc) (indices.map (fun n => holEl n env1)) source.code = some (args, body) →
      findCode (some loc) (indices.map (fun n => holEl n env2)) target.code = some (args', body') →
      envRel false f args args' → noMutcons body →
      (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
        rewriteWrapperSource loc workerLoc args.length body = some body') →
      evaluate [body] args (BviSem.decClock (ticks + 1) source) = (bodyResult, bodyFinal) →
      bodyResult ≠ .err (.abort .typeError) →
      Core [body'] args' f (BviSem.decClock (ticks + 1) target) bodyResult bodyFinal)
    (result : BviResult) (final : BviState (Nat × C) F)
    (wf : wfBlock env1.length cb) (run : evaluate [callBlockToBvi loc cb] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    Core [callBlockToBvi loc cb] env2 f target result final := by
  apply CallBlockFrame.evaluate_cb_core loc cb source env1 opt f target env2 environments ?_ result final wf run notTypeError
  intro ticks indices leafResult leafFinal leafWf leafRun leafSafe
  apply evaluate_rcall_core loc ticks indices source env1 leafResult leafFinal opt f target env2
    leafRun leafSafe leafWf environments states
  intro body body' args args' bodyResult clockBound sourceFound targetFound argsRel safe changed bodyRun bodySafe
  exact bodyIH ticks indices body body' args args' bodyResult leafFinal leafWf clockBound sourceFound targetFound
    argsRel safe changed bodyRun bodySafe

end Flapjack.Compiler.Backend.BviTmc.CallBlockLeaf
