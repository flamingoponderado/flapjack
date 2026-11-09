import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallSimulation

/-! Equal-clock closure application simulation for the proof-side evaluator.
The evaluator and state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Closure application agrees across related states when the body and
remaining applications agree at smaller clocks. -/
theorem evaluateApp_noInstall_relation_step {C F : Type} (location : Option Nat) (function : ClosSem.Value)
    (args : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (functionOk : valueNoInstall function = true) (argsOk : valuesNoInstall args = true)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start target last : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), start.clock < source.clock →
      ClosLang.hasInstall body = false → valuesNoInstall env = true →
      ClosSem.evaluate [body] env start = (bodyResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [body] env target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (appIH : ∀ (value : ClosSem.Value) (remaining : List ClosSem.Value) (start target last : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value), start.clock < source.clock →
      valueNoInstall value = true → valuesNoInstall remaining = true →
      ClosSem.evaluateApp location value remaining start = (appResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluateApp location value remaining target = (appResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall appResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluateApp location function args source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluateApp location function args target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  have clockEq := stateRelNoInstall_clock related
  cases args with
  | nil =>
    simp [ClosSem.evaluateApp] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluateApp], related, by simp [resultNoInstall, valuesNoInstall, functionOk]⟩
  | cons first rest =>
    cases found : ClosSem.destClosure source.maxApp location function (first :: rest) with
    | none =>
      rw [ClosSem.evaluateApp, found] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨target, ?_, related, trivial⟩
      have foundTarget : ClosSem.destClosure target.maxApp location function (first :: rest) = none := by
        simpa [maxEq] using found
      rw [ClosSem.evaluateApp, foundTarget]
      rfl
    | some kind =>
      have foundTarget : ClosSem.destClosure target.maxApp location function (first :: rest) = some kind := by
        simpa [maxEq] using found
      have kindOk := destClosure_noInstall source.maxApp location function (first :: rest) kind functionOk argsOk found
      cases kind with
      | partialApp value =>
        dsimp only at kindOk
        rw [ClosSem.evaluateApp, found] at run
        dsimp only at run
        by_cases timeout : source.clock < (first :: rest).length
        · rw [if_pos timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with clock := 0 }, ?_, stateRelNoInstall_withClock related 0, trivial⟩
          rw [ClosSem.evaluateApp, foundTarget]
          dsimp only
          rw [if_pos (by simpa [clockEq] using timeout)]
          rfl
        · rw [if_neg timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨ClosSem.decClock (first :: rest).length target, ?_,
            stateRelNoInstall_decClock source target related _, by simp [resultNoInstall, valuesNoInstall, kindOk]⟩
          rw [ClosSem.evaluateApp, foundTarget]
          dsimp only
          rw [if_neg (by simpa [clockEq] using timeout)]
      | fullApp body bodyEnv remaining =>
        dsimp only at kindOk
        obtain ⟨bodyOk, envOk, remainingOk⟩ := kindOk
        have remainingLt := ClosSem.destClosure_full_remaining_lt source.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have positive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        by_cases timeout : source.clock < cost
        · rw [ClosSem.evaluateApp, found] at run
          dsimp only at run
          rw [if_pos timeout] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ target with clock := 0 }, ?_, stateRelNoInstall_withClock related 0, trivial⟩
          rw [ClosSem.evaluateApp, foundTarget]
          dsimp only
          rw [if_pos (by simpa [clockEq, cost] using timeout)]
          rfl
        · have enough : cost ≤ source.clock := by omega
          have smaller : (ClosSem.decClock cost source).clock < source.clock := by simp [ClosSem.decClock]; omega
          have bodyRelated := stateRelNoInstall_decClock source target related cost
          rw [evaluateApp_full_step location function first rest source body bodyEnv remaining found (by simpa [cost] using enough)] at run
          cases bodyRun : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock cost source) with
          | mk bodyResult sourceMid =>
            have bodyBound : sourceMid.clock ≤ (ClosSem.decClock cost source).clock := by
              have h := ClosSem.evaluate_clock_le [body] bodyEnv (ClosSem.decClock cost source)
              simpa [bodyRun] using h
            rw [bodyRun] at run
            obtain ⟨targetMid, targetBody, midRel, bodyResultOk⟩ :=
              bodyIH body bodyEnv (ClosSem.decClock cost source) (ClosSem.decClock cost target) sourceMid
                bodyResult smaller bodyOk envOk bodyRun bodyRelated
            have targetEnough : (first :: rest).length - remaining.length ≤ target.clock := by
              simpa [clockEq, cost] using enough
            cases bodyResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨targetMid, ?_, midRel, bodyResultOk⟩
              rw [evaluateApp_full_step location function first rest target body bodyEnv remaining foundTarget targetEnough, targetBody]
            | val bodyValues =>
              obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value body bodyEnv
                (ClosSem.decClock cost source) sourceMid bodyValues bodyRun
              dsimp only at run
              have valueOk : valueNoInstall value = true := by simpa [resultNoInstall, valuesNoInstall] using bodyResultOk
              obtain ⟨targetFinal, targetApp, finalRel, resultOk⟩ :=
                appIH value remaining sourceMid targetMid final result (by omega) valueOk remainingOk run midRel
              refine ⟨targetFinal, ?_, finalRel, resultOk⟩
              rw [evaluateApp_full_step location function first rest target body bodyEnv remaining foundTarget targetEnough, targetBody]
              exact targetApp

/-- Forcing a thunk agrees across related stores when the argument evaluation
and the forced computation agree. -/
theorem evaluate_force_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (target last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (argResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate args env target = (argResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall argResult)
    (forceIH : ∀ (value : ClosSem.Value) (start target last : ClosSem.State C F)
      (forceResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ source.clock →
      valueNoInstall value = true →
      ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] start = (forceResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] target = (forceResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall forceResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args env source with
  | mk argResult last =>
    have bound : last.clock ≤ source.clock := by
      have clock := ClosSem.evaluate_clock_le args env source
      simpa [argsRun] using clock
    rw [argsRun] at run
    obtain ⟨targetLast, targetArgs, lastRel, argOk⟩ := argsIH target last argResult argsRun related
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, argOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
    | val arguments =>
      dsimp only at run
      have refsEq : last.refs = targetLast.refs := by
        rw [stateRel1_replaceCompiler last targetLast lastRel.1]
      cases inspected : ClosSem.destThunk arguments last.refs with
      | badRef | notThunk =>
        simp [inspected] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨targetLast, ?_, lastRel, trivial⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
        simp [← refsEq, inspected]
      | isThunk mode value =>
        have valueOk := destThunk_value_noInstall arguments last.refs mode value (by simpa [refsEq] using lastRel.2.2) inspected
        cases mode with
        | evaluated =>
          simp [inspected] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨targetLast, ?_, lastRel, by simp [resultNoInstall, valuesNoInstall, valueOk]⟩
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
          simp [← refsEq, inspected]
        | notEvaluated =>
          rw [inspected] at run
          dsimp only at run
          cases forceRun : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] last with
          | mk forceResult sourceEnd =>
            rw [forceRun] at run
            obtain ⟨targetEnd, targetForce, endRel, forceOk⟩ :=
              forceIH value last targetLast sourceEnd forceResult bound valueOk forceRun lastRel
            have targetInspected : ClosSem.destThunk arguments targetLast.refs = .isThunk .notEvaluated value := by
              simpa [← refsEq] using inspected
            cases forceResult with
            | err error =>
              simp at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨targetEnd, ?_, endRel, forceOk⟩
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
              simp [targetInspected, targetForce]
            | val forced =>
              dsimp only at run
              have endRefsEq : sourceEnd.refs = targetEnd.refs := by
                rw [stateRel1_replaceCompiler sourceEnd targetEnd endRel.1]
              cases updated : ClosSem.updateThunk arguments sourceEnd.refs forced with
              | none =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                refine ⟨targetEnd, ?_, endRel, trivial⟩
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
                simp [targetInspected, targetForce, ← endRefsEq, updated]
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                have refsOk := updateThunk_noInstall arguments forced sourceEnd.refs refs
                  (by simpa [endRefsEq] using endRel.2.2) forceOk updated
                refine ⟨{ targetEnd with refs := refs }, ?_, stateRelNoInstall_withRefs sourceEnd targetEnd endRel refs refsOk, forceOk⟩
                rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
                simp [targetInspected, targetForce, ← endRefsEq, updated]

end Flapjack.Compiler.Backend.ClosInterp
