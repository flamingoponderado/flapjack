import Flapjack.Compiler.Backend.ClosInterp.Proofs.NoInstallRelation

/-! Equal-clock simulation steps for the proof-side no-install evaluator.
The evaluator and state carriers await HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosInterp
open Flapjack.SemanticPrimitivesHOL

/-- Related states have the same clock. -/
theorem stateRelNoInstall_clock {C F : Type} {source target : ClosSem.State C F}
    (related : StateRelNoInstall source target) : target.clock = source.clock := related.1.2.2.2.2.2.1

/-- Replacing the clocks of related states by the same value preserves their relation. -/
theorem stateRelNoInstall_withClock {C F : Type} {source target : ClosSem.State C F}
    (related : StateRelNoInstall source target) (clock : Nat) :
    StateRelNoInstall { source with clock := clock } { target with clock := clock } := by
  rcases related with ⟨⟨safe, sc, tc, maxEq, positive, _, ffi, globals, refs, compiler, oracle⟩, globalsOk, refsOk⟩
  exact ⟨⟨safe, sc, tc, maxEq, positive, rfl, ffi, globals, refs, compiler, oracle⟩, globalsOk, refsOk⟩

/-- A safe evaluation from either side of the relation has a safe result. -/
theorem stateRelNoInstall_result {C F : Type} (expressions : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (safe : ClosLang.hasInstallList expressions = false) (envOk : valuesNoInstall env = true)
    (related : StateRelNoInstall source target) (run : ClosSem.evaluate expressions env source = (result, final)) :
    resultNoInstall result :=
  (evaluate_noInstall.1 expressions env source final result safe envOk
    (stateRelNoInstall_evalStates source target related).1 run).1

/-- Variable evaluation agrees on related states. -/
theorem evaluate_var_noInstall_relation {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true) (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.var trace index] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.var trace index] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  have resultOk := stateRelNoInstall_result [.var trace index] env source target final result
    (by simp [ClosLang.hasInstallList, ClosLang.hasInstall]) envOk related run
  rw [ClosSem.evaluate] at run
  cases found : env[index]? with
  | none =>
    simp [found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluate, found], related, resultOk⟩
  | some value =>
    simp [found] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluate, found], related, resultOk⟩

/-- Sequencing agrees when its head and tail agree at equal clocks. -/
theorem evaluate_cons_noInstall_relation_step {C F : Type} (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (headIH : ∀ (target last : ClosSem.State C F) (headResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [head] env source = (headResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate [head] env target = (headResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall headResult)
    (tailIH : ∀ (start target last : ClosSem.State C F) (tailResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock ≤ source.clock → ClosSem.evaluate tail env start = (tailResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate tail env target = (tailResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall tailResult)
    (related : StateRelNoInstall source target) (run : ClosSem.evaluate (head :: tail) env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate (head :: tail) env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  cases headRun : ClosSem.evaluate [head] env source with
  | mk headResult last =>
    obtain ⟨targetLast, targetHead, lastRel, headOk⟩ := headIH target last headResult headRun related
    cases headResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error head tail env source last error headRun] at run
      simp at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨targetLast, ClosProps.evaluate_cons_error head tail env target targetLast error targetHead, lastRel, headOk⟩
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value head env source last values headRun
      have valueOk : valueNoInstall value = true := by simpa [resultNoInstall, valuesNoInstall] using headOk
      have bound : last.clock ≤ source.clock := by
        have clock := ClosSem.evaluate_clock_le [head] env source
        simpa [headRun] using clock
      have sourceSequence := ClosProps.evaluate_cons_value head tail env source last value headRun
      cases tailRun : ClosSem.evaluate tail env last with
      | mk tailResult sourceEnd =>
        rw [tailRun] at sourceSequence
        obtain ⟨targetEnd, targetTail, endRel, tailOk⟩ := tailIH last targetLast sourceEnd tailResult bound tailRun lastRel
        have targetSequence := ClosProps.evaluate_cons_value head tail env target targetLast value targetHead
        rw [targetTail] at targetSequence
        rw [sourceSequence] at run
        cases tailResult with
        | err error =>
          simp at run targetSequence
          rcases run with ⟨rfl, rfl⟩
          exact ⟨targetEnd, targetSequence, endRel, tailOk⟩
        | val tailValues =>
          simp at run targetSequence
          rcases run with ⟨rfl, rfl⟩
          exact ⟨targetEnd, targetSequence, endRel, by simpa [resultNoInstall, valuesNoInstall, valueOk] using tailOk⟩

/-- Raising an expression agrees when evaluation of the expression agrees. -/
theorem evaluate_raise_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (target last : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (bodyResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate [body] env target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.raise trace body] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.raise trace body] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  cases bodyRun : ClosSem.evaluate [body] env source with
  | mk bodyResult last =>
    rw [ClosSem.evaluate, bodyRun] at run
    obtain ⟨targetLast, targetBody, lastRel, bodyOk⟩ := bodyIH target last bodyResult bodyRun related
    cases bodyResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, bodyOk⟩
      rw [ClosSem.evaluate, targetBody]
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value body env source last values bodyRun
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, ?_⟩
      · rw [ClosSem.evaluate, targetBody]; simp
      · simpa [resultNoInstall, valuesNoInstall] using bodyOk

/-- Let bindings agree when both binding and body evaluations agree. -/
theorem evaluate_let_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true)
    (bindingsIH : ∀ (target last : ClosSem.State C F) (bindingResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate bindings env source = (bindingResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate bindings env target = (bindingResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bindingResult)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start target last : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ source.clock →
      valuesNoInstall bodyEnv = true → ClosSem.evaluate [body] bodyEnv start = (bodyResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [body] bodyEnv target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.let trace bindings body] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.let trace bindings body] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases bindingsRun : ClosSem.evaluate bindings env source with
  | mk bindingResult last =>
    have bound : last.clock ≤ source.clock := by
      have clock := ClosSem.evaluate_clock_le bindings env source
      simpa [bindingsRun] using clock
    rw [bindingsRun] at run
    obtain ⟨targetLast, targetBindings, lastRel, bindingOk⟩ := bindingsIH target last bindingResult bindingsRun related
    cases bindingResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, bindingOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBindings]
    | val values =>
      dsimp only at run
      have bodyEnvOk := (valuesNoInstall_append values env).2 ⟨bindingOk, envOk⟩
      obtain ⟨targetFinal, targetBody, finalRel, resultOk⟩ :=
        bodyIH (values ++ env) last targetLast final result bound bodyEnvOk run lastRel
      refine ⟨targetFinal, ?_, finalRel, resultOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBindings]
      exact targetBody

/-- Conditionals agree when their test and the selected branch agree. -/
theorem evaluate_if_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (conditionIH : ∀ (target last : ClosSem.State C F) (testResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [condition] env source = (testResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate [condition] env target = (testResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall testResult)
    (branchIH : ∀ (choice : Bool) (start target last : ClosSem.State C F)
      (branchResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ source.clock →
      ClosSem.evaluate [if choice then yes else no] env start = (branchResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [if choice then yes else no] env target = (branchResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall branchResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.ifThenElse trace condition yes no] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.ifThenElse trace condition yes no] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases conditionRun : ClosSem.evaluate [condition] env source with
  | mk testResult last =>
    have bound : last.clock ≤ source.clock := by
      have clock := ClosSem.evaluate_clock_le [condition] env source
      simpa [conditionRun] using clock
    rw [conditionRun] at run
    obtain ⟨targetLast, targetTest, lastRel, testOk⟩ := conditionIH target last testResult conditionRun related
    cases testResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, testOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetTest]
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value condition env source last values conditionRun
      dsimp only at run
      cases boolRun : ClosSem.asBool value with
      | none =>
        simp [boolRun] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨targetLast, ?_, lastRel, trivial⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetTest]
        simp [boolRun]
      | some choice =>
        cases choice with
        | false =>
          simp [boolRun] at run
          obtain ⟨targetFinal, targetBranch, finalRel, resultOk⟩ := branchIH false last targetLast final result bound run lastRel
          refine ⟨targetFinal, ?_, finalRel, resultOk⟩
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetTest]
          simpa [boolRun] using targetBranch
        | true =>
          simp [boolRun] at run
          obtain ⟨targetFinal, targetBranch, finalRel, resultOk⟩ := branchIH true last targetLast final result bound run lastRel
          refine ⟨targetFinal, ?_, finalRel, resultOk⟩
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetTest]
          simpa [boolRun] using targetBranch

/-- Handlers agree when the body and the handler for a safe exception agree. -/
theorem evaluate_handle_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (envOk : valuesNoInstall env = true)
    (bodyIH : ∀ (target last : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate [body] env source = (bodyResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate [body] env target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (handlerIH : ∀ (value : ClosSem.Value) (start target last : ClosSem.State C F)
      (handlerResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ source.clock →
      valuesNoInstall (value :: env) = true →
      ClosSem.evaluate [handler] (value :: env) start = (handlerResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [handler] (value :: env) target = (handlerResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall handlerResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.handle trace body handler] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.handle trace body handler] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases bodyRun : ClosSem.evaluate [body] env source with
  | mk bodyResult last =>
    have bound : last.clock ≤ source.clock := by
      have clock := ClosSem.evaluate_clock_le [body] env source
      simpa [bodyRun] using clock
    rw [bodyRun] at run
    obtain ⟨targetLast, targetBody, lastRel, bodyOk⟩ := bodyIH target last bodyResult bodyRun related
    cases bodyResult with
    | val values =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, bodyOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBody]
    | err error =>
      cases error with
      | abort reason =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨targetLast, ?_, lastRel, bodyOk⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBody]
      | raise value =>
        dsimp only at run
        have handlerEnvOk : valuesNoInstall (value :: env) = true := by
          simp [valuesNoInstall, (show valueNoInstall value = true from bodyOk), envOk]
        obtain ⟨targetFinal, targetHandler, finalRel, resultOk⟩ := handlerIH value last targetLast final result bound handlerEnvOk run lastRel
        refine ⟨targetFinal, ?_, finalRel, resultOk⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetBody]
        exact targetHandler

/-- Closure construction agrees on related states. -/
theorem evaluate_fn_noInstall_relation {C F : Type} (name : Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value) (bodyOk : ClosLang.hasInstall body = false)
    (envOk : valuesNoInstall env = true) (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.fn name location selected arity body] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.fn name location selected arity body] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  have resultOk := stateRelNoInstall_result [.fn name location selected arity body] env source target final result
    (by simp [ClosLang.hasInstallList, ClosLang.hasInstall, bodyOk]) envOk related run
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simp [ClosSem.evaluate.eq_def, arityOk] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simp [ClosSem.evaluate.eq_def, maxEq, arityOk], related, resultOk⟩
    | some names =>
      cases captured : ClosSem.lookupVars names env with
      | none =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, by simp [ClosSem.evaluate.eq_def, maxEq, arityOk, captured], related, resultOk⟩
      | some values =>
        simp [ClosSem.evaluate.eq_def, arityOk, captured] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, by simp [ClosSem.evaluate.eq_def, maxEq, arityOk, captured], related, resultOk⟩
  · simp [ClosSem.evaluate.eq_def, arityOk] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluate.eq_def, maxEq, arityOk], related, resultOk⟩

/-- Tick evaluation agrees when the body agrees at the decremented clock. -/
theorem evaluate_tick_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ (start target last : ClosSem.State C F) (bodyResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock < source.clock → ClosSem.evaluate [body] env start = (bodyResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [body] env target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.tick trace body] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.tick trace body] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  have clockEq := stateRelNoInstall_clock related
  rw [ClosSem.evaluate] at run
  by_cases zero : source.clock = 0
  · simp [zero] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluate, clockEq, zero], related, trivial⟩
  · simp [zero] at run
    have smaller : (ClosSem.decClock 1 source).clock < source.clock := by simp [ClosSem.decClock]; omega
    obtain ⟨targetFinal, targetBody, finalRel, resultOk⟩ :=
      bodyIH _ _ final result smaller run (stateRelNoInstall_decClock source target related 1)
    refine ⟨targetFinal, ?_, finalRel, resultOk⟩
    simpa [ClosSem.evaluate, clockEq, zero] using targetBody

/-- Recursive bindings agree when the resulting safe closure environment
leads to agreeing body evaluations. -/
theorem evaluate_letrec_noInstall_relation_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ClosSem.Value) (source target final : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (functionsOk : ClosLang.hasInstallFuns functions = false) (envOk : valuesNoInstall env = true)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (target last : ClosSem.State C F)
      (bodyResult : Result (List ClosSem.Value) ClosSem.Value), valuesNoInstall bodyEnv = true →
      ClosSem.evaluate [body] bodyEnv source = (bodyResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate [body] bodyEnv target = (bodyResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall bodyResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.letrec names location selected functions body] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.letrec names location selected functions body] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  have maxEq : target.maxApp = source.maxApp := related.1.2.2.2.1
  by_cases good : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
  · cases selected with
    | none =>
      rw [ClosSem.evaluate.eq_def] at run
      dsimp only at run
      rw [if_pos good] at run
      have bodyEnvOk : valuesNoInstall
          ((List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] env functions i) ++ env) = true :=
        (valuesNoInstall_append _ _).2 ⟨recursiveClosure_bundle_noInstall location env functions envOk functionsOk, envOk⟩
      obtain ⟨targetFinal, targetBody, finalRel, resultOk⟩ := bodyIH _ target final result bodyEnvOk run related
      refine ⟨targetFinal, ?_, finalRel, resultOk⟩
      rw [ClosSem.evaluate.eq_def]
      dsimp only
      rw [if_pos (by simpa [maxEq] using good)]
      exact targetBody
    | some selected =>
      cases captured : ClosSem.lookupVars selected env with
      | none =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        simp at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨target, ?_, related, trivial⟩
        rw [ClosSem.evaluate.eq_def]
        dsimp only
        rw [if_pos (by simpa [maxEq] using good), captured]
        simp
      | some values =>
        rw [ClosSem.evaluate.eq_def] at run
        dsimp only at run
        rw [if_pos good, captured] at run
        dsimp only at run
        have capturedOk := lookupVars_noInstall selected env values envOk captured
        have bodyEnvOk : valuesNoInstall
            ((List.range functions.length).map (fun i => ClosSem.Value.recclosure location [] values functions i) ++ env) = true :=
          (valuesNoInstall_append _ _).2 ⟨recursiveClosure_bundle_noInstall location values functions capturedOk functionsOk, envOk⟩
        obtain ⟨targetFinal, targetBody, finalRel, resultOk⟩ := bodyIH _ target final result bodyEnvOk run related
        refine ⟨targetFinal, ?_, finalRel, resultOk⟩
        rw [ClosSem.evaluate.eq_def]
        dsimp only
        rw [if_pos (by simpa [maxEq] using good), captured]
        exact targetBody
  · rw [ClosSem.evaluate.eq_def] at run
    dsimp only at run
    rw [if_neg good] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨target, ?_, related, trivial⟩
    rw [ClosSem.evaluate.eq_def]
    dsimp only
    rw [if_neg (by simpa [maxEq] using good)]
    simp

/-- Direct calls agree because the related code stores are both empty. -/
theorem evaluate_call_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (target last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (argResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate args env target = (argResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall argResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.call trace ticks location args] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.call trace ticks location args] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases argsRun : ClosSem.evaluate args env source with
  | mk argResult last =>
    rw [argsRun] at run
    obtain ⟨targetLast, targetArgs, lastRel, argOk⟩ := argsIH target last argResult argsRun related
    cases argResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, argOk⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
    | val arguments =>
      have sourceCode : last.code = HolFiniteMapExact.empty := lastRel.1.2.1
      have targetCode : targetLast.code = HolFiniteMapExact.empty := lastRel.1.2.2.1
      simp [ClosSem.findCode, sourceCode, HolFiniteMapExact.empty] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetLast, ?_, lastRel, trivial⟩
      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgs]
      simp [ClosSem.findCode, targetCode, HolFiniteMapExact.empty]

/-- Application expressions agree when their arguments, function, and
closure application agree. -/
theorem evaluate_app_noInstall_relation_step {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (source target final : ClosSem.State C F) (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ∀ (target last : ClosSem.State C F) (argResult : Result (List ClosSem.Value) ClosSem.Value),
      ClosSem.evaluate args env source = (argResult, last) → StateRelNoInstall source target →
      ∃ targetLast, ClosSem.evaluate args env target = (argResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall argResult)
    (functionIH : ∀ (start target last : ClosSem.State C F) (functionResult : Result (List ClosSem.Value) ClosSem.Value),
      start.clock ≤ source.clock → ClosSem.evaluate [function] env start = (functionResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluate [function] env target = (functionResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall functionResult)
    (appIH : ∀ (value : ClosSem.Value) (arguments : List ClosSem.Value) (start target last : ClosSem.State C F)
      (appResult : Result (List ClosSem.Value) ClosSem.Value), start.clock ≤ source.clock →
      valueNoInstall value = true → valuesNoInstall arguments = true →
      ClosSem.evaluateApp location value arguments start = (appResult, last) → StateRelNoInstall start target →
      ∃ targetLast, ClosSem.evaluateApp location value arguments target = (appResult, targetLast) ∧
        StateRelNoInstall last targetLast ∧ resultNoInstall appResult)
    (related : StateRelNoInstall source target)
    (run : ClosSem.evaluate [.app trace location function args] env source = (result, final)) :
    ∃ targetFinal, ClosSem.evaluate [.app trace location function args] env target = (result, targetFinal) ∧
      StateRelNoInstall final targetFinal ∧ resultNoInstall result := by
  rw [ClosSem.evaluate] at run
  by_cases empty : args.isEmpty = true
  · simp [empty] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [ClosSem.evaluate, empty], related, trivial⟩
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, ClosSem.fixClock_evaluate] at run
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
        rw [ClosSem.evaluate]
        simp only [empty, Bool.false_eq_true, ↓reduceIte]
        rw [ClosSem.fixClock_evaluate, targetArgs]
      | val arguments =>
        dsimp only at run
        cases functionRun : ClosSem.evaluate [function] env last with
        | mk functionResult mid =>
          have functionBound : mid.clock ≤ last.clock := by
            have clock := ClosSem.evaluate_clock_le [function] env last
            simpa [functionRun] using clock
          rw [functionRun] at run
          obtain ⟨targetMid, targetFunction, midRel, functionOk⟩ :=
            functionIH last targetLast mid functionResult bound functionRun lastRel
          cases functionResult with
          | err error =>
            simp at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨targetMid, ?_, midRel, functionOk⟩
            rw [ClosSem.evaluate]
            simp only [empty, Bool.false_eq_true, ↓reduceIte]
            rw [ClosSem.fixClock_evaluate, targetArgs, ClosSem.fixClock_evaluate, targetFunction]
          | val values =>
            obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value function env last mid values functionRun
            dsimp only at run
            have valueOk : valueNoInstall value = true := by simpa [resultNoInstall, valuesNoInstall] using functionOk
            obtain ⟨targetFinal, targetApp, finalRel, resultOk⟩ :=
              appIH value arguments mid targetMid final result (by omega) valueOk argOk run midRel
            refine ⟨targetFinal, ?_, finalRel, resultOk⟩
            rw [ClosSem.evaluate]
            simp only [empty, Bool.false_eq_true, ↓reduceIte]
            rw [ClosSem.fixClock_evaluate, targetArgs, ClosSem.fixClock_evaluate, targetFunction]
            exact targetApp

end Flapjack.Compiler.Backend.ClosInterp
