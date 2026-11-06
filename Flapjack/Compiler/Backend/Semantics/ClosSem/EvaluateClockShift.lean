import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClockShift
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Cases of clock extension for the proof-side closure evaluator. The complete
mutual theorem, evaluator, and carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Adding clock to a variable evaluation preserves its result. -/
theorem evaluate_var_addClock {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (run : evaluate [.var trace index] env state = (result, next)) :
    evaluate [.var trace index] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases found : env[index]? <;> simp [evaluate, found] at run ⊢ <;> rcases run with ⟨rfl, rfl⟩ <;> simp

/-- Adding clock to closure creation preserves its result. -/
theorem evaluate_fn_addClock {C F : Type} (trace : Flapjack.AstHOL.VarN) (location : Option Nat)
    (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (run : evaluate [.fn trace location selected arity body] env state = (result, next)) :
    evaluate [.fn trace location selected arity body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  rw [evaluate.eq_def] at run ⊢
  dsimp only at run ⊢
  repeat' split at run <;> simp_all

/-- Raise case of evaluator clock extension, assuming the operand case. -/
theorem evaluate_raise_addClock {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List Value) Value) (childNext : State C F),
      evaluate [body] env state = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { state with clock := state.clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.raise trace body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.raise trace body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases childRun : evaluate [body] env state with
  | mk childResult childNext =>
    have childNotTimeout : childResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst childResult
      simp [evaluate, childRun] at run
      exact notTimeout run.1.symm
    have shifted := ih childResult childNext childRun childNotTimeout
    rw [evaluate, childRun] at run
    rw [evaluate, shifted]
    cases childResult <;> simp_all


/-- Tick case of evaluator clock extension, assuming its body case. -/
theorem evaluate_tick_addClock {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (ih : ∀ (childResult : Result (List Value) Value) (childNext : State C F),
      evaluate [body] env (decClock 1 state) = (childResult, childNext) →
      childResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { decClock 1 state with clock := (decClock 1 state).clock + extra } =
        (childResult, { childNext with clock := childNext.clock + extra }))
    (run : evaluate [.tick trace body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.tick trace body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
    exact (notTimeout run.1.symm).elim
  · have shiftedNonzero : state.clock + extra ≠ 0 := by omega
    have childRun : evaluate [body] env (decClock 1 state) = (result, next) := by
      simpa [evaluate, zero] using run
    have shifted := ih result next childRun notTimeout
    have clocks : decClock 1 { state with clock := state.clock + extra } =
        { decClock 1 state with clock := (decClock 1 state).clock + extra } := by
      simp only [decClock]
      congr 1
      omega
    simpa [evaluate, zero, clocks] using shifted


/-- Multi-expression list case of clock extension, assuming the head and tail
cases at their respective intermediate states. -/
theorem evaluate_list_addClock {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (env : List Value) (state next : State C F) (result : Result (List Value) Value) (extra : Nat)
    (headIH : ∀ (headResult : Result (List Value) Value) (headNext : State C F),
      evaluate [first] env state = (headResult, headNext) →
      headResult ≠ .err (.abort .timeoutError) →
      evaluate [first] env { state with clock := state.clock + extra } =
        (headResult, { headNext with clock := headNext.clock + extra }))
    (tailIH : ∀ (headNext tailNext : State C F) (tailResult : Result (List Value) Value),
      headNext.clock ≤ state.clock → evaluate (second :: rest) env headNext = (tailResult, tailNext) →
      tailResult ≠ .err (.abort .timeoutError) →
      evaluate (second :: rest) env { headNext with clock := headNext.clock + extra } =
        (tailResult, { tailNext with clock := tailNext.clock + extra }))
    (run : evaluate (first :: second :: rest) env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate (first :: second :: rest) env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases headRun : evaluate [first] env state with
  | mk headResult headNext =>
    have headBound : headNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le [first] env state
      simpa [headRun] using bound
    rw [evaluate, fixClock_evaluate, headRun] at run
    cases headResult with
    | err error =>
      simp only at run
      have headNotTimeout : Result.err error ≠ (Result.err (.abort .timeoutError) : Result (List Value) Value) := by
        intro bad
        cases run
        exact notTimeout bad
      have shiftedHead := headIH (.err error) headNext headRun headNotTimeout
      rw [evaluate, fixClock_evaluate, shiftedHead]
      cases run
      rfl
    | val values =>
      cases tailRun : evaluate (second :: rest) env headNext with
      | mk tailResult tailNext =>
        rw [tailRun] at run
        have tailNotTimeout : tailResult ≠ .err (.abort .timeoutError) := by
          intro bad
          subst tailResult
          simp at run
          exact notTimeout run.1.symm
        have shiftedHead := headIH (.val values) headNext headRun (by simp)
        have shiftedTail := tailIH headNext tailNext tailResult headBound tailRun tailNotTimeout
        rw [evaluate, fixClock_evaluate, shiftedHead, shiftedTail]
        cases tailResult <;> simp_all


/-- An ordinary primitive evaluation sequences its arguments and dispatcher. -/
theorem evaluate_ordinaryOp_eq {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    evaluate [.op trace op args] env state =
      match evaluate args env state with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => match doApp op values.reverse last with
        | .err error => (.err error, last)
        | .val (value, final) => (.val [value], final) := by
  rw [evaluate, fixClock_evaluate]
  cases argsRun : evaluate args env state with
  | mk result last =>
    cases result with
    | err error => rfl
    | val values =>
      cases op with
      | install => exact (notInstall rfl).elim
      | thunkOp operation =>
        cases operation with
        | forceThunk => exact (notForce rfl).elim
        | allocThunk mode => rfl
        | updateThunk mode => rfl
      | label | ffi | intOp | wordOp | blockOp | globOp | memOp => rfl

/-- Ordinary operator case of evaluator clock extension, assuming the
argument-list case. -/
theorem evaluate_ordinaryOp_addClock {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (ih : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (run : evaluate [.op trace op args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.op trace op args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    rw [evaluate_ordinaryOp_eq trace op args env state notInstall notForce, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shifted := ih argResult argNext argsRun argNotTimeout
    rw [evaluate_ordinaryOp_eq trace op args env _ notInstall notForce, shifted]
    cases argResult with
    | err error => simp_all
    | val values =>
      dsimp only
      rw [doApp_addClock]
      cases appRun : doApp op values.reverse argNext with
      | err error => simp_all [addClockResult]
      | val pair =>
        obtain ⟨value, final⟩ := pair
        simp_all [addClockResult]


/-- Installation case of evaluator clock extension, assuming argument and
installed-program cases. -/
theorem evaluate_install_addClock {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (argsIH : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (programIH : ∀ (program : List ClosLang.Exp) (installed final : State C F)
      (programResult : Result (List Value) Value), installed.clock < state.clock →
      evaluate program [] installed = (programResult, final) →
      programResult ≠ .err (.abort .timeoutError) →
      evaluate program [] { installed with clock := installed.clock + extra } =
        (programResult, { final with clock := final.clock + extra }))
    (run : evaluate [.op trace .install args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.op trace .install args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have argBound : argNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le args env state
      simpa [argsRun] using bound
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedArgs]
    cases argResult with
    | err error => simp_all
    | val values =>
      cases installRun : doInstall values.reverse argNext with
      | mk installResult installed =>
        cases installResult with
        | err error =>
          dsimp only at run
          rw [installRun] at run
          dsimp only at run
          have installNotTimeout : Result.err error ≠ (Result.err (.abort .timeoutError) : Result (List ClosLang.Exp) Value) := by
            intro bad
            cases bad
            simp at run
            exact notTimeout run.1.symm
          have shiftedInstall := doInstall_addClock values.reverse argNext installed (.err error) extra installRun installNotTimeout
          dsimp only
          rw [shiftedInstall]
          simp_all
        | val program =>
          dsimp only at run
          rw [installRun] at run
          dsimp only at run
          have clockInfo := doInstall_success_clock values.reverse argNext installed program installRun
          have installedSmaller : installed.clock < state.clock := by omega
          cases programRun : evaluate program [] installed with
          | mk programResult final =>
            have programNotTimeout : programResult ≠ .err (.abort .timeoutError) := by
              intro bad
              subst programResult
              rw [programRun] at run
              simp at run
              exact notTimeout run.1.symm
            have shiftedInstall := doInstall_success_addClock values.reverse argNext installed program extra installRun
            have shiftedProgram := programIH program installed final programResult installedSmaller programRun programNotTimeout
            rw [programRun] at run
            dsimp only at run ⊢
            rw [shiftedInstall]
            dsimp only
            rw [shiftedProgram]
            cases programResult <;> simp_all


/-- Let-binding case of clock extension, assuming the bindings and body cases. -/
theorem evaluate_let_addClock {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (bindingsIH : ∀ (bindingResult : Result (List Value) Value) (bindingNext : State C F),
      evaluate bindings env state = (bindingResult, bindingNext) → bindingResult ≠ .err (.abort .timeoutError) →
      evaluate bindings env { state with clock := state.clock + extra } =
        (bindingResult, { bindingNext with clock := bindingNext.clock + extra }))
    (bodyIH : ∀ (values : List Value) (bindingNext final : State C F) (bodyResult : Result (List Value) Value),
      bindingNext.clock ≤ state.clock → evaluate [body] (values ++ env) bindingNext = (bodyResult, final) →
      bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] (values ++ env) { bindingNext with clock := bindingNext.clock + extra } =
        (bodyResult, { final with clock := final.clock + extra }))
    (run : evaluate [.let trace bindings body] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.let trace bindings body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases bindingsRun : evaluate bindings env state with
  | mk bindingResult bindingNext =>
    have bound : bindingNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le bindings env state
      simpa [bindingsRun] using clock
    rw [evaluate, fixClock_evaluate, bindingsRun] at run
    have bindingsNotTimeout : bindingResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst bindingResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedBindings := bindingsIH bindingResult bindingNext bindingsRun bindingsNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedBindings]
    cases bindingResult with
    | err error => simp_all
    | val values =>
      have bodyRun : evaluate [body] (values ++ env) bindingNext = (result, next) := by simpa using run
      exact bodyIH values bindingNext next result bound bodyRun notTimeout

/-- Recursive-binding case of clock extension, assuming its body case. -/
theorem evaluate_letrec_addClock {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (ih : ∀ (newEnv : List Value), evaluate [body] newEnv state = (result, next) →
      evaluate [body] newEnv { state with clock := state.clock + extra } =
        (result, { next with clock := next.clock + extra }))
    (run : evaluate [.letrec names location selected functions body] env state = (result, next)) :
    evaluate [.letrec names location selected functions body] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  rw [evaluate.eq_def] at run ⊢
  dsimp only at run ⊢
  by_cases ok : functions.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · simp only [ok, ↓reduceIte] at run ⊢
    cases selected with
    | none => exact ih _ run
    | some indices =>
      cases captured : lookupVars indices env with
      | none => simp [captured] at run ⊢; rcases run with ⟨rfl, rfl⟩; simp
      | some values =>
        simp only [captured] at run ⊢
        exact ih _ run
  · simp only [ok] at run ⊢
    simp at run
    rcases run with ⟨rfl, rfl⟩
    rfl


/-- Handler case of clock extension, assuming its body and handler cases. -/
theorem evaluate_handle_addClock {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (bodyIH : ∀ (bodyResult : Result (List Value) Value) (bodyNext : State C F),
      evaluate [body] env state = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] env { state with clock := state.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (handlerIH : ∀ (value : Value) (bodyNext final : State C F) (handlerResult : Result (List Value) Value),
      bodyNext.clock ≤ state.clock → evaluate [handler] (value :: env) bodyNext = (handlerResult, final) →
      handlerResult ≠ .err (.abort .timeoutError) →
      evaluate [handler] (value :: env) { bodyNext with clock := bodyNext.clock + extra } =
        (handlerResult, { final with clock := final.clock + extra }))
    (run : evaluate [.handle trace body handler] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.handle trace body handler] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult bodyNext =>
    have bound : bodyNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le [body] env state
      simpa [bodyRun] using clock
    rw [evaluate, fixClock_evaluate, bodyRun] at run
    have bodyNotTimeout : bodyResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst bodyResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedBody := bodyIH bodyResult bodyNext bodyRun bodyNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedBody]
    cases bodyResult with
    | val values => simp_all
    | err error =>
      cases error with
      | abort reason => simp_all
      | raise value =>
        have handlerRun : evaluate [handler] (value :: env) bodyNext = (result, next) := by simpa using run
        exact handlerIH value bodyNext next result bound handlerRun notTimeout


/-- Conditional case of clock extension, assuming its condition and both
branch cases. -/
theorem evaluate_if_addClock {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (conditionIH : ∀ (conditionResult : Result (List Value) Value) (conditionNext : State C F),
      evaluate [condition] env state = (conditionResult, conditionNext) →
      conditionResult ≠ .err (.abort .timeoutError) →
      evaluate [condition] env { state with clock := state.clock + extra } =
        (conditionResult, { conditionNext with clock := conditionNext.clock + extra }))
    (branchIH : ∀ (choice : Bool) (conditionNext final : State C F) (branchResult : Result (List Value) Value),
      conditionNext.clock ≤ state.clock → evaluate [if choice then yes else no] env conditionNext = (branchResult, final) →
      branchResult ≠ .err (.abort .timeoutError) →
      evaluate [if choice then yes else no] env { conditionNext with clock := conditionNext.clock + extra } =
        (branchResult, { final with clock := final.clock + extra }))
    (run : evaluate [.ifThenElse trace condition yes no] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.ifThenElse trace condition yes no] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases conditionRun : evaluate [condition] env state with
  | mk conditionResult conditionNext =>
    have bound : conditionNext.clock ≤ state.clock := by
      have clock := evaluate_clock_le [condition] env state
      simpa [conditionRun] using clock
    rw [evaluate, fixClock_evaluate, conditionRun] at run
    have conditionNotTimeout : conditionResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst conditionResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedCondition := conditionIH conditionResult conditionNext conditionRun conditionNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedCondition]
    cases conditionResult with
    | err error => simp_all
    | val values =>
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => (.err (.abort .typeError), conditionNext)
        | some true => evaluate [yes] env conditionNext
        | some false => evaluate [no] env conditionNext) = (result, next) at run
      change (match asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
        | none => ((Result.err (.abort .typeError) : Result (List Value) Value), { conditionNext with clock := conditionNext.clock + extra })
        | some true => evaluate [yes] env { conditionNext with clock := conditionNext.clock + extra }
        | some false => evaluate [no] env { conditionNext with clock := conditionNext.clock + extra }) = _
      cases found : asBool (@Flapjack.holHd Value ⟨unitValue⟩ values) with
      | none => simp [found] at run ⊢; rcases run with ⟨rfl, rfl⟩; simp
      | some choice =>
        cases choice with
        | false =>
          simp only [found] at run ⊢
          exact branchIH false conditionNext next result bound run notTimeout
        | true =>
          simp only [found] at run ⊢
          exact branchIH true conditionNext next result bound run notTimeout


/-- Direct-call case of clock extension, assuming the argument and selected
body cases. -/
theorem evaluate_call_addClock {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (env : List Value) (state next : State C F)
    (result : Result (List Value) Value) (extra : Nat)
    (argsIH : ∀ (argResult : Result (List Value) Value) (argNext : State C F),
      evaluate args env state = (argResult, argNext) → argResult ≠ .err (.abort .timeoutError) →
      evaluate args env { state with clock := state.clock + extra } =
        (argResult, { argNext with clock := argNext.clock + extra }))
    (bodyIH : ∀ (body : ClosLang.Exp) (values : List Value) (bodyState bodyNext : State C F)
      (bodyResult : Result (List Value) Value), bodyState.clock < state.clock →
      evaluate [body] values bodyState = (bodyResult, bodyNext) → bodyResult ≠ .err (.abort .timeoutError) →
      evaluate [body] values { bodyState with clock := bodyState.clock + extra } =
        (bodyResult, { bodyNext with clock := bodyNext.clock + extra }))
    (run : evaluate [.call trace ticks location args] env state = (result, next))
    (notTimeout : result ≠ .err (.abort .timeoutError)) :
    evaluate [.call trace ticks location args] env { state with clock := state.clock + extra } =
      (result, { next with clock := next.clock + extra }) := by
  cases argsRun : evaluate args env state with
  | mk argResult argNext =>
    have argBound : argNext.clock ≤ state.clock := by
      have bound := evaluate_clock_le args env state
      simpa [argsRun] using bound
    rw [evaluate, fixClock_evaluate, argsRun] at run
    have argNotTimeout : argResult ≠ .err (.abort .timeoutError) := by
      intro bad
      subst argResult
      simp at run
      exact notTimeout run.1.symm
    have shiftedArgs := argsIH argResult argNext argsRun argNotTimeout
    rw [evaluate, fixClock_evaluate, shiftedArgs]
    cases argResult with
    | err error => simp_all
    | val values =>
      cases found : findCode location values argNext.code with
      | none =>
        simp [found] at run ⊢
        rcases run with ⟨rfl, rfl⟩
        simp
      | some selected =>
        obtain ⟨callValues, body⟩ := selected
        by_cases timeout : argNext.clock < ticks + 1
        · simp [found, timeout] at run
          exact (notTimeout run.1.symm).elim
        · have enough : ticks + 1 ≤ argNext.clock := by omega
          have shiftedEnough : ¬ argNext.clock + extra < ticks + 1 := by omega
          have bodyRun : evaluate [body] callValues (decClock (ticks + 1) argNext) = (result, next) := by
            simpa [found, timeout] using run
          have smaller : (decClock (ticks + 1) argNext).clock < state.clock := by
            simp only [decClock]
            omega
          have shiftedBody := bodyIH body callValues (decClock (ticks + 1) argNext) next result
            smaller bodyRun notTimeout
          have clocks : decClock (ticks + 1) { argNext with clock := argNext.clock + extra } =
              { decClock (ticks + 1) argNext with clock := (decClock (ticks + 1) argNext).clock + extra } := by
            simp only [decClock]
            congr 1
            omega
          simpa [found, shiftedEnough, clocks] using shiftedBody

end Flapjack.Compiler.Backend.ClosSem
