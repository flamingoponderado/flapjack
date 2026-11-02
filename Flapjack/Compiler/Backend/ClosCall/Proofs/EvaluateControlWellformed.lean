import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateOrdinaryWellformed

/-! Fuel-aware well-formedness for closure evaluator control flow. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Raising a successfully evaluated value preserves its well-formedness;
an error in the argument is propagated unchanged. -/
theorem evaluate_raise_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : EvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.raise trace body] env state) := by
  cases bodyRun : evaluate [body] env state with
  | mk result final =>
    rw [bodyRun] at bodyIH
    rw [evaluate, bodyRun]
    cases result with
    | err error => exact bodyIH
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value body env state final values bodyRun
      cases bodyIH.1 with
      | cons valueWf tail =>
        cases tail
        exact ⟨valueWf, bodyIH.2⟩

/-- A let binding runs its body with the well-formed bound values prepended
to the well-formed outer environment. -/
theorem evaluate_let_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (bindingsIH : EvalWellFormedFuel fuel g allowed code (evaluate bindings env state))
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      ValuesWellFormedFuel fuel g allowed code bodyEnv → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] bodyEnv start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.let trace bindings body] env state) := by
  cases bindingsRun : evaluate bindings env state with
  | mk result final =>
    rw [bindingsRun] at bindingsIH
    rw [evaluate, fixClock_evaluate, bindingsRun]
    cases result with
    | err error => exact bindingsIH
    | val values => exact bodyIH (values ++ env) final (valuesWellFormedFuel_append bindingsIH.1 envWf) bindingsIH.2

/-- A handler receives a well-formed raised payload, and other outcomes are
propagated without changing the invariant. -/
theorem evaluate_handle_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (bodyIH : EvalWellFormedFuel fuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      ValuesWellFormedFuel fuel g allowed code bodyEnv → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [handler] bodyEnv start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.handle trace body handler] env state) := by
  cases bodyRun : evaluate [body] env state with
  | mk result final =>
    rw [bodyRun] at bodyIH
    rw [evaluate, fixClock_evaluate, bodyRun]
    cases result with
    | val values => exact bodyIH
    | err error =>
      cases error with
      | abort reason => exact bodyIH
      | raise value => exact handlerIH (value :: env) final (.cons bodyIH.1 envWf) bodyIH.2

/-- Conditional evaluation either reports a type error or evaluates one of
its branches from the well-formed state produced by the condition. -/
theorem evaluate_if_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (conditionIH : EvalWellFormedFuel fuel g allowed code (evaluate [condition] env state))
    (yesIH : ∀ (start : ClosSem.State C F), StateWellFormedFuel fuel g allowed code start → EvalWellFormedFuel fuel g allowed code (evaluate [yes] env start))
    (noIH : ∀ (start : ClosSem.State C F), StateWellFormedFuel fuel g allowed code start → EvalWellFormedFuel fuel g allowed code (evaluate [no] env start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.ifThenElse trace condition yes no] env state) := by
  cases conditionRun : evaluate [condition] env state with
  | mk result final =>
    rw [conditionRun] at conditionIH
    rw [evaluate, fixClock_evaluate, conditionRun]
    cases result with
    | err error => exact conditionIH
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state final values conditionRun
      cases choice : asBool value with
      | none => simpa [choice, EvalWellFormedFuel, ResultWellFormedFuel] using conditionIH.2
      | some choiceValue =>
        cases choiceValue with
        | false => simpa [choice] using noIH final conditionIH.2
        | true => simpa [choice] using yesIH final conditionIH.2

/-- Sequential expression lists preserve well-formedness when the head and
tail evaluation induction hypotheses do. -/
theorem evaluate_cons_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (headIH : EvalWellFormedFuel fuel g allowed code (evaluate [first] env state))
    (tailIH : ∀ (start : ClosSem.State C F), StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate (second :: rest) env start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate (first :: second :: rest) env state) := by
  cases headRun : evaluate [first] env state with
  | mk headResult headFinal =>
    rw [headRun] at headIH
    rw [evaluate, fixClock_evaluate, headRun]
    cases headResult with
    | err error => exact headIH
    | val headValues =>
      obtain ⟨head, rfl⟩ := evaluate_singleton_value first env state headFinal headValues headRun
      have headWf : ValueWellFormedFuel fuel g allowed code head := by
        cases headIH.1 with
        | cons firstWf restWf => exact firstWf
      have tailWf := tailIH headFinal headIH.2
      cases tailRun : evaluate (second :: rest) env headFinal with
      | mk tailResult final =>
        rw [tailRun] at tailWf
        cases tailResult with
        | err error => simpa [EvalWellFormedFuel, tailRun] using tailWf
        | val values =>
          simpa [EvalWellFormedFuel, ResultWellFormedFuel, tailRun] using
            And.intro (ValuesWellFormedFuel.cons headWf tailWf.1) tailWf.2

/-- In a well-formed source state, the code map is empty, so a direct call
either propagates an argument error or fails code lookup without changing
the post-argument state. -/
theorem evaluate_call_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (ticks label : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.call trace ticks label args] env state) := by
  cases argsRun : evaluate args env state with
  | mk result final =>
    rw [argsRun] at argsIH
    rw [evaluate, fixClock_evaluate, argsRun]
    cases result with
    | err error => exact argsIH
    | val values =>
      have empty : final.code = HolFiniteMapExact.empty := argsIH.2.2.2
      simpa [EvalWellFormedFuel, ResultWellFormedFuel, findCode, empty, HolFiniteMapExact.empty] using argsIH.2

/-- Application evaluation preserves well-formedness when argument,
function, and closure-application induction hypotheses do. -/
theorem evaluate_app_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (fnIH : ∀ (start : ClosSem.State C F), StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [function] env start))
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : ClosSem.State C F),
      ValueWellFormedFuel fuel g allowed code value → ValuesWellFormedFuel fuel g allowed code values →
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluateApp location value values start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.app trace location function args] env state) := by
  cases args with
  | nil => simpa [evaluate, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) env state with
    | mk result final =>
      rw [argsRun] at argsIH
      rw [evaluate]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, argsRun]
      cases result with
      | err error => exact argsIH
      | val values =>
        rw [fixClock_evaluate]
        have fnWf := fnIH final argsIH.2
        cases fnRun : evaluate [function] env final with
        | mk fnResult fnFinal =>
          rw [fnRun] at fnWf
          cases fnResult with
          | err error => simpa [EvalWellFormedFuel, fixClock_evaluate, fnRun] using fnWf
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value function env final fnFinal fnValues fnRun
            have valueWf : ValueWellFormedFuel fuel g allowed code fnValue := by
              cases fnWf.1 with
              | cons head tail => exact head
            simpa [EvalWellFormedFuel, fixClock_evaluate, fnRun] using
              appIH fnValue values fnFinal valueWf argsIH.1 fnWf.2

/-- Tick either times out with an unchanged well-formed store or evaluates
its body after decrementing the clock. -/
theorem evaluate_tick_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (bodyIH : StateWellFormedFuel fuel g allowed code (decClock 1 state) →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] env (decClock 1 state))) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.tick trace body] env state) := by
  rw [evaluate]
  by_cases zero : state.clock = 0
  · simpa [zero, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
  · simp only [zero, ↓reduceIte]
    exact bodyIH (stateWellFormedFuel_clock stateWf _)

end Flapjack.Compiler.Backend.ClosCall
