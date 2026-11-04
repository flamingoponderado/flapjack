import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateOrdinaryWellformed

/-! Fuel-aware well-formedness for closure evaluator control flow. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- An empty expression list returns an empty value list without changing
the well-formed state. -/
theorem evaluate_nil_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    EvalWellFormedFuel fuel g allowed code (evaluate [] env state) := by
  rw [evaluate]
  exact ⟨.nil, stateWf⟩

/-- A variable lookup leaves the state unchanged, including on a type error. -/
theorem evaluate_var_state_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.var trace index] env state) := by
  refine ⟨evaluate_var_wellFormedFuel trace index env state envWf, ?_⟩
  cases lookup : env[index]? <;> simpa [evaluate, lookup] using stateWf

/-- Numbered function creation preserves both the value and state
invariants, given the bounded relation for its body. -/
theorem evaluate_fn_state_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (name : Flapjack.Basis.Pure.MlString.MlString) (loc arity : Nat)
    (selected : Option (List Nat)) (body : ClosLang.Exp) (targets : List (Nat × ClosLang.Exp))
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (closure : recClosureRelFuel fuel g allowed code loc [(arity, body)] targets) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.fn name (some loc) selected arity body] env state) := by
  by_cases valid : arity ≤ state.maxApp ∧ arity ≠ 0
  · cases selected with
    | none =>
      simpa [evaluate, valid, EvalWellFormedFuel, ResultWellFormedFuel] using
        And.intro (ValuesWellFormedFuel.cons (.closure .nil envWf closure) .nil) stateWf
    | some indices =>
      cases found : lookupVars indices env with
      | none => simpa [evaluate, valid, found, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
      | some captured =>
        have capturedWf := lookupVars_wellFormedFuel indices env captured envWf found
        simpa [evaluate, valid, found, EvalWellFormedFuel, ResultWellFormedFuel] using
          And.intro (ValuesWellFormedFuel.cons (.closure .nil capturedWf closure) .nil) stateWf
  · cases selected <;> simpa [evaluate, valid, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf

/-- Recursive closure construction preserves the state invariant as well as
the result invariant when the body preserves both for well-formed inputs. -/
theorem evaluate_letrec_state_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)}
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Nat)
    (selected : Option (List Nat)) (fns targets : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (closure : recClosureRelFuel fuel g allowed code loc fns targets)
    (bodyIH : ∀ bodyEnv, ValuesWellFormedFuel fuel g allowed code bodyEnv →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] bodyEnv state)) :
    EvalWellFormedFuel fuel g allowed code
      (evaluate [.letrec names (some loc) selected fns body] env state) := by
  rw [evaluate.eq_def]
  by_cases valid : fns.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · simp only [valid, ↓reduceIte]
    cases selected with
    | none =>
      simp only
      exact bodyIH _ (valuesWellFormedFuel_append
        (recClosureBundle_wellFormedFuel loc env fns targets envWf closure) envWf)
    | some indices =>
      cases found : lookupVars indices env with
      | none => simpa [found, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
      | some captured =>
        simp only [found]
        exact bodyIH _ (valuesWellFormedFuel_append
          (recClosureBundle_wellFormedFuel loc captured fns targets
            (lookupVars_wellFormedFuel indices env captured envWf found) closure) envWf)
  · simpa [valid, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf

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
      start.clock ≤ state.clock → ValuesWellFormedFuel fuel g allowed code bodyEnv →
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] bodyEnv start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.let trace bindings body] env state) := by
  cases bindingsRun : evaluate bindings env state with
  | mk result final =>
    rw [bindingsRun] at bindingsIH
    rw [evaluate, fixClock_evaluate, bindingsRun]
    cases result with
    | err error => exact bindingsIH
    | val values =>
      have bound := evaluate_clock_le bindings env state
      rw [bindingsRun] at bound
      exact bodyIH (values ++ env) final bound (valuesWellFormedFuel_append bindingsIH.1 envWf) bindingsIH.2

/-- A handler receives a well-formed raised payload, and other outcomes are
propagated without changing the invariant. -/
theorem evaluate_handle_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (envWf : ValuesWellFormedFuel fuel g allowed code env)
    (bodyIH : EvalWellFormedFuel fuel g allowed code (evaluate [body] env state))
    (handlerIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → ValuesWellFormedFuel fuel g allowed code bodyEnv →
      StateWellFormedFuel fuel g allowed code start →
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
      | raise value =>
        have bound := evaluate_clock_le [body] env state
        rw [bodyRun] at bound
        exact handlerIH (value :: env) final bound (.cons bodyIH.1 envWf) bodyIH.2

/-- Conditional evaluation either reports a type error or evaluates one of
its branches from the well-formed state produced by the condition. -/
theorem evaluate_if_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (conditionIH : EvalWellFormedFuel fuel g allowed code (evaluate [condition] env state))
    (yesIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → StateWellFormedFuel fuel g allowed code start → EvalWellFormedFuel fuel g allowed code (evaluate [yes] env start))
    (noIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → StateWellFormedFuel fuel g allowed code start → EvalWellFormedFuel fuel g allowed code (evaluate [no] env start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.ifThenElse trace condition yes no] env state) := by
  cases conditionRun : evaluate [condition] env state with
  | mk result final =>
    rw [conditionRun] at conditionIH
    rw [evaluate, fixClock_evaluate, conditionRun]
    cases result with
    | err error => exact conditionIH
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state final values conditionRun
      have bound := evaluate_clock_le [condition] env state
      rw [conditionRun] at bound
      cases choice : asBool value with
      | none => simpa [choice, EvalWellFormedFuel, ResultWellFormedFuel] using conditionIH.2
      | some choiceValue =>
        cases choiceValue with
        | false => simpa [choice] using noIH final bound conditionIH.2
        | true => simpa [choice] using yesIH final bound conditionIH.2

/-- Sequential expression lists preserve well-formedness when the head and
tail evaluation induction hypotheses do. -/
theorem evaluate_cons_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (headIH : EvalWellFormedFuel fuel g allowed code (evaluate [first] env state))
    (tailIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → StateWellFormedFuel fuel g allowed code start →
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
      have bound := evaluate_clock_le [first] env state
      rw [headRun] at bound
      have tailWf := tailIH headFinal bound headIH.2
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
    (fnIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [function] env start))
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → ValueWellFormedFuel fuel g allowed code value → ValuesWellFormedFuel fuel g allowed code values →
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
        have argsBound := evaluate_clock_le (first :: rest) env state
        rw [argsRun] at argsBound
        have fnWf := fnIH final argsBound argsIH.2
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
            have fnBound := evaluate_clock_le [function] env final
            rw [fnRun] at fnBound
            dsimp only at argsBound fnBound
            simpa [EvalWellFormedFuel, fixClock_evaluate, fnRun] using
              appIH fnValue values fnFinal (by omega) valueWf argsIH.1 fnWf.2

/-- A closure application preserves the bounded invariant if body evaluation
and subsequent applications preserve it at smaller clocks. -/
theorem evaluateApp_wellFormedFuel_step {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (location : Option Nat)
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → ValuesWellFormedFuel fuel g allowed code env →
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] env start))
    (appIH : ∀ (value : ClosSem.Value) (rest : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → ValueWellFormedFuel fuel g allowed code value →
      ValuesWellFormedFuel fuel g allowed code rest → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluateApp location value rest start)) :
    EvalWellFormedFuel fuel g allowed code (evaluateApp location function args state) := by
  cases args with
  | nil =>
    rw [evaluateApp]
    change ValuesWellFormedFuel fuel g allowed code [function] ∧ _
    exact ⟨.cons functionWf .nil, stateWf⟩
  | cons first rest =>
    rw [evaluateApp]
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none => simpa [found, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
    | some kind =>
      cases kind with
      | partialApp value =>
        have valueWf := destClosure_partial_wellFormedFuel state.maxApp location function
          (first :: rest) value functionWf argsWf found
        dsimp only
        split
        · simpa [EvalWellFormedFuel, ResultWellFormedFuel] using stateWellFormedFuel_clock stateWf 0
        · exact ⟨.cons valueWf .nil, stateWellFormedFuel_clock stateWf _⟩
      | fullApp body bodyEnv remaining =>
        have ⟨envWf, remainingWf⟩ := destClosure_full_wellFormedFuel state.maxApp location function
          (first :: rest) bodyEnv remaining body functionWf argsWf found
        have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        dsimp only
        split
        · simpa [EvalWellFormedFuel, ResultWellFormedFuel] using stateWellFormedFuel_clock stateWf 0
        · rename_i enough
          rw [fixClock_evaluate]
          have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
          have bodyWf := bodyIH body bodyEnv (decClock cost state) smaller envWf
            (stateWellFormedFuel_clock stateWf _)
          cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
          | mk result final =>
            rw [bodyRun] at bodyWf
            have bodyBound : final.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [bodyRun] using bound
            cases result with
            | err error => exact bodyWf
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) final values bodyRun
              cases bodyWf.1 with
              | cons valueWf tail =>
                exact appIH value remaining final (by omega) valueWf remainingWf bodyWf.2

/-- Once evaluation of closure bodies preserves the invariant, so does an
entire sequence of partial and over-applications. -/
theorem evaluateApp_wellFormedFuel_of_body {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (location : Option Nat)
    (bodyWf : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] env start))
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (stateWf : StateWellFormedFuel fuel g allowed code state) :
    EvalWellFormedFuel fuel g allowed code (evaluateApp location function args state) := by
  generalize clockEq : state.clock = clock
  induction clock using Nat.strong_induction_on generalizing function args state with
  | h clock ih =>
    apply evaluateApp_wellFormedFuel_step location function args state functionWf argsWf stateWf
    · intro body env start _ envWf startWf
      exact bodyWf body env start envWf startWf
    · intro value rest start smaller valueWf restWf startWf
      exact ih start.clock (by omega) value rest start valueWf restWf startWf rfl

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

/-- Raising a value carries forward the compiler-state and code growth of
its evaluated argument. This is Flapjack-specific infrastructure. -/
theorem evaluate_raise_growing_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : GrowingEvalWellFormedFuel fuel g allowed code (evaluate [body] env state)) :
    GrowingEvalWellFormedFuel fuel g allowed code (evaluate [.raise trace body] env state) := by
  obtain ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth, wf⟩ := bodyIH
  exact ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth,
    evaluate_raise_wellFormedFuel trace body env state wf⟩

/-- A direct call carries forward the compiler-state and code growth of its
argument evaluation. This is Flapjack-specific infrastructure. -/
theorem evaluate_call_growing_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (ticks label : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : GrowingEvalWellFormedFuel fuel g allowed code (evaluate args env state)) :
    GrowingEvalWellFormedFuel fuel g allowed code (evaluate [.call trace ticks label args] env state) := by
  obtain ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth, wf⟩ := argsIH
  exact ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth,
    evaluate_call_wellFormedFuel trace ticks label args env state wf⟩

/-- An ordinary primitive carries forward the compiler-state and code growth
of its argument evaluation. Install and force use separate cases. This is
Flapjack-specific infrastructure. -/
theorem evaluate_ordinaryOp_growing_wellFormedFuel {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : GrowingEvalWellFormedFuel fuel g allowed code (evaluate args env state)) :
    GrowingEvalWellFormedFuel fuel g allowed code (evaluate [.op trace op args] env state) := by
  obtain ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth, wf⟩ := argsIH
  exact ⟨nextG, nextAllowed, nextCode, growth, allowedGrowth, codeGrowth,
    evaluate_ordinaryOp_wellFormedFuel trace op args env state notInstall notForce wf⟩

end Flapjack.Compiler.Backend.ClosCall
