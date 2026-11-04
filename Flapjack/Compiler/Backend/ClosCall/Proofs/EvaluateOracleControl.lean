import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateControlWellformed

/-! Preservation of empty oracle auxiliary output by closure evaluator
control-flow cases. These induction steps are Flapjack proof infrastructure,
not ports of a HOL declaration. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Empty lists and variable lookup leave the oracle unchanged. -/
theorem evaluate_nil_oracleAuxEmpty {C F : Type} (env : List ClosSem.Value) (state : ClosSem.State C F)
    (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [] env state).2.compileOracle := by
  simpa [evaluate] using empty

theorem evaluate_var_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [.var trace index] env state).2.compileOracle := by
  cases found : env[index]? <;> simpa [evaluate, found] using empty

/-- Creating a closure does not consult or change the compiler oracle. -/
theorem evaluate_fn_oracleAuxEmpty {C F : Type}
    (name : Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat) (arity : Nat)
    (selected : Option (List Nat)) (body : ClosLang.Exp) (env : List ClosSem.Value)
    (state : ClosSem.State C F) (empty : OracleAuxEmpty state.compileOracle) :
    OracleAuxEmpty (evaluate [.fn name loc selected arity body] env state).2.compileOracle := by
  by_cases valid : arity ≤ state.maxApp ∧ arity ≠ 0
  · cases selected with
    | none => simpa [evaluate, valid] using empty
    | some indices => cases found : lookupVars indices env <;> simpa [evaluate, valid, found] using empty
  · cases selected <;> simpa [evaluate, valid] using empty

/-- Raising propagates the oracle produced by evaluation of its argument. -/
theorem evaluate_raise_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : OracleAuxEmpty (evaluate [body] env state).2.compileOracle) :
    OracleAuxEmpty (evaluate [.raise trace body] env state).2.compileOracle := by
  cases run : evaluate [body] env state with
  | mk result final =>
    rw [run] at bodyIH
    rw [evaluate, run]
    cases result <;> exact bodyIH

/-- Let-bindings pass the updated oracle to their body. -/
theorem evaluate_let_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bindingsIH : OracleAuxEmpty (evaluate bindings env state).2.compileOracle)
    (bodyIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [body] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.let trace bindings body] env state).2.compileOracle := by
  cases run : evaluate bindings env state with
  | mk result final =>
    rw [run] at bindingsIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact bindingsIH
    | val values =>
      have bound := evaluate_clock_le bindings env state
      rw [run] at bound
      exact bodyIH (values ++ env) final bound bindingsIH

/-- Handlers preserve the oracle produced before an exception is raised. -/
theorem evaluate_handle_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bodyIH : OracleAuxEmpty (evaluate [body] env state).2.compileOracle)
    (handlerIH : ∀ (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [handler] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.handle trace body handler] env state).2.compileOracle := by
  cases run : evaluate [body] env state with
  | mk result final =>
    rw [run] at bodyIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | val values => exact bodyIH
    | err error =>
      cases error with
      | abort reason => exact bodyIH
      | raise value =>
        have bound := evaluate_clock_le [body] env state
        rw [run] at bound
        exact handlerIH (value :: env) final bound bodyIH

/-- Both conditional branches start with the condition's resulting oracle. -/
theorem evaluate_if_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (conditionIH : OracleAuxEmpty (evaluate [condition] env state).2.compileOracle)
    (yesIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [yes] env start).2.compileOracle)
    (noIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [no] env start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.ifThenElse trace condition yes no] env state).2.compileOracle := by
  cases run : evaluate [condition] env state with
  | mk result final =>
    rw [run] at conditionIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact conditionIH
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env state final values run
      have bound := evaluate_clock_le [condition] env state
      rw [run] at bound
      cases choice : asBool value with
      | none => simpa [choice] using conditionIH
      | some flag =>
        cases flag with
        | false => simpa [choice] using noIH final bound conditionIH
        | true => simpa [choice] using yesIH final bound conditionIH

/-- Sequencing passes the first expression's oracle to the remaining list. -/
theorem evaluate_cons_oracleAuxEmpty {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (headIH : OracleAuxEmpty (evaluate [first] env state).2.compileOracle)
    (tailIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate (second :: rest) env start).2.compileOracle) :
    OracleAuxEmpty (evaluate (first :: second :: rest) env state).2.compileOracle := by
  cases run : evaluate [first] env state with
  | mk result final =>
    rw [run] at headIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact headIH
    | val values =>
      cases tailRun : evaluate (second :: rest) env final with
      | mk tailResult tailFinal =>
        have bound := evaluate_clock_le [first] env state
        rw [run] at bound
        have tailEmpty := tailIH final bound headIH
        rw [tailRun] at tailEmpty
        cases tailResult <;> exact tailEmpty

/-- Application passes the oracle through argument and function evaluation. -/
theorem evaluate_app_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (fnIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [function] env start).2.compileOracle)
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluateApp location value values start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.app trace location function args] env state).2.compileOracle := by
  cases args with
  | nil => simpa [evaluate] using stateEmpty
  | cons first rest =>
    cases run : evaluate (first :: rest) env state with
    | mk result final =>
      rw [run] at argsIH
      rw [evaluate]
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      rw [fixClock_evaluate, run]
      cases result with
      | err error => exact argsIH
      | val values =>
        rw [fixClock_evaluate]
        have argsBound := evaluate_clock_le (first :: rest) env state
        rw [run] at argsBound
        have fnEmpty := fnIH final argsBound argsIH
        cases fnRun : evaluate [function] env final with
        | mk fnResult fnFinal =>
          rw [fnRun] at fnEmpty
          cases fnResult with
          | err error => exact fnEmpty
          | val fnValues =>
            obtain ⟨fnValue, rfl⟩ := evaluate_singleton_value function env final fnFinal fnValues fnRun
            have fnBound := evaluate_clock_le [function] env final
            rw [fnRun] at fnBound
            dsimp only at argsBound fnBound
            simpa using appIH fnValue values fnFinal (by omega) fnEmpty

/-- A closure application preserves oracle emptiness if body evaluation and
subsequent applications do so at smaller clocks. -/
theorem evaluateApp_oracleAuxEmpty_step {C F : Type} (location : Option Nat)
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [body] env start).2.compileOracle)
    (appIH : ∀ (value : ClosSem.Value) (rest : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluateApp location value rest start).2.compileOracle) :
    OracleAuxEmpty (evaluateApp location function args state).2.compileOracle := by
  cases args with
  | nil => simpa [evaluateApp] using stateEmpty
  | cons first rest =>
    rw [evaluateApp]
    cases found : destClosure state.maxApp location function (first :: rest) with
    | none => simpa using stateEmpty
    | some kind =>
      cases kind with
      | partialApp value =>
        dsimp only
        split <;> simpa [decClock] using stateEmpty
      | fullApp body bodyEnv remaining =>
        have remainingLt := destClosure_full_remaining_lt state.maxApp location function (first :: rest)
          bodyEnv remaining body found
        let cost := (first :: rest).length - remaining.length
        have costPositive : 0 < cost := Nat.sub_pos_of_lt remainingLt
        dsimp only
        split
        · simpa using stateEmpty
        · rename_i enough
          rw [fixClock_evaluate]
          have smaller : (decClock cost state).clock < state.clock := by simp [decClock]; omega
          have bodyEmpty := bodyIH body bodyEnv (decClock cost state) smaller stateEmpty
          cases run : evaluate [body] bodyEnv (decClock cost state) with
          | mk result final =>
            rw [run] at bodyEmpty
            have bodyBound : final.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [run] using bound
            cases result with
            | err error => exact bodyEmpty
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) final values run
              exact appIH value remaining final (by omega) bodyEmpty

/-- A clock tick does not itself modify the oracle. -/
theorem evaluate_tick_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : OracleAuxEmpty (evaluate [body] env (decClock 1 state)).2.compileOracle) :
    OracleAuxEmpty (evaluate [.tick trace body] env state).2.compileOracle := by
  rw [evaluate]
  by_cases zero : state.clock = 0
  · simpa [zero] using stateEmpty
  · simpa [zero] using bodyIH

/-- A direct call passes its arguments' oracle to the called code. -/
theorem evaluate_call_oracleAuxEmpty {C F : Type} (trace : BackendCommon.Tra)
    (ticks label : Nat) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (argsIH : OracleAuxEmpty (evaluate args env state).2.compileOracle)
    (bodyIH : ∀ (body : ClosLang.Exp) (bodyEnv : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → OracleAuxEmpty start.compileOracle →
      OracleAuxEmpty (evaluate [body] bodyEnv start).2.compileOracle) :
    OracleAuxEmpty (evaluate [.call trace ticks label args] env state).2.compileOracle := by
  cases run : evaluate args env state with
  | mk result final =>
    rw [run] at argsIH
    rw [evaluate, fixClock_evaluate, run]
    cases result with
    | err error => exact argsIH
    | val values =>
      cases found : findCode label values final.code with
      | none => simpa [found] using argsIH
      | some pair =>
        obtain ⟨bodyEnv, body⟩ := pair
        simp only [found]
        split
        · simpa using argsIH
        · have bound := evaluate_clock_le args env state
          rw [run] at bound
          dsimp only at bound
          exact bodyIH body bodyEnv (decClock (ticks + 1) final) (by simp [decClock]; omega) argsIH

/-- Recursive binding construction leaves the oracle unchanged before the body. -/
theorem evaluate_letrec_oracleAuxEmpty {C F : Type}
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Option Nat)
    (selected : Option (List Nat)) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (stateEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : ∀ bodyEnv, OracleAuxEmpty (evaluate [body] bodyEnv state).2.compileOracle) :
    OracleAuxEmpty (evaluate [.letrec names loc selected fns body] env state).2.compileOracle := by
  rw [evaluate.eq_def]
  by_cases valid : fns.all (fun (arity, _) => arity ≤ state.maxApp && arity != 0) = true
  · simp only [valid, ↓reduceIte]
    cases selected with
    | none => exact bodyIH _
    | some indices =>
      cases found : lookupVars indices env with
      | none => simpa [found] using stateEmpty
      | some captured => simpa [found] using bodyIH _
  · simpa [valid] using stateEmpty

/-- Evaluation and closure application preserve an oracle whose auxiliary
code is always empty. This is a Flapjack invariant of the proof-side
evaluator, not an asserted HOL theorem port. -/
theorem evaluate_oracleAuxEmpty {C F : Type} :
    (∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F),
      OracleAuxEmpty state.compileOracle → OracleAuxEmpty (evaluate expressions env state).2.compileOracle) ∧
    (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F),
      OracleAuxEmpty state.compileOracle → OracleAuxEmpty (evaluateApp location function args state).2.compileOracle) := by
  have all : ∀ clock : Nat,
      (∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F),
        state.clock = clock → OracleAuxEmpty state.compileOracle →
        OracleAuxEmpty (evaluateApp location function args state).2.compileOracle) ∧
      (∀ (weight : Nat) (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F),
        state.clock = clock → expsWeight expressions = weight → OracleAuxEmpty state.compileOracle →
        OracleAuxEmpty (evaluate expressions env state).2.compileOracle) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      have appAll : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
          (state : ClosSem.State C F), state.clock = clock → OracleAuxEmpty state.compileOracle →
          OracleAuxEmpty (evaluateApp location function args state).2.compileOracle := by
        intro location function args state stateClock empty
        apply evaluateApp_oracleAuxEmpty_step location function args state empty
        · intro body env start smaller startEmpty
          exact (clockIH start.clock (by omega)).2 (expsWeight [body]) [body] env start rfl rfl startEmpty
        · intro value rest start smaller startEmpty
          exact (clockIH start.clock (by omega)).1 location value rest start rfl startEmpty
      constructor
      · exact appAll
      · intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          have exprIH : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F),
              state.clock ≤ clock → expsWeight expressions < weight → OracleAuxEmpty state.compileOracle →
              OracleAuxEmpty (evaluate expressions env state).2.compileOracle := by
            intro expressions env state clockLe weightLt empty
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl empty
            · exact weightIH (expsWeight expressions) weightLt expressions env state clockEq rfl empty
          have smaller : ∀ (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F),
              state.clock < clock → OracleAuxEmpty state.compileOracle →
              OracleAuxEmpty (evaluate expressions env state).2.compileOracle := by
            intro expressions env state clockLt empty
            exact (clockIH state.clock clockLt).2 (expsWeight expressions) expressions env state rfl rfl empty
          have appBound : ∀ (location : Option Nat) (function : ClosSem.Value) (args : List ClosSem.Value)
              (state : ClosSem.State C F), state.clock ≤ clock → OracleAuxEmpty state.compileOracle →
              OracleAuxEmpty (evaluateApp location function args state).2.compileOracle := by
            intro location function args state clockLe empty
            rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
            · exact (clockIH state.clock clockLt).1 location function args state rfl empty
            · exact appAll location function args state clockEq empty
          intro expressions env state stateClock measure empty
          cases expressions with
          | nil => exact evaluate_nil_oracleAuxEmpty env state empty
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluate_cons_oracleAuxEmpty first second tail env state
              · apply exprIH [first] env state (by omega) ?_ empty
                simp only [expsWeight] at measure ⊢
                have := expWeight_pos second
                omega
              · intro start bound startEmpty
                apply exprIH (second :: tail) env start (by omega) ?_ startEmpty
                simp only [expsWeight] at measure ⊢
                have := expWeight_pos first
                omega
            | nil =>
              cases first with
              | var trace index => exact evaluate_var_oracleAuxEmpty trace index env state empty
              | fn name location selected arity body => exact evaluate_fn_oracleAuxEmpty name location arity selected body env state empty
              | raise trace body =>
                apply evaluate_raise_oracleAuxEmpty trace body env state
                apply exprIH [body] env state (by omega) ?_ empty
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | tick trace body =>
                apply evaluate_tick_oracleAuxEmpty trace body env state empty
                apply exprIH [body] env (decClock 1 state) ?_ ?_ empty
                · simp [decClock]; omega
                · simp only [expsWeight, expWeight] at measure ⊢; omega
              | op trace op args =>
                apply evaluate_op_oracleAuxEmpty trace op args env state
                · apply exprIH args env state (by omega) ?_ empty
                  simp only [expsWeight] at measure ⊢
                  have := opWeight_gt trace op args
                  omega
                · intro program start bound startEmpty
                  exact smaller program [] start (by omega) startEmpty
                · intro forceEq value start bound startEmpty
                  subst op
                  apply exprIH [appUnit (.var .none 0)] [value] start (by omega) ?_ startEmpty
                  have h := appUnit_var_weight
                  simp only [expsWeight, expWeight] at measure
                  simp only [appUnit, expsWeight, expWeight] at h ⊢
                  omega
              | «let» trace bindings body =>
                apply evaluate_let_oracleAuxEmpty trace bindings body env state
                · apply exprIH bindings env state (by omega) ?_ empty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro bodyEnv start bound startEmpty
                  apply exprIH [body] bodyEnv start (by omega) ?_ startEmpty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | letrec names location selected fns body =>
                apply evaluate_letrec_oracleAuxEmpty names location selected fns body env state empty
                intro bodyEnv
                apply exprIH [body] bodyEnv state (by omega) ?_ empty
                simp only [expsWeight, expWeight] at measure ⊢; omega
              | ifThenElse trace condition yes no =>
                apply evaluate_if_oracleAuxEmpty trace condition yes no env state
                · apply exprIH [condition] env state (by omega) ?_ empty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro start bound startEmpty
                  apply exprIH [yes] env start (by omega) ?_ startEmpty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro start bound startEmpty
                  apply exprIH [no] env start (by omega) ?_ startEmpty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | handle trace body handler =>
                apply evaluate_handle_oracleAuxEmpty trace body handler env state
                · apply exprIH [body] env state (by omega) ?_ empty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro bodyEnv start bound startEmpty
                  apply exprIH [handler] bodyEnv start (by omega) ?_ startEmpty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
              | call trace ticks location args =>
                apply evaluate_call_oracleAuxEmpty trace ticks location args env state
                · apply exprIH args env state (by omega) ?_ empty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro body bodyEnv start bound startEmpty
                  exact smaller [body] bodyEnv start (by omega) startEmpty
              | app trace location function args =>
                apply evaluate_app_oracleAuxEmpty trace location function args env state empty
                · apply exprIH args env state (by omega) ?_ empty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro start bound startEmpty
                  apply exprIH [function] env start (by omega) ?_ startEmpty
                  simp only [expsWeight, expWeight] at measure ⊢; omega
                · intro value values start bound startEmpty
                  exact appBound location value values start (by omega) startEmpty
  constructor
  · intro expressions env state empty
    exact (all state.clock).2 (expsWeight expressions) expressions env state rfl rfl empty
  · intro location function args state empty
    exact (all state.clock).1 location function args state rfl empty

/-- A closure application preserves well-formedness when body evaluation and
shorter applications preserve it for states with an empty auxiliary oracle.
This is Flapjack-specific proof infrastructure. -/
theorem evaluateApp_wellFormedFuel_step_of_oracle {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (location : Option Nat)
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (oracleEmpty : OracleAuxEmpty state.compileOracle)
    (bodyIH : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → ValuesWellFormedFuel fuel g allowed code env →
      StateWellFormedFuel fuel g allowed code start → OracleAuxEmpty start.compileOracle →
      EvalWellFormedFuel fuel g allowed code (evaluate [body] env start))
    (appIH : ∀ (value : ClosSem.Value) (rest : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock < state.clock → ValueWellFormedFuel fuel g allowed code value →
      ValuesWellFormedFuel fuel g allowed code rest → StateWellFormedFuel fuel g allowed code start → OracleAuxEmpty start.compileOracle →
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
            (stateWellFormedFuel_clock stateWf _) (by simpa [decClock] using oracleEmpty)
          have bodyOracle := (evaluate_oracleAuxEmpty (C := C) (F := F)).1 [body] bodyEnv (decClock cost state)
            (by simpa [decClock] using oracleEmpty)
          cases bodyRun : evaluate [body] bodyEnv (decClock cost state) with
          | mk result final =>
            rw [bodyRun] at bodyWf bodyOracle
            have bodyBound : final.clock ≤ (decClock cost state).clock := by
              have bound := evaluate_clock_le [body] bodyEnv (decClock cost state)
              simpa [bodyRun] using bound
            cases result with
            | err error => exact bodyWf
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body bodyEnv (decClock cost state) final values bodyRun
              cases bodyWf.1 with
              | cons valueWf tail =>
                exact appIH value remaining final (by omega) valueWf remainingWf bodyWf.2 bodyOracle

/-- Application evaluation preserves well-formedness when argument,
function, and closure-application induction hypotheses do. -/
theorem evaluate_app_wellFormedFuel_of_oracle {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra) (location : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (oracleEmpty : OracleAuxEmpty state.compileOracle)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (fnIH : ∀ (start : ClosSem.State C F), start.clock ≤ state.clock → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [function] env start))
    (appIH : ∀ (value : ClosSem.Value) (values : List ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → ValueWellFormedFuel fuel g allowed code value → ValuesWellFormedFuel fuel g allowed code values →
      StateWellFormedFuel fuel g allowed code start → OracleAuxEmpty start.compileOracle →
      EvalWellFormedFuel fuel g allowed code (evaluateApp location value values start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.app trace location function args] env state) := by
  cases args with
  | nil => simpa [evaluate, EvalWellFormedFuel, ResultWellFormedFuel] using stateWf
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) env state with
    | mk result final =>
      have argsOracle := (evaluate_oracleAuxEmpty (C := C) (F := F)).1 (first :: rest) env state oracleEmpty
      rw [argsRun] at argsIH argsOracle
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
        have fnOracle := (evaluate_oracleAuxEmpty (C := C) (F := F)).1 [function] env final argsOracle
        cases fnRun : evaluate [function] env final with
        | mk fnResult fnFinal =>
          rw [fnRun] at fnWf fnOracle
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
              appIH fnValue values fnFinal (by omega) valueWf argsIH.1 fnWf.2 fnOracle

/-- Closure application preserves well-formedness when each closure body
does so under an empty auxiliary oracle. This is Flapjack-specific proof
infrastructure and leaves body well-formedness as a premise. -/
theorem evaluateApp_wellFormedFuel_of_body_oracle {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (location : Option Nat)
    (bodyWf : ∀ (body : ClosLang.Exp) (env : List ClosSem.Value) (start : ClosSem.State C F),
      ValuesWellFormedFuel fuel g allowed code env → StateWellFormedFuel fuel g allowed code start →
      OracleAuxEmpty start.compileOracle → EvalWellFormedFuel fuel g allowed code (evaluate [body] env start))
    (function : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State C F)
    (functionWf : ValueWellFormedFuel fuel g allowed code function)
    (argsWf : ValuesWellFormedFuel fuel g allowed code args)
    (stateWf : StateWellFormedFuel fuel g allowed code state)
    (oracleEmpty : OracleAuxEmpty state.compileOracle) :
    EvalWellFormedFuel fuel g allowed code (evaluateApp location function args state) := by
  generalize clockEq : state.clock = clock
  induction clock using Nat.strong_induction_on generalizing function args state with
  | h clock ih =>
    apply evaluateApp_wellFormedFuel_step_of_oracle location function args state functionWf argsWf stateWf oracleEmpty
    · intro body env start _ envWf startWf empty
      exact bodyWf body env start envWf startWf empty
    · intro value rest start smaller valueWf restWf startWf empty
      exact ih start.clock (by omega) value rest start valueWf restWf startWf empty rfl

/-- Primitive evaluation needs only the initial oracle condition: the
general oracle-preservation theorem supplies it after argument evaluation. -/
theorem evaluate_op_wellFormedFuel_of_oracle {C F : Type} {fuel : Nat} {g : State} {allowed : Set Nat}
    {code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (oracleEmpty : OracleAuxEmpty state.compileOracle)
    (argsIH : EvalWellFormedFuel fuel g allowed code (evaluate args env state))
    (installIH : ∀ (program : List ClosLang.Exp) (start : ClosSem.State C F),
      start.clock < state.clock → StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate program [] start))
    (forceIH : op = .thunkOp .forceThunk → ∀ (value : ClosSem.Value) (start : ClosSem.State C F),
      start.clock ≤ state.clock → ValueWellFormedFuel fuel g allowed code value →
      StateWellFormedFuel fuel g allowed code start →
      EvalWellFormedFuel fuel g allowed code (evaluate [appUnit (.var .none 0)] [value] start)) :
    EvalWellFormedFuel fuel g allowed code (evaluate [.op trace op args] env state) := by
  apply evaluate_op_wellFormedFuel trace op args env state argsIH ?_ installIH forceIH
  exact ((evaluate_oracleAuxEmpty (C := C) (F := F)).1 args env state oracleEmpty) 0

end Flapjack.Compiler.Backend.ClosCall
