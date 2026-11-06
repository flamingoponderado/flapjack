import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateTicks

/-! Cases of environment extension for the BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlProps
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace ExpandEnvCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ExpandEnvCarrier

/-- The empty-expression-list case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_nil {C F : Type} (env extra : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (_notType : (evaluateTuple ([], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([], env ++ extra, state) = evaluateTuple ([], env, state) := by
  simp [evaluateTuple, evaluate]

/-- The variable case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_var {C F : Type} (index : Nat) (env extra : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (notType : (evaluateTuple ([.var index], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.var index], env ++ extra, state) = evaluateTuple ([.var index], env, state) := by
  cases found : env[index]? with
  | none => simp [evaluateTuple, evaluate, found] at notType
  | some value =>
    have bound : index < env.length := List.getElem?_eq_some_iff.mp found |>.1
    simp [evaluateTuple, evaluate, List.getElem?_append, bound]

/-- The force case needs only the original successful environment lookup: the
recursive call runs in the thunk's own argument environment. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_force {C F : Type} (location index : Nat) (env extra : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (notType : (evaluateTuple ([.force location index], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.force location index], env ++ extra, state) =
      evaluateTuple ([.force location index], env, state) := by
  cases found : env[index]? with
  | none => simp [evaluateTuple, evaluate, found] at notType
  | some value =>
    have bound : index < env.length := List.getElem?_eq_some_iff.mp found |>.1
    simp [evaluateTuple, evaluate, List.getElem?_append, bound]

/-- The tick case of environment extension, using the body induction
hypothesis at the decremented clock. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_tick {C F : Type} (body : Bvl.Exp) (env extra : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bodyIH : state.clock ≠ 0 →
      (evaluateTuple ([body], env, decClock 1 state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([body], env ++ extra, decClock 1 state) =
        evaluateTuple ([body], env, decClock 1 state))
    (notType : (evaluateTuple ([.tick body], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.tick body], env ++ extra, state) =
      evaluateTuple ([.tick body], env, state) := by
  by_cases zero : state.clock = 0
  · simp [evaluateTuple, evaluate, zero]
  · have bodyNotType : (evaluateTuple ([body], env, decClock 1 state)).1 ≠ .err (.abort .typeError) := by
      simpa [evaluateTuple, evaluate, zero] using notType
    simpa [evaluateTuple, evaluate, zero] using bodyIH zero bodyNotType

/-- The Raise case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_raise {C F : Type} (body : Bvl.Exp) (env extra : List BvlSem.Value)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bodyIH : (evaluateTuple ([body], env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([body], env ++ extra, state) = evaluateTuple ([body], env, state))
    (notType : (evaluateTuple ([.raise body], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.raise body], env ++ extra, state) = evaluateTuple ([.raise body], env, state) := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult last =>
    have bodyNotType : (evaluateTuple ([body], env, state)).1 ≠ .err (.abort .typeError) := by
      cases bodyResult with
      | val values => simp [evaluateTuple, bodyRun]
      | err error =>
        simpa [evaluateTuple, evaluate, bodyRun] using notType
    have same := bodyIH bodyNotType
    change evaluate [body] (env ++ extra) state = _ at same
    simp only [evaluateTuple, evaluate, same]

/-- The operator case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_op {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (argsIH : (evaluateTuple (args, env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple (args, env ++ extra, state) = evaluateTuple (args, env, state))
    (notType : (evaluateTuple ([.op op args], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op op args], env ++ extra, state) = evaluateTuple ([.op op args], env, state) := by
  cases argsRun : evaluate args env state with
  | mk argsResult last =>
    have argsNotType : (evaluateTuple (args, env, state)).1 ≠ .err (.abort .typeError) := by
      cases argsResult with
      | val values => simp [evaluateTuple, argsRun]
      | err error =>
        simpa [evaluateTuple, evaluate, fixClock, argsRun] using notType
    have same := argsIH argsNotType
    change evaluate args (env ++ extra) state = _ at same
    simp only [evaluateTuple, evaluate, same]

/-- The Call case of environment extension: the selected body receives the
same call arguments, independently of the caller's remaining environment. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_call {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (argsIH : (evaluateTuple (args, env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple (args, env ++ extra, state) = evaluateTuple (args, env, state))
    (notType : (evaluateTuple ([.call ticks dest args], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.call ticks dest args], env ++ extra, state) =
      evaluateTuple ([.call ticks dest args], env, state) := by
  cases argsRun : evaluate args env state with
  | mk argsResult last =>
    have argsNotType : (evaluateTuple (args, env, state)).1 ≠ .err (.abort .typeError) := by
      cases argsResult with
      | val values => simp [evaluateTuple, argsRun]
      | err error =>
        simpa [evaluateTuple, evaluate, fixClock, argsRun] using notType
    have same := argsIH argsNotType
    change evaluate args (env ++ extra) state = _ at same
    simp only [evaluateTuple, evaluate, same]

/-- The Let case of environment extension. The body receives the same bound
values before both the original and extended environments. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_let {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bindingsIH : (evaluateTuple (bindings, env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple (bindings, env ++ extra, state) = evaluateTuple (bindings, env, state))
    (bodyIH : ∀ (values : List BvlSem.Value) (middle : State C F),
      evaluateTuple (bindings, env, state) = (.val values, middle) →
      (evaluateTuple ([body], values ++ env, middle)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([body], (values ++ env) ++ extra, middle) =
        evaluateTuple ([body], values ++ env, middle))
    (notType : (evaluateTuple ([.let bindings body], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.let bindings body], env ++ extra, state) =
      evaluateTuple ([.let bindings body], env, state) := by
  cases bindingsRun : evaluate bindings env state with
  | mk bindingsResult middle =>
    have bound : middle.clock ≤ state.clock := by
      have h := evaluate_clock_le bindings env state
      simpa [bindingsRun] using h
    have bindingsNotType : (evaluateTuple (bindings, env, state)).1 ≠ .err (.abort .typeError) := by
      cases bindingsResult with
      | val values => simp [evaluateTuple, bindingsRun]
      | err error => simpa [evaluateTuple, evaluate, fixClock, bindingsRun] using notType
    have same := bindingsIH bindingsNotType
    change evaluate bindings (env ++ extra) state = evaluate bindings env state at same
    cases bindingsResult with
    | err error => simp [evaluateTuple, evaluate, same, bindingsRun, fixClock]
    | val values =>
      have bodyNotType : (evaluateTuple ([body], values ++ env, middle)).1 ≠ .err (.abort .typeError) := by
        simpa [evaluateTuple, evaluate, bindingsRun, fixClock, Nat.min_eq_right bound] using notType
      have bodySame := bodyIH values middle bindingsRun bodyNotType
      change evaluate [body] ((values ++ env) ++ extra) middle = _ at bodySame
      simpa [evaluateTuple, evaluate, same, bindingsRun, fixClock, Nat.min_eq_right bound,
        List.append_assoc] using bodySame

/-- The non-singleton list case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_cons {C F : Type} (first second : Bvl.Exp) (tail : List Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (headIH : (evaluateTuple ([first], env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([first], env ++ extra, state) = evaluateTuple ([first], env, state))
    (tailIH : ∀ (values : List BvlSem.Value) (middle : State C F),
      evaluateTuple ([first], env, state) = (.val values, middle) →
      (evaluateTuple (second :: tail, env, middle)).1 ≠ .err (.abort .typeError) →
      evaluateTuple (second :: tail, env ++ extra, middle) =
        evaluateTuple (second :: tail, env, middle))
    (notType : (evaluateTuple (first :: second :: tail, env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple (first :: second :: tail, env ++ extra, state) =
      evaluateTuple (first :: second :: tail, env, state) := by
  cases headRun : evaluate [first] env state with
  | mk headResult middle =>
    have bound : middle.clock ≤ state.clock := by
      have h := evaluate_clock_le [first] env state
      simpa [headRun] using h
    have headNotType : (evaluateTuple ([first], env, state)).1 ≠ .err (.abort .typeError) := by
      cases headResult with
      | val values => simp [evaluateTuple, headRun]
      | err error => simpa [evaluateTuple, evaluate, fixClock, headRun] using notType
    have same := headIH headNotType
    change evaluate [first] (env ++ extra) state = evaluate [first] env state at same
    cases headResult with
    | err error => simp [evaluateTuple, evaluate, same, headRun, fixClock]
    | val values =>
      cases tailRun : evaluate (second :: tail) env middle with
      | mk tailResult last =>
        have tailNotType : (evaluateTuple (second :: tail, env, middle)).1 ≠ .err (.abort .typeError) := by
          cases tailResult with
          | val values => simp [evaluateTuple, tailRun]
          | err error =>
            simpa [evaluateTuple, evaluate, headRun, fixClock, Nat.min_eq_right bound, tailRun] using notType
        have tailSame := tailIH values middle headRun tailNotType
        change evaluate (second :: tail) (env ++ extra) middle = _ at tailSame
        simp [evaluateTuple, evaluate, same, headRun, fixClock, Nat.min_eq_right bound, tailSame]

/-- The Handle case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_handle {C F : Type} (body handler : Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (bodyIH : (evaluateTuple ([body], env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([body], env ++ extra, state) = evaluateTuple ([body], env, state))
    (handlerIH : ∀ (value : BvlSem.Value) (middle : State C F),
      evaluateTuple ([body], env, state) = (.err (.raise value), middle) →
      (evaluateTuple ([handler], value :: env, middle)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([handler], (value :: env) ++ extra, middle) =
        evaluateTuple ([handler], value :: env, middle))
    (notType : (evaluateTuple ([.handle body handler], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.handle body handler], env ++ extra, state) =
      evaluateTuple ([.handle body handler], env, state) := by
  cases bodyRun : evaluate [body] env state with
  | mk bodyResult middle =>
    have bound : middle.clock ≤ state.clock := by
      have h := evaluate_clock_le [body] env state
      simpa [bodyRun] using h
    have bodyNotType : (evaluateTuple ([body], env, state)).1 ≠ .err (.abort .typeError) := by
      cases bodyResult with
      | val values => simp [evaluateTuple, bodyRun]
      | err error =>
        cases error with
        | raise value => simp [evaluateTuple, bodyRun]
        | abort reason => simpa [evaluateTuple, evaluate, fixClock, bodyRun] using notType
    have same := bodyIH bodyNotType
    change evaluate [body] (env ++ extra) state = evaluate [body] env state at same
    cases bodyResult with
    | val values => simp [evaluateTuple, evaluate, same, bodyRun, fixClock]
    | err error =>
      cases error with
      | abort reason => simp [evaluateTuple, evaluate, same, bodyRun, fixClock]
      | raise value =>
        have handlerNotType : (evaluateTuple ([handler], value :: env, middle)).1 ≠ .err (.abort .typeError) := by
          simpa [evaluateTuple, evaluate, bodyRun, fixClock, Nat.min_eq_right bound] using notType
        have handlerSame := handlerIH value middle bodyRun handlerNotType
        change evaluate [handler] ((value :: env) ++ extra) middle = _ at handlerSame
        simpa [evaluateTuple, evaluate, same, bodyRun, fixClock, Nat.min_eq_right bound] using handlerSame

/-- The If case of environment extension. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv_if {C F : Type} (condition yes no : Bvl.Exp)
    (env extra : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (conditionIH : (evaluateTuple ([condition], env, state)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([condition], env ++ extra, state) = evaluateTuple ([condition], env, state))
    (branchIH : ∀ (choice : Bool) (value : BvlSem.Value) (middle : State C F),
      evaluateTuple ([condition], env, state) = (.val [value], middle) →
      asBool value = some choice →
      (evaluateTuple ([if choice then yes else no], env, middle)).1 ≠ .err (.abort .typeError) →
      evaluateTuple ([if choice then yes else no], env ++ extra, middle) =
        evaluateTuple ([if choice then yes else no], env, middle))
    (notType : (evaluateTuple ([.ifThenElse condition yes no], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.ifThenElse condition yes no], env ++ extra, state) =
      evaluateTuple ([.ifThenElse condition yes no], env, state) := by
  cases conditionRun : evaluate [condition] env state with
  | mk conditionResult middle =>
    have bound : middle.clock ≤ state.clock := by
      have h := evaluate_clock_le [condition] env state
      simpa [conditionRun] using h
    have conditionNotType : (evaluateTuple ([condition], env, state)).1 ≠ .err (.abort .typeError) := by
      cases conditionResult with
      | val values => simp [evaluateTuple, conditionRun]
      | err error => simpa [evaluateTuple, evaluate, fixClock, conditionRun] using notType
    have same := conditionIH conditionNotType
    change evaluate [condition] (env ++ extra) state = evaluate [condition] env state at same
    cases conditionResult with
    | err error => simp [evaluateTuple, evaluate, same, conditionRun, fixClock]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton condition env state middle values conditionRun
      cases boolRun : asBool value with
      | none => simp [evaluateTuple, evaluate, conditionRun, fixClock, boolRun] at notType
      | some choice =>
        cases choice with
        | false =>
          have branchNotType : (evaluateTuple ([no], env, middle)).1 ≠ .err (.abort .typeError) := by
            simpa [evaluateTuple, evaluate, conditionRun, fixClock, Nat.min_eq_right bound, boolRun] using notType
          have branchSame := branchIH false value middle conditionRun boolRun branchNotType
          simpa [evaluateTuple, evaluate, same, conditionRun, fixClock, Nat.min_eq_right bound, boolRun] using branchSame
        | true =>
          have branchNotType : (evaluateTuple ([yes], env, middle)).1 ≠ .err (.abort .typeError) := by
            simpa [evaluateTuple, evaluate, conditionRun, fixClock, Nat.min_eq_right bound, boolRun] using notType
          have branchSame := branchIH true value middle conditionRun boolRun branchNotType
          simpa [evaluateTuple, evaluate, same, conditionRun, fixClock, Nat.min_eq_right bound, boolRun] using branchSame

/-- Adding an environment suffix preserves any BVL evaluation that does not
produce a type error. -/
@[hol "cakeml/compiler/backend/semantics/bvlPropsScript.sml" "evaluate_expand_env"
  (fmap_as_finite_support := [refs])]
theorem evaluateExpandEnv {C F : Type} (expressions : List Bvl.Exp)
    (env : List BvlSem.Value) (state : Flapjack.Compiler.Backend.BvlSem.State C F)
    (extra : List BvlSem.Value)
    (notType : (evaluateTuple (expressions, env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple (expressions, env ++ extra, state) = evaluateTuple (expressions, env, state) := by
  have allRanks : ∀ clock weight : Nat, ∀ (es : List Bvl.Exp)
      (a suffix : List BvlSem.Value) (s : State C F), s.clock = clock → expsWeight es = weight →
      (evaluateTuple (es, a, s)).1 ≠ .err (.abort .typeError) →
      evaluateTuple (es, a ++ suffix, s) = evaluateTuple (es, a, s) := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (es : List Bvl.Exp) (a suffix : List BvlSem.Value) (s : State C F),
            s.clock ≤ clock → expsWeight es < weight →
            (evaluateTuple (es, a, s)).1 ≠ .err (.abort .typeError) →
            evaluateTuple (es, a ++ suffix, s) = evaluateTuple (es, a, s) := by
          intro es a suffix s clockLe weightLt valid
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH s.clock clockLt (expsWeight es) es a suffix s rfl rfl valid
          · exact weightIH (expsWeight es) weightLt es a suffix s clockEq rfl valid
        intro es a suffix s stateClock measure valid
        cases es with
        | nil => exact evaluateExpandEnv_nil a suffix s valid
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply evaluateExpandEnv_cons first second tail a suffix s ?_ ?_ valid
            · intro h
              apply exprIH [first] a suffix s (by omega) ?_ h
              simp only [expsWeight] at measure ⊢; have := expWeight_pos second; omega
            · intro values middle run h
              change evaluate [first] a s = _ at run
              have bound : middle.clock ≤ s.clock := by
                have b := evaluate_clock_le [first] a s
                simpa [run] using b
              apply exprIH (second :: tail) a suffix middle (by omega) ?_ h
              simp only [expsWeight] at measure ⊢; omega
          | nil =>
            cases first with
            | var index => exact evaluateExpandEnv_var index a suffix s valid
            | force location index => exact evaluateExpandEnv_force location index a suffix s valid
            | tick body =>
              apply evaluateExpandEnv_tick body a suffix s ?_ valid
              intro nonzero h
              have smaller : (decClock 1 s).clock < clock := by simp [decClock]; omega
              exact clockIH (decClock 1 s).clock smaller (expsWeight [body]) [body] a suffix (decClock 1 s) rfl rfl h
            | raise body =>
              apply evaluateExpandEnv_raise body a suffix s ?_ valid
              intro h
              apply exprIH [body] a suffix s (by omega) ?_ h
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | op op args =>
              apply evaluateExpandEnv_op op args a suffix s ?_ valid
              intro h
              apply exprIH args a suffix s (by omega) ?_ h
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | call ticks dest args =>
              apply evaluateExpandEnv_call ticks dest args a suffix s ?_ valid
              intro h
              apply exprIH args a suffix s (by omega) ?_ h
              simp only [expsWeight, expWeight] at measure ⊢; omega
            | «let» bindings body =>
              apply evaluateExpandEnv_let bindings body a suffix s ?_ ?_ valid
              · intro h
                apply exprIH bindings a suffix s (by omega) ?_ h
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro values middle run h
                change evaluate bindings a s = _ at run
                have bound : middle.clock ≤ s.clock := by
                  have b := evaluate_clock_le bindings a s
                  simpa [run] using b
                apply exprIH [body] (values ++ a) suffix middle (by omega) ?_ h
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | handle body handler =>
              apply evaluateExpandEnv_handle body handler a suffix s ?_ ?_ valid
              · intro h
                apply exprIH [body] a suffix s (by omega) ?_ h
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro value middle run h
                change evaluate [body] a s = _ at run
                have bound : middle.clock ≤ s.clock := by
                  have b := evaluate_clock_le [body] a s
                  simpa [run] using b
                apply exprIH [handler] (value :: a) suffix middle (by omega) ?_ h
                simp only [expsWeight, expWeight] at measure ⊢; omega
            | ifThenElse condition yes no =>
              apply evaluateExpandEnv_if condition yes no a suffix s ?_ ?_ valid
              · intro h
                apply exprIH [condition] a suffix s (by omega) ?_ h
                simp only [expsWeight, expWeight] at measure ⊢; omega
              · intro choice value middle run _ h
                change evaluate [condition] a s = _ at run
                have bound : middle.clock ≤ s.clock := by
                  have b := evaluate_clock_le [condition] a s
                  simpa [run] using b
                apply exprIH [if choice then yes else no] a suffix middle (by omega) ?_ h
                cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte, expsWeight, expWeight] at measure ⊢ <;> omega
  exact allRanks state.clock (expsWeight expressions) expressions env extra state rfl rfl notType

end Flapjack.Compiler.Backend.BvlProps
