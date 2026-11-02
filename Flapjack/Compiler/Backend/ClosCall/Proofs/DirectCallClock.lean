import Flapjack.Compiler.Backend.ClosCall.Proofs.DirectCallLookup
import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift

/-! Clock and argument behavior of generated direct calls. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosSem SemanticPrimitivesHOL

private theorem lookupVars_append {A : Type} (xs ys : List Nat) (env : List A) :
    lookupVars (xs ++ ys) env = (do
      let left ← lookupVars xs env
      let right ← lookupVars ys env
      pure (left ++ right)) := by
  induction xs with
  | nil => simp [lookupVars]
  | cons first rest ih =>
    simp only [List.cons_append, lookupVars, ih]
    cases env[first]? <;> simp
    case some value =>
      cases lookupVars rest env with
      | none => simp
      | some values => cases lookupVars ys env <;> rfl

/-- Looking up an initial range of variables retrieves the corresponding
environment prefix. -/
theorem lookupVars_range {A : Type} (env : List A) (count : Nat) (bound : count ≤ env.length) :
    lookupVars (List.range count) env = some (env.take count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have previous : count ≤ env.length := by omega
    have atIndex : count < env.length := by omega
    rw [List.range_succ, lookupVars_append, ih previous]
    rw [List.take_succ_eq_append_getElem atIndex]
    simp only [lookupVars, List.getElem?_eq_getElem atIndex]
    rfl

/-- Evaluating variable expressions in order agrees with the corresponding
environment lookup and does not change the state. -/
theorem evaluate_variables_lookup {C F : Type} (trace : BackendCommon.Tra)
    (indices : List Nat) (env : List ClosSem.Value) (state : ClosSem.State C F) (values : List ClosSem.Value)
    (lookup : lookupVars indices env = some values) :
    evaluate (indices.map (.var trace)) env state = (.val values, state) := by
  induction indices generalizing values with
  | nil => simp [lookupVars] at lookup; subst values; simp [evaluate]
  | cons index rest ih =>
    simp only [lookupVars, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at lookup
    obtain ⟨value, found, tail, tailFound, rfl⟩ := lookup
    have firstRun : evaluate [.var trace index] env state = (.val [value], state) := by
      simp [evaluate, found]
    have tailRun := ih tail tailFound
    simp only [List.map_cons, ClosProps.evaluate_cons_value _ _ _ _ _ _ firstRun, tailRun]

/-- The generated variable list evaluates to the argument prefix without
consuming clock or changing any other state. -/
theorem evaluate_variables {C F : Type} (trace : BackendCommon.Tra) (count : Nat)
    (env : List ClosSem.Value) (state : ClosSem.State C F) (bound : count ≤ env.length) :
    evaluate (ClosCall.variables trace count) env state = (.val (env.take count), state) := by
  exact evaluate_variables_lookup trace (List.range count) env state (env.take count) (lookupVars_range env count bound)

/-- A generated stub with one extra starting tick executes the installed
body at the original clock, using the selected argument prefix. -/
theorem evaluate_generated_stub {C F : Type} (trace : BackendCommon.Tra) (label arity : Nat)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (bound : arity ≤ env.length) (code : state.code.lookup label = some (arity, body)) :
    evaluate [.call trace 0 label (ClosCall.variables trace arity)] env
      { state with clock := state.clock + 1 } = evaluate [body] (env.take arity) state := by
  rw [evaluate]
  rw [fixClock_evaluate, evaluate_variables trace arity env _ bound]
  simp [findCode, code, List.length_take, Nat.min_eq_left bound, decClock]

/-- A rewritten direct call spends its extra tick as part of the call cost.
This is a local evaluator fact; it does not establish the pass simulation. -/
theorem evaluate_rewritten_call {C F : Type} (trace : BackendCommon.Tra) (label : Nat)
    (args : List ClosLang.Exp) (env values : List ClosSem.Value)
    (state afterArgs : ClosSem.State C F) (body : ClosLang.Exp)
    (argsRun : evaluate args env state = (.val values, afterArgs))
    (code : afterArgs.code.lookup label = some (values.length, body)) :
    evaluate [.call trace values.length label args] env { state with clock := state.clock + 1 } =
      if afterArgs.clock < values.length then
        (.err (.abort .timeoutError), { afterArgs with clock := 0 })
      else evaluate [body] values (decClock values.length afterArgs) := by
  have shifted := (evaluate_addClock (C := C) (F := F)).1 args env state afterArgs
    (.val values) 1 argsRun (by simp)
  rw [evaluate, fixClock_evaluate, shifted]
  by_cases enough : values.length ≤ afterArgs.clock
  · have notShort : ¬ afterArgs.clock < values.length := by omega
    simp [findCode, code, notShort, decClock, Nat.add_sub_add_right]
  · have short : afterArgs.clock < values.length := by omega
    simp [findCode, code, short]

end Flapjack.Compiler.Backend.ClosCall
