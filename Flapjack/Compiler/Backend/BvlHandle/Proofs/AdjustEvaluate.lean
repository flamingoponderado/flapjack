import Flapjack.Compiler.Backend.BvlHandle.Proofs.HelpersProduction
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateLength

/-! Evaluation under the handler pass's inserted environment segment. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Inserting a segment after a before agrees with the handler pass's
adjustment of any de Bruijn index, including out-of-range indices. -/
theorem getElem?_insert_adjusted {α : Type} (before inserted env : List α) (index : Nat) :
    (before ++ (inserted ++ env))[if index < before.length then index else index + inserted.length]? =
      (before ++ env)[index]? := by
  by_cases bound : index < before.length
  · simp [bound, List.getElem?_append]
  · simp only [bound, ↓reduceIte, List.getElem?_append]
    have bound' : ¬index + inserted.length < before.length := by omega
    simp only [bound', ↓reduceIte]
    have shift : index + inserted.length - before.length = (index - before.length) + inserted.length := by omega
    rw [shift]
    have notInserted : ¬index - before.length + inserted.length < inserted.length := by omega
    simp only [notInserted, ↓reduceIte]
    congr 1
    omega

/-- Variable evaluation is preserved by inserting an environment segment and
adjusting free indices. -/
theorem evaluate_handleAdjVars_var {C F : Type} (index : Nat)
    (before inserted env : List Value) (state : State C F) :
    evaluate [handleAdjVars before.length inserted.length (.var index)] (before ++ (inserted ++ env)) state =
      evaluate [.var index] (before ++ env) state := by
  simp only [handleAdjVars, evaluate]
  rw [getElem?_insert_adjusted]

/-- Thunk forcing uses the same adjusted lookup; any recursive evaluation is
performed in the thunk's own environment. -/
theorem evaluate_handleAdjVars_force {C F : Type} (location index : Nat)
    (before inserted env : List Value) (state : State C F) :
    evaluate [handleAdjVars before.length inserted.length (.force location index)]
      (before ++ (inserted ++ env)) state = evaluate [.force location index] (before ++ env) state := by
  simp only [handleAdjVars, evaluate]
  rw [getElem?_insert_adjusted]

/-- A raise preserves the evaluation correspondence of its operand. -/
theorem evaluate_handleAdjVars_raise {C F : Type} (body : Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (ih : evaluate [handleAdjVars before.length inserted.length body] (before ++ (inserted ++ env)) state =
      evaluate [body] (before ++ env) state) :
    evaluate [handleAdjVars before.length inserted.length (.raise body)] (before ++ (inserted ++ env)) state =
      evaluate [.raise body] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, ih]

/-- A tick preserves the evaluation correspondence of its operand at the
decremented clock. -/
theorem evaluate_handleAdjVars_tick {C F : Type} (body : Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (ih : evaluate [handleAdjVars before.length inserted.length body]
        (before ++ (inserted ++ env)) (decClock 1 state) =
      evaluate [body] (before ++ env) (decClock 1 state)) :
    evaluate [handleAdjVars before.length inserted.length (.tick body)] (before ++ (inserted ++ env)) state =
      evaluate [.tick body] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, ih]

/-- A primitive operation preserves the correspondence of its arguments. -/
theorem evaluate_handleAdjVars_op {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (ih : evaluate (handleAdjVarsList before.length inserted.length args) (before ++ (inserted ++ env)) state =
      evaluate args (before ++ env) state) :
    evaluate [handleAdjVars before.length inserted.length (.op op args)] (before ++ (inserted ++ env)) state =
      evaluate [.op op args] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, ih]

/-- A call evaluates the same arguments and then enters the same callee. -/
theorem evaluate_handleAdjVars_call {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (ih : evaluate (handleAdjVarsList before.length inserted.length args) (before ++ (inserted ++ env)) state =
      evaluate args (before ++ env) state) :
    evaluate [handleAdjVars before.length inserted.length (.call ticks dest args)] (before ++ (inserted ++ env)) state =
      evaluate [.call ticks dest args] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, ih]

/-- A conditional preserves the correspondence of its condition and both
branches in every intermediate state. -/
theorem evaluate_handleAdjVars_if {C F : Type} (condition yes no : Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (conditionIH : evaluate [handleAdjVars before.length inserted.length condition]
      (before ++ (inserted ++ env)) state = evaluate [condition] (before ++ env) state)
    (yesIH : ∀ next : State C F, evaluate [handleAdjVars before.length inserted.length yes]
      (before ++ (inserted ++ env)) next = evaluate [yes] (before ++ env) next)
    (noIH : ∀ next : State C F, evaluate [handleAdjVars before.length inserted.length no]
      (before ++ (inserted ++ env)) next = evaluate [no] (before ++ env) next) :
    evaluate [handleAdjVars before.length inserted.length (.ifThenElse condition yes no)]
      (before ++ (inserted ++ env)) state = evaluate [.ifThenElse condition yes no] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, conditionIH]
  repeat' split <;> simp_all

/-- Exception handlers add the raised value in front of both environments,
so the adjustment depth increases by one. -/
theorem evaluate_handleAdjVars_handle {C F : Type} (body handler : Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (bodyIH : evaluate [handleAdjVars before.length inserted.length body]
      (before ++ (inserted ++ env)) state = evaluate [body] (before ++ env) state)
    (handlerIH : ∀ (value : Value) (next : State C F),
      evaluate [handleAdjVars (value :: before).length inserted.length handler]
        ((value :: before) ++ (inserted ++ env)) next =
      evaluate [handler] ((value :: before) ++ env) next) :
    evaluate [handleAdjVars before.length inserted.length (.handle body handler)]
      (before ++ (inserted ++ env)) state = evaluate [.handle body handler] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, bodyIH]
  repeat' split <;> simp_all

/-- A let extends the binder prefix by the evaluated bindings. Successful
binding evaluation returns exactly one value for each binding. -/
theorem evaluate_handleAdjVars_let {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (bindingsIH : evaluate (handleAdjVarsList before.length inserted.length bindings)
      (before ++ (inserted ++ env)) state = evaluate bindings (before ++ env) state)
    (bodyIH : ∀ (values : List Value) (next : State C F),
      evaluate [handleAdjVars (values ++ before).length inserted.length body]
        ((values ++ before) ++ (inserted ++ env)) next =
      evaluate [body] ((values ++ before) ++ env) next) :
    evaluate [handleAdjVars before.length inserted.length (.let bindings body)]
      (before ++ (inserted ++ env)) state = evaluate [.let bindings body] (before ++ env) state := by
  simp only [handleAdjVars, evaluate, bindingsIH, fixClock_evaluate]
  cases bindingsRun : evaluate bindings (before ++ env) state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      have length := BvlProps.evaluateImpLength bindings (before ++ env) state values next bindingsRun
      have bodyEq := bodyIH values next
      simp only [List.length_append, ← length] at bodyEq
      simpa only [bindingsRun, List.append_assoc, Nat.add_comm] using bodyEq

/-- A nonempty tail remains nonempty after variable adjustment, allowing the
list evaluator to compose head and tail correspondences. -/
theorem evaluate_handleAdjVars_cons {C F : Type} (first second : Bvl.Exp) (rest : List Bvl.Exp)
    (before inserted env : List Value) (state : State C F)
    (headIH : evaluate [handleAdjVars before.length inserted.length first]
      (before ++ (inserted ++ env)) state = evaluate [first] (before ++ env) state)
    (tailIH : ∀ next : State C F,
      evaluate (handleAdjVarsList before.length inserted.length (second :: rest))
        (before ++ (inserted ++ env)) next = evaluate (second :: rest) (before ++ env) next) :
    evaluate (handleAdjVarsList before.length inserted.length (first :: second :: rest))
      (before ++ (inserted ++ env)) state = evaluate (first :: second :: rest) (before ++ env) state := by
  simp only [handleAdjVarsList] at tailIH
  simp only [handleAdjVarsList, evaluate, headIH, tailIH]

/-- Inserting a segment into the environment and adjusting free variables
preserves BVL evaluation for every expression list. Untagged pending review
of the underlying evaluator's HOL correspondence. -/
theorem evaluate_handleAdjVarsList {C F : Type} (expressions : List Bvl.Exp)
    (before inserted env : List Value) (state : State C F) :
    evaluate (handleAdjVarsList before.length inserted.length expressions)
      (before ++ (inserted ++ env)) state = evaluate expressions (before ++ env) state := by
  have allWeights : ∀ weight : Nat, ∀ (expressions : List Bvl.Exp)
      (before inserted env : List Value) (state : State C F), expsWeight expressions = weight →
      evaluate (handleAdjVarsList before.length inserted.length expressions)
        (before ++ (inserted ++ env)) state = evaluate expressions (before ++ env) state := by
    intro weight
    induction weight using Nat.strongRecOn with
    | ind weight ih =>
      intro expressions before inserted env state measure
      cases expressions with
      | nil => simp [handleAdjVarsList, evaluate]
      | cons first rest =>
        cases rest with
        | cons second tail =>
          apply evaluate_handleAdjVars_cons first second tail before inserted env state ?_ ?_
          · have h := ih (expsWeight [first]) (by simp only [expsWeight] at measure ⊢; omega)
              [first] before inserted env state rfl
            simpa [handleAdjVarsList] using h
          · intro next
            exact ih (expsWeight (second :: tail)) (by simp only [expsWeight] at measure ⊢; omega)
              (second :: tail) before inserted env next rfl
        | nil =>
          simp only [handleAdjVarsList]
          cases first with
          | var index => exact evaluate_handleAdjVars_var index before inserted env state
          | force location index => exact evaluate_handleAdjVars_force location index before inserted env state
          | raise body =>
            apply evaluate_handleAdjVars_raise body before inserted env state
            have h := ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              [body] before inserted env state rfl
            simpa [handleAdjVarsList] using h
          | tick body =>
            apply evaluate_handleAdjVars_tick body before inserted env state
            have h := ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              [body] before inserted env (decClock 1 state) rfl
            simpa [handleAdjVarsList] using h
          | op op args =>
            apply evaluate_handleAdjVars_op op args before inserted env state
            exact ih (expsWeight args) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              args before inserted env state rfl
          | call ticks dest args =>
            apply evaluate_handleAdjVars_call ticks dest args before inserted env state
            exact ih (expsWeight args) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              args before inserted env state rfl
          | ifThenElse condition yes no =>
            apply evaluate_handleAdjVars_if condition yes no before inserted env state ?_ ?_ ?_
            · have h := ih (expsWeight [condition]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [condition] before inserted env state rfl
              simpa [handleAdjVarsList] using h
            · intro next
              have h := ih (expsWeight [yes]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [yes] before inserted env next rfl
              simpa [handleAdjVarsList] using h
            · intro next
              have h := ih (expsWeight [no]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [no] before inserted env next rfl
              simpa [handleAdjVarsList] using h
          | handle body handler =>
            apply evaluate_handleAdjVars_handle body handler before inserted env state ?_ ?_
            · have h := ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [body] before inserted env state rfl
              simpa [handleAdjVarsList] using h
            · intro value next
              have h := ih (expsWeight [handler]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [handler] (value :: before) inserted env next rfl
              simpa [handleAdjVarsList] using h
          | «let» bindings body =>
            apply evaluate_handleAdjVars_let bindings body before inserted env state ?_ ?_
            · exact ih (expsWeight bindings) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                bindings before inserted env state rfl
            · intro values next
              have h := ih (expsWeight [body]) (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                [body] (values ++ before) inserted env next rfl
              simpa [handleAdjVarsList] using h
  exact allWeights (expsWeight expressions) expressions before inserted env state rfl

/-- Singleton form of environment insertion for handler variable adjustment. -/
theorem evaluate_handleAdjVars {C F : Type} (expression : Bvl.Exp)
    (before inserted env : List Value) (state : State C F) :
    evaluate [handleAdjVars before.length inserted.length expression]
      (before ++ (inserted ++ env)) state = evaluate [expression] (before ++ env) state := by
  simpa [handleAdjVarsList] using evaluate_handleAdjVarsList [expression] before inserted env state

/-- Extending the inserted segment before an existing adjusted environment
preserves evaluation when the original segment lies inside the environment. -/
theorem evaluate_handleAdjVars_extend {C F : Type} (expression : Bvl.Exp) (depth : Nat)
    (before inserted env : List Value) (state : State C F) (bound : depth ≤ env.length) :
    evaluate [handleAdjVars before.length (depth + inserted.length) expression]
      (before ++ (inserted ++ env)) state =
    evaluate [handleAdjVars before.length depth expression] (before ++ env) state := by
  let first := env.take depth
  let rest := env.drop depth
  have split : first ++ rest = env := List.take_append_drop depth env
  have length : first.length = depth := by simp [first, Nat.min_eq_left bound]
  have extended := evaluate_handleAdjVars expression before (inserted ++ first) rest state
  have original := evaluate_handleAdjVars expression before first rest state
  simp only [List.length_append, length, List.append_assoc, split] at extended original
  simpa [Nat.add_comm] using extended.trans original.symm

/-- Extensional singleton evaluation equality is preserved under handler
variable adjustment when the requested segment is available. -/
theorem handleAdjVars_evaluate_congr {C F : Type} (first second : Bvl.Exp)
    (depth shift : Nat) (env : List Value) (state : State C F)
    (equal : ∀ env, evaluate [first] env state = evaluate [second] env state)
    (bound : depth + shift ≤ env.length) :
    evaluate [handleAdjVars depth shift first] env state =
      evaluate [handleAdjVars depth shift second] env state := by
  let before := env.take depth
  let afterBefore := env.drop depth
  let inserted := afterBefore.take shift
  let rest := afterBefore.drop shift
  have beforeLength : before.length = depth := by
    simp only [before, List.length_take]
    omega
  have insertedLength : inserted.length = shift := by
    simp only [inserted, afterBefore, List.length_take, List.length_drop]
    omega
  have decomposition : before ++ (inserted ++ rest) = env := by
    have parts : inserted ++ rest = afterBefore := List.take_append_drop shift afterBefore
    rw [parts]
    exact List.take_append_drop depth env
  have firstEq := evaluate_handleAdjVars first before inserted rest state
  have secondEq := evaluate_handleAdjVars second before inserted rest state
  rw [beforeLength, insertedLength, decomposition] at firstEq secondEq
  exact firstEq.trans ((equal (before ++ rest)).trans secondEq.symm)

end Flapjack.Compiler.Backend.BvlHandle.Proofs
