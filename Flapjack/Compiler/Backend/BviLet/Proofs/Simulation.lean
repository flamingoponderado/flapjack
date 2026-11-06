import Flapjack.Compiler.Backend.BviLet.Proofs.Calls
import Flapjack.Compiler.Backend.BviLet.Proofs.SourceAgreement

/-! Simulation of the source-shaped BVI let optimizer. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

private theorem dropLastSize (xs : List Bvi.Exp) : sizeOf xs.dropLast ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.dropLast, List.cons.sizeOf_spec] at *
      omega

private theorem lastSize (xs : List Bvi.Exp) (nonempty : xs ≠ []) :
    sizeOf (xs.getLast nonempty) < sizeOf xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simp_wf; omega
    | cons y ys =>
      have bound := ih (by simp)
      simp only [List.getLast, List.cons.sizeOf_spec] at *
      omega

/-- Evaluation is preserved by let propagation for non-type-error results.
The captured HOL statement quantifies an unused, independently typed `ys`;
this statement omits it and uses the source-shaped `compileList`. It remains
untagged until the BVI evaluator and dispatcher have been reviewed. -/
theorem evaluate_envRel {C F : Type} (xs : List Bvi.Exp) (offsets : List Nat) (d : Nat)
    (source target : List Value) (state final : BviState C F) (result : BviResult)
    (run : evaluateTuple (xs, source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList offsets d xs, target, state) = (result, final) := by
  cases xs with
  | nil => simpa [compileList, evaluateTuple, evaluate] using run
  | cons x rest =>
    cases rest with
    | cons y rest =>
      apply evaluate_compile_cons x (y :: rest) offsets d source target state final result
      · intro s t r h ok
        simpa [compileList] using evaluate_envRel [x] offsets d source target s t r h related ok
      · intro s t r h ok
        exact evaluate_envRel (y :: rest) offsets d source target s t r h related ok
      · exact run
      · exact notTypeError
    | nil =>
      simp only [compileList] at ⊢
      cases x with
      | var index => exact evaluate_compile_var offsets d index source target state final result related run notTypeError
      | force location index => exact evaluate_compile_force location index offsets d source target state final result run related notTypeError
      | op op args =>
        apply evaluate_compile_op op args offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | tick body =>
        apply evaluate_compile_tick body offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | raise body =>
        apply evaluate_compile_raise body offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | «return» args =>
        apply evaluate_compile_return args offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | ifThenElse guard yes no =>
        apply evaluate_compile_if guard yes no offsets d source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [guard] offsets d source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [yes] offsets d source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [no] offsets d source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | call ticks dest args handler =>
        apply evaluate_compile_call ticks dest args handler offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · intro handlerBody eq value s t r h rel ok
          subst handler
          simpa [compileList] using evaluate_envRel [handlerBody] (0 :: offsets) d
            (value :: source) (value :: target) s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | letCall rets ticks dest args body =>
        apply evaluate_compile_letCall rets ticks dest args body offsets d source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args offsets d source target s t r h rel ok
        · intro values s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] (List.replicate rets 0 ++ offsets) d
            (values ++ source) (values ++ target) s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | «let» bindings body =>
        cases bindings with
        | nil =>
          apply evaluate_compile_let_empty body offsets d source target state final result
          · intro s t r h rel ok
            simpa [compileList] using evaluate_envRel [body] offsets d source target s t r h rel ok
          · exact run
          · exact related
          · exact notTypeError
        | cons first rest =>
          by_cases last : body = .var rest.length
          · subst body
            let front := (first :: rest).dropLast
            let endExp := (first :: rest).getLast (by simp)
            have split : first :: rest = front ++ [endExp] :=
              (List.dropLast_concat_getLast (by simp : first :: rest ≠ [])).symm
            have length : rest.length = front.length := by
              have sizes := congrArg List.length split
              simp only [List.length_cons, List.length_append, List.length_nil] at sizes
              omega
            rw [split, length] at run ⊢
            apply evaluate_compile_let_last_branch front endExp offsets d source target state final result
            · intro s t r h rel ok
              exact evaluate_envRel front offsets d source target s t r h rel ok
            · intro ax depth src dst s t r h rel ok
              simpa [compileList] using evaluate_envRel [endExp] ax depth src dst s t r h rel ok
            · exact run
            · exact related
            · exact notTypeError
          · apply evaluate_compile_let_normal first rest body offsets d source target state final result last
            · intro s t r h rel ok
              exact evaluate_envRel (first :: rest) offsets d source target s t r h rel ok
            · intro ax depth src dst s t r h rel ok
              simpa [compileList] using evaluate_envRel [body] ax depth src dst s t r h rel ok
            · exact run
            · exact related
            · exact notTypeError
termination_by sizeOf xs
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try (cases y <;> simp_wf <;> omega)
  all_goals try (have bound := dropLastSize (first :: rest); simp only [List.cons.sizeOf_spec] at bound; omega)
  all_goals try (have bound := lastSize (first :: rest) (by simp); simp only [List.cons.sizeOf_spec] at bound; omega)

/-- Empty-displacement specialization of the optimizer simulation. -/
theorem evaluate_compileList {C F : Type} (xs : List Bvi.Exp) (env : List Value)
    (state final : BviState C F) (result : BviResult)
    (run : evaluateTuple (xs, env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList [] 0 xs, env, state) = (result, final) :=
  evaluate_envRel xs [] 0 env env state final result run (by simp [envRel]) notTypeError

/-- The executed bounded optimizer preserves every non-type-error evaluation.
Untagged until the BVI evaluator and dispatcher have been reviewed. -/
theorem evaluate_compileBounded {C F : Type} (fuel : Nat) (expression : Bvi.Exp)
    (env : List Value) (state final : BviState C F) (result : BviResult)
    (run : evaluateTuple ([expression], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel [] 0 expression = some output ∧
      evaluateTuple ([output], env, state) = (result, final) := by
  refine ⟨compileSing [] 0 expression, compileBounded_eq_compileSing fuel [] 0 expression, ?_⟩
  simpa [compileList] using evaluate_compileList [expression] env state final result run notTypeError

end Flapjack.Compiler.Backend.BviLet.Proofs
