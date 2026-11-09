import Flapjack.Compiler.Backend.BvlConst.Proofs.Let
/-! Full constant-propagation simulation and production corollary. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Full simulation corresponding to `evaluate_env_rel`, using the total
`compileList` traversal (the source `compile_eq` relates it to `compile`).
Untagged because the environment relation quantifies over a state containing
a finite map, which has no supported nested qualifier. -/
theorem evaluate_envRel {C F : Type} (xs : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple (xs, source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList annotations xs, target, state) = (result, final) := by
  cases xs with
  | nil => simpa [compileList, evaluateTuple, evaluate] using run
  | cons x rest =>
    cases rest with
    | cons y rest =>
      apply evaluate_compile_cons x (y :: rest) annotations source target state final result
      · intro s t r h ok
        simpa [compileList] using evaluate_envRel [x] annotations source target s t r h related ok
      · intro s t r h ok
        exact evaluate_envRel (y :: rest) annotations source target s t r h related ok
      · exact run
      · exact notTypeError
    | nil =>
      simp only [compileList] at ⊢
      cases x with
      | var index => exact evaluate_compile_var index annotations source target state final result run related notTypeError
      | force location index => exact evaluate_compile_force location index annotations source target state final result run related notTypeError
      | op op args =>
        apply evaluate_compile_op op args annotations source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args annotations source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | tick body =>
        apply evaluate_compile_tick body annotations source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] annotations source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | raise body =>
        apply evaluate_compile_raise body annotations source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] annotations source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | call ticks dest args =>
        apply evaluate_compile_call ticks dest args annotations source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel args annotations source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | handle body handler =>
        apply evaluate_compile_handle body handler annotations source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] annotations source target s t r h rel ok
        · intro value s t r h rel ok
          simpa [compileList] using evaluate_envRel [handler] (none :: annotations) (value :: source) (value :: target) s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | ifThenElse guard yes no =>
        apply evaluate_compile_if guard yes no annotations source target state final result
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [guard] annotations source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [yes] annotations source target s t r h rel ok
        · intro s t r h rel ok
          simpa [compileList] using evaluate_envRel [no] annotations source target s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
      | «let» bindings body =>
        apply evaluate_compile_let bindings body annotations source target state final result
        · intro s t r h rel ok
          exact evaluate_envRel bindings annotations source target s t r h rel ok
        · intro ax src dst s t r h rel ok
          simpa [compileList] using evaluate_envRel [body] ax src dst s t r h rel ok
        · exact run
        · exact related
        · exact notTypeError
termination_by sizeOf xs
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals cases y <;> simp_wf <;> omega

/-- Empty-annotation specialization corresponding to `compile_thm`. It remains
untagged until the source `compile`/`compileList` correspondence is recorded
in Lean. -/
theorem evaluate_compileList {C F : Type} (xs : List Bvl.Exp) (env : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple (xs, env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList [] xs, env, state) = (result, final) :=
  evaluate_envRel xs [] env env state final result run rfl notTypeError

/-- Singleton specialization corresponding to `evaluate_compile_exp`. It is
untagged until the source `compile_exp`/`compileSing` correspondence is
recorded in Lean. -/
theorem evaluate_compileSing {C F : Type} (expression : Bvl.Exp) (env : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([expression], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing [] expression], env, state) = (result, final) := by
  simpa [compileList] using evaluate_compileList [expression] env state final result run notTypeError

/-- The production traversal returns a transformed expression that preserves
all non-type-error evaluations, for any initial fuel. -/
theorem evaluate_compileBounded {C F : Type} (fuel : Nat) (expression : Bvl.Exp) (env : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([expression], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel [] expression = some output ∧
      evaluateTuple ([output], env, state) = (result, final) :=
  ⟨compileSing [] expression, compileBounded_eq fuel [] expression,
    evaluate_compileSing expression env state final result run notTypeError⟩

end Flapjack.Compiler.Backend.BvlConst.Proofs
