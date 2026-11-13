module

public import Flapjack.Compiler.Backend.BvlConst.Proofs.Let
public import Flapjack.Compiler.Backend.BvlConst.SourceCompile

@[expose] public section

/-! Full constant-propagation simulation and production corollary. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

namespace SimulationCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
    (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SimulationCarrier

/-- Curried induction engine for the constant-propagation simulation. -/
private theorem evaluate_envRel {C F : Type} (xs : List Bvl.Exp)
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

/-- Full source-shaped constant-propagation simulation. The final `ys` binder
is vacuous in the HOL statement and has an independent type. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "evaluate_env_rel"
  (fmap_as_finite_support := [refs])]
theorem evaluate_envRel_source {C F α : Type} (xs : List Bvl.Exp) (env1 : List Value)
    (s1 : Flapjack.Compiler.Backend.BvlSem.State C F) (ax : List (Option Bvl.Exp))
    (env2 : List Value) (res : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (s2 : Flapjack.Compiler.Backend.BvlSem.State C F) (_ys : α)
    (premises : evaluateTuple (xs, env1, s1) = (res, s2) ∧
      envRel C F ax env1 env2 ∧ res ≠ .err (.abort .typeError)) :
    evaluateTuple (BvlConst.compile ax xs, env2, s1) = (res, s2) := by
  exact evaluate_envRel xs ax env1 env2 s1 s2 res premises.1 premises.2.1 premises.2.2

/-- Empty-annotation specialization used by the production simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "compile_thm"
  (fmap_as_finite_support := [refs])]
theorem evaluate_compileList {C F : Type} (xs : List Bvl.Exp)
    (state : Flapjack.Compiler.Backend.BvlSem.State C F) (env : List Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (premises : evaluateTuple (xs, env, state) = (result, final) ∧
      result ≠ .err (.abort .typeError)) :
    evaluateTuple (BvlConst.compile [] xs, env, state) = (result, final) :=
  evaluate_envRel xs [] env env state final result premises.1 rfl premises.2

/-- Singleton specialization used by the production simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "evaluate_compile_exp"
  (fmap_as_finite_support := [refs])]
theorem evaluate_compileSing {C F : Type} (expression : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (premises : evaluateTuple ([expression], env, state) = (result, final) ∧
      result ≠ .err (.abort .typeError)) :
    evaluateTuple ([BvlConst.compileExp expression], env, state) = (result, final) := by
  simpa [BvlConst.compile, compileList, BvlConst.compileExp_eq] using
    evaluate_compileList [expression] state env result final premises

end Flapjack.Compiler.Backend.BvlConst.Proofs
