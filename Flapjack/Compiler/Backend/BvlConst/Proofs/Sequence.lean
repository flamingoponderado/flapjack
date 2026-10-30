import Flapjack.Compiler.Backend.BvlConst.Proofs.Variables
/-! List and operation cases of constant-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Cons case of the source list simulation, using the recursive singleton
and tail hypotheses. Untagged for the environment relation's nested state. -/
theorem evaluate_compile_cons {C F : Type} (x : Bvl.Exp) (rest : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (headIH : ∀ (s t : State C F) r, evaluateTuple ([x], source, s) = (r, t) →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing annotations x], target, s) = (r, t))
    (tailIH : ∀ (s t : State C F) r, evaluateTuple (rest, source, s) = (r, t) →
      r ≠ .err (.abort .typeError) → evaluateTuple (compileList annotations rest, target, s) = (r, t))
    (run : evaluateTuple (x :: rest, source, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple (compileList annotations (x :: rest), target, state) = (result, final) := by
  rw [compileList, evaluateCons]
  rw [evaluateCons] at run
  cases head : evaluateTuple ([x], source, state) with
  | mk headResult next =>
    cases headResult with
    | err error =>
      simp only [head] at run
      have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := headIH state next (.err error) head ok
      rw [mapped]
      exact run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x source state values next head
      have mapped := headIH state next (.val [value]) head (by simp)
      rw [mapped]
      dsimp only
      simp only [head] at run
      cases tail : evaluateTuple (rest, source, next) with
      | mk tailResult last =>
        cases tailResult with
        | err error =>
          simp only [tail] at run
          have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
            intro bad
            apply notTypeError
            exact (congrArg Prod.fst run).symm.trans bad
          have mappedTail := tailIH next last (.err error) tail ok
          rw [mappedTail]
          exact run
        | val vs =>
          have mappedTail := tailIH next last (.val vs) tail (by simp)
          rw [mappedTail]
          simpa [tail] using run


/-- Expand operation evaluation after evaluating its arguments. This is a
Flapjack helper for the operation case of the source simulation. -/
theorem evaluate_operation {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op op args], env, state) =
      match evaluateTuple (args, env, state) with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match doApp op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, final) => (.val [value], final) := by
  change evaluate [.op op args] env state = _
  rw [evaluate, fixClock_evaluate]
  cases h : evaluate args env state with
  | mk result next =>
    cases result with
    | val values => simp only [evaluateTuple, h]; rfl
    | err error => simp only [evaluateTuple, h]

/-- The operation case of constant-propagation simulation. The premise is
exactly the recursive argument-list simulation. It remains untagged because
the relation quantifies over the finite-map state. -/
theorem evaluate_compile_op {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (ih : ∀ (s t : State C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList annotations args, target, s) = (r, t))
    (run : evaluateTuple ([.op op args], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.op op args)], target, state) = (result, final) := by
  have compiledOp : evaluateTuple ([.op op (compileList annotations args)], target, state) = (result, final) := by
    rw [evaluate_operation] at run ⊢
    cases original : evaluateTuple (args, source, state) with
    | mk argResult next =>
      cases argResult with
      | err error =>
        simp only [original] at run
        have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have transformed := ih state next (.err error) original related ok
        rw [transformed]
        exact run
      | val values =>
        have transformed := ih state next (.val values) original related (by simp)
        rw [transformed]
        simpa [original] using run
  simpa only [compileSing] using
    smartOp_correct op (compileList annotations args) target state final result compiledOp notTypeError


/-- Apply the operation simulation to the executed bounded traversal. This
Flapjack helper retains the same recursive argument-list hypothesis. -/
theorem evaluate_compileBounded_op {C F : Type} (fuel : Nat) (op : ClosLang.Op) (args : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (ih : ∀ (s t : State C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList annotations args, target, s) = (r, t))
    (run : evaluateTuple ([.op op args], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel annotations (.op op args) = some output ∧
      evaluateTuple ([output], target, state) = (result, final) := by
  exact ⟨compileSing annotations (.op op args), compileBounded_eq fuel annotations _,
    evaluate_compile_op op args annotations source target state final result ih run related notTypeError⟩

end Flapjack.Compiler.Backend.BvlConst.Proofs
