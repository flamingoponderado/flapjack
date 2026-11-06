import Flapjack.Compiler.Backend.BvlConst.Proofs.Sequence
/-! Clock, exception and call cases of constant-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- The clock case of constant-propagation simulation. Untagged because the
recursive environment relation contains the finite-map state. -/
theorem evaluate_compile_tick {C F : Type} (body : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (ih : ∀ (s t : State C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations body], target, s) = (r, t))
    (run : evaluateTuple ([.tick body], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.tick body)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.tick (compileSing annotations body)] target state = _
  change evaluate [.tick body] source state = _ at run
  rw [evaluate] at run ⊢
  by_cases zero : state.clock = 0
  · simpa [zero] using run
  · simp only [zero, ↓reduceIte] at run ⊢
    exact ih _ _ result run related notTypeError

/-- The exception-raising case of constant propagation. Untagged because the
recursive environment relation contains the finite-map state. -/
theorem evaluate_compile_raise {C F : Type} (body : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (ih : ∀ (s t : State C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations body], target, s) = (r, t))
    (run : evaluateTuple ([.raise body], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.raise body)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.raise (compileSing annotations body)] target state = _
  change evaluate [.raise body] source state = _ at run
  rw [evaluate] at run ⊢
  cases original : evaluate [body] source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have transformed := ih state next (.err error) original related ok
      change evaluate [compileSing annotations body] target state = _ at transformed
      rw [transformed]
      exact run
    | val values =>
      have transformed := ih state next (.val values) original related (by simp)
      change evaluate [compileSing annotations body] target state = _ at transformed
      rw [transformed]
      simpa [original] using run

/-- The call case of constant propagation, preserving argument order, clock,
lookup, and state. Untagged for the environment relation's nested state. -/
theorem evaluate_compile_call {C F : Type} (ticks : Nat) (dest : Option Nat) (args : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (ih : ∀ (s t : State C F) r, evaluateTuple (args, source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList annotations args, target, s) = (r, t))
    (run : evaluateTuple ([.call ticks dest args], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.call ticks dest args)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.call ticks dest (compileList annotations args)] target state = _
  change evaluate [.call ticks dest args] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate args source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have transformed := ih state next (.err error) original related ok
      change evaluate (compileList annotations args) target state = _ at transformed
      rw [transformed]
      exact run
    | val values =>
      have transformed := ih state next (.val values) original related (by simp)
      change evaluate (compileList annotations args) target state = _ at transformed
      rw [transformed]
      simpa [original] using run


/-- The exception-handler case of constant propagation. The handler receives
the identical raised value and related extended environments. Untagged for
the environment relation's nested finite-map state. -/
theorem evaluate_compile_handle {C F : Type} (body handler : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (bodyIH : ∀ (s t : State C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations body], target, s) = (r, t))
    (handlerIH : ∀ value (s t : State C F) r, evaluateTuple ([handler], value :: source, s) = (r, t) →
      envRel C F (none :: annotations) (value :: source) (value :: target) →
      r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing (none :: annotations) handler], value :: target, s) = (r, t))
    (run : evaluateTuple ([.handle body handler], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.handle body handler)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.handle (compileSing annotations body) (compileSing (none :: annotations) handler)] target state = _
  change evaluate [.handle body handler] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate [body] source state with
  | mk inner next =>
    cases inner with
    | val values =>
      have mapped := bodyIH state next (.val values) original related (by simp)
      change evaluate [compileSing annotations body] target state = _ at mapped
      rw [mapped]
      simpa [original] using run
    | err error =>
      cases error with
      | raise value =>
        have mapped := bodyIH state next (.err (.raise value)) original related (by simp)
        change evaluate [compileSing annotations body] target state = _ at mapped
        rw [mapped]
        simp only [original] at run
        have extended : envRel C F (none :: annotations) (value :: source) (value :: target) := by
          simpa [envRel] using related
        exact handlerIH value next final result run extended notTypeError
      | abort reason =>
        simp only [original] at run
        have ok : (.err (.abort reason) : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
          intro bad
          apply notTypeError
          exact (congrArg Prod.fst run).symm.trans bad
        have mapped := bodyIH state next (.err (.abort reason)) original related ok
        change evaluate [compileSing annotations body] target state = _ at mapped
        rw [mapped]
        exact run

end Flapjack.Compiler.Backend.BvlConst.Proofs
