import Flapjack.Compiler.Backend.BvlConst.Proofs.Control
/-! Conditional case of constant-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Expose conditional compilation as a semantics-preserving source
conditional. This is Flapjack infrastructure for the recursive case. -/
theorem evaluate_compile_if_shape {C F : Type} (guard yes no : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (env : List Value) (state : State C F) :
    evaluateTuple ([compileSing annotations (.ifThenElse guard yes no)], env, state) =
    evaluateTuple ([.ifThenElse (compileSing annotations guard) (compileSing annotations yes)
      (compileSing annotations no)], env, state) := by
  simp only [compileSing]
  generalize h : compileSing annotations guard = condition
  cases condition <;> try rfl
  case op operation args =>
    cases operation <;> try rfl
    case blockOp block =>
      cases block <;> try rfl
      case cons tag =>
        cases tag with
        | zero =>
          cases args with
          | cons x xs => rfl
          | nil => simp [evaluateTuple, evaluate, fixClock, doApp, applyBlock, asBool]
        | succ tag =>
          cases tag with
          | zero =>
            cases args with
            | cons x xs => rfl
            | nil => simp [evaluateTuple, evaluate, fixClock, doApp, applyBlock, asBool]
          | succ tag => rfl

/-- The conditional case of constant propagation, including eliminated
Boolean branches. Untagged because the environment relation quantifies over
the finite-map state. -/
theorem evaluate_compile_if {C F : Type} (guard yes no : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (guardIH : ∀ (s t : State C F) r, evaluateTuple ([guard], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations guard], target, s) = (r, t))
    (yesIH : ∀ (s t : State C F) r, evaluateTuple ([yes], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations yes], target, s) = (r, t))
    (noIH : ∀ (s t : State C F) r, evaluateTuple ([no], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations no], target, s) = (r, t))
    (run : evaluateTuple ([.ifThenElse guard yes no], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.ifThenElse guard yes no)], target, state) = (result, final) := by
  rw [evaluate_compile_if_shape guard yes no annotations target state]
  change evaluate [.ifThenElse (compileSing annotations guard) (compileSing annotations yes) (compileSing annotations no)] target state = _
  change evaluate [.ifThenElse guard yes no] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate [guard] source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := guardIH state next (.err error) original related ok
      change evaluate [compileSing annotations guard] target state = _ at mapped
      rw [mapped]
      exact run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing guard source state values next original
      have mapped := guardIH state next (.val [value]) original related (by simp)
      change evaluate [compileSing annotations guard] target state = _ at mapped
      rw [mapped]
      simp only [original] at run
      cases h : asBool value with
      | none =>
        simp [h] at run
        exact False.elim (notTypeError run.1.symm)
      | some choice =>
        cases choice <;> simp [h] at run ⊢
        · exact noIH next final result run related notTypeError
        · exact yesIH next final result run related notTypeError


/-- Connect the conditional simulation to the executed bounded traversal. -/
theorem evaluate_compileBounded_if {C F : Type} (fuel : Nat) (guard yes no : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (guardIH : ∀ (s t : State C F) r, evaluateTuple ([guard], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations guard], target, s) = (r, t))
    (yesIH : ∀ (s t : State C F) r, evaluateTuple ([yes], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations yes], target, s) = (r, t))
    (noIH : ∀ (s t : State C F) r, evaluateTuple ([no], source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing annotations no], target, s) = (r, t))
    (run : evaluateTuple ([.ifThenElse guard yes no], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ output, compileBounded fuel annotations (.ifThenElse guard yes no) = some output ∧
      evaluateTuple ([output], target, state) = (result, final) := by
  exact ⟨compileSing annotations (.ifThenElse guard yes no), compileBounded_eq fuel annotations _,
    evaluate_compile_if guard yes no annotations source target state final result guardIH yesIH noIH run related notTypeError⟩


end Flapjack.Compiler.Backend.BvlConst.Proofs
