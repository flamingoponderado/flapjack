import Flapjack.Compiler.Backend.BvlConst.Proofs.Conditional
import Flapjack.Compiler.Backend.BvlConst.Proofs.DeleteVar

/-! Let-binding case of constant-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- The let-binding case of constant propagation, using the recursive binding
and body simulations and the source variable-deletion relation. Untagged
because the environment relation quantifies over the finite-map state. -/
theorem evaluate_compile_let {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (source target : List Value)
    (state final : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (bindingsIH : ∀ (s t : State C F) r, evaluateTuple (bindings, source, s) = (r, t) →
      envRel C F annotations source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList annotations bindings, target, s) = (r, t))
    (bodyIH : ∀ (ax : List (Option Bvl.Exp)) (src dst : List Value) (s t : State C F) r,
      evaluateTuple ([body], src, s) = (r, t) → envRel C F ax src dst →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing ax body], dst, s) = (r, t))
    (run : evaluateTuple ([.let bindings body], source, state) = (result, final))
    (related : envRel C F annotations source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing annotations (.let bindings body)], target, state) = (result, final) := by
  simp only [compileSing]
  change evaluate [.let ((compileList annotations bindings).map deleteVar)
    (compileSing (extractList (compileList annotations bindings) ++ annotations) body)] target state = _
  change evaluate [.let bindings body] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate bindings source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := bindingsIH state next (.err error) original related ok
      have errorOK : error ≠ .abort .typeError := by simpa using ok
      have deleted := evaluate_deleteVar_list_error (compileList annotations bindings) state next target error mapped errorOK
      change evaluate ((compileList annotations bindings).map deleteVar) target state = _ at deleted
      rw [deleted]
      exact run
    | val values =>
      have mapped := bindingsIH state next (.val values) original related (by simp)
      obtain ⟨output, deleted, extended⟩ := evaluate_deleteVar_list_success
        (compileList annotations bindings) target source state next values annotations mapped related
      change evaluate ((compileList annotations bindings).map deleteVar) target state = _ at deleted
      rw [deleted]
      simp only [original] at run
      exact bodyIH _ _ _ next final result run extended notTypeError

end Flapjack.Compiler.Backend.BvlConst.Proofs
