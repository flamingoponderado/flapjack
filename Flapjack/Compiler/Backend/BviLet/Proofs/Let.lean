import Flapjack.Compiler.Backend.BviLet.Proofs.DeleteVar

/-! Ordinary let-binding case of the BVI let-propagation simulation. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The ordinary let transformation preserves non-type-error evaluations
given the binding and body induction hypotheses. This is untagged until the
BVI evaluator and dispatcher are reviewed. -/
theorem evaluate_compile_let_general {C F : Type} (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (bindingsIH : ∀ (s t : BviState C F) r, evaluateTuple (bindings, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d bindings, target, s) = (r, t))
    (bodyIH : ∀ (ax : List Nat) (depth : Nat) (src dst : List Value) (s t : BviState C F) r,
      evaluateTuple ([body], src, s) = (r, t) → envRel ax depth src dst →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing ax depth body], dst, s) = (r, t))
    (run : evaluateTuple ([.let bindings body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.let ((compileList offsets d bindings).map deleteVar)
      (compileSing (extractList (compileList offsets d bindings) ++ offsets) d body)], target, state) =
      (result, final) := by
  change evaluate [.let bindings body] source state = _ at run
  change evaluate [.let ((compileList offsets d bindings).map deleteVar)
    (compileSing (extractList (compileList offsets d bindings) ++ offsets) d body)] target state = _
  rw [evaluate, fixClock_evaluate] at run ⊢
  cases original : evaluate bindings source state with
  | mk inner next =>
    cases inner with
    | err error =>
      simp only [original] at run
      have ok : (.err error : BviResult) ≠ .err (.abort .typeError) := by
        intro bad
        apply notTypeError
        exact (congrArg Prod.fst run).symm.trans bad
      have mapped := bindingsIH state next (.err error) original related ok
      have errorOK : error ≠ .abort .typeError := by simpa using ok
      have deleted := evaluate_deleteVar_list_error (compileList offsets d bindings) target state next error mapped errorOK
      change evaluate ((compileList offsets d bindings).map deleteVar) target state = _ at deleted
      rw [deleted]
      exact run
    | val values =>
      have mapped := bindingsIH state next (.val values) original related (by simp)
      obtain ⟨output, deleted, extended⟩ := evaluate_deleteVar_list_success
        (compileList offsets d bindings) target source state next values offsets d mapped related
      change evaluate ((compileList offsets d bindings).map deleteVar) target state = _ at deleted
      rw [deleted]
      simp only [original] at run
      exact bodyIH _ _ _ _ next final result run extended notTypeError

/-- For a nonempty let whose body is not the final bound variable, the
optimizer uses the ordinary variable-deletion transformation. -/
theorem compileSing_let_normal (offsets : List Nat) (d : Nat)
    (first : Bvi.Exp) (rest : List Bvi.Exp) (body : Bvi.Exp)
    (notLast : body ≠ .var rest.length) :
    compileSing offsets d (.let (first :: rest) body) =
      .let ((compileList offsets d (first :: rest)).map deleteVar)
        (compileSing (extractList (compileList offsets d (first :: rest)) ++ offsets) d body) := by
  cases body with
  | var index =>
    have different : index ≠ rest.length := by
      intro same
      apply notLast
      rw [same]
    simp [compileSing, different]
  | _ => simp only [compileSing]

/-- Ordinary nonempty let bindings preserve evaluation, assuming the
recursive cases. The special final-variable optimization is a separate case.
Untagged until BVI evaluation is reviewed. -/
theorem evaluate_compile_let_normal {C F : Type} (first : Bvi.Exp) (rest : List Bvi.Exp)
    (body : Bvi.Exp) (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (notLast : body ≠ .var rest.length)
    (bindingsIH : ∀ (s t : BviState C F) r, evaluateTuple (first :: rest, source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple (compileList offsets d (first :: rest), target, s) = (r, t))
    (bodyIH : ∀ (ax : List Nat) (depth : Nat) (src dst : List Value) (s t : BviState C F) r,
      evaluateTuple ([body], src, s) = (r, t) → envRel ax depth src dst →
      r ≠ .err (.abort .typeError) → evaluateTuple ([compileSing ax depth body], dst, s) = (r, t))
    (run : evaluateTuple ([.let (first :: rest) body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.let (first :: rest) body)], target, state) = (result, final) := by
  rw [compileSing_let_normal offsets d first rest body notLast]
  exact evaluate_compile_let_general (first :: rest) body offsets d source target state final result
    bindingsIH bodyIH run related notTypeError

/-- The empty let reduces to its body in both the evaluator and optimizer.
Untagged until BVI evaluation is reviewed. -/
theorem evaluate_compile_let_empty {C F : Type} (body : Bvi.Exp)
    (offsets : List Nat) (d : Nat) (source target : List Value)
    (state final : BviState C F) (result : BviResult)
    (bodyIH : ∀ (s t : BviState C F) r, evaluateTuple ([body], source, s) = (r, t) →
      envRel offsets d source target → r ≠ .err (.abort .typeError) →
      evaluateTuple ([compileSing offsets d body], target, s) = (r, t))
    (run : evaluateTuple ([.let [] body], source, state) = (result, final))
    (related : envRel offsets d source target)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([compileSing offsets d (.let [] body)], target, state) = (result, final) := by
  change evaluate [.let [] body] source state = _ at run
  rw [evaluate, fixClock_evaluate] at run
  simp only [evaluate] at run
  simpa only [compileSing] using bodyIH state final result run related notTypeError

end Flapjack.Compiler.Backend.BviLet.Proofs
