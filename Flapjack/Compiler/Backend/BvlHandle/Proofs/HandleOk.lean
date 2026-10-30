import Flapjack.Compiler.Backend.Semantics.BvlProps.VarBound

/-! Structural preconditions for BVL exception-handler lowering. -/
namespace Flapjack.Compiler.Backend.BvlHandle.Proofs
open Flapjack.Compiler.Backend.BvlSem (expsWeight expWeight)
open Flapjack.Compiler.Backend.BvlProps (isVar bVarBound)

/-- A let has variable-only bindings and a body scoped by those bindings. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "let_ok_def"]
def letOk : Bvl.Exp → Prop
  | .let xs body => xs.all isVar = true ∧ bVarBound xs.length [body]
  | _ => False

/-- The source handler-shape invariant. `handleOk_emptyLet` establishes that
the terminating match in the empty-let clause is the source's quantified
condition. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_def"]
def handleOk : List Bvl.Exp → Prop
  | [] => True
  | x :: y :: xs => handleOk [x] ∧ handleOk (y :: xs)
  | [.var _] | [.force _ _] => True
  | [.ifThenElse x y z] => handleOk [x] ∧ handleOk [y] ∧ handleOk [z]
  | [.let xs body] =>
    if xs.length = 0 then
      letOk body ∧ match body with
        | .let _ inner => handleOk [inner]
        | _ => True
    else handleOk xs ∧ handleOk [body]
  | [.raise x] | [.tick x] => handleOk [x]
  | [.op _ xs] | [.call _ _ xs] => handleOk xs
  | [.handle x y] =>
    match x with
    | .let xs body => xs.all isVar = true ∧ bVarBound xs.length [body] ∧
        handleOk [body] ∧ handleOk [y]
    | _ => False
termination_by xs => expsWeight xs
decreasing_by
  all_goals simp only [expsWeight, expWeight]
  all_goals try (have := BvlSem.expWeight_pos y)
  all_goals omega

/-- The empty-binding case exposes the source's quantified body condition. -/
theorem handleOk_emptyLet (body : Bvl.Exp) :
    handleOk [.let [] body] ↔
      letOk body ∧ ∀ ys inner, body = .let ys inner → handleOk [inner] := by
  cases body <;> simp [handleOk, letOk]

/-- The handler invariant decomposes over a list head and tail. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_CONS"]
theorem handleOk_cons (x : Bvl.Exp) (xs : List Bvl.Exp) :
    handleOk (x :: xs) ↔ handleOk [x] ∧ handleOk xs := by
  cases xs with
  | nil => simp [handleOk]
  | cons y ys => rw [handleOk]

/-- Membership formulation of the handler invariant, used as Flapjack
infrastructure. The source theorem is stated with `EVERY`. -/
theorem handleOk_every (xs : List Bvl.Exp) :
    handleOk xs ↔ ∀ x ∈ xs, handleOk [x] := by
  induction xs with
  | nil => simp [handleOk]
  | cons x xs ih =>
    rw [handleOk_cons, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

end Flapjack.Compiler.Backend.BvlHandle.Proofs
