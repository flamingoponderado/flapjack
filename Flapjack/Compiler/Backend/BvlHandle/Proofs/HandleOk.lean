module

public import Flapjack.Compiler.Backend.Semantics.BvlProps.VarBound
public import Mathlib.Data.List.Basic

@[expose] public section

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

/-- The handler invariant holds exactly when it holds for every singleton. -/
@[hol "cakeml/compiler/backend/proofs/bvl_handleProofScript.sml" "handle_ok_EVERY"]
theorem handleOk_every (xs : List Bvl.Exp) :
    handleOk xs ↔ xs.Forall (fun x => handleOk [x]) := by
  induction xs with
  | nil => simp [handleOk]
  | cons x xs ih =>
    rw [handleOk_cons, List.forall_cons, ih]

end Flapjack.Compiler.Backend.BvlHandle.Proofs
