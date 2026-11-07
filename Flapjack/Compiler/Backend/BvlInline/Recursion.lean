import Flapjack.Compiler.Backend.BvlInline.Proofs.RecursiveTotal
import Flapjack.Compiler.Backend.BvlInline.Small

/-! Total source-shaped recursion and inlining eligibility checks. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

mutual
/-- Detect a call to a given function in one BVL expression. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_rec_sing_def"]
def isRecSing (name : Nat) : Exp → Bool
  | .var _ | .force _ _ => false
  | .ifThenElse x y z => isRecSing name x || isRecSing name y || isRecSing name z
  | .let xs body => isRecList name xs || isRecSing name body
  | .raise x | .tick x => isRecSing name x
  | .handle x y => isRecSing name x || isRecSing name y
  | .op _ xs => isRecList name xs
  | .call _ dest xs => (dest == some name) || isRecList name xs
termination_by e => sizeOf e

/-- Detect a call to a given function in an expression list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_rec_sing_def"]
def isRecList (name : Nat) : List Exp → Bool
  | [] => false
  | x :: xs => isRecSing name x || isRecList name xs
termination_by xs => sizeOf xs
end

/-- Original list form of the recursion test. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_rec_def"]
def isRec (name : Nat) (xs : List Exp) : Bool := isRecList name xs

/-- The singleton and list recursion tests agree with the original list form. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_rec_sing"]
theorem isRecSing_equivalence :
    (∀ e n, isRec n [e] = isRecSing n e) ∧
      (∀ es n, isRecList n es = isRec n es) := by
  constructor
  · intro e n; simp [isRec, isRecList]
  · intro es n; rfl

/-- Cache a function exactly when its body is small and nonrecursive. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "must_inline_def"]
def mustInline (name limit : Nat) (e : Exp) : Bool :=
  if isSmall limit e then !isRec name [e] else false

/-- The recursion-list traversal is a short-circuiting list `any`. This
decomposition is Flapjack infrastructure, not a standalone HOL declaration. -/
theorem isRecList_eq_any (name : Nat) (xs : List Exp) :
    isRecList name xs = xs.any (isRecSing name) := by
  induction xs with
  | nil => simp [isRecList]
  | cons x xs ih => simp [isRecList, ih]

end Flapjack.Compiler.Backend.BvlInline
