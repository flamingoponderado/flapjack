import Flapjack.Compiler.Backend.BvlInline.Proofs.SmallTotal

/-! Total source-shaped size check for BVL inlining. The production bounded
traversal is proved equal in `Proofs.SmallProduction`. -/
namespace Flapjack.Compiler.Backend.BvlInline
open Bvl

mutual
/-- Remaining size budget for one expression. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_small_sing_def"]
def isSmallSing : Nat → Exp → Nat
  | n, .var _ | n, .force _ _ => n
  | n, .tick e => isSmallSing n e
  | n, .ifThenElse x y z =>
    let n := n - 1
    if n = 0 then 0 else
    let n := isSmallSing n x
    if n = 0 then 0 else
    let n := isSmallSing n y
    if n = 0 then 0 else isSmallSing n z
  | n, .let xs body =>
    let n := n - 1
    if n = 0 then 0 else
    let n := isSmallList n xs
    if n = 0 then 0 else isSmallSing n body
  | n, .raise e =>
    let n := n - 1
    if n = 0 then 0 else isSmallSing n e
  | n, .handle x y =>
    let n := n - 1
    if n = 0 then 0 else
    let n := isSmallSing n x
    if n = 0 then 0 else isSmallSing n y
  | n, .op _ xs | n, .call _ _ xs =>
    let n := n - 1
    if n = 0 then 0 else isSmallList n xs
termination_by _ e => sizeOf e

/-- Remaining size budget for an expression list. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_small_sing_def"]
def isSmallList : Nat → List Exp → Nat
  | n, [] => n
  | n, x :: xs =>
    if n = 0 then n else
    let n := isSmallSing n x
    if n = 0 then n else isSmallList n xs
termination_by _ xs => sizeOf xs
end

/-- The list form of the size-budget traversal. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_small_aux_def"]
def isSmallAux (n : Nat) (xs : List Exp) : Nat := isSmallList n xs

private theorem isSmallSing_zero (e : Exp) : isSmallSing 0 e = 0 := by
  cases e <;> simp only [isSmallSing, Nat.zero_sub, if_true]
  case tick e => exact isSmallSing_zero e
termination_by sizeOf e
decreasing_by all_goals simp_wf

/-- The list and singleton traversals agree with the original size check. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_small_sing"]
theorem isSmallSing_equivalence :
    (∀ e n, isSmallAux n [e] = isSmallSing n e) ∧
      (∀ es n, isSmallList n es = isSmallAux n es) := by
  constructor
  · intro e n
    by_cases h : n = 0
    · subst n; simp [isSmallAux, isSmallList, isSmallSing_zero]
    · simp [isSmallAux, isSmallList, h]
  · intro es n; rfl

/-- The original test accepts a body exactly when budget remains. -/
@[hol "cakeml/compiler/backend/bvl_inlineScript.sml" "is_small_def"]
def isSmall (limit : Nat) (e : Exp) : Bool := isSmallSing limit e != 0

end Flapjack.Compiler.Backend.BvlInline
