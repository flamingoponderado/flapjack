import Flapjack.Compiler.Backend.Bvl.Syntax

/-! Balanced switch construction for BVL. -/
namespace Flapjack.Compiler.Backend.BvlJump

/-- Build the source's balanced jump tree, retaining its small-constant cutoff. -/
@[hol "cakeml/compiler/backend/bvl_jumpScript.sml" "JumpList_def"]
def jumpList (n : Nat) (xs : List Bvl.Exp) : Bvl.Exp :=
  match xs with
  | [] => .op (.intOp (.const 0)) []
  | [x] => x
  | x :: y :: rest =>
      let xs := x :: y :: rest
      let k := xs.length / 2
      let lt := if n + xs.length < 1000000 ∧ n + k < 1000000 then
        Bvl.Exp.op (.intOp (.lessConstSmall (n + k))) [.var 0]
      else Bvl.Exp.op (.intOp .less) [.op (.intOp (.const (Int.ofNat (n + k)))) [], .var 0]
      .ifThenElse lt (jumpList n (xs.take k)) (jumpList (n + k) (xs.drop k))
termination_by xs.length
decreasing_by all_goals simp_wf <;> (try simp_all [List.length_take, List.length_drop]) <;> omega

/-- Bind the selector and dispatch through the balanced tree. -/
@[hol "cakeml/compiler/backend/bvl_jumpScript.sml" "Jump_def"]
def jump (x : Bvl.Exp) (xs : List Bvl.Exp) : Bvl.Exp := .let [x] (jumpList 0 xs)

end Flapjack.Compiler.Backend.BvlJump
