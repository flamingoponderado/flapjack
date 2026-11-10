module

public import Flapjack.Compiler.Backend.Bvl.Syntax
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Balanced switch construction for BVL. -/
namespace Flapjack.Compiler.Backend.BvlJump

/-- Build the source's balanced jump tree, retaining its small-constant cutoff. -/
@[hol "cakeml/compiler/backend/bvl_jumpScript.sml" "JumpList_def"]
def jumpList (n : Nat) (xs : List Bvl.Exp) : Bvl.Exp :=
  let len := xs.length
  if len = 0 then .op (.intOp (.const 0)) []
  else if len = 1 then xs.headD (.var 0)
  else
    let k := len / 2
    let ys := xs.take k
    let zs := xs.drop k
    let lt := if n + len < 1000000 ∧ n + k < 1000000 then
      Bvl.Exp.op (.intOp (.lessConstSmall (n + k))) [.var 0]
    else Bvl.Exp.op (.intOp .less) [.op (.intOp (.const (Int.ofNat (n + k)))) [], .var 0]
    .ifThenElse lt (jumpList n ys) (jumpList (n + k) zs)
termination_by xs.length
decreasing_by all_goals simp_wf <;> (try simp_all [List.length_take, List.length_drop]) <;> omega

/-- HOL-shaped equation for the executable jump tree. This Flapjack-specific
equation exposes HOL's `HD`; the default in `headD` is unreachable here. -/
theorem jumpList_hol (n : Nat) (xs : List Bvl.Exp) :
    jumpList n xs =
      let len := xs.length
      if len = 0 then .op (.intOp (.const 0)) []
      else if len = 1 then @Flapjack.holHd Bvl.Exp ⟨.var 0⟩ xs
      else
        let k := len / 2
        let ys := xs.take k
        let zs := xs.drop k
        let lt := if n + len < 1000000 ∧ n + k < 1000000 then
          Bvl.Exp.op (.intOp (.lessConstSmall (n + k))) [.var 0]
        else Bvl.Exp.op (.intOp .less) [.op (.intOp (.const (Int.ofNat (n + k)))) [], .var 0]
        .ifThenElse lt (jumpList n ys) (jumpList (n + k) zs) := by
  rw [jumpList]
  cases xs <;> simp [Flapjack.holHd]

/-- Bind the selector and dispatch through the balanced tree. -/
@[hol "cakeml/compiler/backend/bvl_jumpScript.sml" "Jump_def"]
def jump (x : Bvl.Exp) (xs : List Bvl.Exp) : Bvl.Exp := .let [x] (jumpList 0 xs)

end Flapjack.Compiler.Backend.BvlJump
