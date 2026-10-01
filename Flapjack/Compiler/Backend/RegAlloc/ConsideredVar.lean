import Flapjack.Compiler.Backend.RegAlloc.Accessors

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `is_Fixed` (`reg_allocScript.sml:449-454`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_Fixed_def"]
def isFixed (x : Nat) : M State Bool StateException :=
  bind (nodeTagSub x) fun xt =>
    ret (match xt with
      | .Fixed _ => true
      | _ => false)

/-- Literal `is_Atemp` (`reg_allocScript.sml:490-495`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_Atemp_def"]
def isAtemp (d : Nat) : M State Bool StateException :=
  bind (nodeTagSub d) fun dt => ret (decide (dt = .Atemp))

/-- Literal `is_Fixed_k` (`reg_allocScript.sml:498-503`): a fixed colour
below `k`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "is_Fixed_k_def"]
def isFixedK (k x : Nat) : M State Bool StateException :=
  bind (nodeTagSub x) fun xt =>
    ret (match xt with
      | .Fixed n => decide (n < k)
      | _ => false)

/-- Literal `considered_var` (`reg_allocScript.sml:506-513`): both tests run,
`is_Atemp` first, before the disjunction. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "considered_var_def"]
def consideredVar (k x : Nat) : M State Bool StateException :=
  bind (isAtemp x) fun bx =>
    bind (isFixedK k x) fun fx => ret (bx || fx)

/-- Literal `deg_or_inf` (`reg_allocScript.sml:516-521`): fixed colours below
`k` count as degree `k`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "deg_or_inf_def"]
def degOrInf (k x : Nat) : M State Nat StateException :=
  bind (isFixedK k x) fun bx => if bx then ret k else degreesSub x

end Flapjack.RegAlloc
