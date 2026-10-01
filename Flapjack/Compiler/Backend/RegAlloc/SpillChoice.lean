import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.SafeDiv
import Flapjack.Misc.LookupAny

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Literal `st_ex_list_MAX_deg` (`reg_allocScript.sml:794-807`): scan
in-dimension nodes for a strictly larger degree, collecting every
non-selected candidate (including replaced ones) into `acc`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_list_MAX_deg_def"]
def stExListMaxDeg : List Nat → Nat → Nat → Nat → List Nat →
    M State (Nat × List Nat) StateException
  | [], _, k, _, acc => ret (k, acc)
  | x :: xs, d, k, v, acc =>
    if x < d then
      bind (degreesSub x) fun xv =>
        if v < xv then stExListMaxDeg xs d x xv (k :: acc)
        else stExListMaxDeg xs d k v (x :: acc)
    else stExListMaxDeg xs d k v acc

/-- Literal `st_ex_list_MIN_cost` (`reg_allocScript.sml:778-792`): as
`st_ex_list_MAX_deg`, minimising `safe_div (lookup_any x scost 0) degree`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "st_ex_list_MIN_cost_def"]
def stExListMinCost (scost : Spt Nat) : List Nat → Nat → Nat → Nat → List Nat →
    M State (Nat × List Nat) StateException
  | [], _, k, _, acc => ret (k, acc)
  | x :: xs, d, k, v, acc =>
    if x < d then
      bind (degreesSub x) fun xv =>
        bind (ret (safeDiv (lookupAny x scost 0) xv)) fun cost =>
          if v > cost then stExListMinCost scost xs d x cost (k :: acc)
          else stExListMinCost scost xs d k v (x :: acc)
    else stExListMinCost scost xs d k v acc

end Flapjack.RegAlloc
