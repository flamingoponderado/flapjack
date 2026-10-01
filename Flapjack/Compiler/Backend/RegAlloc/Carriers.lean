import Flapjack.HolRef

namespace Flapjack.RegAlloc

/-- Native node tags; the fixed colour is an unbounded natural. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "tag"]
inductive Tag where
  | Fixed (colour : Nat)
  | Atemp
  | Stemp
  deriving DecidableEq, Repr

/-- Literal HOL list state, including both priority/move association lists.
This carrier is separate from the executed IRC implementation's array state;
establishing that implementation's correspondence remains open. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "ra_state"]
structure State where
  adj_ls : List (List Nat)
  node_tag : List Tag
  degrees : List Nat
  dim : Nat
  simp_wl : List Nat
  spill_wl : List Nat
  freeze_wl : List Nat
  avail_moves_wl : List (Nat × (Nat × Nat))
  unavail_moves_wl : List (Nat × (Nat × Nat))
  coalesced : List Nat
  move_related : List Bool
  stack : List Nat
  deriving DecidableEq, Repr

@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "algorithm"]
inductive Algorithm where
  | Simple
  | IRC
  deriving DecidableEq, Repr

end Flapjack.RegAlloc
