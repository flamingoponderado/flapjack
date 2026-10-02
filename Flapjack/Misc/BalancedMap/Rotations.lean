import Flapjack.Misc.BalancedMap.Core

namespace Flapjack.Misc.BalancedMap

/-- Literal HOL left balancing, including the malformed-tree error result.
Cached sizes and arithmetic follow the source; no invariant is assumed. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceL_def"]
def balanceL {κ ν : Type} (k : κ) (x : ν) : Map κ ν → Map κ ν → Map κ ν
  | .tip, .tip => .bin 1 k x .tip .tip
  | .bin s' k' v' .tip .tip, .tip => .bin 2 k x (.bin s' k' v' .tip .tip) .tip
  | .bin _ lk lx .tip (.bin _ lrk lrx _ _), .tip =>
    .bin 3 lrk lrx (.bin 1 lk lx .tip .tip) (.bin 1 k x .tip .tip)
  | .bin _ lk lx (.bin s' k' v' l' r') .tip, .tip =>
    .bin 3 lk lx (.bin s' k' v' l' r') (.bin 1 k x .tip .tip)
  | .bin ls lk lx (.bin lls k' v' l' r') (.bin lrs lrk lrx lrl lrr), .tip =>
    if lrs < ratio * lls then
      .bin (1 + ls) lk lx (.bin lls k' v' l' r')
        (.bin (1 + lrs) k x (.bin lrs lrk lrx lrl lrr) .tip)
    else
      .bin (1 + ls) lrk lrx
        (.bin (1 + lls + size lrl) lk lx (.bin lls k' v' l' r') lrl)
        (.bin (1 + size lrr) k x lrr .tip)
  | .tip, .bin rs k' v' l' r' =>
    .bin (1 + rs) k x .tip (.bin rs k' v' l' r')
  | .bin ls lk lx ll lr, .bin rs k' v' l' r' =>
    if ls > delta * rs then
      match ll, lr with
      | .bin lls _ _ _ _, .bin lrs lrk lrx lrl lrr =>
        if lrs < ratio * lls then
          .bin (1 + ls + rs) lk lx ll
            (.bin (1 + rs + lrs) k x lr (.bin rs k' v' l' r'))
        else
          .bin (1 + ls + rs) lrk lrx
            (.bin (1 + lls + size lrl) lk lx ll lrl)
            (.bin (1 + rs + size lrr) k x lrr (.bin rs k' v' l' r'))
      | _, _ => .tip
    else .bin (1 + ls + rs) k x (.bin ls lk lx ll lr) (.bin rs k' v' l' r')

/-- Literal HOL right balancing with every cached-size and error branch. -/
@[hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "balanceR_def"]
def balanceR {κ ν : Type} (k : κ) (x : ν) : Map κ ν → Map κ ν → Map κ ν
  | .tip, .tip => .bin 1 k x .tip .tip
  | .tip, .bin s' k' v' .tip .tip => .bin 2 k x .tip (.bin s' k' v' .tip .tip)
  | .tip, .bin _ rk rx .tip (.bin s' k' v' l' r') =>
    .bin 3 rk rx (.bin 1 k x .tip .tip) (.bin s' k' v' l' r')
  | .tip, .bin _ rk rx (.bin _ rlk rlx _ _) .tip =>
    .bin 3 rlk rlx (.bin 1 k x .tip .tip) (.bin 1 rk rx .tip .tip)
  | .tip, .bin rs rk rx (.bin rls rlk rlx rll rlr) (.bin rrs k' v' l' r') =>
    if rls < ratio * rrs then
      .bin (1 + rs) rk rx
        (.bin (1 + rls) k x .tip (.bin rls rlk rlx rll rlr)) (.bin rrs k' v' l' r')
    else
      .bin (1 + rs) rlk rlx (.bin (1 + size rll) k x .tip rll)
        (.bin (1 + rrs + size rlr) rk rx rlr (.bin rrs k' v' l' r'))
  | .bin ls k' v' l' r', .tip =>
    .bin (1 + ls) k x (.bin ls k' v' l' r') .tip
  | .bin ls k' v' l' r', .bin rs rk rx rl rr =>
    if rs > delta * ls then
      match rl, rr with
      | .bin rls rlk rlx rll rlr, .bin rrs _ _ _ _ =>
        if rls < ratio * rrs then
          .bin (1 + ls + rs) rk rx
            (.bin (1 + ls + rls) k x (.bin ls k' v' l' r') rl) rr
        else
          .bin (1 + ls + rs) rlk rlx
            (.bin (1 + ls + size rll) k x (.bin ls k' v' l' r') rll)
            (.bin (1 + rrs + size rlr) rk rx rlr rr)
      | _, _ => .tip
    else .bin (1 + ls + rs) k x (.bin ls k' v' l' r') (.bin rs rk rx rl rr)

end Flapjack.Misc.BalancedMap
