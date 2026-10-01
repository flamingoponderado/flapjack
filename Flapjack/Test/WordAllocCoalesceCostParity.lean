import Flapjack.Compiler.Backend.WordAlloc.CoalesceCost

namespace Flapjack.Test.WordAllocCoalesceCostParity
open Flapjack Flapjack.WordAlloc
/-! Same-input kernel replay of original HOL cost rows. Payload magnitude is
irrelevant; identical endpoints contribute twice. -/
-- cc_absent=(80,7,8)
example : getCoalesceCost (.ln : Spt Nat) (2,3,(7,8)) = (80,(7,8)) := by decide +kernel
-- cc_left=(82,7,8)
example : getCoalesceCost (sptInsert 7 999 .ln) (2,3,(7,8)) = (82,(7,8)) := by decide +kernel
-- cc_right=(82,7,8)
example : getCoalesceCost (sptInsert 8 0 .ln) (2,3,(7,8)) = (82,(7,8)) := by decide +kernel
-- cc_both=(84,7,8)
example : getCoalesceCost (sptInsert 7 999 (sptInsert 8 0 .ln)) (2,3,(7,8)) = (84,(7,8)) := by decide +kernel
-- cc_same=(84,7,7)
example : getCoalesceCost (sptInsert 7 false .ln) (2,3,(7,7)) = (84,(7,7)) := by decide +kernel
-- cc_zero=(0,7,8)
example : getCoalesceCost (sptInsert 7 true .ln) (0,3,(7,8)) = (0,(7,8)) := by decide +kernel
-- cc_large=(184467440737095516160,7,8)
example : getCoalesceCost (.ln : Spt Nat) (18446744073709551616,0,(7,8)) =
    (184467440737095516160,(7,8)) := by decide +kernel
-- cc_raw=(10,0,1)
example : getCoalesceCost (.bn .ln .ln : Spt Nat) (1,0,(0,1)) = (10,(0,1)) := by decide +kernel
end Flapjack.Test.WordAllocCoalesceCostParity
