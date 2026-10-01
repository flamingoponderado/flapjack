import Flapjack.Misc.Sptree.Map

namespace Flapjack.Test.SptMapParity
open Flapjack
/-! Kernel tree replay of direct original HOL payload-only map observations.
Malformed internal nodes must remain internal, and mapping may change payload
types. Finite regression evidence does not establish cross-prover equivalence. -/
-- sm_empty=T
example : sptMap (fun x : Nat => x+1) .ln = .ln := by decide +kernel
-- sm_leaf=T
example : sptMap (fun x : Nat => x+1) (.ls 7) = .ls 8 := by decide +kernel
-- sm_children=T
example : sptMap (fun x : Nat => x+1) (.bn (.ls 7) (.ls 8)) =
    .bn (.ls 8) (.ls 9) := by decide +kernel
-- sm_root=T
example : sptMap (fun x : Nat => x+1) (.bs (.ls 7) 8 (.ls 9)) =
    .bs (.ls 8) 9 (.ls 10) := by decide +kernel
-- sm_raw_bn=T
example : sptMap (fun x : Nat => x+1) (.bn .ln .ln) =
    .bn .ln .ln := by decide +kernel
-- sm_raw_bs=T
example : sptMap (fun x : Nat => x+1) (.bs .ln 7 .ln) =
    .bs .ln 8 .ln := by decide +kernel
-- sm_raw_nested=T
example : sptMap (fun x : Nat => x+1) (.bs (.bn .ln .ln) 7 (.bs .ln 8 .ln)) =
    .bs (.bn .ln .ln) 8 (.bs .ln 9 .ln) := by decide +kernel
-- sm_bool_nat=T
example : sptMap (fun x : Bool => if x then 1 else 0)
    (.bs (.ls false) true (.ls true)) = .bs (.ls 0) 1 (.ls 1) := by decide +kernel
-- sm_nat_bool=T
example : sptMap (fun x : Nat => decide (x = 0))
    (.bs (.ls 7) 0 (.ls 8)) = .bs (.ls false) true (.ls false) := by decide +kernel
-- sm_unit_raw=T
example : sptMap (fun _ : Nat => ()) (.bs (.bn .ln .ln) 7 (.ls 8)) =
    .bs (.bn .ln .ln) () (.ls ()) := by decide +kernel
end Flapjack.Test.SptMapParity
