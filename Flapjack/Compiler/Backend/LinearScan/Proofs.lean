import Flapjack.Compiler.Backend.LinearScan.Proofs.LiveTree
import Flapjack.Compiler.Backend.LinearScan.Proofs.Intervals
import Flapjack.Compiler.Backend.LinearScan.Proofs.CheckIntervals
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange
import Flapjack.Compiler.Backend.LinearScan.Proofs.GoodState
import Flapjack.Compiler.Backend.LinearScan.Proofs.SpillRegister
import Flapjack.Compiler.Backend.LinearScan.Proofs.Bijection
import Flapjack.Compiler.Backend.LinearScan.Proofs.ApplyBijection
import Flapjack.Compiler.Backend.LinearScan.Proofs.IntervalMonad

/-!
# linear_scan proofs

Counterpart of
`cakeml/compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml`. The
script's theorem groups are ported in submodules, following the script's own
order:

* `LiveTree`: `linear_scanProofScript.sml:23-598`, list insertion/deletion,
  partial-colouring checker invariants and the `get_live_tree` /
  `check_clash_tree` correspondence.
* `Intervals`: `linear_scanProofScript.sml:600-1765`, properties of
  `get_intervals`, `get_intervals_withlive` and `check_number_property`.
* `CheckIntervals`: `linear_scanProofScript.sml:1767-2018`,
  `check_intervals_check_live_tree` and `get_intervals_ct_eq`.
* `RegExchange`: `linear_scanProofScript.sml:2020-2402`, the generated
  array accessor equations and `apply_reg_exchange_correct`.
* `GoodState`: `linear_scanProofScript.sml:2404-2696`, the colouring-state
  invariant `good_linear_scan_state`, releasing inactive intervals and
  finding a colour.
* `SpillRegister`: `linear_scanProofScript.sml:2697-2946`, sparse sublists
  and `spill_register` preserving `good_linear_scan_state`.
* `Bijection`: `linear_scanProofScript.sml:4997-5204`, the register
  bijection invariants.
* `ApplyBijection`: `linear_scanProofScript.sml:5565-6006`, checking a
  renamed clash tree and reading back the colouring.
* `IntervalMonad`: `linear_scanProofScript.sml:5206-5469`, the interval monad
  against `get_intervals_ct` and live-tree registers.

Declarations whose statements use HOL `EL` render it by the exact tagged
`holEl` (`Flapjack.Misc.ListEl`); each was re-tagged after its own statement
review.

The top-level `linear_scan_reg_alloc_correct` is not yet ported.
-/
