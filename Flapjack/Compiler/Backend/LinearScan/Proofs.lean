import Flapjack.Compiler.Backend.LinearScan.Proofs.LiveTree
import Flapjack.Compiler.Backend.LinearScan.Proofs.Intervals
import Flapjack.Compiler.Backend.LinearScan.Proofs.CheckIntervals
import Flapjack.Compiler.Backend.LinearScan.Proofs.RegExchange

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

The top-level `linear_scan_reg_alloc_correct` is not yet ported.
-/
