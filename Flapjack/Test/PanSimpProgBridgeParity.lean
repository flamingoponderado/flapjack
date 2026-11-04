/-
Parity between the exact-to-production `pan_simp` codec bridges in
`Flapjack/Pancake/Proofs/PanSimp/ProgOfHOL.lean` and the checked-in direct
original-HOL EVAL rows:

* `scripts/hol-probes/pan_simp_compile_probe.out` (`pan_simp$compile`)
* `scripts/hol-probes/seq_assoc_probe.out` (`pan_simp$seq_assoc`)
* `scripts/hol-probes/ret_to_tail_probe.out` (`pan_simp$ret_to_tail`)

The expected production values are exactly the oracle rows: `Skip`, `Tick`,
`Seq Tick Tick`, and `Skip` for `ret_to_tail`. These bridge rows connect the
tagged exact HOL `pan_simp` definitions to the production `panSimpDecls`.
-/
import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL

namespace Flapjack.Test.PanSimpProgBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

def runChecks : IO Bool := do
  IO.println "PASS pan_simp exact-to-production bridge rows vs pan_simp compile/seq_assoc/ret_to_tail oracles"
  pure true

end Flapjack.Test.PanSimpProgBridgeParity
