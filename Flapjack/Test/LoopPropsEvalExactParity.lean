import Flapjack.Pancake.Semantics.LoopProps.EvalExact

/-!
# Exact loopLang `locals_touched` against HOL oracle rows

Rows of `scripts/hol-probes/loop_lang_locals_touched_probe.out` replayed on the
exact `holLoopLocalsTouched` (bead `flapjack-pxgp.11`).  The loopProps
`eval`/`get_vars` update lemmas of the same bead are kernel-checked theorems in
`Flapjack/Pancake/Semantics/LoopProps/EvalExact.lean`.
-/

namespace Flapjack.Test.LoopPropsEvalExactParity

open Flapjack

private abbrev E := HolLoopExp 32

#guard holLoopLocalsTouched (.const 7 : E) == []
#guard holLoopLocalsTouched (.var 3 : E) == [3]
#guard holLoopLocalsTouched (.load (.var 4) : E) == [4]
#guard holLoopLocalsTouched (.op .add [.var 2, .load (.var 4), .const 7] : E) == [2, 4]
#guard holLoopLocalsTouched (.baseAddr : E) == []

def runChecks : IO Bool := do
  IO.println "PASS exact loopLang locals_touched HOL parity (loop_lang_locals_touched_probe)"
  pure true

end Flapjack.Test.LoopPropsEvalExactParity
