import Flapjack.Compiler.Backend.WordRemove

/-!
# `word_remove$remove_must_terminate` original-oracle rows

Kernel replay of the eight rows of
`scripts/hol-probes/word_remove_must_terminate_probe.out`, evaluated by HOL
`EVAL` on the original `remove_must_terminate_def`.
-/

namespace Flapjack.Test.WordRemoveMustTerminateParity

open Flapjack Flapjack.Compiler.Backend.WordRemove

private abbrev P := WordLangProgHOL (BitVec 8)

-- rmt_mt_seq=Seq Skip Tick
example : removeMustTerminate (.mustTerminate (.seq .skip .tick) : P) = .seq .skip .tick := rfl
-- rmt_mt_nested=Tick
example : removeMustTerminate (.mustTerminate (.mustTerminate .tick) : P) = .tick := rfl
-- rmt_seq=Seq Skip Tick
example : removeMustTerminate (.seq (.mustTerminate .skip) (.mustTerminate .tick) : P) =
    .seq .skip .tick := rfl
-- rmt_if=If Equal 1 (Imm 0w) Skip Tick
example : removeMustTerminate (.ite .equal 1 (.imm 0) (.mustTerminate .skip) .tick : P) =
    .ite .equal 1 (.imm 0) .skip .tick := rfl
-- rmt_loop=Loop LN (Break 0) LN
example : removeMustTerminate (.loop .ln (.mustTerminate (.break 0)) .ln : P) =
    .loop .ln (.break 0) .ln := rfl
-- rmt_call_ret_handler=Call (SOME ([1],(LN,LN),Skip,2,3)) NONE [4] (SOME (5,Tick,6,7))
example : removeMustTerminate (.call (some ([1], (.ln, .ln), .mustTerminate .skip, 2, 3)) none [4]
      (some (5, .mustTerminate .tick, 6, 7)) : P) =
    .call (some ([1], (.ln, .ln), .skip, 2, 3)) none [4] (some (5, .tick, 6, 7)) := rfl
-- rmt_call_tail_handler=Call NONE (SOME 1) [2] (SOME (3,Skip,4,5))
example : removeMustTerminate (.call none (some 1) [2] (some (3, .mustTerminate .skip, 4, 5)) : P) =
    .call none (some 1) [2] (some (3, .skip, 4, 5)) := rfl
-- rmt_tick=Tick
example : removeMustTerminate (.tick : P) = .tick := rfl

def runChecks : IO Bool := do
  IO.println "PASS remove_must_terminate matches eight original HOL rows (kernel-checked)"
  pure true

end Flapjack.Test.WordRemoveMustTerminateParity
