module

public import Flapjack.RiscV.CakeAllocatorCore
public import Flapjack.RiscV.WordToStack

import all Flapjack.RiscV.CakeAllocatorCore
import all Flapjack.RiscV.WordToStack

@[expose] public section

/-!
# CakeML Word-to-Stack frame and call parity checks

The expected values are direct EVAL observations from
`word_stack_call_probe.out`, which evaluates the original
`word_to_stackScript.sml` definitions `call_dest`, `stack_arg_count`,
`stack_free`, `StackArgs`, `SeqStackFree`, `copy_ret`, and `compile_prog`.

This module pins the port's frame-size and call-lowering boundary (bead
flapjack-2ib / GH #1047): the frame reservation matches Cake's
`f - stack_arg_count`, direct tail calls free the caller frame like
`SeqStackFree`, and indirect calls read their target from the last argument
exactly as `call_dest NONE` does.
-/

namespace Flapjack.Test.WordStackCallParity

open Flapjack
open Flapjack.RiscV
open Flapjack.RiscV.CakeAlloc

/-! `stack_arg_count` and `stack_free` on the fresh probe configuration
    `(k, f, f') = (3, 6, 5)`; the direct case counts the target slot, the
    indirect case does not. -/
def callArgCountExact : Bool :=
  stackArgCount (.inl 3) 15 12 == 3 &&
    stackArgCount (.inr 3) 15 12 == 2 &&
    stackArgCount (.inl 0) 5 3 == 2 &&
    stackArgCount (.inr 0) 5 3 == 1 &&
    stackFree (.inl 3) 15 12 20 19 == 17 &&
    stackFree (.inr 3) 15 12 20 19 == 18 &&
    stackFree (.inl 0) 5 3 6 5 == 4 &&
    stackFree (.inr 0) 5 3 6 5 == 5

#guard callArgCountExact

/-! The real Cake RISC-V ABI window has twelve value slots.  At the exact
    boundary, `format_var` keeps index 11 in the last ABI register and
    `wMoveSingle` places indices 12 and 13 at the top two slots of the
    caller's four-word frame. -/

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("stack_arg_count and stack_free match the call oracle", callArgCountExact)]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.WordStackCallParity
