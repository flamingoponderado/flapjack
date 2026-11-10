module

public import Flapjack.RiscV.CakeAllocatorBitsBridge
public import Flapjack.Compiler.Backend.WordToStack

@[expose] public section

/-!
# Executable Cake bitmap recursion ↔ tagged `bitsToWordW`/`wordListW`

Untagged bridge regression for bead `flapjack-pxn.18.5.15.3.1.1`: the executed
`Flapjack.RiscV.CakeAlloc` bitmap recursion maps onto the tagged
`bitsToWordW`/`wordListW` for every input, including the out-of-range
`LENGTH > width` boundary (both sides truncate). The direct original-HOL rows
are in `scripts/hol-probes/word_to_stack_bits_to_word_probe.out`
(`bits_overflow_65=0xFFFFFFFFFFFFFFFFw`, `wordlist_chunk=[7w; 7w; 1w]`).
-/

namespace Flapjack.Test.CakeAllocatorBitsBridgeParity

open Flapjack
open Flapjack.Compiler.Backend.WordToStack
open Flapjack.RiscV.CakeAlloc

end Flapjack.Test.CakeAllocatorBitsBridgeParity