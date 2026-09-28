import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact loopSem `loop_primop` and wordSem `write_bytearray` against HOL rows

Rows from `scripts/hol-probes/loop_sem_primop_probe.out` and
`scripts/hol-probes/pan_sem_write_bytearray_probe.out` (panSem
`write_bytearray` has the same text as the wordSem one, with `word_lab` for
`word_loc`).  Bead `flapjack-pxgp.7`.
-/

namespace Flapjack.Test.LoopSemPrimopBytesExactParity

open Flapjack

private abbrev W := WordLocW 64

-- valid_no_carry=SOME [Word 7w; Word 0w]
#guard LoopSemStateFiniteExact.loopPrimop .addCarry
  [(.word 3#64 : W), .word 4#64, .word 0#64] == some [.word 7#64, .word 0#64]
-- valid_carry=SOME [Word 0x10000000000000000w; Word 1w] (the HOL numeral is
-- 2^64, i.e. 0w at width 64)
#guard LoopSemStateFiniteExact.loopPrimop .addCarry
  [(.word 0xffffffffffffffff#64 : W), .word 0#64, .word 1#64] ==
    some [.word 0#64, .word 1#64]
-- invalid_arity=NONE, invalid_nonword=NONE
#guard LoopSemStateFiniteExact.loopPrimop .addCarry [(.word 3#64 : W), .word 4#64] == none
#guard LoopSemStateFiniteExact.loopPrimop .addCarry
  [(.loc 0 0 : W), .word 4#64, .word 0#64] == none

private def initialMemory : BitVec 64 → W :=
  fun a => if a = 8#64 then .word 0#64 else .word 1#64

-- write_empty=Word 0w, write_hit=Word 170w, write_miss=Word 0w
#guard writeBytearrayExact 8#64 [] initialMemory (fun a => a == 8#64) false 8#64 == .word 0#64
#guard writeBytearrayExact 8#64 [0xaa#8] initialMemory (fun a => a == 8#64) false 8#64 ==
  .word 170#64
#guard writeBytearrayExact 8#64 [0xaa#8] initialMemory (fun a => a == 16#64) false 8#64 ==
  .word 0#64

def runChecks : IO Bool := do
  IO.println "PASS exact loopSem loop_primop and wordSem write_bytearray HOL parity"
  pure true

end Flapjack.Test.LoopSemPrimopBytesExactParity
