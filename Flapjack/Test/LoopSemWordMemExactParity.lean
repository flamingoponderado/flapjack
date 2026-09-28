import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.LoopSemStateExact

/-!
# Exact wordSem memory helpers and loopSem `exit_loop` against HOL oracle rows

Rows from `scripts/hol-probes/pan_fixed_load_probe.out`,
`scripts/hol-probes/pan_sem_mem_store_32_probe.out` (panSem's `mem_load_32`,
`mem_load_byte` and `mem_store_32` have the same text as the wordSem ones, with
`word_lab` for `word_loc`), and `scripts/hol-probes/loop_sem_exit_loop_probe.out`.
-/

namespace Flapjack.Test.LoopSemWordMemExactParity

open Flapjack

private def m64 : BitVec 64 → WordLocW 64 := fun _ => .word 0x0807060504030201#64
private def dom8 : BitVec 64 → Bool := fun a => a == 8#64
private def dom16 : BitVec 64 → Bool := fun a => a == 16#64

-- byte_hit=SOME 2w, byte_miss=NONE, byte_big_endian=SOME 7w
#guard memLoadByteAuxExact m64 dom8 false 9#64 == some 2#8
#guard memLoadByteAuxExact m64 dom16 false 9#64 == none
#guard memLoadByteAuxExact m64 dom8 true 9#64 == some 7#8
-- load32_hit, load32_unaligned, load32_domain_miss, load32_big_endian
#guard memLoad32Exact m64 dom8 false 8#64 == some 0x4030201#32
#guard memLoad32Exact m64 dom8 false 9#64 == none
#guard memLoad32Exact m64 dom16 false 8#64 == none
#guard memLoad32Exact m64 dom8 true 8#64 == some 0x8070605#32
-- byte_hit_width8=SOME 165w, load32_hit_width8=SOME 0xA5A5A5A5w
#guard memLoadByteAuxExact (fun _ : BitVec 8 => (.word 0xa5#8 : WordLocW 8))
  (fun a => a == 0#8) false 0#8 == some 165#8
#guard memLoad32Exact (fun _ : BitVec 8 => (.word 0xa5#8 : WordLocW 8))
  (fun a => a == 0#8) false 0#8 == some 0xA5A5A5A5#32
-- load32_unaligned_width1_address1=NONE,
-- load32_aligned_width1_address0 = SOME 0x00010001w (MOD_0 simp row)
#guard memLoad32Exact (fun _ : BitVec 1 => (.word 1#1 : WordLocW 1))
  (fun _ => true) false 1#1 == none
#guard memLoad32Exact (fun _ : BitVec 1 => (.word 1#1 : WordLocW 1))
  (fun _ => true) false 0#1 == some 0x00010001#32

private def m0 : BitVec 64 → WordLocW 64 := fun _ => .word 0#64
private def dom0 : BitVec 64 → Bool := fun a => a == 0#64

private def ms32 (dom : BitVec 64 → Bool) (be : Bool) (addr read : BitVec 64) :
    WordLocW 64 :=
  match memStore32Exact m0 dom be addr 0x11223344#32 with
  | some m => m read
  | none => .word 0#64

-- ms32_aligned .. ms32_other_cell
#guard ms32 dom0 false 0#64 0#64 == .word 0x11223344#64
#guard ms32 dom0 false 4#64 0#64 == .word 0x1122334400000000#64
#guard ms32 dom0 false 2#64 0#64 == .word 0#64
#guard ms32 (fun _ => false) false 0#64 0#64 == .word 0#64
#guard ms32 dom0 true 0#64 0#64 == .word 0x1122334400000000#64
#guard ms32 dom0 false 0#64 8#64 == .word 0#64

-- mem_store_byte_aux round-trips through mem_load_byte_aux.
#guard (memStoreByteAuxExact m64 dom8 false 9#64 0xee#8).bind
  (fun m => memLoadByteAuxExact m dom8 false 9#64) == some 0xee#8
#guard (memStoreByteAuxExact m64 dom8 false 9#64 0xee#8).map (· 8#64) ==
  some (.word 0x080706050403ee01#64)
#guard (memStoreByteAuxExact m64 dom16 false 9#64 0xee#8).isNone

-- loop_sem_exit_loop_probe.out, rendered by a small tag so no `BEq` is needed
-- on the tagged result type.
private def tag : Option (LoopSemStateFiniteExact.LoopResultExact 64) → String
  | none => "NONE"
  | some (.break n) => s!"Break {n}"
  | some (.continue n) => s!"Continue {n}"
  | some .timeOut => "TimeOut"
  | some .error => "Error"
  | some _ => "other"

#guard tag (LoopSemStateFiniteExact.exitLoop (some (.break 3))) == "Break 2"
#guard tag (LoopSemStateFiniteExact.exitLoop (some (.break 0))) == "Break 0"
#guard tag (LoopSemStateFiniteExact.exitLoop (some (.continue 2))) == "Continue 1"
#guard tag (LoopSemStateFiniteExact.exitLoop (some .timeOut)) == "TimeOut"
#guard tag (LoopSemStateFiniteExact.exitLoop none) == "NONE"
#guard tag (LoopSemStateFiniteExact.exitLoop (some .error)) == "Error"

def runChecks : IO Bool := do
  IO.println "PASS exact wordSem mem_load_32/mem_store_32/mem_*_byte_aux and loopSem exit_loop HOL parity"
  pure true

end Flapjack.Test.LoopSemWordMemExactParity
