import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel

/-!
# Parity checks for the two sides of `write_bytearray_mem_rel`

Direct HOL oracle: `scripts/hol-probes/crep_to_loop_write_bytearray_mem_rel_probe.out`
(probe `crep_to_loop_write_bytearray_mem_rel_probeScript.sml`), evaluating
`panSem$write_bytearray` and `wordSem$write_bytearray` on the same address
(`14w`), bytes (`[0xaa; 0xbb; 0xcc]`), domain and endianness from
`wlab_wloc`-related 64-bit memories, and reading the two affected aligned
words. The Lean replays are the exact `panWriteBytearrayWord8HOL` and
`writeBytearrayExact` related by the tagged `write_bytearray_mem_rel`.
Regenerate with `CAKEML=/home/zksecurity/pancake-lean/cakeml
HOL_PROBE_ONLY=crep_to_loop_write_bytearray_mem_rel_probeScript.sml
bash scripts/hol-probes/regenerate.sh`.
-/

namespace Flapjack.Test.CrepToLoopWriteBytearrayMemRelParity

open Flapjack

def panMem : BitVec 64 → HolWordLab 64 :=
  fun a => if a = 8#64 then .word 0x1122334455667788#64 else .word 0#64

def wordMem : BitVec 64 → WordLocW 64 :=
  fun a => if a = 8#64 then .word 0x1122334455667788#64 else .word 0#64

def bytes : List (BitVec 8) := [0xaa#8, 0xbb#8, 0xcc#8]

def domFull (a : BitVec 64) : Bool := a == 8#64 || a == 16#64
def domPart (a : BitVec 64) : Bool := a == 16#64

def pan (dom : BitVec 64 → Bool) (be : Bool) (a : BitVec 64) : HolWordLab 64 :=
  panWriteBytearrayWord8HOL 14#64 bytes panMem (fun x => dom x = true) be a

def word (dom : BitVec 64 → Bool) (be : Bool) (a : BitVec 64) : WordLocW 64 :=
  writeBytearrayExact 14#64 bytes wordMem dom be a

-- le_full_8_pan = le_full_8_word = Word 0xBBAA334455667788w
#guard pan domFull false 8#64 == .word 0xBBAA334455667788#64
#guard word domFull false 8#64 == .word 0xBBAA334455667788#64
-- le_full_16_{pan,word} = Word 204w
#guard pan domFull false 16#64 == .word 204#64
#guard word domFull false 16#64 == .word 204#64
-- be_full_8_{pan,word} = Word 0x112233445566AABBw
#guard pan domFull true 8#64 == .word 0x112233445566AABB#64
#guard word domFull true 8#64 == .word 0x112233445566AABB#64
-- be_full_16_{pan,word} = Word 0xCC00000000000000w
#guard pan domFull true 16#64 == .word 0xCC00000000000000#64
#guard word domFull true 16#64 == .word 0xCC00000000000000#64
-- le_part_16_{pan,word} = Word 0w (the failed store at 14w returns the input memory)
#guard pan domPart false 16#64 == .word 0#64
#guard word domPart false 16#64 == .word 0#64
-- le_part_8_{pan,word} = Word 0x1122334455667788w
#guard pan domPart false 8#64 == .word 0x1122334455667788#64
#guard word domPart false 8#64 == .word 0x1122334455667788#64

-- `mem_rel` conclusion on the domain: `wlab_wloc (pan a) = word a`.
#guard [8#64, 16#64].all fun a =>
  [false, true].all fun be => wlabWlocExact (pan domFull be a) == word domFull be a

def runChecks : IO Bool := do
  IO.println "PASS crep_to_loop write_bytearray_mem_rel direct HOL oracle parity"
  pure true

end Flapjack.Test.CrepToLoopWriteBytearrayMemRelParity
