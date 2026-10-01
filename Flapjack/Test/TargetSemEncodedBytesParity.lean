import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Misc.BytesInMemory

/-!
Kernel exercise for the exact targetSem prerequisites `apply_oracle_def`,
`encoded_bytes_in_mem_def` (`targetSemScript.sml:46-57`) and miscScript
`bytes_in_memory_def` (`miscScript.sml:4176-4180`), paired with the original
HOL `EVAL` rows in `scripts/hol-probes/target_sem_encoded_bytes_probe.out`.
Concrete `AsmConfigExact`/`HolAsm` values are used (no normalized substitute).
-/

namespace Flapjack.Test.TargetSemEncodedBytesParity

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Concrete 8-bit asm config whose `encode` returns `[10,20,30,40]`, with
    `code_alignment = 1` so each block is two bytes. -/
def testConfig : AsmConfigExact 8 where
  isa := .riscv
  encode := fun _ => [10, 20, 30, 40]
  bigEndian := false
  codeAlignment := 1
  linkReg := none
  avoidRegs := []
  regCount := 8
  fpRegCount := 8
  twoRegArith := true
  validImm := fun _ _ => true
  addrOffset := (0, 0)
  hwOffset := (0, 0)
  byteOffset := (0, 0)
  jumpOffset := (0, 0)
  cjumpOffset := (0, 0)
  locOffset := (0, 0)

/-- Original HOL `oracle_first=5`. -/
example : (applyOracleHOL (fun n (x : Nat) => n + x) 5).1 = 5 := rfl

/-- Original HOL `oracle_shift=8` (`shift_seq 1`). -/
example : (applyOracleHOL (fun n (x : Nat) => n + x) 5).2 0 7 = 8 := rfl

/-- Original HOL `bytes_empty=T`. -/
example : bytesInMemoryHOL (width := 8) 0 ([] : List (BitVec 8))
    (fun _ => 0) (fun _ => False) = True := rfl

/-- Original HOL `bytes_nonempty=T`. -/
example : bytesInMemoryHOL (width := 8) 0 [30, 40]
    (fun a : BitVec 8 => if a = 0 then 30 else if a = 1 then 40 else 0)
    (fun _ => True) = True := by simp [bytesInMemoryHOL]

/-- Original HOL `bytes_domain_fail=F`. -/
example : bytesInMemoryHOL (width := 8) 0 [30] (fun _ => 30)
    (fun a : BitVec 8 => a ≠ 0) = False := by simp [bytesInMemoryHOL]

/-- Original HOL `bytes_wrap=T` (address `255w` then `0w` at width 1). -/
example : bytesInMemoryHOL (width := 1) 255 [1, 2]
    (fun a : BitVec 1 => if a = 255 then 1 else if a = 0 then 2 else 0)
    (fun _ => True) = True := by simp [bytesInMemoryHOL]

/-- Original HOL `encoded_guard_strict=F`: the alignment guard is strict. -/
example : ¬ (2 * 2 ^ testConfig.codeAlignment <
    (testConfig.encode (HolAsm.jump (0 : BitVec 8))).length) := by decide

/-- Original HOL `encoded_drop`/`encoded_bytes_match`: the `DROP` alignment
    offset is exercised with a concrete `HolAsm` witness. -/
example : encodedBytesInMemHOL testConfig 0
    (fun a : BitVec 8 => if a = 0 then 30 else if a = 1 then 40 else 0)
    (fun _ => True) :=
  ⟨HolAsm.jump (0 : BitVec 8), 1, by decide, by simp [bytesInMemoryHOL, testConfig]⟩

def runChecks : IO Bool := do
  IO.println "PASS targetSem apply_oracle/bytes_in_memory/encoded_bytes_in_mem kernel rows (9 rows)"
  pure true

end Flapjack.Test.TargetSemEncodedBytesParity
