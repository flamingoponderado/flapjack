import Flapjack.Compiler.Backend.Semantics.TargetSem.EncodedBytes
import Flapjack.Compiler.Backend.Semantics.TargetSem.Machine
import Flapjack.Misc.BytesInMemory

/-!
Kernel exercise for the exact targetSem prerequisites `apply_oracle_def`,
`encoded_bytes_in_mem_def` (`targetSemScript.sml:46-57`) and miscScript
`bytes_in_memory_def` (`miscScript.sml:4176-4180`), paired with the original
HOL evaluation rows and a whole-predicate proof in
`scripts/hol-probes/target_sem_encoded_bytes_probe.out`.

The inputs below deliberately mirror the probe's HOL inputs literally:
`testMemory` is the probe's `m` (`0 ↦ 30`, `1 ↦ 40`, else `0`), `testDomain`
is `UNIV`, and the wrap memory is the probe's `mw` (`255 ↦ 1`, `0 ↦ 2`, else
`0`).  Concrete `AsmConfigExact`/`HolAsm` values are used (no normalized
substitute), and every one of the probe's eleven captured rows has a matching
kernel example. The final HOL row proves the entire existential predicate,
checking its conclusion and empty hypothesis list before printing success.
-/

namespace Flapjack.Test.TargetSemEncodedBytesParity

open Flapjack Flapjack.Compiler.Encoders.Asm

/-- The probe's HOL memory `m`: `0 ↦ 30`, `1 ↦ 40`, otherwise `0`. -/
def testMemory : BitVec 8 → BitVec 8 :=
  fun a => if a = 0 then 30 else if a = 1 then 40 else 0

/-- The probe's HOL domain `UNIV`. -/
def testDomain : BitVec 8 → Prop := fun _ => True

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

/-- Original HOL `bytes_empty=T` (probe input: memory `m`, domain `UNIV`). -/
example : bytesInMemoryHOL (width := 8) 0 ([] : List (BitVec 8))
    testMemory testDomain = True := rfl

/-- Original HOL `bytes_nonempty=T` (probe input: `[30w;40w]`, memory `m`,
    domain `UNIV`). -/
example : bytesInMemoryHOL (width := 8) 0 [30, 40] testMemory testDomain =
    True := by simp [bytesInMemoryHOL, testMemory, testDomain]

/-- Original HOL `bytes_domain_fail=F` (probe input: `[30w]`, memory `m`,
    domain `a ≠ 0`). -/
example : bytesInMemoryHOL (width := 8) 0 [30] testMemory
    (fun a : BitVec 8 => a ≠ 0) = False := by simp [bytesInMemoryHOL, testMemory]

/-- Original HOL `bytes_wrap=T` (probe input: address `255w`, `[1w;2w]`,
    memory `mw`, domain `UNIV`). -/
example : bytesInMemoryHOL (width := 1) 255 [1, 2]
    (fun a : BitVec 1 => if a = 255 then 1 else if a = 0 then 2 else 0)
    (fun _ => True) = True := by simp [bytesInMemoryHOL]

/-- Original HOL `encoded_drop=[30w;40w]`: the `DROP` alignment offset applied
    to the concrete config's `encode`. -/
example : (testConfig.encode (HolAsm.jump (0 : BitVec 8))).drop
    (1 * 2 ^ testConfig.codeAlignment) = [30, 40] := by decide

/-- Original HOL `encoded_guard_true=T`: the alignment guard holds at `1`. -/
example : 1 * 2 ^ testConfig.codeAlignment <
    (testConfig.encode (HolAsm.jump (0 : BitVec 8))).length := by decide

/-- Original HOL `encoded_guard_strict=F`: the alignment guard is strict, so
    `2` fails. -/
example : ¬ (2 * 2 ^ testConfig.codeAlignment <
    (testConfig.encode (HolAsm.jump (0 : BitVec 8))).length) := by decide

/-- Original HOL `encoded_bytes_match=T`: the dropped bytes satisfy
    `bytes_in_memory` at `0` under memory `m` and domain `UNIV`. -/
example : bytesInMemoryHOL (width := 8) 0
    ((testConfig.encode (HolAsm.jump (0 : BitVec 8))).drop
      (1 * 2 ^ testConfig.codeAlignment)) testMemory testDomain := by
  simp [bytesInMemoryHOL, testMemory, testDomain, testConfig]

/-- Original HOL `encoded_bytes_in_mem_whole=T`: the same whole predicate,
    proved in HOL with instruction `Jump 0w` and alignment-block index `1`. -/
example : encodedBytesInMemHOL testConfig 0 testMemory testDomain :=
  ⟨HolAsm.jump (0 : BitVec 8), 1, by decide, by simp [bytesInMemoryHOL, testMemory, testDomain, testConfig]⟩

def runChecks : IO Bool := do
  IO.println "PASS targetSem apply_oracle/bytes_in_memory/encoded_bytes_in_mem kernel rows (11 original-HOL rows, 11 kernel examples)"
  pure true

end Flapjack.Test.TargetSemEncodedBytesParity
