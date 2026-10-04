import Flapjack.Compiler.Backend.LabSem.Memory

/-! Native shared-memory FFI transitions corresponding to labSemScript429–488.
Unlike ordinary memory operations, shared-memory Load16/Store16 are supported.
All fields outside the explicit HOL record updates remain unchanged. Protocol
bytes are little endian independently of the ordinary-memory `be` field.
-/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Byte-carrier infrastructure for HOL library word_to_bytes; no CakeML
declaration owns this library operation. Uses the reviewed byte extractor. -/
def sharedMemoryWordBytes {width : Nat} (value : BitVec width) : List (BitVec 8) :=
  (List.range (width / 8)).map fun index =>
    Flapjack.getByteHOL8 (BitVec.ofNat width index) value false

/-- Whole-word requests require word alignment and the exact address in the
shared domain; narrow requests require only its byte-aligned base in that
domain. A returning load decodes every returned byte, irrespective of size. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shareMemLoad {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) (size : Nat) :
    Option (HolFfiResult F × Flapjack.Compiler.Backend.LabSem.State width C F) :=
  match addrValue address state with
  | none => none
  | some value =>
      if (if size = 0 then
          value.toNat % (width / 8) == 0 && state.sharedMemDomain value
        else state.sharedMemDomain (Flapjack.riscvByteAlignHOL value)) then
        match callFFIHOL state.ffi (.sharedMem .mappedRead)
            [BitVec.ofNat 8 size] (sharedMemoryWordBytes value) with
        | .final outcome => some (.final outcome, state)
        | .ret ffi bytes =>
            some (.ret ffi bytes, { state with
              ffi := ffi
              regs := (fun r => if r = register then
                .word (Flapjack.wordOfBytesHOL8 false 0 bytes) else state.regs r)
              pc := state.pc + 1
              clock := state.clock - 1 })
      else none

/-- Stores send the requested prefix of the value bytes followed by the full
address bytes. Final outcomes preserve the original state; returns advance
the PC and decrement the clock after replacing only the FFI state. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shareMemStore {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) (size : Nat) :
    Option (HolFfiResult F × Flapjack.Compiler.Backend.LabSem.State width C F) :=
  match state.regs register with
  | .loc _ _ => none
  | .word word =>
      match addrValue address state with
      | none => none
      | some value =>
          if (if size = 0 then
              value.toNat % (width / 8) == 0 && state.sharedMemDomain value
            else state.sharedMemDomain (Flapjack.riscvByteAlignHOL value)) then
            match callFFIHOL state.ffi (.sharedMem .mappedWrite)
                [BitVec.ofNat 8 size]
                ((if size = 0 then sharedMemoryWordBytes word
                  else (sharedMemoryWordBytes word).take size) ++ sharedMemoryWordBytes value) with
            | .final outcome => some (.final outcome, state)
            | .ret ffi bytes => some (.ret ffi bytes, incPc (decClock { state with ffi := ffi }))
          else none

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shareMemOp {width : Nat} [NeZero width] {C F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (state : Flapjack.Compiler.Backend.LabSem.State width C F) :
    Option (HolFfiResult F × Flapjack.Compiler.Backend.LabSem.State width C F) :=
  match operator with
  | .load => shareMemLoad register address state 0
  | .load8 => shareMemLoad register address state 1
  | .load16 => shareMemLoad register address state 2
  | .load32 => shareMemLoad register address state 4
  | .store => shareMemStore register address state 0
  | .store8 => shareMemStore register address state 1
  | .store16 => shareMemStore register address state 2
  | .store32 => shareMemStore register address state 4

/-- Flapjack-only equation consequence for the full evaluator's termination
proof. This is not a separate HOL declaration: the original evaluator unfolds
the three shared-memory definitions to establish the same clock decrease. -/
theorem shareMemLoad_ret_clock {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (size : Nat) (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemLoad register address state size = some (.ret ffi bytes, next)) :
    next.clock = state.clock - 1 := by
  unfold shareMemLoad at h
  repeat' first | split at h | simp_all
  all_goals exact (congrArg (fun s : Flapjack.Compiler.Backend.LabSem.State width C F => s.clock) h.2).symm

/-- Flapjack-only store equation consequence, used with the load consequence
to discharge the original evaluator's successful shared-memory recursion. -/
theorem shareMemStore_ret_clock {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (size : Nat) (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemStore register address state size = some (.ret ffi bytes, next)) :
    next.clock = state.clock - 1 := by
  unfold shareMemStore at h
  repeat' first | split at h | simp_all [incPc, decClock]
  all_goals exact (congrArg (fun s : Flapjack.Compiler.Backend.LabSem.State width C F => s.clock) h.2).symm

/-- Flapjack-only clock consequence for every source shared-memory case;
the return hypothesis exposes a successful transition, not an assumed bound. -/
theorem shareMemOp_ret_clock {width : Nat} [NeZero width] {C F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (state next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemOp operator register address state = some (.ret ffi bytes, next)) :
    next.clock = state.clock - 1 := by
  cases operator <;> simp only [shareMemOp] at h
  all_goals first
    | exact shareMemLoad_ret_clock _ _ _ _ _ _ _ h
    | exact shareMemStore_ret_clock _ _ _ _ _ _ _ h

end Flapjack.Compiler.Backend.LabSem
