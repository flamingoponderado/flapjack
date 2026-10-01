import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Encoders.AsmSem.State
import Flapjack.Misc.AsmWriteBytearray

/-!
# Exact targetSem post-FFI / post-cache-clear successor asm states

Counterpart of `cakeml/compiler/backend/semantics/targetSemScript.sml`'s
`post_ffi_asm_def` (`:395-408`) and `post_ccache_asm_def` (`:410-423`), over
the exact carriers `MachineConfig`, `HolAsmTarget` and `AsmState`.

Both definitions refresh caller-saved registers and all FP registers from the
machine state and set the program counter to the link-register value.
`postFfiAsmHOL` additionally writes the returned bytes to memory with
`asm_write_bytearray` (ported in `Flapjack.Misc.AsmWriteBytearray`), whereas
`postCcacheAsmHOL` leaves memory unchanged and instead preserves the pointer
register.

`'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
discharge; `word8` is `BitVec 8`.  These modules supply definitions only, no
evaluator.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `post_ffi_asm_def` (`cakeml/compiler/backend/semantics/targetSemScript.sml:395-408`).
    Caller-saved registers and all FP registers come from the machine state;
    the returned bytes are written with `asm_write_bytearray`; the pc is the
    link-register value. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "post_ffi_asm_def"
  (words_as_type_indexed_bitvec)]
def postFfiAsmHOL {width : Nat} [NeZero width] {state projection : Type}
    (mcConf : MachineConfig width state projection) (t1 : AsmState width)
    (newBytes : List (BitVec 8)) (ms' : state) : AsmState width :=
  { t1 with
    regs := fun a =>
      if mcConf.calleeSavedRegs.contains a ||
          decide (¬ a < mcConf.target.config.regCount) ||
          mcConf.target.config.avoidRegs.contains a then
        t1.regs a
      else
        mcConf.target.getReg ms' a
    fpRegs := fun i => mcConf.target.getFpReg ms' i
    mem := asmWriteBytearrayHOL (t1.regs mcConf.ptr2Reg) newBytes t1.mem
    pc := t1.regs (match mcConf.target.config.linkReg with | none => 0 | some n => n) }

/-- Exact HOL `post_ccache_asm_def` (`cakeml/compiler/backend/semantics/targetSemScript.sml:410-423`).
    Like `postFfiAsmHOL` but additionally preserving the pointer register and
    not touching memory. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "post_ccache_asm_def"
  (words_as_type_indexed_bitvec)]
def postCcacheAsmHOL {width : Nat} [NeZero width] {state projection : Type}
    (mcConf : MachineConfig width state projection) (t1 : AsmState width)
    (ms' : state) : AsmState width :=
  { t1 with
    regs := fun a =>
      if mcConf.calleeSavedRegs.contains a ||
          a = mcConf.ptrReg ||
          decide (¬ a < mcConf.target.config.regCount) ||
          mcConf.target.config.avoidRegs.contains a then
        t1.regs a
      else
        mcConf.target.getReg ms' a
    fpRegs := fun i => mcConf.target.getFpReg ms' i
    pc := t1.regs (match mcConf.target.config.linkReg with | none => 0 | some n => n) }

end Flapjack
