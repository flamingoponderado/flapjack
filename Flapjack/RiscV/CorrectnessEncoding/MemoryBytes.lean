import Flapjack.RiscV.L3.Step.ByteMemory
import Flapjack.RiscV.CorrectnessEncoding.MemoryRun

/-! Flapjack-specific byte consequences of the actual native memory definitions.
The byte-level library lives in `L3.Step.ByteMemory` and is shared here; this
module keeps only the LBU consequence that needs the native Run equations.
No independently named HOL theorem is claimed. -/
set_option autoImplicit false
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step.ByteMemory

/-- Actual native LBU loads the addressed byte under only original RV64 validity.
Registers and signed offsets are unrestricted, including zero and aliases;
this local consequence is not tagged as the full encoder theorem. -/
theorem memory_run_lbu_byte (rd rs : BitVec 5) (offs : BitVec 12)
    (s : riscv_state)
    (ok : Flapjack.Compiler.Encoders.RiscV.Target.riscvOk s = true) :
    Run (.Load (.LBU (rd,rs,offs))) s =
      «write'GPR» ((s.MEM8 (GPR rs s + offs.signExtend 64)).setWidth 64,rd) s := by
  rw [memory_run_lbu rd rs offs s ok, memory_raw_read_low_byte]

end Flapjack.RiscV.TargetProof
