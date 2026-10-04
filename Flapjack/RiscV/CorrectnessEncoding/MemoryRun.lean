import Flapjack.RiscV.CorrectnessEncoding.BinopRun
import Flapjack.RiscV.L3.Step.StoreStep
import Flapjack.Compiler.Encoders.RiscV.Target.State

/-! Literal actual native memory Run compositions for the original fixed RV64
target. Mode and bare translation follow only from riscvOk; every intrinsic
register and signed-offset bit pattern remains arbitrary, including register
zero and aliases. These local compositions have no separately named HOL
original and remain untagged. The full encoder case must still derive source
memory-domain and alignment obligations, actual fetch/Next, interference and
assertions from its original source-step/initial relation premises. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Original actual LD Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_ld (rd rs : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Load (.LD (rd, rs, offs))) ms =
      «write'GPR» (rawReadData (GPR rs ms + offs.signExtend 64) ms, rd) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp only [Run, «dfn'LD»]
  have mode : in32BitMode () ms = (false, ms) := by
    simp [in32BitMode, curArch, architecture, MCSR, arch]
  rw [mode]
  simp only [Bool.false_eq_true, reduceIte]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual LWU Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_lwu (rd rs : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Load (.LWU (rd, rs, offs))) ms =
      «write'GPR» ((RiscV.L3.holWordExtract 32 31 0 (rawReadData (GPR rs ms + offs.signExtend 64) ms)).setWidth 64, rd) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp only [Run, «dfn'LWU»]
  have mode : in32BitMode () ms = (false, ms) := by
    simp [in32BitMode, curArch, architecture, MCSR, arch]
  rw [mode]
  simp only [Bool.false_eq_true, reduceIte]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual LHU Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_lhu (rd rs : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Load (.LHU (rd, rs, offs))) ms =
      «write'GPR» ((RiscV.L3.holWordExtract 16 15 0 (rawReadData (GPR rs ms + offs.signExtend 64) ms)).setWidth 64, rd) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  simp only [Run, «dfn'LHU»]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual LBU Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_lbu (rd rs : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Load (.LBU (rd, rs, offs))) ms =
      «write'GPR» ((RiscV.L3.holWordExtract 8 7 0 (rawReadData (GPR rs ms + offs.signExtend 64) ms)).setWidth 64, rd) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  simp only [Run, «dfn'LBU»]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual SD Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_sd (base value : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Store (.SD (base, value, offs))) ms =
      rawWriteData (GPR base ms + offs.signExtend 64, GPR value ms, 8) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  have arch := ((riscvOk_iff ms).mp ok).2.1
  simp only [Run, «dfn'SD»]
  have mode : in32BitMode () ms = (false, ms) := by
    simp [in32BitMode, curArch, architecture, MCSR, arch]
  rw [mode]
  simp only [Bool.false_eq_true, reduceIte]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual SW Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_sw (base value : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Store (.SW (base, value, offs))) ms =
      rawWriteData (GPR base ms + offs.signExtend 64, GPR value ms, 4) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  simp only [Run, «dfn'SW»]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual SH Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_sh (base value : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Store (.SH (base, value, offs))) ms =
      rawWriteData (GPR base ms + offs.signExtend 64, GPR value ms, 2) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  simp only [Run, «dfn'SH»]
  rw [translateAddr_bare _ _ _ ms vm]

/-- Original actual SB Run under fixed-target validity alone; local
infrastructure, no separately named HOL original. -/
theorem memory_run_sb (base value : BitVec 5) (offs : BitVec 12)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    Run (.Store (.SB (base, value, offs))) ms =
      rawWriteData (GPR base ms + offs.signExtend 64, GPR value ms, 1) ms := by
  have vm := ((riscvOk_iff ms).mp ok).1
  simp only [Run, «dfn'SB»]
  rw [translateAddr_bare _ _ _ ms vm]

end Flapjack.RiscV.TargetProof
