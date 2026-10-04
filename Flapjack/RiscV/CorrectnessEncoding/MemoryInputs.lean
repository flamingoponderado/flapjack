import Flapjack.RiscV.CorrectnessEncoding.MemoryRun
import Flapjack.RiscV.CorrectnessEncoding.Immediate
import Flapjack.Compiler.Encoders.AsmSem.Step
import Flapjack.Compiler.Encoders.RiscV.Target.AsmOkRewrites

/-! Source-to-native inputs for the original Mem case (riscv_targetProof661–669).
These are local compositions of the reviewed asm guards, initial state relation,
address definition and signed immediate reconstruction, with no separately named
HOL originals. They stay untagged. Full native fetch, interference, assertions
and the complete post-state relation remain obligations of the Mem case. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 20000

/-- All eight literal memory constructors have the same register and signed
offset guards. No successful native execution is assumed. -/
theorem memory_source_guards (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (ok : asmOkExact (.inst (.mem m r (.addr base w))) riscvConfig = true) :
    asmRegOkExact r riscvConfig = true ∧
    asmRegOkExact base riscvConfig = true ∧
    -2048 ≤ w.toInt ∧ w.toInt ≤ 2047 := by
  cases m
  all_goals
    simp [asmOkExact, asmInstOkExact, asmAddrOffsetOkExact,
      asmHwOffsetOkExact, asmByteOffsetOkExact, asmOffsetOkExact,
      asmAligned, riscvConfig, Bool.and_eq_true, and_assoc,
      Nat.mod_one] at ok
    exact ⟨ok.1, ok.2.1, of_decide_eq_true ok.2.2.1,
      of_decide_eq_true ok.2.2.2⟩

/-- The initial relation supplies the actual native GPR, including proof that
the source-permitted register is not architectural zero. -/
theorem memory_source_register (r : Nat) (s : AsmState 64) (t : riscv_state)
    (ok : asmRegOkExact r riscvConfig = true)
    (relation : targetStateRel riscvTarget s t) :
    GPR (BitVec.ofNat 5 r) t = readReg r s := by
  have guards : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact, Bool.and_eq_true] using ok
  have bound : r < 32 := guards.1
  have nonzero : r ≠ 0 := by
    intro zero
    simpa [zero, riscvConfig] using guards.2
  have encoded_nonzero : BitVec.ofNat 5 r ≠ 0 := by
    intro zero
    have eq := congrArg BitVec.toNat zero
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at eq
    exact nonzero eq
  have eq := relation.2.2.2.1 r guards
  have test : (BitVec.ofNat 5 r == (0 : BitVec 5)) = false := by
    simp only [beq_eq_false_iff_ne]
    exact encoded_nonzero
  change (if BitVec.ofNat 5 r == (0 : BitVec 5) then 0
    else t.c_gpr t.procID (BitVec.ofNat 5 r)) = s.regs r
  rw [test]
  exact eq

/-- The signed12 native offset reconstructs the full original word64 offset
from the actual source guard, retaining both signed endpoints. -/
theorem memory_source_offset (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (ok : asmOkExact (.inst (.mem m r (.addr base w))) riscvConfig = true) :
    (w.setWidth 12).signExtend 64 = w := by
  have bounds := (memory_source_guards m r base w ok).2.2
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  have eq := BitVec.toInt_signExtend_eq_toInt_bmod_of_le w (by decide : 12 ≤ 64)
  rw [BitVec.signExtend_eq_setWidth_of_le w (by decide : 12 ≤ 64)] at eq
  rw [eq]
  apply Int.bmod_eq_of_le <;> omega

/-- Both native base-address and store-value inputs follow from the original
source guard and initial relation alone; source register aliases are admitted. -/
theorem memory_source_inputs (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s : AsmState 64) (t : riscv_state)
    (ok : asmOkExact (.inst (.mem m r (.addr base w))) riscvConfig = true)
    (relation : targetStateRel riscvTarget s t) :
    GPR (BitVec.ofNat 5 base) t + (w.setWidth 12).signExtend 64 =
      addrHOL (.addr base w) s ∧
    GPR (BitVec.ofNat 5 r) t = readReg r s := by
  have guards := memory_source_guards m r base w ok
  rw [memory_source_offset m r base w ok,
    memory_source_register base s t guards.2.1 relation,
    memory_source_register r s t guards.1 relation]
  exact ⟨rfl, rfl⟩

/-- The original seven-conjunct source step discharges every input guard;
there is no desired target-run or post-state premise. -/
theorem memory_step_inputs (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64) (t : riscv_state)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s')
    (relation : targetStateRel riscvTarget s t) :
    GPR (BitVec.ofNat 5 base) t + (w.setWidth 12).signExtend 64 =
      addrHOL (.addr base w) s ∧
    GPR (BitVec.ofNat 5 r) t = readReg r s :=
  memory_source_inputs m r base w s t step.2.2.2.2.2.2 relation

/-- Actual Run of every emitted memory AST, expressed using original source
address/value inputs. Membership only selects the instruction emitted by
`riscvAst`; neither a target execution nor its result is a premise. -/
theorem memory_emitted_run (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s : AsmState 64) (t : riscv_state) (native : instruction)
    (ok : asmOkExact (.inst (.mem m r (.addr base w))) riscvConfig = true)
    (relation : targetStateRel riscvTarget s t)
    (emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w)))) :
    Run native t =
      match m with
      | .load => «write'GPR» (rawReadData (addrHOL (.addr base w) s) t,
          BitVec.ofNat 5 r) t
      | .load32 => «write'GPR» ((RiscV.L3.holWordExtract 32 31 0
          (rawReadData (addrHOL (.addr base w) s) t)).setWidth 64,
          BitVec.ofNat 5 r) t
      | .load16 => «write'GPR» ((RiscV.L3.holWordExtract 16 15 0
          (rawReadData (addrHOL (.addr base w) s) t)).setWidth 64,
          BitVec.ofNat 5 r) t
      | .load8 => «write'GPR» ((RiscV.L3.holWordExtract 8 7 0
          (rawReadData (addrHOL (.addr base w) s) t)).setWidth 64,
          BitVec.ofNat 5 r) t
      | .store => rawWriteData (addrHOL (.addr base w) s, readReg r s, 8) t
      | .store32 => rawWriteData (addrHOL (.addr base w) s, readReg r s, 4) t
      | .store16 => rawWriteData (addrHOL (.addr base w) s, readReg r s, 2) t
      | .store8 => rawWriteData (addrHOL (.addr base w) s, readReg r s, 1) t := by
  have inputs := memory_source_inputs m r base w s t ok relation
  have valid : riscvOk t = true := relation.1
  cases m
  all_goals
    simp only [riscvAst, riscvMemop, List.mem_singleton] at emitted
    subst native
    first
    | rw [memory_run_ld _ _ _ t valid, inputs.1]
    | rw [memory_run_lwu _ _ _ t valid, inputs.1]
    | rw [memory_run_lhu _ _ _ t valid, inputs.1]
    | rw [memory_run_lbu _ _ _ t valid, inputs.1]
    | rw [memory_run_sd _ _ _ t valid, inputs.1, inputs.2]
    | rw [memory_run_sw _ _ _ t valid, inputs.1, inputs.2]
    | rw [memory_run_sh _ _ _ t valid, inputs.1, inputs.2]
    | rw [memory_run_sb _ _ _ t valid, inputs.1, inputs.2]

/-- Matched original regressions: all constructors admit both signed endpoints. -/
theorem memory_inputs_signed_endpoints (m : HolMemop) :
    asmOkExact (.inst (.mem m 1 (.addr 30 (-2048)))) riscvConfig = true ∧
    asmOkExact (.inst (.mem m 1 (.addr 30 2047))) riscvConfig = true ∧
    ((-2048 : BitVec 64).setWidth 12).signExtend 64 = -2048 ∧
    ((2047 : BitVec 64).setWidth 12).signExtend 64 = 2047 := by
  cases m <;> decide

/-- Matched original regressions: architectural exclusions and numeric overflow
are rejected on both destination/value and base registers. -/
theorem memory_inputs_reject_registers (m : HolMemop) :
    ([0,2,3,4,31,32,64] : List Nat).all (fun r =>
      !(asmOkExact (.inst (.mem m r (.addr 1 0))) riscvConfig) &&
      !(asmOkExact (.inst (.mem m 1 (.addr r 0))) riscvConfig)) = true := by
  cases m <;> decide

/-- Matched original regressions retain both just-outside signed limits. -/
theorem memory_inputs_reject_offsets (m : HolMemop) :
    asmOkExact (.inst (.mem m 1 (.addr 30 (-2049)))) riscvConfig = false ∧
    asmOkExact (.inst (.mem m 1 (.addr 30 2048))) riscvConfig = false := by
  cases m <;> decide

/-- Matched literal source/native alias and wraparound observation; the native
state's unrelated fields and the source carrier are arbitrary. -/
theorem memory_inputs_alias_wrap (s : AsmState 64) (t : riscv_state) :
    addrHOL (.addr 1 (-2048)) {s with regs := fun _ => 2047} = -1 ∧
    GPR 1 {t with c_gpr := fun _ _ => 2047} +
      ((-2048 : BitVec 64).setWidth 12).signExtend 64 = -1 ∧
    readReg 1 {s with regs := fun _ => 2047} = 2047 ∧
    GPR 1 {t with c_gpr := fun _ _ => 2047} = 2047 := by
  change (2047 : BitVec 64) + -2048 = -1 ∧
    2047 + ((-2048 : BitVec 64).setWidth 12).signExtend 64 = -1 ∧
    (2047 : BitVec 64) = 2047 ∧ (2047 : BitVec 64) = 2047
  decide

end Flapjack.RiscV.TargetProof
