import Flapjack.RiscV.CorrectnessEncoding.ConstStep
import Flapjack.RiscV.CorrectnessEncoding.DecodeShift
import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop
import Flapjack.RiscV.CorrectnessEncoding.ShiftRun

/-! Case-local native execution support for the original Shift Ror paths.
These compositions have no separately named HOL originals and remain untagged.
They derive actual Next from literal bytes and the original fixed-target riscvOk,
with internal nonzero destinations discharged by source asmOk in full case proofs.
All intrinsic operands/counts and the entire native post-state are retained.
The complete Ror encoder traces/assertions remain separate open work. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Literal SRLI full Next composition; untagged local infrastructure. -/
theorem next_ror_encoded_srli (ms : riscv_state) (rd rs : BitVec 5) (shamt : BitVec 6)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.Shift (.SRLI (rd,rs,shamt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms >>> shamt.toNat)) := by
  have lowbits : (Encode (.Shift (.SRLI (rd,rs,shamt)))).getLsbD 0 = true ∧
      (Encode (.Shift (.SRLI (rd,rs,shamt)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.Shift (.SRLI (rd,rs,shamt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms >>> shamt.toNat,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simp [Run, «dfn'SRLI», in32BitMode, curArch, architecture, MCSR, arch, GPR, gpr]
  exact write_next ms (.Shift (.SRLI (rd,rs,shamt))) (Encode (.Shift (.SRLI (rd,rs,shamt)))) rd (GPR rs ms >>> shamt.toNat)
    rn ok (decode_encode_srli _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Literal SLL full Next composition; untagged local infrastructure. -/
theorem next_ror_encoded_sll (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.Shift (.SLL (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms <<< (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat))) := by
  have lowbits : (Encode (.Shift (.SLL (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.Shift (.SLL (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.Shift (.SLL (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms <<< (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat),rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simp [Run, «dfn'SLL», in32BitMode, curArch, architecture, MCSR, arch, GPR, gpr]
  exact write_next ms (.Shift (.SLL (rd,rs,rt))) (Encode (.Shift (.SLL (rd,rs,rt)))) rd (GPR rs ms <<< (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat))
    rn ok (decode_encode_sll _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Literal SRL full Next composition; untagged local infrastructure. -/
theorem next_ror_encoded_srl (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.Shift (.SRL (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms >>> (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat))) := by
  have lowbits : (Encode (.Shift (.SRL (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.Shift (.SRL (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.Shift (.SRL (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms >>> (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat),rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    have arch := ((riscvOk_iff ms).mp ok).2.1
    simp [Run, «dfn'SRL», in32BitMode, curArch, architecture, MCSR, arch, GPR, gpr]
  exact write_next ms (.Shift (.SRL (rd,rs,rt))) (Encode (.Shift (.SRL (rd,rs,rt)))) rd (GPR rs ms >>> (((RiscV.L3.holWordExtract 6 5 0 (GPR rt ms)).setWidth 64).toNat))
    rn ok (decode_encode_srl _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Literal SUB full Next composition; untagged local infrastructure. -/
theorem next_ror_encoded_sub (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithR (.SUB (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms - GPR rt ms)) := by
  have lowbits : (Encode (.ArithR (.SUB (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.ArithR (.SUB (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithR (.SUB (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms - GPR rt ms,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'SUB», GPR, gpr]
  exact write_next ms (.ArithR (.SUB (rd,rs,rt))) (Encode (.ArithR (.SUB (rd,rs,rt)))) rd (GPR rs ms - GPR rt ms)
    rn ok (decode_encode_sub _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Literal missing operations plus previously checked Const operations used by
Ror. This local proof family is not a separately named HOL datatype. -/
inductive RorInstruction : instruction → Prop
  | prior (i : instruction) (kind : ConstRegisterInstruction i) : RorInstruction i
  | srli (rd rs : BitVec 5) (n : BitVec 6) : RorInstruction (.Shift (.SRLI (rd,rs,n)))
  | sll (rd rs rt : BitVec 5) : RorInstruction (.Shift (.SLL (rd,rs,rt)))
  | srl (rd rs rt : BitVec 5) : RorInstruction (.Shift (.SRL (rd,rs,rt)))
  | sub (rd rs rt : BitVec 5) : RorInstruction (.ArithR (.SUB (rd,rs,rt)))

/-- Literal destination selector for this local native instruction family. -/
def rorDestination (i : instruction) : BitVec 5 :=
  match i with
  | .Shift (.SRLI (rd,_,_)) | .Shift (.SLL (rd,_,_))
  | .Shift (.SRL (rd,_,_)) | .ArithR (.SUB (rd,_,_)) => rd
  | _ => constDestination i

/-- Complete native effect includes PC advancement and Skip4; reuse the checked
pure-step definition, not a replacement evaluator or target-run assumption. -/
noncomputable abbrev rorStep := constStep

/-- Actual native Next for this entire local family. Untagged composition. -/
theorem next_ror_step (i : instruction) (kind : RorInstruction i)
    (ms : riscv_state) (rn : rorDestination i ≠ 0#5)
    (ok : riscvOk ms = true) (bytes : encodedInstructionBytes ms i) :
    NextRISCV ms = some (rorStep i ms) := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases kind with
  | prior i kind =>
    have dest : rorDestination i = constDestination i := by
      cases kind <;> rfl
    rw [dest] at rn
    exact next_const_step i kind ms rn ok bytes
  | srli rd rs n =>
    change rd ≠ 0#5 at rn
    have next := next_ror_encoded_srli ms rd rs n rn ok bytes
    simpa [rorStep, constStep, Run, «dfn'SRLI», «write'GPR», «write'gpr»,
      writePost, rn, in32BitMode, curArch, architecture, MCSR, arch] using next
  | sll rd rs rt =>
    change rd ≠ 0#5 at rn
    have next := next_ror_encoded_sll ms rd rs rt rn ok bytes
    simpa [rorStep, constStep, Run, «dfn'SLL», «write'GPR», «write'gpr»,
      writePost, rn, in32BitMode, curArch, architecture, MCSR, arch] using next
  | srl rd rs rt =>
    change rd ≠ 0#5 at rn
    have next := next_ror_encoded_srl ms rd rs rt rn ok bytes
    simpa [rorStep, constStep, Run, «dfn'SRL», «write'GPR», «write'gpr»,
      writePost, rn, in32BitMode, curArch, architecture, MCSR, arch] using next
  | sub rd rs rt =>
    change rd ≠ 0#5 at rn
    have next := next_ror_encoded_sub ms rd rs rt rn ok bytes
    simpa [rorStep, constStep, Run, «dfn'SUB», «write'GPR», «write'gpr», writePost, rn] using next

/-- Full original native Run frame, proved rather than an input. -/
theorem ror_run_frame (i : instruction) (kind : RorInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (Run i ms).procID = ms.procID ∧ (Run i ms).c_PC = ms.c_PC ∧
    (Run i ms).MEM8 = ms.MEM8 ∧ (Run i ms).c_MCSR = ms.c_MCSR ∧
    (Run i ms).c_NextFetch = ms.c_NextFetch ∧ (Run i ms).exception = ms.exception := by
  have arch := ((riscvOk_iff ms).mp ok).2.1
  cases kind
  · exact const_run_frame _ ‹ConstRegisterInstruction _› ms ok
  all_goals
    simp [Run, «dfn'SRLI», «dfn'SLL», «dfn'SRL», «dfn'SUB»,
      in32BitMode, curArch, architecture, MCSR, arch, «write'GPR», «write'gpr»]
    split_ifs <;> simp

/-- Complete native step frame: original memory and processor plus PC+4. -/
theorem ror_step_frame (i : instruction) (kind : RorInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    (rorStep i ms).procID = ms.procID ∧
    (rorStep i ms).MEM8 = ms.MEM8 ∧
    (rorStep i ms).c_PC ms.procID = ms.c_PC ms.procID + 4 := by
  have frame := ror_run_frame i kind ms ok
  simp [rorStep, constStep, frame.1, frame.2.1, frame.2.2.1, holUpdate]

/-- Original target validity follows through the complete native step. -/
theorem ror_step_ok (i : instruction) (kind : RorInstruction i)
    (ms : riscv_state) (ok : riscvOk ms = true) :
    riscvOk (rorStep i ms) = true := by
  have frame := ror_run_frame i kind ms ok
  have fields := (riscvOk_iff ms).mp ok
  apply (riscvOk_iff _).mpr
  simpa [rorStep, constStep, frame.1, frame.2.1, frame.2.2.2.1,
    frame.2.2.2.2.1, frame.2.2.2.2.2, holUpdate] using
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      aligned_add_four _ fields.2.2.2.2⟩

private theorem gpr_projection_eq (d : BitVec 64 → Prop) (ms ns : riscv_state)
    (r : BitVec 5) (h : riscvProj d ms = riscvProj d ns) : GPR r ms = GPR r ns := by
  simp only [riscvProj, Prod.mk.injEq] at h
  simp [GPR, gpr, h.2.2.2.2.1]

private theorem write_gpr_ok (ms : riscv_state) (r : BitVec 5) (v : BitVec 64) :
    riscvOk («write'GPR» (v,r) ms) = riscvOk ms := by
  by_cases zero : r = 0#5 <;> simp [«write'GPR», «write'gpr», riscvOk, zero]

private theorem write_gpr_projection_eq (d : BitVec 64 → Prop)
    (ms ns : riscv_state) (r : BitVec 5) (v : BitVec 64)
    (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d («write'GPR» (v,r) ms) = riscvProj d («write'GPR» (v,r) ns) := by
  by_cases zero : r = 0#5
  · subst r
    simpa [«write'GPR»] using h
  · simp only [riscvProj, Prod.mk.injEq] at h
    simpa [riscvProj, «write'GPR», «write'gpr», holUpdate, zero] using
      ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
        congrArg (holUpdate r v) h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

/-- Full original Run projection congruence, including every scratch GPR. -/
theorem ror_run_projection_eq (d : BitVec 64 → Prop) (i : instruction)
    (kind : RorInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (Run i ms) = riscvProj d (Run i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have archMs := ((riscvOk_iff ms).mp ok).2.1
  have archNs := ((riscvOk_iff ns).mp okNs).2.1
  cases kind with
  | prior i kind => exact const_run_projection_eq d i kind ms ns ok h
  | srli rd rs n =>
    simp [Run, «dfn'SRLI», in32BitMode, curArch, architecture, MCSR, archMs, archNs]
    rw [gpr_projection_eq d ms ns rs h]
    exact write_gpr_projection_eq d ms ns rd _ h
  | sll rd rs rt =>
    simp [Run, «dfn'SLL», in32BitMode, curArch, architecture, MCSR, archMs, archNs]
    rw [gpr_projection_eq d ms ns rs h, gpr_projection_eq d ms ns rt h]
    exact write_gpr_projection_eq d ms ns rd _ h
  | srl rd rs rt =>
    simp [Run, «dfn'SRL», in32BitMode, curArch, architecture, MCSR, archMs, archNs]
    rw [gpr_projection_eq d ms ns rs h, gpr_projection_eq d ms ns rt h]
    exact write_gpr_projection_eq d ms ns rd _ h
  | sub rd rs rt =>
    simp only [Run, «dfn'SUB»]
    rw [gpr_projection_eq d ms ns rs h, gpr_projection_eq d ms ns rt h]
    exact write_gpr_projection_eq d ms ns rd _ h

/-- Complete native step projection congruence, with PC advancement. -/
theorem ror_step_projection_eq (d : BitVec 64 → Prop) (i : instruction)
    (kind : RorInstruction i) (ms ns : riscv_state)
    (ok : riscvOk ms = true) (h : riscvProj d ms = riscvProj d ns) :
    riscvProj d (rorStep i ms) = riscvProj d (rorStep i ns) := by
  have okNs : riscvOk ns = true := (riscv_ok_of_projection_eq d ms ns h).symm.trans ok
  have fm := ror_run_frame i kind ms ok
  have fn := ror_run_frame i kind ns okNs
  have runH := ror_run_projection_eq d i kind ms ns ok h
  simp only [riscvProj, Prod.mk.injEq, fm.1, fn.1] at runH
  simp only [riscvProj, Prod.mk.injEq] at h
  simpa [riscvProj, rorStep, constStep, fm.1, fn.1, fm.2.1, fn.2.1,
    fm.2.2.1, fn.2.2.1, fm.2.2.2.1, fn.2.2.2.1,
    fm.2.2.2.2.1, fn.2.2.2.2.1, fm.2.2.2.2.2, fn.2.2.2.2.2,
    holUpdate] using
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, runH.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩


end Flapjack.RiscV.TargetProof
