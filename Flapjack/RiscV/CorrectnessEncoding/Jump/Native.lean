import Flapjack.RiscV.CorrectnessEncoding.Skip
import Flapjack.RiscV.CorrectnessEncoding.DecodeControl
import Flapjack.RiscV.L3.Step.JumpStep
import Flapjack.RiscV.CorrectnessEncoding.Immediate
import Flapjack.RiscV.CorrectnessEncoding.DecodeAddi
import Flapjack.RiscV.CorrectnessEncoding.DecodeUpperImmediates
import Flapjack.RiscV.L3.Defs.UpperJump

/-! Native execution infrastructure for the full original Jump case.
These local compositions have no separately named HOL originals and remain
untagged. branch_next composes the full native fetch/decode/run/PC update;
near_jump_next derives its decoder and Run premises from actual JAL and bytes.
The signed arithmetic-shift offset is reconstructed under the original near
range and alignment, with no target-execution assumption. The assembling Jump
theorem discharges these obligations from the original source step.
Native Run retains the reviewed reals_as_rational_cuts assurance limit. -/
namespace Flapjack.RiscV.TargetProof.Jump
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem byte0 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 7 0 w = BitVec.extractLsb' 0 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte1 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 15 8 w = BitVec.extractLsb' 8 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte2 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 23 16 w = BitVec.extractLsb' 16 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem byte3 (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w = BitVec.extractLsb' 24 8 w := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem reassemble (w : BitVec 32) :
    RiscV.L3.holWordExtract 8 31 24 w ++
      (RiscV.L3.holWordExtract 8 23 16 w ++
        (RiscV.L3.holWordExtract 8 15 8 w ++
          RiscV.L3.holWordExtract 8 7 0 w)) = w := by
  rw [byte0,byte1,byte2,byte3]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

private theorem encoded_fetch (ms : riscv_state) (w : BitVec 32)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    Fetch ms = (.Word w, {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}) := by
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _ at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _ at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _ at b3
  rw [fetch_bare ms vm]
  have lo0 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 0 = true := by
    simpa [byte0] using low0
  have lo1 : (RiscV.L3.holWordExtract 8 7 0 w).getLsbD 1 = true := by
    simpa [byte0] using low1
  simp [rawReadInst, boolify8, b0, b1, b2, b3, lo0, lo1, «write'Skip»]
  exact reassemble w

private theorem aligned_low (pc : BitVec 64) (h : holAligned 2 pc = true) :
    pc.getLsbD 0 = false := by
  have he := of_decide_eq_true h
  rw [← he, holAlign_eq_shift]
  simp

/-- Local no-link native execution infrastructure for the actual near Jump
instruction; source alignment will be discharged from asmStep in assembly. -/
theorem near_jump_run (ms : riscv_state) (imm : BitVec 20)
    (aligned : holAligned 2
      (ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat))) = true) :
    Run (.Branch (.JAL (0, imm))) ms =
      {ms with c_NextFetch := (holUpdate ms.procID
        (some (.BranchTo (ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat)))))
        ms.c_NextFetch)} := by
  have low := aligned_low _ aligned
  have lowElem : (ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat)))[0] = false := by
    simpa using low
  simp [Run, «dfn'JAL», PC, «write'GPR», branchTo, «write'NextFetch», lowElem]

def branchPost (ms : riscv_state) (a : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_PC := holUpdate ms.procID a ms.c_PC}

theorem branch_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
    (a : BitVec 64) (ok : riscvOk ms = true)
    (decode : DecodeAny (.Word w) = i)
    (run : Run i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      {ms with
        c_Skip := holUpdate ms.procID 4 ms.c_Skip
        c_NextFetch := holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch})
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 w) :
    NextRISCV ms = some (branchPost ms a) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  let jumped : riscv_state := {fetched with c_NextFetch :=
    (holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch)}
  have hf := encoded_fetch ms w fields.1 low0 low1 b0 b1 b2 b3
  have hr : Run i fetched = jumped := run
  have hn := nextRISCV_branch ms (.Word w) fetched i jumped a
    ⟨hf, decode, hr, fields.2.2.2.1, by simp [jumped, fetched, holUpdate]⟩
  have clear : holUpdate ms.procID none
      (holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch) = ms.c_NextFetch := by
    funext key
    by_cases he : ms.procID = key
    · subst key
      simpa [holUpdate] using fields.2.2.1.symm
    · simp [holUpdate, he]
  simpa [jumped, fetched, branchPost, update_pc, «write'PC», «write'NextFetch», holUpdate,
    clear] using hn

theorem near_jump_next (ms : riscv_state) (imm : BitVec 20)
    (ok : riscvOk ms = true)
    (aligned : holAligned 2
      (ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat))) = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JAL (0,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JAL (0,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JAL (0,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JAL (0,imm))))) :
    NextRISCV ms = some
      (branchPost ms (ms.c_PC ms.procID + (imm.signExtend 64 <<< (1 : Nat)))) := by
  have low : (Encode (.Branch (.JAL (0,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.JAL (0,imm)))).getLsbD 1 = true := by
    simp only [Encode, UJtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  apply branch_next ms (.Branch (.JAL (0,imm))) _ _ ok
    (decode_encode_jal 0 imm) ?_ low.1 low.2 b0 b1 b2 b3
  simpa using near_jump_run
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} imm aligned

private theorem near_jump_offset_logical (a : BitVec 64)
    (range : -1048576 ≤ a.toInt ∧ a.toInt ≤ 1048575)
    (aligned : a.toNat % 4 = 0) :
    ((a >>> (1 : Nat)).setWidth 20).signExtend 64 <<< (1 : Nat) = a := by
  apply BitVec.eq_of_toNat_eq
  have bound := a.isLt
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.msb_eq_decide, BitVec.toInt_eq_msb_cond,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq] at *
  repeat (any_goals first | split | split at range)
  all_goals omega

theorem near_jump_offset (a : BitVec 64)
    (range : -1048576 ≤ a.toInt ∧ a.toInt ≤ 1048575)
    (aligned : a.toNat % 4 = 0) :
    ((a.sshiftRight 1).setWidth 20).signExtend 64 <<< (1 : Nat) = a := by
  have bits : (a.sshiftRight 1).setWidth 20 = (a >>> (1 : Nat)).setWidth 20 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
      BitVec.getLsbD_ushiftRight]
    simp [hi, show ¬64 ≤ i by omega, show 1 + i < 64 by omega]
  rw [bits]
  exact near_jump_offset_logical a range aligned
/-- Literal native no-link JALR preserves the original masked target for every
source register and byte offset, including zero and aliased registers. -/
theorem far_jump_run (ms : riscv_state) (rs : BitVec 5) (imm : BitVec 12) :
    Run (.Branch (.JALR (0,rs,imm))) ms =
      {ms with c_NextFetch := (holUpdate ms.procID
        (some (.BranchTo ((GPR rs ms + imm.signExtend 64) &&&
          BitVec.signExtend 64 (2#2)))) ms.c_NextFetch)} := by
  simp [Run, «dfn'JALR», «write'GPR», branchTo, «write'NextFetch»]

/-- Actual JALR fetch/decode/run/PC transition from its four emitted bytes.
The masked target remains literal here; source assembly discharges its mask. -/
theorem far_jump_next (ms : riscv_state) (rs : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JALR (0,rs,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JALR (0,rs,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JALR (0,rs,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JALR (0,rs,imm))))) :
    NextRISCV ms = some (branchPost ms
      ((GPR rs ms + imm.signExtend 64) &&& BitVec.signExtend 64 (2#2))) := by
  have low : (Encode (.Branch (.JALR (0,rs,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.JALR (0,rs,imm)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  apply branch_next ms (.Branch (.JALR (0,rs,imm))) _ _ ok
    (decode_encode_jalr 0 rs imm) ?_ low.1 low.2 b0 b1 b2 b3
  simpa [GPR, gpr] using far_jump_run
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} rs imm

theorem aligned_add (pc c : BitVec 64) (hp : holAligned 2 pc = true)
    (hc : c.toNat % 4 = 0) : holAligned 2 (pc + c) = true := by
  have ep := congrArg BitVec.toNat (of_decide_eq_true hp)
  rw [holAlign_eq_div] at ep
  change decide (holAlign 2 (pc + c) = pc + c) = true
  apply decide_eq_true
  apply BitVec.eq_of_toNat_eq
  rw [holAlign_eq_div]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at *
  norm_num at *
  have bp := pc.isLt
  have bc := c.isLt
  omega

/-- Full native post-relation for a PC-only branch; this includes source
memory, all permitted registers and the original target validity conditions. -/
theorem branch_post_rel (s : AsmState 64) (ms : riscv_state) (a : BitVec 64)
    (hr : targetStateRel riscvTarget s ms) (ha : holAligned 2 a = true) :
    targetStateRel riscvTarget (updPc a s) (branchPost ms a) := by
  rcases hr with ⟨ok, pc, mem, regs, fp⟩
  have fields := (riscvOk_iff ms).mp ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (riscvOk_iff _).mpr
    simpa [branchPost, holUpdate] using
      ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, ha⟩
  · change (branchPost ms a).c_PC (branchPost ms a).procID = a
    simp [branchPost, holUpdate]
  · exact mem
  · exact regs
  · intro i hi
    change i < 0 at hi
    omega

end Flapjack.RiscV.TargetProof.Jump
