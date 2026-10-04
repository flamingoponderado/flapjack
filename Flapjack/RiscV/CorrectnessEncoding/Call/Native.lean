import Flapjack.RiscV.CorrectnessEncoding.Jump.Native
import Flapjack.RiscV.CorrectnessEncoding.InstructionStep
import Flapjack.RiscV.L3.Step.JumpStep

/-! Literal native link-writing transitions used by full Call assembly.
Local infrastructure without separately named HOL originals. The instruction
source is read before the link write even when rd=rs1=1. Full source assembly
will discharge every byte/decode/run obligation; native Run inherits the
reviewed reals_as_rational_cuts assurance limit. -/
namespace Flapjack.RiscV.TargetProof.Call
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

/-- Literal far Call Run reads register1 before overwriting that same register
with the link. The mask and original PC+Skip link remain unchanged. -/
theorem far_call_run (ms : riscv_state) (imm : BitVec 12) :
    Run (.Branch (.JALR (1#5,1#5,imm))) ms =
      {ms with
        c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo ((GPR (1#5) ms + imm.signExtend 64) &&&
            BitVec.signExtend 64 (2#2)))) ms.c_NextFetch)
        c_gpr := (holUpdate ms.procID
          (holUpdate (1#5) (ms.c_PC ms.procID + ms.c_Skip ms.procID)
            (ms.c_gpr ms.procID)) ms.c_gpr)} := by
  simp [Run, «dfn'JALR», PC, Skip, «write'GPR», «write'gpr», branchTo, «write'NextFetch»]


def callPost (ms : riscv_state) (a : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_gpr := holUpdate ms.procID
      (holUpdate (1#5) (ms.c_PC ms.procID+4) (ms.c_gpr ms.procID)) ms.c_gpr
    c_PC := holUpdate ms.procID a ms.c_PC}

theorem call_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
    (a : BitVec 64) (ok : riscvOk ms = true)
    (decode : DecodeAny (.Word w) = i)
    (run : Run i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      {ms with
        c_Skip := holUpdate ms.procID 4 ms.c_Skip
        c_NextFetch := holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch
        c_gpr := holUpdate ms.procID
          (holUpdate (1#5) (ms.c_PC ms.procID+4) (ms.c_gpr ms.procID)) ms.c_gpr})
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 w) :
    NextRISCV ms = some (callPost ms a) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  let linked : riscv_state := {fetched with
    c_NextFetch := holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch
    c_gpr := holUpdate ms.procID
      (holUpdate (1#5) (ms.c_PC ms.procID+4) (ms.c_gpr ms.procID)) ms.c_gpr}
  have hf := encoded_fetch ms w fields.1 low0 low1 b0 b1 b2 b3
  have hr : Run i fetched = linked := run
  have hn := nextRISCV_branch ms (.Word w) fetched i linked a
    ⟨hf,decode,hr,fields.2.2.2.1,by simp [linked,fetched,holUpdate]⟩
  have clear : holUpdate ms.procID none
      (holUpdate ms.procID (some (.BranchTo a)) ms.c_NextFetch) = ms.c_NextFetch := by
    funext key
    by_cases he : ms.procID = key
    · subst key
      simpa [holUpdate] using fields.2.2.1.symm
    · simp [holUpdate,he]
  simpa [linked,fetched,callPost,update_pc,«write'PC»,«write'NextFetch»,holUpdate,clear] using hn

theorem near_call_run (ms : riscv_state) (imm : BitVec 20)
    (aligned : holAligned 2
      (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))) = true) :
    Run (.Branch (.JAL (1#5,imm))) ms =
      {ms with
        c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)
        c_gpr := (holUpdate ms.procID
          (holUpdate (1#5) (ms.c_PC ms.procID+ms.c_Skip ms.procID)
            (ms.c_gpr ms.procID)) ms.c_gpr)} := by
  have low : (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))).getLsbD 0 = false := by
    have he := of_decide_eq_true aligned
    rw [←he,holAlign_eq_shift]
    simp
  have lo : (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat)))[0] = false := by
    simpa using low
  simp [Run,«dfn'JAL»,PC,Skip,«write'GPR»,«write'gpr»,branchTo,«write'NextFetch»,lo]

theorem near_call_next (ms : riscv_state) (imm : BitVec 20)
    (ok : riscvOk ms = true)
    (aligned : holAligned 2 (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))) = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JAL (1#5,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JAL (1#5,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JAL (1#5,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JAL (1#5,imm))))) :
    NextRISCV ms = some (callPost ms (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat)))) := by
  have low : (Encode (.Branch (.JAL (1#5,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.JAL (1#5,imm)))).getLsbD 1 = true := by
    simp only [Encode,UJtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  apply call_next ms (.Branch (.JAL (1#5,imm))) _ _ ok
    (decode_encode_jal (1#5) imm) ?_ low.1 low.2 b0 b1 b2 b3
  simpa [holUpdate] using near_call_run
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} imm aligned

theorem far_call_next (ms : riscv_state) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JALR (1#5,1#5,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JALR (1#5,1#5,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JALR (1#5,1#5,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JALR (1#5,1#5,imm))))) :
    NextRISCV ms = some (callPost ms
      ((GPR (1#5) ms+imm.signExtend 64) &&& BitVec.signExtend 64 (2#2))) := by
  have low : (Encode (.Branch (.JALR (1#5,1#5,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.JALR (1#5,1#5,imm)))).getLsbD 1 = true := by
    simp only [Encode,Itype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  apply call_next ms (.Branch (.JALR (1#5,1#5,imm))) _ _ ok
    (decode_encode_jalr (1#5) (1#5) imm) ?_ low.1 low.2 b0 b1 b2 b3
  simpa [GPR,gpr,holUpdate] using far_call_run
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} imm

theorem call_post_rel (s : AsmState 64) (ms : riscv_state) (a : BitVec 64)
    (hr : targetStateRel riscvTarget s ms) (aligned : holAligned 2 a = true) :
    targetStateRel riscvTarget (updPc a (updReg 1 (s.pc+4) s)) (callPost ms a) := by
  have written := write_post_rel s ms 1 (s.pc+4) (by decide) hr
  have branched := Jump.branch_post_rel
    (updPc (s.pc+4) (updReg 1 (s.pc+4) s))
    (writePost ms (1#5) (s.pc+4)) a written aligned
  have pc := hr.2.1
  change ms.c_PC ms.procID = s.pc at pc
  have overwrite (f : BitVec 8 → BitVec 64) (x y : BitVec 64) :
      holUpdate ms.procID x (holUpdate ms.procID y f) = holUpdate ms.procID x f := by
    funext key
    by_cases he : ms.procID = key <;> simp [holUpdate,he]
  simpa [updPc,writePost,Jump.branchPost,callPost,overwrite,pc] using branched

end Flapjack.RiscV.TargetProof.Call
