import Flapjack.RiscV.CorrectnessEncoding.Jump.Native
import Flapjack.RiscV.CorrectnessEncoding.DecodeBranches
import Flapjack.RiscV.L3.Step.ConditionalBranchStep

/-! Full byte-driven native conditional branch transitions. These untagged
composition lemmas have no separately named HOL original: they combine the
reviewed native Encode/DecodeAny identities, literal primitive Run equations,
actual four-byte Fetch and NextRISCV. Every intrinsic word5 register and word12
logical halfword payload is retained, including zero, aliases and odd payloads.
Only initial riscvOk and the four actual emitted bytes are public premises.
Architecture selector2 supplies full64 operands; conditional branches do not
perform the JAL alignment check. Taken and fallthrough results preserve every
other native state field through Jump.branchPost. Full JumpCmp encoder
correctness is separate dependent work. Native Run retains the reviewed
reals_as_rational_cuts assurance limit recorded in SOUNDNESS section 8. -/

namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
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

theorem fallthrough_next (ms : riscv_state) (i : instruction) (w : BitVec 32)
    (ok : riscvOk ms = true) (decode : DecodeAny (.Word w) = i)
    (run : Run i {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip})
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 w)
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 w)
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 w)
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 w) :
    NextRISCV ms = some (Jump.branchPost ms (ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have hf := encoded_fetch ms w fields.1 low0 low1 b0 b1 b2 b3
  have hr : Run i fetched = fetched := run
  have hn := nextRISCV ms (.Word w) fetched i fetched
    ⟨hf,decode,hr,fields.2.2.2.1,fields.2.2.1⟩
  simpa [fetched,Jump.branchPost,update_pc,«write'PC»,Skip,holUpdate] using hn

theorem beq_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BEQ (rs1,rs2,imm))) ms =
      if GPR rs1 ms = GPR rs2 ms then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BEQ»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem beq_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BEQ (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BEQ (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BEQ (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BEQ (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if GPR rs1 ms = GPR rs2 ms then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BEQ (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BEQ (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := beq_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : GPR rs1 ms = GPR rs2 ms
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BEQ (rs1,rs2,imm))) _ _ ok
      (decode_encode_beq rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BEQ (rs1,rs2,imm))) _ ok
      (decode_encode_beq rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run


theorem bne_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BNE (rs1,rs2,imm))) ms =
      if GPR rs1 ms ≠ GPR rs2 ms then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BNE»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem bne_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BNE (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BNE (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BNE (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BNE (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if GPR rs1 ms ≠ GPR rs2 ms then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BNE (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BNE (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := bne_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : GPR rs1 ms ≠ GPR rs2 ms
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BNE (rs1,rs2,imm))) _ _ ok
      (decode_encode_bne rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BNE (rs1,rs2,imm))) _ ok
      (decode_encode_bne rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run


theorem blt_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BLT (rs1,rs2,imm))) ms =
      if (GPR rs1 ms).slt (GPR rs2 ms) = true then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BLT»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem blt_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BLT (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BLT (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BLT (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BLT (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if (GPR rs1 ms).slt (GPR rs2 ms) = true then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BLT (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BLT (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := blt_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : (GPR rs1 ms).slt (GPR rs2 ms) = true
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BLT (rs1,rs2,imm))) _ _ ok
      (decode_encode_blt rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BLT (rs1,rs2,imm))) _ ok
      (decode_encode_blt rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run


theorem bltu_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BLTU (rs1,rs2,imm))) ms =
      if (GPR rs1 ms).ult (GPR rs2 ms) = true then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BLTU»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem bltu_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BLTU (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BLTU (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BLTU (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BLTU (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if (GPR rs1 ms).ult (GPR rs2 ms) = true then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BLTU (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BLTU (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := bltu_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : (GPR rs1 ms).ult (GPR rs2 ms) = true
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BLTU (rs1,rs2,imm))) _ _ ok
      (decode_encode_bltu rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BLTU (rs1,rs2,imm))) _ ok
      (decode_encode_bltu rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run


theorem bge_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BGE (rs1,rs2,imm))) ms =
      if (GPR rs2 ms).sle (GPR rs1 ms) = true then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BGE»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem bge_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BGE (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BGE (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BGE (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BGE (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if (GPR rs2 ms).sle (GPR rs1 ms) = true then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BGE (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BGE (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := bge_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : (GPR rs2 ms).sle (GPR rs1 ms) = true
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BGE (rs1,rs2,imm))) _ _ ok
      (decode_encode_bge rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BGE (rs1,rs2,imm))) _ ok
      (decode_encode_bge rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run


theorem bgeu_run (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (arch : (ms.c_MCSR ms.procID).mcpuid.ArchBase = 2) :
    Run (.Branch (.BGEU (rs1,rs2,imm))) ms =
      if (GPR rs1 ms).ult (GPR rs2 ms) = false then
        {ms with c_NextFetch := (holUpdate ms.procID
          (some (.BranchTo (ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))))) ms.c_NextFetch)}
      else ms := by
  simp [Run,«dfn'BGEU»,in32BitMode,curArch,architecture,MCSR,arch,
    branchTo,«write'NextFetch»,PC,beq_iff_eq]

theorem bgeu_next (ms : riscv_state) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.BGEU (rs1,rs2,imm)))))
    (b1 : ms.MEM8 (ms.c_PC ms.procID+1) = RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.BGEU (rs1,rs2,imm)))))
    (b2 : ms.MEM8 (ms.c_PC ms.procID+2) = RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.BGEU (rs1,rs2,imm)))))
    (b3 : ms.MEM8 (ms.c_PC ms.procID+3) = RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.BGEU (rs1,rs2,imm))))) :
    NextRISCV ms = some (Jump.branchPost ms
      (if (GPR rs1 ms).ult (GPR rs2 ms) = false then ms.c_PC ms.procID+(imm.signExtend 64 <<< (1 : Nat))
       else ms.c_PC ms.procID+4)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have low : (Encode (.Branch (.BGEU (rs1,rs2,imm)))).getLsbD 0 = true ∧
      (Encode (.Branch (.BGEU (rs1,rs2,imm)))).getLsbD 1 = true := by
    simp only [Encode,SBtype,opc,BitVec.setWidth_eq,BitVec.getLsbD_append]
    simp
  have run := bgeu_run fetched rs1 rs2 imm fields.2.1
  have g1 : GPR rs1 fetched = GPR rs1 ms := rfl
  have g2 : GPR rs2 fetched = GPR rs2 ms := rfl
  rw [g1, g2] at run
  by_cases taken : (GPR rs1 ms).ult (GPR rs2 ms) = false
  · simp only [if_pos taken]
    apply Jump.branch_next ms (.Branch (.BGEU (rs1,rs2,imm))) _ _ ok
      (decode_encode_bgeu rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run
  · simp only [if_neg taken]
    apply fallthrough_next ms (.Branch (.BGEU (rs1,rs2,imm))) _ ok
      (decode_encode_bgeu rs1 rs2 imm) ?_ low.1 low.2 b0 b1 b2 b3
    simpa [fetched,taken] using run

end Flapjack.RiscV.TargetProof.JumpCmp
