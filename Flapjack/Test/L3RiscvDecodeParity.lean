import Flapjack.RiscV.L3.Defs

/-! Kernel replay of `scripts/hol-probes/l3_riscv_decode_probe.out`: the L3 RISC-V model's
`Decode` on HOL's own `Encode` of each probed instruction, and on two words outside the
instruction encodings, against original-HOL evaluation. -/

namespace Flapjack.Test.L3RiscvDecodeParity
open Flapjack.RiscV.L3

-- enc0=0x310093w  dec0=ArithI (ADDI (1w,2w,3w))
example : Decode (BitVec.ofNat 32 0x310093) = (instruction.ArithI (ArithI.ADDI (1, 2, 3))) := by decide
-- enc1=0xFFF00F93w  dec1=ArithI (ADDI (31w,0w,4095w))
example : Decode (BitVec.ofNat 32 0xfff00f93) = (instruction.ArithI (ArithI.ADDI (31, 0, 4095))) := by decide
-- enc2=0x8003029Bw  dec2=ArithI (ADDIW (5w,6w,2048w))
example : Decode (BitVec.ofNat 32 0x8003029b) = (instruction.ArithI (ArithI.ADDIW (5, 6, 2048))) := by decide
-- enc3=0x7FF47393w  dec3=ArithI (ANDI (7w,8w,2047w))
example : Decode (BitVec.ofNat 32 0x7ff47393) = (instruction.ArithI (ArithI.ANDI (7, 8, 2047))) := by decide
-- enc4=0x156493w  dec4=ArithI (ORI (9w,10w,1w))
example : Decode (BitVec.ofNat 32 0x156493) = (instruction.ArithI (ArithI.ORI (9, 10, 1))) := by decide
-- enc5=0xABC64593w  dec5=ArithI (XORI (11w,12w,2748w))
example : Decode (BitVec.ofNat 32 0xabc64593) = (instruction.ArithI (ArithI.XORI (11, 12, 2748))) := by decide
-- enc6=0x572693w  dec6=ArithI (SLTI (13w,14w,5w))
example : Decode (BitVec.ofNat 32 0x572693) = (instruction.ArithI (ArithI.SLTI (13, 14, 5))) := by decide
-- enc7=0x683793w  dec7=ArithI (SLTIU (15w,16w,6w))
example : Decode (BitVec.ofNat 32 0x683793) = (instruction.ArithI (ArithI.SLTIU (15, 16, 6))) := by decide
-- enc8=0xFFFFF8B7w  dec8=ArithI (LUI (17w,0xFFFFFw))
example : Decode (BitVec.ofNat 32 0xfffff8b7) = (instruction.ArithI (ArithI.LUI (17, 1048575))) := by decide
-- enc9=0x12345917w  dec9=ArithI (AUIPC (18w,0x12345w))
example : Decode (BitVec.ofNat 32 0x12345917) = (instruction.ArithI (ArithI.AUIPC (18, 74565))) := by decide
-- enc10=0x3100B3w  dec10=ArithR (ADD (1w,2w,3w))
example : Decode (BitVec.ofNat 32 0x3100b3) = (instruction.ArithR (ArithR.ADD (1, 2, 3))) := by decide
-- enc11=0x40628233w  dec11=ArithR (SUB (4w,5w,6w))
example : Decode (BitVec.ofNat 32 0x40628233) = (instruction.ArithR (ArithR.SUB (4, 5, 6))) := by decide
-- enc12=0x9473B3w  dec12=ArithR (AND (7w,8w,9w))
example : Decode (BitVec.ofNat 32 0x9473b3) = (instruction.ArithR (ArithR.AND (7, 8, 9))) := by decide
-- enc13=0xC5E533w  dec13=ArithR (OR (10w,11w,12w))
example : Decode (BitVec.ofNat 32 0xc5e533) = (instruction.ArithR (ArithR.OR (10, 11, 12))) := by decide
-- enc14=0xF746B3w  dec14=ArithR (XOR (13w,14w,15w))
example : Decode (BitVec.ofNat 32 0xf746b3) = (instruction.ArithR (ArithR.XOR (13, 14, 15))) := by decide
-- enc15=0x128A833w  dec15=ArithR (SLT (16w,17w,18w))
example : Decode (BitVec.ofNat 32 0x128a833) = (instruction.ArithR (ArithR.SLT (16, 17, 18))) := by decide
-- enc16=0x15A39B3w  dec16=ArithR (SLTU (19w,20w,21w))
example : Decode (BitVec.ofNat 32 0x15a39b3) = (instruction.ArithR (ArithR.SLTU (19, 20, 21))) := by decide
-- enc17=0x18B8B3Bw  dec17=ArithR (ADDW (22w,23w,24w))
example : Decode (BitVec.ofNat 32 0x18b8b3b) = (instruction.ArithR (ArithR.ADDW (22, 23, 24))) := by decide
-- enc18=0x41BD0CBBw  dec18=ArithR (SUBW (25w,26w,27w))
example : Decode (BitVec.ofNat 32 0x41bd0cbb) = (instruction.ArithR (ArithR.SUBW (25, 26, 27))) := by decide
-- enc19=0x3110B3w  dec19=Shift (SLL (1w,2w,3w))
example : Decode (BitVec.ofNat 32 0x3110b3) = (instruction.Shift (Shift.SLL (1, 2, 3))) := by decide
-- enc20=0x62D233w  dec20=Shift (SRL (4w,5w,6w))
example : Decode (BitVec.ofNat 32 0x62d233) = (instruction.Shift (Shift.SRL (4, 5, 6))) := by decide
-- enc21=0x409453B3w  dec21=Shift (SRA (7w,8w,9w))
example : Decode (BitVec.ofNat 32 0x409453b3) = (instruction.Shift (Shift.SRA (7, 8, 9))) := by decide
-- enc22=0x3F59513w  dec22=Shift (SLLI (10w,11w,63w))
example : Decode (BitVec.ofNat 32 0x3f59513) = (instruction.Shift (Shift.SLLI (10, 11, 63))) := by decide
-- enc23=0x16D613w  dec23=Shift (SRLI (12w,13w,1w))
example : Decode (BitVec.ofNat 32 0x16d613) = (instruction.Shift (Shift.SRLI (12, 13, 1))) := by decide
-- enc24=0x4207D713w  dec24=Shift (SRAI (14w,15w,32w))
example : Decode (BitVec.ofNat 32 0x4207d713) = (instruction.Shift (Shift.SRAI (14, 15, 32))) := by decide
-- enc25=0x1F8981Bw  dec25=Shift (SLLIW (16w,17w,31w))
example : Decode (BitVec.ofNat 32 0x1f8981b) = (instruction.Shift (Shift.SLLIW (16, 17, 31))) := by decide
-- enc26=0x4149D93Bw  dec26=Shift (SRAW (18w,19w,20w))
example : Decode (BitVec.ofNat 32 0x4149d93b) = (instruction.Shift (Shift.SRAW (18, 19, 20))) := by decide
-- enc27=0x802000EFw  dec27=Branch (JAL (1w,0x80001w))
example : Decode (BitVec.ofNat 32 0x802000ef) = (instruction.Branch (Branch.JAL (1, 524289))) := by decide
-- enc28=0xFF018167w  dec28=Branch (JALR (2w,3w,4080w))
example : Decode (BitVec.ofNat 32 0xff018167) = (instruction.Branch (Branch.JALR (2, 3, 4080))) := by decide
-- enc29=0x80520063w  dec29=Branch (BEQ (4w,5w,2048w))
example : Decode (BitVec.ofNat 32 0x80520063) = (instruction.Branch (Branch.BEQ (4, 5, 2048))) := by decide
-- enc30=0x731463w  dec30=Branch (BNE (6w,7w,4w))
example : Decode (BitVec.ofNat 32 0x731463) = (instruction.Branch (Branch.BNE (6, 7, 4))) := by decide
-- enc31=0xFE944EE3w  dec31=Branch (BLT (8w,9w,4094w))
example : Decode (BitVec.ofNat 32 0xfe944ee3) = (instruction.Branch (Branch.BLT (8, 9, 4094))) := by decide
-- enc32=0xB55863w  dec32=Branch (BGE (10w,11w,8w))
example : Decode (BitVec.ofNat 32 0xb55863) = (instruction.Branch (Branch.BGE (10, 11, 8))) := by decide
-- enc33=0xD66C63w  dec33=Branch (BLTU (12w,13w,12w))
example : Decode (BitVec.ofNat 32 0xd66c63) = (instruction.Branch (Branch.BLTU (12, 13, 12))) := by decide
-- enc34=0x2F77063w  dec34=Branch (BGEU (14w,15w,16w))
example : Decode (BitVec.ofNat 32 0x2f77063) = (instruction.Branch (Branch.BGEU (14, 15, 16))) := by decide
-- enc35=0x813083w  dec35=Load (LD (1w,2w,8w))
example : Decode (BitVec.ofNat 32 0x813083) = (instruction.Load (Load.LD (1, 2, 8))) := by decide
-- enc36=0xFFC22183w  dec36=Load (LW (3w,4w,4092w))
example : Decode (BitVec.ofNat 32 0xffc22183) = (instruction.Load (Load.LW (3, 4, 4092))) := by decide
-- enc37=0x436283w  dec37=Load (LWU (5w,6w,4w))
example : Decode (BitVec.ofNat 32 0x436283) = (instruction.Load (Load.LWU (5, 6, 4))) := by decide
-- enc38=0x241383w  dec38=Load (LH (7w,8w,2w))
example : Decode (BitVec.ofNat 32 0x241383) = (instruction.Load (Load.LH (7, 8, 2))) := by decide
-- enc39=0x655483w  dec39=Load (LHU (9w,10w,6w))
example : Decode (BitVec.ofNat 32 0x655483) = (instruction.Load (Load.LHU (9, 10, 6))) := by decide
-- enc40=0x160583w  dec40=Load (LB (11w,12w,1w))
example : Decode (BitVec.ofNat 32 0x160583) = (instruction.Load (Load.LB (11, 12, 1))) := by decide
-- enc41=0x7FF74683w  dec41=Load (LBU (13w,14w,2047w))
example : Decode (BitVec.ofNat 32 0x7ff74683) = (instruction.Load (Load.LBU (13, 14, 2047))) := by decide
-- enc42=0x20B823w  dec42=Store (SD (1w,2w,16w))
example : Decode (BitVec.ofNat 32 0x20b823) = (instruction.Store (Store.SD (1, 2, 16))) := by decide
-- enc43=0x8041A023w  dec43=Store (SW (3w,4w,2048w))
example : Decode (BitVec.ofNat 32 0x8041a023) = (instruction.Store (Store.SW (3, 4, 2048))) := by decide
-- enc44=0x629123w  dec44=Store (SH (5w,6w,2w))
example : Decode (BitVec.ofNat 32 0x629123) = (instruction.Store (Store.SH (5, 6, 2))) := by decide
-- enc45=0x8380A3w  dec45=Store (SB (7w,8w,1w))
example : Decode (BitVec.ofNat 32 0x8380a3) = (instruction.Store (Store.SB (7, 8, 1))) := by decide
-- enc46=0x23100B3w  dec46=MulDiv (MUL (1w,2w,3w))
example : Decode (BitVec.ofNat 32 0x23100b3) = (instruction.MulDiv (MulDiv.MUL (1, 2, 3))) := by decide
-- enc47=0x2629233w  dec47=MulDiv (MULH (4w,5w,6w))
example : Decode (BitVec.ofNat 32 0x2629233) = (instruction.MulDiv (MulDiv.MULH (4, 5, 6))) := by decide
-- enc48=0x29433B3w  dec48=MulDiv (MULHU (7w,8w,9w))
example : Decode (BitVec.ofNat 32 0x29433b3) = (instruction.MulDiv (MulDiv.MULHU (7, 8, 9))) := by decide
-- enc49=0x2C5C533w  dec49=MulDiv ($DIV (10w,11w,12w))
example : Decode (BitVec.ofNat 32 0x2c5c533) = (instruction.MulDiv (MulDiv.DIV (10, 11, 12))) := by decide
-- enc50=0x2F756B3w  dec50=MulDiv (DIVU (13w,14w,15w))
example : Decode (BitVec.ofNat 32 0x2f756b3) = (instruction.MulDiv (MulDiv.DIVU (13, 14, 15))) := by decide
-- enc51=0x328E833w  dec51=MulDiv (REM (16w,17w,18w))
example : Decode (BitVec.ofNat 32 0x328e833) = (instruction.MulDiv (MulDiv.REM (16, 17, 18))) := by decide
-- enc52=0x35A79B3w  dec52=MulDiv (REMU (19w,20w,21w))
example : Decode (BitVec.ofNat 32 0x35a79b3) = (instruction.MulDiv (MulDiv.REMU (19, 20, 21))) := by decide
-- enc53=0x38B8B3Bw  dec53=MulDiv (MULW (22w,23w,24w))
example : Decode (BitVec.ofNat 32 0x38b8b3b) = (instruction.MulDiv (MulDiv.MULW (22, 23, 24))) := by decide
-- enc54=0x813087w  dec54=FPLoad (FLD (1w,2w,8w))
example : Decode (BitVec.ofNat 32 0x813087) = (instruction.FPLoad (FPLoad.FLD (1, 2, 8))) := by decide
-- enc55=0x41B827w  dec55=FPStore (FSD (3w,4w,16w))
example : Decode (BitVec.ofNat 32 0x41b827) = (instruction.FPStore (FPStore.FSD (3, 4, 16))) := by decide
-- enc56=0x23100D3w  dec56=FArith (FADD_D (1w,2w,3w,0w))
example : Decode (BitVec.ofNat 32 0x23100d3) = (instruction.FArith (FArith.FADD_D (1, 2, 3, 0))) := by decide
-- enc57=0x5A02F253w  dec57=FArith (FSQRT_D (4w,5w,7w))
example : Decode (BitVec.ofNat 32 0x5a02f253) = (instruction.FArith (FArith.FSQRT_D (4, 5, 7))) := by decide
-- enc58=0xE2038353w  dec58=FConv (FMV_X_D (6w,7w))
example : Decode (BitVec.ofNat 32 0xe2038353) = (instruction.FConv (FConv.FMV_X_D (6, 7))) := by decide
-- enc59=0xF2048453w  dec59=FConv (FMV_D_X (8w,9w))
example : Decode (BitVec.ofNat 32 0xf2048453) = (instruction.FConv (FConv.FMV_D_X (8, 9))) := by decide
-- enc60=115w  dec60=System ECALL
example : Decode (BitVec.ofNat 32 0x73) = (instruction.System System.ECALL) := by decide
-- enc61=0x100073w  dec61=System EBREAK
example : Decode (BitVec.ofNat 32 0x100073) = (instruction.System System.EBREAK) := by decide
-- dec_zero=UnknownInstruction
example : Decode (BitVec.ofNat 32 0x0) = instruction.UnknownInstruction := by decide
-- dec_ones=UnknownInstruction
example : Decode (BitVec.ofNat 32 0xffffffff) = instruction.UnknownInstruction := by decide

end Flapjack.Test.L3RiscvDecodeParity
