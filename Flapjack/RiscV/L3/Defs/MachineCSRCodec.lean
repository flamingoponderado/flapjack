import Flapjack.RiscV.L3.Defs
namespace Flapjack.RiscV.L3

/-! Literal complete machine CSR codec section. Every fixed-width field and
reserved-bit segment retains original concatenation order. Boolean fields
use original word1 conversion; no record well-formedness premise is introduced.
Original probes and full transition review remain separate requirements. -/

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mip_def"]
def «reg'mip» (x : mip) : (BitVec 64) :=
  (match x with | ⟨HSIP, HTIP, MSIP, MTIP, SSIP, STIP, mip_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 56 55 0 mip_rst) ++ ((BitVec.setWidth 8 (((holV2w 1 ((MTIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((HTIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 1 56 56 mip_rst) ++ ((BitVec.setWidth 4 (((holV2w 1 ((MSIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((HSIP :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIP :: (([] : (List Bool))))))) ++ (holWordExtract 1 57 57 mip_rst)))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mcause_def"]
def «reg'mcause» (x : mcause) : (BitVec 64) :=
  (match x with | ⟨EC, Int, mcause_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((Int :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 (mcause_rst ++ EC))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mie_def"]
def «reg'mie» (x : mie) : (BitVec 64) :=
  (match x with | ⟨HSIE, HTIE, MSIE, MTIE, SSIE, STIE, mie_rst⟩ => (BitVec.setWidth 64 ((holWordExtract 56 55 0 mie_rst) ++ ((BitVec.setWidth 8 (((holV2w 1 ((MTIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 7 (((holV2w 1 ((HTIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (((holV2w 1 ((STIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 5 ((holWordExtract 1 56 56 mie_rst) ++ ((BitVec.setWidth 4 (((holV2w 1 ((MSIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (((holV2w 1 ((HSIE :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 2 (((holV2w 1 ((SSIE :: (([] : (List Bool))))))) ++ (holWordExtract 1 57 57 mie_rst)))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mtdeleg_def"]
def «reg'mtdeleg» (x : mtdeleg) : (BitVec 64) :=
  (match x with | ⟨Exc_deleg, Intr_deleg⟩ => (BitVec.setWidth 64 (Intr_deleg ++ Exc_deleg)))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mstatus_def"]
def «reg'mstatus» (x : mstatus) : (BitVec 64) :=
  (match x with | ⟨MFS, MIE, MIE1, MIE2, MIE3, MMPRV, MPRV, MPRV1, MPRV2, MPRV3, MSD, MXS, VM, mstatus_rst⟩ => (BitVec.setWidth 64 (((holV2w 1 ((MSD :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 63 (mstatus_rst ++ ((BitVec.setWidth 22 (VM ++ ((BitVec.setWidth 17 (((holV2w 1 ((MMPRV :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 16 (MXS ++ ((BitVec.setWidth 14 (MFS ++ ((BitVec.setWidth 12 (MPRV3 ++ ((BitVec.setWidth 10 (((holV2w 1 ((MIE3 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 9 (MPRV2 ++ ((BitVec.setWidth 7 (((holV2w 1 ((MIE2 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 6 (MPRV1 ++ ((BitVec.setWidth 4 (((holV2w 1 ((MIE1 :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 3 (MPRV ++ ((holV2w 1 ((MIE :: (([] : (List Bool))))))))))))))))))))))))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mimpid_def"]
def «reg'mimpid» (x : mimpid) : (BitVec 64) :=
  (match x with | ⟨RVImpl, RVSource⟩ => (BitVec.setWidth 64 (RVImpl ++ RVSource)))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "reg'mcpuid_def"]
def «reg'mcpuid» (x : mcpuid) : (BitVec 64) :=
  (match x with | ⟨ArchBase, I_, M, S_, U, mcpuid_rst⟩ => (BitVec.setWidth 64 (ArchBase ++ ((BitVec.setWidth 62 ((holWordExtract 41 40 0 mcpuid_rst) ++ ((BitVec.setWidth 21 (((holV2w 1 ((U :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 20 ((holWordExtract 1 41 41 mcpuid_rst) ++ ((BitVec.setWidth 19 (((holV2w 1 ((S_ :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 18 ((holWordExtract 5 46 42 mcpuid_rst) ++ ((BitVec.setWidth 13 (((holV2w 1 ((M :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 12 ((holWordExtract 3 49 47 mcpuid_rst) ++ ((BitVec.setWidth 9 (((holV2w 1 ((I_ :: (([] : (List Bool))))))) ++ (holWordExtract 8 57 50 mcpuid_rst))))))))))))))))))))))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mip_def"]
def «rec'mip» (x : (BitVec 64)) : mip :=
  (mip.mk (x.getLsbD 2) (x.getLsbD 6) (x.getLsbD 3) (x.getLsbD 7) (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 58 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 57 ((holWordExtract 1 4 4 x) ++ (holWordExtract 56 63 8 x))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mcause_def"]
def «rec'mcause» (x : (BitVec 64)) : mcause :=
  (mcause.mk (holWordExtract 4 3 0 x) (x.getLsbD 63) (holWordExtract 59 62 4 x))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mie_def"]
def «rec'mie» (x : (BitVec 64)) : mie :=
  (mie.mk (x.getLsbD 2) (x.getLsbD 6) (x.getLsbD 3) (x.getLsbD 7) (x.getLsbD 1) (x.getLsbD 5) ((BitVec.setWidth 58 ((holWordExtract 1 0 0 x) ++ ((BitVec.setWidth 57 ((holWordExtract 1 4 4 x) ++ (holWordExtract 56 63 8 x))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mtdeleg_def"]
def «rec'mtdeleg» (x : (BitVec 64)) : mtdeleg :=
  (mtdeleg.mk (holWordExtract 16 15 0 x) (holWordExtract 48 63 16 x))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mstatus_def"]
def «rec'mstatus» (x : (BitVec 64)) : mstatus :=
  (mstatus.mk (holWordExtract 2 13 12 x) (x.getLsbD 0) (x.getLsbD 3) (x.getLsbD 6) (x.getLsbD 9) (x.getLsbD 16) (holWordExtract 2 2 1 x) (holWordExtract 2 5 4 x) (holWordExtract 2 8 7 x) (holWordExtract 2 11 10 x) (x.getLsbD 63) (holWordExtract 2 15 14 x) (holWordExtract 5 21 17 x) (holWordExtract 41 62 22 x))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mcpuid_def"]
def «rec'mcpuid» (x : BitVec 64) : mcpuid :=
  { ArchBase := holWordExtract 2 63 62 x, I := x.getLsbD 8,
    M := x.getLsbD 12, S := x.getLsbD 18, U := x.getLsbD 20,
    «mcpuid'rst» := holWordExtract 8 7 0 x ++ holWordExtract 3 11 9 x ++
      holWordExtract 5 17 13 x ++ holWordExtract 1 19 19 x ++ holWordExtract 41 61 21 x }

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "rec'mimpid_def"]
def «rec'mimpid» (x : BitVec 64) : mimpid :=
  { RVImpl := holWordExtract 48 63 16 x, RVSource := holWordExtract 16 15 0 x }

end Flapjack.RiscV.L3
