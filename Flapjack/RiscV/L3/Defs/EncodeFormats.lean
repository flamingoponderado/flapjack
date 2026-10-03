import Flapjack.RiscV.L3.Support

/-! Complete fixed-width original instruction encoding formats. All argument
positions, slices and concatenations are retained from the pinned HOL definitions. -/
namespace Flapjack.RiscV.L3

/-- HOL `riscv$opc` (`opc_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "opc_def"]
def opc (code : (BitVec 8)) : (BitVec 7) :=
  (BitVec.setWidth 7 ((holWordExtract 5 4 0 code) ++ (BitVec.ofNat 2 3)))

/-- HOL `riscv$Itype` (`Itype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Itype_def"]
def Itype (arg0 : ((BitVec 7) × ((BitVec 3) × ((BitVec 5) × ((BitVec 5) × (BitVec 12)))))) : (BitVec 32) :=
  match arg0 with
  | (o, (f3, (rd, (rs1, imm)))) =>
  (BitVec.setWidth 32 (imm ++ ((BitVec.setWidth 20 (rs1 ++ ((BitVec.setWidth 15 (f3 ++ ((BitVec.setWidth 12 (rd ++ o)))))))))))

/-- HOL `riscv$Stype` (`Stype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Stype_def"]
def Stype (arg0 : ((BitVec 7) × ((BitVec 3) × ((BitVec 5) × ((BitVec 5) × (BitVec 12)))))) : (BitVec 32) :=
  match arg0 with
  | (o, (f3, (rs1, (rs2, imm)))) =>
  (BitVec.setWidth 32 ((holWordExtract 7 11 5 imm) ++ ((BitVec.setWidth 25 (rs2 ++ ((BitVec.setWidth 20 (rs1 ++ ((BitVec.setWidth 15 (f3 ++ ((BitVec.setWidth 12 ((holWordExtract 5 4 0 imm) ++ o))))))))))))))

/-- HOL `riscv$Rtype` (`Rtype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Rtype_def"]
def Rtype (arg0 : ((BitVec 7) × ((BitVec 3) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 7))))))) : (BitVec 32) :=
  match arg0 with
  | (o, (f3, (rd, (rs1, (rs2, f7))))) =>
  (BitVec.setWidth 32 (f7 ++ ((BitVec.setWidth 25 (rs2 ++ ((BitVec.setWidth 20 (rs1 ++ ((BitVec.setWidth 15 (f3 ++ ((BitVec.setWidth 12 (rd ++ o))))))))))))))

/-- HOL `riscv$R4type` (`R4type_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "R4type_def"]
def R4type (arg0 : ((BitVec 7) × ((BitVec 3) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × ((BitVec 5) × (BitVec 2)))))))) : (BitVec 32) :=
  match arg0 with
  | (o, (f3, (rd, (rs1, (rs2, (rs3, f2)))))) =>
  (BitVec.setWidth 32 (rs3 ++ ((BitVec.setWidth 27 (f2 ++ ((BitVec.setWidth 25 (rs2 ++ ((BitVec.setWidth 20 (rs1 ++ ((BitVec.setWidth 15 (f3 ++ ((BitVec.setWidth 12 (rd ++ o)))))))))))))))))

/-- HOL `riscv$UJtype` (`UJtype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "UJtype_def"]
def UJtype (arg0 : ((BitVec 7) × ((BitVec 5) × (BitVec 20)))) : (BitVec 32) :=
  match arg0 with
  | (o, (rd, imm)) =>
  (BitVec.setWidth 32 (((holV2w 1 (((imm.getLsbD 19) :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 31 ((holWordExtract 10 9 0 imm) ++ ((BitVec.setWidth 21 (((holV2w 1 (((imm.getLsbD 10) :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 20 ((holWordExtract 8 18 11 imm) ++ ((BitVec.setWidth 12 (rd ++ o))))))))))))))

/-- HOL `riscv$SBtype` (`SBtype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "SBtype_def"]
def SBtype (arg0 : ((BitVec 7) × ((BitVec 3) × ((BitVec 5) × ((BitVec 5) × (BitVec 12)))))) : (BitVec 32) :=
  match arg0 with
  | (o, (f3, (rs1, (rs2, imm)))) =>
  (BitVec.setWidth 32 (((holV2w 1 (((imm.getLsbD 11) :: (([] : (List Bool))))))) ++ ((BitVec.setWidth 31 ((holWordExtract 6 9 4 imm) ++ ((BitVec.setWidth 25 (rs2 ++ ((BitVec.setWidth 20 (rs1 ++ ((BitVec.setWidth 15 (f3 ++ ((BitVec.setWidth 12 ((holWordExtract 4 3 0 imm) ++ ((BitVec.setWidth 8 (((holV2w 1 (((imm.getLsbD 10) :: (([] : (List Bool))))))) ++ o))))))))))))))))))))

/-- HOL `riscv$Utype` (`Utype_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "Utype_def"]
def Utype (arg0 : ((BitVec 7) × ((BitVec 5) × (BitVec 20)))) : (BitVec 32) :=
  match arg0 with
  | (o, (rd, imm)) =>
  (BitVec.setWidth 32 (imm ++ ((BitVec.setWidth 12 (rd ++ o)))))

/-- HOL `riscv$amofunc` (`amofunc_def`), mechanically rendered from the elaborated HOL definition. -/
@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "amofunc_def"]
def amofunc (arg0 : ((BitVec 5) × ((BitVec 1) × (BitVec 1)))) : (BitVec 7) :=
  match arg0 with
  | (code, (aq, rl)) =>
  (BitVec.setWidth 7 (code ++ ((BitVec.setWidth 2 (aq ++ rl)))))

end Flapjack.RiscV.L3
