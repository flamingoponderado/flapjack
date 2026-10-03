import Flapjack.RiscV.L3.Types

/-! Complete fixed-width immediate assembly used by original Decode.
These concatenate the encoded fields in literal source order; the encoded
sign bit stays a bit. No signed interpretation or offset shift occurs here. -/
namespace Flapjack.RiscV.L3

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asSImm12_def"]
def asSImm12 (arg0 : ((BitVec 7) × (BitVec 5))) : (BitVec 12) :=
  match arg0 with
  | (immhi, immlo) =>
  (BitVec.setWidth 12 (immhi ++ immlo))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asImm20_def"]
def asImm20 (arg0 : ((BitVec 1) × ((BitVec 8) × ((BitVec 1) × (BitVec 10))))) : (BitVec 20) :=
  match arg0 with
  | (imm20, (immhi, (imm11, immlo))) =>
  (BitVec.setWidth 20 (imm20 ++ ((BitVec.setWidth 19 (immhi ++ ((BitVec.setWidth 11 (imm11 ++ immlo))))))))

@[hol "HOL/examples/l3-machine-code/riscv/model/riscvScript.sml" "asImm12_def"]
def asImm12 (arg0 : ((BitVec 1) × ((BitVec 1) × ((BitVec 6) × (BitVec 4))))) : (BitVec 12) :=
  match arg0 with
  | (imm12, (imm11, (immhi, immlo))) =>
  (BitVec.setWidth 12 (imm12 ++ ((BitVec.setWidth 11 (imm11 ++ ((BitVec.setWidth 10 (immhi ++ immlo))))))))

end Flapjack.RiscV.L3
