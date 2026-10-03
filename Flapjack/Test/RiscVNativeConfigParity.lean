import Flapjack.Compiler.Encoders.RiscV.Target.State
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-! Whole original native config projections and all immediate-policy classes.
Finite policy fixtures are not universal cross-language equivalence; the encoder
projection is a full function equality, not a successful-run assumption. -/
-- Full generic target-state consumers, independent of any successful run.
example (s : Flapjack.RiscV.L3.riscv_state) :
    Flapjack.Compiler.Encoders.RiscV.Target.riscvNext s =
      Flapjack.holThe (Flapjack.RiscV.L3.Step.NextRISCV s) := rfl
example (d : BitVec 64 → Prop) (s : Flapjack.RiscV.L3.riscv_state)
    (a : BitVec 64) (b : BitVec 8) :
    (Flapjack.Compiler.Encoders.RiscV.Target.riscvProj d s).2.2.2.2.2.1 (a,b) ↔
      s.MEM8 a = b ∧ d a :=
  Flapjack.Compiler.Encoders.RiscV.Target.riscvProj_memory d s a b

namespace Flapjack.Test.RiscVNativeConfigParity
open Flapjack.Compiler.Encoders.RiscV.Target

example : riscvConfig.isa = .riscv := by decide
example : riscvConfig.regCount = 32 := by decide
example : riscvConfig.avoidRegs = [0,2,3,4,31] := by decide
example : riscvConfig.fpRegCount = 0 := by decide
example : riscvConfig.linkReg = some 1 := by decide
example : riscvConfig.twoRegArith = false := by decide
example : riscvConfig.bigEndian = false := by decide
example : riscvConfig.codeAlignment = 2 := by decide
example : riscvConfig.addrOffset = (-2048,2047) := by decide
example : riscvConfig.hwOffset = (-2048,2047) := by decide
example : riscvConfig.byteOffset = (-2048,2047) := by decide
example : riscvConfig.jumpOffset = (-2147483648,0x7FFFF7FF) := by decide
example : riscvConfig.cjumpOffset = (-1048576+8,1048575+4) := by decide
example : riscvConfig.locOffset = (-2147483648,0x7FFFF7FF) := by decide
example : riscvConfig.encode = riscvEnc := rfl
example : riscvConfig.encode (.inst .skip) = [19#8,0#8,0#8,0#8] := by decide

-- Oracle cfg_imm_Add_0
example : riscvConfig.validImm (.inl .add) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Add_1
example : riscvConfig.validImm (.inl .add) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Add_2
example : riscvConfig.validImm (.inl .add) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Add_3
example : riscvConfig.validImm (.inl .add) (0#64) = true := by decide
-- Oracle cfg_imm_Add_4
example : riscvConfig.validImm (.inl .add) (2047#64) = true := by decide
-- Oracle cfg_imm_Add_5
example : riscvConfig.validImm (.inl .add) (2048#64) = false := by decide
-- Oracle cfg_imm_Sub_0
example : riscvConfig.validImm (.inl .sub) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Sub_1
example : riscvConfig.validImm (.inl .sub) (18446744073709549568#64) = false := by decide
-- Oracle cfg_imm_Sub_2
example : riscvConfig.validImm (.inl .sub) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Sub_3
example : riscvConfig.validImm (.inl .sub) (0#64) = true := by decide
-- Oracle cfg_imm_Sub_4
example : riscvConfig.validImm (.inl .sub) (2047#64) = true := by decide
-- Oracle cfg_imm_Sub_5
example : riscvConfig.validImm (.inl .sub) (2048#64) = false := by decide
-- Oracle cfg_imm_And_0
example : riscvConfig.validImm (.inl .and) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_And_1
example : riscvConfig.validImm (.inl .and) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_And_2
example : riscvConfig.validImm (.inl .and) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_And_3
example : riscvConfig.validImm (.inl .and) (0#64) = true := by decide
-- Oracle cfg_imm_And_4
example : riscvConfig.validImm (.inl .and) (2047#64) = true := by decide
-- Oracle cfg_imm_And_5
example : riscvConfig.validImm (.inl .and) (2048#64) = false := by decide
-- Oracle cfg_imm_Or_0
example : riscvConfig.validImm (.inl .or) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Or_1
example : riscvConfig.validImm (.inl .or) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Or_2
example : riscvConfig.validImm (.inl .or) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Or_3
example : riscvConfig.validImm (.inl .or) (0#64) = true := by decide
-- Oracle cfg_imm_Or_4
example : riscvConfig.validImm (.inl .or) (2047#64) = true := by decide
-- Oracle cfg_imm_Or_5
example : riscvConfig.validImm (.inl .or) (2048#64) = false := by decide
-- Oracle cfg_imm_Xor_0
example : riscvConfig.validImm (.inl .xor) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Xor_1
example : riscvConfig.validImm (.inl .xor) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Xor_2
example : riscvConfig.validImm (.inl .xor) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Xor_3
example : riscvConfig.validImm (.inl .xor) (0#64) = true := by decide
-- Oracle cfg_imm_Xor_4
example : riscvConfig.validImm (.inl .xor) (2047#64) = true := by decide
-- Oracle cfg_imm_Xor_5
example : riscvConfig.validImm (.inl .xor) (2048#64) = false := by decide
-- Oracle cfg_imm_Equal_0
example : riscvConfig.validImm (.inr .equal) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Equal_1
example : riscvConfig.validImm (.inr .equal) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Equal_2
example : riscvConfig.validImm (.inr .equal) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Equal_3
example : riscvConfig.validImm (.inr .equal) (0#64) = true := by decide
-- Oracle cfg_imm_Equal_4
example : riscvConfig.validImm (.inr .equal) (2047#64) = true := by decide
-- Oracle cfg_imm_Equal_5
example : riscvConfig.validImm (.inr .equal) (2048#64) = false := by decide
-- Oracle cfg_imm_Less_0
example : riscvConfig.validImm (.inr .less) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Less_1
example : riscvConfig.validImm (.inr .less) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Less_2
example : riscvConfig.validImm (.inr .less) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Less_3
example : riscvConfig.validImm (.inr .less) (0#64) = true := by decide
-- Oracle cfg_imm_Less_4
example : riscvConfig.validImm (.inr .less) (2047#64) = true := by decide
-- Oracle cfg_imm_Less_5
example : riscvConfig.validImm (.inr .less) (2048#64) = false := by decide
-- Oracle cfg_imm_Lower_0
example : riscvConfig.validImm (.inr .lower) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Lower_1
example : riscvConfig.validImm (.inr .lower) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Lower_2
example : riscvConfig.validImm (.inr .lower) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Lower_3
example : riscvConfig.validImm (.inr .lower) (0#64) = true := by decide
-- Oracle cfg_imm_Lower_4
example : riscvConfig.validImm (.inr .lower) (2047#64) = true := by decide
-- Oracle cfg_imm_Lower_5
example : riscvConfig.validImm (.inr .lower) (2048#64) = false := by decide
-- Oracle cfg_imm_Test_0
example : riscvConfig.validImm (.inr .test) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_Test_1
example : riscvConfig.validImm (.inr .test) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_Test_2
example : riscvConfig.validImm (.inr .test) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_Test_3
example : riscvConfig.validImm (.inr .test) (0#64) = true := by decide
-- Oracle cfg_imm_Test_4
example : riscvConfig.validImm (.inr .test) (2047#64) = true := by decide
-- Oracle cfg_imm_Test_5
example : riscvConfig.validImm (.inr .test) (2048#64) = false := by decide
-- Oracle cfg_imm_NotEqual_0
example : riscvConfig.validImm (.inr .notEqual) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_NotEqual_1
example : riscvConfig.validImm (.inr .notEqual) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_NotEqual_2
example : riscvConfig.validImm (.inr .notEqual) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_NotEqual_3
example : riscvConfig.validImm (.inr .notEqual) (0#64) = true := by decide
-- Oracle cfg_imm_NotEqual_4
example : riscvConfig.validImm (.inr .notEqual) (2047#64) = true := by decide
-- Oracle cfg_imm_NotEqual_5
example : riscvConfig.validImm (.inr .notEqual) (2048#64) = false := by decide
-- Oracle cfg_imm_NotLess_0
example : riscvConfig.validImm (.inr .notLess) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_NotLess_1
example : riscvConfig.validImm (.inr .notLess) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_NotLess_2
example : riscvConfig.validImm (.inr .notLess) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_NotLess_3
example : riscvConfig.validImm (.inr .notLess) (0#64) = true := by decide
-- Oracle cfg_imm_NotLess_4
example : riscvConfig.validImm (.inr .notLess) (2047#64) = true := by decide
-- Oracle cfg_imm_NotLess_5
example : riscvConfig.validImm (.inr .notLess) (2048#64) = false := by decide
-- Oracle cfg_imm_NotLower_0
example : riscvConfig.validImm (.inr .notLower) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_NotLower_1
example : riscvConfig.validImm (.inr .notLower) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_NotLower_2
example : riscvConfig.validImm (.inr .notLower) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_NotLower_3
example : riscvConfig.validImm (.inr .notLower) (0#64) = true := by decide
-- Oracle cfg_imm_NotLower_4
example : riscvConfig.validImm (.inr .notLower) (2047#64) = true := by decide
-- Oracle cfg_imm_NotLower_5
example : riscvConfig.validImm (.inr .notLower) (2048#64) = false := by decide
-- Oracle cfg_imm_NotTest_0
example : riscvConfig.validImm (.inr .notTest) (18446744073709549567#64) = false := by decide
-- Oracle cfg_imm_NotTest_1
example : riscvConfig.validImm (.inr .notTest) (18446744073709549568#64) = true := by decide
-- Oracle cfg_imm_NotTest_2
example : riscvConfig.validImm (.inr .notTest) (18446744073709549569#64) = true := by decide
-- Oracle cfg_imm_NotTest_3
example : riscvConfig.validImm (.inr .notTest) (0#64) = true := by decide
-- Oracle cfg_imm_NotTest_4
example : riscvConfig.validImm (.inr .notTest) (2047#64) = true := by decide
-- Oracle cfg_imm_NotTest_5
example : riscvConfig.validImm (.inr .notTest) (2048#64) = false := by decide
end Flapjack.Test.RiscVNativeConfigParity
