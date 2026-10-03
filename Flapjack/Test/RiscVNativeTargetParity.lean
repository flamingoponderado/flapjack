import Flapjack.Compiler.Encoders.RiscV.Target

/-! Original complete native target AST lists and byte lists. Finite regression
evidence, not universal HOL-to-Lean equivalence. -/
namespace Flapjack.Test.RiscVNativeTargetParity
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3

-- Oracle Target_Skip_0: complete original AST and byte result.
example : riscvAst (.inst .skip) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst .skip) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Const_1: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (0#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 0 (0#64))) = [19#8, 96#8, 0#8, 0#8] := by decide

-- Oracle Target_Const_2: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (2047#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 0 (2047#64))) = [19#8, 96#8, 240#8, 127#8] := by decide

-- Oracle Target_Const_3: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (2048#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 0 (2048#64))) = [55#8, 240#8, 255#8, 255#8, 19#8, 64#8, 0#8, 128#8] := by decide

-- Oracle Target_Const_4: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (18446744073709549568#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 0 (18446744073709549568#64))) = [19#8, 96#8, 0#8, 128#8] := by decide

-- Oracle Target_Const_5: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (18446744073709549567#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 0 (18446744073709549567#64))) = [55#8, 240#8, 255#8, 255#8, 19#8, 0#8, 240#8, 127#8] := by decide

-- Oracle Target_Const_6: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (18446744073709551615#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 0 (18446744073709551615#64))) = [19#8, 96#8, 240#8, 255#8] := by decide

-- Oracle Target_Const_7: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (2147483647#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 0 (2147483647#64))) = [55#8, 0#8, 0#8, 128#8, 19#8, 64#8, 240#8, 255#8] := by decide

-- Oracle Target_Const_8: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (2147483648#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (2147483648#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 143#8, 15#8, 0#8, 55#8, 0#8, 0#8, 0#8, 19#8, 64#8, 240#8, 255#8, 19#8, 16#8, 0#8, 2#8, 51#8, 64#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_9: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (4294967295#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (4294967295#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 207#8, 255#8, 255#8, 55#8, 0#8, 0#8, 0#8, 19#8, 64#8, 240#8, 255#8, 19#8, 16#8, 0#8, 2#8, 51#8, 64#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_10: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (4294967296#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 1))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (4294967296#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 143#8, 15#8, 0#8, 55#8, 0#8, 0#8, 0#8, 19#8, 0#8, 16#8, 0#8, 19#8, 16#8, 0#8, 2#8, 51#8, 96#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_11: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (1311768467015204863#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 74565))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 1656))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (1311768467015204863#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 207#8, 255#8, 255#8, 55#8, 80#8, 52#8, 18#8, 19#8, 0#8, 128#8, 103#8, 19#8, 16#8, 0#8, 2#8, 51#8, 96#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_12: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (1311768467015204864#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 74565))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2439))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (1311768467015204864#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 143#8, 15#8, 0#8, 55#8, 80#8, 52#8, 18#8, 19#8, 64#8, 112#8, 152#8, 19#8, 16#8, 0#8, 2#8, 51#8, 64#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_13: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (9223372036854775808#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (9223372036854775808#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 143#8, 15#8, 0#8, 55#8, 0#8, 0#8, 128#8, 19#8, 0#8, 0#8, 0#8, 19#8, 16#8, 0#8, 2#8, 51#8, 96#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_14: complete original AST and byte result.
example : riscvAst (.inst (.const 0 (9223372036854775807#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 0), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 0 (9223372036854775807#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 207#8, 255#8, 255#8, 55#8, 0#8, 0#8, 128#8, 19#8, 0#8, 0#8, 0#8, 19#8, 16#8, 0#8, 2#8, 51#8, 64#8, 240#8, 1#8] := by decide

-- Oracle Target_Const_15: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (0#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 37 (0#64))) = [147#8, 98#8, 0#8, 0#8] := by decide

-- Oracle Target_Const_16: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (2047#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 37 (2047#64))) = [147#8, 98#8, 240#8, 127#8] := by decide

-- Oracle Target_Const_17: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (2048#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 37 (2048#64))) = [183#8, 242#8, 255#8, 255#8, 147#8, 194#8, 2#8, 128#8] := by decide

-- Oracle Target_Const_18: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (18446744073709549568#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 37 (18446744073709549568#64))) = [147#8, 98#8, 0#8, 128#8] := by decide

-- Oracle Target_Const_19: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (18446744073709549567#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 37 (18446744073709549567#64))) = [183#8, 242#8, 255#8, 255#8, 147#8, 130#8, 242#8, 127#8] := by decide

-- Oracle Target_Const_20: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (18446744073709551615#64))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.const 37 (18446744073709551615#64))) = [147#8, 98#8, 240#8, 255#8] := by decide

-- Oracle Target_Const_21: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (2147483647#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.const 37 (2147483647#64))) = [183#8, 2#8, 0#8, 128#8, 147#8, 194#8, 242#8, 255#8] := by decide

-- Oracle Target_Const_22: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (2147483648#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (2147483648#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 143#8, 15#8, 0#8, 183#8, 2#8, 0#8, 0#8, 147#8, 194#8, 242#8, 255#8, 147#8, 146#8, 2#8, 2#8, 179#8, 194#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_23: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (4294967295#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (4294967295#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 207#8, 255#8, 255#8, 183#8, 2#8, 0#8, 0#8, 147#8, 194#8, 242#8, 255#8, 147#8, 146#8, 2#8, 2#8, 179#8, 194#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_24: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (4294967296#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 1))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (4294967296#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 143#8, 15#8, 0#8, 183#8, 2#8, 0#8, 0#8, 147#8, 130#8, 18#8, 0#8, 147#8, 146#8, 2#8, 2#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_25: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (1311768467015204863#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 74565))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 1656))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (1311768467015204863#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 207#8, 255#8, 255#8, 183#8, 82#8, 52#8, 18#8, 147#8, 130#8, 130#8, 103#8, 147#8, 146#8, 2#8, 2#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_26: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (1311768467015204864#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 74565))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2439))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (1311768467015204864#64))) = [183#8, 15#8, 0#8, 128#8, 147#8, 143#8, 15#8, 0#8, 183#8, 82#8, 52#8, 18#8, 147#8, 194#8, 114#8, 152#8, 147#8, 146#8, 2#8, 2#8, 179#8, 194#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_27: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (9223372036854775808#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (9223372036854775808#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 143#8, 15#8, 0#8, 183#8, 2#8, 0#8, 128#8, 147#8, 130#8, 2#8, 0#8, 147#8, 146#8, 2#8, 2#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_Const_28: complete original AST and byte result.
example : riscvAst (.inst (.const 37 (9223372036854775807#64))) = (((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithI ((ArithI.LUI (((BitVec.ofNat 5 37), (BitVec.ofNat 20 524288))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 6 32))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.const 37 (9223372036854775807#64))) = [183#8, 15#8, 0#8, 0#8, 147#8, 207#8, 255#8, 255#8, 183#8, 2#8, 0#8, 128#8, 147#8, 130#8, 2#8, 0#8, 147#8, 146#8, 2#8, 2#8, 179#8, 194#8, 242#8, 1#8] := by decide

-- Oracle Target_BinopReg_29: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .add 37 34 (.reg 35)))) = (((instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .add 37 34 (.reg 35)))) = [179#8, 2#8, 49#8, 0#8] := by decide

-- Oracle Target_BinopImm_30: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .add 37 34 (.imm (0#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .add 37 34 (.imm (0#64))))) = [147#8, 2#8, 1#8, 0#8] := by decide

-- Oracle Target_BinopImm_31: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .add 37 34 (.imm (2048#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .add 37 34 (.imm (2048#64))))) = [147#8, 2#8, 1#8, 128#8] := by decide

-- Oracle Target_BinopImm_32: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .add 37 34 (.imm (18446744073709551615#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .add 37 34 (.imm (18446744073709551615#64))))) = [147#8, 2#8, 241#8, 255#8] := by decide

-- Oracle Target_BinopReg_33: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .sub 37 34 (.reg 35)))) = (((instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .sub 37 34 (.reg 35)))) = [179#8, 2#8, 49#8, 64#8] := by decide

-- Oracle Target_BinopImm_34: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .sub 37 34 (.imm (0#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .sub 37 34 (.imm (0#64))))) = [147#8, 2#8, 1#8, 0#8] := by decide

-- Oracle Target_BinopImm_35: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .sub 37 34 (.imm (2048#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .sub 37 34 (.imm (2048#64))))) = [147#8, 2#8, 1#8, 128#8] := by decide

-- Oracle Target_BinopImm_36: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .sub 37 34 (.imm (18446744073709551615#64))))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 1))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .sub 37 34 (.imm (18446744073709551615#64))))) = [147#8, 2#8, 17#8, 0#8] := by decide

-- Oracle Target_BinopReg_37: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .and 37 34 (.reg 35)))) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .and 37 34 (.reg 35)))) = [179#8, 114#8, 49#8, 0#8] := by decide

-- Oracle Target_BinopImm_38: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .and 37 34 (.imm (0#64))))) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .and 37 34 (.imm (0#64))))) = [147#8, 114#8, 1#8, 0#8] := by decide

-- Oracle Target_BinopImm_39: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .and 37 34 (.imm (2048#64))))) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .and 37 34 (.imm (2048#64))))) = [147#8, 114#8, 1#8, 128#8] := by decide

-- Oracle Target_BinopImm_40: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .and 37 34 (.imm (18446744073709551615#64))))) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .and 37 34 (.imm (18446744073709551615#64))))) = [147#8, 114#8, 241#8, 255#8] := by decide

-- Oracle Target_BinopReg_41: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .or 37 34 (.reg 35)))) = (((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .or 37 34 (.reg 35)))) = [179#8, 98#8, 49#8, 0#8] := by decide

-- Oracle Target_BinopImm_42: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .or 37 34 (.imm (0#64))))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .or 37 34 (.imm (0#64))))) = [147#8, 98#8, 1#8, 0#8] := by decide

-- Oracle Target_BinopImm_43: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .or 37 34 (.imm (2048#64))))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .or 37 34 (.imm (2048#64))))) = [147#8, 98#8, 1#8, 128#8] := by decide

-- Oracle Target_BinopImm_44: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .or 37 34 (.imm (18446744073709551615#64))))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .or 37 34 (.imm (18446744073709551615#64))))) = [147#8, 98#8, 241#8, 255#8] := by decide

-- Oracle Target_BinopReg_45: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .xor 37 34 (.reg 35)))) = (((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .xor 37 34 (.reg 35)))) = [179#8, 66#8, 49#8, 0#8] := by decide

-- Oracle Target_BinopImm_46: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .xor 37 34 (.imm (0#64))))) = (((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .xor 37 34 (.imm (0#64))))) = [147#8, 66#8, 1#8, 0#8] := by decide

-- Oracle Target_BinopImm_47: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .xor 37 34 (.imm (2048#64))))) = (((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .xor 37 34 (.imm (2048#64))))) = [147#8, 66#8, 1#8, 128#8] := by decide

-- Oracle Target_BinopImm_48: complete original AST and byte result.
example : riscvAst (.inst (.arith (.binop .xor 37 34 (.imm (18446744073709551615#64))))) = (((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.binop .xor 37 34 (.imm (18446744073709551615#64))))) = [147#8, 66#8, 241#8, 255#8] := by decide

-- Oracle Target_ShiftReg_49: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.reg 35)))) = (((instruction.Shift ((Shift.SLL (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.reg 35)))) = [179#8, 18#8, 49#8, 0#8] := by decide

-- Oracle Target_ShiftImm_50: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (0#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (0#64))))) = [147#8, 18#8, 1#8, 0#8] := by decide

-- Oracle Target_ShiftImm_51: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (1#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 1))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (1#64))))) = [147#8, 18#8, 17#8, 0#8] := by decide

-- Oracle Target_ShiftImm_52: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (63#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 63))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (63#64))))) = [147#8, 18#8, 241#8, 3#8] := by decide

-- Oracle Target_ShiftImm_53: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (64#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 64))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (64#64))))) = [147#8, 18#8, 1#8, 0#8] := by decide

-- Oracle Target_ShiftImm_54: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (65#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 65))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (65#64))))) = [147#8, 18#8, 17#8, 0#8] := by decide

-- Oracle Target_ShiftImm_55: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsl 37 34 (.imm (18446744073709551615#64))))) = (((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 18446744073709551615))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsl 37 34 (.imm (18446744073709551615#64))))) = [147#8, 18#8, 241#8, 3#8] := by decide

-- Oracle Target_ShiftReg_56: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.reg 35)))) = (((instruction.Shift ((Shift.SRL (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.reg 35)))) = [179#8, 82#8, 49#8, 0#8] := by decide

-- Oracle Target_ShiftImm_57: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (0#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (0#64))))) = [147#8, 82#8, 1#8, 0#8] := by decide

-- Oracle Target_ShiftImm_58: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (1#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 1))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (1#64))))) = [147#8, 82#8, 17#8, 0#8] := by decide

-- Oracle Target_ShiftImm_59: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (63#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 63))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (63#64))))) = [147#8, 82#8, 241#8, 3#8] := by decide

-- Oracle Target_ShiftImm_60: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (64#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 64))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (64#64))))) = [147#8, 82#8, 1#8, 0#8] := by decide

-- Oracle Target_ShiftImm_61: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (65#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 65))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (65#64))))) = [147#8, 82#8, 17#8, 0#8] := by decide

-- Oracle Target_ShiftImm_62: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .lsr 37 34 (.imm (18446744073709551615#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 18446744073709551615))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .lsr 37 34 (.imm (18446744073709551615#64))))) = [147#8, 82#8, 241#8, 3#8] := by decide

-- Oracle Target_ShiftReg_63: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.reg 35)))) = (((instruction.Shift ((Shift.SRA (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.reg 35)))) = [179#8, 82#8, 49#8, 64#8] := by decide

-- Oracle Target_ShiftImm_64: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (0#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (0#64))))) = [147#8, 82#8, 1#8, 64#8] := by decide

-- Oracle Target_ShiftImm_65: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (1#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 1))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (1#64))))) = [147#8, 82#8, 17#8, 64#8] := by decide

-- Oracle Target_ShiftImm_66: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (63#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 63))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (63#64))))) = [147#8, 82#8, 241#8, 67#8] := by decide

-- Oracle Target_ShiftImm_67: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (64#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 64))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (64#64))))) = [147#8, 82#8, 1#8, 64#8] := by decide

-- Oracle Target_ShiftImm_68: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (65#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 65))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (65#64))))) = [147#8, 82#8, 17#8, 64#8] := by decide

-- Oracle Target_ShiftImm_69: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .asr 37 34 (.imm (18446744073709551615#64))))) = (((instruction.Shift ((Shift.SRAI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 18446744073709551615))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.shift .asr 37 34 (.imm (18446744073709551615#64))))) = [147#8, 82#8, 241#8, 67#8] := by decide

-- Oracle Target_ShiftReg_70: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.reg 35)))) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 64))))))))) :: ((((instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 35))))))))) :: ((((instruction.Shift ((Shift.SLL (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 31))))))))) :: ((((instruction.Shift ((Shift.SRL (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.reg 35)))) = [147#8, 111#8, 0#8, 4#8, 179#8, 143#8, 63#8, 64#8, 179#8, 31#8, 241#8, 1#8, 179#8, 82#8, 49#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_71: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (0#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 64))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (0#64))))) = [147#8, 95#8, 1#8, 0#8, 147#8, 18#8, 1#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_72: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (1#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 1))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 63))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (1#64))))) = [147#8, 95#8, 17#8, 0#8, 147#8, 18#8, 241#8, 3#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_73: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (63#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 63))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 1))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (63#64))))) = [147#8, 95#8, 241#8, 3#8, 147#8, 18#8, 17#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_74: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (64#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 64))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (64#64))))) = [147#8, 95#8, 1#8, 0#8, 147#8, 18#8, 1#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_75: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (65#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 65))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (65#64))))) = [147#8, 95#8, 17#8, 0#8, 147#8, 18#8, 1#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_ShiftImm_76: complete original AST and byte result.
example : riscvAst (.inst (.arith (.shift .ror 37 34 (.imm (18446744073709551615#64))))) = (((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 18446744073709551615))))))))) :: ((((instruction.Shift ((Shift.SLLI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 6 0))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.inst (.arith (.shift .ror 37 34 (.imm (18446744073709551615#64))))) = [147#8, 95#8, 241#8, 3#8, 147#8, 18#8, 1#8, 0#8, 179#8, 226#8, 242#8, 1#8] := by decide

-- Oracle Target_Div_77: complete original AST and byte result.
example : riscvAst (.inst (.arith (.div 33 34 35))) = (((instruction.MulDiv ((MulDiv.DIV (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.div 33 34 35))) = [179#8, 64#8, 49#8, 2#8] := by decide

-- Oracle Target_LongMul_78: complete original AST and byte result.
example : riscvAst (.inst (.arith (.longMul 33 34 35 36))) = (((instruction.MulDiv ((MulDiv.MULHU (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 35), (BitVec.ofNat 5 36))))))))) :: ((((instruction.MulDiv ((MulDiv.MUL (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 35), (BitVec.ofNat 5 36))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.inst (.arith (.longMul 33 34 35 36))) = [179#8, 176#8, 65#8, 2#8, 51#8, 129#8, 65#8, 2#8] := by decide

-- Oracle Target_LongDiv_79: complete original AST and byte result.
example : riscvAst (.inst (.arith (.longDiv 33 34 35 36 37))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.arith (.longDiv 33 34 35 36 37))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_AddCarry_80: complete original AST and byte result.
example : riscvAst (.inst (.arith (.addCarry 33 34 35 36))) = (((instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 5 36))))))))) :: ((((instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 33), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 33), (BitVec.ofNat 5 31))))))))) :: ((((instruction.ArithR ((ArithR.SLTU (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 33), (BitVec.ofNat 5 31))))))))) :: ((((instruction.ArithR ((ArithR.OR (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 36), (BitVec.ofNat 5 31))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.arith (.addCarry 33 34 35 36))) = [179#8, 63#8, 64#8, 0#8, 179#8, 0#8, 49#8, 0#8, 51#8, 178#8, 48#8, 0#8, 179#8, 128#8, 240#8, 1#8, 179#8, 191#8, 240#8, 1#8, 51#8, 98#8, 242#8, 1#8] := by decide

-- Oracle Target_AddOverflow_81: complete original AST and byte result.
example : riscvAst (.inst (.arith (.addOverflow 33 34 35 36))) = (((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithR ((ArithR.ADD (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 35), (BitVec.ofNat 5 33))))))))) :: ((((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 36))))))))) :: ((((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 36), (BitVec.ofNat 6 63))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.arith (.addOverflow 33 34 35 36))) = [179#8, 79#8, 49#8, 0#8, 147#8, 207#8, 255#8, 255#8, 179#8, 0#8, 49#8, 0#8, 51#8, 194#8, 17#8, 0#8, 51#8, 242#8, 79#8, 0#8, 19#8, 82#8, 242#8, 3#8] := by decide

-- Oracle Target_SubOverflow_82: complete original AST and byte result.
example : riscvAst (.inst (.arith (.subOverflow 33 34 35 36))) = (((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.SUB (((BitVec.ofNat 5 33), (((BitVec.ofNat 5 34), (BitVec.ofNat 5 35))))))))) :: ((((instruction.ArithR ((ArithR.XOR (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 35), (BitVec.ofNat 5 33))))))))) :: ((((instruction.ArithI ((ArithI.XORI (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 36), (BitVec.ofNat 12 4095))))))))) :: ((((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 31), (BitVec.ofNat 5 36))))))))) :: ((((instruction.Shift ((Shift.SRLI (((BitVec.ofNat 5 36), (((BitVec.ofNat 5 36), (BitVec.ofNat 6 63))))))))) :: (([] : (List instruction)))))))))))))) := by decide
example : riscvEnc (.inst (.arith (.subOverflow 33 34 35 36))) = [179#8, 79#8, 49#8, 0#8, 179#8, 0#8, 49#8, 64#8, 51#8, 194#8, 17#8, 0#8, 19#8, 66#8, 242#8, 255#8, 51#8, 242#8, 79#8, 0#8, 19#8, 82#8, 242#8, 3#8] := by decide

-- Oracle Target_Mem_83: complete original AST and byte result.
example : riscvAst (.inst (.mem .load 37 (.addr 34 (0#64)))) = (((instruction.Load ((Load.LD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load 37 (.addr 34 (0#64)))) = [131#8, 50#8, 1#8, 0#8] := by decide

-- Oracle Target_Mem_84: complete original AST and byte result.
example : riscvAst (.inst (.mem .load 37 (.addr 34 (2047#64)))) = (((instruction.Load ((Load.LD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load 37 (.addr 34 (2047#64)))) = [131#8, 50#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_85: complete original AST and byte result.
example : riscvAst (.inst (.mem .load 37 (.addr 34 (2048#64)))) = (((instruction.Load ((Load.LD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load 37 (.addr 34 (2048#64)))) = [131#8, 50#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_86: complete original AST and byte result.
example : riscvAst (.inst (.mem .load 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Load ((Load.LD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load 37 (.addr 34 (18446744073709549568#64)))) = [131#8, 50#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_87: complete original AST and byte result.
example : riscvAst (.inst (.mem .load 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Load ((Load.LD (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load 37 (.addr 34 (18446744073709549567#64)))) = [131#8, 50#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_88: complete original AST and byte result.
example : riscvAst (.inst (.mem .load8 37 (.addr 34 (0#64)))) = (((instruction.Load ((Load.LBU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load8 37 (.addr 34 (0#64)))) = [131#8, 66#8, 1#8, 0#8] := by decide

-- Oracle Target_Mem_89: complete original AST and byte result.
example : riscvAst (.inst (.mem .load8 37 (.addr 34 (2047#64)))) = (((instruction.Load ((Load.LBU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load8 37 (.addr 34 (2047#64)))) = [131#8, 66#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_90: complete original AST and byte result.
example : riscvAst (.inst (.mem .load8 37 (.addr 34 (2048#64)))) = (((instruction.Load ((Load.LBU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load8 37 (.addr 34 (2048#64)))) = [131#8, 66#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_91: complete original AST and byte result.
example : riscvAst (.inst (.mem .load8 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Load ((Load.LBU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load8 37 (.addr 34 (18446744073709549568#64)))) = [131#8, 66#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_92: complete original AST and byte result.
example : riscvAst (.inst (.mem .load8 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Load ((Load.LBU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load8 37 (.addr 34 (18446744073709549567#64)))) = [131#8, 66#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_93: complete original AST and byte result.
example : riscvAst (.inst (.mem .load16 37 (.addr 34 (0#64)))) = (((instruction.Load ((Load.LHU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load16 37 (.addr 34 (0#64)))) = [131#8, 82#8, 1#8, 0#8] := by decide

-- Oracle Target_Mem_94: complete original AST and byte result.
example : riscvAst (.inst (.mem .load16 37 (.addr 34 (2047#64)))) = (((instruction.Load ((Load.LHU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load16 37 (.addr 34 (2047#64)))) = [131#8, 82#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_95: complete original AST and byte result.
example : riscvAst (.inst (.mem .load16 37 (.addr 34 (2048#64)))) = (((instruction.Load ((Load.LHU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load16 37 (.addr 34 (2048#64)))) = [131#8, 82#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_96: complete original AST and byte result.
example : riscvAst (.inst (.mem .load16 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Load ((Load.LHU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load16 37 (.addr 34 (18446744073709549568#64)))) = [131#8, 82#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_97: complete original AST and byte result.
example : riscvAst (.inst (.mem .load16 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Load ((Load.LHU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load16 37 (.addr 34 (18446744073709549567#64)))) = [131#8, 82#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_98: complete original AST and byte result.
example : riscvAst (.inst (.mem .load32 37 (.addr 34 (0#64)))) = (((instruction.Load ((Load.LWU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load32 37 (.addr 34 (0#64)))) = [131#8, 98#8, 1#8, 0#8] := by decide

-- Oracle Target_Mem_99: complete original AST and byte result.
example : riscvAst (.inst (.mem .load32 37 (.addr 34 (2047#64)))) = (((instruction.Load ((Load.LWU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load32 37 (.addr 34 (2047#64)))) = [131#8, 98#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_100: complete original AST and byte result.
example : riscvAst (.inst (.mem .load32 37 (.addr 34 (2048#64)))) = (((instruction.Load ((Load.LWU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load32 37 (.addr 34 (2048#64)))) = [131#8, 98#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_101: complete original AST and byte result.
example : riscvAst (.inst (.mem .load32 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Load ((Load.LWU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load32 37 (.addr 34 (18446744073709549568#64)))) = [131#8, 98#8, 1#8, 128#8] := by decide

-- Oracle Target_Mem_102: complete original AST and byte result.
example : riscvAst (.inst (.mem .load32 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Load ((Load.LWU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .load32 37 (.addr 34 (18446744073709549567#64)))) = [131#8, 98#8, 241#8, 127#8] := by decide

-- Oracle Target_Mem_103: complete original AST and byte result.
example : riscvAst (.inst (.mem .store 37 (.addr 34 (0#64)))) = (((instruction.Store ((Store.SD (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store 37 (.addr 34 (0#64)))) = [35#8, 48#8, 81#8, 0#8] := by decide

-- Oracle Target_Mem_104: complete original AST and byte result.
example : riscvAst (.inst (.mem .store 37 (.addr 34 (2047#64)))) = (((instruction.Store ((Store.SD (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store 37 (.addr 34 (2047#64)))) = [163#8, 63#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_105: complete original AST and byte result.
example : riscvAst (.inst (.mem .store 37 (.addr 34 (2048#64)))) = (((instruction.Store ((Store.SD (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store 37 (.addr 34 (2048#64)))) = [35#8, 48#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_106: complete original AST and byte result.
example : riscvAst (.inst (.mem .store 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Store ((Store.SD (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store 37 (.addr 34 (18446744073709549568#64)))) = [35#8, 48#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_107: complete original AST and byte result.
example : riscvAst (.inst (.mem .store 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Store ((Store.SD (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store 37 (.addr 34 (18446744073709549567#64)))) = [163#8, 63#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_108: complete original AST and byte result.
example : riscvAst (.inst (.mem .store8 37 (.addr 34 (0#64)))) = (((instruction.Store ((Store.SB (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store8 37 (.addr 34 (0#64)))) = [35#8, 0#8, 81#8, 0#8] := by decide

-- Oracle Target_Mem_109: complete original AST and byte result.
example : riscvAst (.inst (.mem .store8 37 (.addr 34 (2047#64)))) = (((instruction.Store ((Store.SB (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store8 37 (.addr 34 (2047#64)))) = [163#8, 15#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_110: complete original AST and byte result.
example : riscvAst (.inst (.mem .store8 37 (.addr 34 (2048#64)))) = (((instruction.Store ((Store.SB (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store8 37 (.addr 34 (2048#64)))) = [35#8, 0#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_111: complete original AST and byte result.
example : riscvAst (.inst (.mem .store8 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Store ((Store.SB (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store8 37 (.addr 34 (18446744073709549568#64)))) = [35#8, 0#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_112: complete original AST and byte result.
example : riscvAst (.inst (.mem .store8 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Store ((Store.SB (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store8 37 (.addr 34 (18446744073709549567#64)))) = [163#8, 15#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_113: complete original AST and byte result.
example : riscvAst (.inst (.mem .store16 37 (.addr 34 (0#64)))) = (((instruction.Store ((Store.SH (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store16 37 (.addr 34 (0#64)))) = [35#8, 16#8, 81#8, 0#8] := by decide

-- Oracle Target_Mem_114: complete original AST and byte result.
example : riscvAst (.inst (.mem .store16 37 (.addr 34 (2047#64)))) = (((instruction.Store ((Store.SH (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store16 37 (.addr 34 (2047#64)))) = [163#8, 31#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_115: complete original AST and byte result.
example : riscvAst (.inst (.mem .store16 37 (.addr 34 (2048#64)))) = (((instruction.Store ((Store.SH (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store16 37 (.addr 34 (2048#64)))) = [35#8, 16#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_116: complete original AST and byte result.
example : riscvAst (.inst (.mem .store16 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Store ((Store.SH (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store16 37 (.addr 34 (18446744073709549568#64)))) = [35#8, 16#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_117: complete original AST and byte result.
example : riscvAst (.inst (.mem .store16 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Store ((Store.SH (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store16 37 (.addr 34 (18446744073709549567#64)))) = [163#8, 31#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_118: complete original AST and byte result.
example : riscvAst (.inst (.mem .store32 37 (.addr 34 (0#64)))) = (((instruction.Store ((Store.SW (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store32 37 (.addr 34 (0#64)))) = [35#8, 32#8, 81#8, 0#8] := by decide

-- Oracle Target_Mem_119: complete original AST and byte result.
example : riscvAst (.inst (.mem .store32 37 (.addr 34 (2047#64)))) = (((instruction.Store ((Store.SW (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store32 37 (.addr 34 (2047#64)))) = [163#8, 47#8, 81#8, 126#8] := by decide

-- Oracle Target_Mem_120: complete original AST and byte result.
example : riscvAst (.inst (.mem .store32 37 (.addr 34 (2048#64)))) = (((instruction.Store ((Store.SW (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store32 37 (.addr 34 (2048#64)))) = [35#8, 32#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_121: complete original AST and byte result.
example : riscvAst (.inst (.mem .store32 37 (.addr 34 (18446744073709549568#64)))) = (((instruction.Store ((Store.SW (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store32 37 (.addr 34 (18446744073709549568#64)))) = [35#8, 32#8, 81#8, 128#8] := by decide

-- Oracle Target_Mem_122: complete original AST and byte result.
example : riscvAst (.inst (.mem .store32 37 (.addr 34 (18446744073709549567#64)))) = (((instruction.Store ((Store.SW (((BitVec.ofNat 5 34), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.mem .store32 37 (.addr 34 (18446744073709549567#64)))) = [163#8, 47#8, 81#8, 126#8] := by decide

-- Oracle Target_FP_123: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpLess 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpLess 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_124: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpLessEqual 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpLessEqual 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_125: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpEqual 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpEqual 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_126: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpAbs 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpAbs 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_127: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpNeg 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpNeg 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_128: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpSqrt 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpSqrt 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_129: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpAdd 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpAdd 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_130: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpSub 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpSub 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_131: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpMul 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpMul 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_132: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpDiv 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpDiv 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_133: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpFma 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpFma 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_134: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpMov 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpMov 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_135: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpMovToReg 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpMovToReg 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_136: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpMovFromReg 37 38 39))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpMovFromReg 37 38 39))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_137: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpToInt 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpToInt 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_FP_138: complete original AST and byte result.
example : riscvAst (.inst (.fp (.fpFromInt 37 38))) = (((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.inst (.fp (.fpFromInt 37 38))) = [19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Jump_139: complete original AST and byte result.
example : riscvAst (.jump (18446744073708503039#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 31), (BitVec.ofNat 20 1048320))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jump (18446744073708503039#64)) = [151#8, 15#8, 240#8, 255#8, 103#8, 128#8, 255#8, 255#8] := by decide

-- Oracle Target_Jump_140: complete original AST and byte result.
example : riscvAst (.jump (18446744073708503040#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 524288))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jump (18446744073708503040#64)) = [111#8, 0#8, 0#8, 128#8] := by decide

-- Oracle Target_Jump_141: complete original AST and byte result.
example : riscvAst (.jump (18446744073709551615#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048575))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jump (18446744073709551615#64)) = [111#8, 240#8, 255#8, 255#8] := by decide

-- Oracle Target_Jump_142: complete original AST and byte result.
example : riscvAst (.jump (0#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jump (0#64)) = [111#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Jump_143: complete original AST and byte result.
example : riscvAst (.jump (1048575#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 524287))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jump (1048575#64)) = [111#8, 240#8, 255#8, 127#8] := by decide

-- Oracle Target_Jump_144: complete original AST and byte result.
example : riscvAst (.jump (1048576#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 31), (BitVec.ofNat 20 256))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jump (1048576#64)) = [151#8, 15#8, 16#8, 0#8, 103#8, 128#8, 15#8, 0#8] := by decide

-- Oracle Target_Jump_145: complete original AST and byte result.
example : riscvAst (.jump (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jump (9223372036854775808#64)) = [151#8, 15#8, 0#8, 0#8, 103#8, 128#8, 15#8, 0#8] := by decide

-- Oracle Target_Jump_146: complete original AST and byte result.
example : riscvAst (.jump (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 31), (BitVec.ofNat 20 0))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jump (9223372036854775807#64)) = [151#8, 15#8, 0#8, 0#8, 103#8, 128#8, 255#8, 255#8] := by decide

-- Oracle Target_Call_147: complete original AST and byte result.
example : riscvAst (.call (18446744073708503039#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 1), (BitVec.ofNat 20 1048320))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 1), (((BitVec.ofNat 5 1), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.call (18446744073708503039#64)) = [151#8, 0#8, 240#8, 255#8, 231#8, 128#8, 240#8, 255#8] := by decide

-- Oracle Target_Call_148: complete original AST and byte result.
example : riscvAst (.call (18446744073708503040#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 1), (BitVec.ofNat 20 524288))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.call (18446744073708503040#64)) = [239#8, 0#8, 0#8, 128#8] := by decide

-- Oracle Target_Call_149: complete original AST and byte result.
example : riscvAst (.call (18446744073709551615#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 1), (BitVec.ofNat 20 1048575))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.call (18446744073709551615#64)) = [239#8, 240#8, 255#8, 255#8] := by decide

-- Oracle Target_Call_150: complete original AST and byte result.
example : riscvAst (.call (0#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 1), (BitVec.ofNat 20 0))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.call (0#64)) = [239#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Call_151: complete original AST and byte result.
example : riscvAst (.call (1048575#64)) = (((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 1), (BitVec.ofNat 20 524287))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.call (1048575#64)) = [239#8, 240#8, 255#8, 127#8] := by decide

-- Oracle Target_Call_152: complete original AST and byte result.
example : riscvAst (.call (1048576#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 1), (BitVec.ofNat 20 256))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 1), (((BitVec.ofNat 5 1), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.call (1048576#64)) = [151#8, 0#8, 16#8, 0#8, 231#8, 128#8, 0#8, 0#8] := by decide

-- Oracle Target_Call_153: complete original AST and byte result.
example : riscvAst (.call (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 1), (BitVec.ofNat 20 0))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 1), (((BitVec.ofNat 5 1), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.call (9223372036854775808#64)) = [151#8, 0#8, 0#8, 0#8, 231#8, 128#8, 0#8, 0#8] := by decide

-- Oracle Target_Call_154: complete original AST and byte result.
example : riscvAst (.call (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 1), (BitVec.ofNat 20 0))))))) :: ((((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 1), (((BitVec.ofNat 5 1), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.call (9223372036854775807#64)) = [151#8, 0#8, 0#8, 0#8, 231#8, 128#8, 240#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_155: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (18446744073709547523#64)) = [99#8, 148#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_156: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (18446744073709547524#64)) = [99#8, 130#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_157: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (18446744073709551615#64)) = [227#8, 143#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_158: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (0#64)) = [99#8, 128#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_159: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (4095#64)) = [227#8, 143#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_160: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (4096#64)) = [99#8, 148#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_161: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (9223372036854775808#64)) = [99#8, 148#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_162: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.reg 34) (9223372036854775807#64)) = [99#8, 148#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_163: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 148#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_164: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 128#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_165: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 141#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_166: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 142#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_167: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 141#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_168: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 148#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_169: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 148#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_170: complete original AST and byte result.
example : riscvAst (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .equal 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 148#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_171: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (18446744073709547523#64)) = [99#8, 212#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_172: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (18446744073709547524#64)) = [99#8, 194#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_173: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (18446744073709551615#64)) = [227#8, 207#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_174: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (0#64)) = [99#8, 192#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_175: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (4095#64)) = [227#8, 207#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_176: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (4096#64)) = [99#8, 212#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_177: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (9223372036854775808#64)) = [99#8, 212#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_178: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.reg 34) (9223372036854775807#64)) = [99#8, 212#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_179: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 212#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_180: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 192#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_181: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 205#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_182: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 206#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_183: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 205#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_184: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 212#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_185: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 212#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_186: complete original AST and byte result.
example : riscvAst (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .less 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 212#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_187: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (18446744073709547523#64)) = [99#8, 244#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_188: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (18446744073709547524#64)) = [99#8, 226#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_189: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (18446744073709551615#64)) = [227#8, 239#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_190: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (0#64)) = [99#8, 224#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_191: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (4095#64)) = [227#8, 239#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_192: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (4096#64)) = [99#8, 244#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_193: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (9223372036854775808#64)) = [99#8, 244#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_194: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.reg 34) (9223372036854775807#64)) = [99#8, 244#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_195: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 244#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_196: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 224#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_197: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 237#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_198: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 238#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_199: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 237#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_200: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 244#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_201: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 244#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_202: complete original AST and byte result.
example : riscvAst (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .lower 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 244#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_203: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (18446744073709547523#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (18446744073709547523#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 148#8, 15#8, 0#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_204: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (18446744073709547524#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (18446744073709547524#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 128#8, 15#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_205: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (18446744073709551615#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (18446744073709551615#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 141#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_206: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (0#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (0#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 142#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_207: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (4095#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (4095#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 141#8, 15#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_208: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (4096#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (4096#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 148#8, 15#8, 0#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_209: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (9223372036854775808#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (9223372036854775808#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 148#8, 15#8, 0#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_210: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.reg 34) (9223372036854775807#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.reg 34) (9223372036854775807#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 148#8, 15#8, 0#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_211: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 148#8, 15#8, 0#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_212: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 128#8, 15#8, 128#8] := by decide

-- Oracle Target_JumpCmpImm_213: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 141#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpImm_214: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 142#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpImm_215: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 141#8, 15#8, 126#8] := by decide

-- Oracle Target_JumpCmpImm_216: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 148#8, 15#8, 0#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_217: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 148#8, 15#8, 0#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_218: complete original AST and byte result.
example : riscvAst (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .test 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 148#8, 15#8, 0#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_219: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (18446744073709547523#64)) = [99#8, 132#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_220: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (18446744073709547524#64)) = [99#8, 146#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_221: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (18446744073709551615#64)) = [227#8, 159#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_222: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (0#64)) = [99#8, 144#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_223: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (4095#64)) = [227#8, 159#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_224: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (4096#64)) = [99#8, 132#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_225: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (9223372036854775808#64)) = [99#8, 132#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_226: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.reg 34) (9223372036854775807#64)) = [99#8, 132#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_227: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 132#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_228: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 144#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_229: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 157#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_230: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 158#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_231: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 157#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_232: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 132#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_233: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 132#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_234: complete original AST and byte result.
example : riscvAst (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notEqual 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 132#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_235: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (18446744073709547523#64)) = [99#8, 196#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_236: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (18446744073709547524#64)) = [99#8, 210#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_237: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (18446744073709551615#64)) = [227#8, 223#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_238: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (0#64)) = [99#8, 208#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_239: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (4095#64)) = [227#8, 223#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_240: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (4096#64)) = [99#8, 196#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_241: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (9223372036854775808#64)) = [99#8, 196#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_242: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.reg 34) (9223372036854775807#64)) = [99#8, 196#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_243: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 196#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_244: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 208#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_245: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 221#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_246: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 222#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_247: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGE (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 221#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_248: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 196#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_249: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 196#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_250: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLT (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLess 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 196#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_251: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (18446744073709547523#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046527))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (18446744073709547523#64)) = [99#8, 228#8, 34#8, 0#8, 111#8, 224#8, 255#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_252: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (18446744073709547524#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2050))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (18446744073709547524#64)) = [99#8, 242#8, 34#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_253: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (18446744073709551615#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (18446744073709551615#64)) = [227#8, 255#8, 34#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_254: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (0#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (0#64)) = [99#8, 240#8, 34#8, 0#8] := by decide

-- Oracle Target_JumpCmpReg_255: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (4095#64)) = (((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (4095#64)) = [227#8, 255#8, 34#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_256: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (4096#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2046))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (4096#64)) = [99#8, 228#8, 34#8, 0#8, 111#8, 0#8, 208#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_257: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (9223372036854775808#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048574))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (9223372036854775808#64)) = [99#8, 228#8, 34#8, 0#8, 111#8, 240#8, 223#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_258: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.reg 34) (9223372036854775807#64)) = (((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 34), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048573))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.reg 34) (9223372036854775807#64)) = [99#8, 228#8, 34#8, 0#8, 111#8, 240#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_259: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 228#8, 242#8, 1#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_260: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 240#8, 242#8, 129#8] := by decide

-- Oracle Target_JumpCmpImm_261: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 253#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_262: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 254#8, 242#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_263: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BGEU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 111#8, 240#8, 127#8, 227#8, 253#8, 242#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_264: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 228#8, 242#8, 1#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_265: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 228#8, 242#8, 1#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_266: complete original AST and byte result.
example : riscvAst (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ORI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BLTU (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notLower 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 111#8, 240#8, 127#8, 99#8, 228#8, 242#8, 1#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_267: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (18446744073709547523#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (18446744073709547523#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 132#8, 15#8, 0#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_268: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (18446744073709547524#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (18446744073709547524#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 144#8, 15#8, 128#8] := by decide

-- Oracle Target_JumpCmpReg_269: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (18446744073709551615#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (18446744073709551615#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 157#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_270: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (0#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (0#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 158#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpReg_271: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (4095#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (4095#64)) = [179#8, 255#8, 34#8, 0#8, 227#8, 157#8, 15#8, 126#8] := by decide

-- Oracle Target_JumpCmpReg_272: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (4096#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (4096#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 132#8, 15#8, 0#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpReg_273: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (9223372036854775808#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (9223372036854775808#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 132#8, 15#8, 0#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpReg_274: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.reg 34) (9223372036854775807#64)) = (((instruction.ArithR ((ArithR.AND (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 5 34))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.reg 34) (9223372036854775807#64)) = [179#8, 255#8, 34#8, 0#8, 99#8, 132#8, 15#8, 0#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_275: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1046525))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709547523#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 132#8, 15#8, 0#8, 111#8, 224#8, 191#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_276: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709547524#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 144#8, 15#8, 128#8] := by decide

-- Oracle Target_JumpCmpImm_277: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4093))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (18446744073709551615#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 157#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpImm_278: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (0#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4094))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (0#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 158#8, 15#8, 254#8] := by decide

-- Oracle Target_JumpCmpImm_279: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (4095#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BNE (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2045))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (4095#64)) = [147#8, 255#8, 242#8, 127#8, 227#8, 157#8, 15#8, 126#8] := by decide

-- Oracle Target_JumpCmpImm_280: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (4096#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 2044))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (4096#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 132#8, 15#8, 0#8, 111#8, 0#8, 144#8, 127#8] := by decide

-- Oracle Target_JumpCmpImm_281: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048572))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (9223372036854775808#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 132#8, 15#8, 0#8, 111#8, 240#8, 159#8, 255#8] := by decide

-- Oracle Target_JumpCmpImm_282: complete original AST and byte result.
example : riscvAst (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.ANDI (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: ((((instruction.Branch ((Branch.BEQ (((BitVec.ofNat 5 31), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4))))))))) :: ((((instruction.Branch ((Branch.JAL (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048571))))))) :: (([] : (List instruction)))))))) := by decide
example : riscvEnc (.jumpCmp .notTest 37 (.imm (18446744073709549567#64)) (9223372036854775807#64)) = [147#8, 255#8, 242#8, 127#8, 99#8, 132#8, 15#8, 0#8, 111#8, 240#8, 127#8, 255#8] := by decide

-- Oracle Target_JumpReg_283: complete original AST and byte result.
example : riscvAst (.jumpReg 0) = (((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpReg 0) = [103#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_JumpReg_284: complete original AST and byte result.
example : riscvAst (.jumpReg 31) = (((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 31), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpReg 31) = [103#8, 128#8, 15#8, 0#8] := by decide

-- Oracle Target_JumpReg_285: complete original AST and byte result.
example : riscvAst (.jumpReg 37) = (((instruction.Branch ((Branch.JALR (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))) := by decide
example : riscvEnc (.jumpReg 37) = [103#8, 128#8, 2#8, 0#8] := by decide

-- Oracle Target_Loc_286: complete original AST and byte result.
example : riscvAst (.loc 0 (0#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (0#64)) = [23#8, 0#8, 0#8, 0#8, 19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Loc_287: complete original AST and byte result.
example : riscvAst (.loc 0 (2047#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (2047#64)) = [23#8, 0#8, 0#8, 0#8, 19#8, 0#8, 240#8, 127#8] := by decide

-- Oracle Target_Loc_288: complete original AST and byte result.
example : riscvAst (.loc 0 (2048#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (2048#64)) = [23#8, 16#8, 0#8, 0#8, 19#8, 0#8, 0#8, 128#8] := by decide

-- Oracle Target_Loc_289: complete original AST and byte result.
example : riscvAst (.loc 0 (18446744073709549568#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (18446744073709549568#64)) = [23#8, 0#8, 0#8, 0#8, 19#8, 0#8, 0#8, 128#8] := by decide

-- Oracle Target_Loc_290: complete original AST and byte result.
example : riscvAst (.loc 0 (18446744073709549567#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (18446744073709549567#64)) = [23#8, 240#8, 255#8, 255#8, 19#8, 0#8, 240#8, 127#8] := by decide

-- Oracle Target_Loc_291: complete original AST and byte result.
example : riscvAst (.loc 0 (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (9223372036854775808#64)) = [23#8, 0#8, 0#8, 0#8, 19#8, 0#8, 0#8, 0#8] := by decide

-- Oracle Target_Loc_292: complete original AST and byte result.
example : riscvAst (.loc 0 (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 0), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 0), (((BitVec.ofNat 5 0), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 0 (9223372036854775807#64)) = [23#8, 0#8, 0#8, 0#8, 19#8, 0#8, 240#8, 255#8] := by decide

-- Oracle Target_Loc_293: complete original AST and byte result.
example : riscvAst (.loc 37 (0#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (0#64)) = [151#8, 2#8, 0#8, 0#8, 147#8, 130#8, 2#8, 0#8] := by decide

-- Oracle Target_Loc_294: complete original AST and byte result.
example : riscvAst (.loc 37 (2047#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (2047#64)) = [151#8, 2#8, 0#8, 0#8, 147#8, 130#8, 242#8, 127#8] := by decide

-- Oracle Target_Loc_295: complete original AST and byte result.
example : riscvAst (.loc 37 (2048#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 1))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (2048#64)) = [151#8, 18#8, 0#8, 0#8, 147#8, 130#8, 2#8, 128#8] := by decide

-- Oracle Target_Loc_296: complete original AST and byte result.
example : riscvAst (.loc 37 (18446744073709549568#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2048))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (18446744073709549568#64)) = [151#8, 2#8, 0#8, 0#8, 147#8, 130#8, 2#8, 128#8] := by decide

-- Oracle Target_Loc_297: complete original AST and byte result.
example : riscvAst (.loc 37 (18446744073709549567#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 1048575))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 2047))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (18446744073709549567#64)) = [151#8, 242#8, 255#8, 255#8, 147#8, 130#8, 242#8, 127#8] := by decide

-- Oracle Target_Loc_298: complete original AST and byte result.
example : riscvAst (.loc 37 (9223372036854775808#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 0))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (9223372036854775808#64)) = [151#8, 2#8, 0#8, 0#8, 147#8, 130#8, 2#8, 0#8] := by decide

-- Oracle Target_Loc_299: complete original AST and byte result.
example : riscvAst (.loc 37 (9223372036854775807#64)) = (((instruction.ArithI ((ArithI.AUIPC (((BitVec.ofNat 5 37), (BitVec.ofNat 20 0))))))) :: ((((instruction.ArithI ((ArithI.ADDI (((BitVec.ofNat 5 37), (((BitVec.ofNat 5 37), (BitVec.ofNat 12 4095))))))))) :: (([] : (List instruction)))))) := by decide
example : riscvEnc (.loc 37 (9223372036854775807#64)) = [151#8, 2#8, 0#8, 0#8, 147#8, 130#8, 242#8, 255#8] := by decide

end Flapjack.Test.RiscVNativeTargetParity
