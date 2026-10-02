import Flapjack.RiscV.Lab
import Flapjack.RiscV.Encoding

/-! Fresh original riscv_ast/riscv_encode byte vectors from
scripts/hol-probes/riscv_jumpcmp_polarity_probe.out. These compare the actual
executed Lab emitter across all eight predicates, both operand forms and both
short/long ranges. Untagged regression infrastructure, not a HOL proof port. -/
namespace Flapjack.Test.RiscVBranchPolarity
open Flapjack Flapjack.RiscV
private def emitted (op : Cmp) (rhs : WordRegImm (BitVec 64)) (target : Nat) :=
  (labCompileAsm (width := 64) {services := []} 7 [(99,target)] 0
    (.jumpCmp op 1 rhs ⟨7,99⟩)).map (fun xs => (encodeInstructions xs).map BitVec.toNat)

-- branch_equal_reg_short
example : emitted .equal (.reg 2) 16 = some [99, 136, 32, 0] := by decide

-- branch_equal_reg_long
example : emitted .equal (.reg 2) 8192 = some [99, 148, 32, 0, 111, 16, 208, 127] := by decide

-- branch_equal_imm_short
example : emitted .equal (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 134, 240, 1] := by decide

-- branch_equal_imm_long
example : emitted .equal (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 148, 240, 1, 111, 16, 144, 127] := by decide

-- branch_notequal_reg_short
example : emitted .notEqual (.reg 2) 16 = some [99, 152, 32, 0] := by decide

-- branch_notequal_reg_long
example : emitted .notEqual (.reg 2) 8192 = some [99, 132, 32, 0, 111, 16, 208, 127] := by decide

-- branch_notequal_imm_short
example : emitted .notEqual (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 150, 240, 1] := by decide

-- branch_notequal_imm_long
example : emitted .notEqual (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 132, 240, 1, 111, 16, 144, 127] := by decide

-- branch_less_reg_short
example : emitted .less (.reg 2) 16 = some [99, 200, 32, 0] := by decide

-- branch_less_reg_long
example : emitted .less (.reg 2) 8192 = some [99, 212, 32, 0, 111, 16, 208, 127] := by decide

-- branch_less_imm_short
example : emitted .less (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 198, 240, 1] := by decide

-- branch_less_imm_long
example : emitted .less (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 212, 240, 1, 111, 16, 144, 127] := by decide

-- branch_notless_reg_short
example : emitted .notLess (.reg 2) 16 = some [99, 216, 32, 0] := by decide

-- branch_notless_reg_long
example : emitted .notLess (.reg 2) 8192 = some [99, 196, 32, 0, 111, 16, 208, 127] := by decide

-- branch_notless_imm_short
example : emitted .notLess (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 214, 240, 1] := by decide

-- branch_notless_imm_long
example : emitted .notLess (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 196, 240, 1, 111, 16, 144, 127] := by decide

-- branch_lower_reg_short
example : emitted .lower (.reg 2) 16 = some [99, 232, 32, 0] := by decide

-- branch_lower_reg_long
example : emitted .lower (.reg 2) 8192 = some [99, 244, 32, 0, 111, 16, 208, 127] := by decide

-- branch_lower_imm_short
example : emitted .lower (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 230, 240, 1] := by decide

-- branch_lower_imm_long
example : emitted .lower (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 244, 240, 1, 111, 16, 144, 127] := by decide

-- branch_notlower_reg_short
example : emitted .notLower (.reg 2) 16 = some [99, 248, 32, 0] := by decide

-- branch_notlower_reg_long
example : emitted .notLower (.reg 2) 8192 = some [99, 228, 32, 0, 111, 16, 208, 127] := by decide

-- branch_notlower_imm_short
example : emitted .notLower (.imm (BitVec.ofNat 64 7)) 16 = some [147, 111, 112, 0, 99, 246, 240, 1] := by decide

-- branch_notlower_imm_long
example : emitted .notLower (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 111, 112, 0, 99, 228, 240, 1, 111, 16, 144, 127] := by decide

-- branch_test_reg_short
example : emitted .test (.reg 2) 16 = some [179, 255, 32, 0, 99, 134, 15, 0] := by decide

-- branch_test_reg_long
example : emitted .test (.reg 2) 8192 = some [179, 255, 32, 0, 99, 148, 15, 0, 111, 16, 144, 127] := by decide

-- branch_test_imm_short
example : emitted .test (.imm (BitVec.ofNat 64 7)) 16 = some [147, 255, 112, 0, 99, 134, 15, 0] := by decide

-- branch_test_imm_long
example : emitted .test (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 255, 112, 0, 99, 148, 15, 0, 111, 16, 144, 127] := by decide

-- branch_nottest_reg_short
example : emitted .notTest (.reg 2) 16 = some [179, 255, 32, 0, 99, 150, 15, 0] := by decide

-- branch_nottest_reg_long
example : emitted .notTest (.reg 2) 8192 = some [179, 255, 32, 0, 99, 132, 15, 0, 111, 16, 144, 127] := by decide

-- branch_nottest_imm_short
example : emitted .notTest (.imm (BitVec.ofNat 64 7)) 16 = some [147, 255, 112, 0, 99, 150, 15, 0] := by decide

-- branch_nottest_imm_long
example : emitted .notTest (.imm (BitVec.ofNat 64 7)) 8192 = some [147, 255, 112, 0, 99, 132, 15, 0, 111, 16, 144, 127] := by decide

end Flapjack.Test.RiscVBranchPolarity
